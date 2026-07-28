import EverettianProbability.Frequency.Distribution
import Mathlib.Data.Nat.Choose.Sum

/-!
**FR.** # Moments de la distribution des fréquences

Le premier moment du nombre de résultats égaux à `1` est défini par la
somme finie

`∑ k, k · frequencyMass R α β k`.

Le module formalise les moments du nombre de résultats `1`, la variance du
compte, la fréquence relative, ses premier et second moments, ainsi que sa
variance exacte pour `R > 0`. Il établit les identités binomiales générales
disponibles et leurs spécialisations sous normalisation.

Pour le premier moment, il prouve l'identité binomiale pondérée générale

`∑ k k C(R,k) a^(R-k) b^k
   = R b (a+b)^(R-1)`,

puis l'applique aux poids projectifs des cellules de fréquence. Sous
l'hypothèse `‖α‖² + ‖β‖² = 1`, le premier moment vaut exactement
`R ‖β‖²`.

La concentration, la définition des cellules typiques et atypiques, et la
typicalité asymptotique restent ouvertes.

**EN.** # Moments of the frequency distribution

The first moment of the number of outcomes equal to `1` is defined by the
finite sum

`∑ k, k · frequencyMass R α β k`.

The module formalizes the moments of the number of outcomes equal to `1`, the
count variance, relative frequency, its first and second moments, and its
exact variance for `R > 0`. It establishes the available general binomial
identities and their specializations under normalization.

For the first moment, it proves the general weighted binomial identity

`∑ k k C(R,k) a^(R-k) b^k
   = R b (a+b)^(R-1)`,

and then applies it to the projective weights of the frequency cells.
Under the hypothesis `‖α‖² + ‖β‖² = 1`, the first moment is exactly
`R ‖β‖²`.

Concentration, the definition of typical and atypical cells, and asymptotic
typicality remain open.
-/

namespace EverettianProbability.Frequency

open scoped Classical BigOperators

noncomputable section

/-- **FR.** Identité binomiale pondérée donnant le premier moment brut.

**EN.** Weighted binomial identity giving the raw first moment. -/
theorem sum_range_cast_mul_choose_mul_powers
    (R : ℕ) (a b : ℝ) :
    (∑ k ∈ Finset.range (R + 1),
        (k : ℝ) * (Nat.choose R k : ℝ) *
          (a ^ (R - k) * b ^ k)) =
      (R : ℝ) * b * (a + b) ^ (R - 1) := by
  cases R with
  | zero =>
      simp
  | succ n =>
      rw [Finset.sum_range_succ']
      simp only [
        Nat.cast_zero,
        zero_mul,
        add_zero
      ]
      calc
        (∑ k ∈ Finset.range (n + 1),
            ((k + 1 : ℕ) : ℝ) *
              (Nat.choose (n + 1) (k + 1) : ℝ) *
              (a ^ (n + 1 - (k + 1)) *
                b ^ (k + 1))) =
            ∑ k ∈ Finset.range (n + 1),
              ((n + 1 : ℕ) : ℝ) * b *
                ((Nat.choose n k : ℝ) *
                  (a ^ (n - k) * b ^ k)) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hchoose :
              ((k + 1 : ℕ) : ℝ) *
                  (Nat.choose (n + 1) (k + 1) : ℝ) =
                ((n + 1 : ℕ) : ℝ) *
                  (Nat.choose n k : ℝ) := by
            exact_mod_cast
              (by
                simpa [Nat.mul_comm] using
                  (Nat.add_one_mul_choose_eq n k).symm)
          rw [
            Nat.add_sub_add_right,
            pow_succ,
            hchoose
          ]
          ring
        _ =
            ((n + 1 : ℕ) : ℝ) * b *
              (∑ k ∈ Finset.range (n + 1),
                (Nat.choose n k : ℝ) *
                  (a ^ (n - k) * b ^ k)) := by
          rw [Finset.mul_sum]
        _ =
            ((n + 1 : ℕ) : ℝ) * b *
              (a + b) ^ n := by
          congr 1
          simpa [
            add_comm,
            mul_comm,
            mul_left_comm,
            mul_assoc
          ] using
            (add_pow b a n).symm
        _ =
            (((n + 1 : ℕ) : ℝ) * b *
              (a + b) ^ ((n + 1) - 1)) := by
          simp

/-- **FR.** Premier moment brut du nombre de résultats égaux à `1`.

**EN.** Raw first moment of the number of outcomes equal to `1`. -/
def frequencyCountFirstMoment
    (R : ℕ) (α β : ℂ) : ℝ :=
  ∑ k : Fin (R + 1),
    (k.val : ℝ) * frequencyMass R α β k

/-- **FR.** Le premier moment est non négatif.

**EN.** The first moment is nonnegative. -/
theorem frequencyCountFirstMoment_nonneg
    (R : ℕ) (α β : ℂ) :
    0 ≤ frequencyCountFirstMoment R α β := by
  unfold frequencyCountFirstMoment
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg
      (Nat.cast_nonneg k.val)
      (frequencyMass_nonneg R α β k)

/-- **FR.** Sans supposer la normalisation élémentaire, le premier moment
vaut

`R ‖β‖² (‖α‖² + ‖β‖²)^(R-1)`.

**EN.** Without assuming elementary normalization, the first moment is

`R ‖β‖² (‖α‖² + ‖β‖²)^(R-1)`. -/
theorem frequencyCountFirstMoment_eq_general
    (R : ℕ) (α β : ℂ) :
    frequencyCountFirstMoment R α β =
      (R : ℝ) * (‖β‖ ^ 2) *
        (‖α‖ ^ 2 + ‖β‖ ^ 2) ^ (R - 1) := by
  classical
  let f : ℕ → ℝ := fun k =>
    if hk : k < R + 1 then
      (k : ℝ) * frequencyMass R α β ⟨k, hk⟩
    else 0
  have hfin :
      frequencyCountFirstMoment R α β =
        ∑ k : Fin (R + 1), f k := by
    unfold frequencyCountFirstMoment
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [f]
    rw [dif_pos k.isLt]
  have hsum :
      (∑ k ∈ Finset.range (R + 1), f k) =
        ∑ k ∈ Finset.range (R + 1),
          (k : ℝ) * (Nat.choose R k : ℝ) *
            ((‖α‖ ^ 2) ^ (R - k) *
              (‖β‖ ^ 2) ^ k) := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [f]
    rw [dif_pos (Finset.mem_range.mp hk)]
    rw [frequencyMass_eq_binomial]
    ring
  calc
    frequencyCountFirstMoment R α β =
        ∑ k : Fin (R + 1), f k := hfin
    _ = ∑ k ∈ Finset.range (R + 1), f k :=
      Fin.sum_univ_eq_sum_range f (R + 1)
    _ = ∑ k ∈ Finset.range (R + 1),
          (k : ℝ) * (Nat.choose R k : ℝ) *
            ((‖α‖ ^ 2) ^ (R - k) *
              (‖β‖ ^ 2) ^ k) := hsum
    _ = (R : ℝ) * (‖β‖ ^ 2) *
          (‖α‖ ^ 2 + ‖β‖ ^ 2) ^ (R - 1) := by
      simpa [mul_assoc] using
        (sum_range_cast_mul_choose_mul_powers
          R (‖α‖ ^ 2) (‖β‖ ^ 2))

/-- **FR.** Sous l'hypothèse de normalisation élémentaire, le nombre moyen
de résultats égaux à `1` est exactement `R ‖β‖²`.

**EN.** Under the elementary normalization hypothesis, the mean number of
outcomes equal to `1` is exactly `R ‖β‖²`. -/
theorem frequencyCountFirstMoment_eq
    (R : ℕ) (α β : ℂ)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    frequencyCountFirstMoment R α β =
      (R : ℝ) * (‖β‖ ^ 2) := by
  rw [
    frequencyCountFirstMoment_eq_general,
    hnorm,
    one_pow,
    mul_one
  ]

/-- **FR.** Identité binomiale pondérée donnant le second moment
factoriel brut.

**EN.** Weighted binomial identity giving the raw second factorial
moment. -/
theorem sum_range_cast_fallingTwo_mul_choose_mul_powers
    (R : ℕ) (a b : ℝ) :
    (∑ k ∈ Finset.range (R + 1),
        ((k * (k - 1) : ℕ) : ℝ) *
          (Nat.choose R k : ℝ) *
          (a ^ (R - k) * b ^ k)) =
      (R : ℝ) * ((R - 1 : ℕ) : ℝ) *
        b ^ 2 * (a + b) ^ (R - 2) := by
  cases R with
  | zero =>
      simp
  | succ R =>
      cases R with
      | zero =>
          norm_num [Finset.sum_range_succ']
      | succ n =>
          rw [Finset.sum_range_succ', Finset.sum_range_succ']
          norm_num
          change
            (∑ k ∈ Finset.range (n + 1),
                ((k : ℝ) + 1 + 1) * ((k : ℝ) + 1) *
                  (Nat.choose (n + 1 + 1) (k + 1 + 1) : ℝ) *
                  (a ^ (n + 1 + 1 - (k + 1 + 1)) *
                    b ^ (k + 1 + 1))) =
              ((n : ℝ) + 1 + 1) * ((n : ℝ) + 1) * b ^ 2 *
                (a + b) ^ (n + 1 + 1 - 2)
          calc
            (∑ k ∈ Finset.range (n + 1),
                ((k : ℝ) + 1 + 1) * ((k : ℝ) + 1) *
                  (Nat.choose (n + 1 + 1) (k + 1 + 1) : ℝ) *
                  (a ^ (n + 1 + 1 - (k + 1 + 1)) *
                    b ^ (k + 1 + 1))) =
                ∑ k ∈ Finset.range (n + 1),
                  ((n : ℝ) + 1 + 1) * ((n : ℝ) + 1) * b ^ 2 *
                    ((Nat.choose n k : ℝ) *
                      (a ^ (n - k) * b ^ k)) := by
              apply Finset.sum_congr rfl
              intro k hk
              have hchoose (k : ℕ) :
                  (k + 2) * (k + 1) *
                      Nat.choose (n + 2) (k + 2) =
                    (n + 2) * (n + 1) *
                      Nat.choose n k := by
                have hfirst :
                    (k + 2) * Nat.choose (n + 2) (k + 2) =
                      (n + 2) * Nat.choose (n + 1) (k + 1) := by
                  calc
                    (k + 2) * Nat.choose (n + 2) (k + 2) =
                        Nat.choose (n + 2) (k + 2) * (k + 2) := by
                      ring
                    _ = (n + 2) * Nat.choose (n + 1) (k + 1) :=
                      (Nat.add_one_mul_choose_eq (n + 1) (k + 1)).symm
                have hsecond :
                    (k + 1) * Nat.choose (n + 1) (k + 1) =
                      (n + 1) * Nat.choose n k := by
                  calc
                    (k + 1) * Nat.choose (n + 1) (k + 1) =
                        Nat.choose (n + 1) (k + 1) * (k + 1) := by
                      ring
                    _ = (n + 1) * Nat.choose n k :=
                      (Nat.add_one_mul_choose_eq n k).symm
                calc
                  (k + 2) * (k + 1) *
                      Nat.choose (n + 2) (k + 2) =
                      (k + 1) *
                        ((k + 2) * Nat.choose (n + 2) (k + 2)) := by
                    ring
                  _ = (k + 1) *
                        ((n + 2) * Nat.choose (n + 1) (k + 1)) := by
                    rw [hfirst]
                  _ = (n + 2) *
                        ((k + 1) * Nat.choose (n + 1) (k + 1)) := by
                    ring
                  _ = (n + 2) *
                        ((n + 1) * Nat.choose n k) := by
                    rw [hsecond]
                  _ = (n + 2) * (n + 1) * Nat.choose n k := by
                    ring
              have hchooseReal :
                  ((k : ℝ) + 1 + 1) * ((k : ℝ) + 1) *
                      (Nat.choose (n + 1 + 1) (k + 1 + 1) : ℝ) =
                    ((n : ℝ) + 1 + 1) * ((n : ℝ) + 1) *
                      (Nat.choose n k : ℝ) := by
                exact_mod_cast hchoose k
              have hsub : n + 1 + 1 - (k + 1 + 1) = n - k := by
                omega
              rw [hsub, pow_succ, pow_succ]
              rw [hchooseReal]
              ring
            _ =
                ((n : ℝ) + 1 + 1) * ((n : ℝ) + 1) * b ^ 2 *
                  (∑ k ∈ Finset.range (n + 1),
                    (Nat.choose n k : ℝ) *
                      (a ^ (n - k) * b ^ k)) := by
              rw [Finset.mul_sum]
            _ =
                ((n : ℝ) + 1 + 1) * ((n : ℝ) + 1) * b ^ 2 *
                  (a + b) ^ n := by
              congr 1
              simpa [
                add_comm,
                mul_comm,
                mul_left_comm,
                mul_assoc
              ] using
                (add_pow b a n).symm
            _ =
                ((n : ℝ) + 1 + 1) * ((n : ℝ) + 1) * b ^ 2 *
                  (a + b) ^ (n + 1 + 1 - 2) := by
              have hsub : n + 1 + 1 - 2 = n := by
                omega
              rw [hsub]

/-- **FR.** Second moment factoriel brut du nombre de résultats égaux à
`1`, c'est-à-dire la moyenne pondérée de `k(k-1)`.

**EN.** Raw second factorial moment of the number of outcomes equal to
`1`, namely the weighted mean of `k(k-1)`. -/
def frequencyCountSecondFactorialMoment
    (R : ℕ) (α β : ℂ) : ℝ :=
  ∑ k : Fin (R + 1),
    ((k.val * (k.val - 1) : ℕ) : ℝ) *
      frequencyMass R α β k

/-- **FR.** Le second moment factoriel est non négatif.

**EN.** The second factorial moment is nonnegative. -/
theorem frequencyCountSecondFactorialMoment_nonneg
    (R : ℕ) (α β : ℂ) :
    0 ≤ frequencyCountSecondFactorialMoment R α β := by
  unfold frequencyCountSecondFactorialMoment
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg
      (Nat.cast_nonneg
        (k.val * (k.val - 1)))
      (frequencyMass_nonneg R α β k)

/-- **FR.** Sans hypothèse de normalisation élémentaire, le second moment
factoriel vaut

`R (R-1) ‖β‖⁴ (‖α‖² + ‖β‖²)^(R-2)`.

**EN.** Without the elementary normalization hypothesis, the second
factorial moment is

`R (R-1) ‖β‖⁴ (‖α‖² + ‖β‖²)^(R-2)`. -/
theorem frequencyCountSecondFactorialMoment_eq_general
    (R : ℕ) (α β : ℂ) :
    frequencyCountSecondFactorialMoment R α β =
      (R : ℝ) * ((R - 1 : ℕ) : ℝ) *
        (‖β‖ ^ 2) ^ 2 *
        (‖α‖ ^ 2 + ‖β‖ ^ 2) ^ (R - 2) := by
  classical
  let f : ℕ → ℝ := fun k =>
    if hk : k < R + 1 then
      ((k * (k - 1) : ℕ) : ℝ) * frequencyMass R α β ⟨k, hk⟩
    else 0
  have hfin :
      frequencyCountSecondFactorialMoment R α β =
        ∑ k : Fin (R + 1), f k := by
    unfold frequencyCountSecondFactorialMoment
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [f]
    rw [dif_pos k.isLt]
  have hsum :
      (∑ k ∈ Finset.range (R + 1), f k) =
        ∑ k ∈ Finset.range (R + 1),
          ((k * (k - 1) : ℕ) : ℝ) *
            (Nat.choose R k : ℝ) *
            ((‖α‖ ^ 2) ^ (R - k) *
              (‖β‖ ^ 2) ^ k) := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [f]
    rw [dif_pos (Finset.mem_range.mp hk)]
    rw [frequencyMass_eq_binomial]
    ring
  calc
    frequencyCountSecondFactorialMoment R α β =
        ∑ k : Fin (R + 1), f k := hfin
    _ = ∑ k ∈ Finset.range (R + 1), f k :=
      Fin.sum_univ_eq_sum_range f (R + 1)
    _ = ∑ k ∈ Finset.range (R + 1),
          ((k * (k - 1) : ℕ) : ℝ) *
            (Nat.choose R k : ℝ) *
            ((‖α‖ ^ 2) ^ (R - k) *
              (‖β‖ ^ 2) ^ k) := hsum
    _ = (R : ℝ) * ((R - 1 : ℕ) : ℝ) *
          (‖β‖ ^ 2) ^ 2 *
          (‖α‖ ^ 2 + ‖β‖ ^ 2) ^ (R - 2) :=
      sum_range_cast_fallingTwo_mul_choose_mul_powers
        R (‖α‖ ^ 2) (‖β‖ ^ 2)

/-- **FR.** Sous l'hypothèse de normalisation élémentaire, le second
moment factoriel vaut exactement

`R (R-1) ‖β‖⁴`.

**EN.** Under the elementary normalization hypothesis, the second
factorial moment is exactly

`R (R-1) ‖β‖⁴`. -/
theorem frequencyCountSecondFactorialMoment_eq
    (R : ℕ) (α β : ℂ)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    frequencyCountSecondFactorialMoment R α β =
      (R : ℝ) * ((R - 1 : ℕ) : ℝ) *
        (‖β‖ ^ 2) ^ 2 := by
  rw [
    frequencyCountSecondFactorialMoment_eq_general,
    hnorm,
    one_pow,
    mul_one
  ]

/-- **FR.** Second moment brut du nombre de résultats égaux à `1`,
c'est-à-dire la moyenne pondérée de `k²`.

**EN.** Raw second moment of the number of outcomes equal to `1`, namely
the weighted mean of `k²`. -/
def frequencyCountSecondMoment
    (R : ℕ) (α β : ℂ) : ℝ :=
  ∑ k : Fin (R + 1),
    ((k.val ^ 2 : ℕ) : ℝ) *
      frequencyMass R α β k

/-- **FR.** Le second moment brut est la somme du second moment
factoriel et du premier moment, par l'identité naturelle
`k² = k(k-1) + k`.

**EN.** The raw second moment is the sum of the second factorial moment
and the first moment, by the natural-number identity
`k² = k(k-1) + k`. -/
theorem frequencyCountSecondMoment_eq_secondFactorialMoment_add_firstMoment
    (R : ℕ) (α β : ℂ) :
    frequencyCountSecondMoment R α β =
      frequencyCountSecondFactorialMoment R α β +
        frequencyCountFirstMoment R α β := by
  unfold frequencyCountSecondMoment
  unfold frequencyCountSecondFactorialMoment
  unfold frequencyCountFirstMoment
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hnat (m : ℕ) : m ^ 2 = m * (m - 1) + m := by
    cases m with
    | zero =>
        norm_num
    | succ m =>
        simp [pow_two]
        ring
  rw [hnat k.val, Nat.cast_add]
  ring

/-- **FR.** Le second moment brut est non négatif.

**EN.** The raw second moment is nonnegative. -/
theorem frequencyCountSecondMoment_nonneg
    (R : ℕ) (α β : ℂ) :
    0 ≤ frequencyCountSecondMoment R α β := by
  unfold frequencyCountSecondMoment
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg
      (Nat.cast_nonneg (k.val ^ 2))
      (frequencyMass_nonneg R α β k)

/-- **FR.** Sans hypothèse de normalisation élémentaire, le second
moment brut est la somme des formules générales du moment factoriel
d'ordre deux et du premier moment.

**EN.** Without the elementary normalization hypothesis, the raw second
moment is the sum of the general formulas for the second factorial
moment and the first moment. -/
theorem frequencyCountSecondMoment_eq_general
    (R : ℕ) (α β : ℂ) :
    frequencyCountSecondMoment R α β =
      (R : ℝ) * ((R - 1 : ℕ) : ℝ) *
          (‖β‖ ^ 2) ^ 2 *
          (‖α‖ ^ 2 + ‖β‖ ^ 2) ^ (R - 2) +
        (R : ℝ) * (‖β‖ ^ 2) *
          (‖α‖ ^ 2 + ‖β‖ ^ 2) ^ (R - 1) := by
  rw [
    frequencyCountSecondMoment_eq_secondFactorialMoment_add_firstMoment,
    frequencyCountSecondFactorialMoment_eq_general,
    frequencyCountFirstMoment_eq_general
  ]

/-- **FR.** Sous normalisation élémentaire, le second moment brut vaut

`R(R-1) ‖β‖⁴ + R ‖β‖²`.

**EN.** Under elementary normalization, the raw second moment is

`R(R-1) ‖β‖⁴ + R ‖β‖²`. -/
theorem frequencyCountSecondMoment_eq
    (R : ℕ) (α β : ℂ)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    frequencyCountSecondMoment R α β =
      (R : ℝ) * ((R - 1 : ℕ) : ℝ) *
          (‖β‖ ^ 2) ^ 2 +
        (R : ℝ) * (‖β‖ ^ 2) := by
  rw [
    frequencyCountSecondMoment_eq_secondFactorialMoment_add_firstMoment,
    frequencyCountSecondFactorialMoment_eq R α β hnorm,
    frequencyCountFirstMoment_eq R α β hnorm
  ]

/-- **FR.** Expression algébrique de la variance du nombre de résultats
égaux à `1`.

Cette quantité possède son interprétation probabiliste lorsque
`frequencyMass` est normalisée.

**EN.** Algebraic expression for the variance of the number of outcomes
equal to `1`.

This quantity has its probabilistic interpretation when `frequencyMass`
is normalized. -/
def frequencyCountVariance
    (R : ℕ) (α β : ℂ) : ℝ :=
  frequencyCountSecondMoment R α β -
    (frequencyCountFirstMoment R α β) ^ 2

/-- **FR.** Sous normalisation élémentaire, la variance du nombre de
résultats égaux à `1` est exactement

`R ‖β‖² (1 - ‖β‖²)`.

**EN.** Under elementary normalization, the variance of the number of
outcomes equal to `1` is exactly

`R ‖β‖² (1 - ‖β‖²)`. -/
theorem frequencyCountVariance_eq
    (R : ℕ) (α β : ℂ)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    frequencyCountVariance R α β =
      (R : ℝ) * (‖β‖ ^ 2) *
        (1 - ‖β‖ ^ 2) := by
  unfold frequencyCountVariance
  rw [
    frequencyCountSecondMoment_eq R α β hnorm,
    frequencyCountFirstMoment_eq R α β hnorm
  ]
  cases R with
  | zero =>
      simp
  | succ n =>
      simp only [
        Nat.add_sub_cancel,
        Nat.cast_add
      ]
      ring

/-- **FR.** Sous normalisation élémentaire, la variance est non négative.

**EN.** Under elementary normalization, the variance is nonnegative. -/
theorem frequencyCountVariance_nonneg
    (R : ℕ) (α β : ℂ)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    0 ≤ frequencyCountVariance R α β := by
  rw [frequencyCountVariance_eq R α β hnorm]
  have hp0 : 0 ≤ ‖β‖ ^ 2 :=
    sq_nonneg ‖β‖
  have ha0 : 0 ≤ ‖α‖ ^ 2 :=
    sq_nonneg ‖α‖
  have hp1 : ‖β‖ ^ 2 ≤ 1 := by
    nlinarith [hnorm]
  exact
    mul_nonneg
      (mul_nonneg
        (Nat.cast_nonneg R)
        hp0)
      (sub_nonneg.mpr hp1)

/-- **FR.** Fréquence relative des résultats égaux à `1` dans la cellule
d'indice `k`.

Pour `R = 0`, cette expression utilise la convention de division de
`ℝ`, donc vaut `0`. Les résultats probabilistes ultérieurs supposent
explicitement `0 < R`.

**EN.** Relative frequency of outcomes equal to `1` in the cell indexed
by `k`.

For `R = 0`, this expression uses the division convention of `ℝ` and
therefore equals `0`. Later probabilistic results explicitly assume
`0 < R`. -/
def frequencyRelativeValue
    (R : ℕ) (k : Fin (R + 1)) : ℝ :=
  (k.val : ℝ) / (R : ℝ)

/-- **FR.** Premier moment pondéré de la fréquence relative.

**EN.** Weighted first moment of the relative frequency. -/
def frequencyRelativeFirstMoment
    (R : ℕ) (α β : ℂ) : ℝ :=
  ∑ k : Fin (R + 1),
    frequencyRelativeValue R k *
      frequencyMass R α β k

/-- **FR.** Le premier moment de la fréquence relative est le premier
moment du compte divisé par `R`.

L'identité algébrique est valable avec la convention de division de
`ℝ`, y compris pour `R = 0`.

**EN.** The first moment of the relative frequency is the first moment
of the count divided by `R`.

The algebraic identity is valid with the division convention of `ℝ`,
including when `R = 0`. -/
theorem frequencyRelativeFirstMoment_eq_countFirstMoment_div
    (R : ℕ) (α β : ℂ) :
    frequencyRelativeFirstMoment R α β =
      frequencyCountFirstMoment R α β / (R : ℝ) := by
  unfold frequencyRelativeFirstMoment
  unfold frequencyRelativeValue
  unfold frequencyCountFirstMoment
  calc
    (∑ k : Fin (R + 1),
        ((k.val : ℝ) / (R : ℝ)) *
          frequencyMass R α β k) =
        ∑ k : Fin (R + 1),
          ((k.val : ℝ) *
            frequencyMass R α β k) / (R : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ =
        (∑ k : Fin (R + 1),
          (k.val : ℝ) *
            frequencyMass R α β k) / (R : ℝ) := by
      rw [Finset.sum_div]

/-- **FR.** Sous normalisation élémentaire et pour `R > 0`, la fréquence
relative moyenne des résultats `1` vaut exactement `‖β‖²`.

**EN.** Under elementary normalization and for `R > 0`, the mean relative
frequency of outcomes `1` is exactly `‖β‖²`. -/
theorem frequencyRelativeFirstMoment_eq
    (R : ℕ) (α β : ℂ)
    (hR : 0 < R)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    frequencyRelativeFirstMoment R α β =
      ‖β‖ ^ 2 := by
  have hR0 : (R : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hR)
  rw [
    frequencyRelativeFirstMoment_eq_countFirstMoment_div,
    frequencyCountFirstMoment_eq R α β hnorm
  ]
  field_simp [hR0]

/-- **FR.** Second moment pondéré de la fréquence relative.

**EN.** Weighted second moment of the relative frequency. -/
def frequencyRelativeSecondMoment
    (R : ℕ) (α β : ℂ) : ℝ :=
  ∑ k : Fin (R + 1),
    (frequencyRelativeValue R k) ^ 2 *
      frequencyMass R α β k

/-- **FR.** Le second moment de la fréquence relative est le second
moment du compte divisé par `R²`.

**EN.** The second moment of the relative frequency is the second moment
of the count divided by `R²`. -/
theorem frequencyRelativeSecondMoment_eq_countSecondMoment_div_sq
    (R : ℕ) (α β : ℂ) :
    frequencyRelativeSecondMoment R α β =
      frequencyCountSecondMoment R α β /
        (R : ℝ) ^ 2 := by
  unfold frequencyRelativeSecondMoment
  unfold frequencyRelativeValue
  unfold frequencyCountSecondMoment
  calc
    (∑ k : Fin (R + 1),
        (((k.val : ℝ) / (R : ℝ)) ^ 2) *
          frequencyMass R α β k) =
        ∑ k : Fin (R + 1),
          (((k.val ^ 2 : ℕ) : ℝ) *
            frequencyMass R α β k) /
              (R : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Nat.cast_pow]
      ring
    _ =
        (∑ k : Fin (R + 1),
          ((k.val ^ 2 : ℕ) : ℝ) *
            frequencyMass R α β k) /
              (R : ℝ) ^ 2 := by
      rw [Finset.sum_div]

/-- **FR.** Variance algébrique de la fréquence relative.

Cette quantité possède son interprétation probabiliste lorsque la famille
`frequencyMass` est normalisée.

**EN.** Algebraic variance of the relative frequency.

This quantity has its probabilistic interpretation when the
`frequencyMass` family is normalized. -/
def frequencyRelativeVariance
    (R : ℕ) (α β : ℂ) : ℝ :=
  frequencyRelativeSecondMoment R α β -
    (frequencyRelativeFirstMoment R α β) ^ 2

/-- **FR.** Pour `R > 0`, la variance de la fréquence relative est la
variance du compte divisée par `R²`.

**EN.** For `R > 0`, the variance of the relative frequency is the count
variance divided by `R²`. -/
theorem frequencyRelativeVariance_eq_countVariance_div_sq
    (R : ℕ) (α β : ℂ)
    (hR : 0 < R) :
    frequencyRelativeVariance R α β =
      frequencyCountVariance R α β /
        (R : ℝ) ^ 2 := by
  have hR0 : (R : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hR)
  unfold frequencyRelativeVariance
  unfold frequencyCountVariance
  rw [
    frequencyRelativeSecondMoment_eq_countSecondMoment_div_sq,
    frequencyRelativeFirstMoment_eq_countFirstMoment_div
  ]
  field_simp [hR0]

/-- **FR.** Sous normalisation élémentaire et pour `R > 0`, la variance
de la fréquence relative est exactement

`‖β‖² (1 - ‖β‖²) / R`.

**EN.** Under elementary normalization and for `R > 0`, the variance of
the relative frequency is exactly

`‖β‖² (1 - ‖β‖²) / R`. -/
theorem frequencyRelativeVariance_eq
    (R : ℕ) (α β : ℂ)
    (hR : 0 < R)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    frequencyRelativeVariance R α β =
      (‖β‖ ^ 2) * (1 - ‖β‖ ^ 2) /
        (R : ℝ) := by
  have hR0 : (R : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hR)
  rw [
    frequencyRelativeVariance_eq_countVariance_div_sq
      R α β hR,
    frequencyCountVariance_eq R α β hnorm
  ]
  field_simp [hR0]

/-- **FR.** Sous les mêmes hypothèses, la variance de la fréquence
relative est non négative.

**EN.** Under the same hypotheses, the relative-frequency variance is
nonnegative. -/
theorem frequencyRelativeVariance_nonneg
    (R : ℕ) (α β : ℂ)
    (hR : 0 < R)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    0 ≤ frequencyRelativeVariance R α β := by
  rw [
    frequencyRelativeVariance_eq
      R α β hR hnorm
  ]
  have hp0 : 0 ≤ ‖β‖ ^ 2 :=
    sq_nonneg ‖β‖
  have ha0 : 0 ≤ ‖α‖ ^ 2 :=
    sq_nonneg ‖α‖
  have hp1 : ‖β‖ ^ 2 ≤ 1 := by
    nlinarith [hnorm]
  have hRnonneg : 0 ≤ (R : ℝ) := by
    positivity
  exact
    div_nonneg
      (mul_nonneg hp0 (sub_nonneg.mpr hp1))
      hRnonneg

end
end EverettianProbability.Frequency
