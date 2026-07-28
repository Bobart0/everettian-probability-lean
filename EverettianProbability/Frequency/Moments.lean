import EverettianProbability.Frequency.Distribution
import Mathlib.Data.Nat.Choose.Sum

/-!
**FR.** # Premier moment de la distribution des fréquences

Le premier moment du nombre de résultats égaux à `1` est défini par la
somme finie

`∑ k, k · frequencyMass R α β k`.

Le module prouve d'abord l'identité binomiale pondérée générale

`∑ k k C(R,k) a^(R-k) b^k
   = R b (a+b)^(R-1)`,

puis l'applique aux poids projectifs des cellules de fréquence. Sous
l'hypothèse `‖α‖² + ‖β‖² = 1`, le premier moment vaut exactement
`R ‖β‖²`.

Aucune variance, borne de concentration ou typicalité n'est encore
introduite.

**EN.** # First moment of the frequency distribution

The first moment of the number of outcomes equal to `1` is defined by the
finite sum

`∑ k, k · frequencyMass R α β k`.

The module first proves the general weighted binomial identity

`∑ k k C(R,k) a^(R-k) b^k
   = R b (a+b)^(R-1)`,

and then applies it to the projective weights of the frequency cells.
Under the hypothesis `‖α‖² + ‖β‖² = 1`, the first moment is exactly
`R ‖β‖²`.

No variance, concentration bound, or typicality statement is introduced
yet.
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

end
end EverettianProbability.Frequency
