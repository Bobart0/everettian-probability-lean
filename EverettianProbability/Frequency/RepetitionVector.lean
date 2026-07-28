import EverettianProbability.Frequency.HammingCounting
import Mathlib.Data.Nat.Choose.Sum

/-!
**FR.** # Vecteur d'amplitudes de répétition — noyau P10

Pour deux amplitudes complexes `α` et `β`, l'amplitude d'une configuration
binaire de `R` sites est définie par

`α ^ (R - k) * β ^ k`,

où `k` est son poids de Hamming. Le vecteur obtenu est d'abord défini dans
la représentation par sites, puis transporté vers `H (2 ^ R)`.

Ce module définit le vecteur de répétition, factorise ses poids de
configuration, prouve la décomposition binomiale de sa norme et sa
normalisation lorsque `‖α‖² + ‖β‖² = 1`. Les poids projectifs des cellules,
la concentration et la typicalité restent ouverts. Aucune factorisation
tensorielle explicite ni notion autonome d'indépendance probabiliste n'est
introduite.

**EN.** # Repetition-amplitude vector — P10 kernel

For two complex amplitudes `α` and `β`, the amplitude of a binary
configuration on `R` sites is defined as

`α ^ (R - k) * β ^ k`,

where `k` is its Hamming weight. The resulting vector is first defined in
the site representation and then transported to `H (2 ^ R)`.

This module defines the repetition vector, factors its configuration weights,
proves the binomial decomposition of its norm, and proves normalization when
`‖α‖² + ‖β‖² = 1`. Projective cell weights, concentration, and typicality
remain open. No explicit tensor factorization or autonomous notion of
probabilistic independence is introduced.
-/

namespace EverettianProbability.Frequency

open QuantumFoundations.ProbabilityAPI
open QuantumFoundations.ProbabilityAPI.Repetition
open scoped Classical InnerProductSpace

noncomputable section

/-- **FR.** Amplitude associée à une configuration de `R` répétitions :
`α` pour chaque zéro et `β` pour chaque un.

**EN.** Amplitude associated with a configuration of `R` repetitions:
`α` for each zero and `β` for each one. -/
def repetitionAmplitude
    (R : ℕ) (α β : ℂ) (g : Fin R → Fin 2) : ℂ :=
  α ^ (R - hammingWeight g) * β ^ hammingWeight g

/-- **FR.** Vecteur d'amplitudes dans la représentation par sites.

**EN.** Amplitude vector in the site representation. -/
def repetitionSitesVector
    (R : ℕ) (α β : ℂ) : Sites R 2 :=
  (WithLp.equiv 2 ((Fin R → Fin 2) → ℂ)).symm
    (fun g => repetitionAmplitude R α β g)

/-- **FR.** Transport du vecteur de répétition vers l'espace standard
`H (2 ^ R)`.

**EN.** Transport of the repetition vector to the standard space
`H (2 ^ R)`. -/
def repetitionVector
    (R : ℕ) (α β : ℂ) : H (2 ^ R) :=
  (sitesEquivR R).symm (repetitionSitesVector R α β)

/-- **FR.** Formule de coordonnée du vecteur dans la représentation par
sites.

**EN.** Coordinate formula for the vector in the site representation. -/
@[simp] theorem repetitionSitesVector_apply
    (R : ℕ) (α β : ℂ) (g : Fin R → Fin 2) :
    repetitionSitesVector R α β g =
      repetitionAmplitude R α β g := by
  simp [repetitionSitesVector]

/-- **FR.** Le transport inverse restitue exactement le vecteur défini par
ses amplitudes sur les configurations.

**EN.** Transporting back recovers exactly the vector defined by its
configuration amplitudes. -/
@[simp] theorem sitesEquivR_repetitionVector
    (R : ℕ) (α β : ℂ) :
    sitesEquivR R (repetitionVector R α β) =
      repetitionSitesVector R α β := by
  simp [repetitionVector]

/-- **FR.** Deux configurations de même poids de Hamming reçoivent la même
amplitude.

**EN.** Two configurations with the same Hamming weight receive the same
amplitude. -/
theorem repetitionAmplitude_eq_of_hammingWeight_eq
    {R : ℕ} {α β : ℂ} {g h : Fin R → Fin 2}
    (hweight : hammingWeight g = hammingWeight h) :
    repetitionAmplitude R α β g =
      repetitionAmplitude R α β h := by
  simp [repetitionAmplitude, hweight]

/-- **FR.** Le vecteur par sites est constant sur chaque classe de
configurations de même poids de Hamming.

**EN.** The site vector is constant on every class of configurations with
the same Hamming weight. -/
theorem repetitionSitesVector_eq_of_hammingWeight_eq
    {R : ℕ} {α β : ℂ} {g h : Fin R → Fin 2}
    (hweight : hammingWeight g = hammingWeight h) :
    repetitionSitesVector R α β g =
      repetitionSitesVector R α β h := by
  simp only [repetitionSitesVector_apply]
  exact repetitionAmplitude_eq_of_hammingWeight_eq hweight

/-- **FR.** Sur la configuration canonique de poids `k`, l'amplitude vaut
exactement `α ^ (R - k) * β ^ k`.

**EN.** On the canonical configuration of weight `k`, the amplitude is
exactly `α ^ (R - k) * β ^ k`. -/
theorem repetitionAmplitude_prefixConfiguration
    (R : ℕ) (k : Fin (R + 1)) (α β : ℂ) :
    repetitionAmplitude R α β
        (prefixConfiguration R k) =
      α ^ (R - k.val) * β ^ k.val := by
  simp [repetitionAmplitude,
    hammingWeight_prefixConfiguration]

/-- **FR.** Poids scalaire d'une configuration : carré de la norme de son
amplitude complexe.

**EN.** Scalar weight of a configuration: the squared norm of its complex
amplitude. -/
def repetitionConfigurationWeight
    (R : ℕ) (α β : ℂ) (g : Fin R → Fin 2) : ℝ :=
  ‖repetitionAmplitude R α β g‖ ^ 2

/-- **FR.** Le poids d'une configuration est non négatif.

**EN.** A configuration weight is nonnegative. -/
theorem repetitionConfigurationWeight_nonneg
    (R : ℕ) (α β : ℂ) (g : Fin R → Fin 2) :
    0 ≤ repetitionConfigurationWeight R α β g := by
  unfold repetitionConfigurationWeight
  positivity

/-- **FR.** Deux configurations de même poids de Hamming reçoivent le même
poids scalaire.

**EN.** Two configurations with the same Hamming weight receive the same
scalar weight. -/
theorem repetitionConfigurationWeight_eq_of_hammingWeight_eq
    {R : ℕ} {α β : ℂ} {g h : Fin R → Fin 2}
    (hweight : hammingWeight g = hammingWeight h) :
    repetitionConfigurationWeight R α β g =
      repetitionConfigurationWeight R α β h := by
  unfold repetitionConfigurationWeight
  rw [repetitionAmplitude_eq_of_hammingWeight_eq hweight]

/-- **FR.** Sur la configuration canonique de poids `k`, le poids scalaire
est le carré de la norme de `α^(R-k) β^k`.

**EN.** On the canonical configuration of weight `k`, the scalar weight is
the squared norm of `α^(R-k) β^k`. -/
theorem repetitionConfigurationWeight_prefixConfiguration
    (R : ℕ) (k : Fin (R + 1)) (α β : ℂ) :
    repetitionConfigurationWeight R α β
        (prefixConfiguration R k) =
      ‖α ^ (R - k.val) * β ^ k.val‖ ^ 2 := by
  unfold repetitionConfigurationWeight
  rw [repetitionAmplitude_prefixConfiguration]

/-- **FR.** Le carré de la norme du vecteur de répétition est la somme des
poids de toutes les configurations.

**EN.** The squared norm of the repetition vector is the sum of the weights
of all configurations. -/
theorem repetitionVector_norm_sq_eq_sum
    (R : ℕ) (α β : ℂ) :
    ‖repetitionVector R α β‖ ^ 2 =
      ∑ g : Fin R → Fin 2,
        repetitionConfigurationWeight R α β g := by
  simpa [
    repetitionVector,
    repetitionConfigurationWeight,
    repetitionSitesVector_apply
  ] using
    (EuclideanSpace.norm_sq_eq
      (repetitionSitesVector R α β))

/-- **FR.** Le poids d'une configuration se factorise en puissances des
poids élémentaires `‖α‖²` et `‖β‖²`.

**EN.** A configuration weight factors into powers of the elementary
weights `‖α‖²` and `‖β‖²`. -/
theorem repetitionConfigurationWeight_eq_norm_sq_powers
    (R : ℕ) (α β : ℂ) (g : Fin R → Fin 2) :
    repetitionConfigurationWeight R α β g =
      (‖α‖ ^ 2) ^ (R - hammingWeight g) *
        (‖β‖ ^ 2) ^ hammingWeight g := by
  unfold repetitionConfigurationWeight repetitionAmplitude
  rw [norm_mul, norm_pow, norm_pow]
  simp only [pow_two, mul_pow]
  ring

/-- **FR.** Pour la configuration canonique de poids `k`, le poids vaut
`(‖α‖²)^(R-k) (‖β‖²)^k`.

**EN.** For the canonical configuration of weight `k`, the weight is
`(‖α‖²)^(R-k) (‖β‖²)^k`. -/
theorem repetitionConfigurationWeight_prefix_eq_norm_sq_powers
    (R : ℕ) (k : Fin (R + 1)) (α β : ℂ) :
    repetitionConfigurationWeight R α β
        (prefixConfiguration R k) =
      (‖α‖ ^ 2) ^ (R - k.val) *
        (‖β‖ ^ 2) ^ k.val := by
  rw [
    repetitionConfigurationWeight_eq_norm_sq_powers,
    hammingWeight_prefixConfiguration
  ]

/-- **FR.** Le carré de la norme du vecteur est la somme, sur toutes les
configurations, des produits de puissances des poids élémentaires.

**EN.** The squared norm of the vector is the sum, over all configurations,
of the products of powers of the elementary weights. -/
theorem repetitionVector_norm_sq_eq_sum_norm_sq_powers
    (R : ℕ) (α β : ℂ) :
    ‖repetitionVector R α β‖ ^ 2 =
      ∑ g : Fin R → Fin 2,
        (‖α‖ ^ 2) ^ (R - hammingWeight g) *
          (‖β‖ ^ 2) ^ hammingWeight g := by
  rw [repetitionVector_norm_sq_eq_sum]
  apply Finset.sum_congr rfl
  intro g hg
  exact
    repetitionConfigurationWeight_eq_norm_sq_powers
      R α β g

/-- **FR.** Le carré de la norme du vecteur de répétition possède la
décomposition binomiale exacte obtenue en regroupant les configurations
selon leur poids de Hamming.

Ce résultat est une identité algébrique et combinatoire finie. Il ne suppose
pas encore `‖α‖² + ‖β‖² = 1` et n'énonce donc pas encore la normalisation.

**EN.** The squared norm of the repetition vector has the exact binomial
decomposition obtained by grouping configurations according to their
Hamming weight.

This is a finite algebraic and combinatorial identity. It does not yet
assume `‖α‖² + ‖β‖² = 1` and therefore does not yet state normalization. -/
theorem repetitionVector_norm_sq_eq_binomial_sum
    (R : ℕ) (α β : ℂ) :
    ‖repetitionVector R α β‖ ^ 2 =
      ∑ k ∈ Finset.range (R + 1),
        (Nat.choose R k : ℝ) *
          ((‖α‖ ^ 2) ^ (R - k) *
            (‖β‖ ^ 2) ^ k) := by
  rw [repetitionVector_norm_sq_eq_sum_norm_sq_powers]
  let f : ℕ → ℝ :=
    fun k =>
      (‖α‖ ^ 2) ^ (R - k) *
        (‖β‖ ^ 2) ^ k
  change
    (∑ g : Fin R → Fin 2,
      f (hammingWeight g)) =
      ∑ k ∈ Finset.range (R + 1),
        (Nat.choose R k : ℝ) * f k
  have hcomp :
      (∑ g : Fin R → Fin 2,
        f (hammingWeight g)) =
        ∑ k ∈ Finset.range (R + 1),
          (configurationsOfWeight R k).card •
            f k := by
    have h :=
      Finset.sum_comp
        (s :=
          (Finset.univ :
            Finset (Fin R → Fin 2)))
        f
        (fun g : Fin R → Fin 2 =>
          hammingWeight g)
    rw [hammingWeight_image_univ R] at h
    simpa [configurationsOfWeight] using h
  calc
    (∑ g : Fin R → Fin 2,
      f (hammingWeight g)) =
        ∑ k ∈ Finset.range (R + 1),
          (configurationsOfWeight R k).card •
            f k :=
      hcomp
    _ =
        ∑ k ∈ Finset.range (R + 1),
          (Nat.choose R k : ℝ) * f k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [configurationsOfWeight_card]
      simp [nsmul_eq_mul]

/-- **FR.** Le carré de la norme du vecteur de répétition est la puissance
`R` de la somme des deux poids élémentaires.

**EN.** The squared norm of the repetition vector is the `R`-th power of
the sum of the two elementary weights. -/
theorem repetitionVector_norm_sq_eq_elementary_sum_pow
    (R : ℕ) (α β : ℂ) :
    ‖repetitionVector R α β‖ ^ 2 =
      (‖α‖ ^ 2 + ‖β‖ ^ 2) ^ R := by
  rw [repetitionVector_norm_sq_eq_binomial_sum]
  calc
    ∑ k ∈ Finset.range (R + 1),
        (Nat.choose R k : ℝ) *
          ((‖α‖ ^ 2) ^ (R - k) *
            (‖β‖ ^ 2) ^ k) =
        ∑ k ∈ Finset.range (R + 1),
          (Nat.choose R k : ℝ) *
            ((‖β‖ ^ 2) ^ k *
              (‖α‖ ^ 2) ^ (R - k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ k ∈ Finset.range (R + 1),
          ((‖β‖ ^ 2) ^ k *
            (‖α‖ ^ 2) ^ (R - k)) *
            (Nat.choose R k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (‖α‖ ^ 2 + ‖β‖ ^ 2) ^ R := by
      calc
        ∑ k ∈ Finset.range (R + 1),
            ((‖β‖ ^ 2) ^ k *
              (‖α‖ ^ 2) ^ (R - k)) *
              (Nat.choose R k : ℝ) =
            (‖β‖ ^ 2 + ‖α‖ ^ 2) ^ R :=
          (add_pow (‖β‖ ^ 2) (‖α‖ ^ 2) R).symm
        _ = (‖α‖ ^ 2 + ‖β‖ ^ 2) ^ R := by
          rw [add_comm]

/-- **FR.** Si les deux poids élémentaires somment à `1`, le carré de la
norme du vecteur de répétition vaut `1`.

**EN.** If the two elementary weights sum to `1`, the squared norm of the
repetition vector is `1`. -/
theorem repetitionVector_norm_sq_eq_one
    (R : ℕ) (α β : ℂ)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    ‖repetitionVector R α β‖ ^ 2 = 1 := by
  rw [
    repetitionVector_norm_sq_eq_elementary_sum_pow,
    hnorm,
    one_pow
  ]

/-- **FR.** Sous la même hypothèse élémentaire, le vecteur de répétition
est normalisé.

**EN.** Under the same elementary hypothesis, the repetition vector is
normalized. -/
theorem repetitionVector_norm_eq_one
    (R : ℕ) (α β : ℂ)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    ‖repetitionVector R α β‖ = 1 := by
  have hsq :=
    repetitionVector_norm_sq_eq_one R α β hnorm
  have hnonneg :
      0 ≤ ‖repetitionVector R α β‖ :=
    norm_nonneg _
  nlinarith

end
end EverettianProbability.Frequency
