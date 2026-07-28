import EverettianProbability.Frequency.CellProjection

/-!
**FR.** # Masse finie des cellules de fréquence

Pour un vecteur de répétition, `frequencyMass R α β k` est le poids
projectif de la cellule contenant exactement `k` résultats égaux à `1`.

Le module expose cette famille comme une fonction réelle sur
`Fin (R + 1)`, établit sa formule binomiale, sa positivité et sa
normalisation sous l'hypothèse `‖α‖² + ‖β‖² = 1`.

Il ne construit pas encore une mesure abstraite ou une `PMF`. Il ne
définit pas encore l'espérance, la variance, la concentration ou la
typicalité.

**EN.** # Finite mass of frequency cells

For a repetition vector, `frequencyMass R α β k` is the projective weight
of the cell containing exactly `k` outcomes equal to `1`.

The module exposes this family as a real-valued function on
`Fin (R + 1)` and proves its binomial formula, nonnegativity, and
normalization under the hypothesis `‖α‖² + ‖β‖² = 1`.

It does not yet construct an abstract measure or `PMF`. It does not yet
define expectation, variance, concentration, or typicality.
-/

namespace EverettianProbability.Frequency

open QuantumFoundations.ProbabilityAPI
open scoped Classical InnerProductSpace

noncomputable section

/-- **FR.** Poids projectif de la cellule contenant exactement `k`
résultats égaux à `1`.

**EN.** Projective weight of the cell containing exactly `k` outcomes
equal to `1`. -/
def frequencyMass
    (R : ℕ) (α β : ℂ) (k : Fin (R + 1)) : ℝ :=
  ‖projL (frequencyCell R k.val)
      (repetitionVector R α β)‖ ^ 2

/-- **FR.** `frequencyMass` est exactement le carré de la norme de la
projection sur la cellule correspondante.

**EN.** `frequencyMass` is exactly the squared norm of the projection onto
the corresponding cell. -/
@[simp] theorem frequencyMass_eq_projectiveWeight
    (R : ℕ) (α β : ℂ) (k : Fin (R + 1)) :
    frequencyMass R α β k =
      ‖projL (frequencyCell R k.val)
          (repetitionVector R α β)‖ ^ 2 := by
  rfl

/-- **FR.** Chaque masse de fréquence est non négative.

**EN.** Every frequency mass is nonnegative. -/
theorem frequencyMass_nonneg
    (R : ℕ) (α β : ℂ) (k : Fin (R + 1)) :
    0 ≤ frequencyMass R α β k := by
  unfold frequencyMass
  positivity

/-- **FR.** Formule binomiale exacte de la masse de fréquence.

**EN.** Exact binomial formula for the frequency mass. -/
theorem frequencyMass_eq_binomial
    (R : ℕ) (α β : ℂ) (k : Fin (R + 1)) :
    frequencyMass R α β k =
      (Nat.choose R k.val : ℝ) *
        ((‖α‖ ^ 2) ^ (R - k.val) *
          (‖β‖ ^ 2) ^ k.val) := by
  simpa [frequencyMass] using
    (projL_frequencyCell_repetitionVector_norm_sq_eq_binomial
      R k.val α β)

/-- **FR.** La masse totale est la puissance `R` de la somme des poids
élémentaires.

**EN.** The total mass is the `R`-th power of the sum of the elementary
weights. -/
theorem sum_frequencyMass_eq_elementary_sum_pow
    (R : ℕ) (α β : ℂ) :
    (∑ k : Fin (R + 1), frequencyMass R α β k) =
      (‖α‖ ^ 2 + ‖β‖ ^ 2) ^ R := by
  simpa [frequencyMass] using
    (sum_projL_frequencyCell_repetitionVector_norm_sq_eq_elementary_sum_pow
      R α β)

/-- **FR.** Sous l'hypothèse de normalisation élémentaire, la masse totale
vaut exactement `1`.

**EN.** Under the elementary normalization hypothesis, the total mass is
exactly `1`. -/
theorem sum_frequencyMass_eq_one
    (R : ℕ) (α β : ℂ)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    (∑ k : Fin (R + 1), frequencyMass R α β k) = 1 := by
  simpa [frequencyMass] using
    (sum_projL_frequencyCell_repetitionVector_norm_sq_eq_one
      R α β hnorm)

/-- **FR.** Sous normalisation élémentaire, `frequencyMass` constitue une
famille finie de masses non négatives de somme `1`.

Cet énoncé ne crée pas une nouvelle structure probabiliste ; il regroupe
seulement les deux propriétés nécessaires aux calculs finis ultérieurs.

**EN.** Under elementary normalization, `frequencyMass` is a finite family
of nonnegative masses summing to `1`.

This statement creates no new probability structure; it merely packages
the two properties required by later finite calculations. -/
theorem frequencyMass_isProbabilityFamily
    (R : ℕ) (α β : ℂ)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    (∀ k : Fin (R + 1),
        0 ≤ frequencyMass R α β k) ∧
      (∑ k : Fin (R + 1),
        frequencyMass R α β k) = 1 := by
  constructor
  · intro k
    exact frequencyMass_nonneg R α β k
  · exact sum_frequencyMass_eq_one R α β hnorm

end
end EverettianProbability.Frequency
