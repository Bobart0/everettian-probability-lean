import EverettianProbability.Preference.ExpectationFunctional

/-!
**FR.** # Théorème de représentation

Toute fonctionnelle d'espérance rationnelle, restreinte à une perspective
`D`, se représente de façon unique comme une somme pondérée sur les
cellules de `D` : il existe un unique `p : Submodule ℂ (H n) → ℝ` tel que
`V D a = ∑ c ∈ D.cells, p c * a c` pour tout acte `a`. C'est l'analogue,
côté théorie de la décision, du théorème de représentation de von
Neumann–Morgenstern / Savage : l'affinité et la monotonie de `V` suffisent
à produire des poids, sans qu'aucune interprétation probabiliste ne soit
encore injectée. Énoncé comme but ouvert dans ce jalon P1.

**EN.** # Representation theorem

Every rational expectation functional, restricted to a perspective `D`, is
uniquely represented as a weighted sum over the cells of `D`: there exists
a unique `p : Submodule ℂ (H n) → ℝ` such that
`V D a = ∑ c ∈ D.cells, p c * a c` for every act `a`. This is the
decision-theoretic analogue of the von Neumann–Morgenstern / Savage
representation theorem: the affinity and monotonicity of `V` alone suffice
to produce weights, without any probabilistic interpretation being
injected yet. Stated as an open goal in this P1 milestone.
-/

namespace EverettianProbability.Preference

open QuantumFoundations.BornRule Gleason EverettianProbability.Core

variable {n : ℕ}

/-- Existence and uniqueness of the representing weights of a rational
expectation family, at a fixed perspective `D`. -/
theorem exists_unique_weights (F : RationalExpectationFamily n) (D : Perspective n) :
    ∃! p : Submodule ℂ (H n) → ℝ, ∀ a : Act n, F.V D a = ∑ c ∈ D.cells, p c * a c := by
  sorry

end EverettianProbability.Preference
