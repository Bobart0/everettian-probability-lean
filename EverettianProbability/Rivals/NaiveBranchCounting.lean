import QuantumFoundations.BornRule.Assembly

/-!
**FR.** # Comptage naïf des branches (règle rivale)

La règle rivale la plus simple : chaque cellule d'une perspective reçoit un
poids `1 / |D.cells|`, indépendamment de tout contenu hilbertien. Fiche
complète (justification revendiquée, prémisse violée, statut) dans
`docs/RIVAL_RULES.md`. La violation de `AxGrain` est énoncée comme but ouvert :
c'est un résultat mathématique (bien que court) hors de portée de P1.

**EN.** # Naive branch counting (rival rule)

The simplest rival rule: every cell of a perspective receives weight
`1 / |D.cells|`, independent of any Hilbert-space content. Full entry
(claimed justification, violated premise, status) in
`docs/RIVAL_RULES.md`. The violation of `AxGrain` is stated as an open goal:
this is a mathematical result (albeit a short one) out of scope for P1.
-/

namespace EverettianProbability.Rivals

open QuantumFoundations.BornRule Gleason

/-- Naive branch counting: every cell of a perspective counts equally. -/
noncomputable def naiveCounting (n : ℕ) : Perspective n → Submodule ℂ (H n) → ℝ :=
  fun D _ => 1 / (D.cells.card : ℝ)

/-- Naive counting violates (Grain): refining a perspective changes the
number of cells, hence the uniform weight, in a way incompatible with
additive coherence across the refinement. Witnessed concretely at `n = 3`
via the binary-split / basis-refinement pair already used in
`Core/Nonvacuity.lean`. -/
theorem naiveCounting_violates_grain : ¬ AxGrain (naiveCounting 3) := by
  sorry

end EverettianProbability.Rivals
