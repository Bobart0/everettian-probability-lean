import QuantumFoundations.ProbabilityAPI
import EverettianProbability.Core.Nonvacuity

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
open EverettianProbability.Core
open scoped Classical

private theorem exampleLine_finrank : Module.finrank ℂ exampleLine = 1 := by
  apply finrank_span_singleton
  intro hzero
  have hnorm := (EuclideanSpace.basisFun (Fin 3) ℂ).orthonormal.1 (0 : Fin 3)
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

private theorem exampleLine_ne_orthogonal : exampleLine ≠ exampleLineᗮ := by
  intro h
  have hsum := Submodule.finrank_add_finrank_orthogonal exampleLine
  have hfr := congrArg
    (fun K : Submodule ℂ (H 3) => Module.finrank ℂ K) h
  rw [exampleLine_finrank] at hfr hsum
  simp at hsum
  omega

private theorem cellLines_card (c : Submodule ℂ (H 3)) :
    (cellLines c).card = Module.finrank ℂ c := by
  unfold cellLines
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j hij
    exact cellLines_injective c (by simp) (by simp) hij

/-- **FR.** Le nombre de lignes de la décomposition de base d'une cellule est
sa dimension hilbertienne finie.

**EN.** The number of lines in a cell's basis decomposition is its finite
Hilbert dimension. -/
theorem cellLines_card_eq_finrank (c : Submodule ℂ (H 3)) :
    (cellLines c).card = Module.finrank ℂ c :=
  cellLines_card c

private theorem exampleFine_card : exampleFine.cells.card = 3 := by
  have hdisjoint : ∀ c ∈ exampleCoarse.cells, ∀ d ∈ exampleCoarse.cells,
      c ≠ d → Disjoint (cellLines c) (cellLines d) := by
    intro c hc d hd hcd
    rw [Finset.disjoint_left]
    intro x hxc hxd
    exact (hcd (exampleCoarse.unique_parent hc hd
      (cellLines_ne_bot c x hxc) (cellLines_le c x hxc) (cellLines_le d x hxd))).elim
  have hsum : Module.finrank ℂ exampleLine + Module.finrank ℂ exampleLineᗮ = 3 := by
    rw [Submodule.finrank_add_finrank_orthogonal]
    simp
  rw [exampleLine_finrank] at hsum
  change (exampleCoarse.cells.biUnion cellLines).card = 3
  rw [Finset.card_biUnion hdisjoint]
  change (∑ c ∈ exampleCoarse.cells, (cellLines c).card) = 3
  rw [show exampleCoarse.cells = {exampleLine, exampleLineᗮ} by rfl]
  rw [Finset.sum_insert]
  · simp only [Finset.sum_singleton, cellLines_card, exampleLine_finrank]
    exact hsum
  · simpa only [Finset.mem_singleton] using exampleLine_ne_orthogonal

private theorem exampleCoarse_card : exampleCoarse.cells.card = 2 := by
  change ({exampleLine, exampleLineᗮ} : Finset (Submodule ℂ (H 3))).card = 2
  rw [Finset.card_insert_of_notMem]
  · simp
  · simpa only [Finset.mem_singleton] using exampleLine_ne_orthogonal

/-- **FR.** Cardinal de la perspective binaire explicite, exposé pour les
tests concrets de règles d'espérance sur la même paire de perspectives.

**EN.** Cardinality of the explicit binary perspective, exposed for concrete
tests of expectation rules on the same pair of perspectives. -/
theorem exampleCoarse_cells_card : exampleCoarse.cells.card = 2 :=
  exampleCoarse_card

/-- **FR.** Cardinal de son raffinement explicite en trois lignes, exposé
pour les tests concrets de règles d'espérance.

**EN.** Cardinality of its explicit three-line refinement, exposed for
concrete tests of expectation rules. -/
theorem exampleFine_cells_card : exampleFine.cells.card = 3 :=
  exampleFine_card

/-- Naive branch counting: every cell of a perspective counts equally. -/
noncomputable def naiveCounting (n : ℕ) : Perspective n → Submodule ℂ (H n) → ℝ :=
  fun D _ => 1 / (D.cells.card : ℝ)

/-- Naive counting violates (Grain): refining a perspective changes the
number of cells, hence the uniform weight, in a way incompatible with
additive coherence across the refinement. Witnessed concretely at `n = 3`
via the binary-split / basis-refinement pair already used in
`Core/Nonvacuity.lean`. -/
theorem naiveCounting_violates_grain : ¬ AxGrain (naiveCounting 3) := by
  intro hgrain
  have h := hgrain exampleFine exampleCoarse exampleFine_refines
    exampleLine exampleLine_mem_exampleCoarse
  change 1 / (exampleCoarse.cells.card : ℝ) =
    ∑ c' ∈ exampleFine.cells.filter (· ≤ exampleLine),
      1 / (exampleFine.cells.card : ℝ) at h
  unfold exampleFine at h
  rw [refine_filter_eq_cellLines exampleCoarse exampleLine
    exampleLine_mem_exampleCoarse] at h
  have hfine := exampleFine_card
  unfold exampleFine at hfine
  rw [exampleCoarse_card, hfine] at h
  have hline : (cellLines exampleLine).card = 1 := by
    rw [cellLines_card, exampleLine_finrank]
  rw [Finset.sum_const, hline] at h
  norm_num at h

end EverettianProbability.Rivals
