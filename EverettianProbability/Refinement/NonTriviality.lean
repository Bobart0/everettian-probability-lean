import EverettianProbability.Refinement.PayoffPreserving
import EverettianProbability.Preference.Nonvacuity
import EverettianProbability.Core.Nonvacuity
import EverettianProbability.Rivals.NaiveBranchCounting

/-!
**FR.** # Non-trivialité — `Refinement`

Le témoin négatif est le pendant obligatoire de la non-vacuité : la famille
d'espérance uniforme concrète satisfait les axiomes généraux de rationalité,
mais ne satisfait pas la prémisse normative `RefinementInvariantLocal`. Sur la
cellule orthogonale complémentaire de la perspective binaire explicite, elle
attribue `1 / 2` avant raffinement et `2 / 3` après le raffinement en trois
lignes. La prémisse discrimine donc effectivement.

**EN.** # Nontriviality — `Refinement`

The negative witness is the mandatory counterpart of nonvacuity: the concrete
uniform expectation family satisfies the general rationality axioms but does
not satisfy the normative premise `RefinementInvariantLocal`. On the
orthogonal-complement cell of the explicit binary perspective, it assigns
`1 / 2` before refinement and `2 / 3` after the three-line refinement. The
premise therefore genuinely discriminates.
-/

namespace EverettianProbability.Refinement

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Core EverettianProbability.Preference
open EverettianProbability.Rivals
open scoped Classical

private theorem exampleLine_finrank : Module.finrank ℂ exampleLine = 1 := by
  apply finrank_span_singleton
  intro hzero
  have hnorm := (EuclideanSpace.basisFun (Fin 3) ℂ).orthonormal.1 (0 : Fin 3)
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

private theorem exampleLine_orthogonal_finrank :
    Module.finrank ℂ exampleLineᗮ = 2 := by
  have hsum : Module.finrank ℂ exampleLine + Module.finrank ℂ exampleLineᗮ = 3 := by
    rw [Submodule.finrank_add_finrank_orthogonal]
    simp
  rw [exampleLine_finrank] at hsum
  omega

private theorem exampleLine_orthogonal_mem_exampleCoarse :
    exampleLineᗮ ∈ exampleCoarse.cells := by
  simp only [exampleCoarse, Perspective.binary, Finset.mem_insert,
    Finset.mem_singleton, or_true]

private theorem uniformExpectation_coarse_complement :
    uniformExpectationFamily.V exampleCoarse (Act.indicator exampleLineᗮ) = 1 / 2 := by
  change uniformExpectation exampleCoarse (Act.indicator exampleLineᗮ) = 1 / 2
  unfold uniformExpectation
  rw [Finset.sum_eq_single exampleLineᗮ]
  · rw [Act.indicator_self, exampleCoarse_cells_card]
    norm_num
  · intro d hd hdc
    rw [Act.indicator_of_ne hdc]
  · exact fun hnot => (hnot exampleLine_orthogonal_mem_exampleCoarse).elim

private theorem uniformExpectation_fine_pullback_complement :
    uniformExpectationFamily.V exampleFine
      (pullbackAct exampleFine_refines (Act.indicator exampleLineᗮ)) = 2 / 3 := by
  change uniformExpectation exampleFine
    (pullbackAct exampleFine_refines (Act.indicator exampleLineᗮ)) = 2 / 3
  unfold uniformExpectation pullbackAct Act.indicator
  simp only [Function.comp_apply]
  have hsum :
      (∑ c' ∈ exampleFine.cells,
        if parentOf exampleFine_refines c' = exampleLineᗮ then (1 : ℝ) else 0) =
        ∑ c' ∈ exampleFine.cells.filter (· ≤ exampleLineᗮ), (1 : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c' hc'
    by_cases hle : c' ≤ exampleLineᗮ
    · have hp := parentOf_eq_of_le exampleFine_refines hc'
        exampleLine_orthogonal_mem_exampleCoarse hle
      simp only [hle, hp]
    · have hp : parentOf exampleFine_refines c' ≠ exampleLineᗮ := by
        intro heq
        apply hle
        rw [← heq]
        exact parentOf_le exampleFine_refines hc'
      simp only [hle, hp]
  calc
    (∑ c' ∈ exampleFine.cells,
        if parentOf exampleFine_refines c' = exampleLineᗮ then 1 else 0) /
          (exampleFine.cells.card : ℝ) =
        (∑ c' ∈ exampleFine.cells.filter (· ≤ exampleLineᗮ), 1) /
          (exampleFine.cells.card : ℝ) :=
      congrArg (fun x : ℝ => x / (exampleFine.cells.card : ℝ)) hsum
    _ = (∑ c' ∈ cellLines exampleLineᗮ, 1) /
          (exampleFine.cells.card : ℝ) := by
      unfold exampleFine
      rw [refine_filter_eq_cellLines exampleCoarse exampleLineᗮ
        exampleLine_orthogonal_mem_exampleCoarse]
    _ = 2 / 3 := by
      rw [Finset.sum_const, cellLines_card_eq_finrank,
        exampleLine_orthogonal_finrank, exampleFine_cells_card]
      norm_num

/-- **FR.** `PREMISE` de non-trivialité : la famille uniforme rationnelle ne
satisfait pas l'invariance locale sous raffinement. Le calcul concret est
`1 / 2 ≠ 2 / 3`.

**EN.** Nontriviality witness for the `PREMISE`: the rational uniform family
does not satisfy local refinement invariance. The concrete calculation is
`1 / 2 ≠ 2 / 3`. -/
theorem uniform_not_refinementInvariantLocal :
    ¬ RefinementInvariantLocal uniformExpectationFamily.V := by
  intro hinv
  have h := hinv exampleFine_refines
    (pullbackAct exampleFine_refines (Act.indicator exampleLineᗮ))
    (Act.indicator exampleLineᗮ)
    (Act.agreeOn_refl exampleFine
      (pullbackAct exampleFine_refines (Act.indicator exampleLineᗮ)))
  rw [uniformExpectation_fine_pullback_complement,
    uniformExpectation_coarse_complement] at h
  norm_num at h

end EverettianProbability.Refinement
