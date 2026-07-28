import EverettianProbability.SelfLocation.UniformCredenceRival
import EverettianProbability.Refinement.NonTriviality

/-!
**FR.** # Échec du concurrent uniforme sous raffinement

Ce module applique la famille uniforme de crédences à un raffinement projectif
concret. La perspective grossière explicite possède deux cellules, tandis que
son raffinement en possède trois : une ligne est conservée et sa cellule
orthogonale complémentaire est décomposée en deux lignes.

La crédence uniforme attribue donc `1/2` à la cellule complémentaire avant
raffinement, mais une crédence totale `2/3` à ses deux subdivisions. Le
comptage uniforme dépend ainsi du grain descriptif : il satisfait la
normalisation et l'invariance des cotes sous simple restriction d'un record,
mais pas la cohérence sous subdivision des alternatives.

Ce témoin ne suppose pas que les cellules projectives exactes soient déjà des
branches physiques macroscopiques. Il montre une incompatibilité mathématique
avec le principe de cohérence sous raffinement.

**EN.** # Failure of the uniform rival under refinement

This module applies the uniform credence family to an explicit projective
refinement. The explicit coarse perspective has two cells, whereas its
refinement has three: one line is retained and its orthogonal complement is
decomposed into two lines.

Uniform credence therefore assigns `1/2` to the complementary coarse cell
before refinement, but total credence `2/3` to its two fine subdivisions.
Uniform counting thus depends on descriptive grain: it satisfies normalization
and odds invariance under mere record restriction, but not coherence under
subdivision of alternatives.

The witness does not assume that exact projective cells are already macroscopic
physical branches. It establishes a mathematical incompatibility with
refinement coherence.
-/

namespace EverettianProbability.Abstract

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Core
open EverettianProbability.Rivals
open scoped BigOperators Classical

noncomputable section

/-- The complementary cell of the explicit coarse projective perspective,
packaged as a cell of the abstract projective interface. -/
def projectiveExampleCoarseComplementCell :
    (Projective.interface 3).Cell exampleCoarse :=
  ⟨exampleLineᗮ, by
    simp [exampleCoarse, Perspective.binary]⟩

@[simp]
theorem pullbackRecordCells_univ
    {I : PerspectiveInterface}
    {fine coarse : I.Perspective}
    (r : I.Refinement fine coarse) :
    pullbackRecordCells r
        (Finset.univ : Finset (I.Cell coarse)) =
      (Finset.univ : Finset (I.Cell fine)) := by
  ext i
  simp [pullbackRecordCells]

private theorem projectiveExampleLine_finrank :
    Module.finrank ℂ exampleLine = 1 := by
  apply finrank_span_singleton
  intro hzero
  have hnorm :=
    (EuclideanSpace.basisFun (Fin 3) ℂ).orthonormal.1 (0 : Fin 3)
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

private theorem projectiveExampleLine_orthogonal_finrank :
    Module.finrank ℂ exampleLineᗮ = 2 := by
  have hsum :
      Module.finrank ℂ exampleLine + Module.finrank ℂ exampleLineᗮ = 3 := by
    rw [Submodule.finrank_add_finrank_orthogonal]
    simp
  rw [projectiveExampleLine_finrank] at hsum
  omega

private theorem projectiveExampleLine_orthogonal_mem_coarse :
    exampleLineᗮ ∈ exampleCoarse.cells := by
  simp only [exampleCoarse, Perspective.binary, Finset.mem_insert,
    Finset.mem_singleton, or_true]

private theorem parentCell_eq_complement_iff
    (i : (Projective.interface 3).Cell exampleFine) :
    (Projective.interface 3).parentCell exampleFine_refines i =
        projectiveExampleCoarseComplementCell ↔
      parentOf exampleFine_refines i.val = exampleLineᗮ := by
  rw [Projective.interface_parentCell_apply]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- The fibre over the complementary coarse cell contains exactly two fine
cells. -/
theorem projectiveExampleFine_complementFiber_card :
    (Finset.univ.filter
      (fun i : (Projective.interface 3).Cell exampleFine =>
        (Projective.interface 3).parentCell
            exampleFine_refines i =
          projectiveExampleCoarseComplementCell)).card =
      2 := by
  rw [Finset.card_filter]
  calc
    (∑ i ∈ (Finset.univ : Finset ((Projective.interface 3).Cell exampleFine)),
      if (Projective.interface 3).parentCell exampleFine_refines i =
          projectiveExampleCoarseComplementCell then 1 else 0) =
        ∑ i : (Projective.interface 3).Cell exampleFine,
          if parentOf exampleFine_refines i.val = exampleLineᗮ then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [parentCell_eq_complement_iff]
    _ = ∑ i ∈ exampleFine.cells,
          if parentOf exampleFine_refines i = exampleLineᗮ then 1 else 0 := by
            symm
            exact
              Finset.sum_subtype exampleFine.cells (fun i => by simp)
                (fun i =>
                  if parentOf exampleFine_refines i = exampleLineᗮ then 1 else 0)
    _ = ∑ i ∈ cellLines exampleLineᗮ, 1 := by
          rw [← Finset.sum_filter]
          rw [← coarseCells_eq_fiber_parentOf
            exampleFine_refines projectiveExampleLine_orthogonal_mem_coarse]
          unfold coarseCells exampleFine
          rw [refine_filter_eq_cellLines exampleCoarse exampleLineᗮ
            projectiveExampleLine_orthogonal_mem_coarse]
    _ = 2 := by
          rw [Finset.sum_const, cellLines_card_eq_finrank,
            projectiveExampleLine_orthogonal_finrank]
          norm_num

theorem uniformRecordCredence_projectiveCoarse_complement_eq :
    (uniformRecordCredenceFamily
        (Projective.interface 3)).credence
      exampleCoarse
      Finset.univ
      projectiveExampleCoarseComplementCell =
        1 / 2 := by
  have hcard :
      Fintype.card ((Projective.interface 3).Cell exampleCoarse) = 2 := by
    change Fintype.card {c // c ∈ exampleCoarse.cells} = 2
    rw [Fintype.card_coe]
    exact exampleCoarse_cells_card
  rw [uniformRecordCredenceFamily_credence]
  rw [Finset.card_univ, hcard]
  norm_num

private theorem uniformRecordCredence_projectiveFine_univ_eq
    (i : (Projective.interface 3).Cell exampleFine) :
    (uniformRecordCredenceFamily
        (Projective.interface 3)).credence
      exampleFine
      Finset.univ
      i =
        1 / 3 := by
  have hcard :
      Fintype.card ((Projective.interface 3).Cell exampleFine) = 3 := by
    change Fintype.card {c // c ∈ exampleFine.cells} = 3
    rw [Fintype.card_coe]
    exact exampleFine_cells_card
  rw [uniformRecordCredenceFamily_credence]
  rw [Finset.card_univ, hcard]
  norm_num

theorem uniformRecordCredence_projectiveFine_complementFiber_eq :
    (∑ i : (Projective.interface 3).Cell exampleFine,
      if (Projective.interface 3).parentCell
            exampleFine_refines i =
          projectiveExampleCoarseComplementCell then
        (uniformRecordCredenceFamily
            (Projective.interface 3)).credence
          exampleFine
          (pullbackRecordCells
            exampleFine_refines
            (Finset.univ :
              Finset ((Projective.interface 3).Cell exampleCoarse)))
          i
      else
        0) =
      2 / 3 := by
  rw [pullbackRecordCells_univ]
  calc
    (∑ i : (Projective.interface 3).Cell exampleFine,
      if (Projective.interface 3).parentCell
            exampleFine_refines i =
          projectiveExampleCoarseComplementCell then
        (uniformRecordCredenceFamily
            (Projective.interface 3)).credence exampleFine Finset.univ i
      else 0) =
        ∑ i : (Projective.interface 3).Cell exampleFine,
          if (Projective.interface 3).parentCell
                exampleFine_refines i =
              projectiveExampleCoarseComplementCell then (1 / 3 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hparent :
                (Projective.interface 3).parentCell exampleFine_refines i =
                  projectiveExampleCoarseComplementCell
            · rw [if_pos hparent, if_pos hparent]
              exact uniformRecordCredence_projectiveFine_univ_eq i
            · rw [if_neg hparent, if_neg hparent]
    _ = ∑ i ∈ (Finset.univ.filter
          (fun i : (Projective.interface 3).Cell exampleFine =>
            (Projective.interface 3).parentCell exampleFine_refines i =
              projectiveExampleCoarseComplementCell)),
          (1 / 3 : ℝ) := by
            exact (Finset.sum_filter _ _).symm
    _ = (Finset.univ.filter
          (fun i : (Projective.interface 3).Cell exampleFine =>
            (Projective.interface 3).parentCell exampleFine_refines i =
              projectiveExampleCoarseComplementCell)).card • (1 / 3 : ℝ) := by
            rw [Finset.sum_const]
    _ = 2 / 3 := by
          rw [projectiveExampleFine_complementFiber_card, nsmul_eq_mul]
          norm_num

/-- Explicit failure of refinement coherence for uniform credence:
`1/2 ≠ 2/3`. -/
theorem uniformRecordCredence_projective_refinement_failure :
    (uniformRecordCredenceFamily
        (Projective.interface 3)).credence
      exampleCoarse
      Finset.univ
      projectiveExampleCoarseComplementCell ≠
    ∑ i : (Projective.interface 3).Cell exampleFine,
      if (Projective.interface 3).parentCell
            exampleFine_refines i =
          projectiveExampleCoarseComplementCell then
        (uniformRecordCredenceFamily
            (Projective.interface 3)).credence
          exampleFine
          (pullbackRecordCells
            exampleFine_refines
            (Finset.univ :
              Finset ((Projective.interface 3).Cell exampleCoarse)))
          i
      else
        0 := by
  rw [uniformRecordCredence_projectiveCoarse_complement_eq,
    uniformRecordCredence_projectiveFine_complementFiber_eq]
  norm_num

private theorem projectiveInterface3_outcome_injective :
    ∀ D : (Projective.interface 3).Perspective,
      Function.Injective
        (@(Projective.interface 3).outcome D) := by
  intro D
  exact Subtype.val_injective

/-- The uniform family fails the abstract refinement-coherence requirement on
the explicit projective witness. The numerical contradiction is independent
of the rational expectation family in the hypotheses. -/
theorem uniformRecordCredenceFamily_not_refinementCoherent_on_projectiveExample
    (F :
      RationalExpectationFamily
        (Projective.interface 3))
    (hinv :
      RefinementInvariantLocal F.V) :
    ¬ (uniformRecordCredenceFamily
        (Projective.interface 3)).RefinementCoherent
          F
          hinv
          projectiveInterface3_outcome_injective := by
  intro hcoherent
  have hmass :
      recordCompatibleMass
          F
          exampleCoarse
          (Finset.univ :
            Finset ((Projective.interface 3).Cell exampleCoarse)) ≠
        0 := by
    rw [recordCompatibleMass_univ F exampleCoarse
      (projectiveInterface3_outcome_injective exampleCoarse)]
    norm_num
  have h :=
    hcoherent
      exampleFine_refines
      (Finset.univ :
        Finset ((Projective.interface 3).Cell exampleCoarse))
      projectiveExampleCoarseComplementCell
      hmass
  exact uniformRecordCredence_projective_refinement_failure h

end
end EverettianProbability.Abstract
