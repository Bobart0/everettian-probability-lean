import EverettianProbability.Diachronic.EqualNormLocalUnitary

/-!
**FR.** # Orbite bloc-diagonale du record bornien

Ce module assemble les unitaires internes aux cellules d'une perspective
en une évolution linéaire globale. La somme des blocs projette dans chaque
cellule, applique l'unitaire local, puis réinjecte la composante obtenue.
L'orthogonalité et la complétude des cellules donnent la commutation avec
les projecteurs et la conservation de la norme.

**EN.** # Block-diagonal orbit of the Born record

This module assembles the unitaries internal to the cells of a perspective
into one global linear evolution. The sum of the blocks projects into each
cell, applies its local unitary, and includes the resulting component back
into the ambient space. Orthogonality and completeness yield commutation
with the projectors and preservation of norm.
-/

namespace EverettianProbability.Abstract

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core
open EverettianProbability.PhysicalRefinement
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : ℕ}

/-- Orthogonal projection onto a cell, with codomain restricted to that
cell subspace itself. -/
def cellProjectionToSubmodule
    (D : Perspective n)
    (c : (Projective.interface n).Cell D) :
    H n →ₗ[ℂ] c.val :=
  (projL c.val).codRestrict
    c.val
    (fun z => Submodule.starProjection_apply_mem c.val z)

@[simp]
theorem cellProjectionToSubmodule_val
    (D : Perspective n)
    (c : (Projective.interface n).Cell D)
    (z : H n) :
    ((cellProjectionToSubmodule D c z : c.val) : H n) =
      cellComponent D c z := by
  change projL c.val z = cellComponent D c z
  rfl

/-- Global linear block obtained by projection to one cell, application
of its local unitary, and inclusion back into the full Hilbert space. -/
def cellBlockLinearMap
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y)
    (c : (Projective.interface n).Cell D) :
    H n →ₗ[ℂ] H n :=
  (Submodule.subtype c.val).comp
    ((W.localUnitary c).toLinearEquiv.toLinearMap.comp
      (cellProjectionToSubmodule D c))

@[simp]
theorem cellBlockLinearMap_apply
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y)
    (c : (Projective.interface n).Cell D)
    (z : H n) :
    cellBlockLinearMap W c z =
      ((W.localUnitary c
        (cellProjectionToSubmodule D c z) : c.val) : H n) := by
  rfl

/-- Every output of one block belongs to that block's cell. -/
theorem cellBlockLinearMap_mem
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y)
    (c : (Projective.interface n).Cell D)
    (z : H n) :
    cellBlockLinearMap W c z ∈ c.val := by
  exact
    (W.localUnitary c
      (cellProjectionToSubmodule D c z)).property

/-- Distinct cells of a perspective are orthogonal subspaces. -/
theorem perspectiveCells_isOrtho
    (D : Perspective n)
    {c d : (Projective.interface n).Cell D}
    (hcd : c ≠ d) :
    c.val ⟂ d.val := by
  apply Submodule.isOrtho_iff_le.mpr
  exact
    D.ortho c.val c.property d.val d.property
      (fun h => hcd (Subtype.ext h))

/-- Projecting a block output back onto the same cell leaves it
unchanged. -/
theorem projL_cellBlockLinearMap_self
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y)
    (c : (Projective.interface n).Cell D)
    (z : H n) :
    projL c.val (cellBlockLinearMap W c z) =
      cellBlockLinearMap W c z := by
  exact
    Submodule.starProjection_eq_self_iff.mpr
      (cellBlockLinearMap_mem W c z)

/-- Projecting the output of a distinct block onto `c` gives zero. -/
theorem projL_cellBlockLinearMap_eq_zero_of_ne
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y)
    {c d : (Projective.interface n).Cell D}
    (hcd : c ≠ d)
    (z : H n) :
    projL c.val (cellBlockLinearMap W d z) = 0 := by
  change c.val.starProjection (cellBlockLinearMap W d z) = 0
  rw [Submodule.starProjection_apply_eq_zero_iff]
  exact
    (Submodule.isOrtho_iff_le.mp
      (perspectiveCells_isOrtho D hcd).symm)
      (cellBlockLinearMap_mem W d z)

/-- Sum of all cell blocks. -/
def blockDiagonalLinearMap
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y) :
    H n →ₗ[ℂ] H n :=
  ∑ c : (Projective.interface n).Cell D,
    cellBlockLinearMap W c

@[simp]
theorem blockDiagonalLinearMap_apply
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y)
    (z : H n) :
    blockDiagonalLinearMap W z =
      ∑ c : (Projective.interface n).Cell D,
        cellBlockLinearMap W c z := by
  simp [blockDiagonalLinearMap]

/-- Projecting the global block-diagonal map onto `c` selects exactly
the `c` block. -/
theorem projL_blockDiagonalLinearMap
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y)
    (c : (Projective.interface n).Cell D)
    (z : H n) :
    projL c.val (blockDiagonalLinearMap W z) =
      cellBlockLinearMap W c z := by
  rw [blockDiagonalLinearMap_apply, map_sum, Finset.sum_eq_single c]
  · exact projL_cellBlockLinearMap_self W c z
  · intro d _ hdc
    exact projL_cellBlockLinearMap_eq_zero_of_ne W hdc.symm z
  · exact fun hnot => (hnot (Finset.mem_univ c)).elim

private theorem projL_projL_self
    (D : Perspective n)
    (c : (Projective.interface n).Cell D)
    (z : H n) :
    projL c.val (projL c.val z) = projL c.val z := by
  exact
    Submodule.starProjection_eq_self_iff.mpr
      (Submodule.starProjection_apply_mem c.val z)

private theorem projL_projL_eq_zero_of_ne
    (D : Perspective n)
    {c d : (Projective.interface n).Cell D}
    (hdc : d ≠ c)
    (z : H n) :
    projL d.val (projL c.val z) = 0 := by
  change d.val.starProjection (projL c.val z) = 0
  rw [Submodule.starProjection_apply_eq_zero_iff]
  exact
    (Submodule.isOrtho_iff_le.mp
      (perspectiveCells_isOrtho D hdc).symm)
      (Submodule.starProjection_apply_mem c.val z)

/-- Applying the global block-diagonal operator to the projection onto
`c` also selects the `c` block. -/
theorem blockDiagonalLinearMap_projL
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y)
    (c : (Projective.interface n).Cell D)
    (z : H n) :
    blockDiagonalLinearMap W (projL c.val z) =
      cellBlockLinearMap W c z := by
  rw [blockDiagonalLinearMap_apply, Finset.sum_eq_single c]
  · rw [cellBlockLinearMap_apply, cellBlockLinearMap_apply]
    congr 2
    apply Subtype.ext
    change projL c.val (projL c.val z) = projL c.val z
    exact projL_projL_self D c z
  · intro d _ hdc
    have hzero : cellProjectionToSubmodule D d (projL c.val z) = 0 := by
      apply Subtype.ext
      change projL d.val (projL c.val z) = 0
      exact projL_projL_eq_zero_of_ne D hdc z
    simp [cellBlockLinearMap_apply, hzero]
  · exact fun hnot => (hnot (Finset.mem_univ c)).elim

/-- The assembled block-diagonal map commutes with every projector of
the perspective. -/
theorem blockDiagonalLinearMap_commutes
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y) :
    CommutesWithPerspectiveProjectors D (blockDiagonalLinearMap W) := by
  intro c z
  rw [projL_blockDiagonalLinearMap, blockDiagonalLinearMap_projL]

/-- Each block has the same norm as the corresponding projected
component. -/
theorem norm_cellBlockLinearMap
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y)
    (c : (Projective.interface n).Cell D)
    (z : H n) :
    ‖cellBlockLinearMap W c z‖ =
      ‖cellComponent D c z‖ := by
  change
    ‖W.localUnitary c (cellProjectionToSubmodule D c z)‖ =
      ‖projL c.val z‖
  rw [(W.localUnitary c).norm_map]
  change ‖(projL c.val z : H n)‖ = ‖projL c.val z‖
  rfl

/-- The squared norms of all cell components sum to the squared norm of
the full state. -/
theorem sum_cellComponent_norm_sq_eq_norm_sq
    (D : Perspective n)
    (z : H n) :
    (∑ c : (Projective.interface n).Cell D,
      ‖cellComponent D c z‖ ^ 2) =
      ‖z‖ ^ 2 := by
  change (∑ c : {c : Submodule ℂ (H n) // c ∈ D.cells}, ‖projL c.val z‖ ^ 2) = ‖z‖ ^ 2
  calc
    (∑ c : {c : Submodule ℂ (H n) // c ∈ D.cells}, ‖projL c.val z‖ ^ 2) =
        ∑ c ∈ D.cells, ‖projL c z‖ ^ 2 := by
      symm
      exact Finset.sum_subtype D.cells (fun c => Iff.rfl) (fun c => ‖projL c z‖ ^ 2)
    _ = ‖z‖ ^ 2 := by
      have h := QuantumFoundations.BornRule.sum_sq_projL_of_pairwise_isOrtho D.cells D.ortho z
      rw [Finset.sup_id_eq_sSup, D.span] at h
      have htop : projL (⊤ : Submodule ℂ (H n)) = LinearMap.id := by
        unfold projL
        rw [Submodule.starProjection_top]
        rfl
      rw [htop] at h
      simpa using h.symm

/-- The assembled global map preserves squared norm. -/
theorem blockDiagonalLinearMap_norm_sq
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y)
    (z : H n) :
    ‖blockDiagonalLinearMap W z‖ ^ 2 = ‖z‖ ^ 2 := by
  calc
    ‖blockDiagonalLinearMap W z‖ ^ 2 =
        ∑ c : (Projective.interface n).Cell D,
          ‖cellComponent D c (blockDiagonalLinearMap W z)‖ ^ 2 := by
      symm
      exact sum_cellComponent_norm_sq_eq_norm_sq D (blockDiagonalLinearMap W z)
    _ = ∑ c : (Projective.interface n).Cell D, ‖cellBlockLinearMap W c z‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro c _
      unfold cellComponent
      rw [projL_blockDiagonalLinearMap]
    _ = ∑ c : (Projective.interface n).Cell D, ‖cellComponent D c z‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [norm_cellBlockLinearMap]
    _ = ‖z‖ ^ 2 := sum_cellComponent_norm_sq_eq_norm_sq D z

/-- The global block-diagonal map is an isometry. -/
theorem blockDiagonalLinearMap_isometry
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y)
    (z : H n) :
    ‖blockDiagonalLinearMap W z‖ = ‖z‖ := by
  have hSq := blockDiagonalLinearMap_norm_sq W z
  nlinarith [norm_nonneg (blockDiagonalLinearMap W z), norm_nonneg z]

/-- The global map sends every source cell component to the
corresponding target component. -/
theorem blockDiagonalLinearMap_maps_cellComponent
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y)
    (c : (Projective.interface n).Cell D) :
    blockDiagonalLinearMap W (cellComponent D c x) =
      cellComponent D c y := by
  change blockDiagonalLinearMap W (projL c.val x) = cellComponent D c y
  rw [blockDiagonalLinearMap_projL]
  change ((W.localUnitary c (sourceCellVector D c x) : c.val) : H n) = cellComponent D c y
  exact W.maps_component_val c

/-- The assembled block-diagonal operator maps the source state to the
target state. -/
theorem blockDiagonalLinearMap_maps_state
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y) :
    blockDiagonalLinearMap W x = y := by
  exact
    maps_state_of_maps_all_cellComponents
      D (blockDiagonalLinearMap W) x y
      (blockDiagonalLinearMap_maps_cellComponent W)

/-- Equal Born record is sufficient for a projector-commuting isometric
orbit. -/
theorem projectorCommutingIsometricOrbit_of_sameBornRecord
    {D : Perspective n}
    {x y : H n}
    (hRecord : SameBornRecord D x y) :
    ProjectorCommutingIsometricOrbit D x y := by
  let W : CellwiseUnitaryData D x y :=
    cellwiseUnitaryData_of_sameBornRecord hRecord
  exact ⟨blockDiagonalLinearMap W, blockDiagonalLinearMap_isometry W,
    blockDiagonalLinearMap_commutes W, blockDiagonalLinearMap_maps_state W⟩

/-- Equality of the complete Born record exactly characterizes the
projector-commuting isometric orbit. -/
theorem projectorCommutingIsometricOrbit_iff_sameBornRecord
    (D : Perspective n)
    (x y : H n) :
    ProjectorCommutingIsometricOrbit D x y ↔ SameBornRecord D x y := by
  constructor
  · exact sameBornRecord_of_projectorCommutingIsometricOrbit
  · exact projectorCommutingIsometricOrbit_of_sameBornRecord

/-- Explicit block-diagonal form of the orbit theorem. -/
theorem sameBornRecord_iff_exists_projectorCommutingIsometry
    (D : Perspective n)
    (x y : H n) :
    SameBornRecord D x y ↔
      ∃ evolution : H n →ₗ[ℂ] H n,
        (∀ z : H n, ‖evolution z‖ = ‖z‖) ∧
        CommutesWithPerspectiveProjectors D evolution ∧
        evolution x = y := by
  exact (projectorCommutingIsometricOrbit_iff_sameBornRecord D x y).symm

/-- Noncomputably assembled block-diagonal evolution for the concrete
record-neutral states. -/
noncomputable def recordNeutralAssembledBlockEvolution : H 3 →ₗ[ℂ] H 3 :=
  blockDiagonalLinearMap recordNeutralCellwiseUnitaryData

theorem recordNeutralAssembledBlockEvolution_isometry
    (z : H 3) :
    ‖recordNeutralAssembledBlockEvolution z‖ = ‖z‖ := by
  exact blockDiagonalLinearMap_isometry recordNeutralCellwiseUnitaryData z

theorem recordNeutralAssembledBlockEvolution_commutes :
    CommutesWithPerspectiveProjectors coarsePerspective
      recordNeutralAssembledBlockEvolution := by
  exact blockDiagonalLinearMap_commutes recordNeutralCellwiseUnitaryData

theorem recordNeutralAssembledBlockEvolution_maps_state :
    recordNeutralAssembledBlockEvolution psiBefore = psiAfter := by
  exact blockDiagonalLinearMap_maps_state recordNeutralCellwiseUnitaryData

/-- Integrated block-diagonal orbit witness. -/
theorem recordNeutralBlockDiagonalRecordOrbit_integratedWitness :
    psiBefore ≠ psiAfter ∧
    SameBornRecord coarsePerspective psiBefore psiAfter ∧
    ProjectorCommutingIsometricOrbit coarsePerspective psiBefore psiAfter ∧
    (∀ z : H 3, ‖recordNeutralAssembledBlockEvolution z‖ = ‖z‖) ∧
    CommutesWithPerspectiveProjectors coarsePerspective recordNeutralAssembledBlockEvolution ∧
    recordNeutralAssembledBlockEvolution psiBefore = psiAfter := by
  refine ⟨ProjectorCommutingProjectiveContinuation.recordNeutral_psiBefore_ne_psiAfter,
    ProjectorCommutingProjectiveContinuation.recordNeutral_psiBefore_psiAfter_sameBornRecord,
    projectorCommutingIsometricOrbit_of_sameBornRecord
      ProjectorCommutingProjectiveContinuation.recordNeutral_psiBefore_psiAfter_sameBornRecord,
    recordNeutralAssembledBlockEvolution_isometry,
    recordNeutralAssembledBlockEvolution_commutes,
    recordNeutralAssembledBlockEvolution_maps_state⟩

end
end EverettianProbability.Abstract
