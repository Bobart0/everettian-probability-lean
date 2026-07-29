import EverettianProbability.Diachronic.BlockDiagonalRecordOrbit

/-!
**FR.** # Orbite unitaire du record bornien

Ce module renforce le theoreme d'orbite bloc-diagonale en construisant
une veritable equivalence lineaire isometrique globale. L'operateur
assemble preserve la norme, est bijectif en dimension finie, commute avec
les projecteurs du record et envoie l'etat source sur l'etat cible.

L'inverse commute egalement avec ces projecteurs et ramene l'etat cible
sur l'etat source. La conclusion concerne des perspectives projectives
finies et ne construit pas encore de partage fin arbitraire des poids.

**EN.** # Unitary orbit of the Born record

This module strengthens the block-diagonal orbit theorem by constructing
a genuine global linear isometric equivalence. The assembled operator
preserves norm, is bijective in finite dimension, commutes with record
projectors, and maps the source state to the target state.

Its inverse also commutes with these projectors and maps the target state
back to the source state. The conclusion concerns finite projective
perspectives and does not yet construct an arbitrary fine weight split.
-/

namespace EverettianProbability.Abstract

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core
open EverettianProbability.PhysicalRefinement
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : ℕ}

/-- A norm-preserving linear map bundled as a linear isometry. -/
def linearIsometryOfNormPreserving
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    (f : E →ₗ[ℂ] E)
    (hNorm : ∀ x : E, ‖f x‖ = ‖x‖) :
    E →ₗᵢ[ℂ] E where
  toLinearMap := f
  norm_map' := hNorm

@[simp]
theorem linearIsometryOfNormPreserving_apply
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    (f : E →ₗ[ℂ] E)
    (hNorm : ∀ x : E, ‖f x‖ = ‖x‖)
    (x : E) :
    linearIsometryOfNormPreserving f hNorm x = f x := by
  rfl

theorem linearIsometryOfNormPreserving_injective
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    (f : E →ₗ[ℂ] E)
    (hNorm : ∀ x : E, ‖f x‖ = ‖x‖) :
    Function.Injective f := by
  exact (linearIsometryOfNormPreserving f hNorm).injective

/-- A norm-preserving linear endomorphism of a finite-dimensional complex
space is surjective. -/
theorem normPreservingLinearMap_surjective
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (f : E →ₗ[ℂ] E)
    (hNorm : ∀ x : E, ‖f x‖ = ‖x‖) :
    Function.Surjective f := by
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f) rfl).mp
      (linearIsometryOfNormPreserving_injective f hNorm)

/-- A norm-preserving finite-dimensional linear endomorphism packaged as a
linear isometric equivalence. -/
noncomputable def linearIsometryEquivOfNormPreserving
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (f : E →ₗ[ℂ] E)
    (hNorm : ∀ x : E, ‖f x‖ = ‖x‖) :
    E ≃ₗᵢ[ℂ] E :=
  LinearIsometryEquiv.ofSurjective
    (linearIsometryOfNormPreserving f hNorm)
    (normPreservingLinearMap_surjective f hNorm)

@[simp]
theorem linearIsometryEquivOfNormPreserving_apply
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (f : E →ₗ[ℂ] E)
    (hNorm : ∀ x : E, ‖f x‖ = ‖x‖)
    (x : E) :
    linearIsometryEquivOfNormPreserving f hNorm x = f x := by
  rfl

theorem linearIsometryEquivOfNormPreserving_toLinearMap
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (f : E →ₗ[ℂ] E)
    (hNorm : ∀ x : E, ‖f x‖ = ‖x‖) :
    (linearIsometryEquivOfNormPreserving f hNorm).toLinearEquiv.toLinearMap = f := by
  ext x
  rfl

/-- The assembled block-diagonal map bundled as a linear isometry. -/
def blockDiagonalLinearIsometry
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y) :
    H n →ₗᵢ[ℂ] H n :=
  linearIsometryOfNormPreserving
    (blockDiagonalLinearMap W)
    (blockDiagonalLinearMap_isometry W)

@[simp]
theorem blockDiagonalLinearIsometry_apply
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y)
    (z : H n) :
    blockDiagonalLinearIsometry W z = blockDiagonalLinearMap W z := by
  rfl

theorem blockDiagonalLinearIsometry_surjective
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y) :
    Function.Surjective (blockDiagonalLinearIsometry W) := by
  exact
    normPreservingLinearMap_surjective
      (blockDiagonalLinearMap W)
      (blockDiagonalLinearMap_isometry W)

/-- Global block-diagonal unitary assembled from local cell unitaries. -/
noncomputable def blockDiagonalUnitary
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y) :
    H n ≃ₗᵢ[ℂ] H n :=
  LinearIsometryEquiv.ofSurjective
    (blockDiagonalLinearIsometry W)
    (blockDiagonalLinearIsometry_surjective W)

@[simp]
theorem blockDiagonalUnitary_apply
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y)
    (z : H n) :
    blockDiagonalUnitary W z = blockDiagonalLinearMap W z := by
  rfl

theorem blockDiagonalUnitary_toLinearMap
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y) :
    (blockDiagonalUnitary W).toLinearEquiv.toLinearMap = blockDiagonalLinearMap W := by
  ext z
  rfl

/-- The assembled unitary commutes with every projector of the perspective. -/
theorem blockDiagonalUnitary_commutes
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y) :
    CommutesWithPerspectiveProjectors
      D (blockDiagonalUnitary W).toLinearEquiv.toLinearMap := by
  change CommutesWithPerspectiveProjectors D (blockDiagonalLinearMap W)
  exact blockDiagonalLinearMap_commutes W

theorem blockDiagonalUnitary_commutes_cell
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y)
    (c : (Projective.interface n).Cell D) :
    CommutesWithProjector
      (blockDiagonalUnitary W).toLinearEquiv.toLinearMap c.val := by
  exact blockDiagonalUnitary_commutes W c

/-- The assembled unitary maps the source state to the target state. -/
theorem blockDiagonalUnitary_maps_state
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y) :
    blockDiagonalUnitary W x = y := by
  change blockDiagonalLinearMap W x = y
  exact blockDiagonalLinearMap_maps_state W

/-- The inverse of a unitary commuting with one projector also commutes with
that projector. -/
theorem LinearIsometryEquiv.commutesWithProjector_symm
    (U : H n ≃ₗᵢ[ℂ] H n)
    {c : Submodule ℂ (H n)}
    (hCommutes : CommutesWithProjector U.toLinearEquiv.toLinearMap c) :
    CommutesWithProjector U.symm.toLinearEquiv.toLinearMap c := by
  intro z
  apply U.injective
  change U (projL c (U.symm z)) = U (U.symm (projL c z))
  calc
    U (projL c (U.symm z)) =
        projL c (U.toLinearEquiv.toLinearMap (U.symm z)) :=
      (hCommutes (U.symm z)).symm
    _ = projL c z := by
      change projL c (U (U.symm z)) = projL c z
      rw [U.apply_symm_apply]
    _ = U (U.symm (projL c z)) := by rw [U.apply_symm_apply]

theorem LinearIsometryEquiv.commutesWithPerspectiveProjectors_symm
    (U : H n ≃ₗᵢ[ℂ] H n)
    {D : Perspective n}
  (hCommutes : CommutesWithPerspectiveProjectors D U.toLinearEquiv.toLinearMap) :
    CommutesWithPerspectiveProjectors D U.symm.toLinearEquiv.toLinearMap := by
  intro c
  exact LinearIsometryEquiv.commutesWithProjector_symm U (hCommutes c)

theorem blockDiagonalUnitary_symm_commutes
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y) :
    CommutesWithPerspectiveProjectors
      D (blockDiagonalUnitary W).symm.toLinearEquiv.toLinearMap := by
  exact
    LinearIsometryEquiv.commutesWithPerspectiveProjectors_symm
      (blockDiagonalUnitary W)
      (blockDiagonalUnitary_commutes W)

theorem blockDiagonalUnitary_symm_maps_state
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y) :
    (blockDiagonalUnitary W).symm y = x := by
  calc
    (blockDiagonalUnitary W).symm y =
        (blockDiagonalUnitary W).symm (blockDiagonalUnitary W x) :=
      congrArg (blockDiagonalUnitary W).symm
        (blockDiagonalUnitary_maps_state W).symm
    _ = x := (blockDiagonalUnitary W).symm_apply_apply x

/-- Two states lie in the same projector-commuting unitary orbit when a
linear isometric equivalence commuting with every projector maps one to the
other. -/
def ProjectorCommutingUnitaryOrbit
    (D : Perspective n)
    (x y : H n) : Prop :=
  ∃ U : H n ≃ₗᵢ[ℂ] H n,
    CommutesWithPerspectiveProjectors D U.toLinearEquiv.toLinearMap ∧ U x = y

theorem ProjectorCommutingUnitaryOrbit.refl
    (D : Perspective n)
    (x : H n) :
    ProjectorCommutingUnitaryOrbit D x x := by
  refine ⟨LinearIsometryEquiv.refl ℂ (H n), ?_, rfl⟩
  change CommutesWithPerspectiveProjectors D (LinearMap.id : H n →ₗ[ℂ] H n)
  exact commutesWithPerspectiveProjectors_id D

theorem ProjectorCommutingUnitaryOrbit.symm
    {D : Perspective n}
    {x y : H n}
    (h : ProjectorCommutingUnitaryOrbit D x y) :
    ProjectorCommutingUnitaryOrbit D y x := by
  rcases h with ⟨U, hCommutes, hMap⟩
  refine ⟨U.symm,
    LinearIsometryEquiv.commutesWithPerspectiveProjectors_symm U hCommutes, ?_⟩
  rw [← hMap, U.symm_apply_apply]

theorem ProjectorCommutingUnitaryOrbit.trans
    {D : Perspective n}
    {x y z : H n}
    (hxy : ProjectorCommutingUnitaryOrbit D x y)
    (hyz : ProjectorCommutingUnitaryOrbit D y z) :
    ProjectorCommutingUnitaryOrbit D x z := by
  rcases hxy with ⟨Uxy, hUxyCommutes, hUxyMap⟩
  rcases hyz with ⟨Uyz, hUyzCommutes, hUyzMap⟩
  refine ⟨Uxy.trans Uyz, ?_, ?_⟩
  · change CommutesWithPerspectiveProjectors D
      (Uyz.toLinearEquiv.toLinearMap.comp Uxy.toLinearEquiv.toLinearMap)
    exact hUyzCommutes.comp hUxyCommutes
  · rw [LinearIsometryEquiv.trans_apply, hUxyMap, hUyzMap]

/-- A projector-commuting unitary orbit is in particular a
projector-commuting isometric orbit. -/
theorem projectorCommutingIsometricOrbit_of_unitaryOrbit
    {D : Perspective n}
    {x y : H n}
    (hUnitary : ProjectorCommutingUnitaryOrbit D x y) :
    ProjectorCommutingIsometricOrbit D x y := by
  rcases hUnitary with ⟨U, hCommutes, hMap⟩
  refine ⟨U.toLinearEquiv.toLinearMap, ?_, hCommutes, hMap⟩
  intro z
  exact U.norm_map z

/-- In finite dimension, every projector-commuting isometric orbit can be
upgraded to a projector-commuting unitary orbit. -/
theorem projectorCommutingUnitaryOrbit_of_isometricOrbit
    {D : Perspective n}
    {x y : H n}
    (hIsometric : ProjectorCommutingIsometricOrbit D x y) :
    ProjectorCommutingUnitaryOrbit D x y := by
  rcases hIsometric with ⟨evolution, hIso, hCommutes, hMap⟩
  let U : H n ≃ₗᵢ[ℂ] H n :=
    linearIsometryEquivOfNormPreserving evolution hIso
  refine ⟨U, ?_, ?_⟩
  · change CommutesWithPerspectiveProjectors D evolution
    exact hCommutes
  · change evolution x = y
    exact hMap

theorem projectorCommutingUnitaryOrbit_iff_isometricOrbit
    (D : Perspective n)
    (x y : H n) :
    ProjectorCommutingUnitaryOrbit D x y ↔
      ProjectorCommutingIsometricOrbit D x y := by
  constructor
  · exact projectorCommutingIsometricOrbit_of_unitaryOrbit
  · exact projectorCommutingUnitaryOrbit_of_isometricOrbit

theorem sameBornRecord_of_projectorCommutingUnitaryOrbit
    {D : Perspective n}
    {x y : H n}
    (hOrbit : ProjectorCommutingUnitaryOrbit D x y) :
    SameBornRecord D x y := by
  exact
    sameBornRecord_of_projectorCommutingIsometricOrbit
      (projectorCommutingIsometricOrbit_of_unitaryOrbit hOrbit)

/-- Equal Born record supplies a global projector-commuting unitary. -/
theorem projectorCommutingUnitaryOrbit_of_sameBornRecord
    {D : Perspective n}
    {x y : H n}
    (hRecord : SameBornRecord D x y) :
    ProjectorCommutingUnitaryOrbit D x y := by
  let W : CellwiseUnitaryData D x y := cellwiseUnitaryData_of_sameBornRecord hRecord
  exact ⟨blockDiagonalUnitary W, blockDiagonalUnitary_commutes W,
    blockDiagonalUnitary_maps_state W⟩

/-- Equality of the complete Born record exactly characterizes the orbit of
projector-commuting global unitaries. -/
theorem projectorCommutingUnitaryOrbit_iff_sameBornRecord
    (D : Perspective n)
    (x y : H n) :
    ProjectorCommutingUnitaryOrbit D x y ↔ SameBornRecord D x y := by
  constructor
  · exact sameBornRecord_of_projectorCommutingUnitaryOrbit
  · exact projectorCommutingUnitaryOrbit_of_sameBornRecord

/-- Explicit unitary form of the Born-record orbit theorem. -/
theorem sameBornRecord_iff_exists_projectorCommutingUnitary
    (D : Perspective n)
    (x y : H n) :
    SameBornRecord D x y ↔
      ∃ U : H n ≃ₗᵢ[ℂ] H n,
        CommutesWithPerspectiveProjectors D U.toLinearEquiv.toLinearMap ∧ U x = y := by
  exact (projectorCommutingUnitaryOrbit_iff_sameBornRecord D x y).symm

/-- States in the same projector-commuting unitary orbit assign equal Born
values to every act on the record perspective. -/
theorem bornExpectation_eq_of_projectorCommutingUnitaryOrbit
    {D : Perspective n}
    {x y : H n}
    (hOrbit : ProjectorCommutingUnitaryOrbit D x y)
    (a : EverettianProbability.Core.Act n) :
    EverettianProbability.Refinement.bornExpectation x D a =
      EverettianProbability.Refinement.bornExpectation y D a := by
  exact
    bornExpectation_eq_of_sameBornRecord
      (sameBornRecord_of_projectorCommutingUnitaryOrbit hOrbit) a

/-- Assembled global unitary for the record-neutral before/after states. -/
noncomputable def recordNeutralAssembledBlockUnitary :
    H 3 ≃ₗᵢ[ℂ] H 3 :=
  blockDiagonalUnitary recordNeutralCellwiseUnitaryData

theorem recordNeutralAssembledBlockUnitary_maps_state :
    recordNeutralAssembledBlockUnitary psiBefore = psiAfter := by
  exact blockDiagonalUnitary_maps_state recordNeutralCellwiseUnitaryData

theorem recordNeutralAssembledBlockUnitary_symm_maps_state :
    recordNeutralAssembledBlockUnitary.symm psiAfter = psiBefore := by
  exact blockDiagonalUnitary_symm_maps_state recordNeutralCellwiseUnitaryData

theorem recordNeutralAssembledBlockUnitary_commutes :
    CommutesWithPerspectiveProjectors coarsePerspective
      recordNeutralAssembledBlockUnitary.toLinearEquiv.toLinearMap := by
  exact blockDiagonalUnitary_commutes recordNeutralCellwiseUnitaryData

theorem recordNeutralAssembledBlockUnitary_symm_commutes :
    CommutesWithPerspectiveProjectors coarsePerspective
      recordNeutralAssembledBlockUnitary.symm.toLinearEquiv.toLinearMap := by
  exact blockDiagonalUnitary_symm_commutes recordNeutralCellwiseUnitaryData

theorem recordNeutral_projectorCommutingUnitaryOrbit :
    ProjectorCommutingUnitaryOrbit coarsePerspective psiBefore psiAfter := by
  exact
    projectorCommutingUnitaryOrbit_of_sameBornRecord
      ProjectorCommutingProjectiveContinuation.recordNeutral_psiBefore_psiAfter_sameBornRecord

/-- Integrated unitary Born-record orbit witness. -/
theorem recordNeutralUnitaryRecordOrbit_integratedWitness :
    psiBefore ≠ psiAfter ∧
    SameBornRecord coarsePerspective psiBefore psiAfter ∧
    ProjectorCommutingUnitaryOrbit coarsePerspective psiBefore psiAfter ∧
    recordNeutralAssembledBlockUnitary psiBefore = psiAfter ∧
    recordNeutralAssembledBlockUnitary.symm psiAfter = psiBefore ∧
    CommutesWithPerspectiveProjectors coarsePerspective
      recordNeutralAssembledBlockUnitary.toLinearEquiv.toLinearMap ∧
    CommutesWithPerspectiveProjectors coarsePerspective
      recordNeutralAssembledBlockUnitary.symm.toLinearEquiv.toLinearMap := by
  exact ⟨ProjectorCommutingProjectiveContinuation.recordNeutral_psiBefore_ne_psiAfter,
    ProjectorCommutingProjectiveContinuation.recordNeutral_psiBefore_psiAfter_sameBornRecord,
    recordNeutral_projectorCommutingUnitaryOrbit,
    recordNeutralAssembledBlockUnitary_maps_state,
    recordNeutralAssembledBlockUnitary_symm_maps_state,
    recordNeutralAssembledBlockUnitary_commutes,
    recordNeutralAssembledBlockUnitary_symm_commutes⟩

end
end EverettianProbability.Abstract
