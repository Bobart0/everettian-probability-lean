import EverettianProbability.Diachronic.PhysicalBornRatioComposition

/-!
**FR.** # Continuations commutant avec les projecteurs du record

Ce module donne une condition structurelle suffisante pour conserver les
poids borniens : une evolution isometrique commute avec tous les projecteurs
de la perspective presente. La conservation du record reste une premisse
physique separee.

**EN.** # Continuations commuting with record projectors

This module gives a structural sufficient condition for preserving Born
weights: an isometric evolution commutes with all projectors of the present
perspective. Record preservation remains a separate physical premise.
-/

namespace EverettianProbability.Abstract

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.PhysicalRefinement
open QuantumFoundations.Uhlhorn (projL_singleton_unit)
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : Nat}

/-- A linear evolution commutes with one projective orthogonal projector. -/
def CommutesWithProjector (evolution : H n →ₗ[ℂ] H n)
    (c : Submodule ℂ (H n)) : Prop :=
  ∀ x : H n, projL c (evolution x) = evolution (projL c x)

theorem commutesWithProjector_id (c : Submodule ℂ (H n)) :
    CommutesWithProjector (LinearMap.id : H n →ₗ[ℂ] H n) c := fun _ => rfl

theorem CommutesWithProjector.comp {c : Submodule ℂ (H n)}
    {later earlier : H n →ₗ[ℂ] H n}
    (hlater : CommutesWithProjector later c)
    (hearlier : CommutesWithProjector earlier c) :
    CommutesWithProjector (later.comp earlier) c := by
  intro x
  change projL c (later (earlier x)) = later (earlier (projL c x))
  calc
    projL c (later (earlier x)) = later (projL c (earlier x)) := hlater _
    _ = later (earlier (projL c x)) := by rw [hearlier x]

/-- A linear evolution commutes with every cell projector of a perspective. -/
def CommutesWithPerspectiveProjectors (D : Perspective n)
    (evolution : H n →ₗ[ℂ] H n) : Prop :=
  ∀ c : (Projective.interface n).Cell D, CommutesWithProjector evolution c.val

theorem commutesWithPerspectiveProjectors_id (D : Perspective n) :
    CommutesWithPerspectiveProjectors D (LinearMap.id : H n →ₗ[ℂ] H n) :=
  fun c => commutesWithProjector_id c.val

theorem CommutesWithPerspectiveProjectors.comp {D : Perspective n}
    {later earlier : H n →ₗ[ℂ] H n}
    (hlater : CommutesWithPerspectiveProjectors D later)
    (hearlier : CommutesWithPerspectiveProjectors D earlier) :
    CommutesWithPerspectiveProjectors D (later.comp earlier) :=
  fun c => (hlater c).comp (hearlier c)

/-- Commutation with a projector implies commutation with its orthogonal
complement projector. -/
theorem CommutesWithProjector.orthogonalComplement
    {evolution : H n →ₗ[ℂ] H n} {c : Submodule ℂ (H n)}
    (hcomm : CommutesWithProjector evolution c) :
    CommutesWithProjector evolution cᗮ := by
  intro x
  change (cᗮ.starProjection : H n →ₗ[ℂ] H n) (evolution x) =
    evolution ((cᗮ.starProjection : H n →ₗ[ℂ] H n) x)
  rw [Submodule.starProjection_orthogonal']
  change evolution x - projL c (evolution x) = evolution (x - projL c x)
  rw [hcomm x, map_sub]

/-- An isometric evolution commuting with a projector preserves its Born
weight. -/
theorem bornWeight_preserved_of_commutesWithProjector
    (evolution : H n →ₗ[ℂ] H n) (hIsometry : ∀ x : H n, ‖evolution x‖ = ‖x‖)
    (c : Submodule ℂ (H n)) (hcomm : CommutesWithProjector evolution c)
    (x : H n) :
    ‖projL c x‖ ^ 2 = ‖projL c (evolution x)‖ ^ 2 := by
  rw [hcomm x, hIsometry]

theorem presentBornWeight_preserved_of_commutesWithPerspectiveProjectors
    (D : Perspective n) (evolution : H n →ₗ[ℂ] H n)
    (hIsometry : ∀ x : H n, ‖evolution x‖ = ‖x‖)
    (hcomm : CommutesWithPerspectiveProjectors D evolution)
    (x : H n) (c : (Projective.interface n).Cell D) :
    ‖projL c.val x‖ ^ 2 = ‖projL c.val (evolution x)‖ ^ 2 :=
  bornWeight_preserved_of_commutesWithProjector evolution hIsometry c.val (hcomm c) x

/-- A continuation whose isometric evolution commutes with each present
projector. -/
structure ProjectorCommutingProjectiveContinuation
    (n : Nat) (future present : Perspective n) where
  step : ContinuationStep (Projective.interface n) future present
  evolution : H n →ₗ[ℂ] H n
  isometry : ∀ x : H n, ‖evolution x‖ = ‖x‖
  commutes_present_projectors : CommutesWithPerspectiveProjectors present evolution

namespace ProjectorCommutingProjectiveContinuation

theorem presentBornWeight_preserved {future present : Perspective n}
    (W : ProjectorCommutingProjectiveContinuation n future present)
    (x : H n) (c : (Projective.interface n).Cell present) :
    ‖projL c.val x‖ ^ 2 = ‖projL c.val (W.evolution x)‖ ^ 2 :=
  presentBornWeight_preserved_of_commutesWithPerspectiveProjectors present W.evolution
    W.isometry W.commutes_present_projectors x c

/-- Add a separately justified accessible-record observable. -/
def toUniform {future present : Perspective n}
    (W : ProjectorCommutingProjectiveContinuation n future present)
    (R : Type) (record : H n → R)
    (hRecord : PreservesRecordObservable record W.evolution) :
    UniformRecordRespectingProjectiveContinuation n future present where
  Record := R
  step := W.step
  evolution := W.evolution
  isometry := W.isometry
  accessibleRecord := record
  record_preserved := hRecord
  presentBornWeight_preserved := fun x c => W.presentBornWeight_preserved x c

@[simp] theorem toUniform_evolution_apply {future present : Perspective n}
    (W : ProjectorCommutingProjectiveContinuation n future present)
    (R : Type) (record : H n → R)
    (hRecord : PreservesRecordObservable record W.evolution) (x : H n) :
    (W.toUniform R record hRecord).evolution x = W.evolution x := rfl

theorem toUniform_presentBornWeight_preserved {future present : Perspective n}
    (W : ProjectorCommutingProjectiveContinuation n future present)
    (R : Type) (record : H n → R)
    (hRecord : PreservesRecordObservable record W.evolution)
    (x : H n) (c : (Projective.interface n).Cell present) :
    ‖projL c.val x‖ ^ 2 = ‖projL c.val ((W.toUniform R record hRecord).evolution x)‖ ^ 2 :=
  (W.toUniform R record hRecord).presentBornWeight_preserved x c

theorem continuatorCredence_eq_physicalBornRatio {future present : Perspective n}
    (W : ProjectorCommutingProjectiveContinuation n future present)
    (R : Type) (record : H n → R)
    (hRecord : PreservesRecordObservable record W.evolution)
    (F : RationalExpectationFamily (Projective.interface n))
    (hn3 : 3 ≤ n) (hinv : RefinementInvariantLocal F.V)
    (x : H n) (hx : ‖x‖ = 1)
    (hNul : AxNul (EverettianProbability.BornCalibration.canonicalWeight
      (projectiveConcreteExpectationFamily F)) (W.evolution x))
    (c : (Projective.interface n).Cell present) (hc : ‖projL c.val x‖ ^ 2 ≠ 0)
    (i : (Projective.interface n).Cell future) :
    W.step.continuatorCredence F c i =
      (W.toUniform R record hRecord).physicalContinuatorBornRatio x c i :=
  (W.toUniform R record hRecord).continuatorCredence_eq_physicalContinuatorBornRatio
    F hn3 hinv x hx hNul c hc i

theorem coupleU_b0 : coupleU (b 0 : H 3) = (b 0 : H 3) := by
  unfold coupleU
  simp

theorem coupleU_commutes_label0Line :
    CommutesWithProjector coupleULin label0Line := by
  intro x
  change projL label0Line (coupleU x) = coupleU (projL label0Line x)
  unfold label0Line
  rw [projL_singleton_unit _ _ b0_unit, projL_singleton_unit _ _ b0_unit,
    inner_b0_coupleU, coupleU_smul, coupleU_b0]

theorem coupleU_commutes_label1Space :
    CommutesWithProjector coupleULin label1Space := by
  unfold label1Space
  exact coupleU_commutes_label0Line.orthogonalComplement

theorem coupleU_commutes_coarsePerspectiveProjectors :
    CommutesWithPerspectiveProjectors coarsePerspective coupleULin := by
  intro c
  rcases c with ⟨c, hc⟩
  rw [coarsePerspective_cells_eq] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with h0 | h1
  · subst c; exact coupleU_commutes_label0Line
  · subst c; exact coupleU_commutes_label1Space

def recordNeutralProjectorCommutingContinuation :
    ProjectorCommutingProjectiveContinuation 3 finePerspective coarsePerspective where
  step := recordNeutralContinuationStep
  evolution := coupleULin
  isometry := coupleU_isometry
  commutes_present_projectors := coupleU_commutes_coarsePerspectiveProjectors

def recordNeutralUniformFromProjectorCommutation :
    UniformRecordRespectingProjectiveContinuation 3 finePerspective coarsePerspective :=
  recordNeutralProjectorCommutingContinuation.toUniform (ℝ × ℝ)
    accessibleRecord accessibleRecord_coupleU

@[simp] theorem recordNeutralUniformFromProjectorCommutation_evolution (x : H 3) :
    recordNeutralUniformFromProjectorCommutation.evolution x = coupleU x := rfl

theorem recordNeutralUniformFromProjectorCommutation_evolutionEquivalent :
    UniformRecordRespectingProjectiveContinuation.EvolutionEquivalent
      recordNeutralUniformFromProjectorCommutation recordNeutralUniformPhysicalContinuation :=
  fun _ => rfl

theorem recordNeutralUniformFromProjectorCommutation_recordPreserved (x : H 3) :
    recordNeutralUniformFromProjectorCommutation.accessibleRecord x =
      recordNeutralUniformFromProjectorCommutation.accessibleRecord
        (recordNeutralUniformFromProjectorCommutation.evolution x) :=
  recordNeutralUniformFromProjectorCommutation.record_preserved x

theorem recordNeutralProjectorCommuting_anc0PhysicalBornRatio_eq :
    recordNeutralUniformFromProjectorCommutation.physicalContinuatorBornRatio psiBefore
      recordNeutralPresentComplementCell recordNeutralFutureAnc0Cell = 9 / 25 := by
  unfold UniformRecordRespectingProjectiveContinuation.physicalContinuatorBornRatio
  have hparent : (Projective.interface 3).parentCell
      recordNeutralUniformFromProjectorCommutation.step.refinement
      recordNeutralFutureAnc0Cell = recordNeutralPresentComplementCell :=
    recordNeutral_parent_anc0
  rw [if_pos hparent]
  change ‖projL anc0Line (coupleU psiBefore)‖ ^ 2 / ‖projL label1Space psiBefore‖ ^ 2 = 9 / 25
  rw [coupleU_psiBefore, weight_anc0_after, weight_label1Space_before]
  norm_num

theorem recordNeutralProjectorCommuting_anc1PhysicalBornRatio_eq :
    recordNeutralUniformFromProjectorCommutation.physicalContinuatorBornRatio psiBefore
      recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell = 16 / 25 := by
  unfold UniformRecordRespectingProjectiveContinuation.physicalContinuatorBornRatio
  have hparent : (Projective.interface 3).parentCell
      recordNeutralUniformFromProjectorCommutation.step.refinement
      recordNeutralFutureAnc1Cell = recordNeutralPresentComplementCell :=
    recordNeutral_parent_anc1
  rw [if_pos hparent]
  change ‖projL anc1Line (coupleU psiBefore)‖ ^ 2 / ‖projL label1Space psiBefore‖ ^ 2 = 16 / 25
  rw [coupleU_psiBefore, weight_anc1_after, weight_label1Space_before]
  norm_num

theorem recordNeutralProjectorCommuting_anc1Credence_eq
    (F : RationalExpectationFamily (Projective.interface 3))
    (hinv : RefinementInvariantLocal F.V)
    (hNul : AxNul (EverettianProbability.BornCalibration.canonicalWeight
      (projectiveConcreteExpectationFamily F)) psiAfter) :
    recordNeutralProjectorCommutingContinuation.step.continuatorCredence F
      recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell = 16 / 25 := by
  have hc : ‖projL recordNeutralPresentComplementCell.val psiBefore‖ ^ 2 ≠ 0 := by
    change ‖projL label1Space psiBefore‖ ^ 2 ≠ 0
    rw [weight_label1Space_before]
    norm_num
  have hNul' : AxNul (EverettianProbability.BornCalibration.canonicalWeight
      (projectiveConcreteExpectationFamily F))
      (recordNeutralProjectorCommutingContinuation.evolution psiBefore) := by
    change AxNul (EverettianProbability.BornCalibration.canonicalWeight
      (projectiveConcreteExpectationFamily F)) (coupleU psiBefore)
    simpa [coupleU_psiBefore] using hNul
  have h := recordNeutralProjectorCommutingContinuation.continuatorCredence_eq_physicalBornRatio
    (ℝ × ℝ) accessibleRecord accessibleRecord_coupleU F (by norm_num) hinv
    psiBefore psiBefore_norm hNul'
    recordNeutralPresentComplementCell hc recordNeutralFutureAnc1Cell
  have hratio :
      (recordNeutralProjectorCommutingContinuation.toUniform
        (ℝ × ℝ) accessibleRecord accessibleRecord_coupleU).physicalContinuatorBornRatio psiBefore
            recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell = 16 / 25 := by
    exact recordNeutralProjectorCommuting_anc1PhysicalBornRatio_eq
  exact h.trans hratio

theorem recordNeutralProjectorCommutation_integratedWitness :
    CommutesWithPerspectiveProjectors coarsePerspective coupleULin ∧
    (∀ (x : H 3) (c : (Projective.interface 3).Cell coarsePerspective),
      ‖projL c.val x‖ ^ 2 = ‖projL c.val (coupleU x)‖ ^ 2) ∧
    UniformRecordRespectingProjectiveContinuation.EvolutionEquivalent
      recordNeutralUniformFromProjectorCommutation recordNeutralUniformPhysicalContinuation ∧
    recordNeutralUniformFromProjectorCommutation.physicalContinuatorBornRatio psiBefore
      recordNeutralPresentComplementCell recordNeutralFutureAnc0Cell = 9 / 25 ∧
    recordNeutralUniformFromProjectorCommutation.physicalContinuatorBornRatio psiBefore
      recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell = 16 / 25 := by
  exact ⟨coupleU_commutes_coarsePerspectiveProjectors,
    fun x c => recordNeutralProjectorCommutingContinuation.presentBornWeight_preserved x c,
    recordNeutralUniformFromProjectorCommutation_evolutionEquivalent,
    recordNeutralProjectorCommuting_anc0PhysicalBornRatio_eq,
    recordNeutralProjectorCommuting_anc1PhysicalBornRatio_eq⟩

end ProjectorCommutingProjectiveContinuation
end
end EverettianProbability.Abstract
