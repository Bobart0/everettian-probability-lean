import EverettianProbability.Diachronic.UniformRecordRespectingContinuation

/-!
**FR.** # Identite et composition des continuations respectant le record

Ce module ferme par identite et composition compatible la classe des
continuations projectives uniformement respectueuses du record. La
compatibilite exige explicitement que l'evolution tardive preserve aussi le
record retenu par l'etape anterieure.

La conservation grossiere n'est pas supposee : elle est derivee de la
conservation de tous les poids intermediaires et de l'additivite de Grain sur
les fibres du raffinement. Cela ne montre pas que toute evolution physique ou
tout raffinement abstrait appartient a cette classe.

**EN.** # Identity and composition of record-respecting continuations

This module closes the class of uniformly record-respecting projective
continuations under identity and compatible composition. Compatibility
explicitly requires the later evolution to preserve the earlier step's
accessible record as well.

Coarse preservation is not assumed: it is derived from preservation of all
intermediate weights and Grain additivity over refinement fibres. This does
not show that every physical evolution or abstract refinement belongs to the
class.
-/

namespace EverettianProbability.Abstract

open QuantumFoundations.BornRule Gleason
open EverettianProbability.PhysicalRefinement
open QuantumFoundations.ProbabilityAPI
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : Nat}

/-- A linear evolution preserves a specified record observable on every state. -/
def PreservesRecordObservable {R : Type}
    (record : H n → R) (evolution : H n →ₗ[ℂ] H n) : Prop :=
  ∀ x : H n, record x = record (evolution x)

theorem preservesRecordObservable_id {R : Type} (record : H n → R) :
    PreservesRecordObservable record (LinearMap.id : H n →ₗ[ℂ] H n) := by
  intro x
  rfl

theorem PreservesRecordObservable.comp {R : Type}
    (record : H n → R) (later earlier : H n →ₗ[ℂ] H n)
    (hearlier : PreservesRecordObservable record earlier)
    (hlater : PreservesRecordObservable record later) :
    PreservesRecordObservable record (later.comp earlier) := by
  intro x
  calc
    record x = record (earlier x) := hearlier x
    _ = record (later (earlier x)) := hlater (earlier x)
    _ = record ((later.comp earlier) x) := rfl

namespace UniformRecordRespectingProjectiveContinuation

/-- Identity continuation at one projective perspective. -/
def identity (D : Perspective n) (R : Type) (record : H n → R) :
    UniformRecordRespectingProjectiveContinuation n D D where
  Record := R
  step := { refinement := (Projective.interface n).refl D }
  evolution := LinearMap.id
  isometry := by intro x; rfl
  accessibleRecord := record
  record_preserved := by intro x; rfl
  presentBornWeight_preserved := by intro x c; rfl

@[simp] theorem identity_evolution_apply
    (D : Perspective n) (R : Type) (record : H n → R) (x : H n) :
    (identity D R record).evolution x = x := rfl

theorem identity_record_preserved
    (D : Perspective n) (R : Type) (record : H n → R) :
    PreservesRecordObservable record (identity D R record).evolution :=
  preservesRecordObservable_id record

theorem identity_presentBornWeight_preserved
    (D : Perspective n) (R : Type) (record : H n → R)
    (x : H n) (c : (Projective.interface n).Cell D) :
    ‖projL c.val x‖ ^ 2 = ‖projL c.val ((identity D R record).evolution x)‖ ^ 2 := rfl

/-- Fine-cell Born-weight preservation implies coarse-cell preservation by
Grain additivity over a projective refinement fibre. -/
theorem preserves_coarseBornWeight_of_preserves_fineBornWeight
    {fine coarse : Perspective n} (r : Refines fine coarse)
    (evolution : H n →ₗ[ℂ] H n)
    (hFine : ∀ (x : H n) (i : (Projective.interface n).Cell fine),
      ‖projL i.val x‖ ^ 2 = ‖projL i.val (evolution x)‖ ^ 2)
    (x : H n) (c : (Projective.interface n).Cell coarse) :
    ‖projL c.val x‖ ^ 2 = ‖projL c.val (evolution x)‖ ^ 2 := by
  have hx := Projective.grain_of_axGrain
    (QuantumFoundations.ProbabilityAPI.BornRule.E₀ x)
    (QuantumFoundations.ProbabilityAPI.BornRule.E₀_isGrain x) r c
  have hy := Projective.grain_of_axGrain
    (QuantumFoundations.ProbabilityAPI.BornRule.E₀ (evolution x))
    (QuantumFoundations.ProbabilityAPI.BornRule.E₀_isGrain (evolution x)) r c
  simp only [Projective.interface_weight_apply,
    QuantumFoundations.ProbabilityAPI.BornRule.E₀] at hx hy
  calc
    ‖projL c.val x‖ ^ 2 = ∑ i : (Projective.interface n).Cell fine,
        if (Projective.interface n).parentCell r i = c then ‖projL i.val x‖ ^ 2 else 0 := hx
    _ = ∑ i : (Projective.interface n).Cell fine,
        if (Projective.interface n).parentCell r i = c then
          ‖projL i.val (evolution x)‖ ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hp : (Projective.interface n).parentCell r i = c
      · rw [if_pos hp, if_pos hp, hFine x i]
      · have hsub :
            ¬ (⟨parentOf r i.val, parentOf_mem r i.property⟩ :
              (Projective.interface n).Cell coarse) = c := by
          simpa [Projective.interface_parentCell_apply] using hp
        rw [Projective.interface_parentCell_apply]
        simp only [if_neg hsub]
    _ = ‖projL c.val (evolution x)‖ ^ 2 := hy.symm

/-- Compatible composition retaining the earlier accessible record. -/
def trans {future middle present : Perspective n}
    (later : UniformRecordRespectingProjectiveContinuation n future middle)
    (earlier : UniformRecordRespectingProjectiveContinuation n middle present)
    (hlaterRecord : PreservesRecordObservable earlier.accessibleRecord later.evolution) :
    UniformRecordRespectingProjectiveContinuation n future present where
  Record := earlier.Record
  step := later.step.trans earlier.step
  evolution := later.evolution.comp earlier.evolution
  isometry := by
    intro x
    change ‖later.evolution (earlier.evolution x)‖ = ‖x‖
    rw [later.isometry, earlier.isometry]
  accessibleRecord := earlier.accessibleRecord
  record_preserved := by
    intro x
    change earlier.accessibleRecord x =
      earlier.accessibleRecord (later.evolution (earlier.evolution x))
    calc
      earlier.accessibleRecord x = earlier.accessibleRecord (earlier.evolution x) :=
        earlier.record_preserved x
      _ = earlier.accessibleRecord (later.evolution (earlier.evolution x)) :=
        hlaterRecord (earlier.evolution x)
  presentBornWeight_preserved := by
    intro x c
    change ‖projL c.val x‖ ^ 2 = ‖projL c.val (later.evolution (earlier.evolution x))‖ ^ 2
    calc
      ‖projL c.val x‖ ^ 2 = ‖projL c.val (earlier.evolution x)‖ ^ 2 :=
        earlier.presentBornWeight_preserved x c
      _ = ‖projL c.val (later.evolution (earlier.evolution x))‖ ^ 2 :=
        preserves_coarseBornWeight_of_preserves_fineBornWeight
          earlier.step.refinement later.evolution later.presentBornWeight_preserved
          (earlier.evolution x) c

@[simp] theorem trans_evolution_apply {future middle present : Perspective n}
    (later : UniformRecordRespectingProjectiveContinuation n future middle)
    (earlier : UniformRecordRespectingProjectiveContinuation n middle present)
    (hlaterRecord : PreservesRecordObservable earlier.accessibleRecord later.evolution)
    (x : H n) :
    (later.trans earlier hlaterRecord).evolution x = later.evolution (earlier.evolution x) := rfl

@[simp] theorem trans_accessibleRecord {future middle present : Perspective n}
    (later : UniformRecordRespectingProjectiveContinuation n future middle)
    (earlier : UniformRecordRespectingProjectiveContinuation n middle present)
    (hlaterRecord : PreservesRecordObservable earlier.accessibleRecord later.evolution) :
    (later.trans earlier hlaterRecord).accessibleRecord = earlier.accessibleRecord := rfl

theorem trans_isometry {future middle present : Perspective n}
    (later : UniformRecordRespectingProjectiveContinuation n future middle)
    (earlier : UniformRecordRespectingProjectiveContinuation n middle present)
    (hlaterRecord : PreservesRecordObservable earlier.accessibleRecord later.evolution)
    (x : H n) : ‖(later.trans earlier hlaterRecord).evolution x‖ = ‖x‖ :=
  (later.trans earlier hlaterRecord).isometry x

theorem trans_record_preserved {future middle present : Perspective n}
    (later : UniformRecordRespectingProjectiveContinuation n future middle)
    (earlier : UniformRecordRespectingProjectiveContinuation n middle present)
    (hlaterRecord : PreservesRecordObservable earlier.accessibleRecord later.evolution)
    (x : H n) : earlier.accessibleRecord x =
      earlier.accessibleRecord ((later.trans earlier hlaterRecord).evolution x) :=
  (later.trans earlier hlaterRecord).record_preserved x

theorem trans_presentBornWeight_preserved {future middle present : Perspective n}
    (later : UniformRecordRespectingProjectiveContinuation n future middle)
    (earlier : UniformRecordRespectingProjectiveContinuation n middle present)
    (hlaterRecord : PreservesRecordObservable earlier.accessibleRecord later.evolution)
    (x : H n) (c : (Projective.interface n).Cell present) :
    ‖projL c.val x‖ ^ 2 = ‖projL c.val ((later.trans earlier hlaterRecord).evolution x)‖ ^ 2 :=
  (later.trans earlier hlaterRecord).presentBornWeight_preserved x c

@[simp] theorem trans_atState_stateAfter {future middle present : Perspective n}
    (later : UniformRecordRespectingProjectiveContinuation n future middle)
    (earlier : UniformRecordRespectingProjectiveContinuation n middle present)
    (hlaterRecord : PreservesRecordObservable earlier.accessibleRecord later.evolution)
    (x : H n) (hx : ‖x‖ = 1) :
    ((later.trans earlier hlaterRecord).atState x hx).stateAfter =
      later.evolution (earlier.evolution x) := rfl

theorem trans_atState_after_normalized {future middle present : Perspective n}
    (later : UniformRecordRespectingProjectiveContinuation n future middle)
    (earlier : UniformRecordRespectingProjectiveContinuation n middle present)
    (hlaterRecord : PreservesRecordObservable earlier.accessibleRecord later.evolution)
    (x : H n) (hx : ‖x‖ = 1) :
    ‖((later.trans earlier hlaterRecord).atState x hx).stateAfter‖ = 1 :=
  (later.trans earlier hlaterRecord).atState_after_normalized x hx

theorem identity_trans_evolution {future present : Perspective n}
    (W : UniformRecordRespectingProjectiveContinuation n future present) (x : H n) :
    ((identity future W.Record W.accessibleRecord).trans W
      (preservesRecordObservable_id W.accessibleRecord)).evolution x = W.evolution x := rfl

theorem trans_identity_evolution {future present : Perspective n}
    (W : UniformRecordRespectingProjectiveContinuation n future present) (x : H n) :
    (W.trans (identity present W.Record W.accessibleRecord) W.record_preserved).evolution x =
      W.evolution x := rfl

def recordNeutralFutureIdentity :
    UniformRecordRespectingProjectiveContinuation 3 finePerspective finePerspective :=
  identity finePerspective (ℝ × ℝ)
    EverettianProbability.PhysicalRefinement.accessibleRecord

def recordNeutralPresentIdentity :
    UniformRecordRespectingProjectiveContinuation 3 coarsePerspective coarsePerspective :=
  identity coarsePerspective (ℝ × ℝ)
    EverettianProbability.PhysicalRefinement.accessibleRecord

def recordNeutralWithFutureIdentity :
    UniformRecordRespectingProjectiveContinuation 3 finePerspective coarsePerspective :=
  recordNeutralFutureIdentity.trans recordNeutralUniformPhysicalContinuation
    (preservesRecordObservable_id
      EverettianProbability.PhysicalRefinement.accessibleRecord)

def recordNeutralWithPresentIdentity :
    UniformRecordRespectingProjectiveContinuation 3 finePerspective coarsePerspective :=
  recordNeutralUniformPhysicalContinuation.trans recordNeutralPresentIdentity
    accessibleRecord_coupleU

theorem recordNeutralWithFutureIdentity_evolution (x : H 3) :
    recordNeutralWithFutureIdentity.evolution x = coupleU x := rfl

theorem recordNeutralWithPresentIdentity_evolution (x : H 3) :
    recordNeutralWithPresentIdentity.evolution x = coupleU x := rfl

theorem recordNeutralWithFutureIdentity_record (x : H 3) :
    recordNeutralWithFutureIdentity.accessibleRecord x =
      EverettianProbability.PhysicalRefinement.accessibleRecord x := rfl

theorem recordNeutralWithPresentIdentity_record (x : H 3) :
    recordNeutralWithPresentIdentity.accessibleRecord x =
      EverettianProbability.PhysicalRefinement.accessibleRecord x := rfl

theorem recordNeutralUniformContinuation_identityClosureWitness :
    (∀ x : H 3, recordNeutralWithFutureIdentity.evolution x = coupleU x) ∧
    (∀ x : H 3, recordNeutralWithPresentIdentity.evolution x = coupleU x) ∧
    (∀ (x : H 3) (c : (Projective.interface 3).Cell coarsePerspective),
      ‖projL c.val x‖ ^ 2 = ‖projL c.val (recordNeutralWithFutureIdentity.evolution x)‖ ^ 2) ∧
    (∀ (x : H 3) (c : (Projective.interface 3).Cell coarsePerspective),
      ‖projL c.val x‖ ^ 2 = ‖projL c.val (recordNeutralWithPresentIdentity.evolution x)‖ ^ 2) := by
  exact ⟨recordNeutralWithFutureIdentity_evolution,
    recordNeutralWithPresentIdentity_evolution,
    fun x c => recordNeutralWithFutureIdentity.presentBornWeight_preserved x c,
    fun x c => recordNeutralWithPresentIdentity.presentBornWeight_preserved x c⟩

end UniformRecordRespectingProjectiveContinuation

end
end EverettianProbability.Abstract
