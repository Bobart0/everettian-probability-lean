import EverettianProbability.Diachronic.UniformContinuationComposition

/-!
**FR.** # Associativite extensionnelle des continuations physiques

Les deux parenthesages d'une triple continuation peuvent embarquer des
temoins de raffinement differents. Ce module les compare donc
extensionnellement : meme evolution sur tout etat, meme record ancien et
memes poids finaux, sans postuler une egalite entre ces temoins.

**EN.** # Extensional associativity of physical continuations

The two parenthesizations of a triple continuation can contain different
refinement witnesses. This module therefore compares them extensionally:
same evolution on every state, same earliest record, and same final weights,
without postulating equality of those witnesses.
-/

namespace EverettianProbability.Abstract

open QuantumFoundations.BornRule Gleason
open EverettianProbability.PhysicalRefinement
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : Nat}

namespace UniformRecordRespectingProjectiveContinuation

/-- Physical equivalence requiring equal state evolution on every input. -/
def EvolutionEquivalent {future present : Perspective n}
    (A B : UniformRecordRespectingProjectiveContinuation n future present) : Prop :=
  ∀ x : H n, A.evolution x = B.evolution x

theorem EvolutionEquivalent.refl {future present : Perspective n}
    (A : UniformRecordRespectingProjectiveContinuation n future present) :
    EvolutionEquivalent A A := fun _ => rfl

theorem EvolutionEquivalent.symm {future present : Perspective n}
    {A B : UniformRecordRespectingProjectiveContinuation n future present}
    (h : EvolutionEquivalent A B) : EvolutionEquivalent B A := fun x => (h x).symm

theorem EvolutionEquivalent.trans {future present : Perspective n}
    {A B C : UniformRecordRespectingProjectiveContinuation n future present}
    (hAB : EvolutionEquivalent A B) (hBC : EvolutionEquivalent B C) :
    EvolutionEquivalent A C := fun x => (hAB x).trans (hBC x)

theorem finalBornWeight_eq_of_evolutionEquivalent {future present : Perspective n}
    {A B : UniformRecordRespectingProjectiveContinuation n future present}
    (h : EvolutionEquivalent A B) (x : H n) (c : (Projective.interface n).Cell future) :
    ‖projL c.val (A.evolution x)‖ ^ 2 = ‖projL c.val (B.evolution x)‖ ^ 2 := by rw [h x]

theorem atState_stateAfter_eq_of_evolutionEquivalent {future present : Perspective n}
    {A B : UniformRecordRespectingProjectiveContinuation n future present}
    (h : EvolutionEquivalent A B) (x : H n) (hx : ‖x‖ = 1) :
    (A.atState x hx).stateAfter = (B.atState x hx).stateAfter := h x

theorem evolved_normalized {future present : Perspective n}
    (A : UniformRecordRespectingProjectiveContinuation n future present)
    (x : H n) (hx : ‖x‖ = 1) : ‖A.evolution x‖ = 1 := by rw [A.isometry x, hx]

theorem laterPair_preserves_earliestRecord
    {future middle₂ middle₁ present : Perspective n}
    (third : UniformRecordRespectingProjectiveContinuation n future middle₂)
    (second : UniformRecordRespectingProjectiveContinuation n middle₂ middle₁)
    (first : UniformRecordRespectingProjectiveContinuation n middle₁ present)
    (hThirdSecond : PreservesRecordObservable second.accessibleRecord third.evolution)
    (hSecondFirst : PreservesRecordObservable first.accessibleRecord second.evolution)
    (hThirdFirst : PreservesRecordObservable first.accessibleRecord third.evolution) :
    PreservesRecordObservable first.accessibleRecord (third.trans second hThirdSecond).evolution := by
  intro x
  change first.accessibleRecord x = first.accessibleRecord (third.evolution (second.evolution x))
  calc
    first.accessibleRecord x = first.accessibleRecord (second.evolution x) := hSecondFirst x
    _ = first.accessibleRecord (third.evolution (second.evolution x)) := hThirdFirst _

def transLeftAssociated {future middle₂ middle₁ present : Perspective n}
    (third : UniformRecordRespectingProjectiveContinuation n future middle₂)
    (second : UniformRecordRespectingProjectiveContinuation n middle₂ middle₁)
    (first : UniformRecordRespectingProjectiveContinuation n middle₁ present)
    (hThirdSecond : PreservesRecordObservable second.accessibleRecord third.evolution)
    (hSecondFirst : PreservesRecordObservable first.accessibleRecord second.evolution)
    (hThirdFirst : PreservesRecordObservable first.accessibleRecord third.evolution) :
    UniformRecordRespectingProjectiveContinuation n future present :=
  (third.trans second hThirdSecond).trans first
    (laterPair_preserves_earliestRecord third second first hThirdSecond hSecondFirst hThirdFirst)

def transRightAssociated {future middle₂ middle₁ present : Perspective n}
    (third : UniformRecordRespectingProjectiveContinuation n future middle₂)
    (second : UniformRecordRespectingProjectiveContinuation n middle₂ middle₁)
    (first : UniformRecordRespectingProjectiveContinuation n middle₁ present)
    (_hThirdSecond : PreservesRecordObservable second.accessibleRecord third.evolution)
    (hSecondFirst : PreservesRecordObservable first.accessibleRecord second.evolution)
    (hThirdFirst : PreservesRecordObservable first.accessibleRecord third.evolution) :
    UniformRecordRespectingProjectiveContinuation n future present :=
  third.trans (second.trans first hSecondFirst) hThirdFirst

@[simp] theorem transLeftAssociated_evolution_apply {future middle₂ middle₁ present : Perspective n}
    (third : UniformRecordRespectingProjectiveContinuation n future middle₂)
    (second : UniformRecordRespectingProjectiveContinuation n middle₂ middle₁)
    (first : UniformRecordRespectingProjectiveContinuation n middle₁ present)
    (a : PreservesRecordObservable second.accessibleRecord third.evolution)
    (b : PreservesRecordObservable first.accessibleRecord second.evolution)
    (c : PreservesRecordObservable first.accessibleRecord third.evolution) (x : H n) :
    (transLeftAssociated third second first a b c).evolution x = third.evolution (second.evolution (first.evolution x)) := rfl

@[simp] theorem transRightAssociated_evolution_apply {future middle₂ middle₁ present : Perspective n}
    (third : UniformRecordRespectingProjectiveContinuation n future middle₂)
    (second : UniformRecordRespectingProjectiveContinuation n middle₂ middle₁)
    (first : UniformRecordRespectingProjectiveContinuation n middle₁ present)
    (a : PreservesRecordObservable second.accessibleRecord third.evolution)
    (b : PreservesRecordObservable first.accessibleRecord second.evolution)
    (c : PreservesRecordObservable first.accessibleRecord third.evolution) (x : H n) :
    (transRightAssociated third second first a b c).evolution x = third.evolution (second.evolution (first.evolution x)) := rfl

theorem trans_associative_evolutionEquivalent {future middle₂ middle₁ present : Perspective n}
    (third : UniformRecordRespectingProjectiveContinuation n future middle₂)
    (second : UniformRecordRespectingProjectiveContinuation n middle₂ middle₁)
    (first : UniformRecordRespectingProjectiveContinuation n middle₁ present)
    (a : PreservesRecordObservable second.accessibleRecord third.evolution)
    (b : PreservesRecordObservable first.accessibleRecord second.evolution)
    (c : PreservesRecordObservable first.accessibleRecord third.evolution) :
    EvolutionEquivalent (transLeftAssociated third second first a b c)
      (transRightAssociated third second first a b c) := fun _ => rfl

@[simp] theorem transLeftAssociated_accessibleRecord {future middle₂ middle₁ present : Perspective n}
    (third : UniformRecordRespectingProjectiveContinuation n future middle₂)
    (second : UniformRecordRespectingProjectiveContinuation n middle₂ middle₁)
    (first : UniformRecordRespectingProjectiveContinuation n middle₁ present)
    (a : PreservesRecordObservable second.accessibleRecord third.evolution)
    (b : PreservesRecordObservable first.accessibleRecord second.evolution)
    (c : PreservesRecordObservable first.accessibleRecord third.evolution) :
    (transLeftAssociated third second first a b c).accessibleRecord = first.accessibleRecord := rfl

@[simp] theorem transRightAssociated_accessibleRecord {future middle₂ middle₁ present : Perspective n}
    (third : UniformRecordRespectingProjectiveContinuation n future middle₂)
    (second : UniformRecordRespectingProjectiveContinuation n middle₂ middle₁)
    (first : UniformRecordRespectingProjectiveContinuation n middle₁ present)
    (a : PreservesRecordObservable second.accessibleRecord third.evolution)
    (b : PreservesRecordObservable first.accessibleRecord second.evolution)
    (c : PreservesRecordObservable first.accessibleRecord third.evolution) :
    (transRightAssociated third second first a b c).accessibleRecord = first.accessibleRecord := rfl

theorem trans_associative_atState {future middle₂ middle₁ present : Perspective n}
    (third : UniformRecordRespectingProjectiveContinuation n future middle₂)
    (second : UniformRecordRespectingProjectiveContinuation n middle₂ middle₁)
    (first : UniformRecordRespectingProjectiveContinuation n middle₁ present)
    (a : PreservesRecordObservable second.accessibleRecord third.evolution)
    (b : PreservesRecordObservable first.accessibleRecord second.evolution)
    (c : PreservesRecordObservable first.accessibleRecord third.evolution)
    (x : H n) (hx : ‖x‖ = 1) :
    ((transLeftAssociated third second first a b c).atState x hx).stateAfter =
      ((transRightAssociated third second first a b c).atState x hx).stateAfter :=
  atState_stateAfter_eq_of_evolutionEquivalent (trans_associative_evolutionEquivalent third second first a b c) x hx

theorem transLeftAssociated_atState_stateAfter {future middle₂ middle₁ present : Perspective n}
    (third : UniformRecordRespectingProjectiveContinuation n future middle₂)
    (second : UniformRecordRespectingProjectiveContinuation n middle₂ middle₁)
    (first : UniformRecordRespectingProjectiveContinuation n middle₁ present)
    (a : PreservesRecordObservable second.accessibleRecord third.evolution)
    (b : PreservesRecordObservable first.accessibleRecord second.evolution)
    (c : PreservesRecordObservable first.accessibleRecord third.evolution)
    (x : H n) (hx : ‖x‖ = 1) :
    ((transLeftAssociated third second first a b c).atState x hx).stateAfter =
      third.evolution (second.evolution (first.evolution x)) := rfl

theorem transRightAssociated_atState_stateAfter {future middle₂ middle₁ present : Perspective n}
    (third : UniformRecordRespectingProjectiveContinuation n future middle₂)
    (second : UniformRecordRespectingProjectiveContinuation n middle₂ middle₁)
    (first : UniformRecordRespectingProjectiveContinuation n middle₁ present)
    (a : PreservesRecordObservable second.accessibleRecord third.evolution)
    (b : PreservesRecordObservable first.accessibleRecord second.evolution)
    (c : PreservesRecordObservable first.accessibleRecord third.evolution)
    (x : H n) (hx : ‖x‖ = 1) :
    ((transRightAssociated third second first a b c).atState x hx).stateAfter =
      third.evolution (second.evolution (first.evolution x)) := rfl

theorem trans_atState_stateAfter_eq_sequential {future middle present : Perspective n}
    (later : UniformRecordRespectingProjectiveContinuation n future middle)
    (earlier : UniformRecordRespectingProjectiveContinuation n middle present)
    (h : PreservesRecordObservable earlier.accessibleRecord later.evolution)
    (x : H n) (hx : ‖x‖ = 1) :
    ((later.trans earlier h).atState x hx).stateAfter = later.evolution ((earlier.atState x hx).stateAfter) := rfl

theorem trans_atState_eq_later_atEvolvedState {future middle present : Perspective n}
    (later : UniformRecordRespectingProjectiveContinuation n future middle)
    (earlier : UniformRecordRespectingProjectiveContinuation n middle present)
    (h : PreservesRecordObservable earlier.accessibleRecord later.evolution)
    (x : H n) (hx : ‖x‖ = 1) :
    ((later.trans earlier h).atState x hx).stateAfter =
      (later.atState (earlier.evolution x) (earlier.evolved_normalized x hx)).stateAfter := rfl

theorem identity_trans_evolutionEquivalent {future present : Perspective n}
    (W : UniformRecordRespectingProjectiveContinuation n future present) :
    EvolutionEquivalent ((identity future W.Record W.accessibleRecord).trans W
      (preservesRecordObservable_id W.accessibleRecord)) W := fun _ => rfl

theorem trans_identity_evolutionEquivalent {future present : Perspective n}
    (W : UniformRecordRespectingProjectiveContinuation n future present) :
    EvolutionEquivalent (W.trans (identity present W.Record W.accessibleRecord) W.record_preserved) W := fun _ => rfl

def recordNeutralThreeStageLeft : UniformRecordRespectingProjectiveContinuation 3 finePerspective coarsePerspective :=
  transLeftAssociated recordNeutralFutureIdentity recordNeutralUniformPhysicalContinuation recordNeutralPresentIdentity
    (preservesRecordObservable_id EverettianProbability.PhysicalRefinement.accessibleRecord)
    accessibleRecord_coupleU
    (preservesRecordObservable_id EverettianProbability.PhysicalRefinement.accessibleRecord)

def recordNeutralThreeStageRight : UniformRecordRespectingProjectiveContinuation 3 finePerspective coarsePerspective :=
  transRightAssociated recordNeutralFutureIdentity recordNeutralUniformPhysicalContinuation recordNeutralPresentIdentity
    (preservesRecordObservable_id EverettianProbability.PhysicalRefinement.accessibleRecord)
    accessibleRecord_coupleU
    (preservesRecordObservable_id EverettianProbability.PhysicalRefinement.accessibleRecord)

theorem recordNeutralThreeStageLeft_evolution (x : H 3) : recordNeutralThreeStageLeft.evolution x = coupleU x := rfl
theorem recordNeutralThreeStageRight_evolution (x : H 3) : recordNeutralThreeStageRight.evolution x = coupleU x := rfl

theorem recordNeutralThreeStage_associativityWitness :
    EvolutionEquivalent recordNeutralThreeStageLeft recordNeutralThreeStageRight ∧
    (∀ x : H 3, recordNeutralThreeStageLeft.evolution x = coupleU x) ∧
    (∀ x : H 3, recordNeutralThreeStageRight.evolution x = coupleU x) ∧
    (∀ (x : H 3) (hx : ‖x‖ = 1),
      (recordNeutralThreeStageLeft.atState x hx).stateAfter =
        (recordNeutralThreeStageRight.atState x hx).stateAfter) ∧
    (∀ (x : H 3) (c : (Projective.interface 3).Cell coarsePerspective),
      ‖projL c.val (recordNeutralThreeStageLeft.evolution x)‖ ^ 2 =
        ‖projL c.val (recordNeutralThreeStageRight.evolution x)‖ ^ 2) := by
  refine ⟨?_, recordNeutralThreeStageLeft_evolution, recordNeutralThreeStageRight_evolution, ?_, ?_⟩
  · exact trans_associative_evolutionEquivalent recordNeutralFutureIdentity recordNeutralUniformPhysicalContinuation recordNeutralPresentIdentity
      (preservesRecordObservable_id EverettianProbability.PhysicalRefinement.accessibleRecord)
      accessibleRecord_coupleU
      (preservesRecordObservable_id EverettianProbability.PhysicalRefinement.accessibleRecord)
  · intro x hx
    change recordNeutralThreeStageLeft.evolution x =
      recordNeutralThreeStageRight.evolution x
    rw [recordNeutralThreeStageLeft_evolution,
      recordNeutralThreeStageRight_evolution]
  · intro x c
    rw [recordNeutralThreeStageLeft_evolution,
      recordNeutralThreeStageRight_evolution]

end UniformRecordRespectingProjectiveContinuation
end
end EverettianProbability.Abstract
