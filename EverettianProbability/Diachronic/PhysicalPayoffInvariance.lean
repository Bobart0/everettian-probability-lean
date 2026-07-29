import EverettianProbability.Diachronic.ProjectorCommutingContinuation
import EverettianProbability.PhysicalRefinement.Nonvacuity

/-!
**FR.** # Invariance physique des consequences portees par le record

La commutation projective et l'isometrie conservent les poids de chaque
cellule presente; avec Grain, elles conservent donc les esperances de Born
des consequences portees par le record. Cette realisation physique reste
distincte de la premisse normative universelle d'invariance.

**EN.** # Physical invariance of record-based consequences

Projector commutation and isometry preserve every present-cell weight; with
Grain they therefore preserve Born expectations of record-based
consequences. This physical realization remains distinct from the universal
normative invariance premise.
-/

namespace EverettianProbability.Abstract

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core
open EverettianProbability.PhysicalRefinement
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : Nat}

def PreservesBornExpectationOnPerspective (D : Perspective n)
    (evolution : H n →ₗ[ℂ] H n) : Prop :=
  ∀ (x : H n) (a : EverettianProbability.Core.Act n),
    EverettianProbability.Refinement.bornExpectation (evolution x) D a =
      EverettianProbability.Refinement.bornExpectation x D a

theorem preservesBornExpectationOnPerspective_id (D : Perspective n) :
    PreservesBornExpectationOnPerspective D (LinearMap.id : H n →ₗ[ℂ] H n) := fun _ _ => rfl

theorem PreservesBornExpectationOnPerspective.comp {D : Perspective n}
    {later earlier : H n →ₗ[ℂ] H n}
    (hlater : PreservesBornExpectationOnPerspective D later)
    (hearlier : PreservesBornExpectationOnPerspective D earlier) :
    PreservesBornExpectationOnPerspective D (later.comp earlier) := by
  intro x a
  calc
    EverettianProbability.Refinement.bornExpectation (later (earlier x)) D a =
      EverettianProbability.Refinement.bornExpectation (earlier x) D a := hlater _ _
    _ = EverettianProbability.Refinement.bornExpectation x D a := hearlier _ _

theorem bornExpectation_congr_of_agreeOn (x : H n) (D : Perspective n)
    {a b : EverettianProbability.Core.Act n}
    (h : EverettianProbability.Core.Act.AgreeOn D a b) :
    EverettianProbability.Refinement.bornExpectation x D a =
      EverettianProbability.Refinement.bornExpectation x D b := by
  unfold EverettianProbability.Refinement.bornExpectation
  apply Finset.sum_congr rfl
  intro c hc
  rw [h c hc]

theorem preservesBornExpectation_of_preservesCellBornWeights
    (D : Perspective n) (evolution : H n →ₗ[ℂ] H n)
    (hWeight : ∀ (x : H n) (c : (Projective.interface n).Cell D),
      ‖projL c.val x‖ ^ 2 = ‖projL c.val (evolution x)‖ ^ 2) :
    PreservesBornExpectationOnPerspective D evolution := by
  intro x a
  unfold EverettianProbability.Refinement.bornExpectation
  apply Finset.sum_congr rfl
  intro c hc
  rw [← hWeight x ⟨c, hc⟩]

def RealizesBornPayoffInvariance {future present : Perspective n}
    (step : ContinuationStep (Projective.interface n) future present)
    (evolution : H n →ₗ[ℂ] H n) : Prop :=
  ∀ (x : H n) (aFuture aPresent : EverettianProbability.Core.Act n),
    EverettianProbability.Refinement.PayoffEquivalentAt step.refinement aFuture aPresent →
      EverettianProbability.Refinement.bornExpectation (evolution x) future aFuture =
        EverettianProbability.Refinement.bornExpectation x present aPresent

namespace UniformRecordRespectingProjectiveContinuation

theorem preservesBornExpectation_present {future present : Perspective n}
    (W : UniformRecordRespectingProjectiveContinuation n future present) :
    PreservesBornExpectationOnPerspective present W.evolution :=
  preservesBornExpectation_of_preservesCellBornWeights present W.evolution W.presentBornWeight_preserved

theorem physicalBornExpectation_pullback_eq {future present : Perspective n}
    (W : UniformRecordRespectingProjectiveContinuation n future present)
    (x : H n) (a : EverettianProbability.Core.Act n) :
    EverettianProbability.Refinement.bornExpectation (W.evolution x) future
      (EverettianProbability.Refinement.pullbackAct W.step.refinement a) =
    EverettianProbability.Refinement.bornExpectation x present a := by
  calc
    EverettianProbability.Refinement.bornExpectation (W.evolution x) future
        (EverettianProbability.Refinement.pullbackAct W.step.refinement a) =
      EverettianProbability.Refinement.bornExpectation (W.evolution x) present a :=
        EverettianProbability.Refinement.bornExpectation_pullback_eq
          (W.evolution x) future present W.step.refinement a
    _ = EverettianProbability.Refinement.bornExpectation x present a :=
      W.preservesBornExpectation_present x a

theorem physicalBornExpectation_eq_of_payoffEquivalent {future present : Perspective n}
    (W : UniformRecordRespectingProjectiveContinuation n future present)
    (x : H n) (aFuture aPresent : EverettianProbability.Core.Act n)
    (hEquivalent : EverettianProbability.Refinement.PayoffEquivalentAt
      W.step.refinement aFuture aPresent) :
    EverettianProbability.Refinement.bornExpectation (W.evolution x) future aFuture =
      EverettianProbability.Refinement.bornExpectation x present aPresent := by
  calc
    EverettianProbability.Refinement.bornExpectation (W.evolution x) future aFuture =
      EverettianProbability.Refinement.bornExpectation (W.evolution x) future
        (EverettianProbability.Refinement.pullbackAct W.step.refinement aPresent) :=
      bornExpectation_congr_of_agreeOn (W.evolution x) future hEquivalent
    _ = EverettianProbability.Refinement.bornExpectation x present aPresent :=
      W.physicalBornExpectation_pullback_eq x aPresent

theorem realizesBornPayoffInvariance {future present : Perspective n}
    (W : UniformRecordRespectingProjectiveContinuation n future present) :
    RealizesBornPayoffInvariance W.step W.evolution :=
  fun x aFuture aPresent h => W.physicalBornExpectation_eq_of_payoffEquivalent x aFuture aPresent h

end UniformRecordRespectingProjectiveContinuation

namespace ProjectorCommutingProjectiveContinuation

theorem preservesBornExpectation_present {future present : Perspective n}
    (W : ProjectorCommutingProjectiveContinuation n future present) :
    PreservesBornExpectationOnPerspective present W.evolution :=
  preservesBornExpectation_of_preservesCellBornWeights present W.evolution W.presentBornWeight_preserved

theorem physicalBornExpectation_pullback_eq {future present : Perspective n}
    (W : ProjectorCommutingProjectiveContinuation n future present)
    (x : H n) (a : EverettianProbability.Core.Act n) :
    EverettianProbability.Refinement.bornExpectation (W.evolution x) future
      (EverettianProbability.Refinement.pullbackAct W.step.refinement a) =
    EverettianProbability.Refinement.bornExpectation x present a := by
  calc
    EverettianProbability.Refinement.bornExpectation (W.evolution x) future
        (EverettianProbability.Refinement.pullbackAct W.step.refinement a) =
      EverettianProbability.Refinement.bornExpectation (W.evolution x) present a :=
        EverettianProbability.Refinement.bornExpectation_pullback_eq
          (W.evolution x) future present W.step.refinement a
    _ = EverettianProbability.Refinement.bornExpectation x present a :=
      W.preservesBornExpectation_present x a

theorem physicalBornExpectation_eq_of_payoffEquivalent {future present : Perspective n}
    (W : ProjectorCommutingProjectiveContinuation n future present)
    (x : H n) (aFuture aPresent : EverettianProbability.Core.Act n)
    (hEquivalent : EverettianProbability.Refinement.PayoffEquivalentAt
      W.step.refinement aFuture aPresent) :
    EverettianProbability.Refinement.bornExpectation (W.evolution x) future aFuture =
      EverettianProbability.Refinement.bornExpectation x present aPresent := by
  calc
    EverettianProbability.Refinement.bornExpectation (W.evolution x) future aFuture =
      EverettianProbability.Refinement.bornExpectation (W.evolution x) future
        (EverettianProbability.Refinement.pullbackAct W.step.refinement aPresent) :=
      bornExpectation_congr_of_agreeOn (W.evolution x) future hEquivalent
    _ = EverettianProbability.Refinement.bornExpectation x present aPresent :=
      W.physicalBornExpectation_pullback_eq x aPresent

theorem realizesBornPayoffInvariance {future present : Perspective n}
    (W : ProjectorCommutingProjectiveContinuation n future present) :
    RealizesBornPayoffInvariance W.step W.evolution :=
  fun x aFuture aPresent h => W.physicalBornExpectation_eq_of_payoffEquivalent x aFuture aPresent h

theorem recordNeutral_realizesBornPayoffInvariance :
    RealizesBornPayoffInvariance recordNeutralContinuationStep coupleULin :=
  recordNeutralProjectorCommutingContinuation.realizesBornPayoffInvariance

theorem recordNeutral_bornExpectation_pullback_eq_all_states
    (x : H 3) (a : EverettianProbability.Core.Act 3) :
    EverettianProbability.Refinement.bornExpectation (coupleU x) finePerspective
      (EverettianProbability.Refinement.pullbackAct recordNeutral_refines a) =
    EverettianProbability.Refinement.bornExpectation x coarsePerspective a :=
  recordNeutralProjectorCommutingContinuation.physicalBornExpectation_pullback_eq x a

theorem recordNeutral_bornExpectation_eq_of_payoffEquivalent
    (x : H 3) (aFuture aPresent : EverettianProbability.Core.Act 3)
    (hEquivalent : EverettianProbability.Refinement.PayoffEquivalentAt
      recordNeutral_refines aFuture aPresent) :
    EverettianProbability.Refinement.bornExpectation (coupleU x) finePerspective aFuture =
      EverettianProbability.Refinement.bornExpectation x coarsePerspective aPresent :=
  recordNeutralProjectorCommutingContinuation.physicalBornExpectation_eq_of_payoffEquivalent
    x aFuture aPresent hEquivalent

theorem recordNeutral_payoff_invariant_all_states (x : H 3) :
    EverettianProbability.Refinement.bornExpectation (coupleU x) finePerspective
      (EverettianProbability.Refinement.pullbackAct recordNeutral_refines payoff) =
    EverettianProbability.Refinement.bornExpectation x coarsePerspective payoff :=
  recordNeutral_bornExpectation_pullback_eq_all_states x payoff

theorem recordNeutral_payoffExpectation_before_eq_sixteen_twenty_fifths :
    EverettianProbability.Refinement.bornExpectation psiBefore coarsePerspective payoff = 16 / 25 := by
  rw [EverettianProbability.PhysicalRefinement.bornExpectation_coarse_payoff]
  unfold accessibleRecord
  exact weight_label1Space_before

theorem recordNeutral_payoffExpectation_after_eq_sixteen_twenty_fifths :
    EverettianProbability.Refinement.bornExpectation psiAfter finePerspective
      (EverettianProbability.Refinement.pullbackAct recordNeutral_refines payoff) = 16 / 25 := by
  rw [← coupleU_psiBefore]
  exact (recordNeutral_payoff_invariant_all_states psiBefore).trans
    recordNeutral_payoffExpectation_before_eq_sixteen_twenty_fifths

theorem recordNeutral_payoff_nonconstant : payoff label0Line = 0 ∧ payoff label1Space = 1 := by
  constructor
  · unfold payoff
    rw [EverettianProbability.Core.Act.indicator_of_ne label0Line_ne_label1Space]
  · unfold payoff
    exact EverettianProbability.Core.Act.indicator_self label1Space

theorem recordNeutralPhysicalPayoffInvariance_integratedWitness :
    RealizesBornPayoffInvariance recordNeutralContinuationStep coupleULin ∧
    (∀ (x : H 3) (a : EverettianProbability.Core.Act 3),
      EverettianProbability.Refinement.bornExpectation (coupleU x) finePerspective
        (EverettianProbability.Refinement.pullbackAct recordNeutral_refines a) =
      EverettianProbability.Refinement.bornExpectation x coarsePerspective a) ∧
    payoff label0Line = 0 ∧ payoff label1Space = 1 ∧
    EverettianProbability.Refinement.bornExpectation psiBefore coarsePerspective payoff = 16 / 25 ∧
    EverettianProbability.Refinement.bornExpectation psiAfter finePerspective
      (EverettianProbability.Refinement.pullbackAct recordNeutral_refines payoff) = 16 / 25 :=
  ⟨recordNeutral_realizesBornPayoffInvariance,
    recordNeutral_bornExpectation_pullback_eq_all_states,
    recordNeutral_payoff_nonconstant.1, recordNeutral_payoff_nonconstant.2,
    recordNeutral_payoffExpectation_before_eq_sixteen_twenty_fifths,
    recordNeutral_payoffExpectation_after_eq_sixteen_twenty_fifths⟩

end ProjectorCommutingProjectiveContinuation
end
end EverettianProbability.Abstract
