import EverettianProbability.Diachronic.PhysicalPayoffInvariance

/-!
**FR.** # Equivalence entre record bornien et invariance des consequences

Le record bornien d'une perspective finie est la famille de ses poids de
cellules. Ce module montre que cette famille determine exactement les
esperances de Born de tous les actes accessibles et les invariances locales
apres raffinement.

**EN.** # Equivalence between Born records and payoff invariance

The Born record of a finite perspective is its family of cell weights. This
module shows that this family exactly determines Born expectations of all
accessible acts and local invariances after refinement.
-/

namespace EverettianProbability.Abstract

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core
open EverettianProbability.PhysicalRefinement
open scoped BigOperators Classical InnerProductSpace

noncomputable section
variable {n : Nat}

def bornRecord (D : Perspective n) (x : H n) :
    (Projective.interface n).Cell D → ℝ := fun c => ‖projL c.val x‖ ^ 2

def SameBornRecord (D : Perspective n) (x y : H n) : Prop :=
  ∀ c : (Projective.interface n).Cell D, ‖projL c.val x‖ ^ 2 = ‖projL c.val y‖ ^ 2

theorem sameBornRecord_iff_bornRecord_eq (D : Perspective n) (x y : H n) :
    SameBornRecord D x y ↔ bornRecord D x = bornRecord D y := by
  constructor
  · intro h; funext c; exact h c
  · intro h c; exact congrFun h c

theorem SameBornRecord.refl (D : Perspective n) (x : H n) : SameBornRecord D x x := fun _ => rfl
theorem SameBornRecord.symm {D : Perspective n} {x y : H n}
    (h : SameBornRecord D x y) : SameBornRecord D y x := fun c => (h c).symm
theorem SameBornRecord.trans {D : Perspective n} {x y z : H n}
    (hxy : SameBornRecord D x y) (hyz : SameBornRecord D y z) : SameBornRecord D x z :=
  fun c => (hxy c).trans (hyz c)

theorem bornExpectation_indicator_cell (x : H n) (D : Perspective n)
    (c : (Projective.interface n).Cell D) :
    EverettianProbability.Refinement.bornExpectation x D
      (EverettianProbability.Core.Act.indicator c.val) = ‖projL c.val x‖ ^ 2 := by
  unfold EverettianProbability.Refinement.bornExpectation
  rw [Finset.sum_eq_single c.val]
  · rw [EverettianProbability.Core.Act.indicator_self, mul_one]
  · intro d _ hdc
    rw [EverettianProbability.Core.Act.indicator_of_ne hdc, mul_zero]
  · simp [EverettianProbability.Core.Act.indicator_self]

theorem bornExpectation_eq_of_sameBornRecord {D : Perspective n} {x y : H n}
    (hRecord : SameBornRecord D x y) (a : EverettianProbability.Core.Act n) :
    EverettianProbability.Refinement.bornExpectation x D a =
      EverettianProbability.Refinement.bornExpectation y D a := by
  unfold EverettianProbability.Refinement.bornExpectation
  apply Finset.sum_congr rfl
  intro c hc
  rw [hRecord ⟨c, hc⟩]

theorem sameBornRecord_of_bornExpectation_eq_all (D : Perspective n) (x y : H n)
    (hExpectation : ∀ a : EverettianProbability.Core.Act n,
      EverettianProbability.Refinement.bornExpectation x D a =
        EverettianProbability.Refinement.bornExpectation y D a) :
    SameBornRecord D x y := by
  intro c
  have h := hExpectation (EverettianProbability.Core.Act.indicator c.val)
  rw [bornExpectation_indicator_cell, bornExpectation_indicator_cell] at h
  exact h

theorem sameBornRecord_iff_bornExpectation_eq_all (D : Perspective n) (x y : H n) :
    SameBornRecord D x y ↔ ∀ a : EverettianProbability.Core.Act n,
      EverettianProbability.Refinement.bornExpectation x D a =
        EverettianProbability.Refinement.bornExpectation y D a := by
  constructor
  · intro h a; exact bornExpectation_eq_of_sameBornRecord h a
  · exact sameBornRecord_of_bornExpectation_eq_all D x y

theorem sameBornRecord_iff_pullbackBornExpectation_eq_all
    {future present : Perspective n} (r : Refines future present) (x y : H n) :
    SameBornRecord present x y ↔ ∀ a : EverettianProbability.Core.Act n,
      EverettianProbability.Refinement.bornExpectation y future
        (EverettianProbability.Refinement.pullbackAct r a) =
      EverettianProbability.Refinement.bornExpectation x present a := by
  constructor
  · intro h a
    calc
      EverettianProbability.Refinement.bornExpectation y future
          (EverettianProbability.Refinement.pullbackAct r a) =
        EverettianProbability.Refinement.bornExpectation y present a :=
          EverettianProbability.Refinement.bornExpectation_pullback_eq y future present r a
      _ = EverettianProbability.Refinement.bornExpectation x present a :=
        (bornExpectation_eq_of_sameBornRecord h a).symm
  · intro h
    apply sameBornRecord_of_bornExpectation_eq_all present x y
    intro a
    calc
      EverettianProbability.Refinement.bornExpectation x present a =
        EverettianProbability.Refinement.bornExpectation y future
          (EverettianProbability.Refinement.pullbackAct r a) := (h a).symm
      _ = EverettianProbability.Refinement.bornExpectation y present a :=
        EverettianProbability.Refinement.bornExpectation_pullback_eq y future present r a

theorem bornExpectation_eq_of_sameBornRecord_and_payoffEquivalent
    {future present : Perspective n} (r : Refines future present) {x y : H n}
    (hRecord : SameBornRecord present x y)
    (aFuture aPresent : EverettianProbability.Core.Act n)
    (hEquivalent : EverettianProbability.Refinement.PayoffEquivalentAt r aFuture aPresent) :
    EverettianProbability.Refinement.bornExpectation y future aFuture =
      EverettianProbability.Refinement.bornExpectation x present aPresent := by
  calc
    EverettianProbability.Refinement.bornExpectation y future aFuture =
      EverettianProbability.Refinement.bornExpectation y future
        (EverettianProbability.Refinement.pullbackAct r aPresent) :=
      bornExpectation_congr_of_agreeOn y future hEquivalent
    _ = EverettianProbability.Refinement.bornExpectation y present aPresent :=
      EverettianProbability.Refinement.bornExpectation_pullback_eq y future present r aPresent
    _ = EverettianProbability.Refinement.bornExpectation x present aPresent :=
      (bornExpectation_eq_of_sameBornRecord hRecord aPresent).symm

theorem realizesBornPayoffInvariance_iff_sameBornRecord
    {future present : Perspective n}
    (step : ContinuationStep (Projective.interface n) future present)
    (evolution : H n →ₗ[ℂ] H n) :
    RealizesBornPayoffInvariance step evolution ↔ ∀ x : H n,
      SameBornRecord present x (evolution x) := by
  constructor
  · intro h x
    apply (sameBornRecord_iff_pullbackBornExpectation_eq_all step.refinement x (evolution x)).2
    intro a
    apply h x (EverettianProbability.Refinement.pullbackAct step.refinement a) a
    exact EverettianProbability.Core.Act.agreeOn_refl future
      (EverettianProbability.Refinement.pullbackAct step.refinement a)
  · intro h x aFuture aPresent hEquivalent
    exact bornExpectation_eq_of_sameBornRecord_and_payoffEquivalent step.refinement
      (h x) aFuture aPresent hEquivalent

namespace UniformRecordRespectingProjectiveContinuation
theorem sameBornRecord_before_after {future present : Perspective n}
    (W : UniformRecordRespectingProjectiveContinuation n future present) (x : H n) :
    SameBornRecord present x (W.evolution x) := fun c => W.presentBornWeight_preserved x c
theorem realizesBornPayoffInvariance_iff {future present : Perspective n}
    (W : UniformRecordRespectingProjectiveContinuation n future present) :
    RealizesBornPayoffInvariance W.step W.evolution ↔ ∀ x : H n,
      SameBornRecord present x (W.evolution x) :=
  realizesBornPayoffInvariance_iff_sameBornRecord W.step W.evolution
end UniformRecordRespectingProjectiveContinuation

namespace ProjectorCommutingProjectiveContinuation
theorem sameBornRecord_before_after {future present : Perspective n}
    (W : ProjectorCommutingProjectiveContinuation n future present) (x : H n) :
    SameBornRecord present x (W.evolution x) := fun c => W.presentBornWeight_preserved x c

theorem recordNeutral_psiBefore_ne_psiAfter : psiBefore ≠ psiAfter := by
  intro h
  have hInner : ⟪(b 2 : H 3), psiBefore⟫_ℂ = ⟪(b 2 : H 3), psiAfter⟫_ℂ :=
    congrArg (fun z : H 3 => ⟪(b 2 : H 3), z⟫_ℂ) h
  rw [inner_b2_psiBefore, inner_b2_psiAfter] at hInner
  norm_num at hInner

theorem recordNeutral_psiBefore_psiAfter_sameBornRecord :
    SameBornRecord coarsePerspective psiBefore psiAfter := by
  have h := recordNeutralProjectorCommutingContinuation.sameBornRecord_before_after psiBefore
  change SameBornRecord coarsePerspective psiBefore (coupleU psiBefore) at h
  rw [coupleU_psiBefore] at h
  exact h

theorem recordNeutral_allCoarseBornExpectations_eq (a : EverettianProbability.Core.Act 3) :
    EverettianProbability.Refinement.bornExpectation psiBefore coarsePerspective a =
      EverettianProbability.Refinement.bornExpectation psiAfter coarsePerspective a :=
  bornExpectation_eq_of_sameBornRecord recordNeutral_psiBefore_psiAfter_sameBornRecord a

theorem recordNeutral_allPullbackBornExpectations_eq (a : EverettianProbability.Core.Act 3) :
    EverettianProbability.Refinement.bornExpectation psiAfter finePerspective
      (EverettianProbability.Refinement.pullbackAct recordNeutral_refines a) =
    EverettianProbability.Refinement.bornExpectation psiBefore coarsePerspective a :=
  (sameBornRecord_iff_pullbackBornExpectation_eq_all recordNeutral_refines psiBefore psiAfter).1
    recordNeutral_psiBefore_psiAfter_sameBornRecord a

theorem recordNeutralRecordWeightEquivalence_integratedWitness :
    psiBefore ≠ psiAfter ∧ SameBornRecord coarsePerspective psiBefore psiAfter ∧
    (∀ a : EverettianProbability.Core.Act 3,
      EverettianProbability.Refinement.bornExpectation psiBefore coarsePerspective a =
        EverettianProbability.Refinement.bornExpectation psiAfter coarsePerspective a) ∧
    (∀ a : EverettianProbability.Core.Act 3,
      EverettianProbability.Refinement.bornExpectation psiAfter finePerspective
        (EverettianProbability.Refinement.pullbackAct recordNeutral_refines a) =
      EverettianProbability.Refinement.bornExpectation psiBefore coarsePerspective a) ∧
    RealizesBornPayoffInvariance recordNeutralContinuationStep coupleULin :=
  ⟨recordNeutral_psiBefore_ne_psiAfter,
    recordNeutral_psiBefore_psiAfter_sameBornRecord,
    recordNeutral_allCoarseBornExpectations_eq,
    recordNeutral_allPullbackBornExpectations_eq,
    recordNeutral_realizesBornPayoffInvariance⟩
end ProjectorCommutingProjectiveContinuation
end
end EverettianProbability.Abstract
