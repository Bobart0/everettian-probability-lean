import EverettianProbability.Diachronic.ThreeLevelTowerWitness
import EverettianProbability.BornCalibration.BornExpectation

/-!
**FR.** # Crédence bornienne envers les continuateurs projectifs

Ce module raccorde la calibration bornienne de P4 à la théorie diachronique
abstraite de P7–P8b. Sous l'invariance normative locale, la nullité physique
sur le support orthogonal et `3 ≤ n`, le poids canonique projectif est le poids
de Born. La crédence d'un continuateur est alors le rapport des poids de Born
sur sa fibre.

Cette conclusion reste conditionnelle aux ponts `NORM`, `PHYS` et `SEM`.
Une `ContinuationStep` demeure un raffinement temporel abstrait, dont la
réalisabilité unitaire record-respectueuse n'est pas établie ici.

**EN.** # Born credence over projective continuators

This module connects P4 Born calibration to the P7–P8b abstract diachronic
theory. Under normative local invariance, physical null support, and `3 ≤ n`,
projective canonical weight is Born weight. Continuator credence is then the
ratio of Born weights on its fibre.

The conclusion remains conditional on the `NORM`, `PHYS`, and `SEM` bridges.
A `ContinuationStep` remains an abstract temporal refinement whose
record-respecting unitary realization is not established here.
-/

namespace EverettianProbability.Abstract

open QuantumFoundations.BornRule Gleason
open scoped BigOperators Classical

noncomputable section

variable {n : ℕ}

/-- The concrete projective expectation family corresponding to an abstract
family on `Projective.interface n`. -/
def projectiveConcreteExpectationFamily
    (F : RationalExpectationFamily (Projective.interface n)) :
    EverettianProbability.Preference.RationalExpectationFamily n where
  V := F.V
  affine := by
    intro D t a b
    exact F.affine D t a b
  monotone := by
    intro D a b hab
    apply F.monotone D a b
    intro c
    exact hab c.val c.property
  normalized_const := by
    intro D k
    exact F.normalized_const D k

@[simp] theorem projectiveConcreteExpectationFamily_V
    (F : RationalExpectationFamily (Projective.interface n))
    (D : Perspective n)
    (a : EverettianProbability.Core.Act n) :
    (projectiveConcreteExpectationFamily F).V D a = F.V D a := by
  rfl

/-- Outcomes of projective cells are injective. -/
theorem projectiveInterface_outcome_injective :
    ∀ D : (Projective.interface n).Perspective,
      Function.Injective (@(Projective.interface n).outcome D) := by
  intro D
  exact Subtype.val_injective

/-- Abstract projective refinement invariance induces the concrete premise. -/
theorem projectiveRefinementInvariantLocal_toConcrete
    (F : RationalExpectationFamily (Projective.interface n))
    (hinv : RefinementInvariantLocal F.V) :
    EverettianProbability.Refinement.RefinementInvariantLocal
      (projectiveConcreteExpectationFamily F).V := by
  intro fine coarse r a' a hequiv
  apply hinv r a' a
  intro c
  exact hequiv c.val c.property

/-- The abstract canonical weight agrees with the concrete contextual weight. -/
theorem projectiveCanonicalWeight_eq_concreteCanonicalWeight
    (F : RationalExpectationFamily (Projective.interface n))
    (D : Perspective n)
    (c : (Projective.interface n).Cell D) :
    canonicalWeight F D c =
      EverettianProbability.BornCalibration.canonicalWeight
        (projectiveConcreteExpectationFamily F) D c.val := by
  unfold canonicalWeight EverettianProbability.BornCalibration.canonicalWeight
  rw [if_pos c.property]
  change
    F.V D (Act.indicator c.val) =
      F.V D (EverettianProbability.Core.Act.indicator c.val)
  apply V_congr_of_agreeOn F D
  intro d
  rfl

/-- Projective abstract canonical weight is Born weight under the P4 premises.
`hinv` is normative and `hNul` is the physical support bridge. -/
theorem projectiveCanonicalWeight_eq_born
    (F : RationalExpectationFamily (Projective.interface n))
    (hn3 : 3 ≤ n)
    (hinv : RefinementInvariantLocal F.V)
    {v : H n}
    (hv : ‖v‖ = 1)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight
        (projectiveConcreteExpectationFamily F)) v)
    (D : Perspective n)
    (c : (Projective.interface n).Cell D) :
    canonicalWeight F D c = ‖projL c.val v‖ ^ 2 := by
  have hConcreteInv :
      EverettianProbability.Refinement.RefinementInvariantLocal
        (projectiveConcreteExpectationFamily F).V :=
    projectiveRefinementInvariantLocal_toConcrete F hinv
  have hGrain : AxGrain
      (EverettianProbability.BornCalibration.canonicalWeight
        (projectiveConcreteExpectationFamily F)) :=
    EverettianProbability.BornCalibration.refinement_invariant_implies_grain
      (projectiveConcreteExpectationFamily F) hConcreteInv
  have hBorn := grainCoherenceTheorem_projector
    (EverettianProbability.BornCalibration.canonicalWeight
      (projectiveConcreteExpectationFamily F)) hn3 hGrain
    (EverettianProbability.Preference.canonicalWeight_axNorm
      (projectiveConcreteExpectationFamily F))
    (EverettianProbability.Preference.canonicalWeight_axPos
      (projectiveConcreteExpectationFamily F)) hv hNul
  rw [projectiveCanonicalWeight_eq_concreteCanonicalWeight F D c]
  exact hBorn D c.property

namespace ContinuationStep

/-- Born formula for credence over a projective future continuator. -/
theorem projectiveContinuatorCredence_eq_bornRatio
    (F : RationalExpectationFamily (Projective.interface n))
    (hn3 : 3 ≤ n) (hinv : RefinementInvariantLocal F.V)
    {v : H n} (hv : ‖v‖ = 1)
    (hNul : AxNul (EverettianProbability.BornCalibration.canonicalWeight
      (projectiveConcreteExpectationFamily F)) v)
    {future present : Perspective n}
    (step : ContinuationStep (Projective.interface n) future present)
    (c : (Projective.interface n).Cell present)
    (hcBorn : ‖projL c.val v‖ ^ 2 ≠ 0)
    (i : (Projective.interface n).Cell future) :
    step.continuatorCredence F c i =
      if (Projective.interface n).parentCell step.refinement i = c then
        ‖projL i.val v‖ ^ 2 / ‖projL c.val v‖ ^ 2 else 0 := by
  rw [step.continuatorCredence_eq_conditionalWeight_total F hinv
    projectiveInterface_outcome_injective c i]
  unfold conditionalWeight
  rw [projectiveCanonicalWeight_eq_born F hn3 hinv hv hNul present c,
    projectiveCanonicalWeight_eq_born F hn3 hinv hv hNul future i]
  simp [hcBorn]

/-- Born formula for a conditional future-act value. -/
theorem projectiveContinuatorExpectedValue_eq_born
    (F : RationalExpectationFamily (Projective.interface n))
    (hn3 : 3 ≤ n) (hinv : RefinementInvariantLocal F.V)
    {v : H n} (hv : ‖v‖ = 1)
    (hNul : AxNul (EverettianProbability.BornCalibration.canonicalWeight
      (projectiveConcreteExpectationFamily F)) v)
    {future present : Perspective n}
    (step : ContinuationStep (Projective.interface n) future present)
    (c : (Projective.interface n).Cell present)
    (hcBorn : ‖projL c.val v‖ ^ 2 ≠ 0)
    (a : Act (Projective.interface n)) :
    step.continuatorExpectedValue F c a =
      ∑ i : (Projective.interface n).Cell future,
        (if (Projective.interface n).parentCell step.refinement i = c then
          ‖projL i.val v‖ ^ 2 / ‖projL c.val v‖ ^ 2 else 0) * a i.val := by
  unfold continuatorExpectedValue
  apply Finset.sum_congr rfl
  intro i _
  rw [step.projectiveContinuatorCredence_eq_bornRatio F hn3 hinv hv hNul c hcBorn i]
  rfl

/-- Projective Born form of the diachronic total-expectation law. -/
theorem projectiveFutureDecisionValue_eq_bornTotalExpectation
    (F : RationalExpectationFamily (Projective.interface n))
    (hn3 : 3 ≤ n) (hinv : RefinementInvariantLocal F.V)
    {v : H n} (hv : ‖v‖ = 1)
    (hNul : AxNul (EverettianProbability.BornCalibration.canonicalWeight
      (projectiveConcreteExpectationFamily F)) v)
    {future present : Perspective n}
    (step : ContinuationStep (Projective.interface n) future present)
    (a : Act (Projective.interface n)) :
    F.V future a = ∑ c : (Projective.interface n).Cell present,
      ‖projL c.val v‖ ^ 2 * step.continuatorExpectedValue F c a := by
  rw [step.futureDecisionValue_eq_sum_presentWeight_mul_continuatorExpectedValue
    F hinv projectiveInterface_outcome_injective a]
  apply Finset.sum_congr rfl
  intro c _
  rw [projectiveCanonicalWeight_eq_born F hn3 hinv hv hNul present c]

end ContinuationStep

namespace RecordCredenceFamily

/-- Every admissible projective credence family assigns the Born ratio. -/
theorem projectiveCredence_on_continuators_eq_bornRatio
    (C : RecordCredenceFamily (Projective.interface n))
    (F : RationalExpectationFamily (Projective.interface n))
    (hnorm : C.NormalizedOnNonzeroMass F)
    (hdecision : C.RepresentsUnrestrictedDecisionValue F)
    (hodds : C.OddsInvariantUnderRecordRestriction F)
    (hn3 : 3 ≤ n) (hinv : RefinementInvariantLocal F.V)
    {v : H n} (hv : ‖v‖ = 1)
    (hNul : AxNul (EverettianProbability.BornCalibration.canonicalWeight
      (projectiveConcreteExpectationFamily F)) v)
    {future present : Perspective n}
    (step : ContinuationStep (Projective.interface n) future present)
    (c : (Projective.interface n).Cell present)
    (hcBorn : ‖projL c.val v‖ ^ 2 ≠ 0)
    (i : (Projective.interface n).Cell future) :
    C.credence future (step.continuatorCells c) i =
      if (Projective.interface n).parentCell step.refinement i = c then
        ‖projL i.val v‖ ^ 2 / ‖projL c.val v‖ ^ 2 else 0 := by
  have hcCanonical : canonicalWeight F present c ≠ 0 := by
    rw [projectiveCanonicalWeight_eq_born F hn3 hinv hv hNul present c]
    exact hcBorn
  calc
    C.credence future (step.continuatorCells c) i = step.continuatorCredence F c i :=
      C.credence_on_continuators_eq F hnorm hdecision hodds hinv
        projectiveInterface_outcome_injective step c hcCanonical i
    _ = _ := step.projectiveContinuatorCredence_eq_bornRatio F hn3 hinv hv hNul c hcBorn i

/-- Every admissible projective credence family gives Born conditional values. -/
theorem projectiveCredenceExpectedFutureValue_eq_born
    (C : RecordCredenceFamily (Projective.interface n))
    (F : RationalExpectationFamily (Projective.interface n))
    (hnorm : C.NormalizedOnNonzeroMass F)
    (hdecision : C.RepresentsUnrestrictedDecisionValue F)
    (hodds : C.OddsInvariantUnderRecordRestriction F)
    (hn3 : 3 ≤ n) (hinv : RefinementInvariantLocal F.V)
    {v : H n} (hv : ‖v‖ = 1)
    (hNul : AxNul (EverettianProbability.BornCalibration.canonicalWeight
      (projectiveConcreteExpectationFamily F)) v)
    {future present : Perspective n}
    (step : ContinuationStep (Projective.interface n) future present)
    (c : (Projective.interface n).Cell present)
    (hcBorn : ‖projL c.val v‖ ^ 2 ≠ 0)
    (a : Act (Projective.interface n)) :
    C.credenceExpectedFutureValue step c a =
      ∑ i : (Projective.interface n).Cell future,
        (if (Projective.interface n).parentCell step.refinement i = c then
          ‖projL i.val v‖ ^ 2 / ‖projL c.val v‖ ^ 2 else 0) * a i.val := by
  unfold credenceExpectedFutureValue
  apply Finset.sum_congr rfl
  intro i _
  rw [C.projectiveCredence_on_continuators_eq_bornRatio F hnorm hdecision hodds
    hn3 hinv hv hNul step c hcBorn i]
  rfl

/-- Every admissible projective credence family yields the Born-weighted
diachronic total-expectation law. -/
theorem projectiveFutureDecisionValue_eq_bornTotalExpectation
    (C : RecordCredenceFamily (Projective.interface n))
    (F : RationalExpectationFamily (Projective.interface n))
    (hnorm : C.NormalizedOnNonzeroMass F)
    (hdecision : C.RepresentsUnrestrictedDecisionValue F)
    (hodds : C.OddsInvariantUnderRecordRestriction F)
    (hn3 : 3 ≤ n) (hinv : RefinementInvariantLocal F.V)
    {v : H n} (hv : ‖v‖ = 1)
    (hNul : AxNul (EverettianProbability.BornCalibration.canonicalWeight
      (projectiveConcreteExpectationFamily F)) v)
    {future present : Perspective n}
    (step : ContinuationStep (Projective.interface n) future present)
    (a : Act (Projective.interface n)) :
    F.V future a = ∑ c : (Projective.interface n).Cell present,
      ‖projL c.val v‖ ^ 2 * C.credenceExpectedFutureValue step c a := by
  rw [C.futureDecisionValue_eq_sum_presentWeight_mul_credenceExpectedFutureValue
    F hnorm hdecision hodds hinv projectiveInterface_outcome_injective step a]
  apply Finset.sum_congr rfl
  intro c _
  rw [projectiveCanonicalWeight_eq_born F hn3 hinv hv hNul present c]

end RecordCredenceFamily

end
end EverettianProbability.Abstract
