import EverettianProbability.API.ConditionalBorn
import EverettianProbability.Diachronic.TowerProperty

/-!
**FR.** # API diachronique conditionnelle de la regle de Born

Cette facade expose les consequences diachroniques conditionnelles des
premisses projectives publiques : credence des continuateurs, valeur
conditionnelle, normalisation, esperance totale, regle de chaine et loi de la
tour. Elle reste explicitement conditionnelle aux premisses normatives et
semantiques deja isolees.

**EN.** # Conditional diachronic Born-rule API

This facade exposes the conditional diachronic consequences of the public
projective premises: continuator credence, conditional value, normalization,
total expectation, the chain rule, and the tower law. It remains explicitly
conditional on the already separated normative and semantic premises.
-/

namespace EverettianProbability.API.Conditional

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core
open EverettianProbability.Abstract
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : ℕ}

namespace ProjectiveBornPremises

/-- Continuator credence is the conditional Born ratio. -/
theorem continuatorCredence_eq_bornRatio
    (P : ProjectiveBornPremises n)
    {future present : Perspective n}
    (step : ContinuationStep (Projective.interface n) future present)
    (c : (Projective.interface n).Cell present)
    (hc : ‖projL c.val P.state‖ ^ 2 ≠ 0)
    (i : (Projective.interface n).Cell future) :
    step.continuatorCredence P.F c i =
      if (Projective.interface n).parentCell step.refinement i = c then
        ‖projL i.val P.state‖ ^ 2 / ‖projL c.val P.state‖ ^ 2
      else 0 :=
  step.projectiveContinuatorCredence_eq_bornRatio P.F P.dim_ge_three
    P.refinement_invariant P.normalized P.null_support c hc i

theorem continuatorExpectedValue_eq_born
    (P : ProjectiveBornPremises n)
    {future present : Perspective n}
    (step : ContinuationStep (Projective.interface n) future present)
    (c : (Projective.interface n).Cell present)
    (hc : ‖projL c.val P.state‖ ^ 2 ≠ 0)
    (a : ProjectiveAct n) :
    step.continuatorExpectedValue P.F c a =
      ∑ i : (Projective.interface n).Cell future,
        (if (Projective.interface n).parentCell step.refinement i = c then
          ‖projL i.val P.state‖ ^ 2 / ‖projL c.val P.state‖ ^ 2
        else 0) * a i.val :=
  step.projectiveContinuatorExpectedValue_eq_born P.F P.dim_ge_three
    P.refinement_invariant P.normalized P.null_support c hc a

theorem sum_continuatorCredence_eq_one
    (P : ProjectiveBornPremises n)
    {future present : Perspective n}
    (step : ContinuationStep (Projective.interface n) future present)
    (c : (Projective.interface n).Cell present)
    (hc : ‖projL c.val P.state‖ ^ 2 ≠ 0) :
    (∑ i : (Projective.interface n).Cell future,
      step.continuatorCredence P.F c i) = 1 :=
  step.sum_continuatorCredence_eq_one P.F P.refinement_invariant
    projectiveInterface_outcome_injective c
    (P.canonicalWeight_ne_zero_of_bornWeight_ne_zero present c hc)

theorem futureDecisionValue_eq_bornTotalExpectation
    (P : ProjectiveBornPremises n)
    {future present : Perspective n}
    (step : ContinuationStep (Projective.interface n) future present)
    (a : ProjectiveAct n) :
    P.F.V future a =
      ∑ c : (Projective.interface n).Cell present,
        ‖projL c.val P.state‖ ^ 2 * step.continuatorExpectedValue P.F c a :=
  step.projectiveFutureDecisionValue_eq_bornTotalExpectation P.F P.dim_ge_three
    P.refinement_invariant P.normalized P.null_support a

theorem continuatorCredence_chain_rule
    (P : ProjectiveBornPremises n)
    {future middle present : Perspective n}
    (later : ContinuationStep (Projective.interface n) future middle)
    (earlier : ContinuationStep (Projective.interface n) middle present)
    (c : (Projective.interface n).Cell present)
    (hc : ‖projL c.val P.state‖ ^ 2 ≠ 0)
    (i : (Projective.interface n).Cell future) :
    earlier.continuatorCredence P.F c ((Projective.interface n).parentCell later.refinement i) *
      later.continuatorCredence P.F ((Projective.interface n).parentCell later.refinement i) i =
      (later.trans earlier).continuatorCredence P.F c i :=
  later.continuatorCredence_chain_rule_at_parent P.F P.refinement_invariant
    projectiveInterface_outcome_injective earlier c
    (P.canonicalWeight_ne_zero_of_bornWeight_ne_zero present c hc) i

theorem sum_intermediateCredence_eq_composite
    (P : ProjectiveBornPremises n)
    {future middle present : Perspective n}
    (later : ContinuationStep (Projective.interface n) future middle)
    (earlier : ContinuationStep (Projective.interface n) middle present)
    (c : (Projective.interface n).Cell present)
    (hc : ‖projL c.val P.state‖ ^ 2 ≠ 0)
    (i : (Projective.interface n).Cell future) :
    (∑ j : (Projective.interface n).Cell middle,
      earlier.continuatorCredence P.F c j * later.continuatorCredence P.F j i) =
      (later.trans earlier).continuatorCredence P.F c i :=
  later.sum_intermediateCredence_mul_laterCredence_eq_composite P.F
    P.refinement_invariant projectiveInterface_outcome_injective earlier c
    (P.canonicalWeight_ne_zero_of_bornWeight_ne_zero present c hc) i

theorem continuatorExpectedValue_tower
    (P : ProjectiveBornPremises n)
    {future middle present : Perspective n}
    (later : ContinuationStep (Projective.interface n) future middle)
    (earlier : ContinuationStep (Projective.interface n) middle present)
    (c : (Projective.interface n).Cell present)
    (hc : ‖projL c.val P.state‖ ^ 2 ≠ 0)
    (a : ProjectiveAct n) :
    (later.trans earlier).continuatorExpectedValue P.F c a =
      ContinuationStep.stagedContinuatorExpectedValue P.F later earlier c a :=
  later.continuatorExpectedValue_tower P.F P.refinement_invariant
    projectiveInterface_outcome_injective earlier c
    (P.canonicalWeight_ne_zero_of_bornWeight_ne_zero present c hc) a

/-- Every admissible record-credence family assigns the same conditional Born
ratio to projective continuators. -/
theorem admissibleCredence_eq_bornRatio
    (P : ProjectiveBornPremises n)
    (C : RecordCredenceFamily (Projective.interface n))
    (hnorm : C.NormalizedOnNonzeroMass P.F)
    (hdecision : C.RepresentsUnrestrictedDecisionValue P.F)
    (hodds : C.OddsInvariantUnderRecordRestriction P.F)
    {future present : Perspective n}
    (step : ContinuationStep (Projective.interface n) future present)
    (c : (Projective.interface n).Cell present)
    (hc : ‖projL c.val P.state‖ ^ 2 ≠ 0)
    (i : (Projective.interface n).Cell future) :
    C.credence future (step.continuatorCells c) i =
      if (Projective.interface n).parentCell step.refinement i = c then
        ‖projL i.val P.state‖ ^ 2 / ‖projL c.val P.state‖ ^ 2
      else 0 :=
  C.projectiveCredence_on_continuators_eq_bornRatio P.F hnorm hdecision hodds
    P.dim_ge_three P.refinement_invariant P.normalized P.null_support step c hc i

end ProjectiveBornPremises

end
end EverettianProbability.API.Conditional
