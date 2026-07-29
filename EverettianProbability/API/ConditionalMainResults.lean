import EverettianProbability.API.ConditionalBorn
import EverettianProbability.API.DiachronicBorn

/-!
**FR.** # Resultats principaux conditionnels de Born

Ce fichier est le point d'entree recommande pour le premier Saint-Graal
formel conditionnel. Il regroupe les conclusions stables a une et deux etapes,
sans ajouter de premisse de realisabilite physique.

**EN.** # Conditional Born main results

This file is the recommended entry point for the first conditional formal
Saint Grail. It bundles stable one- and two-step conclusions without adding a
physical-realizability premise.
-/

namespace EverettianProbability.API.Conditional

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core
open EverettianProbability.Abstract
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : ℕ}

/-- Stable one-step conclusion bundle of the conditional Born theorem. -/
structure OneStepConditionalBornResults
    (P : ProjectiveBornPremises n)
    {future present : Perspective n}
    (step : ContinuationStep (Projective.interface n) future present)
    (c : (Projective.interface n).Cell present)
    (hc : ‖projL c.val P.state‖ ^ 2 ≠ 0)
    (presentAct futureAct : ProjectiveAct n) : Prop where
  present_value_is_born :
    P.F.V present presentAct =
      ∑ d ∈ present.cells, ‖projL d P.state‖ ^ 2 * presentAct d
  future_value_is_born :
    P.F.V future futureAct =
      ∑ i ∈ future.cells, ‖projL i P.state‖ ^ 2 * futureAct i
  continuator_credence_is_born : ∀ i : (Projective.interface n).Cell future,
    step.continuatorCredence P.F c i =
      if (Projective.interface n).parentCell step.refinement i = c then
        ‖projL i.val P.state‖ ^ 2 / ‖projL c.val P.state‖ ^ 2 else 0
  continuator_credence_normalized :
    (∑ i : (Projective.interface n).Cell future,
      step.continuatorCredence P.F c i) = 1
  future_total_expectation :
    P.F.V future futureAct =
      ∑ d : (Projective.interface n).Cell present,
        ‖projL d.val P.state‖ ^ 2 * step.continuatorExpectedValue P.F d futureAct

/-- Main one-step conditional Born result. -/
theorem oneStepConditionalBornResults
    (P : ProjectiveBornPremises n)
    {future present : Perspective n}
    (step : ContinuationStep (Projective.interface n) future present)
    (c : (Projective.interface n).Cell present)
    (hc : ‖projL c.val P.state‖ ^ 2 ≠ 0)
    (presentAct futureAct : ProjectiveAct n) :
    OneStepConditionalBornResults P step c hc presentAct futureAct := by
  refine {
    present_value_is_born := P.value_eq_bornExpectation present presentAct
    future_value_is_born := P.value_eq_bornExpectation future futureAct
    continuator_credence_is_born := ?_
    continuator_credence_normalized := P.sum_continuatorCredence_eq_one step c hc
    future_total_expectation := P.futureDecisionValue_eq_bornTotalExpectation step futureAct }
  intro i
  exact P.continuatorCredence_eq_bornRatio step c hc i

/-- Stable two-step conclusion bundle: chain rule and tower property. -/
structure TwoStepConditionalBornResults
    (P : ProjectiveBornPremises n)
    {future middle present : Perspective n}
    (later : ContinuationStep (Projective.interface n) future middle)
    (earlier : ContinuationStep (Projective.interface n) middle present)
    (c : (Projective.interface n).Cell present)
    (hc : ‖projL c.val P.state‖ ^ 2 ≠ 0)
    (futureAct : ProjectiveAct n) : Prop where
  chain_rule : ∀ i : (Projective.interface n).Cell future,
    earlier.continuatorCredence P.F c ((Projective.interface n).parentCell later.refinement i) *
      later.continuatorCredence P.F ((Projective.interface n).parentCell later.refinement i) i =
      (later.trans earlier).continuatorCredence P.F c i
  summed_chain_rule : ∀ i : (Projective.interface n).Cell future,
    (∑ j : (Projective.interface n).Cell middle,
      earlier.continuatorCredence P.F c j * later.continuatorCredence P.F j i) =
      (later.trans earlier).continuatorCredence P.F c i
  tower_property :
    (later.trans earlier).continuatorExpectedValue P.F c futureAct =
      ContinuationStep.stagedContinuatorExpectedValue P.F later earlier c futureAct

/-- Main two-step conditional Born result. -/
theorem twoStepConditionalBornResults
    (P : ProjectiveBornPremises n)
    {future middle present : Perspective n}
    (later : ContinuationStep (Projective.interface n) future middle)
    (earlier : ContinuationStep (Projective.interface n) middle present)
    (c : (Projective.interface n).Cell present)
    (hc : ‖projL c.val P.state‖ ^ 2 ≠ 0)
    (futureAct : ProjectiveAct n) :
    TwoStepConditionalBornResults P later earlier c hc futureAct :=
  { chain_rule := fun i => P.continuatorCredence_chain_rule later earlier c hc i
    summed_chain_rule := fun i => P.sum_intermediateCredence_eq_composite later earlier c hc i
    tower_property := P.continuatorExpectedValue_tower later earlier c hc futureAct }

/-- Integrated stable facade of the conditional Born result. -/
theorem conditionalBornMainResults
    (P : ProjectiveBornPremises n)
    {future middle present : Perspective n}
    (later : ContinuationStep (Projective.interface n) future middle)
    (earlier : ContinuationStep (Projective.interface n) middle present)
    (c : (Projective.interface n).Cell present)
    (hc : ‖projL c.val P.state‖ ^ 2 ≠ 0)
    (presentAct futureAct : ProjectiveAct n) :
    OneStepConditionalBornResults P (later.trans earlier) c hc presentAct futureAct ∧
      TwoStepConditionalBornResults P later earlier c hc futureAct :=
  ⟨oneStepConditionalBornResults P (later.trans earlier) c hc presentAct futureAct,
    twoStepConditionalBornResults P later earlier c hc futureAct⟩

end
end EverettianProbability.API.Conditional
