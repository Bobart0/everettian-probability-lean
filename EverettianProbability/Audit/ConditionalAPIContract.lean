import EverettianProbability.API.ConditionalMainResults

/-!
**FR.** # Contrat compilable de l'API conditionnelle

Ce fichier fixe les noms et les types publics de l'API conditionnelle stable
`v1.x`. Il importe uniquement la façade agrégée, afin de détecter toute
rupture de contrat ou toute dépendance d'import non voulue.

**EN.** # Compilable conditional API contract

This file freezes the public names and types of the stable `v1.x`
conditional API. It imports only the aggregate facade, so that it detects
both contract breaks and unintended import dependencies.
-/

namespace EverettianProbability.Audit.ConditionalAPIContract

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core
open EverettianProbability.Abstract
open EverettianProbability.API.Conditional
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : ℕ}

#check ProjectiveAct
#check ProjectiveExpectationFamily
#check ProjectiveBornPremises
#check ProjectiveBornPremises.canonicalWeight_eq_born
#check ProjectiveBornPremises.canonicalWeight_ne_zero_of_bornWeight_ne_zero
#check ProjectiveBornPremises.value_eq_bornExpectation
#check ProjectiveBornPremises.canonicalWeight_nonneg
#check ProjectiveBornPremises.sum_canonicalWeight_eq_one
#check ProjectiveBornPremises.continuatorCredence_eq_bornRatio
#check ProjectiveBornPremises.continuatorExpectedValue_eq_born
#check ProjectiveBornPremises.sum_continuatorCredence_eq_one
#check ProjectiveBornPremises.futureDecisionValue_eq_bornTotalExpectation
#check ProjectiveBornPremises.continuatorCredence_chain_rule
#check ProjectiveBornPremises.sum_intermediateCredence_eq_composite
#check ProjectiveBornPremises.continuatorExpectedValue_tower
#check ProjectiveBornPremises.admissibleCredence_eq_bornRatio
#check OneStepConditionalBornResults
#check TwoStepConditionalBornResults
#check oneStepConditionalBornResults
#check twoStepConditionalBornResults
#check conditionalBornMainResults

example
    (P : ProjectiveBornPremises n)
    (D : Perspective n)
    (a : ProjectiveAct n) :
    P.F.V D a =
      ∑ c ∈ D.cells,
        ‖projL c P.state‖ ^ 2 * a c :=
  P.value_eq_bornExpectation D a

example
    (P : ProjectiveBornPremises n)
    {future present : Perspective n}
    (step :
      ContinuationStep
        (Projective.interface n)
        future present)
    (c : (Projective.interface n).Cell present)
    (hc : ‖projL c.val P.state‖ ^ 2 ≠ 0)
    (presentAct futureAct : ProjectiveAct n) :
    OneStepConditionalBornResults
      P step c hc presentAct futureAct :=
  oneStepConditionalBornResults
    P step c hc presentAct futureAct

example
    (P : ProjectiveBornPremises n)
    {future middle present : Perspective n}
    (later :
      ContinuationStep
        (Projective.interface n)
        future middle)
    (earlier :
      ContinuationStep
        (Projective.interface n)
        middle present)
    (c : (Projective.interface n).Cell present)
    (hc : ‖projL c.val P.state‖ ^ 2 ≠ 0)
    (presentAct futureAct : ProjectiveAct n) :
    OneStepConditionalBornResults
        P
        (later.trans earlier)
        c hc presentAct futureAct
      ∧
    TwoStepConditionalBornResults
        P later earlier c hc futureAct :=
  conditionalBornMainResults
    P later earlier c hc presentAct futureAct

end
end EverettianProbability.Audit.ConditionalAPIContract
