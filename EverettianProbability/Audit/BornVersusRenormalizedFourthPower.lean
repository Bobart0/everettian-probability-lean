import EverettianProbability.Confirmation.BornVersusRenormalizedFourthPower

/-!
**FR.** # Audit E2 — Born contre puissance quatrieme renormalisee

Ce module expose les declarations principales de E2 et imprime leurs
dependances axiomatiques. Il verifie la surface d'audit sans ajouter de
preuve et reste conditionnel au principe CW de Greaves--Myrvold.

**EN.** # E2 audit — Born versus renormalized fourth power

This module exposes the main E2 declarations and prints their axiomatic
dependencies. It checks the audit surface without adding proofs and remains
conditional on the Greaves--Myrvold CW principle.
-/

namespace EverettianProbability.Audit

open EverettianProbability.Confirmation

#check @bornVersusRenormalizedFourthPowerModel
#check @bornVersusRenormalizedFourthPowerModel_likelihood_nonneg
#check @bornVersusRenormalizedFourthPowerModel_likelihood_sum_eq_one
#check @model_likelihood_eq_of_bornAgreement
#check @model_observationLikelihoodProduct_eq_of_bornAgreement
#check @model_evidence_term_eq_of_bornAgreement
#check @model_evidence_eq_two_mul_common_term_of_bornAgreement
#check @model_posteriorWeight_eq_of_bornAgreement
#check @finiteObservationBayesFactor_eq_one_of_bornAgreement
#check @finiteObservationPosteriorOdds_eq_priorOdds_of_bornAgreement
#check @coarse_label0_bayesFactor_eq
#check @coarse_label1_bayesFactor_eq
#check @coarse_label0_posteriorOdds_eq
#check @coarse_label1_posteriorOdds_eq
#check @coarse_label0_batch_bayesFactor_two_eq
#check @coarse_label0_batch_bayesFactor_three_eq

#print axioms EverettianProbability.Confirmation.bornVersusRenormalizedFourthPowerModel
#print axioms EverettianProbability.Confirmation.model_likelihood_eq_of_bornAgreement
#print axioms EverettianProbability.Confirmation.model_observationLikelihoodProduct_eq_of_bornAgreement
#print axioms EverettianProbability.Confirmation.model_evidence_term_eq_of_bornAgreement
#print axioms EverettianProbability.Confirmation.model_posteriorWeight_eq_of_bornAgreement
#print axioms EverettianProbability.Confirmation.finiteObservationBayesFactor_eq_one_of_bornAgreement
#print axioms EverettianProbability.Confirmation.finiteObservationPosteriorOdds_eq_priorOdds_of_bornAgreement
#print axioms EverettianProbability.Confirmation.coarse_label0_bayesFactor_eq
#print axioms EverettianProbability.Confirmation.coarse_label1_bayesFactor_eq
#print axioms EverettianProbability.Confirmation.coarse_label0_batch_bayesFactor_two_eq
#print axioms EverettianProbability.Confirmation.coarse_label0_batch_bayesFactor_three_eq

end EverettianProbability.Audit
