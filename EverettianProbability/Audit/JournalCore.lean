import EverettianProbability.Preference.Representation
import EverettianProbability.BornCalibration.RefinementImpliesGrain
import EverettianProbability.BornCalibration.BornExpectation
import EverettianProbability.BornCalibration.NonCircularity
import EverettianProbability.BornCalibration.DecisionNonCircularity
import EverettianProbability.Refinement.GlobalPayoffVacuity
import EverettianProbability.Rivals.NaiveBranchCounting
import EverettianProbability.Rivals.FourthPowerWeight
import EverettianProbability.API.ConditionalMainResults

/-!
# Journal audit: decision-level non-Born countermodel and its infrastructure

**EN.** This publication-facing module is a focused corrective audit for the
coordinated journal-audit release. It checks, independently of the
repository's broader audit surface (`Audit/MainResults.lean`), the exact
public-contract shape and trust base of the new decision-level countermodel
and the results it composes:

- the representation/uniqueness infrastructure (`represents`,
  `canonicalWeight_axPos`, `canonicalWeight_axNorm`);
- the Grain bridge (`refinementInvariantLocal_iff_axGrain`) and the headline
  conditional theorem it feeds (`born_expectation_of_invariance`);
- the weight-level countermodel (`grain_does_not_imply_born_at_two`);
- the decision-level infrastructure and countermodel
  (`skewExpectationFamily`, `skewExpectationFamily_canonicalWeight_eq`,
  `skewExpectationFamily_refinementInvariantLocal`,
  `decision_premises_do_not_imply_born_at_two`);
- the new projection-measure-level countermodel (`skewProjMeasure`,
  `skewProjMeasure_not_representable`,
  `exists_nonrepresentable_projMeasure_two`): a dimension-two
  `Gleason.ProjMeasure` representable by no density operator via
  `Gleason.bornValue`, completing the weight-level and decision-level
  countermodels with a third, measure-level witness;
- the two rival-weight witnesses (`globalPremise_vacuous`,
  `uniformExpectationFamily_globalPremise_vacuous`,
  `naiveCounting_violates_grain`, `fourthPowerWeight_not_axNorm`);
- the unchanged stable conditional API aggregate
  (`conditionalBornMainResults`), audited here only to confirm this release
  introduces no regression to it.

This module does not modify any theorem body; it only checks public
signatures (`#check`) and invokes `#print axioms` on already-proved
declarations. Every declaration below is expected to depend only on the
standard Lean/Mathlib kernel trio `[propext, Classical.choice, Quot.sound]`.

**FR.** Ce module, destiné à la publication, est un audit correctif ciblé
pour la release coordonnée d'audit pré-journal. Il vérifie, indépendamment de
la surface d'audit plus large du dépôt (`Audit/MainResults.lean`), la forme
exacte du contrat public et la base de confiance du nouveau contre-modèle
niveau décision et des résultats qu'il compose :

- l'infrastructure de représentation/unicité (`represents`,
  `canonicalWeight_axPos`, `canonicalWeight_axNorm`) ;
- le pont vers Grain (`refinementInvariantLocal_iff_axGrain`) et le théorème
  conditionnel principal qu'il alimente (`born_expectation_of_invariance`) ;
- le contre-modèle niveau poids (`grain_does_not_imply_born_at_two`) ;
- l'infrastructure et le contre-modèle niveau décision
  (`skewExpectationFamily`, `skewExpectationFamily_canonicalWeight_eq`,
  `skewExpectationFamily_refinementInvariantLocal`,
  `decision_premises_do_not_imply_born_at_two`) ;
- le nouveau contre-modèle niveau mesure-de-projection (`skewProjMeasure`,
  `skewProjMeasure_not_representable`,
  `exists_nonrepresentable_projMeasure_two`) : une `Gleason.ProjMeasure` en
  dimension 2 représentable par aucun opérateur densité au sens de
  `Gleason.bornValue`, complétant les contre-modèles niveau poids et niveau
  décision par un troisième témoin, niveau mesure ;
- les deux témoins de poids rivaux (`globalPremise_vacuous`,
  `uniformExpectationFamily_globalPremise_vacuous`,
  `naiveCounting_violates_grain`, `fourthPowerWeight_not_axNorm`) ;
- l'agrégat d'API conditionnelle stable inchangé
  (`conditionalBornMainResults`), audité ici seulement pour confirmer que
  cette release ne lui introduit aucune régression.

Ce module ne modifie aucun corps de preuve ; il ne fait que vérifier des
signatures publiques (`#check`) et invoquer `#print axioms` sur des
déclarations déjà démontrées.
-/

open EverettianProbability.Preference
open EverettianProbability.BornCalibration
open EverettianProbability.Refinement
open EverettianProbability.Rivals
open EverettianProbability.API.Conditional

-- ── Public-contract visibility ──────────────────────────────────────

#check @represents
#check @canonicalWeight_axPos
#check @canonicalWeight_axNorm
#check @refinementInvariantLocal_iff_axGrain
#check @born_expectation_of_invariance
#check @grain_does_not_imply_born_at_two
#check @skewExpectationFamily
#check @skewExpectationFamily_canonicalWeight_eq
#check @skewExpectationFamily_refinementInvariantLocal
#check @decision_premises_do_not_imply_born_at_two
#check @skewProjMeasure
#check @skewProjMeasure_not_representable
#check @exists_nonrepresentable_projMeasure_two
#check @globalPremise_vacuous
#check @uniformExpectationFamily_globalPremise_vacuous
#check @naiveCounting_violates_grain
#check @fourthPowerWeight_not_axNorm
#check @conditionalBornMainResults

-- ── Trust-base audit ─────────────────────────────────────────────────

#print axioms EverettianProbability.Preference.represents
#print axioms EverettianProbability.Preference.canonicalWeight_axPos
#print axioms EverettianProbability.Preference.canonicalWeight_axNorm
#print axioms EverettianProbability.BornCalibration.refinementInvariantLocal_iff_axGrain
#print axioms EverettianProbability.BornCalibration.born_expectation_of_invariance
#print axioms EverettianProbability.BornCalibration.grain_does_not_imply_born_at_two
#print axioms EverettianProbability.BornCalibration.skewExpectationFamily
#print axioms EverettianProbability.BornCalibration.skewExpectationFamily_canonicalWeight_eq
#print axioms EverettianProbability.BornCalibration.skewExpectationFamily_refinementInvariantLocal
#print axioms EverettianProbability.BornCalibration.decision_premises_do_not_imply_born_at_two
#print axioms EverettianProbability.BornCalibration.skewProjMeasure
#print axioms EverettianProbability.BornCalibration.skewProjMeasure_not_representable
#print axioms EverettianProbability.BornCalibration.exists_nonrepresentable_projMeasure_two
#print axioms EverettianProbability.Refinement.globalPremise_vacuous
#print axioms EverettianProbability.Refinement.uniformExpectationFamily_globalPremise_vacuous
#print axioms EverettianProbability.Rivals.naiveCounting_violates_grain
#print axioms EverettianProbability.Rivals.fourthPowerWeight_not_axNorm
#print axioms EverettianProbability.API.Conditional.conditionalBornMainResults
