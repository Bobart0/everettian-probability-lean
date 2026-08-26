import EverettianProbability.Preference.Representation
import EverettianProbability.BornCalibration.RefinementImpliesGrain
import EverettianProbability.BornCalibration.BornExpectation
import EverettianProbability.BornCalibration.NonCircularity
import EverettianProbability.BornCalibration.DecisionNonCircularity
import EverettianProbability.Refinement.GlobalPayoffVacuity
import EverettianProbability.Rivals.NaiveBranchCounting
import EverettianProbability.Rivals.FourthPowerWeight
import EverettianProbability.API.ConditionalMainResults
import EverettianProbability.Audit.PremiseNecessity
import EverettianProbability.Audit.UhlhornDimensionTwo

/-!
# Journal audit: publication-facing theorem interfaces

**EN.** This publication-facing module is the consolidated trust-base audit for
the journal-revision release. It checks public signatures (`#check`) and
invokes `#print axioms` on the declarations used by the manuscript, without
modifying any theorem body.

It retains the earlier checks for representation/uniqueness infrastructure,
the Grain bridge, the weight-, decision-, and projection-measure-level
countermodels, the rival-weight witnesses, and the stable conditional API
aggregate. The journal-revision campaign adds four groups:

- `W0`--`W5`, the weight-level dimension-sharpness and relative-necessity
  witnesses for the exposed Born-calibration premises;
- `D1`--`D3`, the corresponding deletion tests at the
  `RationalExpectationFamily` interface;
- the two L3 formulation-minimality results, one for weight normalization
  under Grain and one for constant normalization of a raw affine valuation;
- the L2 dimension-two one-way Uhlhorn boundary witness
  `dimensionTwo_orthogonality_not_injective`.

Every declaration below is expected to be free of `sorryAx`; the ordinary
Lean/Mathlib logical axioms reported by `#print axioms` are not project axioms.

**FR.** Ce module destiné à la publication constitue l'audit consolidé de la
base de confiance pour la release de révision du journal. Il vérifie les
signatures publiques (`#check`) et invoque `#print axioms` sur les déclarations
utilisées par le manuscrit, sans modifier aucun corps de preuve.

Il conserve les contrôles antérieurs sur l'infrastructure de
représentation/unicité, le pont Grain, les contre-modèles aux niveaux poids,
décision et mesure de projection, les poids rivaux et l'agrégat d'API
conditionnelle stable. La campagne de révision ajoute quatre groupes :

- `W0`--`W5`, témoins de netteté dimensionnelle et de nécessité relative au
  niveau poids pour les prémisses exposées de calibration de Born ;
- `D1`--`D3`, tests de suppression correspondants à l'interface
  `RationalExpectationFamily` ;
- les deux résultats L3 de minimalité de formulation, pour la normalisation
  des poids sous Grain et pour la normalisation des constantes d'une valuation
  affine brute ;
- le témoin L2 de frontière Uhlhorn one-way en dimension deux
  `dimensionTwo_orthogonality_not_injective`.

Toutes les déclarations ci-dessous doivent être exemptes de `sorryAx`; les
axiomes logiques ordinaires Lean/Mathlib rapportés par `#print axioms` ne sont
pas des axiomes propres au projet.
-/

open EverettianProbability.Preference
open EverettianProbability.BornCalibration
open EverettianProbability.Refinement
open EverettianProbability.Rivals
open EverettianProbability.API.Conditional

-- ── Public-contract visibility: previously released surface ──────────

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

-- ── Public-contract visibility: JAR L0/L2/L3 campaign ────────────────

#check @EverettianProbability.BornCalibration.w0_dimension_two_countermodel
#check @EverettianProbability.BornCalibration.w1_remove_axNorm
#check @EverettianProbability.BornCalibration.w2_remove_axNul
#check @EverettianProbability.BornCalibration.w3_remove_unit_norm
#check @EverettianProbability.BornCalibration.w4_remove_axGrain
#check @EverettianProbability.BornCalibration.w5_remove_axPos
#check @EverettianProbability.BornCalibration.d1_remove_canonical_null_support
#check @EverettianProbability.BornCalibration.d2_remove_unit_norm
#check @EverettianProbability.BornCalibration.d3_remove_refinementInvariantLocal
#check @EverettianProbability.Audit.axNorm_iff_singletonTop_of_axGrain
#check @EverettianProbability.Audit.normalizedConst_iff_zero_one_of_affine
#check @EverettianProbability.Audit.dimensionTwo_orthogonality_not_injective

-- ── Trust-base audit: previously released surface ────────────────────

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

-- ── Trust-base audit: JAR L0/L2/L3 campaign ──────────────────────────

#print axioms EverettianProbability.BornCalibration.w0_dimension_two_countermodel
#print axioms EverettianProbability.BornCalibration.w1_remove_axNorm
#print axioms EverettianProbability.BornCalibration.w2_remove_axNul
#print axioms EverettianProbability.BornCalibration.w3_remove_unit_norm
#print axioms EverettianProbability.BornCalibration.w4_remove_axGrain
#print axioms EverettianProbability.BornCalibration.w5_remove_axPos
#print axioms EverettianProbability.BornCalibration.d1_remove_canonical_null_support
#print axioms EverettianProbability.BornCalibration.d2_remove_unit_norm
#print axioms EverettianProbability.BornCalibration.d3_remove_refinementInvariantLocal
#print axioms EverettianProbability.Audit.axNorm_iff_singletonTop_of_axGrain
#print axioms EverettianProbability.Audit.normalizedConst_iff_zero_one_of_affine
#print axioms EverettianProbability.Audit.dimensionTwo_orthogonality_not_injective
