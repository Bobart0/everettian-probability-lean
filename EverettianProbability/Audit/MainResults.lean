import EverettianProbability.BornCalibration.BornExpectation
import EverettianProbability.BornCalibration.NonCircularity
import EverettianProbability.BornCalibration.Nonvacuity
import EverettianProbability.Core.Interface
import EverettianProbability.Refinement.Nonvacuity
import EverettianProbability.Refinement.NonTriviality
import EverettianProbability.Refinement.GlobalPayoffVacuity
import EverettianProbability.Preference.Nonvacuity
import EverettianProbability.Preference.NonTriviality
import EverettianProbability.Rivals.NaiveBranchCounting
import EverettianProbability.Rivals.FourthPowerWeight
import EverettianProbability.Rivals.Nonvacuity
import EverettianProbability.PhysicalRefinement.RecordNeutralWitness
import EverettianProbability.PhysicalRefinement.Nonvacuity
import EverettianProbability.PhysicalRefinement.NonTriviality
import EverettianProbability.EffectCalibration.EstimationRulePackaging
import EverettianProbability.EffectCalibration.EffectBornExpectation
import EverettianProbability.EffectCalibration.QubitWitness
import EverettianProbability.EffectCalibration.Nonvacuity
import EverettianProbability.EffectCalibration.NonTriviality
import EverettianProbability.Diachronic.Conditioning
import EverettianProbability.Diachronic.NonTriviality
import EverettianProbability.Frequency.HammingCells

/-!
**FR.** # Audit des axiomes — résultats principaux

Un `#print axioms` par déclaration publique majeure, à enrichir au fil des
jalons (voir `docs/THEOREM_MAP.md`). Les déclarations construites sans
but ouvert ne doivent dépendre que de `propext`, `Classical.choice`,
`Quot.sound` (la même signature que l'amont, `Gleason.gleason` inclus) ;
celles qui citent une spécification encore ouverte en amont (directement
ou transitivement) doivent, elles, révéler `sorryAx` — c'est attendu et
documente précisément la dette de ce jalon, en miroir de `SORRY_BUDGET` et
`MILESTONES.md`.

**EN.** # Axiom audit — main results

One `#print axioms` per major public declaration, to be extended milestone
by milestone (see `docs/THEOREM_MAP.md`). Declarations built with no goal
left open must depend only on `propext`, `Classical.choice`, `Quot.sound`
(the same signature as upstream, `Gleason.gleason` included); those that
cite a still-open upstream specification (directly or transitively)
must, conversely, reveal `sorryAx` — this is expected, and it documents
precisely this milestone's debt, mirroring `SORRY_BUDGET` and
`MILESTONES.md`.
-/

namespace EverettianProbability.Audit

open EverettianProbability.Core EverettianProbability.Refinement
open EverettianProbability.Preference EverettianProbability.BornCalibration
open EverettianProbability.Rivals EverettianProbability.PhysicalRefinement

-- No-open-goal declarations: must show only propext / Classical.choice / Quot.sound.
#print axioms pullbackAct_const
#print axioms pullbackAct_agree_of_agree
#print axioms const_payoffEquivalentAt
#print axioms bornExpectation_pullback_eq
#print axioms bornExpectation_refinementInvariant
#print axioms bornExpectation_refinementInvariantLocal
#print axioms uniform_not_refinementInvariantLocal
#print axioms refinementInvariantLocal_iff_pullback
#print axioms globallyPayoffPreserving_const
#print axioms not_globallyPayoffPreserving_indicator
#print axioms globalPremise_vacuous
#print axioms uniformExpectationFamily_globalPremise_vacuous
#print axioms uniformExpectationFamily
#print axioms represents
#print axioms weights_unique_on_cells
#print axioms naiveCounting_axPos
#print axioms EverettianProbability.Abstract.expectation_refinementInvariant
#print axioms EverettianProbability.Abstract.Projective.born_refinementInvariant
#print axioms EverettianProbability.Abstract.Effects.pureState_refinementInvariant
#print axioms refinement_invariant_implies_grain
#print axioms refinementInvariantLocal_iff_axGrain
#print axioms born_expectation_of_invariance
#print axioms born_expectation_formula
#print axioms naiveCounting_violates_grain
#print axioms fourthPowerWeight_axPos
#print axioms fourthPowerWeight_coarse_sum
#print axioms fourthPowerWeight_not_axNorm
#print axioms perspective_two_cases
#print axioms skewWeight_axPos
#print axioms skewWeight_axNul
#print axioms skewWeight_axNorm
#print axioms skewWeight_axGrain
#print axioms grain_does_not_imply_born_at_two
#print axioms maxExpectation_monotone
#print axioms maxExpectation_normalized_const
#print axioms maxExpectation_not_affine
#print axioms recordNeutral_refines
#print axioms recordNeutral_record_eq
#print axioms recordNeutral_payoff_eq
#print axioms recordNeutral_bornWeight_eq
#print axioms refinementNotInRecordAlgebra_holds
#print axioms born_insensitive_to_recordNeutral_refinement
#print axioms born_determined_by_accessible_record
#print axioms counting_sensitive_to_recordNeutral_refinement
#print axioms counting_underdetermined_by_accessible_record

-- Abstract lift (route qubit) and its EffectCalibration instantiation.
-- Fully qualified: several names collide with their concrete counterparts
-- already opened above (represents, canonicalWeight_axPos/axNorm,
-- RefinementInvariantLocal, refinementInvariantLocal_iff_pullback).
#print axioms EverettianProbability.Abstract.Act.agreeOn_refl
#print axioms EverettianProbability.Abstract.Act.agreeOn_symm
#print axioms EverettianProbability.Abstract.Act.agreeOn_trans
#print axioms EverettianProbability.Abstract.Act.indicator_self
#print axioms EverettianProbability.Abstract.Act.indicator_of_ne
#print axioms EverettianProbability.Abstract.Act.agreeOn_indicatorExpansion
#print axioms EverettianProbability.Abstract.V_congr_of_agreeOn
#print axioms EverettianProbability.Abstract.represents
#print axioms EverettianProbability.Abstract.weights_unique_on_cells
#print axioms EverettianProbability.Abstract.canonicalWeight_axPos
#print axioms EverettianProbability.Abstract.canonicalWeight_axNorm
#print axioms EverettianProbability.Abstract.refinementInvariantLocal_iff_pullback
#print axioms EverettianProbability.Abstract.canonicalWeight_grain
#print axioms EverettianProbability.Abstract.outcome_injective_effects
#print axioms EverettianProbability.Abstract.canonicalWeight_familyOfEstimationRule
#print axioms EverettianProbability.Abstract.effectExpectation_represents
#print axioms EverettianProbability.Abstract.effectWeight_eq_born_of_invariance
#print axioms EverettianProbability.Abstract.spinState_norm
#print axioms EverettianProbability.Abstract.spinLine_ne_bot
#print axioms EverettianProbability.Abstract.spinLine_ne_top
#print axioms EverettianProbability.Abstract.spinLine_weight
#print axioms EverettianProbability.Abstract.spinPerspective_effect_zero
#print axioms EverettianProbability.Abstract.F0_refinementInvariantLocal
#print axioms EverettianProbability.Abstract.F0_contextualNullSupport
#print axioms EverettianProbability.Abstract.spinUp_weight_eq_born
#print axioms EverettianProbability.Abstract.rationalExpectationFamily_effects_nonvacuous
#print axioms EverettianProbability.Abstract.refinementInvariantLocal_effects_nonvacuous
#print axioms EverettianProbability.Abstract.effectPerspective_outcomes_pos
#print axioms EverettianProbability.Abstract.pullbackAct_effects_apply
#print axioms EverettianProbability.Abstract.effectUniformCredence_coarse
#print axioms EverettianProbability.Abstract.effectUniformCredence_fine
#print axioms EverettianProbability.Abstract.effectUniform_not_refinementInvariantLocal

-- Static conditioning under refinement (P8): no record or temporal dynamics.
#print axioms EverettianProbability.Abstract.conditionalWeight_zero_of_not_in_fiber
#print axioms EverettianProbability.Abstract.conditionalWeight_nonneg
#print axioms EverettianProbability.Abstract.conditionalWeight_sum_eq_zero_or_one
#print axioms EverettianProbability.Abstract.conditionalWeight_normalized
#print axioms EverettianProbability.Abstract.conditionalExpectation_pullback_eq_of_weight_ne_zero
#print axioms EverettianProbability.Abstract.conditionalExpectation_total
#print axioms EverettianProbability.Abstract.conditionalWeight_trans_fiber
#print axioms EverettianProbability.Diachronic.uniformProjectiveExpectationFamily
#print axioms EverettianProbability.Diachronic.uniform_conditionalWeight_trans_fiber_lhs
#print axioms EverettianProbability.Diachronic.uniform_conditionalWeight_trans_fiber_rhs
#print axioms EverettianProbability.Diachronic.uniform_conditionalWeight_trans_fiber_fails

#print axioms EverettianProbability.Frequency.configurationBasis_mem_frequencySitesCell
#print axioms EverettianProbability.Frequency.frequencySitesCell_ortho
#print axioms EverettianProbability.Frequency.configurationBranch_norm
#print axioms EverettianProbability.Frequency.configurationBranch_ne_zero
#print axioms EverettianProbability.Frequency.configurationBranch_inner_eq_zero_of_ne
#print axioms EverettianProbability.Frequency.configurationBranch_mem_frequencyCell
#print axioms EverettianProbability.Frequency.frequencyCell_ortho
#print axioms EverettianProbability.Frequency.frequencySitesCell_iSup
#print axioms EverettianProbability.Frequency.frequencyCell_iSup
#print axioms EverettianProbability.Frequency.hammingWeight_le
#print axioms EverettianProbability.Frequency.frequencySitesCell_eq_bot_of_lt
#print axioms EverettianProbability.Frequency.frequencyCell_eq_bot_of_lt
#print axioms EverettianProbability.Frequency.frequencySitesCell_iSup_fin
#print axioms EverettianProbability.Frequency.frequencyCell_iSup_fin
#print axioms EverettianProbability.Frequency.hammingWeight_prefixConfiguration
#print axioms EverettianProbability.Frequency.frequencyCell_ne_bot

end EverettianProbability.Audit
