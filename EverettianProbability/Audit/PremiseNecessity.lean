import EverettianProbability.BornCalibration.DimensionNecessity
import EverettianProbability.BornCalibration.DecisionNecessity
import EverettianProbability.Audit.Minimality

/-!
# L0 premise-necessity and L3 formulation-minimality audit

This audit closes the JAR L0 countermodel campaign at the level of theorem
dependencies.  `W1`--`W5` are relative-necessity witnesses for the five
non-dimensional premises exposed by
`QuantumFoundations.BornRule.grainCoherenceTheorem_projector`; `W0` separately
audits sharpness of the ambient-dimension boundary by an explicit model on
`H 2`.  `D1`--`D3` lift the corresponding deletion tests to the
`RationalExpectationFamily` interface of `born_expectation_of_invariance`,
covering canonical null support, unit-state normalization, and local refinement
invariance.

L3 adds two formulation-minimality results that were previously stated only in
prose: under Grain, `AxNorm` reduces to one singleton-top scalar equation; and
under the released affine law, normalization on all constant acts reduces to
normalization at constants `0` and `1`.

Each declaration is compiled in the public package closure.  The `#print
axioms` commands below make any accidental dependence on an open goal visible;
the Lean workflow additionally fails if their output contains `sorryAx`.
-/

namespace EverettianProbability.Audit

#print axioms EverettianProbability.BornCalibration.w0_dimension_two_countermodel
#print axioms EverettianProbability.BornCalibration.w1_remove_axNorm
#print axioms EverettianProbability.BornCalibration.w2_remove_axNul
#print axioms EverettianProbability.BornCalibration.w3_remove_unit_norm
#print axioms EverettianProbability.BornCalibration.w4_remove_axGrain
#print axioms EverettianProbability.BornCalibration.w5_remove_axPos

#print axioms EverettianProbability.BornCalibration.d1_remove_canonical_null_support
#print axioms EverettianProbability.BornCalibration.d2_remove_unit_norm
#print axioms EverettianProbability.BornCalibration.d3_remove_refinementInvariantLocal

#print axioms axNorm_iff_singletonTop_of_axGrain
#print axioms normalizedConst_iff_zero_one_of_affine

end EverettianProbability.Audit
