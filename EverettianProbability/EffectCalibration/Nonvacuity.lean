import EverettianProbability.EffectCalibration.QubitWitness

/-!
**FR.** # Non-vacuité — `EffectCalibration`

Cette levée abstraite introduit deux nouvelles structures d'hypothèses :
`Abstract.RationalExpectationFamily` et `Abstract.RefinementInvariantLocal`,
instanciées à `I := Effects.interface n`. Le témoin `EffectCalibration.
QubitWitness.F0` (la famille induite par la règle d'état pur amont, en
`n = 2`) les satisfait toutes les deux à la fois, ainsi que la nullité de
support relative à `spinState` — précisément ce que `spinUp_weight_eq_born`
utilise. Rien de nouveau à prouver ici : ce fichier ne fait que nommer,
comme témoin de non-vacuité, ce que `QubitWitness.lean` établit déjà.

**EN.** # Nonvacuity — `EffectCalibration`

This abstract lift introduces two new hypothesis-bundling structures:
`Abstract.RationalExpectationFamily` and `Abstract.RefinementInvariantLocal`,
instantiated at `I := Effects.interface n`. The witness
`EffectCalibration.QubitWitness.F0` (the family induced by the upstream
pure-state rule, at `n = 2`) satisfies both of them at once, together with
null support relative to `spinState` — precisely what
`spinUp_weight_eq_born` uses. Nothing new to prove here: this file only
names, as the nonvacuity witness, what `QubitWitness.lean` already
establishes.
-/

namespace EverettianProbability.Abstract

/-- **FR.** Témoin de non-vacuité de `RationalExpectationFamily` (niveau
abstrait, instance effets) : `F0` en est un habitant concret.

**EN.** Nonvacuity witness for `RationalExpectationFamily` (abstract
level, effect instance): `F0` is a concrete inhabitant. -/
theorem rationalExpectationFamily_effects_nonvacuous :
    Nonempty (RationalExpectationFamily (Effects.interface 2)) :=
  ⟨F0⟩

/-- **FR.** Témoin de non-vacuité de `RefinementInvariantLocal` (niveau
abstrait, instance effets) : `F0.V` la satisfait.

**EN.** Nonvacuity witness for `RefinementInvariantLocal` (abstract level,
effect instance): `F0.V` satisfies it. -/
theorem refinementInvariantLocal_effects_nonvacuous :
    ∃ F : RationalExpectationFamily (Effects.interface 2), RefinementInvariantLocal F.V :=
  ⟨F0, F0_refinementInvariantLocal⟩

end EverettianProbability.Abstract
