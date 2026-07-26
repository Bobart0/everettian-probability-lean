import EverettianProbability.BornCalibration.BornExpectation
import EverettianProbability.BornCalibration.Nonvacuity
import EverettianProbability.Core.Interface
import EverettianProbability.Refinement.Nonvacuity
import EverettianProbability.Preference.Nonvacuity
import EverettianProbability.Rivals.NaiveBranchCounting
import EverettianProbability.Rivals.Nonvacuity

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
open EverettianProbability.Rivals

-- No-open-goal declarations: must show only propext / Classical.choice / Quot.sound.
#print axioms pullbackAct_const
#print axioms pullbackAct_agree_of_agree
#print axioms const_payoffPreserving
#print axioms bornExpectation_pullback_eq
#print axioms bornExpectation_refinementInvariant
#print axioms uniformExpectationFamily
#print axioms naiveCounting_axPos
#print axioms EverettianProbability.Abstract.expectation_refinementInvariant
#print axioms EverettianProbability.Abstract.Projective.born_refinementInvariant
#print axioms EverettianProbability.Abstract.Effects.pureState_refinementInvariant

-- Open-goal-carrying declarations (directly or transitively): must show `sorryAx`.
#print axioms exists_unique_weights
#print axioms refinement_invariant_implies_grain
#print axioms born_expectation_formula
#print axioms naiveCounting_violates_grain

end EverettianProbability.Audit
