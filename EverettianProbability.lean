import EverettianProbability.Core.Interface
import EverettianProbability.Core.Act
import EverettianProbability.Core.Parent
import EverettianProbability.Core.Nonvacuity
import EverettianProbability.Refinement.PullbackAct
import EverettianProbability.Refinement.PayoffPreserving
import EverettianProbability.Refinement.Nonvacuity
import EverettianProbability.Preference.ExpectationFunctional
import EverettianProbability.Preference.Representation
import EverettianProbability.Preference.Nonvacuity
import EverettianProbability.BornCalibration.ContextualWeight
import EverettianProbability.BornCalibration.RefinementImpliesGrain
import EverettianProbability.BornCalibration.BornExpectation
import EverettianProbability.BornCalibration.NonCircularity
import EverettianProbability.BornCalibration.Nonvacuity
import EverettianProbability.Rivals.NaiveBranchCounting
import EverettianProbability.Rivals.Nonvacuity
import EverettianProbability.Audit.MainResults

/-!
**FR.** Point d'entrée du paquet `EverettianProbability`. Importe tous les
modules du jalon P1, dans l'ordre de dépendance : `Core` (interface,
actes, carte parent), `Refinement` (tiré-en-arrière, invariance),
`Preference` (espérance rationnelle, représentation), `BornCalibration`
(poids contextuel, pont vers Grain, espérance de Born, non-circularité),
`Rivals` (comptage naïf), `Audit` (audit des axiomes).

**EN.** Entry point of the `EverettianProbability` package. Imports every
module of the P1 milestone, in dependency order: `Core` (interface, acts,
parent map), `Refinement` (pullback, invariance), `Preference` (rational
expectation, representation), `BornCalibration` (contextual weight, bridge
to Grain, Born expectation, non-circularity), `Rivals` (naive counting),
`Audit` (axioms audit).
-/
