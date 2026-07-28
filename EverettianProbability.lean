import EverettianProbability.Core.Interface
import EverettianProbability.Core.Act
import EverettianProbability.Core.AbstractAct
import EverettianProbability.Core.Nonvacuity
import EverettianProbability.Refinement.PullbackAct
import EverettianProbability.Refinement.PayoffPreserving
import EverettianProbability.Refinement.AbstractPayoffPreserving
import EverettianProbability.Refinement.GlobalPayoffVacuity
import EverettianProbability.Refinement.Nonvacuity
import EverettianProbability.Refinement.NonTriviality
import EverettianProbability.Preference.ExpectationFunctional
import EverettianProbability.Preference.AbstractExpectationFunctional
import EverettianProbability.Preference.Representation
import EverettianProbability.Preference.AbstractRepresentation
import EverettianProbability.Preference.Nonvacuity
import EverettianProbability.Preference.NonTriviality
import EverettianProbability.BornCalibration.ContextualWeight
import EverettianProbability.BornCalibration.AbstractContextualWeight
import EverettianProbability.BornCalibration.RefinementImpliesGrain
import EverettianProbability.BornCalibration.AbstractRefinementImpliesGrain
import EverettianProbability.BornCalibration.BornExpectation
import EverettianProbability.BornCalibration.NonCircularity
import EverettianProbability.BornCalibration.Nonvacuity
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
import EverettianProbability.Frequency.HammingCounting
import EverettianProbability.Frequency.RepetitionVector
import EverettianProbability.Frequency.CellProjection
import EverettianProbability.Frequency.Distribution
import EverettianProbability.Frequency.Moments
import EverettianProbability.Frequency.Concentration
import EverettianProbability.Frequency.Typicality
import EverettianProbability.Frequency.AsymptoticTypicality
import EverettianProbability.Confirmation.FiniteBayes
import EverettianProbability.Confirmation.FrequencyModel
import EverettianProbability.Confirmation.PosteriorOdds
import EverettianProbability.Confirmation.HypothesisComparison
import EverettianProbability.Confirmation.RationalWitness
import EverettianProbability.Confirmation.SequentialUpdate
import EverettianProbability.Confirmation.FiniteObservationBatch
import EverettianProbability.Confirmation.IteratedUpdate
import EverettianProbability.Confirmation.BatchPosteriorOdds
import EverettianProbability.Audit.MainResults

/-!
**FR.** Point d'entrée du paquet `EverettianProbability`. Importe tous les
modules, dans l'ordre de dépendance : `Core` (interface, actes, carte
parent, actes abstraits), `Refinement` (tiré-en-arrière, invariance,
invariance abstraite), `Preference` (espérance rationnelle,
représentation, et leurs levées abstraites), `BornCalibration` (poids
contextuel, pont vers Grain, espérance de Born, non-circularité, et leurs
levées abstraites), `Rivals` (comptage naïf et témoin de puissance quatrième), `PhysicalRefinement` (témoin
physique du raffinement record-neutre, P6a), `EffectCalibration` (route
qubit : empaquetage en règle d'estimation d'effets, espérance de Born
côté effets pour tout `n ≥ 1`, témoin concret en `n = 2`), `Diachronic`
(conditionnement statique sur fibres de raffinement : aucune dynamique
temporelle, aucun continuateur et aucun record accessible ne sont formalisés),
puis `Audit` (audit des axiomes).

**EN.** Entry point of the `EverettianProbability` package. Imports every
module, in dependency order: `Core` (interface, acts, parent map,
abstract acts), `Refinement` (pullback, invariance, abstract invariance),
`Preference` (rational expectation, representation, and their abstract
lifts), `BornCalibration` (contextual weight, bridge to Grain, Born
expectation, non-circularity, and their abstract lifts), `Rivals` (naive
counting and fourth-power witness), `PhysicalRefinement` (physical witness of the record-neutral
refinement, P6a), `EffectCalibration` (qubit route: packaging into an
effect estimation rule, effect-side Born expectation for every `n ≥ 1`,
concrete `n = 2` witness), `Diachronic` (static conditioning on refinement
fibers: no temporal dynamics, continuator, or accessible record is
formalized), then `Audit` (axioms audit).
-/
