import EverettianProbability.ExactFinite.MainResults

/-!
**FR.** # Contrat de complétude exacte finie

Ce fichier compile le contrat du deuxième résultat exact fini. Il ne
stabilise pas encore cette API pour `v1.x`, distingue strictement les
couches CORE et CALIBRATED, et ne couvre aucune décohérence approximative.

**EN.** # Exact-finite completeness contract

This file compiles the contract of the second exact-finite result. It
does not yet stabilize this API for `v1.x`, strictly distinguishes CORE
from CALIBRATED, and covers no approximate decoherence.
-/

namespace EverettianProbability.Audit.ExactFiniteCompletenessAudit

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core
open EverettianProbability.Abstract
open EverettianProbability.ExactFinite
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : ℕ}

#check ExactFiniteCalibrationPremises
#check ExactFiniteCoreResults
#check ExactFiniteCalibratedResults
#check ExactFiniteMainResults
#check exactFiniteCoreResults
#check exactFiniteCalibratedResults
#check exactFiniteMainResults

example
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q) :
    ExactFiniteCoreResults h :=
  exactFiniteCoreResults h

example
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q)
    (P : ExactFiniteCalibrationPremises h)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0) :
    ExactFiniteCalibratedResults h P c hc :=
  exactFiniteCalibratedResults h P c hc

example
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q)
    (P : ExactFiniteCalibrationPremises h)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0) :
    ExactFiniteMainResults h P c hc :=
  exactFiniteMainResults h P c hc

end
end EverettianProbability.Audit.ExactFiniteCompletenessAudit
