import EverettianProbability.ExactFinite.MainResults

/-!
**FR.** # Audit contradictoire de la couche exacte finie

Ce fichier compile les frontières de prémisses, y compris le cas d'une
cellule parente de poids nul. Il ne stabilise pas encore l'API exacte finie,
n'ajoute aucune conclusion physique, et n'établit ni décohérence ni
Hamiltonien réaliste.

**EN.** # Contradictory audit of the exact-finite layer

This file compiles premise boundaries, including the zero-weight parent-cell
case. It does not yet stabilize the exact-finite API, adds no physical
conclusion, and establishes neither decoherence nor a realistic Hamiltonian.
-/

namespace EverettianProbability.Audit.ExactFiniteContradictoryAudit

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core
open EverettianProbability.Abstract
open EverettianProbability.ExactFinite
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : ℕ}

#check CompatibleFineWeights
#check compatibleFineWeights_iff_unitaryRealizable
#check compatibleFineWeights_iff_nonempty_physicalRealization

#check ExactFiniteCoreResults
#check exactFiniteCoreResults

#check ExactFiniteCalibrationPremises
#check ExactFiniteCalibratedResults
#check exactFiniteCalibratedResults

#check ExactFiniteMainResults
#check exactFiniteMainResults

#check compatibleFineWeight_eq_zero_of_parentWeight_eq_zero
#check prescribedRatio_eq_zero_of_parentWeight_eq_zero
#check ExactFiniteNullParentResults
#check exactFiniteNullParentResults

example
    {future present : Perspective n}
    (r : Refines future present)
    (x : H n)
    (q : (Projective.interface n).Cell future → ℝ) :
    CompatibleFineWeights r x q ↔
      Nonempty (PhysicalRealization r x q) :=
  compatibleFineWeights_iff_nonempty_physicalRealization r x q

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
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c = 0) :
    ExactFiniteNullParentResults h c hc :=
  exactFiniteNullParentResults h c hc

end
end EverettianProbability.Audit.ExactFiniteContradictoryAudit
