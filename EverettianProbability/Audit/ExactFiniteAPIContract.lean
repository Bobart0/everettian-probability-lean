import EverettianProbability.API.ExactFiniteMainResults

/-!
**FR.** # Contrat de l'API exacte finie

Ce fichier fixe les noms et les types publics de l'API exacte finie `v2.x`.

**EN.** # Exact-finite API contract

This file freezes the public names and types of the `v2.x` exact-finite API.
-/

namespace EverettianProbability.Audit.ExactFiniteAPIContract

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core
open EverettianProbability.Abstract
open EverettianProbability.API.ExactFinite
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : ℕ}

#check SameRecord
#check RecordUnitaryOrbit
#check FineWeightPlan
#check CompatibleFineWeights
#check UnitaryRealizesFineWeights
#check PhysicalRealization
#check canonicalTargetState
#check canonicalPhysicalRealization
#check prescribedRatio
#check recordUnitaryOrbit_iff_sameRecord
#check canonicalTargetState_bornWeight
#check canonicalTargetState_sameRecord
#check compatibleFineWeights_iff_unitaryRealizable
#check compatibleFineWeights_iff_nonempty_physicalRealization
#check ExactFiniteCalibrationPremises
#check ExactFiniteCoreResults
#check ExactFiniteCalibratedResults
#check ExactFiniteNullParentResults
#check ExactFiniteMainResults
#check exactFiniteCoreResults
#check exactFiniteCalibratedResults
#check exactFiniteNullParentResults
#check exactFiniteMainResults
#check exactPhysicalAdequacy

example (D : Perspective n) (x y : H n) :
    RecordUnitaryOrbit D x y ↔ SameRecord D x y :=
  recordUnitaryOrbit_iff_sameRecord D x y

example
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q) :
    ExactFiniteCoreResults h :=
  exactFiniteCoreResults h

example
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q)
    (P : ExactFiniteCalibrationPremises h)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0) :
    ExactFiniteMainResults h P c hc :=
  exactFiniteMainResults h P c hc

example
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c = 0) :
    ExactFiniteNullParentResults h c hc :=
  exactFiniteNullParentResults h c hc

end
end EverettianProbability.Audit.ExactFiniteAPIContract
