import EverettianProbability.ExactFinite.PhysicalAdequacy

/-!
**FR.** # Contrat de l'architecture exacte finie

Ce contrat compilable fixe les noms de la facade exacte finie experimentale.
Elle n'est pas couverte par la stabilite `v1.x` de l'API conditionnelle.

**EN.** # Exact-finite architecture contract

This compilable contract fixes the names of the experimental exact-finite
facade. It is not covered by the conditional API's `v1.x` stability promise.
-/

namespace EverettianProbability.Audit.ExactFiniteArchitectureContract

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core
open EverettianProbability.Abstract
open EverettianProbability.ExactFinite
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : ℕ}

#check SameRecord
#check RecordUnitaryOrbit
#check RecordUnitaryWitness
#check recordUnitaryOrbit_iff_sameRecord
#check sameRecord_iff_exists_recordUnitary
#check nonempty_recordUnitaryWitness_iff_sameRecord
#check FineWeightPlan
#check canonicalTargetState
#check canonicalTargetState_bornWeight
#check canonicalTargetState_sameRecord
#check exists_recordUnitary_realizing_plan
#check CompatibleFineWeights
#check UnitaryRealizesFineWeights
#check PhysicalRealization
#check compatibleFineWeights_iff_unitaryRealizable
#check compatibleFineWeights_iff_nonempty_physicalRealization
#check physicalRealizationOfCompatible
#check exactPhysicalAdequacy
#check exactPhysicalAdequacy_calibrated

example
    (D : Perspective n)
    (x y : H n) :
    RecordUnitaryOrbit D x y ↔ SameRecord D x y :=
  recordUnitaryOrbit_iff_sameRecord D x y

example
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineWeightPlan r x) :
    SameRecord present x (canonicalTargetState plan) :=
  canonicalTargetState_sameRecord plan

example
    {future present : Perspective n}
    (r : Refines future present)
    (x : H n)
    (q : (Projective.interface n).Cell future → ℝ) :
    CompatibleFineWeights r x q ↔ Nonempty (PhysicalRealization r x q) :=
  compatibleFineWeights_iff_nonempty_physicalRealization r x q

end
end EverettianProbability.Audit.ExactFiniteArchitectureContract
