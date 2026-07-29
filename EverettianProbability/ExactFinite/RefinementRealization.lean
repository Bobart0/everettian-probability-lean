import EverettianProbability.ExactFinite.RecordOrbit
import EverettianProbability.Diachronic.FineBornWeightRealization

/-!
**FR.** # Realisation geometrique d'un plan de poids fin

Cette facade experimentale expose les plans positifs de poids fins, leur etat
cible canonique et leur realisation unitaire. Elle n'interprete pas encore ce
fait comme une continuation physique complete.

**EN.** # Geometric realization of a fine-weight plan

This experimental facade exposes positive fine-weight plans, their canonical
target states, and their unitary realization. It does not yet interpret that
fact as a complete physical continuation.
-/

namespace EverettianProbability.ExactFinite

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core
open EverettianProbability.Abstract
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : ℕ}

/-- Positive future weight profile compatible fibrewise with the present Born
record. -/
abbrev FineWeightPlan
    {future present : Perspective n}
    (r : Refines future present)
    (x : H n) :=
  EverettianProbability.Abstract.FineBornWeightPlan r x

/-- Canonical target state associated with a compatible fine-weight plan. -/
noncomputable def canonicalTargetState
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineWeightPlan r x) : H n :=
  EverettianProbability.Abstract.FineBornWeightPlan.fineWeightTargetState plan

theorem canonicalTargetState_bornWeight
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineWeightPlan r x)
    (i : (Projective.interface n).Cell future) :
    bornRecord future (canonicalTargetState plan) i = plan.weight i := by
  exact EverettianProbability.Abstract.FineBornWeightPlan.fineWeightTargetState_bornWeight plan i

theorem canonicalTargetState_sameRecord
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineWeightPlan r x) :
    SameRecord present x (canonicalTargetState plan) := by
  exact EverettianProbability.Abstract.FineBornWeightPlan.fineWeightTargetState_sameBornRecord plan

theorem canonicalTargetState_norm_eq
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineWeightPlan r x) :
    ‖canonicalTargetState plan‖ = ‖x‖ := by
  exact EverettianProbability.Abstract.FineBornWeightPlan.fineWeightTargetState_norm_eq plan

theorem canonicalTargetState_normalized
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineWeightPlan r x)
    (hx : ‖x‖ = 1) :
    ‖canonicalTargetState plan‖ = 1 := by
  exact EverettianProbability.Abstract.FineBornWeightPlan.fineWeightTargetState_normalized plan hx

/-- Every compatible fine-weight plan is realized by a global unitary internal
to the present record blocks. -/
theorem exists_recordUnitary_realizing_plan
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineWeightPlan r x) :
    ∃ U : H n ≃ₗᵢ[ℂ] H n,
      CommutesWithPerspectiveProjectors present U.toLinearEquiv.toLinearMap ∧
        U x = canonicalTargetState plan ∧
          ∀ i : (Projective.interface n).Cell future,
            bornRecord future (U x) i = plan.weight i := by
  exact
    EverettianProbability.Abstract.FineBornWeightPlan.exists_projectorCommutingUnitary_realizing_fineBornWeightPlan
      plan

/-- Explicit target-state and record-unitary realization form. -/
theorem exists_target_and_recordUnitary_realizing_plan
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineWeightPlan r x) :
    ∃ y : H n,
      SameRecord present x y ∧
        (∀ i : (Projective.interface n).Cell future,
          bornRecord future y i = plan.weight i) ∧
        Nonempty (RecordUnitaryWitness present x y) := by
  refine ⟨canonicalTargetState plan, canonicalTargetState_sameRecord plan,
    canonicalTargetState_bornWeight plan, ?_⟩
  obtain ⟨U, hCommutes, hMap, _⟩ := exists_recordUnitary_realizing_plan plan
  exact ⟨{ unitary := U, commutes := hCommutes, maps_state := hMap }⟩

noncomputable def fineWeightPlanOfTargetState
    {future present : Perspective n}
    (r : Refines future present)
    (x y : H n)
    (hRecord : SameRecord present x y) :
    FineWeightPlan r x :=
  EverettianProbability.Abstract.FineBornWeightPlan.ofTargetState r x y hRecord

@[simp]
theorem fineWeightPlanOfTargetState_weight
    {future present : Perspective n}
    (r : Refines future present)
    (x y : H n)
    (hRecord : SameRecord present x y)
    (i : (Projective.interface n).Cell future) :
    (fineWeightPlanOfTargetState r x y hRecord).weight i =
      bornRecord future y i := by
  rfl

end
end EverettianProbability.ExactFinite
