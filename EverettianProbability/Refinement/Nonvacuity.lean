import EverettianProbability.Refinement.PayoffPreserving
import EverettianProbability.Core.Nonvacuity

/-!
**FR.** # Non-vacuité — `Refinement`

Témoin concret : deux actes constants de même valeur sont localement
équivalents pour n'importe quel raffinement. Preuve complète, aucun but ouvert.

Le témoin fort fixe en outre le premier vecteur de base de `H 3`, la
perspective binaire explicite de `Core.Nonvacuity` et son raffinement concret.
L'espérance bornienne est globalement invariante et ses valeurs sur l'acte
constant unité sont calculées à `1` des deux côtés du raffinement.

**EN.** # Nonvacuity — `Refinement`

Concrete witness: two constant acts with the same value are locally equivalent
for any refinement. Full proof, no goal left open.

The strong witness additionally fixes the first basis vector of `H 3`, the
explicit binary perspective from `Core.Nonvacuity`, and its concrete
refinement. Born expectation is globally invariant, and its values on the
constant unit act are computed to be `1` on both sides of the refinement.
-/

namespace EverettianProbability.Refinement

open QuantumFoundations.BornRule Gleason EverettianProbability.Core

variable {n : ℕ}

/-- **FR.** Deux descriptions constantes identiques sont équivalentes.

**EN.** Two identical constant descriptions are equivalent. -/
theorem const_payoffEquivalentAt {D' D : Perspective n} (r : Refines D' D) (k : ℝ) :
    PayoffEquivalentAt r (Act.const k) (Act.const k : Act n) := by
  intro c' _hc'
  rfl

/-- Concrete unit state: the first standard basis vector of `H 3`. -/
noncomputable def exampleState : H 3 :=
  EuclideanSpace.single (0 : Fin 3) 1

theorem exampleState_norm : ‖exampleState‖ = 1 := by
  simp [exampleState]

/-- A concrete inhabitant of the central normative premise. -/
theorem exampleBorn_refinementInvariant :
    RefinementInvariantLocal (bornExpectation exampleState) :=
  bornExpectation_refinementInvariantLocal exampleState

private theorem exampleBornExpectation_const_one (D : Perspective 3) :
    bornExpectation exampleState D (Act.const 1) = 1 := by
  have hnorm :=
    (QuantumFoundations.ProbabilityAPI.BornRule.E₀_satisfies_axioms
      exampleState exampleState_norm).2.1 D
  simpa only [bornExpectation, Act.const, mul_one,
    QuantumFoundations.ProbabilityAPI.BornRule.E₀] using hnorm

/-- Computed values on the explicit binary perspective and its concrete
strict refinement: both Born expectations are `1`. -/
theorem exampleBornExpectation_values :
    bornExpectation exampleState EverettianProbability.Core.exampleFine
        (pullbackAct EverettianProbability.Core.exampleFine_refines
          (Act.const 1 : Act 3)) = 1 ∧
      bornExpectation exampleState EverettianProbability.Core.exampleCoarse
        (Act.const 1 : Act 3) = 1 := by
  constructor
  · rw [bornExpectation_pullback_eq exampleState
      EverettianProbability.Core.exampleFine
      EverettianProbability.Core.exampleCoarse
      EverettianProbability.Core.exampleFine_refines]
    exact exampleBornExpectation_const_one EverettianProbability.Core.exampleCoarse
  · exact exampleBornExpectation_const_one EverettianProbability.Core.exampleCoarse

end EverettianProbability.Refinement
