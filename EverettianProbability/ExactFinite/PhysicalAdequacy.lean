import EverettianProbability.ExactFinite.RefinementRealization
import EverettianProbability.API.ExactFinitePhysicalRichness

/-!
**FR.** # Adequation physique exacte finie

Ce module est le point d'entree recommande de la couche experimentale exacte
finie. Sa conclusion est exacte, projective et finie; la facade conditionnelle
`v1.x` reste independante. Aucune decoherence approximative ni naturalite
hamiltonienne n'est etablie.

**EN.** # Exact finite physical adequacy

This module is the recommended entry point for the experimental exact finite
layer. Its conclusion is exact, projective, and finite; the conditional `v1.x`
facade remains independent. No approximate decoherence or Hamiltonian
naturalness is established.
-/

namespace EverettianProbability.ExactFinite

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core
open EverettianProbability.Abstract
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : ℕ}

abbrev CompatibleFineWeights
    {future present : Perspective n}
    (r : Refines future present)
    (x : H n)
    (q : (Projective.interface n).Cell future → ℝ) : Prop :=
  EverettianProbability.API.CompatibleFineBornWeights r x q

abbrev UnitaryRealizesFineWeights
    {future present : Perspective n}
    (r : Refines future present)
    (x : H n)
    (q : (Projective.interface n).Cell future → ℝ) : Prop :=
  EverettianProbability.API.ProjectorCommutingUnitaryRealizesFineWeights r x q

abbrev PhysicalRealization
    {future present : Perspective n}
    (r : Refines future present)
    (x : H n)
    (q : (Projective.interface n).Cell future → ℝ) :=
  EverettianProbability.API.ExactFinitePhysicalRealization r x q

/-- Fibrewise compatibility is exactly unitary realizability inside present
record blocks. -/
theorem compatibleFineWeights_iff_unitaryRealizable
    {future present : Perspective n}
    (r : Refines future present)
    (x : H n)
    (q : (Projective.interface n).Cell future → ℝ) :
    CompatibleFineWeights r x q ↔ UnitaryRealizesFineWeights r x q := by
  exact EverettianProbability.API.compatibleFineBornWeights_iff_projectorCommutingUnitary r x q

/-- Fibrewise compatibility is equivalent to existence of a bundled exact
physical realization. -/
theorem compatibleFineWeights_iff_nonempty_physicalRealization
    {future present : Perspective n}
    (r : Refines future present)
    (x : H n)
    (q : (Projective.interface n).Cell future → ℝ) :
    CompatibleFineWeights r x q ↔ Nonempty (PhysicalRealization r x q) := by
  exact EverettianProbability.API.compatibleFineBornWeights_iff_nonempty_exactRealization r x q

noncomputable def physicalRealizationOfCompatible
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q) :
    PhysicalRealization r x q :=
  EverettianProbability.API.exactFinitePhysicalRealizationOfCompatible h

/-- Exact finite physical adequacy for a compatible fine-weight profile. -/
theorem exactPhysicalAdequacy
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q) :
    ∃ U : H n ≃ₗᵢ[ℂ] H n,
      CommutesWithPerspectiveProjectors present U.toLinearEquiv.toLinearMap ∧
        (∀ i : (Projective.interface n).Cell future,
          bornRecord future (U x) i = q i) ∧
        RealizesBornPayoffInvariance
          (ContinuationStep.mk r)
          U.toLinearEquiv.toLinearMap := by
  exact EverettianProbability.API.exactFinitePhysicalRichness h

namespace PhysicalRealization

theorem preserves_presentRecord
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : PhysicalRealization r x q) :
    PreservesRecordObservable (bornRecord present) R.evolution := by
  exact R.preserves_presentBornRecord

theorem realizes_futureWeights
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : PhysicalRealization r x q)
    (i : (Projective.interface n).Cell future) :
    bornRecord future (R.toUniformContinuation.evolution x) i = q i := by
  exact R.toUniformContinuation_realizes_weights i

theorem realizes_payoffInvariance
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : PhysicalRealization r x q) :
    RealizesBornPayoffInvariance
      R.toUniformContinuation.step
      R.toUniformContinuation.evolution := by
  exact R.realizesBornPayoffInvariance

theorem bornExpectation_pullback_eq
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : PhysicalRealization r x q)
    (z : H n)
    (a : EverettianProbability.Core.Act n) :
    EverettianProbability.Refinement.bornExpectation
        (R.evolution z)
        future
        (EverettianProbability.Refinement.pullbackAct r a) =
      EverettianProbability.Refinement.bornExpectation z present a := by
  exact
    EverettianProbability.API.ExactFinitePhysicalRealization.bornExpectation_pullback_eq
      R z a

end PhysicalRealization

def prescribedRatio
    {future present : Perspective n}
    (r : Refines future present)
    (x : H n)
    (q : (Projective.interface n).Cell future → ℝ)
    (c : (Projective.interface n).Cell present)
    (i : (Projective.interface n).Cell future) : ℝ :=
  EverettianProbability.API.prescribedConditionalRatio r x q c i

namespace PhysicalRealization

theorem continuatorCredence_eq_prescribedRatio
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : PhysicalRealization r x q)
    (F : RationalExpectationFamily (Projective.interface n))
    (hn3 : 3 ≤ n)
    (hinv : RefinementInvariantLocal F.V)
    (hx : ‖x‖ = 1)
    (hNul :
      AxNul
        (EverettianProbability.BornCalibration.canonicalWeight
          (projectiveConcreteExpectationFamily F))
        R.targetState)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0)
    (i : (Projective.interface n).Cell future) :
    R.toUniformContinuation.step.continuatorCredence F c i =
      prescribedRatio r x q c i := by
  exact R.continuatorCredence_eq_prescribedConditionalRatio F hn3 hinv hx hNul c hc i

theorem sum_continuatorCredence_eq_one
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : PhysicalRealization r x q)
    (hCompatible : CompatibleFineWeights r x q)
    (F : RationalExpectationFamily (Projective.interface n))
    (hn3 : 3 ≤ n)
    (hinv : RefinementInvariantLocal F.V)
    (hx : ‖x‖ = 1)
    (hNul :
      AxNul
        (EverettianProbability.BornCalibration.canonicalWeight
          (projectiveConcreteExpectationFamily F))
        R.targetState)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0) :
    (∑ i : (Projective.interface n).Cell future,
      R.toUniformContinuation.step.continuatorCredence F c i) = 1 := by
  exact
    EverettianProbability.API.ExactFinitePhysicalRealization.sum_continuatorCredence_eq_one
      R hCompatible F hn3 hinv hx hNul c hc

theorem parentWeight_mul_continuatorCredence_eq_fineWeight
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : PhysicalRealization r x q)
    (F : RationalExpectationFamily (Projective.interface n))
    (hn3 : 3 ≤ n)
    (hinv : RefinementInvariantLocal F.V)
    (hx : ‖x‖ = 1)
    (hNul :
      AxNul
        (EverettianProbability.BornCalibration.canonicalWeight
          (projectiveConcreteExpectationFamily F))
        R.targetState)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0)
    (i : (Projective.interface n).Cell future)
    (hparent : (Projective.interface n).parentCell r i = c) :
    bornRecord present x c * R.toUniformContinuation.step.continuatorCredence F c i =
      q i := by
  exact
    EverettianProbability.API.ExactFinitePhysicalRealization.parentWeight_mul_continuatorCredence_eq_fineWeight
      R F hn3 hinv hx hNul c hc i hparent

end PhysicalRealization

theorem exactPhysicalAdequacy_calibrated
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q)
    (F : RationalExpectationFamily (Projective.interface n))
    (hn3 : 3 ≤ n)
    (hinv : RefinementInvariantLocal F.V)
    (hx : ‖x‖ = 1)
    (hNul :
      AxNul
        (EverettianProbability.BornCalibration.canonicalWeight
          (projectiveConcreteExpectationFamily F))
        (physicalRealizationOfCompatible h).targetState)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0) :
    (∀ i : (Projective.interface n).Cell future,
      ContinuationStep.continuatorCredence F
        ((physicalRealizationOfCompatible h).toUniformContinuation.step)
        c i = prescribedRatio r x q c i) ∧
    (∑ i : (Projective.interface n).Cell future,
      ContinuationStep.continuatorCredence F
        ((physicalRealizationOfCompatible h).toUniformContinuation.step)
        c i) = 1 ∧
    RealizesBornPayoffInvariance
      (physicalRealizationOfCompatible h).toUniformContinuation.step
      (physicalRealizationOfCompatible h).toUniformContinuation.evolution := by
  exact
    EverettianProbability.API.exactFinitePhysicalRichness_calibrated
      h F hn3 hinv hx hNul c hc

noncomputable abbrev recordNeutralPhysicalRealization :=
  EverettianProbability.API.recordNeutralExactFinitePhysicalRealization

theorem recordNeutralPhysicalAdequacy_integratedWitness :
    EverettianProbability.API.CompatibleFineBornWeights
        EverettianProbability.PhysicalRefinement.recordNeutral_refines
        EverettianProbability.PhysicalRefinement.psiBefore
        FineBornWeightPlan.recordNeutralFineBornWeightPlan.weight ∧
      CommutesWithPerspectiveProjectors
        EverettianProbability.PhysicalRefinement.coarsePerspective
        recordNeutralPhysicalRealization.unitary.toLinearEquiv.toLinearMap ∧
      bornRecord EverettianProbability.PhysicalRefinement.finePerspective
          (recordNeutralPhysicalRealization.unitary
            EverettianProbability.PhysicalRefinement.psiBefore)
          EverettianProbability.Abstract.recordNeutralFutureAnc0Cell = 144 / 625 ∧
      bornRecord EverettianProbability.PhysicalRefinement.finePerspective
          (recordNeutralPhysicalRealization.unitary
            EverettianProbability.PhysicalRefinement.psiBefore)
          EverettianProbability.Abstract.recordNeutralFutureAnc1Cell = 256 / 625 ∧
      RealizesBornPayoffInvariance
        recordNeutralPhysicalRealization.toUniformContinuation.step
        recordNeutralPhysicalRealization.toUniformContinuation.evolution := by
  exact EverettianProbability.API.recordNeutralExactFinitePhysicalRichness_integratedWitness

end
end EverettianProbability.ExactFinite
