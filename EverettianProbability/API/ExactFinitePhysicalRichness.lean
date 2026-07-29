import EverettianProbability.Diachronic.PhysicalFinePlanContinuation

/-!
**FR.** # Richesse physique exacte des raffinements projectifs finis

Cette API publique caracterise les profils de poids fins qui peuvent etre
realises par un unitaire commutant avec le record present. La compatibilite
geometrique est la positivite et l'egalite des sommes sur les fibres avec le
record bornien present. Elle est equivalente a une realisation unitaire, qui
s'empaquette ensuite comme continuation physique uniforme.

Sous les premisses explicites de calibration P4, les credences de
continuateurs sont les rapports conditionnels des poids fins. Le resultat est
exact et fini : il ne postule ni decoherence approximative, ni Hamiltonien
privilegie, ni identite personnelle.

**EN.** # Exact physical richness of finite projective refinements

This public API characterizes fine-weight profiles realizable by a unitary
commuting with the present record. Geometric compatibility is nonnegativity
and fibrewise agreement with the present Born record. It is equivalent to a
unitary realization, which is then packaged as a uniform physical continuation.

Under explicit P4 calibration premises, continuator credences are the
conditional ratios of fine weights. The result is exact and finite: it assumes
neither approximate decoherence, a preferred Hamiltonian, nor personal
identity.
-/

namespace EverettianProbability.API

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core
open EverettianProbability.PhysicalRefinement
open EverettianProbability.Abstract
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : ℕ}

/-- A future Born-weight profile is compatible with the present state when it
is nonnegative and sums fibrewise to the present Born record. -/
def CompatibleFineBornWeights
    {future present : Perspective n}
    (r : Refines future present)
    (x : H n)
    (q : (Projective.interface n).Cell future → ℝ) : Prop :=
  (∀ i : (Projective.interface n).Cell future, 0 ≤ q i) ∧
  ∀ c : (Projective.interface n).Cell present,
    (∑ i : (Projective.interface n).Cell future,
      if (Projective.interface n).parentCell r i = c then q i else 0) =
      bornRecord present x c

namespace CompatibleFineBornWeights

theorem nonneg
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineBornWeights r x q)
    (i : (Projective.interface n).Cell future) :
    0 ≤ q i := h.1 i

theorem fibre_sum
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineBornWeights r x q)
    (c : (Projective.interface n).Cell present) :
    (∑ i : (Projective.interface n).Cell future,
      if (Projective.interface n).parentCell r i = c then q i else 0) =
      bornRecord present x c := h.2 c

end CompatibleFineBornWeights

/-- A compatible profile packaged as a fine Born-weight plan. -/
def fineBornWeightPlanOfCompatible
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineBornWeights r x q) : FineBornWeightPlan r x where
  weight := q
  nonneg := h.1
  fibre_sum := h.2

@[simp] theorem fineBornWeightPlanOfCompatible_weight
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineBornWeights r x q)
    (i : (Projective.interface n).Cell future) :
    (fineBornWeightPlanOfCompatible h).weight i = q i := rfl

theorem compatibleFineBornWeights_of_plan
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) :
    CompatibleFineBornWeights r x plan.weight :=
  ⟨plan.nonneg, plan.fibre_sum⟩

/-- A fine-weight profile realized by a unitary internal to present record
blocks. -/
def ProjectorCommutingUnitaryRealizesFineWeights
    {future present : Perspective n}
    (r : Refines future present)
    (x : H n)
    (q : (Projective.interface n).Cell future → ℝ) : Prop :=
  ∃ U : H n ≃ₗᵢ[ℂ] H n,
    CommutesWithPerspectiveProjectors present U.toLinearEquiv.toLinearMap ∧
    ∀ i : (Projective.interface n).Cell future,
      bornRecord future (U x) i = q i

theorem projectorCommutingUnitaryRealizesFineWeights_of_compatible
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineBornWeights r x q) :
    ProjectorCommutingUnitaryRealizesFineWeights r x q := by
  let plan : FineBornWeightPlan r x := fineBornWeightPlanOfCompatible h
  refine ⟨plan.realizingUnitary, plan.realizingUnitary_commutes, ?_⟩
  intro i
  calc
    bornRecord future (plan.realizingUnitary x) i = plan.weight i :=
      plan.realizingUnitary_bornWeight i
    _ = q i := rfl

theorem compatibleFineBornWeights_of_projectorCommutingUnitary
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (hPhysical : ProjectorCommutingUnitaryRealizesFineWeights r x q) :
    CompatibleFineBornWeights r x q := by
  rcases hPhysical with ⟨U, hCommutes, hWeights⟩
  have hOrbit : ProjectorCommutingUnitaryOrbit present x (U x) :=
    ⟨U, hCommutes, rfl⟩
  have hRecord : SameBornRecord present x (U x) :=
    sameBornRecord_of_projectorCommutingUnitaryOrbit hOrbit
  let plan : FineBornWeightPlan r x := FineBornWeightPlan.ofTargetState r x (U x) hRecord
  constructor
  · intro i
    rw [← hWeights i]
    exact sq_nonneg _
  · intro c
    calc
      (∑ i : (Projective.interface n).Cell future,
        if (Projective.interface n).parentCell r i = c then q i else 0) =
        ∑ i : (Projective.interface n).Cell future,
          if (Projective.interface n).parentCell r i = c then plan.weight i else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hparent : (Projective.interface n).parentCell r i = c
            · simp only [if_pos hparent]
              rw [FineBornWeightPlan.ofTargetState_weight]
              exact (hWeights i).symm
            · simp only [if_neg hparent]
      _ = bornRecord present x c := plan.fibre_sum c

/-- Exact finite physical richness: compatibility is equivalent to unitary
realizability inside present record blocks. -/
theorem compatibleFineBornWeights_iff_projectorCommutingUnitary
    {future present : Perspective n}
    (r : Refines future present) (x : H n)
    (q : (Projective.interface n).Cell future → ℝ) :
    CompatibleFineBornWeights r x q ↔
      ProjectorCommutingUnitaryRealizesFineWeights r x q := by
  constructor
  · exact projectorCommutingUnitaryRealizesFineWeights_of_compatible
  · exact compatibleFineBornWeights_of_projectorCommutingUnitary

/-- Exact finite physical realization of one compatible fine-weight profile. -/
structure ExactFinitePhysicalRealization
    {future present : Perspective n}
    (r : Refines future present) (x : H n)
    (q : (Projective.interface n).Cell future → ℝ) where
  unitary : H n ≃ₗᵢ[ℂ] H n
  commutes_present :
    CommutesWithPerspectiveProjectors present unitary.toLinearEquiv.toLinearMap
  realizes_weights : ∀ i : (Projective.interface n).Cell future,
    bornRecord future (unitary x) i = q i

namespace ExactFinitePhysicalRealization

def evolution
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : ExactFinitePhysicalRealization r x q) : H n →ₗ[ℂ] H n :=
  R.unitary.toLinearEquiv.toLinearMap

def targetState
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : ExactFinitePhysicalRealization r x q) : H n := R.unitary x

@[simp] theorem evolution_apply
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : ExactFinitePhysicalRealization r x q) (z : H n) :
    R.evolution z = R.unitary z := rfl

theorem evolution_isometry
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : ExactFinitePhysicalRealization r x q) (z : H n) :
    ‖R.evolution z‖ = ‖z‖ := R.unitary.norm_map z

theorem preserves_presentBornRecord
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : ExactFinitePhysicalRealization r x q) :
    PreservesRecordObservable (bornRecord present) R.evolution := by
  intro z
  funext c
  exact bornWeight_preserved_of_commutesWithProjector
    R.evolution R.evolution_isometry c.val (R.commutes_present c) z

def toProjectorCommutingContinuation
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : ExactFinitePhysicalRealization r x q) :
    ProjectorCommutingProjectiveContinuation n future present where
  step := ⟨r⟩
  evolution := R.evolution
  isometry := R.evolution_isometry
  commutes_present_projectors := R.commutes_present

@[simp] theorem toProjectorCommutingContinuation_refinement
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : ExactFinitePhysicalRealization r x q) :
    R.toProjectorCommutingContinuation.step.refinement = r := rfl

@[simp] theorem toProjectorCommutingContinuation_evolution
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : ExactFinitePhysicalRealization r x q) (z : H n) :
    R.toProjectorCommutingContinuation.evolution z = R.unitary z := rfl

def toUniformContinuation
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : ExactFinitePhysicalRealization r x q) :
    UniformRecordRespectingProjectiveContinuation n future present :=
  R.toProjectorCommutingContinuation.toUniform
    ((Projective.interface n).Cell present → ℝ)
    (bornRecord present) R.preserves_presentBornRecord

@[simp] theorem toUniformContinuation_refinement
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : ExactFinitePhysicalRealization r x q) :
    R.toUniformContinuation.step.refinement = r := rfl

@[simp] theorem toUniformContinuation_evolution
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : ExactFinitePhysicalRealization r x q) (z : H n) :
    R.toUniformContinuation.evolution z = R.unitary z := rfl

theorem toUniformContinuation_realizes_weights
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : ExactFinitePhysicalRealization r x q)
    (i : (Projective.interface n).Cell future) :
    bornRecord future (R.toUniformContinuation.evolution x) i = q i :=
  R.realizes_weights i

theorem realizesBornPayoffInvariance
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : ExactFinitePhysicalRealization r x q) :
    RealizesBornPayoffInvariance R.toUniformContinuation.step R.toUniformContinuation.evolution :=
  R.toUniformContinuation.realizesBornPayoffInvariance

theorem bornExpectation_pullback_eq
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : ExactFinitePhysicalRealization r x q) (z : H n)
    (a : EverettianProbability.Core.Act n) :
    EverettianProbability.Refinement.bornExpectation (R.evolution z) future
        (EverettianProbability.Refinement.pullbackAct r a) =
      EverettianProbability.Refinement.bornExpectation z present a :=
  R.toUniformContinuation.physicalBornExpectation_pullback_eq z a

/-- Conditional ratio associated with an arbitrary fine-weight profile. -/
def prescribedConditionalRatio
    {future present : Perspective n}
    (r : Refines future present) (x : H n)
    (q : (Projective.interface n).Cell future → ℝ)
    (c : (Projective.interface n).Cell present)
    (i : (Projective.interface n).Cell future) : ℝ :=
  if (Projective.interface n).parentCell r i = c then
    q i / bornRecord present x c else 0

theorem physicalContinuatorBornRatio_eq_prescribed
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : ExactFinitePhysicalRealization r x q)
    (c : (Projective.interface n).Cell present)
    (i : (Projective.interface n).Cell future) :
    R.toUniformContinuation.physicalContinuatorBornRatio x c i =
      prescribedConditionalRatio r x q c i := by
  unfold UniformRecordRespectingProjectiveContinuation.physicalContinuatorBornRatio
    prescribedConditionalRatio
  by_cases hparent : (Projective.interface n).parentCell r i = c
  · rw [if_pos hparent, if_pos hparent]
    change bornRecord future (R.toUniformContinuation.evolution x) i /
        bornRecord present x c = q i / bornRecord present x c
    rw [R.toUniformContinuation_realizes_weights i]
  · rw [if_neg hparent, if_neg hparent]

theorem sum_prescribedConditionalRatio_eq_one
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (hCompatible : CompatibleFineBornWeights r x q)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0) :
    (∑ i : (Projective.interface n).Cell future,
      prescribedConditionalRatio r x q c i) = 1 := by
  exact (fineBornWeightPlanOfCompatible hCompatible).sum_conditionalRatio_eq_one c hc

theorem continuatorCredence_eq_prescribedConditionalRatio
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : ExactFinitePhysicalRealization r x q)
    (F : RationalExpectationFamily (Projective.interface n))
    (hn3 : 3 ≤ n) (hinv : RefinementInvariantLocal F.V) (hx : ‖x‖ = 1)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight (projectiveConcreteExpectationFamily F))
      R.targetState)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0)
    (i : (Projective.interface n).Cell future) :
    R.toUniformContinuation.step.continuatorCredence F c i =
      prescribedConditionalRatio r x q c i := by
  calc
    R.toUniformContinuation.step.continuatorCredence F c i =
      R.toUniformContinuation.physicalContinuatorBornRatio x c i := by
        exact R.toUniformContinuation.continuatorCredence_eq_physicalContinuatorBornRatio
          F hn3 hinv x hx (by simpa [targetState] using hNul) c hc i
    _ = prescribedConditionalRatio r x q c i :=
      R.physicalContinuatorBornRatio_eq_prescribed c i

theorem sum_continuatorCredence_eq_one
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : ExactFinitePhysicalRealization r x q)
    (hCompatible : CompatibleFineBornWeights r x q)
    (F : RationalExpectationFamily (Projective.interface n))
    (hn3 : 3 ≤ n) (hinv : RefinementInvariantLocal F.V) (hx : ‖x‖ = 1)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight (projectiveConcreteExpectationFamily F))
      R.targetState)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0) :
    (∑ i : (Projective.interface n).Cell future,
      R.toUniformContinuation.step.continuatorCredence F c i) = 1 := by
  calc
    (∑ i : (Projective.interface n).Cell future,
      R.toUniformContinuation.step.continuatorCredence F c i) =
      ∑ i : (Projective.interface n).Cell future,
        prescribedConditionalRatio r x q c i := by
          apply Finset.sum_congr rfl
          intro i _
          exact R.continuatorCredence_eq_prescribedConditionalRatio F hn3 hinv hx hNul c hc i
    _ = 1 := sum_prescribedConditionalRatio_eq_one hCompatible c hc

theorem parentWeight_mul_continuatorCredence_eq_fineWeight
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (R : ExactFinitePhysicalRealization r x q)
    (F : RationalExpectationFamily (Projective.interface n))
    (hn3 : 3 ≤ n) (hinv : RefinementInvariantLocal F.V) (hx : ‖x‖ = 1)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight (projectiveConcreteExpectationFamily F))
      R.targetState)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0)
    (i : (Projective.interface n).Cell future)
    (hparent : (Projective.interface n).parentCell r i = c) :
    bornRecord present x c * R.toUniformContinuation.step.continuatorCredence F c i = q i := by
  rw [R.continuatorCredence_eq_prescribedConditionalRatio F hn3 hinv hx hNul c hc i]
  unfold prescribedConditionalRatio
  rw [if_pos hparent]
  exact mul_div_cancel₀ _ hc

end ExactFinitePhysicalRealization

/-- Public conditional ratio for an arbitrary compatible fine profile. -/
def prescribedConditionalRatio
    {future present : Perspective n}
    (r : Refines future present) (x : H n)
    (q : (Projective.interface n).Cell future → ℝ)
    (c : (Projective.interface n).Cell present)
    (i : (Projective.interface n).Cell future) : ℝ :=
  ExactFinitePhysicalRealization.prescribedConditionalRatio r x q c i

theorem sum_prescribedConditionalRatio_eq_one
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (hCompatible : CompatibleFineBornWeights r x q)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0) :
    (∑ i : (Projective.interface n).Cell future,
      prescribedConditionalRatio r x q c i) = 1 :=
  ExactFinitePhysicalRealization.sum_prescribedConditionalRatio_eq_one hCompatible c hc

noncomputable def exactFinitePhysicalRealizationOfCompatible
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineBornWeights r x q) :
    ExactFinitePhysicalRealization r x q := by
  let plan : FineBornWeightPlan r x := fineBornWeightPlanOfCompatible h
  exact {
    unitary := plan.realizingUnitary
    commutes_present := plan.realizingUnitary_commutes
    realizes_weights := by
      intro i
      calc
        bornRecord future (plan.realizingUnitary x) i = plan.weight i :=
          plan.realizingUnitary_bornWeight i
        _ = q i := rfl }

theorem compatibleFineBornWeights_iff_nonempty_exactRealization
    {future present : Perspective n}
    (r : Refines future present) (x : H n)
    (q : (Projective.interface n).Cell future → ℝ) :
    CompatibleFineBornWeights r x q ↔ Nonempty (ExactFinitePhysicalRealization r x q) := by
  constructor
  · intro h
    exact ⟨exactFinitePhysicalRealizationOfCompatible h⟩
  · rintro ⟨R⟩
    exact compatibleFineBornWeights_of_projectorCommutingUnitary
      ⟨R.unitary, R.commutes_present, R.realizes_weights⟩

theorem exactFinitePhysicalRichness
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineBornWeights r x q) :
    ∃ U : H n ≃ₗᵢ[ℂ] H n,
      CommutesWithPerspectiveProjectors present U.toLinearEquiv.toLinearMap ∧
      (∀ i : (Projective.interface n).Cell future, bornRecord future (U x) i = q i) ∧
      RealizesBornPayoffInvariance (ContinuationStep.mk r) U.toLinearEquiv.toLinearMap := by
  let R := exactFinitePhysicalRealizationOfCompatible h
  refine ⟨R.unitary, R.commutes_present, R.realizes_weights, ?_⟩
  intro y aFuture aPresent hEquivalent
  exact R.toUniformContinuation.physicalBornExpectation_eq_of_payoffEquivalent
    y aFuture aPresent hEquivalent

theorem exactFinitePhysicalRichness_calibrated
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineBornWeights r x q)
    (F : RationalExpectationFamily (Projective.interface n))
    (hn3 : 3 ≤ n) (hinv : RefinementInvariantLocal F.V) (hx : ‖x‖ = 1)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight (projectiveConcreteExpectationFamily F))
      (exactFinitePhysicalRealizationOfCompatible h).targetState)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0) :
    (∀ i : (Projective.interface n).Cell future,
      ContinuationStep.continuatorCredence
          F ((exactFinitePhysicalRealizationOfCompatible h).toUniformContinuation.step)
          c i = prescribedConditionalRatio r x q c i) ∧
    (∑ i : (Projective.interface n).Cell future,
      ContinuationStep.continuatorCredence
          F ((exactFinitePhysicalRealizationOfCompatible h).toUniformContinuation.step)
          c i) = 1 ∧
    RealizesBornPayoffInvariance
      (exactFinitePhysicalRealizationOfCompatible h).toUniformContinuation.step
      (exactFinitePhysicalRealizationOfCompatible h).toUniformContinuation.evolution := by
  let R := exactFinitePhysicalRealizationOfCompatible h
  refine ⟨?_, ?_, R.realizesBornPayoffInvariance⟩
  · intro i
    exact R.continuatorCredence_eq_prescribedConditionalRatio F hn3 hinv hx hNul c hc i
  · exact R.sum_continuatorCredence_eq_one h F hn3 hinv hx hNul c hc

def recordNeutralCompatibleFineBornWeights :
    CompatibleFineBornWeights recordNeutral_refines psiBefore
      FineBornWeightPlan.recordNeutralFineBornWeightPlan.weight :=
  compatibleFineBornWeights_of_plan FineBornWeightPlan.recordNeutralFineBornWeightPlan

noncomputable def recordNeutralExactFinitePhysicalRealization :
    ExactFinitePhysicalRealization recordNeutral_refines psiBefore
      FineBornWeightPlan.recordNeutralFineBornWeightPlan.weight :=
  exactFinitePhysicalRealizationOfCompatible recordNeutralCompatibleFineBornWeights

theorem recordNeutralExactFinitePhysicalRealization_anc0 :
    bornRecord finePerspective (recordNeutralExactFinitePhysicalRealization.unitary psiBefore)
      recordNeutralFutureAnc0Cell = 144 / 625 := by
  calc
    bornRecord finePerspective (recordNeutralExactFinitePhysicalRealization.unitary psiBefore)
        recordNeutralFutureAnc0Cell = FineBornWeightPlan.recordNeutralFineBornWeightPlan.weight recordNeutralFutureAnc0Cell :=
      recordNeutralExactFinitePhysicalRealization.realizes_weights recordNeutralFutureAnc0Cell
    _ = 144 / 625 := FineBornWeightPlan.recordNeutralFineBornWeightPlan_anc0

theorem recordNeutralExactFinitePhysicalRealization_anc1 :
    bornRecord finePerspective (recordNeutralExactFinitePhysicalRealization.unitary psiBefore)
      recordNeutralFutureAnc1Cell = 256 / 625 := by
  calc
    bornRecord finePerspective (recordNeutralExactFinitePhysicalRealization.unitary psiBefore)
        recordNeutralFutureAnc1Cell = FineBornWeightPlan.recordNeutralFineBornWeightPlan.weight recordNeutralFutureAnc1Cell :=
      recordNeutralExactFinitePhysicalRealization.realizes_weights recordNeutralFutureAnc1Cell
    _ = 256 / 625 := FineBornWeightPlan.recordNeutralFineBornWeightPlan_anc1

theorem recordNeutralExactFinitePhysicalRealization_commutes :
    CommutesWithPerspectiveProjectors coarsePerspective
      recordNeutralExactFinitePhysicalRealization.unitary.toLinearEquiv.toLinearMap :=
  recordNeutralExactFinitePhysicalRealization.commutes_present

theorem recordNeutralExactFinitePhysicalRichness_integratedWitness :
    CompatibleFineBornWeights recordNeutral_refines psiBefore FineBornWeightPlan.recordNeutralFineBornWeightPlan.weight ∧
    CommutesWithPerspectiveProjectors coarsePerspective
      recordNeutralExactFinitePhysicalRealization.unitary.toLinearEquiv.toLinearMap ∧
    bornRecord finePerspective (recordNeutralExactFinitePhysicalRealization.unitary psiBefore)
      recordNeutralFutureAnc0Cell = 144 / 625 ∧
    bornRecord finePerspective (recordNeutralExactFinitePhysicalRealization.unitary psiBefore)
      recordNeutralFutureAnc1Cell = 256 / 625 ∧
    RealizesBornPayoffInvariance recordNeutralExactFinitePhysicalRealization.toUniformContinuation.step
      recordNeutralExactFinitePhysicalRealization.toUniformContinuation.evolution := by
  exact ⟨recordNeutralCompatibleFineBornWeights,
    recordNeutralExactFinitePhysicalRealization_commutes,
    recordNeutralExactFinitePhysicalRealization_anc0,
    recordNeutralExactFinitePhysicalRealization_anc1,
    recordNeutralExactFinitePhysicalRealization.realizesBornPayoffInvariance⟩

end
end EverettianProbability.API
