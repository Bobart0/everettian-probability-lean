import EverettianProbability.Diachronic.FineBornWeightRealization

/-!
**FR.** # Continuation physique realisant un plan fin de poids

Ce module empaquette un plan fin compatible en un unitaire commutant avec les
projecteurs presents, puis en continuation uniformement respectueuse du
record complet des poids borniens. Les ratios physiques et les credences
calibrees y sont identifies aux rapports conditionnels du plan.

Cette construction demeure conditionnelle a la lecture semantique des
cellules futures comme continuateurs et ne fournit pas de modele de
decoherence.

**EN.** # Physical continuation realizing a fine-weight plan

This module packages a compatible fine plan into a unitary commuting with
present projectors, and then into a uniformly record-respecting continuation
for the complete Born-weight record. Physical ratios and calibrated credences
are identified with the plan's conditional ratios.

The construction remains conditional on the semantic reading of future cells
as continuators and supplies no model of decoherence.
-/

namespace EverettianProbability.Abstract

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core
open EverettianProbability.PhysicalRefinement
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : ℕ}

namespace FineBornWeightPlan

/-- Conditional ratio prescribed by a fine Born-weight plan. -/
def conditionalRatio
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineBornWeightPlan r x)
    (c : (Projective.interface n).Cell present)
    (i : (Projective.interface n).Cell future) : ℝ :=
  if (Projective.interface n).parentCell r i = c then
    plan.weight i / bornRecord present x c
  else 0

theorem conditionalRatio_def
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineBornWeightPlan r x)
    (c : (Projective.interface n).Cell present)
    (i : (Projective.interface n).Cell future) :
    plan.conditionalRatio c i =
      if (Projective.interface n).parentCell r i = c then
        plan.weight i / bornRecord present x c else 0 :=
  rfl

theorem conditionalRatio_nonneg
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineBornWeightPlan r x)
    (c : (Projective.interface n).Cell present)
    (i : (Projective.interface n).Cell future) :
    0 ≤ plan.conditionalRatio c i := by
  unfold conditionalRatio
  split_ifs
  · exact div_nonneg (plan.nonneg i) (sq_nonneg _)
  · exact le_rfl

theorem conditionalRatio_zero_of_parent_ne
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineBornWeightPlan r x)
    (c : (Projective.interface n).Cell present)
    (i : (Projective.interface n).Cell future)
    (hparent : (Projective.interface n).parentCell r i ≠ c) :
    plan.conditionalRatio c i = 0 := by
  have hsub :
      ¬ (⟨parentOf r i.val, parentOf_mem r i.property⟩ :
          (Projective.interface n).Cell present) = c := by
    simpa [Projective.interface_parentCell_apply] using hparent
  unfold conditionalRatio
  rw [Projective.interface_parentCell_apply, if_neg hsub]

/-- The prescribed conditional ratios sum to one in every nonzero fibre. -/
theorem sum_conditionalRatio_eq_one
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineBornWeightPlan r x)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0) :
    (∑ i : (Projective.interface n).Cell future, plan.conditionalRatio c i) = 1 := by
  unfold conditionalRatio
  calc
    (∑ i : (Projective.interface n).Cell future,
      if (Projective.interface n).parentCell r i = c then
        plan.weight i / bornRecord present x c else 0) =
      (∑ i : (Projective.interface n).Cell future,
        if (Projective.interface n).parentCell r i = c then plan.weight i else 0) /
        bornRecord present x c := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i _
          have hsub :
              (⟨parentOf r i.val, parentOf_mem r i.property⟩ :
                  (Projective.interface n).Cell present) =
                (Projective.interface n).parentCell r i := by
            rw [Projective.interface_parentCell_apply]
          rw [← hsub]
          by_cases hparent :
              (⟨parentOf r i.val, parentOf_mem r i.property⟩ :
                  (Projective.interface n).Cell present) = c
          · simp only [if_pos hparent]
          · simp only [if_neg hparent, zero_div]
    _ = bornRecord present x c / bornRecord present x c := by rw [plan.fibre_sum c]
    _ = 1 := div_self hc

/-- A chosen global unitary realizing the compatible fine-weight plan. -/
noncomputable def realizingUnitary
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineBornWeightPlan r x) : H n ≃ₗᵢ[ℂ] H n :=
  Classical.choose (exists_projectorCommutingUnitary_realizing_fineBornWeightPlan plan)

theorem realizingUnitary_commutes
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) :
    CommutesWithPerspectiveProjectors present plan.realizingUnitary.toLinearEquiv.toLinearMap :=
  (Classical.choose_spec
    (exists_projectorCommutingUnitary_realizing_fineBornWeightPlan plan)).1

theorem realizingUnitary_maps_state
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) :
    plan.realizingUnitary x = fineWeightTargetState plan :=
  (Classical.choose_spec
    (exists_projectorCommutingUnitary_realizing_fineBornWeightPlan plan)).2.1

theorem realizingUnitary_bornWeight
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x)
    (i : (Projective.interface n).Cell future) :
    bornRecord future (plan.realizingUnitary x) i = plan.weight i :=
  (Classical.choose_spec
    (exists_projectorCommutingUnitary_realizing_fineBornWeightPlan plan)).2.2 i

/-- Linear evolution underlying the chosen realizing unitary. -/
noncomputable def realizingEvolution
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) : H n →ₗ[ℂ] H n :=
  plan.realizingUnitary.toLinearEquiv.toLinearMap

@[simp] theorem realizingEvolution_apply
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) (z : H n) :
    plan.realizingEvolution z = plan.realizingUnitary z := by rfl

theorem realizingEvolution_isometry
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) (z : H n) :
    ‖plan.realizingEvolution z‖ = ‖z‖ :=
  plan.realizingUnitary.norm_map z

theorem realizingEvolution_maps_state
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) :
    plan.realizingEvolution x = fineWeightTargetState plan :=
  plan.realizingUnitary_maps_state

/-- The realizing evolution preserves the complete present Born record for
every vector. -/
theorem realizingEvolution_preserves_bornRecord
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) :
    PreservesRecordObservable (bornRecord present) plan.realizingEvolution := by
  intro z
  funext c
  exact
    bornWeight_preserved_of_commutesWithProjector
      plan.realizingEvolution plan.realizingEvolution_isometry c.val
      (plan.realizingUnitary_commutes c) z

/-- Projector-commuting physical continuation realizing the plan. -/
noncomputable def realizingProjectorCommutingContinuation
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) :
    ProjectorCommutingProjectiveContinuation n future present where
  step := ⟨r⟩
  evolution := plan.realizingEvolution
  isometry := plan.realizingEvolution_isometry
  commutes_present_projectors := plan.realizingUnitary_commutes

@[simp] theorem realizingProjectorCommutingContinuation_refinement
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) :
    plan.realizingProjectorCommutingContinuation.step.refinement = r := by rfl

@[simp] theorem realizingProjectorCommutingContinuation_evolution
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) (z : H n) :
    plan.realizingProjectorCommutingContinuation.evolution z = plan.realizingUnitary z := by rfl

theorem realizingProjectorCommutingContinuation_presentBornWeight_preserved
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) (z : H n)
    (c : (Projective.interface n).Cell present) :
    bornRecord present z c =
      bornRecord present (plan.realizingProjectorCommutingContinuation.evolution z) c :=
  plan.realizingProjectorCommutingContinuation.presentBornWeight_preserved z c

/-- Uniform physical continuation realizing the plan, with complete present
Born record as accessible record. -/
noncomputable def realizingUniformContinuation
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) :
    UniformRecordRespectingProjectiveContinuation n future present :=
  plan.realizingProjectorCommutingContinuation.toUniform
    ((Projective.interface n).Cell present → ℝ)
    (bornRecord present) plan.realizingEvolution_preserves_bornRecord

@[simp] theorem realizingUniformContinuation_refinement
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) :
    plan.realizingUniformContinuation.step.refinement = r := by rfl

@[simp] theorem realizingUniformContinuation_evolution
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) (z : H n) :
    plan.realizingUniformContinuation.evolution z = plan.realizingUnitary z := by rfl

theorem realizingUniformContinuation_evolution_at_source
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) :
    plan.realizingUniformContinuation.evolution x = fineWeightTargetState plan :=
  plan.realizingUnitary_maps_state

theorem realizingUniformContinuation_record_preserved
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) (z : H n) :
    bornRecord present z = bornRecord present (plan.realizingUniformContinuation.evolution z) :=
  plan.realizingUniformContinuation.record_preserved z

theorem realizingUniformContinuation_futureBornWeight
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x)
    (i : (Projective.interface n).Cell future) :
    bornRecord future (plan.realizingUniformContinuation.evolution x) i = plan.weight i :=
  plan.realizingUnitary_bornWeight i

/-- State-specific record-respecting continuation generated from the physical
realization of a fine-weight plan. -/
noncomputable def realizingContinuationAt
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) (hx : ‖x‖ = 1) :
    RecordRespectingProjectiveContinuation n future present :=
  plan.realizingUniformContinuation.atState x hx

@[simp] theorem realizingContinuationAt_stateBefore
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) (hx : ‖x‖ = 1) :
    (plan.realizingContinuationAt hx).stateBefore = x := by rfl

@[simp] theorem realizingContinuationAt_stateAfter
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) (hx : ‖x‖ = 1) :
    (plan.realizingContinuationAt hx).stateAfter = fineWeightTargetState plan :=
  plan.realizingUniformContinuation_evolution_at_source

theorem physicalContinuatorBornRatio_eq_conditionalRatio
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x)
    (c : (Projective.interface n).Cell present)
    (i : (Projective.interface n).Cell future) :
    plan.realizingUniformContinuation.physicalContinuatorBornRatio x c i =
      plan.conditionalRatio c i := by
  unfold UniformRecordRespectingProjectiveContinuation.physicalContinuatorBornRatio conditionalRatio
  by_cases hparent : (Projective.interface n).parentCell r i = c
  · rw [if_pos hparent, if_pos hparent]
    change bornRecord future (plan.realizingUniformContinuation.evolution x) i /
        bornRecord present x c = plan.weight i / bornRecord present x c
    rw [plan.realizingUniformContinuation_futureBornWeight i]
  · rw [if_neg hparent, if_neg hparent]

theorem continuatorCredence_eq_conditionalRatio
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x)
    (F : RationalExpectationFamily (Projective.interface n))
    (hn3 : 3 ≤ n) (hinv : RefinementInvariantLocal F.V)
    (hx : ‖x‖ = 1)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight
        (projectiveConcreteExpectationFamily F))
      (fineWeightTargetState plan))
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0)
    (i : (Projective.interface n).Cell future) :
    plan.realizingUniformContinuation.step.continuatorCredence F c i =
      plan.conditionalRatio c i := by
  have hNulEvolution : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight
        (projectiveConcreteExpectationFamily F))
      (plan.realizingUniformContinuation.evolution x) := by
    simpa [plan.realizingUniformContinuation_evolution_at_source] using hNul
  calc
    plan.realizingUniformContinuation.step.continuatorCredence F c i =
      plan.realizingUniformContinuation.physicalContinuatorBornRatio x c i := by
        exact plan.realizingUniformContinuation.continuatorCredence_eq_physicalContinuatorBornRatio
          F hn3 hinv x hx hNulEvolution c hc i
    _ = plan.conditionalRatio c i := plan.physicalContinuatorBornRatio_eq_conditionalRatio c i

theorem sum_realizedContinuatorCredence_eq_one
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x)
    (F : RationalExpectationFamily (Projective.interface n))
    (hn3 : 3 ≤ n) (hinv : RefinementInvariantLocal F.V) (hx : ‖x‖ = 1)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight (projectiveConcreteExpectationFamily F))
      (fineWeightTargetState plan))
    (c : (Projective.interface n).Cell present) (hc : bornRecord present x c ≠ 0) :
    (∑ i : (Projective.interface n).Cell future,
      plan.realizingUniformContinuation.step.continuatorCredence F c i) = 1 := by
  calc
    (∑ i : (Projective.interface n).Cell future,
      plan.realizingUniformContinuation.step.continuatorCredence F c i) =
      ∑ i : (Projective.interface n).Cell future, plan.conditionalRatio c i := by
        apply Finset.sum_congr rfl
        intro i _
        exact plan.continuatorCredence_eq_conditionalRatio F hn3 hinv hx hNul c hc i
    _ = 1 := plan.sum_conditionalRatio_eq_one c hc

theorem realizedContinuatorCredence_zero_of_parent_ne
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x)
    (F : RationalExpectationFamily (Projective.interface n))
    (hn3 : 3 ≤ n) (hinv : RefinementInvariantLocal F.V) (hx : ‖x‖ = 1)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight (projectiveConcreteExpectationFamily F))
      (fineWeightTargetState plan))
    (c : (Projective.interface n).Cell present) (hc : bornRecord present x c ≠ 0)
    (i : (Projective.interface n).Cell future)
    (hparent : (Projective.interface n).parentCell r i ≠ c) :
    plan.realizingUniformContinuation.step.continuatorCredence F c i = 0 := by
  rw [plan.continuatorCredence_eq_conditionalRatio F hn3 hinv hx hNul c hc i]
  exact plan.conditionalRatio_zero_of_parent_ne c i hparent

theorem presentBornWeight_mul_continuatorCredence_eq_planWeight
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x)
    (F : RationalExpectationFamily (Projective.interface n))
    (hn3 : 3 ≤ n) (hinv : RefinementInvariantLocal F.V) (hx : ‖x‖ = 1)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight (projectiveConcreteExpectationFamily F))
      (fineWeightTargetState plan))
    (c : (Projective.interface n).Cell present) (hc : bornRecord present x c ≠ 0)
    (i : (Projective.interface n).Cell future)
    (hparent : (Projective.interface n).parentCell r i = c) :
    bornRecord present x c *
      plan.realizingUniformContinuation.step.continuatorCredence F c i = plan.weight i := by
  rw [plan.continuatorCredence_eq_conditionalRatio F hn3 hinv hx hNul c hc i]
  unfold conditionalRatio
  rw [if_pos hparent]
  exact mul_div_cancel₀ _ hc

theorem realizingContinuation_bornExpectation_pullback_eq
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) (z : H n) (a : EverettianProbability.Core.Act n) :
    EverettianProbability.Refinement.bornExpectation
        (plan.realizingUniformContinuation.evolution z) future
        (EverettianProbability.Refinement.pullbackAct r a) =
      EverettianProbability.Refinement.bornExpectation z present a :=
  plan.realizingUniformContinuation.physicalBornExpectation_pullback_eq z a

theorem realizingContinuation_realizesBornPayoffInvariance
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) :
    RealizesBornPayoffInvariance plan.realizingUniformContinuation.step
      plan.realizingUniformContinuation.evolution :=
  plan.realizingUniformContinuation.realizesBornPayoffInvariance

theorem exists_uniformContinuation_realizing_plan
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x) :
    ∃ W : UniformRecordRespectingProjectiveContinuation n future present,
      W.step.refinement = r ∧
      CommutesWithPerspectiveProjectors present W.evolution ∧
      W.evolution x = fineWeightTargetState plan ∧
      (∀ i : (Projective.interface n).Cell future,
        bornRecord future (W.evolution x) i = plan.weight i) ∧
      RealizesBornPayoffInvariance W.step W.evolution := by
  refine ⟨plan.realizingUniformContinuation, rfl, plan.realizingUnitary_commutes,
    plan.realizingUniformContinuation_evolution_at_source,
    plan.realizingUniformContinuation_futureBornWeight, ?_⟩
  exact plan.realizingUniformContinuation.realizesBornPayoffInvariance

theorem exactFinitePhysicalFinePlanRealization
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineBornWeightPlan r x)
    (F : RationalExpectationFamily (Projective.interface n))
    (hn3 : 3 ≤ n) (hinv : RefinementInvariantLocal F.V) (hx : ‖x‖ = 1)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight (projectiveConcreteExpectationFamily F))
      (fineWeightTargetState plan))
    (c : (Projective.interface n).Cell present) (hc : bornRecord present x c ≠ 0) :
    CommutesWithPerspectiveProjectors present plan.realizingUniformContinuation.evolution ∧
    plan.realizingUniformContinuation.evolution x = fineWeightTargetState plan ∧
    (∀ i : (Projective.interface n).Cell future,
      bornRecord future (plan.realizingUniformContinuation.evolution x) i = plan.weight i) ∧
    (∀ i : (Projective.interface n).Cell future,
      plan.realizingUniformContinuation.step.continuatorCredence F c i = plan.conditionalRatio c i) ∧
    (∑ i : (Projective.interface n).Cell future,
      plan.realizingUniformContinuation.step.continuatorCredence F c i) = 1 := by
  exact ⟨plan.realizingUnitary_commutes,
    plan.realizingUniformContinuation_evolution_at_source,
    plan.realizingUniformContinuation_futureBornWeight,
    fun i => plan.continuatorCredence_eq_conditionalRatio F hn3 hinv hx hNul c hc i,
    plan.sum_realizedContinuatorCredence_eq_one F hn3 hinv hx hNul c hc⟩

noncomputable def recordNeutralFinePlanUniformContinuation :
    UniformRecordRespectingProjectiveContinuation 3 finePerspective coarsePerspective :=
  recordNeutralFineBornWeightPlan.realizingUniformContinuation

theorem recordNeutralFinePlanUniformContinuation_maps_state :
    recordNeutralFinePlanUniformContinuation.evolution psiBefore =
      fineWeightTargetState recordNeutralFineBornWeightPlan :=
  recordNeutralFineBornWeightPlan.realizingUniformContinuation_evolution_at_source

theorem recordNeutralFinePlanUniformContinuation_commutes :
    CommutesWithPerspectiveProjectors coarsePerspective
      recordNeutralFinePlanUniformContinuation.evolution :=
  recordNeutralFineBornWeightPlan.realizingUnitary_commutes

private theorem recordNeutral_complement_weight_eq :
    bornRecord coarsePerspective psiBefore recordNeutralPresentComplementCell = 16 / 25 := by
  change ‖projL label1Space psiBefore‖ ^ 2 = 16 / 25
  exact weight_label1Space_before

theorem recordNeutralFinePlan_anc0PhysicalRatio_eq :
    recordNeutralFinePlanUniformContinuation.physicalContinuatorBornRatio psiBefore
      recordNeutralPresentComplementCell recordNeutralFutureAnc0Cell = 9 / 25 := by
  unfold UniformRecordRespectingProjectiveContinuation.physicalContinuatorBornRatio
  rw [if_pos recordNeutral_parent_anc0]
  rw [recordNeutralFinePlanUniformContinuation_maps_state]
  change
    bornRecord finePerspective (fineWeightTargetState recordNeutralFineBornWeightPlan)
      recordNeutralFutureAnc0Cell /
      bornRecord coarsePerspective psiBefore recordNeutralPresentComplementCell = 9 / 25
  rw [recordNeutralFineWeightTarget_anc0, recordNeutral_complement_weight_eq]
  norm_num

theorem recordNeutralFinePlan_anc1PhysicalRatio_eq :
    recordNeutralFinePlanUniformContinuation.physicalContinuatorBornRatio psiBefore
      recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell = 16 / 25 := by
  unfold UniformRecordRespectingProjectiveContinuation.physicalContinuatorBornRatio
  rw [if_pos recordNeutral_parent_anc1]
  rw [recordNeutralFinePlanUniformContinuation_maps_state]
  change
    bornRecord finePerspective (fineWeightTargetState recordNeutralFineBornWeightPlan)
      recordNeutralFutureAnc1Cell /
      bornRecord coarsePerspective psiBefore recordNeutralPresentComplementCell = 16 / 25
  rw [recordNeutralFineWeightTarget_anc1, recordNeutral_complement_weight_eq]
  norm_num

private theorem recordNeutral_complement_weight_ne_zero :
    bornRecord coarsePerspective psiBefore recordNeutralPresentComplementCell ≠ 0 := by
  rw [recordNeutral_complement_weight_eq]
  norm_num

theorem recordNeutralFinePlan_anc0Credence_eq
    (F : RationalExpectationFamily (Projective.interface 3))
    (hinv : RefinementInvariantLocal F.V)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight (projectiveConcreteExpectationFamily F))
      (fineWeightTargetState recordNeutralFineBornWeightPlan)) :
    recordNeutralFinePlanUniformContinuation.step.continuatorCredence F
      recordNeutralPresentComplementCell recordNeutralFutureAnc0Cell = 9 / 25 := by
  calc
    recordNeutralFinePlanUniformContinuation.step.continuatorCredence F
        recordNeutralPresentComplementCell recordNeutralFutureAnc0Cell =
      recordNeutralFineBornWeightPlan.conditionalRatio
        recordNeutralPresentComplementCell recordNeutralFutureAnc0Cell := by
          exact recordNeutralFineBornWeightPlan.continuatorCredence_eq_conditionalRatio
            F (by norm_num) hinv psiBefore_norm hNul
            recordNeutralPresentComplementCell recordNeutral_complement_weight_ne_zero
            recordNeutralFutureAnc0Cell
    _ = 9 / 25 := by
      unfold conditionalRatio
      rw [if_pos recordNeutral_parent_anc0]
      rw [recordNeutralFineBornWeightPlan_anc0]
      rw [recordNeutral_complement_weight_eq]
      norm_num

theorem recordNeutralFinePlan_anc1Credence_eq
    (F : RationalExpectationFamily (Projective.interface 3))
    (hinv : RefinementInvariantLocal F.V)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight (projectiveConcreteExpectationFamily F))
      (fineWeightTargetState recordNeutralFineBornWeightPlan)) :
    recordNeutralFinePlanUniformContinuation.step.continuatorCredence F
      recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell = 16 / 25 := by
  calc
    recordNeutralFinePlanUniformContinuation.step.continuatorCredence F
        recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell =
      recordNeutralFineBornWeightPlan.conditionalRatio
        recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell := by
          exact recordNeutralFineBornWeightPlan.continuatorCredence_eq_conditionalRatio
            F (by norm_num) hinv psiBefore_norm hNul
            recordNeutralPresentComplementCell recordNeutral_complement_weight_ne_zero
            recordNeutralFutureAnc1Cell
    _ = 16 / 25 := by
      unfold conditionalRatio
      rw [if_pos recordNeutral_parent_anc1]
      rw [recordNeutralFineBornWeightPlan_anc1]
      rw [recordNeutral_complement_weight_eq]
      norm_num

theorem recordNeutralPhysicalFinePlanContinuation_integratedWitness
    (F : RationalExpectationFamily (Projective.interface 3))
    (hinv : RefinementInvariantLocal F.V)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight (projectiveConcreteExpectationFamily F))
      (fineWeightTargetState recordNeutralFineBornWeightPlan)) :
    CommutesWithPerspectiveProjectors coarsePerspective
        recordNeutralFinePlanUniformContinuation.evolution ∧
    recordNeutralFinePlanUniformContinuation.evolution psiBefore =
        fineWeightTargetState recordNeutralFineBornWeightPlan ∧
    ‖fineWeightTargetState recordNeutralFineBornWeightPlan‖ = 1 ∧
    bornRecord finePerspective (recordNeutralFinePlanUniformContinuation.evolution psiBefore)
        recordNeutralFutureAnc0Cell = 144 / 625 ∧
    bornRecord finePerspective (recordNeutralFinePlanUniformContinuation.evolution psiBefore)
        recordNeutralFutureAnc1Cell = 256 / 625 ∧
    recordNeutralFinePlanUniformContinuation.step.continuatorCredence F
        recordNeutralPresentComplementCell recordNeutralFutureAnc0Cell = 9 / 25 ∧
    recordNeutralFinePlanUniformContinuation.step.continuatorCredence F
        recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell = 16 / 25 := by
  refine ⟨recordNeutralFinePlanUniformContinuation_commutes,
    recordNeutralFinePlanUniformContinuation_maps_state,
    recordNeutralFineWeightTarget_normalized, ?_, ?_,
    recordNeutralFinePlan_anc0Credence_eq F hinv hNul,
    recordNeutralFinePlan_anc1Credence_eq F hinv hNul⟩
  · rw [recordNeutralFinePlanUniformContinuation_maps_state]
    exact recordNeutralFineWeightTarget_anc0
  · rw [recordNeutralFinePlanUniformContinuation_maps_state]
    exact recordNeutralFineWeightTarget_anc1

end FineBornWeightPlan

end
end EverettianProbability.Abstract
