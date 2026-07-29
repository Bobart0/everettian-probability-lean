import EverettianProbability.Diachronic.RecordNeutralPhysicalContinuation

/-!
**FR.** # Continuation uniformement respectueuse du record

Le temoin precedent concernait `psiBefore` et `psiAfter`. Ce module formule
une version uniforme : une meme transformation lineaire isometrique preserve
le record accessible et les poids borniens de chaque cellule presente pour
tout vecteur. Le couplage concret `coupleU` satisfait cette propriete.

Pour tout etat normalise `x`, il fournit ainsi une continuation physique de
`x` vers `coupleU x`. Sous les premisses explicites `NORM`, `PHYS` et `SEM`,
la credence d'un continuateur est alors le rapport du poids futur au poids
parent evalue avant l'evolution.

Ce resultat reste un temoin pour une transformation et un raffinement
particuliers. Il ne montre ni que cette classe est complete, ni que P6b ou
P8b sont clos.

**EN.** # Uniformly record-respecting continuation

The preceding witness concerned `psiBefore` and `psiAfter`. This module
states a uniform version: one linear isometric transformation preserves the
accessible record and every present-cell Born weight for every vector. The
concrete coupling `coupleU` satisfies this property.

For every normalized `x`, it therefore supplies a physical continuation from
`x` to `coupleU x`. Under the explicit `NORM`, `PHYS`, and `SEM` premises,
continuator credence is the ratio of future weight to parent weight evaluated
before the evolution.

The result remains a witness for one transformation and one refinement. It
does not show that this class is complete or that P6b or P8b are closed.
-/

namespace EverettianProbability.Abstract

open QuantumFoundations.BornRule Gleason
open EverettianProbability.PhysicalRefinement
open QuantumFoundations.Uhlhorn (projL_singleton_unit)
open scoped BigOperators Classical InnerProductSpace

noncomputable section

/-- A projective continuation whose transformation preserves the accessible
record and every present-cell Born weight for all state vectors. -/
structure UniformRecordRespectingProjectiveContinuation
    (n : Nat) (future present : Perspective n) where
  Record : Type
  step : ContinuationStep (Projective.interface n) future present
  evolution : H n →ₗ[ℂ] H n
  isometry : ∀ x : H n, ‖evolution x‖ = ‖x‖
  accessibleRecord : H n → Record
  record_preserved : ∀ x : H n, accessibleRecord x = accessibleRecord (evolution x)
  presentBornWeight_preserved :
    ∀ (x : H n) (c : (Projective.interface n).Cell present),
      ‖projL c.val x‖ ^ 2 = ‖projL c.val (evolution x)‖ ^ 2

namespace UniformRecordRespectingProjectiveContinuation

/-- Specialization of a uniform physical continuation to one normalized
initial state. -/
def atState
    {n : Nat} {future present : Perspective n}
    (W : UniformRecordRespectingProjectiveContinuation n future present)
    (x : H n) (hx : ‖x‖ = 1) :
    RecordRespectingProjectiveContinuation n future present where
  Record := W.Record
  step := W.step
  evolution := W.evolution
  stateBefore := x
  stateAfter := W.evolution x
  evolves := rfl
  isometry := W.isometry
  before_normalized := hx
  accessibleRecord := W.accessibleRecord
  record_preserved := W.record_preserved x
  presentBornWeight_preserved := by
    intro c
    exact W.presentBornWeight_preserved x c

@[simp] theorem atState_stateBefore
    {n : Nat} {future present : Perspective n}
    (W : UniformRecordRespectingProjectiveContinuation n future present)
    (x : H n) (hx : ‖x‖ = 1) :
    (W.atState x hx).stateBefore = x := rfl

@[simp] theorem atState_stateAfter
    {n : Nat} {future present : Perspective n}
    (W : UniformRecordRespectingProjectiveContinuation n future present)
    (x : H n) (hx : ‖x‖ = 1) :
    (W.atState x hx).stateAfter = W.evolution x := rfl

theorem atState_after_normalized
    {n : Nat} {future present : Perspective n}
    (W : UniformRecordRespectingProjectiveContinuation n future present)
    (x : H n) (hx : ‖x‖ = 1) :
    ‖(W.atState x hx).stateAfter‖ = 1 := by
  exact (W.atState x hx).after_normalized

end UniformRecordRespectingProjectiveContinuation

/-- Pythagorean decomposition over the two coarse record cells without a
normalization assumption. -/
theorem coarse_weight_sum_general (x : H 3) :
    ‖projL label0Line x‖ ^ 2 + ‖projL label1Space x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hpyth := QuantumFoundations.BornRule.sum_sq_projL_of_pairwise_isOrtho
    coarsePerspective.cells coarsePerspective.ortho x
  have htop : coarsePerspective.cells.sup id = (⊤ : Submodule ℂ (H 3)) := by
    rw [Finset.sup_id_eq_sSup]
    exact coarsePerspective.span
  have hid : projL (⊤ : Submodule ℂ (H 3)) = LinearMap.id := by
    unfold projL
    rw [Submodule.starProjection_top]
    rfl
  rw [htop, hid] at hpyth
  simp only [LinearMap.id_coe, id_eq] at hpyth
  rw [coarsePerspective_cells_eq,
    Finset.sum_insert (by simpa using label0Line_ne_label1Space),
    Finset.sum_singleton] at hpyth
  exact hpyth.symm

/-- The coupling leaves the coefficient along the recorded line unchanged. -/
theorem inner_b0_coupleU (x : H 3) :
    ⟪(b 0 : H 3), coupleU x⟫_ℂ = ⟪(b 0 : H 3), x⟫_ℂ := by
  unfold coupleU
  have h00 : ⟪(b 0 : H 3), (b 0 : H 3)⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
    rw [b0_unit]
    norm_num
  have h01 : ⟪(b 0 : H 3), (b 1 : H 3)⟫_ℂ = 0 := b.orthonormal.2 (by decide)
  have h02 : ⟪(b 0 : H 3), (b 2 : H 3)⟫_ℂ = 0 := b.orthonormal.2 (by decide)
  simp only [inner_add_right, inner_smul_right, h00, h01, h02,
    mul_one, mul_zero, add_zero]
  exact OrthonormalBasis.repr_apply_apply b x 0

/-- The coupling preserves the Born weight of `label0Line` for every state. -/
theorem coupleU_preserves_label0_bornWeight (x : H 3) :
    ‖projL label0Line (coupleU x)‖ ^ 2 = ‖projL label0Line x‖ ^ 2 := by
  unfold label0Line
  rw [projL_singleton_unit _ _ b0_unit, projL_singleton_unit _ _ b0_unit,
    inner_b0_coupleU]

/-- The coupling preserves the Born weight of the complementary coarse cell. -/
theorem coupleU_preserves_label1Space_bornWeight (x : H 3) :
    ‖projL label1Space (coupleU x)‖ ^ 2 = ‖projL label1Space x‖ ^ 2 := by
  have hBefore := coarse_weight_sum_general x
  have hAfter := coarse_weight_sum_general (coupleU x)
  rw [coupleU_preserves_label0_bornWeight, coupleU_isometry] at hAfter
  linarith

/-- Every coarse record cell has its Born weight preserved by `coupleU`. -/
theorem coupleU_preserves_coarseCell_bornWeight
    (x : H 3) (c : (Projective.interface 3).Cell coarsePerspective) :
    ‖projL c.val x‖ ^ 2 = ‖projL c.val (coupleU x)‖ ^ 2 := by
  rcases c with ⟨c, hc⟩
  rw [coarsePerspective_cells_eq] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with h0 | h1
  · subst c
    exact (coupleU_preserves_label0_bornWeight x).symm
  · subst c
    exact (coupleU_preserves_label1Space_bornWeight x).symm

/-- The accessible coarse record is preserved by the coupling for every state. -/
theorem accessibleRecord_coupleU (x : H 3) :
    accessibleRecord x = accessibleRecord (coupleU x) := by
  unfold accessibleRecord
  rw [coupleU_preserves_label0_bornWeight,
    coupleU_preserves_label1Space_bornWeight]

theorem accessibleRecord_psiBefore_psiAfter_from_uniform :
    accessibleRecord psiBefore = accessibleRecord psiAfter := by
  rw [← coupleU_psiBefore]
  exact accessibleRecord_coupleU psiBefore

/-- The record-neutral coupling packaged as a uniformly record-respecting
physical continuation. -/
def recordNeutralUniformPhysicalContinuation :
    UniformRecordRespectingProjectiveContinuation 3 finePerspective coarsePerspective where
  Record := ℝ × ℝ
  step := recordNeutralContinuationStep
  evolution := coupleULin
  isometry := by
    intro x
    exact coupleU_isometry x
  accessibleRecord := accessibleRecord
  record_preserved := by
    intro x
    change accessibleRecord x = accessibleRecord (coupleU x)
    exact accessibleRecord_coupleU x
  presentBornWeight_preserved := by
    intro x c
    change ‖projL c.val x‖ ^ 2 = ‖projL c.val (coupleU x)‖ ^ 2
    exact coupleU_preserves_coarseCell_bornWeight x c

/-- State-specific continuation obtained uniformly from any normalized state. -/
def recordNeutralPhysicalContinuationAt (x : H 3) (hx : ‖x‖ = 1) :
    RecordRespectingProjectiveContinuation 3 finePerspective coarsePerspective :=
  recordNeutralUniformPhysicalContinuation.atState x hx

@[simp] theorem recordNeutralPhysicalContinuationAt_stateBefore
    (x : H 3) (hx : ‖x‖ = 1) :
    (recordNeutralPhysicalContinuationAt x hx).stateBefore = x := rfl

@[simp] theorem recordNeutralPhysicalContinuationAt_stateAfter
    (x : H 3) (hx : ‖x‖ = 1) :
    (recordNeutralPhysicalContinuationAt x hx).stateAfter = coupleU x := rfl

theorem recordNeutralPhysicalContinuationAt_after_normalized
    (x : H 3) (hx : ‖x‖ = 1) :
    ‖(recordNeutralPhysicalContinuationAt x hx).stateAfter‖ = 1 := by
  exact recordNeutralUniformPhysicalContinuation.atState_after_normalized x hx

theorem recordNeutralPhysicalContinuationAt_psiBefore_stateAfter :
    (recordNeutralPhysicalContinuationAt psiBefore psiBefore_norm).stateAfter = psiAfter := by
  change coupleU psiBefore = psiAfter
  exact coupleU_psiBefore

/-- For every normalized initial state, continuator credence is the future
Born weight divided by the preserved parent weight evaluated before evolution. -/
theorem recordNeutralContinuatorCredence_eq_bornRatio_before
    (F : RationalExpectationFamily (Projective.interface 3))
    (hinv : RefinementInvariantLocal F.V)
    (x : H 3) (hx : ‖x‖ = 1)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight
        (projectiveConcreteExpectationFamily F)) (coupleU x))
    (c : (Projective.interface 3).Cell coarsePerspective)
    (hcBefore : ‖projL c.val x‖ ^ 2 ≠ 0)
    (i : (Projective.interface 3).Cell finePerspective) :
    recordNeutralContinuationStep.continuatorCredence F c i =
      if (Projective.interface 3).parentCell recordNeutral_refines i = c then
        ‖projL i.val (coupleU x)‖ ^ 2 / ‖projL c.val x‖ ^ 2
      else 0 := by
  have hxAfter : ‖coupleU x‖ = 1 := by rw [coupleU_isometry, hx]
  have hparentPreserved : ‖projL c.val x‖ ^ 2 =
      ‖projL c.val (coupleU x)‖ ^ 2 :=
    coupleU_preserves_coarseCell_bornWeight x c
  have hcAfter : ‖projL c.val (coupleU x)‖ ^ 2 ≠ 0 := by
    rw [← hparentPreserved]
    exact hcBefore
  have h := recordNeutralContinuationStep.projectiveContinuatorCredence_eq_bornRatio
    F (by norm_num) hinv hxAfter hNul c hcAfter i
  rw [← hparentPreserved] at h
  exact h

/-- Born conditional expected value for an arbitrary normalized state, with
the parent denominator evaluated before physical evolution. -/
theorem recordNeutralContinuatorExpectedValue_eq_born_before
    (F : RationalExpectationFamily (Projective.interface 3))
    (hinv : RefinementInvariantLocal F.V)
    (x : H 3) (hx : ‖x‖ = 1)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight
        (projectiveConcreteExpectationFamily F)) (coupleU x))
    (c : (Projective.interface 3).Cell coarsePerspective)
    (hcBefore : ‖projL c.val x‖ ^ 2 ≠ 0)
    (a : Act (Projective.interface 3)) :
    recordNeutralContinuationStep.continuatorExpectedValue F c a =
      ∑ i : (Projective.interface 3).Cell finePerspective,
        (if (Projective.interface 3).parentCell recordNeutral_refines i = c then
          ‖projL i.val (coupleU x)‖ ^ 2 / ‖projL c.val x‖ ^ 2 else 0) * a i.val := by
  unfold ContinuationStep.continuatorExpectedValue
  apply Finset.sum_congr rfl
  intro i _
  rw [recordNeutralContinuatorCredence_eq_bornRatio_before F hinv x hx hNul c hcBefore i]
  rfl

namespace RecordCredenceFamily

/-- Every admissible credence family obeys the same before-to-after
Born-ratio formula. -/
theorem recordNeutralAdmissibleCredence_eq_bornRatio_before
    (C : RecordCredenceFamily (Projective.interface 3))
    (F : RationalExpectationFamily (Projective.interface 3))
    (hnorm : C.NormalizedOnNonzeroMass F)
    (hdecision : C.RepresentsUnrestrictedDecisionValue F)
    (hodds : C.OddsInvariantUnderRecordRestriction F)
    (hinv : RefinementInvariantLocal F.V)
    (x : H 3) (hx : ‖x‖ = 1)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight
        (projectiveConcreteExpectationFamily F)) (coupleU x))
    (c : (Projective.interface 3).Cell coarsePerspective)
    (hcBefore : ‖projL c.val x‖ ^ 2 ≠ 0)
    (i : (Projective.interface 3).Cell finePerspective) :
    C.credence finePerspective (recordNeutralContinuationStep.continuatorCells c) i =
      if (Projective.interface 3).parentCell recordNeutral_refines i = c then
        ‖projL i.val (coupleU x)‖ ^ 2 / ‖projL c.val x‖ ^ 2
      else 0 := by
  have hxAfter : ‖coupleU x‖ = 1 := by rw [coupleU_isometry, hx]
  have hparentPreserved : ‖projL c.val x‖ ^ 2 =
      ‖projL c.val (coupleU x)‖ ^ 2 :=
    coupleU_preserves_coarseCell_bornWeight x c
  have hcAfter : ‖projL c.val (coupleU x)‖ ^ 2 ≠ 0 := by
    rw [← hparentPreserved]
    exact hcBefore
  have h := C.projectiveCredence_on_continuators_eq_bornRatio
    F hnorm hdecision hodds (by norm_num) hinv hxAfter hNul
    recordNeutralContinuationStep c hcAfter i
  rw [← hparentPreserved] at h
  exact h

end RecordCredenceFamily

/-- Integrated uniform physical witness. -/
theorem recordNeutralUniformPhysicalContinuation_integratedWitness :
    (∀ x : H 3, accessibleRecord x = accessibleRecord (coupleU x)) ∧
    (∀ (x : H 3) (c : (Projective.interface 3).Cell coarsePerspective),
      ‖projL c.val x‖ ^ 2 = ‖projL c.val (coupleU x)‖ ^ 2) ∧
    (∀ x : H 3, ‖coupleU x‖ = ‖x‖) := by
  exact ⟨accessibleRecord_coupleU, coupleU_preserves_coarseCell_bornWeight,
    coupleU_isometry⟩

end
end EverettianProbability.Abstract
