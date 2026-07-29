import EverettianProbability.Diachronic.UniformContinuationAssociativity

/-!
**FR.** # Composition physique des ratios de Born

Ce module relie la calibration de Born de P4 aux credences envers les
continuateurs. Un ratio physique est le rapport entre le poids de Born
d'une cellule future et celui de sa cellule presente, dans la fibre de
raffinement correspondante. Les regles de chaine restent conditionnelles
aux hypotheses explicites de non-nullite et de compatibilite des records.

**EN.** # Physical composition of Born ratios

This module connects P4 Born calibration to credence over continuators.
A physical ratio compares the Born weight of a future cell with that of
its present parent in the corresponding refinement fibre. The chain rules
remain conditional on explicit nonzero and record-compatibility hypotheses.
-/

namespace EverettianProbability.Abstract

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.PhysicalRefinement
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : Nat}

namespace UniformRecordRespectingProjectiveContinuation

/-- Physical Born ratio from a present cell before the evolution to a
future cell after the evolution. -/
def physicalContinuatorBornRatio
    {future present : Perspective n}
    (W : UniformRecordRespectingProjectiveContinuation n future present)
    (x : H n)
    (c : (Projective.interface n).Cell present)
    (i : (Projective.interface n).Cell future) : ℝ :=
  if (Projective.interface n).parentCell W.step.refinement i = c then
    ‖projL i.val (W.evolution x)‖ ^ 2 / ‖projL c.val x‖ ^ 2
  else
    0

theorem physicalContinuatorBornRatio_def
    {future present : Perspective n}
    (W : UniformRecordRespectingProjectiveContinuation n future present)
    (x : H n)
    (c : (Projective.interface n).Cell present)
    (i : (Projective.interface n).Cell future) :
    W.physicalContinuatorBornRatio x c i =
      if (Projective.interface n).parentCell W.step.refinement i = c then
        ‖projL i.val (W.evolution x)‖ ^ 2 / ‖projL c.val x‖ ^ 2
      else 0 := by
  rfl

/-- A future cell outside the continuation fibre has zero physical Born
ratio. -/
theorem physicalContinuatorBornRatio_zero_of_parent_ne
    {future present : Perspective n}
    (W : UniformRecordRespectingProjectiveContinuation n future present)
    (x : H n)
    (c : (Projective.interface n).Cell present)
    (i : (Projective.interface n).Cell future)
    (hparent : (Projective.interface n).parentCell W.step.refinement i ≠ c) :
    W.physicalContinuatorBornRatio x c i = 0 := by
  unfold physicalContinuatorBornRatio
  rw [if_neg hparent]

/-- Under P4 calibration, canonical continuator credence is the physical
before-to-after Born ratio. -/
theorem continuatorCredence_eq_physicalContinuatorBornRatio
    {future present : Perspective n}
    (W : UniformRecordRespectingProjectiveContinuation n future present)
    (F : RationalExpectationFamily (Projective.interface n))
    (hn3 : 3 ≤ n)
    (hinv : RefinementInvariantLocal F.V)
    (x : H n)
    (hx : ‖x‖ = 1)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight
        (projectiveConcreteExpectationFamily F))
      (W.evolution x))
    (c : (Projective.interface n).Cell present)
    (hcBefore : ‖projL c.val x‖ ^ 2 ≠ 0)
    (i : (Projective.interface n).Cell future) :
    W.step.continuatorCredence F c i = W.physicalContinuatorBornRatio x c i := by
  have hxAfter : ‖W.evolution x‖ = 1 := W.evolved_normalized x hx
  have hpreserved : ‖projL c.val x‖ ^ 2 = ‖projL c.val (W.evolution x)‖ ^ 2 :=
    W.presentBornWeight_preserved x c
  have hcAfter : ‖projL c.val (W.evolution x)‖ ^ 2 ≠ 0 := by
    rw [← hpreserved]
    exact hcBefore
  have h := W.step.projectiveContinuatorCredence_eq_bornRatio
    F hn3 hinv hxAfter hNul c hcAfter i
  unfold physicalContinuatorBornRatio
  rw [← hpreserved] at h
  exact h

/-- Physical Born-ratio chain rule at the actual intermediate parent. -/
theorem physicalContinuatorBornRatio_chain_at_parent
    {future middle present : Perspective n}
    (later : UniformRecordRespectingProjectiveContinuation n future middle)
    (earlier : UniformRecordRespectingProjectiveContinuation n middle present)
    (hlaterRecord : PreservesRecordObservable earlier.accessibleRecord later.evolution)
    (x : H n)
    (c : (Projective.interface n).Cell present)
    (i : (Projective.interface n).Cell future)
    (hc : ‖projL c.val x‖ ^ 2 ≠ 0)
    (hj : ‖projL ((Projective.interface n).parentCell later.step.refinement i).val
      (earlier.evolution x)‖ ^ 2 ≠ 0)
    (hancestor : (Projective.interface n).parentCell earlier.step.refinement
      ((Projective.interface n).parentCell later.step.refinement i) = c) :
    earlier.physicalContinuatorBornRatio x c
        ((Projective.interface n).parentCell later.step.refinement i) *
      later.physicalContinuatorBornRatio (earlier.evolution x)
        ((Projective.interface n).parentCell later.step.refinement i) i =
      (later.trans earlier hlaterRecord).physicalContinuatorBornRatio x c i := by
  unfold physicalContinuatorBornRatio
  have hcomposite : (Projective.interface n).parentCell
      (later.trans earlier hlaterRecord).step.refinement i = c := by
    change (Projective.interface n).parentCell
      ((Projective.interface n).trans later.step.refinement earlier.step.refinement) i = c
    rw [(Projective.interface n).parentCell_trans
      later.step.refinement earlier.step.refinement i, hancestor]
  rw [if_pos hancestor, if_pos rfl, if_pos hcomposite]
  change
    (‖projL ((Projective.interface n).parentCell later.step.refinement i).val
        (earlier.evolution x)‖ ^ 2 / ‖projL c.val x‖ ^ 2) *
      (‖projL i.val (later.evolution (earlier.evolution x))‖ ^ 2 /
        ‖projL ((Projective.interface n).parentCell later.step.refinement i).val
          (earlier.evolution x)‖ ^ 2) =
      ‖projL i.val (later.evolution (earlier.evolution x))‖ ^ 2 /
        ‖projL c.val x‖ ^ 2
  have hcnorm : ‖projL c.val x‖ ≠ 0 := fun h => hc (by simp [h])
  have hjnorm : ‖projL ((Projective.interface n).parentCell later.step.refinement i).val
      (earlier.evolution x)‖ ≠ 0 := by
    intro h
    apply hj
    change ‖projL (parentOf later.step.refinement i.val) (earlier.evolution x)‖ ^ 2 = 0
    change ‖projL (parentOf later.step.refinement i.val) (earlier.evolution x)‖ = 0 at h
    simp [h]
  field_simp [hcnorm, hjnorm]

/-- Summing the products of ratios over intermediate cells gives the
direct ratio. -/
theorem sum_intermediatePhysicalBornRatio_eq_composite
    {future middle present : Perspective n}
    (later : UniformRecordRespectingProjectiveContinuation n future middle)
    (earlier : UniformRecordRespectingProjectiveContinuation n middle present)
    (hlaterRecord : PreservesRecordObservable earlier.accessibleRecord later.evolution)
    (x : H n)
    (c : (Projective.interface n).Cell present)
    (i : (Projective.interface n).Cell future)
    (hc : ‖projL c.val x‖ ^ 2 ≠ 0)
    (hj : ‖projL ((Projective.interface n).parentCell later.step.refinement i).val
      (earlier.evolution x)‖ ^ 2 ≠ 0)
    (hancestor : (Projective.interface n).parentCell earlier.step.refinement
      ((Projective.interface n).parentCell later.step.refinement i) = c) :
    (∑ j : (Projective.interface n).Cell middle,
      earlier.physicalContinuatorBornRatio x c j *
        later.physicalContinuatorBornRatio (earlier.evolution x) j i) =
      (later.trans earlier hlaterRecord).physicalContinuatorBornRatio x c i := by
  let j₀ : (Projective.interface n).Cell middle :=
    (Projective.interface n).parentCell later.step.refinement i
  rw [Finset.sum_eq_single j₀]
  · exact physicalContinuatorBornRatio_chain_at_parent later earlier hlaterRecord
      x c i hc hj hancestor
  · intro j _ hne
    have hparent : (Projective.interface n).parentCell later.step.refinement i ≠ j :=
      fun h => hne h.symm
    rw [later.physicalContinuatorBornRatio_zero_of_parent_ne
      (earlier.evolution x) j i hparent]
    simp
  · exact fun hnot => (hnot (Finset.mem_univ j₀)).elim

/-- Both triple parenthesizations give the same earliest parent for a final cell. -/
theorem trans_associated_parentCell_eq
    {future middle₂ middle₁ present : Perspective n}
    (third : UniformRecordRespectingProjectiveContinuation n future middle₂)
    (second : UniformRecordRespectingProjectiveContinuation n middle₂ middle₁)
    (first : UniformRecordRespectingProjectiveContinuation n middle₁ present)
    (hThirdSecond : PreservesRecordObservable second.accessibleRecord third.evolution)
    (hSecondFirst : PreservesRecordObservable first.accessibleRecord second.evolution)
    (hThirdFirst : PreservesRecordObservable first.accessibleRecord third.evolution)
    (i : (Projective.interface n).Cell future) :
    (Projective.interface n).parentCell
    (transLeftAssociated third second first hThirdSecond hSecondFirst hThirdFirst).step.refinement i =
      (Projective.interface n).parentCell
        (transRightAssociated third second first hThirdSecond hSecondFirst hThirdFirst).step.refinement i := by
  change (Projective.interface n).parentCell
      ((Projective.interface n).trans
        ((Projective.interface n).trans third.step.refinement second.step.refinement)
        first.step.refinement) i =
    (Projective.interface n).parentCell
      ((Projective.interface n).trans third.step.refinement
        ((Projective.interface n).trans second.step.refinement first.step.refinement)) i
  rfl

/-- The direct physical ratio is independent of triple parenthesization. -/
theorem physicalContinuatorBornRatio_associative
    {future middle₂ middle₁ present : Perspective n}
    (third : UniformRecordRespectingProjectiveContinuation n future middle₂)
    (second : UniformRecordRespectingProjectiveContinuation n middle₂ middle₁)
    (first : UniformRecordRespectingProjectiveContinuation n middle₁ present)
    (hThirdSecond : PreservesRecordObservable second.accessibleRecord third.evolution)
    (hSecondFirst : PreservesRecordObservable first.accessibleRecord second.evolution)
    (hThirdFirst : PreservesRecordObservable first.accessibleRecord third.evolution)
    (x : H n) (c : (Projective.interface n).Cell present)
    (i : (Projective.interface n).Cell future) :
    (transLeftAssociated third second first hThirdSecond hSecondFirst hThirdFirst).physicalContinuatorBornRatio x c i =
    (transRightAssociated third second first hThirdSecond hSecondFirst hThirdFirst).physicalContinuatorBornRatio x c i := by
  unfold physicalContinuatorBornRatio
  rw [transLeftAssociated_evolution_apply, transRightAssociated_evolution_apply,
    trans_associated_parentCell_eq third second first hThirdSecond hSecondFirst hThirdFirst i]

/-- Under P4 calibration, canonical continuator credence is independent of
the parenthesization of three compatible continuations. -/
theorem continuatorCredence_associative_physical
    {future middle₂ middle₁ present : Perspective n}
    (third : UniformRecordRespectingProjectiveContinuation n future middle₂)
    (second : UniformRecordRespectingProjectiveContinuation n middle₂ middle₁)
    (first : UniformRecordRespectingProjectiveContinuation n middle₁ present)
    (hThirdSecond : PreservesRecordObservable second.accessibleRecord third.evolution)
    (hSecondFirst : PreservesRecordObservable first.accessibleRecord second.evolution)
    (hThirdFirst : PreservesRecordObservable first.accessibleRecord third.evolution)
    (F : RationalExpectationFamily (Projective.interface n))
    (hn3 : 3 ≤ n) (hinv : RefinementInvariantLocal F.V)
    (x : H n) (hx : ‖x‖ = 1)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight
        (projectiveConcreteExpectationFamily F))
      (third.evolution (second.evolution (first.evolution x))))
    (c : (Projective.interface n).Cell present)
    (hc : ‖projL c.val x‖ ^ 2 ≠ 0)
    (i : (Projective.interface n).Cell future) :
    (transLeftAssociated third second first hThirdSecond hSecondFirst hThirdFirst).step.continuatorCredence F c i =
    (transRightAssociated third second first hThirdSecond hSecondFirst hThirdFirst).step.continuatorCredence F c i := by
  let left := transLeftAssociated third second first hThirdSecond hSecondFirst hThirdFirst
  let right := transRightAssociated third second first hThirdSecond hSecondFirst hThirdFirst
  have hNulLeft : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight
        (projectiveConcreteExpectationFamily F)) (left.evolution x) := by
    simpa [left, transLeftAssociated_evolution_apply] using hNul
  have hNulRight : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight
        (projectiveConcreteExpectationFamily F)) (right.evolution x) := by
    simpa [right, transRightAssociated_evolution_apply] using hNul
  calc
    left.step.continuatorCredence F c i = left.physicalContinuatorBornRatio x c i :=
      left.continuatorCredence_eq_physicalContinuatorBornRatio F hn3 hinv x hx hNulLeft c hc i
    _ = right.physicalContinuatorBornRatio x c i :=
      physicalContinuatorBornRatio_associative third second first
        hThirdSecond hSecondFirst hThirdFirst x c i
    _ = right.step.continuatorCredence F c i :=
      (right.continuatorCredence_eq_physicalContinuatorBornRatio
        F hn3 hinv x hx hNulRight c hc i).symm

/-- Three successive physical Born ratios equal the direct right-associated ratio. -/
theorem physicalContinuatorBornRatio_threeStage_product
    {future middle₂ middle₁ present : Perspective n}
    (third : UniformRecordRespectingProjectiveContinuation n future middle₂)
    (second : UniformRecordRespectingProjectiveContinuation n middle₂ middle₁)
    (first : UniformRecordRespectingProjectiveContinuation n middle₁ present)
    (hThirdSecond : PreservesRecordObservable second.accessibleRecord third.evolution)
    (hSecondFirst : PreservesRecordObservable first.accessibleRecord second.evolution)
    (hThirdFirst : PreservesRecordObservable first.accessibleRecord third.evolution)
    (x : H n) (c : (Projective.interface n).Cell present)
    (j₁ : (Projective.interface n).Cell middle₁)
    (j₂ : (Projective.interface n).Cell middle₂)
    (i : (Projective.interface n).Cell future)
    (hc : ‖projL c.val x‖ ^ 2 ≠ 0)
    (hj₁ : ‖projL j₁.val (first.evolution x)‖ ^ 2 ≠ 0)
    (hj₂ : ‖projL j₂.val (second.evolution (first.evolution x))‖ ^ 2 ≠ 0)
    (hParent₁ : (Projective.interface n).parentCell first.step.refinement j₁ = c)
    (hParent₂ : (Projective.interface n).parentCell second.step.refinement j₂ = j₁)
    (hParent₃ : (Projective.interface n).parentCell third.step.refinement i = j₂) :
    first.physicalContinuatorBornRatio x c j₁ *
      second.physicalContinuatorBornRatio (first.evolution x) j₁ j₂ *
      third.physicalContinuatorBornRatio (second.evolution (first.evolution x)) j₂ i =
    (transRightAssociated third second first hThirdSecond hSecondFirst hThirdFirst).physicalContinuatorBornRatio x c i := by
  unfold physicalContinuatorBornRatio
  have hParentTriple : (Projective.interface n).parentCell
      (transRightAssociated third second first hThirdSecond hSecondFirst hThirdFirst).step.refinement i = c := by
    change (Projective.interface n).parentCell
      ((Projective.interface n).trans third.step.refinement
        ((Projective.interface n).trans second.step.refinement first.step.refinement)) i = c
    rw [(Projective.interface n).parentCell_trans
      third.step.refinement ((Projective.interface n).trans
        second.step.refinement first.step.refinement) i,
      hParent₃,
      (Projective.interface n).parentCell_trans
        second.step.refinement first.step.refinement j₂,
      hParent₂, hParent₁]
  rw [if_pos hParent₁, if_pos hParent₂, if_pos hParent₃, if_pos hParentTriple]
  change
    (‖projL j₁.val (first.evolution x)‖ ^ 2 / ‖projL c.val x‖ ^ 2) *
      (‖projL j₂.val (second.evolution (first.evolution x))‖ ^ 2 /
        ‖projL j₁.val (first.evolution x)‖ ^ 2) *
      (‖projL i.val (third.evolution (second.evolution (first.evolution x)))‖ ^ 2 /
        ‖projL j₂.val (second.evolution (first.evolution x))‖ ^ 2) =
      ‖projL i.val (third.evolution (second.evolution (first.evolution x)))‖ ^ 2 /
        ‖projL c.val x‖ ^ 2
  have hcnorm : ‖projL c.val x‖ ≠ 0 := fun h => hc (by simp [h])
  have hj₁norm : ‖projL j₁.val (first.evolution x)‖ ≠ 0 := fun h => hj₁ (by simp [h])
  have hj₂norm : ‖projL j₂.val (second.evolution (first.evolution x))‖ ≠ 0 := fun h => hj₂ (by simp [h])
  field_simp [hcnorm, hj₁norm, hj₂norm]

theorem physicalContinuatorBornRatio_threeStage_product_left
    {future middle₂ middle₁ present : Perspective n}
    (third : UniformRecordRespectingProjectiveContinuation n future middle₂)
    (second : UniformRecordRespectingProjectiveContinuation n middle₂ middle₁)
    (first : UniformRecordRespectingProjectiveContinuation n middle₁ present)
    (hThirdSecond : PreservesRecordObservable second.accessibleRecord third.evolution)
    (hSecondFirst : PreservesRecordObservable first.accessibleRecord second.evolution)
    (hThirdFirst : PreservesRecordObservable first.accessibleRecord third.evolution)
    (x : H n) (c : (Projective.interface n).Cell present)
    (j₁ : (Projective.interface n).Cell middle₁) (j₂ : (Projective.interface n).Cell middle₂)
    (i : (Projective.interface n).Cell future)
    (hc : ‖projL c.val x‖ ^ 2 ≠ 0)
    (hj₁ : ‖projL j₁.val (first.evolution x)‖ ^ 2 ≠ 0)
    (hj₂ : ‖projL j₂.val (second.evolution (first.evolution x))‖ ^ 2 ≠ 0)
    (hParent₁ : (Projective.interface n).parentCell first.step.refinement j₁ = c)
    (hParent₂ : (Projective.interface n).parentCell second.step.refinement j₂ = j₁)
    (hParent₃ : (Projective.interface n).parentCell third.step.refinement i = j₂) :
    first.physicalContinuatorBornRatio x c j₁ *
      second.physicalContinuatorBornRatio (first.evolution x) j₁ j₂ *
      third.physicalContinuatorBornRatio (second.evolution (first.evolution x)) j₂ i =
    (transLeftAssociated third second first hThirdSecond hSecondFirst hThirdFirst).physicalContinuatorBornRatio x c i := by
  rw [physicalContinuatorBornRatio_threeStage_product third second first
    hThirdSecond hSecondFirst hThirdFirst x c j₁ j₂ i hc hj₁ hj₂ hParent₁ hParent₂ hParent₃]
  exact (physicalContinuatorBornRatio_associative third second first
    hThirdSecond hSecondFirst hThirdFirst x c i).symm

/-- The concrete left-associated three-stage process assigns physical Born
ratio `16 / 25` to `anc1Line`. -/
theorem recordNeutralThreeStageLeft_anc1PhysicalBornRatio_eq :
    recordNeutralThreeStageLeft.physicalContinuatorBornRatio psiBefore
      recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell = 16 / 25 := by
  unfold physicalContinuatorBornRatio
  have hparent : (Projective.interface 3).parentCell
      recordNeutralThreeStageLeft.step.refinement recordNeutralFutureAnc1Cell =
      recordNeutralPresentComplementCell := by
    change (Projective.interface 3).parentCell
      ((Projective.interface 3).trans
        ((Projective.interface 3).trans ((Projective.interface 3).refl finePerspective)
          recordNeutral_refines)
        ((Projective.interface 3).refl coarsePerspective)) recordNeutralFutureAnc1Cell =
      recordNeutralPresentComplementCell
    rw [(Projective.interface 3).parentCell_trans
      ((Projective.interface 3).trans ((Projective.interface 3).refl finePerspective)
        recordNeutral_refines)
      ((Projective.interface 3).refl coarsePerspective)
      recordNeutralFutureAnc1Cell,
      (Projective.interface 3).parentCell_trans
      ((Projective.interface 3).refl finePerspective)
      recordNeutral_refines
      recordNeutralFutureAnc1Cell,
      (Projective.interface 3).parentCell_refl finePerspective recordNeutralFutureAnc1Cell,
      recordNeutral_parent_anc1,
      (Projective.interface 3).parentCell_refl coarsePerspective
        recordNeutralPresentComplementCell]
  rw [if_pos hparent, recordNeutralThreeStageLeft_evolution, coupleU_psiBefore]
  change ‖projL anc1Line psiAfter‖ ^ 2 / ‖projL label1Space psiBefore‖ ^ 2 = 16 / 25
  rw [weight_anc1_after, weight_label1Space_before]
  norm_num

theorem recordNeutralThreeStageRight_anc1PhysicalBornRatio_eq :
    recordNeutralThreeStageRight.physicalContinuatorBornRatio psiBefore
      recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell = 16 / 25 := by
  calc
    recordNeutralThreeStageRight.physicalContinuatorBornRatio psiBefore
        recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell =
      recordNeutralThreeStageLeft.physicalContinuatorBornRatio psiBefore
        recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell := by
        exact (physicalContinuatorBornRatio_associative
          recordNeutralFutureIdentity recordNeutralUniformPhysicalContinuation
          recordNeutralPresentIdentity
          (preservesRecordObservable_id
            EverettianProbability.PhysicalRefinement.accessibleRecord)
          accessibleRecord_coupleU
          (preservesRecordObservable_id
            EverettianProbability.PhysicalRefinement.accessibleRecord)
          psiBefore recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell).symm
    _ = 16 / 25 := recordNeutralThreeStageLeft_anc1PhysicalBornRatio_eq

/-- Concrete nontrivial witness of physically composed Born ratios. -/
theorem recordNeutralThreeStage_physicalBornRatioWitness :
    recordNeutralThreeStageLeft.physicalContinuatorBornRatio psiBefore
        recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell =
      recordNeutralThreeStageRight.physicalContinuatorBornRatio psiBefore
        recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell ∧
    recordNeutralThreeStageLeft.physicalContinuatorBornRatio psiBefore
        recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell = 16 / 25 ∧
    recordNeutralThreeStageRight.physicalContinuatorBornRatio psiBefore
        recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell = 16 / 25 := by
  refine ⟨physicalContinuatorBornRatio_associative
    recordNeutralFutureIdentity recordNeutralUniformPhysicalContinuation
    recordNeutralPresentIdentity
    (preservesRecordObservable_id
      EverettianProbability.PhysicalRefinement.accessibleRecord)
    accessibleRecord_coupleU
    (preservesRecordObservable_id
      EverettianProbability.PhysicalRefinement.accessibleRecord)
    psiBefore recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell,
    recordNeutralThreeStageLeft_anc1PhysicalBornRatio_eq,
    recordNeutralThreeStageRight_anc1PhysicalBornRatio_eq⟩

end UniformRecordRespectingProjectiveContinuation

end
end EverettianProbability.Abstract
