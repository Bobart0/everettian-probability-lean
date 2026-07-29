import EverettianProbability.Diachronic.ProjectiveBornContinuators
import EverettianProbability.PhysicalRefinement.RecordNeutralWitness

/-!
**FR.** # Temoin physique record-neutre de credence diachronique

Ce module raccorde le temoin unitaire-isometrique de P6a a la theorie
des continuateurs developpee dans P7--P8b. L'evolution concrete preserve
le record accessible et les poids borniens grossiers, tandis que les deux
cellules fines de la fibre de `label1Space` recoivent les credences exactes
`9/25` et `16/25`.

La lecture des cellules fines comme continuateurs et la qualification
record-neutre restent conditionnelles aux premisses semantiques et a
`RefinementNotInRecordAlgebra`. Le modele ne postule aucune factorisation
tensorielle ni aucune fermeture de P6b ou P8b.

**EN.** # Record-neutral physical witness of diachronic credence

This module connects the P6a isometric-unitary witness to the continuator
theory developed in P7--P8b. The concrete evolution preserves the accessible
record and coarse Born weights, while the two fine cells in the `label1Space`
fibre receive the exact credences `9/25` and `16/25`.

Reading the fine cells as continuators and calling the refinement
record-neutral remain conditional on the semantic premises and on
`RefinementNotInRecordAlgebra`. The model assumes no tensor factorization and
does not close P6b or P8b.
-/

namespace EverettianProbability.Abstract

open QuantumFoundations.BornRule Gleason
open EverettianProbability.PhysicalRefinement
open scoped BigOperators Classical InnerProductSpace

noncomputable section

/-- A projective continuation equipped with concrete isometric evolution,
an accessible record, and preservation of present Born weights. -/
structure RecordRespectingProjectiveContinuation
    (n : Nat)
    (future present : Perspective n) where
  Record : Type
  step : ContinuationStep (Projective.interface n) future present
  evolution : H n →ₗ[ℂ] H n
  stateBefore : H n
  stateAfter : H n
  evolves : evolution stateBefore = stateAfter
  isometry : ∀ x : H n, ‖evolution x‖ = ‖x‖
  before_normalized : ‖stateBefore‖ = 1
  accessibleRecord : H n → Record
  record_preserved : accessibleRecord stateBefore = accessibleRecord stateAfter
  presentBornWeight_preserved :
    ∀ c : (Projective.interface n).Cell present,
      ‖projL c.val stateBefore‖ ^ 2 = ‖projL c.val stateAfter‖ ^ 2

namespace RecordRespectingProjectiveContinuation

/-- An isometric continuation sends a normalized present state to a
normalized future state. -/
theorem after_normalized
    {n : Nat} {future present : Perspective n}
    (W : RecordRespectingProjectiveContinuation n future present) :
    ‖W.stateAfter‖ = 1 := by
  rw [← W.evolves, W.isometry]
  exact W.before_normalized

end RecordRespectingProjectiveContinuation

/-- The record-neutral refinement viewed as a future-to-present continuation. -/
def recordNeutralContinuationStep :
    ContinuationStep (Projective.interface 3) finePerspective coarsePerspective where
  refinement := recordNeutral_refines

/-- Named present and future cells of the record-neutral witness. -/
def recordNeutralPresentLabel0Cell :
    (Projective.interface 3).Cell coarsePerspective :=
  ⟨label0Line, by simp [coarsePerspective, Perspective.binary]⟩

def recordNeutralPresentComplementCell :
    (Projective.interface 3).Cell coarsePerspective :=
  ⟨label1Space, label1Space_mem_coarse⟩

def recordNeutralFutureLabel0Cell :
    (Projective.interface 3).Cell finePerspective :=
  ⟨label0Line, label0Line_mem_fine⟩

def recordNeutralFutureAnc0Cell :
    (Projective.interface 3).Cell finePerspective :=
  ⟨anc0Line, anc0Line_mem_fine⟩

def recordNeutralFutureAnc1Cell :
    (Projective.interface 3).Cell finePerspective :=
  ⟨anc1Line, anc1Line_mem_fine⟩

@[simp] theorem recordNeutral_parent_label0 :
    (Projective.interface 3).parentCell recordNeutral_refines
        recordNeutralFutureLabel0Cell = recordNeutralPresentLabel0Cell := by
  apply Subtype.ext
  exact parentOf_eq_of_le recordNeutral_refines label0Line_mem_fine
    recordNeutralPresentLabel0Cell.property le_rfl

@[simp] theorem recordNeutral_parent_anc0 :
    (Projective.interface 3).parentCell recordNeutral_refines
        recordNeutralFutureAnc0Cell = recordNeutralPresentComplementCell := by
  apply Subtype.ext
  exact parentOf_eq_of_le recordNeutral_refines anc0Line_mem_fine
    label1Space_mem_coarse anc0Line_le_label1Space

@[simp] theorem recordNeutral_parent_anc1 :
    (Projective.interface 3).parentCell recordNeutral_refines
        recordNeutralFutureAnc1Cell = recordNeutralPresentComplementCell := by
  apply Subtype.ext
  exact parentOf_eq_of_le recordNeutral_refines anc1Line_mem_fine
    label1Space_mem_coarse anc1Line_le_label1Space

theorem recordNeutral_presentLabel0_ne_complement :
    recordNeutralPresentLabel0Cell ≠ recordNeutralPresentComplementCell := by
  intro h
  apply label0Line_ne_label1Space
  exact congrArg Subtype.val h

/-- The existing P6a witness packaged as a physical projective continuation. -/
def recordNeutralPhysicalContinuation :
    RecordRespectingProjectiveContinuation 3 finePerspective coarsePerspective where
  Record := ℝ × ℝ
  step := recordNeutralContinuationStep
  evolution := coupleULin
  stateBefore := psiBefore
  stateAfter := psiAfter
  evolves := by
    change coupleU psiBefore = psiAfter
    exact coupleU_psiBefore
  isometry := by
    intro x
    exact coupleU_isometry x
  before_normalized := psiBefore_norm
  accessibleRecord := accessibleRecord
  record_preserved := recordNeutral_record_eq
  presentBornWeight_preserved := by
    intro c
    rcases c with ⟨c, hc⟩
    rw [coarsePerspective_cells_eq] at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with hlabel0 | hlabel1
    · subst c
      exact recordNeutral_bornWeight_eq.1
    · subst c
      exact recordNeutral_bornWeight_eq.2

theorem recordNeutralPhysicalContinuation_after_normalized :
    ‖recordNeutralPhysicalContinuation.stateAfter‖ = 1 := by
  exact recordNeutralPhysicalContinuation.after_normalized

/-- The newly distinguished fine cells are outside the stipulated record algebra. -/
theorem recordNeutralContinuation_refinementHiddenFromRecord :
    RefinementNotInRecordAlgebra :=
  refinementNotInRecordAlgebra_holds

private theorem label1Space_after_weight_ne_zero :
    ‖projL label1Space psiAfter‖ ^ 2 ≠ 0 := by
  rw [weight_label1Space_after]
  norm_num

/-- Exact Born credence of the first fine continuator within `label1Space`. -/
theorem recordNeutral_anc0ContinuatorCredence_eq_nine_twenty_fifths
    (F : RationalExpectationFamily (Projective.interface 3))
    (hinv : RefinementInvariantLocal F.V)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight
        (projectiveConcreteExpectationFamily F)) psiAfter) :
    recordNeutralContinuationStep.continuatorCredence F
        recordNeutralPresentComplementCell recordNeutralFutureAnc0Cell = 9 / 25 := by
  rw [recordNeutralContinuationStep.projectiveContinuatorCredence_eq_bornRatio
    F (by norm_num) hinv psiAfter_norm hNul recordNeutralPresentComplementCell
    label1Space_after_weight_ne_zero recordNeutralFutureAnc0Cell]
  rw [recordNeutral_parent_anc0]
  rw [if_pos rfl]
  change ‖projL anc0Line psiAfter‖ ^ 2 / ‖projL label1Space psiAfter‖ ^ 2 = 9 / 25
  rw [weight_anc0_after, weight_label1Space_after]
  norm_num

/-- Exact Born credence of the second fine continuator within `label1Space`. -/
theorem recordNeutral_anc1ContinuatorCredence_eq_sixteen_twenty_fifths
    (F : RationalExpectationFamily (Projective.interface 3))
    (hinv : RefinementInvariantLocal F.V)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight
        (projectiveConcreteExpectationFamily F)) psiAfter) :
    recordNeutralContinuationStep.continuatorCredence F
        recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell = 16 / 25 := by
  rw [recordNeutralContinuationStep.projectiveContinuatorCredence_eq_bornRatio
    F (by norm_num) hinv psiAfter_norm hNul recordNeutralPresentComplementCell
    label1Space_after_weight_ne_zero recordNeutralFutureAnc1Cell]
  rw [recordNeutral_parent_anc1]
  rw [if_pos rfl]
  change ‖projL anc1Line psiAfter‖ ^ 2 / ‖projL label1Space psiAfter‖ ^ 2 = 16 / 25
  rw [weight_anc1_after, weight_label1Space_after]
  norm_num

/-- The fine `label0Line` cell is outside the `label1Space` continuator fibre. -/
theorem recordNeutral_label0ContinuatorCredence_eq_zero
    (F : RationalExpectationFamily (Projective.interface 3)) :
    recordNeutralContinuationStep.continuatorCredence F
        recordNeutralPresentComplementCell recordNeutralFutureLabel0Cell = 0 := by
  apply recordNeutralContinuationStep.continuatorCredence_zero_of_parent_ne
  rw [recordNeutral_parent_label0]
  exact recordNeutral_presentLabel0_ne_complement

/-- The two fine continuators in `label1Space` exhaust its conditional credence. -/
theorem recordNeutral_splitCredence_eq_one
    (F : RationalExpectationFamily (Projective.interface 3))
    (hinv : RefinementInvariantLocal F.V)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight
        (projectiveConcreteExpectationFamily F)) psiAfter) :
    recordNeutralContinuationStep.continuatorCredence F
          recordNeutralPresentComplementCell recordNeutralFutureAnc0Cell +
      recordNeutralContinuationStep.continuatorCredence F
          recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell = 1 := by
  rw [recordNeutral_anc0ContinuatorCredence_eq_nine_twenty_fifths F hinv hNul,
    recordNeutral_anc1ContinuatorCredence_eq_sixteen_twenty_fifths F hinv hNul]
  norm_num

/-- Unit-payoff act on the second fine continuator. -/
def recordNeutralAnc1IndicatorAct : Act (Projective.interface 3) :=
  Act.indicator anc1Line

/-- The conditional value of the unit-payoff act on `anc1Line` is `16/25`. -/
theorem recordNeutral_anc1IndicatorExpectedValue_eq_sixteen_twenty_fifths
    (F : RationalExpectationFamily (Projective.interface 3))
    (hinv : RefinementInvariantLocal F.V)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight
        (projectiveConcreteExpectationFamily F)) psiAfter) :
    recordNeutralContinuationStep.continuatorExpectedValue F
        recordNeutralPresentComplementCell recordNeutralAnc1IndicatorAct = 16 / 25 := by
  have hindicator :
      Act.indicator ((Projective.interface 3).outcome recordNeutralFutureAnc1Cell) =
        recordNeutralAnc1IndicatorAct := by
    rfl
  rw [← hindicator,
    recordNeutralContinuationStep.continuatorExpectedValue_indicator F
      recordNeutralPresentComplementCell
      (projectiveInterface_outcome_injective finePerspective)
      recordNeutralFutureAnc1Cell]
  exact recordNeutral_anc1ContinuatorCredence_eq_sixteen_twenty_fifths F hinv hNul

namespace RecordCredenceFamily

/-- Every admissible credence family gives `9/25` to the first continuator. -/
theorem recordNeutral_admissibleCredence_anc0_eq_nine_twenty_fifths
    (C : RecordCredenceFamily (Projective.interface 3))
    (F : RationalExpectationFamily (Projective.interface 3))
    (hnorm : C.NormalizedOnNonzeroMass F)
    (hdecision : C.RepresentsUnrestrictedDecisionValue F)
    (hodds : C.OddsInvariantUnderRecordRestriction F)
    (hinv : RefinementInvariantLocal F.V)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight
        (projectiveConcreteExpectationFamily F)) psiAfter) :
    C.credence finePerspective
        (recordNeutralContinuationStep.continuatorCells recordNeutralPresentComplementCell)
        recordNeutralFutureAnc0Cell = 9 / 25 := by
  rw [C.projectiveCredence_on_continuators_eq_bornRatio F hnorm hdecision hodds
    (by norm_num) hinv psiAfter_norm hNul recordNeutralContinuationStep
    recordNeutralPresentComplementCell label1Space_after_weight_ne_zero
    recordNeutralFutureAnc0Cell]
  rw [recordNeutral_parent_anc0]
  rw [if_pos rfl]
  change ‖projL anc0Line psiAfter‖ ^ 2 / ‖projL label1Space psiAfter‖ ^ 2 = 9 / 25
  rw [weight_anc0_after, weight_label1Space_after]
  norm_num

/-- Every admissible credence family gives `16/25` to the second continuator. -/
theorem recordNeutral_admissibleCredence_anc1_eq_sixteen_twenty_fifths
    (C : RecordCredenceFamily (Projective.interface 3))
    (F : RationalExpectationFamily (Projective.interface 3))
    (hnorm : C.NormalizedOnNonzeroMass F)
    (hdecision : C.RepresentsUnrestrictedDecisionValue F)
    (hodds : C.OddsInvariantUnderRecordRestriction F)
    (hinv : RefinementInvariantLocal F.V)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight
        (projectiveConcreteExpectationFamily F)) psiAfter) :
    C.credence finePerspective
        (recordNeutralContinuationStep.continuatorCells recordNeutralPresentComplementCell)
        recordNeutralFutureAnc1Cell = 16 / 25 := by
  rw [C.projectiveCredence_on_continuators_eq_bornRatio F hnorm hdecision hodds
    (by norm_num) hinv psiAfter_norm hNul recordNeutralContinuationStep
    recordNeutralPresentComplementCell label1Space_after_weight_ne_zero
    recordNeutralFutureAnc1Cell]
  rw [recordNeutral_parent_anc1]
  rw [if_pos rfl]
  change ‖projL anc1Line psiAfter‖ ^ 2 / ‖projL label1Space psiAfter‖ ^ 2 = 16 / 25
  rw [weight_anc1_after, weight_label1Space_after]
  norm_num

end RecordCredenceFamily

/-- Integrated physical nontriviality witness. -/
theorem recordNeutralPhysicalContinuation_integratedWitness
    (F : RationalExpectationFamily (Projective.interface 3))
    (hinv : RefinementInvariantLocal F.V)
    (hNul : AxNul
      (EverettianProbability.BornCalibration.canonicalWeight
        (projectiveConcreteExpectationFamily F)) psiAfter) :
    recordNeutralPhysicalContinuation.accessibleRecord
          recordNeutralPhysicalContinuation.stateBefore =
      recordNeutralPhysicalContinuation.accessibleRecord
          recordNeutralPhysicalContinuation.stateAfter ∧
    recordNeutralContinuationStep.continuatorCredence F
          recordNeutralPresentComplementCell recordNeutralFutureAnc0Cell = 9 / 25 ∧
    recordNeutralContinuationStep.continuatorCredence F
          recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell = 16 / 25 ∧
    recordNeutralContinuationStep.continuatorCredence F
          recordNeutralPresentComplementCell recordNeutralFutureAnc0Cell +
      recordNeutralContinuationStep.continuatorCredence F
          recordNeutralPresentComplementCell recordNeutralFutureAnc1Cell = 1 := by
  exact ⟨recordNeutralPhysicalContinuation.record_preserved,
    recordNeutral_anc0ContinuatorCredence_eq_nine_twenty_fifths F hinv hNul,
    recordNeutral_anc1ContinuatorCredence_eq_sixteen_twenty_fifths F hinv hNul,
    recordNeutral_splitCredence_eq_one F hinv hNul⟩

end
end EverettianProbability.Abstract
