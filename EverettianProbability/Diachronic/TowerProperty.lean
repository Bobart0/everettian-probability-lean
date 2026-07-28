import EverettianProbability.Diachronic.FutureActTotalExpectation

/-!
**FR.** # Loi de la tour pour les continuateurs

Ce module compare le conditionnement direct sur les continuateurs futurs d'une
cellule présente au conditionnement en deux étapes, d'abord parmi ses
continuateurs intermédiaires puis parmi les continuateurs futurs de chacun.
La loi de la tour établit que les deux évaluations coïncident.

Le noyau algébrique est la règle de chaîne `Cr(j | c) Cr(i | j) = Cr(i | c)`
au parent intermédiaire de `i`; sa forme sommée reconstruit la crédence directe
des continuateurs lointains. Le résultat est ensuite transporté à toute
famille de crédences admissible.

Ce module relie `MATH`, `NORM` et `SEM`. Il ne démontre pas qu'une étape
abstraite de continuation est une évolution unitaire physiquement réalisable.

**EN.** # Tower property for continuators

This module compares direct conditioning on the future continuators of a
present cell with two-stage conditioning, first among its intermediate
continuators and then among each of their future continuators. The tower
property proves that the two evaluations coincide.

Its algebraic core is the chain rule `Cr(j | c) Cr(i | j) = Cr(i | c)` at the
intermediate parent of `i`; the summed form reconstructs direct distant
continuator credence. The result is then transported to every admissible
credence family.

This module connects `MATH`, `NORM`, and `SEM`. It does not prove that an
abstract continuation step is a physically realizable unitary evolution.
-/

namespace EverettianProbability.Abstract

open scoped BigOperators Classical

noncomputable section

variable {I : PerspectiveInterface}

namespace ContinuationStep

/-- A zero canonical weight for a future cell forces zero continuator
credence, irrespective of the conditioning present cell. -/
theorem continuatorCredence_eq_zero_of_futureWeight_eq_zero
    (F : RationalExpectationFamily I)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {future present : I.Perspective}
    (step : ContinuationStep I future present)
    (c : I.Cell present)
    (i : I.Cell future)
    (hi : canonicalWeight F future i = 0) :
    step.continuatorCredence F c i = 0 := by
  rw [step.continuatorCredence_eq_conditionalWeight_total F hinv hInjAll c i]
  unfold conditionalWeight
  by_cases hc : canonicalWeight F present c = 0
  · simp [hc]
  · by_cases hparent : I.parentCell step.refinement i = c
    · simp [hc, hparent, hi]
    · simp [hc, hparent]

/-- A future cell that is not a continuator of `c` receives zero continuator
credence. -/
theorem continuatorCredence_zero_of_parent_ne
    (F : RationalExpectationFamily I)
    {future present : I.Perspective}
    (step : ContinuationStep I future present)
    (c : I.Cell present)
    (i : I.Cell future)
    (hparent : I.parentCell step.refinement i ≠ c) :
    step.continuatorCredence F c i = 0 := by
  unfold continuatorCredence
  apply recordConditionedCredence_zero_of_not_mem
  simpa [continuatorCells] using hparent

/-- Credence chain rule at the actual intermediate parent of a future cell. -/
theorem continuatorCredence_chain_rule_at_parent
    (F : RationalExpectationFamily I)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {future middle present : I.Perspective}
    (later : ContinuationStep I future middle)
    (earlier : ContinuationStep I middle present)
    (c : I.Cell present)
    (hc : canonicalWeight F present c ≠ 0)
    (i : I.Cell future) :
    earlier.continuatorCredence F c (I.parentCell later.refinement i) *
        later.continuatorCredence F (I.parentCell later.refinement i) i =
      (later.trans earlier).continuatorCredence F c i := by
  let j : I.Cell middle := I.parentCell later.refinement i
  change earlier.continuatorCredence F c j * later.continuatorCredence F j i =
    (later.trans earlier).continuatorCredence F c i
  rw [earlier.continuatorCredence_eq_conditionalWeight_total F hinv hInjAll c j,
    later.continuatorCredence_eq_conditionalWeight_total F hinv hInjAll j i,
    (later.trans earlier).continuatorCredence_eq_conditionalWeight_total F hinv hInjAll c i]
  have hparent_later : I.parentCell later.refinement i = j := by rfl
  by_cases hj : canonicalWeight F middle j = 0
  · have hi : canonicalWeight F future i = 0 := by
      have h := canonicalWeight_mul_conditionalWeight F hinv hInjAll later j i
      rw [if_pos hparent_later] at h
      simpa [hj] using h.symm
    unfold conditionalWeight
    by_cases hjc : I.parentCell earlier.refinement j = c
    · have htrans : I.parentCell (I.trans later.refinement earlier.refinement) i = c := by
        rw [I.parentCell_trans, hparent_later, hjc]
      simp [hc, hj, hi, hjc, htrans, ContinuationStep.trans]
    · have htrans : I.parentCell (I.trans later.refinement earlier.refinement) i ≠ c := by
        rw [I.parentCell_trans, hparent_later]
        exact hjc
      simp [hc, hj, hjc, htrans, ContinuationStep.trans]
  · unfold conditionalWeight
    by_cases hjc : I.parentCell earlier.refinement j = c
    · have htrans : I.parentCell (I.trans later.refinement earlier.refinement) i = c := by
        rw [I.parentCell_trans, hparent_later, hjc]
      simp only [hc, hj, hparent_later, hjc, htrans, if_false, if_true,
        ContinuationStep.trans]
      field_simp [hc, hj]
    · have htrans : I.parentCell (I.trans later.refinement earlier.refinement) i ≠ c := by
        rw [I.parentCell_trans, hparent_later]
        exact hjc
      simp [hc, hj, hparent_later, hjc, htrans, ContinuationStep.trans]

/-- Summing over all intermediate cells reconstructs the direct credence of a
distant continuator. -/
theorem sum_intermediateCredence_mul_laterCredence_eq_composite
    (F : RationalExpectationFamily I)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {future middle present : I.Perspective}
    (later : ContinuationStep I future middle)
    (earlier : ContinuationStep I middle present)
    (c : I.Cell present)
    (hc : canonicalWeight F present c ≠ 0)
    (i : I.Cell future) :
    (∑ j : I.Cell middle,
      earlier.continuatorCredence F c j * later.continuatorCredence F j i) =
      (later.trans earlier).continuatorCredence F c i := by
  let j₀ : I.Cell middle := I.parentCell later.refinement i
  rw [Finset.sum_eq_single j₀]
  · exact later.continuatorCredence_chain_rule_at_parent F hinv hInjAll earlier c hc i
  · intro j hj hne
    have hparent : I.parentCell later.refinement i ≠ j := fun h => hne h.symm
    rw [later.continuatorCredence_zero_of_parent_ne F j i hparent]
    simp
  · exact fun hnot => (hnot (Finset.mem_univ j₀)).elim

/-- Two-stage conditional evaluation of a future act. -/
def stagedContinuatorExpectedValue
    (F : RationalExpectationFamily I)
    {future middle present : I.Perspective}
    (later : ContinuationStep I future middle)
    (earlier : ContinuationStep I middle present)
    (c : I.Cell present)
    (a : Act I) : ℝ :=
  ∑ j : I.Cell middle,
    earlier.continuatorCredence F c j * later.continuatorExpectedValue F j a

@[simp]
theorem stagedContinuatorExpectedValue_def
    (F : RationalExpectationFamily I)
    {future middle present : I.Perspective}
    (later : ContinuationStep I future middle)
    (earlier : ContinuationStep I middle present)
    (c : I.Cell present)
    (a : Act I) :
    stagedContinuatorExpectedValue F later earlier c a =
      ∑ j : I.Cell middle,
        earlier.continuatorCredence F c j * later.continuatorExpectedValue F j a := by
  rfl

/-- Tower property for canonical continuator credence. -/
theorem continuatorExpectedValue_tower
    (F : RationalExpectationFamily I)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {future middle present : I.Perspective}
    (later : ContinuationStep I future middle)
    (earlier : ContinuationStep I middle present)
    (c : I.Cell present)
    (hc : canonicalWeight F present c ≠ 0)
    (a : Act I) :
    (later.trans earlier).continuatorExpectedValue F c a =
      ContinuationStep.stagedContinuatorExpectedValue F later earlier c a := by
  unfold continuatorExpectedValue stagedContinuatorExpectedValue
  calc
    (∑ i : I.Cell future, (later.trans earlier).continuatorCredence F c i * a (I.outcome i)) =
        ∑ i : I.Cell future,
          (∑ j : I.Cell middle,
            earlier.continuatorCredence F c j * later.continuatorCredence F j i) * a (I.outcome i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [later.sum_intermediateCredence_mul_laterCredence_eq_composite F hinv hInjAll earlier c hc i]
    _ = ∑ j : I.Cell middle,
          earlier.continuatorCredence F c j *
            ∑ i : I.Cell future, later.continuatorCredence F j i * a (I.outcome i) := by
          calc
            (∑ i : I.Cell future,
              (∑ j : I.Cell middle,
                earlier.continuatorCredence F c j * later.continuatorCredence F j i) * a (I.outcome i)) =
                ∑ i : I.Cell future, ∑ j : I.Cell middle,
                  (earlier.continuatorCredence F c j * later.continuatorCredence F j i) * a (I.outcome i) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    rw [Finset.sum_mul]
            _ = ∑ j : I.Cell middle, ∑ i : I.Cell future,
                  (earlier.continuatorCredence F c j * later.continuatorCredence F j i) * a (I.outcome i) := by
                    rw [Finset.sum_comm]
            _ = _ := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring

/-- Tower property specialized to the unit-payoff indicator of one future
cell. -/
theorem continuatorExpectedValue_indicator_tower
    (F : RationalExpectationFamily I)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {future middle present : I.Perspective}
    (later : ContinuationStep I future middle)
    (earlier : ContinuationStep I middle present)
    (c : I.Cell present)
    (hc : canonicalWeight F present c ≠ 0)
    (i : I.Cell future) :
    (later.trans earlier).continuatorExpectedValue F c (Act.indicator (I.outcome i)) =
      stagedContinuatorExpectedValue F later earlier c (Act.indicator (I.outcome i)) := by
  exact continuatorExpectedValue_tower F hinv hInjAll later earlier c hc
    (Act.indicator (I.outcome i))

end ContinuationStep

namespace RecordCredenceFamily

/-- Two-stage expected value computed with an abstract credence family. -/
def stagedCredenceExpectedFutureValue
    (C : RecordCredenceFamily I)
    {future middle present : I.Perspective}
    (later : ContinuationStep I future middle)
    (earlier : ContinuationStep I middle present)
    (c : I.Cell present)
    (a : Act I) : ℝ :=
  ∑ j : I.Cell middle,
    C.credence middle (earlier.continuatorCells c) j * C.credenceExpectedFutureValue later j a

/-- Every admissible credence family gives the canonical two-stage conditional
value. -/
theorem stagedCredenceExpectedFutureValue_eq_stagedContinuatorExpectedValue
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I)
    (hnorm : C.NormalizedOnNonzeroMass F)
    (hdecision : C.RepresentsUnrestrictedDecisionValue F)
    (hodds : C.OddsInvariantUnderRecordRestriction F)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {future middle present : I.Perspective}
    (later : ContinuationStep I future middle)
    (earlier : ContinuationStep I middle present)
    (c : I.Cell present)
    (hc : canonicalWeight F present c ≠ 0)
    (a : Act I) :
    C.stagedCredenceExpectedFutureValue later earlier c a =
      ContinuationStep.stagedContinuatorExpectedValue F later earlier c a := by
  unfold stagedCredenceExpectedFutureValue ContinuationStep.stagedContinuatorExpectedValue
  apply Finset.sum_congr rfl
  intro j hj_mem
  rw [C.credence_on_continuators_eq F hnorm hdecision hodds hinv hInjAll earlier c hc j]
  by_cases hj : canonicalWeight F middle j = 0
  · have hzero :
        recordConditionedCredence F middle (earlier.continuatorCells c) j = 0 := by
      exact earlier.continuatorCredence_eq_zero_of_futureWeight_eq_zero F hinv hInjAll c j hj
    simp [hzero]
  · rw [C.credenceExpectedFutureValue_eq_continuatorExpectedValue
      F hnorm hdecision hodds hinv hInjAll later j hj a]

/-- Tower property for every admissible record credence family. -/
theorem credenceExpectedFutureValue_tower
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I)
    (hnorm : C.NormalizedOnNonzeroMass F)
    (hdecision : C.RepresentsUnrestrictedDecisionValue F)
    (hodds : C.OddsInvariantUnderRecordRestriction F)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {future middle present : I.Perspective}
    (later : ContinuationStep I future middle)
    (earlier : ContinuationStep I middle present)
    (c : I.Cell present)
    (hc : canonicalWeight F present c ≠ 0)
    (a : Act I) :
    C.credenceExpectedFutureValue (later.trans earlier) c a =
      C.stagedCredenceExpectedFutureValue later earlier c a := by
  calc
    C.credenceExpectedFutureValue (later.trans earlier) c a =
        (later.trans earlier).continuatorExpectedValue F c a := by
          exact C.credenceExpectedFutureValue_eq_continuatorExpectedValue
            F hnorm hdecision hodds hinv hInjAll (later.trans earlier) c hc a
    _ = ContinuationStep.stagedContinuatorExpectedValue F later earlier c a := by
          exact ContinuationStep.continuatorExpectedValue_tower F hinv hInjAll later earlier c hc a
    _ = C.stagedCredenceExpectedFutureValue later earlier c a := by
          symm
          exact C.stagedCredenceExpectedFutureValue_eq_stagedContinuatorExpectedValue
            F hnorm hdecision hodds hinv hInjAll later earlier c hc a

/-- The global value of a future act can be reconstructed by present weights,
intermediate credences, and future conditional values. -/
theorem futureDecisionValue_eq_sum_presentWeight_mul_stagedCredenceExpectedFutureValue
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I)
    (hnorm : C.NormalizedOnNonzeroMass F)
    (hdecision : C.RepresentsUnrestrictedDecisionValue F)
    (hodds : C.OddsInvariantUnderRecordRestriction F)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {future middle present : I.Perspective}
    (later : ContinuationStep I future middle)
    (earlier : ContinuationStep I middle present)
    (a : Act I) :
    F.V future a =
      ∑ c : I.Cell present,
        canonicalWeight F present c * C.stagedCredenceExpectedFutureValue later earlier c a := by
  rw [C.futureDecisionValue_eq_sum_presentWeight_mul_credenceExpectedFutureValue
    F hnorm hdecision hodds hinv hInjAll (later.trans earlier) a]
  apply Finset.sum_congr rfl
  intro c hc_mem
  by_cases hc : canonicalWeight F present c = 0
  · simp [hc]
  · rw [C.credenceExpectedFutureValue_tower
      F hnorm hdecision hodds hinv hInjAll later earlier c hc a]

end RecordCredenceFamily

end
end EverettianProbability.Abstract
