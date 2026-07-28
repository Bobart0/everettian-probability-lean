import EverettianProbability.Diachronic.ContinuatorCredence

/-!
**FR.** # Actes futurs et loi diachronique de l'espérance totale

Ce module associe à chaque cellule présente une valeur conditionnelle d'un acte
futur, calculée avec les crédences envers ses continuateurs. Il établit que la
valeur globale future est la somme des poids présents multipliés par ces
valeurs conditionnelles futures.

Le même résultat est transporté à toute famille de crédences satisfaisant la
normalisation, le pont entre valeur décisionnelle et crédence, et l'invariance
des cotes sous restriction informationnelle. Le module relie ainsi valeur
rationnelle (`NORM`), crédence envers les continuateurs (`SEM`) et
décomposition additive par fibres (`MATH`).

Aucune évolution unitaire, identité personnelle complète ou dynamique physique
des records n'est encore formalisée.

**EN.** # Future acts and the diachronic law of total expectation

This module assigns to each present cell a conditional value of a future act,
computed with credences over its continuators. It proves that global future
value is the sum of present weights multiplied by these future conditional
values.

The same result is transported to every credence family satisfying
normalization, the decision-to-credence bridge, and odds invariance under
record restriction. The module thereby connects rational value (`NORM`),
credence over continuators (`SEM`), and additive decomposition over fibres
(`MATH`).

No unitary evolution, complete personal identity, or physical record dynamics
is yet formalized.
-/

namespace EverettianProbability.Abstract

open scoped BigOperators Classical

noncomputable section

variable {I : PerspectiveInterface}

namespace ContinuationStep

/-- Continuator credence agrees with conditional canonical weight, including
the zero-present-weight case. -/
theorem continuatorCredence_eq_conditionalWeight_total
    (F : RationalExpectationFamily I)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {future present : I.Perspective}
    (step : ContinuationStep I future present)
    (c : I.Cell present)
    (i : I.Cell future) :
    step.continuatorCredence F c i = conditionalWeight F step.refinement c i := by
  by_cases hc : canonicalWeight F present c = 0
  · have hmass :
        recordCompatibleMass F future (step.continuatorCells c) = 0 := by
      rw [step.continuatorMass_eq_presentWeight F hinv hInjAll c]
      exact hc
    unfold continuatorCredence recordConditionedCredence conditionalWeight
    simp [hmass, hc]
  · exact step.continuatorCredence_eq_conditionalWeight F hinv hInjAll c hc i

/-- Expected value of a future act among the continuators of a present cell. -/
def continuatorExpectedValue
    (F : RationalExpectationFamily I)
    {future present : I.Perspective}
    (step : ContinuationStep I future present)
    (c : I.Cell present)
    (a : Act I) : ℝ :=
  ∑ i : I.Cell future, step.continuatorCredence F c i * a (I.outcome i)

@[simp]
theorem continuatorExpectedValue_def
    (F : RationalExpectationFamily I)
    {future present : I.Perspective}
    (step : ContinuationStep I future present)
    (c : I.Cell present)
    (a : Act I) :
    step.continuatorExpectedValue F c a =
      ∑ i : I.Cell future, step.continuatorCredence F c i * a (I.outcome i) := by
  rfl

/-- The expected value computed with continuator credence is exactly the
existing conditional expectation on the continuation fibre. -/
theorem continuatorExpectedValue_eq_conditionalExpectation
    (F : RationalExpectationFamily I)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {future present : I.Perspective}
    (step : ContinuationStep I future present)
    (c : I.Cell present)
    (a : Act I) :
    step.continuatorExpectedValue F c a =
      conditionalExpectation F step.refinement c a := by
  unfold continuatorExpectedValue conditionalExpectation
  apply Finset.sum_congr rfl
  intro i hi
  rw [step.continuatorCredence_eq_conditionalWeight_total F hinv hInjAll c i]

/-- A constant future act has that same conditional value on every nonzero
weight present cell. -/
theorem continuatorExpectedValue_const
    (F : RationalExpectationFamily I)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {future present : I.Perspective}
    (step : ContinuationStep I future present)
    (c : I.Cell present)
    (hc : canonicalWeight F present c ≠ 0)
    (k : ℝ) :
    step.continuatorExpectedValue F c (Act.const k) = k := by
  unfold continuatorExpectedValue Act.const
  rw [← Finset.sum_mul]
  rw [step.sum_continuatorCredence_eq_one F hinv hInjAll c hc]
  simp

/-- The conditional value of a unit-payoff act for one future cell is the
credence assigned to that continuator. -/
theorem continuatorExpectedValue_indicator
    (F : RationalExpectationFamily I)
    {future present : I.Perspective}
    (step : ContinuationStep I future present)
    (c : I.Cell present)
    (hInj : Function.Injective (@I.outcome future))
    (i : I.Cell future) :
    step.continuatorExpectedValue F c (Act.indicator (I.outcome i)) =
      step.continuatorCredence F c i := by
  unfold continuatorExpectedValue
  rw [Finset.sum_eq_single i]
  · simp [Act.indicator_self]
  · intro j hj hji
    have houtcome : I.outcome j ≠ I.outcome i := fun h => hji (hInj h)
    simp [Act.indicator, houtcome]
  · exact fun hnot => (hnot (Finset.mem_univ i)).elim

private theorem canonicalWeight_eq_zero_of_parentWeight_eq_zero
    (F : RationalExpectationFamily I)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {fine coarse : I.Perspective}
    (r : I.Refinement fine coarse)
    (c : I.Cell coarse)
    (i : I.Cell fine)
    (hparent : I.parentCell r i = c)
    (hc : canonicalWeight F coarse c = 0) :
    canonicalWeight F fine i = 0 := by
  have hgrain := canonicalWeight_grain F hinv hInjAll r c
  have hsum :
      (∑ x : I.Cell fine,
        if I.parentCell r x = c then canonicalWeight F fine x else 0) = 0 := by
    rw [← hgrain, hc]
  have hnonneg : ∀ x ∈ (Finset.univ : Finset (I.Cell fine)),
      0 ≤ if I.parentCell r x = c then canonicalWeight F fine x else 0 := by
    intro x hx
    by_cases hxc : I.parentCell r x = c <;> simp [hxc, canonicalWeight_axPos]
  have hall : ∀ x ∈ (Finset.univ : Finset (I.Cell fine)),
      (if I.parentCell r x = c then canonicalWeight F fine x else 0) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
  have hi := hall i (Finset.mem_univ i)
  simpa [hparent] using hi

/-- Multiplying a conditional weight by its present parent weight recovers the
future weight on the fibre and zero outside it. -/
theorem canonicalWeight_mul_conditionalWeight
    (F : RationalExpectationFamily I)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {future present : I.Perspective}
    (step : ContinuationStep I future present)
    (c : I.Cell present)
    (i : I.Cell future) :
    canonicalWeight F present c * conditionalWeight F step.refinement c i =
      if I.parentCell step.refinement i = c then canonicalWeight F future i else 0 := by
  by_cases hc : canonicalWeight F present c = 0
  · have hleft : canonicalWeight F present c * conditionalWeight F step.refinement c i = 0 := by
      simp [hc]
    rw [hleft]
    by_cases hparent : I.parentCell step.refinement i = c
    · rw [if_pos hparent]
      symm
      exact canonicalWeight_eq_zero_of_parentWeight_eq_zero
        F hinv hInjAll step.refinement c i hparent hc
    · simp [hparent]
  · unfold conditionalWeight
    by_cases hparent : I.parentCell step.refinement i = c
    · simp only [hc, hparent, if_false, if_true]
      field_simp [hc]
    · simp [hc, hparent]

/-- Summing the present-weighted conditional weights over all present cells
reconstructs the future canonical weight. -/
theorem sum_presentWeight_mul_conditionalWeight_eq_futureWeight
    (F : RationalExpectationFamily I)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {future present : I.Perspective}
    (step : ContinuationStep I future present)
    (i : I.Cell future) :
    (∑ c : I.Cell present,
      canonicalWeight F present c * conditionalWeight F step.refinement c i) =
      canonicalWeight F future i := by
  calc
    (∑ c : I.Cell present,
      canonicalWeight F present c * conditionalWeight F step.refinement c i) =
        ∑ c : I.Cell present,
          if I.parentCell step.refinement i = c then canonicalWeight F future i else 0 := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [step.canonicalWeight_mul_conditionalWeight F hinv hInjAll c i]
    _ = ∑ c : I.Cell present,
          if c = I.parentCell step.refinement i then canonicalWeight F future i else 0 := by
          apply Finset.sum_congr rfl
          intro c hc
          by_cases hparent : I.parentCell step.refinement i = c
          · have hreverse : c = I.parentCell step.refinement i := hparent.symm
            rw [if_pos hparent, if_pos hreverse]
          · have hreverse : c ≠ I.parentCell step.refinement i :=
              fun h => hparent h.symm
            rw [if_neg hparent, if_neg hreverse]
    _ = canonicalWeight F future i := by
          rw [Finset.sum_ite_eq']
          simp

/-- Diachronic law of total expectation for future acts. -/
theorem futureDecisionValue_eq_sum_presentWeight_mul_continuatorExpectedValue
    (F : RationalExpectationFamily I)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {future present : I.Perspective}
    (step : ContinuationStep I future present)
    (a : Act I) :
    F.V future a =
      ∑ c : I.Cell present,
        canonicalWeight F present c * step.continuatorExpectedValue F c a := by
  rw [represents F future (hInjAll future) a]
  unfold continuatorExpectedValue
  calc
    (∑ i : I.Cell future, canonicalWeight F future i * a (I.outcome i)) =
        ∑ i : I.Cell future,
          (∑ c : I.Cell present,
            canonicalWeight F present c * conditionalWeight F step.refinement c i) *
              a (I.outcome i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [step.sum_presentWeight_mul_conditionalWeight_eq_futureWeight F hinv hInjAll i]
    _ = ∑ i : I.Cell future,
          ∑ c : I.Cell present,
            (canonicalWeight F present c * conditionalWeight F step.refinement c i) *
              a (I.outcome i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
    _ = ∑ c : I.Cell present,
          ∑ i : I.Cell future,
            (canonicalWeight F present c * conditionalWeight F step.refinement c i) *
              a (I.outcome i) := by
          rw [Finset.sum_comm]
    _ = ∑ c : I.Cell present,
          canonicalWeight F present c *
            ∑ i : I.Cell future,
              conditionalWeight F step.refinement c i * a (I.outcome i) := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = ∑ c : I.Cell present,
          canonicalWeight F present c *
            ∑ i : I.Cell future,
              step.continuatorCredence F c i * a (I.outcome i) := by
          apply Finset.sum_congr rfl
          intro c hc
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [step.continuatorCredence_eq_conditionalWeight_total F hinv hInjAll c i]

end ContinuationStep

namespace RecordCredenceFamily

/-- Conditional expected value of a future act computed with an abstract record
credence family. -/
def credenceExpectedFutureValue
    (C : RecordCredenceFamily I)
    {future present : I.Perspective}
    (step : ContinuationStep I future present)
    (c : I.Cell present)
    (a : Act I) : ℝ :=
  ∑ i : I.Cell future,
    C.credence future (step.continuatorCells c) i * a (I.outcome i)

/-- Every admissible credence family gives the canonical conditional value to
future acts on a nonzero-weight continuator fibre. -/
theorem credenceExpectedFutureValue_eq_continuatorExpectedValue
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I)
    (hnorm : C.NormalizedOnNonzeroMass F)
    (hdecision : C.RepresentsUnrestrictedDecisionValue F)
    (hodds : C.OddsInvariantUnderRecordRestriction F)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {future present : I.Perspective}
    (step : ContinuationStep I future present)
    (c : I.Cell present)
    (hc : canonicalWeight F present c ≠ 0)
    (a : Act I) :
    C.credenceExpectedFutureValue step c a = step.continuatorExpectedValue F c a := by
  unfold credenceExpectedFutureValue ContinuationStep.continuatorExpectedValue
  apply Finset.sum_congr rfl
  intro i hi
  rw [C.credence_on_continuators_eq F hnorm hdecision hodds hinv hInjAll step c hc i]

/-- Every admissible credence family yields the same diachronic law of total
expectation. -/
theorem futureDecisionValue_eq_sum_presentWeight_mul_credenceExpectedFutureValue
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I)
    (hnorm : C.NormalizedOnNonzeroMass F)
    (hdecision : C.RepresentsUnrestrictedDecisionValue F)
    (hodds : C.OddsInvariantUnderRecordRestriction F)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {future present : I.Perspective}
    (step : ContinuationStep I future present)
    (a : Act I) :
    F.V future a =
      ∑ c : I.Cell present,
        canonicalWeight F present c * C.credenceExpectedFutureValue step c a := by
  rw [step.futureDecisionValue_eq_sum_presentWeight_mul_continuatorExpectedValue
    F hinv hInjAll a]
  apply Finset.sum_congr rfl
  intro c hc_mem
  by_cases hc : canonicalWeight F present c = 0
  · simp [hc]
  · rw [C.credenceExpectedFutureValue_eq_continuatorExpectedValue
      F hnorm hdecision hodds hinv hInjAll step c hc a]

end RecordCredenceFamily

end
end EverettianProbability.Abstract
