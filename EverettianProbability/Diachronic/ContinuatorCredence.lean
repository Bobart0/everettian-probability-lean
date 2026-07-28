import EverettianProbability.SelfLocation.DecisionCredenceBridge

/-!
**FR.** # Crédence envers les continuateurs futurs

Ce module ouvre la composante véritablement diachronique du programme. Une
`ContinuationStep` distingue explicitement une perspective présente et une
perspective future ; son raffinement associe à chaque cellule future sa cellule
parente présente.

Les continuateurs d'une cellule présente sont les cellules futures de cette
fibre. Leur crédence est la crédence auto-localisante conditionnée par
l'information d'appartenir à cette fibre. Le module établit son accord avec le
poids conditionnel, sa normalisation lorsque le poids présent est non nul, et
sa cohérence à travers plusieurs étapes de continuation.

La lecture en termes de continuateurs est un pont sémantique et diachronique.
Une `ContinuationStep` n'est pas identifiée à une évolution unitaire
physiquement réalisable, et aucune théorie complète de l'identité personnelle
n'est introduite.

**EN.** # Credence over future continuators

This module opens the genuinely diachronic component of the program. A
`ContinuationStep` explicitly distinguishes a present perspective from a
future perspective; its refinement maps every future cell to its present
parent cell.

The continuators of a present cell are the future cells in that fibre. Their
credence is self-locating credence conditioned on belonging to the fibre. The
module proves its agreement with conditional weight, its normalization when
the present weight is nonzero, and its coherence through multiple continuation
steps.

The continuator interpretation is a semantic and diachronic bridge. A
`ContinuationStep` is not identified with a physically realizable unitary
evolution, and no complete theory of personal identity is introduced.
-/

namespace EverettianProbability.Abstract

open scoped BigOperators Classical

noncomputable section

variable {I : PerspectiveInterface}

/-- A temporally oriented refinement from a future perspective to a present
perspective. -/
structure ContinuationStep
    (I : PerspectiveInterface)
    (future present : I.Perspective) where
  refinement :
    I.Refinement future present

namespace ContinuationStep

/-- Composition of a later continuation step with an earlier one. -/
def trans
    {future middle present : I.Perspective}
    (later :
      ContinuationStep I future middle)
    (earlier :
      ContinuationStep I middle present) :
    ContinuationStep I future present where
  refinement :=
    I.trans later.refinement earlier.refinement

@[simp]
theorem trans_refinement
    {future middle present : I.Perspective}
    (later :
      ContinuationStep I future middle)
    (earlier :
      ContinuationStep I middle present) :
    (later.trans earlier).refinement =
      I.trans later.refinement earlier.refinement := by
  rfl

/-- Future cells continuing a given present cell. -/
def continuatorCells
    {future present : I.Perspective}
    (step :
      ContinuationStep I future present)
    (c : I.Cell present) :
    Finset (I.Cell future) :=
  pullbackRecordCells step.refinement {c}

@[simp]
theorem mem_continuatorCells
    {future present : I.Perspective}
    (step :
      ContinuationStep I future present)
    (c : I.Cell present)
    (i : I.Cell future) :
    i ∈ step.continuatorCells c ↔
      I.parentCell step.refinement i = c := by
  simp [continuatorCells]

/-- Direct continuators through a composite step are exactly the pullback of
the intermediate continuator set through the later step. -/
theorem continuatorCells_trans
    {future middle present : I.Perspective}
    (later :
      ContinuationStep I future middle)
    (earlier :
      ContinuationStep I middle present)
    (c : I.Cell present) :
    (later.trans earlier).continuatorCells c =
      pullbackRecordCells
        later.refinement
        (earlier.continuatorCells c) := by
  ext i
  simp [continuatorCells, trans, I.parentCell_trans]

/-- Candidate credence of a future continuator, conditioned on its descending
from the present cell `c`. -/
def continuatorCredence
    (F : RationalExpectationFamily I)
    {future present : I.Perspective}
    (step :
      ContinuationStep I future present)
    (c : I.Cell present)
    (i : I.Cell future) : ℝ :=
  recordConditionedCredence
    F
    future
    (step.continuatorCells c)
    i

@[simp]
theorem continuatorCredence_def
    (F : RationalExpectationFamily I)
    {future present : I.Perspective}
    (step :
      ContinuationStep I future present)
    (c : I.Cell present)
    (i : I.Cell future) :
    step.continuatorCredence F c i =
      recordConditionedCredence
        F future
        (step.continuatorCells c)
        i := by
  rfl

/-- The total canonical mass of the future continuators of `c` equals the
canonical weight of `c` at the present perspective. -/
theorem continuatorMass_eq_presentWeight
    (F : RationalExpectationFamily I)
    (hinv :
      RefinementInvariantLocal F.V)
    (hInjAll :
      ∀ D : I.Perspective,
        Function.Injective (@I.outcome D))
    {future present : I.Perspective}
    (step :
      ContinuationStep I future present)
    (c : I.Cell present) :
    recordCompatibleMass
        F future
        (step.continuatorCells c) =
      canonicalWeight F present c := by
  unfold continuatorCells
  rw [recordCompatibleMass_pullback F hinv hInjAll step.refinement
    ({c} : Finset (I.Cell present))]
  simp [recordCompatibleMass]

/-- Continuator credence agrees with the canonical conditional weight on the
future fibre of a present cell. -/
theorem continuatorCredence_eq_conditionalWeight
    (F : RationalExpectationFamily I)
    (hinv :
      RefinementInvariantLocal F.V)
    (hInjAll :
      ∀ D : I.Perspective,
        Function.Injective (@I.outcome D))
    {future present : I.Perspective}
    (step :
      ContinuationStep I future present)
    (c : I.Cell present)
    (hc :
      canonicalWeight F present c ≠ 0)
    (i : I.Cell future) :
    step.continuatorCredence F c i =
      conditionalWeight
        F step.refinement c i := by
  have hmass :
      recordCompatibleMass
          F future
          (step.continuatorCells c) ≠ 0 := by
    rw [step.continuatorMass_eq_presentWeight F hinv hInjAll c]
    exact hc
  unfold continuatorCredence recordConditionedCredence conditionalWeight
  rw [if_neg hmass, if_neg hc]
  by_cases hi : I.parentCell step.refinement i = c
  · have himem : i ∈ step.continuatorCells c := by
      simp [hi]
    rw [if_pos himem, if_pos hi]
    rw [step.continuatorMass_eq_presentWeight F hinv hInjAll c]
  · have hinotmem : i ∉ step.continuatorCells c := by
      simp [hi]
    rw [if_neg hinotmem, if_neg hi]

theorem continuatorCredence_nonneg
    (F : RationalExpectationFamily I)
    {future present : I.Perspective}
    (step :
      ContinuationStep I future present)
    (c : I.Cell present)
    (i : I.Cell future) :
    0 ≤ step.continuatorCredence F c i := by
  exact
    recordConditionedCredence_nonneg
      F future (step.continuatorCells c) i

/-- Credence over all future continuators of a nonzero-weight present cell is
normalized. -/
theorem sum_continuatorCredence_eq_one
    (F : RationalExpectationFamily I)
    (hinv :
      RefinementInvariantLocal F.V)
    (hInjAll :
      ∀ D : I.Perspective,
        Function.Injective (@I.outcome D))
    {future present : I.Perspective}
    (step :
      ContinuationStep I future present)
    (c : I.Cell present)
    (hc :
      canonicalWeight F present c ≠ 0) :
    (∑ i : I.Cell future,
      step.continuatorCredence F c i) = 1 := by
  have hmass :
      recordCompatibleMass
          F future
          (step.continuatorCells c) ≠ 0 := by
    rw [step.continuatorMass_eq_presentWeight F hinv hInjAll c]
    exact hc
  exact
    recordConditionedCredence_normalized
      F future (step.continuatorCells c) hmass

/-- Diachronic fibre coherence: the credence assigned now to an intermediate
continuator equals the total credence now assigned to all of its later
continuators. -/
theorem continuatorCredence_trans_fiber
    (F : RationalExpectationFamily I)
    (hinv :
      RefinementInvariantLocal F.V)
    (hInjAll :
      ∀ D : I.Perspective,
        Function.Injective (@I.outcome D))
    {future middle present : I.Perspective}
    (later :
      ContinuationStep I future middle)
    (earlier :
      ContinuationStep I middle present)
    (c : I.Cell present)
    (j : I.Cell middle)
    (hc :
      canonicalWeight F present c ≠ 0) :
    earlier.continuatorCredence F c j =
      ∑ i : I.Cell future,
        if I.parentCell later.refinement i = j then
          (later.trans earlier).continuatorCredence F c i
        else 0 := by
  rw [earlier.continuatorCredence_eq_conditionalWeight F hinv hInjAll c hc j]
  rw [conditionalWeight_trans_fiber F hinv hInjAll later.refinement
    earlier.refinement c j hc]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hparent : I.parentCell later.refinement i = j
  · rw [if_pos hparent, if_pos hparent]
    symm
    exact
      (later.trans earlier).continuatorCredence_eq_conditionalWeight
        F hinv hInjAll c hc i
  · simp [hparent]

end ContinuationStep

namespace RecordCredenceFamily

/-- Any credence family satisfying the decision bridge, normalization, and
record-restriction odds invariance agrees with canonical continuator credence. -/
theorem credence_on_continuators_eq
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I)
    (hnorm :
      C.NormalizedOnNonzeroMass F)
    (hdecision :
      C.RepresentsUnrestrictedDecisionValue F)
    (hodds :
      C.OddsInvariantUnderRecordRestriction F)
    (hinv :
      RefinementInvariantLocal F.V)
    (hInjAll :
      ∀ D : I.Perspective,
        Function.Injective (@I.outcome D))
    {future present : I.Perspective}
    (step :
      ContinuationStep I future present)
    (c : I.Cell present)
    (hc :
      canonicalWeight F present c ≠ 0)
    (i : I.Cell future) :
    C.credence future (step.continuatorCells c) i =
      step.continuatorCredence F c i := by
  have hmass :
      recordCompatibleMass F future (step.continuatorCells c) ≠ 0 := by
    rw [step.continuatorMass_eq_presentWeight F hinv hInjAll c]
    exact hc
  exact
    C.credence_eq_recordConditionedCredence_of_normalized_of_decisionRepresentation_of_oddsInvariant
      F hnorm hdecision hodds hInjAll future
      (step.continuatorCells c) hmass i

/-- Every admissible credence family preserves total credence through
successive continuation steps. -/
theorem credence_on_continuators_trans_fiber
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I)
    (hnorm :
      C.NormalizedOnNonzeroMass F)
    (hdecision :
      C.RepresentsUnrestrictedDecisionValue F)
    (hodds :
      C.OddsInvariantUnderRecordRestriction F)
    (hinv :
      RefinementInvariantLocal F.V)
    (hInjAll :
      ∀ D : I.Perspective,
        Function.Injective (@I.outcome D))
    {future middle present : I.Perspective}
    (later :
      ContinuationStep I future middle)
    (earlier :
      ContinuationStep I middle present)
    (c : I.Cell present)
    (j : I.Cell middle)
    (hc :
      canonicalWeight F present c ≠ 0) :
    C.credence middle (earlier.continuatorCells c) j =
      ∑ i : I.Cell future,
        if I.parentCell later.refinement i = j then
          C.credence future ((later.trans earlier).continuatorCells c) i
        else 0 := by
  have hcoherent :
      C.RefinementCoherent F hinv hInjAll :=
    C.refinementCoherent_of_normalized_of_decisionRepresentation_of_oddsInvariant
      F hnorm hdecision hodds hinv hInjAll
  have hmass :
      recordCompatibleMass F middle (earlier.continuatorCells c) ≠ 0 := by
    rw [earlier.continuatorMass_eq_presentWeight F hinv hInjAll c]
    exact hc
  have h :=
    hcoherent later.refinement (earlier.continuatorCells c) j hmass
  rw [← later.continuatorCells_trans earlier c] at h
  exact h

end RecordCredenceFamily

end
end EverettianProbability.Abstract
