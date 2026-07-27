import EverettianProbability.BornCalibration.AbstractRefinementImpliesGrain

/-!
**FR.** # Conditionnement sur les fibres de raffinement

Ce module formalise le conditionnement comme une renormalisation des poids
canoniques sur la fibre d'une cellule grossière. Il ne construit pas une
nouvelle perspective : `conditionalExpectation` est une somme finie sur les
cellules de la perspective fine existante.

**EN.** # Conditioning on refinement fibres

This module formalizes conditioning as a renormalization of canonical weights
on the fibre of a coarse cell. It constructs no new perspective:
`conditionalExpectation` is a finite sum over the cells of the existing fine
perspective.
-/

namespace EverettianProbability.Abstract

open scoped BigOperators Classical

variable {I : PerspectiveInterface}

/-- Conditional canonical weight on a refinement fibre. The definition is
total: it is zero when the conditioning weight is zero or when the fine cell
does not lie above the conditioning cell. -/
noncomputable def conditionalWeight (F : RationalExpectationFamily I)
    {fine coarse : I.Perspective} (r : I.Refinement fine coarse)
    (c : I.Cell coarse) (i : I.Cell fine) : ℝ :=
  if canonicalWeight F coarse c = 0 then 0
  else if I.parentCell r i = c then
    canonicalWeight F fine i / canonicalWeight F coarse c
  else 0

/-- Conditional evaluation of a total fine act, weighted by
`conditionalWeight` on the chosen fibre. -/
noncomputable def conditionalExpectation (F : RationalExpectationFamily I)
    {fine coarse : I.Perspective} (r : I.Refinement fine coarse)
    (c : I.Cell coarse) (a : Act I) : ℝ :=
  ∑ i : I.Cell fine, conditionalWeight F r c i * a (I.outcome i)

/-- **FR.** Le poids conditionnel est nul hors de la fibre de la cellule
conditionnante. Portée : aucun temps ni aucune dynamique ne sont formalisés ;
un raffinement ne reçoit qu'une lecture diachronique interprétative.

**EN.** The conditional weight vanishes outside the conditioning cell's
fibre. Scope: no time or dynamics is formalized; a refinement receives only
an interpretive diachronic reading. -/
theorem conditionalWeight_zero_of_not_in_fiber (F : RationalExpectationFamily I)
    {fine coarse : I.Perspective} (r : I.Refinement fine coarse)
    (c : I.Cell coarse) (i : I.Cell fine) (hi : I.parentCell r i ≠ c) :
    conditionalWeight F r c i = 0 := by
  unfold conditionalWeight
  split_ifs <;> simp_all

/-- **FR.** Les poids conditionnels sont positifs. Portée : aucun temps ni
aucune dynamique ne sont formalisés ; un raffinement ne reçoit qu'une lecture
diachronique interprétative.

**EN.** Conditional weights are nonnegative. Scope: no time or dynamics is
formalized; a refinement receives only an interpretive diachronic reading. -/
theorem conditionalWeight_nonneg (F : RationalExpectationFamily I)
    {fine coarse : I.Perspective} (r : I.Refinement fine coarse)
    (c : I.Cell coarse) (i : I.Cell fine) :
    0 ≤ conditionalWeight F r c i := by
  unfold conditionalWeight
  split_ifs with hweight hparent
  · exact le_rfl
  · apply div_nonneg
    · exact canonicalWeight_axPos F fine i
    · exact (lt_of_le_of_ne (canonicalWeight_axPos F coarse c) (Ne.symm hweight)).le
  · exact le_rfl

/-- **FR.** La masse totale du poids conditionnel est nulle lorsque le poids
conditionnant est nul, et égale à un sinon. Portée : aucun temps ni aucune
dynamique ne sont formalisés ; un raffinement ne reçoit qu'une lecture
diachronique interprétative.

**EN.** The conditional weight's total mass is zero when the conditioning
weight is zero and one otherwise. Scope: no time or dynamics is formalized;
a refinement receives only an interpretive diachronic reading. -/
theorem conditionalWeight_sum_eq_zero_or_one
    (F : RationalExpectationFamily I)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {fine coarse : I.Perspective} (r : I.Refinement fine coarse)
    (c : I.Cell coarse) :
    ∑ i : I.Cell fine, conditionalWeight F r c i =
      if canonicalWeight F coarse c = 0 then 0 else 1 := by
  by_cases hweight : canonicalWeight F coarse c = 0
  · simp only [conditionalWeight, hweight, ↓reduceIte, Finset.sum_const_zero]
  · rw [if_neg hweight]
    have hgrain := canonicalWeight_grain F hinv hInjAll r c
    calc
      ∑ i : I.Cell fine, conditionalWeight F r c i =
          ∑ i : I.Cell fine,
            if I.parentCell r i = c then
              canonicalWeight F fine i / canonicalWeight F coarse c
            else 0 := by
              apply Finset.sum_congr rfl
              intro i _
              simp only [conditionalWeight, hweight, ↓reduceIte]
      _ = (∑ i : I.Cell fine,
            if I.parentCell r i = c then canonicalWeight F fine i else 0) /
          canonicalWeight F coarse c := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : I.parentCell r i = c <;> simp [hi]
      _ = canonicalWeight F coarse c / canonicalWeight F coarse c := by
            rw [← hgrain]
      _ = 1 := div_self hweight

/-- **FR.** La normalisation usuelle est le cas où le poids conditionnant est
non nul. Portée : aucun temps ni aucune dynamique ne sont formalisés ; un
raffinement ne reçoit qu'une lecture diachronique interprétative.

**EN.** Ordinary normalization is the case of a nonzero conditioning weight.
Scope: no time or dynamics is formalized; a refinement receives only an
interpretive diachronic reading. -/
theorem conditionalWeight_normalized
    (F : RationalExpectationFamily I)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {fine coarse : I.Perspective} (r : I.Refinement fine coarse)
    (c : I.Cell coarse) (hc : canonicalWeight F coarse c ≠ 0) :
    ∑ i : I.Cell fine, conditionalWeight F r c i = 1 := by
  simpa only [if_neg hc] using
    conditionalWeight_sum_eq_zero_or_one F hinv hInjAll r c

end EverettianProbability.Abstract
