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

/-- **FR.** L'évaluation conditionnelle du tiré-en-arrière d'un acte grossier
est la conséquence de sa cellule conditionnante lorsque le poids de celle-ci
est non nul. Portée : aucun temps ni aucune dynamique ne sont formalisés ; un
raffinement ne reçoit qu'une lecture diachronique interprétative.

**EN.** Conditional evaluation of a coarse act's pullback is the consequence
of its conditioning cell when that cell's weight is nonzero. Scope: no time
or dynamics is formalized; a refinement receives only an interpretive
diachronic reading. -/
theorem conditionalExpectation_pullback_eq_of_weight_ne_zero
    (F : RationalExpectationFamily I)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {fine coarse : I.Perspective} (r : I.Refinement fine coarse)
    (c : I.Cell coarse) (a : Act I)
    (hc : canonicalWeight F coarse c ≠ 0) :
    conditionalExpectation F r c (pullbackAct I r a) =
      a (I.outcome c) := by
  unfold conditionalExpectation
  calc
    ∑ i : I.Cell fine,
        conditionalWeight F r c i * (pullbackAct I r a) (I.outcome i) =
        ∑ i : I.Cell fine,
          conditionalWeight F r c i * a (I.outcome (I.parentCell r i)) := by
            apply Finset.sum_congr rfl
            intro i _
            unfold pullbackAct
            rw [Function.comp_apply, I.parentOutcome_cell]
    _ = ∑ i : I.Cell fine,
          conditionalWeight F r c i * a (I.outcome c) := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : I.parentCell r i = c
            · rw [hi]
            · rw [conditionalWeight_zero_of_not_in_fiber F r c i hi]
              simp
    _ = (∑ i : I.Cell fine, conditionalWeight F r c i) * a (I.outcome c) := by
            rw [Finset.sum_mul]
    _ = a (I.outcome c) := by
            rw [conditionalWeight_normalized F hinv hInjAll r c hc, one_mul]

/-- **FR.** Loi de totalité : l'évaluation grossière est la somme des
évaluations conditionnelles des tirés-en-arrière, pondérées par les poids
canoniques grossiers. Portée : aucun temps ni aucune dynamique ne sont
formalisés ; un raffinement ne reçoit qu'une lecture diachronique
interprétative.

**EN.** Totality law: coarse evaluation is the sum of conditional evaluations
of pullbacks, weighted by coarse canonical weights. Scope: no time or
dynamics is formalized; a refinement receives only an interpretive diachronic
reading. -/
theorem conditionalExpectation_total
    (F : RationalExpectationFamily I)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {fine coarse : I.Perspective} (r : I.Refinement fine coarse)
    (a : Act I) :
    F.V coarse a =
      ∑ c : I.Cell coarse,
        canonicalWeight F coarse c *
          conditionalExpectation F r c (pullbackAct I r a) := by
  rw [represents F coarse (hInjAll coarse) a]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : canonicalWeight F coarse c = 0
  · simp only [hc, zero_mul]
  · rw [conditionalExpectation_pullback_eq_of_weight_ne_zero
      F hinv hInjAll r c a hc]

end EverettianProbability.Abstract
