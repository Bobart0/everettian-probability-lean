import EverettianProbability.Core.AbstractAct

/-!
**FR.** # Famille d'espérance rationnelle, niveau abstrait

L'analogue de `Preference/ExpectationFunctional.lean` pour une interface
`PerspectiveInterface` quelconque `I`, plutôt que pour `Perspective n`
spécifiquement. Les trois axiomes (affinité, monotonie locale,
normalisation) sont énoncés mot pour mot, avec `Act I` à la place de
`Act n`. Instanciée en `I := Projective.interface n`, cette structure
recouvre exactement `Preference.RationalExpectationFamily n` ; instanciée en
`I := Effects.interface n`, elle donne l'objet dont a besoin la route
qubit (`EffectCalibration/`).

**EN.** # Rational expectation family, abstract level

The analogue of `Preference/ExpectationFunctional.lean` for an arbitrary
`PerspectiveInterface` `I`, rather than specifically `Perspective n`. The
three axioms (affinity, local monotonicity, normalization) are stated
verbatim, with `Act I` in place of `Act n`. Instantiated at
`I := Projective.interface n`, this structure exactly recovers
`Preference.RationalExpectationFamily n`; instantiated at
`I := Effects.interface n`, it gives the object the qubit route
(`EffectCalibration/`) needs.
-/

namespace EverettianProbability.Abstract

variable {I : PerspectiveInterface}

/-- Abstract rational expectation family: affine, monotone, normalized on
constants, over an arbitrary `PerspectiveInterface`. -/
structure RationalExpectationFamily (I : PerspectiveInterface) where
  /-- The expectation functional itself. -/
  V : (D : I.Perspective) → Act I → ℝ
  /-- Affinity: the expectation of an affine combination of two acts is the
  affine combination of their expectations. -/
  affine : ∀ (D : I.Perspective) (t : ℝ) (a b : Act I),
    V D (fun o => t * a o + (1 - t) * b o) = t * V D a + (1 - t) * V D b
  /-- Monotonicity, on the cells of the relevant perspective. -/
  monotone : ∀ (D : I.Perspective) (a b : Act I),
    (∀ c : I.Cell D, a (I.outcome c) ≤ b (I.outcome c)) → V D a ≤ V D b
  /-- Normalization: the expectation of a certain payoff is that payoff. -/
  normalized_const : ∀ (D : I.Perspective) (k : ℝ), V D (Act.const k) = k

/-- **FR.** La monotonie locale force la fonctionnelle à ne dépendre que des
valeurs de l'acte sur les cellules de la perspective.

**EN.** Local monotonicity forces the functional to depend only on the
act's values on the cells of the perspective. -/
theorem V_congr_of_agreeOn (F : RationalExpectationFamily I) (D : I.Perspective)
    {a b : Act I} (h : AgreeOn I D a b) : F.V D a = F.V D b := by
  apply le_antisymm
  · exact F.monotone D a b fun c => (h c).le
  · exact F.monotone D b a fun c => (h c).ge

end EverettianProbability.Abstract
