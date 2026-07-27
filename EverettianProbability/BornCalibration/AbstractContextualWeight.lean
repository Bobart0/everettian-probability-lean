import EverettianProbability.Preference.AbstractExpectationFunctional

/-!
**FR.** # Poids contextuel canonique, niveau abstrait

L'analogue de `BornCalibration/ContextualWeight.lean` : la valeur de l'acte
indicateur, cette fois évaluée à la sortie d'une cellule abstraite. Aucun
`if c ∈ D.cells then ... else 0` n'est nécessaire ici, à la différence du
cas concret : `c : I.Cell D` porte déjà, par son type, l'appartenance à `D`
— une simplification que permet la dépendance de `Cell` envers
`Perspective` dans `PerspectiveInterface`.

**EN.** # Canonical contextual weight, abstract level

The analogue of `BornCalibration/ContextualWeight.lean`: the value of the
indicator act, now evaluated at an abstract cell's outcome. No
`if c ∈ D.cells then ... else 0` is needed here, unlike the concrete case:
`c : I.Cell D` already carries membership in `D` through its type — a
simplification enabled by `Cell`'s dependency on `Perspective` in
`PerspectiveInterface`.
-/

namespace EverettianProbability.Abstract

variable {I : PerspectiveInterface}

/-- Canonical weight: the value of the indicator act at a cell's outcome. -/
noncomputable def canonicalWeight (F : RationalExpectationFamily I) (D : I.Perspective)
    (c : I.Cell D) : ℝ :=
  F.V D (Act.indicator (I.outcome c))

end EverettianProbability.Abstract
