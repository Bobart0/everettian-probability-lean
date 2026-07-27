import EverettianProbability.Core.Interface

/-!
**FR.** # Actes abstraits

L'analogue, au niveau de `PerspectiveInterface`, de `Core/Act.lean` : l'acte
constant, l'indicatrice d'une sortie, et l'expansion finie d'un acte en
indicatrices — le tout paramétré par une interface `I` quelconque plutôt que
par `Perspective n`. `AgreeOn` existe déjà dans `Core/Interface.lean` ; ce
fichier fournit les opérations et l'algèbre qui en dépendent.

Le lemme `agreeOn_indicatorExpansion` est l'endroit précis où l'injectivité
de `I.outcome` sur les cellules de `D` entre en jeu : sans elle, deux
cellules distinctes pourraient partager la même sortie, et aucun acte ne
pourrait alors les séparer — l'argument « l'indicatrice isole un seul
terme » s'effondrerait. C'est exactement le diagnostic qui autorise la
levée de `represents`/`refinement_invariant_implies_grain` au niveau
abstrait (voir `Preference/AbstractRepresentation.lean`,
`BornCalibration/AbstractRefinementImpliesGrain.lean`) : l'hypothèse est
passée en argument à chaque théorème qui en a besoin, jamais ajoutée comme
champ de `PerspectiveInterface` — cela casserait les instances projective et
effets déjà validées par P0.3.

**EN.** # Abstract acts

The `PerspectiveInterface`-level analogue of `Core/Act.lean`: the constant
act, the indicator of an outcome, and the finite indicator expansion of an
act — all parametrized by an arbitrary interface `I` rather than by
`Perspective n`. `AgreeOn` already exists in `Core/Interface.lean`; this
file supplies the operations and algebra that build on it.

`agreeOn_indicatorExpansion` is the precise place where injectivity of
`I.outcome` on `D`'s cells enters: without it, two distinct cells could
share the same outcome, and no act could then separate them — the
"indicator isolates a single term" argument would collapse. This is
exactly the diagnostic that licenses lifting `represents`/
`refinement_invariant_implies_grain` to the abstract level (see
`Preference/AbstractRepresentation.lean`,
`BornCalibration/AbstractRefinementImpliesGrain.lean`): the hypothesis is
passed as an argument to every theorem that needs it, never added as a
field of `PerspectiveInterface` — that would break the already-validated
projective and effect instances (P0.3).
-/

namespace EverettianProbability.Abstract

open scoped BigOperators Classical

variable {I : PerspectiveInterface}

namespace Act

/-- The constant act. -/
noncomputable def const (k : ℝ) : Act I := fun _ => k

/-- The indicator of a single outcome. -/
noncomputable def indicator (o₀ : I.Outcome) : Act I := fun o => if o = o₀ then 1 else 0

/-- Expansion of an act in the indicators of a perspective's cells. -/
noncomputable def indicatorExpansion (D : I.Perspective) (a : Act I) : Act I :=
  letI := I.cellFintype D
  fun o => ∑ c : I.Cell D, a (I.outcome c) * indicator (I.outcome c) o

theorem agreeOn_refl (D : I.Perspective) (a : Act I) : AgreeOn I D a a := fun _ => rfl

theorem agreeOn_symm {D : I.Perspective} {a b : Act I} (h : AgreeOn I D a b) : AgreeOn I D b a :=
  fun c => (h c).symm

theorem agreeOn_trans {D : I.Perspective} {a b d : Act I}
    (hab : AgreeOn I D a b) (hbd : AgreeOn I D b d) : AgreeOn I D a d :=
  fun c => (hab c).trans (hbd c)

@[simp] theorem indicator_self (o₀ : I.Outcome) : indicator (I := I) o₀ o₀ = 1 := by
  unfold indicator; simp

theorem indicator_of_ne {o o₀ : I.Outcome} (h : o ≠ o₀) : indicator (I := I) o₀ o = 0 := by
  unfold indicator; simp [h]

/-- **FR.** Le point d'entrée de l'injectivité : sur une perspective `D` où
`outcome` est injective sur les cellules, tout acte coïncide avec son
expansion finie en indicatrices.

**EN.** The entry point for injectivity: on a perspective `D` where
`outcome` is injective on the cells, every act agrees with its finite
indicator expansion. -/
theorem agreeOn_indicatorExpansion (D : I.Perspective)
    (hInj : Function.Injective (@I.outcome D)) (a : Act I) :
    AgreeOn I D a (indicatorExpansion D a) := by
  letI := I.cellFintype D
  letI := I.cellDecidableEq D
  intro c
  unfold indicatorExpansion
  rw [Finset.sum_eq_single c]
  · rw [indicator_self, mul_one]
  · intro d _ hdc
    rw [indicator_of_ne (fun h => hdc (hInj h).symm), mul_zero]
  · exact fun h => (h (Finset.mem_univ c)).elim

end Act
end EverettianProbability.Abstract
