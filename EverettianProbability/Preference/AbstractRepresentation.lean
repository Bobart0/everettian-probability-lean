import EverettianProbability.BornCalibration.AbstractContextualWeight

/-!
**FR.** # Théorème de représentation, niveau abstrait

L'analogue de `Preference/Representation.lean`. Deux différences avec le
cas concret, toutes deux dues au découplage `Cell`/`Outcome` de
`PerspectiveInterface` :

1. La somme porte sur `I.Cell D` (un `Fintype`), pas sur un `Finset` de
   sorties : il n'y a pas, au niveau abstrait, de « `D.cells` comme
   sous-ensemble de `Outcome` ».
2. `represents` et `canonicalWeight_axNorm` prennent en argument
   `hInj : Function.Injective (@I.outcome D)`. Sans elle, deux cellules
   distinctes pourraient partager la même sortie et l'argument
   d'expansion en indicatrices ne séparerait plus rien — voir
   `Core/AbstractAct.lean`. Les deux instances concrètes (projective :
   `Subtype.val_injective`, effets : `Fin.val_injective`) la satisfont
   trivialement.

`weights_unique_on_cells` et `canonicalWeight_axPos`, en revanche, n'ont pas
besoin de cette hypothèse : la première isole une cellule directement dans
l'hypothèse `hp` (déjà cellule-indexée), la seconde ne fait appel qu'à la
monotonie.

**EN.** # Representation theorem, abstract level

The analogue of `Preference/Representation.lean`. Two differences from the
concrete case, both stemming from `PerspectiveInterface`'s `Cell`/`Outcome`
decoupling:

1. The sum ranges over `I.Cell D` (a `Fintype`), not over a `Finset` of
   outcomes: there is no abstract-level notion of "`D.cells` as a subset of
   `Outcome`".
2. `represents` and `canonicalWeight_axNorm` take
   `hInj : Function.Injective (@I.outcome D)` as an argument. Without it,
   two distinct cells could share the same outcome and the indicator-
   expansion argument would separate nothing — see `Core/AbstractAct.lean`.
   Both concrete instances (projective: `Subtype.val_injective`; effects:
   `Fin.val_injective`) satisfy it trivially.

`weights_unique_on_cells` and `canonicalWeight_axPos`, by contrast, do not
need this hypothesis: the former isolates a cell directly from the
(already cell-indexed) hypothesis `hp`, the latter only invokes
monotonicity.
-/

namespace EverettianProbability.Abstract

open scoped BigOperators Classical

variable {I : PerspectiveInterface}

private theorem V_zero (F : RationalExpectationFamily I) (D : I.Perspective) :
    F.V D (Act.const 0) = 0 :=
  F.normalized_const D 0

private theorem V_smul (F : RationalExpectationFamily I) (D : I.Perspective)
    (t : ℝ) (a : Act I) :
    F.V D (fun o => t * a o) = t * F.V D a := by
  have h := F.affine D t a (Act.const 0)
  rw [F.normalized_const D 0] at h
  simpa only [Act.const, mul_zero, add_zero] using h

private theorem V_add (F : RationalExpectationFamily I) (D : I.Perspective)
    (a b : Act I) :
    F.V D (fun o => a o + b o) = F.V D a + F.V D b := by
  calc
    F.V D (fun o => a o + b o) =
        F.V D (fun o => (1 / 2 : ℝ) * (2 * a o) + (1 - (1 / 2 : ℝ)) * (2 * b o)) := by
          congr 1
          funext o
          ring
    _ = (1 / 2 : ℝ) * F.V D (fun o => 2 * a o) +
        (1 - (1 / 2 : ℝ)) * F.V D (fun o => 2 * b o) :=
      F.affine D (1 / 2 : ℝ) (fun o => 2 * a o) (fun o => 2 * b o)
    _ = F.V D a + F.V D b := by
      rw [V_smul F D 2 a, V_smul F D 2 b]
      ring

private theorem V_sum {ι : Type*} (F : RationalExpectationFamily I)
    (D : I.Perspective) (s : Finset ι) (f : ι → Act I) :
    F.V D (fun o => s.sum fun i => f i o) = s.sum fun i => F.V D (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change F.V D (Act.const 0) = 0
      exact V_zero F D
  | @insert i s hi ih =>
      calc
        F.V D (fun o => (insert i s).sum fun j => f j o) =
            F.V D (fun o => f i o + s.sum fun j => f j o) := by
          congr 1
          funext o
          rw [Finset.sum_insert hi]
        _ = F.V D (f i) + F.V D (fun o => s.sum fun j => f j o) :=
          V_add F D (f i) (fun o => s.sum fun j => f j o)
        _ = F.V D (f i) + s.sum fun j => F.V D (f j) := by rw [ih]
        _ = (insert i s).sum fun j => F.V D (f j) := by
          rw [Finset.sum_insert hi]

/-- **FR.** Toute fonctionnelle rationnelle est la somme finie pondérée par
son poids canonique sur les cellules de la perspective. Nécessite `outcome`
injective sur `D`.

**EN.** Every rational functional is the finite sum weighted by its
canonical weight on the perspective's cells. Needs `outcome` injective
on `D`. -/
theorem represents (F : RationalExpectationFamily I) (D : I.Perspective)
    (hInj : Function.Injective (@I.outcome D)) (a : Act I) :
    letI := I.cellFintype D
    F.V D a = ∑ c : I.Cell D, canonicalWeight F D c * a (I.outcome c) := by
  letI := I.cellFintype D
  letI := I.cellDecidableEq D
  calc
    F.V D a = F.V D (Act.indicatorExpansion D a) :=
      V_congr_of_agreeOn F D (Act.agreeOn_indicatorExpansion D hInj a)
    _ = F.V D (fun o => ∑ c : I.Cell D, (fun o' => a (I.outcome c) * Act.indicator (I.outcome c) o') o) := rfl
    _ = ∑ c : I.Cell D, F.V D (fun o' => a (I.outcome c) * Act.indicator (I.outcome c) o') :=
      V_sum F D Finset.univ (fun c o' => a (I.outcome c) * Act.indicator (I.outcome c) o')
    _ = ∑ c : I.Cell D, a (I.outcome c) * F.V D (Act.indicator (I.outcome c)) := by
      apply Finset.sum_congr rfl
      intro c _
      exact V_smul F D (a (I.outcome c)) (Act.indicator (I.outcome c))
    _ = ∑ c : I.Cell D, canonicalWeight F D c * a (I.outcome c) := by
      apply Finset.sum_congr rfl
      intro c _
      unfold canonicalWeight
      ring

/-- **FR.** Tout autre système représentant la fonctionnelle coïncide avec
le poids canonique sur les cellules.

**EN.** Every other system representing the functional agrees with the
canonical weight on the cells. -/
theorem weights_unique_on_cells (F : RationalExpectationFamily I) (D : I.Perspective)
    (hInj : Function.Injective (@I.outcome D)) (p : I.Cell D → ℝ)
    (hp : ∀ a : Act I, letI := I.cellFintype D
      F.V D a = ∑ c : I.Cell D, p c * a (I.outcome c)) :
    ∀ c : I.Cell D, p c = canonicalWeight F D c := by
  letI := I.cellFintype D
  letI := I.cellDecidableEq D
  intro c
  have h := hp (Act.indicator (I.outcome c))
  rw [Finset.sum_eq_single c] at h
  · simpa only [Act.indicator_self, mul_one, canonicalWeight] using h.symm
  · intro d _ hdc
    rw [Act.indicator_of_ne (fun hh => hdc (hInj hh)), mul_zero]
  · exact fun hnot => (hnot (Finset.mem_univ c)).elim

/-- **FR.** La positivité du poids canonique est dérivée de la monotonie
locale, sans hypothèse d'injectivité.

**EN.** Positivity of the canonical weight follows from local
monotonicity, with no injectivity hypothesis. -/
theorem canonicalWeight_axPos (F : RationalExpectationFamily I) (D : I.Perspective)
    (c : I.Cell D) : 0 ≤ canonicalWeight F D c := by
  unfold canonicalWeight
  rw [← F.normalized_const D 0]
  apply F.monotone D (Act.const 0) (Act.indicator (I.outcome c))
  intro d
  unfold Act.const Act.indicator
  split_ifs <;> norm_num

/-- **FR.** La normalisation du poids canonique découle de `represents`
appliqué à l'acte constant unitaire ; nécessite donc `outcome` injective.

**EN.** Normalization of the canonical weight follows from `represents`
applied to the unit constant act; hence needs `outcome` injective. -/
theorem canonicalWeight_axNorm (F : RationalExpectationFamily I) (D : I.Perspective)
    (hInj : Function.Injective (@I.outcome D)) :
    letI := I.cellFintype D
    ∑ c : I.Cell D, canonicalWeight F D c = 1 := by
  letI := I.cellFintype D
  have h := represents F D hInj (Act.const 1)
  rw [F.normalized_const D 1] at h
  simpa only [Act.const, mul_one] using h.symm

end EverettianProbability.Abstract
