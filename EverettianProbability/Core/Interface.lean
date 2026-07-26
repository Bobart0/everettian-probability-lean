import QuantumFoundations.ProbabilityAPI

/-!
**FR.** # Interface abstraite des perspectives

Cette interface tranche la décision P0.3 en séparant trois niveaux : un
espace ambiant de conséquences, les cellules finies d'une perspective, et
une relation de raffinement munie d'une carte parent. Un acte reste toujours
une fonction **totale** sur l'espace ambiant. Le type dépendant `Cell D` ne
sert qu'à énumérer les cellules effectivement présentes dans `D`.

La cohérence `Grain` d'une règle d'estimation est formulée une fois, de même
que le tiré-en-arrière, l'invariance sous raffinement et la preuve abstraite
que l'espérance pondérée est invariante. Les instances projective et effets
montrent que cette interface couvre les deux routes amont sans identifier
leurs objets physiques.

**EN.** # Abstract perspective interface

This interface settles decision P0.3 by separating three levels: an ambient
consequence space, the finite cells of a perspective, and a refinement
relation equipped with a parent map. An act always remains a **total**
function on the ambient space. The dependent type `Cell D` is used only to
enumerate the cells actually present in `D`.

The `Grain` coherence of an estimation rule is stated once, as are pullback,
refinement invariance, and the abstract proof that weighted expectation is
invariant. The projective and effect instances show that the interface covers
both upstream routes without identifying their physical objects.
-/

namespace EverettianProbability.Abstract

open scoped BigOperators Classical

universe uP uO uC uR uE

/-- Common data needed by a finite perspective model. `parentOutcome` is
total so that pullback preserves the total-act convention; `parentCell`
records its meaningful restriction to the finite cells. -/
class PerspectiveInterface where
  Perspective : Type uP
  Outcome : Type uO
  Cell : Perspective → Type uC
  cellFintype : (D : Perspective) → Fintype (Cell D)
  cellDecidableEq : (D : Perspective) → DecidableEq (Cell D)
  outcome : {D : Perspective} → Cell D → Outcome
  Refinement : Perspective → Perspective → Sort uR
  parentOutcome : {fine coarse : Perspective} → Refinement fine coarse → Outcome → Outcome
  parentCell : {fine coarse : Perspective} → Refinement fine coarse → Cell fine → Cell coarse
  parentOutcome_cell : ∀ {fine coarse} (r : Refinement fine coarse) (c : Cell fine),
    parentOutcome r (outcome c) = outcome (parentCell r c)
  refl : (D : Perspective) → Refinement D D
  trans : ∀ {fine mid coarse}, Refinement fine mid → Refinement mid coarse →
    Refinement fine coarse
  parentCell_refl : ∀ (D : Perspective) (c : Cell D), parentCell (refl D) c = c
  parentCell_trans : ∀ {fine mid coarse} (r₁ : Refinement fine mid)
    (r₂ : Refinement mid coarse) (c : Cell fine),
    parentCell (trans r₁ r₂) c = parentCell r₂ (parentCell r₁ c)
  EstimationRule : Type uE
  weight : EstimationRule → (D : Perspective) → Cell D → ℝ

variable (I : PerspectiveInterface)

instance cellFintypeInstance (D : I.Perspective) : Fintype (I.Cell D) :=
  I.cellFintype D

instance cellDecidableEqInstance (D : I.Perspective) : DecidableEq (I.Cell D) :=
  I.cellDecidableEq D

/-- An abstract act is total on the model's ambient outcome space. -/
abbrev Act := I.Outcome → ℝ

/-- Two abstract acts agree on every cell of a perspective. -/
def AgreeOn (D : I.Perspective) (a b : Act I) : Prop :=
  ∀ c : I.Cell D, a (I.outcome c) = b (I.outcome c)

/-- Pull an act back along the total ambient parent map. -/
def pullbackAct {fine coarse : I.Perspective}
    (r : I.Refinement fine coarse) (a : Act I) : Act I :=
  a ∘ I.parentOutcome r

/-- Abstract pullback by reflexivity is the identity on the cells of the
perspective. Values away from those cells remain deliberately unspecified. -/
theorem pullbackAct_refl_agree (D : I.Perspective) (a : Act I) :
    AgreeOn I D (pullbackAct I (I.refl D) a) a := by
  intro c
  unfold pullbackAct
  rw [Function.comp_apply, I.parentOutcome_cell, I.parentCell_refl]

/-- Abstract pullback respects composition on all cells of the finest
perspective. -/
theorem pullbackAct_trans_agree {fine mid coarse : I.Perspective}
    (r₁ : I.Refinement fine mid) (r₂ : I.Refinement mid coarse) (a : Act I) :
    AgreeOn I fine (pullbackAct I (I.trans r₁ r₂) a)
      (pullbackAct I r₁ (pullbackAct I r₂ a)) := by
  intro c
  unfold pullbackAct
  rw [Function.comp_apply, Function.comp_apply, Function.comp_apply,
    I.parentOutcome_cell, I.parentCell_trans, I.parentOutcome_cell,
    I.parentOutcome_cell]

/-- Refinement coherence of an abstract estimation rule. -/
def Grain (E : I.EstimationRule) : Prop :=
  ∀ {fine coarse : I.Perspective} (r : I.Refinement fine coarse)
    (j : I.Cell coarse),
    I.weight E coarse j =
      ∑ i : I.Cell fine, if I.parentCell r i = j then I.weight E fine i else 0

/-- Expectation of a total act, summed only over a perspective's finite
cells. -/
noncomputable def expectation (E : I.EstimationRule) (D : I.Perspective)
    (a : Act I) : ℝ :=
  letI := I.cellFintype D
  ∑ c : I.Cell D, I.weight E D c * a (I.outcome c)

/-- Refinement invariance is stated once at the interface level. -/
def RefinementInvariant (V : I.Perspective → Act I → ℝ) : Prop :=
  ∀ {fine coarse : I.Perspective} (r : I.Refinement fine coarse) (a : Act I),
    V fine (pullbackAct I r a) = V coarse a

/-- The measure-to-functional bridge at the abstract level: Grain coherence
of cell weights makes their expectation functional refinement-invariant. -/
theorem expectation_refinementInvariant (E : I.EstimationRule) (hE : Grain I E) :
    RefinementInvariant I (expectation I E) := by
  intro fine coarse r a
  letI := I.cellFintype fine
  letI := I.cellFintype coarse
  letI := I.cellDecidableEq coarse
  unfold expectation pullbackAct
  simp only [Function.comp_apply]
  calc
    (∑ i : I.Cell fine,
        I.weight E fine i * a (I.parentOutcome r (I.outcome i))) =
        ∑ i : I.Cell fine,
          I.weight E fine i * a (I.outcome (I.parentCell r i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [I.parentOutcome_cell]
    _ = ∑ j : I.Cell coarse, ∑ i : I.Cell fine,
          if I.parentCell r i = j
          then I.weight E fine i * a (I.outcome j) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      calc
        I.weight E fine i * a (I.outcome (I.parentCell r i)) =
            ∑ j : I.Cell coarse,
              if j = I.parentCell r i
              then I.weight E fine i * a (I.outcome j) else 0 := by
          rw [Finset.sum_ite_eq' Finset.univ (I.parentCell r i)]
          simp
        _ = ∑ j : I.Cell coarse,
              if I.parentCell r i = j
              then I.weight E fine i * a (I.outcome j) else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hij : I.parentCell r i = j
          · rw [if_pos hij, if_pos hij.symm]
          · have hji : ¬j = I.parentCell r i := fun h => hij h.symm
            rw [if_neg hij, if_neg hji]
    _ = ∑ j : I.Cell coarse, I.weight E coarse j * a (I.outcome j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hE r j]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hij : I.parentCell r i = j <;> simp [hij]

/-! ## Projective route -/

namespace Projective

open QuantumFoundations.ProbabilityAPI

/-- The projective implementation. Its dependent cell subtype is confined
to finite summation; its acts are total functions on all subspaces. -/
@[reducible] noncomputable def interface (n : ℕ) : PerspectiveInterface where
  Perspective := Perspective n
  Outcome := Submodule ℂ (H n)
  Cell := fun D => {c // c ∈ D.cells}
  cellFintype := fun D => Fintype.ofFinset D.cells (by simp)
  cellDecidableEq := fun _ => Classical.decEq _
  outcome := Subtype.val
  Refinement := Refines
  parentOutcome := parentOf
  parentCell := fun r c => ⟨parentOf r c, parentOf_mem r c.property⟩
  parentOutcome_cell := by
    intro fine coarse r c
    rfl
  refl := Refines.refl
  trans := Refines.trans
  parentCell_refl := by
    intro D c
    apply Subtype.ext
    exact parentOf_eq_of_le (Refines.refl D) c.property c.property le_rfl
  parentCell_trans := by
    intro fine mid coarse r₁ r₂ c
    apply Subtype.ext
    exact parentOf_eq_of_le (Refines.trans r₁ r₂) c.property
      (parentOf_mem r₂ (parentOf_mem r₁ c.property))
      (le_trans (parentOf_le r₁ c.property)
        (parentOf_le r₂ (parentOf_mem r₁ c.property)))
  EstimationRule := Perspective n → Submodule ℂ (H n) → ℝ
  weight := fun E D c => E D c

@[simp] theorem interface_weight_apply {n : ℕ}
    (E : Perspective n → Submodule ℂ (H n) → ℝ) (D : Perspective n)
    (c : (interface n).Cell D) :
    (interface n).weight E D c = E D c.val := rfl

@[simp] theorem interface_parentCell_apply {n : ℕ}
    {fine coarse : Perspective n} (r : Refines fine coarse)
    (c : (interface n).Cell fine) :
    (interface n).parentCell r c =
      ⟨parentOf r c.val, parentOf_mem r c.property⟩ := rfl

private theorem grain_concrete {n : ℕ}
    (E : Perspective n → Submodule ℂ (H n) → ℝ) (hE : AxGrain E) :
    ∀ {fine coarse : Perspective n} (r : Refines fine coarse)
      (j : {c // c ∈ coarse.cells}),
      E coarse j.val = ∑ i : {c // c ∈ fine.cells},
        if parentOf r i.val = j.val then E fine i.val else 0 := by
  intro fine coarse r j
  have hgrain := (axGrain_iff_coarseCells E).mp hE fine coarse r j.val j.property
  rw [hgrain, coarseCells_eq_fiber_parentOf r j.property]
  rw [Finset.sum_filter]
  exact Finset.sum_subtype fine.cells (by simp)
    (fun i => if parentOf r i = j.val then E fine i else 0)

/-- The upstream projective Grain condition is exactly the interface-level
finite-fibre coherence. -/
theorem grain_of_axGrain {n : ℕ}
    (E : Perspective n → Submodule ℂ (H n) → ℝ) (hE : AxGrain E) :
    Grain (interface n) E := by
  unfold Grain
  intro fine coarse r j
  rw [interface_weight_apply]
  calc
    E coarse j.val = ∑ i : {c // c ∈ fine.cells},
        if parentOf r i.val = j.val then E fine i.val else 0 :=
      grain_concrete E hE r j
    _ = ∑ i : (interface n).Cell fine,
        if (interface n).parentCell r i = j
        then (interface n).weight E fine i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [interface_weight_apply]
      by_cases hi : parentOf r i.val = j.val
      · have hisub : (interface n).parentCell r i = j := by
          rw [interface_parentCell_apply]
          exact Subtype.ext hi
        rw [if_pos hi, if_pos hisub]
      · have hisub : ¬(interface n).parentCell r i = j := by
          intro h
          apply hi
          exact congrArg Subtype.val h
        rw [if_neg hi, if_neg hisub]

/-- The concrete Born weights supply a nonempty projective estimation rule
whose abstract expectation is refinement-invariant. -/
theorem born_refinementInvariant {n : ℕ} (v : H n) :
    RefinementInvariant (interface n)
      (expectation (interface n) (QuantumFoundations.ProbabilityAPI.BornRule.E₀ v)) :=
  expectation_refinementInvariant (interface n)
    (QuantumFoundations.ProbabilityAPI.BornRule.E₀ v)
    (grain_of_axGrain _ (QuantumFoundations.ProbabilityAPI.BornRule.E₀_isGrain v))

end Projective

/-! ## Effect route -/

namespace Effects

open QuantumFoundations.ProbabilityAPI

private abbrev NativeRefines {n : ℕ} :=
  QuantumFoundations.BornRule.EffectPerspectives.Refines (n := n)

/-- The effect implementation uses natural numbers as the ambient outcome
space. Out-of-perspective values are junk values; valid cells use the native
`Fin` parent carried by effect refinement. -/
@[reducible] noncomputable def interface (n : ℕ) : PerspectiveInterface where
  Perspective := EffectPerspectives.EffectPerspective n
  Outcome := ℕ
  Cell := fun D => Fin D.outcomes
  cellFintype := fun _ => inferInstance
  cellDecidableEq := fun _ => inferInstance
  outcome := Fin.val
  Refinement := NativeRefines
  parentOutcome := fun {fine} _ r i =>
    if hi : i < fine.outcomes then (r.parent ⟨i, hi⟩).val else 0
  parentCell := fun r => r.parent
  parentOutcome_cell := by
    intro fine coarse r c
    rw [dif_pos c.isLt]
  refl := QuantumFoundations.BornRule.EffectPerspectives.Refines.refl
  trans := QuantumFoundations.BornRule.EffectPerspectives.Refines.trans
  parentCell_refl := by
    intro D c
    rfl
  parentCell_trans := by
    intro fine mid coarse r₁ r₂ c
    rfl
  EstimationRule := EffectPerspectives.EstimationRule n
  weight := fun E D i => E.weight D i

/-- Every upstream effect estimation rule satisfies the single abstract
Grain predicate. -/
theorem estimationRule_grain {n : ℕ} (E : EffectPerspectives.EstimationRule n) :
    Grain (interface n) E := by
  intro fine coarse r j
  exact E.grain r j

/-- The concrete pure-state rule exposed by the API validates the effect
instance and its abstract refinement-invariant expectation. -/
theorem pureState_refinementInvariant {n : ℕ} (v : H n) (hv : ‖v‖ = 1) :
    RefinementInvariant (interface n)
      (expectation (interface n) (EffectPerspectives.pureStateEstimationRule v hv)) :=
  expectation_refinementInvariant (interface n)
    (EffectPerspectives.pureStateEstimationRule v hv)
    (estimationRule_grain _)

end Effects

end EverettianProbability.Abstract
