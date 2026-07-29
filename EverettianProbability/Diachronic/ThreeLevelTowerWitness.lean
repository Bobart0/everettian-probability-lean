import EverettianProbability.Diachronic.TowerProperty

/-!
**FR.** # Témoin numérique à trois niveaux de la loi de la tour

Ce module construit une interface finie comportant une perspective présente,
une perspective intermédiaire et une perspective future. La cellule présente
se divise en deux continuateurs de poids `1/3` et `2/3`, eux-mêmes divisés en
quatre cellules futures de poids `1/6`, `1/6`, `1/6` et `1/2`.

Un acte futur non constant prend les valeurs `0`, `6`, `3` et `1`. Ses valeurs
conditionnelles intermédiaires sont `3` et `3/2`, tandis que les évaluations
directe et étagée depuis la cellule présente valent toutes deux `2`.

Ce modèle est un témoin abstrait fini de cohérence. Il n'est pas présenté comme
une dynamique quantique physique ni comme un modèle complet de décohérence ou
d'identité personnelle.

**EN.** # Three-level numerical witness for the tower property

This module constructs a finite interface with present, intermediate, and
future perspectives. The present cell divides into continuators of weights
`1/3` and `2/3`, themselves divided into four future cells of weights `1/6`,
`1/6`, `1/6`, and `1/2`.

A nonconstant future act has values `0`, `6`, `3`, and `1`. Its intermediate
conditional values are `3` and `3/2`, while both direct and staged evaluation
from the present cell equal `2`.

This model is a finite abstract coherence witness. It is not presented as a
physical quantum dynamics or as a complete model of decoherence or personal
identity.
-/

namespace EverettianProbability.Abstract

open scoped BigOperators Classical

noncomputable section

namespace ThreeLevelTowerWitness

inductive Perspective
  | present
  | middle
  | future
  deriving DecidableEq

abbrev Cell : Perspective → Type
  | .present => Fin 1
  | .middle => Fin 2
  | .future => Fin 4

instance cellFintype (D : Perspective) : Fintype (Cell D) := by
  cases D <;> infer_instance

instance cellDecidableEq (D : Perspective) : DecidableEq (Cell D) := by
  cases D <;> infer_instance

def outcome : {D : Perspective} → Cell D → Fin 4
  | .present, _ => 0
  | .middle, c => ⟨c.val, by omega⟩
  | .future, c => c

theorem outcome_injective :
    ∀ D : Perspective, Function.Injective (@outcome D) := by
  intro D
  cases D
  · exact fun _ _ _ => Subsingleton.elim _ _
  · intro x y h
    apply Fin.ext
    simpa [outcome] using congrArg Fin.val h
  · exact fun _ _ h => h

inductive Refinement : Perspective → Perspective → Type
  | refl (D : Perspective) : Refinement D D
  | later : Refinement .future .middle
  | earlier : Refinement .middle .present
  | composite : Refinement .future .present

def parentCell :
    {fine coarse : Perspective} →
      Refinement fine coarse → Cell fine → Cell coarse
  | _, _, .refl _, c => c
  | _, _, .later, c => ⟨c.val / 2, by omega⟩
  | _, _, .earlier, _ => 0
  | _, _, .composite, _ => 0

def parentOutcome :
    {fine coarse : Perspective} →
      Refinement fine coarse → Fin 4 → Fin 4
  | _, _, .refl _, x => x
  | _, _, .later, x => ⟨x.val / 2, by omega⟩
  | _, _, .earlier, _ => 0
  | _, _, .composite, _ => 0

theorem parentOutcome_cell
    {fine coarse : Perspective}
    (r : Refinement fine coarse)
    (c : Cell fine) :
    parentOutcome r (outcome c) = outcome (parentCell r c) := by
  cases r <;> rfl

def refinementRefl (D : Perspective) : Refinement D D := .refl D

def refinementTrans :
    ∀ {fine mid coarse : Perspective},
      Refinement fine mid → Refinement mid coarse →
        Refinement fine coarse
  | _, _, _, .refl _, r => r
  | _, _, _, r, .refl _ => r
  | _, _, _, .later, .earlier => .composite

theorem parentCell_refl (D : Perspective) (c : Cell D) :
    parentCell (refinementRefl D) c = c := by
  rfl

theorem parentCell_trans
    {fine mid coarse : Perspective}
    (r₁ : Refinement fine mid)
    (r₂ : Refinement mid coarse)
    (c : Cell fine) :
    parentCell (refinementTrans r₁ r₂) c =
      parentCell r₂ (parentCell r₁ c) := by
  cases r₁ <;> cases r₂ <;> rfl

def weight : (D : Perspective) → Cell D → ℝ
  | .present, _ => 1
  | .middle, c => if c.val = 0 then 1 / 3 else 2 / 3
  | .future, c =>
      match c.val with
      | 0 => 1 / 6
      | 1 => 1 / 6
      | 2 => 1 / 6
      | _ => 1 / 2

@[reducible] def interface : PerspectiveInterface where
  Perspective := Perspective
  Outcome := Fin 4
  Cell := Cell
  cellFintype := cellFintype
  cellDecidableEq := cellDecidableEq
  outcome := outcome
  Refinement := Refinement
  parentOutcome := parentOutcome
  parentCell := parentCell
  parentOutcome_cell := parentOutcome_cell
  refl := refinementRefl
  trans := refinementTrans
  parentCell_refl := parentCell_refl
  parentCell_trans := parentCell_trans
  EstimationRule := Unit
  weight := fun _ D c => weight D c

@[simp] theorem interface_weight_eq (D : Perspective) (c : Cell D) :
    interface.weight () D c = weight D c := rfl

@[simp] theorem interface_parentCell_eq
    {fine coarse : Perspective} (r : Refinement fine coarse) (c : Cell fine) :
    interface.parentCell r c = parentCell r c := rfl

@[simp] theorem interface_outcome_eq {D : Perspective} (c : Cell D) :
    interface.outcome c = outcome c := rfl

theorem weight_nonneg (D : Perspective) (c : Cell D) :
    0 ≤ interface.weight () D c := by
  change 0 ≤ weight D c
  cases D <;> fin_cases c <;> norm_num [weight]

theorem sum_weight_eq_one (D : Perspective) :
    (∑ c : interface.Cell D, interface.weight () D c) = 1 := by
  change (∑ c : Cell D, weight D c) = 1
  cases D
  · simp [weight]
  · rw [Fin.sum_univ_two]
    norm_num [weight]
  · rw [Fin.sum_univ_four]
    norm_num [weight]

theorem weight_grain : Grain interface () := by
  classical
  intro fine coarse r j
  change weight coarse j =
    ∑ i : Cell fine, if parentCell r i = j then weight fine i else 0
  cases r
  · cases fine
    · fin_cases j
      simp [weight, parentCell]
    · fin_cases j <;> rw [Fin.sum_univ_two] <;>
        norm_num [weight, parentCell]
    · fin_cases j <;> rw [Fin.sum_univ_four] <;>
        norm_num [weight, parentCell, Fin.ext_iff]
  · fin_cases j <;> rw [Fin.sum_univ_four] <;>
      norm_num [weight, parentCell]
  · fin_cases j
    rw [Fin.sum_univ_two]
    norm_num [weight, parentCell]
  · fin_cases j
    rw [Fin.sum_univ_four]
    norm_num [weight, parentCell]

noncomputable def expectationFamily : RationalExpectationFamily interface where
  V := fun D a => ∑ c : Cell D, weight D c * a (outcome c)
  affine := by
    intro D t a b
    calc
      (∑ c : Cell D, weight D c *
          (fun o => t * a o + (1 - t) * b o) (outcome c)) =
          ∑ c : Cell D, (t * (weight D c * a (outcome c)) +
            (1 - t) * (weight D c * b (outcome c))) := by
            apply Finset.sum_congr rfl
            intro c _
            ring
      _ = t * (∑ c : Cell D, weight D c * a (outcome c)) +
          (1 - t) * (∑ c : Cell D, weight D c * b (outcome c)) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  monotone := by
    intro D a b hab
    apply Finset.sum_le_sum
    intro c _
    exact mul_le_mul_of_nonneg_left (hab c) (weight_nonneg D c)
  normalized_const := by
    intro D k
    unfold Act.const
    rw [← Finset.sum_mul]
    cases D
    · simp [weight]
    · rw [Fin.sum_univ_two]
      norm_num [weight]
    · rw [Fin.sum_univ_four]
      norm_num [weight]

theorem refinementInvariantLocal :
    RefinementInvariantLocal expectationFamily.V := by
  rw [refinementInvariantLocal_iff_pullback expectationFamily]
  change RefinementInvariant interface (expectation interface ())
  exact expectation_refinementInvariant interface () weight_grain

theorem canonicalWeight_eq_explicitWeight
    (D : Perspective)
    (c : interface.Cell D) :
    canonicalWeight expectationFamily D c = interface.weight () D c := by
  have h := weights_unique_on_cells expectationFamily D (outcome_injective D)
    (weight D) (by intro a; rfl) c
  exact h.symm

def presentCell : Cell Perspective.present := ⟨0, by omega⟩
def middleLeft : Cell Perspective.middle := ⟨0, by omega⟩
def middleRight : Cell Perspective.middle := ⟨1, by omega⟩
def futureZero : Cell Perspective.future := ⟨0, by omega⟩
def futureOne : Cell Perspective.future := ⟨1, by omega⟩
def futureTwo : Cell Perspective.future := ⟨2, by omega⟩
def futureThree : Cell Perspective.future := ⟨3, by omega⟩

def earlier : ContinuationStep interface Perspective.middle Perspective.present where
  refinement := Refinement.earlier

def later : ContinuationStep interface Perspective.future Perspective.middle where
  refinement := Refinement.later

def futureAct : Act interface := fun o =>
  match o.val with
  | 0 => 0
  | 1 => 6
  | 2 => 3
  | _ => 1

@[simp] theorem futureAct_at_zero : futureAct (interface.outcome futureZero) = 0 := by rfl
@[simp] theorem futureAct_at_one : futureAct (interface.outcome futureOne) = 6 := by rfl
@[simp] theorem futureAct_at_two : futureAct (interface.outcome futureTwo) = 3 := by rfl
@[simp] theorem futureAct_at_three : futureAct (interface.outcome futureThree) = 1 := by rfl

theorem presentWeight_eq_one :
    canonicalWeight expectationFamily Perspective.present presentCell = 1 := by
  rw [canonicalWeight_eq_explicitWeight]
  norm_num [interface, weight, presentCell]

theorem middleLeftWeight_eq_one_third :
    canonicalWeight expectationFamily Perspective.middle middleLeft = 1 / 3 := by
  rw [canonicalWeight_eq_explicitWeight]
  norm_num [interface, weight, middleLeft]

theorem middleRightWeight_eq_two_thirds :
    canonicalWeight expectationFamily Perspective.middle middleRight = 2 / 3 := by
  rw [canonicalWeight_eq_explicitWeight]
  norm_num [interface, weight, middleRight]

theorem futureZeroWeight_eq_one_sixth :
    canonicalWeight expectationFamily Perspective.future futureZero = 1 / 6 := by
  rw [canonicalWeight_eq_explicitWeight]
  norm_num [interface, weight, futureZero]

theorem futureOneWeight_eq_one_sixth :
    canonicalWeight expectationFamily Perspective.future futureOne = 1 / 6 := by
  rw [canonicalWeight_eq_explicitWeight]
  norm_num [interface, weight, futureOne]

theorem futureTwoWeight_eq_one_sixth :
    canonicalWeight expectationFamily Perspective.future futureTwo = 1 / 6 := by
  rw [canonicalWeight_eq_explicitWeight]
  norm_num [interface, weight, futureTwo]

theorem futureThreeWeight_eq_one_half :
    canonicalWeight expectationFamily Perspective.future futureThree = 1 / 2 := by
  rw [canonicalWeight_eq_explicitWeight]
  norm_num [interface, weight, futureThree]

private theorem continuatorCredence_eq_ratio
    {futureD presentD : Perspective}
    (step : ContinuationStep interface futureD presentD)
    (c : interface.Cell presentD)
    (i : interface.Cell futureD)
    (hc : canonicalWeight expectationFamily presentD c ≠ 0) :
    step.continuatorCredence expectationFamily c i =
      if interface.parentCell step.refinement i = c then
        canonicalWeight expectationFamily futureD i /
          canonicalWeight expectationFamily presentD c
      else 0 := by
  rw [step.continuatorCredence_eq_conditionalWeight_total expectationFamily
    refinementInvariantLocal outcome_injective c i]
  unfold conditionalWeight
  simp [hc]

theorem middleLeftCredence_eq_one_third :
    earlier.continuatorCredence expectationFamily presentCell middleLeft = 1 / 3 := by
  rw [continuatorCredence_eq_ratio earlier presentCell middleLeft]
  · rw [middleLeftWeight_eq_one_third, presentWeight_eq_one]
    norm_num [earlier, interface, parentCell, presentCell, middleLeft]
  · rw [presentWeight_eq_one]
    norm_num

theorem middleRightCredence_eq_two_thirds :
    earlier.continuatorCredence expectationFamily presentCell middleRight = 2 / 3 := by
  rw [continuatorCredence_eq_ratio earlier presentCell middleRight]
  · rw [middleRightWeight_eq_two_thirds, presentWeight_eq_one]
    norm_num [earlier, interface, parentCell, presentCell, middleRight]
  · rw [presentWeight_eq_one]
    norm_num

theorem futureZeroCredence_given_middleLeft_eq_one_half :
    later.continuatorCredence expectationFamily middleLeft futureZero = 1 / 2 := by
  rw [continuatorCredence_eq_ratio later middleLeft futureZero]
  · rw [futureZeroWeight_eq_one_sixth, middleLeftWeight_eq_one_third]
    norm_num [later, interface, parentCell, middleLeft, futureZero]
  · rw [middleLeftWeight_eq_one_third]
    norm_num

theorem futureOneCredence_given_middleLeft_eq_one_half :
    later.continuatorCredence expectationFamily middleLeft futureOne = 1 / 2 := by
  rw [continuatorCredence_eq_ratio later middleLeft futureOne]
  · rw [futureOneWeight_eq_one_sixth, middleLeftWeight_eq_one_third]
    norm_num [later, interface, parentCell, middleLeft, futureOne]
  · rw [middleLeftWeight_eq_one_third]
    norm_num

theorem futureTwoCredence_given_middleRight_eq_one_quarter :
    later.continuatorCredence expectationFamily middleRight futureTwo = 1 / 4 := by
  rw [continuatorCredence_eq_ratio later middleRight futureTwo]
  · rw [futureTwoWeight_eq_one_sixth, middleRightWeight_eq_two_thirds]
    norm_num [later, interface, parentCell, middleRight, futureTwo]
  · rw [middleRightWeight_eq_two_thirds]
    norm_num

theorem futureThreeCredence_given_middleRight_eq_three_quarters :
    later.continuatorCredence expectationFamily middleRight futureThree = 3 / 4 := by
  rw [continuatorCredence_eq_ratio later middleRight futureThree]
  · rw [futureThreeWeight_eq_one_half, middleRightWeight_eq_two_thirds]
    norm_num [later, interface, parentCell, middleRight, futureThree]
  · rw [middleRightWeight_eq_two_thirds]
    norm_num

private theorem futureCredence_zero_of_not_parent
    (c : interface.Cell Perspective.middle)
    (i : interface.Cell Perspective.future)
    (h : interface.parentCell later.refinement i ≠ c) :
    later.continuatorCredence expectationFamily c i = 0 :=
  later.continuatorCredence_zero_of_parent_ne expectationFamily c i h

theorem leftConditionalExpectedValue_eq_three :
    later.continuatorExpectedValue expectationFamily middleLeft futureAct = 3 := by
  unfold ContinuationStep.continuatorExpectedValue
  change (∑ i : Fin 4,
    later.continuatorCredence expectationFamily middleLeft i *
      futureAct (outcome (D := Perspective.future) i)) = 3
  rw [Fin.sum_univ_four]
  have hzero' : later.continuatorCredence expectationFamily middleLeft (0 : Fin 4) = 1 / 2 := by
    simpa [futureZero] using futureZeroCredence_given_middleLeft_eq_one_half
  have hone' : later.continuatorCredence expectationFamily middleLeft (1 : Fin 4) = 1 / 2 := by
    simpa [futureOne] using futureOneCredence_given_middleLeft_eq_one_half
  have htwo : later.continuatorCredence expectationFamily middleLeft futureTwo = 0 := by
    apply futureCredence_zero_of_not_parent
    change parentCell Refinement.later futureTwo ≠ middleLeft
    norm_num [parentCell, futureTwo, middleLeft]
  have hthree : later.continuatorCredence expectationFamily middleLeft futureThree = 0 := by
    apply futureCredence_zero_of_not_parent
    change parentCell Refinement.later futureThree ≠ middleLeft
    norm_num [parentCell, futureThree, middleLeft]
  have htwo' : later.continuatorCredence expectationFamily middleLeft (2 : Fin 4) = 0 := by
    simpa [futureTwo] using htwo
  have hthree' : later.continuatorCredence expectationFamily middleLeft (3 : Fin 4) = 0 := by
    simpa [futureThree] using hthree
  rw [hzero', hone', htwo', hthree']
  norm_num [futureAct, outcome, futureZero, futureOne, futureTwo, futureThree]

theorem rightConditionalExpectedValue_eq_three_halves :
    later.continuatorExpectedValue expectationFamily middleRight futureAct = 3 / 2 := by
  unfold ContinuationStep.continuatorExpectedValue
  change (∑ i : Fin 4,
    later.continuatorCredence expectationFamily middleRight i *
      futureAct (outcome (D := Perspective.future) i)) = 3 / 2
  rw [Fin.sum_univ_four]
  have htwo' : later.continuatorCredence expectationFamily middleRight (2 : Fin 4) = 1 / 4 := by
    simpa [futureTwo] using futureTwoCredence_given_middleRight_eq_one_quarter
  have hthree' : later.continuatorCredence expectationFamily middleRight (3 : Fin 4) = 3 / 4 := by
    simpa [futureThree] using futureThreeCredence_given_middleRight_eq_three_quarters
  have hzero : later.continuatorCredence expectationFamily middleRight futureZero = 0 := by
    apply futureCredence_zero_of_not_parent
    change parentCell Refinement.later futureZero ≠ middleRight
    norm_num [parentCell, futureZero, middleRight]
  have hone : later.continuatorCredence expectationFamily middleRight futureOne = 0 := by
    apply futureCredence_zero_of_not_parent
    change parentCell Refinement.later futureOne ≠ middleRight
    norm_num [parentCell, futureOne, middleRight]
  have hzero' : later.continuatorCredence expectationFamily middleRight (0 : Fin 4) = 0 := by
    simpa [futureZero] using hzero
  have hone' : later.continuatorCredence expectationFamily middleRight (1 : Fin 4) = 0 := by
    simpa [futureOne] using hone
  rw [hzero', hone', htwo', hthree']
  norm_num [futureAct, outcome, futureZero, futureOne, futureTwo, futureThree]

private theorem directFutureCredence_eq_weight
    (i : interface.Cell Perspective.future) :
    (later.trans earlier).continuatorCredence expectationFamily presentCell i =
      canonicalWeight expectationFamily Perspective.future i := by
  rw [continuatorCredence_eq_ratio (later.trans earlier) presentCell i]
  · rw [presentWeight_eq_one]
    change (if parentCell (refinementTrans Refinement.later Refinement.earlier) i = presentCell then
      canonicalWeight expectationFamily Perspective.future i / 1 else 0) =
        canonicalWeight expectationFamily Perspective.future i
    simp [refinementTrans, parentCell, presentCell]
  · rw [presentWeight_eq_one]
    norm_num

theorem directConditionalExpectedValue_eq_two :
    (later.trans earlier).continuatorExpectedValue expectationFamily presentCell futureAct = 2 := by
  unfold ContinuationStep.continuatorExpectedValue
  change (∑ i : Fin 4,
    (later.trans earlier).continuatorCredence expectationFamily presentCell i *
      futureAct (outcome (D := Perspective.future) i)) = 2
  rw [Fin.sum_univ_four]
  have hzero : (later.trans earlier).continuatorCredence expectationFamily presentCell (0 : Fin 4) = 1 / 6 := by
    rw [← futureZeroWeight_eq_one_sixth]
    simpa [futureZero] using directFutureCredence_eq_weight futureZero
  have hone : (later.trans earlier).continuatorCredence expectationFamily presentCell (1 : Fin 4) = 1 / 6 := by
    rw [← futureOneWeight_eq_one_sixth]
    simpa [futureOne] using directFutureCredence_eq_weight futureOne
  have htwo : (later.trans earlier).continuatorCredence expectationFamily presentCell (2 : Fin 4) = 1 / 6 := by
    rw [← futureTwoWeight_eq_one_sixth]
    simpa [futureTwo] using directFutureCredence_eq_weight futureTwo
  have hthree : (later.trans earlier).continuatorCredence expectationFamily presentCell (3 : Fin 4) = 1 / 2 := by
    rw [← futureThreeWeight_eq_one_half]
    simpa [futureThree] using directFutureCredence_eq_weight futureThree
  rw [hzero, hone, htwo, hthree]
  norm_num [futureAct, outcome, futureZero, futureOne, futureTwo, futureThree]

theorem stagedConditionalExpectedValue_eq_two :
    ContinuationStep.stagedContinuatorExpectedValue expectationFamily later earlier
      presentCell futureAct = 2 := by
  unfold ContinuationStep.stagedContinuatorExpectedValue
  change (∑ j : Fin 2,
    earlier.continuatorCredence expectationFamily presentCell j *
      later.continuatorExpectedValue expectationFamily j futureAct) = 2
  rw [Fin.sum_univ_two]
  have hleftC : earlier.continuatorCredence expectationFamily presentCell (0 : Fin 2) = 1 / 3 := by
    simpa [middleLeft] using middleLeftCredence_eq_one_third
  have hrightC : earlier.continuatorCredence expectationFamily presentCell (1 : Fin 2) = 2 / 3 := by
    simpa [middleRight] using middleRightCredence_eq_two_thirds
  have hleftV : later.continuatorExpectedValue expectationFamily (0 : Fin 2) futureAct = 3 := by
    simpa [middleLeft] using leftConditionalExpectedValue_eq_three
  have hrightV : later.continuatorExpectedValue expectationFamily (1 : Fin 2) futureAct = 3 / 2 := by
    simpa [middleRight] using rightConditionalExpectedValue_eq_three_halves
  rw [hleftC, hrightC, hleftV, hrightV]
  norm_num

/-- Exact nontrivial numerical witness of the continuator tower property. -/
theorem towerProperty_exact_witness :
    (later.trans earlier).continuatorExpectedValue expectationFamily presentCell futureAct =
      ContinuationStep.stagedContinuatorExpectedValue expectationFamily later earlier
        presentCell futureAct := by
  rw [directConditionalExpectedValue_eq_two, stagedConditionalExpectedValue_eq_two]

/-- The explicit numerical equality is also an instance of the abstract tower theorem. -/
theorem towerProperty_exact_witness_from_general_theorem :
    (later.trans earlier).continuatorExpectedValue expectationFamily presentCell futureAct =
      ContinuationStep.stagedContinuatorExpectedValue expectationFamily later earlier
        presentCell futureAct := by
  apply ContinuationStep.continuatorExpectedValue_tower expectationFamily
    refinementInvariantLocal outcome_injective later earlier presentCell
  rw [presentWeight_eq_one]
  norm_num

/-- The tower witness is nontrivial: intermediate credences and values differ. -/
theorem towerProperty_witness_nontrivial :
    earlier.continuatorCredence expectationFamily presentCell middleLeft ≠
        earlier.continuatorCredence expectationFamily presentCell middleRight ∧
    later.continuatorExpectedValue expectationFamily middleLeft futureAct ≠
        later.continuatorExpectedValue expectationFamily middleRight futureAct ∧
    (later.trans earlier).continuatorExpectedValue expectationFamily presentCell futureAct =
      ContinuationStep.stagedContinuatorExpectedValue expectationFamily later earlier
        presentCell futureAct := by
  constructor
  · rw [middleLeftCredence_eq_one_third, middleRightCredence_eq_two_thirds]
    norm_num
  constructor
  · rw [leftConditionalExpectedValue_eq_three, rightConditionalExpectedValue_eq_three_halves]
    norm_num
  · exact towerProperty_exact_witness

end ThreeLevelTowerWitness

end
end EverettianProbability.Abstract
