import EverettianProbability.Diachronic.Conditioning
import EverettianProbability.Preference.Nonvacuity
import EverettianProbability.Core.Nonvacuity
import EverettianProbability.Rivals.NaiveBranchCounting

/-!
**FR.** # Non-trivialité du conditionnement sous raffinement

Ce module adapte la famille uniforme concrète à l'interface projective et
calcule directement l'échec de l'identité de marginalisation conditionnelle :
le membre gauche vaut `1`, tandis que le membre droit vaut `4 / 3`. L'identité
est donc non triviale. `conditionalWeight_trans_fiber` reste logiquement un
corollaire de Grain, et non une prémisse diachronique indépendante. Aucune
dynamique temporelle n'est formalisée : le raffinement ne reçoit qu'une lecture
diachronique interprétative.

**EN.** # Nontriviality of conditioning under refinement

This module adapts the concrete uniform family to the projective interface and
directly computes failure of conditional marginalization: the left-hand side
is `1`, while the right-hand side is `4 / 3`. The identity is therefore
nontrivial. `conditionalWeight_trans_fiber` remains logically a corollary of
Grain, not an independent diachronic premise. No temporal dynamics is
formalized: refinement receives only an interpretive diachronic reading.
-/

namespace EverettianProbability.Diachronic

open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Abstract EverettianProbability.Core
open EverettianProbability.Preference EverettianProbability.Rivals
open scoped BigOperators Classical

/-- **FR.** Famille d'espérance uniforme concrète, transportée vers
l'interface projective abstraite. Elle sert uniquement au contre-témoin
arithmétique de marginalisation conditionnelle ; aucune dynamique temporelle,
aucun record accessible et aucun continuateur ne figurent dans son type.

**EN.** Concrete uniform expectation family, transported to the abstract
projective interface. It is used only for the arithmetic counter-witness to
conditional marginalization; its type contains no temporal dynamics,
accessible record, or continuator. -/
noncomputable def uniformProjectiveExpectationFamily :
    RationalExpectationFamily (Projective.interface 3) where
  V := uniformExpectation
  affine := uniformExpectation_affine
  monotone := by
    intro D a b h
    apply uniformExpectation_monotone D a b
    intro c hc
    exact h ⟨c, hc⟩
  normalized_const := uniformExpectation_normalized_const

private theorem complement_mem_exampleCoarse : exampleLineᗮ ∈ exampleCoarse.cells := by
  simp only [exampleCoarse, QuantumFoundations.BornRule.Perspective.binary,
    Finset.mem_insert, Finset.mem_singleton, or_true]

private noncomputable def complementCell :
    (Projective.interface 3).Cell exampleCoarse :=
  ⟨exampleLineᗮ, complement_mem_exampleCoarse⟩

private theorem uniformProjective_weight (D : Perspective 3)
    (c : (Projective.interface 3).Cell D) :
    canonicalWeight uniformProjectiveExpectationFamily D c =
      1 / (D.cells.card : ℝ) := by
  unfold canonicalWeight uniformProjectiveExpectationFamily
  change (∑ d ∈ D.cells, if d = c.val then 1 else 0) / (D.cells.card : ℝ) =
    1 / (D.cells.card : ℝ)
  rw [Finset.sum_eq_single c.val]
  · simp
  · intro d hd hdc
    simp only [hdc, if_false]
  · exact fun hnot => (hnot c.property).elim

private theorem exampleLine_finrank : Module.finrank ℂ exampleLine = 1 := by
  apply finrank_span_singleton
  intro hzero
  have hnorm := (EuclideanSpace.basisFun (Fin 3) ℂ).orthonormal.1 (0 : Fin 3)
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

private theorem complement_finrank : Module.finrank ℂ exampleLineᗮ = 2 := by
  have hsum : Module.finrank ℂ exampleLine + Module.finrank ℂ exampleLineᗮ = 3 := by
    rw [Submodule.finrank_add_finrank_orthogonal]
    simp
  rw [exampleLine_finrank] at hsum
  omega

private theorem coarse_weight :
    canonicalWeight uniformProjectiveExpectationFamily exampleCoarse complementCell = 1 / 2 := by
  rw [uniformProjective_weight, exampleCoarse_cells_card]
  norm_num

private theorem fine_weight (i : (Projective.interface 3).Cell exampleFine) :
    canonicalWeight uniformProjectiveExpectationFamily exampleFine i = 1 / 3 := by
  rw [uniformProjective_weight, exampleFine_cells_card]
  norm_num

private theorem fine_parent_eq_complement
    (i : (Projective.interface 3).Cell exampleFine) :
    (Projective.interface 3).parentCell exampleFine_refines i = complementCell ↔
      parentOf exampleFine_refines i.val = exampleLineᗮ := by
  rw [Projective.interface_parentCell_apply]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- **FR.** Dans la configuration uniforme explicite, le membre gauche de
l'identité conditionnelle vaut `1`. Portée : aucun temps ni aucune dynamique
ne sont formalisés ; un raffinement ne reçoit qu'une lecture diachronique
interprétative.

**EN.** In the explicit uniform configuration, the left-hand side of the
conditional identity is `1`. Scope: no time or dynamics is formalized; a
refinement receives only an interpretive diachronic reading. -/
theorem uniform_conditionalWeight_trans_fiber_lhs :
    conditionalWeight uniformProjectiveExpectationFamily
      (Refines.refl exampleCoarse) complementCell complementCell = 1 := by
  have hparent :
      (Projective.interface 3).parentCell (Refines.refl exampleCoarse) complementCell =
        complementCell :=
    (Projective.interface 3).parentCell_refl exampleCoarse complementCell
  simp only [conditionalWeight, ↓reduceIte, hparent, coarse_weight]
  norm_num

/-- **FR.** Dans la configuration uniforme explicite, le membre droit de
l'identité conditionnelle vaut `4 / 3`. Portée : aucun temps ni aucune
dynamique ne sont formalisés ; un raffinement ne reçoit qu'une lecture
diachronique interprétative.

**EN.** In the explicit uniform configuration, the right-hand side of the
conditional identity is `4 / 3`. Scope: no time or dynamics is formalized; a
refinement receives only an interpretive diachronic reading. -/
theorem uniform_conditionalWeight_trans_fiber_rhs :
    (∑ i : (Projective.interface 3).Cell exampleFine,
      if (Projective.interface 3).parentCell exampleFine_refines i = complementCell then
        conditionalWeight uniformProjectiveExpectationFamily
          ((Projective.interface 3).trans exampleFine_refines (Refines.refl exampleCoarse))
          complementCell i
      else 0) = 4 / 3 := by
  calc
    (∑ i : (Projective.interface 3).Cell exampleFine,
      if (Projective.interface 3).parentCell exampleFine_refines i = complementCell then
        conditionalWeight uniformProjectiveExpectationFamily
          ((Projective.interface 3).trans exampleFine_refines (Refines.refl exampleCoarse))
          complementCell i
      else 0) =
        ∑ i : (Projective.interface 3).Cell exampleFine,
          if (Projective.interface 3).parentCell exampleFine_refines i = complementCell then
            (2 / 3 : ℝ)
          else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : (Projective.interface 3).parentCell exampleFine_refines i = complementCell
            · simp only [hi, ↓reduceIte, conditionalWeight, fine_weight, coarse_weight]
              norm_num
            · simp only [if_neg hi]
    _ = (∑ x ∈ exampleFine.cells,
          if parentOf exampleFine_refines x = exampleLineᗮ then (2 / 3 : ℝ) else 0) := by
          calc
            (∑ i : (Projective.interface 3).Cell exampleFine,
              if (Projective.interface 3).parentCell exampleFine_refines i = complementCell then
                (2 / 3 : ℝ)
              else 0) =
                ∑ i : (Projective.interface 3).Cell exampleFine,
                  if parentOf exampleFine_refines i.val = exampleLineᗮ then (2 / 3 : ℝ) else 0 := by
                    apply Finset.sum_congr rfl
                    intro i _
                    simp only [fine_parent_eq_complement]
            _ = (∑ x ∈ exampleFine.cells,
                  if parentOf exampleFine_refines x = exampleLineᗮ then (2 / 3 : ℝ) else 0) := by
                    symm
                    exact Finset.sum_subtype exampleFine.cells (fun x => by simp) (fun x =>
                      if parentOf exampleFine_refines x = exampleLineᗮ then (2 / 3 : ℝ) else 0)
    _ = ∑ x ∈ QuantumFoundations.BornRule.cellLines exampleLineᗮ, (2 / 3 : ℝ) := by
          rw [← Finset.sum_filter]
          rw [← QuantumFoundations.BornRule.coarseCells_eq_fiber_parentOf
            exampleFine_refines complement_mem_exampleCoarse]
          unfold QuantumFoundations.BornRule.coarseCells
          unfold exampleFine
          rw [QuantumFoundations.BornRule.refine_filter_eq_cellLines exampleCoarse
            exampleLineᗮ complement_mem_exampleCoarse]
    _ = 4 / 3 := by
          rw [Finset.sum_const, cellLines_card_eq_finrank, complement_finrank]
          norm_num

/-- **FR.** Le comptage uniforme viole directement l'identité conditionnelle
de marginalisation : ses membres calculés sont `1` et `4 / 3`. Portée : aucun
temps ni aucune dynamique ne sont formalisés ; un raffinement ne reçoit qu'une
lecture diachronique interprétative.

**EN.** Uniform counting directly violates the conditional marginalization
identity: its computed sides are `1` and `4 / 3`. Scope: no time or dynamics
is formalized; a refinement receives only an interpretive diachronic reading. -/
theorem uniform_conditionalWeight_trans_fiber_fails :
    ¬ (conditionalWeight uniformProjectiveExpectationFamily
        (Refines.refl exampleCoarse) complementCell complementCell =
      ∑ i : (Projective.interface 3).Cell exampleFine,
        if (Projective.interface 3).parentCell exampleFine_refines i = complementCell then
          conditionalWeight uniformProjectiveExpectationFamily
            ((Projective.interface 3).trans exampleFine_refines (Refines.refl exampleCoarse))
            complementCell i
        else 0) := by
  intro h
  rw [uniform_conditionalWeight_trans_fiber_lhs,
    uniform_conditionalWeight_trans_fiber_rhs] at h
  norm_num at h

end EverettianProbability.Diachronic
