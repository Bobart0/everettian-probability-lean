import QuantumFoundations.ProbabilityAPI

/-!
**FR.** # Actes finis

Un acte est une fonction totale sur tous les sous-espaces. Seules ses valeurs
sur les cellules d'une perspective ont un contenu décisionnel. Ce module
fournit les opérations ponctuelles et la décomposition finie d'un acte en
indicatrices, modulo `AgreeOn`.

**EN.** # Finite acts

An act is a total function on all subspaces. Only its values on a
perspective's cells carry decision-theoretic content. This module provides
the pointwise operations and the finite indicator decomposition of an act,
modulo `AgreeOn`.
-/

namespace EverettianProbability.Core

open QuantumFoundations.ProbabilityAPI
open scoped Classical

variable {n : ℕ}

/-- An act is a total payoff function; values outside the current
perspective are junk. -/
def Act (n : ℕ) := Submodule ℂ (H n) → ℝ

namespace Act

/-- Two acts agree on all cells of `D`. -/
def AgreeOn (D : Perspective n) (a b : Act n) : Prop :=
  ∀ c ∈ D.cells, a c = b c

/-- The constant act. -/
def const (k : ℝ) : Act n := fun _ => k

/-- The indicator of one ambient subspace. -/
noncomputable def indicator (c₀ : Submodule ℂ (H n)) : Act n :=
  fun c => if c = c₀ then 1 else 0

/-- Pointwise addition of acts. -/
def add (a b : Act n) : Act n := fun c => a c + b c

/-- Pointwise order on acts. -/
def PointwiseLE (a b : Act n) : Prop := ∀ c, a c ≤ b c

/-- Pointwise convex combination. -/
noncomputable def convComb (t : ℝ) (a b : Act n) : Act n :=
  fun c => t * a c + (1 - t) * b c

/-- Expansion of an act in the indicators of the cells of `D`. -/
noncomputable def indicatorExpansion (D : Perspective n) (a : Act n) : Act n :=
  fun c => ∑ d ∈ D.cells, a d * indicator d c

theorem agreeOn_refl (D : Perspective n) (a : Act n) : AgreeOn D a a := by
  intro c _
  rfl

theorem agreeOn_symm {D : Perspective n} {a b : Act n} (h : AgreeOn D a b) :
    AgreeOn D b a := by
  intro c hc
  exact (h c hc).symm

theorem agreeOn_trans {D : Perspective n} {a b d : Act n}
    (hab : AgreeOn D a b) (hbd : AgreeOn D b d) : AgreeOn D a d := by
  intro c hc
  exact (hab c hc).trans (hbd c hc)

/-- Agreement is stable under pointwise addition. -/
theorem agreeOn_add {D : Perspective n} {a₁ a₂ b₁ b₂ : Act n}
    (h₁ : AgreeOn D a₁ b₁) (h₂ : AgreeOn D a₂ b₂) :
    AgreeOn D (add a₁ a₂) (add b₁ b₂) := by
  intro c hc
  rw [add, add, h₁ c hc, h₂ c hc]

/-- Agreement is stable under convex combinations. -/
theorem agreeOn_convComb {D : Perspective n} {a₁ a₂ b₁ b₂ : Act n}
    (t : ℝ) (h₁ : AgreeOn D a₁ b₁) (h₂ : AgreeOn D a₂ b₂) :
    AgreeOn D (convComb t a₁ a₂) (convComb t b₁ b₂) := by
  intro c hc
  rw [convComb, convComb, h₁ c hc, h₂ c hc]

@[simp] theorem indicator_self (c : Submodule ℂ (H n)) : indicator c c = 1 := by
  simp only [indicator, if_pos]

theorem indicator_of_ne {c d : Submodule ℂ (H n)} (h : c ≠ d) :
    indicator d c = 0 := by
  simp only [indicator, if_neg h]

/-- On `D`, every act agrees with its finite expansion in cell indicators. -/
theorem agreeOn_indicatorExpansion (D : Perspective n) (a : Act n) :
    AgreeOn D a (indicatorExpansion D a) := by
  intro c hc
  unfold indicatorExpansion
  rw [Finset.sum_eq_single c]
  · simp only [indicator_self, mul_one]
  · intro d hd hdc
    rw [indicator_of_ne (Ne.symm hdc), mul_zero]
  · exact fun h => (h hc).elim

end Act
end EverettianProbability.Core
