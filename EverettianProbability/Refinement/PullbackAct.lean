import EverettianProbability.Core.Act

/-!
**FR.** # Tiré-en-arrière d'un acte

Le tiré-en-arrière compose un acte total avec la carte parent totale de
l'API amont. Les lois de réflexivité et de composition sont énoncées sur les
cellules pertinentes, là où la valeur poubelle de `parentOf` n'intervient pas.

**EN.** # Pullback of an act

Pullback composes a total act with the upstream API's total parent map. The
identity and composition laws are stated on the relevant cells, where
`parentOf`'s junk value is immaterial.
-/

namespace EverettianProbability.Refinement

open QuantumFoundations.ProbabilityAPI EverettianProbability.Core
open scoped Classical

variable {n : ℕ}

/-- Pull an act on `D` back to a refinement `D'`. -/
noncomputable def pullbackAct {D' D : Perspective n} (r : Refines D' D)
    (a : Act n) : Act n := a ∘ parentOf r

/-- The indicator of the fiber of `parentOf r` above `c`. -/
noncomputable def fiberIndicator {D' D : Perspective n} (r : Refines D' D)
    (c : Submodule ℂ (H n)) : Act n :=
  fun c' => if parentOf r c' = c then 1 else 0

theorem pullbackAct_const {D' D : Perspective n} (r : Refines D' D) (k : ℝ) :
    pullbackAct r (Act.const k) = Act.const k := rfl

theorem pullbackAct_agree_of_agree {D' D : Perspective n} (r : Refines D' D)
    {a b : Act n} (h : Act.AgreeOn D a b) :
    Act.AgreeOn D' (pullbackAct r a) (pullbackAct r b) := by
  intro c' hc'
  exact h (parentOf r c') (parentOf_mem r hc')

/-- Pullback along a reflexive refinement acts as the identity on cells. -/
theorem pullbackAct_refl_agree (D : Perspective n) (a : Act n) :
    Act.AgreeOn D (pullbackAct (Refines.refl D) a) a := by
  intro c hc
  change a (parentOf (Refines.refl D) c) = a c
  rw [parentOf_eq_of_le (Refines.refl D) hc hc (le_refl c)]

/-- Pullback is compatible with transitive composition on fine cells. -/
theorem pullbackAct_trans_agree {D'' D' D : Perspective n}
    (r₁ : Refines D'' D') (r₂ : Refines D' D) (a : Act n) :
    Act.AgreeOn D'' (pullbackAct (Refines.trans r₁ r₂) a)
      (pullbackAct r₁ (pullbackAct r₂ a)) := by
  intro c'' hc''
  change a (parentOf (Refines.trans r₁ r₂) c'') =
    a (parentOf r₂ (parentOf r₁ c''))
  rw [parentOf_eq_of_le (Refines.trans r₁ r₂) hc''
    (parentOf_mem r₂ (parentOf_mem r₁ hc''))
    ((parentOf_le r₁ hc'').trans (parentOf_le r₂ (parentOf_mem r₁ hc'')))]

/-- Pulling back an indicator gives exactly the indicator of its parent
fiber, as total acts. -/
theorem pullbackAct_indicator {D' D : Perspective n} (r : Refines D' D)
    (c : Submodule ℂ (H n)) :
    pullbackAct r (Act.indicator c) = fiberIndicator r c := rfl

/-- On fine cells, the pulled-back indicator is one exactly on the
`coarseCells` fiber supplied by the upstream API. -/
theorem pullbackAct_indicator_eq_one_iff {D' D : Perspective n}
    (r : Refines D' D) {c : Submodule ℂ (H n)} (hc : c ∈ D.cells)
    {c' : Submodule ℂ (H n)} (hc' : c' ∈ D'.cells) :
    pullbackAct r (Act.indicator c) c' = 1 ↔ c' ∈ coarseCells D' c := by
  rw [coarseCells_eq_fiber_parentOf r hc]
  simp only [Finset.mem_filter, hc', true_and, pullbackAct, Function.comp_apply,
    Act.indicator]
  constructor
  · by_cases hparent : parentOf r c' = c
    · exact fun _ => hparent
    · simp only [hparent, if_false, zero_ne_one, false_implies]
  · intro hparent
    simp only [hparent, if_true]

end EverettianProbability.Refinement
