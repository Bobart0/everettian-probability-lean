import EverettianProbability.BornCalibration.GrainNecessity

/-!
# Relative necessity at the decision-functional interface

This file lifts the weight-level L0 witnesses to the public
`RationalExpectationFamily` interface used by `born_expectation_of_invariance`.
The generic construction `expectationFamilyOfWeight` turns any positive,
normalized contextual weight into the corresponding finite weighted-expectation
functional.  Its canonical weight agrees with the original weight on every
actual perspective cell.

The three deletion tests then reuse the already-certified weight-level
witnesses:

* `D1` removes canonical null support, using `W2`;
* `D2` removes the unit-state premise, using `W3`;
* `D3` removes local refinement invariance, using `W4`.

Each theorem retains every other exposed premise of
`born_expectation_of_invariance`, explicitly violates the removed premise, and
falsifies the theorem's exact expectation formula on an indicator act.
-/

namespace EverettianProbability.BornCalibration

open QuantumFoundations.ProbabilityAPI
open QuantumFoundations.ProbabilityAPI.BornRule
open EverettianProbability.Core
open EverettianProbability.Preference
open EverettianProbability.Refinement
open scoped Classical

noncomputable section

/-- Lift a positive normalized contextual weight to the finite weighted
expectation functional that it induces.  Grain is deliberately not required:
that premise remains exposed so that `D3` can delete it at the decision level. -/
def expectationFamilyOfWeight {n : ℕ}
    (Est : Perspective n → Submodule ℂ (H n) → ℝ)
    (hNorm : AxNorm Est) (hPos : AxPos Est) : RationalExpectationFamily n where
  V D a := ∑ c ∈ D.cells, Est D c * a c
  affine D t a b := by
    show ∑ c ∈ D.cells, Est D c * (t * a c + (1 - t) * b c) =
        t * ∑ c ∈ D.cells, Est D c * a c +
          (1 - t) * ∑ c ∈ D.cells, Est D c * b c
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    ring
  monotone D a b hab := by
    show ∑ c ∈ D.cells, Est D c * a c ≤
      ∑ c ∈ D.cells, Est D c * b c
    apply Finset.sum_le_sum
    intro c hc
    exact mul_le_mul_of_nonneg_left (hab c hc) (hPos D c hc)
  normalized_const D k := by
    show ∑ c ∈ D.cells, Est D c * k = k
    rw [← Finset.sum_mul, hNorm D, one_mul]

/-- On every actual cell, the canonical weight of the lifted expectation
family is exactly the contextual weight from which it was built. -/
theorem expectationFamilyOfWeight_canonicalWeight_eq {n : ℕ}
    (Est : Perspective n → Submodule ℂ (H n) → ℝ)
    (hNorm : AxNorm Est) (hPos : AxPos Est)
    {D : Perspective n} {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
    canonicalWeight (expectationFamilyOfWeight Est hNorm hPos) D c = Est D c := by
  show (if c ∈ D.cells then
      (expectationFamilyOfWeight Est hNorm hPos).V D (Act.indicator c) else 0) = Est D c
  rw [if_pos hc]
  show ∑ c' ∈ D.cells, Est D c' * Act.indicator c c' = Est D c
  rw [Finset.sum_eq_single c]
  · rw [Act.indicator_self, mul_one]
  · intro c' _ hne
    rw [Act.indicator_of_ne hne, mul_zero]
  · intro h
    exact absurd hc h

/-- The lifted functional evaluates a cell indicator to the original cell
weight. -/
theorem expectationFamilyOfWeight_indicator {n : ℕ}
    (Est : Perspective n → Submodule ℂ (H n) → ℝ)
    (hNorm : AxNorm Est) (hPos : AxPos Est)
    {D : Perspective n} {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
    (expectationFamilyOfWeight Est hNorm hPos).V D (Act.indicator c) = Est D c := by
  show ∑ c' ∈ D.cells, Est D c' * Act.indicator c c' = Est D c
  rw [Finset.sum_eq_single c]
  · rw [Act.indicator_self, mul_one]
  · intro c' _ hne
    rw [Act.indicator_of_ne hne, mul_zero]
  · intro h
    exact absurd hc h

/-- Grain coherence transports from a contextual weight to the canonical
weight of its lifted expectation family. -/
theorem expectationFamilyOfWeight_axGrain {n : ℕ}
    (Est : Perspective n → Submodule ℂ (H n) → ℝ)
    (hNorm : AxNorm Est) (hPos : AxPos Est) (hGrain : AxGrain Est) :
    AxGrain (canonicalWeight (expectationFamilyOfWeight Est hNorm hPos)) := by
  intro D' D hRefines c hc
  rw [expectationFamilyOfWeight_canonicalWeight_eq Est hNorm hPos hc,
    hGrain D' D hRefines c hc]
  apply Finset.sum_congr rfl
  intro c' hc'
  exact (expectationFamilyOfWeight_canonicalWeight_eq Est hNorm hPos
    (Finset.mem_filter.mp hc').1).symm

/-- A failure of Grain is reflected by the canonical weight of the lifted
family.  This is the direction needed by `D3`. -/
theorem expectationFamilyOfWeight_not_axGrain {n : ℕ}
    (Est : Perspective n → Submodule ℂ (H n) → ℝ)
    (hNorm : AxNorm Est) (hPos : AxPos Est) (hNotGrain : ¬ AxGrain Est) :
    ¬ AxGrain (canonicalWeight (expectationFamilyOfWeight Est hNorm hPos)) := by
  intro hCanonical
  apply hNotGrain
  intro D' D hRefines c hc
  calc
    Est D c = canonicalWeight (expectationFamilyOfWeight Est hNorm hPos) D c :=
      (expectationFamilyOfWeight_canonicalWeight_eq Est hNorm hPos hc).symm
    _ = ∑ c' ∈ D'.cells.filter (· ≤ c),
          canonicalWeight (expectationFamilyOfWeight Est hNorm hPos) D' c' :=
      hCanonical D' D hRefines c hc
    _ = ∑ c' ∈ D'.cells.filter (· ≤ c), Est D' c' := by
      apply Finset.sum_congr rfl
      intro c' hc'
      exact expectationFamilyOfWeight_canonicalWeight_eq Est hNorm hPos
        (Finset.mem_filter.mp hc').1

/-- Null support transports from the original contextual weight to the
canonical weight of its lifted expectation family. -/
theorem expectationFamilyOfWeight_axNul {n : ℕ}
    (Est : Perspective n → Submodule ℂ (H n) → ℝ)
    (hNorm : AxNorm Est) (hPos : AxPos Est) {v : H n}
    (hNul : AxNul Est v) :
    AxNul (canonicalWeight (expectationFamilyOfWeight Est hNorm hPos)) v := by
  intro D c hc horth
  rw [expectationFamilyOfWeight_canonicalWeight_eq Est hNorm hPos hc]
  exact hNul D c hc horth

/-- Failure of null support is likewise reflected by the canonical weight. -/
theorem expectationFamilyOfWeight_not_axNul {n : ℕ}
    (Est : Perspective n → Submodule ℂ (H n) → ℝ)
    (hNorm : AxNorm Est) (hPos : AxPos Est) {v : H n}
    (hNotNul : ¬ AxNul Est v) :
    ¬ AxNul (canonicalWeight (expectationFamilyOfWeight Est hNorm hPos)) v := by
  intro hCanonical
  apply hNotNul
  intro D c hc horth
  rw [← expectationFamilyOfWeight_canonicalWeight_eq Est hNorm hPos hc]
  exact hCanonical D c hc horth

private theorem born_indicator_sum_eq {n : ℕ} {v : H n}
    {D : Perspective n} {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
    (∑ d ∈ D.cells, ‖projL d v‖ ^ 2 * Act.indicator c d) =
      ‖projL c v‖ ^ 2 := by
  rw [Finset.sum_eq_single c]
  · rw [Act.indicator_self, mul_one]
  · intro d _ hne
    rw [Act.indicator_of_ne hne, mul_zero]
  · intro h
    exact absurd hc h

/-! ## D1 — remove canonical null support -/

/-- `D1`.  At the exact decision-functional interface, canonical null support
is relatively necessary.  The witness is the lifted `W2` weight: local
refinement invariance and unit normalization remain true, canonical null
support is false, and the exact Born expectation formula fails on an explicit
indicator act. -/
theorem d1_remove_canonical_null_support :
    ∃ (F : RationalExpectationFamily 3) (v : H 3),
      3 ≤ (3 : ℕ) ∧
      RefinementInvariantLocal F.V ∧
      ‖v‖ = 1 ∧
      ¬ AxNul (canonicalWeight F) v ∧
      ∃ (D : Perspective 3) (c : Submodule ℂ (H 3)),
        c ∈ D.cells ∧
        F.V D (Act.indicator c) ≠
          ∑ d ∈ D.cells, ‖projL d v‖ ^ 2 * Act.indicator c d := by
  rcases w2_remove_axNul with
    ⟨Est, v, hn3, hGrain, hNorm, hPos, hv, hNotNul, D, c, hc, hMismatch⟩
  refine ⟨expectationFamilyOfWeight Est hNorm hPos, v, hn3, ?_, hv, ?_,
    D, c, hc, ?_⟩
  · exact (refinementInvariantLocal_iff_axGrain
      (expectationFamilyOfWeight Est hNorm hPos)).mpr
        (expectationFamilyOfWeight_axGrain Est hNorm hPos hGrain)
  · exact expectationFamilyOfWeight_not_axNul Est hNorm hPos hNotNul
  · rw [expectationFamilyOfWeight_indicator Est hNorm hPos hc,
      born_indicator_sum_eq hc]
    exact hMismatch

/-! ## D2 — remove unit normalization of the tested state -/

/-- `D2`.  The unit-state premise is relatively necessary at the decision
interface.  The witness lifts `W3`: refinement invariance and canonical null
support remain true, the tested vector is explicitly non-unit, and the exact
Born expectation formula fails on an indicator act. -/
theorem d2_remove_unit_norm :
    ∃ (F : RationalExpectationFamily 3) (v : H 3),
      3 ≤ (3 : ℕ) ∧
      RefinementInvariantLocal F.V ∧
      AxNul (canonicalWeight F) v ∧
      ‖v‖ ≠ 1 ∧
      ∃ (D : Perspective 3) (c : Submodule ℂ (H 3)),
        c ∈ D.cells ∧
        F.V D (Act.indicator c) ≠
          ∑ d ∈ D.cells, ‖projL d v‖ ^ 2 * Act.indicator c d := by
  rcases w3_remove_unit_norm with
    ⟨Est, v, hn3, hGrain, hNorm, hPos, hNul, hNotUnit, D, c, hc, hMismatch⟩
  refine ⟨expectationFamilyOfWeight Est hNorm hPos, v, hn3, ?_, ?_, hNotUnit,
    D, c, hc, ?_⟩
  · exact (refinementInvariantLocal_iff_axGrain
      (expectationFamilyOfWeight Est hNorm hPos)).mpr
        (expectationFamilyOfWeight_axGrain Est hNorm hPos hGrain)
  · exact expectationFamilyOfWeight_axNul Est hNorm hPos hNul
  · rw [expectationFamilyOfWeight_indicator Est hNorm hPos hc,
      born_indicator_sum_eq hc]
    exact hMismatch

/-! ## D3 — remove local refinement invariance -/

/-- `D3`.  Local refinement invariance is relatively necessary at the exact
decision-functional interface.  The lifted `W4` amplitude weight remains a
positive normalized rational expectation family with unit state and canonical
null support, but its canonical weight fails Grain and therefore its
functional fails `RefinementInvariantLocal`; the exact Born expectation
formula also fails on the same witness cell's indicator act. -/
theorem d3_remove_refinementInvariantLocal :
    ∃ (F : RationalExpectationFamily 3) (v : H 3),
      3 ≤ (3 : ℕ) ∧
      ‖v‖ = 1 ∧
      AxNul (canonicalWeight F) v ∧
      ¬ RefinementInvariantLocal F.V ∧
      ∃ (D : Perspective 3) (c : Submodule ℂ (H 3)),
        c ∈ D.cells ∧
        F.V D (Act.indicator c) ≠
          ∑ d ∈ D.cells, ‖projL d v‖ ^ 2 * Act.indicator c d := by
  rcases w4_remove_axGrain with
    ⟨Est, v, hn3, hNorm, hPos, hv, hNul, hNotGrain, D, c, hc, hMismatch⟩
  refine ⟨expectationFamilyOfWeight Est hNorm hPos, v, hn3, hv, ?_, ?_,
    D, c, hc, ?_⟩
  · exact expectationFamilyOfWeight_axNul Est hNorm hPos hNul
  · intro hInv
    exact expectationFamilyOfWeight_not_axGrain Est hNorm hPos hNotGrain
      ((refinementInvariantLocal_iff_axGrain
        (expectationFamilyOfWeight Est hNorm hPos)).mp hInv)
  · rw [expectationFamilyOfWeight_indicator Est hNorm hPos hc,
      born_indicator_sum_eq hc]
    exact hMismatch

end

end EverettianProbability.BornCalibration
