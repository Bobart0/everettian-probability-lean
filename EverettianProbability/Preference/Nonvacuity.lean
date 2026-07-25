import EverettianProbability.Preference.ExpectationFunctional

/-!
**FR.** # Non-vacuité — `Preference`

Témoin concret d'une `RationalExpectationFamily` : la moyenne uniforme sur
les cellules d'une perspective, `V D a := (∑ c ∈ D.cells, a c) / |D.cells|`,
à `n = 3` fixé. Ce witness est délibérément **dégénéré** — un comptage
uniforme, pas une règle bornienne — précisément pour rester non circulaire
(voir `DEPENDENCY_LEDGER.md`) : il ne présuppose ni norme hilbertienne ni
mesure de Born, seulement l'existence d'au moins une cellule (garantie par
`D.span = ⊤` dès que `H n ≠ ⊥`, ici `n = 3`). Les trois axiomes sont
prouvés en entier, aucun but ouvert.

**EN.** # Nonvacuity — `Preference`

Concrete witness of a `RationalExpectationFamily`: the uniform average
over the cells of a perspective, `V D a := (∑ c ∈ D.cells, a c) / |D.cells|`,
at fixed `n = 3`. This witness is deliberately **degenerate** — a uniform
count, not a Born-based rule — precisely to stay non-circular (see
`DEPENDENCY_LEDGER.md`): it presupposes neither a Hilbert-space norm nor a
Born measure, only the existence of at least one cell (guaranteed by
`D.span = ⊤` as soon as `H n ≠ ⊥`, here `n = 3`). All three axioms are
proved in full, no goal is left open.
-/

namespace EverettianProbability.Preference

open QuantumFoundations.BornRule Gleason EverettianProbability.Core

/-- `H 3` is nontrivial: `⊤ ≠ ⊥`. -/
theorem top_ne_bot_H3 : (⊤ : Submodule ℂ (H 3)) ≠ ⊥ := by
  intro h
  have h1 : Module.finrank ℂ (⊤ : Submodule ℂ (H 3)) = 3 := by rw [finrank_top]; simp
  rw [h] at h1
  simp at h1

/-- Every perspective on `H 3` has at least one cell. -/
theorem cells_nonempty (D : Perspective 3) : D.cells.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  apply top_ne_bot_H3
  rw [← D.span, hempty]
  simp

/-- The uniform average of an act over the cells of a perspective. -/
noncomputable def uniformExpectation (D : Perspective 3) (a : Act 3) : ℝ :=
  (∑ c ∈ D.cells, a c) / (D.cells.card : ℝ)

theorem uniformExpectation_affine (D : Perspective 3) (t : ℝ) (a b : Act 3) :
    uniformExpectation D (fun c => t * a c + (1 - t) * b c)
      = t * uniformExpectation D a + (1 - t) * uniformExpectation D b := by
  unfold uniformExpectation
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, add_div, mul_div_assoc,
    mul_div_assoc]

theorem uniformExpectation_monotone (D : Perspective 3) (a b : Act 3)
    (h : ∀ c ∈ D.cells, a c ≤ b c) : uniformExpectation D a ≤ uniformExpectation D b := by
  unfold uniformExpectation
  have hsum : ∑ c ∈ D.cells, a c ≤ ∑ c ∈ D.cells, b c := Finset.sum_le_sum h
  gcongr

theorem uniformExpectation_normalized_const (D : Perspective 3) (k : ℝ) :
    uniformExpectation D (Act.const k) = k := by
  unfold uniformExpectation Act.const
  have hne : D.cells.Nonempty := cells_nonempty D
  have hcard : (D.cells.card : ℝ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact Finset.card_ne_zero_of_mem hne.choose_spec
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- The concrete nonvacuity witness: the uniform-average expectation family
on `H 3`. -/
noncomputable def uniformExpectationFamily : RationalExpectationFamily 3 where
  V := uniformExpectation
  affine := uniformExpectation_affine
  monotone := uniformExpectation_monotone
  normalized_const := uniformExpectation_normalized_const

end EverettianProbability.Preference
