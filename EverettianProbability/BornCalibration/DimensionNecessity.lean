import EverettianProbability.BornCalibration.GrainNecessity
import Gleason.Nonvacuity

/-!
# Sharpness of the dimension bound

This file supplies `W0` of the JAR L0 campaign.  Unlike the relative-necessity
witnesses for the exposed axioms, the hypothesis `3 ≤ n` is a boundary on the
ambient Hilbert space.  Its sharpness is therefore audited separately, by an
explicit model on `H 2`.

Start with the pure-state Born projection measure for the first computational
basis vector, and deform every probability `t ∈ [0,1]` by

`g(t) = 3 t^2 - 2 t^3`.

In dimension two, two nonzero orthogonal subspaces necessarily span the whole
space.  Hence their Born probabilities are complementary, and
`g(t) + g(1-t) = 1`; the deformed assignment is still a normalized positive
finitely additive projection measure.  It vanishes on every subspace
orthogonal to the chosen state, but differs from Born on an oblique line.
-/

namespace EverettianProbability.BornCalibration

open QuantumFoundations.ProbabilityAPI
open QuantumFoundations.ProbabilityAPI.BornRule
open scoped Classical InnerProductSpace

noncomputable section

/-- Polynomial deformation used for the dimension-two Gleason countermodel. -/
def w0Smoothstep (t : ℝ) : ℝ := 3 * t ^ 2 - 2 * t ^ 3

/-- First computational basis vector of `H 2`. -/
def w0e0 : H 2 := EuclideanSpace.single (0 : Fin 2) (1 : ℂ)

/-- Second computational basis vector of `H 2`. -/
def w0e1 : H 2 := EuclideanSpace.single (1 : Fin 2) (1 : ℂ)

theorem w0e0_norm : ‖w0e0‖ = 1 := by
  simp [w0e0]

theorem w0e1_norm : ‖w0e1‖ = 1 := by
  simp [w0e1]

/-- The ordinary pure-state Born projection measure anchored at `w0e0`. -/
def w0BornMeasure : Gleason.ProjMeasure 2 :=
  Gleason.pureState w0e0 w0e0_norm

/-- In `H 2`, two nonzero orthogonal subspaces necessarily span the whole space. -/
private theorem w0_sup_eq_top_of_isOrtho {A B : Submodule ℂ (H 2)}
    (hA : A ≠ ⊥) (hB : B ≠ ⊥) (hAB : A ⟂ B) : A ⊔ B = ⊤ := by
  have hApos : 0 < Module.finrank ℂ A := by
    rw [Module.finrank_pos_iff_of_free]
    exact Submodule.nontrivial_iff_ne_bot.mpr hA
  have hBpos : 0 < Module.finrank ℂ B := by
    rw [Module.finrank_pos_iff_of_free]
    exact Submodule.nontrivial_iff_ne_bot.mpr hB
  have hdim : Module.finrank ℂ (H 2) ≤ Module.finrank ℂ A + Module.finrank ℂ B := by
    simp
    omega
  exact Submodule.eq_top_of_disjoint A B hdim hAB.disjoint

/-- The smoothstep deformation of a pure-state projection measure.  The special
feature of dimension two makes it remain finitely additive. -/
def w0NonBornMeasure : Gleason.ProjMeasure 2 where
  μ A := w0Smoothstep (w0BornMeasure.μ A)
  nonneg A := by
    have hle : w0BornMeasure.μ A ≤ 1 := w0BornMeasure.le_one A
    change 0 ≤ w0Smoothstep (w0BornMeasure.μ A)
    unfold w0Smoothstep
    rw [show 3 * w0BornMeasure.μ A ^ 2 - 2 * w0BornMeasure.μ A ^ 3 =
      w0BornMeasure.μ A ^ 2 * (3 - 2 * w0BornMeasure.μ A) by ring]
    exact mul_nonneg (sq_nonneg _) (by linarith)
  top_eq_one := by
    rw [w0BornMeasure.top_eq_one]
    norm_num [w0Smoothstep]
  add_isOrtho A B hAB := by
    by_cases hA : A = ⊥
    · subst A
      simp [w0Smoothstep, w0BornMeasure.bot_eq_zero]
    by_cases hB : B = ⊥
    · subst B
      simp [w0Smoothstep, w0BornMeasure.bot_eq_zero]
    have htop : A ⊔ B = ⊤ := w0_sup_eq_top_of_isOrtho hA hB hAB
    have hp := w0BornMeasure.add_isOrtho A B hAB
    rw [htop, w0BornMeasure.top_eq_one] at hp
    change w0Smoothstep (w0BornMeasure.μ (A ⊔ B)) =
      w0Smoothstep (w0BornMeasure.μ A) + w0Smoothstep (w0BornMeasure.μ B)
    rw [htop, w0BornMeasure.top_eq_one]
    have hBcomp : w0BornMeasure.μ B = 1 - w0BornMeasure.μ A := by
      linarith [hp]
    rw [hBcomp]
    unfold w0Smoothstep
    ring

/-- Context-level weight induced by the dimension-two projection measure. -/
def w0Weight : Perspective 2 → Submodule ℂ (H 2) → ℝ :=
  fun _ c => w0NonBornMeasure.μ c

theorem w0Weight_axGrain : AxGrain w0Weight := by
  intro D' D hRefines c hc
  change w0NonBornMeasure.μ c =
    ∑ c' ∈ D'.cells.filter (· ≤ c), w0NonBornMeasure.μ c'
  have hsum := w0NonBornMeasure.sum_eq_of_pairwise_isOrtho
    (D'.cells.filter (· ≤ c)) id
    (fun c' hc' c'' hc'' hne =>
      D'.ortho c' (Finset.mem_filter.mp hc').1
        c'' (Finset.mem_filter.mp hc'').1 hne)
  have hsup := refine_filter_sup_eq D' D hRefines c hc
  rw [hsup] at hsum
  simpa using hsum

theorem w0Weight_axNorm : AxNorm w0Weight := by
  intro D
  have htop : D.cells.sup id = (⊤ : Submodule ℂ (H 2)) := by
    rw [Finset.sup_id_eq_sSup]
    exact D.span
  have hsum := w0NonBornMeasure.sum_eq_of_pairwise_isOrtho D.cells id
    (fun c hc c' hc' hne => D.ortho c hc c' hc' hne)
  rw [htop, w0NonBornMeasure.top_eq_one] at hsum
  simpa [w0Weight] using hsum.symm

theorem w0Weight_axPos : AxPos w0Weight := by
  intro D c hc
  exact w0NonBornMeasure.nonneg c

private theorem w0BornMeasure_eq_zero_of_orthogonal
    {c : Submodule ℂ (H 2)} (horth : w0e0 ∈ cᗮ) : w0BornMeasure.μ c = 0 := by
  have hp : c.starProjection w0e0 = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff c).mpr horth
  change ‖c.starProjection w0e0‖ ^ 2 = 0
  rw [hp]
  norm_num

theorem w0Weight_axNul : AxNul w0Weight w0e0 := by
  intro D c hc horth
  change w0Smoothstep (w0BornMeasure.μ c) = 0
  rw [w0BornMeasure_eq_zero_of_orthogonal horth]
  norm_num [w0Smoothstep]

/-- Oblique unit vector with Born probability `9/25` relative to `w0e0`. -/
def w0x : H 2 := (3 / 5 : ℂ) • w0e0 + (4 / 5 : ℂ) • w0e1

private theorem w0x_zero : w0x 0 = (3 / 5 : ℂ) := by
  norm_num [w0x, w0e0, w0e1,
    show (0 : Fin 2) ≠ (1 : Fin 2) by decide]

private theorem w0x_one : w0x 1 = (4 / 5 : ℂ) := by
  norm_num [w0x, w0e0, w0e1,
    show (1 : Fin 2) ≠ (0 : Fin 2) by decide]

theorem w0x_norm : ‖w0x‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, w0x_zero, w0x_one]
  norm_num

/-- The oblique line on which the deformed measure differs from Born. -/
def w0LineX : Submodule ℂ (H 2) := ℂ ∙ w0x

private theorem w0LineX_ne_bot : w0LineX ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  refine ⟨w0x, Submodule.mem_span_singleton_self _, ?_⟩
  exact norm_ne_zero_iff.mp (by rw [w0x_norm]; norm_num)

private theorem w0LineX_ne_top : w0LineX ≠ ⊤ := by
  intro htop
  have hxne : w0x ≠ 0 := norm_ne_zero_iff.mp (by rw [w0x_norm]; norm_num)
  have h1 : Module.finrank ℂ w0LineX = 1 := by
    unfold w0LineX
    exact finrank_span_singleton hxne
  rw [htop] at h1
  have h2 : Module.finrank ℂ (⊤ : Submodule ℂ (H 2)) = 2 := by
    rw [finrank_top]
    simp
  rw [h2] at h1
  omega

/-- Binary perspective containing the oblique line. -/
def w0Perspective : Perspective 2 :=
  Perspective.binary w0LineX w0LineX_ne_bot w0LineX_ne_top

private theorem w0LineX_mem_perspective : w0LineX ∈ w0Perspective.cells := by
  exact Finset.mem_insert_self _ _

private theorem inner_w0e0_w0x : ⟪w0e0, w0x⟫_ℂ = (3 / 5 : ℂ) := by
  unfold w0e0
  rw [EuclideanSpace.inner_single_left, w0x_zero]
  norm_num

private theorem inner_w0x_w0e0 : ⟪w0x, w0e0⟫_ℂ = (3 / 5 : ℂ) := by
  rw [show ⟪w0x, w0e0⟫_ℂ = starRingEnd ℂ ⟪w0e0, w0x⟫_ℂ from
    (inner_conj_symm w0x w0e0).symm]
  rw [inner_w0e0_w0x]
  simp only [starRingEnd_apply]
  norm_num

private theorem projL_w0LineX_w0e0_norm : ‖projL w0LineX w0e0‖ = 3 / 5 := by
  unfold w0LineX
  rw [QuantumFoundations.Uhlhorn.projL_singleton_unit w0x w0e0 w0x_norm,
    inner_w0x_w0e0, norm_smul, w0x_norm]
  norm_num

private theorem w0BornMeasure_lineX : w0BornMeasure.μ w0LineX = 9 / 25 := by
  change ‖projL w0LineX w0e0‖ ^ 2 = 9 / 25
  rw [projL_w0LineX_w0e0_norm]
  norm_num

private theorem w0NonBornMeasure_lineX :
    w0NonBornMeasure.μ w0LineX = 4617 / 15625 := by
  change w0Smoothstep (w0BornMeasure.μ w0LineX) = 4617 / 15625
  rw [w0BornMeasure_lineX]
  norm_num [w0Smoothstep]

private theorem w0Weight_not_born_on_lineX :
    w0Weight w0Perspective w0LineX ≠ ‖projL w0LineX w0e0‖ ^ 2 := by
  change w0NonBornMeasure.μ w0LineX ≠ ‖projL w0LineX w0e0‖ ^ 2
  rw [w0NonBornMeasure_lineX, projL_w0LineX_w0e0_norm]
  norm_num

/--
`W0`. The dimension hypothesis of the public grain-coherence theorem is sharp
at the first excluded dimension.  In `H 2`, all the other hypotheses hold for
`w0Weight` and the unit state `w0e0`, but the Born conclusion fails on the
explicit oblique line `w0LineX`.
-/
theorem w0_dimension_two_countermodel :
    ∃ (Est : Perspective 2 → Submodule ℂ (H 2) → ℝ) (v : H 2),
      ¬ 3 ≤ (2 : ℕ) ∧
      AxGrain Est ∧
      AxNorm Est ∧
      AxPos Est ∧
      ‖v‖ = 1 ∧
      AxNul Est v ∧
      ∃ (D : Perspective 2) (c : Submodule ℂ (H 2)),
        c ∈ D.cells ∧ Est D c ≠ ‖projL c v‖ ^ 2 := by
  refine ⟨w0Weight, w0e0, by norm_num,
    w0Weight_axGrain,
    w0Weight_axNorm,
    w0Weight_axPos,
    w0e0_norm,
    w0Weight_axNul,
    w0Perspective, w0LineX, w0LineX_mem_perspective,
    w0Weight_not_born_on_lineX⟩

end

end EverettianProbability.BornCalibration
