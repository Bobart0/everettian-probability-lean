import EverettianProbability.PhysicalRefinement.RecordNeutralWitness

/-!
**FR.** # Règle rivale à puissance quatrième renormalisée

Pour un état non nul, cette règle élève chaque poids de Born au carré puis
renormalise sur la perspective courante. La dépendance à la perspective du
dénominateur est intentionnelle. Elle permet `AxNorm`, mais elle n'est pas
compatible en général avec `AxGrain` ; ce second point est établi dans
`BornAgreement.lean`.

La normalisation est énoncée sous `v ≠ 0`. Sans cette condition, la formule
donne `0 / 0 = 0` dans ℝ et `AxNorm` serait fausse pour l'état nul.

**EN.** # Renormalized fourth-power rival rule

For a nonzero state, this rule squares each Born weight and renormalizes over
the current perspective. The dependence of the denominator on the perspective
is intentional. It gives `AxNorm`, but is not generally compatible with
`AxGrain`; the latter point is established in `BornAgreement.lean`.

Normalization is stated under `v ≠ 0`. Without that condition, the formula
has `0 / 0 = 0` in ℝ and `AxNorm` would be false for the zero state.
-/

namespace EverettianProbability.Rivals

open QuantumFoundations.BornRule
open QuantumFoundations.ProbabilityAPI
open Gleason
open scoped Classical

noncomputable def fourthPowerDenominator {n : ℕ} (v : H n) (D : Perspective n) : ℝ :=
  ∑ c ∈ D.cells, ‖projL c v‖ ^ 4

noncomputable def renormalizedFourthPower {n : ℕ} (v : H n) :
    Perspective n → Submodule ℂ (H n) → ℝ :=
  fun D c => ‖projL c v‖ ^ 4 / fourthPowerDenominator v D

private theorem projL_top_apply {n : ℕ} (v : H n) :
    projL (⊤ : Submodule ℂ (H n)) v = v := by
  have htop : projL (⊤ : Submodule ℂ (H n)) = LinearMap.id := by
    unfold projL
    rw [Submodule.starProjection_top]
    rfl
  rw [htop]
  rfl

private theorem fourthPowerDenominator_nonneg {n : ℕ} (v : H n) (D : Perspective n) :
    0 ≤ fourthPowerDenominator v D := by
  unfold fourthPowerDenominator
  exact Finset.sum_nonneg (by
    intro c hc
    positivity)

theorem fourthPowerDenominator_pos {n : ℕ} {v : H n} (hv : v ≠ 0) (D : Perspective n) :
    0 < fourthPowerDenominator v D := by
  unfold fourthPowerDenominator
  apply Finset.sum_pos'
  · intro c hc
    positivity
  · by_contra h
    have hzero : ∀ c ∈ D.cells, ‖projL c v‖ ^ 4 = 0 := by
      intro c hc
      apply le_antisymm
      · exact le_of_not_gt (fun hpos => h ⟨c, hc, hpos⟩)
      · positivity
    have hproj : ∀ c ∈ D.cells, projL c v = 0 := by
      intro c hc
      have hnot : ¬ 0 < ‖projL c v‖ := by
        intro hpos
        have hfour : 0 < ‖projL c v‖ ^ 4 := by positivity
        linarith [hzero c hc]
      have hnorm : ‖projL c v‖ = 0 :=
        le_antisymm (le_of_not_gt hnot) (norm_nonneg _)
      exact norm_eq_zero.mp hnorm
    have hpyth := QuantumFoundations.BornRule.sum_sq_projL_of_pairwise_isOrtho
      D.cells D.ortho v
    have htop : D.cells.sup id = (⊤ : Submodule ℂ (H n)) := by
      rw [Finset.sup_id_eq_sSup]
      exact D.span
    rw [htop, projL_top_apply] at hpyth
    have hsum : (∑ c ∈ D.cells, ‖projL c v‖ ^ 2) = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg (by
        intro c hc
        positivity)).mpr
      intro c hc
      rw [hproj c hc, norm_zero]
      norm_num
    rw [hsum] at hpyth
    have hnorm : ‖v‖ = 0 := by
      nlinarith [norm_nonneg v, hpyth]
    exact hv (norm_eq_zero.mp hnorm)

theorem renormalizedFourthPower_axPos {n : ℕ} {v : H n} (hv : v ≠ 0) :
    AxPos (renormalizedFourthPower v) := by
  intro D c hc
  unfold renormalizedFourthPower
  exact div_nonneg (by positivity) (le_of_lt (fourthPowerDenominator_pos hv D))

theorem renormalizedFourthPower_axNorm {n : ℕ} {v : H n} (hv : v ≠ 0) :
    AxNorm (renormalizedFourthPower v) := by
  intro D
  unfold renormalizedFourthPower
  rw [← Finset.sum_div]
  unfold fourthPowerDenominator
  exact div_self (ne_of_gt (fourthPowerDenominator_pos hv D))

end EverettianProbability.Rivals
