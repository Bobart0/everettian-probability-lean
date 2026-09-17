import EverettianProbability.Rivals.RenormalizedFourthPower

/-!
**FR.** # Accord exact avec Born

Ce module fixe une perspective et caractérise exactement quand la règle à
puissance quatrième renormalisée coïncide cellule par cellule avec la règle de
Born. Pour un état unitaire, l'accord équivaut à l'égalité des poids de Born
sur les cellules de poids non nul.

Il contient aussi le témoin de violation de `AxGrain` demandé pour la règle
renormalisée : sur la perspective binaire et son raffinement en trois lignes,
le poids de `label0Line` change parce que les dénominateurs dépendent de la
perspective.

**EN.** # Exact agreement with Born

This module fixes a perspective and exactly characterizes when the normalized
fourth-power rule agrees cell by cell with the Born rule. For a unit state,
agreement is equivalent to equality of the Born weights on the nonzero-weight
cells.

It also contains the requested `AxGrain` violation witness for the
renormalized rule: on the binary perspective and its three-line refinement,
the weight of `label0Line` changes because the denominators depend on the
perspective.
-/

namespace EverettianProbability.Rivals

open QuantumFoundations.BornRule
open QuantumFoundations.ProbabilityAPI
open Gleason
open EverettianProbability.PhysicalRefinement
open scoped Classical

noncomputable def bornWeight {n : ℕ} (v : H n) :
    Perspective n → Submodule ℂ (H n) → ℝ :=
  fun _ c => ‖projL c v‖ ^ 2

private theorem bornWeight_nonneg {n : ℕ} (v : H n) (D : Perspective n)
    (c : Submodule ℂ (H n)) :
    0 ≤ bornWeight v D c := by
  unfold bornWeight
  positivity

private theorem fourth_eq_born_sq {n : ℕ} (v : H n) (D : Perspective n)
    (c : Submodule ℂ (H n)) :
    ‖projL c v‖ ^ 4 = bornWeight v D c ^ 2 := by
  unfold bornWeight
  ring

private theorem bornWeight_sum_eq_one {n : ℕ} {v : H n} (hv : ‖v‖ = 1)
    (D : Perspective n) :
    ∑ c ∈ D.cells, bornWeight v D c = 1 := by
  have hpyth := QuantumFoundations.BornRule.sum_sq_projL_of_pairwise_isOrtho
    D.cells D.ortho v
  have htop : D.cells.sup id = (⊤ : Submodule ℂ (H n)) := by
    rw [Finset.sup_id_eq_sSup]
    exact D.span
  have hid : projL (⊤ : Submodule ℂ (H n)) = LinearMap.id := by
    unfold projL
    rw [Submodule.starProjection_top]
    rfl
  rw [htop, hid] at hpyth
  simp only [LinearMap.id_coe, id_eq, hv, one_pow] at hpyth
  exact hpyth.symm

theorem renormalizedFourthPower_agrees_iff {n : ℕ} {v : H n} (hv : ‖v‖ = 1)
    (D : Perspective n) :
    (∀ c ∈ D.cells,
      renormalizedFourthPower v D c = bornWeight v D c) ↔
    (∀ c₁ ∈ D.cells, ∀ c₂ ∈ D.cells,
      bornWeight v D c₁ ≠ 0 → bornWeight v D c₂ ≠ 0 →
        bornWeight v D c₁ = bornWeight v D c₂) := by
  have hv0 : v ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hv
    norm_num at hv
  have hden : 0 < fourthPowerDenominator v D :=
    fourthPowerDenominator_pos hv0 D
  constructor
  · intro hagree c₁ hc₁ c₂ hc₂ hne₁ hne₂
    have hpositive : ∀ c ∈ D.cells, bornWeight v D c ≠ 0 →
        0 < bornWeight v D c := by
      intro c hc hne
      exact lt_of_le_of_ne (bornWeight_nonneg v D c) (Ne.symm hne)
    have hto_den : ∀ c ∈ D.cells, bornWeight v D c ≠ 0 →
        bornWeight v D c = fourthPowerDenominator v D := by
      intro c hc hne
      have hscalar :
          bornWeight v D c ^ 2 / fourthPowerDenominator v D =
            bornWeight v D c := by
        simpa only [renormalizedFourthPower, fourth_eq_born_sq v D c] using
          hagree c hc
      have hmul := (div_eq_iff (ne_of_gt hden)).mp hscalar
      nlinarith [hmul, hpositive c hc hne]
    exact (hto_den c₁ hc₁ hne₁).trans (hto_den c₂ hc₂ hne₂).symm
  · intro hequal c hc
    by_cases hzero : bornWeight v D c = 0
    · have hnorm : ‖projL c v‖ = 0 := by
        unfold bornWeight at hzero
        have hnonneg := norm_nonneg (projL c v)
        nlinarith
      simp [renormalizedFourthPower, hnorm, hzero]
    · have hterm : ∀ d ∈ D.cells,
          bornWeight v D d ^ 2 = bornWeight v D c * bornWeight v D d := by
        intro d hd
        by_cases hd_zero : bornWeight v D d = 0
        · simp [hd_zero]
        · have hdc := hequal d hd c hc hd_zero hzero
          rw [hdc]
          ring
      have hden_eq : fourthPowerDenominator v D = bornWeight v D c := by
        calc
          fourthPowerDenominator v D =
              ∑ d ∈ D.cells, bornWeight v D d ^ 2 := by
            unfold fourthPowerDenominator
            apply Finset.sum_congr rfl
            intro d hd
            exact fourth_eq_born_sq v D d
          _ = ∑ d ∈ D.cells, bornWeight v D c * bornWeight v D d := by
            apply Finset.sum_congr rfl
            intro d hd
            exact hterm d hd
          _ = bornWeight v D c * ∑ d ∈ D.cells, bornWeight v D d := by
            rw [Finset.mul_sum]
          _ = bornWeight v D c := by
            rw [bornWeight_sum_eq_one hv D]
            ring
      rw [renormalizedFourthPower, fourth_eq_born_sq v D c, hden_eq]
      field_simp [hzero]

theorem renormalizedFourthPower_not_axGrain :
    ¬ AxGrain (renormalizedFourthPower psiAfter) := by
  intro hgrain
  have h := hgrain finePerspective coarsePerspective recordNeutral_refines
    label0Line (by
      rw [coarsePerspective_cells_eq]
      simp)
  have hfilter :
      finePerspective.cells.filter (· ≤ label0Line) = {label0Line} := by
    unfold finePerspective QuantumFoundations.BornRule.basisPerspective
    ext c
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨i, rfl⟩, hle⟩
      fin_cases i
      · rfl
      · exfalso
        have hperp : (ℂ ∙ (b 1 : H 3)) ≤ label0Lineᗮ := by
          simpa [anc0Line, label1Space] using anc0Line_le_label1Space
        have hbot : (ℂ ∙ (b 1 : H 3)) = (⊥ : Submodule ℂ (H 3)) := by
          rw [Submodule.eq_bot_iff]
          intro x hx
          have hx0 : x ∈ label0Line := hle hx
          have hxperp : x ∈ label0Lineᗮ := hperp hx
          exact inner_self_eq_zero.mp
            ((Submodule.mem_orthogonal label0Line x).mp hxperp x hx0)
        exact (QuantumFoundations.BornRule.line_ne_bot b 1 hbot).elim
      · exfalso
        have hperp : (ℂ ∙ (b 2 : H 3)) ≤ label0Lineᗮ := by
          simpa [anc1Line, label1Space] using anc1Line_le_label1Space
        have hbot : (ℂ ∙ (b 2 : H 3)) = (⊥ : Submodule ℂ (H 3)) := by
          rw [Submodule.eq_bot_iff]
          intro x hx
          have hx0 : x ∈ label0Line := hle hx
          have hxperp : x ∈ label0Lineᗮ := hperp hx
          exact inner_self_eq_zero.mp
            ((Submodule.mem_orthogonal label0Line x).mp hxperp x hx0)
        exact (QuantumFoundations.BornRule.line_ne_bot b 2 hbot).elim
    · intro hc
      subst c
      exact ⟨⟨0, rfl⟩, le_refl _⟩
  rw [hfilter] at h
  rw [Finset.sum_singleton] at h
  have hlabel0_fourth : ‖projL label0Line psiAfter‖ ^ 4 = (81 / 625 : ℝ) := by
    calc
      ‖projL label0Line psiAfter‖ ^ 4 =
          (‖projL label0Line psiAfter‖ ^ 2) ^ 2 := by ring
      _ = (81 / 625 : ℝ) := by rw [weight_label0_after]; norm_num
  have hlabel1_fourth : ‖projL label1Space psiAfter‖ ^ 4 = (256 / 625 : ℝ) := by
    calc
      ‖projL label1Space psiAfter‖ ^ 4 =
          (‖projL label1Space psiAfter‖ ^ 2) ^ 2 := by ring
      _ = (256 / 625 : ℝ) := by rw [weight_label1Space_after]; norm_num
  have hanc0_fourth : ‖projL anc0Line psiAfter‖ ^ 4 = (20736 / 390625 : ℝ) := by
    calc
      ‖projL anc0Line psiAfter‖ ^ 4 =
          (‖projL anc0Line psiAfter‖ ^ 2) ^ 2 := by ring
      _ = (20736 / 390625 : ℝ) := by rw [weight_anc0_after]; norm_num
  have hanc1_fourth : ‖projL anc1Line psiAfter‖ ^ 4 = (65536 / 390625 : ℝ) := by
    calc
      ‖projL anc1Line psiAfter‖ ^ 4 =
          (‖projL anc1Line psiAfter‖ ^ 2) ^ 2 := by ring
      _ = (65536 / 390625 : ℝ) := by rw [weight_anc1_after]; norm_num
  have hcoarse : fourthPowerDenominator psiAfter coarsePerspective =
      (337 / 625 : ℝ) := by
    unfold fourthPowerDenominator
    rw [coarsePerspective_cells_eq, Finset.sum_insert,
      Finset.sum_singleton, hlabel0_fourth, hlabel1_fourth]
    · norm_num
    · simpa using label0Line_ne_label1Space
  have hfine : fourthPowerDenominator psiAfter finePerspective =
      (136897 / 390625 : ℝ) := by
    unfold fourthPowerDenominator finePerspective QuantumFoundations.BornRule.basisPerspective
    rw [Finset.sum_image (QuantumFoundations.BornRule.line_injective b)]
    rw [Fin.sum_univ_three]
    change ‖projL label0Line psiAfter‖ ^ 4 +
      ‖projL anc0Line psiAfter‖ ^ 4 +
      ‖projL anc1Line psiAfter‖ ^ 4 = _
    rw [hlabel0_fourth, hanc0_fourth, hanc1_fourth]
    norm_num
  simp only [renormalizedFourthPower] at h
  rw [hcoarse, hfine, hlabel0_fourth] at h
  field_simp at h
  norm_num at h

end EverettianProbability.Rivals
