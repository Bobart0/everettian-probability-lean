import EverettianProbability.Rivals.SupportAgreement
import EverettianProbability.Rivals.Nonvacuity

/-!
**FR.** # Taux de discrimination

Pour un état unitaire et une perspective fixée, ce module définit le
log-facteur de Bayes moyen par observation sous chacune des deux règles : la
règle de Born et la règle à puissance quatrième renormalisée. Les
vraisemblances restent propres à chaque hypothèse. L'égalité des supports
établie dans `Rivals.SupportAgreement` rend les rapports bien définis même
avec la convention de Lean `0 / 0 = 0`.

Les résultats sont conditionnels au principe CW de Greaves--Myrvold ; ils ne
formalisent ni n'établissent ce principe.

**EN.** # Discrimination rate

For a unit state and a fixed perspective, this module defines the expected
log Bayes factor per observation under each rule: the Born rule and the
renormalized fourth-power rule. The likelihoods remain hypothesis-specific.
The support equality established in `Rivals.SupportAgreement` makes the
ratios well-defined even with Lean's convention `0 / 0 = 0`.

The results are conditional on Greaves--Myrvold's CW principle; they neither
formalize nor establish that principle.
-/

namespace EverettianProbability.Confirmation

open QuantumFoundations.BornRule
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Rivals
open Gleason
open scoped Classical

noncomputable def bornDiscriminationRate {n : ℕ} (v : H n) (D : Perspective n) : ℝ :=
  ∑ c ∈ D.cells,
    bornWeight v D c * Real.log (bornWeight v D c / renormalizedFourthPower v D c)

noncomputable def rivalDiscriminationRate {n : ℕ} (v : H n) (D : Perspective n) : ℝ :=
  ∑ c ∈ D.cells,
    renormalizedFourthPower v D c *
      Real.log (renormalizedFourthPower v D c / bornWeight v D c)

private theorem bornWeight_sum_eq_one
    {n : ℕ} {v : H n} (hv : ‖v‖ = 1) (D : Perspective n) :
    ∑ c ∈ D.cells, bornWeight v D c = 1 := by
  have hnorm := QuantumFoundations.BornRule.E₀_isNorm v hv
  change AxNorm (QuantumFoundations.BornRule.E₀ v) at hnorm
  exact hnorm D

private theorem rivalWeight_sum_eq_one
    {n : ℕ} {v : H n} (hv : ‖v‖ = 1) (D : Perspective n) :
    ∑ c ∈ D.cells, renormalizedFourthPower v D c = 1 := by
  have hv0 : v ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hv
    norm_num at hv
  exact renormalizedFourthPower_axNorm hv0 D

private theorem finite_gibbs_gap_nonneg
    {n : ℕ} (D : Perspective n)
    (b r : Submodule ℂ (H n) → ℝ)
    (hb : ∀ c ∈ D.cells, 0 ≤ b c)
    (hr : ∀ c ∈ D.cells, 0 ≤ r c)
    (hsupport : ∀ c ∈ D.cells, r c = 0 ↔ b c = 0) :
    ∀ c ∈ D.cells,
      0 ≤ b c * Real.log (b c / r c) - (b c - r c) := by
  intro c hc
  by_cases hbzero : b c = 0
  · have hrzero : r c = 0 := (hsupport c hc).mpr hbzero
    simp [hbzero, hrzero]
  · have hbpos : 0 < b c := lt_of_le_of_ne (hb c hc) (Ne.symm hbzero)
    have hrne : r c ≠ 0 := by
      intro hzero
      exact hbzero ((hsupport c hc).mp hzero)
    have hrpos : 0 < r c := lt_of_le_of_ne (hr c hc) (Ne.symm hrne)
    have hx : 0 ≤ b c / r c := le_of_lt (div_pos hbpos hrpos)
    have hkl : 0 ≤ InformationTheory.klFun (b c / r c) :=
      InformationTheory.klFun_nonneg hx
    have hidentity :
        b c * Real.log (b c / r c) - (b c - r c) =
          r c * InformationTheory.klFun (b c / r c) := by
      unfold InformationTheory.klFun
      field_simp [ne_of_gt hbpos, ne_of_gt hrpos]
      ring
    rw [hidentity]
    exact mul_nonneg (le_of_lt hrpos) hkl

private theorem finite_gibbs_gap_eq_zero_iff
    {n : ℕ} (D : Perspective n)
    (b r : Submodule ℂ (H n) → ℝ)
    (hb : ∀ c ∈ D.cells, 0 ≤ b c)
    (hr : ∀ c ∈ D.cells, 0 ≤ r c)
    (hsupport : ∀ c ∈ D.cells, r c = 0 ↔ b c = 0)
    {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
    b c * Real.log (b c / r c) - (b c - r c) = 0 ↔ b c = r c := by
  by_cases hbzero : b c = 0
  · have hrzero : r c = 0 := (hsupport c hc).mpr hbzero
    simp [hbzero, hrzero]
  · have hbpos : 0 < b c := lt_of_le_of_ne (hb c hc) (Ne.symm hbzero)
    have hrne : r c ≠ 0 := by
      intro hzero
      exact hbzero ((hsupport c hc).mp hzero)
    have hrpos : 0 < r c := lt_of_le_of_ne (hr c hc) (Ne.symm hrne)
    have hx : 0 ≤ b c / r c := le_of_lt (div_pos hbpos hrpos)
    have hidentity :
        b c * Real.log (b c / r c) - (b c - r c) =
          r c * InformationTheory.klFun (b c / r c) := by
      unfold InformationTheory.klFun
      field_simp [ne_of_gt hbpos, ne_of_gt hrpos]
      ring
    rw [hidentity]
    constructor
    · intro hzero
      have hkl : InformationTheory.klFun (b c / r c) = 0 := by
        rcases mul_eq_zero.mp hzero with hrzero | hkl
        · exact (hrne hrzero).elim
        · exact hkl
      have hratio : b c / r c = 1 :=
        (InformationTheory.klFun_eq_zero_iff hx).mp hkl
      have hmul : b c = 1 * r c := (div_eq_iff hrne).mp hratio
      simpa using hmul
    · intro hbr
      rw [hbr, div_self hrne]
      simp [InformationTheory.klFun]

private theorem finite_gibbs_nonneg
    {n : ℕ} (D : Perspective n)
    (b r : Submodule ℂ (H n) → ℝ)
    (hb : ∀ c ∈ D.cells, 0 ≤ b c)
    (hr : ∀ c ∈ D.cells, 0 ≤ r c)
    (hbsum : ∑ c ∈ D.cells, b c = 1)
    (hrsum : ∑ c ∈ D.cells, r c = 1)
    (hsupport : ∀ c ∈ D.cells, r c = 0 ↔ b c = 0) :
    0 ≤ ∑ c ∈ D.cells, b c * Real.log (b c / r c) := by
  have hgap :
      0 ≤ ∑ c ∈ D.cells,
        (b c * Real.log (b c / r c) - (b c - r c)) := by
    apply Finset.sum_nonneg
    intro c hc
    exact finite_gibbs_gap_nonneg D b r hb hr hsupport c hc
  have hdiff : (∑ c ∈ D.cells, (b c - r c)) = 0 := by
    rw [Finset.sum_sub_distrib, hbsum, hrsum]
    ring
  rw [Finset.sum_sub_distrib, hdiff] at hgap
  simpa using hgap

private theorem finite_gibbs_eq_zero_iff
    {n : ℕ} (D : Perspective n)
    (b r : Submodule ℂ (H n) → ℝ)
    (hb : ∀ c ∈ D.cells, 0 ≤ b c)
    (hr : ∀ c ∈ D.cells, 0 ≤ r c)
    (hbsum : ∑ c ∈ D.cells, b c = 1)
    (hrsum : ∑ c ∈ D.cells, r c = 1)
    (hsupport : ∀ c ∈ D.cells, r c = 0 ↔ b c = 0) :
    (∑ c ∈ D.cells, b c * Real.log (b c / r c) = 0) ↔
      (∀ c ∈ D.cells, b c = r c) := by
  constructor
  · intro hzero c hc
    have hgap_nonneg : ∀ d ∈ D.cells,
        0 ≤ b d * Real.log (b d / r d) - (b d - r d) :=
      finite_gibbs_gap_nonneg D b r hb hr hsupport
    have hdiff : (∑ d ∈ D.cells, (b d - r d)) = 0 := by
      rw [Finset.sum_sub_distrib, hbsum, hrsum]
      ring
    have hgap_sum :
        (∑ d ∈ D.cells,
          (b d * Real.log (b d / r d) - (b d - r d))) = 0 := by
      rw [Finset.sum_sub_distrib, hdiff]
      simpa using hzero
    have hgap :
        b c * Real.log (b c / r c) - (b c - r c) = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun d hd => hgap_nonneg d hd)).mp hgap_sum c hc
    exact (finite_gibbs_gap_eq_zero_iff D b r hb hr hsupport hc).mp hgap
  · intro hagree
    apply le_antisymm
    · have hsum : (∑ c ∈ D.cells, b c * Real.log (b c / r c)) = 0 := by
        apply Finset.sum_eq_zero
        intro c hc
        rw [hagree c hc]
        simp
      exact hsum.le
    · exact finite_gibbs_nonneg D b r hb hr hbsum hrsum hsupport

theorem bornDiscriminationRate_nonneg
    {n : ℕ} {v : H n} (hv : ‖v‖ = 1) (D : Perspective n) :
    0 ≤ bornDiscriminationRate v D := by
  unfold bornDiscriminationRate
  apply finite_gibbs_nonneg D (bornWeight v D) (renormalizedFourthPower v D)
  · intro c hc
    unfold bornWeight
    positivity
  · intro c hc
    exact renormalizedFourthPower_axPos
      (by
        intro hzero
        rw [hzero, norm_zero] at hv
        norm_num at hv) D c hc
  · exact bornWeight_sum_eq_one hv D
  · exact rivalWeight_sum_eq_one hv D
  · intro c hc
    exact renormalizedFourthPower_eq_zero_iff_bornWeight_eq_zero
      (by
        intro hzero
        rw [hzero, norm_zero] at hv
        norm_num at hv) D (c := c) hc

theorem rivalDiscriminationRate_nonneg
    {n : ℕ} {v : H n} (hv : ‖v‖ = 1) (D : Perspective n) :
    0 ≤ rivalDiscriminationRate v D := by
  unfold rivalDiscriminationRate
  apply finite_gibbs_nonneg D (renormalizedFourthPower v D) (bornWeight v D)
  · intro c hc
    exact renormalizedFourthPower_axPos
      (by
        intro hzero
        rw [hzero, norm_zero] at hv
        norm_num at hv) D c hc
  · intro c hc
    unfold bornWeight
    positivity
  · exact rivalWeight_sum_eq_one hv D
  · exact bornWeight_sum_eq_one hv D
  · intro c hc
    have hzero := renormalizedFourthPower_eq_zero_iff_bornWeight_eq_zero (v := v)
      (by
        intro hzero
        rw [hzero, norm_zero] at hv
        norm_num at hv) D (c := c) hc
    exact hzero.symm

theorem bornDiscriminationRate_eq_zero_iff
    {n : ℕ} {v : H n} (hv : ‖v‖ = 1) (D : Perspective n) :
    bornDiscriminationRate v D = 0 ↔
      ∀ c ∈ D.cells, bornWeight v D c = renormalizedFourthPower v D c := by
  unfold bornDiscriminationRate
  exact finite_gibbs_eq_zero_iff D (bornWeight v D)
    (renormalizedFourthPower v D)
    (by intro c hc; unfold bornWeight; positivity)
    (by
      intro c hc
      exact renormalizedFourthPower_axPos
        (by
          intro hzero
          rw [hzero, norm_zero] at hv
          norm_num at hv) D c hc)
    (bornWeight_sum_eq_one hv D) (rivalWeight_sum_eq_one hv D)
    (by
      intro c hc
      exact renormalizedFourthPower_eq_zero_iff_bornWeight_eq_zero
        (by
          intro hzero
          rw [hzero, norm_zero] at hv
          norm_num at hv) D hc)

theorem rivalDiscriminationRate_eq_zero_iff
    {n : ℕ} {v : H n} (hv : ‖v‖ = 1) (D : Perspective n) :
    rivalDiscriminationRate v D = 0 ↔
      ∀ c ∈ D.cells, renormalizedFourthPower v D c = bornWeight v D c := by
  unfold rivalDiscriminationRate
  exact finite_gibbs_eq_zero_iff D (renormalizedFourthPower v D)
    (bornWeight v D)
    (by
      intro c hc
      exact renormalizedFourthPower_axPos
        (by
          intro hzero
          rw [hzero, norm_zero] at hv
          norm_num at hv) D c hc)
    (by intro c hc; unfold bornWeight; positivity)
    (rivalWeight_sum_eq_one hv D) (bornWeight_sum_eq_one hv D)
    (by
      intro c hc
      have hzero := renormalizedFourthPower_eq_zero_iff_bornWeight_eq_zero (v := v)
        (by
          intro hzero
          rw [hzero, norm_zero] at hv
          norm_num at hv) D (c := c) hc
      exact hzero.symm)

theorem bornDiscriminationRate_eq_zero_iff_bornAgreement
    {n : ℕ} {v : H n} (hv : ‖v‖ = 1) (D : Perspective n) :
    bornDiscriminationRate v D = 0 ↔
      ∀ c₁ ∈ D.cells, ∀ c₂ ∈ D.cells,
        bornWeight v D c₁ ≠ 0 → bornWeight v D c₂ ≠ 0 →
          bornWeight v D c₁ = bornWeight v D c₂ := by
  constructor
  · intro hrate
    apply (renormalizedFourthPower_agrees_iff hv D).mp
    intro c hc
    exact ((bornDiscriminationRate_eq_zero_iff hv D).mp hrate c hc).symm
  · intro hagree
    apply (bornDiscriminationRate_eq_zero_iff hv D).mpr
    intro c hc
    exact ((renormalizedFourthPower_agrees_iff hv D).mpr hagree c hc).symm

open EverettianProbability.PhysicalRefinement

private theorem coarse_rival_label1_eq :
    renormalizedFourthPower psiAfter coarsePerspective label1Space =
      (256 / 337 : ℝ) := by
  have hlabel0_fourth : ‖projL label0Line psiAfter‖ ^ 4 = (81 / 625 : ℝ) := by
    calc
      ‖projL label0Line psiAfter‖ ^ 4 =
          (‖projL label0Line psiAfter‖ ^ 2) ^ 2 := by ring
      _ = (9 / 25 : ℝ) ^ 2 := by rw [weight_label0_after]
      _ = 81 / 625 := by norm_num
  have hlabel1_fourth : ‖projL label1Space psiAfter‖ ^ 4 = (256 / 625 : ℝ) := by
    calc
      ‖projL label1Space psiAfter‖ ^ 4 =
          (‖projL label1Space psiAfter‖ ^ 2) ^ 2 := by ring
      _ = (16 / 25 : ℝ) ^ 2 := by rw [weight_label1Space_after]
      _ = 256 / 625 := by norm_num
  have hden : fourthPowerDenominator psiAfter coarsePerspective = (337 / 625 : ℝ) := by
    unfold fourthPowerDenominator
    rw [coarsePerspective_cells_eq,
      Finset.sum_insert (by simpa using label0Line_ne_label1Space),
      Finset.sum_singleton, hlabel0_fourth, hlabel1_fourth]
    norm_num
  unfold renormalizedFourthPower
  rw [hden, hlabel1_fourth]
  norm_num

theorem coarse_bornDiscriminationRate_eq :
    bornDiscriminationRate psiAfter coarsePerspective =
      (9 / 25 : ℝ) * Real.log (337 / 225) +
        (16 / 25 : ℝ) * Real.log (337 / 400) := by
  have hzero := renormalizedFourthPower_disagreement_witness.1
  have hone := coarse_rival_label1_eq
  unfold bornDiscriminationRate
  rw [coarsePerspective_cells_eq,
    Finset.sum_insert (by simpa using label0Line_ne_label1Space),
    Finset.sum_singleton]
  · dsimp [bornWeight]
    rw [weight_label0_after, weight_label1Space_after, hzero, hone]
    norm_num

theorem coarse_bornDiscriminationRate_pos :
    0 < bornDiscriminationRate psiAfter coarsePerspective := by
  have hne : bornDiscriminationRate psiAfter coarsePerspective ≠ 0 := by
    intro hzero
    have hagree := (bornDiscriminationRate_eq_zero_iff
      psiAfter_norm coarsePerspective).mp hzero
    have hcell := hagree label0Line (by
      rw [coarsePerspective_cells_eq]
      simp)
    have hw := renormalizedFourthPower_disagreement_witness
    rw [hw.1, hw.2.1] at hcell
    norm_num at hcell
  exact lt_of_le_of_ne
    (bornDiscriminationRate_nonneg psiAfter_norm coarsePerspective)
    (Ne.symm hne)

/-
**FR.** Valeur indicative externe, non vérifiée par le noyau : l'expression
ci-dessus vaut approximativement `0.0357494754`; le nombre d'observations associé
à un log-facteur de Bayes donné dépend du seuil choisi. Aucune approximation
logarithmique n'est un théorème de ce module. E3.6, qui demanderait une loi
produit sur les suites, reste donc hors de portée de cet incrément.

**EN.** External, kernel-unverified indicative value: the expression above is
approximately `0.0357494754`; the corresponding number of observations depends
on the chosen log-Bayes-factor threshold. No logarithmic approximation is a
theorem of this module. E3.6, which would require a product law on sequences,
therefore remains outside this increment.
-/

end EverettianProbability.Confirmation
