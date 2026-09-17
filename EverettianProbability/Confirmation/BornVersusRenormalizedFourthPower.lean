import EverettianProbability.Confirmation.BatchPosteriorOdds
import EverettianProbability.Rivals.Nonvacuity

/-!
**FR.** # Born contre la puissance quatrieme renormalisee

Ce module construit le modele bayesien fini a deux hypotheses demande pour
E2. Les deux hypotheses fournissent leurs propres vraisemblances : Born
utilise `bornWeight`, tandis que la rivale utilise
`renormalizedFourthPower`. Le modele est conditionne par le principe CW de
Greaves--Myrvold ; il ne l'etablit pas.

E2.3a est l'enonce fort : sous l'accord exact de `BornAgreement.lean`, les
vraisemblances coincident sur toute cellule, et les produits, contributions
d'evidence et poids posterieurs coincident pour toute liste, y compris en
presence de vraisemblances nulles. E2.3b ajoute seulement la non-nullite
necessaire pour donner un sens aux divisions bayesiennes ; cette hypothese
est une condition de definition du conditionnement, non un affaiblissement
de E2.3a.
E2.3c est illimite lorsque toute cellule de la perspective a un poids non nul;
le temoin singleton `agreementPerspective` suffit comme illustration.

**EN.** # Born versus renormalized fourth power

This module builds the finite two-hypothesis Bayesian model requested for E2.
The two hypotheses provide their own likelihoods: Born uses `bornWeight`,
while the rival uses `renormalizedFourthPower`. The model is conditional on
the Greaves--Myrvold CW principle; it does not establish that principle.

E2.3a is the strong statement: under the exact agreement condition from
`BornAgreement.lean`, likelihoods agree on every cell, and products, evidence
contributions, and posterior weights agree for every list, including lists
containing zero likelihoods. E2.3b adds only the nonzero condition needed to
give Bayesian divisions their usual meaning; this is a condition for defining
conditioning, not a weakening of E2.3a.
E2.3c is unrestricted when every cell of the perspective has nonzero weight;
the singleton witness `agreementPerspective` is sufficient as an illustration.
-/

namespace EverettianProbability.Confirmation

open QuantumFoundations.BornRule
open QuantumFoundations.ProbabilityAPI
open Gleason
open EverettianProbability.Rivals
open EverettianProbability.PhysicalRefinement
open scoped Classical BigOperators

noncomputable section

abbrev BornVersusRenormalizedFourthPowerHypothesis := Fin 2

def bornHypothesis : BornVersusRenormalizedFourthPowerHypothesis := 0

def renormalizedFourthPowerHypothesis :
    BornVersusRenormalizedFourthPowerHypothesis := 1

abbrev BornVersusRenormalizedFourthPowerObservation
    {n : ℕ} (D : Perspective n) := {c : Submodule ℂ (H n) // c ∈ D.cells}

def bornVersusRenormalizedFourthPowerPrior
    (_ : BornVersusRenormalizedFourthPowerHypothesis) : ℝ :=
  1 / 2

theorem bornVersusRenormalizedFourthPowerPrior_nonneg
    (θ : BornVersusRenormalizedFourthPowerHypothesis) :
    0 ≤ bornVersusRenormalizedFourthPowerPrior θ := by
  norm_num [bornVersusRenormalizedFourthPowerPrior]

theorem bornVersusRenormalizedFourthPowerPrior_sum_eq_one :
    (∑ θ : BornVersusRenormalizedFourthPowerHypothesis,
      bornVersusRenormalizedFourthPowerPrior θ) = 1 := by
  rw [Fin.sum_univ_two]
  norm_num [bornVersusRenormalizedFourthPowerPrior]

def bornVersusRenormalizedFourthPowerLikelihood
    {n : ℕ} (v : H n) (D : Perspective n)
    (θ : BornVersusRenormalizedFourthPowerHypothesis)
    (c : BornVersusRenormalizedFourthPowerObservation D) : ℝ :=
  if θ = bornHypothesis then
    bornWeight v D c.1
  else
    renormalizedFourthPower v D c.1

private theorem bornWeight_sum_subtype_eq_one
    {n : ℕ} {v : H n} (hv : ‖v‖ = 1) (D : Perspective n) :
    (∑ c : BornVersusRenormalizedFourthPowerObservation D,
      bornWeight v D c.1) = 1 := by
  have hnorm := QuantumFoundations.BornRule.E₀_isNorm v hv
  change AxNorm (QuantumFoundations.BornRule.E₀ v) at hnorm
  calc
    (∑ c : BornVersusRenormalizedFourthPowerObservation D,
        bornWeight v D c.1) = ∑ c ∈ D.cells, bornWeight v D c := by
      symm
      exact Finset.sum_subtype D.cells (fun c => Iff.rfl)
        (fun c => bornWeight v D c)
    _ = 1 := hnorm D

private theorem renormalizedFourthPower_sum_subtype_eq_one
    {n : ℕ} {v : H n} (hv : ‖v‖ = 1) (D : Perspective n) :
    (∑ c : BornVersusRenormalizedFourthPowerObservation D,
      renormalizedFourthPower v D c.1) = 1 := by
  have hv0 : v ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hv
    norm_num at hv
  have hnorm := renormalizedFourthPower_axNorm hv0 D
  calc
    (∑ c : BornVersusRenormalizedFourthPowerObservation D,
        renormalizedFourthPower v D c.1) =
        ∑ c ∈ D.cells, renormalizedFourthPower v D c := by
      symm
      exact Finset.sum_subtype D.cells (fun c => Iff.rfl)
        (fun c => renormalizedFourthPower v D c)
    _ = 1 := hnorm

private theorem bornVersusRenormalizedFourthPowerLikelihood_nonneg
    {n : ℕ} {v : H n} (hv : ‖v‖ = 1) (D : Perspective n)
    (θ : BornVersusRenormalizedFourthPowerHypothesis)
    (c : BornVersusRenormalizedFourthPowerObservation D) :
    0 ≤ bornVersusRenormalizedFourthPowerLikelihood v D θ c := by
  by_cases hθ : θ = bornHypothesis
  · subst θ
    unfold bornVersusRenormalizedFourthPowerLikelihood bornWeight
    exact sq_nonneg _
  · have hθ' : θ ≠ bornHypothesis := hθ
    rw [show bornVersusRenormalizedFourthPowerLikelihood v D θ c =
        renormalizedFourthPower v D c.1 by
      unfold bornVersusRenormalizedFourthPowerLikelihood
      simp [hθ']]
    have hv0 : v ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hv
      norm_num at hv
    exact renormalizedFourthPower_axPos hv0 D c.1 c.2

private theorem bornVersusRenormalizedFourthPowerLikelihood_sum_eq_one
    {n : ℕ} {v : H n} (hv : ‖v‖ = 1) (D : Perspective n)
    (θ : BornVersusRenormalizedFourthPowerHypothesis) :
    (∑ c : BornVersusRenormalizedFourthPowerObservation D,
      bornVersusRenormalizedFourthPowerLikelihood v D θ c) = 1 := by
  by_cases hθ : θ = bornHypothesis
  · subst θ
    exact bornWeight_sum_subtype_eq_one hv D
  · have hθ' : θ ≠ bornHypothesis := hθ
    rw [show (∑ c : BornVersusRenormalizedFourthPowerObservation D,
        bornVersusRenormalizedFourthPowerLikelihood v D θ c) =
        ∑ c : BornVersusRenormalizedFourthPowerObservation D,
          renormalizedFourthPower v D c.1 by
      apply Finset.sum_congr rfl
      intro c hc
      unfold bornVersusRenormalizedFourthPowerLikelihood
      simp [hθ']]
    exact renormalizedFourthPower_sum_subtype_eq_one hv D

/-- **FR.** Modele fini a deux hypotheses, a priori uniforme, dont chaque
hypothese fournit sa propre regle de vraisemblance. Tous les resultats qui
suivent restent conditionnels au principe CW de Greaves--Myrvold.

**EN.** Finite two-hypothesis model with a uniform prior, in which each
hypothesis supplies its own likelihood rule. All subsequent results remain
conditional on the Greaves--Myrvold CW principle. -/
def bornVersusRenormalizedFourthPowerModel
    {n : ℕ} (v : H n) (D : Perspective n) (hv : ‖v‖ = 1) :
    FiniteBayesModel
      BornVersusRenormalizedFourthPowerHypothesis
      (BornVersusRenormalizedFourthPowerObservation D) :=
  { prior := bornVersusRenormalizedFourthPowerPrior
    likelihood := bornVersusRenormalizedFourthPowerLikelihood v D
    prior_nonneg := bornVersusRenormalizedFourthPowerPrior_nonneg
    prior_sum_one := bornVersusRenormalizedFourthPowerPrior_sum_eq_one
    likelihood_nonneg := by
      intro θ c
      exact bornVersusRenormalizedFourthPowerLikelihood_nonneg hv D θ c
    likelihood_sum_one := by
      intro θ
      exact bornVersusRenormalizedFourthPowerLikelihood_sum_eq_one hv D θ }

theorem bornVersusRenormalizedFourthPowerModel_likelihood_nonneg
    {n : ℕ} {v : H n} {D : Perspective n} (hv : ‖v‖ = 1)
    (θ : BornVersusRenormalizedFourthPowerHypothesis)
    (c : BornVersusRenormalizedFourthPowerObservation D) :
    0 ≤ (bornVersusRenormalizedFourthPowerModel v D hv).likelihood θ c := by
  exact (bornVersusRenormalizedFourthPowerModel v D hv).likelihood_nonneg θ c

theorem bornVersusRenormalizedFourthPowerModel_likelihood_sum_eq_one
    {n : ℕ} {v : H n} {D : Perspective n} (hv : ‖v‖ = 1)
    (θ : BornVersusRenormalizedFourthPowerHypothesis) :
    (∑ c : BornVersusRenormalizedFourthPowerObservation D,
      (bornVersusRenormalizedFourthPowerModel v D hv).likelihood θ c) = 1 := by
  exact (bornVersusRenormalizedFourthPowerModel v D hv).likelihood_sum_one θ

theorem model_likelihood_eq_of_bornAgreement
    {n : ℕ} {v : H n} {D : Perspective n} (hv : ‖v‖ = 1)
    (hAgreement : ∀ c₁ ∈ D.cells, ∀ c₂ ∈ D.cells,
      bornWeight v D c₁ ≠ 0 → bornWeight v D c₂ ≠ 0 →
        bornWeight v D c₁ = bornWeight v D c₂)
    (c : BornVersusRenormalizedFourthPowerObservation D) :
    (bornVersusRenormalizedFourthPowerModel v D hv).likelihood bornHypothesis c =
      (bornVersusRenormalizedFourthPowerModel v D hv).likelihood
        renormalizedFourthPowerHypothesis c := by
  have hagree :=
    (renormalizedFourthPower_agrees_iff hv D).mpr hAgreement
  change bornWeight v D c.1 = renormalizedFourthPower v D c.1
  exact (hagree c.1 c.2).symm

theorem model_observationLikelihoodProduct_eq_of_bornAgreement
    {n : ℕ} {v : H n} {D : Perspective n} (hv : ‖v‖ = 1)
    (hAgreement : ∀ c₁ ∈ D.cells, ∀ c₂ ∈ D.cells,
      bornWeight v D c₁ ≠ 0 → bornWeight v D c₂ ≠ 0 →
        bornWeight v D c₁ = bornWeight v D c₂)
    (observations : List (BornVersusRenormalizedFourthPowerObservation D)) :
    (bornVersusRenormalizedFourthPowerModel v D hv).observationLikelihoodProduct
        observations bornHypothesis =
      (bornVersusRenormalizedFourthPowerModel v D hv).observationLikelihoodProduct
        observations renormalizedFourthPowerHypothesis := by
  induction observations with
  | nil => simp
  | cons c observations ih =>
      rw [FiniteBayesModel.observationLikelihoodProduct_cons,
        FiniteBayesModel.observationLikelihoodProduct_cons,
        model_likelihood_eq_of_bornAgreement hv hAgreement c, ih]

theorem model_evidence_term_eq_of_bornAgreement
    {n : ℕ} {v : H n} {D : Perspective n} (hv : ‖v‖ = 1)
    (hAgreement : ∀ c₁ ∈ D.cells, ∀ c₂ ∈ D.cells,
      bornWeight v D c₁ ≠ 0 → bornWeight v D c₂ ≠ 0 →
        bornWeight v D c₁ = bornWeight v D c₂)
    (observations : List (BornVersusRenormalizedFourthPowerObservation D)) :
      (bornVersusRenormalizedFourthPowerModel v D hv).prior bornHypothesis *
        (bornVersusRenormalizedFourthPowerModel v D hv).observationLikelihoodProduct
          observations bornHypothesis =
      (bornVersusRenormalizedFourthPowerModel v D hv).prior
          renormalizedFourthPowerHypothesis *
        (bornVersusRenormalizedFourthPowerModel v D hv).observationLikelihoodProduct
          observations renormalizedFourthPowerHypothesis := by
  rw [model_observationLikelihoodProduct_eq_of_bornAgreement
    hv hAgreement observations]
  rfl

theorem model_posteriorWeight_eq_of_bornAgreement
    {n : ℕ} {v : H n} {D : Perspective n} (hv : ‖v‖ = 1)
    (hAgreement : ∀ c₁ ∈ D.cells, ∀ c₂ ∈ D.cells,
      bornWeight v D c₁ ≠ 0 → bornWeight v D c₂ ≠ 0 →
        bornWeight v D c₁ = bornWeight v D c₂)
    (observations : List (BornVersusRenormalizedFourthPowerObservation D)) :
    (bornVersusRenormalizedFourthPowerModel v D hv).finiteObservationPosteriorWeight
        observations bornHypothesis =
      (bornVersusRenormalizedFourthPowerModel v D hv).finiteObservationPosteriorWeight
        observations renormalizedFourthPowerHypothesis := by
  unfold FiniteBayesModel.finiteObservationPosteriorWeight
  rw [model_observationLikelihoodProduct_eq_of_bornAgreement
    hv hAgreement observations]
  rfl

theorem model_evidence_eq_two_mul_common_term_of_bornAgreement
    {n : ℕ} {v : H n} {D : Perspective n} (hv : ‖v‖ = 1)
    (hAgreement : ∀ c₁ ∈ D.cells, ∀ c₂ ∈ D.cells,
      bornWeight v D c₁ ≠ 0 → bornWeight v D c₂ ≠ 0 →
        bornWeight v D c₁ = bornWeight v D c₂)
    (observations : List (BornVersusRenormalizedFourthPowerObservation D)) :
    (bornVersusRenormalizedFourthPowerModel v D hv).finiteObservationEvidence
        observations =
      2 * ((bornVersusRenormalizedFourthPowerModel v D hv).prior bornHypothesis *
        (bornVersusRenormalizedFourthPowerModel v D hv).observationLikelihoodProduct
          observations bornHypothesis) := by
  unfold FiniteBayesModel.finiteObservationEvidence
  rw [Fin.sum_univ_two]
  calc
    (bornVersusRenormalizedFourthPowerPrior bornHypothesis) *
        (bornVersusRenormalizedFourthPowerModel v D hv).observationLikelihoodProduct
          observations bornHypothesis +
      (bornVersusRenormalizedFourthPowerPrior
        renormalizedFourthPowerHypothesis) *
        (bornVersusRenormalizedFourthPowerModel v D hv).observationLikelihoodProduct
          observations renormalizedFourthPowerHypothesis =
      2 * ((bornVersusRenormalizedFourthPowerModel v D hv).prior bornHypothesis *
        (bornVersusRenormalizedFourthPowerModel v D hv).observationLikelihoodProduct
          observations bornHypothesis) := by
            rw [model_observationLikelihoodProduct_eq_of_bornAgreement
              hv hAgreement observations]
            norm_num [bornVersusRenormalizedFourthPowerModel,
              bornVersusRenormalizedFourthPowerPrior, bornHypothesis,
              renormalizedFourthPowerHypothesis]
            ring

/-- **FR.** E2.3b : si chaque observation de la liste a une vraisemblance
Born non nulle, le facteur de Bayes vaut `1` et les cotes posterieures
egalent les cotes a priori. La condition de support est la condition usuelle
de definition du conditionnement bayesien ; elle ne restreint pas E2.3a,
qui affirme deja l'identite observationnelle sans cette condition.

**EN.** E2.3b: if every observation in the list has nonzero Born
likelihood, the Bayes factor is `1` and posterior odds equal prior odds. The
support condition is the usual condition for defining Bayesian conditioning;
it does not restrict E2.3a, which already states observational identity
without that condition. -/
theorem finiteObservationBayesFactor_eq_one_of_bornAgreement
    {n : ℕ} {v : H n} {D : Perspective n} (hv : ‖v‖ = 1)
    (hAgreement : ∀ c₁ ∈ D.cells, ∀ c₂ ∈ D.cells,
      bornWeight v D c₁ ≠ 0 → bornWeight v D c₂ ≠ 0 →
        bornWeight v D c₁ = bornWeight v D c₂)
    (observations : List (BornVersusRenormalizedFourthPowerObservation D))
    (hsupport : ∀ c ∈ observations, bornWeight v D c.1 ≠ 0) :
    (bornVersusRenormalizedFourthPowerModel v D hv).finiteObservationBayesFactor
        observations bornHypothesis renormalizedFourthPowerHypothesis = 1 := by
  let M := bornVersusRenormalizedFourthPowerModel v D hv
  have hnonzero : ∀ c ∈ observations,
      M.likelihood renormalizedFourthPowerHypothesis c ≠ 0 := by
    intro c hc
    change renormalizedFourthPower v D c.1 ≠ 0
    have hagree :=
      (renormalizedFourthPower_agrees_iff hv D).mpr hAgreement
    rw [hagree c.1 c.2]
    exact hsupport c hc
  rw [M.finiteObservationBayesFactor_eq_ratioProduct
    observations bornHypothesis renormalizedFourthPowerHypothesis hnonzero]
  induction observations with
  | nil => simp
  | cons c observations ih =>
      rw [M.observationLikelihoodRatioProduct_cons]
      have hc := model_likelihood_eq_of_bornAgreement hv hAgreement c
      have hcne :
          M.likelihood renormalizedFourthPowerHypothesis c ≠ 0 :=
        hnonzero c (by simp)
      have hsupportTail : ∀ c' ∈ observations, bornWeight v D c'.1 ≠ 0 := by
        intro c' hc'
        exact hsupport c' (by simp [hc'])
      have hnonzeroTail : ∀ c' ∈ observations,
          M.likelihood renormalizedFourthPowerHypothesis c' ≠ 0 := by
        intro c' hc'
        exact hnonzero c' (by simp [hc'])
      rw [hc]
      rw [div_self hcne, ih hsupportTail hnonzeroTail]
      ring

theorem finiteObservationPosteriorOdds_eq_priorOdds_of_bornAgreement
    {n : ℕ} {v : H n} {D : Perspective n} (hv : ‖v‖ = 1)
    (hAgreement : ∀ c₁ ∈ D.cells, ∀ c₂ ∈ D.cells,
      bornWeight v D c₁ ≠ 0 → bornWeight v D c₂ ≠ 0 →
        bornWeight v D c₁ = bornWeight v D c₂)
    (observations : List (BornVersusRenormalizedFourthPowerObservation D))
    (hsupport : ∀ c ∈ observations, bornWeight v D c.1 ≠ 0) :
    (bornVersusRenormalizedFourthPowerModel v D hv).finiteObservationPosteriorWeight
        observations bornHypothesis /
      (bornVersusRenormalizedFourthPowerModel v D hv).finiteObservationPosteriorWeight
        observations renormalizedFourthPowerHypothesis =
    (bornVersusRenormalizedFourthPowerModel v D hv).prior bornHypothesis /
      (bornVersusRenormalizedFourthPowerModel v D hv).prior
        renormalizedFourthPowerHypothesis := by
  let M := bornVersusRenormalizedFourthPowerModel v D hv
  have hnonzero : ∀ c ∈ observations,
      M.likelihood renormalizedFourthPowerHypothesis c ≠ 0 := by
    intro c hc
    change renormalizedFourthPower v D c.1 ≠ 0
    have hagree :=
      (renormalizedFourthPower_agrees_iff hv D).mpr hAgreement
    rw [hagree c.1 c.2]
    exact hsupport c hc
  have hproduct := M.observationLikelihoodProduct_ne_zero
    observations renormalizedFourthPowerHypothesis hnonzero
  have hprior : M.prior renormalizedFourthPowerHypothesis ≠ 0 := by
    norm_num [M, bornVersusRenormalizedFourthPowerModel,
      bornVersusRenormalizedFourthPowerPrior]
  have hevidence : M.finiteObservationEvidence observations ≠ 0 := by
    rw [show M.finiteObservationEvidence observations =
        2 * (M.prior bornHypothesis *
          M.observationLikelihoodProduct observations bornHypothesis) by
      exact model_evidence_eq_two_mul_common_term_of_bornAgreement
        hv hAgreement observations]
    have hpriorBorn : M.prior bornHypothesis ≠ 0 := by
      norm_num [M, bornVersusRenormalizedFourthPowerModel,
        bornVersusRenormalizedFourthPowerPrior]
    have hproductBorn :
        M.observationLikelihoodProduct observations bornHypothesis ≠ 0 := by
      rw [model_observationLikelihoodProduct_eq_of_bornAgreement
        hv hAgreement observations]
      exact hproduct
    exact mul_ne_zero (by norm_num) (mul_ne_zero hpriorBorn hproductBorn)
  change M.finiteObservationPosteriorWeight observations bornHypothesis /
      M.finiteObservationPosteriorWeight observations
        renormalizedFourthPowerHypothesis =
    M.prior bornHypothesis / M.prior renormalizedFourthPowerHypothesis
  rw [M.finiteObservationPosteriorOdds_eq
    observations bornHypothesis renormalizedFourthPowerHypothesis
    hevidence hprior hproduct]
  rw [finiteObservationBayesFactor_eq_one_of_bornAgreement
    hv hAgreement observations hsupport]
  ring

noncomputable def coarseLabel0Observation :
    BornVersusRenormalizedFourthPowerObservation coarsePerspective :=
  ⟨label0Line, by rw [coarsePerspective_cells_eq]; simp⟩

noncomputable def coarseLabel1Observation :
    BornVersusRenormalizedFourthPowerObservation coarsePerspective :=
  ⟨label1Space, by rw [coarsePerspective_cells_eq]; simp⟩

private theorem coarse_fourth_denominator_after_eq :
    fourthPowerDenominator psiAfter coarsePerspective = (337 / 625 : ℝ) := by
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
  unfold fourthPowerDenominator
  rw [coarsePerspective_cells_eq,
    Finset.sum_insert (by simpa using label0Line_ne_label1Space),
    Finset.sum_singleton, hlabel0_fourth, hlabel1_fourth]
  norm_num

private theorem coarse_rival_label0_eq :
    renormalizedFourthPower psiAfter coarsePerspective label0Line =
      (81 / 337 : ℝ) := by
  have h := renormalizedFourthPower_disagreement_witness
  exact h.1

private theorem coarse_rival_label1_eq :
    renormalizedFourthPower psiAfter coarsePerspective label1Space =
      (256 / 337 : ℝ) := by
  have hlabel1_fourth : ‖projL label1Space psiAfter‖ ^ 4 = (256 / 625 : ℝ) := by
    calc
      ‖projL label1Space psiAfter‖ ^ 4 =
          (‖projL label1Space psiAfter‖ ^ 2) ^ 2 := by ring
      _ = (16 / 25 : ℝ) ^ 2 := by rw [weight_label1Space_after]
      _ = 256 / 625 := by norm_num
  unfold renormalizedFourthPower
  rw [coarse_fourth_denominator_after_eq, hlabel1_fourth]
  norm_num

private theorem coarse_model_likelihood_label0_eq :
    (bornVersusRenormalizedFourthPowerModel
      psiAfter coarsePerspective psiAfter_norm).likelihood
        bornHypothesis coarseLabel0Observation = (9 / 25 : ℝ) := by
  dsimp [bornVersusRenormalizedFourthPowerModel,
    bornVersusRenormalizedFourthPowerLikelihood, bornHypothesis]
  change bornWeight psiAfter coarsePerspective label0Line = (9 / 25 : ℝ)
  exact weight_label0_after

private theorem coarse_model_likelihood_label1_eq :
    (bornVersusRenormalizedFourthPowerModel
      psiAfter coarsePerspective psiAfter_norm).likelihood
        bornHypothesis coarseLabel1Observation = (16 / 25 : ℝ) := by
  dsimp [bornVersusRenormalizedFourthPowerModel,
    bornVersusRenormalizedFourthPowerLikelihood, bornHypothesis]
  change bornWeight psiAfter coarsePerspective label1Space = (16 / 25 : ℝ)
  unfold bornWeight
  exact weight_label1Space_after

private theorem coarse_model_rival_label0_eq :
    (bornVersusRenormalizedFourthPowerModel
      psiAfter coarsePerspective psiAfter_norm).likelihood
        renormalizedFourthPowerHypothesis coarseLabel0Observation =
      (81 / 337 : ℝ) := by
  dsimp [bornVersusRenormalizedFourthPowerModel,
    bornVersusRenormalizedFourthPowerLikelihood,
    renormalizedFourthPowerHypothesis, bornHypothesis]
  change renormalizedFourthPower psiAfter coarsePerspective label0Line = _
  exact coarse_rival_label0_eq

private theorem coarse_model_rival_label1_eq :
    (bornVersusRenormalizedFourthPowerModel
      psiAfter coarsePerspective psiAfter_norm).likelihood
        renormalizedFourthPowerHypothesis coarseLabel1Observation =
      (256 / 337 : ℝ) := by
  dsimp [bornVersusRenormalizedFourthPowerModel,
    bornVersusRenormalizedFourthPowerLikelihood,
    renormalizedFourthPowerHypothesis, bornHypothesis]
  change renormalizedFourthPower psiAfter coarsePerspective label1Space = _
  exact coarse_rival_label1_eq

private theorem coarse_model_evidence_label0_ne_zero :
    (bornVersusRenormalizedFourthPowerModel
      psiAfter coarsePerspective psiAfter_norm).evidence
        coarseLabel0Observation ≠ 0 := by
  unfold FiniteBayesModel.evidence
  rw [Fin.sum_univ_two]
  have hborn :
      (bornVersusRenormalizedFourthPowerModel
        psiAfter coarsePerspective psiAfter_norm).likelihood 0
          coarseLabel0Observation = (9 / 25 : ℝ) := by
    simpa [bornHypothesis] using coarse_model_likelihood_label0_eq
  have hrival :
      (bornVersusRenormalizedFourthPowerModel
        psiAfter coarsePerspective psiAfter_norm).likelihood 1
          coarseLabel0Observation = (81 / 337 : ℝ) := by
    simpa [renormalizedFourthPowerHypothesis] using coarse_model_rival_label0_eq
  rw [hborn, hrival]
  norm_num [bornVersusRenormalizedFourthPowerModel,
    bornVersusRenormalizedFourthPowerPrior]

private theorem coarse_model_evidence_label1_ne_zero :
    (bornVersusRenormalizedFourthPowerModel
      psiAfter coarsePerspective psiAfter_norm).evidence
        coarseLabel1Observation ≠ 0 := by
  unfold FiniteBayesModel.evidence
  rw [Fin.sum_univ_two]
  have hborn :
      (bornVersusRenormalizedFourthPowerModel
        psiAfter coarsePerspective psiAfter_norm).likelihood 0
          coarseLabel1Observation = (16 / 25 : ℝ) := by
    simpa [bornHypothesis] using coarse_model_likelihood_label1_eq
  have hrival :
      (bornVersusRenormalizedFourthPowerModel
        psiAfter coarsePerspective psiAfter_norm).likelihood 1
          coarseLabel1Observation = (256 / 337 : ℝ) := by
    simpa [renormalizedFourthPowerHypothesis] using coarse_model_rival_label1_eq
  rw [hborn, hrival]
  norm_num [bornVersusRenormalizedFourthPowerModel,
    bornVersusRenormalizedFourthPowerPrior]

theorem coarse_label0_posteriorOdds_eq :
    let M := bornVersusRenormalizedFourthPowerModel
      psiAfter coarsePerspective psiAfter_norm
    M.posteriorWeight coarseLabel0Observation bornHypothesis /
        M.posteriorWeight coarseLabel0Observation
          renormalizedFourthPowerHypothesis =
      337 / 225 := by
  let M := bornVersusRenormalizedFourthPowerModel
    psiAfter coarsePerspective psiAfter_norm
  have h := M.posteriorWeight_div_posteriorWeight_eq
    coarseLabel0Observation bornHypothesis renormalizedFourthPowerHypothesis
    (by simpa [M] using coarse_model_evidence_label0_ne_zero)
    (by norm_num [M, bornVersusRenormalizedFourthPowerModel,
      bornVersusRenormalizedFourthPowerPrior])
    (by rw [coarse_model_rival_label0_eq]; norm_num)
  dsimp [M] at h ⊢
  rw [h, coarse_model_likelihood_label0_eq, coarse_model_rival_label0_eq]
  norm_num [bornVersusRenormalizedFourthPowerModel,
    bornVersusRenormalizedFourthPowerPrior]

theorem coarse_label1_posteriorOdds_eq :
    let M := bornVersusRenormalizedFourthPowerModel
      psiAfter coarsePerspective psiAfter_norm
    M.posteriorWeight coarseLabel1Observation bornHypothesis /
        M.posteriorWeight coarseLabel1Observation
          renormalizedFourthPowerHypothesis =
      337 / 400 := by
  let M := bornVersusRenormalizedFourthPowerModel
    psiAfter coarsePerspective psiAfter_norm
  have h := M.posteriorWeight_div_posteriorWeight_eq
    coarseLabel1Observation bornHypothesis renormalizedFourthPowerHypothesis
    (by simpa [M] using coarse_model_evidence_label1_ne_zero)
    (by norm_num [M, bornVersusRenormalizedFourthPowerModel,
      bornVersusRenormalizedFourthPowerPrior])
    (by rw [coarse_model_rival_label1_eq]; norm_num)
  dsimp [M] at h ⊢
  rw [h, coarse_model_likelihood_label1_eq, coarse_model_rival_label1_eq]
  norm_num [bornVersusRenormalizedFourthPowerModel,
    bornVersusRenormalizedFourthPowerPrior]

theorem coarse_label0_bayesFactor_gt_one :
    (1 : ℝ) < 337 / 225 := by norm_num

theorem coarse_label1_bayesFactor_lt_one :
    (337 / 400 : ℝ) < 1 := by norm_num

theorem coarse_label0_bayesFactor_eq :
    (bornVersusRenormalizedFourthPowerModel
      psiAfter coarsePerspective psiAfter_norm).finiteObservationBayesFactor
        [coarseLabel0Observation] bornHypothesis
          renormalizedFourthPowerHypothesis = 337 / 225 := by
  unfold FiniteBayesModel.finiteObservationBayesFactor
  simp only [FiniteBayesModel.observationLikelihoodProduct,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [coarse_model_likelihood_label0_eq,
    coarse_model_rival_label0_eq]
  norm_num

theorem coarse_label1_bayesFactor_eq :
    (bornVersusRenormalizedFourthPowerModel
      psiAfter coarsePerspective psiAfter_norm).finiteObservationBayesFactor
        [coarseLabel1Observation] bornHypothesis
          renormalizedFourthPowerHypothesis = 337 / 400 := by
  unfold FiniteBayesModel.finiteObservationBayesFactor
  simp only [FiniteBayesModel.observationLikelihoodProduct,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [coarse_model_likelihood_label1_eq,
    coarse_model_rival_label1_eq]
  norm_num

theorem coarse_label0_batch_bayesFactor_two_eq :
    (bornVersusRenormalizedFourthPowerModel
      psiAfter coarsePerspective psiAfter_norm).finiteObservationBayesFactor
        [coarseLabel0Observation, coarseLabel0Observation]
        bornHypothesis renormalizedFourthPowerHypothesis =
      113569 / 50625 := by
  let M := bornVersusRenormalizedFourthPowerModel
    psiAfter coarsePerspective psiAfter_norm
  have h := M.finiteObservationBayesFactor_eq_ratioProduct
    [coarseLabel0Observation, coarseLabel0Observation]
    bornHypothesis renormalizedFourthPowerHypothesis (by
      intro c hc
      have hc' : c = coarseLabel0Observation ∨
          c = coarseLabel0Observation := by simpa using hc
      have hne : M.likelihood renormalizedFourthPowerHypothesis
          coarseLabel0Observation ≠ 0 := by
        have heq : M.likelihood renormalizedFourthPowerHypothesis
            coarseLabel0Observation = (81 / 337 : ℝ) := by
          simpa [M] using coarse_model_rival_label0_eq
        rw [heq]
        norm_num
      rcases hc' with h | h <;> subst c <;> exact hne)
  rw [h]
  simp only [FiniteBayesModel.observationLikelihoodRatioProduct,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [coarse_model_likelihood_label0_eq,
    coarse_model_rival_label0_eq]
  norm_num

theorem coarse_label0_batch_bayesFactor_three_eq :
    (bornVersusRenormalizedFourthPowerModel
      psiAfter coarsePerspective psiAfter_norm).finiteObservationBayesFactor
        [coarseLabel0Observation, coarseLabel0Observation, coarseLabel0Observation]
        bornHypothesis renormalizedFourthPowerHypothesis =
      38272753 / 11390625 := by
  let M := bornVersusRenormalizedFourthPowerModel
    psiAfter coarsePerspective psiAfter_norm
  have h := M.finiteObservationBayesFactor_eq_ratioProduct
    [coarseLabel0Observation, coarseLabel0Observation, coarseLabel0Observation]
    bornHypothesis renormalizedFourthPowerHypothesis (by
      intro c hc
      have hc' : c = coarseLabel0Observation ∨
          c = coarseLabel0Observation ∨ c = coarseLabel0Observation := by
        simpa using hc
      have hne : M.likelihood renormalizedFourthPowerHypothesis
          coarseLabel0Observation ≠ 0 := by
        have heq : M.likelihood renormalizedFourthPowerHypothesis
            coarseLabel0Observation = (81 / 337 : ℝ) := by
          simpa [M] using coarse_model_rival_label0_eq
        rw [heq]
        norm_num
      rcases hc' with h | h | h <;> subst c <;> exact hne)
  rw [h]
  simp only [FiniteBayesModel.observationLikelihoodRatioProduct,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [coarse_model_likelihood_label0_eq,
    coarse_model_rival_label0_eq]
  norm_num

end
end EverettianProbability.Confirmation
