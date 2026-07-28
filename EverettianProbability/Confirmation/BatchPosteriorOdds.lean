import EverettianProbability.Confirmation.IteratedUpdate

/-!
**FR.** # Cotes postérieures pour un lot fini d'observations

Ce module généralise la règle des cotes postérieures à une liste finie
d'observations conditionnellement factorisées sous chaque hypothèse.

Pour deux hypothèses `θ₁` et `θ₂`, le facteur de Bayes du lot est le
rapport entre les produits de leurs vraisemblances. Lorsque toutes les
vraisemblances du dénominateur sont non nulles, ce rapport est aussi le
produit des rapports de vraisemblance observation par observation.

Le résultat est ensuite transporté au prior final du modèle obtenu par
mise à jour itérée, grâce à l'équivalence déjà prouvée entre mise à jour
itérée et mise à jour globale. La factorisation des vraisemblances reste
une hypothèse du modèle. Aucun statut de vérité, aucune consistance
postérieure et aucune limite asymptotique ne sont introduits.

**EN.** # Posterior odds for a finite observation batch

This module generalizes the posterior-odds rule to a finite list of
observations whose likelihoods factor conditionally under each hypothesis.

For two hypotheses `θ₁` and `θ₂`, the batch Bayes factor is the ratio of
their likelihood products. When every denominator likelihood is nonzero,
this ratio is also the product of the observation-by-observation
likelihood ratios.

The result is then transported to the final prior of the iteratively
updated model, using the already proved equivalence between iterated and
global updating. Likelihood factorization remains an assumption of the
model. No truth status, posterior consistency, or asymptotic limit is
introduced.
-/

namespace EverettianProbability.Confirmation

open scoped Classical BigOperators

noncomputable section

variable {Θ Ω : Type*} [Fintype Θ] [Fintype Ω]

/-- **FR.** Produit des rapports de vraisemblance fournis par une liste
finie d'observations pour comparer `θ₁` à `θ₂`.

**EN.** Product of the likelihood ratios supplied by a finite observation
list for comparing `θ₁` with `θ₂`. -/
def FiniteBayesModel.observationLikelihoodRatioProduct
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω)
    (θ₁ θ₂ : Θ) : ℝ :=
  (observations.map
    (fun ω =>
      M.likelihood θ₁ ω /
        M.likelihood θ₂ ω)).prod

@[simp]
theorem FiniteBayesModel.observationLikelihoodRatioProduct_nil
    (M : FiniteBayesModel Θ Ω)
    (θ₁ θ₂ : Θ) :
    M.observationLikelihoodRatioProduct [] θ₁ θ₂ = 1 := by
  simp [FiniteBayesModel.observationLikelihoodRatioProduct]

@[simp]
theorem FiniteBayesModel.observationLikelihoodRatioProduct_cons
    (M : FiniteBayesModel Θ Ω)
    (ω : Ω)
    (observations : List Ω)
    (θ₁ θ₂ : Θ) :
    M.observationLikelihoodRatioProduct
        (ω :: observations) θ₁ θ₂ =
      (M.likelihood θ₁ ω / M.likelihood θ₂ ω) *
        M.observationLikelihoodRatioProduct
          observations θ₁ θ₂ := by
  simp [FiniteBayesModel.observationLikelihoodRatioProduct]

/-- **FR.** Le produit des rapports de vraisemblance est non négatif.

**EN.** The likelihood-ratio product is nonnegative. -/
theorem FiniteBayesModel.observationLikelihoodRatioProduct_nonneg
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω)
    (θ₁ θ₂ : Θ) :
    0 ≤
      M.observationLikelihoodRatioProduct
        observations θ₁ θ₂ := by
  induction observations with
  | nil =>
      simp
  | cons ω observations ih =>
      rw [
        M.observationLikelihoodRatioProduct_cons
          ω observations θ₁ θ₂
      ]
      exact
        mul_nonneg
          (div_nonneg
            (M.likelihood_nonneg θ₁ ω)
            (M.likelihood_nonneg θ₂ ω))
          ih

/-- **FR.** Si chaque vraisemblance d'une liste est non nulle, leur
produit est non nul.

**EN.** If every likelihood in a list is nonzero, their product is
nonzero. -/
theorem FiniteBayesModel.observationLikelihoodProduct_ne_zero
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω)
    (θ : Θ)
    (hnonzero :
      ∀ ω ∈ observations,
        M.likelihood θ ω ≠ 0) :
    M.observationLikelihoodProduct observations θ ≠ 0 := by
  induction observations with
  | nil =>
      simp
  | cons ω observations ih =>
      rw [
        M.observationLikelihoodProduct_cons
          ω observations θ
      ]
      apply mul_ne_zero
      · exact hnonzero ω (by simp)
      · apply ih
        intro ω' hω'
        exact hnonzero ω' (by simp [hω'])

/-- **FR.** Lorsque toutes les vraisemblances de `θ₂` sont non nulles,
le rapport des produits de vraisemblance est égal au produit des rapports
observation par observation.

**EN.** When all likelihoods under `θ₂` are nonzero, the ratio of the
likelihood products equals the product of the observation-by-observation
ratios. -/
theorem FiniteBayesModel.observationLikelihoodProduct_div_eq_ratioProduct
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω)
    (θ₁ θ₂ : Θ)
    (hnonzero :
      ∀ ω ∈ observations,
        M.likelihood θ₂ ω ≠ 0) :
    M.observationLikelihoodProduct observations θ₁ /
        M.observationLikelihoodProduct observations θ₂ =
      M.observationLikelihoodRatioProduct
        observations θ₁ θ₂ := by
  induction observations with
  | nil =>
      simp
  | cons ω observations ih =>
      have hω :
          M.likelihood θ₂ ω ≠ 0 :=
        hnonzero ω (by simp)
      have htail :
          ∀ ω' ∈ observations,
            M.likelihood θ₂ ω' ≠ 0 := by
        intro ω' hω'
        exact hnonzero ω' (by simp [hω'])
      have htailProduct :
          M.observationLikelihoodProduct
              observations θ₂ ≠ 0 :=
        M.observationLikelihoodProduct_ne_zero
          observations θ₂ htail
      rw [
        M.observationLikelihoodProduct_cons
          ω observations θ₁,
        M.observationLikelihoodProduct_cons
          ω observations θ₂,
        M.observationLikelihoodRatioProduct_cons
          ω observations θ₁ θ₂
      ]
      calc
        M.likelihood θ₁ ω *
            M.observationLikelihoodProduct observations θ₁ /
            (M.likelihood θ₂ ω *
              M.observationLikelihoodProduct observations θ₂) =
            (M.likelihood θ₁ ω / M.likelihood θ₂ ω) *
              (M.observationLikelihoodProduct observations θ₁ /
                M.observationLikelihoodProduct observations θ₂) := by
          field_simp [hω, htailProduct]
        _ = _ := by rw [ih htail]

/-- **FR.** Facteur de Bayes associé à une liste finie d'observations.

**EN.** Bayes factor associated with a finite observation list. -/
def FiniteBayesModel.finiteObservationBayesFactor
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω)
    (θ₁ θ₂ : Θ) : ℝ :=
  M.observationLikelihoodProduct observations θ₁ /
    M.observationLikelihoodProduct observations θ₂

/-- **FR.** Le facteur de Bayes d'un lot fini est non négatif.

**EN.** The finite-batch Bayes factor is nonnegative. -/
theorem FiniteBayesModel.finiteObservationBayesFactor_nonneg
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω)
    (θ₁ θ₂ : Θ) :
    0 ≤
      M.finiteObservationBayesFactor
        observations θ₁ θ₂ := by
  unfold FiniteBayesModel.finiteObservationBayesFactor
  exact
    div_nonneg
      (M.observationLikelihoodProduct_nonneg
        observations θ₁)
      (M.observationLikelihoodProduct_nonneg
        observations θ₂)

/-- **FR.** Lorsque les vraisemblances de `θ₂` sont toutes non nulles,
le facteur de Bayes du lot est le produit des rapports de vraisemblance.

**EN.** When all likelihoods under `θ₂` are nonzero, the batch Bayes
factor is the product of the likelihood ratios. -/
theorem FiniteBayesModel.finiteObservationBayesFactor_eq_ratioProduct
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω)
    (θ₁ θ₂ : Θ)
    (hnonzero :
      ∀ ω ∈ observations,
        M.likelihood θ₂ ω ≠ 0) :
    M.finiteObservationBayesFactor
        observations θ₁ θ₂ =
      M.observationLikelihoodRatioProduct
        observations θ₁ θ₂ := by
  unfold FiniteBayesModel.finiteObservationBayesFactor
  exact
    M.observationLikelihoodProduct_div_eq_ratioProduct
      observations θ₁ θ₂ hnonzero

/-- **FR.** Forme sans division de la comparaison de deux poids
postérieurs globaux d'un lot fini.

Elle reste vraie lorsque l'évidence du lot est nulle.

**EN.** Division-free comparison between two global posterior weights
for a finite batch.

It remains true when batch evidence is zero. -/
theorem FiniteBayesModel.finiteObservationPosteriorWeight_cross_mul
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω)
    (θ₁ θ₂ : Θ) :
    M.finiteObservationPosteriorWeight observations θ₁ *
        (M.prior θ₂ *
          M.observationLikelihoodProduct observations θ₂) =
      M.finiteObservationPosteriorWeight observations θ₂ *
        (M.prior θ₁ *
          M.observationLikelihoodProduct observations θ₁) := by
  unfold FiniteBayesModel.finiteObservationPosteriorWeight
  by_cases hevidence :
      M.finiteObservationEvidence observations = 0
  · simp [hevidence]
  · field_simp [hevidence]

/-- **FR.** Règle générale des cotes postérieures pour un lot fini :

`posteriorOdds = priorOdds × batchBayesFactor`.

**EN.** General posterior-odds rule for a finite batch:

`posteriorOdds = priorOdds × batchBayesFactor`. -/
theorem FiniteBayesModel.finiteObservationPosteriorOdds_eq
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω)
    (θ₁ θ₂ : Θ)
    (hevidence :
      M.finiteObservationEvidence observations ≠ 0)
    (hprior₂ :
      M.prior θ₂ ≠ 0)
    (hproduct₂ :
      M.observationLikelihoodProduct observations θ₂ ≠ 0) :
    M.finiteObservationPosteriorWeight observations θ₁ /
        M.finiteObservationPosteriorWeight observations θ₂ =
      (M.prior θ₁ / M.prior θ₂) *
        M.finiteObservationBayesFactor
          observations θ₁ θ₂ := by
  unfold FiniteBayesModel.finiteObservationPosteriorWeight
  unfold FiniteBayesModel.finiteObservationBayesFactor
  field_simp [hevidence, hprior₂, hproduct₂]

/-- **FR.** Lorsque toutes les vraisemblances de `θ₂` sont non nulles,
les cotes postérieures sont les cotes a priori multipliées par le produit
des rapports de vraisemblance observation par observation.

**EN.** When all likelihoods under `θ₂` are nonzero, posterior odds are
prior odds multiplied by the observation-by-observation likelihood-ratio
product. -/
theorem FiniteBayesModel.finiteObservationPosteriorOdds_eq_priorOdds_mul_ratioProduct
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω)
    (θ₁ θ₂ : Θ)
    (hevidence :
      M.finiteObservationEvidence observations ≠ 0)
    (hprior₂ :
      M.prior θ₂ ≠ 0)
    (hnonzero :
      ∀ ω ∈ observations,
        M.likelihood θ₂ ω ≠ 0) :
    M.finiteObservationPosteriorWeight observations θ₁ /
        M.finiteObservationPosteriorWeight observations θ₂ =
      (M.prior θ₁ / M.prior θ₂) *
        M.observationLikelihoodRatioProduct
          observations θ₁ θ₂ := by
  have hproduct₂ :
      M.observationLikelihoodProduct
          observations θ₂ ≠ 0 :=
    M.observationLikelihoodProduct_ne_zero
      observations θ₂ hnonzero
  rw [
    M.finiteObservationPosteriorOdds_eq
      observations θ₁ θ₂
      hevidence hprior₂ hproduct₂,
    M.finiteObservationBayesFactor_eq_ratioProduct
      observations θ₁ θ₂ hnonzero
  ]

/-- **FR.** Règle des cotes pour le prior final du modèle obtenu par
mise à jour itérée.

**EN.** Odds rule for the final prior of the iteratively updated model. -/
theorem FiniteBayesModel.iteratedPosteriorModel_priorOdds_eq
    (M : FiniteBayesModel Θ Ω)
    {observations : List Ω}
    (witness :
      M.SequentialUpdateWitness observations)
    (θ₁ θ₂ : Θ)
    (hprior₂ :
      M.prior θ₂ ≠ 0)
    (hproduct₂ :
      M.observationLikelihoodProduct observations θ₂ ≠ 0) :
    (M.iteratedPosteriorModel witness).prior θ₁ /
        (M.iteratedPosteriorModel witness).prior θ₂ =
      (M.prior θ₁ / M.prior θ₂) *
        M.finiteObservationBayesFactor
          observations θ₁ θ₂ := by
  have hevidence :
      M.finiteObservationEvidence observations ≠ 0 :=
    witness.finiteObservationEvidence_ne_zero
  rw [
    M.iteratedPosteriorModel_prior_eq_finiteObservationPosteriorWeight
      witness θ₁,
    M.iteratedPosteriorModel_prior_eq_finiteObservationPosteriorWeight
      witness θ₂
  ]
  exact
    M.finiteObservationPosteriorOdds_eq
      observations θ₁ θ₂
      hevidence hprior₂ hproduct₂

/-- **FR.** Sous non-nullité observation par observation, les cotes du
prior final sont les cotes initiales multipliées par le produit de tous
les rapports de vraisemblance.

**EN.** Under observation-by-observation nonzero likelihoods, final-prior
odds are initial odds multiplied by the product of all likelihood
ratios. -/
theorem FiniteBayesModel.iteratedPosteriorModel_priorOdds_eq_priorOdds_mul_ratioProduct
    (M : FiniteBayesModel Θ Ω)
    {observations : List Ω}
    (witness :
      M.SequentialUpdateWitness observations)
    (θ₁ θ₂ : Θ)
    (hprior₂ :
      M.prior θ₂ ≠ 0)
    (hnonzero :
      ∀ ω ∈ observations,
        M.likelihood θ₂ ω ≠ 0) :
    (M.iteratedPosteriorModel witness).prior θ₁ /
        (M.iteratedPosteriorModel witness).prior θ₂ =
      (M.prior θ₁ / M.prior θ₂) *
        M.observationLikelihoodRatioProduct
          observations θ₁ θ₂ := by
  have hevidence :
      M.finiteObservationEvidence observations ≠ 0 :=
    witness.finiteObservationEvidence_ne_zero
  rw [
    M.iteratedPosteriorModel_prior_eq_finiteObservationPosteriorWeight
      witness θ₁,
    M.iteratedPosteriorModel_prior_eq_finiteObservationPosteriorWeight
      witness θ₂
  ]
  exact
    M.finiteObservationPosteriorOdds_eq_priorOdds_mul_ratioProduct
      observations θ₁ θ₂
      hevidence hprior₂ hnonzero

end
end EverettianProbability.Confirmation
