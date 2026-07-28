import EverettianProbability.Confirmation.SequentialUpdate

/-!
**FR.** # Lots finis d'observations

Ce module généralise la mise à jour à deux observations à une liste finie
d'observations conditionnellement indépendantes sous chaque hypothèse.

Pour une hypothèse `θ` et une liste `[ω₁, …, ωₙ]`, la vraisemblance
jointe est le produit `likelihood θ ω₁ × ⋯ × likelihood θ ωₙ`. L'évidence
du lot est la somme de cette vraisemblance jointe pondérée par le prior.
Le poids postérieur global est ensuite obtenu par normalisation.

Le lot vide laisse le prior inchangé. Les listes à une et deux
observations reproduisent exactement les constructions déjà établies.
L'ordre d'une liste renversée ne change ni la vraisemblance jointe, ni
l'évidence, ni le posterior, par commutativité du produit réel.

Ce module construit seulement la mise à jour globale d'un lot fini.
L'équivalence avec une mise à jour itérée observation par observation sera
établie séparément.

**EN.** # Finite batches of observations

This module generalizes the two-observation update to a finite list of
observations conditionally independent under each hypothesis.

For a hypothesis `θ` and a list `[ω₁, …, ωₙ]`, the joint likelihood is
the product `likelihood θ ω₁ × ⋯ × likelihood θ ωₙ`. Batch evidence is the
prior-weighted sum of this joint likelihood. The global posterior weight
is then obtained by normalization.

The empty batch leaves the prior unchanged. Singleton and two-element
lists reproduce the previously established constructions exactly.
Reversing a list changes neither its joint likelihood, its evidence, nor
its posterior, by commutativity of real multiplication.

This module constructs only the global update associated with a finite
batch. Equivalence with observation-by-observation iteration will be
proved separately.
-/

namespace EverettianProbability.Confirmation

open scoped Classical BigOperators

noncomputable section

variable {Θ Ω : Type*} [Fintype Θ] [Fintype Ω]

/-- **FR.** Produit des vraisemblances d'une liste finie d'observations
sous une hypothèse. La liste vide possède la vraisemblance `1`.

**EN.** Product of the likelihoods of a finite observation list under a
hypothesis. The empty list has likelihood `1`. -/
def FiniteBayesModel.observationLikelihoodProduct
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω)
    (θ : Θ) : ℝ :=
  (observations.map (M.likelihood θ)).prod

@[simp]
theorem FiniteBayesModel.observationLikelihoodProduct_nil
    (M : FiniteBayesModel Θ Ω)
    (θ : Θ) :
    M.observationLikelihoodProduct [] θ = 1 := by
  simp [FiniteBayesModel.observationLikelihoodProduct]

@[simp]
theorem FiniteBayesModel.observationLikelihoodProduct_cons
    (M : FiniteBayesModel Θ Ω)
    (ω : Ω) (observations : List Ω)
    (θ : Θ) :
    M.observationLikelihoodProduct (ω :: observations) θ =
      M.likelihood θ ω *
        M.observationLikelihoodProduct observations θ := by
  simp [FiniteBayesModel.observationLikelihoodProduct]

@[simp]
theorem FiniteBayesModel.observationLikelihoodProduct_append
    (M : FiniteBayesModel Θ Ω)
    (observations₁ observations₂ : List Ω)
    (θ : Θ) :
    M.observationLikelihoodProduct
        (observations₁ ++ observations₂) θ =
      M.observationLikelihoodProduct observations₁ θ *
        M.observationLikelihoodProduct observations₂ θ := by
  simp [
    FiniteBayesModel.observationLikelihoodProduct,
    List.map_append,
    List.prod_append
  ]

/-- **FR.** Le produit des vraisemblances est non négatif.

**EN.** The likelihood product is nonnegative. -/
theorem FiniteBayesModel.observationLikelihoodProduct_nonneg
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω)
    (θ : Θ) :
    0 ≤ M.observationLikelihoodProduct observations θ := by
  induction observations with
  | nil =>
      simp
  | cons ω observations ih =>
      rw [
        M.observationLikelihoodProduct_cons
          ω observations θ
      ]
      exact
        mul_nonneg
          (M.likelihood_nonneg θ ω)
          ih

/-- **FR.** Renverser l'ordre des observations ne change pas le produit
des vraisemblances.

**EN.** Reversing the order of observations does not change the
likelihood product. -/
theorem FiniteBayesModel.observationLikelihoodProduct_reverse
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω)
    (θ : Θ) :
    M.observationLikelihoodProduct observations.reverse θ =
      M.observationLikelihoodProduct observations θ := by
  unfold FiniteBayesModel.observationLikelihoodProduct
  rw [List.map_reverse, List.prod_reverse]

/-- **FR.** Évidence marginale associée à une liste finie
d'observations.

**EN.** Marginal evidence associated with a finite observation list. -/
def FiniteBayesModel.finiteObservationEvidence
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω) : ℝ :=
  ∑ θ,
    M.prior θ *
      M.observationLikelihoodProduct observations θ

/-- **FR.** L'évidence d'un lot fini est non négative.

**EN.** Evidence of a finite batch is nonnegative. -/
theorem FiniteBayesModel.finiteObservationEvidence_nonneg
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω) :
    0 ≤ M.finiteObservationEvidence observations := by
  unfold FiniteBayesModel.finiteObservationEvidence
  exact Finset.sum_nonneg fun θ _ =>
    mul_nonneg
      (M.prior_nonneg θ)
      (M.observationLikelihoodProduct_nonneg
        observations θ)

/-- **FR.** L'évidence du lot vide vaut `1`.

**EN.** Evidence of the empty batch is `1`. -/
@[simp]
theorem FiniteBayesModel.finiteObservationEvidence_nil
    (M : FiniteBayesModel Θ Ω) :
    M.finiteObservationEvidence [] = 1 := by
  simpa [
    FiniteBayesModel.finiteObservationEvidence
  ] using M.prior_sum_one

/-- **FR.** L'évidence d'un singleton coïncide avec l'évidence déjà
définie pour une observation.

**EN.** Evidence of a singleton agrees with the previously defined
single-observation evidence. -/
@[simp]
theorem FiniteBayesModel.finiteObservationEvidence_singleton
    (M : FiniteBayesModel Θ Ω)
    (ω : Ω) :
    M.finiteObservationEvidence [ω] =
      M.evidence ω := by
  unfold FiniteBayesModel.finiteObservationEvidence
  unfold FiniteBayesModel.evidence
  apply Finset.sum_congr rfl
  intro θ hθ
  simp [FiniteBayesModel.observationLikelihoodProduct]

/-- **FR.** L'évidence d'une liste de deux observations coïncide avec
l'évidence conjointe déjà définie.

**EN.** Evidence of a two-element list agrees with the previously
defined joint evidence. -/
@[simp]
theorem FiniteBayesModel.finiteObservationEvidence_pair
    (M : FiniteBayesModel Θ Ω)
    (ω₁ ω₂ : Ω) :
    M.finiteObservationEvidence [ω₁, ω₂] =
      M.twoObservationEvidence ω₁ ω₂ := by
  unfold FiniteBayesModel.finiteObservationEvidence
  unfold FiniteBayesModel.twoObservationEvidence
  apply Finset.sum_congr rfl
  intro θ hθ
  simp [FiniteBayesModel.observationLikelihoodProduct]
  ring

/-- **FR.** Renverser la liste ne change pas son évidence.

**EN.** Reversing the list does not change its evidence. -/
theorem FiniteBayesModel.finiteObservationEvidence_reverse
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω) :
    M.finiteObservationEvidence observations.reverse =
      M.finiteObservationEvidence observations := by
  unfold FiniteBayesModel.finiteObservationEvidence
  apply Finset.sum_congr rfl
  intro θ hθ
  rw [
    M.observationLikelihoodProduct_reverse
      observations θ
  ]

/-- **FR.** Poids postérieur global associé à un lot fini
d'observations. Lorsque l'évidence du lot est nulle, ce poids vaut `0`
par convention de division dans `ℝ`.

**EN.** Global posterior weight associated with a finite observation
batch. When batch evidence is zero, this weight is `0` by the division
convention in `ℝ`. -/
def FiniteBayesModel.finiteObservationPosteriorWeight
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω)
    (θ : Θ) : ℝ :=
  M.prior θ *
      M.observationLikelihoodProduct observations θ /
    M.finiteObservationEvidence observations

/-- **FR.** Tout poids postérieur d'un lot fini est non négatif.

**EN.** Every finite-batch posterior weight is nonnegative. -/
theorem FiniteBayesModel.finiteObservationPosteriorWeight_nonneg
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω)
    (θ : Θ) :
    0 ≤ M.finiteObservationPosteriorWeight observations θ := by
  unfold FiniteBayesModel.finiteObservationPosteriorWeight
  exact
    div_nonneg
      (mul_nonneg
        (M.prior_nonneg θ)
        (M.observationLikelihoodProduct_nonneg
          observations θ))
      (M.finiteObservationEvidence_nonneg observations)

/-- **FR.** Lorsque l'évidence du lot est non nulle, les poids
postérieurs somment à `1`.

**EN.** When batch evidence is nonzero, posterior weights sum to `1`. -/
theorem FiniteBayesModel.sum_finiteObservationPosteriorWeight_eq_one
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω)
    (hevidence :
      M.finiteObservationEvidence observations ≠ 0) :
    (∑ θ,
      M.finiteObservationPosteriorWeight observations θ) = 1 := by
  unfold FiniteBayesModel.finiteObservationPosteriorWeight
  rw [← Finset.sum_div]
  change
    M.finiteObservationEvidence observations /
        M.finiteObservationEvidence observations = 1
  exact div_self hevidence

/-- **FR.** Lorsque l'évidence du lot est nulle, tous les poids
postérieurs somment à `0`.

**EN.** When batch evidence is zero, all posterior weights sum to `0`. -/
theorem FiniteBayesModel.sum_finiteObservationPosteriorWeight_eq_zero
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω)
    (hevidence :
      M.finiteObservationEvidence observations = 0) :
    (∑ θ,
      M.finiteObservationPosteriorWeight observations θ) = 0 := by
  simp [
    FiniteBayesModel.finiteObservationPosteriorWeight,
    hevidence
  ]

/-- **FR.** Le lot vide laisse exactement le prior inchangé.

**EN.** The empty batch leaves the prior exactly unchanged. -/
@[simp]
theorem FiniteBayesModel.finiteObservationPosteriorWeight_nil
    (M : FiniteBayesModel Θ Ω)
    (θ : Θ) :
    M.finiteObservationPosteriorWeight [] θ =
      M.prior θ := by
  simp [
    FiniteBayesModel.finiteObservationPosteriorWeight
  ]

/-- **FR.** Le posterior d'un singleton coïncide exactement avec le
posterior à une observation.

**EN.** The posterior of a singleton agrees exactly with the
single-observation posterior. -/
@[simp]
theorem FiniteBayesModel.finiteObservationPosteriorWeight_singleton
    (M : FiniteBayesModel Θ Ω)
    (ω : Ω)
    (θ : Θ) :
    M.finiteObservationPosteriorWeight [ω] θ =
      M.posteriorWeight ω θ := by
  unfold FiniteBayesModel.finiteObservationPosteriorWeight
  unfold FiniteBayesModel.posteriorWeight
  rw [M.finiteObservationEvidence_singleton ω]
  simp [FiniteBayesModel.observationLikelihoodProduct]

/-- **FR.** Le posterior d'une liste de deux observations coïncide
exactement avec le posterior conjoint déjà défini.

**EN.** The posterior of a two-element list agrees exactly with the
previously defined joint posterior. -/
@[simp]
theorem FiniteBayesModel.finiteObservationPosteriorWeight_pair
    (M : FiniteBayesModel Θ Ω)
    (ω₁ ω₂ : Ω)
    (θ : Θ) :
    M.finiteObservationPosteriorWeight [ω₁, ω₂] θ =
      M.twoObservationPosteriorWeight ω₁ ω₂ θ := by
  unfold FiniteBayesModel.finiteObservationPosteriorWeight
  unfold FiniteBayesModel.twoObservationPosteriorWeight
  rw [M.finiteObservationEvidence_pair ω₁ ω₂]
  simp [FiniteBayesModel.observationLikelihoodProduct]
  ring

/-- **FR.** Renverser l'ordre du lot ne change pas le poids postérieur
global.

**EN.** Reversing batch order does not change the global posterior
weight. -/
theorem FiniteBayesModel.finiteObservationPosteriorWeight_reverse
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω)
    (θ : Θ) :
    M.finiteObservationPosteriorWeight
        observations.reverse θ =
      M.finiteObservationPosteriorWeight
        observations θ := by
  unfold FiniteBayesModel.finiteObservationPosteriorWeight
  rw [
    M.observationLikelihoodProduct_reverse
      observations θ,
    M.finiteObservationEvidence_reverse
      observations
  ]

end
end EverettianProbability.Confirmation
