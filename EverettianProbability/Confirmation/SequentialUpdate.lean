import EverettianProbability.Confirmation.RationalWitness

/-!
**FR.** # Mise à jour bayésienne séquentielle finie

Ce module formalise deux observations successives dans un modèle
bayésien fini.

Après une première observation d'évidence non nulle, les poids
postérieurs deviennent le prior d'un nouveau modèle possédant les mêmes
vraisemblances. Une seconde observation peut alors être traitée par une
nouvelle application de la règle de Bayes.

Le module montre que cette mise à jour séquentielle est exactement
équivalente à une mise à jour unique fondée sur le produit des deux
vraisemblances :

`prior θ × likelihood θ ω₁ × likelihood θ ω₂`.

Cette factorisation encode l'hypothèse que les deux observations sont
conditionnellement indépendantes et identiquement distribuées sous
chaque hypothèse. Elle n'est pas dérivée de la dynamique quantique.

L'ordre des deux observations n'affecte pas le poids postérieur final
lorsque toutes les évidences nécessaires sont non nulles.

**EN.** # Finite sequential Bayesian updating

This module formalizes two successive observations in a finite Bayesian
model.

After a first observation with nonzero evidence, posterior weights become
the prior of a new model with the same likelihoods. A second observation
can then be processed by another application of Bayes' rule.

The module proves that this sequential update is exactly equivalent to a
single update based on the product of the two likelihoods:

`prior θ × likelihood θ ω₁ × likelihood θ ω₂`.

This factorization encodes the assumption that the two observations are
conditionally independent and identically distributed under each
hypothesis. It is not derived from quantum dynamics.

The order of the two observations does not affect the final posterior
weight whenever all required evidences are nonzero.
-/

namespace EverettianProbability.Confirmation

open scoped Classical BigOperators

noncomputable section

variable {Θ Ω : Type*} [Fintype Θ] [Fintype Ω]

/-- **FR.** Modèle obtenu après une première observation d'évidence non
nulle. Le posterior devient le nouveau prior ; les vraisemblances restent
inchangées.

**EN.** Model obtained after a first observation with nonzero evidence.
The posterior becomes the new prior; likelihoods remain unchanged. -/
def FiniteBayesModel.posteriorUpdatedModel
    (M : FiniteBayesModel Θ Ω)
    (ω₁ : Ω)
    (hevidence₁ : M.evidence ω₁ ≠ 0) :
    FiniteBayesModel Θ Ω where
  prior := M.posteriorWeight ω₁
  likelihood := M.likelihood
  prior_nonneg := by
    intro θ
    exact M.posteriorWeight_nonneg ω₁ θ
  prior_sum_one :=
    M.sum_posteriorWeight_eq_one ω₁ hevidence₁
  likelihood_nonneg := by
    intro θ ω
    exact M.likelihood_nonneg θ ω
  likelihood_sum_one := by
    intro θ
    exact M.likelihood_sum_one θ

@[simp]
theorem FiniteBayesModel.posteriorUpdatedModel_prior
    (M : FiniteBayesModel Θ Ω)
    (ω₁ : Ω)
    (hevidence₁ : M.evidence ω₁ ≠ 0)
    (θ : Θ) :
    (M.posteriorUpdatedModel ω₁ hevidence₁).prior θ =
      M.posteriorWeight ω₁ θ := by
  rfl

@[simp]
theorem FiniteBayesModel.posteriorUpdatedModel_likelihood
    (M : FiniteBayesModel Θ Ω)
    (ω₁ : Ω)
    (hevidence₁ : M.evidence ω₁ ≠ 0)
    (θ : Θ) (ω : Ω) :
    (M.posteriorUpdatedModel ω₁ hevidence₁).likelihood θ ω =
      M.likelihood θ ω := by
  rfl

/-- **FR.** Évidence conjointe de deux observations sous l'hypothèse de
factorisation conditionnelle des vraisemblances.

**EN.** Joint evidence of two observations under conditional
factorization of their likelihoods. -/
def FiniteBayesModel.twoObservationEvidence
    (M : FiniteBayesModel Θ Ω)
    (ω₁ ω₂ : Ω) : ℝ :=
  ∑ θ,
    M.prior θ *
      M.likelihood θ ω₁ *
      M.likelihood θ ω₂

/-- **FR.** L'évidence de deux observations est non négative.

**EN.** The evidence of two observations is nonnegative. -/
theorem FiniteBayesModel.twoObservationEvidence_nonneg
    (M : FiniteBayesModel Θ Ω)
    (ω₁ ω₂ : Ω) :
    0 ≤ M.twoObservationEvidence ω₁ ω₂ := by
  unfold FiniteBayesModel.twoObservationEvidence
  exact Finset.sum_nonneg fun θ _ =>
    mul_nonneg
      (mul_nonneg
        (M.prior_nonneg θ)
        (M.likelihood_nonneg θ ω₁))
      (M.likelihood_nonneg θ ω₂)

/-- **FR.** L'évidence conjointe ne dépend pas de l'ordre des deux
observations.

**EN.** Joint evidence does not depend on the order of the two
observations. -/
theorem FiniteBayesModel.twoObservationEvidence_comm
    (M : FiniteBayesModel Θ Ω)
    (ω₁ ω₂ : Ω) :
    M.twoObservationEvidence ω₁ ω₂ =
      M.twoObservationEvidence ω₂ ω₁ := by
  unfold FiniteBayesModel.twoObservationEvidence
  apply Finset.sum_congr rfl
  intro θ hθ
  ring

/-- **FR.** Poids postérieur obtenu en une étape à partir du produit des
deux vraisemblances.

Lorsque l'évidence conjointe est nulle, ce poids vaut `0` par convention
de division dans `ℝ`.

**EN.** Posterior weight obtained in one step from the product of the two
likelihoods.

When the joint evidence is zero, this weight is `0` by the division
convention in `ℝ`. -/
def FiniteBayesModel.twoObservationPosteriorWeight
    (M : FiniteBayesModel Θ Ω)
    (ω₁ ω₂ : Ω)
    (θ : Θ) : ℝ :=
  M.prior θ *
      M.likelihood θ ω₁ *
      M.likelihood θ ω₂ /
    M.twoObservationEvidence ω₁ ω₂

/-- **FR.** Tout poids postérieur à deux observations est non négatif.

**EN.** Every two-observation posterior weight is nonnegative. -/
theorem FiniteBayesModel.twoObservationPosteriorWeight_nonneg
    (M : FiniteBayesModel Θ Ω)
    (ω₁ ω₂ : Ω)
    (θ : Θ) :
    0 ≤ M.twoObservationPosteriorWeight ω₁ ω₂ θ := by
  unfold FiniteBayesModel.twoObservationPosteriorWeight
  exact
    div_nonneg
      (mul_nonneg
        (mul_nonneg
          (M.prior_nonneg θ)
          (M.likelihood_nonneg θ ω₁))
        (M.likelihood_nonneg θ ω₂))
      (M.twoObservationEvidence_nonneg ω₁ ω₂)

/-- **FR.** Si l'évidence conjointe est non nulle, les poids postérieurs
à deux observations somment à `1`.

**EN.** If the joint evidence is nonzero, the two-observation posterior
weights sum to `1`. -/
theorem FiniteBayesModel.sum_twoObservationPosteriorWeight_eq_one
    (M : FiniteBayesModel Θ Ω)
    (ω₁ ω₂ : Ω)
    (hevidence :
      M.twoObservationEvidence ω₁ ω₂ ≠ 0) :
    (∑ θ,
      M.twoObservationPosteriorWeight ω₁ ω₂ θ) = 1 := by
  unfold FiniteBayesModel.twoObservationPosteriorWeight
  rw [← Finset.sum_div]
  change
    M.twoObservationEvidence ω₁ ω₂ /
        M.twoObservationEvidence ω₁ ω₂ = 1
  exact div_self hevidence

/-- **FR.** L'évidence de la seconde observation dans le modèle mis à
jour est l'évidence conjointe divisée par l'évidence de la première
observation.

**EN.** Evidence of the second observation in the updated model is the
joint evidence divided by the evidence of the first observation. -/
theorem FiniteBayesModel.posteriorUpdatedModel_evidence_eq
    (M : FiniteBayesModel Θ Ω)
    (ω₁ ω₂ : Ω)
    (hevidence₁ : M.evidence ω₁ ≠ 0) :
    (M.posteriorUpdatedModel ω₁ hevidence₁).evidence ω₂ =
      M.twoObservationEvidence ω₁ ω₂ /
        M.evidence ω₁ := by
  unfold FiniteBayesModel.evidence
  change
    (∑ θ,
      (M.prior θ * M.likelihood θ ω₁ /
          M.evidence ω₁) *
        M.likelihood θ ω₂) =
      M.twoObservationEvidence ω₁ ω₂ /
        M.evidence ω₁
  unfold FiniteBayesModel.twoObservationEvidence
  calc
    (∑ θ,
      (M.prior θ * M.likelihood θ ω₁ /
          M.evidence ω₁) *
        M.likelihood θ ω₂) =
      ∑ θ,
        (M.prior θ * M.likelihood θ ω₁ *
          M.likelihood θ ω₂) /
          M.evidence ω₁ := by
        apply Finset.sum_congr rfl
        intro θ hθ
        ring
    _ =
      (∑ θ,
        M.prior θ * M.likelihood θ ω₁ *
          M.likelihood θ ω₂) /
        M.evidence ω₁ := by
      rw [Finset.sum_div]

/-- **FR.** La mise à jour séquentielle après deux observations est
exactement égale à la mise à jour en une étape par le produit des
vraisemblances.

**EN.** Sequential updating after two observations is exactly equal to
one-step updating by the product of the likelihoods. -/
theorem FiniteBayesModel.posteriorUpdatedModel_posteriorWeight_eq
    (M : FiniteBayesModel Θ Ω)
    (ω₁ ω₂ : Ω)
    (θ : Θ)
    (hevidence₁ : M.evidence ω₁ ≠ 0)
    (hevidence₁₂ :
      M.twoObservationEvidence ω₁ ω₂ ≠ 0) :
    (M.posteriorUpdatedModel
        ω₁ hevidence₁).posteriorWeight ω₂ θ =
      M.twoObservationPosteriorWeight ω₁ ω₂ θ := by
  unfold FiniteBayesModel.posteriorWeight
  change
    ((M.prior θ * M.likelihood θ ω₁ /
          M.evidence ω₁) *
        M.likelihood θ ω₂) /
        (M.posteriorUpdatedModel
          ω₁ hevidence₁).evidence ω₂ =
      M.twoObservationPosteriorWeight ω₁ ω₂ θ
  rw [
    M.posteriorUpdatedModel_evidence_eq
      ω₁ ω₂ hevidence₁
  ]
  unfold FiniteBayesModel.twoObservationPosteriorWeight
  field_simp [hevidence₁, hevidence₁₂]

/-- **FR.** Sous les hypothèses de non-nullité nécessaires, permuter
l'ordre des deux observations ne change pas le poids postérieur final.

**EN.** Under the required nonzero-evidence assumptions, swapping the
order of the two observations does not change the final posterior
weight. -/
theorem FiniteBayesModel.sequentialPosteriorWeight_comm
    (M : FiniteBayesModel Θ Ω)
    (ω₁ ω₂ : Ω)
    (θ : Θ)
    (hevidence₁ : M.evidence ω₁ ≠ 0)
    (hevidence₂ : M.evidence ω₂ ≠ 0)
    (hevidence₁₂ :
      M.twoObservationEvidence ω₁ ω₂ ≠ 0) :
    (M.posteriorUpdatedModel
        ω₁ hevidence₁).posteriorWeight ω₂ θ =
      (M.posteriorUpdatedModel
        ω₂ hevidence₂).posteriorWeight ω₁ θ := by
  have hevidence₂₁ :
      M.twoObservationEvidence ω₂ ω₁ ≠ 0 := by
    rw [M.twoObservationEvidence_comm ω₂ ω₁]
    exact hevidence₁₂
  rw [
    M.posteriorUpdatedModel_posteriorWeight_eq
      ω₁ ω₂ θ hevidence₁ hevidence₁₂,
    M.posteriorUpdatedModel_posteriorWeight_eq
      ω₂ ω₁ θ hevidence₂ hevidence₂₁
  ]
  unfold FiniteBayesModel.twoObservationPosteriorWeight
  rw [M.twoObservationEvidence_comm ω₂ ω₁]
  ring

end
end EverettianProbability.Confirmation
