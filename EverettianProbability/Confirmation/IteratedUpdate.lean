import EverettianProbability.Confirmation.FiniteObservationBatch

/-!
**FR.** # Équivalence entre mise à jour itérée et mise à jour globale

Ce module formalise l'application successive de la règle de Bayes le
long d'une liste finie d'observations.

La construction est dépendante : à chaque étape, un témoin fournit la
preuve que l'évidence de l'observation courante dans le modèle courant
est non nulle. Cette preuve permet de transformer le posterior courant
en prior du modèle suivant.

Le résultat principal montre que le prior du modèle obtenu après toutes
les mises à jour successives est exactement le poids postérieur global
défini à partir du produit des vraisemblances de la liste entière.

Ainsi, sous les hypothèses explicites de non-nullité requises,
`mise à jour observation par observation = mise à jour globale du lot
fini`. La factorisation conditionnelle des vraisemblances reste une
hypothèse du modèle. Aucun résultat de consistance, aucune hypothèse vraie
et aucune limite asymptotique ne sont introduits.

**EN.** # Equivalence between iterated and global updating

This module formalizes successive applications of Bayes' rule along a
finite observation list.

The construction is dependent: at every step, a witness supplies a proof
that the current observation has nonzero evidence in the current model.
This proof allows the current posterior to become the prior of the next
model.

The main result shows that the prior of the model obtained after all
successive updates is exactly the global posterior weight defined from
the product of the likelihoods of the entire list.

Thus, under the explicit required nonzero assumptions,
`observation-by-observation updating = global finite-batch updating`.
Conditional factorization of likelihoods remains an assumption of the
model. No consistency result, true hypothesis, or asymptotic limit is
introduced.
-/

namespace EverettianProbability.Confirmation

open scoped Classical BigOperators

noncomputable section

variable {Θ Ω : Type*} [Fintype Θ] [Fintype Ω]

/-- **FR.** Témoin dépendant certifiant que chaque observation d'une
liste possède une évidence non nulle dans le modèle obtenu après les
observations précédentes.

**EN.** Dependent witness certifying that every observation in a list
has nonzero evidence in the model obtained after the preceding
observations. -/
inductive FiniteBayesModel.SequentialUpdateWitness :
    FiniteBayesModel Θ Ω → List Ω → Type _
  | nil (M : FiniteBayesModel Θ Ω) :
      M.SequentialUpdateWitness []
  | cons
      {M : FiniteBayesModel Θ Ω}
      (ω : Ω)
      (observations : List Ω)
      (evidence : M.evidence ω ≠ 0)
      (tail :
        (M.posteriorUpdatedModel
          ω evidence).SequentialUpdateWitness observations) :
      M.SequentialUpdateWitness (ω :: observations)

/-- **FR.** Modèle obtenu après mise à jour successive le long d'une
liste munie d'un témoin de non-nullité séquentielle.

**EN.** Model obtained after successive updating along a list equipped
with a sequential nonzero-evidence witness. -/
def FiniteBayesModel.iteratedPosteriorModel
    (M : FiniteBayesModel Θ Ω) :
    {observations : List Ω} →
      M.SequentialUpdateWitness observations →
        FiniteBayesModel Θ Ω
  | [], .nil _ =>
      M
  | _ :: _, .cons ω observations evidence tail =>
      (M.posteriorUpdatedModel
        ω evidence).iteratedPosteriorModel tail

@[simp]
theorem FiniteBayesModel.iteratedPosteriorModel_nil
    (M : FiniteBayesModel Θ Ω) :
    M.iteratedPosteriorModel
        (.nil M) = M := by
  rfl

@[simp]
theorem FiniteBayesModel.iteratedPosteriorModel_cons
    (M : FiniteBayesModel Θ Ω)
    (ω : Ω)
    (observations : List Ω)
    (evidence : M.evidence ω ≠ 0)
    (tail :
      (M.posteriorUpdatedModel
        ω evidence).SequentialUpdateWitness observations) :
    M.iteratedPosteriorModel
        (.cons ω observations evidence tail) =
      (M.posteriorUpdatedModel
        ω evidence).iteratedPosteriorModel tail := by
  rfl

private theorem posteriorUpdatedModel_observationLikelihoodProduct_eq
    (M : FiniteBayesModel Θ Ω)
    (ω : Ω)
    (observations : List Ω)
    (evidence : M.evidence ω ≠ 0)
    (θ : Θ) :
    (M.posteriorUpdatedModel
      ω evidence).observationLikelihoodProduct observations θ =
      M.observationLikelihoodProduct observations θ := by
  unfold FiniteBayesModel.observationLikelihoodProduct
  simp [FiniteBayesModel.posteriorUpdatedModel]

/-- **FR.** Après traitement de la première observation, l'évidence de
la liste restante est l'évidence globale de la liste complète divisée
par l'évidence de la première observation.

**EN.** After processing the first observation, the evidence of the
remaining list is the global evidence of the full list divided by the
evidence of the first observation. -/
theorem FiniteBayesModel.posteriorUpdatedModel_finiteObservationEvidence_eq
    (M : FiniteBayesModel Θ Ω)
    (ω : Ω)
    (observations : List Ω)
    (evidence : M.evidence ω ≠ 0) :
    (M.posteriorUpdatedModel
        ω evidence).finiteObservationEvidence observations =
      M.finiteObservationEvidence (ω :: observations) /
        M.evidence ω := by
  unfold FiniteBayesModel.finiteObservationEvidence
  change
    (∑ θ,
      (M.prior θ * M.likelihood θ ω /
          M.evidence ω) *
        (M.posteriorUpdatedModel
          ω evidence).observationLikelihoodProduct observations θ) =
      (∑ θ,
        M.prior θ *
          M.observationLikelihoodProduct (ω :: observations) θ) /
        M.evidence ω
  calc
    (∑ θ,
      (M.prior θ * M.likelihood θ ω /
          M.evidence ω) *
        (M.posteriorUpdatedModel
          ω evidence).observationLikelihoodProduct observations θ) =
      ∑ θ,
        (M.prior θ * M.likelihood θ ω /
          M.evidence ω) *
          M.observationLikelihoodProduct observations θ := by
        apply Finset.sum_congr rfl
        intro θ hθ
        rw [
          posteriorUpdatedModel_observationLikelihoodProduct_eq
            M ω observations evidence θ
        ]
    _ =
      ∑ θ,
        (M.prior θ * M.likelihood θ ω *
          M.observationLikelihoodProduct observations θ) /
          M.evidence ω := by
        apply Finset.sum_congr rfl
        intro θ hθ
        ring
    _ =
      (∑ θ,
        M.prior θ * M.likelihood θ ω *
          M.observationLikelihoodProduct observations θ) /
        M.evidence ω := by
      rw [Finset.sum_div]
    _ =
      (∑ θ,
        M.prior θ *
          M.observationLikelihoodProduct (ω :: observations) θ) /
        M.evidence ω := by
      congr 1
      apply Finset.sum_congr rfl
      intro θ hθ
      rw [
        M.observationLikelihoodProduct_cons
          ω observations θ
      ]
      ring

/-- **FR.** Mettre d'abord à jour par `ω`, puis traiter globalement la
liste restante, donne exactement le posterior global de la liste
complète.

**EN.** Updating first by `ω` and then globally processing the remaining
list gives exactly the global posterior of the full list. -/
theorem FiniteBayesModel.posteriorUpdatedModel_finiteObservationPosteriorWeight_eq
    (M : FiniteBayesModel Θ Ω)
    (ω : Ω)
    (observations : List Ω)
    (θ : Θ)
    (evidence : M.evidence ω ≠ 0)
    (hbatch :
      M.finiteObservationEvidence
        (ω :: observations) ≠ 0) :
    (M.posteriorUpdatedModel
        ω evidence).finiteObservationPosteriorWeight
          observations θ =
      M.finiteObservationPosteriorWeight
        (ω :: observations) θ := by
  unfold FiniteBayesModel.finiteObservationPosteriorWeight
  rw [
    M.posteriorUpdatedModel_finiteObservationEvidence_eq
      ω observations evidence,
    M.observationLikelihoodProduct_cons
      ω observations θ
  ]
  rw [
    posteriorUpdatedModel_observationLikelihoodProduct_eq
      M ω observations evidence θ
  ]
  rw [M.posteriorUpdatedModel_prior]
  unfold FiniteBayesModel.posteriorWeight
  field_simp [evidence, hbatch]

/-- **FR.** Un témoin séquentiel implique que l'évidence globale de la
liste complète est non nulle.

**EN.** A sequential witness implies that the global evidence of the
entire list is nonzero. -/
theorem FiniteBayesModel.SequentialUpdateWitness.finiteObservationEvidence_ne_zero
    {M : FiniteBayesModel Θ Ω}
    {observations : List Ω}
    (witness :
      M.SequentialUpdateWitness observations) :
    M.finiteObservationEvidence observations ≠ 0 := by
  induction witness with
  | nil M =>
      simp
  | @cons M ω observations evidence tail ih =>
      intro hbatch
      have htail :
          (M.posteriorUpdatedModel
            ω evidence).finiteObservationEvidence observations ≠ 0 :=
        ih
      apply htail
      rw [
        M.posteriorUpdatedModel_finiteObservationEvidence_eq
          ω observations evidence,
        hbatch
      ]
      simp

/-- **FR.** Les mises à jour successives modifient uniquement le prior ;
la fonction de vraisemblance du modèle final reste celle du modèle
initial.

**EN.** Successive updates modify only the prior; the final model keeps
the initial model's likelihood function. -/
theorem FiniteBayesModel.iteratedPosteriorModel_likelihood
    (M : FiniteBayesModel Θ Ω)
    {observations : List Ω}
    (witness :
      M.SequentialUpdateWitness observations)
    (θ : Θ)
    (ω : Ω) :
    (M.iteratedPosteriorModel witness).likelihood θ ω =
      M.likelihood θ ω := by
  induction witness with
  | nil M =>
      simp [FiniteBayesModel.iteratedPosteriorModel]
  | @cons M ω₁ observations evidence tail ih =>
      simp only [FiniteBayesModel.iteratedPosteriorModel]
      rw [ih, M.posteriorUpdatedModel_likelihood]

/-- **FR.** Théorème principal de mise à jour itérée.

Le prior du modèle obtenu après traitement successif de toutes les
observations est exactement le posterior global calculé à partir du
produit de toutes leurs vraisemblances.

**EN.** Main iterated-update theorem.

The prior of the model obtained after successively processing all
observations is exactly the global posterior computed from the product
of all their likelihoods. -/
theorem FiniteBayesModel.iteratedPosteriorModel_prior_eq_finiteObservationPosteriorWeight
    (M : FiniteBayesModel Θ Ω)
    {observations : List Ω}
    (witness :
      M.SequentialUpdateWitness observations)
    (θ : Θ) :
    (M.iteratedPosteriorModel witness).prior θ =
      M.finiteObservationPosteriorWeight
        observations θ := by
  induction witness with
  | nil M =>
      simp
  | @cons M ω observations evidence tail ih =>
      simp only [FiniteBayesModel.iteratedPosteriorModel]
      calc
        ((M.posteriorUpdatedModel
          ω evidence).iteratedPosteriorModel tail).prior θ =
          (M.posteriorUpdatedModel
            ω evidence).finiteObservationPosteriorWeight
              observations θ := ih
        _ =
          M.finiteObservationPosteriorWeight
            (ω :: observations) θ := by
            apply
              M.posteriorUpdatedModel_finiteObservationPosteriorWeight_eq
                ω observations θ evidence
            exact
              (FiniteBayesModel.SequentialUpdateWitness.cons
                ω observations evidence tail).finiteObservationEvidence_ne_zero

/-- **FR.** Lorsque des témoins séquentiels existent dans les deux ordres,
renverser la liste ne change pas le prior final.

**EN.** When sequential witnesses exist in both orders, reversing the
list does not change the final prior. -/
theorem FiniteBayesModel.iteratedPosteriorModel_prior_reverse
    (M : FiniteBayesModel Θ Ω)
    (observations : List Ω)
    (forward :
      M.SequentialUpdateWitness observations)
    (backward :
      M.SequentialUpdateWitness observations.reverse)
    (θ : Θ) :
    (M.iteratedPosteriorModel backward).prior θ =
      (M.iteratedPosteriorModel forward).prior θ := by
  rw [
    M.iteratedPosteriorModel_prior_eq_finiteObservationPosteriorWeight
      backward θ,
    M.iteratedPosteriorModel_prior_eq_finiteObservationPosteriorWeight
      forward θ,
    M.finiteObservationPosteriorWeight_reverse
      observations θ
  ]

/-- **FR.** Le prior du modèle final reste normalisé.

**EN.** The prior of the final model remains normalized. -/
theorem FiniteBayesModel.sum_iteratedPosteriorModel_prior_eq_one
    (M : FiniteBayesModel Θ Ω)
    {observations : List Ω}
    (witness :
      M.SequentialUpdateWitness observations) :
    (∑ θ,
      (M.iteratedPosteriorModel witness).prior θ) = 1 := by
  exact
    (M.iteratedPosteriorModel witness).prior_sum_one

end
end EverettianProbability.Confirmation
