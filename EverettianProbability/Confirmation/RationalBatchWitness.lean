import EverettianProbability.Confirmation.FrequencyBatchOdds

/-!
**FR.** # Témoin rationnel sur un lot de cellules de fréquence

Ce module prolonge le témoin rationnel à une liste de deux observations
identiques. Les produits de vraisemblance, l'évidence globale, les
postérieurs et les cotes sont calculés exactement. Un témoin séquentiel
explicite relie enfin le prior itéré au posterior global du lot.

Le témoin utilise les vraisemblances borniennes déjà acquises ; il ne
désigne aucune hypothèse comme vraie et n'établit aucune consistance
asymptotique.

**EN.** # Rational witness for a batch of frequency cells

This module extends the rational witness to a list of two identical
observations. It computes exactly the likelihood products, global evidence,
posteriors, and odds. An explicit sequential witness finally relates the
iterated prior to the global batch posterior.

The witness uses already established Born likelihoods; it designates no
hypothesis as true and proves no asymptotic consistency.
-/

namespace EverettianProbability.Confirmation

open EverettianProbability.Frequency
open scoped Classical BigOperators

noncomputable section

/-- **FR.** Deux observations identiques de la cellule tous-`1`.

**EN.** Two identical observations of the all-`1` cell. -/
def rationalWitnessObservationBatch : List (Fin 3) :=
  [
    rationalWitnessObservation,
    rationalWitnessObservation
  ]

/-- **FR.** Le produit des vraisemblances basses du lot vaut
`6561/390625`.

**EN.** The batch low-likelihood product is `6561/390625`. -/
theorem rationalWitnessLow_likelihoodProduct_eq :
    rationalWitnessModel.observationLikelihoodProduct
        rationalWitnessObservationBatch
        rationalWitnessLow =
      6561 / 390625 := by
  rw [
    show rationalWitnessObservationBatch =
      [rationalWitnessObservation, rationalWitnessObservation] by rfl,
    rationalWitnessModel.observationLikelihoodProduct_cons,
    rationalWitnessModel.observationLikelihoodProduct_cons,
    rationalWitnessModel.observationLikelihoodProduct_nil,
    rationalWitnessLow_likelihood_eq
  ]
  norm_num

/-- **FR.** Le produit des vraisemblances hautes du lot vaut
`65536/390625`.

**EN.** The batch high-likelihood product is `65536/390625`. -/
theorem rationalWitnessHigh_likelihoodProduct_eq :
    rationalWitnessModel.observationLikelihoodProduct
        rationalWitnessObservationBatch
        rationalWitnessHigh =
      65536 / 390625 := by
  rw [
    show rationalWitnessObservationBatch =
      [rationalWitnessObservation, rationalWitnessObservation] by rfl,
    rationalWitnessModel.observationLikelihoodProduct_cons,
    rationalWitnessModel.observationLikelihoodProduct_cons,
    rationalWitnessModel.observationLikelihoodProduct_nil,
    rationalWitnessHigh_likelihood_eq
  ]
  norm_num

/-- **FR.** Le produit des rapports de noyaux du lot vaut `65536/6561`.

**EN.** The batch kernel-ratio product is `65536/6561`. -/
theorem rationalWitness_kernelRatioProduct_eq :
    frequencyKernelRatioProduct
        2
        rationalWitnessAlpha
        rationalWitnessBeta
        rationalWitnessObservationBatch
        rationalWitnessHigh
        rationalWitnessLow =
      65536 / 6561 := by
  rw [
    show rationalWitnessObservationBatch =
      [rationalWitnessObservation, rationalWitnessObservation] by rfl,
    frequencyKernelRatioProduct_cons,
    frequencyKernelRatioProduct_cons,
    frequencyKernelRatioProduct_nil,
    rationalWitnessHigh_kernel_eq,
    rationalWitnessLow_kernel_eq
  ]
  norm_num

/-- **FR.** Le produit des rapports de noyaux est le produit des deux
facteurs de Bayes unitaires.

**EN.** The kernel-ratio product is the product of the two single-cell
Bayes factors. -/
theorem rationalWitness_kernelRatioProduct_eq_singleBayesFactors :
    frequencyKernelRatioProduct
        2
        rationalWitnessAlpha
        rationalWitnessBeta
        rationalWitnessObservationBatch
        rationalWitnessHigh
        rationalWitnessLow =
      frequencyBayesFactor
          2
          rationalWitnessAlpha
          rationalWitnessBeta
          rationalWitnessHigh
          rationalWitnessLow
          rationalWitnessObservation *
        frequencyBayesFactor
          2
          rationalWitnessAlpha
          rationalWitnessBeta
          rationalWitnessHigh
          rationalWitnessLow
          rationalWitnessObservation := by
  rw [
    rationalWitness_kernelRatioProduct_eq,
    rationalWitness_bayesFactor_eq
  ]
  norm_num

private theorem rationalWitnessLow_kernel_ne_zero_on_batch :
    ∀ k ∈ rationalWitnessObservationBatch,
      frequencyCellKernel
          2
          rationalWitnessAlpha
          rationalWitnessBeta
          rationalWitnessLow
          k ≠ 0 := by
  intro k hk
  simp [rationalWitnessObservationBatch] at hk
  subst k
  rw [rationalWitnessLow_kernel_eq]
  norm_num

/-- **FR.** Le facteur de Bayes du lot vaut `65536/6561`.

**EN.** The batch Bayes factor is `65536/6561`. -/
theorem rationalWitness_batchBayesFactor_eq :
    rationalWitnessModel.finiteObservationBayesFactor
        rationalWitnessObservationBatch
        rationalWitnessHigh
        rationalWitnessLow =
      65536 / 6561 := by
  simpa [rationalWitnessModel] using
    (frequencyConfirmationModel_finiteObservationBayesFactor_eq_kernelRatioProduct
      2
      rationalWitnessPrior
      rationalWitnessAlpha
      rationalWitnessBeta
      rationalWitnessPrior_nonneg
      sum_rationalWitnessPrior_eq_one
      rationalWitnessAmplitudes_normalized
      rationalWitnessObservationBatch
      rationalWitnessHigh
      rationalWitnessLow
      rationalWitnessLow_kernel_ne_zero_on_batch).trans
      rationalWitness_kernelRatioProduct_eq

/-- **FR.** L'évidence globale du lot vaut `72097/781250`.

**EN.** The global batch evidence is `72097/781250`. -/
theorem rationalWitness_batchEvidence_eq :
    rationalWitnessModel.finiteObservationEvidence
        rationalWitnessObservationBatch =
      72097 / 781250 := by
  unfold FiniteBayesModel.finiteObservationEvidence
  rw [Fin.sum_univ_two]
  change
    rationalWitnessPrior rationalWitnessLow *
        rationalWitnessModel.observationLikelihoodProduct
          rationalWitnessObservationBatch rationalWitnessLow +
      rationalWitnessPrior rationalWitnessHigh *
        rationalWitnessModel.observationLikelihoodProduct
          rationalWitnessObservationBatch rationalWitnessHigh =
      72097 / 781250
  rw [
    rationalWitnessLow_likelihoodProduct_eq,
    rationalWitnessHigh_likelihoodProduct_eq
  ]
  norm_num [rationalWitnessPrior]

private theorem rationalWitness_firstEvidence_ne_zero :
    rationalWitnessModel.evidence
        rationalWitnessObservation ≠ 0 := by
  rw [rationalWitness_evidence_eq]
  norm_num

private theorem rationalWitness_batchEvidence_ne_zero :
    rationalWitnessModel.finiteObservationEvidence
        rationalWitnessObservationBatch ≠ 0 := by
  rw [rationalWitness_batchEvidence_eq]
  norm_num

/-- **FR.** Le posterior global bas du lot vaut `6561/72097`.

**EN.** The low global batch posterior is `6561/72097`. -/
theorem rationalWitnessLow_batchPosteriorWeight_eq :
    rationalWitnessModel.finiteObservationPosteriorWeight
        rationalWitnessObservationBatch
        rationalWitnessLow =
      6561 / 72097 := by
  unfold FiniteBayesModel.finiteObservationPosteriorWeight
  change
    rationalWitnessPrior rationalWitnessLow *
        rationalWitnessModel.observationLikelihoodProduct
          rationalWitnessObservationBatch rationalWitnessLow /
      rationalWitnessModel.finiteObservationEvidence
        rationalWitnessObservationBatch =
      6561 / 72097
  rw [
    rationalWitnessLow_likelihoodProduct_eq,
    rationalWitness_batchEvidence_eq
  ]
  norm_num [rationalWitnessPrior]

/-- **FR.** Le posterior global haut du lot vaut `65536/72097`.

**EN.** The high global batch posterior is `65536/72097`. -/
theorem rationalWitnessHigh_batchPosteriorWeight_eq :
    rationalWitnessModel.finiteObservationPosteriorWeight
        rationalWitnessObservationBatch
        rationalWitnessHigh =
      65536 / 72097 := by
  unfold FiniteBayesModel.finiteObservationPosteriorWeight
  change
    rationalWitnessPrior rationalWitnessHigh *
        rationalWitnessModel.observationLikelihoodProduct
          rationalWitnessObservationBatch rationalWitnessHigh /
      rationalWitnessModel.finiteObservationEvidence
        rationalWitnessObservationBatch =
      65536 / 72097
  rw [
    rationalWitnessHigh_likelihoodProduct_eq,
    rationalWitness_batchEvidence_eq
  ]
  norm_num [rationalWitnessPrior]

/-- **FR.** Les cotes postérieures globales du lot valent `65536/6561`.

**EN.** The global batch posterior odds are `65536/6561`. -/
theorem rationalWitness_batchPosteriorOdds_eq :
    rationalWitnessModel.finiteObservationPosteriorWeight
          rationalWitnessObservationBatch
          rationalWitnessHigh /
        rationalWitnessModel.finiteObservationPosteriorWeight
          rationalWitnessObservationBatch
          rationalWitnessLow =
      65536 / 6561 := by
  rw [
    rationalWitnessHigh_batchPosteriorWeight_eq,
    rationalWitnessLow_batchPosteriorWeight_eq
  ]
  norm_num

/-- **FR.** Les cotes postérieures globales sont le facteur de Bayes du
lot.

**EN.** The global posterior odds equal the batch Bayes factor. -/
theorem rationalWitness_batchPosteriorOdds_eq_bayesFactor :
    rationalWitnessModel.finiteObservationPosteriorWeight
          rationalWitnessObservationBatch
          rationalWitnessHigh /
        rationalWitnessModel.finiteObservationPosteriorWeight
          rationalWitnessObservationBatch
          rationalWitnessLow =
      rationalWitnessModel.finiteObservationBayesFactor
        rationalWitnessObservationBatch
        rationalWitnessHigh
        rationalWitnessLow := by
  rw [
    rationalWitness_batchPosteriorOdds_eq,
    rationalWitness_batchBayesFactor_eq
  ]

/-- **FR.** L'évidence de la seconde mise à jour vaut `72097/210625`.

**EN.** The evidence of the second update is `72097/210625`. -/
theorem rationalWitness_secondEvidence_eq :
    (rationalWitnessModel.posteriorUpdatedModel
        rationalWitnessObservation
        rationalWitness_firstEvidence_ne_zero).evidence
          rationalWitnessObservation =
      72097 / 210625 := by
  rw [
    rationalWitnessModel.posteriorUpdatedModel_evidence_eq
      rationalWitnessObservation
      rationalWitnessObservation
      rationalWitness_firstEvidence_ne_zero,
    ← rationalWitnessModel.finiteObservationEvidence_pair
      rationalWitnessObservation
      rationalWitnessObservation
  ]
  change
    rationalWitnessModel.finiteObservationEvidence
        rationalWitnessObservationBatch /
      rationalWitnessModel.evidence
        rationalWitnessObservation =
      72097 / 210625
  rw [
    rationalWitness_batchEvidence_eq,
    rationalWitness_evidence_eq
  ]
  norm_num

private theorem rationalWitness_secondEvidence_ne_zero :
    (rationalWitnessModel.posteriorUpdatedModel
        rationalWitnessObservation
        rationalWitness_firstEvidence_ne_zero).evidence
          rationalWitnessObservation ≠ 0 := by
  rw [rationalWitness_secondEvidence_eq]
  norm_num

/-- **FR.** Témoin séquentiel de non-nullité pour le lot de deux
observations.

**EN.** Sequential nonzero-evidence witness for the two-observation batch. -/
def rationalWitnessObservationBatchWitness :
    rationalWitnessModel.SequentialUpdateWitness
      rationalWitnessObservationBatch :=
  .cons
    rationalWitnessObservation
    [rationalWitnessObservation]
    rationalWitness_firstEvidence_ne_zero
    (.cons
      rationalWitnessObservation
      []
      rationalWitness_secondEvidence_ne_zero
      (.nil _))

/-- **FR.** Le prior itéré bas vaut `6561/72097`.

**EN.** The low iterated prior is `6561/72097`. -/
theorem rationalWitnessLow_iteratedPrior_eq :
    (rationalWitnessModel.iteratedPosteriorModel
        rationalWitnessObservationBatchWitness).prior
          rationalWitnessLow =
      6561 / 72097 := by
  exact
    (FiniteBayesModel.iteratedPosteriorModel_prior_eq_finiteObservationPosteriorWeight
      rationalWitnessModel
      rationalWitnessObservationBatchWitness
      rationalWitnessLow).trans
      rationalWitnessLow_batchPosteriorWeight_eq

/-- **FR.** Le prior itéré haut vaut `65536/72097`.

**EN.** The high iterated prior is `65536/72097`. -/
theorem rationalWitnessHigh_iteratedPrior_eq :
    (rationalWitnessModel.iteratedPosteriorModel
        rationalWitnessObservationBatchWitness).prior
          rationalWitnessHigh =
      65536 / 72097 := by
  exact
    (FiniteBayesModel.iteratedPosteriorModel_prior_eq_finiteObservationPosteriorWeight
      rationalWitnessModel
      rationalWitnessObservationBatchWitness
      rationalWitnessHigh).trans
      rationalWitnessHigh_batchPosteriorWeight_eq

/-- **FR.** Les cotes du prior itéré valent `65536/6561`.

**EN.** The iterated-prior odds are `65536/6561`. -/
theorem rationalWitness_iteratedPriorOdds_eq :
    (rationalWitnessModel.iteratedPosteriorModel
          rationalWitnessObservationBatchWitness).prior
            rationalWitnessHigh /
        (rationalWitnessModel.iteratedPosteriorModel
          rationalWitnessObservationBatchWitness).prior
            rationalWitnessLow =
      65536 / 6561 := by
  rw [
    rationalWitnessHigh_iteratedPrior_eq,
    rationalWitnessLow_iteratedPrior_eq
  ]
  norm_num

/-- **FR.** Le prior itéré bas est strictement inférieur au prior itéré
haut.

**EN.** The low iterated prior is strictly less than the high iterated
prior. -/
theorem rationalWitnessLow_iteratedPrior_lt_high :
    (rationalWitnessModel.iteratedPosteriorModel
        rationalWitnessObservationBatchWitness).prior
          rationalWitnessLow <
      (rationalWitnessModel.iteratedPosteriorModel
        rationalWitnessObservationBatchWitness).prior
          rationalWitnessHigh := by
  rw [
    rationalWitnessLow_iteratedPrior_eq,
    rationalWitnessHigh_iteratedPrior_eq
  ]
  norm_num

end
end EverettianProbability.Confirmation
