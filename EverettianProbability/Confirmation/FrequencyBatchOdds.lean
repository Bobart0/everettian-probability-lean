import EverettianProbability.Confirmation.BatchPosteriorOdds

/-!
**FR.** # Cotes postérieures pour des lots de cellules de fréquence

Ce module spécialise la règle générale des cotes postérieures à des listes
finies de cellules de fréquence. Pour une cellule, le coefficient binomial
commun s'annule du rapport entre deux hypothèses. Pour une liste, le facteur
de Bayes devient donc le produit des rapports de noyaux fréquentiels.

Sous les hypothèses explicites de non-nullité, les cotes postérieures
globales, puis celles du prior final obtenu par mise à jour itérée, sont les
cotes initiales multipliées par ce produit. Cette spécialisation utilise les
vraisemblances borniennes déjà établies ; elle n'introduit aucune hypothèse
vraie, consistance postérieure, ni justification indépendante de Born.

**EN.** # Posterior odds for batches of frequency cells

This module specializes the general posterior-odds rule to finite lists of
frequency cells. For one cell, the common binomial coefficient cancels from
the ratio between two hypotheses. For a list, the Bayes factor is therefore
the product of frequency-kernel ratios.

Under the explicit nonzero assumptions, global posterior odds, and then the
final-prior odds obtained by iterated updating, equal initial odds multiplied
by this product. This specialization uses the already established Born
likelihoods; it introduces no true hypothesis, posterior consistency, or
independent justification of the Born rule.
-/

namespace EverettianProbability.Confirmation

open EverettianProbability.Frequency
open scoped Classical BigOperators

noncomputable section

variable {Θ : Type*} [Fintype Θ]

/-- **FR.** Produit des rapports de noyaux fréquentiels pour une liste
finie de cellules.

**EN.** Product of frequency-kernel ratios for a finite list of cells. -/
def frequencyKernelRatioProduct
    (R : ℕ)
    (α β : Θ → ℂ)
    (observations : List (Fin (R + 1)))
    (θ₁ θ₂ : Θ) : ℝ :=
  (observations.map
    (fun k =>
      frequencyCellKernel R α β θ₁ k /
        frequencyCellKernel R α β θ₂ k)).prod

@[simp]
theorem frequencyKernelRatioProduct_nil
    (R : ℕ)
    (α β : Θ → ℂ)
    (θ₁ θ₂ : Θ) :
    frequencyKernelRatioProduct
        R α β [] θ₁ θ₂ = 1 := by
  simp [frequencyKernelRatioProduct]

@[simp]
theorem frequencyKernelRatioProduct_cons
    (R : ℕ)
    (α β : Θ → ℂ)
    (k : Fin (R + 1))
    (observations : List (Fin (R + 1)))
    (θ₁ θ₂ : Θ) :
    frequencyKernelRatioProduct
        R α β (k :: observations) θ₁ θ₂ =
      (frequencyCellKernel R α β θ₁ k /
        frequencyCellKernel R α β θ₂ k) *
      frequencyKernelRatioProduct
        R α β observations θ₁ θ₂ := by
  simp [frequencyKernelRatioProduct]

/-- **FR.** Le produit des rapports de noyaux fréquentiels est non
négatif.

**EN.** The frequency-kernel ratio product is nonnegative. -/
theorem frequencyKernelRatioProduct_nonneg
    (R : ℕ)
    (α β : Θ → ℂ)
    (observations : List (Fin (R + 1)))
    (θ₁ θ₂ : Θ) :
    0 ≤
      frequencyKernelRatioProduct
        R α β observations θ₁ θ₂ := by
  induction observations with
  | nil =>
      simp
  | cons k observations ih =>
      rw [
        frequencyKernelRatioProduct_cons
          R α β k observations θ₁ θ₂
      ]
      exact
        mul_nonneg
          (div_nonneg
            (frequencyCellKernel_nonneg
              R α β θ₁ k)
            (frequencyCellKernel_nonneg
              R α β θ₂ k))
          ih

/-- **FR.** Pour une liste de cellules, le produit des rapports de
vraisemblance du modèle fréquentiel est égal au produit des rapports de
noyaux, lorsque chaque noyau dénominateur est non nul.

**EN.** For a cell list, the frequency model's likelihood-ratio product
equals the kernel-ratio product when every denominator kernel is nonzero. -/
theorem frequencyConfirmationModel_likelihoodRatioProduct_eq_kernelRatioProduct
    (R : ℕ)
    (prior : Θ → ℝ)
    (α β : Θ → ℂ)
    (hprior_nonneg : ∀ θ, 0 ≤ prior θ)
    (hprior_sum_one : (∑ θ, prior θ) = 1)
    (hnorm :
      ∀ θ, ‖α θ‖ ^ 2 + ‖β θ‖ ^ 2 = 1)
    (observations : List (Fin (R + 1)))
    (θ₁ θ₂ : Θ)
    (hkernel₂ :
      ∀ k ∈ observations,
        frequencyCellKernel R α β θ₂ k ≠ 0) :
    (frequencyConfirmationModel
        R prior α β
        hprior_nonneg hprior_sum_one hnorm).observationLikelihoodRatioProduct
        observations θ₁ θ₂ =
      frequencyKernelRatioProduct
        R α β observations θ₁ θ₂ := by
  induction observations with
  | nil =>
      simp
  | cons k observations ih =>
      have hk :
          frequencyCellKernel R α β θ₂ k ≠ 0 :=
        hkernel₂ k (by simp)
      have htail :
          ∀ k' ∈ observations,
            frequencyCellKernel R α β θ₂ k' ≠ 0 := by
        intro k' hk'
        exact hkernel₂ k' (by simp [hk'])
      rw [
        FiniteBayesModel.observationLikelihoodRatioProduct_cons,
        frequencyKernelRatioProduct_cons
      ]
      change
        (frequencyLikelihood R α β θ₁ k /
          frequencyLikelihood R α β θ₂ k) *
          FiniteBayesModel.observationLikelihoodRatioProduct
            (frequencyConfirmationModel
              R prior α β
              hprior_nonneg hprior_sum_one hnorm)
            observations θ₁ θ₂ =
          frequencyCellKernel R α β θ₁ k /
            frequencyCellKernel R α β θ₂ k *
              frequencyKernelRatioProduct
                R α β observations θ₁ θ₂
      rw [
        frequencyLikelihood_div_eq_kernel_div
          R α β θ₁ θ₂ k hk,
        ih htail
      ]

/-- **FR.** La non-nullité d'un noyau fréquentiel implique celle de la
vraisemblance correspondante.

**EN.** Nonzero frequency kernel implies nonzero corresponding
likelihood. -/
theorem frequencyLikelihood_ne_zero_of_kernel_ne_zero
    (R : ℕ)
    (α β : Θ → ℂ)
    (θ : Θ)
    (k : Fin (R + 1))
    (hkernel :
      frequencyCellKernel R α β θ k ≠ 0) :
    frequencyLikelihood R α β θ k ≠ 0 := by
  rw [frequencyLikelihood_eq_choose_mul_kernel]
  apply mul_ne_zero
  · have hk : k.val ≤ R :=
      Nat.lt_succ_iff.mp k.isLt
    exact_mod_cast (Nat.choose_ne_zero hk)
  · exact hkernel

/-- **FR.** Si chaque noyau dénominateur est non nul, chaque
vraisemblance dénominateur du lot est non nulle.

**EN.** If every denominator kernel is nonzero, every denominator
likelihood in the batch is nonzero. -/
theorem frequencyConfirmationModel_likelihood_ne_zero_of_kernel_ne_zero
    (R : ℕ)
    (prior : Θ → ℝ)
    (α β : Θ → ℂ)
    (hprior_nonneg : ∀ θ, 0 ≤ prior θ)
    (hprior_sum_one : (∑ θ, prior θ) = 1)
    (hnorm :
      ∀ θ, ‖α θ‖ ^ 2 + ‖β θ‖ ^ 2 = 1)
    (observations : List (Fin (R + 1)))
    (θ : Θ)
    (hkernel :
      ∀ k ∈ observations,
        frequencyCellKernel R α β θ k ≠ 0) :
    ∀ k ∈ observations,
      (frequencyConfirmationModel
        R prior α β
        hprior_nonneg hprior_sum_one hnorm).likelihood θ k ≠ 0 := by
  intro k hk
  change frequencyLikelihood R α β θ k ≠ 0
  exact
    frequencyLikelihood_ne_zero_of_kernel_ne_zero
      R α β θ k (hkernel k hk)

/-- **FR.** Le facteur de Bayes d'un lot de cellules de fréquence est le
produit des rapports de noyaux lorsque tous les noyaux dénominateurs sont
non nuls.

**EN.** The Bayes factor of a frequency-cell batch is the kernel-ratio
product when all denominator kernels are nonzero. -/
theorem frequencyConfirmationModel_finiteObservationBayesFactor_eq_kernelRatioProduct
    (R : ℕ)
    (prior : Θ → ℝ)
    (α β : Θ → ℂ)
    (hprior_nonneg : ∀ θ, 0 ≤ prior θ)
    (hprior_sum_one : (∑ θ, prior θ) = 1)
    (hnorm :
      ∀ θ, ‖α θ‖ ^ 2 + ‖β θ‖ ^ 2 = 1)
    (observations : List (Fin (R + 1)))
    (θ₁ θ₂ : Θ)
    (hkernel₂ :
      ∀ k ∈ observations,
        frequencyCellKernel R α β θ₂ k ≠ 0) :
    (frequencyConfirmationModel
        R prior α β
        hprior_nonneg hprior_sum_one hnorm).finiteObservationBayesFactor
        observations θ₁ θ₂ =
      frequencyKernelRatioProduct
        R α β observations θ₁ θ₂ := by
  let M :=
    frequencyConfirmationModel
      R prior α β
      hprior_nonneg hprior_sum_one hnorm
  have hlikelihood₂ :
      ∀ k ∈ observations,
        M.likelihood θ₂ k ≠ 0 := by
    simpa [M] using
      frequencyConfirmationModel_likelihood_ne_zero_of_kernel_ne_zero
        R prior α β
        hprior_nonneg hprior_sum_one hnorm
        observations θ₂ hkernel₂
  calc
    M.finiteObservationBayesFactor
        observations θ₁ θ₂ =
      M.observationLikelihoodRatioProduct
        observations θ₁ θ₂ := by
      exact
        M.finiteObservationBayesFactor_eq_ratioProduct
          observations θ₁ θ₂ hlikelihood₂
    _ =
      frequencyKernelRatioProduct
        R α β observations θ₁ θ₂ := by
      simpa [M] using
        frequencyConfirmationModel_likelihoodRatioProduct_eq_kernelRatioProduct
          R prior α β
          hprior_nonneg hprior_sum_one hnorm
          observations θ₁ θ₂ hkernel₂

/-- **FR.** Dans le modèle fréquentiel, les cotes postérieures globales
d'un lot sont les cotes a priori multipliées par le produit des rapports
de noyaux fréquentiels.

**EN.** In the frequency model, global posterior odds for a batch are
prior odds multiplied by the frequency-kernel ratio product. -/
theorem frequencyConfirmationModel_finiteObservationPosteriorOdds_eq
    (R : ℕ)
    (prior : Θ → ℝ)
    (α β : Θ → ℂ)
    (hprior_nonneg : ∀ θ, 0 ≤ prior θ)
    (hprior_sum_one : (∑ θ, prior θ) = 1)
    (hnorm :
      ∀ θ, ‖α θ‖ ^ 2 + ‖β θ‖ ^ 2 = 1)
    (observations : List (Fin (R + 1)))
    (θ₁ θ₂ : Θ)
    (hevidence :
      (frequencyConfirmationModel
        R prior α β
        hprior_nonneg hprior_sum_one hnorm).finiteObservationEvidence observations ≠ 0)
    (hprior₂ :
      prior θ₂ ≠ 0)
    (hkernel₂ :
      ∀ k ∈ observations,
        frequencyCellKernel R α β θ₂ k ≠ 0) :
    (frequencyConfirmationModel
        R prior α β
        hprior_nonneg hprior_sum_one hnorm).finiteObservationPosteriorWeight observations θ₁ /
      (frequencyConfirmationModel
        R prior α β
        hprior_nonneg hprior_sum_one hnorm).finiteObservationPosteriorWeight observations θ₂ =
      (prior θ₁ / prior θ₂) *
        frequencyKernelRatioProduct
          R α β observations θ₁ θ₂ := by
  let M :=
    frequencyConfirmationModel
      R prior α β
      hprior_nonneg hprior_sum_one hnorm
  have hlikelihood₂ :
      ∀ k ∈ observations,
        M.likelihood θ₂ k ≠ 0 := by
    simpa [M] using
      frequencyConfirmationModel_likelihood_ne_zero_of_kernel_ne_zero
        R prior α β
        hprior_nonneg hprior_sum_one hnorm
        observations θ₂ hkernel₂
  calc
    M.finiteObservationPosteriorWeight observations θ₁ /
        M.finiteObservationPosteriorWeight observations θ₂ =
      (M.prior θ₁ / M.prior θ₂) *
        M.observationLikelihoodRatioProduct
          observations θ₁ θ₂ := by
      exact
        M.finiteObservationPosteriorOdds_eq_priorOdds_mul_ratioProduct
          observations θ₁ θ₂
          hevidence hprior₂ hlikelihood₂
    _ =
      (prior θ₁ / prior θ₂) *
        frequencyKernelRatioProduct
          R α β observations θ₁ θ₂ := by
      rw [
        frequencyConfirmationModel_likelihoodRatioProduct_eq_kernelRatioProduct
          R prior α β
          hprior_nonneg hprior_sum_one hnorm
          observations θ₁ θ₂ hkernel₂
      ]
      change
        (prior θ₁ / prior θ₂) *
            frequencyKernelRatioProduct
              R α β observations θ₁ θ₂ =
          (prior θ₁ / prior θ₂) *
            frequencyKernelRatioProduct
              R α β observations θ₁ θ₂
      rfl

/-- **FR.** Pour un modèle fréquentiel mis à jour observation par
observation, les cotes du prior final sont les cotes initiales
multipliées par le produit des rapports de noyaux.

**EN.** For a frequency model updated observation by observation, final
prior odds equal initial odds multiplied by the kernel-ratio product. -/
theorem frequencyConfirmationModel_iteratedPriorOdds_eq
    (R : ℕ)
    (prior : Θ → ℝ)
    (α β : Θ → ℂ)
    (hprior_nonneg : ∀ θ, 0 ≤ prior θ)
    (hprior_sum_one : (∑ θ, prior θ) = 1)
    (hnorm :
      ∀ θ, ‖α θ‖ ^ 2 + ‖β θ‖ ^ 2 = 1)
    {observations : List (Fin (R + 1))}
    (witness :
      (frequencyConfirmationModel
        R prior α β
        hprior_nonneg hprior_sum_one hnorm).SequentialUpdateWitness observations)
    (θ₁ θ₂ : Θ)
    (hprior₂ :
      prior θ₂ ≠ 0)
    (hkernel₂ :
      ∀ k ∈ observations,
        frequencyCellKernel R α β θ₂ k ≠ 0) :
    ((frequencyConfirmationModel
        R prior α β
        hprior_nonneg hprior_sum_one hnorm).iteratedPosteriorModel witness).prior θ₁ /
      ((frequencyConfirmationModel
        R prior α β
        hprior_nonneg hprior_sum_one hnorm).iteratedPosteriorModel witness).prior θ₂ =
      (prior θ₁ / prior θ₂) *
        frequencyKernelRatioProduct
          R α β observations θ₁ θ₂ := by
  let M :=
    frequencyConfirmationModel
      R prior α β
      hprior_nonneg hprior_sum_one hnorm
  have hevidence :
      M.finiteObservationEvidence observations ≠ 0 :=
    witness.finiteObservationEvidence_ne_zero
  rw [
    M.iteratedPosteriorModel_prior_eq_finiteObservationPosteriorWeight
      witness θ₁,
    M.iteratedPosteriorModel_prior_eq_finiteObservationPosteriorWeight
      witness θ₂
  ]
  simpa [M] using
    frequencyConfirmationModel_finiteObservationPosteriorOdds_eq
      R prior α β
      hprior_nonneg hprior_sum_one hnorm
      observations θ₁ θ₂
      hevidence hprior₂ hkernel₂

end
end EverettianProbability.Confirmation
