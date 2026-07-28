import EverettianProbability.Confirmation.FrequencyModel

/-!
**FR.** # Cotes postérieures et rapports de vraisemblance

Ce module établit la forme multiplicative de la mise à jour bayésienne
sur un modèle fini.

Pour deux hypothèses `θ₁` et `θ₂`, lorsque les dénominateurs pertinents
sont non nuls, le rapport de leurs poids postérieurs est égal au produit

`cotes a priori × rapport des vraisemblances`.

Dans le modèle fréquentiel de P11, le coefficient binomial commun à une
cellule observée s'annule dans le rapport des vraisemblances. Le facteur
informatif restant ne dépend que des poids élémentaires attribués par
chaque hypothèse aux deux résultats.

Cette formalisation demeure explicitement conditionnelle aux
vraisemblances borniennes fournies par P10. Elle ne constitue pas une
dérivation indépendante de ces vraisemblances.

**EN.** # Posterior odds and likelihood ratios

This module proves the multiplicative form of Bayesian updating in a
finite model.

For two hypotheses `θ₁` and `θ₂`, whenever the relevant denominators are
nonzero, the ratio of their posterior weights equals

`prior odds × likelihood ratio`.

In the P11 frequency model, the binomial coefficient shared by an
observed cell cancels from the likelihood ratio. The remaining
informative factor depends only on the elementary weights assigned by
each hypothesis to the two outcomes.

This formalization remains explicitly conditional on the Born
likelihoods supplied by P10. It is not an independent derivation of
those likelihoods.
-/

namespace EverettianProbability.Confirmation

open EverettianProbability.Frequency
open scoped Classical BigOperators

noncomputable section

variable {Θ Ω : Type*} [Fintype Θ] [Fintype Ω]

/-- **FR.** Forme sans division de la comparaison entre deux poids
postérieurs.

Elle reste vraie lorsque l'évidence est nulle, auquel cas les deux poids
postérieurs valent `0`.

**EN.** Division-free comparison between two posterior weights.

It remains true when the evidence is zero, in which case both posterior
weights are `0`. -/
theorem FiniteBayesModel.posteriorWeight_cross_mul
    (M : FiniteBayesModel Θ Ω)
    (ω : Ω) (θ₁ θ₂ : Θ) :
    M.posteriorWeight ω θ₁ *
        (M.prior θ₂ * M.likelihood θ₂ ω) =
      M.posteriorWeight ω θ₂ *
        (M.prior θ₁ * M.likelihood θ₁ ω) := by
  unfold FiniteBayesModel.posteriorWeight
  by_cases hevidence : M.evidence ω = 0
  · simp [hevidence]
  · field_simp [hevidence]

/-- **FR.** Règle des cotes postérieures :

`posterior₁ / posterior₂
   = (prior₁ / prior₂) × (likelihood₁ / likelihood₂)`.

**EN.** Posterior-odds rule:

`posterior₁ / posterior₂
   = (prior₁ / prior₂) × (likelihood₁ / likelihood₂)`. -/
theorem FiniteBayesModel.posteriorWeight_div_posteriorWeight_eq
    (M : FiniteBayesModel Θ Ω)
    (ω : Ω) (θ₁ θ₂ : Θ)
    (hevidence : M.evidence ω ≠ 0)
    (hprior₂ : M.prior θ₂ ≠ 0)
    (hlikelihood₂ : M.likelihood θ₂ ω ≠ 0) :
    M.posteriorWeight ω θ₁ /
        M.posteriorWeight ω θ₂ =
      (M.prior θ₁ / M.prior θ₂) *
        (M.likelihood θ₁ ω /
          M.likelihood θ₂ ω) := by
  unfold FiniteBayesModel.posteriorWeight
  field_simp [hevidence, hprior₂, hlikelihood₂]

end

section Frequency

noncomputable section

variable {Θ : Type*} [Fintype Θ]

/-- **FR.** Facteur propre à une hypothèse dans la vraisemblance d'une
cellule de fréquence, après retrait du coefficient binomial commun.

**EN.** Hypothesis-specific factor in the likelihood of a frequency cell,
after removing the common binomial coefficient. -/
def frequencyCellKernel
    (R : ℕ) (α β : Θ → ℂ)
    (θ : Θ) (k : Fin (R + 1)) : ℝ :=
  (‖α θ‖ ^ 2) ^ (R - k.val) *
    (‖β θ‖ ^ 2) ^ k.val

/-- **FR.** Le noyau fréquentiel propre à une hypothèse est non négatif.

**EN.** The hypothesis-specific frequency kernel is nonnegative. -/
theorem frequencyCellKernel_nonneg
    (R : ℕ) (α β : Θ → ℂ)
    (θ : Θ) (k : Fin (R + 1)) :
    0 ≤ frequencyCellKernel R α β θ k := by
  unfold frequencyCellKernel
  positivity

/-- **FR.** La vraisemblance d'une cellule est le produit du coefficient
binomial commun par le noyau propre à l'hypothèse.

**EN.** The likelihood of a cell is the product of the common binomial
coefficient and the hypothesis-specific kernel. -/
theorem frequencyLikelihood_eq_choose_mul_kernel
    (R : ℕ) (α β : Θ → ℂ)
    (θ : Θ) (k : Fin (R + 1)) :
    frequencyLikelihood R α β θ k =
      (Nat.choose R k.val : ℝ) *
        frequencyCellKernel R α β θ k := by
  simpa [frequencyCellKernel] using
    (frequencyLikelihood_eq_binomial R α β θ k)

private theorem frequencyChoose_cast_ne_zero
    (R : ℕ) (k : Fin (R + 1)) :
    (Nat.choose R k.val : ℝ) ≠ 0 := by
  have hk : k.val ≤ R :=
    Nat.lt_succ_iff.mp k.isLt
  exact_mod_cast (Nat.choose_ne_zero hk)

/-- **FR.** Dans le rapport des vraisemblances de deux hypothèses pour
une même cellule, le coefficient binomial commun s'annule.

**EN.** In the likelihood ratio of two hypotheses for the same cell, the
common binomial coefficient cancels. -/
theorem frequencyLikelihood_div_eq_kernel_div
    (R : ℕ) (α β : Θ → ℂ)
    (θ₁ θ₂ : Θ) (k : Fin (R + 1))
    (hkernel₂ :
      frequencyCellKernel R α β θ₂ k ≠ 0) :
    frequencyLikelihood R α β θ₁ k /
        frequencyLikelihood R α β θ₂ k =
      frequencyCellKernel R α β θ₁ k /
        frequencyCellKernel R α β θ₂ k := by
  rw [
    frequencyLikelihood_eq_choose_mul_kernel,
    frequencyLikelihood_eq_choose_mul_kernel
  ]
  have hchoose :=
    frequencyChoose_cast_ne_zero R k
  field_simp [hchoose, hkernel₂]

/-- **FR.** Mise à jour exacte des cotes entre deux hypothèses dans le
modèle fréquentiel.

Après observation de la cellule `k`, les cotes postérieures sont les
cotes a priori multipliées par le rapport des noyaux fréquentiels propres
aux deux hypothèses.

**EN.** Exact odds update between two hypotheses in the frequency model.

After observing cell `k`, posterior odds are prior odds multiplied by the
ratio of the two hypotheses' frequency kernels. -/
theorem frequencyConfirmationModel_posteriorWeight_div_eq
    (R : ℕ)
    (prior : Θ → ℝ)
    (α β : Θ → ℂ)
    (hprior_nonneg : ∀ θ, 0 ≤ prior θ)
    (hprior_sum_one : (∑ θ, prior θ) = 1)
    (hnorm :
      ∀ θ, ‖α θ‖ ^ 2 + ‖β θ‖ ^ 2 = 1)
    (θ₁ θ₂ : Θ)
    (k : Fin (R + 1))
    (hevidence :
      (frequencyConfirmationModel
        R prior α β
        hprior_nonneg hprior_sum_one hnorm).evidence k ≠ 0)
    (hprior₂ : prior θ₂ ≠ 0)
    (hkernel₂ :
      frequencyCellKernel R α β θ₂ k ≠ 0) :
    (frequencyConfirmationModel
        R prior α β
        hprior_nonneg hprior_sum_one hnorm).posteriorWeight k θ₁ /
      (frequencyConfirmationModel
        R prior α β
        hprior_nonneg hprior_sum_one hnorm).posteriorWeight k θ₂ =
      (prior θ₁ / prior θ₂) *
        (frequencyCellKernel R α β θ₁ k /
          frequencyCellKernel R α β θ₂ k) := by
  let M :=
    frequencyConfirmationModel
      R prior α β
      hprior_nonneg hprior_sum_one hnorm
  have hchoose :
      (Nat.choose R k.val : ℝ) ≠ 0 :=
    frequencyChoose_cast_ne_zero R k
  have hlikelihood₂ :
      frequencyLikelihood R α β θ₂ k ≠ 0 := by
    rw [frequencyLikelihood_eq_choose_mul_kernel]
    exact mul_ne_zero hchoose hkernel₂
  calc
    M.posteriorWeight k θ₁ /
        M.posteriorWeight k θ₂ =
      (prior θ₁ / prior θ₂) *
        (frequencyLikelihood R α β θ₁ k /
          frequencyLikelihood R α β θ₂ k) := by
      simpa [M, frequencyConfirmationModel] using
        (M.posteriorWeight_div_posteriorWeight_eq
          k θ₁ θ₂
          hevidence hprior₂ hlikelihood₂)
    _ =
      (prior θ₁ / prior θ₂) *
        (frequencyCellKernel R α β θ₁ k /
          frequencyCellKernel R α β θ₂ k) := by
      rw [
        frequencyLikelihood_div_eq_kernel_div
          R α β θ₁ θ₂ k hkernel₂
      ]

end
end Frequency

end EverettianProbability.Confirmation
