import EverettianProbability.Confirmation.PosteriorOdds

/-!
**FR.** # Comparaison finie entre hypothèses

Ce module précise le sens algébrique selon lequel une observation
« favorise » une hypothèse dans le modèle bayésien fini.

Dans un modèle général, lorsque l'évidence est strictement positive,
l'ordre entre deux poids postérieurs est exactement l'ordre entre leurs
masses conjointes

`prior × likelihood`.

Dans le modèle fréquentiel, le facteur de Bayes associé à une cellule
est le rapport des noyaux fréquentiels propres aux deux hypothèses. À
priors égaux et strictement positifs, une hypothèse reçoit un poids
postérieur plus élevé exactement lorsque son noyau fréquentiel est plus
élevé pour la cellule observée.

Le terme « favorise » désigne uniquement cette comparaison de
vraisemblances et de poids postérieurs. Aucun statut de vérité, aucune
distance à une hypothèse vraie et aucune consistance asymptotique ne sont
introduits.

**EN.** # Finite comparison between hypotheses

This module makes precise the algebraic sense in which an observation
“favors” a hypothesis in the finite Bayesian model.

In a general model, when the evidence is strictly positive, the ordering
of two posterior weights is exactly the ordering of their joint masses

`prior × likelihood`.

In the frequency model, the Bayes factor associated with a cell is the
ratio of the two hypotheses' frequency kernels. Under equal, strictly
positive priors, a hypothesis receives a larger posterior weight exactly
when its frequency kernel is larger for the observed cell.

The term “favors” refers only to this comparison of likelihoods and
posterior weights. No truth status, distance from a true hypothesis, or
asymptotic consistency is introduced.
-/

namespace EverettianProbability.Confirmation

open EverettianProbability.Frequency
open scoped Classical BigOperators

noncomputable section

variable {Θ Ω : Type*} [Fintype Θ] [Fintype Ω]

/-- **FR.** Lorsque l'évidence est strictement positive, comparer deux
poids postérieurs revient exactement à comparer leurs masses conjointes
`prior × likelihood`.

**EN.** When the evidence is strictly positive, comparing two posterior
weights is exactly the same as comparing their joint masses
`prior × likelihood`. -/
theorem FiniteBayesModel.posteriorWeight_lt_iff_jointWeight_lt
    (M : FiniteBayesModel Θ Ω)
    (ω : Ω) (θ₁ θ₂ : Θ)
    (hevidence : 0 < M.evidence ω) :
    M.posteriorWeight ω θ₁ <
        M.posteriorWeight ω θ₂ ↔
      M.prior θ₁ * M.likelihood θ₁ ω <
        M.prior θ₂ * M.likelihood θ₂ ω := by
  unfold FiniteBayesModel.posteriorWeight
  exact div_lt_div_iff_of_pos_right hevidence

/-- **FR.** Sous évidence strictement positive, deux poids postérieurs
sont égaux exactement lorsque leurs masses conjointes sont égales.

**EN.** Under strictly positive evidence, two posterior weights are equal
exactly when their joint masses are equal. -/
theorem FiniteBayesModel.posteriorWeight_eq_iff_jointWeight_eq
    (M : FiniteBayesModel Θ Ω)
    (ω : Ω) (θ₁ θ₂ : Θ)
    (hevidence : 0 < M.evidence ω) :
    M.posteriorWeight ω θ₁ =
        M.posteriorWeight ω θ₂ ↔
      M.prior θ₁ * M.likelihood θ₁ ω =
        M.prior θ₂ * M.likelihood θ₂ ω := by
  have hevidence0 : M.evidence ω ≠ 0 :=
    ne_of_gt hevidence
  unfold FiniteBayesModel.posteriorWeight
  exact div_left_inj' hevidence0

end

section FrequencyComparison

noncomputable section

variable {Θ : Type*} [Fintype Θ]

/-- **FR.** Facteur de Bayes fourni par une cellule de fréquence pour
comparer `θ₁` à `θ₂`.

**EN.** Bayes factor supplied by a frequency cell for comparing `θ₁`
with `θ₂`. -/
def frequencyBayesFactor
    (R : ℕ) (α β : Θ → ℂ)
    (θ₁ θ₂ : Θ) (k : Fin (R + 1)) : ℝ :=
  frequencyCellKernel R α β θ₁ k /
    frequencyCellKernel R α β θ₂ k

/-- **FR.** Le facteur de Bayes fréquentiel est non négatif.

**EN.** The frequency Bayes factor is nonnegative. -/
theorem frequencyBayesFactor_nonneg
    (R : ℕ) (α β : Θ → ℂ)
    (θ₁ θ₂ : Θ) (k : Fin (R + 1)) :
    0 ≤ frequencyBayesFactor R α β θ₁ θ₂ k := by
  unfold frequencyBayesFactor
  exact
    div_nonneg
      (frequencyCellKernel_nonneg R α β θ₁ k)
      (frequencyCellKernel_nonneg R α β θ₂ k)

/-- **FR.** Lorsque le noyau de `θ₂` est strictement positif, le facteur
de Bayes en faveur de `θ₁` est supérieur à `1` exactement lorsque le
noyau de `θ₁` est supérieur à celui de `θ₂`.

**EN.** When the kernel of `θ₂` is strictly positive, the Bayes factor in
favor of `θ₁` exceeds `1` exactly when the kernel of `θ₁` exceeds that of
`θ₂`. -/
theorem one_lt_frequencyBayesFactor_iff
    (R : ℕ) (α β : Θ → ℂ)
    (θ₁ θ₂ : Θ) (k : Fin (R + 1))
    (hkernel₂ :
      0 < frequencyCellKernel R α β θ₂ k) :
    1 < frequencyBayesFactor R α β θ₁ θ₂ k ↔
      frequencyCellKernel R α β θ₂ k <
        frequencyCellKernel R α β θ₁ k := by
  unfold frequencyBayesFactor
  exact one_lt_div hkernel₂

/-- **FR.** Dans le modèle fréquentiel, les cotes postérieures sont les
cotes a priori multipliées par le facteur de Bayes de la cellule
observée.

**EN.** In the frequency model, posterior odds are prior odds multiplied
by the Bayes factor of the observed cell. -/
theorem frequencyConfirmationModel_posteriorOdds_eq_priorOdds_mul_bayesFactor
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
        frequencyBayesFactor R α β θ₁ θ₂ k := by
  simpa [frequencyBayesFactor] using
    (frequencyConfirmationModel_posteriorWeight_div_eq
      R prior α β
      hprior_nonneg hprior_sum_one hnorm
      θ₁ θ₂ k
      hevidence hprior₂ hkernel₂)

/-- **FR.** À priors égaux et strictement positifs, les cotes
postérieures sont exactement le facteur de Bayes de la cellule observée.

**EN.** Under equal, strictly positive priors, posterior odds are exactly
the Bayes factor of the observed cell. -/
theorem frequencyConfirmationModel_posteriorOdds_eq_bayesFactor_of_equal_prior
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
    (hprior_eq : prior θ₁ = prior θ₂)
    (hprior_pos : 0 < prior θ₁)
    (hkernel₂ :
      frequencyCellKernel R α β θ₂ k ≠ 0) :
    (frequencyConfirmationModel
        R prior α β
        hprior_nonneg hprior_sum_one hnorm).posteriorWeight k θ₁ /
      (frequencyConfirmationModel
        R prior α β
        hprior_nonneg hprior_sum_one hnorm).posteriorWeight k θ₂ =
      frequencyBayesFactor R α β θ₁ θ₂ k := by
  have hprior₂ : prior θ₂ ≠ 0 := by
    rw [← hprior_eq]
    exact ne_of_gt hprior_pos
  rw [
    frequencyConfirmationModel_posteriorOdds_eq_priorOdds_mul_bayesFactor
      R prior α β
      hprior_nonneg hprior_sum_one hnorm
      θ₁ θ₂ k
      hevidence hprior₂ hkernel₂
  ]
  have hratio : prior θ₁ / prior θ₂ = 1 := by
    rw [hprior_eq, div_self hprior₂]
  rw [hratio, one_mul]

/-- **FR.** À priors égaux et strictement positifs, l'ordre des poids
postérieurs est exactement l'ordre des noyaux fréquentiels de la cellule
observée.

Ainsi, dans le sens strictement bayésien utilisé ici, la cellule
« favorise » `θ₂` plutôt que `θ₁` exactement lorsque son noyau sous
`θ₂` est supérieur à son noyau sous `θ₁`.

**EN.** Under equal, strictly positive priors, the ordering of posterior
weights is exactly the ordering of the frequency kernels for the
observed cell.

Thus, in the strictly Bayesian sense used here, the cell “favors” `θ₂`
over `θ₁` exactly when its kernel under `θ₂` exceeds its kernel under
`θ₁`. -/
theorem frequencyConfirmationModel_posteriorWeight_lt_iff_kernel_lt_of_equal_prior
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
      0 <
        (frequencyConfirmationModel
          R prior α β
          hprior_nonneg hprior_sum_one hnorm).evidence k)
    (hprior_eq : prior θ₁ = prior θ₂)
    (hprior_pos : 0 < prior θ₁) :
    (frequencyConfirmationModel
        R prior α β
        hprior_nonneg hprior_sum_one hnorm).posteriorWeight k θ₁ <
      (frequencyConfirmationModel
        R prior α β
        hprior_nonneg hprior_sum_one hnorm).posteriorWeight k θ₂ ↔
      frequencyCellKernel R α β θ₁ k <
        frequencyCellKernel R α β θ₂ k := by
  let M :=
    frequencyConfirmationModel
      R prior α β
      hprior_nonneg hprior_sum_one hnorm
  rw [
    M.posteriorWeight_lt_iff_jointWeight_lt
      k θ₁ θ₂ hevidence
  ]
  change
    prior θ₁ * frequencyLikelihood R α β θ₁ k <
        prior θ₂ * frequencyLikelihood R α β θ₂ k ↔
      frequencyCellKernel R α β θ₁ k <
        frequencyCellKernel R α β θ₂ k
  rw [← hprior_eq]
  rw [
    frequencyLikelihood_eq_choose_mul_kernel,
    frequencyLikelihood_eq_choose_mul_kernel
  ]
  have hk : k.val ≤ R :=
    Nat.lt_succ_iff.mp k.isLt
  have hchoose :
      0 < (Nat.choose R k.val : ℝ) := by
    exact_mod_cast (Nat.choose_pos hk)
  have hfactor :
      0 <
        prior θ₁ *
          (Nat.choose R k.val : ℝ) :=
    mul_pos hprior_pos hchoose
  constructor
  · intro h
    apply lt_of_mul_lt_mul_left _ hfactor.le
    simpa [mul_assoc] using h
  · intro h
    simpa [mul_assoc] using
      (mul_lt_mul_of_pos_left h hfactor)

end
end FrequencyComparison

end EverettianProbability.Confirmation
