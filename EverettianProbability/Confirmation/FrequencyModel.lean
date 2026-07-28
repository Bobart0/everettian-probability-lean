import EverettianProbability.Confirmation.FiniteBayes
import EverettianProbability.Frequency.AsymptoticTypicality

/-!
**FR.** # Modèle bayésien fini pour les fréquences everettiennes

Ce module instancie le noyau bayésien fini avec les masses projectives
des cellules de fréquence établies dans P10.

Chaque hypothèse `θ` fournit deux amplitudes complexes `α θ` et `β θ`.
Sous l'hypothèse

`‖α θ‖² + ‖β θ‖² = 1`,

la fonction

`k ↦ frequencyMass R (α θ) (β θ) k`

est une vraisemblance normalisée sur les `R + 1` cellules de fréquence.

Cette formalisation est volontairement conditionnelle : elle utilise les
poids borniens déjà calibrés comme vraisemblances. Elle ne constitue pas
une justification indépendante de la règle de Born et ne doit pas être
présentée comme telle.

**EN.** # Finite Bayesian model for Everettian frequencies

This module instantiates the finite Bayesian core with the projective
masses of frequency cells established in P10.

Each hypothesis `θ` supplies two complex amplitudes `α θ` and `β θ`.
Under the hypothesis

`‖α θ‖² + ‖β θ‖² = 1`,

the function

`k ↦ frequencyMass R (α θ) (β θ) k`

is a normalized likelihood on the `R + 1` frequency cells.

This formalization is deliberately conditional: it uses already
calibrated Born weights as likelihoods. It is not an independent
justification of the Born rule and must not be presented as one.
-/

namespace EverettianProbability.Confirmation

open EverettianProbability.Frequency
open scoped Classical BigOperators

noncomputable section

variable {Θ : Type*} [Fintype Θ]

/-- **FR.** Vraisemblance d'observer la cellule de fréquence `k` sous
l'hypothèse `θ`.

**EN.** Likelihood of observing frequency cell `k` under hypothesis
`θ`. -/
def frequencyLikelihood
    (R : ℕ) (α β : Θ → ℂ)
    (θ : Θ) (k : Fin (R + 1)) : ℝ :=
  frequencyMass R (α θ) (β θ) k

/-- **FR.** La vraisemblance fréquentielle est non négative.

**EN.** The frequency likelihood is nonnegative. -/
theorem frequencyLikelihood_nonneg
    (R : ℕ) (α β : Θ → ℂ)
    (θ : Θ) (k : Fin (R + 1)) :
    0 ≤ frequencyLikelihood R α β θ k := by
  exact frequencyMass_nonneg R (α θ) (β θ) k

/-- **FR.** Formule binomiale exacte de la vraisemblance fréquentielle.

**EN.** Exact binomial formula for the frequency likelihood. -/
theorem frequencyLikelihood_eq_binomial
    (R : ℕ) (α β : Θ → ℂ)
    (θ : Θ) (k : Fin (R + 1)) :
    frequencyLikelihood R α β θ k =
      (Nat.choose R k.val : ℝ) *
        ((‖α θ‖ ^ 2) ^ (R - k.val) *
          (‖β θ‖ ^ 2) ^ k.val) := by
  exact frequencyMass_eq_binomial R (α θ) (β θ) k

/-- **FR.** Sous normalisation de l'hypothèse, les vraisemblances de
toutes les cellules de fréquence somment à `1`.

**EN.** Under normalization of the hypothesis, the likelihoods of all
frequency cells sum to `1`. -/
theorem sum_frequencyLikelihood_eq_one
    (R : ℕ) (α β : Θ → ℂ) (θ : Θ)
    (hnorm :
      ‖α θ‖ ^ 2 + ‖β θ‖ ^ 2 = 1) :
    (∑ k : Fin (R + 1),
      frequencyLikelihood R α β θ k) = 1 := by
  exact sum_frequencyMass_eq_one R (α θ) (β θ) hnorm

/-- **FR.** Modèle bayésien fini dont les vraisemblances sont les masses
projectives des cellules de fréquence.

**EN.** Finite Bayesian model whose likelihoods are the projective masses
of frequency cells. -/
def frequencyConfirmationModel
    (R : ℕ)
    (prior : Θ → ℝ)
    (α β : Θ → ℂ)
    (hprior_nonneg : ∀ θ, 0 ≤ prior θ)
    (hprior_sum_one : (∑ θ, prior θ) = 1)
    (hnorm :
      ∀ θ, ‖α θ‖ ^ 2 + ‖β θ‖ ^ 2 = 1) :
    FiniteBayesModel Θ (Fin (R + 1)) where
  prior := prior
  likelihood := frequencyLikelihood R α β
  prior_nonneg := hprior_nonneg
  prior_sum_one := hprior_sum_one
  likelihood_nonneg := by
    intro θ k
    exact frequencyLikelihood_nonneg R α β θ k
  likelihood_sum_one := by
    intro θ
    exact sum_frequencyLikelihood_eq_one R α β θ (hnorm θ)

/-- **FR.** L'évidence du modèle de fréquence est la somme des produits
`prior × frequencyMass` sur les hypothèses.

**EN.** Evidence in the frequency model is the sum of
`prior × frequencyMass` over hypotheses. -/
theorem frequencyConfirmationModel_evidence_eq
    (R : ℕ)
    (prior : Θ → ℝ)
    (α β : Θ → ℂ)
    (hprior_nonneg : ∀ θ, 0 ≤ prior θ)
    (hprior_sum_one : (∑ θ, prior θ) = 1)
    (hnorm :
      ∀ θ, ‖α θ‖ ^ 2 + ‖β θ‖ ^ 2 = 1)
    (k : Fin (R + 1)) :
    (frequencyConfirmationModel
        R prior α β
        hprior_nonneg hprior_sum_one hnorm).evidence k =
      ∑ θ,
        prior θ *
          frequencyMass R (α θ) (β θ) k := by
  rfl

/-- **FR.** La distribution prédictive des cellules de fréquence est
normalisée.

**EN.** The predictive distribution of frequency cells is normalized. -/
theorem sum_frequencyConfirmationModel_evidence_eq_one
    (R : ℕ)
    (prior : Θ → ℝ)
    (α β : Θ → ℂ)
    (hprior_nonneg : ∀ θ, 0 ≤ prior θ)
    (hprior_sum_one : (∑ θ, prior θ) = 1)
    (hnorm :
      ∀ θ, ‖α θ‖ ^ 2 + ‖β θ‖ ^ 2 = 1) :
    (∑ k : Fin (R + 1),
      (frequencyConfirmationModel
        R prior α β
        hprior_nonneg hprior_sum_one hnorm).evidence k) = 1 := by
  exact
    (frequencyConfirmationModel
      R prior α β
      hprior_nonneg hprior_sum_one hnorm).sum_evidence_eq_one

/-- **FR.** Si l'évidence de la cellule observée est non nulle, les poids
postérieurs des hypothèses somment à `1`.

**EN.** If the evidence of the observed cell is nonzero, posterior
hypothesis weights sum to `1`. -/
theorem sum_frequencyConfirmationModel_posteriorWeight_eq_one
    (R : ℕ)
    (prior : Θ → ℝ)
    (α β : Θ → ℂ)
    (hprior_nonneg : ∀ θ, 0 ≤ prior θ)
    (hprior_sum_one : (∑ θ, prior θ) = 1)
    (hnorm :
      ∀ θ, ‖α θ‖ ^ 2 + ‖β θ‖ ^ 2 = 1)
    (k : Fin (R + 1))
    (hevidence :
      (frequencyConfirmationModel
        R prior α β
        hprior_nonneg hprior_sum_one hnorm).evidence k ≠ 0) :
    (∑ θ,
      (frequencyConfirmationModel
        R prior α β
        hprior_nonneg hprior_sum_one hnorm).posteriorWeight k θ) = 1 := by
  exact
    (frequencyConfirmationModel
      R prior α β
      hprior_nonneg hprior_sum_one hnorm).sum_posteriorWeight_eq_one
        k hevidence

end
end EverettianProbability.Confirmation
