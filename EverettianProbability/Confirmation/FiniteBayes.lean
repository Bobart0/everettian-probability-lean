import Mathlib

/-!
**FR.** # Modèle bayésien fini

Ce module fournit un noyau bayésien entièrement fini, sans mesure,
`PMF`, variable aléatoire abstraite ni espace mesurable.

Un modèle comporte :

* une masse a priori sur un type fini d'hypothèses ;
* pour chaque hypothèse, une vraisemblance normalisée sur un type fini
  d'observations.

L'évidence d'une observation est la masse prédictive marginale. Le poids
a posteriori est défini par la formule de Bayes lorsque l'évidence est
non nulle. Avec la convention de division de `ℝ`, tous les poids
postérieurs valent `0` lorsque l'évidence vaut `0`.

Ce module est purement algébrique. Il ne prétend pas justifier le choix
des vraisemblances et ne contient aucune affirmation proprement
everettienne.

**EN.** # Finite Bayesian model

This module provides a fully finite Bayesian core, without measures,
`PMF`, abstract random variables, or measurable spaces.

A model consists of:

* a prior mass on a finite hypothesis type;
* for each hypothesis, a normalized likelihood on a finite observation
  type.

The evidence of an observation is its marginal predictive mass. The
posterior weight is defined by Bayes' formula when the evidence is
nonzero. Under the division convention of `ℝ`, all posterior weights are
`0` when the evidence is `0`.

This module is purely algebraic. It does not justify the choice of
likelihoods and makes no specifically Everettian claim.
-/

namespace EverettianProbability.Confirmation

open scoped Classical BigOperators

noncomputable section

/-- **FR.** Modèle bayésien sur des ensembles finis d'hypothèses et
d'observations.

**EN.** Bayesian model on finite hypothesis and observation types. -/
structure FiniteBayesModel
    (Θ Ω : Type*) [Fintype Θ] [Fintype Ω] where
  prior : Θ → ℝ
  likelihood : Θ → Ω → ℝ
  prior_nonneg : ∀ θ, 0 ≤ prior θ
  prior_sum_one : (∑ θ, prior θ) = 1
  likelihood_nonneg : ∀ θ ω, 0 ≤ likelihood θ ω
  likelihood_sum_one : ∀ θ, (∑ ω, likelihood θ ω) = 1

variable {Θ Ω : Type*} [Fintype Θ] [Fintype Ω]

/-- **FR.** Masse prédictive marginale, ou évidence, d'une observation.

**EN.** Marginal predictive mass, or evidence, of an observation. -/
def FiniteBayesModel.evidence
    (M : FiniteBayesModel Θ Ω) (ω : Ω) : ℝ :=
  ∑ θ, M.prior θ * M.likelihood θ ω

/-- **FR.** L'évidence est non négative.

**EN.** Evidence is nonnegative. -/
theorem FiniteBayesModel.evidence_nonneg
    (M : FiniteBayesModel Θ Ω) (ω : Ω) :
    0 ≤ M.evidence ω := by
  unfold FiniteBayesModel.evidence
  exact Finset.sum_nonneg fun θ _ =>
    mul_nonneg
      (M.prior_nonneg θ)
      (M.likelihood_nonneg θ ω)

/-- **FR.** Les évidences de toutes les observations somment à `1`.

**EN.** The evidences of all observations sum to `1`. -/
theorem FiniteBayesModel.sum_evidence_eq_one
    (M : FiniteBayesModel Θ Ω) :
    (∑ ω, M.evidence ω) = 1 := by
  classical
  unfold FiniteBayesModel.evidence
  calc
    (∑ ω, ∑ θ,
        M.prior θ * M.likelihood θ ω) =
        ∑ θ, ∑ ω,
          M.prior θ * M.likelihood θ ω := by
      rw [Finset.sum_comm]
    _ =
        ∑ θ,
          M.prior θ *
            (∑ ω, M.likelihood θ ω) := by
      apply Finset.sum_congr rfl
      intro θ hθ
      rw [Finset.mul_sum]
    _ = ∑ θ, M.prior θ := by
      apply Finset.sum_congr rfl
      intro θ hθ
      rw [M.likelihood_sum_one θ, mul_one]
    _ = 1 :=
      M.prior_sum_one

/-- **FR.** Poids a posteriori d'une hypothèse après observation.

Lorsque l'évidence est nulle, cette définition vaut `0` par convention
de division dans `ℝ`.

**EN.** Posterior weight of a hypothesis after an observation.

When the evidence is zero, this definition is `0` by the division
convention in `ℝ`. -/
def FiniteBayesModel.posteriorWeight
    (M : FiniteBayesModel Θ Ω) (ω : Ω) (θ : Θ) : ℝ :=
  M.prior θ * M.likelihood θ ω / M.evidence ω

/-- **FR.** Tout poids postérieur est non négatif.

**EN.** Every posterior weight is nonnegative. -/
theorem FiniteBayesModel.posteriorWeight_nonneg
    (M : FiniteBayesModel Θ Ω) (ω : Ω) (θ : Θ) :
    0 ≤ M.posteriorWeight ω θ := by
  unfold FiniteBayesModel.posteriorWeight
  exact
    div_nonneg
      (mul_nonneg
        (M.prior_nonneg θ)
        (M.likelihood_nonneg θ ω))
      (M.evidence_nonneg ω)

/-- **FR.** Lorsque l'évidence est non nulle, les poids postérieurs
somment à `1`.

**EN.** When the evidence is nonzero, posterior weights sum to `1`. -/
theorem FiniteBayesModel.sum_posteriorWeight_eq_one
    (M : FiniteBayesModel Θ Ω) (ω : Ω)
    (hevidence : M.evidence ω ≠ 0) :
    (∑ θ, M.posteriorWeight ω θ) = 1 := by
  classical
  unfold FiniteBayesModel.posteriorWeight
  rw [← Finset.sum_div]
  change M.evidence ω / M.evidence ω = 1
  exact div_self hevidence

/-- **FR.** Lorsque l'évidence est nulle, tous les poids postérieurs
somment à `0`.

**EN.** When the evidence is zero, all posterior weights sum to `0`. -/
theorem FiniteBayesModel.sum_posteriorWeight_eq_zero
    (M : FiniteBayesModel Θ Ω) (ω : Ω)
    (hevidence : M.evidence ω = 0) :
    (∑ θ, M.posteriorWeight ω θ) = 0 := by
  classical
  simp [
    FiniteBayesModel.posteriorWeight,
    hevidence
  ]

/-- **FR.** Forme multiplicative de la règle de Bayes lorsque l'évidence
est non nulle.

**EN.** Multiplicative form of Bayes' rule when the evidence is nonzero. -/
theorem FiniteBayesModel.posteriorWeight_mul_evidence
    (M : FiniteBayesModel Θ Ω) (ω : Ω) (θ : Θ)
    (hevidence : M.evidence ω ≠ 0) :
    M.posteriorWeight ω θ * M.evidence ω =
      M.prior θ * M.likelihood θ ω := by
  unfold FiniteBayesModel.posteriorWeight
  exact div_mul_cancel₀ _ hevidence

end
end EverettianProbability.Confirmation
