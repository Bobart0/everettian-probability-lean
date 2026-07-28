import EverettianProbability.Confirmation.HypothesisComparison

/-!
**FR.** # Témoin rationnel de confirmation bayésienne

Ce module donne un exemple entièrement calculé du modèle de confirmation
fini.

Deux hypothèses attribuent respectivement au résultat `1` les poids
élémentaires `9/25` et `16/25`. Les priors sont égaux à `1/2`.
Après deux répétitions et l'observation de la cellule `k = 2`, les
vraisemblances valent respectivement

`81/625` et `256/625`.

L'évidence vaut `337/1250`, et les poids postérieurs deviennent
exactement

`81/337` et `256/337`.

Le témoin établit ainsi une modification non triviale des cotes à partir
des vraisemblances borniennes déjà acquises. Il ne désigne aucune
hypothèse comme vraie et ne constitue pas une justification indépendante
de la règle de Born.

**EN.** # Rational witness of Bayesian confirmation

This module gives a fully calculated example of the finite confirmation
model.

Two hypotheses assign elementary weights `9/25` and `16/25`,
respectively, to outcome `1`. Both priors are `1/2`. After two
repetitions and observation of cell `k = 2`, the likelihoods are

`81/625` and `256/625`.

The evidence is `337/1250`, and the posterior weights become exactly

`81/337` and `256/337`.

The witness therefore exhibits a nontrivial odds update from already
established Born likelihoods. It does not designate either hypothesis as
true and is not an independent justification of the Born rule.
-/

namespace EverettianProbability.Confirmation

open EverettianProbability.Frequency
open scoped Classical BigOperators

noncomputable section

/-- **FR.** Les deux hypothèses employées par le témoin rationnel.

**EN.** The two hypotheses used by the rational witness. -/
abbrev RationalWitnessHypothesis := Fin 2

/-- **FR.** Hypothèse attribuant le poids élémentaire `9/25` au résultat
`1`.

**EN.** Hypothesis assigning elementary weight `9/25` to outcome `1`. -/
def rationalWitnessLow : RationalWitnessHypothesis :=
  0

/-- **FR.** Hypothèse attribuant le poids élémentaire `16/25` au résultat
`1`.

**EN.** Hypothesis assigning elementary weight `16/25` to outcome `1`. -/
def rationalWitnessHigh : RationalWitnessHypothesis :=
  1

/-- **FR.** Prior uniforme sur les deux hypothèses.

**EN.** Uniform prior on the two hypotheses. -/
def rationalWitnessPrior
    (_ : RationalWitnessHypothesis) : ℝ :=
  1 / 2

/-- **FR.** Amplitude du résultat `0` sous chaque hypothèse.

**EN.** Amplitude of outcome `0` under each hypothesis. -/
def rationalWitnessAlpha
    (θ : RationalWitnessHypothesis) : ℂ :=
  if θ = rationalWitnessLow then
    (4 : ℂ) / 5
  else
    (3 : ℂ) / 5

/-- **FR.** Amplitude du résultat `1` sous chaque hypothèse.

**EN.** Amplitude of outcome `1` under each hypothesis. -/
def rationalWitnessBeta
    (θ : RationalWitnessHypothesis) : ℂ :=
  if θ = rationalWitnessLow then
    (3 : ℂ) / 5
  else
    (4 : ℂ) / 5

/-- **FR.** Cellule observée : deux résultats égaux à `1` en deux
répétitions.

**EN.** The observed cell: two outcomes equal to `1` in two repetitions. -/
def rationalWitnessObservation : Fin 3 :=
  ⟨2, by decide⟩

/-- **FR.** Le prior du témoin est non négatif.

**EN.** The witness prior is nonnegative. -/
theorem rationalWitnessPrior_nonneg
    (θ : RationalWitnessHypothesis) :
    0 ≤ rationalWitnessPrior θ := by
  norm_num [rationalWitnessPrior]

/-- **FR.** La somme des deux priors uniformes vaut `1`.

**EN.** The two uniform priors sum to `1`. -/
theorem sum_rationalWitnessPrior_eq_one :
    (∑ θ : RationalWitnessHypothesis,
      rationalWitnessPrior θ) = 1 := by
  rw [Fin.sum_univ_two]
  norm_num [rationalWitnessPrior]

/-- **FR.** Les deux amplitudes de chaque hypothèse sont normalisées.

**EN.** Each hypothesis has normalized two-outcome amplitudes. -/
theorem rationalWitnessAmplitudes_normalized
    (θ : RationalWitnessHypothesis) :
    ‖rationalWitnessAlpha θ‖ ^ 2 +
        ‖rationalWitnessBeta θ‖ ^ 2 = 1 := by
  fin_cases θ <;>
    norm_num [
      rationalWitnessAlpha,
      rationalWitnessBeta,
      rationalWitnessLow,
      Complex.norm_real
    ]

/-- **FR.** Modèle fini de confirmation du témoin rationnel.

**EN.** Finite confirmation model for the rational witness. -/
def rationalWitnessModel :
    FiniteBayesModel RationalWitnessHypothesis (Fin 3) :=
  frequencyConfirmationModel
    2
    rationalWitnessPrior
    rationalWitnessAlpha
    rationalWitnessBeta
    rationalWitnessPrior_nonneg
    sum_rationalWitnessPrior_eq_one
    rationalWitnessAmplitudes_normalized

/-- **FR.** Le noyau de l'hypothèse basse dans la cellule observée vaut
`81/625`.

**EN.** The low-hypothesis kernel in the observed cell is `81/625`. -/
theorem rationalWitnessLow_kernel_eq :
    frequencyCellKernel
        2 rationalWitnessAlpha rationalWitnessBeta
        rationalWitnessLow rationalWitnessObservation =
      81 / 625 := by
  norm_num [
    frequencyCellKernel,
    rationalWitnessAlpha,
    rationalWitnessBeta,
    rationalWitnessLow,
    rationalWitnessObservation,
    Complex.norm_real
  ]

/-- **FR.** Le noyau de l'hypothèse haute dans la cellule observée vaut
`256/625`.

**EN.** The high-hypothesis kernel in the observed cell is `256/625`. -/
theorem rationalWitnessHigh_kernel_eq :
    frequencyCellKernel
        2 rationalWitnessAlpha rationalWitnessBeta
        rationalWitnessHigh rationalWitnessObservation =
      256 / 625 := by
  norm_num [
    frequencyCellKernel,
    rationalWitnessAlpha,
    rationalWitnessBeta,
    rationalWitnessLow,
    rationalWitnessHigh,
    rationalWitnessObservation,
    Complex.norm_real
  ]

/-- **FR.** La vraisemblance basse de la cellule observée vaut `81/625`.

**EN.** The low likelihood of the observed cell is `81/625`. -/
theorem rationalWitnessLow_likelihood_eq :
    rationalWitnessModel.likelihood
        rationalWitnessLow rationalWitnessObservation =
      81 / 625 := by
  change
    frequencyLikelihood 2 rationalWitnessAlpha rationalWitnessBeta
      rationalWitnessLow rationalWitnessObservation = 81 / 625
  rw [frequencyLikelihood_eq_choose_mul_kernel,
    rationalWitnessLow_kernel_eq]
  norm_num [rationalWitnessObservation]

/-- **FR.** La vraisemblance haute de la cellule observée vaut `256/625`.

**EN.** The high likelihood of the observed cell is `256/625`. -/
theorem rationalWitnessHigh_likelihood_eq :
    rationalWitnessModel.likelihood
        rationalWitnessHigh rationalWitnessObservation =
      256 / 625 := by
  change
    frequencyLikelihood 2 rationalWitnessAlpha rationalWitnessBeta
      rationalWitnessHigh rationalWitnessObservation = 256 / 625
  rw [frequencyLikelihood_eq_choose_mul_kernel,
    rationalWitnessHigh_kernel_eq]
  norm_num [rationalWitnessObservation]

/-- **FR.** L'évidence de la cellule observée vaut `337/1250`.

**EN.** The evidence of the observed cell is `337/1250`. -/
theorem rationalWitness_evidence_eq :
    rationalWitnessModel.evidence
        rationalWitnessObservation =
      337 / 1250 := by
  unfold FiniteBayesModel.evidence
  rw [Fin.sum_univ_two]
  change
    rationalWitnessPrior rationalWitnessLow *
        rationalWitnessModel.likelihood
          rationalWitnessLow rationalWitnessObservation +
      rationalWitnessPrior rationalWitnessHigh *
        rationalWitnessModel.likelihood
          rationalWitnessHigh rationalWitnessObservation =
      337 / 1250
  rw [
    rationalWitnessLow_likelihood_eq,
    rationalWitnessHigh_likelihood_eq
  ]
  norm_num [rationalWitnessPrior]

/-- **FR.** Le poids postérieur bas vaut exactement `81/337`.

**EN.** The low posterior weight is exactly `81/337`. -/
theorem rationalWitnessLow_posteriorWeight_eq :
    rationalWitnessModel.posteriorWeight
        rationalWitnessObservation rationalWitnessLow =
      81 / 337 := by
  unfold FiniteBayesModel.posteriorWeight
  change
    rationalWitnessPrior rationalWitnessLow *
        rationalWitnessModel.likelihood
          rationalWitnessLow rationalWitnessObservation /
      rationalWitnessModel.evidence rationalWitnessObservation =
      81 / 337
  rw [
    rationalWitnessLow_likelihood_eq,
    rationalWitness_evidence_eq
  ]
  norm_num [rationalWitnessPrior]

/-- **FR.** Le poids postérieur haut vaut exactement `256/337`.

**EN.** The high posterior weight is exactly `256/337`. -/
theorem rationalWitnessHigh_posteriorWeight_eq :
    rationalWitnessModel.posteriorWeight
        rationalWitnessObservation rationalWitnessHigh =
      256 / 337 := by
  unfold FiniteBayesModel.posteriorWeight
  change
    rationalWitnessPrior rationalWitnessHigh *
        rationalWitnessModel.likelihood
          rationalWitnessHigh rationalWitnessObservation /
      rationalWitnessModel.evidence rationalWitnessObservation =
      256 / 337
  rw [
    rationalWitnessHigh_likelihood_eq,
    rationalWitness_evidence_eq
  ]
  norm_num [rationalWitnessPrior]

/-- **FR.** Le facteur de Bayes en faveur de l'hypothèse haute vaut
`256/81`.

**EN.** The Bayes factor in favor of the high hypothesis is `256/81`. -/
theorem rationalWitness_bayesFactor_eq :
    frequencyBayesFactor
        2 rationalWitnessAlpha rationalWitnessBeta
        rationalWitnessHigh rationalWitnessLow
        rationalWitnessObservation =
      256 / 81 := by
  unfold frequencyBayesFactor
  rw [
    rationalWitnessHigh_kernel_eq,
    rationalWitnessLow_kernel_eq
  ]
  norm_num

/-- **FR.** Les cotes postérieures haute contre basse valent `256/81`.

**EN.** The high-to-low posterior odds equal `256/81`. -/
theorem rationalWitness_posteriorOdds_eq :
    rationalWitnessModel.posteriorWeight
          rationalWitnessObservation rationalWitnessHigh /
        rationalWitnessModel.posteriorWeight
          rationalWitnessObservation rationalWitnessLow =
      256 / 81 := by
  rw [
    rationalWitnessHigh_posteriorWeight_eq,
    rationalWitnessLow_posteriorWeight_eq
  ]
  norm_num

/-- **FR.** L'observation augmente strictement le soutien relatif de
l'hypothèse de poids élevé.

**EN.** The observation strictly increases the relative support for the
high-weight hypothesis. -/
theorem rationalWitness_lowPosterior_lt_highPosterior :
    rationalWitnessModel.posteriorWeight
        rationalWitnessObservation rationalWitnessLow <
      rationalWitnessModel.posteriorWeight
        rationalWitnessObservation rationalWitnessHigh := by
  rw [
    rationalWitnessLow_posteriorWeight_eq,
    rationalWitnessHigh_posteriorWeight_eq
  ]
  norm_num

end
end EverettianProbability.Confirmation
