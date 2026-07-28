# THEOREM_MAP.md

## Français

## P10 — Fréquences et typicalité

| Fichier | Déclaration Lean exacte | Prémisses importantes | Conclusion | Limites et amont |
|---|---|---|---|---|
| `Frequency/Distribution.lean` | `frequencyMass_eq_binomial`; `sum_frequencyMass_eq_one` | Vecteur de répétition et poids quadratiques; normalisation pour la seconde | Formule binomiale exacte et masse totale `1` | Réutilise les poids calibrés en amont; ni `PMF`, ni mesure. |
| `Frequency/Moments.lean` | `frequencyRelativeVariance_eq` | `0 < R`, normalisation élémentaire | Variance relative `‖β‖²(1-‖β‖²)/R` | Calcul fini. |
| `Frequency/Concentration.lean` | `frequencyAtypicalMass_le_chebyshev` | `0 < R`, `0 < ε`, normalisation | Borne finie de Chebyshev | Pas de limite. |
| `Frequency/Typicality.lean` | `one_sub_delta_le_frequencyTypicalMass` | Borne de Chebyshev au plus `δ` | Masse typique au moins `1-δ` | Typicalité finie seulement. |
| `Frequency/AsymptoticTypicality.lean` | `exists_frequencyTypicality_threshold` | `ε > 0`, `δ > 0`, normalisation | Seuil naturel positif explicite | Quantifié, sans `Tendsto`; ne dérive pas Born. |

## P11 — Confirmation conditionnelle finie

| Fichier | Déclaration Lean exacte | Prémisses importantes | Conclusion | Limites et amont |
|---|---|---|---|---|
| `Confirmation/FiniteBayes.lean` | `FiniteBayesModel.sum_posteriorWeight_eq_one` | Évidence non nulle | Posterieurs normalisés | Modèle fini algébrique. |
| `Confirmation/PosteriorOdds.lean` | `FiniteBayesModel.posteriorWeight_div_posteriorWeight_eq` | Évidence, prior et vraisemblance dénominateurs non nuls | Cotes postérieures = cotes a priori × rapport de vraisemblance | Divisions conditionnelles. |
| `Confirmation/HypothesisComparison.lean` | `frequencyConfirmationModel_posteriorWeight_lt_iff_kernel_lt_of_equal_prior` | Priors égaux positifs, évidence positive | Ordre des postérieurs = ordre des noyaux | Pas d'hypothèse vraie. |
| `Confirmation/SequentialUpdate.lean` | `FiniteBayesModel.posteriorUpdatedModel_posteriorWeight_eq` | Évidences explicites non nulles | Mise à jour à deux observations | Factorisation conditionnelle. |
| `Confirmation/IteratedUpdate.lean` | `FiniteBayesModel.iteratedPosteriorModel_prior_eq_finiteObservationPosteriorWeight` | Témoin séquentiel de non-nullité | Mise à jour itérée = posterior global du lot | Pas de convergence. |
| `Confirmation/BatchPosteriorOdds.lean` | `FiniteBayesModel.iteratedPosteriorModel_priorOdds_eq_priorOdds_mul_ratioProduct` | Non-nullités des dénominateurs | Cotes finales = produit des rapports | Lot fini. |
| `Confirmation/FrequencyBatchOdds.lean` | `frequencyConfirmationModel_iteratedPriorOdds_eq` | Noyaux dénominateurs non nuls | Spécialisation aux noyaux fréquentiels | Masses P10 comme vraisemblances. |
| `Confirmation/RationalBatchWitness.lean` | `rationalWitnessLow_iteratedPrior_lt_high` | Témoin rationnel explicite | Comparaison stricte après deux observations | Exemple, pas consistance. |

```text
P4 Born calibration
    ↓
P10 frequencyMass and typicality
    ↓
P11 finite likelihoods and Bayesian updating
```

| Statut | Déclaration | Module | Dépendances directes | Limite de portée | Audit |
|---|---|---|---|---|---|
| Résultat original | `born_expectation_of_invariance` | `BornCalibration/BornExpectation.lean` | **Deux prémisses-ponts** : `RefinementInvariantLocal` (normative pure) et `AxNul (canonicalWeight F) v` (normative-physique — seul point d'entrée de l'état `v`), plus `RationalExpectationFamily`, `‖v‖ = 1`, `3 ≤ n` ; `AxNorm`/`AxPos` sur `canonicalWeight F` sont dérivées, non assumées | Route projective uniquement ; invariance sur **tous** les raffinements projectifs, sans restriction de records ; n'affirme aucune dérivation dynamique des deux prémisses-ponts | `[propext, Classical.choice, Quot.sound]` |
| Théorème de connexion | `refinement_invariant_implies_grain` | `BornCalibration/RefinementImpliesGrain.lean` | Représentation canonique et invariance locale | Même quantification projective non restreinte | `[propext, Classical.choice, Quot.sound]` |
| Théorème de représentation | `represents` | `Preference/Representation.lean` | Affinité, monotonie locale, normalisation | Perspectives finies ; les actes restent totaux | `[propext, Classical.choice, Quot.sound]` |
| Témoin de non-vacuité | `bornExpectation_refinementInvariantLocal` | `Refinement/PayoffPreserving.lean` | Cohérence Grain de Born amont | Montre seulement l'existence d'un habitant de la prémisse | `[propext, Classical.choice, Quot.sound]` |
| Témoin de non-trivialité | `uniform_not_refinementInvariantLocal` | `Refinement/NonTriviality.lean` | Famille uniforme et paire explicite binaire / trois lignes dans `H 3` | Calcul spécifique à `n = 3` : `1 / 2 ≠ 2 / 3` | `[propext, Classical.choice, Quot.sound]` |
| Résultat négatif original | `globalPremise_vacuous` | `Refinement/GlobalPayoffVacuity.lean` | Raffinement vers `{⊤}` | Porte sur l'ancienne lecture globale, explicitement non employée comme prémisse | `[propext, Classical.choice, Quot.sound]` |
| Résultat original | `refinementInvariantLocal_iff_axGrain` | `BornCalibration/RefinementImpliesGrain.lean` | `represents`, `refinement_invariant_implies_grain`, `refinementInvariantLocal_iff_pullback` | Équivalence, pas seulement implication : la prémisse normative est **exactement** `AxGrain` sur `canonicalWeight F`, ni plus forte ni plus faible ; même quantification projective non restreinte | `[propext, Classical.choice, Quot.sound]` |
| Résultat original | `grain_does_not_imply_born_at_two` | `BornCalibration/NonCircularity.lean` | `perspective_two_cases` (structurel, `n = 2`), `skewWeight` et ses quatre propriétés, témoin explicite `witnessState = (3/5, 4/5)` | Spécifique à `n = 2`, où le théorème de Gleason échoue ; ne prétend rien sur `n ≥ 3` (domaine de `grainCoherenceTheorem_projector`) ; le témoin est un exemple, pas une classification de toutes les règles non-boriennes cohérentes sous Grain | `[propext, Classical.choice, Quot.sound]` |
| Témoin de non-trivialité | `maxExpectation_not_affine` | `Preference/NonTriviality.lean` | Perspective binaire explicite dans `H 3` | Calcul spécifique à `n = 3` : `1/2 ≠ 1` ; établit que le maximum sur les cellules ne peut pas compléter une `RationalExpectationFamily`, pas une classification de tous les fonctionnels non affines | `[propext, Classical.choice, Quot.sound]` |
| Témoin physique (P6a) | `recordNeutral_refines`, `recordNeutral_record_eq`, `recordNeutral_payoff_eq`, `recordNeutral_bornWeight_eq` | `PhysicalRefinement/RecordNeutralWitness.lean` | Couplage unitaire concret `coupleU` dans `H 3` (rotation `(3/5,4/5;4/5,-3/5)` sur un ancilla à deux niveaux), hypothèse nommée `RefinementNotInRecordAlgebra` (`refinementNotInRecordAlgebra_holds`) | **Témoin schématique** : `H 3` n'a ni factorisation tensorielle explicite système/ancilla, ni dynamique, ni décohérence ; l'algèbre de records y est *stipulée*, non dérivée. Établit une existence, pas une universalité ; brique manquante nommée pour la généraliser : une porte de rotation d'amplitude *contrôlée* (combinant le contrôle à deux sites de `ControlledBitFlip` avec le mélange de `AmplitudeRotation` en amont), à construire et exporter | `[propext, Classical.choice, Quot.sound]` |
| Témoin de non-trivialité (P6a) | `counting_sensitive_to_recordNeutral_refinement`, `counting_underdetermined_by_accessible_record` | `PhysicalRefinement/NonTriviality.lean` | Comptage uniforme restreint aux cellules actives (`activeCells`, `uniformCredence`) sur le même témoin physique | Calcul spécifique au témoin : `1/2 ≠ 1/3` ; ne classifie pas toutes les règles de comptage, seulement celle-ci | `[propext, Classical.choice, Quot.sound]` |
| Corollaire bornien (P6a) | `born_insensitive_to_recordNeutral_refinement`, `born_determined_by_accessible_record` | `PhysicalRefinement/Nonvacuity.lean` | `bornExpectation_pullback_eq` (`Refinement/PayoffPreserving.lean`), même témoin physique | Contraste avec le comptage sur le même témoin ; ne prétend rien au-delà de ce paiement et de cette paire de perspectives | `[propext, Classical.choice, Quot.sound]` |
| Théorème de représentation (route qubit) | `EverettianProbability.Abstract.effectExpectation_represents` | `EffectCalibration/EffectBornExpectation.lean` | `represents` levé abstraitement, injectivité de `outcome` (`Fin.val_injective`) | Aucune restriction de dimension, aucune hypothèse de projectivité — vaut pour tout `n` | `[propext, Classical.choice, Quot.sound]` |
| Résultat original (route qubit) | `EverettianProbability.Abstract.effectWeight_eq_born_of_invariance` | `EffectCalibration/EffectBornExpectation.lean` | Invariance locale abstraite, empaquetage en `EstimationRule` (`canonicalEstimationRule`), nullité de support contextuelle, `hAi : D.effects i = Gleason.projL A` | Vaut pour **tout** `n ≥ 1` (qubit compris) mais **seulement** pour les sorties dont l'effet est une projection ; les POVM non projectifs sont différés en amont (QB8.3) ; ne contredit pas `grain_does_not_imply_born_at_two` — voir le docstring du fichier | `[propext, Classical.choice, Quot.sound]` |
| Témoin concret (route qubit) | `EverettianProbability.Abstract.spinUp_weight_eq_born` | `EffectCalibration/QubitWitness.lean` | Perspective d'effets explicite en `H 2`, amplitudes `3/5`, `4/5` | Calcul spécifique à ce témoin : poids canonique `= 9/25` | `[propext, Classical.choice, Quot.sound]` |
| Témoin de non-trivialité (route qubit) | `EverettianProbability.Abstract.effectUniform_not_refinementInvariantLocal` | `EffectCalibration/NonTriviality.lean` | Comptage uniforme sur *toutes* les sorties (pas seulement actives), raffinement à sortie fantôme toujours silencieuse (`phantomZeroRefines`, construit sans `binaryPerspective`/`complementEffect` amont) | Calcul spécifique au témoin : `1/2 ≠ 2/3` ; ne classifie pas toutes les règles de comptage | `[propext, Classical.choice, Quot.sound]` |
| Témoin P9 | `fourthPowerWeight_axPos`, `fourthPowerWeight_coarse_sum`, `fourthPowerWeight_not_axNorm` | `Rivals/FourthPowerWeight.lean` | `psiBefore`, `coarsePerspective` | Témoin projectif concret dans `H 3`, exposant fixé à `4` : positivité, somme `337/625`, puis échec de `AxNorm`. Aucune classification des exposants. | `[propext, Classical.choice, Quot.sound]` |

L'énoncé principal exact (route projective) est :

```lean
theorem born_expectation_of_invariance (F : RationalExpectationFamily n) (hn3 : 3 ≤ n)
    (hinv : RefinementInvariantLocal F.V)
    {v : H n} (hv : ‖v‖ = 1) (hNul : AxNul (canonicalWeight F) v)
    (D : Perspective n) (a : Act n) :
    F.V D a = ∑ c ∈ D.cells, ‖projL c v‖ ^ 2 * a c
```

L'énoncé principal exact (route effets, route qubit) est :

```lean
theorem effectWeight_eq_born_of_invariance {n : ℕ} (hn : 1 ≤ n)
    (F : RationalExpectationFamily (Effects.interface n))
    (hinv : RefinementInvariantLocal F.V)
    {v : H n} (hv : ‖v‖ = 1)
    (hNull : EffectPerspectives.ContextualNullSupport (canonicalEstimationRule F hinv) v)
    (D : EffectPerspectives.EffectPerspective n) (i : Fin D.outcomes)
    (A : Submodule ℂ (H n))
    (hAi : (D.effects i : H n →ₗ[ℂ] H n) = Gleason.projL A) :
    canonicalWeight F D i = ‖A.starProjection v‖ ^ 2
```

### P8 — conditionnement statique / static conditioning

| Déclaration / declaration | Module | Ce qui est établi / what is established | Portée / scope |
|---|---|---|---|
| `conditionalWeight_sum_eq_zero_or_one` | `Diachronic/Conditioning.lean` | La masse totale conditionnelle vaut `0` si le poids conditionnant est nul, `1` sinon. / Total conditional mass is `0` at zero conditioning weight and `1` otherwise. | Définition totale, convention `0` au dénominateur nul. / Total definition with the zero-denominator convention. |
| `conditionalWeight_normalized` | `Diachronic/Conditioning.lean` | Corollaire de normalisation lorsque le poids conditionnant est non nul. / Nonzero conditioning-weight normalization corollary. | Aucun temps n'est formalisé. / No time is formalized. |
| `conditionalExpectation_pullback_eq_of_weight_ne_zero` | `Diachronic/Conditioning.lean` | L'acte grossier tiré en arrière restitue la conséquence de la cellule conditionnante. / A pulled-back coarse act recovers the conditioning cell's consequence. | Aucun record accessible ni continuateur. / No accessible record or continuator. |
| `conditionalExpectation_total` | `Diachronic/Conditioning.lean` | Loi de totalité. / Law of total expectation. | Raffinements statiques seulement. / Static refinements only. |
| `conditionalWeight_trans_fiber` | `Diachronic/Conditioning.lean` | Marginalisation conditionnelle sous raffinement ultérieur. / Conditional marginalization under a later refinement. | Chaîne logique : `RefinementInvariantLocal → canonicalWeight_grain → conditionalWeight_trans_fiber`; c'est un corollaire de Grain, pas une prémisse indépendante. / It is a Grain corollary, not an independent premise. |
| `uniform_conditionalWeight_trans_fiber_fails` | `Diachronic/NonTriviality.lean` | Échec direct `1 ≠ 4 / 3`. / Direct failure `1 ≠ 4 / 3`. | La famille uniforme ne satisfait pas `RefinementInvariantLocal`, donc ne contredit pas le théorème. / The uniform family lacks `RefinementInvariantLocal`, so it does not contradict the theorem. |

## English

## P10 — Frequency and typicality

| File | Exact Lean declaration | Important premises | Conclusion | Scope limits and upstream |
|---|---|---|---|---|
| `Frequency/Distribution.lean` | `frequencyMass_eq_binomial`; `sum_frequencyMass_eq_one` | Repetition vector and quadratic weights; normalization for the latter | Exact binomial formula and total mass `1` | Reuses upstream-calibrated weights; no `PMF` or measure. |
| `Frequency/Moments.lean` | `frequencyRelativeVariance_eq` | `0 < R`, elementary normalization | Relative variance `‖β‖²(1-‖β‖²)/R` | Finite calculation. |
| `Frequency/Concentration.lean` | `frequencyAtypicalMass_le_chebyshev` | `0 < R`, `0 < ε`, normalization | Finite Chebyshev bound | No limit theorem. |
| `Frequency/Typicality.lean` | `one_sub_delta_le_frequencyTypicalMass` | Chebyshev bound at most `δ` | Typical mass at least `1-δ` | Finite typicality only. |
| `Frequency/AsymptoticTypicality.lean` | `exists_frequencyTypicality_threshold` | `ε > 0`, `δ > 0`, normalization | Explicit positive natural threshold | Quantified, without `Tendsto`; does not derive Born. |

## P11 — Finite conditional confirmation

| File | Exact Lean declaration | Important premises | Conclusion | Scope limits and upstream |
|---|---|---|---|---|
| `Confirmation/FiniteBayes.lean` | `FiniteBayesModel.sum_posteriorWeight_eq_one` | Nonzero evidence | Normalized posterior weights | Finite algebraic model. |
| `Confirmation/PosteriorOdds.lean` | `FiniteBayesModel.posteriorWeight_div_posteriorWeight_eq` | Nonzero evidence, denominator prior and likelihood | Posterior odds = prior odds × likelihood ratio | Conditional divisions. |
| `Confirmation/HypothesisComparison.lean` | `frequencyConfirmationModel_posteriorWeight_lt_iff_kernel_lt_of_equal_prior` | Equal positive priors, positive evidence | Posterior order = kernel order | No true hypothesis. |
| `Confirmation/SequentialUpdate.lean` | `FiniteBayesModel.posteriorUpdatedModel_posteriorWeight_eq` | Explicit nonzero evidences | Two-observation update | Conditional factorization. |
| `Confirmation/IteratedUpdate.lean` | `FiniteBayesModel.iteratedPosteriorModel_prior_eq_finiteObservationPosteriorWeight` | Sequential nonzero-evidence witness | Iterated update = global batch posterior | No convergence. |
| `Confirmation/BatchPosteriorOdds.lean` | `FiniteBayesModel.iteratedPosteriorModel_priorOdds_eq_priorOdds_mul_ratioProduct` | Nonzero denominators | Final odds = ratio-product update | Finite batch. |
| `Confirmation/FrequencyBatchOdds.lean` | `frequencyConfirmationModel_iteratedPriorOdds_eq` | Nonzero denominator kernels | Frequency-kernel specialization | P10 masses are likelihoods. |
| `Confirmation/RationalBatchWitness.lean` | `rationalWitnessLow_iteratedPrior_lt_high` | Explicit rational witness | Strict comparison after two observations | Example, not consistency. |

```text
P4 Born calibration
    ↓
P10 frequencyMass and typicality
    ↓
P11 finite likelihoods and Bayesian updating
```

| Status | Declaration | Module | Direct dependencies | Scope limitation | Audit |
|---|---|---|---|---|---|
| Original result | `born_expectation_of_invariance` | `BornCalibration/BornExpectation.lean` | **Two bridge premises**: `RefinementInvariantLocal` (purely normative) and `AxNul (canonicalWeight F) v` (normative-physical — the only entry point for the state `v`), plus `RationalExpectationFamily`, `‖v‖ = 1`, `3 ≤ n`; `AxNorm`/`AxPos` on `canonicalWeight F` are derived, not assumed | Projective route only; invariance over **all** projective refinements, with no record restriction; it does not dynamically derive either bridge premise | `[propext, Classical.choice, Quot.sound]` |
| Connection theorem | `refinement_invariant_implies_grain` | `BornCalibration/RefinementImpliesGrain.lean` | Canonical representation and local invariance | Same unrestricted projective quantification | `[propext, Classical.choice, Quot.sound]` |
| Representation theorem | `represents` | `Preference/Representation.lean` | Affinity, local monotonicity, normalization | Finite perspectives; acts remain total | `[propext, Classical.choice, Quot.sound]` |
| Nonvacuity witness | `bornExpectation_refinementInvariantLocal` | `Refinement/PayoffPreserving.lean` | Upstream Born Grain coherence | Establishes only that the premise has an inhabitant | `[propext, Classical.choice, Quot.sound]` |
| Nontriviality witness | `uniform_not_refinementInvariantLocal` | `Refinement/NonTriviality.lean` | Uniform family and the explicit binary / three-line pair in `H 3` | Dimension-specific calculation at `n = 3`: `1 / 2 ≠ 2 / 3` | `[propext, Classical.choice, Quot.sound]` |
| Original negative result | `globalPremise_vacuous` | `Refinement/GlobalPayoffVacuity.lean` | Refinement to `{⊤}` | Concerns the former global reading, explicitly not used as a premise | `[propext, Classical.choice, Quot.sound]` |
| Original result | `refinementInvariantLocal_iff_axGrain` | `BornCalibration/RefinementImpliesGrain.lean` | `represents`, `refinement_invariant_implies_grain`, `refinementInvariantLocal_iff_pullback` | Equivalence, not just implication: the normative premise is **exactly** `AxGrain` on `canonicalWeight F`, neither stronger nor weaker; same unrestricted projective quantification | `[propext, Classical.choice, Quot.sound]` |
| Original result | `grain_does_not_imply_born_at_two` | `BornCalibration/NonCircularity.lean` | `perspective_two_cases` (structural, `n = 2`), `skewWeight` and its four properties, explicit witness `witnessState = (3/5, 4/5)` | Specific to `n = 2`, where Gleason's theorem fails; claims nothing about `n ≥ 3` (the domain of `grainCoherenceTheorem_projector`); the witness is one example, not a classification of every non-Born rule coherent under Grain | `[propext, Classical.choice, Quot.sound]` |
| Nontriviality witness | `maxExpectation_not_affine` | `Preference/NonTriviality.lean` | Explicit binary perspective in `H 3` | Dimension-specific calculation at `n = 3`: `1/2 ≠ 1`; establishes that the max over cells cannot complete a `RationalExpectationFamily`, not a classification of every non-affine functional | `[propext, Classical.choice, Quot.sound]` |
| Physical witness (P6a) | `recordNeutral_refines`, `recordNeutral_record_eq`, `recordNeutral_payoff_eq`, `recordNeutral_bornWeight_eq` | `PhysicalRefinement/RecordNeutralWitness.lean` | Concrete unitary coupling `coupleU` in `H 3` (rotation `(3/5,4/5;4/5,-3/5)` on a two-level ancilla), named hypothesis `RefinementNotInRecordAlgebra` (`refinementNotInRecordAlgebra_holds`) | **Schematic witness**: `H 3` has no explicit system/ancilla tensor factorization, no dynamics, no decoherence; the record algebra is *stipulated*, not derived. Establishes an existence, not a universality claim; named missing brick to generalize it: a *controlled* amplitude-rotation gate (combining `ControlledBitFlip`'s two-site control with `AmplitudeRotation`'s mixing, upstream), to be built and exported | `[propext, Classical.choice, Quot.sound]` |
| Nontriviality witness (P6a) | `counting_sensitive_to_recordNeutral_refinement`, `counting_underdetermined_by_accessible_record` | `PhysicalRefinement/NonTriviality.lean` | Uniform counting restricted to active cells (`activeCells`, `uniformCredence`) on the same physical witness | Calculation specific to the witness: `1/2 ≠ 1/3`; does not classify every counting rule, only this one | `[propext, Classical.choice, Quot.sound]` |
| Born corollary (P6a) | `born_insensitive_to_recordNeutral_refinement`, `born_determined_by_accessible_record` | `PhysicalRefinement/Nonvacuity.lean` | `bornExpectation_pullback_eq` (`Refinement/PayoffPreserving.lean`), same physical witness | Contrast with counting on the same witness; claims nothing beyond this payoff and this pair of perspectives | `[propext, Classical.choice, Quot.sound]` |
| Representation theorem (qubit route) | `EverettianProbability.Abstract.effectExpectation_represents` | `EffectCalibration/EffectBornExpectation.lean` | Abstractly lifted `represents`, `outcome` injectivity (`Fin.val_injective`) | No dimension restriction, no projectivity hypothesis — holds for every `n` | `[propext, Classical.choice, Quot.sound]` |
| Original result (qubit route) | `EverettianProbability.Abstract.effectWeight_eq_born_of_invariance` | `EffectCalibration/EffectBornExpectation.lean` | Abstract local invariance, packaging into an `EstimationRule` (`canonicalEstimationRule`), contextual null support, `hAi : D.effects i = Gleason.projL A` | Holds for **every** `n ≥ 1` (qubit included) but **only** for outcomes whose effect is a projection; non-projective POVMs are deferred upstream (QB8.3); does not contradict `grain_does_not_imply_born_at_two` — see the file's module docstring | `[propext, Classical.choice, Quot.sound]` |
| Concrete witness (qubit route) | `EverettianProbability.Abstract.spinUp_weight_eq_born` | `EffectCalibration/QubitWitness.lean` | Explicit effect perspective in `H 2`, amplitudes `3/5`, `4/5` | Calculation specific to this witness: canonical weight `= 9/25` | `[propext, Classical.choice, Quot.sound]` |
| Nontriviality witness (qubit route) | `EverettianProbability.Abstract.effectUniform_not_refinementInvariantLocal` | `EffectCalibration/NonTriviality.lean` | Uniform counting over *every* outcome (not only active ones), refinement with an always-silent phantom outcome (`phantomZeroRefines`, built without upstream `binaryPerspective`/`complementEffect`) | Calculation specific to the witness: `1/2 ≠ 2/3`; does not classify every counting rule | `[propext, Classical.choice, Quot.sound]` |
| P9 witness | `fourthPowerWeight_axPos`, `fourthPowerWeight_coarse_sum`, `fourthPowerWeight_not_axNorm` | `Rivals/FourthPowerWeight.lean` | `psiBefore`, `coarsePerspective` | Concrete projective witness in `H 3`, exponent fixed at `4`: positivity, sum `337/625`, then failure of `AxNorm`. No classification of exponents. | `[propext, Classical.choice, Quot.sound]` |

The exact headline statement (projective route) is:

```lean
theorem born_expectation_of_invariance (F : RationalExpectationFamily n) (hn3 : 3 ≤ n)
    (hinv : RefinementInvariantLocal F.V)
    {v : H n} (hv : ‖v‖ = 1) (hNul : AxNul (canonicalWeight F) v)
    (D : Perspective n) (a : Act n) :
    F.V D a = ∑ c ∈ D.cells, ‖projL c v‖ ^ 2 * a c
```

The exact headline statement (effect route, qubit route) is:

```lean
theorem effectWeight_eq_born_of_invariance {n : ℕ} (hn : 1 ≤ n)
    (F : RationalExpectationFamily (Effects.interface n))
    (hinv : RefinementInvariantLocal F.V)
    {v : H n} (hv : ‖v‖ = 1)
    (hNull : EffectPerspectives.ContextualNullSupport (canonicalEstimationRule F hinv) v)
    (D : EffectPerspectives.EffectPerspective n) (i : Fin D.outcomes)
    (A : Submodule ℂ (H n))
    (hAi : (D.effects i : H n →ₗ[ℂ] H n) = Gleason.projL A) :
    canonicalWeight F D i = ‖A.starProjection v‖ ^ 2
```
