# CLAIM_MATRIX.md — everettian-probability-lean

## Français

### Statut courant de release -- 2026-07-29

| Jalon | Resultat | Premisses | Conclusion | Statut |
|---|---|---|---|---|
| Saint-Graal formel conditionnel | `conditionalBornMainResults` | `ProjectiveBornPremises` : `n >= 3`, rationalite, invariance locale, etat normalise, `AxNul`; SEM explicite | Born statique et conditionnel, continuateurs, esperance totale, chaine et tour | **CLOS DANS SA PORTEE PROJECTIVE FINIE ET EXPLICITEMENT CONDITIONNELLE** |
| P7 | `recordConditionedCredence`, unicite conditionnelle | Record compatible, normalisation, pont decisionnel et invariance des cotes | Credence finie conditionnee et unicite sous admissibilite | Etabli; interpretation personnelle non derivee |
| P8b | `ContinuationStep` et lois diachroniques | Raffinements orientes et SEM des continuateurs | Normalisation, total expectation, chaine et tour | Etabli dans la portee abstraite; identite personnelle absente |
| Richesse physique exacte finie | orbite unitaire et plans fins | Construction exacte projective finie | Continuations uniformes et ratios prescrits | Etabli, API experimentale |

La matrice datee restante est conservee comme **statut historique**; elle ne
remplace pas les lignes de release ci-dessus.

| Jalon | Résultat | Prémisses | Conclusion | Statut |
|---|---|---|---|---|
| P2 | `bornExpectation_pullback_eq` | Grain du poids bornien amont | L’espérance bornienne est invariante par tiré-en-arrière | Clos |
| P3 | `represents`, `weights_unique_on_cells` | Affinité, monotonie locale, normalisation | Représentation par le poids canonique, unique sur les cellules | Clos |
| P4 | `refinement_invariant_implies_grain` | `RationalExpectationFamily`, `RefinementInvariantLocal` | `AxGrain (canonicalWeight F)` | Clos et non vacueux |
| P4 | `born_expectation_of_invariance` | **Deux prémisses-ponts** : invariance locale (normative pure) et `hNul` (normative-physique, référence l’état `v`) ; `3 ≤ n` ; Norm et Pos **dérivées**, non assumées | Formule d’espérance de Born | Clos, non vacueux et non trivial |
| Témoin de non-trivialité | `uniform_not_refinementInvariantLocal` | Perspective binaire explicite et raffinement en trois lignes | La famille uniforme viole la prémisse locale (`1/2 ≠ 2/3`) | Clos |
| Résultat négatif original | `globalPremise_vacuous` et `uniformExpectationFamily_globalPremise_vacuous` | Ancienne lecture globale | Toute famille rationnelle satisfait la prémisse filtrée ; la famille uniforme viole Grain | Clos |
| P6 | `naiveCounting_violates_grain` | Perspective binaire et raffinement en trois lignes | Le comptage uniforme viole Grain (`1/2 ≠ 1/3`) | Clos |
| P6a | `recordNeutral_refines`, `recordNeutral_record_eq`, `recordNeutral_payoff_eq`, `recordNeutral_bornWeight_eq` | Couplage unitaire concret dans `H 3`, amplitudes inégales (3/5, 4/5), hypothèse nommée `RefinementNotInRecordAlgebra` | Un raffinement peut redécrire les branches plus finement sans en créer de nouvelles au sens physique ; le comptage actif y est sensible (`counting_underdetermined_by_accessible_record`), l'espérance bornienne non (`born_determined_by_accessible_record`) | Clos — témoin d'existence, pas d'universalité |
| Route qubit | `effectExpectation_represents`, `effectWeight_eq_born_of_invariance` | Levée abstraite de `RationalExpectationFamily`/`represents`/`canonicalWeight`/`refinement_invariant_implies_grain` (injectivité de `outcome` threadée en argument), empaquetage en `EstimationRule`, `hAi : D.effects i = Gleason.projL A` | Pour tout `n ≥ 1` (qubit compris, témoin concret en `n = 2` : `EffectCalibration/QubitWitness.lean`, `9/25`), le poids canonique d'une sortie **projective** égale sa valeur de Born ; ne couvre pas les effets POVM non projectifs (différé en amont, QB8.3) ; ne contredit pas `grain_does_not_imply_born_at_two` (Grain seul, sans structure des effets) | Clos — restreint aux sorties projectives |
| P8 | `conditionalWeight_sum_eq_zero_or_one`, `conditionalWeight_normalized`, `conditionalExpectation_pullback_eq_of_weight_ne_zero`, `conditionalExpectation_total`, `conditionalWeight_trans_fiber` | `RefinementInvariantLocal → canonicalWeight_grain`; la normalisation et la totalité n'ajoutent aucune prémisse | Masse totale `0` ou `1`, restitution de la conséquence, loi de totalité et marginalisation conditionnelle ; pas de temps, record ni continuateur | Clos dans sa portée formelle révisée |
| Témoin P8 | `uniform_conditionalWeight_trans_fiber_fails` | Famille uniforme, qui ne satisfait pas `RefinementInvariantLocal` | Échec direct `1 ≠ 4 / 3` : le théorème n'est pas contredit car son hypothèse d'invariance est absente | Clos |
| P9 | `fourthPowerWeight_axPos`, `fourthPowerWeight_not_axNorm` | `psiBefore`, `coarsePerspective` | Positivité satisfaite ; normalisation violée par `337/625 ≠ 1` | Partiel, cas `q = 4` seulement |
| P10 | `frequencyMass_eq_binomial`, `sum_frequencyMass_eq_one`, `frequencyRelativeVariance_eq`, `frequencyAtypicalMass_le_chebyshev`, `one_sub_delta_le_frequencyTypicalMass`, `exists_frequencyTypicality_threshold` | Poids quadratiques déjà calibrés; normalisation; hypothèses positives explicites pour concentration | Masses de fréquence finies normalisées, typicalité et seuil quantifié | **Clos dans sa portée finie et asymptotique quantifiée**; pas de `PMF`, mesure ou dérivation indépendante de Born |
| P11 | `FiniteBayesModel.sum_posteriorWeight_eq_one`, `FiniteBayesModel.posteriorWeight_div_posteriorWeight_eq`, `FiniteBayesModel.iteratedPosteriorModel_prior_eq_finiteObservationPosteriorWeight`, `frequencyConfirmationModel_iteratedPriorOdds_eq` | Priors; masses P10 comme vraisemblances; factorisation conditionnelle; non-nullités explicites | Confirmation bayésienne finie, lots et mise à jour itérée | **Clos dans sa portée bayésienne finie et conditionnelle**; ni hypothèse vraie, ni consistance, ni justification indépendante de Born |
| P5, P6b, P7, P12, route des préférences primitives | Extensions | — | — | Non ouvertes |

Décision P0.3 : l’interface commune reste en aval ; les actes sont totaux et
les sous-types de cellules servent uniquement à l’énumération.

## English

### Current release status -- 2026-07-29

| Milestone | Result | Premises | Conclusion | Status |
|---|---|---|---|---|
| Conditional formal Saint-Graal | `conditionalBornMainResults` | `ProjectiveBornPremises`: `n >= 3`, rationality, local invariance, normalized state, `AxNul`; explicit SEM | Static and conditional Born, continuators, total expectation, chain, and tower | **CLOSED IN ITS EXPLICIT CONDITIONAL FINITE-PROJECTIVE SCOPE** |
| P7 | `recordConditionedCredence`, conditional uniqueness | Compatible record, normalization, decision bridge, odds invariance | Finite conditioned credence and uniqueness under admissibility | Established; personal interpretation not derived |
| P8b | `ContinuationStep` and diachronic laws | Oriented refinements and continuator SEM | Normalization, total expectation, chain, and tower | Established in abstract scope; no personal identity |
| Exact finite physical richness | unitary orbit and fine plans | Exact finite projective construction | Uniform continuations and prescribed ratios | Established, experimental API |

The remaining dated matrix is preserved as **historical status**; it does not
replace the release rows above.

| Milestone | Result | Premises | Conclusion | Status |
|---|---|---|---|---|
| P2 | `bornExpectation_pullback_eq` | Upstream Grain for Born weights | Born expectation is pullback-invariant | Closed |
| P3 | `represents`, `weights_unique_on_cells` | Affinity, local monotonicity, normalization | Representation by the canonical weight, unique on cells | Closed |
| P4 | `refinement_invariant_implies_grain` | `RationalExpectationFamily`, `RefinementInvariantLocal` | `AxGrain (canonicalWeight F)` | Closed and nonvacuous |
| P4 | `born_expectation_of_invariance` | **Two bridge premises**: local invariance (purely normative) and `hNul` (normative-physical, references the state `v`); `3 ≤ n`; Norm and Pos **derived**, not assumed | Born expectation formula | Closed, nonvacuous, and nontrivial |
| Nontriviality witness | `uniform_not_refinementInvariantLocal` | Explicit binary perspective and three-line refinement | The uniform family violates the local premise (`1/2 ≠ 2/3`) | Closed |
| Original negative result | `globalPremise_vacuous` and `uniformExpectationFamily_globalPremise_vacuous` | Former global reading | Every rational family satisfies the filtered premise; the uniform family violates Grain | Closed |
| P6 | `naiveCounting_violates_grain` | Binary perspective and three-line refinement | Uniform counting violates Grain (`1/2 ≠ 1/3`) | Closed |
| P6a | `recordNeutral_refines`, `recordNeutral_record_eq`, `recordNeutral_payoff_eq`, `recordNeutral_bornWeight_eq` | Concrete unitary coupling in `H 3`, unequal amplitudes (3/5, 4/5), named hypothesis `RefinementNotInRecordAlgebra` | A refinement can redescribe branches more finely without physically creating new ones; active counting is sensitive to it (`counting_underdetermined_by_accessible_record`), Born expectation is not (`born_determined_by_accessible_record`) | Closed — existence witness, not universality |
| Qubit route | `effectExpectation_represents`, `effectWeight_eq_born_of_invariance` | Abstract lifting of `RationalExpectationFamily`/`represents`/`canonicalWeight`/`refinement_invariant_implies_grain` (`outcome` injectivity threaded as an argument), packaging into `EstimationRule`, `hAi : D.effects i = Gleason.projL A` | For every `n ≥ 1` (including the qubit; concrete `n = 2` witness in `EffectCalibration/QubitWitness.lean`, `9/25`), the canonical weight of a **projective** outcome equals its Born value; does not cover non-projective POVM effects (deferred upstream, QB8.3); does not contradict `grain_does_not_imply_born_at_two` (Grain alone, without effect structure) | Closed — restricted to projective outcomes |
| P8 | `conditionalWeight_sum_eq_zero_or_one`, `conditionalWeight_normalized`, `conditionalExpectation_pullback_eq_of_weight_ne_zero`, `conditionalExpectation_total`, `conditionalWeight_trans_fiber` | `RefinementInvariantLocal → canonicalWeight_grain`; normalization and totality add no premise | Total mass `0` or `1`, consequence recovery, totality, and conditional marginalization; no time, record, or continuator | Closed in its revised formal scope |
| P8 witness | `uniform_conditionalWeight_trans_fiber_fails` | Uniform family, which does not satisfy `RefinementInvariantLocal` | Direct failure `1 ≠ 4 / 3`: it does not contradict the theorem because its invariance hypothesis is absent | Closed |
| P9 | `fourthPowerWeight_axPos`, `fourthPowerWeight_not_axNorm` | `psiBefore`, `coarsePerspective` | Positivity holds; normalization fails through `337/625 ≠ 1` | Partial, `q = 4` only |
| P10 | `frequencyMass_eq_binomial`, `sum_frequencyMass_eq_one`, `frequencyRelativeVariance_eq`, `frequencyAtypicalMass_le_chebyshev`, `one_sub_delta_le_frequencyTypicalMass`, `exists_frequencyTypicality_threshold` | Already calibrated quadratic weights; normalization; explicit positive hypotheses for concentration | Normalized finite frequency masses, typicality, quantified threshold | **Closed in its finite and quantified-asymptotic scope**; no `PMF`, measure, or independent Born derivation |
| P11 | `FiniteBayesModel.sum_posteriorWeight_eq_one`, `FiniteBayesModel.posteriorWeight_div_posteriorWeight_eq`, `FiniteBayesModel.iteratedPosteriorModel_prior_eq_finiteObservationPosteriorWeight`, `frequencyConfirmationModel_iteratedPriorOdds_eq` | Priors; P10 masses as likelihoods; conditional factorization; explicit nonzero assumptions | Finite Bayesian confirmation, batches, iterated updating | **Closed in its finite conditional Bayesian scope**; no true hypothesis, consistency, or independent Born justification |
| P5, P6b, P7, P12 | Extensions | — | — | Not opened |

Decision P0.3: the common interface remains downstream; acts are total and
cell subtypes are used only for enumeration.

### P10/P11 wording audit (2026-07-28)

| Claim | Status | Authorized formulation | Forbidden formulation |
|---|---|---|---|
| P10 frequency masses and typicality | Closed in finite and quantified-asymptotic scope | “Born-calibrated weights yield normalized finite frequency masses.” “The atypical mass admits an explicit Chebyshev bound.” | “Typicality independently derives the Born rule.” |
| P11 finite conditional confirmation | Closed in finite conditional Bayesian scope | “Born-calibrated frequency masses can serve as finite Bayesian likelihoods.” “Sequential and batch updating agree under explicit nonzero assumptions.” | “Bayesian confirmation independently justifies the Born rule.” “Unitary dynamics alone determines epistemic probability.” “Posterior consistency has been proved.” “The self-location problem has been solved.” |

### Audit des formulations P10/P11 (2026-07-28)

| Revendication | Statut | Formulation autorisée | Formulation interdite |
|---|---|---|---|
| Masses et typicalité P10 | Clos dans la portée finie et asymptotique quantifiée | « Les poids calibrés par Born donnent des masses de fréquence finies normalisées. » « La masse atypique admet une borne de Chebyshev explicite. » | « La typicalité dérive indépendamment la règle de Born. » |
| Confirmation finie conditionnelle P11 | Clos dans la portée bayésienne finie et conditionnelle | « Les masses de fréquence calibrées par Born peuvent servir de vraisemblances bayésiennes finies. » « Les mises à jour séquentielle et par lot coïncident sous hypothèses explicites de non-nullité. » | « La confirmation bayésienne justifie indépendamment Born. » « La dynamique unitaire seule détermine la probabilité épistémique. » « La consistance postérieure est prouvée. » « Le problème d'auto-localisation est résolu. » |
