# CLAIM_MATRIX.md — everettian-probability-lean

## Français

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
| P5, P6b, P7, P10–P12, route des préférences primitives | Extensions | — | — | Non ouvertes |

Décision P0.3 : l’interface commune reste en aval ; les actes sont totaux et
les sous-types de cellules servent uniquement à l’énumération.

## English

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
| P5, P6b, P7, P10–P12 | Extensions | — | — | Not opened |

Decision P0.3: the common interface remains downstream; acts are total and
cell subtypes are used only for enumeration.
