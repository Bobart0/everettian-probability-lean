# CLAIM_MATRIX.md — everettian-probability-lean

## Français

| Jalon | Résultat | Prémisses | Conclusion | Statut |
|---|---|---|---|---|
| P2 | `bornExpectation_pullback_eq` | Grain du poids bornien amont | L’espérance bornienne est invariante par tiré-en-arrière | Clos |
| P3 | `represents`, `weights_unique_on_cells` | Affinité, monotonie locale, normalisation | Représentation par le poids canonique, unique sur les cellules | Clos |
| P4 | `refinement_invariant_implies_grain` | `RationalExpectationFamily`, `RefinementInvariantLocal` | `AxGrain (canonicalWeight F)` | Clos et non vacueux |
| P4 | `born_expectation_formula` | Grain dérivé, Norm, Pos, Null, `3 ≤ n` | Formule d’espérance de Born | Clos et non vacueux |
| Résultat négatif original | `globalPremise_vacuous` et `uniformExpectationFamily_globalPremise_vacuous` | Ancienne lecture globale | Toute famille rationnelle satisfait la prémisse filtrée ; la famille uniforme viole Grain | Clos |
| P6 | `naiveCounting_violates_grain` | Perspective binaire et raffinement en trois lignes | Le comptage uniforme viole Grain (`1/2 ≠ 1/3`) | Clos |
| P6a | Réalisabilité physique record-neutre | Non formulée ici | Pont futur vers Grain complet depuis une invariance restreinte | Non ouvert |
| P5, P7–P11 | Extensions | — | — | Non ouvertes |

Décision P0.3 : l’interface commune reste en aval ; les actes sont totaux et
les sous-types de cellules servent uniquement à l’énumération.

## English

| Milestone | Result | Premises | Conclusion | Status |
|---|---|---|---|---|
| P2 | `bornExpectation_pullback_eq` | Upstream Grain for Born weights | Born expectation is pullback-invariant | Closed |
| P3 | `represents`, `weights_unique_on_cells` | Affinity, local monotonicity, normalization | Representation by the canonical weight, unique on cells | Closed |
| P4 | `refinement_invariant_implies_grain` | `RationalExpectationFamily`, `RefinementInvariantLocal` | `AxGrain (canonicalWeight F)` | Closed and nonvacuous |
| P4 | `born_expectation_formula` | Derived Grain, Norm, Pos, Null, `3 ≤ n` | Born expectation formula | Closed and nonvacuous |
| Original negative result | `globalPremise_vacuous` and `uniformExpectationFamily_globalPremise_vacuous` | Former global reading | Every rational family satisfies the filtered premise; the uniform family violates Grain | Closed |
| P6 | `naiveCounting_violates_grain` | Binary perspective and three-line refinement | Uniform counting violates Grain (`1/2 ≠ 1/3`) | Closed |
| P6a | Record-neutral physical realizability | Not formulated here | Future bridge from restricted invariance to full Grain | Not opened |
| P5, P7–P11 | Extensions | — | — | Not opened |

Decision P0.3: the common interface remains downstream; acts are total and
cell subtypes are used only for enumeration.
