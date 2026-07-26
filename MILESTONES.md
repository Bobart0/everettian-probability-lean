# MILESTONES.md — everettian-probability-lean

## Français

### État au 2026-07-26

| Jalon | Objet | Statut | Buts fermés dans cette reprise |
|---|---|---|---:|
| P0 | Décisions d’architecture | P0.3 tranchée en aval ; P0.4 ouverte | 0 |
| P1 | Infrastructure et squelette | Clos | 0 |
| P2 | Actes finis, tiré-en-arrière, non-vacuité bornienne | Clos | 0 |
| P3 | Représentation affine canonique | Clos | 1 |
| P4 | Invariance locale ⇒ Grain ⇒ Born | Clos, non vacueux et non trivial | 2 |
| P6 | Exclusion du comptage naïf | Résultat scalaire clos ; P6a non ouverte | 1 |
| P5, P7–P11 | Jalons ultérieurs | Non ouverts | 0 |

### Fermetures de la reprise P3/P4

| Fichier | Ancien but | Résultat final | Buts fermés |
|---|---|---|---:|
| `Preference/Representation.lean` | `exists_unique_weights` (énoncé faux) | `canonicalWeight`, `represents`, `weights_unique_on_cells` | 1 |
| `BornCalibration/RefinementImpliesGrain.lean` | `refinement_invariant_implies_grain` | Fermé sous `RefinementInvariantLocal` | 1 |
| `BornCalibration/BornExpectation.lean` | `born_expectation_formula` | Fermé via Grain et le théorème amont | 1 |
| `Rivals/NaiveBranchCounting.lean` | `naiveCounting_violates_grain` | Calcul concret `1/2 ≠ 1/3` | 1 |

Le budget est passé de `4` à `0`. Aucun `sorry` ni `sorryAx` ne subsiste
dans une déclaration aval. La garde impose en outre qu’un éventuel futur
`sorry` porte immédiatement une annotation `SATISFIABILITY:`.

La non-vacuité accompagne la prémisse adoptée :
`bornExpectation_refinementInvariantLocal` prouve que l’espérance bornienne
satisfait l’invariance locale. Le fichier `GlobalPayoffVacuity.lean` conserve
séparément l’ancienne lecture globale comme résultat négatif et exhibe
`uniformExpectationFamily` comme contre-témoin à Grain.

La reprise de non-trivialité ajoute `uniform_not_refinementInvariantLocal` :
sur la cellule complémentaire de la paire explicite en dimension trois, la
famille uniforme donne `1/2` côté grossier et `2/3` côté fin. La prémisse
locale possède donc à la fois son témoin positif bornien et son témoin négatif
uniforme.

## English

### Status on 2026-07-26

| Milestone | Subject | Status | Goals closed in this resumption |
|---|---|---|---:|
| P0 | Architecture decisions | P0.3 settled downstream; P0.4 open | 0 |
| P1 | Infrastructure and skeleton | Closed | 0 |
| P2 | Finite acts, pullback, Born nonvacuity | Closed | 0 |
| P3 | Canonical affine representation | Closed | 1 |
| P4 | Local invariance ⇒ Grain ⇒ Born | Closed, nonvacuous, and nontrivial | 2 |
| P6 | Exclusion of naive counting | Scalar result closed; P6a not opened | 1 |
| P5, P7–P11 | Later milestones | Not opened | 0 |

### P3/P4 resumption closures

| File | Former goal | Final result | Goals closed |
|---|---|---|---:|
| `Preference/Representation.lean` | `exists_unique_weights` (false statement) | `canonicalWeight`, `represents`, `weights_unique_on_cells` | 1 |
| `BornCalibration/RefinementImpliesGrain.lean` | `refinement_invariant_implies_grain` | Closed under `RefinementInvariantLocal` | 1 |
| `BornCalibration/BornExpectation.lean` | `born_expectation_formula` | Closed through Grain and the upstream theorem | 1 |
| `Rivals/NaiveBranchCounting.lean` | `naiveCounting_violates_grain` | Concrete computation `1/2 ≠ 1/3` | 1 |

The budget moved from `4` to `0`. No `sorry` or `sorryAx` remains in a
downstream declaration. The guard additionally requires any future `sorry`
to carry an immediately preceding `SATISFIABILITY:` annotation.

Nonvacuity accompanies the adopted premise:
`bornExpectation_refinementInvariantLocal` proves that Born expectation
satisfies local invariance. `GlobalPayoffVacuity.lean` separately retains the
former global reading as a negative result and exhibits
`uniformExpectationFamily` as a counter-witness to Grain.

The nontriviality resumption adds `uniform_not_refinementInvariantLocal`: on
the complement cell of the explicit dimension-three pair, the uniform family
gives `1/2` on the coarse side and `2/3` on the fine side. The local premise
therefore has both its positive Born witness and its negative uniform witness.
