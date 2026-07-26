# CLAIM_MATRIX.md — everettian-probability-lean

## Français

| Jalon | Problème | Résultat | Prémisses | Conclusion | Rivale exclue | Reste ouvert |
|---|---|---|---|---|---|---|
| P2 | Consistance de l'invariance sous raffinement | `bornExpectation_pullback_eq`, témoin concret en `H 3`, interface abstraite à deux instances | Grain amont pour `E₀`; invariance reconnue comme prémisse normative | La fonctionnelle bornienne satisfait réellement l'invariance; la prémisse centrale n'est pas vide | Aucune | Arbitrage comptable/spécification décrit dans `MILESTONES.md` |
| P3 | Représentation affine | Non ouvert | — | — | — | Corriger en session dédiée la notion d'unicité hors `D.cells` |
| P4 | Invariance ⟹ Grain ⟹ Born | Non ouvert, mais désormais non vacueux | Rationalité, invariance normative, représentation P3 | La prémisse possède le témoin bornien fort de P2 | — | Localité de `PayoffPreserving`, puis P3 et preuve P4 |
| P5 | Non-circularité | Non ouvert | — | — | — | P0.4 |
| P6 | Comptage naïf | Non ouvert | — | — | — | `naiveCounting_violates_grain` |
| P7–P11 | Extensions | Non ouvertes | — | — | — | Sessions ultérieures |

Décision P0.3 : l'interface commune vit uniquement en aval. Les cellules
peuvent être dépendantes pour l'énumération, mais les actes restent des
fonctions totales sur un espace ambiant.

## English

| Milestone | Problem | Result | Premises | Conclusion | Rival excluded | Still open |
|---|---|---|---|---|---|---|
| P2 | Consistency of refinement invariance | `bornExpectation_pullback_eq`, concrete `H 3` witness, two-instance abstract interface | Upstream Grain for `E₀`; invariance recognized as normative | The Born functional really satisfies invariance; the central premise is not empty | None | Accounting/specification decision recorded in `MILESTONES.md` |
| P3 | Affine representation | Not opened | — | — | — | Fix off-`D.cells` uniqueness in a dedicated session |
| P4 | Invariance ⟹ Grain ⟹ Born | Not opened, but now nonvacuous | Rationality, normative invariance, P3 representation | The premise has P2's strong Born witness | — | Locality of `PayoffPreserving`, then P3 and the P4 proof |
| P5 | Non-circularity | Not opened | — | — | — | P0.4 |
| P6 | Naive counting | Not opened | — | — | — | `naiveCounting_violates_grain` |
| P7–P11 | Extensions | Not opened | — | — | — | Later sessions |

Decision P0.3: the common interface lives downstream only. Cells may be
dependent for enumeration, while acts remain total functions on an ambient
space.
