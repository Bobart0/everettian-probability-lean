# MILESTONES.md — everettian-probability-lean

## Français

### Table des jalons

| Jalon | Objet | Statut | Date | Buts ouverts introduits | Buts ouverts fermés |
|---|---|---|---|---|---|
| P0 | Red team sur papier et décisions d'architecture | P0.3 tranchée en aval; autres décisions hors de cette session | 2026-07-26 | 0 | 0 |
| P1 | Infrastructure du dépôt, squelette compilable | ✅ CLOS | 2026-07-25 | 7 | 0 |
| P2 | Modèle fini des actes et consistance de l'invariance | ⚠️ RÉSULTATS TECHNIQUES CLOS; CRITÈRE COMPTABLE NON ATTEINT | 2026-07-26 | 0 | 3 |
| P3 | Théorème de représentation | Non ouvert | — | — | — |
| P4 | Invariance ⟹ Grain ⟹ Born | Non ouvert; prémisse prouvée non vacueuse | — | — | — |
| P5–P11 | Jalons ultérieurs | Non ouverts | — | — | — |

### P2 — résultats effectivement fermés

Le pin vise `v1.1.1-probability-api`; le diff du manifeste est limité à
`quantum_foundations`. Les trois anciens buts de `Core/Parent.lean` ont été
supprimés avec ce fichier et remplacés par `parentOf` et ses lemmes publics.
`Core/` et `Refinement/` sont à zéro `sorry`.

| Fichier | Résultat fermé pendant P2 | Nombre de buts fermés |
|---|---|---:|
| `Core/Parent.lean` | Suppression de `parent_mem`, `parent_le`, `parent_unique`, devenus redondants | 3 |
| `Core/Act.lean` | Actes totaux, indicatrices, ordre, combinaisons et décomposition finie | 0 (squelette complété sans nouveau `sorry`) |
| `Refinement/PullbackAct.lean` | Réflexivité, transitivité et indicatrice de fibre via l'API amont | 0 |
| `Refinement/PayoffPreserving.lean` | `bornExpectation_pullback_eq` et témoin général d'invariance | 0 |
| `Refinement/Nonvacuity.lean` | État, raffinement binaire strict et valeurs `1` calculées dans `H 3` | 0 |
| `Core/Interface.lean` | Interface abstraite, instances projective/effets et pont abstrait Grain → invariance | 0 |

Le pont fort mesure → fonctionnelle est désormais prouvé : la somme est
regroupée par fibres de `parentOf`, les fibres sont identifiées à
`coarseCells`, puis `E₀_isGrain` ferme chaque somme intérieure. Le témoin
concret calcule l'espérance de l'acte constant `1` sur les perspectives
binaires fine et grossière.

### Budget final et condition de sortie non satisfaite

Le budget réel reste `4`, contre `7` à l'entrée de P2. Les quatre occurrences
restantes sont :

| Fichier | Déclaration | Jalon prévu |
|---|---|---|
| `Preference/Representation.lean` | `exists_unique_weights` | P3 |
| `BornCalibration/RefinementImpliesGrain.lean` | `refinement_invariant_implies_grain` | P4 / reprise de spécification |
| `BornCalibration/BornExpectation.lean` | `born_expectation_formula` | P4 |
| `Rivals/NaiveBranchCounting.lean` | `naiveCounting_violates_grain` | P6 |

Le seuil demandé `SORRY_COUNT ≤ 2` est donc incompatible avec l'instruction
« ne pas ouvrir P3 » et avec l'interdiction de laisser `sorryAx` sous une
déclaration censée close. En effet, les deux théorèmes P4 utilisent le poids
fourni par `exists_unique_weights`. De plus, l'hypothèse actuelle de
`refinement_invariant_implies_grain` ne porte que sur les actes globalement
`PayoffPreserving`; les indicatrices de cellules nécessaires à la preuve de
Grain ne satisfont pas cette propriété globale. Aucun énoncé n'a été affaibli
et aucun but n'a été fermé artificiellement. P2 est donc techniquement
réalisé, mais son statut global reste signalé tant que cet arbitrage de
spécification n'est pas pris.

## English

### Milestone table

| Milestone | Subject | Status | Date | Open goals introduced | Open goals closed |
|---|---|---|---|---|---|
| P0 | Paper red team and architecture decisions | P0.3 settled downstream; other decisions outside this session | 2026-07-26 | 0 | 0 |
| P1 | Repository infrastructure, compilable skeleton | ✅ CLOSED | 2026-07-25 | 7 | 0 |
| P2 | Finite act model and consistency of invariance | ⚠️ TECHNICAL RESULTS CLOSED; ACCOUNTING CRITERION NOT MET | 2026-07-26 | 0 | 3 |
| P3 | Representation theorem | Not opened | — | — | — |
| P4 | Invariance ⟹ Grain ⟹ Born | Not opened; premise proved nonvacuous | — | — | — |
| P5–P11 | Later milestones | Not opened | — | — | — |

### P2 — results actually closed

The pin targets `v1.1.1-probability-api`; the manifest diff is limited to
`quantum_foundations`. The three former goals in `Core/Parent.lean` vanished
with that file and were replaced by `parentOf` and its public lemmas. `Core/`
and `Refinement/` contain no `sorry`.

| File | Result closed during P2 | Goals closed |
|---|---|---:|
| `Core/Parent.lean` | Deleted `parent_mem`, `parent_le`, and `parent_unique` as redundant | 3 |
| `Core/Act.lean` | Total acts, indicators, order, combinations, and finite decomposition | 0 (skeleton completed without a new `sorry`) |
| `Refinement/PullbackAct.lean` | Reflexivity, transitivity, and fibre indicator through the upstream API | 0 |
| `Refinement/PayoffPreserving.lean` | `bornExpectation_pullback_eq` and the general invariance witness | 0 |
| `Refinement/Nonvacuity.lean` | State, strict binary refinement, and computed value `1` in `H 3` | 0 |
| `Core/Interface.lean` | Abstract interface, projective/effect instances, and abstract Grain-to-invariance bridge | 0 |

The strong measure-to-functional bridge is now proved: the sum is regrouped
over `parentOf` fibres, fibres are identified with `coarseCells`, and
`E₀_isGrain` closes each inner sum. The concrete witness computes the
expectation of constant act `1` on the fine and coarse binary perspectives.

### Final budget and unmet exit condition

The actual budget remains `4`, down from `7` at P2 entry. The four remaining
occurrences are:

| File | Declaration | Planned milestone |
|---|---|---|
| `Preference/Representation.lean` | `exists_unique_weights` | P3 |
| `BornCalibration/RefinementImpliesGrain.lean` | `refinement_invariant_implies_grain` | P4 / specification revisit |
| `BornCalibration/BornExpectation.lean` | `born_expectation_formula` | P4 |
| `Rivals/NaiveBranchCounting.lean` | `naiveCounting_violates_grain` | P6 |

The requested `SORRY_COUNT ≤ 2` threshold is therefore incompatible with the
instruction not to open P3 and with the prohibition on leaving `sorryAx`
under a declaration presented as closed. Both P4 theorems use the weight
supplied by `exists_unique_weights`. Moreover, the current hypothesis of
`refinement_invariant_implies_grain` applies only to globally
`PayoffPreserving` acts; the cell indicators needed for Grain do not satisfy
that global property. No statement was weakened and no goal was closed
artificially. P2 is technically implemented, but its overall status remains
flagged until this specification decision is made.

<!-- PIN_BUMP_AUDIT: **FR.** Mise à jour ciblée de `quantum_foundations` autorisée par `ALLOW_PIN_BUMP=1`. **EN.** Targeted `quantum_foundations` update authorized by `ALLOW_PIN_BUMP=1`. -->

<!-- PIN_BUMP_AUDIT: **FR.** Mise à jour ciblée de `quantum_foundations` autorisée par `ALLOW_PIN_BUMP=1`. **EN.** Targeted `quantum_foundations` update authorized by `ALLOW_PIN_BUMP=1`. -->
