# MILESTONES.md — everettian-probability-lean

## Français

### État au 2026-07-26

| Jalon | Objet | Statut | Buts fermés dans cette reprise |
|---|---|---|---:|
| P0 | Décisions d’architecture | P0.3 et **P0.4 closes** | 0 |
| P1 | Infrastructure et squelette | Clos | 0 |
| P2 | Actes finis, tiré-en-arrière, non-vacuité bornienne | Clos | 0 |
| P3 | Représentation affine canonique | Clos | 1 |
| P4 | Invariance locale ⇔ Grain ⇒ Born (**équivalence**, pas seulement implication) | Clos, non vacueux et non trivial | 2 |
| P6 | Exclusion du comptage naïf | Résultat scalaire clos ; **P6a close** (témoin d'existence) | 2 |
| P5, P7–P11 | Jalons ultérieurs | Non ouverts (rapport de faisabilité route effets/qubit dans `docs/QUBIT_FEASIBILITY_REPORT.md`) | 0 |

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

### Reprise du 2026-07-26 (suite) — équivalence, P0.4, classification, non-trivialité

- **`refinementInvariantLocal_iff_axGrain`** (`BornCalibration/
  RefinementImpliesGrain.lean`) : la prémisse normative n'est plus
  seulement suffisante pour Grain, elle lui est **équivalente**. Le sens
  réciproque combine `represents` avec une nouvelle identité de sommation
  générique (`grain_pullback_sum_eq`, généralisant
  `bornExpectation_pullback_eq` à tout poids satisfaisant `AxGrain`).
- **P0.4 close** : `BornCalibration/NonCircularity.lean` contient
  désormais `perspective_two_cases` (classification structurelle en
  `n = 2`) et `skewWeight` — une règle non bornienne satisfaisant
  `AxGrain`, `AxNorm`, `AxPos`, `AxNul` — avec le témoin explicite
  `grain_does_not_imply_born_at_two` (`witnessState = (3/5, 4/5)`,
  `skewF(9/25) = 81/337 ≠ 9/25`). Le fichier n'est plus un placeholder.
- **Classification de `hNul`** corrigée dans `CLAIM_MATRIX.md`,
  `docs/THEOREM_MAP.md`, `docs/SCOPE_AND_LIMITATIONS.md` : le théorème
  principal repose sur deux prémisses-ponts, pas une seule — l'invariance
  locale (normative pure) et `hNul` (normative-physique, seul point
  d'entrée de l'état `v`).
- **`maxExpectation_not_affine`** (`Preference/NonTriviality.lean`) :
  témoin négatif manquant identifié par l'audit rétroactif
  (`ARCHITECTURE_NOTES.md`) — le maximum sur les cellules est monotone et
  normalisé mais viole l'affinité, et ne peut donc pas compléter une
  `RationalExpectationFamily`.
- **Rapport de faisabilité route effets/qubit** :
  `docs/QUBIT_FEASIBILITY_REPORT.md`. Aucun code ouvert ; identifie une
  brique amont manquante nommée (`projectionEffect_weight_eq_born`/
  `contextual_projection_weight_eq_born`, déjà prouvées pour `n ≥ 1` en
  amont mais non réexportées) et trois différences structurelles de
  `Refines` empêchant une transposition telle quelle de
  `RefinementInvariantLocal`.

Budget toujours à `0` ; aucun `sorry` introduit par cette reprise.

### Reprise du 2026-07-26 (suite 2) — P6a, témoin physique de raffinement record-neutre

- **`EverettianProbability/PhysicalRefinement/`** (nouveau répertoire,
  route B — construction autonome sur Mathlib, sans dépendance amont
  supplémentaire) : témoin concret, à amplitudes inégales (`3/5`, `4/5`),
  qu'un raffinement peut redécrire les branches plus finement sans en créer
  de nouvelles au sens physique. Dans `H 3`, un ancilla à deux niveaux
  (`b 1`, `b 2`) initialisé sur `b 1` est couplé par une rotation unitaire
  `coupleU` à la branche observée `b 0`, sans jamais faire sortir la
  population de la cellule grossière complémentaire `label1Space`.
- **`RecordNeutralWitness.lean`** : les quatre théorèmes demandés, sans
  `sorry` — `recordNeutral_refines` (le raffinement en trois lignes
  raffine bien la perspective binaire grossière), `recordNeutral_record_eq`
  (le record accessible, restreint aux deux cellules grossières, est
  inchangé), `recordNeutral_payoff_eq` (le paiement tiré en arrière vaut
  `1` sur les deux cellules d'ancilla), `recordNeutral_bornWeight_eq` (les
  poids borniens des deux cellules grossières sont inchangés). L'hypothèse
  qui fait de ce raffinement un témoin *record-neutre* — les lignes
  d'ancilla ne sont pas des cellules de l'algèbre de records — est rendue
  explicite et nommée : `RefinementNotInRecordAlgebra`, prouvée dans ce modèle
  par `refinementNotInRecordAlgebra_holds`.
- **`NonTriviality.lean`** : le comptage uniforme *restreint aux cellules
  actives* (`activeCells`, `uniformCredence` — un comptage sur toutes les
  cellules de `finePerspective` serait aveugle, puisque son cardinal ne
  change pas) distingue avant et après le couplage (`1/2 ≠ 1/3`,
  `counting_sensitive_to_recordNeutral_refinement`), et la forme
  existentielle demandée `counting_underdetermined_by_accessible_record`
  exhibe deux états (`psiBefore`, `psiAfter = coupleU psiBefore`) au même
  record accessible mais à des verdicts de comptage différents.
- **`Nonvacuity.lean`** : le pendant bornien —
  `born_insensitive_to_recordNeutral_refinement` et sa généralisation
  `born_determined_by_accessible_record` — montre que l'espérance
  bornienne, à la différence du comptage, est entièrement déterminée par le
  record accessible.
- **Portée** : ce témoin établit une **existence**, pas une universalité ;
  voir l'encart dédié dans `docs/SCOPE_AND_LIMITATIONS.md`.

Budget toujours à `0` ; aucun `sorry` introduit.

## English

### Status on 2026-07-26

| Milestone | Subject | Status | Goals closed in this resumption |
|---|---|---|---:|
| P0 | Architecture decisions | P0.3 and **P0.4 closed** | 0 |
| P1 | Infrastructure and skeleton | Closed | 0 |
| P2 | Finite acts, pullback, Born nonvacuity | Closed | 0 |
| P3 | Canonical affine representation | Closed | 1 |
| P4 | Local invariance ⇔ Grain ⇒ Born (**equivalence**, not just implication) | Closed, nonvacuous, and nontrivial | 2 |
| P6 | Exclusion of naive counting | Scalar result closed; **P6a closed** (existence witness) | 2 |
| P5, P7–P11 | Later milestones | Not opened (effect/qubit route feasibility report in `docs/QUBIT_FEASIBILITY_REPORT.md`) | 0 |

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

### 2026-07-26 resumption (continued) — equivalence, P0.4, classification, nontriviality

- **`refinementInvariantLocal_iff_axGrain`** (`BornCalibration/
  RefinementImpliesGrain.lean`): the normative premise is no longer just
  sufficient for Grain, it is **equivalent** to it. The converse combines
  `represents` with a new generic summation identity
  (`grain_pullback_sum_eq`, generalizing `bornExpectation_pullback_eq` to
  any weight satisfying `AxGrain`).
- **P0.4 closed**: `BornCalibration/NonCircularity.lean` now contains
  `perspective_two_cases` (structural classification at `n = 2`) and
  `skewWeight` — a non-Born rule satisfying `AxGrain`, `AxNorm`, `AxPos`,
  `AxNul` — with the explicit witness
  `grain_does_not_imply_born_at_two` (`witnessState = (3/5, 4/5)`,
  `skewF(9/25) = 81/337 ≠ 9/25`). The file is no longer a placeholder.
- **`hNul` classification** corrected in `CLAIM_MATRIX.md`,
  `docs/THEOREM_MAP.md`, `docs/SCOPE_AND_LIMITATIONS.md`: the headline
  theorem rests on two bridge premises, not one — local invariance
  (purely normative) and `hNul` (normative-physical, the only entry
  point for the state `v`).
- **`maxExpectation_not_affine`** (`Preference/NonTriviality.lean`): the
  missing negative witness identified by the retroactive audit
  (`ARCHITECTURE_NOTES.md`) — the max over cells is monotone and
  normalized but violates affinity, and therefore cannot complete a
  `RationalExpectationFamily`.
- **Effect/qubit route feasibility report**:
  `docs/QUBIT_FEASIBILITY_REPORT.md`. No work opened; identifies one
  named missing upstream brick
  (`projectionEffect_weight_eq_born`/`contextual_projection_weight_eq_born`,
  already proved for `n ≥ 1` upstream but not re-exported) and three
  structural differences in `Refines` preventing a direct transposition
  of `RefinementInvariantLocal`.

Budget still `0`; no `sorry` introduced by this resumption.

### 2026-07-26 resumption (continued 2) — P6a, physical witness of a record-neutral refinement

- **`EverettianProbability/PhysicalRefinement/`** (new directory, Route B —
  self-contained construction on Mathlib, no additional upstream
  dependency): a concrete witness, with unequal amplitudes (`3/5`, `4/5`),
  that a refinement can redescribe branches more finely without physically
  creating new ones. In `H 3`, a two-level ancilla (`b 1`, `b 2`)
  initialized on `b 1` is coupled by a unitary rotation `coupleU` to the
  observed branch `b 0`, never moving population out of the complementary
  coarse cell `label1Space`.
- **`RecordNeutralWitness.lean`**: the four required theorems, with no
  `sorry` — `recordNeutral_refines` (the three-line refinement does refine
  the coarse binary perspective), `recordNeutral_record_eq` (the
  accessible record, restricted to the two coarse cells, is unchanged),
  `recordNeutral_payoff_eq` (the pulled-back payoff equals `1` on both
  ancilla cells), `recordNeutral_bornWeight_eq` (the Born weights of the
  two coarse cells are unchanged). The hypothesis that makes this
  refinement a *record-neutral* witness — the ancilla lines are not cells
  of the record algebra — is made explicit and named:
  `RefinementNotInRecordAlgebra`, proved for this model by
  `refinementNotInRecordAlgebra_holds`.
- **`NonTriviality.lean`**: uniform counting *restricted to active cells*
  (`activeCells`, `uniformCredence` — counting over every cell of
  `finePerspective` would be blind, since its cardinality never changes)
  discriminates before and after the coupling (`1/2 ≠ 1/3`,
  `counting_sensitive_to_recordNeutral_refinement`), and the requested
  existential form `counting_underdetermined_by_accessible_record`
  exhibits two states (`psiBefore`, `psiAfter = coupleU psiBefore`) with
  the same accessible record but different counting verdicts.
- **`Nonvacuity.lean`**: the Born counterpart —
  `born_insensitive_to_recordNeutral_refinement` and its generalization
  `born_determined_by_accessible_record` — shows that Born expectation,
  unlike counting, is fully determined by the accessible record.
- **Scope**: this witness establishes an **existence**, not a
  universality claim; see the dedicated caveat in
  `docs/SCOPE_AND_LIMITATIONS.md`.

Budget still `0`; no `sorry` introduced.
