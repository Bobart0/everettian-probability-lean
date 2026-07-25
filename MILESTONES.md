# MILESTONES.md — everettian-probability-lean

## Français

### Table des jalons

| Jalon | Objet | Statut | Date | Buts ouverts introduits | Buts ouverts fermés |
|---|---|---|---|---|---|
| P0 | Red team sur papier (portée, décisions P0.2/P0.3) | Préalable, hors dépôt (`PLAN_REVISE_everettian-probability-lean.md`) | — | — | — |
| P1 | Infrastructure du dépôt, squelette compilable | 🚧 EN COURS | 2026-07-25 | 7 | 0 |
| P2 | Invariance sous raffinement ⟹ Grain (preuve réelle) | Non ouvert | — | — | — |
| P3 | Théorème de représentation (preuve réelle) | Non ouvert | — | — | — |
| P4 | Espérance de Born (preuve réelle) | Non ouvert | — | — | — |
| P5 | Non-circularité (témoin qubit non bornien) | Non ouvert | — | — | — |
| P6 | Comptage naïf viole Grain (preuve réelle) | Non ouvert | — | — | — |
| P7 | Route effets / raffinement physique | Non ouvert | — | — | — |
| P8 | Incertitude diachronique | Non ouvert | — | — | — |
| P9 | Auto-localisation | Non ouvert | — | — | — |
| P10 | Confirmation empirique | Non ouvert | — | — | — |
| P11 | Calibration approximative, clôture | Non ouvert | — | — | — |

Seul **P1** est ouvert. Les jalons P2–P11 seront détaillés (stratégie,
sous-étapes, blueprint mathématique) à leur ouverture, sur le modèle des
sections « Jalons — … » de `quantum-foundations-lean/MILESTONES.md`.

### P1 — Infrastructure et squelette compilable

**Budget de buts ouverts : 7** (fichier `SORRY_BUDGET` à la racine, lu et
vérifié par `scripts/guard.sh`). Aucune augmentation de ce budget sans
commit dédié et justification ici.

| Fichier | Déclaration | Jalon de clôture prévu |
|---|---|---|
| `Core/Parent.lean` | `parent_mem` | P2 (immédiat une fois `Refines` déballé, mais différé pour garder P1 strictement infrastructurel) |
| `Core/Parent.lean` | `parent_le` | P2 |
| `Core/Parent.lean` | `parent_unique` | P2 |
| `Preference/Representation.lean` | `exists_unique_weights` | P3 |
| `BornCalibration/RefinementImpliesGrain.lean` | `refinement_invariant_implies_grain` | P2 |
| `BornCalibration/BornExpectation.lean` | `born_expectation_formula` | P4 |
| `Rivals/NaiveBranchCounting.lean` | `naiveCounting_violates_grain` | P6 |

Tout le reste du squelette P1 (dix-neuf fichiers Lean, dont cinq
`Nonvacuity.lean` et les deux fichiers placeholder `Core/Interface.lean`
et `BornCalibration/NonCircularity.lean`) compile sans aucun but ouvert.
Voir `Audit/MainResults.lean` pour l'audit `#print axioms` correspondant :
les déclarations ci-dessus révèlent `sorryAx` (directement ou par
transitivité via `pullbackAct_agree_of_agree`, seule déclaration à but
fermé qui en dépend transitivement) ; toutes les autres ne dépendent que
de `propext`, `Classical.choice`, `Quot.sound`.

**Critères de sortie de P1** (voir prompt de bootstrap, section 8) :
`lake build` vert, `scripts/preflight.sh` vert, `scripts/guard.sh` en
`GUARD_RESULT=PASS`, CI verte sur `master`, l'exemple de branchement de
`BornCalibration/BornExpectation.lean` compile sans but ouvert, et cette
table à jour.

## English

### Milestone table

| Milestone | Subject | Status | Date | Open goals introduced | Open goals closed |
|---|---|---|---|---|---|
| P0 | Paper red team (scope, decisions P0.2/P0.3) | Prerequisite, outside the repository (`PLAN_REVISE_everettian-probability-lean.md`) | — | — | — |
| P1 | Repository infrastructure, compilable skeleton | 🚧 IN PROGRESS | 2026-07-25 | 7 | 0 |
| P2 | Refinement invariance ⟹ Grain (real proof) | Not opened | — | — | — |
| P3 | Representation theorem (real proof) | Not opened | — | — | — |
| P4 | Born expectation (real proof) | Not opened | — | — | — |
| P5 | Non-circularity (non-Born qubit witness) | Not opened | — | — | — |
| P6 | Naive counting violates Grain (real proof) | Not opened | — | — | — |
| P7 | Effect route / physical refinement | Not opened | — | — | — |
| P8 | Diachronic uncertainty | Not opened | — | — | — |
| P9 | Self-location | Not opened | — | — | — |
| P10 | Empirical confirmation | Not opened | — | — | — |
| P11 | Approximate calibration, closure | Not opened | — | — | — |

Only **P1** is open. Milestones P2–P11 will be detailed (strategy,
sub-steps, mathematical blueprint) when they open, following the
"Milestones — …" section pattern of
`quantum-foundations-lean/MILESTONES.md`.

### P1 — Infrastructure and compilable skeleton

**Open-goal budget: 7** (`SORRY_BUDGET` file at the repository root, read
and checked by `scripts/guard.sh`). No increase to this budget without a
dedicated commit and justification here.

| File | Declaration | Planned closing milestone |
|---|---|---|
| `Core/Parent.lean` | `parent_mem` | P2 (immediate once `Refines` is unpacked, but deferred to keep P1 strictly infrastructural) |
| `Core/Parent.lean` | `parent_le` | P2 |
| `Core/Parent.lean` | `parent_unique` | P2 |
| `Preference/Representation.lean` | `exists_unique_weights` | P3 |
| `BornCalibration/RefinementImpliesGrain.lean` | `refinement_invariant_implies_grain` | P2 |
| `BornCalibration/BornExpectation.lean` | `born_expectation_formula` | P4 |
| `Rivals/NaiveBranchCounting.lean` | `naiveCounting_violates_grain` | P6 |

Everything else in the P1 skeleton (nineteen Lean files, including five
`Nonvacuity.lean` files and the two placeholder files
`Core/Interface.lean` and `BornCalibration/NonCircularity.lean`) compiles
with no open goal. See `Audit/MainResults.lean` for the corresponding
`#print axioms` audit: the declarations above reveal `sorryAx` (directly,
or transitively via `pullbackAct_agree_of_agree`, the only closed-goal
declaration that transitively depends on one); every other declaration
depends only on `propext`, `Classical.choice`, `Quot.sound`.

**P1 exit criteria** (see bootstrap prompt, section 8): green
`lake build`, green `scripts/preflight.sh`, `scripts/guard.sh` reporting
`GUARD_RESULT=PASS`, green CI on `master`, the bridging example in
`BornCalibration/BornExpectation.lean` compiling with no open goal, and
this table kept up to date.
