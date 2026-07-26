# MILESTONES.md — everettian-probability-lean

## Français

### Table des jalons

| Jalon | Objet | Statut | Date | Buts ouverts introduits | Buts ouverts fermés |
|---|---|---|---|---|---|
| P0 | Red team sur papier (portée, décisions P0.2/P0.3) | Préalable, hors dépôt (`PLAN_REVISE_everettian-probability-lean.md`) | — | — | — |
| P1 | Infrastructure du dépôt, squelette compilable | ✅ CLOS | 2026-07-25 | 7 | 0 |
| P2 | Modèle fini des actes et invariance sous raffinement | ⛔ BLOQUÉ PAR L'API AMONT | 2026-07-26 | 0 | 3 |
| P3 | Théorème de représentation (preuve réelle) | Non ouvert | — | — | — |
| P4 | Espérance de Born (preuve réelle) | Non ouvert | — | — | — |
| P5 | Non-circularité (témoin qubit non bornien) | Non ouvert | — | — | — |
| P6 | Comptage naïf viole Grain (preuve réelle) | Non ouvert | — | — | — |
| P7 | Route effets / raffinement physique | Non ouvert | — | — | — |
| P8 | Incertitude diachronique | Non ouvert | — | — | — |
| P9 | Auto-localisation | Non ouvert | — | — | — |
| P10 | Confirmation empirique | Non ouvert | — | — | — |
| P11 | Calibration approximative, clôture | Non ouvert | — | — | — |

P1 est clos. P2 est ouvert mais ne peut pas être clos avant une seconde
itération additive de l'API amont, détaillée ci-dessous. P3 n'est pas ouvert.

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

### P2 — État après jonction de l'API

Le pin vise `v1.1.0-probability-api`; le manifeste ne change que pour
`quantum_foundations`. `Core/Parent.lean` a été supprimé au profit de
`parentOf`. Les trois buts `parent_mem`, `parent_le`, `parent_unique` ont donc
disparu et le budget global passe de 7 à 4. `Core/` et les lemmes actuellement
présents dans `Refinement/` ne contiennent aucun `sorry`.

P2 reste néanmoins **non clos** : la non-vacuité forte demandée doit prouver
l'invariance de l'espérance bornienne sous un raffinement arbitraire. Cette
preuve requiert le résultat amont déjà existant
`QuantumFoundations.BornRule.refine_filter_sup_eq`, ou son corollaire
`E₀_isGrain`. Aucun des deux n'est atteignable depuis l'unique point d'entrée
`QuantumFoundations.ProbabilityAPI`. Les réimporter directement violerait la
frontière d'API; les reprouver en aval violerait la règle de non-duplication.
Une release additive amont doit donc les réexporter avant la reprise de P2.

## English

### Milestone table

| Milestone | Subject | Status | Date | Open goals introduced | Open goals closed |
|---|---|---|---|---|---|
| P0 | Paper red team (scope, decisions P0.2/P0.3) | Prerequisite, outside the repository (`PLAN_REVISE_everettian-probability-lean.md`) | — | — | — |
| P1 | Repository infrastructure, compilable skeleton | ✅ CLOSED | 2026-07-25 | 7 | 0 |
| P2 | Finite act model and refinement invariance | ⛔ BLOCKED BY UPSTREAM API | 2026-07-26 | 0 | 3 |
| P3 | Representation theorem (real proof) | Not opened | — | — | — |
| P4 | Born expectation (real proof) | Not opened | — | — | — |
| P5 | Non-circularity (non-Born qubit witness) | Not opened | — | — | — |
| P6 | Naive counting violates Grain (real proof) | Not opened | — | — | — |
| P7 | Effect route / physical refinement | Not opened | — | — | — |
| P8 | Diachronic uncertainty | Not opened | — | — | — |
| P9 | Self-location | Not opened | — | — | — |
| P10 | Empirical confirmation | Not opened | — | — | — |
| P11 | Approximate calibration, closure | Not opened | — | — | — |

P1 is closed. P2 is open but cannot be closed before a second additive
upstream API iteration, detailed below. P3 has not been opened.

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

### P2 — State after the API junction

The pin targets `v1.1.0-probability-api`; only `quantum_foundations` changes
in the manifest. `Core/Parent.lean` was deleted in favor of `parentOf`. The
three goals `parent_mem`, `parent_le`, and `parent_unique` therefore vanished,
reducing the global budget from 7 to 4. `Core/` and the lemmas currently
present in `Refinement/` contain no `sorry`.

P2 nevertheless remains **open**: the requested strong nonvacuity result must
prove that Born expectation is invariant under an arbitrary refinement. That
proof requires the existing upstream result
`QuantumFoundations.BornRule.refine_filter_sup_eq`, or its corollary
`E₀_isGrain`. Neither is reachable from the sole entry point
`QuantumFoundations.ProbabilityAPI`. Importing either directly would breach
the API boundary; reproving either downstream would breach the no-duplication
rule. An additive upstream release must re-export them before P2 resumes.

<!-- PIN_BUMP_AUDIT: **FR.** Mise à jour ciblée de `quantum_foundations` autorisée par `ALLOW_PIN_BUMP=1`. **EN.** Targeted `quantum_foundations` update authorized by `ALLOW_PIN_BUMP=1`. -->
