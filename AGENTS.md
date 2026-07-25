# AGENTS.md — everettian-probability-lean

## Mission

Formaliser en Lean 4 / Mathlib la **couche de théorie de la décision** de
l'article II du programme de recherche dont le premier volet,
`quantum-foundations-lean` (archive Zenodo, DOI, tag
`v1.0.1-fop-companion`), est clos et non modifié. L'objectif scientifique :
montrer que toute espérance cohérente sur les conséquences accessibles
produit un poids contextuel, que l'invariance sous raffinement de ces
conséquences force l'axiome Grain, et que le théorème de représentation
déjà prouvé en amont (`grainCoherenceTheorem_projector`) transforme alors
cette espérance en espérance de Born.

**État d'avancement par jalon** (détail et suivi du budget de buts ouverts
dans `MILESTONES.md`) :

- **P0** — red team sur papier (portée, décisions P0.2/P0.3). Préalable à P1.
- **P1** — infrastructure du dépôt et squelette compilable. 🚧 EN COURS.
  Dix-neuf fichiers Lean (`Core`, `Refinement`, `Preference`,
  `BornCalibration`, `Rivals`, `Audit`), sept buts ouverts budgétés
  (`SORRY_BUDGET`), aucun résultat scientifique prouvé.
- **P2–P11** — non ouverts. Voir `CLAIM_MATRIX.md` pour la table vide
  colonnée qui les attend.

## Dépendance `quantum_foundations`

Le paquet `quantum_foundations` est une dépendance Lake épinglée sur le tag
`v1.0.1-fop-companion` (`lakefile.toml`). Il tire lui-même `gleason`
(`v1.0-gleason`) et `mathlib` (rev figée) : Lake les résout
transitivement, ils ne sont **jamais** redéclarés ici. **NE JAMAIS
re-prouver ce qui existe déjà en amont** : importer directement
`Perspective`, `Refines`, `AxGrain`/`AxNorm`/`AxPos`/`AxNul`,
`grainCoherenceTheorem_projector`, l'API `EffectPerspectives`, l'API
`BornBridge`. En cas de doute sur l'existence d'un lemme côté amont :
`grep` le paquet cloné en lecture seule (ou `.lake/packages/`) AVANT
d'écrire, comme documenté dans le prompt de bootstrap, section 3.

## Conventions

Reprend celles de l'amont (voir sa copie ci-dessous, section « Conventions
héritées »), plus trois spécifiques à ce dépôt :

- **Un acte est une fonction totale** `Submodule ℂ (H n) → ℝ`, avec valeur
  poubelle hors perspective, jamais un sous-type dépendant d'une
  perspective (`EverettianProbability/Core/Act.lean`).
- **Le poids contextuel** doit atterrir **exactement** dans le type
  `Perspective n → Submodule ℂ (H n) → ℝ`, afin que
  `grainCoherenceTheorem_projector` s'applique sans adaptateur
  (`BornCalibration/ContextualWeight.lean`).
- **`Refines` est une relation `∀∃`**, pas une fonction : toute carte
  parent passe par `Classical.choice` plus `Perspective.unique_parent`,
  avec lemmes de spécification séparés (`Core/Parent.lean`).

## Règles absolues

1. `axiom` INTERDIT. `native_decide` INTERDIT. La CI (`scripts/guard.sh`)
   échoue sinon.
2. `set_option maxHeartbeats 0` INTERDIT. Valeur finie uniquement, portée
   locale (`in`).
3. But ouvert honnête : ne JAMAIS affaiblir un énoncé pour le fermer. Tout
   changement d'énoncé = commit dédié + message explicite.
4. **Nonvacuity** : toute nouvelle structure d'hypothèses reçoit un
   habitant concret dans un `Nonvacuity.lean` du même sous-répertoire,
   DANS LE MÊME COMMIT.
5. `lake build` après CHAQUE modification. Commit après chaque étape
   verte.
6. Fichiers < 1500 lignes.
7. `git push --force` INTERDIT sans confirmation humaine explicite.
8. `lake update` INTERDIT. Les révisions sont épinglées et ne dérivent
   pas ; un bump intentionnel est une action séparée, explicite,
   approuvée par un humain.
9. Bilinguisme : tout fichier `.md` et tout docstring de module est
   rédigé en français puis en anglais (blocs `**FR.** … **EN.** …` en
   Lean, sections `## Français` / `## English` en Markdown).
10. Aucune signature n'est devinée : avant d'écrire du code contre l'API
    du dépôt amont, elle est vérifiée par `grep` puis par
    `lake env lean --stdin`.

### Conventions héritées (patrons anti-lenteur, `gleason`/`quantum-foundations-lean`)

- Si un `rw` substitue une grosse expression (somme indexée) que des
  réécritures ultérieures doivent traverser → `generalize` immédiat sous
  un nom opaque ; assemblages lourds → lemme `private` à contexte
  minimal.
- `simp` toujours contraint (`simp only [...]`) dans les assemblages ;
  jamais `simp [lemme]` nu dans un assemblage lourd.
- Un dépassement de `maxHeartbeats` est un signal de restructuration
  (extraire un lemme `private` à contexte minimal, `generalize`), jamais
  une augmentation aveugle.
- Si un `obtain`/`refine` composant plusieurs lemmes part en timeout au
  `whnf` malgré une preuve mathématiquement immédiate : extraire l'énoncé
  combiné dans un lemme `private` à part entière, puis l'appliquer par
  simple application de fonction aux cas concrets — jamais d'inlining
  forcé ni d'augmentation de `maxHeartbeats`.
- Si un but résiste plus de 20–30 minutes : montrer le but exact plutôt
  que d'empiler des tactiques à l'aveugle.

## Frontière de portée

> Aucun théorème de ce dépôt ne dérive une norme de rationalité de la
> seule dynamique unitaire ; l'invariance sous raffinement
> (`PayoffPreserving`, préservée par la fonctionnelle d'espérance `V`)
> est une **prémisse normative**, assumée comme telle et jamais dérivée.
> Détail complet dans `docs/SCOPE_AND_LIMITATIONS.md`.

## Git

- Branche `master` (pas `main`, pour rester homogène avec l'amont),
  commits atomiques, messages `feat|fix|chore(scope): …`.
- JAMAIS `git push --force` sans confirmation humaine explicite.
- Ne jamais changer la visibilité du dépôt soi-même.

---

## English translation

# AGENTS.md — everettian-probability-lean

## Mission

Formalize in Lean 4 / Mathlib the **decision-theoretic layer** of paper II
of the research program whose first installment,
`quantum-foundations-lean` (Zenodo archive, DOI, tag
`v1.0.1-fop-companion`), is closed and never modified. The scientific
goal: to show that every coherent expectation over accessible consequences
produces a contextual weight, that refinement invariance of those
consequences forces the Grain axiom, and that the representation theorem
already proved upstream (`grainCoherenceTheorem_projector`) then turns
that expectation into a Born expectation.

**Milestone status** (detail and open-goal budget tracking in
`MILESTONES.md`):

- **P0** — paper red team (scope, decisions P0.2/P0.3). Prerequisite to P1.
- **P1** — repository infrastructure and compilable skeleton. 🚧 IN
  PROGRESS. Nineteen Lean files (`Core`, `Refinement`, `Preference`,
  `BornCalibration`, `Rivals`, `Audit`), seven budgeted open goals
  (`SORRY_BUDGET`), no scientific result proved.
- **P2–P11** — not opened. See `CLAIM_MATRIX.md` for the empty, columned
  table awaiting them.

## `quantum_foundations` dependency

The `quantum_foundations` package is a Lake dependency pinned to tag
`v1.0.1-fop-companion` (`lakefile.toml`). It itself pulls `gleason`
(`v1.0-gleason`) and `mathlib` (fixed revision): Lake resolves them
transitively, they are **never** redeclared here. **NEVER re-prove what
already exists upstream**: import `Perspective`, `Refines`,
`AxGrain`/`AxNorm`/`AxPos`/`AxNul`,
`grainCoherenceTheorem_projector`, the `EffectPerspectives` API, and the
`BornBridge` API directly. When in doubt about whether an upstream lemma
exists: `grep` the read-only cloned package (or `.lake/packages/`) BEFORE
writing, as documented in the bootstrap prompt, section 3.

## Conventions

Inherits upstream's own (see its copy below, "Inherited conventions"
section), plus three specific to this repository:

- **An act is a total function** `Submodule ℂ (H n) → ℝ`, with a junk
  value outside the perspective, never a subtype depending on a
  perspective (`EverettianProbability/Core/Act.lean`).
- **The contextual weight** must land **exactly** in the type
  `Perspective n → Submodule ℂ (H n) → ℝ`, so that
  `grainCoherenceTheorem_projector` applies with no adapter
  (`BornCalibration/ContextualWeight.lean`).
- **`Refines` is a `∀∃` relation**, not a function: every parent map goes
  through `Classical.choice` plus `Perspective.unique_parent`, with
  separate specification lemmas (`Core/Parent.lean`).

## Absolute rules

1. `axiom` FORBIDDEN. `native_decide` FORBIDDEN. CI (`scripts/guard.sh`)
   fails otherwise.
2. `set_option maxHeartbeats 0` FORBIDDEN. Finite value only, local scope
   (`in`).
3. Honest open goals: NEVER weaken a statement to close it. Any statement
   change = dedicated commit + explicit message.
4. **Nonvacuity**: every new hypothesis-bundling structure receives a
   concrete witness in a `Nonvacuity.lean` in the same subdirectory, IN
   THE SAME COMMIT.
5. `lake build` after EVERY change. Commit after every green step.
6. Files < 1500 lines.
7. `git push --force` FORBIDDEN without explicit human confirmation.
8. `lake update` FORBIDDEN. Revisions are pinned and do not drift; an
   intentional bump is a separate, explicit, human-approved action.
9. Bilingualism: every `.md` file and every module docstring is written
   in French then English (`**FR.** … **EN.** …` blocks in Lean,
   `## Français` / `## English` sections in Markdown).
10. No signature is ever guessed: before writing code against the
    upstream repository's API, it is checked via `grep` then via
    `lake env lean --stdin`.

### Inherited conventions (anti-slowness patterns, `gleason`/`quantum-foundations-lean`)

- If a `rw` substitutes a large expression (an indexed sum) that later
  rewrites must traverse → immediate `generalize` under an opaque name;
  heavy assemblies → a `private` lemma at minimal context.
- `simp` always constrained (`simp only [...]`) in assemblies; never a
  bare `simp [lemma]` in a heavy assembly.
- A `maxHeartbeats` overrun is a restructuring signal (extract a
  `private` lemma at minimal context, `generalize`), never a blind
  increase.
- If an `obtain`/`refine` composing several lemmas times out at `whnf`
  despite a mathematically immediate proof: extract the combined
  statement into its own `private` lemma, then apply it by plain
  function application to the concrete cases — never forced inlining nor
  a blind `maxHeartbeats` increase.
- If a goal resists for more than 20–30 minutes: show the exact goal
  rather than stacking tactics blindly.

## Scope boundary

> No theorem in this repository derives a rationality norm from unitary
> dynamics alone; refinement invariance (`PayoffPreserving`, preserved by
> the expectation functional `V`) is a **normative premise**, assumed as
> such and never derived. Full detail in
> `docs/SCOPE_AND_LIMITATIONS.md`.

## Git

- Branch `master` (not `main`, to stay consistent with upstream), atomic
  commits, `feat|fix|chore(scope): …` messages.
- NEVER `git push --force` without explicit human confirmation.
- Never change the repository's visibility unilaterally.
