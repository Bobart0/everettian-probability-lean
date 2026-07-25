# Everettian Probability in Lean

> **Results are under construction. Nothing in this repository should be
> cited as an established result until milestone P11 closes.** See
> `MILESTONES.md` for exact status and `SORRY_BUDGET` for the current
> count of open goals.
>
> **Résultats en cours de construction. Rien dans ce dépôt ne doit être
> cité comme un résultat établi tant que le jalon P11 n'est pas clos.**
> Voir `MILESTONES.md` pour le statut exact et `SORRY_BUDGET` pour le
> nombre courant de buts ouverts.

## English

### Purpose

A Lean 4 / Mathlib formalization of the decision-theoretic layer of paper
II of a two-part research program: acts, consequences, refinement
invariance, rational expectation, and Bornian calibration, built on top of
the grain-coherence-to-Born representation theorem already proved in the
first installment, [`quantum-foundations-lean`](https://github.com/Bobart0/quantum-foundations-lean).
The scientific target is to show that every coherent expectation over
accessible consequences produces a contextual weight, that refinement
invariance of those consequences forces the upstream Grain axiom, and that
the upstream representation theorem then turns that expectation into a
Born expectation.

This milestone (**P1**) delivers repository infrastructure and a
compilable skeleton only. No scientific theorem is proved here; see
`docs/THEOREM_MAP.md` (currently empty) and `MILESTONES.md` for what is
open.

### Relation to `quantum-foundations-lean`

`quantum-foundations-lean` is an archived, DOI-tagged artifact
(`v1.0.1-fop-companion`) accompanying a manuscript submitted to
*Foundations of Physics*. It is **never modified** by this repository; it
is pulled in read-only, pinned, via a Lake dependency
(`lakefile.toml`). See `AGENTS.md` for the exact pin and the rule against
re-proving anything that already exists upstream.

### Repository structure

```
EverettianProbability/
├── Core/            — acts, the parent map, the (placeholder) interface
├── Refinement/       — act pullback, payoff-preserving invariance
├── Preference/        — rational expectation family, representation theorem
├── BornCalibration/    — contextual weight, Grain bridge, Born expectation,
│                         non-circularity target
├── Rivals/             — naive branch counting (a rival rule)
└── Audit/               — consolidated axiom audit
```

Milestone directories not yet opened (`PhysicalRefinement/`,
`Diachronic/`, `SelfLocation/`, `Confirmation/`, `Approximate/`) do not
exist yet and are created only when their milestone opens.

### Scope and limitations

No theorem in this repository derives a rationality norm from unitary
dynamics alone; refinement invariance is an assumed normative premise,
never derived. See `docs/SCOPE_AND_LIMITATIONS.md` for the full list.

### Reproducibility

```sh
git clone https://github.com/Bobart0/everettian-probability-lean.git
cd everettian-probability-lean
bash setup.sh   # lake exe cache get && lake build, plus git hooks
```

See `docs/REPRODUCIBILITY.md` for exact toolchain/revision pins and
PowerShell-equivalent commands.

### Axiom audit

```sh
lake env lean EverettianProbability/Audit/MainResults.lean
bash scripts/guard.sh
```

`scripts/guard.sh` fails on any `axiom`, `native_decide`, or
`maxHeartbeats 0`, and on an open-goal count exceeding `SORRY_BUDGET`.

### Citation

See `CITATION.cff`. Working title: *Everettian Probability in Lean:
Refinement-Invariant Rational Expectation*, version `0.1.0-dev`.

### AI-assisted development

See `docs/AI_ASSISTANCE.md`.

## Français

### Objet

Une formalisation Lean 4 / Mathlib de la couche de théorie de la décision
de l'article II d'un programme de recherche en deux volets : actes,
conséquences, invariance sous raffinement, espérance rationnelle et
calibration bornienne, construite au-dessus du théorème de représentation
« cohérence de grain vers Born » déjà prouvé dans le premier volet,
[`quantum-foundations-lean`](https://github.com/Bobart0/quantum-foundations-lean).
L'objectif scientifique est de montrer que toute espérance cohérente sur
les conséquences accessibles produit un poids contextuel, que l'invariance
sous raffinement de ces conséquences force l'axiome Grain amont, et que le
théorème de représentation amont transforme alors cette espérance en
espérance de Born.

Ce jalon (**P1**) livre uniquement l'infrastructure du dépôt et un
squelette compilable. Aucun théorème scientifique n'y est prouvé ; voir
`docs/THEOREM_MAP.md` (vide pour l'instant) et `MILESTONES.md` pour ce qui
reste ouvert.

### Relation avec `quantum-foundations-lean`

`quantum-foundations-lean` est un artefact archivé, avec DOI et tag
(`v1.0.1-fop-companion`), accompagnant un manuscrit soumis à *Foundations
of Physics*. Il n'est **jamais modifié** par ce dépôt ; il est tiré en
lecture seule, épinglé, via une dépendance Lake (`lakefile.toml`). Voir
`AGENTS.md` pour le pin exact et la règle interdisant de re-prouver ce qui
existe déjà en amont.

### Structure du dépôt

Voir la section anglaise ci-dessus (le contenu est identique). Les
répertoires des jalons non ouverts (`PhysicalRefinement/`, `Diachronic/`,
`SelfLocation/`, `Confirmation/`, `Approximate/`) n'existent pas encore et
ne sont créés qu'à l'ouverture de leur jalon respectif.

### Portée et limites

Aucun théorème de ce dépôt ne dérive une norme de rationalité de la seule
dynamique unitaire ; l'invariance sous raffinement est une prémisse
normative assumée, jamais dérivée. Liste complète dans
`docs/SCOPE_AND_LIMITATIONS.md`.

### Reproductibilité

```sh
git clone https://github.com/Bobart0/everettian-probability-lean.git
cd everettian-probability-lean
bash setup.sh   # lake exe cache get && lake build, plus les hooks git
```

Voir `docs/REPRODUCIBILITY.md` pour les épinglages exacts de la chaîne
d'outils et des révisions, ainsi que les commandes équivalentes en
PowerShell.

### Audit des axiomes

```sh
lake env lean EverettianProbability/Audit/MainResults.lean
bash scripts/guard.sh
```

`scripts/guard.sh` échoue sur tout `axiom`, `native_decide`, ou
`maxHeartbeats 0`, et sur un nombre de buts ouverts dépassant
`SORRY_BUDGET`.

### Citation

Voir `CITATION.cff`. Titre de travail : *Everettian Probability in Lean:
Refinement-Invariant Rational Expectation*, version `0.1.0-dev`.

### Assistance par intelligence artificielle

Voir `docs/AI_ASSISTANCE.md`.
