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

### Main results, with their scope limitations

- **`refinementInvariantLocal_iff_axGrain`**
  (`BornCalibration/RefinementImpliesGrain.lean`): local invariance under
  refinement is **exactly** the upstream Grain axiom on the canonical
  weight — an equivalence, not just one direction.
- **`born_expectation_of_invariance`**
  (`BornCalibration/BornExpectation.lean`): the headline theorem. Rests on
  **two bridge premises**, not one — local refinement invariance (purely
  normative) and null canonical weight on the state's support (`AxNul`, a
  normative-physical bridge, since it references the physical state `v`)
  — plus `RationalExpectationFamily` and, critically, **`3 ≤ n`**: the
  result covers Hilbert spaces of dimension at least 3 (the domain of the
  upstream Gleason theorem), not the qubit.
- **`grain_does_not_imply_born_at_two`**
  (`BornCalibration/NonCircularity.lean`): at `n = 2`, an explicit
  non-Born rule (`skewWeight`) satisfies Grain, Norm, Pos, and Null — the
  repository's own witness that the headline premise is not the Born rule
  in disguise, and the reason the `3 ≤ n` restriction above is load-bearing
  rather than a formality.
- **`naiveCounting_violates_grain`** (`Rivals/NaiveBranchCounting.lean`):
  naive branch counting violates Grain, a concrete exclusion result for
  the simplest rival rule.
- **`PhysicalRefinement/`** (milestone P6a): a concrete unitary witness, in
  `H 3`, that a refinement can redescribe branches more finely without
  physically creating new ones — record, payoff, and Born weights
  unchanged, active-cell count increased. This is an **existence** witness
  (one construction, in a schematic model with a stipulated, not derived,
  record algebra), not a universality claim about every refinement.

Every result above is proved with `SORRY_COUNT = 0`; see
`docs/THEOREM_MAP.md` for the full dependency and scope table, and
`docs/SCOPE_AND_LIMITATIONS.md` for the complete list of caveats,
including the ones above.

### Milestone status

| Milestone | Subject | Status |
|---|---|---|
| P0.3, P0.4 | Interface decision; `n = 2` non-circularity witness | Closed |
| P1–P4 | Infrastructure; acts and pullback; canonical representation; invariance ⇔ Grain ⇒ Born | Closed |
| P6 | Exclusion of naive counting | Closed |
| P6a | Physical witness of a record-neutral refinement | Closed (existence witness) |
| P5, P6b, P7–P12, qubit route, primitive-preference route | Later milestones | Not opened |

See `MILESTONES.md` for closure details and `docs/PROGRAM_STATUS.md` for a
full audit of every milestone, including — for each not-yet-opened one —
whether reusable scaffolding exists, whether the difficulty is one of
proof or of design, and what non-formal decisions must be made first.

### Relation to `quantum-foundations-lean`

`quantum-foundations-lean` is an archived, DOI-tagged artifact accompanying
a manuscript submitted to *Foundations of Physics*. It is **never
modified** by this repository; it is pulled in read-only, pinned to a
specific tag, via a Lake dependency (`lakefile.toml`). See `AGENTS.md` for
the exact pin and the rule against re-proving anything that already exists
upstream.

### Repository structure

```
EverettianProbability/
├── Core/                — acts, the abstract perspective interface
├── Refinement/           — act pullback, payoff-preserving invariance
├── Preference/            — rational expectation family, representation theorem
├── BornCalibration/        — contextual weight, Grain bridge, Born expectation,
│                             non-circularity witness (n = 2)
├── Rivals/                 — naive branch counting (a rival rule)
├── PhysicalRefinement/      — physical witness of a record-neutral refinement (P6a)
└── Audit/                    — consolidated axiom audit
```

Milestone directories not yet opened (`Diachronic/`, `SelfLocation/`,
`Confirmation/`, `Approximate/`) do not exist yet and are created only
when their milestone opens.

### Scope and limitations

No theorem in this repository derives a rationality norm from unitary
dynamics alone; refinement invariance is an assumed normative premise,
never derived. The headline theorem rests on two bridge premises and a
`3 ≤ n` dimension restriction (see above). See
`docs/SCOPE_AND_LIMITATIONS.md` for the full list, and
`docs/ARGUMENT_MAP.md` for an explicit audit of formulations this
repository does and does not license.

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
`maxHeartbeats 0`, and on an open-goal count exceeding `SORRY_BUDGET`
(currently `0`).

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

### Résultats principaux, avec leurs limitations de portée

- **`refinementInvariantLocal_iff_axGrain`**
  (`BornCalibration/RefinementImpliesGrain.lean`) : l'invariance locale
  sous raffinement est **exactement** l'axiome Grain amont sur le poids
  canonique — une équivalence, pas seulement un sens.
- **`born_expectation_of_invariance`**
  (`BornCalibration/BornExpectation.lean`) : le théorème principal. Repose
  sur **deux prémisses-ponts**, pas une seule — l'invariance locale sous
  raffinement (purement normative) et la nullité du poids canonique sur le
  support de l'état (`AxNul`, un pont normatif-physique, car elle
  référence l'état physique `v`) — plus `RationalExpectationFamily` et,
  point critique, **`3 ≤ n`** : le résultat couvre les espaces de Hilbert
  de dimension au moins 3 (le domaine du théorème de Gleason amont), pas
  le qubit.
- **`grain_does_not_imply_born_at_two`**
  (`BornCalibration/NonCircularity.lean`) : en `n = 2`, une règle non
  bornienne explicite (`skewWeight`) satisfait Grain, Norm, Pos et Null —
  le témoin propre du dépôt que la prémisse principale n'est pas la règle
  de Born déguisée, et la raison pour laquelle la restriction `3 ≤ n`
  ci-dessus est structurante, pas une formalité.
- **`naiveCounting_violates_grain`** (`Rivals/NaiveBranchCounting.lean`) :
  le comptage naïf des branches viole Grain, un résultat d'exclusion
  concret pour la règle rivale la plus simple.
- **`PhysicalRefinement/`** (jalon P6a) : un témoin unitaire concret, dans
  `H 3`, qu'un raffinement peut redécrire les branches plus finement sans
  en créer de nouvelles au sens physique — record, paiement et poids
  borniens inchangés, nombre de cellules actives augmenté. C'est un témoin
  d'**existence** (une construction, dans un modèle schématique à
  l'algèbre de records stipulée, non dérivée), pas une revendication
  d'universalité sur tout raffinement.

Chaque résultat ci-dessus est prouvé avec `SORRY_COUNT = 0` ; voir
`docs/THEOREM_MAP.md` pour la table complète des dépendances et de la
portée, et `docs/SCOPE_AND_LIMITATIONS.md` pour la liste complète des
réserves, incluant celles ci-dessus.

### État des jalons

| Jalon | Objet | Statut |
|---|---|---|
| P0.3, P0.4 | Décision d'architecture ; témoin de non-circularité en `n = 2` | Clos |
| P1–P4 | Infrastructure ; actes et tiré-en-arrière ; représentation canonique ; invariance ⇔ Grain ⇒ Born | Clos |
| P6 | Exclusion du comptage naïf | Clos |
| P6a | Témoin physique de raffinement record-neutre | Clos (témoin d'existence) |
| P5, P6b, P7–P12, route qubit, route des préférences primitives | Jalons ultérieurs | Non ouverts |

Voir `MILESTONES.md` pour le détail des fermetures et
`docs/PROGRAM_STATUS.md` pour un audit complet de chaque jalon, incluant —
pour chaque jalon non ouvert — l'existence ou non d'un échafaudage
réutilisable, la nature de la difficulté (preuve ou conception), et les
décisions non formelles préalables requises.

### Relation avec `quantum-foundations-lean`

`quantum-foundations-lean` est un artefact archivé, avec DOI, accompagnant
un manuscrit soumis à *Foundations of Physics*. Il n'est **jamais
modifié** par ce dépôt ; il est tiré en lecture seule, épinglé à un tag
précis, via une dépendance Lake (`lakefile.toml`). Voir `AGENTS.md` pour le
pin exact et la règle interdisant de re-prouver ce qui existe déjà en
amont.

### Structure du dépôt

Voir la section anglaise ci-dessus (le contenu est identique). Les
répertoires des jalons non ouverts (`Diachronic/`, `SelfLocation/`,
`Confirmation/`, `Approximate/`) n'existent pas encore et ne sont créés
qu'à l'ouverture de leur jalon respectif.

### Portée et limites

Aucun théorème de ce dépôt ne dérive une norme de rationalité de la seule
dynamique unitaire ; l'invariance sous raffinement est une prémisse
normative assumée, jamais dérivée. Le théorème principal repose sur deux
prémisses-ponts et une restriction de dimension `3 ≤ n` (voir ci-dessus).
Liste complète dans `docs/SCOPE_AND_LIMITATIONS.md`, et audit explicite des
formulations autorisées ou non dans `docs/ARGUMENT_MAP.md`.

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
`SORRY_BUDGET` (actuellement `0`).

### Citation

Voir `CITATION.cff`. Titre de travail : *Everettian Probability in Lean:
Refinement-Invariant Rational Expectation*, version `0.1.0-dev`.

### Assistance par intelligence artificielle

Voir `docs/AI_ASSISTANCE.md`.
