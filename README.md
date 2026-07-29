# Everettian Probability in Lean

> **The first conditional formal result is closed and the `v1.0.0`
> conditional API is stable.** The exact finite physical core exists as a
> separate experimental layer whose API is not yet frozen. Realistic and
> approximate physical programmes remain unfinished. No rational norm is
> claimed to follow from unitary dynamics alone.
>
> **Le premier resultat formel conditionnel est clos et l'API conditionnelle
> `v1.0.0` est stable.** Le noyau physique exact fini existe comme couche
> experimentale separee dont l'API n'est pas encore figee. Les programmes
> physiques realistes et approximatifs restent inacheves. Aucune norme
> rationnelle n'est derivee de la seule dynamique unitaire.

## English

### Purpose

This Lean 4 / Mathlib repository formalizes conditional Born results from
explicitly separated mathematical, normative, physical-bridge, and semantic
premises. It builds on the pinned
[`quantum-foundations-lean`](https://github.com/Bobart0/quantum-foundations-lean)
dependency and keeps the distinction between a conditional theorem and a
derivation of its premises explicit.

## Stable conditional API

```lean
import EverettianProbability.API.ConditionalMainResults
```

The stable aggregate theorem is `conditionalBornMainResults`; the one- and
two-step packaged results are `oneStepConditionalBornResults` and
`twoStepConditionalBornResults`. `ProjectiveBornPremises` records a finite
projective dimension `n >= 3`, rational expectation, a normalized state,
local refinement invariance, and the explicit null-support bridge.

The API proves canonical weight equals Born weight, act value equals Born
expectation, continuator credence equals conditional Born weight on a nonzero
parent fibre, and diachronic total-expectation, chain, and tower laws.
`API.ExactFinitePhysicalRichness` is present but experimental: it is outside
the stability guarantee for `v1.x`.

### Current status

| Layer | Current status |
|---|---|
| P0-P4 | Closed in their stated finite-projective scope. |
| Self-location | Finite record-conditioned credence formalism and uniqueness under explicit admissibility premises are established; personal uncertainty remains semantic. |
| Diachronic | Continuation steps, normalized continuator credence, total expectation, chain, tower, physical composition and associativity are formalized; complete personal identity is not. |
| Exact finite physical richness | Exact unitary orbit and compatible positive fine-weight-plan realization are established; natural Hamiltonians, decoherence emergence, and approximation are not. |
| P10 / P11 | Closed in their documented finite conditional scopes. |
| P9 | Partial (`q = 4` witness). |

### Repository structure

```text
EverettianProbability/
├── API/
│   ├── ConditionalBorn.lean
│   ├── DiachronicBorn.lean
│   ├── ConditionalMainResults.lean
│   └── ExactFinitePhysicalRichness.lean
├── ExactFinite/
│   ├── RecordOrbit.lean
│   ├── RefinementRealization.lean
│   └── PhysicalAdequacy.lean
├── SelfLocation/       -- record-conditioned credence and semantic bridges
├── Diachronic/         -- ContinuationStep, continuator credence, total
│                         expectation, chain, tower, physical continuation,
│                         composition, associativity, unitary orbit, and
│                         exact fine-weight-plan realization
├── Frequency/          -- finite frequency masses and typicality
├── Confirmation/       -- finite conditional Bayesian confirmation
└── Audit/              -- axiom and stable-API contracts
```

The remaining limitations and the exact conditional scope are documented in
[`docs/CONDITIONAL_BORN_SCOPE.md`](docs/CONDITIONAL_BORN_SCOPE.md). The
compatibility contract is in [`docs/API_STABILITY.md`](docs/API_STABILITY.md).

### Experimental exact-finite entry point

```lean
import EverettianProbability.ExactFinite.PhysicalAdequacy
```

This layered facade postdates `v1.0.0`, is not covered by the `v1.x` stability
guarantee, and only organizes existing exact finite results. The stable
conditional entry point remains `API.ConditionalMainResults`.

### Reproducibility and citation

```sh
lake env lean EverettianProbability/Audit/ConditionalAPIContract.lean
lake env lean EverettianProbability/Audit/MainResults.lean
lake build
bash scripts/guard.sh
```

See `CITATION.cff` for *Everettian Probability in Lean:
Refinement-Invariant Rational Expectation*, version `1.0.0`.

## Francais

### Objet

Ce depot Lean 4 / Mathlib formalise des resultats de Born conditionnels a
partir de premisses mathematiques, normatives, physiques-ponts et semantiques
explicitement separees. Il repose sur la dependance epinglee
[`quantum-foundations-lean`](https://github.com/Bobart0/quantum-foundations-lean)
et distingue toujours le theoreme conditionnel de la justification de ses
premisses.

## API conditionnelle stable

```lean
import EverettianProbability.API.ConditionalMainResults
```

Le theoreme agrege stable est `conditionalBornMainResults`; les resultats
empaquetes a une et deux etapes sont `oneStepConditionalBornResults` et
`twoStepConditionalBornResults`. `ProjectiveBornPremises` rassemble une
dimension projective finie `n >= 3`, l'esperance rationnelle, un etat
normalise, l'invariance locale sous raffinement et le pont explicite de
support nul.

L'API prouve que le poids canonique est le poids de Born, que la valeur d'un
acte est son esperance de Born, que la credence d'un continuateur est le poids
bornien conditionnel sur une fibre parentale non nulle, ainsi que les lois
diachroniques d'esperance totale, de chaine et de tour.
`API.ExactFinitePhysicalRichness` est disponible mais experimentale : elle est
hors de la garantie de stabilite `v1.x`.

### Statut courant

| Couche | Statut courant |
|---|---|
| P0-P4 | Clos dans leur portee projective finie indiquee. |
| Auto-localisation | Formalisme fini de credence conditionnee par les records et unicite sous premisses d'admissibilite explicites etablis; l'incertitude personnelle reste semantique. |
| Diachronie | Etapes de continuation, credences normalisees, esperance totale, chaine, tour, composition et associativite physiques formalisees; identite personnelle complete absente. |
| Richesse physique exacte finie | Orbite unitaire exacte et realisation de tout plan positif compatible etablies; Hamiltonien naturel, emergence par decoherence et approximation absents. |
| P10 / P11 | Clos dans leurs portees finies conditionnelles documentees. |
| P9 | Partiel (temoin `q = 4`). |

### Structure du depot

```text
EverettianProbability/
├── API/
│   ├── ConditionalBorn.lean
│   ├── DiachronicBorn.lean
│   ├── ConditionalMainResults.lean
│   └── ExactFinitePhysicalRichness.lean
├── ExactFinite/
│   ├── RecordOrbit.lean
│   ├── RefinementRealization.lean
│   └── PhysicalAdequacy.lean
├── SelfLocation/       -- credence conditionnee par les records et ponts semantiques
├── Diachronic/         -- ContinuationStep, credence envers les continuateurs,
│                         esperance totale, chaine, tour, continuations physiques,
│                         composition, associativite, orbite unitaire et realisation
│                         exacte de plans de poids fins
├── Frequency/          -- masses de frequence finies et typicalite
├── Confirmation/       -- confirmation bayesienne finie conditionnelle
└── Audit/              -- contrats d'axiomes et d'API stable
```

La portee conditionnelle exacte et les limitations sont dans
[`docs/CONDITIONAL_BORN_SCOPE.md`](docs/CONDITIONAL_BORN_SCOPE.md). Le contrat
de compatibilite est dans [`docs/API_STABILITY.md`](docs/API_STABILITY.md).

### Point d'entree exact fini experimental

```lean
import EverettianProbability.ExactFinite.PhysicalAdequacy
```

Cette facade stratifiee est posterieure a `v1.0.0`, n'est pas couverte par la
garantie de stabilite `v1.x` et organise seulement des resultats exacts finis
existants. Le point d'entree conditionnel stable reste
`API.ConditionalMainResults`.

### Reproductibilite et citation

```sh
lake env lean EverettianProbability/Audit/ConditionalAPIContract.lean
lake env lean EverettianProbability/Audit/MainResults.lean
lake build
bash scripts/guard.sh
```

Voir `CITATION.cff` pour *Everettian Probability in Lean:
Refinement-Invariant Rational Expectation*, version `1.0.0`.
