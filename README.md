# Everettian Probability in Lean

> **The conditional and exact-finite public APIs are stable in `v2.0.0`.**
> Their normative, physical, and semantic premises remain explicit. Realistic and
> approximate physical programmes remain unfinished. No rational norm is
> claimed to follow from unitary dynamics alone.
>
> **Le premier resultat formel conditionnel est clos et l'API conditionnelle
> `v2.0.0` sont stables.** Leurs prémisses normatives, physiques et sémantiques
> restent explicites. Les programmes
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

## Stable exact-finite API

```lean
import EverettianProbability.API.ExactFiniteMainResults
```

This facade exposes the exact finite physical result. The implementation
modules may evolve; users should prefer the two stable facades above.

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
│   ├── PhysicalAdequacy.lean
│   └── MainResults.lean
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
The exact-finite stage codification is in
[`docs/EXACT_FINITE_STAGES.md`](docs/EXACT_FINITE_STAGES.md): EF8 is the
audited scientific aggregation, EF9 audits contradictory scope boundaries and
the zero-parent-fibre case, and EF10 is not open.

### Experimental exact-finite entry point

```lean
import EverettianProbability.ExactFinite.MainResults
```

`MainResults` remains the scientific implementation aggregation and
`PhysicalAdequacy` its detailed facade. The stable external entry point is now
`API.ExactFiniteMainResults`; the conditional entry point remains
`API.ConditionalMainResults`.

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
│   ├── PhysicalAdequacy.lean
│   └── MainResults.lean
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
La codification des etapes exactes finies est dans
[`docs/EXACT_FINITE_STAGES.md`](docs/EXACT_FINITE_STAGES.md) : EF8 est
l'agregation scientifique auditee, EF9 audite les frontieres contradictoires
et le cas de fibre parente nulle, et EF10 n'est pas ouvert.

### Point d'entree exact fini experimental

```lean
import EverettianProbability.ExactFinite.MainResults
```

`MainResults` est l'agregation scientifique de la couche exacte finie
experimentale; `PhysicalAdequacy` demeure sa facade detaillee. Cette couche
est posterieure a `v1.0.0`, n'est pas couverte par la garantie de stabilite
`v1.x` et organise seulement des resultats exacts finis existants. Le point
d'entree conditionnel stable reste `API.ConditionalMainResults`.

### Reproductibilite et citation

```sh
lake env lean EverettianProbability/Audit/ConditionalAPIContract.lean
lake env lean EverettianProbability/Audit/MainResults.lean
lake build
bash scripts/guard.sh
```

Voir `CITATION.cff` pour *Everettian Probability in Lean:
Refinement-Invariant Rational Expectation*, version `1.0.0`.
