# Everettian Probability in Lean

> **The conditional and exact-finite public APIs are stable in `v2.0.0`.**
> Their normative, physical, and semantic premises remain explicit. Realistic
> and approximate physical programmes remain outside this repository. No
> rational norm is claimed to follow from unitary dynamics alone.
>
> **Les API publiques conditionnelle et exacte finie sont stables en `v2.0.0`.**
> Leurs prémisses normatives, physiques et sémantiques restent explicites. Les
> programmes physiques réalistes et approximatifs restent extérieurs à ce
> dépôt. Aucune norme rationnelle n'est dérivée de la seule dynamique unitaire.

## English

### Purpose

This Lean 4 / Mathlib repository formalizes conditional Born results from
explicitly separated mathematical, normative, physical-bridge, and semantic
premises. It builds on the pinned
[`quantum-foundations-lean`](https://github.com/Bobart0/quantum-foundations-lean)
dependency and keeps the distinction between a conditional theorem and a
derivation of its premises explicit.

The upstream dependency is pinned to `v1.2.1-everettian-api`.
`EverettianProbability.API.UpstreamQuantumFoundations` is the local import
boundary for its stable Everettian-facing bundle. It does not identify `NSNC1`,
ancilla neutrality, and residual neutrality, and no preferred tensor
factorization is derived.
### Stable public APIs

```lean
import EverettianProbability.API.ConditionalMainResults
import EverettianProbability.API.ExactFiniteMainResults
```

`ConditionalMainResults` is the stable conditional-Born facade. Its aggregate
theorem is `conditionalBornMainResults`; it packages canonical Born weights,
Born expectations, conditional Born credence on nonzero parent fibres, and the
conditional diachronic laws.

`ExactFiniteMainResults` is the stable exact-finite facade since v2.0.0. The
older `API.ExactFinitePhysicalRichness` facade remains available for existing
users but is not the recommended entry point. Implementation modules are not
the stable contract.

### Logical direction

Calibration premises, including `3 ≤ n`, local refinement invariance, a
normalized state, and the `AxNul` bridge, identify Born in the main projective
route. A `CompatibleFineWeights` hypothesis already assumes that each future
fibre sums to the present Born record; from it, the exact-finite CORE realizes
the compatible profile. CORE plus the explicit calibration premises gives the
CALIBRATED credence conclusions. Calibrated weights determine P10 frequency
masses; P10 masses serve as likelihoods in P11.

“One measure” therefore means downstream propagation of a measure identified
upstream, not several independent derivations of Born. See
[`docs/LOGICAL_DEPENDENCY_MAP.md`](docs/LOGICAL_DEPENDENCY_MAP.md).

### Current status

| Layer | Current status |
|---|---|
| P0–P4 | Closed in their stated finite-projective, explicitly conditional scope. |
| Qubit/effect route | Closed for `n ≥ 1` when outcomes have orthogonal-projector effects; genuinely non-projective POVM effects are not covered. |
| Exact-finite CORE | Conditional exact realization from `CompatibleFineWeights`; it is not an independent Born derivation. |
| Exact-finite CALIBRATED | Closed under explicit calibration premises, including `3 ≤ n`. |
| P10 / P11 | Closed in their documented finite conditional scopes; P10 is downstream of calibrated weights and P11 is downstream of P10 masses. |
| P9 | Partial (`q = 4` witness). |
| EF10 | **EF10 RELEASED / PUBLIÉ** — stable exact-finite API frozen in v2.0.0. |
| Non-circularity countermodels (`n = 2`) | Closed. Weight-level (`grain_does_not_imply_born_at_two`, `BornCalibration/NonCircularity.lean`) and decision-level (`decision_premises_do_not_imply_born_at_two`, `BornCalibration/DecisionNonCircularity.lean`) countermodels; each shows `3 ≤ n` in `born_expectation_of_invariance` is indispensable, not a convenience clause. |

### Repository structure

```text
EverettianProbability/
├── API/
│   ├── ConditionalMainResults.lean
│   ├── ExactFiniteMainResults.lean
│   └── ExactFinitePhysicalRichness.lean   # legacy, not recommended
├── ExactFinite/                            # implementation modules
├── Frequency/                              # finite frequency masses and typicality
├── Confirmation/                           # finite conditional Bayesian confirmation
└── Audit/                                  # axiom and stable-API contracts
```

The exact scope and limitations are in
[`docs/CONDITIONAL_BORN_SCOPE.md`](docs/CONDITIONAL_BORN_SCOPE.md) and
[`docs/SCOPE_AND_LIMITATIONS.md`](docs/SCOPE_AND_LIMITATIONS.md). Stable API
contracts are described in [`docs/API_STABILITY.md`](docs/API_STABILITY.md) and
[`docs/EXACT_FINITE_API_STABILITY.md`](docs/EXACT_FINITE_API_STABILITY.md).

### Reproducibility and citation

```sh
lake env lean EverettianProbability/Audit/ConditionalAPIContract.lean
lake env lean EverettianProbability/Audit/ExactFiniteAPIContract.lean
lake env lean EverettianProbability/Audit/MainResults.lean
lake build
bash scripts/guard.sh
```

See `CITATION.cff` for *Everettian Probability in Lean:
Refinement-Invariant Rational Expectation*, version `2.0.0`.

## Français

### Objet

Ce dépôt Lean 4 / Mathlib formalise des résultats conditionnels de Born à
partir de prémisses mathématiques, normatives, de pont physique et sémantiques
explicitement séparées. Il s'appuie sur la dépendance épinglée
[`quantum-foundations-lean`](https://github.com/Bobart0/quantum-foundations-lean)
et conserve la distinction entre un théorème conditionnel et une dérivation de
ses prémisses.

La dépendance amont est épinglée sur `v1.2.1-everettian-api`.
`EverettianProbability.API.UpstreamQuantumFoundations` est la frontière d'import
locale pour son ensemble stable orienté Everett. Elle n'identifie ni `NSNC1`,
ni la neutralité d'ancilla, ni la neutralité résiduelle, et aucune
factorisation tensorielle préférée n'est dérivée.
### API publiques stables

```lean
import EverettianProbability.API.ConditionalMainResults
import EverettianProbability.API.ExactFiniteMainResults
```

`ConditionalMainResults` est la façade stable du résultat conditionnel de
Born. Son théorème agrégé est `conditionalBornMainResults` : il regroupe les
poids de Born canoniques, les espérances de Born, la crédence bornienne
conditionnelle sur les fibres parentes non nulles et les lois diachroniques
conditionnelles.

`ExactFiniteMainResults` est la façade exacte finie stable depuis v2.0.0.
L'ancienne façade `API.ExactFinitePhysicalRichness` reste disponible pour les
utilisateurs existants, mais n'est pas le point d'entrée recommandé. Les
modules d'implémentation ne constituent pas le contrat stable.

### Direction logique

Les prémisses de calibration — notamment `3 ≤ n`, l'invariance locale sous
raffinement, un état normalisé et le pont `AxNul` — identifient Born dans la
route projective principale. Une hypothèse `CompatibleFineWeights` suppose déjà
que chaque fibre future somme au record bornien présent ; le CORE exact fini
réalise alors ce profil compatible. CORE plus les prémisses explicites de
calibration donne les conclusions de crédence CALIBRATED. Les poids calibrés
déterminent les masses de fréquence P10 ; les masses P10 servent de
vraisemblances dans P11.

« Une même mesure » signifie donc la propagation aval d'une mesure identifiée
en amont, et non plusieurs dérivations indépendantes de Born. Voir
[`docs/LOGICAL_DEPENDENCY_MAP.md`](docs/LOGICAL_DEPENDENCY_MAP.md).

### Statut courant

| Couche | Statut courant |
|---|---|
| P0–P4 | Clos dans leur portée projective finie et explicitement conditionnelle. |
| Route qubit/effets | Close pour `n ≥ 1` lorsque les sorties ont des effets projecteurs orthogonaux ; les effets POVM authentiquement non projectifs ne sont pas couverts. |
| CORE exact fini | Réalisation exacte conditionnelle à `CompatibleFineWeights` ; ce n'est pas une dérivation indépendante de Born. |
| CALIBRATED exact fini | Clos sous prémisses explicites de calibration, y compris `3 ≤ n`. |
| P10 / P11 | Clos dans leurs portées finies conditionnelles documentées ; P10 est aval des poids calibrés et P11 aval des masses P10. |
| P9 | Partiel (témoin `q = 4`). |
| EF10 | **EF10 RELEASED / PUBLIÉ** — API exacte finie stable figée dans v2.0.0. |
| Contre-modèles de non-circularité (`n = 2`) | Clos. Niveau poids (`grain_does_not_imply_born_at_two`, `BornCalibration/NonCircularity.lean`) et niveau décision (`decision_premises_do_not_imply_born_at_two`, `BornCalibration/DecisionNonCircularity.lean`) ; chacun montre que `3 ≤ n` dans `born_expectation_of_invariance` est indispensable, pas une clause de confort. |

### Structure du dépôt

```text
EverettianProbability/
├── API/
│   ├── ConditionalMainResults.lean
│   ├── ExactFiniteMainResults.lean
│   └── ExactFinitePhysicalRichness.lean   # ancienne façade, non recommandée
├── ExactFinite/                            # modules d'implémentation
├── Frequency/                              # masses de fréquence finies et typicalité
├── Confirmation/                           # confirmation bayésienne finie conditionnelle
└── Audit/                                  # contrats d'axiomes et d'API stables
```

La portée exacte et les limitations sont dans
[`docs/CONDITIONAL_BORN_SCOPE.md`](docs/CONDITIONAL_BORN_SCOPE.md) et
[`docs/SCOPE_AND_LIMITATIONS.md`](docs/SCOPE_AND_LIMITATIONS.md). Les contrats
d'API stables sont décrits dans [`docs/API_STABILITY.md`](docs/API_STABILITY.md)
et [`docs/EXACT_FINITE_API_STABILITY.md`](docs/EXACT_FINITE_API_STABILITY.md).

### Reproductibilité et citation

```sh
lake env lean EverettianProbability/Audit/ConditionalAPIContract.lean
lake env lean EverettianProbability/Audit/ExactFiniteAPIContract.lean
lake env lean EverettianProbability/Audit/MainResults.lean
lake build
bash scripts/guard.sh
```

Voir `CITATION.cff` pour *Everettian Probability in Lean:
Refinement-Invariant Rational Expectation*, version `2.0.0`.
