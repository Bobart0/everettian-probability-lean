# Changelog

## [Unreleased]
## [2.2.2-journal-audit] - 2026-08-04

### Corrigé

- Dépendance amont `quantum_foundations` repinnée vers
  `v1.3.1-journal-audit` (résolu `f773ed5694c610af055b82427da27a69d528b776`).
- La façade aval reflète désormais le résultat amont : l’indépendance complète
  de contexte découle de `AxGrain` seul, tandis que `AxNorm` reste nécessaire
  pour la normalisation probabiliste aval.

### Fixed

- Pinned upstream `quantum_foundations` to
  `v1.3.1-journal-audit` (resolved
  `f773ed5694c610af055b82427da27a69d528b776`).
- Downstream documentation now reflects that full context independence follows
  from `AxGrain` alone, while `AxNorm` remains required for downstream
  probability normalization.

## [2.2.0-journal-audit] - 2026-08-03

### Added

- Dépendance amont `quantum_foundations` mise à jour vers le tag
  `v1.3.0-journal-audit` (résolu `747d8f441b5cd7beaa579662a535366030efe322`),
  transitivement `gleason` vers `v1.1.0-journal-audit` (résolu
  `5c5bc40d2e4a31a0d1b3112fcc9a3e92b2000ec5`).
- Contre-modèle niveau décision `EverettianProbability.BornCalibration.
  decision_premises_do_not_imply_born_at_two` (`BornCalibration/
  DecisionNonCircularity.lean`) : les prémisses employées par
  `born_expectation_of_invariance` (famille d'espérance rationnelle,
  invariance locale sous raffinement, nullité physique du poids canonique)
  n'impliquent pas, à elles seules, les poids de Born en dimension 2 ;
  complète le contre-modèle niveau poids déjà existant
  (`grain_does_not_imply_born_at_two`).
- Petit lemme numérique public `witnessLine_skewWeight_ne_born`
  (`BornCalibration/NonCircularity.lean`), extrait pour être réutilisé par le
  nouveau contre-modèle sans dupliquer ni exposer la construction privée
  `skewF`.
- Audit de publication ciblé `EverettianProbability.Audit.JournalCore`
  (`#check`/`#print axioms` sur l'infrastructure de représentation, le pont
  Grain, les deux contre-modèles, les témoins de poids rivaux et l'agrégat
  d'API conditionnelle stable — sans régression).
- Corrections documentaires distinguant explicitement contre-modèle niveau
  poids et niveau décision, et précisant que le regroupement des prémisses
  dans `ProjectiveBornPremises` est un choix d'API, non une nécessité
  logique (`README.md`, `CLAIM_MATRIX.md`, `docs/CONDITIONAL_BORN_SCOPE.md`,
  `docs/SCOPE_AND_LIMITATIONS.md`).

- Upstream `quantum_foundations` dependency updated to tag
  `v1.3.0-journal-audit` (resolved
  `747d8f441b5cd7beaa579662a535366030efe322`), transitively `gleason` to
  `v1.1.0-journal-audit` (resolved
  `5c5bc40d2e4a31a0d1b3112fcc9a3e92b2000ec5`).
- Decision-level countermodel `EverettianProbability.BornCalibration.
  decision_premises_do_not_imply_born_at_two` (`BornCalibration/
  DecisionNonCircularity.lean`): the premises used by
  `born_expectation_of_invariance` (rational expectation family, local
  refinement invariance, physical null support of the canonical weight) do
  not, by themselves, imply Born weights in dimension 2; complements the
  already-existing weight-level countermodel
  (`grain_does_not_imply_born_at_two`).
- Small public numeric lemma `witnessLine_skewWeight_ne_born`
  (`BornCalibration/NonCircularity.lean`), extracted for reuse by the new
  countermodel without duplicating or exposing the private `skewF`
  construction.
- Focused publication audit `EverettianProbability.Audit.JournalCore`
  (`#check`/`#print axioms` on the representation infrastructure, the Grain
  bridge, both countermodels, the rival-weight witnesses, and the stable
  conditional API aggregate — with no regression).
- Documentation corrections explicitly distinguishing the weight-level and
  decision-level countermodels, and clarifying that bundling premises into
  `ProjectiveBornPremises` is an API design choice, not a logical necessity
  (`README.md`, `CLAIM_MATRIX.md`, `docs/CONDITIONAL_BORN_SCOPE.md`,
  `docs/SCOPE_AND_LIMITATIONS.md`).

## [2.1.0] - 2026-08-03

### Added

- Frontiere locale stable `EverettianProbability.API.UpstreamQuantumFoundations`, qui reexporte le paquet amont `QuantumFoundations.EverettianAPI` sans API locale plate.
- Contrat de compilation des API amont stables de probabilite, factorisation tensorielle, pont des selecteurs et implementation Naimark.
- Stable local import boundary `EverettianProbability.API.UpstreamQuantumFoundations`, re-exporting the upstream `QuantumFoundations.EverettianAPI` bundle without a flat local API.
- Compile-time contract for the stable upstream quantum-foundations APIs, including the probability, finite-tensor, selector-bridge, and Naimark implementation declarations.

### Further additions
- Documentation post-v2.0.0 : clarification des dépendances CORE/CALIBRATED,
  de la direction logique P10 → P11 et des statuts de release ; ajout de la
  carte bilingue des dépendances logiques. Aucun code ni aucune API n'a été
  modifié.
- Documentation post-v2.0.0: clarified CORE/CALIBRATED dependencies, the P10
  → P11 logical direction, and release statuses; added the bilingual logical
  dependency map. No code or API was modified.
- Placeholder for future compatible additions.
- Layered experimental exact-finite facade: `RecordOrbit`,
  `RefinementRealization`, and `PhysicalAdequacy`.
- Compile-time architecture contract and exact-finite layering guard.
- Aggregated exact-finite main theorem.
- Explicit separation between physical core and P4-calibrated conclusions.
- Exact-finite completeness audit.
- EF9 contradictory scope audit.
- Explicit zero-parent-fibre results.
- Permanent repository terminology guard.
- Exact-finite stage codification.
### Changed

- Dependence `quantum-foundations-lean` epinglee sur `v1.2.1-everettian-api`.
- Pinned `quantum-foundations-lean` to `v1.2.1-everettian-api`.

### Compatibility and scope

- Les signatures publiques conditionnelle et exacte-finie existantes restent inchangees.
- La frontiere amont n identifie ni `NSNC1`, ni neutralite d ancilla, ni neutralite residuelle, et ne derive aucune factorisation tensorielle preferee.
- Existing conditional and exact-finite public signatures are unchanged.
- The upstream boundary does not identify `NSNC1`, ancilla neutrality, and residual neutrality; it derives no preferred tensor factorization.
## [2.0.0] - 2026-07-30

### Added

- Stable exact-finite public API and independent API contract.
- Unitary-orbit and compatible-profile realization facade.
- Separate exact physical core and calibrated conclusions.
- Explicit zero-weight parent-fibre treatment and permanent API boundary guard.
- EF0–EF10 programme codification and contradictory scope audit.

### Compatibility

- The conditional API introduced in v1.0.0 remains unchanged; its import path
  and stable declarations remain supported.

### Scope

- Exact, finite-dimensional, and projective; calibrated credence conclusions
  require explicit P4 premises; no approximate decoherence, natural local
  Hamiltonian, or complete personal-identity semantics.

## [1.0.0] - 2026-07-29

### Added

- Stable conditional API and explicit `ProjectiveBornPremises`.
- Static Born representation; continuator credence as conditional Born weight.
- Normalized credence on nonzero fibres; diachronic total expectation; chain
  and tower laws; uniqueness for admissible credence families.
- Compile-time API contract, permanent import-boundary guard, and exact scope
  documentation.

### Verified

- `SORRY_BUDGET = 0`; no project axioms; no `native_decide`; no
  `maxHeartbeats 0`.
- Audited theorems depend at most on
  `[propext, Classical.choice, Quot.sound]`.

### Experimental

- Exact finite physical-richness API.
- Unitary record-orbit and fine-weight realization layer.

### Not included in the stable claim

- Approximate decoherence, realistic Hamiltonian generation,
  infinite-dimensional dynamics, and complete personal-identity semantics.
