# Changelog

## [Unreleased]

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
