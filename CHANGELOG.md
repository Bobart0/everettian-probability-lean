# Changelog

## [Unreleased]

## [2.4.0-journal-audit] - 2026-08-26

### Ajouté

- Campagne L0 de nécessité relative au niveau poids : `W0` audite la borne de
  dimension et `W1`--`W5` fournissent des témoins de suppression typés pour
  chacune des prémisses séparément exposées par le théorème public de
  calibration de Born.
- Tests décisionnels `D1`--`D3`, obtenus via `expectationFamilyOfWeight`, qui
  portent la suppression de prémisses à l'interface publique
  `RationalExpectationFamily`.
- Audit L2 de la frontière Uhlhorn en dimension deux :
  `dimensionTwo_orthogonality_not_injective` fournit une application
  préservant l'orthogonalité dans un sens mais non injective.
- Deux résultats L3 de minimalité de formulation : réduction de `AxNorm` à la
  perspective singleton-top sous Grain, et réduction de la normalisation des
  constantes d'une valuation affine brute aux constantes `0` et `1`.
- `Audit/JournalCore.lean` étendu à l'ensemble publication-facing L0/L2/L3 ;
  la CI échoue désormais si cet audit consolidé rapporte `sorryAx`.
- Les dépendances amont restent inchangées : Quantum Foundations
  `v1.3.1-journal-audit` à `f773ed5694c610af055b82427da27a69d528b776`,
  transitivement Gleason `v1.1.0-journal-audit` à
  `5c5bc40d2e4a31a0d1b3112fcc9a3e92b2000ec5`.

### Added

- L0 relative-necessity campaign at the weight interface: `W0` audits the
  dimension boundary and `W1`--`W5` provide typed deletion witnesses for each
  separately exposed premise of the public Born-calibration theorem.
- Decision-level tests `D1`--`D3`, via `expectationFamilyOfWeight`, lifting
  premise deletion to the public `RationalExpectationFamily` interface.
- L2 dimension-two Uhlhorn boundary audit:
  `dimensionTwo_orthogonality_not_injective` gives a one-way
  orthogonality-preserving map that is not injective.
- Two L3 formulation-minimality results: reduction of `AxNorm` to the
  singleton-top perspective under Grain, and reduction of full constant
  normalization for a raw affine valuation to constants `0` and `1`.
- `Audit/JournalCore.lean` extended to the publication-facing L0/L2/L3
  declarations; CI now fails if the consolidated journal audit reports
  `sorryAx`.
- Upstream pins are unchanged: Quantum Foundations `v1.3.1-journal-audit` at
  `f773ed5694c610af055b82427da27a69d528b776`, transitively Gleason
  `v1.1.0-journal-audit` at `5c5bc40d2e4a31a0d1b3112fcc9a3e92b2000ec5`.

## [2.3.0-journal-audit] - 2026-08-06

### Ajouté

- Contre-modèle niveau mesure-de-projection `EverettianProbability.
  BornCalibration.skewProjMeasure_not_representable` et sa forme
  existentielle `exists_nonrepresentable_projMeasure_two`
  (`BornCalibration/NonCircularity.lean`) : `skewProjMeasure`, une
  `Gleason.ProjMeasure 2` construite à partir de `skewWeight witnessState`,
  n'est représentable par aucun opérateur densité au sens de
  `Gleason.bornValue`. Preuve par annihilation locale du noyau (schéma
  rescalé, sans `3 ≤ n`), épinglage via
  `QuantumFoundations.BornRule.eq_projL_of_vanishes_on_orthogonal`
  (utilisable en dimension 2) et contradiction rationnelle exacte sur
  `witnessLine` (`81/337 ≠ 9/25`, via `witnessLine_skewWeight_ne_born` et
  `witness_x`). Complète les contre-modèles niveau poids
  (`grain_does_not_imply_born_at_two`) et niveau décision
  (`decision_premises_do_not_imply_born_at_two`) déjà existants par un
  troisième témoin, niveau mesure. Ce résultat est un témoin ponctuel : il
  n'affirme pas qu'aucune mesure projective en dimension 2 n'est
  représentable.
- Audits de publication `Audit/JournalCore.lean` et `Audit/MainResults.lean`
  étendus (`#check`/`#print axioms`) au nouveau contre-modèle niveau mesure,
  sans régression sur la base de confiance existante
  (`[propext, Classical.choice, Quot.sound]`).
- Documentation (`README.md`, `CLAIM_MATRIX.md`,
  `docs/SCOPE_AND_LIMITATIONS.md`) mise à jour pour distinguer les trois
  niveaux de contre-modèle (poids, décision, mesure-de-projection).

### Added

- Projection-measure-level countermodel `EverettianProbability.
  BornCalibration.skewProjMeasure_not_representable` and its existential
  form `exists_nonrepresentable_projMeasure_two`
  (`BornCalibration/NonCircularity.lean`): `skewProjMeasure`, a
  `Gleason.ProjMeasure 2` built from `skewWeight witnessState`, is
  representable by no density operator in the sense of
  `Gleason.bornValue`. Proved via local kernel annihilation (a rescaling
  argument, without `3 ≤ n`), pinning through
  `QuantumFoundations.BornRule.eq_projL_of_vanishes_on_orthogonal` (usable
  at dimension 2), and an exact rational contradiction on `witnessLine`
  (`81/337 ≠ 9/25`, via `witnessLine_skewWeight_ne_born` and `witness_x`).
  Completes the already-existing weight-level
  (`grain_does_not_imply_born_at_two`) and decision-level
  (`decision_premises_do_not_imply_born_at_two`) countermodels with a
  third, measure-level witness. This result is a pointwise witness: it
  does not claim that no projective measure in dimension 2 is
  representable.
- Publication audits `Audit/JournalCore.lean` and `Audit/MainResults.lean`
  extended (`#check`/`#print axioms`) to cover the new measure-level
  countermodel, with no regression to the existing trust base
  (`[propext, Classical.choice, Quot.sound]`).
- Documentation (`README.md`, `CLAIM_MATRIX.md`,
  `docs/SCOPE_AND_LIMITATIONS.md`) updated to distinguish the three
  countermodel levels (weight, decision, projection-measure).

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
