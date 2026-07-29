# Audit de complétude du résultat physique exact fini
# Completeness Audit of the Exact Finite Physical Result

## Français

### CORE — établi sans calibration P4

| Élément | Statut | Résultat public |
|---|---|---|
| Compatibilité positive fibre par fibre | **ÉTABLI** | `CompatibleFineWeights` |
| Construction exacte de l’état cible | **ÉTABLI** | `canonicalTargetState` |
| Même record de Born présent | **ÉTABLI** | `canonicalTargetState_sameRecord`, `ExactFiniteCoreResults.target_same_record` |
| Égalité des normes | **ÉTABLI** | `canonicalTargetState_norm_eq`, `ExactFiniteCoreResults.target_norm_eq` |
| Réalisation exacte de chaque poids futur prescrit | **ÉTABLI** | `PhysicalRealization.realizes_futureWeights` |
| Réalisation unitaire globale | **ÉTABLI** | `exists_recordUnitary_realizing_plan`, `exactPhysicalAdequacy` |
| Commutation avec les projecteurs présents | **ÉTABLI** | `ExactFiniteCoreResults.unitary_commutes` |
| Conservation uniforme du record présent | **ÉTABLI** | `PhysicalRealization.preserves_presentRecord`, `ExactFiniteCoreResults.preserves_present_record` |
| Préservation des conséquences de Born présentes | **ÉTABLI** | `PhysicalRealization.bornExpectation_pullback_eq`, `ExactFiniteCoreResults.born_expectation_pullback` |
| Ratio conditionnel physique exact | **ÉTABLI** | `PhysicalRealization.physicalRatio_eq_prescribedRatio`, `ExactFiniteCoreResults.physical_ratio_is_prescribed` |

### CALIBRATED — établi sous prémisses explicites

| Prémisse ou conclusion | Statut | Résultat public |
|---|---|---|
| `3 ≤ n` | Prémisse explicite | `ExactFiniteCalibrationPremises.dim_ge_three` |
| Famille d’espérance rationnelle | Prémisse explicite | `ExactFiniteCalibrationPremises.F` |
| Invariance locale sous raffinement | Prémisse explicite | `ExactFiniteCalibrationPremises.refinement_invariant` |
| État source normalisé | Prémisse explicite | `ExactFiniteCalibrationPremises.source_normalized` |
| `AxNul` sur l’état cible | Prémisse explicite | `ExactFiniteCalibrationPremises.target_null_support` |
| Poids de Born parent non nul | Prémisse explicite | `hc` de `ExactFiniteCalibratedResults` |
| Crédence du continuateur = ratio prescrit | **ÉTABLI CONDITIONNELLEMENT** | `ExactFiniteCalibratedResults.continuator_credence_is_prescribed` |
| Normalisation de la fibre | **ÉTABLI CONDITIONNELLEMENT** | `ExactFiniteCalibratedResults.continuator_credence_normalized` |
| Reconstruction du poids fin | **ÉTABLI CONDITIONNELLEMENT** | `ExactFiniteCalibratedResults.parent_weight_recovers_fine_weight` |

### Hors de la revendication exacte finie

Non établis : émergence du raffinement par décohérence, conservation
approximative du record, robustesse aux perturbations, Hamiltonien local
naturel, localité ou complexité bornée de l’unitaire, unicité ou canonicité
physique de l’unitaire, détermination physique des phases, extension
infinidimensionnelle, POVM arbitraires, dérivation de l’identité sémantique
des continuateurs, dérivation de la rationalité depuis la dynamique, identité
personnelle complète et accessibilité expérimentale.

**Le deuxième Saint-Graal est clos uniquement dans sa portée exacte, finie,
projective et explicitement calibrée.** Cette clôture ne vaut pas pour un
modèle physiquement réaliste ou approximatif. `ExactFinite` reste
expérimental et la façade conditionnelle `v1.x` reste inchangée.

## English

### CORE — established without P4 calibration

| Item | Status | Public result |
|---|---|---|
| Positive fibrewise compatibility | **ESTABLISHED** | `CompatibleFineWeights` |
| Exact target-state construction | **ESTABLISHED** | `canonicalTargetState` |
| Same present Born record | **ESTABLISHED** | `canonicalTargetState_sameRecord`, `ExactFiniteCoreResults.target_same_record` |
| Equality of norms | **ESTABLISHED** | `canonicalTargetState_norm_eq`, `ExactFiniteCoreResults.target_norm_eq` |
| Exact realization of every prescribed future weight | **ESTABLISHED** | `PhysicalRealization.realizes_futureWeights` |
| Global unitary realization | **ESTABLISHED** | `exists_recordUnitary_realizing_plan`, `exactPhysicalAdequacy` |
| Commutation with all present projectors | **ESTABLISHED** | `ExactFiniteCoreResults.unitary_commutes` |
| Uniform preservation of the present record | **ESTABLISHED** | `PhysicalRealization.preserves_presentRecord`, `ExactFiniteCoreResults.preserves_present_record` |
| Preservation of present Born consequences | **ESTABLISHED** | `PhysicalRealization.bornExpectation_pullback_eq`, `ExactFiniteCoreResults.born_expectation_pullback` |
| Exact physical conditional ratio | **ESTABLISHED** | `PhysicalRealization.physicalRatio_eq_prescribedRatio`, `ExactFiniteCoreResults.physical_ratio_is_prescribed` |

### CALIBRATED — established under explicit premises

| Premise or conclusion | Status | Public result |
|---|---|---|
| `3 ≤ n` | Explicit premise | `ExactFiniteCalibrationPremises.dim_ge_three` |
| Rational expectation family | Explicit premise | `ExactFiniteCalibrationPremises.F` |
| Local refinement invariance | Explicit premise | `ExactFiniteCalibrationPremises.refinement_invariant` |
| Normalized source | Explicit premise | `ExactFiniteCalibrationPremises.source_normalized` |
| `AxNul` at the target | Explicit premise | `ExactFiniteCalibrationPremises.target_null_support` |
| Nonzero parent Born weight | Explicit premise | `hc` of `ExactFiniteCalibratedResults` |
| Continuator credence equals prescribed ratio | **ESTABLISHED CONDITIONALLY** | `ExactFiniteCalibratedResults.continuator_credence_is_prescribed` |
| Fibre normalization | **ESTABLISHED CONDITIONALLY** | `ExactFiniteCalibratedResults.continuator_credence_normalized` |
| Fine-weight reconstruction | **ESTABLISHED CONDITIONALLY** | `ExactFiniteCalibratedResults.parent_weight_recovers_fine_weight` |

### Outside the exact-finite claim

Not established: emergence of refinement through decoherence, approximate
record preservation, robustness under perturbations, a natural local
Hamiltonian, locality or bounded complexity of the unitary, uniqueness or
physical canonicity of the unitary, physical determination of phases,
infinite-dimensional extension, arbitrary POVMs, derivation of semantic
continuator identity, derivation of rationality from dynamics, complete
personal identity, and experimental accessibility.

**The second Saint-Graal is closed only in its exact, finite, projective, and
explicitly calibrated scope.** This closure does not apply to a physically
realistic or approximate model. `ExactFinite` remains experimental and the
conditional `v1.x` facade remains unchanged.
