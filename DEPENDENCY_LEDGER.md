# DEPENDENCY_LEDGER.md — everettian-probability-lean

## Français

Toutes les références amont passent par l'unique import
`QuantumFoundations.ProbabilityAPI`. Une ligne correspond à une déclaration
amont réellement utilisée; « structurel » signifie que la propriété est
transportée par le type reçu, sans prémisse physique supplémentaire.

| Déclaration amont utilisée | Norme hilbertienne | Orthogonalité | Décohérence | Trace | Mesure de Born | Typicalité | Rationalité |
|---|---|---|---|---|---|---|---|
| `Gleason.H` | Non | Non | Non | Non | Non | Non | Non |
| `Gleason.projL` | Oui | Non | Non | Non | Oui | Non | Non |
| `BornRule.Perspective` | Non | Structurel | Non | Non | Non | Non | Non |
| `Perspective.binary` | Non | Structurel | Non | Non | Non | Non | Non |
| `Perspective.unique_parent` | Non | Structurel | Non | Non | Non | Non | Non |
| `BornRule.Refines` | Non | Structurel | Non | Non | Non | Non | Non |
| `Refines.refl` | Non | Non | Non | Non | Non | Non | Non |
| `Refines.trans` | Non | Non | Non | Non | Non | Non | Non |
| `parentOf` | Non | Structurel | Non | Non | Non | Non | Non |
| `parentOf_mem` | Non | Structurel | Non | Non | Non | Non | Non |
| `parentOf_le` | Non | Structurel | Non | Non | Non | Non | Non |
| `parentOf_eq_of_le` | Non | Structurel | Non | Non | Non | Non | Non |
| `coarseCells` | Non | Structurel | Non | Non | Non | Non | Non |
| `mem_coarseCells_iff` | Non | Structurel | Non | Non | Non | Non | Non |
| `coarseCells_eq_fiber_parentOf` | Non | Structurel | Non | Non | Non | Non | Non |
| `axGrain_iff_coarseCells` | Selon le poids | Structurel | Non | Non | Non par définition | Non | Non |
| `refinePerspective` | Non | Structurel | Non | Non | Non | Non | Non |
| `refinePerspective_refines` | Non | Structurel | Non | Non | Non | Non | Non |
| `refine_filter_eq_cellLines` | Non | Structurel | Non | Non | Non | Non | Non |
| `cellLines` | Non | Structurel | Non | Non | Non | Non | Non |
| `cellLines_le` | Non | Structurel | Non | Non | Non | Non | Non |
| `cellLines_ne_bot` | Non | Structurel | Non | Non | Non | Non | Non |
| `cellLines_injective` | Non | Structurel | Non | Non | Non | Non | Non |
| `line_ne_bot` | Non | Non | Non | Non | Non | Non | Non |
| `line_ne_top` | Non | Non | Non | Non | Non | Non | Non |
| `AxGrain` | Selon le poids | Structurel | Non | Non | Non par définition | Non | Norme d'invariance lorsqu'assumée |
| `AxNorm` | Non | Non | Non | Non | Non | Non | Normalisation |
| `AxPos` | Non | Non | Non | Non | Non | Non | Positivité |
| `AxNul` | Selon l'état | Non | Non | Non | Non | Non | Nullité |
| `grainCoherenceTheorem_projector` | Oui | Oui | Non | Non | Oui, conclusion | Non | Non |
| `ProbabilityAPI.BornRule.E₀` | Oui | Non | Non | Non | Oui, définition | Non | Non |
| `ProbabilityAPI.BornRule.E₀_isGrain` | Oui | Structurel | Non | Non | Oui | Non | Non |
| `ProbabilityAPI.BornRule.E₀_satisfies_axioms` | Oui | Structurel | Non | Non | Oui | Non | Non |
| `EffectPerspectives.EffectPerspective` | Non | Non | Non | Non | Non | Non | Non |
| `EffectPerspectives.Refines` | Non | Structurel | Non | Non | Non | Non | Non |
| `EffectPerspectives.Refines.parent` | Non | Structurel | Non | Non | Non | Non | Non |
| `EffectPerspectives.Refines.refl` | Non | Non | Non | Non | Non | Non | Non |
| `EffectPerspectives.Refines.trans` | Non | Non | Non | Non | Non | Non | Non |
| `EffectPerspectives.EstimationRule` | Non | Structurel | Non | Non | Non | Non | Structurel |
| `EffectPerspectives.EstimationRule.weight` | Non | Non | Non | Non | Non | Non | Structurel |
| `EffectPerspectives.EstimationRule.grain` | Selon le poids | Structurel | Non | Non | Non par définition | Non | Cohérence d'estimation |
| `ProbabilityAPI.EffectPerspectives.pureStateEstimationRule` | Oui | Non | Non | Non | Oui, témoin | Non | Non |

`RestrictedRecordSectors` n'est ni importé ni utilisé. La prémisse
`RefinementInvariantLocal` est normative; elle n'est dérivée d'aucune dynamique,
décohérence, typicalité ou hypothèse de saturation physique.

## English

Every upstream reference passes through the sole import
`QuantumFoundations.ProbabilityAPI`. Each row names one upstream declaration
actually used; “structural” means that the property is carried by the input
type, without an additional physical premise.

| Used upstream declaration | Hilbert norm | Orthogonality | Decoherence | Trace | Born measure | Typicality | Rationality |
|---|---|---|---|---|---|---|---|
| `Gleason.H` | No | No | No | No | No | No | No |
| `Gleason.projL` | Yes | No | No | No | Yes | No | No |
| `BornRule.Perspective` | No | Structural | No | No | No | No | No |
| `Perspective.binary` | No | Structural | No | No | No | No | No |
| `Perspective.unique_parent` | No | Structural | No | No | No | No | No |
| `BornRule.Refines` | No | Structural | No | No | No | No | No |
| `Refines.refl` | No | No | No | No | No | No | No |
| `Refines.trans` | No | No | No | No | No | No | No |
| `parentOf` | No | Structural | No | No | No | No | No |
| `parentOf_mem` | No | Structural | No | No | No | No | No |
| `parentOf_le` | No | Structural | No | No | No | No | No |
| `parentOf_eq_of_le` | No | Structural | No | No | No | No | No |
| `coarseCells` | No | Structural | No | No | No | No | No |
| `mem_coarseCells_iff` | No | Structural | No | No | No | No | No |
| `coarseCells_eq_fiber_parentOf` | No | Structural | No | No | No | No | No |
| `axGrain_iff_coarseCells` | Depends on weight | Structural | No | No | Not by definition | No | No |
| `refinePerspective` | No | Structural | No | No | No | No | No |
| `refinePerspective_refines` | No | Structural | No | No | No | No | No |
| `refine_filter_eq_cellLines` | No | Structural | No | No | No | No | No |
| `cellLines` | No | Structural | No | No | No | No | No |
| `cellLines_le` | No | Structural | No | No | No | No | No |
| `cellLines_ne_bot` | No | Structural | No | No | No | No | No |
| `cellLines_injective` | No | Structural | No | No | No | No | No |
| `line_ne_bot` | No | No | No | No | No | No | No |
| `line_ne_top` | No | No | No | No | No | No | No |
| `AxGrain` | Depends on weight | Structural | No | No | Not by definition | No | Invariance norm when assumed |
| `AxNorm` | No | No | No | No | No | No | Normalization |
| `AxPos` | No | No | No | No | No | No | Positivity |
| `AxNul` | Depends on state | No | No | No | No | No | Nullity |
| `grainCoherenceTheorem_projector` | Yes | Yes | No | No | Yes, conclusion | No | No |
| `ProbabilityAPI.BornRule.E₀` | Yes | No | No | No | Yes, definition | No | No |
| `ProbabilityAPI.BornRule.E₀_isGrain` | Yes | Structural | No | No | Yes | No | No |
| `ProbabilityAPI.BornRule.E₀_satisfies_axioms` | Yes | Structural | No | No | Yes | No | No |
| `EffectPerspectives.EffectPerspective` | No | No | No | No | No | No | No |
| `EffectPerspectives.Refines` | No | Structural | No | No | No | No | No |
| `EffectPerspectives.Refines.parent` | No | Structural | No | No | No | No | No |
| `EffectPerspectives.Refines.refl` | No | No | No | No | No | No | No |
| `EffectPerspectives.Refines.trans` | No | No | No | No | No | No | No |
| `EffectPerspectives.EstimationRule` | No | Structural | No | No | No | No | Structural |
| `EffectPerspectives.EstimationRule.weight` | No | No | No | No | No | No | Structural |
| `EffectPerspectives.EstimationRule.grain` | Depends on weight | Structural | No | No | Not by definition | No | Estimation coherence |
| `ProbabilityAPI.EffectPerspectives.pureStateEstimationRule` | Yes | No | No | No | Yes, witness | No | No |

`RestrictedRecordSectors` is neither imported nor used. The
`RefinementInvariantLocal` premise is normative; it is not derived from dynamics,
decoherence, typicality, or a physical saturation assumption.
