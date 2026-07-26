# DEPENDENCY_LEDGER.md — everettian-probability-lean

## Français

Toutes les déclarations amont réellement référencées par le code aval passent
par l'unique import `QuantumFoundations.ProbabilityAPI`. « Structurel » signifie
que la propriété est enfermée dans une structure amont reçue en argument, sans
être utilisée comme prémisse physique par la preuve aval.

| Déclaration amont utilisée | Norme hilbertienne | Orthogonalité | Décohérence | Trace | Mesure de Born | Typicalité | Rationalité |
|---|---|---|---|---|---|---|---|
| `Gleason.H` | Non | Non | Non | Non | Non | Non | Non |
| `Gleason.projL` | Oui | Non | Non | Non | Oui, uniquement dans les conclusions et témoins | Non | Non |
| `BornRule.Perspective` | Non | Structurel | Non | Non | Non | Non | Non |
| `Perspective.binary` | Non | Structurel | Non | Non | Non | Non | Non |
| `BornRule.Refines` | Non | Structurel | Non | Non | Non | Non | Non |
| `Refines.refl` | Non | Non | Non | Non | Non | Non | Non |
| `Refines.trans` | Non | Non | Non | Non | Non | Non | Non |
| `parentOf` | Non | Structurel | Non | Non | Non | Non | Non |
| `parentOf_mem` | Non | Structurel | Non | Non | Non | Non | Non |
| `parentOf_le` | Non | Non | Non | Non | Non | Non | Non |
| `parentOf_eq_of_le` | Non | Structurel | Non | Non | Non | Non | Non |
| `coarseCells` | Non | Non | Non | Non | Non | Non | Non |
| `coarseCells_eq_fiber_parentOf` | Non | Structurel | Non | Non | Non | Non | Non |
| `refinePerspective` | Non | Structurel | Non | Non | Non | Non | Non |
| `refinePerspective_refines` | Non | Structurel | Non | Non | Non | Non | Non |
| `line_ne_bot`, `line_ne_top` | Non | Non | Non | Non | Non | Non | Non |
| `AxGrain`, `AxNorm`, `AxPos`, `AxNul` | Selon l'estimateur | Structurel | Non | Non | Non par définition | Non | Non |
| `grainCoherenceTheorem_projector` | Oui | Oui | Non | Non | Oui, en conclusion seulement | Non | Non |

La prémisse `Refinement.PayoffPreserving` est normative et relève de la
rationalité. Le témoin fort bornien n'a pas été ajouté : le faire sans le
réexport amont indiqué dans `MILESTONES.md` introduirait soit une dépendance
hors façade, soit une duplication de preuve.

## English

Every upstream declaration actually referenced by downstream code passes
through the single `QuantumFoundations.ProbabilityAPI` import. “Structural”
means that the property is packaged in an upstream structure received as an
argument, rather than used as a physical premise by the downstream proof.

| Used upstream declaration | Hilbert norm | Orthogonality | Decoherence | Trace | Born measure | Typicality | Rationality |
|---|---|---|---|---|---|---|---|
| `Gleason.H` | No | No | No | No | No | No | No |
| `Gleason.projL` | Yes | No | No | No | Yes, only in conclusions and witnesses | No | No |
| `BornRule.Perspective` | No | Structural | No | No | No | No | No |
| `Perspective.binary` | No | Structural | No | No | No | No | No |
| `BornRule.Refines` | No | Structural | No | No | No | No | No |
| `Refines.refl` | No | No | No | No | No | No | No |
| `Refines.trans` | No | No | No | No | No | No | No |
| `parentOf` | No | Structural | No | No | No | No | No |
| `parentOf_mem` | No | Structural | No | No | No | No | No |
| `parentOf_le` | No | No | No | No | No | No | No |
| `parentOf_eq_of_le` | No | Structural | No | No | No | No | No |
| `coarseCells` | No | No | No | No | No | No | No |
| `coarseCells_eq_fiber_parentOf` | No | Structural | No | No | No | No | No |
| `refinePerspective` | No | Structural | No | No | No | No | No |
| `refinePerspective_refines` | No | Structural | No | No | No | No | No |
| `line_ne_bot`, `line_ne_top` | No | No | No | No | No | No | No |
| `AxGrain`, `AxNorm`, `AxPos`, `AxNul` | Depends on estimator | Structural | No | No | Not by definition | No | No |
| `grainCoherenceTheorem_projector` | Yes | Yes | No | No | Yes, in the conclusion only | No | No |

The `Refinement.PayoffPreserving` premise is normative and belongs in the
rationality column. The strong Born witness was not added: doing so without
the upstream re-export recorded in `MILESTONES.md` would introduce either an
off-facade dependency or a duplicated proof.
