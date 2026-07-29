# Étapes du programme exact fini
# Exact-Finite Programme Stages

## Français

Ces codes décrivent l'avancement de la couche exacte finie. Ils ne remplacent
pas automatiquement les anciens codes globaux P0–P12.

| Code | Contenu | Statut après EF9 |
|---|---|---|
| EF0 | Définition de la portée exacte finie et architecture | AUDITÉ |
| EF1 | Record bornien, projecteurs et invariance du record | AUDITÉ |
| EF2 | Données cellule par cellule et unitaires locaux | AUDITÉ |
| EF3 | Assemblage bloc-diagonal et orbite unitaire globale | AUDITÉ |
| EF4 | État cible et réalisation des profils fins compatibles | AUDITÉ |
| EF5 | Continuations physiques, ratios et calibration | AUDITÉ |
| EF6 | Première API publique de richesse physique exacte | AUDITÉ |
| EF7 | Façade stratifiée `RecordOrbit → RefinementRealization → PhysicalAdequacy` | AUDITÉ |
| EF8 | Agrégation `MainResults` et audit de complétude | AUDITÉ |
| EF9 | Audit contradictoire et durcissement des frontières | AUDITÉ |
| EF10 | Gel éventuel de l’API exact-fini et publication | NON OUVERT |

Correspondance minimale des étapes :

- EF3 : `Diachronic/UnitaryRecordOrbit.lean`
- EF4 : `Diachronic/FineBornWeightRealization.lean`
- EF5 : `Diachronic/PhysicalFinePlanContinuation.lean`
- EF6 : `API/ExactFinitePhysicalRichness.lean`
- EF7 : `ExactFinite/RecordOrbit.lean`,
  `ExactFinite/RefinementRealization.lean`,
  `ExactFinite/PhysicalAdequacy.lean`
- EF8 : `ExactFinite/MainResults.lean`,
  `docs/EXACT_FINITE_COMPLETENESS_AUDIT.md`
- EF9 : `Audit/ExactFiniteContradictoryAudit.lean`,
  `docs/EXACT_FINITE_CONTRADICTORY_AUDIT.md`

## English

These codes describe progress in the exact-finite layer. They do not
automatically replace the older global P0–P12 codes.

| Code | Content | Status after EF9 |
|---|---|---|
| EF0 | Definition of the exact-finite scope and architecture | AUDITED |
| EF1 | Born record, projectors, and record invariance | AUDITED |
| EF2 | Cellwise data and local unitaries | AUDITED |
| EF3 | Block-diagonal assembly and global unitary orbit | AUDITED |
| EF4 | Target state and realization of compatible fine profiles | AUDITED |
| EF5 | Physical continuations, ratios, and calibration | AUDITED |
| EF6 | First public exact physical-richness API | AUDITED |
| EF7 | Layered `RecordOrbit → RefinementRealization → PhysicalAdequacy` facade | AUDITED |
| EF8 | `MainResults` aggregation and completeness audit | AUDITED |
| EF9 | Contradictory audit and boundary hardening | AUDITED |
| EF10 | Possible exact-finite API freeze and publication | NOT OPENED |

Minimum stage correspondence:

- EF3: `Diachronic/UnitaryRecordOrbit.lean`
- EF4: `Diachronic/FineBornWeightRealization.lean`
- EF5: `Diachronic/PhysicalFinePlanContinuation.lean`
- EF6: `API/ExactFinitePhysicalRichness.lean`
- EF7: `ExactFinite/RecordOrbit.lean`,
  `ExactFinite/RefinementRealization.lean`,
  `ExactFinite/PhysicalAdequacy.lean`
- EF8: `ExactFinite/MainResults.lean`,
  `docs/EXACT_FINITE_COMPLETENESS_AUDIT.md`
- EF9: `Audit/ExactFiniteContradictoryAudit.lean`,
  `docs/EXACT_FINITE_CONTRADICTORY_AUDIT.md`
