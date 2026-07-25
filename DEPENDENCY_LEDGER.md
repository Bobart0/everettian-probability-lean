# DEPENDENCY_LEDGER.md — everettian-probability-lean

## Français

Registre anti-circularité. Pour chaque déclaration publique, note si elle
utilise — directement ou par une hypothèse qu'elle prend en argument — la
norme hilbertienne, la notion d'orthogonalité, la décohérence, la trace,
**la mesure de Born**, la typicalité, ou une norme de rationalité. **Toute
déclaration qui utiliserait la mesure de Born en amont de sa propre
dérivation doit être signalée ci-dessous par 🔴.** Aucune entrée n'est
actuellement rouge : P1 ne contient aucun contenu scientifique, seulement
des définitions et des lemmes de compatibilité triviaux (voir
`ARCHITECTURE_NOTES.md`).

| Déclaration | Norme hilbertienne ? | Orthogonalité ? | Décohérence ? | Trace ? | Mesure de Born ? | Typicalité ? | Rationalité ? |
|---|---|---|---|---|---|---|---|
| `Core.Act` (type, `AgreeOn`, `const`, `indicator`, `PointwiseLE`, `convComb`) | Non | Non | Non | Non | Non | Non | Non |
| `Core.parent` | Non (`Perspective` amont l'utilise en interne, pas ici) | Structurel seulement (via `Perspective`) | Non | Non | Non | Non | Non |
| `Refinement.pullbackAct` | Non | Non | Non | Non | Non | Non | Non |
| `Refinement.PayoffPreserving` | Non | Non | Non | Non | Non | Non | Oui (prémisse normative, voir `docs/SCOPE_AND_LIMITATIONS.md`) |
| `Preference.RationalExpectationFamily` | Non | Non | Non | Non | Non | Non | Oui (affinité, monotonie, normalisation) |
| `Preference.uniformExpectationFamily` (témoin P1) | Non (comptage uniforme, délibérément dégénéré) | Non | Non | Non | Non | Non | Oui (témoin) |
| `Preference.exists_unique_weights` (but ouvert) | Non | Non | Non | Non | Non | Non | Oui |
| `BornCalibration.contextualWeight` | Non par elle-même (hérite du type `Perspective n → Submodule ℂ (H n) → ℝ` amont) | Non | Non | Non | Non | Non | Oui |
| `BornCalibration.refinement_invariant_implies_grain` (but ouvert) | Non | Non | Non | Non | Non (conclut `AxGrain`, n'utilise pas Born en prémisse) | Non | Oui |
| `BornCalibration.born_expectation_formula` (but ouvert) | Oui, via `grainCoherenceTheorem_projector` amont, cité comme conclusion, jamais comme prémisse | Oui (héritée de la conclusion amont) | Non | Non | Oui — **en conclusion uniquement**, jamais en prémisse | Non | Oui |
| `Rivals.naiveCounting` | Non | Non | Non | Non | Non | Non | Non (délibérément non rationnel — c'est l'objet de la réfutation) |

## English

Anti-circularity registry. For each public declaration, notes whether it
uses — directly, or via a hypothesis it takes as an argument — the
Hilbert-space norm, orthogonality, decoherence, trace, **the Born
measure**, typicality, or a rationality norm. **Any declaration that would
use the Born measure upstream of its own derivation must be flagged below
with 🔴.** No entry is currently red: P1 contains no scientific content,
only definitions and trivial compatibility lemmas (see
`ARCHITECTURE_NOTES.md`).

| Declaration | Hilbert norm? | Orthogonality? | Decoherence? | Trace? | Born measure? | Typicality? | Rationality? |
|---|---|---|---|---|---|---|---|
| `Core.Act` (type, `AgreeOn`, `const`, `indicator`, `PointwiseLE`, `convComb`) | No | No | No | No | No | No | No |
| `Core.parent` | No (`Perspective` upstream uses it internally, not here) | Structural only (via `Perspective`) | No | No | No | No | No |
| `Refinement.pullbackAct` | No | No | No | No | No | No | No |
| `Refinement.PayoffPreserving` | No | No | No | No | No | No | Yes (normative premise, see `docs/SCOPE_AND_LIMITATIONS.md`) |
| `Preference.RationalExpectationFamily` | No | No | No | No | No | No | Yes (affinity, monotonicity, normalization) |
| `Preference.uniformExpectationFamily` (P1 witness) | No (uniform count, deliberately degenerate) | No | No | No | No | No | Yes (witness) |
| `Preference.exists_unique_weights` (open goal) | No | No | No | No | No | No | Yes |
| `BornCalibration.contextualWeight` | Not by itself (inherits the upstream type `Perspective n → Submodule ℂ (H n) → ℝ`) | No | No | No | No | No | Yes |
| `BornCalibration.refinement_invariant_implies_grain` (open goal) | No | No | No | No | No (concludes `AxGrain`, does not take Born as a premise) | No | Yes |
| `BornCalibration.born_expectation_formula` (open goal) | Yes, via upstream `grainCoherenceTheorem_projector`, cited as a conclusion, never as a premise | Yes (inherited from the upstream conclusion) | No | No | Yes — **as a conclusion only**, never as a premise | No | Yes |
| `Rivals.naiveCounting` | No | No | No | No | No | No | No (deliberately non-rational — that is the point of the refutation) |
