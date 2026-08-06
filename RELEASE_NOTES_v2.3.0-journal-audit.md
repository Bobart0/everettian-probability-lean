# v2.3.0-journal-audit

## Français

Cette release ajoute un troisième témoin de non-circularité en dimension 2,
au niveau des mesures projectives de Gleason.

`EverettianProbability.BornCalibration.skewProjMeasure` promeut le poids
rival `skewWeight witnessState` (déjà utilisé par les contre-modèles niveau
poids et niveau décision existants) en une véritable
`Gleason.ProjMeasure 2` : `μ A := skewF (‖projL A witnessState‖²)`, avec
`nonneg`, `top_eq_one` et `add_isOrtho` démontrés par disjonction
`⊥ / ⊤ / propre-non-nul`, le dernier cas se concluant via l'identité
pythagoricienne et `skewF_add_symm`.

`skewProjMeasure_not_representable` montre que cette mesure n'est
représentable par AUCUN opérateur densité au sens de `Gleason.bornValue`.
La preuve procède en trois temps : (1) une annihilation locale du noyau
reconstruite par redimensionnement, directement à partir de l'hypothèse de
représentation (sans passer par `AxNul`/`g`, donc valable sans `3 ≤ n`) ;
(2) un épinglage via `QuantumFoundations.BornRule.
eq_projL_of_vanishes_on_orthogonal` (confirmé utilisable en dimension 2)
forçant `ρ = projL (ℂ∙witnessState)` ; (3) une contradiction rationnelle
exacte sur `witnessLine`, opposant `81/337` (valeur rivale, via
`witnessLine_skewWeight_ne_born`) à `9/25` (valeur de Born, via
`witness_x`). La forme existentielle
`exists_nonrepresentable_projMeasure_two` en découle immédiatement.

Ce résultat est un **témoin ponctuel** : il n'affirme pas qu'aucune mesure
projective en dimension 2 n'est représentable, seulement que
`skewProjMeasure` spécifiquement ne l'est pas. Il complète, sans les
remplacer, les contre-modèles niveau poids
(`grain_does_not_imply_born_at_two`) et niveau décision
(`decision_premises_do_not_imply_born_at_two`) déjà présents depuis
`v2.2.0-journal-audit`.

Les audits de publication `Audit/JournalCore.lean` et
`Audit/MainResults.lean` ont été étendus (`#check`/`#print axioms`) sans
régression : toutes les déclarations concernées dépendent exactement de
`[propext, Classical.choice, Quot.sound]`, sans `sorryAx`.

Aucun pin amont (`quantum_foundations` `v1.3.1-journal-audit`, `gleason`
`v1.1.0-journal-audit`) n'a été modifié par cette release ; ni
`lean-toolchain`, ni `lakefile.toml`, ni `lake-manifest.json` n'ont changé.

## English

This release adds a third non-circularity witness in dimension 2, at the
level of Gleason projective measures.

`EverettianProbability.BornCalibration.skewProjMeasure` promotes the rival
weight `skewWeight witnessState` (already used by the existing weight-level
and decision-level countermodels) to a genuine `Gleason.ProjMeasure 2`:
`μ A := skewF (‖projL A witnessState‖²)`, with `nonneg`, `top_eq_one`, and
`add_isOrtho` proved by a `⊥ / ⊤ / proper-nonzero` case split, the last case
closing via the Pythagorean identity and `skewF_add_symm`.

`skewProjMeasure_not_representable` shows this measure is representable by
NO density operator in the sense of `Gleason.bornValue`. The proof proceeds
in three steps: (1) a local kernel-annihilation fact reconstructed by
rescaling, built directly from the representability hypothesis (rather than
from `AxNul`/`g`, hence valid without `3 ≤ n`); (2) pinning via
`QuantumFoundations.BornRule.eq_projL_of_vanishes_on_orthogonal` (confirmed
usable at dimension 2), forcing `ρ = projL (ℂ∙witnessState)`; (3) an exact
rational contradiction on `witnessLine`, pitting `81/337` (rival value, via
`witnessLine_skewWeight_ne_born`) against `9/25` (Born value, via
`witness_x`). The existential form
`exists_nonrepresentable_projMeasure_two` follows immediately.

This result is a **pointwise witness**: it does not claim that no projective
measure in dimension 2 is representable, only that `skewProjMeasure`
specifically is not. It complements, without replacing, the weight-level
(`grain_does_not_imply_born_at_two`) and decision-level
(`decision_premises_do_not_imply_born_at_two`) countermodels already present
since `v2.2.0-journal-audit`.

The publication audits `Audit/JournalCore.lean` and `Audit/MainResults.lean`
were extended (`#check`/`#print axioms`) with no regression: every
declaration involved depends exactly on
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

No upstream pin (`quantum_foundations` `v1.3.1-journal-audit`, `gleason`
`v1.1.0-journal-audit`) was changed by this release; `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json` are all unchanged.
