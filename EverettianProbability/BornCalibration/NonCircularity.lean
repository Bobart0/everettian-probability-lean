/-!
**FR.** # Non-circularité — cible documentée, aucune construction devinée

Ce fichier est un **placeholder documenté**, volontairement vide de code.
Il fixe la cible de la future preuve de non-circularité, sans deviner sa
construction : un témoin en `n = 2` (le cas qubit, hors de portée de la
route projective — voir `Core/Interface.lean`) d'une règle d'estimation
`Est : Perspective 2 → Submodule ℂ (H 2) → ℝ` **non bornienne**, satisfaisant
pourtant `AxGrain`, `AxPos`, `AxNorm` et `AxNul`.

Un tel témoin réfuterait l'objection selon laquelle la prémisse
d'invariance sous raffinement (`PayoffPreserving`, préservée par `V`)
*serait*, déguisée, la règle de Born elle-même : s'il existe une règle
d'estimation cohérente sous Grain qui n'est PAS `‖·‖²`, alors la
conclusion « Grain + Norm + Pos + Null ⟹ Born » (côté mesure) n'absorbe
pas silencieusement la prémisse normative côté décision — celle-ci fait un
travail non trivial.

La construction elle-même — table de dépendances vis-à-vis de la mesure de
Born, statut, jalon d'attaque — est renvoyée à `MILESTONES.md` et
`DEPENDENCY_LEDGER.md`. Aucune tentative n'est faite ici.

**EN.** # Non-circularity — documented target, no guessed construction

This file is a **documented placeholder**, deliberately empty of code. It
fixes the target of the future non-circularity proof, without guessing its
construction: a witness at `n = 2` (the qubit case, out of reach of the
projective route — see `Core/Interface.lean`) of an estimation rule
`Est : Perspective 2 → Submodule ℂ (H 2) → ℝ` that is **not** Born-based,
yet satisfies `AxGrain`, `AxPos`, `AxNorm`, and `AxNul`.

Such a witness would refute the objection that the refinement-invariance
premise (`PayoffPreserving`, preserved by `V`) *is*, in disguise, the Born
rule itself: if a Grain-coherent estimation rule exists that is NOT
`‖·‖²`, then the conclusion "Grain + Norm + Pos + Null ⟹ Born" (on the
measurement side) does not silently absorb the normative premise on the
decision side — the latter does nontrivial work.

The construction itself — its dependency table with respect to the Born
measure, status, attack milestone — is deferred to `MILESTONES.md` and
`DEPENDENCY_LEDGER.md`. No attempt is made here.
-/
