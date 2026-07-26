# QUBIT_FEASIBILITY_REPORT.md

> Rapport de faisabilité (section 4 du prompt de reprise du 2026-07-26).
> Texte seul : aucun code n'est écrit ici, aucun chantier n'est ouvert.
> Feasibility report (section 4 of the 2026-07-26 resumption prompt).
> Text only: no code is written here, no work is opened.

## Français

### 1. L'analogue exact de `born_expectation_of_invariance`

Il n'existe **pas encore**. Ce que la route effets fournit déjà, en amont
et dans `Core/Interface.lean` de ce dépôt, est strictement plus faible :

- `Abstract.Effects.pureState_refinementInvariant` (`Core/Interface.lean`)
  établit l'invariance sous raffinement de `Abstract.expectation` pour un
  `EstimationRule` **déjà construit** (`pureStateEstimationRule`). Il ne
  part pas d'une famille d'espérance rationnelle et n'en dérive rien : il
  part d'une règle qui satisfait déjà `Grain` par construction.
- En amont, `EstimationRule` (`BornRule/EffectPerspectives/Estimation.lean`)
  regroupe `weight`, `nonneg` (Pos), `normalized` (Norm) et **`grain`**
  comme quatre champs simultanés d'une seule structure : contrairement à
  `AxGrain`/`AxNorm`/`AxPos` côté projectif (des `Prop` indépendantes,
  vérifiables séparément), on ne peut pas exhiber un objet qui satisfasse
  Pos et Norm sans satisfaire Grain — Grain est une donnée de la
  construction, pas une conséquence à en tirer.

L'analogue exact demanderait donc une **nouvelle** famille de
déclarations, parallèle à `Preference`/`BornCalibration` mais indexée par
`EffectPerspective n` / `Fin D.outcomes` plutôt que par `Perspective n` /
`Submodule ℂ (H n)` :

1. `RationalExpectationFamily`-effets : une structure `V : (D :
   EffectPerspective n) → (Fin D.outcomes → ℝ) → ℝ` avec affinité,
   monotonie, normalisation — copie mécanique de
   `Preference/ExpectationFunctional.lean`.
2. `represents`-effets et `canonicalWeight`-effets : `canonicalWeight F D i
   := F.V D (indicator i)` — copie mécanique de
   `Preference/Representation.lean` et `BornCalibration/
   ContextualWeight.lean`.
3. Une prémisse d'invariance locale-effets (`RefinementInvariantLocal`
   reformulée, voir section 3 ci-dessous) et le pont
   « invariance ⟹ `EstimationRule.grain` » — l'analogue de
   `refinement_invariant_implies_grain`, mais qui doit désormais produire
   les **quatre** champs de `EstimationRule` (`weight`, `nonneg`,
   `normalized`, `grain`) en un seul objet, plutôt que dériver Grain
   séparément d'axiomes déjà acquis.
4. La composition finale avec le théorème de Busch amont — voir section 2.

### 2. Briques amont manquantes

Une seule, mais réelle et précisément nommable :
`BornRule/EffectPerspectives/Main.lean` contient
`projectionEffect_weight_eq_born` et `contextual_projection_weight_eq_born`,
tous deux prouvés pour `{n : ℕ} (hn : 1 ≤ n)` — **pas** seulement `n = 2`.
Seules leurs spécialisations `qubit_projectionEffect_weight_eq_born` et
`qubit_contextual_projection_weight_eq_born` (fixées à `n = 2`) sont
réexportées par `QuantumFoundations.ProbabilityAPI`
(`namespace EffectPerspectives`, section « From `BornRule.
EffectPerspectives` »). La version générale n'est pas accessible depuis ce
dépôt sans un import direct de `QuantumFoundations.BornRule.
EffectPerspectives.Main`, ce qui violerait la convention d'import unique
(`AGENTS.md`).

**Brique à demander, nommément** : ajouter
`projectionEffect_weight_eq_born` et `contextual_projection_weight_eq_born`
à l'export `EffectPerspectives` de `ProbabilityAPI.lean`. C'est un ajout
strictement additif (aucune déclaration existante n'est modifiée), et il
change la portée du programme : la route effets, une fois cette brique
exposée, couvrirait potentiellement **tout** `n ≥ 1`, pas seulement le
qubit — recouvrant, et non plus seulement complétant, la route projective
(`n ≥ 3`). `ContextualNullSupport` (l'analogue exact de `AxNul`, référençant
l'état) est en revanche déjà réexportable telle quelle si nécessaire — à
vérifier au moment d'ouvrir le jalon.

### 3. `RefinementInvariantLocal` ne se transpose pas telle quelle

Non. Trois différences structurelles, chacune contraignante :

- **`Refines` change de nature.** Côté projectif,
  `Refines D' D := ∀ c' ∈ D'.cells, ∃ c ∈ D.cells, c' ≤ c` est une `Prop`
  existentielle : *tout* raffinement au sens ensembliste en fournit
  automatiquement un témoin. Côté effets,
  `EffectPerspectives.Refines fine coarse` est une **structure** portant
  une donnée (`parent : Fin fine.outcomes → Fin coarse.outcomes`) et une
  preuve (`coarse_eq_fiber_sum`) : il n'existe **pas** de constructeur
  générique transformant une relation de raffinement sémantique en un
  habitant de `Refines`. Seuls quatre constructeurs existent en amont :
  `Refines.refl`, `collapseToChosen`, `splitRefinesBinary`,
  `duplicateZeroRefinesBinary` (plus `Refines.trans`, ajouté récemment,
  sans rôle dans le manuscrit, précisément pour ce dépôt). Une prémisse
  « invariante sous **tout** raffinement » quantifierait donc, de fait,
  sur les raffinements **atteignables par composition de ces quatre
  constructeurs** — une classe strictement plus étroite et plus
  structurée que « tout raffinement ensembliste », et dont il faudrait
  caractériser l'extension exacte avant de revendiquer une prémisse
  aussi générale que `RefinementInvariantLocal` l'est côté projectif.
- **Le tiré-en-arrière est plus simple à définir, mais la fibre est déjà
  fournie, pas à reconstruire.** `r.parent` est total et explicite (pas de
  `Classical.choice`, pas de valeur poubelle à gérer) : `pullbackAct`-effets
  serait `a ∘ r.parent`, sans les lemmes `parentOf_mem`/`parentOf_le`/
  `parentOf_eq_of_le` à invoquer. En contrepartie, `coarse_eq_fiber_sum`
  fournit déjà, comme donnée de `Refines` lui-même, exactement la
  décomposition en fibre que `coarseCells_eq_fiber_parentOf` établit comme
  *théorème* côté projectif — il n'y a rien à prouver, mais rien non plus
  à généraliser au-delà de ce que chaque constructeur fournit explicitement.
- **`ContextualNullSupport`** (`EffectPerspectives/PureStatePinning.lean`)
  est l'exact analogue de `AxNul` : une contrainte sur les poids de
  l'agent référençant l'état `ψ` via `(D.effects i).1 ψ = 0`. La structure
  à deux prémisses-ponts (section 3 du prompt précédent) se reproduit donc
  identiquement sur la route effets — ce n'est pas une singularité du
  formalisme projectif.

### 4. Estimation d'effort et risques

**Effort.** P3+P4 (représentation canonique, invariance ⟹ Grain ⟹ Born,
côté projectif) ont occupé une session complète de reprise, avec deux
défauts de spécification détectés et réparés en cours de route
(`ARCHITECTURE_NOTES.md`, entrées du 2026-07-26). L'analogue effets
demande de reconstruire la même chaîne, sans pouvoir réutiliser telle
quelle l'infrastructure `parentOf`/`coarseCells`/
`axGrain_iff_coarseCells` (spécifique aux sous-espaces), mais avec des
preuves de fibre déjà fournies par `Refines.coarse_eq_fiber_sum` côté
effets. Estimation raisonnable : **une session dédiée complète**,
comparable à P3+P4, avec un risque non négligeable de itérations
supplémentaires dues à l'absence de précédent exact à copier (P3+P4 pour
la route effets n'a jamais été tenté, contrairement à ce que P1 avait déjà
dégrossi pour la route projective).

**Risques, par ordre décroissant :**

1. **Portée réelle de « tout raffinement ».** Tant que l'extension exacte
   des raffinements atteignables par composition des quatre constructeurs
   amont n'est pas caractérisée, il n'est pas certain qu'une prémisse
   `RefinementInvariantLocal`-effets aussi large que son analogue
   projectif soit même **formulable** de façon satisfaisante — ou qu'elle
   coïncide, une fois formulée, avec ce que la littérature de théorie de
   la décision entend par indifférence aux raffinements.
2. **Brique amont à faire approuver.** Le point 2 ci-dessus requiert une
   modification de `quantum-foundations-lean` (un ajout d'export,
   strictement additif mais hors de ce dépôt) — décision qui, par la
   règle absolue 8 (`AGENTS.md`), n'appartient pas à cette session et
   demande une approbation humaine séparée.
3. **Retypage mécanique mais volumineux.** `Act`, `AgreeOn`, `indicator`,
   `PointwiseLE`, `convComb`, et toutes les preuves de `Preference/` et
   `BornCalibration/` qui les utilisent, devraient être reproduites contre
   `Fin D.outcomes` plutôt que `Submodule ℂ (H n)` — mécanique, mais
   représentant l'essentiel du volume de P3+P4.
4. **Gain potentiel sous-estimé si le point 2 est traité.** Si
   `projectionEffect_weight_eq_born`/`contextual_projection_weight_eq_born`
   (portée `n ≥ 1`) sont exposés plutôt que leurs seules spécialisations
   qubit, la route effets cesserait d'être un simple complément à `n = 2`
   pour devenir une **route alternative complète**, potentiellement plus
   générale que la route projective elle-même (qui reste bornée à
   `n ≥ 3`). Ce fait mérite d'être signalé avant toute décision sur l'ordre
   d'attaque des jalons futurs.

## English

### 1. The exact analogue of `born_expectation_of_invariance`

It does **not** exist yet. What the effect route already provides, both
upstream and in this repository's `Core/Interface.lean`, is strictly
weaker:

- `Abstract.Effects.pureState_refinementInvariant`
  (`Core/Interface.lean`) establishes refinement invariance of
  `Abstract.expectation` for an `EstimationRule` that is **already
  built** (`pureStateEstimationRule`). It does not start from a rational
  expectation family and derive anything from it: it starts from a rule
  that already satisfies `Grain` by construction.
- Upstream, `EstimationRule`
  (`BornRule/EffectPerspectives/Estimation.lean`) bundles `weight`,
  `nonneg` (Pos), `normalized` (Norm), and **`grain`** as four
  simultaneous fields of a single structure: unlike
  `AxGrain`/`AxNorm`/`AxPos` on the projective side (independent `Prop`s,
  checkable separately), one cannot exhibit an object satisfying Pos and
  Norm without also satisfying Grain — Grain is data of the construction,
  not a consequence to be drawn from it.

The exact analogue would therefore require a **new** family of
declarations, parallel to `Preference`/`BornCalibration` but indexed by
`EffectPerspective n` / `Fin D.outcomes` rather than `Perspective n` /
`Submodule ℂ (H n)`:

1. An effect-side `RationalExpectationFamily`: a structure `V : (D :
   EffectPerspective n) → (Fin D.outcomes → ℝ) → ℝ` with affinity,
   monotonicity, normalization — a mechanical copy of
   `Preference/ExpectationFunctional.lean`.
2. Effect-side `represents` and `canonicalWeight`: `canonicalWeight F D i
   := F.V D (indicator i)` — a mechanical copy of
   `Preference/Representation.lean` and
   `BornCalibration/ContextualWeight.lean`.
3. An effect-side local-invariance premise (`RefinementInvariantLocal`
   reformulated, see section 3 below) and the bridge "invariance ⟹
   `EstimationRule.grain`" — the analogue of
   `refinement_invariant_implies_grain`, but now required to produce
   `EstimationRule`'s **four** fields (`weight`, `nonneg`, `normalized`,
   `grain`) as a single object, rather than deriving Grain separately
   from already-acquired axioms.
4. The final composition with the upstream Busch theorem — see section 2.

### 2. Missing upstream bricks

Exactly one, but real and precisely nameable:
`BornRule/EffectPerspectives/Main.lean` contains
`projectionEffect_weight_eq_born` and `contextual_projection_weight_eq_born`,
both proved for `{n : ℕ} (hn : 1 ≤ n)` — **not** only `n = 2`. Only their
specializations `qubit_projectionEffect_weight_eq_born` and
`qubit_contextual_projection_weight_eq_born` (fixed at `n = 2`) are
re-exported by `QuantumFoundations.ProbabilityAPI` (`namespace
EffectPerspectives`, the "From `BornRule.EffectPerspectives`" section).
The general version is not reachable from this repository without a
direct import of `QuantumFoundations.BornRule.EffectPerspectives.Main`,
which would violate the single-import convention (`AGENTS.md`).

**Brick to request, by name**: add `projectionEffect_weight_eq_born` and
`contextual_projection_weight_eq_born` to the `EffectPerspectives` export
in `ProbabilityAPI.lean`. This is a strictly additive change (no existing
declaration is modified), and it changes the program's scope: the effect
route, once this brick is exposed, would potentially cover **all**
`n ≥ 1`, not just the qubit — subsuming, not merely complementing, the
projective route (`n ≥ 3`). `ContextualNullSupport` (the exact analogue of
`AxNul`, referencing the state) is, by contrast, already re-exportable as
is if needed — to be verified when the milestone actually opens.

### 3. `RefinementInvariantLocal` does not transpose as-is

No. Three structural differences, each constraining:

- **`Refines` changes nature.** On the projective side,
  `Refines D' D := ∀ c' ∈ D'.cells, ∃ c ∈ D.cells, c' ≤ c` is an
  existential `Prop`: *any* set-theoretic refinement automatically
  furnishes a witness. On the effect side,
  `EffectPerspectives.Refines fine coarse` is a **structure** carrying
  data (`parent : Fin fine.outcomes → Fin coarse.outcomes`) and a proof
  (`coarse_eq_fiber_sum`): there is **no** generic constructor turning a
  semantic refinement relation into an inhabitant of `Refines`. Only four
  constructors exist upstream: `Refines.refl`, `collapseToChosen`,
  `splitRefinesBinary`, `duplicateZeroRefinesBinary` (plus `Refines.trans`,
  added recently, with no manuscript role, precisely for this
  repository). A premise "invariant under **every** refinement" would
  therefore, in effect, quantify only over refinements **reachable by
  composing these four constructors** — a strictly narrower and more
  structured class than "every set-theoretic refinement," whose exact
  extension would need characterizing before claiming a premise as
  general as `RefinementInvariantLocal` is on the projective side.
- **Pullback is simpler to define, but the fiber is already supplied, not
  reconstructed.** `r.parent` is total and explicit (no
  `Classical.choice`, no junk value to manage): effect-side `pullbackAct`
  would be `a ∘ r.parent`, without needing
  `parentOf_mem`/`parentOf_le`/`parentOf_eq_of_le`-style lemmas. In
  exchange, `coarse_eq_fiber_sum` already supplies, as data of `Refines`
  itself, exactly the fiber decomposition that
  `coarseCells_eq_fiber_parentOf` establishes as a *theorem* on the
  projective side — there is nothing to prove, but also nothing to
  generalize beyond what each constructor explicitly supplies.
- **`ContextualNullSupport`** (`EffectPerspectives/PureStatePinning.lean`)
  is the exact analogue of `AxNul`: a constraint on the agent's weights
  referencing the state `ψ` via `(D.effects i).1 ψ = 0`. The two-bridge-
  premise structure (section 3 of the prior prompt) therefore reproduces
  identically on the effect route — it is not a peculiarity of the
  projective formalism.

### 4. Effort estimate and risks

**Effort.** P3+P4 (canonical representation, invariance ⟹ Grain ⟹ Born,
on the projective side) took a full resumption session, with two
specification defects detected and repaired along the way
(`ARCHITECTURE_NOTES.md`, entries dated 2026-07-26). The effect-side
analogue requires rebuilding the same chain without being able to reuse
the `parentOf`/`coarseCells`/`axGrain_iff_coarseCells` infrastructure
as-is (specific to subspaces), but with fiber proofs already supplied by
`Refines.coarse_eq_fiber_sum` on the effect side. Reasonable estimate:
**one full dedicated session**, comparable to P3+P4, with non-negligible
risk of extra iterations due to the absence of an exact precedent to copy
(P3+P4 for the effect route has never been attempted, unlike what P1 had
already sketched for the projective route).

**Risks, in decreasing order:**

1. **Actual scope of "every refinement."** Until the exact extension of
   refinements reachable by composing the four upstream constructors is
   characterized, it is not certain that an effect-side
   `RefinementInvariantLocal` premise as broad as its projective analogue
   is even **satisfactorily formulable** — or that, once formulated, it
   coincides with what the decision-theory literature means by
   refinement indifference.
2. **Upstream brick requiring approval.** Point 2 above requires a change
   to `quantum-foundations-lean` (an export addition, strictly additive
   but outside this repository) — a decision that, per absolute rule 8
   (`AGENTS.md`), does not belong to this session and needs separate
   human approval.
3. **Mechanical but sizable retyping.** `Act`, `AgreeOn`, `indicator`,
   `PointwiseLE`, `convComb`, and every proof in `Preference/` and
   `BornCalibration/` that uses them, would need reproducing against
   `Fin D.outcomes` rather than `Submodule ℂ (H n)` — mechanical, but
   accounting for most of P3+P4's volume.
4. **Potentially underestimated payoff if point 2 is addressed.** If
   `projectionEffect_weight_eq_born`/`contextual_projection_weight_eq_born`
   (scope `n ≥ 1`) are exposed rather than only their qubit
   specializations, the effect route would stop being a mere complement
   at `n = 2` and become a **complete alternative route**, potentially
   more general than the projective route itself (which remains bounded
   to `n ≥ 3`). This is worth flagging before any decision on the
   ordering of future milestones.
