# ARCHITECTURE_NOTES.md — everettian-probability-lean

## Français

### Statut d'architecture courant -- 2026-07-29

La frontiere stable est `EverettianProbability.API.Conditional`. Elle expose
un resultat conditionnel fini-projectif, et non une derivation des premisses
normatives, physiques ou semantiques. `SelfLocation/` fournit le formalisme de
record compatible; `Diachronic/` fournit les continuateurs, les lois de chaine
et de tour, la composition physique et l'associativite. Le noyau de richesse
physique exacte finie est etabli mais son entree `API.ExactFinitePhysicalRichness`
reste experimentale; la realisabilite microscopique generale et approximative
reste hors contrat.

Les notes datees qui suivent sont des **diagnostics historiques**; elles ne
decrivent pas le statut courant de la release.

### Actes, carte parent et interface P0.3

Les actes restent des fonctions totales
`Submodule ℂ (H n) → ℝ`; `AgreeOn D` porte la seule notion d’égalité
décisionnellement pertinente. `Core/Parent.lean` a été supprimé : tous les
tirés-en-arrière utilisent désormais `parentOf` et ses lemmes publics.

L’interface abstraite demeure en aval. Son sous-type projectif
`{c // c ∈ D.cells}` est confiné à l’énumération finie et n’entre jamais dans
le type des actes. Les instances projective et effets valident la décision
P0.3 sans déclencher la condition d’arrêt.

### 2026-07-26 — défaut P3 : contamination par un énoncé faux

`exists_unique_weights` demandait l’unicité d’une fonction ambiante alors que
sa propriété ne consultait que `D.cells`. L’énoncé était faux : modifier le
représentant hors des cellules conservait la représentation. Le
`Classical.choose` qui en dépendait rendait `contextualWeight` sans contenu et
contaminait tout l’aval.

La réparation supprime ces deux déclarations. Le poids est désormais
`canonicalWeight F D c = F.V D (indicator c)` sur les cellules et `0` hors
cellules ; la représentation est prouvée et l’unicité est énoncée seulement
sur `D.cells`. Leçon méthodologique : un `sorry` sur un énoncé faux n’est pas
une dette mais une contamination, et `SORRY_COUNT` ne distingue pas les deux.

### 2026-07-26 — défaut P4 : vacuité de la quantification globale

L’ancienne propriété demandait qu’un même acte coïncide avec son propre
tiré-en-arrière pour tous les raffinements. Le raffinement explicite vers la
perspective `{⊤}` force alors l’acte à être constant sur toutes les cellules
accessibles. Les indicatrices sont exclues et toute famille rationnelle
satisfait la prémisse filtrée. Ce fait est conservé et nommé dans
`GlobalPayoffVacuity.lean`, avec la famille uniforme qui satisfait la prémisse
globale tout en violant Grain.

La prémisse adoptée est `RefinementInvariantLocal` : deux descriptions sont
comparées lorsqu’elles sont `AgreeOn` sur la perspective fine. La localité de
`V`, dérivée de la monotonie dans les deux sens, prouve son équivalence avec
l’égalité sur le tiré-en-arrière canonique. L’espérance bornienne satisfait
cette prémisse, puis les indicatrices donnent Grain.

### 2026-07-26 — voie d’amélioration visée, non acquise

Une prémisse restreinte aux raffinements préservant les records accessibles
serait défendable comme indifférence aux différences physiquement
inaccessibles. Elle ne donnerait directement qu’un Grain restreint, alors que
`AxGrain` quantifie sur tous les raffinements. Le pont manquant est exactement
P6a : réaliser tout raffinement projectif de façon record-neutre par couplage
d’ancilla. L’architecture cible est donc :

`invariance restreinte + réalisabilité physique ⇒ Grain complet ⇒ Born`.

P6a n’est pas ouverte dans cette session et `RestrictedRecordSectors` n’est
ni importé ni utilisé.

### 2026-07-26 — discipline NonTriviality et audit rétroactif

La non-vacuité ne suffit pas à établir la force d'une prémisse :
`bornExpectation_refinementInvariantLocal` avait un habitant positif, alors
que la lecture globale précédente restait sans pouvoir discriminant. La
discipline `NonTriviality` exige désormais, dans le même commit que toute
prémisse, un témoin concret positif (`Nonvacuity`) et un témoin concret
négatif (`NonTriviality`). Elle aurait détecté la vacuité de
`GloballyPayoffPreserving` dès son introduction.

Le témoin négatif de la prémisse adoptée est
`uniform_not_refinementInvariantLocal` : la cellule complémentaire dans la
perspective binaire reçoit `1/2` pour la règle uniforme et `2/3` après son
raffinement en trois lignes. La garde repère déjà, en avertissement, les
`def … : Prop` documentées par le marqueur `PREMISE` qui n'ont pas d'entrée
correspondante dans un `NonTriviality.lean` voisin.

Audit rétrospectif des structures effectivement employées comme hypothèses :

| Structure | Témoin positif | Témoin négatif | État |
|---|---|---|---|
| `RationalExpectationFamily` | `uniformExpectationFamily` | `maxExpectation_not_affine` (`Preference/NonTriviality.lean`) : le maximum sur les cellules est monotone et normalisé, mais viole l'affinité (`1/2 ≠ 1`, perspective binaire explicite) | Complet |
| `RefinementInvariantLocal` | `bornExpectation_refinementInvariantLocal` | `uniform_not_refinementInvariantLocal` | Complet |
| `RefinementInvariant` | `bornExpectation_refinementInvariant` | dérivé de l'équivalence avec la forme locale et du témoin uniforme ; pas encore nommé séparément | Couvert par équivalence, à nommer si cette forme redevient publique |
| `GloballyPayoffPreserving` | non requis : lecture archivée, non admise comme prémisse | `not_globallyPayoffPreserving_indicator` | Résultat négatif conservé |
| `Abstract.RefinementInvariant` | témoins projectif et effets | absent | Hors de la chaîne P3–P4 ; ne pas ouvrir cette extension ici |

La CI distante du dépôt privé est une vérification manuelle à la charge du
mainteneur : cet environnement ne dispose ni de `gh` ni d'un jeton GitHub pour
lire les runs. Les critères automatisés de cette session sont donc `lake build`,
l'audit local des axiomes et `scripts/guard.sh`; la vérification de la CI ne
leur est pas substituée.

## English

### Current architecture status -- 2026-07-29

The stable boundary is `EverettianProbability.API.Conditional`. It exposes a
finite-projective conditional result, not a derivation of normative, physical,
or semantic premises. `SelfLocation/` supplies compatible-record formalism;
`Diachronic/` supplies continuators, chain and tower laws, physical composition,
and associativity. The exact finite physical-richness core is established, but
its `API.ExactFinitePhysicalRichness` entry remains experimental; general and
approximate microscopic realizability remains outside the contract.

The dated notes below are **historical diagnostics** and do not state the
current release status.

### Acts, upstream parent map, and the P0.3 interface

Acts remain total functions `Submodule ℂ (H n) → ℝ`; `AgreeOn D` is the only
decision-relevant equality. `Core/Parent.lean` was deleted: every pullback now
uses `parentOf` and its public lemmas.

The abstract interface remains downstream. Its projective subtype
`{c // c ∈ D.cells}` is confined to finite enumeration and never enters the
act type. The projective and effect instances validate decision P0.3 without
triggering the stop condition.

### 2026-07-26 — P3 defect: contamination by a false statement

`exists_unique_weights` demanded uniqueness of an ambient function although
its property inspected only `D.cells`. The statement was false: changing the
representative outside the cells preserved the representation. Its dependent
`Classical.choose` made `contextualWeight` contentless and contaminated every
downstream result.

The repair deletes both declarations. The weight is now
`canonicalWeight F D c = F.V D (indicator c)` on cells and `0` outside;
representation is proved and uniqueness is stated only on `D.cells`.
Methodological lesson: a `sorry` over a false statement is contamination, not
debt, and `SORRY_COUNT` cannot distinguish them.

### 2026-07-26 — P4 defect: vacuity of global quantification

The former property required one act to agree with its own pullback along all
refinements. The explicit refinement to `{⊤}` then forces the act to be
constant on every accessible cell. Indicators are excluded and every rational
family satisfies the filtered premise. This fact is retained and named in
`GlobalPayoffVacuity.lean`, together with the uniform family satisfying the
global premise while violating Grain.

The adopted premise is `RefinementInvariantLocal`: two descriptions are
compared when they are `AgreeOn` over the fine perspective. Locality of `V`,
derived from monotonicity in both directions, proves equivalence with equality
on the canonical pullback. Born expectation satisfies this premise, after
which indicator acts yield Grain.

### 2026-07-26 — targeted improvement path, not yet achieved

A premise restricted to refinements preserving accessible records would be
defensible as indifference to physically inaccessible differences. It would
directly yield only restricted Grain, whereas `AxGrain` quantifies over every
refinement. The missing bridge is precisely P6a: realizing every projective
refinement record-neutrally through ancilla coupling. The target architecture
is therefore:

`restricted invariance + physical realizability ⇒ full Grain ⇒ Born`.

P6a is not opened in this session, and `RestrictedRecordSectors` is neither
imported nor used.

### 2026-07-26 — NonTriviality discipline and retroactive audit

Nonvacuity alone does not establish the force of a premise:
`bornExpectation_refinementInvariantLocal` had a positive inhabitant while
the former global reading still had no discriminating power. The
`NonTriviality` discipline now requires, in the same commit as every premise,
a concrete positive (`Nonvacuity`) and negative (`NonTriviality`) witness. It
would have detected the vacuity of `GloballyPayoffPreserving` when that
definition was introduced.

The negative witness for the adopted premise is
`uniform_not_refinementInvariantLocal`: the complement cell of the binary
perspective receives `1/2` under the uniform rule and `2/3` after its
three-line refinement. The guard already reports, as a warning, `def … : Prop`
declarations documented with the `PREMISE` marker that lack a corresponding
entry in a neighbouring `NonTriviality.lean`.

Retroactive audit of structures actually used as hypotheses:

| Structure | Positive witness | Negative witness | State |
|---|---|---|---|
| `RationalExpectationFamily` | `uniformExpectationFamily` | `maxExpectation_not_affine` (`Preference/NonTriviality.lean`): the max over cells is monotone and normalized, but violates affinity (`1/2 ≠ 1`, explicit binary perspective) | Complete |
| `RefinementInvariantLocal` | `bornExpectation_refinementInvariantLocal` | `uniform_not_refinementInvariantLocal` | Complete |
| `RefinementInvariant` | `bornExpectation_refinementInvariant` | derived from equivalence with the local form and the uniform witness; not separately named yet | Covered by equivalence; name it if this form becomes public again |
| `GloballyPayoffPreserving` | not required: archived reading, not an admitted premise | `not_globallyPayoffPreserving_indicator` | Retained negative result |
| `Abstract.RefinementInvariant` | projective and effect witnesses | absent | Outside the P3–P4 chain; do not open this extension here |

Remote CI for the private repository is a manual verification owned by the
maintainer: this environment has neither `gh` nor a GitHub token able to read
runs. The automated criteria for this session are therefore `lake build`, the
local axiom audit, and `scripts/guard.sh`; remote CI is not silently replaced
by them.
