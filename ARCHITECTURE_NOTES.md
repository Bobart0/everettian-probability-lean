# ARCHITECTURE_NOTES.md — everettian-probability-lean

## Français

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

## English

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
