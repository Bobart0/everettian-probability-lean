# ARCHITECTURE_NOTES.md — everettian-probability-lean

## Français

Mémoire des écarts entre le plan annoncé (prompt de bootstrap P1) et le
code réellement écrit. Chaque entrée explique une décision, pas seulement
son résultat.

### 1. Acte : fonction totale plutôt que sous-type

Le plan aurait pu représenter un acte comme un sous-type dépendant d'une
perspective (`{a : Submodule ℂ (H n) → ℝ // ...}` indexé par `D`). Choix
retenu (`Core/Act.lean`) : une fonction **totale**
`Submodule ℂ (H n) → ℝ`, avec valeur poubelle hors des cellules de la
perspective effectivement considérée, et une relation `AgreeOn D a b`
distincte pour comparer deux actes *sur* une perspective. Raison :
c'est le patron « définition totale + valeur poubelle + lemmes de
spécification sous hypothèse » déjà utilisé partout en amont (`parent`
suit le même patron) — il évite la prolifération de types dépendants et
de coercions entre `Act D₁` et `Act D₂` pour deux perspectives différentes,
qui aurait rendu `pullbackAct` et `PayoffPreserving` beaucoup plus lourds
à énoncer.

### 2. Carte parent : `Classical.choice` + `Perspective.unique_parent`, `Refines` étant `∀∃`

`Refines D' D` (amont) est une relation `∀∃` — elle affirme l'existence
d'un parent pour chaque cellule fine, sans fournir de fonction. `Core/
Parent.lean` construit `parent r : Submodule ℂ (H n) → Submodule ℂ (H n)`
par `Classical.choice` sur cette existence, valeur poubelle `⊥` hors
domaine. Les trois lemmes de spécification (`parent_mem`, `parent_le`,
`parent_unique`) sont laissés comme buts ouverts en P1 (voir
`MILESTONES.md`) : leur contenu est immédiat une fois déballé
(`Classical.choose_spec` pour les deux premiers, `Perspective.
unique_parent` plus `D'.nz` pour le troisième), mais leur clôture est
différée pour garder P1 strictement infrastructurel, sans aucune preuve
mathématique.

### 3. Type d'atterrissage du poids contextuel

`BornCalibration/ContextualWeight.lean` fixe `contextualWeight F` au type
**exact** `Perspective n → Submodule ℂ (H n) → ℝ` — le type de `Est` dans
`AxGrain`/`AxNorm`/`AxPos`/`AxNul` et dans
`grainCoherenceTheorem_projector` en amont. Alternative rejetée : un type
enrichi (par exemple `Perspective n → {c // c ∈ D.cells} → ℝ`, dépendant
de `D`), plus proche de l'intuition « poids défini seulement sur les
cellules réelles », mais qui aurait exigé un adaptateur avant de brancher
le théorème amont — exactement ce que ce choix de type évite.

### 4. Lemmes de compatibilité de `pullbackAct` : prouvés, pas laissés en but ouvert

Le prompt de bootstrap suggérait des « lemmes de compatibilité en but
ouvert » pour `Refinement/PullbackAct.lean`. En pratique,
`pullbackAct_const` est immédiat par calcul (`rfl`), et
`pullbackAct_agree_of_agree` se déduit directement de `parent_mem` — dont
la preuve est elle-même différée, mais dont l'*énoncé* existe déjà. Les
deux lemmes sont donc prouvés en entier ici : citer une spécification
amont encore ouverte (patron « squelette d'abord, preuves ensuite ») est
légitime et ne fait apparaître aucun nouveau but ouvert dans ce fichier —
`#print axioms` sur `pullbackAct_agree_of_agree` révèle simplement la
dépendance résiduelle (voir `Audit/MainResults.lean`). Ce choix minimise
le budget de buts ouverts sans jamais affaiblir un énoncé, conformément à
la règle 3 de `AGENTS.md`.

## English

Memory of the gaps between the announced plan (P1 bootstrap prompt) and
the code actually written. Each entry explains a decision, not just its
outcome.

### 1. Act: total function rather than subtype

The plan could have represented an act as a subtype depending on a
perspective (`{a : Submodule ℂ (H n) → ℝ // ...}` indexed by `D`). Choice
made (`Core/Act.lean`): a **total** function `Submodule ℂ (H n) → ℝ`, with
a junk value outside the cells of the perspective actually under
consideration, and a separate `AgreeOn D a b` relation to compare two acts
*on* a perspective. Reason: this is the "total definition + junk value +
spec lemmas under hypothesis" pattern already used throughout upstream
(`parent` follows the same pattern) — it avoids the proliferation of
dependent types and coercions between `Act D₁` and `Act D₂` for two
different perspectives, which would have made `pullbackAct` and
`PayoffPreserving` far heavier to state.

### 2. Parent map: `Classical.choice` + `Perspective.unique_parent`, `Refines` being `∀∃`

`Refines D' D` (upstream) is a `∀∃` relation — it asserts the existence of
a parent for every fine cell, without furnishing a function. `Core/
Parent.lean` builds `parent r : Submodule ℂ (H n) → Submodule ℂ (H n)` by
`Classical.choice` on that existence, junk value `⊥` outside the domain.
The three specification lemmas (`parent_mem`, `parent_le`,
`parent_unique`) are left as open goals in P1 (see `MILESTONES.md`): their
content is immediate once unpacked (`Classical.choose_spec` for the first
two, `Perspective.unique_parent` plus `D'.nz` for the third), but closing
them is deferred to keep P1 strictly infrastructural, with no
mathematical proof whatsoever.

### 3. Landing type of the contextual weight

`BornCalibration/ContextualWeight.lean` fixes `contextualWeight F` at the
**exact** type `Perspective n → Submodule ℂ (H n) → ℝ` — the type of `Est`
in `AxGrain`/`AxNorm`/`AxPos`/`AxNul` and in
`grainCoherenceTheorem_projector` upstream. Rejected alternative: a richer
type (e.g. `Perspective n → {c // c ∈ D.cells} → ℝ`, depending on `D`),
closer to the intuition "weight defined only on the actual cells," but one
that would have required an adapter before wiring in the upstream
theorem — exactly what this type choice avoids.

### 4. `pullbackAct` compatibility lemmas: proved outright, not left as open goals

The bootstrap prompt suggested "compatibility lemmas left as open goals"
for `Refinement/PullbackAct.lean`. In practice, `pullbackAct_const` is
immediate by computation (`rfl`), and `pullbackAct_agree_of_agree` follows
directly from `parent_mem` — whose proof is itself deferred, but whose
*statement* already exists. Both lemmas are therefore proved in full here:
citing a still-open upstream specification (the "skeleton first, proofs
later" pattern) is legitimate and introduces no new open goal in this
file — `#print axioms` on `pullbackAct_agree_of_agree` simply reveals the
residual dependency (see `Audit/MainResults.lean`). This choice minimizes
the open-goal budget without ever weakening a statement, in accordance
with rule 3 of `AGENTS.md`.
