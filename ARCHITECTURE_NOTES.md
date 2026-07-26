# ARCHITECTURE_NOTES.md — everettian-probability-lean

## Français

### 1. Actes totaux

`Core/Act.lean` conserve la convention P1 :
`Act n = Submodule ℂ (H n) → ℝ`. Une valeur hors perspective est une valeur
poubelle; `AgreeOn D` exprime la seule égalité pertinente. Aucun type d'acte
ne dépend d'une perspective.

### 2. Carte parent amont

Depuis `v1.1.0-probability-api`, `parentOf` et ses lemmes de spécification
sont publics. `Core/Parent.lean` a été supprimé pour éviter deux choix
classiques concurrents. Tous les tirés-en-arrière projectifs utilisent
désormais `parentOf`.

### 3. Le pont mesure → fonctionnelle n'est pas définitionnel

`E₀_isGrain` porte sur les poids `‖projL c v‖²`; le résultat aval porte sur
la fonctionnelle totale
`∑ c ∈ D.cells, ‖projL c v‖² * a c`. La preuve de
`bornExpectation_pullback_eq` regroupe explicitement la somme fine par les
fibres de `parentOf`, sort le paiement constant de chaque fibre, identifie
la fibre à `coarseCells`, puis applique Grain. Cette étape est la preuve de
consistance de la prémisse normative, pas une simple réécriture.

### 4. Décision P0.3 : interface commune avec actes ambiants

La décision retenue est une interface abstraite en aval. Elle sépare :

- `Outcome`, espace ambiant sur lequel les actes sont totaux;
- `Cell D`, type fini dépendant servant uniquement à l'énumération;
- `Refinement fine coarse`, avec cartes parent sur l'espace ambiant et sur
  les cellules, reliées par une loi de spécification;
- le type des règles d'estimation et leur poids cellulaire.

Le tiré-en-arrière, `Grain`, l'espérance pondérée et l'invariance sont
formulés une seule fois. Le théorème abstrait
`expectation_refinementInvariant` établit Grain → invariance.

L'instance projective prend `Outcome = Submodule ℂ (H n)` et
`Cell D = {c // c ∈ D.cells}`; ce sous-type reste confiné à la somme finie et
ne contamine pas `Act`. L'instance effets prend `Outcome = ℕ` et
`Cell D = Fin D.outcomes`, avec le champ natif `Refines.parent`. Les témoins
`E₀` et `pureStateEstimationRule` valident respectivement les deux routes.
La condition d'arrêt « sous-type dans le type des actes » n'a donc pas été
déclenchée.

### 5. Diagnostic de spécification avant P4

Deux problèmes doivent être arbitrés avant de prétendre clore les théorèmes
P4. Premièrement, `exists_unique_weights` demande l'unicité d'une fonction
totale alors que sa propriété ne contraint ses valeurs que sur `D.cells`;
une normalisation hors cellules ou une notion d'équivalence sera nécessaire
en P3. Deuxièmement, `PayoffPreserving a` quantifie sur tous les raffinements.
Les indicatrices nécessaires à Grain ne sont pas globalement préservantes.
Une prémisse locale au raffinement, ou une autre formulation explicite, doit
être choisie avant la preuve. Aucun de ces énoncés n'a été modifié dans P2.

## English

### 1. Total acts

`Core/Act.lean` keeps the P1 convention:
`Act n = Submodule ℂ (H n) → ℝ`. A value outside the perspective is junk;
`AgreeOn D` expresses the only relevant equality. No act type depends on a
perspective.

### 2. Upstream parent map

Since `v1.1.0-probability-api`, `parentOf` and its specification lemmas are
public. `Core/Parent.lean` was deleted to avoid two competing classical
choices. Every projective pullback now uses `parentOf`.

### 3. The measure-to-functional bridge is not definitional

`E₀_isGrain` concerns the weights `‖projL c v‖²`; the downstream result
concerns the total functional
`∑ c ∈ D.cells, ‖projL c v‖² * a c`.
The proof of `bornExpectation_pullback_eq` explicitly groups the fine sum by
`parentOf` fibres, extracts the constant payoff on each fibre, identifies
the fibre with `coarseCells`, and then applies Grain. This is the consistency
proof for the normative premise, not a mere rewrite.

### 4. Decision P0.3: common interface with ambient acts

The chosen design is a downstream abstract interface. It separates:

- `Outcome`, the ambient space on which acts are total;
- `Cell D`, a dependent finite type used only for enumeration;
- `Refinement fine coarse`, with parent maps on ambient outcomes and cells,
  related by a specification law;
- the estimation-rule type and its cell weight.

Pullback, `Grain`, weighted expectation, and invariance are stated once. The
abstract theorem `expectation_refinementInvariant` proves Grain → invariance.

The projective instance uses `Outcome = Submodule ℂ (H n)` and
`Cell D = {c // c ∈ D.cells}`; this subtype remains confined to finite
summation and never enters `Act`. The effect instance uses `Outcome = ℕ` and
`Cell D = Fin D.outcomes`, with the native `Refines.parent` field. The `E₀`
and `pureStateEstimationRule` witnesses validate the two routes. The stop
condition “subtype in the act type” was therefore not triggered.

### 5. Specification diagnosis before P4

Two issues require an explicit decision before the P4 theorems can honestly
be closed. First, `exists_unique_weights` asks for uniqueness of a total
function although its property constrains values only on `D.cells`; P3 will
need an off-cell normalization or an equivalence notion. Second,
`PayoffPreserving a` quantifies over every refinement. The indicators needed
for Grain are not globally payoff-preserving. A refinement-local premise or
another explicit formulation must be chosen before the proof. Neither
statement was changed in P2.
