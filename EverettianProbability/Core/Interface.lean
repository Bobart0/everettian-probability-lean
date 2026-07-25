/-!
**FR.** # Interface (placeholder — décision P0.3 non prise)

Ce fichier est un **placeholder documenté**, volontairement vide de code.
La couche décisionnelle peut s'attacher à la caractérisation de mesure
amont de deux façons distinctes :

1. **Route projective** : `Perspective`/`Refines`/`AxGrain` tels quels
   (`QuantumFoundations.BornRule.Perspective`), qui héritent de l'hypothèse
   `n ≥ 3` du théorème de Gleason.
2. **Route effets** : `EffectPerspective`/`Effect`/le raffinement d'effets
   (`QuantumFoundations.BornRule.EffectPerspectives`), qui atteint le qubit
   (`n = 2`) via le théorème de Busch, mais change la nature des objets
   manipulés (opérateurs `0 ≤ T ≤ 1`, pas des sous-espaces).

Une troisième option — une interface abstraite commune, instanciée deux
fois (projective et effets) — est envisageable mais n'a pas été tranchée :
c'est précisément la décision **P0.3**, qui doit être prise sur papier
(`PLAN_REVISE_everettian-probability-lean.md`, jalon P0) avant qu'un choix
de types soit gravé dans le code de ce dépôt. Tant que cette décision n'est
pas prise, `Core/Act.lean` et `Core/Parent.lean` sont écrits directement
contre la route projective (`Perspective`, `Refines`), sans passer par une
abstraction — un choix révisable, mais explicite.

Ce fichier n'introduit donc aucune définition et ne demande aucune preuve :
aucun but ouvert.

**EN.** # Interface (placeholder — decision P0.3 not yet made)

This file is a **documented placeholder**, deliberately empty of code. The
decision-theoretic layer can attach to the upstream measurement
characterization in two distinct ways:

1. **Projective route**: `Perspective`/`Refines`/`AxGrain` as they stand
   (`QuantumFoundations.BornRule.Perspective`), which inherit Gleason's
   theorem's `n ≥ 3` hypothesis.
2. **Effect route**: `EffectPerspective`/`Effect`/effect refinement
   (`QuantumFoundations.BornRule.EffectPerspectives`), which reaches the
   qubit (`n = 2`) via Busch's theorem, but changes the nature of the
   objects being manipulated (operators `0 ≤ T ≤ 1`, not subspaces).

A third option — a common abstract interface, instantiated twice
(projective and effect) — is conceivable but has not been settled: this is
precisely decision **P0.3**, to be made on paper
(`PLAN_REVISE_everettian-probability-lean.md`, milestone P0) before a type
choice is cast in this repository's code. Until that decision is made,
`Core/Act.lean` and `Core/Parent.lean` are written directly against the
projective route (`Perspective`, `Refines`), without going through an
abstraction — a revisable but explicit choice.

This file therefore introduces no definition and requires no proof: no
goal is left open.
-/
