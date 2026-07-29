# Stabilité de l'API exacte finie
# Exact-Finite API Stability

## Français

Le point d'entrée stable depuis v2.0.0 est
`EverettianProbability.API.ExactFiniteMainResults`.

Toutes les déclarations contrôlées par `Audit/ExactFiniteAPIContract.lean`
sont stables en v2.x, y compris les noms et types des structures, les noms de
leurs champs et les conclusions des théorèmes publics. Aucun renommage ni
changement de type incompatible n'est autorisé ; des théorèmes additifs et des
évolutions de preuve interne restent possibles. Toute rupture exige v3.0.0 ou
une couche de compatibilité.

Les modules `ExactFinite/*` sont des implémentations, non le contrat externe.
`API/ExactFinitePhysicalRichness.lean` reste disponible mais n'est pas le
point d'entrée stable recommandé.

## English

The stable entry point since v2.0.0 is
`EverettianProbability.API.ExactFiniteMainResults`.

Every declaration checked by `Audit/ExactFiniteAPIContract.lean` is stable in
v2.x, including structure names and types, field names, and public theorem
conclusions. No incompatible rename or type change is allowed; additive
theorems and internal proof evolution remain allowed. A break requires v3.0.0
or a compatibility layer.

The `ExactFinite/*` modules are implementations, not the external contract.
`API/ExactFinitePhysicalRichness.lean` remains available but is not the
recommended stable entry point.
