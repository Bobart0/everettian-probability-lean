# API stability / Stabilité de l'API

## Français

### API conditionnelle stable depuis v1.0.0, conservée en v2.x

Le point d'entrée recommandé est :

```lean
import EverettianProbability.API.ConditionalMainResults
```

Les déclarations de la façade conditionnelle, dont `ProjectiveBornPremises`,
`OneStepConditionalBornResults`, `TwoStepConditionalBornResults` et
`conditionalBornMainResults`, sont stables depuis v1.0.0 et restent prises en
charge en v2.x. Les réparations de preuve internes ne sont pas des ruptures
d'API ; les modules d'implémentation ne font pas partie du contrat externe.

### API exacte finie stable depuis v2.0.0

Le point d'entrée recommandé est :

```lean
import EverettianProbability.API.ExactFiniteMainResults
```

Le contrat v2.x est vérifié par `Audit/ExactFiniteAPIContract.lean` et décrit
dans `docs/EXACT_FINITE_API_STABILITY.md`. Il couvre les structures, leurs
champs et les théorèmes publics de cette façade. Toute rupture incompatible
exige v3.0.0 ou une couche de compatibilité.

### Modules internes non stables

Les modules `ExactFinite/*`, `Frequency/*`, `Confirmation/*` et les autres
modules d'implémentation peuvent évoluer sans modifier les deux contrats
publics stables. Leur existence ne constitue pas une promesse de stabilité.

### Ancienne façade expérimentale conservée

`API.ExactFinitePhysicalRichness` est conservée pour compatibilité avec les
utilisateurs antérieurs à v2.0.0. Elle était la façade expérimentale de la
couche exacte finie avant v2.0.0 et n'est plus le point d'entrée recommandé.
Cette qualification historique ne s'applique pas à
`API.ExactFiniteMainResults`, qui est stable depuis v2.0.0.

## English

### Conditional API stable since v1.0.0, retained in v2.x

The recommended entry point is:

```lean
import EverettianProbability.API.ConditionalMainResults
```

The conditional-facade declarations, including `ProjectiveBornPremises`,
`OneStepConditionalBornResults`, `TwoStepConditionalBornResults`, and
`conditionalBornMainResults`, have been stable since v1.0.0 and remain
supported in v2.x. Internal proof repairs are not API breaks; implementation
modules are not the external contract.

### Exact-finite API stable since v2.0.0

The recommended entry point is:

```lean
import EverettianProbability.API.ExactFiniteMainResults
```

Its v2.x contract is checked by `Audit/ExactFiniteAPIContract.lean` and
documented in `docs/EXACT_FINITE_API_STABILITY.md`. It covers this facade's
structures, field names, and public theorems. An incompatible break requires
v3.0.0 or a compatibility layer.

### Internal modules are not stable

The `ExactFinite/*`, `Frequency/*`, `Confirmation/*`, and other implementation
modules may evolve without changing either stable public contract. Their
existence is not a stability promise.

### Legacy experimental facade retained

`API.ExactFinitePhysicalRichness` is retained for users predating v2.0.0. It
was the experimental exact-finite facade before v2.0.0 and is no longer the
recommended entry point. This dated historical qualification does not apply to
`API.ExactFiniteMainResults`, which has been stable since v2.0.0.
