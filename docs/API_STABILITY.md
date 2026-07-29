# API stability / Stabilité de l'API

## Français

### Stable dans v1.x

Le point d'entrée recommandé et stable est :

```lean
import EverettianProbability.API.ConditionalMainResults
```

Les déclarations stables sont `EverettianProbability.API.Conditional.ProjectiveAct`,
`ProjectiveExpectationFamily`, `ProjectiveBornPremises`, ses méthodes
`canonicalWeight_eq_born`, `canonicalWeight_ne_zero_of_bornWeight_ne_zero`,
`value_eq_bornExpectation`, `canonicalWeight_nonneg`,
`sum_canonicalWeight_eq_one`, `continuatorCredence_eq_bornRatio`,
`continuatorExpectedValue_eq_born`, `sum_continuatorCredence_eq_one`,
`futureDecisionValue_eq_bornTotalExpectation`,
`continuatorCredence_chain_rule`, `sum_intermediateCredence_eq_composite`,
`continuatorExpectedValue_tower` et `admissibleCredence_eq_bornRatio`, ainsi que
`OneStepConditionalBornResults`, `TwoStepConditionalBornResults`,
`oneStepConditionalBornResults`, `twoStepConditionalBornResults` et
`conditionalBornMainResults`.

### Politique de compatibilité

Pendant `v1.x`, aucun de ces noms ne sera renommé et aucun type ne subira de
changement incompatible. Les corrections internes de preuve ne constituent pas
des ruptures, et de nouveaux théorèmes additifs restent permis. Toute rupture
requiert `v2.0.0` ou une façade de compatibilité. Les modules d'implémentation
internes ne sont pas couverts. `API.ExactFinitePhysicalRichness` est
expérimentale et n'est pas couverte par cette garantie.

## English

### Stable in v1.x

The recommended stable entry point is:

```lean
import EverettianProbability.API.ConditionalMainResults
```

The stable declarations are `EverettianProbability.API.Conditional.ProjectiveAct`,
`ProjectiveExpectationFamily`, `ProjectiveBornPremises`, its methods
`canonicalWeight_eq_born`, `canonicalWeight_ne_zero_of_bornWeight_ne_zero`,
`value_eq_bornExpectation`, `canonicalWeight_nonneg`,
`sum_canonicalWeight_eq_one`, `continuatorCredence_eq_bornRatio`,
`continuatorExpectedValue_eq_born`, `sum_continuatorCredence_eq_one`,
`futureDecisionValue_eq_bornTotalExpectation`, `continuatorCredence_chain_rule`,
`sum_intermediateCredence_eq_composite`, `continuatorExpectedValue_tower`, and
`admissibleCredence_eq_bornRatio`, together with
`OneStepConditionalBornResults`, `TwoStepConditionalBornResults`,
`oneStepConditionalBornResults`, `twoStepConditionalBornResults`, and
`conditionalBornMainResults`.

### Compatibility policy

During `v1.x`, none of those names will be renamed and none of their types
will receive an incompatible change. Internal proof repairs are not API
breaks, while additive theorems are allowed. A break requires `v2.0.0` or a
compatibility facade. Internal implementation modules are not covered.
`API.ExactFinitePhysicalRichness` remains experimental and is outside this
guarantee.

## Facade exacte finie experimentale

Le point d'entree recommande est :

```lean
import EverettianProbability.ExactFinite.MainResults
```

`MainResults` est l'agregation scientifique recommandee et `PhysicalAdequacy`
reste la facade detaillee. Cette couche est posterieure a `v1.0.0`, ne recoit
aucune garantie de stabilite `v1.x`, et ses noms peuvent evoluer avant une
future release majeure. Le developpement de cette couche n'autorise aucune
modification de l'API conditionnelle stable : `API.ConditionalMainResults`
reste son point d'entree.

Les résultats expérimentaux EF9 —
`compatibleFineWeight_eq_zero_of_parentWeight_eq_zero`,
`prescribedRatio_eq_zero_of_parentWeight_eq_zero` et
`ExactFiniteNullParentResults` — appartiennent à cette couche non stable.

## Experimental exact-finite facade

The recommended entry point is:

```lean
import EverettianProbability.ExactFinite.MainResults
```

`MainResults` is the recommended scientific aggregation and `PhysicalAdequacy`
remains the detailed facade. This layer postdates `v1.0.0`, has no `v1.x`
stability guarantee, and its names may evolve before a future major release.
Developing this layer does not authorize a change to the stable conditional
API: `API.ConditionalMainResults` remains its entry point.

The experimental EF9 results —
`compatibleFineWeight_eq_zero_of_parentWeight_eq_zero`,
`prescribedRatio_eq_zero_of_parentWeight_eq_zero`, and
`ExactFiniteNullParentResults` — belong to this non-stable layer.
