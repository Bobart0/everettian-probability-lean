# Portée exacte du résultat conditionnel de Born

## Français

### Statut

Le résultat formel conditionnel est clos dans sa portée projective finie et
explicitement conditionnelle. `SORRY_BUDGET = 0`. La façade stable est :

```lean
import EverettianProbability.API.ConditionalMainResults
```

Le théorème agrégé principal est
`EverettianProbability.API.Conditional.conditionalBornMainResults`.

### Prémisses exactes

`ProjectiveBornPremises` contient `F : ProjectiveExpectationFamily n`,
`state : H n`, `dim_ge_three : 3 ≤ n`,
`refinement_invariant : RefinementInvariantLocal F.V`,
`normalized : ‖state‖ = 1`, et `null_support : AxNul (...) state`.

**MATH** : géométrie hilbertienne complexe finie, perspectives projectives,
`3 ≤ n`, et le théorème amont Grain/Gleason. **NORM** :
`RationalExpectationFamily`, affinité, monotonie, normalisation des
constantes et invariance locale sous raffinement. **PHYS–NORM bridge** :
`AxNul` pour l'état spécifié. **SEM** : les cellules futures d'une fibre sont
interprétées comme des continuateurs.

### Conclusions exactes

Le poids canonique est le poids de Born et la valeur de tout acte son
espérance de Born. La crédence envers un continuateur est le rapport bornien
conditionnel; elle est normalisée sur chaque fibre de poids non nul. Sont aussi
établies l'espérance conditionnelle d'actes futurs, l'espérance totale
diachronique, la règle de chaîne, sa forme sommée, la loi de la tour et
l'unicité pour toute famille de crédences satisfaisant les prémisses
d'admissibilité explicites.

### Cas de poids parent nul

Les résultats normalisés exigent que le poids du parent soit non nul. Les
valeurs totalisées par une division réelle à zéro ne sont pas présentées comme
une probabilité conditionnelle physiquement unique d'un événement de poids nul.

### Ce qui n'est pas démontré

Aucune norme rationnelle n'est dérivée de la dynamique unitaire :
`RefinementInvariantLocal` et `AxNul` restent des prémisses. Le dépôt ne donne
ni théorie complète de l'identité personnelle, ni dérivation philosophique de
l'incertitude personnelle, ni décohérence approximative, Hamiltonien local
naturel, dynamique microscopique réaliste générale, extension projective
directe au qubit, dimension infinie, POVM arbitraire, unicité de la réalisation
physique exacte, ni règlement définitif du débat everettien.

`dim_ge_three` n'est pas une clause de confort dans `ProjectiveBornPremises` :
`BornCalibration/NonCircularity.lean` (`grain_does_not_imply_born_at_two`,
niveau poids) et `BornCalibration/DecisionNonCircularity.lean`
(`decision_premises_do_not_imply_born_at_two`, niveau décision, formulé
directement sur les mêmes prémisses que `born_expectation_of_invariance`)
montrent chacun un contre-modèle explicite en `n = 2` satisfaisant toutes les
autres prémisses. Le regroupement de ces prémisses dans `ProjectiveBornPremises`
est un choix d'API ; aucun de ses champs n'est affirmé irréductible, et les
deux contre-modèles ci-dessus reposent précisément sur les arguments séparés
au niveau théorème, pas sur la structure empaquetée.

### Relation avec la couche exacte finie

Depuis v2.0.0, le point d'entrée stable de la couche exacte finie est
`EverettianProbability.API.ExactFiniteMainResults`. L'ancienne façade
`API.ExactFinitePhysicalRichness` reste disponible mais n'est pas le point
d'entrée recommandé. La façade exacte finie n'est pas importée par
`ConditionalMainResults.lean` : les deux contrats restent séparés.

Dans cette couche, CORE assume `CompatibleFineWeights`, donc déjà la
compatibilité des sommes de fibres avec le record bornien présent. CALIBRATED
ajoute les prémisses explicites de calibration. Ces précisions ne changent
aucune conclusion du résultat conditionnel.

# Exact Scope of the Conditional Born Result

## English

### Status

The conditional formal result is closed in its finite-projective and explicitly
conditional scope. `SORRY_BUDGET = 0`. The stable facade is:

```lean
import EverettianProbability.API.ConditionalMainResults
```

The main aggregate theorem is
`EverettianProbability.API.Conditional.conditionalBornMainResults`.

### Exact premises

`ProjectiveBornPremises` contains `F : ProjectiveExpectationFamily n`,
`state : H n`, `dim_ge_three : 3 ≤ n`,
`refinement_invariant : RefinementInvariantLocal F.V`,
`normalized : ‖state‖ = 1`, and `null_support : AxNul (...) state`.

**MATH**: finite complex Hilbert geometry, projective perspectives, `3 ≤ n`,
and the upstream Grain/Gleason theorem. **NORM**: `RationalExpectationFamily`,
affinity, monotonicity, constant normalization, and local refinement
invariance. **PHYS–NORM bridge**: `AxNul` for the specified state. **SEM**:
future cells in a fibre are interpreted as continuators.

### Exact conclusions

Canonical weight is Born weight and every act's value is its Born expectation.
Credence over a continuator is the conditional Born ratio and is normalized on
each nonzero-weight fibre. The development also proves conditional future-act
expectation, diachronic total expectation, the chain rule and its summed form,
the tower law, and uniqueness for every credence family satisfying the stated
admissibility premises.

### Zero parent weight

Normalized results require nonzero parent weight. Totalized real-division-by-
zero values are not presented as a physically unique conditional probability
on a zero-weight event.

### What is not proved

No rational norm is derived from unitary dynamics: `RefinementInvariantLocal`
and `AxNul` remain premises. There is no complete personal-identity theory,
philosophical derivation of personal uncertainty, approximate decoherence,
natural local Hamiltonian, general realistic microscopic dynamics, direct
projective qubit extension, infinite dimension, arbitrary POVM effect,
uniqueness of exact physical realization, or final settlement of the Everett
debate.

`dim_ge_three` is not a convenience clause in `ProjectiveBornPremises`:
`BornCalibration/NonCircularity.lean` (`grain_does_not_imply_born_at_two`,
weight level) and `BornCalibration/DecisionNonCircularity.lean`
(`decision_premises_do_not_imply_born_at_two`, decision level, stated
directly on the same premises as `born_expectation_of_invariance`) each
exhibit an explicit countermodel at `n = 2` satisfying every other premise.
Bundling these premises into `ProjectiveBornPremises` is an API choice; none
of its fields is claimed irreducible, and both countermodels above rely
precisely on the separate theorem-level arguments, not on the bundled
structure.

### Relation to the exact finite layer

Since v2.0.0, the stable entry point for the exact-finite layer is
`EverettianProbability.API.ExactFiniteMainResults`. The legacy
`API.ExactFinitePhysicalRichness` facade remains available but is not the
recommended entry point. The exact-finite facade is not imported by
`ConditionalMainResults.lean`: the two contracts remain separate.

Within that layer, CORE assumes `CompatibleFineWeights`, hence already the
compatibility of fibre sums with the present Born record. CALIBRATED adds the
explicit calibration premises. These clarifications change none of the
conditional result's mathematical conclusions.
