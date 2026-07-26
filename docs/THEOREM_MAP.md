# THEOREM_MAP.md

## Français

| Statut | Déclaration | Module | Dépendances directes | Limite de portée | Audit |
|---|---|---|---|---|---|
| Résultat original | `born_expectation_of_invariance` | `BornCalibration/BornExpectation.lean` | `RationalExpectationFamily`, `RefinementInvariantLocal`, `AxNul (canonicalWeight F) v`, `‖v‖ = 1`, `3 ≤ n` | Route projective uniquement ; invariance sur **tous** les raffinements projectifs, sans restriction de records ; n'affirme aucune dérivation dynamique de la prémisse normative | `[propext, Classical.choice, Quot.sound]` |
| Théorème de connexion | `refinement_invariant_implies_grain` | `BornCalibration/RefinementImpliesGrain.lean` | Représentation canonique et invariance locale | Même quantification projective non restreinte | `[propext, Classical.choice, Quot.sound]` |
| Théorème de représentation | `represents` | `Preference/Representation.lean` | Affinité, monotonie locale, normalisation | Perspectives finies ; les actes restent totaux | `[propext, Classical.choice, Quot.sound]` |
| Témoin de non-vacuité | `bornExpectation_refinementInvariantLocal` | `Refinement/PayoffPreserving.lean` | Cohérence Grain de Born amont | Montre seulement l'existence d'un habitant de la prémisse | `[propext, Classical.choice, Quot.sound]` |
| Témoin de non-trivialité | `uniform_not_refinementInvariantLocal` | `Refinement/NonTriviality.lean` | Famille uniforme et paire explicite binaire / trois lignes dans `H 3` | Calcul spécifique à `n = 3` : `1 / 2 ≠ 2 / 3` | `[propext, Classical.choice, Quot.sound]` |
| Résultat négatif original | `globalPremise_vacuous` | `Refinement/GlobalPayoffVacuity.lean` | Raffinement vers `{⊤}` | Porte sur l'ancienne lecture globale, explicitement non employée comme prémisse | `[propext, Classical.choice, Quot.sound]` |

L'énoncé principal exact est :

```lean
theorem born_expectation_of_invariance (F : RationalExpectationFamily n) (hn3 : 3 ≤ n)
    (hinv : RefinementInvariantLocal F.V)
    {v : H n} (hv : ‖v‖ = 1) (hNul : AxNul (canonicalWeight F) v)
    (D : Perspective n) (a : Act n) :
    F.V D a = ∑ c ∈ D.cells, ‖projL c v‖ ^ 2 * a c
```

## English

| Status | Declaration | Module | Direct dependencies | Scope limitation | Audit |
|---|---|---|---|---|---|
| Original result | `born_expectation_of_invariance` | `BornCalibration/BornExpectation.lean` | `RationalExpectationFamily`, `RefinementInvariantLocal`, `AxNul (canonicalWeight F) v`, `‖v‖ = 1`, `3 ≤ n` | Projective route only; invariance over **all** projective refinements, with no record restriction; it does not derive the normative premise dynamically | `[propext, Classical.choice, Quot.sound]` |
| Connection theorem | `refinement_invariant_implies_grain` | `BornCalibration/RefinementImpliesGrain.lean` | Canonical representation and local invariance | Same unrestricted projective quantification | `[propext, Classical.choice, Quot.sound]` |
| Representation theorem | `represents` | `Preference/Representation.lean` | Affinity, local monotonicity, normalization | Finite perspectives; acts remain total | `[propext, Classical.choice, Quot.sound]` |
| Nonvacuity witness | `bornExpectation_refinementInvariantLocal` | `Refinement/PayoffPreserving.lean` | Upstream Born Grain coherence | Establishes only that the premise has an inhabitant | `[propext, Classical.choice, Quot.sound]` |
| Nontriviality witness | `uniform_not_refinementInvariantLocal` | `Refinement/NonTriviality.lean` | Uniform family and the explicit binary / three-line pair in `H 3` | Dimension-specific calculation at `n = 3`: `1 / 2 ≠ 2 / 3` | `[propext, Classical.choice, Quot.sound]` |
| Original negative result | `globalPremise_vacuous` | `Refinement/GlobalPayoffVacuity.lean` | Refinement to `{⊤}` | Concerns the former global reading, explicitly not used as a premise | `[propext, Classical.choice, Quot.sound]` |

The exact headline statement is:

```lean
theorem born_expectation_of_invariance (F : RationalExpectationFamily n) (hn3 : 3 ≤ n)
    (hinv : RefinementInvariantLocal F.V)
    {v : H n} (hv : ‖v‖ = 1) (hNul : AxNul (canonicalWeight F) v)
    (D : Perspective n) (a : Act n) :
    F.V D a = ∑ c ∈ D.cells, ‖projL c v‖ ^ 2 * a c
```
