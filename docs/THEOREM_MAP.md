# THEOREM_MAP.md

## Français

| Statut | Déclaration | Module | Dépendances directes | Limite de portée | Audit |
|---|---|---|---|---|---|
| Résultat original | `born_expectation_of_invariance` | `BornCalibration/BornExpectation.lean` | **Deux prémisses-ponts** : `RefinementInvariantLocal` (normative pure) et `AxNul (canonicalWeight F) v` (normative-physique — seul point d'entrée de l'état `v`), plus `RationalExpectationFamily`, `‖v‖ = 1`, `3 ≤ n` ; `AxNorm`/`AxPos` sur `canonicalWeight F` sont dérivées, non assumées | Route projective uniquement ; invariance sur **tous** les raffinements projectifs, sans restriction de records ; n'affirme aucune dérivation dynamique des deux prémisses-ponts | `[propext, Classical.choice, Quot.sound]` |
| Théorème de connexion | `refinement_invariant_implies_grain` | `BornCalibration/RefinementImpliesGrain.lean` | Représentation canonique et invariance locale | Même quantification projective non restreinte | `[propext, Classical.choice, Quot.sound]` |
| Théorème de représentation | `represents` | `Preference/Representation.lean` | Affinité, monotonie locale, normalisation | Perspectives finies ; les actes restent totaux | `[propext, Classical.choice, Quot.sound]` |
| Témoin de non-vacuité | `bornExpectation_refinementInvariantLocal` | `Refinement/PayoffPreserving.lean` | Cohérence Grain de Born amont | Montre seulement l'existence d'un habitant de la prémisse | `[propext, Classical.choice, Quot.sound]` |
| Témoin de non-trivialité | `uniform_not_refinementInvariantLocal` | `Refinement/NonTriviality.lean` | Famille uniforme et paire explicite binaire / trois lignes dans `H 3` | Calcul spécifique à `n = 3` : `1 / 2 ≠ 2 / 3` | `[propext, Classical.choice, Quot.sound]` |
| Résultat négatif original | `globalPremise_vacuous` | `Refinement/GlobalPayoffVacuity.lean` | Raffinement vers `{⊤}` | Porte sur l'ancienne lecture globale, explicitement non employée comme prémisse | `[propext, Classical.choice, Quot.sound]` |
| Résultat original | `refinementInvariantLocal_iff_axGrain` | `BornCalibration/RefinementImpliesGrain.lean` | `represents`, `refinement_invariant_implies_grain`, `refinementInvariantLocal_iff_pullback` | Équivalence, pas seulement implication : la prémisse normative est **exactement** `AxGrain` sur `canonicalWeight F`, ni plus forte ni plus faible ; même quantification projective non restreinte | `[propext, Classical.choice, Quot.sound]` |
| Résultat original | `grain_does_not_imply_born_at_two` | `BornCalibration/NonCircularity.lean` | `perspective_two_cases` (structurel, `n = 2`), `skewWeight` et ses quatre propriétés, témoin explicite `witnessState = (3/5, 4/5)` | Spécifique à `n = 2`, où le théorème de Gleason échoue ; ne prétend rien sur `n ≥ 3` (domaine de `grainCoherenceTheorem_projector`) ; le témoin est un exemple, pas une classification de toutes les règles non-boriennes cohérentes sous Grain | `[propext, Classical.choice, Quot.sound]` |
| Témoin de non-trivialité | `maxExpectation_not_affine` | `Preference/NonTriviality.lean` | Perspective binaire explicite dans `H 3` | Calcul spécifique à `n = 3` : `1/2 ≠ 1` ; établit que le maximum sur les cellules ne peut pas compléter une `RationalExpectationFamily`, pas une classification de tous les fonctionnels non affines | `[propext, Classical.choice, Quot.sound]` |

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
| Original result | `born_expectation_of_invariance` | `BornCalibration/BornExpectation.lean` | **Two bridge premises**: `RefinementInvariantLocal` (purely normative) and `AxNul (canonicalWeight F) v` (normative-physical — the only entry point for the state `v`), plus `RationalExpectationFamily`, `‖v‖ = 1`, `3 ≤ n`; `AxNorm`/`AxPos` on `canonicalWeight F` are derived, not assumed | Projective route only; invariance over **all** projective refinements, with no record restriction; it does not dynamically derive either bridge premise | `[propext, Classical.choice, Quot.sound]` |
| Connection theorem | `refinement_invariant_implies_grain` | `BornCalibration/RefinementImpliesGrain.lean` | Canonical representation and local invariance | Same unrestricted projective quantification | `[propext, Classical.choice, Quot.sound]` |
| Representation theorem | `represents` | `Preference/Representation.lean` | Affinity, local monotonicity, normalization | Finite perspectives; acts remain total | `[propext, Classical.choice, Quot.sound]` |
| Nonvacuity witness | `bornExpectation_refinementInvariantLocal` | `Refinement/PayoffPreserving.lean` | Upstream Born Grain coherence | Establishes only that the premise has an inhabitant | `[propext, Classical.choice, Quot.sound]` |
| Nontriviality witness | `uniform_not_refinementInvariantLocal` | `Refinement/NonTriviality.lean` | Uniform family and the explicit binary / three-line pair in `H 3` | Dimension-specific calculation at `n = 3`: `1 / 2 ≠ 2 / 3` | `[propext, Classical.choice, Quot.sound]` |
| Original negative result | `globalPremise_vacuous` | `Refinement/GlobalPayoffVacuity.lean` | Refinement to `{⊤}` | Concerns the former global reading, explicitly not used as a premise | `[propext, Classical.choice, Quot.sound]` |
| Original result | `refinementInvariantLocal_iff_axGrain` | `BornCalibration/RefinementImpliesGrain.lean` | `represents`, `refinement_invariant_implies_grain`, `refinementInvariantLocal_iff_pullback` | Equivalence, not just implication: the normative premise is **exactly** `AxGrain` on `canonicalWeight F`, neither stronger nor weaker; same unrestricted projective quantification | `[propext, Classical.choice, Quot.sound]` |
| Original result | `grain_does_not_imply_born_at_two` | `BornCalibration/NonCircularity.lean` | `perspective_two_cases` (structural, `n = 2`), `skewWeight` and its four properties, explicit witness `witnessState = (3/5, 4/5)` | Specific to `n = 2`, where Gleason's theorem fails; claims nothing about `n ≥ 3` (the domain of `grainCoherenceTheorem_projector`); the witness is one example, not a classification of every non-Born rule coherent under Grain | `[propext, Classical.choice, Quot.sound]` |
| Nontriviality witness | `maxExpectation_not_affine` | `Preference/NonTriviality.lean` | Explicit binary perspective in `H 3` | Dimension-specific calculation at `n = 3`: `1/2 ≠ 1`; establishes that the max over cells cannot complete a `RationalExpectationFamily`, not a classification of every non-affine functional | `[propext, Classical.choice, Quot.sound]` |

The exact headline statement is:

```lean
theorem born_expectation_of_invariance (F : RationalExpectationFamily n) (hn3 : 3 ≤ n)
    (hinv : RefinementInvariantLocal F.V)
    {v : H n} (hv : ‖v‖ = 1) (hNul : AxNul (canonicalWeight F) v)
    (D : Perspective n) (a : Act n) :
    F.V D a = ∑ c ∈ D.cells, ‖projL c v‖ ^ 2 * a c
```
