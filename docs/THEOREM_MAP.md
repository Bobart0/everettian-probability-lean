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
| Témoin physique (P6a) | `recordNeutral_refines`, `recordNeutral_record_eq`, `recordNeutral_payoff_eq`, `recordNeutral_bornWeight_eq` | `PhysicalRefinement/RecordNeutralWitness.lean` | Couplage unitaire concret `coupleU` dans `H 3` (rotation `(3/5,4/5;4/5,-3/5)` sur un ancilla à deux niveaux), hypothèse nommée `AncillaNotInRecordAlgebra` (`ancillaNotInRecordAlgebra_holds`) | **Témoin schématique** : `H 3` n'a ni factorisation tensorielle explicite système/ancilla, ni dynamique, ni décohérence ; l'algèbre de records y est *stipulée*, non dérivée. Établit une existence, pas une universalité ; brique manquante nommée pour la généraliser : une porte de rotation d'amplitude *contrôlée* (combinant le contrôle à deux sites de `ControlledBitFlip` avec le mélange de `AmplitudeRotation` en amont), à construire et exporter | `[propext, Classical.choice, Quot.sound]` |
| Témoin de non-trivialité (P6a) | `counting_sensitive_to_recordNeutral_refinement`, `counting_underdetermined_by_accessible_record` | `PhysicalRefinement/NonTriviality.lean` | Comptage uniforme restreint aux cellules actives (`activeCells`, `uniformCredence`) sur le même témoin physique | Calcul spécifique au témoin : `1/2 ≠ 1/3` ; ne classifie pas toutes les règles de comptage, seulement celle-ci | `[propext, Classical.choice, Quot.sound]` |
| Corollaire bornien (P6a) | `born_insensitive_to_recordNeutral_refinement`, `born_determined_by_accessible_record` | `PhysicalRefinement/Nonvacuity.lean` | `bornExpectation_pullback_eq` (`Refinement/PayoffPreserving.lean`), même témoin physique | Contraste avec le comptage sur le même témoin ; ne prétend rien au-delà de ce paiement et de cette paire de perspectives | `[propext, Classical.choice, Quot.sound]` |

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
| Physical witness (P6a) | `recordNeutral_refines`, `recordNeutral_record_eq`, `recordNeutral_payoff_eq`, `recordNeutral_bornWeight_eq` | `PhysicalRefinement/RecordNeutralWitness.lean` | Concrete unitary coupling `coupleU` in `H 3` (rotation `(3/5,4/5;4/5,-3/5)` on a two-level ancilla), named hypothesis `AncillaNotInRecordAlgebra` (`ancillaNotInRecordAlgebra_holds`) | **Schematic witness**: `H 3` has no explicit system/ancilla tensor factorization, no dynamics, no decoherence; the record algebra is *stipulated*, not derived. Establishes an existence, not a universality claim; named missing brick to generalize it: a *controlled* amplitude-rotation gate (combining `ControlledBitFlip`'s two-site control with `AmplitudeRotation`'s mixing, upstream), to be built and exported | `[propext, Classical.choice, Quot.sound]` |
| Nontriviality witness (P6a) | `counting_sensitive_to_recordNeutral_refinement`, `counting_underdetermined_by_accessible_record` | `PhysicalRefinement/NonTriviality.lean` | Uniform counting restricted to active cells (`activeCells`, `uniformCredence`) on the same physical witness | Calculation specific to the witness: `1/2 ≠ 1/3`; does not classify every counting rule, only this one | `[propext, Classical.choice, Quot.sound]` |
| Born corollary (P6a) | `born_insensitive_to_recordNeutral_refinement`, `born_determined_by_accessible_record` | `PhysicalRefinement/Nonvacuity.lean` | `bornExpectation_pullback_eq` (`Refinement/PayoffPreserving.lean`), same physical witness | Contrast with counting on the same witness; claims nothing beyond this payoff and this pair of perspectives | `[propext, Classical.choice, Quot.sound]` |

The exact headline statement is:

```lean
theorem born_expectation_of_invariance (F : RationalExpectationFamily n) (hn3 : 3 ≤ n)
    (hinv : RefinementInvariantLocal F.V)
    {v : H n} (hv : ‖v‖ = 1) (hNul : AxNul (canonicalWeight F) v)
    (D : Perspective n) (a : Act n) :
    F.V D a = ∑ c ∈ D.cells, ‖projL c v‖ ^ 2 * a c
```
