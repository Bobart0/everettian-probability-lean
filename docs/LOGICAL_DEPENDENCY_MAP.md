# Carte des dépendances logiques
# Logical Dependency Map

## Français

Ce document décrit les dépendances internes vérifiées de ce dépôt. Il ne compare pas ces résultats à des dérivations externes et ne transforme aucune prémisse explicite en conséquence de la dynamique unitaire seule.

### A. Calibration projective conditionnelle

La route projective principale prend `ProjectiveBornPremises` : un espace projectif fini, `3 ≤ n`, une famille d'espérance rationnelle, l'invariance locale sous raffinement, un état normalisé et le pont `AxNul`. Lorsqu'il est question de continuateurs, les prémisses sémantiques correspondantes sont elles aussi explicites.

Dans cette couche, le poids canonique est égal au poids de Born, les valeurs sont les espérances de Born, les crédences conditionnelles sont borniennes et les lois diachroniques conditionnelles sont obtenues. C'est ici que la route projective principale identifie Born ; `3 ≤ n` appartient à cette route. Les prémisses normatives demeurent assumées : aucune norme rationnelle n'est dérivée de la dynamique unitaire seule.

### B. Noyau exact fini CORE

La prémisse centrale de `ExactFiniteCoreResults` est uniquement `CompatibleFineWeights r x q`. D'après sa définition, elle comprend déjà la non-négativité de `q` et, pour chaque cellule parent, l'égalité entre la somme des poids fins de sa fibre et `bornRecord present x c`, le record bornien présent. La compatibilité contient donc déjà l'accord des sommes de fibres fines avec ce record.

À partir de cette compatibilité, `ExactFiniteCoreResults` donne la réalisation unitaire exacte, la préservation du record présent, la réalisation des poids futurs compatibles, les rapports physiques prescrits, l'invariance de paiement et l'invariance de l'espérance bornienne exposées par ses champs publics.

CORE ne requiert pas à lui seul `ExactFiniteCalibrationPremises`. Sa portée est donc plus générale en tant que théorème conditionnel de réalisation. Cela ne constitue pas une dérivation de Born sans `3 ≤ n` : Born est déjà présent dans la condition de compatibilité, et le noyau ne dérive pas Born de la dynamique unitaire seule.

### C. Conclusions exactes finies CALIBRATED

`ExactFiniteCalibratedResults` ajoute à `CompatibleFineWeights` les `ExactFiniteCalibrationPremises` : une famille d'espérance rationnelle, `dim_ge_three : 3 ≤ n`, l'invariance locale, la normalisation de la source et le support nul de la cible. Pour une cellule parent de poids non nul, il conclut que la crédence des continuateurs est le rapport prescrit, que ces crédences sont normalisées et que le poids fin est récupéré à partir du poids parent et du rapport conditionnel.

Les conclusions de crédence réintroduisent donc explicitement les prémisses de calibration ; elles ne suivent pas de CORE seul.

### D. Route qubit / effets

Le dépôt établit une route par effets pour `n ≥ 1`, y compris le qubit, lorsque l'effet de chaque sortie considérée est une projection orthogonale. Elle ne couvre pas les effets POVM authentiquement non projectifs. Grain seul en dimension deux ne suffit pas ; la route par effets ajoute une structure supplémentaire. Aucune comparaison de portée avec un théorème externe n'est revendiquée ici.

### E. P10 — fréquences et typicalité

```text
poids quadratiques déjà calibrés → masses de fréquence → normalisation
→ moments et variance → borne de Chebyshev → seuil de typicalité
```

P10 n'est pas une dérivation indépendante de Born et ne fournit pas une contrainte supplémentaire sélectionnant Born. C'est un résultat aval conditionnel, pas une simple reformulation : il contient ses propres constructions et bornes.

### F. P11 — confirmation bayésienne

```text
masses P10 déjà obtenues + priors + factorisation conditionnelle + non-nullités
→ vraisemblances → postérieurs → cotes → cohérence lot/itération
```

P11 ne justifie pas indépendamment les vraisemblances de Born et ne dérive pas Born. Il ne prouve ni qu'une hypothèse est vraie, ni la consistance postérieure, ni une convergence asymptotique. P11 est un résultat aval conditionnel.

### G. Ce que signifie « une même mesure »

La pondération identifiée comme bornienne dans la couche de calibration est ensuite celle qui détermine les masses de fréquence utilisées par P10, lesquelles servent de vraisemblances dans P11.

Cette formulation n'autorise pas à dire que P10 dérive indépendamment Born, que P11 justifie indépendamment Born, que trois routes indépendantes convergent vers Born, ni que la dynamique unitaire seule impose la probabilité épistémique.

## English

This document describes the verified internal dependencies of this repository. It does not compare these results with external derivations and does not turn an explicit premise into a consequence of unitary dynamics alone.

### A. Conditional projective calibration

The main projective route takes `ProjectiveBornPremises`: a finite projective space, `3 ≤ n`, a rational expectation family, local refinement invariance, a normalized state, and the `AxNul` bridge. Whenever continuators are discussed, the corresponding semantic premises are explicit as well.

In this layer the canonical weight equals the Born weight, values equal Born expectations, conditional credences are Born credences, and conditional diachronic laws follow. This is where the main projective route identifies Born; `3 ≤ n` belongs to this route. The normative premises remain assumed: no rational norm is derived from unitary dynamics alone.

### B. Exact-finite CORE

The central premise of `ExactFiniteCoreResults` is only `CompatibleFineWeights r x q`. By definition it already includes non-negativity of `q` and, for every parent cell, equality between the sum of its fine-fibre weights and `bornRecord present x c`, the present Born record. Compatibility therefore already contains agreement of fine-fibre sums with the present Born record.

From compatibility, `ExactFiniteCoreResults` gives exact unitary realization, preservation of the present record, realization of compatible future weights, prescribed physical ratios, payoff invariance, and the Born-expectation invariance exposed by its public fields.

CORE does not itself require `ExactFiniteCalibrationPremises`. It therefore has a more general scope as a conditional realization theorem. This is not a Born derivation without `3 ≤ n`: Born is already present in the compatibility condition, and the core does not derive Born from unitary dynamics alone.

### C. CALIBRATED exact-finite conclusions

`ExactFiniteCalibratedResults` adds `ExactFiniteCalibrationPremises` to `CompatibleFineWeights`: a rational expectation family, `dim_ge_three : 3 ≤ n`, local invariance, source normalization, and target null support. For a nonzero-weight parent cell, it concludes that continuator credence equals the prescribed ratio, that those credences are normalized, and that the fine weight is recovered from the parent weight and conditional ratio.

The credence conclusions therefore explicitly reintroduce calibration premises; they do not follow from CORE alone.

### D. Qubit / effect route

The repository establishes an effect route for `n ≥ 1`, including the qubit, when every outcome considered has an orthogonal-projector effect. It does not cover genuinely non-projective POVM effects. Grain alone in dimension two is insufficient; the effect route adds extra structure. No comparison of scope with an external theorem is claimed here.

### E. P10 — frequency and typicality

```text
already calibrated quadratic weights → frequency masses → normalization
→ moments and variance → Chebyshev bound → typicality threshold
```

P10 is not an independent derivation of Born and supplies no additional constraint selecting Born. It is a conditional downstream result, not a mere restatement: it contains its own constructions and bounds.

### F. P11 — Bayesian confirmation

```text
already obtained P10 masses + priors + conditional factorization + nonzero assumptions
→ likelihoods → posteriors → odds → batch/iteration coherence
```

P11 does not independently justify Born likelihoods and does not derive Born. It proves neither a true hypothesis, posterior consistency, nor asymptotic convergence. P11 is a conditional downstream result.

### G. What “one measure” means

The weighting identified as Born in the calibration layer is then the one that determines the frequency masses used by P10, which serve as likelihoods in P11.

This wording does not permit claims that P10 independently derives Born, P11 independently justifies Born, three independent routes converge on Born, or unitary dynamics alone imposes epistemic probability.
