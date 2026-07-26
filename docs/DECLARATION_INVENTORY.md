# DECLARATION_INVENTORY.md

> Une ligne par déclaration publique (non `private`, non anonyme) du dépôt.
> Les déclarations `private` sont des pas de calcul internes ; elles sont
> omises ici mais aucune n'a été laissée sans lecture — voir la note de bas
> de tableau par fichier quand leur omission mérite d'être signalée. Les
> `example` anonymes (non nommés) ne sont pas des déclarations publiques
> au sens strict ; les deux qui portent un rôle de témoin sont listées en
> note à la fin de chaque langue.
>
> One line per public declaration (non-`private`, non-anonymous) in the
> repository. `private` declarations are internal computation steps; they
> are omitted here, but none went unread — see the per-file footnote when
> an omission is worth flagging. Anonymous `example`s are not public
> declarations in the strict sense; the two that carry a witness role are
> listed in a note at the end of each language section.

## Français

Catégories : *résultat original*, *théorème de connexion*, *témoin de
non-vacuité*, *témoin de non-trivialité*, *résultat négatif*, *API
auxiliaire*, *définition*.

### `Core/Interface.lean` (namespace `EverettianProbability.Abstract`)

| Déclaration | Fichier | Ce qu'elle affirme | Hypothèses | Portée / limitations | Catégorie |
|---|---|---|---|---|---|
| `PerspectiveInterface` | Core/Interface.lean | Regroupe, en une classe, les données minimales d'un modèle de perspectives finies : cellules, sortie, raffinement, carte parent, règle d'estimation. | Univers `uP,uO,uC,uR,uE` libres. | Interface P0.3 ; ne préjuge d'aucun contenu physique. | définition |
| `cellFintypeInstance`, `cellDecidableEqInstance` | Core/Interface.lean | Rendent les cellules d'une perspective `Fintype`/`DecidableEq` à partir des champs de l'interface. | — | Instances techniques. | API auxiliaire |
| `Act` (abbrev) | Core/Interface.lean | Un acte abstrait est une fonction totale sur l'espace de sortie ambiant. | — | — | définition |
| `AgreeOn` | Core/Interface.lean | Deux actes abstraits coïncident sur toutes les cellules d'une perspective. | — | — | définition |
| `pullbackAct` | Core/Interface.lean | Tiré-en-arrière abstrait : composition avec la carte parent totale. | — | — | définition |
| `pullbackAct_refl_agree` | Core/Interface.lean | Le tiré-en-arrière par la réflexivité coïncide avec l'acte d'origine sur les cellules. | — | Prouvé. | résultat original |
| `pullbackAct_trans_agree` | Core/Interface.lean | Le tiré-en-arrière respecte la composition des raffinements, sur les cellules de la perspective la plus fine. | — | Prouvé. | résultat original |
| `Grain` | Core/Interface.lean | Cohérence de raffinement abstraite d'une règle d'estimation : le poids d'une cellule grossière est la somme des poids de sa fibre fine. | — | Définition, pas un fait physique. | définition |
| `expectation` | Core/Interface.lean | Espérance abstraite d'un acte : somme pondérée sur les cellules d'une perspective. | — | — | définition |
| `RefinementInvariant` | Core/Interface.lean | Une fonctionnelle d'espérance abstraite est invariante par tiré-en-arrière sur tout raffinement. | — | Forme *globale*, quantifiée sur tous les actes, pas la forme locale utilisée ailleurs dans le dépôt. | définition |
| `expectation_refinementInvariant` | Core/Interface.lean | Pont mesure→fonctionnelle au niveau abstrait : la cohérence Grain d'une règle rend son espérance invariante par raffinement. | `Grain I E`. | Prouvé, entièrement abstrait. | théorème de connexion |
| `Projective.interface` | Core/Interface.lean | Instance projective de `PerspectiveInterface` : cellules = sous-espaces d'une `Perspective n`, sortie = `Submodule ℂ (H n)`. | — | Instance projective. | définition |
| `Projective.interface_weight_apply`, `Projective.interface_parentCell_apply` | Core/Interface.lean | Lemmes de simplification pour l'instance projective. | — | — | API auxiliaire |
| `Projective.grain_of_axGrain` | Core/Interface.lean | La condition `AxGrain` amont (côté projectif) est exactement la cohérence `Grain` abstraite pour cette instance. | `AxGrain E`. | Prouvé. | théorème de connexion |
| `Projective.born_refinementInvariant` | Core/Interface.lean | Le poids bornien `E₀ v` fournit une règle d'estimation projective non vide dont l'espérance abstraite est invariante par raffinement. | — | Instancie `expectation_refinementInvariant` ; ne porte aucune hypothèse de dimension. | témoin de non-vacuité |
| `Effects.interface` | Core/Interface.lean | Instance effets de `PerspectiveInterface` : cellules = `Fin D.outcomes`, sortie = `ℕ`. | — | Instance effets. | définition |
| `Effects.estimationRule_grain` | Core/Interface.lean | Toute règle d'estimation amont côté effets satisfait la cohérence `Grain` abstraite. | — | Prouvé ; la structure amont `EstimationRule` porte `grain` comme champ, donc ce fait est quasi immédiat. | théorème de connexion |
| `Effects.pureState_refinementInvariant` | Core/Interface.lean | La règle d'état pur amont donne une espérance abstraite invariante par raffinement côté effets. | `‖v‖ = 1`. | Part d'une règle qui satisfait déjà Grain *par construction* — ne dérive rien d'une prémisse normative (voir `docs/QUBIT_FEASIBILITY_REPORT.md`, section 1). | témoin de non-vacuité |

### `Core/Act.lean` (namespace `EverettianProbability.Core`)

| Déclaration | Fichier | Ce qu'elle affirme | Hypothèses | Portée / limitations | Catégorie |
|---|---|---|---|---|---|
| `Act n` | Core/Act.lean | Un acte est une fonction totale `Submodule ℂ (H n) → ℝ` ; les valeurs hors perspective sont poubelle. | — | — | définition |
| `Act.AgreeOn` | Core/Act.lean | Deux actes coïncident sur toutes les cellules d'une perspective `D`. | — | — | définition |
| `Act.const`, `Act.indicator`, `Act.add`, `Act.PointwiseLE`, `Act.convComb`, `Act.indicatorExpansion` | Core/Act.lean | Opérations ponctuelles sur les actes (constante, indicatrice, somme, ordre, combinaison convexe, expansion en indicatrices). | — | — | définition |
| `Act.agreeOn_refl`, `Act.agreeOn_symm`, `Act.agreeOn_trans` | Core/Act.lean | `AgreeOn D` est une relation d'équivalence. | — | Prouvé. | API auxiliaire |
| `Act.agreeOn_add`, `Act.agreeOn_convComb` | Core/Act.lean | `AgreeOn` est stable par somme ponctuelle et combinaison convexe. | — | Prouvé. | API auxiliaire |
| `Act.indicator_self`, `Act.indicator_of_ne` | Core/Act.lean | Valeurs de l'indicatrice sur sa propre cellule et sur une cellule distincte. | — | Prouvé. | API auxiliaire |
| `Act.agreeOn_indicatorExpansion` | Core/Act.lean | Sur `D`, tout acte coïncide avec son expansion finie en indicatrices de cellules. | — | Prouvé. | résultat original |

### `Core/Nonvacuity.lean`

| Déclaration | Fichier | Ce qu'elle affirme | Hypothèses | Portée / limitations | Catégorie |
|---|---|---|---|---|---|
| `exampleLine` | Core/Nonvacuity.lean | Une ligne concrète non nulle et propre de `H 3` (premier vecteur de base). | — | Fixe `n = 3`. | définition |
| `exampleLine_ne_bot`, `exampleLine_ne_top` | Core/Nonvacuity.lean | `exampleLine` est non nulle et propre. | — | Réutilise `line_ne_bot`/`line_ne_top` amont. | API auxiliaire |
| `exampleCoarse` | Core/Nonvacuity.lean | Perspective grossière concrète : la scission binaire `{exampleLine, exampleLineᗮ}`. | — | — | définition |
| `exampleFine` | Core/Nonvacuity.lean | Raffinement concret de `exampleCoarse`, via la construction amont `refinePerspective`. | — | Réutilise l'infrastructure amont, ne la reconstruit pas. | définition |
| `exampleFine_refines` | Core/Nonvacuity.lean | `exampleFine` raffine bien `exampleCoarse`, strictement (pas la réflexivité triviale). | — | Prouvé. | témoin de non-vacuité |
| `exampleAct` | Core/Nonvacuity.lean | Acte concret : l'indicatrice de `exampleLine`. | — | — | définition |
| `exampleLine_mem_exampleCoarse` | Core/Nonvacuity.lean | `exampleLine` est bien une cellule de `exampleCoarse`. | — | Prouvé. | API auxiliaire |
| `exampleAct_at_exampleLine`, `exampleConst_at_exampleLine` | Core/Nonvacuity.lean | Valeurs concrètes de `exampleAct` et de l'acte constant sur `exampleLine`. | — | Prouvé. | API auxiliaire |

**Note.** Le docstring de ce fichier (lignes 57–61) affirme que `parent_mem`, `parent_le`, `parent_unique` « sont encore des buts ouverts dans `Core/Parent.lean` ». Ce fichier n'existe pas : `ARCHITECTURE_NOTES.md` («Actes, carte parent et interface P0.3») confirme explicitement que `Core/Parent.lean` **a été supprimé** et que tous les tirés-en-arrière utilisent désormais `parentOf` amont. Le docstring n'a pas été mis à jour depuis cette suppression — référence morte, décrite en détail dans le rapport de session.

### `Refinement/PullbackAct.lean`

| Déclaration | Fichier | Ce qu'elle affirme | Hypothèses | Portée / limitations | Catégorie |
|---|---|---|---|---|---|
| `pullbackAct` | Refinement/PullbackAct.lean | Tiré-en-arrière d'un acte le long d'un raffinement : `a ∘ parentOf r`. | — | — | définition |
| `fiberIndicator` | Refinement/PullbackAct.lean | Indicatrice de la fibre de `parentOf r` au-dessus d'une cellule. | — | — | définition |
| `pullbackAct_const` | Refinement/PullbackAct.lean | Le tiré-en-arrière d'un acte constant est le même acte constant. | — | Prouvé (`rfl`). | API auxiliaire |
| `pullbackAct_agree_of_agree` | Refinement/PullbackAct.lean | Si deux actes coïncident sur `D`, leurs tirés-en-arrière coïncident sur `D'`. | — | Prouvé. | API auxiliaire |
| `pullbackAct_refl_agree` | Refinement/PullbackAct.lean | Le tiré-en-arrière par un raffinement réflexif est l'identité sur les cellules. | — | Prouvé. | API auxiliaire |
| `pullbackAct_trans_agree` | Refinement/PullbackAct.lean | Le tiré-en-arrière est compatible avec la composition transitive, sur les cellules fines. | — | Prouvé. | API auxiliaire |
| `pullbackAct_indicator` | Refinement/PullbackAct.lean | Le tiré-en-arrière d'une indicatrice est exactement l'indicatrice de sa fibre parent. | — | Prouvé (`rfl`). | API auxiliaire |
| `pullbackAct_indicator_eq_one_iff` | Refinement/PullbackAct.lean | Sur les cellules fines, l'indicatrice tirée en arrière vaut `1` exactement sur la fibre `coarseCells` amont. | `c ∈ D.cells`, `c' ∈ D'.cells`. | Prouvé. | API auxiliaire |

### `Refinement/PayoffPreserving.lean`

| Déclaration | Fichier | Ce qu'elle affirme | Hypothèses | Portée / limitations | Catégorie |
|---|---|---|---|---|---|
| `PayoffEquivalentAt` | Refinement/PayoffPreserving.lean | Deux descriptions attribuent les mêmes conséquences à chaque branche fine d'un raffinement donné. | — | Prémisse normative, pas un fait dynamique. | définition |
| `RefinementInvariant` | Refinement/PayoffPreserving.lean | Une famille d'espérance est invariante : évaluer un acte grossier ou son tiré-en-arrière donne la même valeur, pour **tout** raffinement et **tout** acte. | — | Forme globale (non filtrée par `PayoffEquivalentAt`). | définition `PREMISE` |
| `RefinementInvariantLocal` | Refinement/PayoffPreserving.lean | Version locale : l'invariance n'est requise qu'entre descriptions localement équivalentes (`PayoffEquivalentAt`). | — | C'est la prémisse effectivement adoptée par le théorème principal. | définition `PREMISE` |
| `refinementInvariantLocal_iff_pullback` | Refinement/PayoffPreserving.lean | Pour une famille rationnelle, la forme locale équivaut à l'invariance évaluée sur le tiré-en-arrière canonique. | `F : RationalExpectationFamily n`. | Prouvé. | résultat original |
| `bornExpectation` | Refinement/PayoffPreserving.lean | Espérance bornienne d'un acte dans l'état `v` : `∑ c ∈ D.cells, ‖projL c v‖² * a c`. | — | — | définition |
| `bornExpectation_pullback_eq` | Refinement/PayoffPreserving.lean | L'espérance bornienne est invariante par tiré-en-arrière projectif arbitraire. | — | Prouvé, pour tout `v`, tout raffinement. | résultat original |
| `bornExpectation_refinementInvariant` | Refinement/PayoffPreserving.lean | Corollaire : l'espérance bornienne satisfait la forme globale `RefinementInvariant`. | — | Prouvé. | témoin de non-vacuité |
| `bornExpectation_refinementInvariantLocal` | Refinement/PayoffPreserving.lean | Corollaire : l'espérance bornienne satisfait la forme locale `RefinementInvariantLocal`. | — | Prouvé ; c'est le témoin positif nommé de la prémisse principale. | témoin de non-vacuité |

### `Refinement/GlobalPayoffVacuity.lean`

| Déclaration | Fichier | Ce qu'elle affirme | Hypothèses | Portée / limitations | Catégorie |
|---|---|---|---|---|---|
| `GloballyPayoffPreserving` | Refinement/GlobalPayoffVacuity.lean | Ancienne lecture globale : un acte coïncide avec son propre tiré-en-arrière pour **tout** raffinement. | — | Explicitement conservée seulement pour établir sa vacuité ; ne doit jamais servir de prémisse. | définition (résultat négatif) |
| `singletonTopPerspective` | Refinement/GlobalPayoffVacuity.lean | La perspective singleton explicite `{⊤}`, en dimension non nulle. | `0 < n`. | — | définition |
| `globallyPayoffPreserving_const` | Refinement/GlobalPayoffVacuity.lean | Un acte globalement préservant est constant sur toutes les cellules de toutes les perspectives accessibles. | `0 < n`. | Prouvé. | résultat négatif |
| `not_globallyPayoffPreserving_indicator` | Refinement/GlobalPayoffVacuity.lean | Sur une fibre propre, l'indicatrice du parent n'est pas globalement préservante. | `c' ≤ c`, `c' ≠ c`, `c' ∈ D'.cells`, `c ∈ D.cells`. | Prouvé ; c'est le témoin négatif de `GloballyPayoffPreserving`. | témoin de non-trivialité |
| `globalPremise_vacuous` | Refinement/GlobalPayoffVacuity.lean | Toute famille rationnelle satisfait automatiquement l'invariance filtrée par `GloballyPayoffPreserving`. | `F : RationalExpectationFamily n`. | Prouvé ; établit la vacuité — la prémisse ne discrimine aucune famille rationnelle. | résultat négatif |
| `uniformExpectationFamily_globalPremise_vacuous` | Refinement/GlobalPayoffVacuity.lean | Témoin nommé : la famille uniforme satisfait la prémisse globale filtrée tout en violant `AxGrain`. | Fixé à `n = 3`. | Prouvé (conjonction de deux faits). | témoin de non-vacuité (négatif pour Grain) |

### `Refinement/Nonvacuity.lean`

| Déclaration | Fichier | Ce qu'elle affirme | Hypothèses | Portée / limitations | Catégorie |
|---|---|---|---|---|---|
| `const_payoffEquivalentAt` | Refinement/Nonvacuity.lean | Deux actes constants identiques sont localement équivalents pour tout raffinement. | — | Prouvé. | témoin de non-vacuité |
| `exampleState` | Refinement/Nonvacuity.lean | Premier vecteur de base standard de `H 3`, comme état concret. | — | — | définition |
| `exampleState_norm` | Refinement/Nonvacuity.lean | `exampleState` est de norme 1. | — | Prouvé. | API auxiliaire |
| `exampleBorn_refinementInvariant` | Refinement/Nonvacuity.lean | Instance concrète de `bornExpectation_refinementInvariantLocal` en `exampleState`. | — | Prouvé. | témoin de non-vacuité |
| `exampleBornExpectation_values` | Refinement/Nonvacuity.lean | Valeurs calculées de l'espérance bornienne sur `exampleFine`/`exampleCoarse` : `1` des deux côtés du raffinement concret. | — | Prouvé. | témoin de non-vacuité |

### `Refinement/NonTriviality.lean`

| Déclaration | Fichier | Ce qu'elle affirme | Hypothèses | Portée / limitations | Catégorie |
|---|---|---|---|---|---|
| `uniform_not_refinementInvariantLocal` | Refinement/NonTriviality.lean | La famille d'espérance uniforme ne satisfait pas `RefinementInvariantLocal` : calcul concret `1/2 ≠ 2/3` sur la cellule complémentaire de la paire binaire/trois-lignes en `H 3`. | Fixé à `n = 3`. | Prouvé ; **spécifique** à cette paire de perspectives et à cet acte — ne classifie aucune autre règle rivale ni aucune autre paire. | témoin de non-trivialité |

### `Preference/ExpectationFunctional.lean`

| Déclaration | Fichier | Ce qu'elle affirme | Hypothèses | Portée / limitations | Catégorie |
|---|---|---|---|---|---|
| `RationalExpectationFamily` | Preference/ExpectationFunctional.lean | Structure regroupant, par perspective, une fonctionnelle d'espérance affine, monotone, normalisée sur les constantes. | — | L'affinité est une hypothèse substantielle, pas neutre (voir chasse à la surinterprétation, point 8). | définition `PREMISE` |
| `V_congr_of_agreeOn` | Preference/ExpectationFunctional.lean | La monotonie locale force `F.V D` à ne dépendre que des valeurs de l'acte sur `D.cells`. | `F : RationalExpectationFamily n`, `Act.AgreeOn D a b`. | Prouvé. | résultat original |

### `Preference/Representation.lean`

| Déclaration | Fichier | Ce qu'elle affirme | Hypothèses | Portée / limitations | Catégorie |
|---|---|---|---|---|---|
| `represents` | Preference/Representation.lean | Toute fonctionnelle rationnelle est la somme finie pondérée par son poids canonique sur les cellules. | `F : RationalExpectationFamily n`. | Prouvé. | résultat original |
| `weights_unique_on_cells` | Preference/Representation.lean | Tout autre système de poids représentant `F.V D` coïncide avec le poids canonique **sur les cellules** (pas hors cellules). | `∀ a, F.V D a = ∑ c ∈ D.cells, p c * a c`. | Prouvé ; l'unicité est explicitement restreinte à `D.cells` — c'est la correction du défaut P3 documenté dans `ARCHITECTURE_NOTES.md`. | résultat original |
| `canonicalWeight_axPos` | Preference/Representation.lean | La positivité du poids canonique est **dérivée** de la monotonie locale, non assumée. | `F : RationalExpectationFamily n`. | Prouvé. | résultat original |
| `canonicalWeight_axNorm` | Preference/Representation.lean | La normalisation du poids canonique est **dérivée** de la normalisation des actes constants, non assumée. | `F : RationalExpectationFamily n`. | Prouvé. | résultat original |

### `Preference/Nonvacuity.lean`

| Déclaration | Fichier | Ce qu'elle affirme | Hypothèses | Portée / limitations | Catégorie |
|---|---|---|---|---|---|
| `top_ne_bot_H3`, `cells_nonempty` | Preference/Nonvacuity.lean | `H 3` est non triviale ; toute perspective sur `H 3` a au moins une cellule. | Fixé à `n = 3`. | Prouvé. | API auxiliaire |
| `uniformExpectation` | Preference/Nonvacuity.lean | Moyenne uniforme d'un acte sur les cellules d'une perspective. | Fixé à `n = 3`. | Règle délibérément dégénérée (comptage, pas Born) pour rester non circulaire. | définition |
| `uniformExpectation_affine`, `uniformExpectation_monotone`, `uniformExpectation_normalized_const` | Preference/Nonvacuity.lean | `uniformExpectation` satisfait les trois axiomes de `RationalExpectationFamily`. | Fixé à `n = 3`. | Prouvé en entier. | témoin de non-vacuité |
| `uniformExpectationFamily` | Preference/Nonvacuity.lean | Le témoin concret : `uniformExpectation` empaqueté en `RationalExpectationFamily 3`. | Fixé à `n = 3`. | Prouvé. | témoin de non-vacuité |

### `Preference/NonTriviality.lean`

| Déclaration | Fichier | Ce qu'elle affirme | Hypothèses | Portée / limitations | Catégorie |
|---|---|---|---|---|---|
| `maxExpectation` | Preference/NonTriviality.lean | Maximum d'un acte sur les cellules d'une perspective, à `n = 3` fixé. | Fixé à `n = 3`. | Bien définie (`D.cells` non vide). | définition |
| `maxExpectation_monotone`, `maxExpectation_normalized_const` | Preference/NonTriviality.lean | `maxExpectation` est monotone et normalisée sur les constantes. | Fixé à `n = 3`. | Prouvé. | API auxiliaire |
| `maxExpectation_not_affine` | Preference/NonTriviality.lean | `maxExpectation` viole l'affinité (`1/2 ≠ 1` sur la perspective binaire explicite), malgré monotonie et normalisation. | Fixé à `n = 3`. | Prouvé ; **spécifique** à cette perspective, ne classifie pas tous les fonctionnels non affines (théories de rang, Quiggin/Yaari, restent seulement *illustrées*, pas couvertes). | témoin de non-trivialité |

### `BornCalibration/ContextualWeight.lean`

| Déclaration | Fichier | Ce qu'elle affirme | Hypothèses | Portée / limitations | Catégorie |
|---|---|---|---|---|---|
| `canonicalWeight` | BornCalibration/ContextualWeight.lean | Poids contextuel canonique : valeur de l'acte indicateur, nul hors des cellules. | — | Définition, pas un choix de représentant. | définition |
| `canonicalWeight_zero_outside` | BornCalibration/ContextualWeight.lean | Le poids canonique est nul hors des cellules de la perspective. | `c ∉ D.cells`. | Prouvé. | API auxiliaire |

### `BornCalibration/RefinementImpliesGrain.lean`

| Déclaration | Fichier | Ce qu'elle affirme | Hypothèses | Portée / limitations | Catégorie |
|---|---|---|---|---|---|
| `refinement_invariant_implies_grain` | BornCalibration/RefinementImpliesGrain.lean | L'invariance locale sous tous les raffinements force `AxGrain` pour le poids canonique. | `F : RationalExpectationFamily n`, `RefinementInvariantLocal F.V`. | Prouvé ; quantification projective **non restreinte** (tous les raffinements). | résultat original |
| `refinementInvariantLocal_iff_axGrain` | BornCalibration/RefinementImpliesGrain.lean | `EQUIVALENCE` : la prémisse normative locale est **exactement** `AxGrain` sur le poids canonique, ni plus forte ni plus faible. | `F : RationalExpectationFamily n`. | Prouvé ; même quantification non restreinte que ci-dessus — l'équivalence porte sur *cette* forme de Grain, pas sur une forme restreinte aux raffinements record-neutres (P6a). | résultat original |

**Note.** `grain_pullback_sum_eq`, la généralisation technique qui rend possible le sens réciproque, est `private` — elle n'apparaît donc pas en ligne propre ci-dessus, bien que son rôle soit documenté en toutes lettres dans le docstring de `refinementInvariantLocal_iff_axGrain`.

### `BornCalibration/BornExpectation.lean`

| Déclaration | Fichier | Ce qu'elle affirme | Hypothèses | Portée / limitations | Catégorie |
|---|---|---|---|---|---|
| `born_expectation_of_invariance` | BornCalibration/BornExpectation.lean | Sous les axiomes généraux de rationalité, l'invariance locale normative et la nullité physique du poids canonique (`AxNul`), la fonctionnelle d'espérance coïncide avec l'espérance de Born, sur toute perspective. | `F : RationalExpectationFamily n`, `3 ≤ n`, `RefinementInvariantLocal F.V`, `‖v‖ = 1`, `AxNul (canonicalWeight F) v`. | Prouvé. Route projective seulement ; `AxNorm`/`AxPos` sont **dérivées**, non assumées ; ne dérive dynamiquement ni prémisse-pont. | résultat original |
| `born_expectation_formula` | BornCalibration/BornExpectation.lean | Corollaire de compatibilité : la même conclusion, avec `AxNorm`/`AxPos` explicites (désormais redondantes). | Comme ci-dessus, plus `AxNorm`, `AxPos` explicites (ignorées dans la preuve). | Prouvé ; strictement un corollaire, sans contenu supplémentaire. | résultat original |

**Note.** Le docstring de module (lignes 5–20) qualifie encore `born_expectation_of_invariance` de « résultat de clôture... énoncé comme but ouvert : résultat scientifique hors de portée de P1 ». C'est faux depuis la reprise P3/P4 : la déclaration est intégralement prouvée, sans `sorry`. Le docstring n'a pas été mis à jour depuis la clôture — décrit en détail dans le rapport de session. L'`example` anonyme du critère de sortie P1 (ligne 89) est authentique et toujours valide ; voir la note de fin de section.

### `BornCalibration/NonCircularity.lean`

| Déclaration | Fichier | Ce qu'elle affirme | Hypothèses | Portée / limitations | Catégorie |
|---|---|---|---|---|---|
| `perspective_two_cases` | BornCalibration/NonCircularity.lean | En dimension 2, toute perspective est soit `{⊤}`, soit une paire `{L, Lᗮ}` — aucune n'a plus de deux cellules. | Fixé à `n = 2`. | Prouvé ; fait structurel spécifique à `n = 2`. | résultat original |
| `skewWeight` | BornCalibration/NonCircularity.lean | Règle d'estimation rivale non bornienne : `f(‖projL c v‖²)` avec `f` non linéaire. | Fixé à `n = 2`. | Définition. | définition |
| `skewWeight_axPos`, `skewWeight_axNul`, `skewWeight_axNorm`, `skewWeight_axGrain` | BornCalibration/NonCircularity.lean | `skewWeight v` satisfait les quatre axiomes `AxPos`, `AxNul`, `AxNorm`, `AxGrain`. | `‖v‖ = 1` pour Norm et Grain. | Prouvé en entier, en `n = 2` seulement. | témoin de non-vacuité (pour les quatre axiomes conjointement) |
| `witnessState` | BornCalibration/NonCircularity.lean | État concret `(3/5, 4/5)` en base computationnelle de `H 2`, amplitudes inégales. | — | Définition. | définition |
| `witnessState_norm` | BornCalibration/NonCircularity.lean | `witnessState` est de norme 1. | — | Prouvé. | API auxiliaire |
| `witnessLine` | BornCalibration/NonCircularity.lean | Ligne engendrée par le premier vecteur de base computationnelle de `H 2`. | — | Définition. | définition |
| `witnessLine_ne_bot`, `witnessLine_ne_top` | BornCalibration/NonCircularity.lean | `witnessLine` est non nulle et propre. | — | Prouvé. | API auxiliaire |
| `witness_x` | BornCalibration/NonCircularity.lean | `‖projL witnessLine witnessState‖² = 9/25`, un recouvrement partiel générique. | — | Prouvé. | API auxiliaire |
| `grain_does_not_imply_born_at_two` | BornCalibration/NonCircularity.lean | `NON-CIRCULARITY WITNESS`. En `n = 2`, il existe une règle satisfaisant `AxGrain ∧ AxNorm ∧ AxPos ∧ AxNul` mais différant de Born (`skewWeight witnessState` sur `witnessLine`). | Fixé à `n = 2`. | Prouvé ; réfute que la prémisse normative *soit* Born déguisée. Ne classifie qu'**un** contre-exemple, pas toutes les règles cohérentes sous Grain en `n = 2`. Ne dit rien sur `n ≥ 3`. | témoin de non-trivialité |

### `BornCalibration/Nonvacuity.lean`

Ce fichier ne contient qu'un `example` anonyme (voir note de fin de section) ; aucune déclaration publique nommée.

### `Rivals/NaiveBranchCounting.lean`

| Déclaration | Fichier | Ce qu'elle affirme | Hypothèses | Portée / limitations | Catégorie |
|---|---|---|---|---|---|
| `cellLines_card_eq_finrank` | Rivals/NaiveBranchCounting.lean | Le nombre de lignes de la décomposition de base d'une cellule est sa dimension hilbertienne finie. | — | Prouvé. | API auxiliaire |
| `exampleCoarse_cells_card`, `exampleFine_cells_card` | Rivals/NaiveBranchCounting.lean | Cardinaux concrets (`2` et `3`) de la paire binaire/trois-lignes explicite en `H 3`. | Fixé à `n = 3`. | Prouvé ; exposés pour réutilisation par d'autres fichiers de témoins. | API auxiliaire |
| `naiveCounting` | Rivals/NaiveBranchCounting.lean | Règle rivale : chaque cellule reçoit le poids uniforme `1/|D.cells|`, indépendamment de tout contenu hilbertien. | — | Définition, pour tout `n`. | définition |
| `naiveCounting_violates_grain` | Rivals/NaiveBranchCounting.lean | Le comptage naïf viole `AxGrain`, sur la paire binaire/trois-lignes explicite en `H 3`. | Fixé à `n = 3`. | Prouvé. | résultat négatif |

**Note.** `docs/RIVAL_RULES.md` qualifie encore ce résultat de « but ouvert budgété (P1... clôture prévue P6) », alors que `naiveCounting_violates_grain` est intégralement prouvé et clos depuis la reprise P3/P4 (confirmé par `CLAIM_MATRIX.md`, `MILESTONES.md`). Référence obsolète, décrite dans le rapport de session.

### `Rivals/Nonvacuity.lean`

| Déclaration | Fichier | Ce qu'elle affirme | Hypothèses | Portée / limitations | Catégorie |
|---|---|---|---|---|---|
| `naiveCounting_axPos` | Rivals/Nonvacuity.lean | Le comptage naïf satisfait `AxPos`, pour tout `n`. | — | Prouvé. | témoin de non-vacuité (partiel — un seul des quatre axiomes) |

### `PhysicalRefinement/RecordNeutralWitness.lean`

| Déclaration | Fichier | Ce qu'elle affirme | Hypothèses | Portée / limitations | Catégorie |
|---|---|---|---|---|---|
| `b`, `label0Line`, `anc0Line`, `anc1Line`, `label1Space` | PhysicalRefinement/RecordNeutralWitness.lean | Base orthonormée fixe de `H 3` et les sous-espaces qui en dérivent (étiquette observée, deux lignes de raffinement, complément orthogonal). | Fixé à `n = 3`. | Définitions ; la lecture « ancilla » de `anc0Line`/`anc1Line` est une interprétation en prose, pas un fait du type (voir section 1 et `AGENTS.md` règle 13). | définition |
| `coarsePerspective`, `finePerspective` | PhysicalRefinement/RecordNeutralWitness.lean | La perspective grossière à deux cellules et son raffinement fin à trois cellules (perspective de base engendrée par `b`). | Fixé à `n = 3`. | Définitions. | définition |
| `recordNeutral_refines` | PhysicalRefinement/RecordNeutralWitness.lean | `finePerspective` raffine bien `coarsePerspective`. | Fixé à `n = 3`. | Prouvé ; un des quatre théorèmes obligatoires du témoin P6a. | résultat original |
| `coupleU`, `coupleULin` | PhysicalRefinement/RecordNeutralWitness.lean | Application de couplage : identité sur `b 0`, rotation `(3/5,4/5;4/5,-3/5)` sur le bloc `{b 1, b 2}`. | Fixé à `n = 3`. | Définition ; linéarité empaquetée séparément (`coupleULin`). | définition |
| `coupleU_isometry` | PhysicalRefinement/RecordNeutralWitness.lean | `coupleU` est une isométrie (donc unitaire, `H 3` étant de dimension finie). | Fixé à `n = 3`. | Prouvé. | résultat original |
| `psiBefore`, `psiAfter` | PhysicalRefinement/RecordNeutralWitness.lean | États témoins concrets, amplitudes `3/5`, `4/5` inégales ; `psiAfter = coupleU psiBefore`. | Fixé à `n = 3`. | Définitions, calculées en rationnels exacts. | définition |
| `coupleU_psiBefore` | PhysicalRefinement/RecordNeutralWitness.lean | `coupleU psiBefore = psiAfter`, calculé explicitement. | Fixé à `n = 3`. | Prouvé. | API auxiliaire |
| `weight_label0_before/after`, `weight_anc0_before/after`, `weight_anc1_before/after`, `weight_label1Space_before/after` | PhysicalRefinement/RecordNeutralWitness.lean | Poids borniens exacts (en rationnels) des quatre cellules, avant et après couplage. | Fixé à `n = 3`. | Prouvé. | API auxiliaire |
| `accessibleRecord` | PhysicalRefinement/RecordNeutralWitness.lean | Le record accessible d'un état : ses poids borniens sur les deux cellules de `coarsePerspective` seulement. | Fixé à `n = 3`. | Définition ; restreinte aux deux cellules grossières **par stipulation**, pas par dérivation (voir `RefinementNotInRecordAlgebra`). | définition |
| `recordNeutral_record_eq` | PhysicalRefinement/RecordNeutralWitness.lean | Le record accessible est inchangé par le couplage. | Fixé à `n = 3`. | Prouvé ; un des quatre théorèmes obligatoires. | résultat original |
| `RefinementNotInRecordAlgebra` | PhysicalRefinement/RecordNeutralWitness.lean | Hypothèse nommée : les cellules `anc0Line`/`anc1Line` produites par le raffinement ne sont pas des cellules de l'algèbre de records. | Fixé à `n = 3`. | Définition (`Prop`) ; contestable par construction — voir section 1. | définition `PREMISE` |
| `refinementNotInRecordAlgebra_holds` | PhysicalRefinement/RecordNeutralWitness.lean | L'hypothèse ci-dessus est satisfaite dans ce modèle précis. | Fixé à `n = 3`. | Prouvé. | témoin de non-vacuité |
| `payoff` | PhysicalRefinement/RecordNeutralWitness.lean | Le paiement décision-pertinent du témoin : l'indicatrice de `label1Space`. | Fixé à `n = 3`. | Définition. | définition |
| `recordNeutral_payoff_eq` | PhysicalRefinement/RecordNeutralWitness.lean | Le paiement tiré en arrière vaut `1` sur les deux cellules d'ancilla. | Fixé à `n = 3`. | Prouvé ; un des quatre théorèmes obligatoires. | résultat original |
| `recordNeutral_bornWeight_eq` | PhysicalRefinement/RecordNeutralWitness.lean | Les poids borniens des deux cellules de records sont inchangés par le couplage. | Fixé à `n = 3`. | Prouvé ; le quatrième théorème obligatoire. | résultat original |

### `PhysicalRefinement/Nonvacuity.lean`

| Déclaration | Fichier | Ce qu'elle affirme | Hypothèses | Portée / limitations | Catégorie |
|---|---|---|---|---|---|
| `bornExpectation_fine_payoff_eq_accessibleRecord_snd` | PhysicalRefinement/Nonvacuity.lean | L'espérance bornienne du paiement tiré en arrière, sur la perspective fine, est exactement la deuxième composante de `accessibleRecord`, pour **tout** état. | Fixé à `n = 3`. | Prouvé ; généralise au-delà de `psiBefore`/`psiAfter`. | résultat original |
| `born_insensitive_to_recordNeutral_refinement` | PhysicalRefinement/Nonvacuity.lean | L'espérance bornienne du paiement tiré en arrière a la même valeur avant et après le couplage. | Fixé à `n = 3`. | Prouvé ; corollaire immédiat du précédent via `recordNeutral_record_eq`. | témoin de non-vacuité |
| `born_determined_by_accessible_record` | PhysicalRefinement/Nonvacuity.lean | Deux états au même record accessible donnent la même espérance bornienne, pour ce paiement. | `accessibleRecord u = accessibleRecord w`. | Prouvé ; pendant bornien de `counting_underdetermined_by_accessible_record`. | résultat original (contraste avec le comptage) |

### `PhysicalRefinement/NonTriviality.lean`

| Déclaration | Fichier | Ce qu'elle affirme | Hypothèses | Portée / limitations | Catégorie |
|---|---|---|---|---|---|
| `activeCells` | PhysicalRefinement/NonTriviality.lean | Cellules d'une perspective où un état a un poids bornien non nul. | Fixé à `n = 3`. | Définition ; restreinte volontairement aux cellules actives, pas à toutes les cellules de la perspective (sinon le témoin est aveugle — voir section 1 du prompt P6a). | définition |
| `uniformCredence` | PhysicalRefinement/NonTriviality.lean | Règle rivale : crédence uniforme sur les cellules actives. | Fixé à `n = 3`. | Définition. | définition |
| `counting_sensitive_to_recordNeutral_refinement` | PhysicalRefinement/NonTriviality.lean | Le comptage actif diffère avant et après le couplage (`1/2 ≠ 1/3`). | Fixé à `n = 3`. | Prouvé ; **spécifique** à ce témoin. | témoin de non-trivialité |
| `counting_underdetermined_by_accessible_record` | PhysicalRefinement/NonTriviality.lean | Il existe deux états au même record accessible mais à des verdicts de comptage actif différents. | Fixé à `n = 3`. | Prouvé ; existentiel, instancié sur `psiBefore`/`psiAfter` uniquement. | témoin de non-trivialité |

### `Audit/MainResults.lean`

Aucune déclaration propre : uniquement une suite de commandes `#print axioms` sur des déclarations définies ailleurs. Le fichier lui-même n'introduit aucun contenu mathématique nouveau ; c'est l'unique fichier de la liste sans ligne de tableau.

### Note — `example` anonymes portant un rôle de témoin

Deux `example` (non nommés, donc non listés ci-dessus comme déclarations publiques au sens strict) portent un rôle significatif :

- `BornCalibration/BornExpectation.lean`, ligne 89 : critère de sortie du jalon P1 — atteste que `grainCoherenceTheorem_projector` est importable avec exactement la signature attendue, sans aucune définition propre à ce dépôt. Toujours valide.
- `Core/Nonvacuity.lean`, ligne 62 : atteste que `parentOf` s'applique sans erreur de type à un raffinement non trivial concret. Toujours valide, mais son docstring adjacent est la référence morte à `Core/Parent.lean` déjà signalée.
- `BornCalibration/Nonvacuity.lean`, ligne 24 : atteste que `canonicalWeight` produit un réel concret sur `uniformExpectationFamily`. Toujours valide.

## English

Categories: *original result*, *connection theorem*, *nonvacuity witness*,
*nontriviality witness*, *negative result*, *auxiliary API*, *definition*.

### `Core/Interface.lean` (namespace `EverettianProbability.Abstract`)

| Declaration | File | What it asserts | Hypotheses | Scope / limitations | Category |
|---|---|---|---|---|---|
| `PerspectiveInterface` | Core/Interface.lean | Bundles, as one class, the minimal data of a finite-perspective model: cells, outcome, refinement, parent map, estimation rule. | Free universes `uP,uO,uC,uR,uE`. | The P0.3 interface; prejudges no physical content. | definition |
| `cellFintypeInstance`, `cellDecidableEqInstance` | Core/Interface.lean | Make a perspective's cells `Fintype`/`DecidableEq` from the interface's fields. | — | Technical instances. | auxiliary API |
| `Act` (abbrev) | Core/Interface.lean | An abstract act is a total function on the ambient outcome space. | — | — | definition |
| `AgreeOn` | Core/Interface.lean | Two abstract acts agree on every cell of a perspective. | — | — | definition |
| `pullbackAct` | Core/Interface.lean | Abstract pullback: composition with the total parent map. | — | — | definition |
| `pullbackAct_refl_agree` | Core/Interface.lean | Pullback by reflexivity agrees with the original act on cells. | — | Proved. | original result |
| `pullbackAct_trans_agree` | Core/Interface.lean | Pullback respects refinement composition, on the finest perspective's cells. | — | Proved. | original result |
| `Grain` | Core/Interface.lean | Abstract refinement coherence of an estimation rule: a coarse cell's weight is the sum of its fine fiber's weights. | — | Definition, not a physical fact. | definition |
| `expectation` | Core/Interface.lean | Abstract expectation of an act: weighted sum over a perspective's cells. | — | — | definition |
| `RefinementInvariant` | Core/Interface.lean | An abstract expectation functional is pullback-invariant under every refinement. | — | *Global* form, quantified over every act, not the local form used elsewhere in the repository. | definition |
| `expectation_refinementInvariant` | Core/Interface.lean | Abstract measure-to-functional bridge: Grain coherence of a rule makes its expectation refinement-invariant. | `Grain I E`. | Proved, entirely abstract. | connection theorem |
| `Projective.interface` | Core/Interface.lean | Projective instance of `PerspectiveInterface`: cells = subspaces of a `Perspective n`, outcome = `Submodule ℂ (H n)`. | — | Projective instance. | definition |
| `Projective.interface_weight_apply`, `Projective.interface_parentCell_apply` | Core/Interface.lean | Simplification lemmas for the projective instance. | — | — | auxiliary API |
| `Projective.grain_of_axGrain` | Core/Interface.lean | The upstream `AxGrain` condition (projective side) is exactly the abstract `Grain` coherence for this instance. | `AxGrain E`. | Proved. | connection theorem |
| `Projective.born_refinementInvariant` | Core/Interface.lean | The Born weight `E₀ v` supplies a nonempty projective estimation rule whose abstract expectation is refinement-invariant. | — | Instantiates `expectation_refinementInvariant`; carries no dimension hypothesis. | nonvacuity witness |
| `Effects.interface` | Core/Interface.lean | Effect instance of `PerspectiveInterface`: cells = `Fin D.outcomes`, outcome = `ℕ`. | — | Effect instance. | definition |
| `Effects.estimationRule_grain` | Core/Interface.lean | Every upstream effect-side estimation rule satisfies the abstract `Grain` coherence. | — | Proved; upstream `EstimationRule` bundles `grain` as a field, so this is near-immediate. | connection theorem |
| `Effects.pureState_refinementInvariant` | Core/Interface.lean | The upstream pure-state rule gives an abstract expectation that is refinement-invariant on the effect side. | `‖v‖ = 1`. | Starts from a rule that already satisfies Grain *by construction* — derives nothing from a normative premise (see `docs/QUBIT_FEASIBILITY_REPORT.md`, section 1). | nonvacuity witness |

### `Core/Act.lean` (namespace `EverettianProbability.Core`)

| Declaration | File | What it asserts | Hypotheses | Scope / limitations | Category |
|---|---|---|---|---|---|
| `Act n` | Core/Act.lean | An act is a total function `Submodule ℂ (H n) → ℝ`; values outside the perspective are junk. | — | — | definition |
| `Act.AgreeOn` | Core/Act.lean | Two acts agree on every cell of a perspective `D`. | — | — | definition |
| `Act.const`, `Act.indicator`, `Act.add`, `Act.PointwiseLE`, `Act.convComb`, `Act.indicatorExpansion` | Core/Act.lean | Pointwise operations on acts (constant, indicator, sum, order, convex combination, indicator expansion). | — | — | definition |
| `Act.agreeOn_refl`, `Act.agreeOn_symm`, `Act.agreeOn_trans` | Core/Act.lean | `AgreeOn D` is an equivalence relation. | — | Proved. | auxiliary API |
| `Act.agreeOn_add`, `Act.agreeOn_convComb` | Core/Act.lean | `AgreeOn` is stable under pointwise sum and convex combination. | — | Proved. | auxiliary API |
| `Act.indicator_self`, `Act.indicator_of_ne` | Core/Act.lean | Values of the indicator on its own cell and on a distinct cell. | — | Proved. | auxiliary API |
| `Act.agreeOn_indicatorExpansion` | Core/Act.lean | On `D`, every act agrees with its finite indicator expansion. | — | Proved. | original result |

### `Core/Nonvacuity.lean`

| Declaration | File | What it asserts | Hypotheses | Scope / limitations | Category |
|---|---|---|---|---|---|
| `exampleLine` | Core/Nonvacuity.lean | A concrete nonzero, proper line of `H 3` (first basis vector). | — | Fixes `n = 3`. | definition |
| `exampleLine_ne_bot`, `exampleLine_ne_top` | Core/Nonvacuity.lean | `exampleLine` is nonzero and proper. | — | Reuses upstream `line_ne_bot`/`line_ne_top`. | auxiliary API |
| `exampleCoarse` | Core/Nonvacuity.lean | Concrete coarse perspective: the binary split `{exampleLine, exampleLineᗮ}`. | — | — | definition |
| `exampleFine` | Core/Nonvacuity.lean | Concrete refinement of `exampleCoarse`, via the upstream `refinePerspective` construction. | — | Reuses upstream infrastructure, does not rebuild it. | definition |
| `exampleFine_refines` | Core/Nonvacuity.lean | `exampleFine` does refine `exampleCoarse`, strictly (not trivial reflexivity). | — | Proved. | nonvacuity witness |
| `exampleAct` | Core/Nonvacuity.lean | Concrete act: the indicator of `exampleLine`. | — | — | definition |
| `exampleLine_mem_exampleCoarse` | Core/Nonvacuity.lean | `exampleLine` is indeed a cell of `exampleCoarse`. | — | Proved. | auxiliary API |
| `exampleAct_at_exampleLine`, `exampleConst_at_exampleLine` | Core/Nonvacuity.lean | Concrete values of `exampleAct` and the constant act on `exampleLine`. | — | Proved. | auxiliary API |

**Note.** This file's docstring (lines 57–61) claims `parent_mem`, `parent_le`, `parent_unique` "are still open goals in `Core/Parent.lean`." That file does not exist: `ARCHITECTURE_NOTES.md` ("Acts, upstream parent map, and the P0.3 interface") explicitly confirms `Core/Parent.lean` **was deleted** and every pullback now uses upstream `parentOf`. The docstring was never updated after that deletion — a dead reference, detailed in the session report.

### `Refinement/PullbackAct.lean`

| Declaration | File | What it asserts | Hypotheses | Scope / limitations | Category |
|---|---|---|---|---|---|
| `pullbackAct` | Refinement/PullbackAct.lean | Pullback of an act along a refinement: `a ∘ parentOf r`. | — | — | definition |
| `fiberIndicator` | Refinement/PullbackAct.lean | Indicator of the fiber of `parentOf r` above a cell. | — | — | definition |
| `pullbackAct_const` | Refinement/PullbackAct.lean | The pullback of a constant act is the same constant act. | — | Proved (`rfl`). | auxiliary API |
| `pullbackAct_agree_of_agree` | Refinement/PullbackAct.lean | If two acts agree on `D`, their pullbacks agree on `D'`. | — | Proved. | auxiliary API |
| `pullbackAct_refl_agree` | Refinement/PullbackAct.lean | Pullback along a reflexive refinement is the identity on cells. | — | Proved. | auxiliary API |
| `pullbackAct_trans_agree` | Refinement/PullbackAct.lean | Pullback is compatible with transitive composition, on fine cells. | — | Proved. | auxiliary API |
| `pullbackAct_indicator` | Refinement/PullbackAct.lean | Pulling back an indicator gives exactly the indicator of its parent fiber. | — | Proved (`rfl`). | auxiliary API |
| `pullbackAct_indicator_eq_one_iff` | Refinement/PullbackAct.lean | On fine cells, the pulled-back indicator is one exactly on the upstream `coarseCells` fiber. | `c ∈ D.cells`, `c' ∈ D'.cells`. | Proved. | auxiliary API |

### `Refinement/PayoffPreserving.lean`

| Declaration | File | What it asserts | Hypotheses | Scope / limitations | Category |
|---|---|---|---|---|---|
| `PayoffEquivalentAt` | Refinement/PayoffPreserving.lean | Two descriptions assign the same consequences to every fine branch of a given refinement. | — | Normative premise, not a dynamical fact. | definition |
| `RefinementInvariant` | Refinement/PayoffPreserving.lean | An expectation family is invariant: evaluating a coarse act or its pullback gives the same value, for **every** refinement and act. | — | Global form (not filtered by `PayoffEquivalentAt`). | `PREMISE` definition |
| `RefinementInvariantLocal` | Refinement/PayoffPreserving.lean | Local version: invariance is required only between locally equivalent descriptions (`PayoffEquivalentAt`). | — | This is the premise actually adopted by the headline theorem. | `PREMISE` definition |
| `refinementInvariantLocal_iff_pullback` | Refinement/PayoffPreserving.lean | For a rational family, the local form is equivalent to invariance evaluated on the canonical pullback. | `F : RationalExpectationFamily n`. | Proved. | original result |
| `bornExpectation` | Refinement/PayoffPreserving.lean | Born expectation of an act in state `v`: `∑ c ∈ D.cells, ‖projL c v‖² * a c`. | — | — | definition |
| `bornExpectation_pullback_eq` | Refinement/PayoffPreserving.lean | Born expectation is invariant under arbitrary projective pullback. | — | Proved, for every `v`, every refinement. | original result |
| `bornExpectation_refinementInvariant` | Refinement/PayoffPreserving.lean | Corollary: Born expectation satisfies the global `RefinementInvariant` form. | — | Proved. | nonvacuity witness |
| `bornExpectation_refinementInvariantLocal` | Refinement/PayoffPreserving.lean | Corollary: Born expectation satisfies the local `RefinementInvariantLocal` form. | — | Proved; the named positive witness of the headline premise. | nonvacuity witness |

### `Refinement/GlobalPayoffVacuity.lean`

| Declaration | File | What it asserts | Hypotheses | Scope / limitations | Category |
|---|---|---|---|---|---|
| `GloballyPayoffPreserving` | Refinement/GlobalPayoffVacuity.lean | Former global reading: an act agrees with its own pullback for **every** refinement. | — | Explicitly retained only to establish its vacuity; must never serve as a premise. | definition (negative result) |
| `singletonTopPerspective` | Refinement/GlobalPayoffVacuity.lean | The explicit singleton perspective `{⊤}`, in nonzero dimension. | `0 < n`. | — | definition |
| `globallyPayoffPreserving_const` | Refinement/GlobalPayoffVacuity.lean | A globally preserving act is constant on every cell of every accessible perspective. | `0 < n`. | Proved. | negative result |
| `not_globallyPayoffPreserving_indicator` | Refinement/GlobalPayoffVacuity.lean | On a proper fiber, the parent's indicator is not globally preserving. | `c' ≤ c`, `c' ≠ c`, `c' ∈ D'.cells`, `c ∈ D.cells`. | Proved; the negative witness of `GloballyPayoffPreserving`. | nontriviality witness |
| `globalPremise_vacuous` | Refinement/GlobalPayoffVacuity.lean | Every rational family automatically satisfies the invariance filtered by `GloballyPayoffPreserving`. | `F : RationalExpectationFamily n`. | Proved; establishes vacuity — the premise discriminates no rational family. | negative result |
| `uniformExpectationFamily_globalPremise_vacuous` | Refinement/GlobalPayoffVacuity.lean | Named witness: the uniform family satisfies the filtered global premise while violating `AxGrain`. | Fixed at `n = 3`. | Proved (conjunction of two facts). | nonvacuity witness (negative for Grain) |

### `Refinement/Nonvacuity.lean`

| Declaration | File | What it asserts | Hypotheses | Scope / limitations | Category |
|---|---|---|---|---|---|
| `const_payoffEquivalentAt` | Refinement/Nonvacuity.lean | Two identical constant acts are locally equivalent for every refinement. | — | Proved. | nonvacuity witness |
| `exampleState` | Refinement/Nonvacuity.lean | First standard basis vector of `H 3`, as a concrete state. | — | — | definition |
| `exampleState_norm` | Refinement/Nonvacuity.lean | `exampleState` has norm 1. | — | Proved. | auxiliary API |
| `exampleBorn_refinementInvariant` | Refinement/Nonvacuity.lean | Concrete instance of `bornExpectation_refinementInvariantLocal` at `exampleState`. | — | Proved. | nonvacuity witness |
| `exampleBornExpectation_values` | Refinement/Nonvacuity.lean | Computed Born expectation values on `exampleFine`/`exampleCoarse`: `1` on both sides of the concrete refinement. | — | Proved. | nonvacuity witness |

### `Refinement/NonTriviality.lean`

| Declaration | File | What it asserts | Hypotheses | Scope / limitations | Category |
|---|---|---|---|---|---|
| `uniform_not_refinementInvariantLocal` | Refinement/NonTriviality.lean | The uniform expectation family does not satisfy `RefinementInvariantLocal`: concrete calculation `1/2 ≠ 2/3` on the complement cell of the binary/three-line pair in `H 3`. | Fixed at `n = 3`. | Proved; **specific** to this pair of perspectives and this act — classifies no other rival rule or pair. | nontriviality witness |

### `Preference/ExpectationFunctional.lean`

| Declaration | File | What it asserts | Hypotheses | Scope / limitations | Category |
|---|---|---|---|---|---|
| `RationalExpectationFamily` | Preference/ExpectationFunctional.lean | Structure bundling, per perspective, an affine, monotone, constant-normalized expectation functional. | — | Affinity is a substantial hypothesis, not neutral (see overreach hunt, point 8). | `PREMISE` definition |
| `V_congr_of_agreeOn` | Preference/ExpectationFunctional.lean | Local monotonicity forces `F.V D` to depend only on the act's values on `D.cells`. | `F : RationalExpectationFamily n`, `Act.AgreeOn D a b`. | Proved. | original result |

### `Preference/Representation.lean`

| Declaration | File | What it asserts | Hypotheses | Scope / limitations | Category |
|---|---|---|---|---|---|
| `represents` | Preference/Representation.lean | Every rational functional is the finite sum weighted by its canonical weight on the cells. | `F : RationalExpectationFamily n`. | Proved. | original result |
| `weights_unique_on_cells` | Preference/Representation.lean | Any other weight system representing `F.V D` agrees with the canonical weight **on the cells** (not outside). | `∀ a, F.V D a = ∑ c ∈ D.cells, p c * a c`. | Proved; uniqueness is explicitly restricted to `D.cells` — the fix for the P3 defect documented in `ARCHITECTURE_NOTES.md`. | original result |
| `canonicalWeight_axPos` | Preference/Representation.lean | Positivity of the canonical weight is **derived** from local monotonicity, not assumed. | `F : RationalExpectationFamily n`. | Proved. | original result |
| `canonicalWeight_axNorm` | Preference/Representation.lean | Normalization of the canonical weight is **derived** from constant-act normalization, not assumed. | `F : RationalExpectationFamily n`. | Proved. | original result |

### `Preference/Nonvacuity.lean`

| Declaration | File | What it asserts | Hypotheses | Scope / limitations | Category |
|---|---|---|---|---|---|
| `top_ne_bot_H3`, `cells_nonempty` | Preference/Nonvacuity.lean | `H 3` is nontrivial; every perspective on `H 3` has at least one cell. | Fixed at `n = 3`. | Proved. | auxiliary API |
| `uniformExpectation` | Preference/Nonvacuity.lean | Uniform average of an act over a perspective's cells. | Fixed at `n = 3`. | Deliberately degenerate rule (counting, not Born) to stay non-circular. | definition |
| `uniformExpectation_affine`, `uniformExpectation_monotone`, `uniformExpectation_normalized_const` | Preference/Nonvacuity.lean | `uniformExpectation` satisfies `RationalExpectationFamily`'s three axioms. | Fixed at `n = 3`. | Proved in full. | nonvacuity witness |
| `uniformExpectationFamily` | Preference/Nonvacuity.lean | The concrete witness: `uniformExpectation` packaged as a `RationalExpectationFamily 3`. | Fixed at `n = 3`. | Proved. | nonvacuity witness |

### `Preference/NonTriviality.lean`

| Declaration | File | What it asserts | Hypotheses | Scope / limitations | Category |
|---|---|---|---|---|---|
| `maxExpectation` | Preference/NonTriviality.lean | Maximum of an act over a perspective's cells, at fixed `n = 3`. | Fixed at `n = 3`. | Well-defined (`D.cells` nonempty). | definition |
| `maxExpectation_monotone`, `maxExpectation_normalized_const` | Preference/NonTriviality.lean | `maxExpectation` is monotone and normalized on constants. | Fixed at `n = 3`. | Proved. | auxiliary API |
| `maxExpectation_not_affine` | Preference/NonTriviality.lean | `maxExpectation` violates affinity (`1/2 ≠ 1` on the explicit binary perspective), despite monotonicity and normalization. | Fixed at `n = 3`. | Proved; **specific** to this perspective, does not classify every non-affine functional (rank-dependent theories, Quiggin/Yaari, are only *illustrated*, not covered). | nontriviality witness |

### `BornCalibration/ContextualWeight.lean`

| Declaration | File | What it asserts | Hypotheses | Scope / limitations | Category |
|---|---|---|---|---|---|
| `canonicalWeight` | BornCalibration/ContextualWeight.lean | Canonical contextual weight: the value of the indicator act, zero outside the cells. | — | Definition, not a representative choice. | definition |
| `canonicalWeight_zero_outside` | BornCalibration/ContextualWeight.lean | The canonical weight vanishes outside the perspective's cells. | `c ∉ D.cells`. | Proved. | auxiliary API |

### `BornCalibration/RefinementImpliesGrain.lean`

| Declaration | File | What it asserts | Hypotheses | Scope / limitations | Category |
|---|---|---|---|---|---|
| `refinement_invariant_implies_grain` | BornCalibration/RefinementImpliesGrain.lean | Local invariance under every refinement forces `AxGrain` for the canonical weight. | `F : RationalExpectationFamily n`, `RefinementInvariantLocal F.V`. | Proved; **unrestricted** projective quantification (every refinement). | original result |
| `refinementInvariantLocal_iff_axGrain` | BornCalibration/RefinementImpliesGrain.lean | `EQUIVALENCE`: the local normative premise is **exactly** `AxGrain` on the canonical weight, neither stronger nor weaker. | `F : RationalExpectationFamily n`. | Proved; same unrestricted quantification as above — the equivalence concerns *this* form of Grain, not a form restricted to record-neutral refinements (P6a). | original result |

**Note.** `grain_pullback_sum_eq`, the technical generalization enabling the converse direction, is `private` — it therefore has no row of its own above, though its role is spelled out in `refinementInvariantLocal_iff_axGrain`'s docstring.

### `BornCalibration/BornExpectation.lean`

| Declaration | File | What it asserts | Hypotheses | Scope / limitations | Category |
|---|---|---|---|---|---|
| `born_expectation_of_invariance` | BornCalibration/BornExpectation.lean | Under general rationality axioms, normative local invariance, and physical null support for the canonical weight (`AxNul`), the expectation functional coincides with Born expectation, on every perspective. | `F : RationalExpectationFamily n`, `3 ≤ n`, `RefinementInvariantLocal F.V`, `‖v‖ = 1`, `AxNul (canonicalWeight F) v`. | Proved. Projective route only; `AxNorm`/`AxPos` are **derived**, not assumed; dynamically derives neither bridge premise. | original result |
| `born_expectation_formula` | BornCalibration/BornExpectation.lean | Compatibility corollary: the same conclusion, with explicit (now redundant) `AxNorm`/`AxPos`. | As above, plus explicit `AxNorm`, `AxPos` (unused in the proof). | Proved; strictly a corollary, no extra content. | original result |

**Note.** The module docstring (lines 5–20) still calls `born_expectation_of_invariance` "the closing result... stated as an open goal: a scientific result out of scope for P1." That is false since the P3/P4 resumption: the declaration is fully proved, no `sorry`. The docstring was never updated after closure — detailed in the session report. The anonymous exit-criterion `example` (line 89) is genuine and still valid; see the end-of-section note.

### `BornCalibration/NonCircularity.lean`

| Declaration | File | What it asserts | Hypotheses | Scope / limitations | Category |
|---|---|---|---|---|---|
| `perspective_two_cases` | BornCalibration/NonCircularity.lean | In dimension 2, every perspective is either `{⊤}` or a pair `{L, Lᗮ}` — none has more than two cells. | Fixed at `n = 2`. | Proved; a structural fact specific to `n = 2`. | original result |
| `skewWeight` | BornCalibration/NonCircularity.lean | Rival, non-Born estimation rule: `f(‖projL c v‖²)` with nonlinear `f`. | Fixed at `n = 2`. | Definition. | definition |
| `skewWeight_axPos`, `skewWeight_axNul`, `skewWeight_axNorm`, `skewWeight_axGrain` | BornCalibration/NonCircularity.lean | `skewWeight v` satisfies all four axioms `AxPos`, `AxNul`, `AxNorm`, `AxGrain`. | `‖v‖ = 1` for Norm and Grain. | Proved in full, at `n = 2` only. | nonvacuity witness (for the four axioms jointly) |
| `witnessState` | BornCalibration/NonCircularity.lean | Concrete state `(3/5, 4/5)` in the computational basis of `H 2`, unequal amplitudes. | — | Definition. | definition |
| `witnessState_norm` | BornCalibration/NonCircularity.lean | `witnessState` has norm 1. | — | Proved. | auxiliary API |
| `witnessLine` | BornCalibration/NonCircularity.lean | Line spanned by the first computational basis vector of `H 2`. | — | Definition. | definition |
| `witnessLine_ne_bot`, `witnessLine_ne_top` | BornCalibration/NonCircularity.lean | `witnessLine` is nonzero and proper. | — | Proved. | auxiliary API |
| `witness_x` | BornCalibration/NonCircularity.lean | `‖projL witnessLine witnessState‖² = 9/25`, a generic partial overlap. | — | Proved. | auxiliary API |
| `grain_does_not_imply_born_at_two` | BornCalibration/NonCircularity.lean | `NON-CIRCULARITY WITNESS`. At `n = 2`, a rule exists satisfying `AxGrain ∧ AxNorm ∧ AxPos ∧ AxNul` yet differing from Born (`skewWeight witnessState` on `witnessLine`). | Fixed at `n = 2`. | Proved; refutes that the normative premise *is* Born in disguise. Classifies only **one** counterexample, not every Grain-coherent rule at `n = 2`. Says nothing about `n ≥ 3`. | nontriviality witness |

### `BornCalibration/Nonvacuity.lean`

This file contains only an anonymous `example` (see end-of-section note); no named public declaration.

### `Rivals/NaiveBranchCounting.lean`

| Declaration | File | What it asserts | Hypotheses | Scope / limitations | Category |
|---|---|---|---|---|---|
| `cellLines_card_eq_finrank` | Rivals/NaiveBranchCounting.lean | The number of lines in a cell's basis decomposition is its finite Hilbert dimension. | — | Proved. | auxiliary API |
| `exampleCoarse_cells_card`, `exampleFine_cells_card` | Rivals/NaiveBranchCounting.lean | Concrete cardinalities (`2` and `3`) of the explicit binary/three-line pair in `H 3`. | Fixed at `n = 3`. | Proved; exposed for reuse by other witness files. | auxiliary API |
| `naiveCounting` | Rivals/NaiveBranchCounting.lean | Rival rule: every cell receives uniform weight `1/|D.cells|`, independent of any Hilbert-space content. | — | Definition, for every `n`. | definition |
| `naiveCounting_violates_grain` | Rivals/NaiveBranchCounting.lean | Naive counting violates `AxGrain`, on the explicit binary/three-line pair in `H 3`. | Fixed at `n = 3`. | Proved. | negative result |

**Note.** `docs/RIVAL_RULES.md` still calls this result a "budgeted open goal (P1... planned closure P6)," although `naiveCounting_violates_grain` has been fully proved and closed since the P3/P4 resumption (confirmed by `CLAIM_MATRIX.md`, `MILESTONES.md`). A stale reference, detailed in the session report.

### `Rivals/Nonvacuity.lean`

| Declaration | File | What it asserts | Hypotheses | Scope / limitations | Category |
|---|---|---|---|---|---|
| `naiveCounting_axPos` | Rivals/Nonvacuity.lean | Naive counting satisfies `AxPos`, for every `n`. | — | Proved. | nonvacuity witness (partial — one of four axioms) |

### `PhysicalRefinement/RecordNeutralWitness.lean`

| Declaration | File | What it asserts | Hypotheses | Scope / limitations | Category |
|---|---|---|---|---|---|
| `b`, `label0Line`, `anc0Line`, `anc1Line`, `label1Space` | PhysicalRefinement/RecordNeutralWitness.lean | Fixed orthonormal frame of `H 3` and the subspaces derived from it (observed label, two refinement lines, orthogonal complement). | Fixed at `n = 3`. | Definitions; the "ancilla" reading of `anc0Line`/`anc1Line` is a prose interpretation, not a fact of the type (see Section 1 and `AGENTS.md` rule 13). | definition |
| `coarsePerspective`, `finePerspective` | PhysicalRefinement/RecordNeutralWitness.lean | The two-cell coarse perspective and its three-cell fine refinement (basis perspective generated by `b`). | Fixed at `n = 3`. | Definitions. | definition |
| `recordNeutral_refines` | PhysicalRefinement/RecordNeutralWitness.lean | `finePerspective` does refine `coarsePerspective`. | Fixed at `n = 3`. | Proved; one of the four required P6a theorems. | original result |
| `coupleU`, `coupleULin` | PhysicalRefinement/RecordNeutralWitness.lean | Coupling map: identity on `b 0`, rotation `(3/5,4/5;4/5,-3/5)` on the `{b 1, b 2}` block. | Fixed at `n = 3`. | Definition; linearity bundled separately (`coupleULin`). | definition |
| `coupleU_isometry` | PhysicalRefinement/RecordNeutralWitness.lean | `coupleU` is an isometry (hence unitary, `H 3` being finite-dimensional). | Fixed at `n = 3`. | Proved. | original result |
| `psiBefore`, `psiAfter` | PhysicalRefinement/RecordNeutralWitness.lean | Concrete witness states, unequal amplitudes `3/5`, `4/5`; `psiAfter = coupleU psiBefore`. | Fixed at `n = 3`. | Definitions, computed in exact rationals. | definition |
| `coupleU_psiBefore` | PhysicalRefinement/RecordNeutralWitness.lean | `coupleU psiBefore = psiAfter`, computed explicitly. | Fixed at `n = 3`. | Proved. | auxiliary API |
| `weight_label0_before/after`, `weight_anc0_before/after`, `weight_anc1_before/after`, `weight_label1Space_before/after` | PhysicalRefinement/RecordNeutralWitness.lean | Exact (rational) Born weights of the four cells, before and after coupling. | Fixed at `n = 3`. | Proved. | auxiliary API |
| `accessibleRecord` | PhysicalRefinement/RecordNeutralWitness.lean | The accessible record of a state: its Born weights on `coarsePerspective`'s two cells only. | Fixed at `n = 3`. | Definition; restricted to the two coarse cells **by stipulation**, not derivation (see `RefinementNotInRecordAlgebra`). | definition |
| `recordNeutral_record_eq` | PhysicalRefinement/RecordNeutralWitness.lean | The accessible record is unchanged by the coupling. | Fixed at `n = 3`. | Proved; one of the four required theorems. | original result |
| `RefinementNotInRecordAlgebra` | PhysicalRefinement/RecordNeutralWitness.lean | Named hypothesis: the refinement-produced cells `anc0Line`/`anc1Line` are not cells of the record algebra. | Fixed at `n = 3`. | Definition (`Prop`); contestable by construction — see Section 1. | `PREMISE` definition |
| `refinementNotInRecordAlgebra_holds` | PhysicalRefinement/RecordNeutralWitness.lean | The above hypothesis holds in this precise model. | Fixed at `n = 3`. | Proved. | nonvacuity witness |
| `payoff` | PhysicalRefinement/RecordNeutralWitness.lean | The witness's decision-relevant payoff: the indicator of `label1Space`. | Fixed at `n = 3`. | Definition. | definition |
| `recordNeutral_payoff_eq` | PhysicalRefinement/RecordNeutralWitness.lean | The pulled-back payoff equals `1` on both ancilla cells. | Fixed at `n = 3`. | Proved; one of the four required theorems. | original result |
| `recordNeutral_bornWeight_eq` | PhysicalRefinement/RecordNeutralWitness.lean | The Born weights of the two record cells are unchanged by coupling. | Fixed at `n = 3`. | Proved; the fourth required theorem. | original result |

### `PhysicalRefinement/Nonvacuity.lean`

| Declaration | File | What it asserts | Hypotheses | Scope / limitations | Category |
|---|---|---|---|---|---|
| `bornExpectation_fine_payoff_eq_accessibleRecord_snd` | PhysicalRefinement/Nonvacuity.lean | Born expectation of the pulled-back payoff, on the fine perspective, is exactly `accessibleRecord`'s second component, for **any** state. | Fixed at `n = 3`. | Proved; generalizes beyond `psiBefore`/`psiAfter`. | original result |
| `born_insensitive_to_recordNeutral_refinement` | PhysicalRefinement/Nonvacuity.lean | Born expectation of the pulled-back payoff has the same value before and after the coupling. | Fixed at `n = 3`. | Proved; immediate corollary of the above via `recordNeutral_record_eq`. | nonvacuity witness |
| `born_determined_by_accessible_record` | PhysicalRefinement/Nonvacuity.lean | Two states with the same accessible record give the same Born expectation, for this payoff. | `accessibleRecord u = accessibleRecord w`. | Proved; Born counterpart of `counting_underdetermined_by_accessible_record`. | original result (contrast with counting) |

### `PhysicalRefinement/NonTriviality.lean`

| Declaration | File | What it asserts | Hypotheses | Scope / limitations | Category |
|---|---|---|---|---|---|
| `activeCells` | PhysicalRefinement/NonTriviality.lean | Cells of a perspective where a state has nonzero Born weight. | Fixed at `n = 3`. | Definition; deliberately restricted to active cells, not every cell of the perspective (otherwise the witness is blind — see Section 1 of the P6a prompt). | definition |
| `uniformCredence` | PhysicalRefinement/NonTriviality.lean | Rival rule: uniform credence over active cells. | Fixed at `n = 3`. | Definition. | definition |
| `counting_sensitive_to_recordNeutral_refinement` | PhysicalRefinement/NonTriviality.lean | Active counting differs before and after coupling (`1/2 ≠ 1/3`). | Fixed at `n = 3`. | Proved; **specific** to this witness. | nontriviality witness |
| `counting_underdetermined_by_accessible_record` | PhysicalRefinement/NonTriviality.lean | Two states exist with the same accessible record but different active-counting verdicts. | Fixed at `n = 3`. | Proved; existential, instantiated only at `psiBefore`/`psiAfter`. | nontriviality witness |

### `Audit/MainResults.lean`

No declaration of its own: only a sequence of `#print axioms` commands on declarations defined elsewhere. The file introduces no new mathematical content; it is the one file in this list with no table row.

### Note — anonymous `example`s carrying a witness role

Two `example`s (unnamed, hence not listed above as public declarations in the strict sense) carry a significant role:

- `BornCalibration/BornExpectation.lean`, line 89: the P1 milestone's exit criterion — certifies that `grainCoherenceTheorem_projector` is importable with exactly the expected signature, with no definition specific to this repository. Still valid.
- `Core/Nonvacuity.lean`, line 62: certifies that `parentOf` type-checks against a concrete nontrivial refinement. Still valid, but its adjacent docstring is the already-flagged dead reference to `Core/Parent.lean`.
- `BornCalibration/Nonvacuity.lean`, line 24: certifies that `canonicalWeight` produces a concrete real for `uniformExpectationFamily`. Still valid.
