# RIVAL_RULES.md

## Français

Fiche par règle rivale de pondération des branches. Consigne de rédaction
stricte : jamais « cette règle est irrationnelle », toujours « cette règle
viole précisément X » ou « cette règle ajoute précisément la structure
Y ». Le comptage naïf et les deux variantes de puissance quatrième
possèdent désormais du code Lean (`Rivals/NaiveBranchCounting.lean`,
`Rivals/FourthPowerWeight.lean` et `Rivals/RenormalizedFourthPower.lean`) ;
les autres entrées restent des fiches de veille.

### Comptage naïf des branches

- **Énoncé.** Chaque cellule d'une perspective reçoit un poids
  `1 / |D.cells|`, indépendamment de tout contenu hilbertien.
- **Justification revendiquée.** Principe d'indifférence : en l'absence
  d'information distinguant les branches, les compter à égalité.
- **Prémisse violée.** L'invariance sous raffinement
  (`PayoffPreserving`) : raffiner une perspective change le nombre de
  cellules, donc le poids uniforme, sans que la conséquence sous-jacente
  ait changé.
- **Statut.** Formalisé et clos (`Rivals/NaiveBranchCounting.lean :
  naiveCounting_violates_grain`, jalon P6, voir `MILESTONES.md` et
  `CLAIM_MATRIX.md`) : la violation de `AxGrain` est intégralement prouvée,
  sans `sorry`, sur la paire binaire/trois-lignes explicite en `H 3`.

### Comptage local (Saunders 2021a)

- **Énoncé.** Le poids d'une branche dépend du nombre de sous-branches
  localement indiscernables qu'elle contient, compté dans un voisinage
  structurel plutôt que sur l'ensemble de la perspective.
- **Justification revendiquée.** Réduire la sensibilité du comptage naïf
  au découpage global de la perspective, en le rendant local.
- **Prémisse violée.** L'invariance sous raffinement reste violée dès
  qu'un raffinement local change le compte sans changer la conséquence ;
  de plus, la règle ajoute une structure de voisinage non présente dans
  `Perspective` (amont), donc hors du cadre `AxGrain`/`AxNorm`/`AxPos`/
  `AxNul` tel quel.
- **Statut.** Non formalisé. Fiche de veille.

### Comptage équi-amplitude (Saunders 2021)

- **Énoncé.** Les branches sont regroupées par classes de norme égale
  (équi-amplitude) et comptées à l'intérieur de chaque classe.
- **Justification revendiquée.** Traiter les branches de même amplitude
  comme symétriques, appliquer le principe d'indifférence à l'intérieur
  de chaque classe seulement.
- **Prémisse violée.** Ajoute précisément une structure de classes
  d'équivalence par amplitude, absente de `Perspective`/`AxGrain` ; la
  cohérence sous raffinement à l'intérieur d'une classe n'est pas
  garantie par (Grain) seul.
- **Statut.** Non formalisé. Fiche de veille.

### Comptage indexé (Khawaja 2026)

- **Énoncé.** Chaque branche porte un indice supplémentaire (par exemple
  un compteur d'enregistrements) et le poids dépend de cet indice, pas
  seulement de la cellule.
- **Justification revendiquée.** Capturer une notion de redondance ou de
  robustesse des enregistrements, au-delà de la seule structure de
  sous-espace.
- **Prémisse violée.** Ajoute précisément une donnée (l'indice) que
  `Est : Perspective n → Submodule ℂ (H n) → ℝ` ne porte pas : la règle
  n'est pas de la forme attendue par `AxGrain` sans extension du type.
- **Statut.** Non formalisé. Fiche de veille.

### `‖ψ‖^q` avec `q ≠ 2`

- **Énoncé.** Remplacer l'exposant `2` de la règle de Born par un
  exposant `q` quelconque.
- **Justification revendiquée.** Généralisation formelle, testant la
  sensibilité de la dérivation à la valeur précise de l'exposant.
- **Prémisse violée.** Dans le seul cas formalisé `q = 4`, `AxNorm` échoue
  sur le témoin explicite ; aucune affirmation générale sur Grain ou sur tous
  les exposants n'est formalisée ici.
- **Statut.** Formalisation partielle dans `Rivals/FourthPowerWeight.lean` :
  le cas `q = 4` satisfait `AxPos` mais viole `AxNorm`. La généralisation à
  tout `q ≠ 2` reste non formalisée.

### Poids histoire-dépendant

- **Énoncé.** Le poids d'une cellule dépend de l'historique complet des
  raffinements successifs qui y ont mené, pas seulement de la cellule et
  de la perspective courante.
- **Justification revendiquée.** Modéliser une dépendance à la
  trajectoire, pertinente dans des cadres à la Kent (inférences
  contraires) ou à la Riedel (enregistrements).
- **Prémisse violée.** Ajoute précisément une dépendance à l'historique
  que le type `Est : Perspective n → Submodule ℂ (H n) → ℝ` ne porte
  pas ; incompatible avec `AxGrain` tel quel, qui ne quantifie que sur
  `(D, c)`.
- **Statut.** Non formalisé. Fiche de veille.

### Amplitude × compte

- **Énoncé.** Le poids d'une branche est le produit de son amplitude au
  carré et d'un facteur de comptage (par exemple le nombre de
  sous-branches qu'elle contient), plutôt que l'amplitude au carré seule.
- **Justification revendiquée.** Combiner la sensibilité hilbertienne de
  Born avec une sensibilité combinatoire au découpage.
- **Prémisse violée.** Viole (Norm) dès que le facteur de comptage n'est
  pas identiquement `1` sur toute perspective normalisée ; ajoute
  précisément un degré de liberté combinatoire que (Grain) seul ne
  contraint pas à disparaître.
- **Statut.** Non formalisé. Fiche de veille.

## English

One entry per rival branch-weighting rule. Strict drafting rule: never
"this rule is irrational," always "this rule violates precisely X" or
"this rule adds precisely structure Y." Naive counting and both fourth-power
variants now have Lean code (`Rivals/NaiveBranchCounting.lean`,
`Rivals/FourthPowerWeight.lean`, and
`Rivals/RenormalizedFourthPower.lean`); the other entries remain watch-list
notes.

### Naive branch counting

- **Statement.** Every cell of a perspective receives weight
  `1 / |D.cells|`, independent of any Hilbert-space content.
- **Claimed justification.** Principle of indifference: absent
  information distinguishing branches, count them equally.
- **Violated premise.** Refinement invariance (`PayoffPreserving`):
  refining a perspective changes the number of cells, hence the uniform
  weight, without the underlying consequence having changed.
- **Status.** Formalized and closed (`Rivals/NaiveBranchCounting.lean :
  naiveCounting_violates_grain`, milestone P6, see `MILESTONES.md` and
  `CLAIM_MATRIX.md`): the violation of `AxGrain` is fully proved, with no
  `sorry`, on the explicit binary/three-line pair in `H 3`.

### Local counting (Saunders 2021a)

- **Statement.** The weight of a branch depends on the number of locally
  indistinguishable sub-branches it contains, counted within a
  structural neighborhood rather than over the whole perspective.
- **Claimed justification.** Reduce naive counting's sensitivity to the
  global partitioning of the perspective, by making it local.
- **Violated premise.** Refinement invariance is still violated as soon
  as a local refinement changes the count without changing the
  consequence; moreover, the rule adds a neighborhood structure absent
  from `Perspective` (upstream), hence outside the
  `AxGrain`/`AxNorm`/`AxPos`/`AxNul` framework as it stands.
- **Status.** Not formalized. Watch-list entry.

### Equi-amplitude counting (Saunders 2021)

- **Statement.** Branches are grouped into equal-norm (equi-amplitude)
  classes and counted within each class.
- **Claimed justification.** Treat equal-amplitude branches as
  symmetric, applying the indifference principle only within each class.
- **Violated premise.** Adds precisely an equivalence-class-by-amplitude
  structure, absent from `Perspective`/`AxGrain`; coherence under
  refinement within a class is not guaranteed by (Grain) alone.
- **Status.** Not formalized. Watch-list entry.

### Indexed counting (Khawaja 2026)

- **Statement.** Every branch carries an additional index (e.g. a
  record count), and the weight depends on that index, not only on the
  cell.
- **Claimed justification.** Capture a notion of record redundancy or
  robustness, beyond subspace structure alone.
- **Violated premise.** Adds precisely a datum (the index) that
  `Est : Perspective n → Submodule ℂ (H n) → ℝ` does not carry: the
  rule is not of the form `AxGrain` expects without extending the type.
- **Status.** Not formalized. Watch-list entry.

### `‖ψ‖^q` with `q ≠ 2`

- **Statement.** Replace the Born rule's exponent `2` with an arbitrary
  exponent `q`.
- **Claimed justification.** Formal generalization, testing the
  derivation's sensitivity to the exact exponent value.
- **Violated premise.** In the sole formalized case `q = 4`, `AxNorm` fails
  on the explicit witness; no general assertion about Grain or all exponents
  is formalized here.
- **Status.** Partial formalization in `Rivals/FourthPowerWeight.lean`:
  the `q = 4` case satisfies `AxPos` but violates `AxNorm`. Generalization to
  every `q ≠ 2` remains unformalized.

### History-dependent weight

- **Statement.** The weight of a cell depends on the full history of
  successive refinements that led to it, not only on the cell and the
  current perspective.
- **Claimed justification.** Model path-dependence, relevant in
  Kent-style (contrary inferences) or Riedel-style (records) settings.
- **Violated premise.** Adds precisely a history dependence that the
  type `Est : Perspective n → Submodule ℂ (H n) → ℝ` does not carry;
  incompatible with `AxGrain` as it stands, which only quantifies over
  `(D, c)`.
- **Status.** Not formalized. Watch-list entry.

### Amplitude × count

- **Statement.** The weight of a branch is the product of its squared
  amplitude and a counting factor (e.g. the number of sub-branches it
  contains), rather than the squared amplitude alone.
- **Claimed justification.** Combine Born's Hilbert-space sensitivity
  with a combinatorial sensitivity to partitioning.
- **Violated premise.** Violates (Norm) as soon as the counting factor
  is not identically `1` on every normalized perspective; adds precisely
  a combinatorial degree of freedom that (Grain) alone does not force
  away.
- **Status.** Not formalized. Watch-list entry.

### E1.1--E1.5 : comptage indexe et puissance quatrieme renormalisee

- **Comptage indexe.** Reference exacte : Khawaja, “Conquering Mount Everett:
  Branch Counting Versus the Born Rule,” *British Journal for the Philosophy
  of Science* 77(2), 313–344, 2026, DOI 10.1086/726282. Statut : non
  formalise, fiche de veille. Aucune formalisation de cette regle n'est
  entreprise dans cet increment.
- **Puissance quatrieme renormalisee.** Pour `v ≠ 0`, le denominateur est
  strictement positif et la regle satisfait `AxPos` et `AxNorm`. Le temoin
  explicite en `H 3` etablit une violation precise de `AxGrain` : le poids de
  `label0Line` est `81/337` sur la perspective binaire et `50625/136897` sur le
  raffinement en trois lignes.
- **Accord avec Born.** A perspective fixee et pour `‖v‖ = 1`,
  `renormalizedFourthPower_agrees_iff` prouve l'equivalence complete avec
  l'egalite des poids de Born non nuls. Le resultat est formalise et audite
  dans `Rivals/RenormalizedFourthPower.lean`, `Rivals/BornAgreement.lean` et
  `Audit/BornAgreement.lean`.
- **Condition de non-nullite.** La condition `v ≠ 0` est explicite pour la
  positivite du denominateur, `AxPos` et `AxNorm`; a `v = 0`, la definition
  donne `0/0 = 0`, donc `AxNorm` ne peut pas etre affirme.

## E1.1--E1.5: indexed counting and renormalized fourth power

- **Indexed counting.** Exact reference: Khawaja, “Conquering Mount Everett:
  Branch Counting Versus the Born Rule,” *British Journal for the Philosophy
  of Science* 77(2), 313–344, 2026, DOI 10.1086/726282. Status: not
  formalized, watch-list entry. This increment does not formalize that rule.
- **Renormalized fourth power.** For `v ≠ 0`, the denominator is strictly
  positive and the rule satisfies `AxPos` and `AxNorm`. The explicit `H 3`
  witness establishes a precise `AxGrain` violation: the weight of
  `label0Line` is `81/337` on the binary perspective and `50625/136897` on the
  three-line refinement.
- **Agreement with Born.** At a fixed perspective and for `‖v‖ = 1`,
  `renormalizedFourthPower_agrees_iff` proves the complete equivalence with
  equality of the nonzero Born weights. The result is formalized and audited
  in `Rivals/RenormalizedFourthPower.lean`, `Rivals/BornAgreement.lean`, and
  `Audit/BornAgreement.lean`.
- **Nonzero condition.** The condition `v ≠ 0` is explicit for denominator
  positivity, `AxPos`, and `AxNorm`; at `v = 0`, the definition gives
  `0/0 = 0`, so `AxNorm` cannot be asserted.

## E2 -- comparaison bayesienne conditionnelle / conditional Bayesian comparison

### Français

Le module `Confirmation/BornVersusRenormalizedFourthPower.lean` construit un
`FiniteBayesModel` a deux hypotheses, avec un a priori uniforme. Born fournit
ses propres vraisemblances par `bornWeight`; la rivale fournit ses propres
vraisemblances par `renormalizedFourthPower`. Aucune vraisemblance des deux
hypotheses n'est engendree a partir de Born seul. Les resultats sont
conditionnels au principe CW qualitatif de Greaves--Myrvold ; ils ne
l'etablissent pas et ne portent aucun jugement de rationalite.

Sous la condition d'accord de `Rivals/BornAgreement.lean`, E2.3a prouve
l'identite des vraisemblances sur toute cellule, des produits de
vraisemblances, des contributions d'evidence et des poids posterieurs pour
toute liste, y compris les cellules de poids nul. E2.3b ajoute la non-nullite
des observations seulement pour definir le facteur de Bayes et les cotes par
division. Quand toute la perspective est de support non nul, le temoin
singleton `agreementPerspective` illustre E2.3c sans restriction de liste.

Sur le temoin rationnel de `H 3`, les facteurs Born/rivale sont `337/225`
pour `label0Line` et `337/400` pour `label1Space`; ils sont respectivement
strictement superieur et strictement inferieur a `1`. Pour deux puis trois
observations `label0Line`, les facteurs de lot sont exactement
`113569/50625` et `38272753/11390625`. Cela mesure seulement la comparaison
algebrique des deux vraisemblances propres ; cela n'etablit ni CW, ni une
conclusion decisionnelle, ni un taux de discrimination general.

**Statut.** E2.2--E2.5 sont formalises et audites par
`Audit/BornVersusRenormalizedFourthPower.lean`. La condition de support de
E2.3b est une condition de definition du conditionnement bayesien, pas un
affaiblissement de l'identite observationnelle inconditionnelle E2.3a.

### English

`Confirmation/BornVersusRenormalizedFourthPower.lean` builds a
`FiniteBayesModel` with two hypotheses and a uniform prior. Born supplies its
own likelihoods through `bornWeight`; the rival supplies its own likelihoods
through `renormalizedFourthPower`. Neither hypothesis is assigned
likelihoods generated from Born alone. The results are conditional on the
qualitative Greaves--Myrvold CW principle; they do not establish it and make
no rationality judgment.

Under the agreement condition from `Rivals/BornAgreement.lean`, E2.3a proves
identity of likelihoods on every cell, likelihood products, evidence
contributions, and posterior weights for every list, including zero-weight
cells. E2.3b adds nonzero observations only to define Bayes factors and odds
by division. When the whole perspective has nonzero support, the singleton
`agreementPerspective` witness illustrates E2.3c without a list restriction.

On the rational `H 3` witness, the Born/rival factors are `337/225` for
`label0Line` and `337/400` for `label1Space`; they are respectively strictly
above and strictly below `1`. For two and then three observations of
`label0Line`, the exact batch factors are `113569/50625` and
`38272753/11390625`. This is only an algebraic comparison of the two proper
likelihoods; it establishes neither CW, nor a decision-theoretic conclusion,
nor a general discrimination rate.

**Status.** E2.2--E2.5 are formalized and audited by
`Audit/BornVersusRenormalizedFourthPower.lean`. The E2.3b support condition is
a condition for defining Bayesian conditioning, not a weakening of the
unconditional observational identity in E2.3a.

## E3 -- taux de discrimination / discrimination rate

### Français

**Formalisé.** `Rivals/SupportAgreement.lean` prouve, pour `v ≠ 0`, que la
règle de Born et la règle à puissance quatrième renormalisée ont exactement
le même support. Il prouve aussi l'invariance d'échelle de la règle
renormalisée et la loi `bornWeight (t • v) D c = ‖t‖² * bornWeight v D c`.
La renormalisation rend la règle rivale automatiquement normalisée sur tout
état non nul, tandis que la règle de Born est utilisée ici sur les états
unitaires.

**Formalisé.** `Confirmation/DiscriminationRate.lean` définit les deux taux
comme des sommes finies de log-facteurs de Bayes, chaque hypothèse fournissant
ses propres vraisemblances. Sous `‖v‖ = 1`, l'inégalité de Gibbs est prouvée
pour les deux sens. Le taux de Born est nul si et seulement si les deux
règles coïncident cellule par cellule, donc si et seulement si la condition
de `BornAgreement.lean` est satisfaite.

Le témoin `psiAfter`/`coarsePerspective` donne exactement
`(9/25) * log (337/225) + (16/25) * log (337/400)` et sa stricte positivité
est prouvée par le théorème d'égalité et le témoin de désaccord. La valeur
décimale est seulement indicative et externe au noyau.

**Non formalisé.** E3.6, la linéarité d'un log-facteur de Bayes espéré en
fonction de `N`, demanderait une loi produit explicite sur les suites. Aucun
résultat de concentration, asymptotique ou décisionnel n'est ajouté.

Tous les résultats E3 restent conditionnels au principe CW de
Greaves--Myrvold ; ils ne l'établissent pas et ne portent aucun jugement de
rationalité.

### English

**Formalized.** `Rivals/SupportAgreement.lean` proves, for `v ≠ 0`, that the
Born rule and the renormalized fourth-power rule have exactly the same
support. It also proves scale invariance of the rival rule and the law
`bornWeight (t • v) D c = ‖t‖² * bornWeight v D c`. Renormalization makes the
rival rule automatically normalized on every nonzero state, whereas the Born
rule is used here on unit states.

**Formalized.** `Confirmation/DiscriminationRate.lean` defines both rates as
finite sums of log Bayes factors, with each hypothesis supplying its own
likelihoods. Under `‖v‖ = 1`, Gibbs' inequality is proved in both directions.
The Born rate is zero iff the two rules agree cellwise, hence iff the
condition from `BornAgreement.lean` holds.

The `psiAfter`/`coarsePerspective` witness gives exactly
`(9/25) * log (337/225) + (16/25) * log (337/400)`, and strict positivity is
proved from the equality theorem and the disagreement witness. The decimal
value is only indicative and external to the kernel.

**Not formalized.** E3.6, linearity of an expected log Bayes factor in `N`,
would require an explicit product law on sequences. No concentration,
asymptotic, or decision-theoretic result is added.

All E3 results remain conditional on Greaves--Myrvold's CW principle; they do
not establish it and make no rationality judgment.
