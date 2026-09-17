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
