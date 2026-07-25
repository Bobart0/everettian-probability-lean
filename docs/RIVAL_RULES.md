# RIVAL_RULES.md

## Français

Fiche par règle rivale de pondération des branches. Consigne de rédaction
stricte : jamais « cette règle est irrationnelle », toujours « cette règle
viole précisément X » ou « cette règle ajoute précisément la structure
Y ». Aucune construction Lean n'est tentée ici au-delà de
`Rivals/NaiveBranchCounting.lean` (P1) ; les autres entrées sont des
fiches de veille, à formaliser aux jalons qui leur seront dédiés.

### Comptage naïf des branches

- **Énoncé.** Chaque cellule d'une perspective reçoit un poids
  `1 / |D.cells|`, indépendamment de tout contenu hilbertien.
- **Justification revendiquée.** Principe d'indifférence : en l'absence
  d'information distinguant les branches, les compter à égalité.
- **Prémisse violée.** L'invariance sous raffinement
  (`PayoffPreserving`) : raffiner une perspective change le nombre de
  cellules, donc le poids uniforme, sans que la conséquence sous-jacente
  ait changé.
- **Statut.** Formalisé (`Rivals/NaiveBranchCounting.lean`) ; la
  violation de `AxGrain` est un but ouvert budgété (P1, voir
  `MILESTONES.md`, clôture prévue P6).

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
- **Prémisse violée.** Viole précisément (Norm) combinée à (Grain) dès
  que `q ≠ 2` sur un espace de dimension `≥ 3` — c'est exactement le
  contenu du théorème de Gleason amont (`Gleason.gleason`), qui exclut
  toute fonction-cadre non quadratique.
- **Statut.** Non formalisé (conséquence directe d'un théorème déjà
  formalisé en amont ; formalisation locale à faible priorité).

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
"this rule adds precisely structure Y." No Lean construction is attempted
here beyond `Rivals/NaiveBranchCounting.lean` (P1); the other entries are
watch-list entries, to be formalized at their dedicated milestones.

### Naive branch counting

- **Statement.** Every cell of a perspective receives weight
  `1 / |D.cells|`, independent of any Hilbert-space content.
- **Claimed justification.** Principle of indifference: absent
  information distinguishing branches, count them equally.
- **Violated premise.** Refinement invariance (`PayoffPreserving`):
  refining a perspective changes the number of cells, hence the uniform
  weight, without the underlying consequence having changed.
- **Status.** Formalized (`Rivals/NaiveBranchCounting.lean`); the
  violation of `AxGrain` is a budgeted open goal (P1, see
  `MILESTONES.md`, planned closure P6).

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
- **Violated premise.** Violates precisely (Norm) combined with (Grain)
  as soon as `q ≠ 2` on a space of dimension `≥ 3` — this is exactly the
  content of the upstream Gleason theorem (`Gleason.gleason`), which
  rules out any non-quadratic frame function.
- **Status.** Not formalized (a direct consequence of a theorem already
  formalized upstream; local formalization is low priority).

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
