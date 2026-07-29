# MILESTONES.md — everettian-probability-lean

## Français

### Statut courant -- 2026-07-29

| Jalon | Statut courant |
|---|---|
| Conditional Born theorem / Saint-Graal formel conditionnel | **CLOS DANS SA PORTEE PROJECTIVE FINIE ET EXPLICITEMENT CONDITIONNELLE**. Fondements : `API/ConditionalBorn.lean`, `API/DiachronicBorn.lean`, `API/ConditionalMainResults.lean`. |
| Self-location | Formalisme fini de credence conditionnee par les records etabli; unicite sous premisses d'admissibilite explicites etablie; interpretation philosophique de l'incertitude personnelle semantique, non derivee. |
| Diachronie | Continuateurs, normalisation, esperance totale, chaine, tour, composition physique et associativite formalises; identite personnelle complete non formalisee. |
| Noyau de richesse physique exacte finie | Etabli : orbite unitaire exacte, realisation de profils fins positifs compatibles et continuation physique uniforme; Hamiltonien naturel, emergence par decoherence et stabilite approximative non etablis. |

Les tableaux dates qui suivent sont conserves comme **statut historique** et
ne remplacent pas ce statut courant.

### Statut historique au 2026-07-28

| Jalon | Objet | Statut | Buts fermés dans cette reprise |
|---|---|---|---:|
| P0 | Décisions d’architecture | P0.3 et **P0.4 closes** | 0 |
| P1 | Infrastructure et squelette | Clos | 0 |
| P2 | Actes finis, tiré-en-arrière, non-vacuité bornienne | Clos | 0 |
| P3 | Représentation affine canonique | Clos | 1 |
| P4 | Invariance locale ⇔ Grain ⇒ Born (**équivalence**, pas seulement implication) | Clos, non vacueux et non trivial | 2 |
| P6 | Exclusion du comptage naïf | Résultat scalaire clos ; **P6a close** (témoin d'existence) | 2 |
| Route qubit | Espérance de Born côté effets (`EffectCalibration/`) | **Clos** — tout `n ≥ 1`, restreint aux sorties projectives | 4 |
| P8 | Conditionnement statique sur fibres de raffinement | **Clos dans sa portée formelle révisée** : conditionnement sur fibres de raffinement, loi de totalité et marginalisation conditionnelle sous composition des raffinements. Aucune dynamique temporelle, aucun continuateur et aucun record accessible ne sont formalisés. | 3 |
| P9 | Règle rivale à puissance quatrième (`q = 4`) | **Partiel** — témoin positif et non normalisé | 1 |
| P10 | Fréquences, typicalité et seuil explicite | **Clos dans sa portée finie et asymptotique quantifiée** | 0 |
| P11 | Confirmation bayésienne finie conditionnelle | **Clos dans sa portée bayésienne finie et conditionnelle** | 0 |
| P5, P6b, P7, P12 | Jalons ultérieurs | Non ouverts | 0 |

### Reprise du 2026-07-28 — P9, puissance quatrième

- `fourthPowerWeight_axPos` prouve la positivité de la règle à puissance
  quatrième.
- `fourthPowerWeight_coarse_sum` calcule exactement `337/625` sur
  `psiBefore` et `coarsePerspective`.
- `fourthPowerWeight_not_axNorm` en déduit l'échec de `AxNorm`.
- Portée strictement limitée à `q = 4`.

### Fermeture du 2026-07-28 — P10 et P11

- **P10 — clos dans sa portée finie et asymptotique quantifiée.**
  `Frequency/` construit les vecteurs de répétition, cellules et projecteurs
  de fréquence, expose les masses `frequencyMass`, leur formule binomiale et
  leur normalisation, puis établit les moments, la variance de fréquence
  relative, Chebyshev fini, les masses typique/atypique et un seuil explicite
  `exists_frequencyTypicality_threshold`. Les poids quadratiques sont ceux
  déjà calibrés : P10 n'est pas une dérivation indépendante de Born. Il ne
  requiert ni variable aléatoire mesurée, ni `PMF`, ni théorie de la mesure,
  et son énoncé asymptotique est quantifié par seuil, sans `Tendsto`.
- **P11 — clos dans sa portée bayésienne finie et conditionnelle.**
  `Confirmation/` contient le modèle bayésien fini, les évidences et
  postérieurs, les cotes, la comparaison d'hypothèses, les témoins rationnels
  à une et deux observations, la mise à jour séquentielle, les lots finis,
  l'équivalence lot/itération, les produits de rapports et la spécialisation
  aux noyaux de fréquence. Il présuppose P4/P10 et emploie ces masses comme
  vraisemblances ; il ne justifie pas Born ni la circularité philosophique,
  n'introduit aucune hypothèse vraie et ne prouve ni consistance ni
  convergence. La factorisation des lots et les non-nullités nécessaires aux
  divisions et mises à jour itérées sont des hypothèses explicites.
- `SORRY_BUDGET = 0`. Les déclarations auditées ont pour axiomes au plus
  `[propext, Classical.choice, Quot.sound]`.

### Fermetures de la reprise P3/P4

| Fichier | Ancien but | Résultat final | Buts fermés |
|---|---|---|---:|
| `Preference/Representation.lean` | `exists_unique_weights` (énoncé faux) | `canonicalWeight`, `represents`, `weights_unique_on_cells` | 1 |
| `BornCalibration/RefinementImpliesGrain.lean` | `refinement_invariant_implies_grain` | Fermé sous `RefinementInvariantLocal` | 1 |
| `BornCalibration/BornExpectation.lean` | `born_expectation_formula` | Fermé via Grain et le théorème amont | 1 |
| `Rivals/NaiveBranchCounting.lean` | `naiveCounting_violates_grain` | Calcul concret `1/2 ≠ 1/3` | 1 |

Le budget est passé de `4` à `0`. Aucun `sorry` ni `sorryAx` ne subsiste
dans une déclaration aval. La garde impose en outre qu’un éventuel futur
`sorry` porte immédiatement une annotation `SATISFIABILITY:`.

La non-vacuité accompagne la prémisse adoptée :
`bornExpectation_refinementInvariantLocal` prouve que l’espérance bornienne
satisfait l’invariance locale. Le fichier `GlobalPayoffVacuity.lean` conserve
séparément l’ancienne lecture globale comme résultat négatif et exhibe
`uniformExpectationFamily` comme contre-témoin à Grain.

La reprise de non-trivialité ajoute `uniform_not_refinementInvariantLocal` :
sur la cellule complémentaire de la paire explicite en dimension trois, la
famille uniforme donne `1/2` côté grossier et `2/3` côté fin. La prémisse
locale possède donc à la fois son témoin positif bornien et son témoin négatif
uniforme.

### Reprise du 2026-07-26 (suite) — équivalence, P0.4, classification, non-trivialité

- **`refinementInvariantLocal_iff_axGrain`** (`BornCalibration/
  RefinementImpliesGrain.lean`) : la prémisse normative n'est plus
  seulement suffisante pour Grain, elle lui est **équivalente**. Le sens
  réciproque combine `represents` avec une nouvelle identité de sommation
  générique (`grain_pullback_sum_eq`, généralisant
  `bornExpectation_pullback_eq` à tout poids satisfaisant `AxGrain`).
- **P0.4 close** : `BornCalibration/NonCircularity.lean` contient
  désormais `perspective_two_cases` (classification structurelle en
  `n = 2`) et `skewWeight` — une règle non bornienne satisfaisant
  `AxGrain`, `AxNorm`, `AxPos`, `AxNul` — avec le témoin explicite
  `grain_does_not_imply_born_at_two` (`witnessState = (3/5, 4/5)`,
  `skewF(9/25) = 81/337 ≠ 9/25`). Le fichier n'est plus un placeholder.
- **Classification de `hNul`** corrigée dans `CLAIM_MATRIX.md`,
  `docs/THEOREM_MAP.md`, `docs/SCOPE_AND_LIMITATIONS.md` : le théorème
  principal repose sur deux prémisses-ponts, pas une seule — l'invariance
  locale (normative pure) et `hNul` (normative-physique, seul point
  d'entrée de l'état `v`).
- **`maxExpectation_not_affine`** (`Preference/NonTriviality.lean`) :
  témoin négatif manquant identifié par l'audit rétroactif
  (`ARCHITECTURE_NOTES.md`) — le maximum sur les cellules est monotone et
  normalisé mais viole l'affinité, et ne peut donc pas compléter une
  `RationalExpectationFamily`.
- **Rapport de faisabilité route effets/qubit** :
  `docs/QUBIT_FEASIBILITY_REPORT.md`. Aucun code ouvert ; identifie une
  brique amont manquante nommée (`projectionEffect_weight_eq_born`/
  `contextual_projection_weight_eq_born`, déjà prouvées pour `n ≥ 1` en
  amont mais non réexportées) et trois différences structurelles de
  `Refines` empêchant une transposition telle quelle de
  `RefinementInvariantLocal`.

Budget toujours à `0` ; aucun `sorry` introduit par cette reprise.

### Reprise du 2026-07-26 (suite 2) — P6a, témoin physique de raffinement record-neutre

- **`EverettianProbability/PhysicalRefinement/`** (nouveau répertoire,
  route B — construction autonome sur Mathlib, sans dépendance amont
  supplémentaire) : témoin concret, à amplitudes inégales (`3/5`, `4/5`),
  qu'un raffinement peut redécrire les branches plus finement sans en créer
  de nouvelles au sens physique. Dans `H 3`, un ancilla à deux niveaux
  (`b 1`, `b 2`) initialisé sur `b 1` est couplé par une rotation unitaire
  `coupleU` à la branche observée `b 0`, sans jamais faire sortir la
  population de la cellule grossière complémentaire `label1Space`.
- **`RecordNeutralWitness.lean`** : les quatre théorèmes demandés, sans
  `sorry` — `recordNeutral_refines` (le raffinement en trois lignes
  raffine bien la perspective binaire grossière), `recordNeutral_record_eq`
  (le record accessible, restreint aux deux cellules grossières, est
  inchangé), `recordNeutral_payoff_eq` (le paiement tiré en arrière vaut
  `1` sur les deux cellules d'ancilla), `recordNeutral_bornWeight_eq` (les
  poids borniens des deux cellules grossières sont inchangés). L'hypothèse
  qui fait de ce raffinement un témoin *record-neutre* — les lignes
  d'ancilla ne sont pas des cellules de l'algèbre de records — est rendue
  explicite et nommée : `RefinementNotInRecordAlgebra`, prouvée dans ce modèle
  par `refinementNotInRecordAlgebra_holds`.
- **`NonTriviality.lean`** : le comptage uniforme *restreint aux cellules
  actives* (`activeCells`, `uniformCredence` — un comptage sur toutes les
  cellules de `finePerspective` serait aveugle, puisque son cardinal ne
  change pas) distingue avant et après le couplage (`1/2 ≠ 1/3`,
  `counting_sensitive_to_recordNeutral_refinement`), et la forme
  existentielle demandée `counting_underdetermined_by_accessible_record`
  exhibe deux états (`psiBefore`, `psiAfter = coupleU psiBefore`) au même
  record accessible mais à des verdicts de comptage différents.
- **`Nonvacuity.lean`** : le pendant bornien —
  `born_insensitive_to_recordNeutral_refinement` et sa généralisation
  `born_determined_by_accessible_record` — montre que l'espérance
  bornienne, à la différence du comptage, est entièrement déterminée par le
  record accessible.
- **Portée** : ce témoin établit une **existence**, pas une universalité ;
  voir l'encart dédié dans `docs/SCOPE_AND_LIMITATIONS.md`.

Budget toujours à `0` ; aucun `sorry` introduit.

### Reprise du 2026-07-27 — ménage documentaire, route qubit

- **Ménage** (commit `docs:` distinct, `7245b5e`) : `README.md` réécrit
  (décrivait encore un dépôt au jalon P1) ; référence morte à
  `Core/Parent.lean` corrigée dans `Core/Nonvacuity.lean` ; docstring de
  `BornCalibration/BornExpectation.lean` qui présentait encore le théorème
  principal (prouvé depuis P3/P4) comme un but ouvert de P1 ; `docs/
  RIVAL_RULES.md` qui présentait encore `naiveCounting_violates_grain`
  comme un `sorry` budgété ; pin périmé dans `docs/REPRODUCIBILITY.md`.
- **Reconnaissance route qubit** : le diagnostic attribué à la session
  `a9dbafe` ne s'y trouvait pas (ce commit est un ajout d'audit trivial,
  sans rapport) — re-dérivé indépendamment : la réciproque de Grain ⟹
  invariance échoue au niveau abstrait faute d'injectivité de `outcome`,
  mais les deux instances concrètes (`Subtype.val`, `Fin.val`) la
  satisfont. Voie retenue par l'utilisateur : **abstraction**.
- **Levée abstraite** (`Core/AbstractAct.lean`, `Preference/
  AbstractExpectationFunctional.lean`, `Preference/AbstractRepresentation.
  lean`, `BornCalibration/AbstractContextualWeight.lean`,
  `BornCalibration/AbstractRefinementImpliesGrain.lean`, `Refinement/
  AbstractPayoffPreserving.lean`) : `RationalExpectationFamily`,
  `represents`, `canonicalWeight`, `refinement_invariant_implies_grain`
  levés au niveau `PerspectiveInterface`, l'hypothèse d'injectivité de
  `outcome` filetée en argument à chaque théorème qui en a besoin (jamais
  ajoutée comme champ de classe — aucune instance existante cassée).
- **`EffectCalibration/`** (nouveau répertoire) : `EstimationRulePackaging.
  lean` (empaquetage du poids canonique en `EffectPerspectives.
  EstimationRule`, puisque celle-ci bundle poids/positivité/normalisation/
  grain simultanément) ; `EffectBornExpectation.lean`
  (`effectExpectation_represents`, `effectWeight_eq_born_of_invariance` —
  couvre tout `n ≥ 1`, restreint aux sorties dont l'effet est une
  projection, `hAi`) ; `QubitWitness.lean` (témoin concret en `n = 2`,
  amplitudes `3/5`, `4/5`, poids canonique `9/25` — construit sans
  `binaryPerspective`/`complementEffect` amont, non réexportés) ;
  `Nonvacuity.lean` et `NonTriviality.lean` (comptage uniforme sur toutes
  les sorties sensible à un raffinement à sortie fantôme silencieuse,
  `1/2 ≠ 2/3`, comme `Refinement/NonTriviality.lean` un niveau plus haut).
- **Clarification `n = 2`** : `grain_does_not_imply_born_at_two` reste
  vrai et ne contredit pas ce résultat — Grain seul (sans la structure des
  effets) n'implique pas Born en `n = 2` ; Grain plus la structure des
  effets, si. Écrite dans le docstring de `effectWeight_eq_born_of_
  invariance` lui-même, pas seulement dans les documents de portée.
- Pin `quantum_foundations` porté à `v1.1.2-probability-api` (export de
  `projectionEffect_weight_eq_born`, `contextual_projection_weight_eq_born`
  en dimension générale, `projectionEffect`, `ContextualNullSupport`).

Budget toujours à `0` ; aucun `sorry` introduit.

## English

### Current status -- 2026-07-29

| Milestone | Current status |
|---|---|
| Conditional Born theorem / formal conditional Saint-Graal | **CLOSED IN ITS EXPLICIT CONDITIONAL FINITE-PROJECTIVE SCOPE**. Foundations: `API/ConditionalBorn.lean`, `API/DiachronicBorn.lean`, `API/ConditionalMainResults.lean`. |
| Self-location | Finite record-conditioned credence formalism is established; uniqueness under explicit admissibility premises is established; philosophical personal uncertainty remains semantic, not derived. |
| Diachrony | Continuators, normalization, total expectation, chain, tower, physical composition, and associativity are formalized; complete personal identity is not. |
| Exact finite physical-richness core | Established: exact unitary orbit, compatible positive fine-profile realization, and uniform physical continuation; natural Hamiltonian, decoherence emergence, and approximate stability are not established. |

The dated tables below are preserved as **historical status** and do not
replace this current status.

### Historical status on 2026-07-28

| Milestone | Subject | Status | Goals closed in this resumption |
|---|---|---|---:|
| P0 | Architecture decisions | P0.3 and **P0.4 closed** | 0 |
| P1 | Infrastructure and skeleton | Closed | 0 |
| P2 | Finite acts, pullback, Born nonvacuity | Closed | 0 |
| P3 | Canonical affine representation | Closed | 1 |
| P4 | Local invariance ⇔ Grain ⇒ Born (**equivalence**, not just implication) | Closed, nonvacuous, and nontrivial | 2 |
| P6 | Exclusion of naive counting | Scalar result closed; **P6a closed** (existence witness) | 2 |
| Qubit route | Effect-side Born expectation (`EffectCalibration/`) | **Closed** — every `n ≥ 1`, restricted to projective outcomes | 4 |
| P8 | Static conditioning on refinement fibers | **Closed in its revised formal scope**: conditioning on refinement fibers, totality, and conditional marginalization under composition of refinements. No temporal dynamics, continuator, or accessible record is formalized. | 3 |
| P9 | Fourth-power rival rule (`q = 4`) | **Partial** — positive, unnormalized witness | 1 |
| P10 | Finite frequencies, typicality, explicit threshold | **Closed in its finite and quantified-asymptotic scope** | 0 |
| P11 | Finite conditional Bayesian confirmation | **Closed in its finite conditional Bayesian scope** | 0 |
| P5, P6b, P7, P12 | Later milestones | Not opened | 0 |

### 2026-07-28 resumption — P9, fourth power

- `fourthPowerWeight_axPos` proves positivity of the fourth-power rule.
- `fourthPowerWeight_coarse_sum` computes exactly `337/625` on
  `psiBefore` and `coarsePerspective`.
- `fourthPowerWeight_not_axNorm` derives failure of `AxNorm`.
- Scope is strictly limited to `q = 4`.

### P3/P4 resumption closures

| File | Former goal | Final result | Goals closed |
|---|---|---|---:|
| `Preference/Representation.lean` | `exists_unique_weights` (false statement) | `canonicalWeight`, `represents`, `weights_unique_on_cells` | 1 |
| `BornCalibration/RefinementImpliesGrain.lean` | `refinement_invariant_implies_grain` | Closed under `RefinementInvariantLocal` | 1 |
| `BornCalibration/BornExpectation.lean` | `born_expectation_formula` | Closed through Grain and the upstream theorem | 1 |
| `Rivals/NaiveBranchCounting.lean` | `naiveCounting_violates_grain` | Concrete computation `1/2 ≠ 1/3` | 1 |

The budget moved from `4` to `0`. No `sorry` or `sorryAx` remains in a
downstream declaration. The guard additionally requires any future `sorry`
to carry an immediately preceding `SATISFIABILITY:` annotation.

Nonvacuity accompanies the adopted premise:
`bornExpectation_refinementInvariantLocal` proves that Born expectation
satisfies local invariance. `GlobalPayoffVacuity.lean` separately retains the
former global reading as a negative result and exhibits
`uniformExpectationFamily` as a counter-witness to Grain.

The nontriviality resumption adds `uniform_not_refinementInvariantLocal`: on
the complement cell of the explicit dimension-three pair, the uniform family
gives `1/2` on the coarse side and `2/3` on the fine side. The local premise
therefore has both its positive Born witness and its negative uniform witness.

### 2026-07-26 resumption (continued) — equivalence, P0.4, classification, nontriviality

- **`refinementInvariantLocal_iff_axGrain`** (`BornCalibration/
  RefinementImpliesGrain.lean`): the normative premise is no longer just
  sufficient for Grain, it is **equivalent** to it. The converse combines
  `represents` with a new generic summation identity
  (`grain_pullback_sum_eq`, generalizing `bornExpectation_pullback_eq` to
  any weight satisfying `AxGrain`).
- **P0.4 closed**: `BornCalibration/NonCircularity.lean` now contains
  `perspective_two_cases` (structural classification at `n = 2`) and
  `skewWeight` — a non-Born rule satisfying `AxGrain`, `AxNorm`, `AxPos`,
  `AxNul` — with the explicit witness
  `grain_does_not_imply_born_at_two` (`witnessState = (3/5, 4/5)`,
  `skewF(9/25) = 81/337 ≠ 9/25`). The file is no longer a placeholder.
- **`hNul` classification** corrected in `CLAIM_MATRIX.md`,
  `docs/THEOREM_MAP.md`, `docs/SCOPE_AND_LIMITATIONS.md`: the headline
  theorem rests on two bridge premises, not one — local invariance
  (purely normative) and `hNul` (normative-physical, the only entry
  point for the state `v`).
- **`maxExpectation_not_affine`** (`Preference/NonTriviality.lean`): the
  missing negative witness identified by the retroactive audit
  (`ARCHITECTURE_NOTES.md`) — the max over cells is monotone and
  normalized but violates affinity, and therefore cannot complete a
  `RationalExpectationFamily`.
- **Effect/qubit route feasibility report**:
  `docs/QUBIT_FEASIBILITY_REPORT.md`. No work opened; identifies one
  named missing upstream brick
  (`projectionEffect_weight_eq_born`/`contextual_projection_weight_eq_born`,
  already proved for `n ≥ 1` upstream but not re-exported) and three
  structural differences in `Refines` preventing a direct transposition
  of `RefinementInvariantLocal`.

Budget still `0`; no `sorry` introduced by this resumption.

### 2026-07-26 resumption (continued 2) — P6a, physical witness of a record-neutral refinement

- **`EverettianProbability/PhysicalRefinement/`** (new directory, Route B —
  self-contained construction on Mathlib, no additional upstream
  dependency): a concrete witness, with unequal amplitudes (`3/5`, `4/5`),
  that a refinement can redescribe branches more finely without physically
  creating new ones. In `H 3`, a two-level ancilla (`b 1`, `b 2`)
  initialized on `b 1` is coupled by a unitary rotation `coupleU` to the
  observed branch `b 0`, never moving population out of the complementary
  coarse cell `label1Space`.
- **`RecordNeutralWitness.lean`**: the four required theorems, with no
  `sorry` — `recordNeutral_refines` (the three-line refinement does refine
  the coarse binary perspective), `recordNeutral_record_eq` (the
  accessible record, restricted to the two coarse cells, is unchanged),
  `recordNeutral_payoff_eq` (the pulled-back payoff equals `1` on both
  ancilla cells), `recordNeutral_bornWeight_eq` (the Born weights of the
  two coarse cells are unchanged). The hypothesis that makes this
  refinement a *record-neutral* witness — the ancilla lines are not cells
  of the record algebra — is made explicit and named:
  `RefinementNotInRecordAlgebra`, proved for this model by
  `refinementNotInRecordAlgebra_holds`.
- **`NonTriviality.lean`**: uniform counting *restricted to active cells*
  (`activeCells`, `uniformCredence` — counting over every cell of
  `finePerspective` would be blind, since its cardinality never changes)
  discriminates before and after the coupling (`1/2 ≠ 1/3`,
  `counting_sensitive_to_recordNeutral_refinement`), and the requested
  existential form `counting_underdetermined_by_accessible_record`
  exhibits two states (`psiBefore`, `psiAfter = coupleU psiBefore`) with
  the same accessible record but different counting verdicts.
- **`Nonvacuity.lean`**: the Born counterpart —
  `born_insensitive_to_recordNeutral_refinement` and its generalization
  `born_determined_by_accessible_record` — shows that Born expectation,
  unlike counting, is fully determined by the accessible record.
- **Scope**: this witness establishes an **existence**, not a
  universality claim; see the dedicated caveat in
  `docs/SCOPE_AND_LIMITATIONS.md`.

Budget still `0`; no `sorry` introduced.

### 2026-07-28 closure — P10 and P11

- **P10 — closed in its finite and quantified-asymptotic scope.**
  `Frequency/` constructs repetition vectors, frequency cells and
  projectors; exposes `frequencyMass`, its binomial formula and
  normalization; and proves moments, relative-frequency variance, finite
  Chebyshev, typical/atypical masses, and the explicit threshold
  `exists_frequencyTypicality_threshold`. It uses already calibrated
  quadratic weights, is not an independent derivation of Born, needs no
  measured random variable, `PMF`, or measure theory, and states its
  asymptotic result by a quantified threshold rather than `Tendsto`.
- **P11 — closed in its finite conditional Bayesian scope.**
  `Confirmation/` provides the finite Bayesian model, evidence and
  posterior weights, odds, hypothesis comparison, rational one- and
  two-observation witnesses, sequential and batch updating, their
  equivalence, likelihood-ratio products, and frequency-kernel
  specialization. It presupposes P4/P10, uses frequency masses as
  likelihoods, and neither independently justifies Born nor resolves
  philosophical circularity. Batch factorization and the nonzero
  assumptions needed for divisions and iterated updating remain explicit;
  no true hypothesis, consistency, or convergence is introduced.
- `SORRY_BUDGET = 0`. Every audited declaration has axioms contained in
  `[propext, Classical.choice, Quot.sound]`.

### 2026-07-27 resumption — documentation housekeeping, qubit route

- **Housekeeping** (distinct `docs:` commit, `7245b5e`): `README.md`
  rewritten (still described a P1-only skeleton); dead reference to
  `Core/Parent.lean` fixed in `Core/Nonvacuity.lean`; the
  `BornCalibration/BornExpectation.lean` module docstring that still
  presented the headline theorem (proved since P3/P4) as an open P1 goal;
  `docs/RIVAL_RULES.md` still calling `naiveCounting_violates_grain` a
  budgeted `sorry`; a stale pin in `docs/REPRODUCIBILITY.md`.
- **Qubit route reconnaissance**: the diagnostic attributed to session
  `a9dbafe` was not there (that commit is a trivial, unrelated audit
  addition) — independently re-derived: the converse of Grain ⟹
  invariance fails at the abstract level for want of `outcome`
  injectivity, but both concrete instances (`Subtype.val`, `Fin.val`)
  satisfy it. Route chosen by the author: **abstraction**.
- **Abstract lift** (`Core/AbstractAct.lean`, `Preference/
  AbstractExpectationFunctional.lean`, `Preference/AbstractRepresentation.
  lean`, `BornCalibration/AbstractContextualWeight.lean`,
  `BornCalibration/AbstractRefinementImpliesGrain.lean`, `Refinement/
  AbstractPayoffPreserving.lean`): `RationalExpectationFamily`,
  `represents`, `canonicalWeight`, `refinement_invariant_implies_grain`
  lifted to the `PerspectiveInterface` level, the `outcome`-injectivity
  hypothesis threaded as an argument to every theorem that needs it
  (never added as a class field — no existing instance broken).
- **`EffectCalibration/`** (new directory): `EstimationRulePackaging.lean`
  (packaging the canonical weight into `EffectPerspectives.EstimationRule`,
  since that structure bundles weight/positivity/normalization/grain
  simultaneously); `EffectBornExpectation.lean`
  (`effectExpectation_represents`, `effectWeight_eq_born_of_invariance` —
  covers every `n ≥ 1`, restricted to outcomes whose effect is a
  projection, `hAi`); `QubitWitness.lean` (concrete witness at `n = 2`,
  amplitudes `3/5`, `4/5`, canonical weight `9/25` — built without
  upstream `binaryPerspective`/`complementEffect`, not re-exported);
  `Nonvacuity.lean` and `NonTriviality.lean` (uniform counting over every
  outcome is sensitive to a refinement with a silent phantom outcome,
  `1/2 ≠ 2/3`, mirroring `Refinement/NonTriviality.lean` one level up).
- **`n = 2` clarification**: `grain_does_not_imply_born_at_two` remains
  true and does not contradict this result — Grain alone (without the
  effect structure) does not imply Born at `n = 2`; Grain plus the effect
  structure does. Written into the docstring of
  `effectWeight_eq_born_of_invariance` itself, not only in the scope
  documents.
- `quantum_foundations` pin bumped to `v1.1.2-probability-api` (exports
  `projectionEffect_weight_eq_born`, `contextual_projection_weight_eq_born`
  at general dimension, `projectionEffect`, `ContextualNullSupport`).

Budget still `0`; no `sorry` introduced.
