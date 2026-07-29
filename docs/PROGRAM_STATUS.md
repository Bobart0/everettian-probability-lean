# PROGRAM_STATUS.md

> État du programme complet (pas seulement de l'article II), au 2026-07-26.
> Document délibérément sévère : un jalon à peine entamé n'est pas classé
> **PARTIEL**, et un jalon jamais défini nulle part dans ce dépôt est
> signalé comme tel plutôt que rempli par supposition.
>
> Status of the full programme (not just paper II), as of 2026-07-26. This
> document is deliberately severe: a barely-started milestone is not
> classified **PARTIAL**, and a milestone never defined anywhere in this
> repository is flagged as such rather than filled in by guesswork.

## Français

### Statut de release courant -- 2026-07-29

| Jalon | Statut courant | Portee exacte |
|---|---|---|
| Résultat conditionnel de Born | **CLOS DANS SA PORTEE PROJECTIVE FINIE ET EXPLICITEMENT CONDITIONNELLE** | API conditionnelle stable `v1.x`; resultats statiques et diachroniques sous premisses explicites. |
| Self-location | Etabli sous forme finie conditionnee par record | Unicite sous admissibilite; l'incertitude personnelle reste une premisse semantique. |
| Diachronie | Formalisee dans la portee abstraite explicite | Continuateurs, normalisation, esperance totale, chaine et tour; pas d'identite personnelle complete. |
| Physique exacte finie | Noyau etabli | Orbite unitaire et plans fins compatibles; pas de Hamiltonien naturel, decoherence emergente ni robustesse approximative. |
| Résultat physique exact fini | **CLOS DANS SA PORTEE EXACTE, PROJECTIVE FINIE ET EXPLICITEMENT CALIBREE** / **CLOSED IN ITS EXACT FINITE-PROJECTIVE AND EXPLICITLY CALIBRATED SCOPE** | `ExactFinite/MainResults.lean` agrège CORE et CALIBRATED; voir `docs/EXACT_FINITE_COMPLETENESS_AUDIT.md`. |
| EF0–EF9 | **AUDITÉS** | Codification : `docs/EXACT_FINITE_STAGES.md`; EF9 est audité. |
| EF10 | **FIGÉ — PUBLICATION EN ATTENTE** | Façade publique et contrat v2.0.0. |
| P5, P6b, P12, preferences primitives | A traiter dans des jalons ulterieurs | Le noyau de richesse exacte ne declare pas automatiquement toute formulation historique de P6b resolue. |

Le diagnostic date ci-dessous est un **diagnostic historique**. Il ne constitue
pas le statut courant de la release `v1.0.0`.

### Statut historique — 2026-07-28

| Jalon | Statut courant | Portée exacte |
|---|---|---|
| P10 | **CLOS** | Fréquences finies, typicalité et seuil explicite quantifié; poids quadratiques déjà calibrés, sans `PMF`, mesure ni `Tendsto`. |
| P11 | **CLOS** | Confirmation bayésienne finie conditionnelle; masses P10 utilisées comme vraisemblances, sous factorisation conditionnelle et non-nullités explicites. |
| P5, P6b, P7, P12, route des préférences primitives | **OUVERTS** | Aucun de ces jalons n'est clos par P10/P11. |
| P8 | **CLOS dans sa portée révisée** | Conditionnement statique sur fibres de raffinement, pas de dynamique temporelle générale. |
| P9 | **PARTIEL** | Témoin `q = 4` seulement; pas de fermeture complète. |

Les passages de diagnostic antérieurs disant que P10 ou P11 n'étaient pas
entamés sont historiques (antérieurs à cette fermeture) et ne constituent
pas le statut courant.

### Diagnostic historique — 2026-07-26

La table et les analyses qui suivent décrivent l'état constaté le 2026-07-26,
avant l'ouverture puis la fermeture documentaire de P10/P11; elles sont
conservées pour la traçabilité et ne constituent pas le statut courant.

#### Table des jalons

| Jalon | Objet | Statut | Ce qui existe | Ce qui manque | Dépendances |
|---|---|---|---|---|---|
| P0.1 | Non retracé séparément dans aucun document du dépôt. | Statut indéterminé | `AGENTS.md` ne mentionne que « P0.2–P0.4 » ; aucun document ne nomme un P0.1 distinct. | Une définition. | — |
| P0.2 | Idem — non nommé séparément ; probablement absorbé par la décision P0.3 documentée. | Statut indéterminé | Voir P0.3. | Une définition séparée, ou confirmation qu'il n'existe pas en tant que jalon distinct. | — |
| P0.3 | Décision d'architecture : l'interface commune des perspectives reste en aval, les actes sont totaux, les sous-types de cellules ne servent qu'à l'énumération. | **CLOS** | `Core/Interface.lean` (`PerspectiveInterface`, instances `Projective`/`Effects`), documenté dans `CLAIM_MATRIX.md` et `ARCHITECTURE_NOTES.md`. | — | — |
| P0.4 | Témoin de non-circularité en `n = 2` : Grain seul n'implique pas Born. | **CLOS** | `BornCalibration/NonCircularity.lean : grain_does_not_imply_born_at_two`. | — | Théorème de Gleason amont (absence en `n = 2`, exploitée, pas contournée). |
| P1 | Infrastructure du dépôt, squelette compilable. | **CLOS** | Voir `README.md`, `MILESTONES.md`. | — | — |
| P2 | Actes finis, tiré-en-arrière, non-vacuité bornienne. | **CLOS** | `Refinement/PullbackAct.lean`, `PayoffPreserving.lean`, `Nonvacuity.lean`. | — | — |
| P3 | Représentation affine canonique. | **CLOS** | `Preference/Representation.lean : represents`, `weights_unique_on_cells`. | — | — |
| P4 | Invariance locale ⇔ Grain ⇒ Born. | **CLOS** | `BornCalibration/RefinementImpliesGrain.lean`, `BornExpectation.lean`. | — | `grainCoherenceTheorem_projector` amont (`3 ≤ n`). |
| P5 | **Non défini dans ce dépôt.** | **NON ENTAMÉ** (non spécifié) | Rien. | Une définition — voir la sous-section dédiée ci-dessous. | Inconnues tant que non défini. |
| P6 | Exclusion du comptage naïf (résultat scalaire). | **CLOS** | `Rivals/NaiveBranchCounting.lean : naiveCounting_violates_grain`. | — | — |
| P6a | Témoin physique de raffinement record-neutre (existence). | **CLOS** — témoin d'existence, pas d'universalité | `PhysicalRefinement/`. | Une généralisation (voir P6b). | — |
| P6b | Pont « invariance restreinte + réalisabilité physique ⟹ Grain complet », esquissé dans `ARCHITECTURE_NOTES.md` sous « voie d'amélioration visée, non acquise ». Jamais nommé « P6b » nulle part dans ce dépôt — inféré du prompt de cette session et de l'architecture cible déjà écrite. | **NON ENTAMÉ** | L'architecture cible en une ligne (`ARCHITECTURE_NOTES.md`) et le témoin d'existence P6a comme brique isolée. | Voir la sous-section dédiée. | P6a ; brique amont nommée (porte de rotation d'amplitude contrôlée, `docs/SCOPE_AND_LIMITATIONS.md`). |
| P7 | Auto-localisation. Correspond au répertoire `SelfLocation/` annoncé par `README.md` comme « pas encore ouvert ». | **NON ENTAMÉ** | Rien en Lean ; le nom du répertoire cible seulement. | Voir la sous-section dédiée. | — |
| P8 | Cohérence diachronique. Correspond à `Diachronic/`. | **NON ENTAMÉ** | Rien en Lean. | Voir la sous-section dédiée. | — |
| P9 | Banc des rivales, au-delà du comptage naïf déjà clos (P6). | **NON ENTAMÉ** | `docs/RIVAL_RULES.md` : six fiches de veille en prose (comptage local, équi-amplitude, indexé, `‖ψ‖^q`, poids histoire-dépendant, amplitude×compte), chacune avec la prémisse qu'elle viole nommée. Aucun code Lean. | Voir la sous-section dédiée. | — |
| P10 | Fréquences et typicalité. | **NON ENTAMÉ** | Rien, ni code ni note de veille dans ce dépôt. | Voir la sous-section dédiée. | — |
| P11 | Confirmation bayésienne. Correspond à `Confirmation/`. `README.md` la présente comme le jalon de clôture du programme (« rien n'est citable avant P11 »). | **NON ENTAMÉ** | Rien en Lean. | Voir la sous-section dédiée. | — |
| P12 | Stabilité approximative. Correspond à `Approximate/`. Postérieure à P11 dans l'ordre du prompt de cette session, ce qui contredit la présentation de `README.md` où P11 est la clôture — incohérence documentaire à signaler, pas à corriger ici. | **NON ENTAMÉ** | Rien. | Voir la sous-section dédiée. | — |
| Route qubit / effets | Généraliser la route projective (`n ≥ 3`) via la route effets, potentiellement `n ≥ 1`. | **NON ENTAMÉ** (zéro ligne de Lean), mais avec un travail préparatoire inhabituellement substantiel | `docs/QUBIT_FEASIBILITY_REPORT.md` (analyse complète : brique manquante nommée, trois différences structurelles, estimation d'effort, quatre risques classés) ; `Core/Interface.lean` (`Effects.interface`, `Effects.pureState_refinementInvariant`) comme scaffold partiel mais **plus faible** (part d'une règle qui satisfait déjà Grain par construction). | Voir la sous-section dédiée. | Export amont additif (`projectionEffect_weight_eq_born`/`contextual_projection_weight_eq_born`), approbation humaine (règle 8, `AGENTS.md`). |
| Route B des préférences primitives | **Aucune trace dans ce dépôt** — ni dans `AGENTS.md`, ni `MILESTONES.md`, ni `CLAIM_MATRIX.md`, ni aucun fichier Lean. | **NON ENTAMÉ** (non défini) | Rien. | Une définition. | Inconnues. |

### P5 — les trois questions

- **Échafaudage réutilisable ?** Aucun. P5 n'apparaît dans aucun document
  de ce dépôt autrement que comme une étiquette dans la liste « P5,
  P7–P11 : non ouverts ». Il n'y a même pas une phrase décrivant son objet.
- **Preuve ou conception ?** Ni l'un ni l'autre n'est encore posable : la
  question qui précède les deux — *que désigne P5 ?* — n'a jamais été
  tranchée dans ce dépôt.
- **Décisions non formelles préalables.** La seule décision requise avant
  toute autre chose est de **documenter ce que P5 désigne**. Tant que cette
  décision n'est pas prise et écrite quelque part (dans `MILESTONES.md` ou
  ailleurs), toute tentative de formaliser « P5 » serait une invention, pas
  une reprise d'un plan existant.

### P6b — les trois questions

- **Échafaudage réutilisable ?** Partiel. `ARCHITECTURE_NOTES.md` fixe déjà
  l'architecture cible en une ligne (« invariance restreinte + réalisabilité
  physique ⇒ Grain complet ⇒ Born ») et P6a fournit une brique isolée (un
  témoin d'existence). Mais aucune des deux notions requises pour
  généraliser — « Grain restreint aux raffinements record-neutres » comme
  `Prop` paramétrée, et une caractérisation de la classe des raffinements
  couverts — n'existe encore.
- **Preuve ou conception ?** Conception d'abord, et la question de
  conception est substantielle : le témoin P6a est **un** exemple ; passer
  de « un raffinement record-neutre existe » à « Grain restreint aux
  raffinements record-neutres force Born » exige soit (a) un théorème de
  généralisation montrant qu'une classe assez large de raffinements est
  record-neutre (un résultat mathématique dont la vérité n'est même pas
  acquise), soit (b) l'acceptation explicite d'un théorème plus faible que
  l'actuel `born_expectation_of_invariance`, restreint dès l'énoncé à cette
  classe. Ce choix change la portée revendiquée du résultat principal.
- **Décisions non formelles préalables.** (i) Définir formellement
  « raffinement record-neutre » pour une paire `(D', D)` **générale**, pas
  seulement pour le couple `coarsePerspective`/`finePerspective` de P6a.
  (ii) Décider si l'objectif est la généralisation complète (récupérer
  `AxGrain` non restreint) ou un théorème authentiquement restreint (une
  conclusion plus faible, honnêtement présentée comme telle). (iii) Statuer
  sur la brique amont nommée dans `docs/SCOPE_AND_LIMITATIONS.md` — une
  porte de rotation d'amplitude contrôlée, combinant `ControlledBitFlip` et
  `AmplitudeRotation` — dont la construction et l'export ne sont pas
  décidés.

### P7 — les trois questions

- **Échafaudage réutilisable ?** Aucun, ni en amont ni en aval. Le
  répertoire `SelfLocation/` n'existe pas. Mathlib fournit une théorie des
  probabilités générale, mais rien de spécifique à l'incertitude
  auto-localisante n'est câblé dans ce dépôt.
- **Preuve ou conception ?** Conception, presque exclusivement. C'est
  l'exemple que le prompt de cette session cite lui-même : il n'existe pas
  de sémantique formelle consensuelle de l'incertitude auto-localisante
  dans une structure de branchement déterministe. La littérature
  philosophique (Elga, Lewis, Sebens–Carroll sur le principe de séparabilité
  épistémique) propose des lectures concurrentes, non convergentes.
- **Décisions non formelles préalables.** Choisir **une** sémantique de
  l'incertitude auto-localisante (crédence en être tel successeur futur
  parmi plusieurs, pondérée comment ?) avant d'écrire le moindre type Lean.
  Cette décision est philosophique, pas mathématique, et aucun dépôt amont
  ne la fournit.

### P8 — les trois questions

- **Échafaudage réutilisable ?** Aucun. Le répertoire `Diachronic/`
  n'existe pas. `Refines` (amont) est une relation **statique** entre deux
  perspectives ; rien ne modélise une séquence temporelle de raffinements.
- **Preuve ou conception ?** Mixte. Conception d'abord : que signifie « la
  crédence reste cohérente au fil du temps » dans un cadre où le temps
  n'est représenté par aucune structure existante — une chaîne de
  `Refines`, ou un index temporel indépendant du raffinement ? Une fois
  cette question tranchée, le volume de preuve attendu est comparable à
  P3+P4 (par analogie avec l'estimation donnée pour la route effets dans
  `docs/QUBIT_FEASIBILITY_REPORT.md`).
- **Décisions non formelles préalables.** Décider si « diachronique »
  signifie une conditionnalisation bayésienne littérale, ou une notion
  propre au branchement (cohérence diachronique au sens de Wallace,
  distincte de la mise à jour bayésienne standard). Ces deux lectures
  mènent à des formalisations disjointes.

### P9 — les trois questions

- **Échafaudage réutilisable ?** Le meilleur de tous les jalons non
  entamés : `docs/RIVAL_RULES.md` fournit six règles rivales déjà
  identifiées, chacune avec sa prémisse violée nommée. Une (`‖ψ‖^q` avec
  `q ≠ 2`) est explicitement notée comme « conséquence directe d'un
  théorème déjà formalisé en amont » (le théorème de Gleason lui-même) —
  quasiment gratuite à formaliser.
- **Preuve ou conception ?** Cela dépend de la règle. `‖ψ‖^q` : preuve
  presque immédiate. Comptage indexé, poids histoire-dépendant : conception
  d'abord, puisque le type `Est : Perspective n → Submodule ℂ (H n) → ℝ`
  ne porte pas les données supplémentaires (indice, historique) que ces
  règles présupposent — il faut décider comment étendre le type avant de
  pouvoir énoncer quoi que ce soit.
- **Décisions non formelles préalables.** Pour les règles qui excèdent le
  type `Est` actuel : décider s'il faut étendre ce type partagé (au risque
  de casser la comparabilité directe avec `AxGrain` tel qu'énoncé) ou
  donner à chaque règle son propre type ad hoc (au risque de rendre les
  comparaisons entre règles rivales non uniformes).

### P10 — les trois questions

- **Échafaudage réutilisable ?** Aucun dans ce dépôt. La littérature plus
  large (mesure d'existence de Vaidman, notions de typicité) existe hors
  de ce dépôt mais n'y est ni citée ni câblée.
- **Preuve ou conception ?** Conception, de façon dominante, et le risque
  conceptuel est spécifique : toute notion de « fréquence » construite à
  partir des poids borniens eux-mêmes risque la circularité que la
  décomposition du problème (maillon 1 de `docs/ARGUMENT_MAP.md`) identifie
  comme le « problème de confirmation » — utiliser Born pour justifier Born
  via un opérateur de fréquence qui présuppose déjà Born.
- **Décisions non formelles préalables.** Définir ce qu'est une
  « fréquence » ou une « typicalité » dans une structure de branchement
  purement déterministe, indépendamment de toute présupposition du poids
  bornien — sans quoi le jalon ne peut que présupposer ce qu'il devrait
  établir.

### P11 — les trois questions

- **Échafaudage réutilisable ?** Aucun dans ce dépôt. Mathlib fournit une
  théorie des probabilités et de l'inférence bayésienne générale,
  techniquement disponible en amont, mais rien ne la relie à `Perspective`/
  `Act` ici.
- **Preuve ou conception ?** Conception d'abord — le problème classique de
  la confirmation everettienne (Greaves & Myrvold, Wallace) est
  précisément que la confirmation bayésienne présuppose déjà une fonction
  de crédence à mettre à jour, ce que P4 fournit seulement sous ses deux
  prémisses-ponts. Décider si P11 présuppose P4 comme acquis ou tente une
  justification indépendante change entièrement la formalisation à
  entreprendre.
- **Décisions non formelles préalables.** Trancher le statut logique de
  P4 par rapport à P11 (prémisse admise, ou objet lui-même à justifier).
  Noter aussi, en toute franchise, que `README.md` présente P11 comme la
  clôture du programme entier (« rien n'est citable avant P11 ») —
  affirmation que l'existence même de P12 dans le prompt de cette session
  rend caduque, sans que `README.md` ait été mis à jour.

### P12 — les trois questions

- **Échafaudage réutilisable ?** Aucun.
- **Preuve ou conception ?** Conception d'abord : « stabilité
  approximative » présuppose une métrique ou une norme quantifiant ce que
  signifie « presque » satisfaire `RefinementInvariantLocal` ou le
  caractère record-neutre d'un raffinement. Aucune de ces notions
  n'existe dans ce dépôt.
- **Décisions non formelles préalables.** Choisir l'espace des
  perturbations pertinent (perturber la prémisse ? l'état ? le
  raffinement ?) et la métrique associée, avant de pouvoir énoncer un
  théorème de stabilité au sens mathématique du terme.

### Route qubit / effets — les trois questions

- **Échafaudage réutilisable ?** Oui, substantiellement : voir
  `docs/QUBIT_FEASIBILITY_REPORT.md`. Ce rapport nomme précisément la
  brique manquante amont, caractérise les trois différences structurelles
  avec la route projective, chiffre l'effort (une session complète,
  comparable à P3+P4) et classe quatre risques par ordre décroissant. C'est
  l'inverse du cas P5 : ici, la question « que faudrait-il faire » a déjà
  une réponse écrite et précise.
- **Preuve ou conception ?** Majoritairement preuve/ingénierie — le
  rapport qualifie lui-même le gros du travail de « retypage mécanique
  mais volumineux » (copier `Preference`/`BornCalibration` contre
  `Fin D.outcomes` plutôt que `Submodule ℂ (H n)`). Une vraie question de
  conception subsiste : caractériser l'extension exacte des raffinements
  atteignables par composition des quatre constructeurs amont de
  `Refines`-effets, avant de pouvoir revendiquer une prémisse aussi large
  que côté projectif.
- **Décisions non formelles préalables.** Demander l'export amont
  strictement additif (`projectionEffect_weight_eq_born`/
  `contextual_projection_weight_eq_born`) — décision qui, par la règle 8 de
  `AGENTS.md`, appartient au mainteneur humain, pas à une session de
  travail. Sans cet export, la route effets reste bornée aux
  spécialisations qubit déjà réexportées.

### Route B des préférences primitives — les trois questions

Aucune des trois questions n'a de réponse défendable : ce nom n'apparaît
dans aucun fichier de ce dépôt, Lean ou Markdown. Y répondre reviendrait à
spéculer au-delà de ce que ce dépôt atteste. La seule réponse honnête est :
la première décision non formelle est de documenter, quelque part, ce que
ce nom désigne — exactement le même défaut que P5, sous un nom différent.

## English

### Current release status -- 2026-07-29

| Milestone | Current status | Exact scope |
|---|---|---|
| Conditional Born result | **CLOSED IN ITS EXPLICIT CONDITIONAL FINITE-PROJECTIVE SCOPE** | Stable `v1.x` conditional API; static and diachronic results under explicit premises. |
| Self-location | Established as finite record-conditioned formalism | Uniqueness under admissibility; personal uncertainty remains a semantic premise. |
| Diachrony | Formalized in its explicit abstract scope | Continuators, normalization, total expectation, chain, and tower; no complete personal identity. |
| Exact finite physics | Core established | Unitary orbit and compatible fine plans; no natural Hamiltonian, emergent decoherence, or approximate robustness. |
| Exact finite physical result | **CLOSED IN ITS EXACT FINITE-PROJECTIVE AND EXPLICITLY CALIBRATED SCOPE** | `ExactFinite/MainResults.lean` aggregates CORE and CALIBRATED; see `docs/EXACT_FINITE_COMPLETENESS_AUDIT.md`. |
| EF0–EF9 | **AUDITED** | Codification: `docs/EXACT_FINITE_STAGES.md`; EF9 is audited. |
| EF10 | **FROZEN — RELEASE PENDING** | Public facade and v2.0.0 contract. |
| P5, P6b, P12, primitive preferences | Future milestones | The exact-richness core does not automatically settle every stronger historical formulation of P6b. |

The dated diagnostic below is **historical status** and is not the current
status of the `v1.0.0` release.

### Current status — 2026-07-28

| Milestone | Current status | Exact scope |
|---|---|---|
| P10 | **CLOSED — finite frequencies, typicality and explicit threshold** | Already calibrated quadratic weights; no `PMF`, measure, or `Tendsto`. |
| P11 | **CLOSED — finite conditional Bayesian confirmation** | P10 masses used as likelihoods, under conditional factorization and explicit nonzero assumptions. |
| P5, P6b, P7, P12, primitive-preference route | **OPEN** | None is closed by P10/P11. |
| P8 | **CLOSED in its revised scope** | Static conditioning on refinement fibers, not general temporal dynamics. |
| P9 | **PARTIAL** | `q = 4` witness only; not fully closed. |

Earlier diagnostic passages describing P10 or P11 as unstarted are historical,
predate this closure, and are not the current status.

### Historical diagnostic — 2026-07-26

The table and analysis below record the state observed on 2026-07-26, before
P10/P11 were opened and then documented as closed; they are retained for
traceability and are not the current status.

#### Milestone table

| Milestone | Subject | Status | What exists | What is missing | Dependencies |
|---|---|---|---|---|---|
| P0.1 | Not tracked separately in any document of this repository. | Undetermined status | `AGENTS.md` mentions only "P0.2–P0.4"; no document names a distinct P0.1. | A definition. | — |
| P0.2 | Same — not separately named; likely absorbed into the documented P0.3 decision. | Undetermined status | See P0.3. | A separate definition, or confirmation it is not a distinct milestone. | — |
| P0.3 | Architecture decision: the common perspective interface stays downstream, acts are total, cell subtypes are used only for enumeration. | **CLOSED** | `Core/Interface.lean` (`PerspectiveInterface`, `Projective`/`Effects` instances), documented in `CLAIM_MATRIX.md` and `ARCHITECTURE_NOTES.md`. | — | — |
| P0.4 | Non-circularity witness at `n = 2`: Grain alone does not imply Born. | **CLOSED** | `BornCalibration/NonCircularity.lean : grain_does_not_imply_born_at_two`. | — | Upstream Gleason theorem (its absence at `n = 2` is exploited, not worked around). |
| P1 | Repository infrastructure, compilable skeleton. | **CLOSED** | See `README.md`, `MILESTONES.md`. | — | — |
| P2 | Finite acts, pullback, Born nonvacuity. | **CLOSED** | `Refinement/PullbackAct.lean`, `PayoffPreserving.lean`, `Nonvacuity.lean`. | — | — |
| P3 | Canonical affine representation. | **CLOSED** | `Preference/Representation.lean : represents`, `weights_unique_on_cells`. | — | — |
| P4 | Local invariance ⇔ Grain ⇒ Born. | **CLOSED** | `BornCalibration/RefinementImpliesGrain.lean`, `BornExpectation.lean`. | — | Upstream `grainCoherenceTheorem_projector` (`3 ≤ n`). |
| P5 | **Not defined anywhere in this repository.** | **NOT STARTED** (unspecified) | Nothing. | A definition — see the dedicated subsection below. | Unknown until defined. |
| P6 | Exclusion of naive counting (scalar result). | **CLOSED** | `Rivals/NaiveBranchCounting.lean : naiveCounting_violates_grain`. | — | — |
| P6a | Physical witness of a record-neutral refinement (existence). | **CLOSED** — existence witness, not universality | `PhysicalRefinement/`. | A generalization (see P6b). | — |
| P6b | The "restricted invariance + physical realizability ⟹ full Grain" bridge, sketched in `ARCHITECTURE_NOTES.md` under "targeted improvement path, not yet achieved." Never named "P6b" anywhere in this repository — inferred from this session's prompt and the already-written target architecture. | **NOT STARTED** | The one-line target architecture (`ARCHITECTURE_NOTES.md`) and P6a's existence witness as an isolated brick. | See the dedicated subsection. | P6a; a named upstream brick (a controlled amplitude-rotation gate, `docs/SCOPE_AND_LIMITATIONS.md`). |
| P7 | Self-location. Corresponds to the `SelfLocation/` directory `README.md` announces as "not yet opened." | **NOT STARTED** | Nothing in Lean; only the target directory's name. | See the dedicated subsection. | — |
| P8 | Diachronic coherence. Corresponds to `Diachronic/`. | **NOT STARTED** | Nothing in Lean. | See the dedicated subsection. | — |
| P9 | Rival bench, beyond the already-closed naive-counting scalar result (P6). | **NOT STARTED** | `docs/RIVAL_RULES.md`: six prose watch-list entries (local counting, equi-amplitude, indexed, `‖ψ‖^q`, history-dependent weight, amplitude×count), each with its violated premise named. No Lean code. | See the dedicated subsection. | — |
| P10 | Frequencies and typicality. | **NOT STARTED** | Nothing, neither code nor a watch-list note, in this repository. | See the dedicated subsection. | — |
| P11 | Bayesian confirmation. Corresponds to `Confirmation/`. `README.md` presents it as the programme's closing milestone ("nothing is citable before P11"). | **NOT STARTED** | Nothing in Lean. | See the dedicated subsection. | — |
| P12 | Approximate stability. Corresponds to `Approximate/`. Placed after P11 in this session's prompt, which contradicts `README.md`'s framing of P11 as the closing milestone — a documentation inconsistency to flag, not to fix here. | **NOT STARTED** | Nothing. | See the dedicated subsection. | — |
| Qubit / effect route | Generalize the projective route (`n ≥ 3`) via the effect route, potentially to `n ≥ 1`. | **NOT STARTED** (zero lines of Lean), but with unusually substantial preparatory work | `docs/QUBIT_FEASIBILITY_REPORT.md` (a full analysis: a named missing brick, three structural differences, an effort estimate, four ranked risks); `Core/Interface.lean` (`Effects.interface`, `Effects.pureState_refinementInvariant`) as a partial but **weaker** scaffold (starts from a rule that already satisfies Grain by construction). | See the dedicated subsection. | An additive upstream export (`projectionEffect_weight_eq_born`/`contextual_projection_weight_eq_born`), human approval (rule 8, `AGENTS.md`). |
| Route B for primitive preferences | **No trace in this repository** — not in `AGENTS.md`, `MILESTONES.md`, `CLAIM_MATRIX.md`, nor any Lean file. | **NOT STARTED** (undefined) | Nothing. | A definition. | Unknown. |

### P5 — the three questions

- **Reusable scaffolding?** None. P5 appears in no document of this
  repository except as a label in the list "P5, P7–P11: not opened." There
  is not even a sentence describing its subject.
- **Proof or design?** Neither question can even be posed yet: the
  question that precedes both — *what does P5 refer to?* — has never been
  settled in this repository.
- **Prior non-formal decisions.** The only decision required before
  anything else is to **document what P5 refers to**. Until that decision
  is made and written down somewhere (in `MILESTONES.md` or elsewhere),
  any attempt to formalize "P5" would be invention, not the resumption of
  an existing plan.

### P6b — the three questions

- **Reusable scaffolding?** Partial. `ARCHITECTURE_NOTES.md` already fixes
  the one-line target architecture ("restricted invariance + physical
  realizability ⇒ full Grain ⇒ Born"), and P6a supplies one isolated
  brick (an existence witness). But neither notion needed to generalize —
  "Grain restricted to record-neutral refinements" as a parametrized
  `Prop`, and a characterization of the class of refinements it would
  cover — exists yet.
- **Proof or design?** Design first, and the design question is
  substantial: the P6a witness is **one** example; going from "a
  record-neutral refinement exists" to "Grain restricted to record-neutral
  refinements forces Born" requires either (a) a generalization theorem
  showing a sufficiently large class of refinements is record-neutral (a
  mathematical claim whose truth is not even established), or (b)
  explicitly accepting a theorem weaker than the current
  `born_expectation_of_invariance`, restricted from the statement onward
  to that class. This choice changes the claimed scope of the headline
  result.
- **Prior non-formal decisions.** (i) Formally define "record-neutral
  refinement" for a **general** pair `(D', D)`, not only for P6a's
  `coarsePerspective`/`finePerspective` pair. (ii) Decide whether the goal
  is full generalization (recovering unrestricted `AxGrain`) or a
  genuinely restricted theorem (a weaker conclusion, honestly presented as
  such). (iii) Settle the named upstream brick in
  `docs/SCOPE_AND_LIMITATIONS.md` — a controlled amplitude-rotation gate
  combining `ControlledBitFlip` and `AmplitudeRotation` — whose
  construction and export are undecided.

### P7 — the three questions

- **Reusable scaffolding?** None, upstream or downstream. The
  `SelfLocation/` directory does not exist. Mathlib supplies general
  probability theory, but nothing specific to self-locating uncertainty is
  wired into this repository.
- **Proof or design?** Design, almost exclusively. This is the exact
  example this session's own prompt cites: no consensus formal semantics
  of self-locating uncertainty exists for a deterministic branching
  structure. The philosophical literature (Elga, Lewis, Sebens–Carroll's
  Epistemic Separability Principle) offers competing, non-convergent
  readings.
- **Prior non-formal decisions.** Choose **one** semantics for
  self-locating uncertainty (credence in being which future successor,
  weighted how?) before writing a single Lean type. This decision is
  philosophical, not mathematical, and no upstream repository supplies it.

### P8 — the three questions

- **Reusable scaffolding?** None. The `Diachronic/` directory does not
  exist. Upstream `Refines` is a **static** relation between two
  perspectives; nothing models a temporal sequence of refinements.
- **Proof or design?** Mixed. Design first: what does "credence stays
  coherent over time" mean in a framework where time is represented by no
  existing structure — a chain of `Refines`, or a temporal index
  independent of refinement? Once that is settled, the expected proof
  volume is comparable to P3+P4 (by analogy with the effort estimate given
  for the effect route in `docs/QUBIT_FEASIBILITY_REPORT.md`).
- **Prior non-formal decisions.** Decide whether "diachronic" means
  literal Bayesian conditionalization, or a branching-specific notion
  (Wallace-style diachronic consistency, distinct from standard Bayesian
  updating). The two readings lead to disjoint formalizations.

### P9 — the three questions

- **Reusable scaffolding?** The best of any not-started milestone:
  `docs/RIVAL_RULES.md` supplies six already-identified rival rules, each
  with its violated premise named. One (`‖ψ‖^q` with `q ≠ 2`) is explicitly
  noted as "a direct consequence of a theorem already formalized upstream"
  (Gleason's theorem itself) — nearly free to formalize.
- **Proof or design?** Depends on the rule. `‖ψ‖^q`: nearly immediate
  proof. Indexed counting, history-dependent weight: design first, since
  the type `Est : Perspective n → Submodule ℂ (H n) → ℝ` does not carry
  the extra data (index, history) these rules presuppose — how to extend
  the type must be decided before anything can even be stated.
- **Prior non-formal decisions.** For rules exceeding the current `Est`
  type: decide whether to extend this shared type (risking broken direct
  comparability with `AxGrain` as currently stated) or give each rule its
  own bespoke type (risking non-uniform comparisons across rival rules).

### P10 — the three questions

- **Reusable scaffolding?** None in this repository. The broader
  literature (Vaidman's measure of existence, typicality notions) exists
  outside this repository but is neither cited nor wired in here.
- **Proof or design?** Dominantly design, and the conceptual risk is
  specific: any notion of "frequency" built from the Born weights
  themselves risks the circularity that the problem decomposition (link 1
  of `docs/ARGUMENT_MAP.md`) identifies as the "confirmation problem" —
  using Born to justify Born via a frequency operator that already
  presupposes Born.
- **Prior non-formal decisions.** Define what a "frequency" or
  "typicality" is in a purely deterministic branching structure,
  independent of any presupposition of the Born weight — otherwise the
  milestone can only presuppose what it is meant to establish.

### P11 — the three questions

- **Reusable scaffolding?** None in this repository. Mathlib supplies
  general probability and Bayesian inference theory, technically available
  upstream, but nothing connects it to `Perspective`/`Act` here.
- **Proof or design?** Design first — the classic Everettian confirmation
  problem (Greaves & Myrvold, Wallace) is precisely that Bayesian
  confirmation already presupposes a credence function to update, which P4
  supplies only under its two bridge premises. Deciding whether P11
  presupposes P4 as given, or attempts an independent justification,
  entirely changes the formalization to undertake.
- **Prior non-formal decisions.** Settle P4's logical status relative to
  P11 (an admitted premise, or itself an object to justify). Also note,
  candidly, that `README.md` presents P11 as the closing milestone of the
  entire programme ("nothing is citable before P11") — a claim that P12's
  very existence in this session's prompt renders outdated, without
  `README.md` having been updated.

### P12 — the three questions

- **Reusable scaffolding?** None.
- **Proof or design?** Design first: "approximate stability" presupposes a
  metric or norm quantifying what it means to "almost" satisfy
  `RefinementInvariantLocal`, or for a refinement to be "almost"
  record-neutral. Neither notion exists in this repository.
- **Prior non-formal decisions.** Choose the relevant perturbation space
  (perturb the premise? the state? the refinement?) and its associated
  metric, before a stability theorem can even be stated in the
  mathematical sense of the term.

### Qubit / effect route — the three questions

- **Reusable scaffolding?** Yes, substantially: see
  `docs/QUBIT_FEASIBILITY_REPORT.md`. That report precisely names the
  missing upstream brick, characterizes the three structural differences
  from the projective route, quantifies the effort (one full session,
  comparable to P3+P4), and ranks four risks in decreasing order. This is
  the inverse of the P5 case: here, the question "what would need doing"
  already has a precise written answer.
- **Proof or design?** Mostly proof/engineering — the report itself
  describes the bulk of the work as "mechanical but sizable retyping"
  (copying `Preference`/`BornCalibration` against `Fin D.outcomes` rather
  than `Submodule ℂ (H n)`). One genuine design question remains:
  characterizing the exact extension of refinements reachable by composing
  the four upstream effect-side `Refines` constructors, before claiming a
  premise as broad as the projective one.
- **Prior non-formal decisions.** Request the strictly additive upstream
  export (`projectionEffect_weight_eq_born`/
  `contextual_projection_weight_eq_born`) — a decision that, per `AGENTS.md`
  rule 8, belongs to the human maintainer, not a working session. Without
  that export, the effect route stays bounded to the qubit specializations
  already re-exported.

### Route B for primitive preferences — the three questions

None of the three questions has a defensible answer: this name appears in
no file of this repository, Lean or Markdown. Answering them would mean
speculating beyond what this repository attests. The only honest answer
is: the first non-formal decision is to document, somewhere, what this
name refers to — exactly the same defect as P5, under a different name.

## Historical status correction -- 2026-07-27 / correction de statut historique

**FR.** Cette section met à jour les lignes P8 et route qubit du relevé daté
du 2026-07-26 ci-dessus. P8 est **clos dans sa portée formelle révisée** :
conditionnement sur fibres de raffinement, loi de totalité et marginalisation
conditionnelle sous composition des raffinements. Aucune dynamique temporelle,
aucun continuateur et aucun record accessible ne sont formalisés. Les résultats
sont `conditionalWeight_sum_eq_zero_or_one` (masse `0` si le poids
conditionnant est nul, `1` sinon), `conditionalWeight_normalized` (cas non
nul), `conditionalExpectation_pullback_eq_of_weight_ne_zero` (restitution de
la conséquence conditionnante), `conditionalExpectation_total` (totalité), et
`conditionalWeight_trans_fiber` (marginalisation). Leur chaîne logique est
`RefinementInvariantLocal → canonicalWeight_grain →
conditionalWeight_trans_fiber` : ce dernier résultat n'est pas une prémisse
diachronique indépendante. L'« accord des continuateurs » est une lecture
interprétative seulement. Le témoin
`uniform_conditionalWeight_trans_fiber_fails` calcule directement
`1 ≠ 4 / 3`; il ne contredit pas le théorème car la famille uniforme ne
satisfait pas `RefinementInvariantLocal`.

La route qubit / effets est également **close** :
`effectExpectation_represents` vaut pour tout `n`, et
`effectWeight_eq_born_of_invariance` donne, pour tout `n ≥ 1`, une conclusion
par sortie lorsque son effet est une projection. Elle ne couvre pas les POVM
non projectifs.

**EN.** This section updates the P8 and qubit-route rows of the dated
2026-07-26 audit above. P8 is **closed in its revised formal scope**:
conditioning on refinement fibers, totality, and conditional marginalization
under composition of refinements. No temporal dynamics, continuator, or
accessible record is formalized. Its results are
`conditionalWeight_sum_eq_zero_or_one` (mass `0` at zero conditioning weight,
`1` otherwise), `conditionalWeight_normalized` (the nonzero case),
`conditionalExpectation_pullback_eq_of_weight_ne_zero` (conditioning
consequence recovery), `conditionalExpectation_total` (totality), and
`conditionalWeight_trans_fiber` (marginalization). Their logical chain is
`RefinementInvariantLocal → canonicalWeight_grain →
conditionalWeight_trans_fiber`: the last result is not an independent
diachronic premise. “Continuator agreement” is an interpretive reading only.
The witness `uniform_conditionalWeight_trans_fiber_fails` directly computes
`1 ≠ 4 / 3`; it does not contradict the theorem because the uniform family does
not satisfy `RefinementInvariantLocal`.

The qubit / effect route is also **closed**: `effectExpectation_represents`
holds for every `n`, and `effectWeight_eq_born_of_invariance` gives, for every
`n ≥ 1`, a per-outcome conclusion when its effect is a projection. It does not
cover non-projective POVMs.

## 2026-07-28 current-status correction / correction d'état courant

**FR.** P9 est désormais partiellement ouvert pour le seul témoin `q = 4` :
`Rivals/FourthPowerWeight.lean` prouve `AxPos` et l'échec de `AxNorm` par
`337/625 ≠ 1` sur `psiBefore` et `coarsePerspective`. Les cinq autres règles
de veille restent non formalisées.

**EN.** P9 is now partially open for the sole `q = 4` witness:
`Rivals/FourthPowerWeight.lean` proves `AxPos` and failure of `AxNorm` through
`337/625 ≠ 1` on `psiBefore` and `coarsePerspective`. The other five
watch-list rules remain unformalized.
