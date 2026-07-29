# Feuille de route vers un théorème intégré de probabilité everettienne

## Français

> **Statut historique -- 2026-07-26.** Cette feuille de route precede la
> formalisation de SelfLocation, de la diachronie et du noyau physique exact
> fini. Elle est conservee pour la tracabilite et ne decrit pas le statut
> courant; voir `CONDITIONAL_BORN_SCOPE.md` et `PROGRAM_STATUS.md`.

### But prudent

Le but final est de construire un théorème intégrateur montrant que, sous des
prémisses normatives, physiques, sémantiques et statistiques explicitement
séparées, la pondération bornienne fournit simultanément l'espérance rationnelle,
la crédence auto-localisante, la cohérence diachronique, la typicalité
fréquentielle et la mise à jour confirmatoire.

Ce but n'est pas « Born ou la probabilité à partir de la seule dynamique
unitaire ». Les prémisses restent identifiées et ne sont pas rétrojustifiées.

### État déjà acquis

- P0–P4 et la route effets/qubit dans sa portée projective.
- P6 et P6a; P8 dans sa portée statique révisée; P9 partiel, `q = 4`.
- P10 fermé; P11 fermé conditionnellement dans sa portée bayésienne finie.

### Étape SG-1 — P7, auto-localisation

Décisions : définition d'une alternative centrée, rôle du record accessible,
relation entre poids canonique et crédence, cellules de poids nul, invariance
sous raffinement. Critère : définition non circulaire ou explicitement
conditionnelle, normalisation, cohérence sous raffinement, témoin de
non-trivialité.

### Étape SG-2 — P8b, diachronie véritable

Décisions : continuateurs, succession temporelle de records, conditionnement
sur l'information accessible, loi de totalité ou tour de l'espérance. Critère :
cohérence entre crédence présente et crédences des continuateurs, au-delà du
conditionnement statique entre deux perspectives.

### Étape SG-3 — P6b, réalisabilité physique générale

Décisions : prédicat général de raffinement record-neutre, classe de
raffinements physiquement réalisables, portes contrôlées de rotation
d'amplitude, objectif complet ou théorème honnêtement restreint.

Critère fort souhaité :

```text
restricted invariance on physically realizable refinements
    ⇒ full Grain
    ⇒ Born.
```

La vérité de cette généralisation n'est pas encore acquise.

### Étape SG-4 — P12, robustesse approximative

Décisions : objet perturbé, métrique, invariance approximative, norme de
proximité à Born. Critère : une borne quantitative,
`approximate premise ⇒ quantitatively near-Born conclusion`.

### Étape SG-5 — Banc des rivales

Cette étape renforce la portée explicative, mais n'est pas le pont logique
principal vers le théorème intégré.

### Étape SG-6 — Théorème intégrateur

Schéma visé, non encore démontré :

```text
Sous :
- [NORM] rationalité affine ;
- [NORM] invariance locale sous raffinement ;
- [NORM/PHYS] support nul ;
- [PHYS] réalisabilité physique pertinente ;
- [SEM] sémantique choisie de l'auto-localisation ;
- [SEM/NORM] cohérence des continuateurs ;
- [STAT] factorisation conditionnelle des expériences répétées ;

alors :
- les poids sont borniens ;
- les espérances sont borniennes ;
- les crédences auto-localisantes sont calibrées par ces poids ;
- les mises à jour diachroniques sont cohérentes ;
- les fréquences sont typiques au sens quantifié de P10 ;
- la confirmation finie suit les règles de P11.
```

### Risques bloquants

1. P6b : vérité mathématique non établie.
2. P7 : absence de sémantique consensuelle.
3. P12 : choix de métrique potentiellement non canonique.
4. Risque de surinterprétation de P10/P11 comme dérivations indépendantes.

### Ordre recommandé

```text
P11 documentation closure
→ P7 architecture decision
→ P7 formalization
→ P8b
→ P6b
→ P12
→ integrated theorem
→ adversarial audit and manuscript alignment
```

P6b peut être exploré en parallèle, mais ne doit pas être déclaré acquis avant
preuve.

# Roadmap to an Integrated Everettian Probability Theorem

## English

> **Historical status -- 2026-07-26.** This roadmap predates the
> formalization of SelfLocation, diachrony, and the exact finite physical
> core. It is retained for traceability and does not describe current status;
> see `CONDITIONAL_BORN_SCOPE.md` and `PROGRAM_STATUS.md`.

### Cautious goal

The final goal is to construct an integrating theorem showing that, under
explicitly separated normative, physical, semantic, and statistical premises,
Born weighting simultaneously supplies rational expectation, self-locating
credence, diachronic coherence, frequency typicality, and confirmatory updating.

This goal is not “Born or probability from unitary dynamics alone.” Premises
remain identified and are not retroactively justified.

### Already acquired

- P0–P4 and the effects/qubit route in its projective scope.
- P6 and P6a; P8 in its revised static scope; P9 partial, `q = 4`.
- P10 closed; P11 conditionally closed in its finite Bayesian scope.

### SG-1 — P7, self-location

Decisions: a centred-alternative definition, the role of accessible records,
canonical weight and credence, zero-weight cells, and refinement invariance.
Criterion: a non-circular or explicitly conditional definition, normalization,
refinement coherence, and a nontriviality witness.

### SG-2 — P8b, genuine diachrony

Decisions: continuators, temporal record succession, conditioning on accessible
information, and a totality law or tower of expectation. Criterion: coherence
between present credence and continuator credences, beyond static conditioning.

### SG-3 — P6b, general physical realizability

Decisions: a general record-neutral refinement predicate, physically realizable
refinements, controlled amplitude-rotation gates, and a complete or honestly
restricted target theorem.

Desired strong criterion:

```text
restricted invariance on physically realizable refinements
    ⇒ full Grain
    ⇒ Born.
```

The truth of this generalization is not yet established.

### SG-4 — P12, approximate robustness

Decisions: perturbed object, metric, approximate invariance, and nearness norm.
Criterion: `approximate premise ⇒ quantitatively near-Born conclusion`.

### SG-5 — Rival-rule bench

This strengthens explanatory scope but is not the main logical bridge.

### SG-6 — Integrating theorem

Target schema, not yet proved:

```text
Under:
- [NORM] affine rationality;
- [NORM] local refinement invariance;
- [NORM/PHYS] null support;
- [PHYS] relevant physical realizability;
- [SEM] chosen self-location semantics;
- [SEM/NORM] continuator coherence;
- [STAT] conditional factorization of repeated experiments;

then:
- weights are Born weights;
- expectations are Born expectations;
- self-locating credences are calibrated by those weights;
- diachronic updates are coherent;
- frequencies are typical in P10's quantified sense;
- finite confirmation follows P11's rules.
```

### Blocking risks

1. P6b: mathematical truth not established.
2. P7: no consensual semantics.
3. P12: potentially non-canonical metric choice.
4. Risk of misreading P10/P11 as independent derivations.

### Recommended order

```text
P11 documentation closure
→ P7 architecture decision
→ P7 formalization
→ P8b
→ P6b
→ P12
→ integrated theorem
→ adversarial audit and manuscript alignment
```

P6b may be explored in parallel, but must not be declared established before
proof.
