# ARGUMENT_MAP.md

> Livrable central de la session de documentation du 2026-07-26. Reconstruit
> la chaîne d'argument que l'article II devra porter, maillon par maillon,
> et audite huit formulations que le manuscrit pourrait être tenté
> d'employer. Aucun théorème nouveau, aucune preuve : ce document ne fait
> que faire correspondre des affirmations en prose à des déclarations Lean
> déjà existantes, ou constater leur absence.
>
> Central deliverable of the 2026-07-26 documentation session. Reconstructs
> the claim chain the manuscript will have to carry, link by link, and
> audits eight formulations the manuscript might be tempted to use. No new
> theorem, no proof: this document only matches prose claims to existing
> Lean declarations, or records their absence.

## Français

### Mise a jour de release -- resultat conditionnel

La chaine stable ajoute explicitement : P4 calibre les poids de Born sous
premisses NORM et PHYS--NORM; P7 choisit conditionnellement une credence de
record sous SEM; P8b applique cette credence aux continuateurs et obtient
normalisation, esperance totale, chaine et tour. La proportionnalite et
l'interpretation des cellules comme continuateurs ne sont pas imposees par la
dynamique unitaire. Le noyau physique exact fini soutient des constructions
additionnelles, mais ne fait pas partie de la garantie d'API `v1.x`.

### P4, P10 et P11 : sens de la chaîne

```text
dérivation/calibration des poids : P4
    ↓
conséquences fréquentielles : P10
    ↓
utilisation confirmatoire conditionnelle : P11
```

P4 calibre les poids dans les prémisses normatives et physiques déjà isolées.
P10 en tire des conséquences fréquentielles : masses binomiales, moments,
concentration et typicalité quantifiée. P11 emploie alors ces masses comme
vraisemblances dans un modèle bayésien fini conditionnel.

| Élément P11 | Classification |
|---|---|
| prior | épistémique |
| likelihoods | héritées de la calibration bornienne P4/P10 |
| factorisation | statistique/modélisatrice |
| non-nullité | technique et substantielle selon le cas |

**Ce qui n'est pas démontré :** P11 n'est pas une dérivation de P4 et ne peut
pas être utilisé comme justification rétroactive de P4. Il ne sélectionne pas
une hypothèse vraie et ne prouve ni convergence ni consistance.

### Méthode

Chaque maillon reçoit un statut unique :

- **FORMALISÉ** — une déclaration nommée l'établit exactement.
- **FORMALISÉ PLUS FAIBLE** — une déclaration approche, mais l'affirmation
  en prose dit strictement plus ; l'écart est précisé.
- **PROSE LÉGITIME** — l'affirmation est philosophique ou interprétative et
  n'a pas vocation à être formalisée.
- **NON ÉTAYÉ** — l'affirmation serait faite sans support, formel ou
  argumenté.

En cas d'hésitation entre FORMALISÉ et FORMALISÉ PLUS FAIBLE, le second a
été choisi systématiquement.

### La chaîne d'argument

| # | Affirmation, telle qu'elle apparaîtra en prose | Déclaration Lean qui la porte | Statut |
|---|---|---|---|
| 1 | Le problème des probabilités everettiennes se scinde en problème numérique, sémantique, normatif, diachronique et de confirmation. | — | PROSE LÉGITIME |
| 2 | Les actes se modélisent par des fonctions totales sur les sous-espaces. | `Core/Act.lean : Act n := Submodule ℂ (H n) → ℝ` | FORMALISÉ |
| 3 | Une famille d'espérance rationnelle admet des poids canoniques. | `Preference/Representation.lean : represents`, `weights_unique_on_cells` | FORMALISÉ |
| 4 | L'invariance locale sous raffinement est exactement Grain. | `BornCalibration/RefinementImpliesGrain.lean : refinementInvariantLocal_iff_axGrain` | FORMALISÉ |
| 5 | L'invariance plus le support nul force les poids de Born. | `BornCalibration/BornExpectation.lean : born_expectation_of_invariance` | FORMALISÉ PLUS FAIBLE |
| 6 | La lecture globale de la préservation des conséquences est vacueuse. | `Refinement/GlobalPayoffVacuity.lean : globalPremise_vacuous`, `uniformExpectationFamily_globalPremise_vacuous` | FORMALISÉ |
| 7 | Grain seul, en `n = 2`, n'implique pas Born — donc la prémisse n'est pas la règle de Born déguisée. | `BornCalibration/NonCircularity.lean : grain_does_not_imply_born_at_two` | FORMALISÉ PLUS FAIBLE |
| 8 | Le comptage naïf viole Grain. | `Rivals/NaiveBranchCounting.lean : naiveCounting_violates_grain` | FORMALISÉ |
| 9 | Le comptage uniforme viole l'invariance (locale). | `Refinement/NonTriviality.lean : uniform_not_refinementInvariantLocal` | FORMALISÉ |
| 10 | L'*indexed branch-counting* (Khawaja) viole l'invariance. | — (`docs/RIVAL_RULES.md` : « Non formalisé. Fiche de veille. ») | NON ÉTAYÉ |
| 11 | Il existe des raffinements record-neutres physiquement réalisables. | `PhysicalRefinement/RecordNeutralWitness.lean : recordNeutral_refines`, `_record_eq`, `_payoff_eq`, `_bornWeight_eq`, `refinementNotInRecordAlgebra_holds` | FORMALISÉ PLUS FAIBLE |
| 12 | Le verdict du comptage n'est pas déterminé par le record accessible ; celui de Born l'est. | `PhysicalRefinement/NonTriviality.lean : counting_underdetermined_by_accessible_record` ; `PhysicalRefinement/Nonvacuity.lean : born_determined_by_accessible_record` | FORMALISÉ PLUS FAIBLE |
| 13 | Un raffinement record-neutre redécrit les successeurs plutôt qu'il n'en crée. | — (lecture interprétative des théorèmes du maillon 11) | PROSE LÉGITIME |
| 14 | L'agrégation inter-branches de Khawaja échoue à la normalisation, et cet échec **est** sa sensibilité au raffinement. | — | NON ÉTAYÉ |
| 15 | Le théorème principal repose sur deux prémisses-ponts distinctes, pas sur une seule prémisse normative. | Signature de `born_expectation_of_invariance` (`hinv` et `hNul` séparés) ; `CLAIM_MATRIX.md`, `docs/THEOREM_MAP.md` | FORMALISÉ |
| 16 | L'affinité de la famille d'espérance rationnelle n'est pas une hypothèse neutre. | `Preference/NonTriviality.lean : maxExpectation_not_affine` | FORMALISÉ |

### Commentaire, maillon par maillon

**1.** Décomposition taxonomique du problème, empruntée à la littérature
(Wallace, Saunders, Sebens–Carroll). Aucun type Lean ne pourrait porter
« problème sémantique » ou « problème de confirmation » comme prédicats
vérifiables ; c'est un découpage de plan de rédaction, pas un énoncé
mathématique. Légitime tant qu'il reste présenté comme tel.

**2.** Correspondance directe et complète. `Act n` est littéralement défini
comme la fonction totale annoncée.

**3.** Complet, avec une précision qui doit être préservée dans le
manuscrit : l'unicité n'est établie **que sur `D.cells`**, pas sur
l'ensemble des sous-espaces (`weights_unique_on_cells` le dit explicitement,
et `ARCHITECTURE_NOTES.md` documente que l'énoncé antérieur, sans cette
restriction, était **faux**). Si le manuscrit énonce l'unicité sans cette
qualification, il régresse vers le défaut P3 déjà corrigé.

**4.** Complet et fort : c'est une **équivalence**, pas seulement un sens.
Le manuscrit peut légitimement écrire « si et seulement si ».

**5.** Écart : le maillon prose, tel que formulé, omet deux restrictions que
le théorème porte explicitement. D'abord, `3 ≤ n` — le résultat ne vaut que
pour les espaces de dimension au moins 3 (domaine du théorème de Gleason
amont) ; ce n'est **pas** une clause secondaire, c'est exactement la
frontière que le maillon 7 exploite pour construire son contre-exemple.
Ensuite, « le support nul » n'est pas une hypothèse physique brute sur
`v` : c'est `AxNul (canonicalWeight F) v`, une contrainte sur les poids de
l'agent **induits par la famille rationnelle**, qui référence `v` sans être
elle-même une loi physique. Le manuscrit doit porter les deux qualifications
à cet endroit précis, faute de quoi il énoncerait un résultat pour tout `n`
sous une prémisse présentée comme purement physique — voir aussi le point 2
de la chasse à la surinterprétation.

**7.** Le fait mathématique (`grain_does_not_imply_born_at_two`) est
complet et net : à `n = 2`, un contre-exemple explicite existe. Mais la
clause « donc la prémisse n'est pas la règle de Born déguisée » est une
inférence argumentative, pas un fait Lean — aucun type ne représente « être
la règle de Born déguisée ». C'est un raisonnement légitime **appuyé sur**
le fait formel, mais qui n'est pas lui-même formalisé ni formalisable tel
quel. Le manuscrit doit distinguer explicitement les deux : le fait
(formalisé) et l'inférence qu'il autorise (argumentée, non formalisée).

**9.** Attention à ne pas confondre avec le maillon 8 : ce sont deux règles
rivales distinctes (`naiveCounting`, qui viole Grain ; `uniformExpectation`/
`uniformExpectationFamily`, qui viole `RefinementInvariantLocal` directement
et sert par ailleurs de témoin de non-vacuité pour `RationalExpectationFamily`
elle-même). Le fait que le même objet serve de témoin positif pour une
structure et de témoin négatif pour une prémisse plus forte n'est pas une
contradiction — c'est exactement le rôle voulu.

**10.** Comme anticipé par le prompt de cette session : aucune formalisation.
`docs/RIVAL_RULES.md` documente une observation plus faible et différente
(voir chasse à la surinterprétation, point 5) — un décalage de type, pas une
violation d'invariance démontrée.

**11.** Écart précis : « physiquement réalisable » suggère une
implémentation physique réelle (couplage effectif, dynamique
hamiltonienne, décohérence qui désigne l'algèbre de records). Ce que le
témoin établit est l'existence d'**une** construction hilbertienne
cohérente — une rotation unitaire interne à `H 3` — satisfaisant les quatre
propriétés requises, sous une désignation de l'algèbre de records
**stipulée** (`RefinementNotInRecordAlgebra`), pas dérivée d'une
factorisation tensorielle ou d'une dynamique de décohérence indépendantes.
Voir aussi la chasse à la surinterprétation, point 4, et
`docs/SCOPE_AND_LIMITATIONS.md`.

**12.** Écart précis : les deux théorèmes sont prouvés pour **un** paiement
fixé (`payoff`, l'indicatrice de `label1Space`) et **une** paire de
perspectives fixée (`coarsePerspective`/`finePerspective` via
`recordNeutral_refines`). La forme universelle de `born_determined_by_
accessible_record` (`∀ u w`) est réelle et notable, mais elle porte sur ce
paiement précis, pas sur « tout paiement ». Si le manuscrit présente ce
maillon comme un fait général sur « le comptage » et « Born » en général,
il dépasse ce qui est prouvé.

**13.** Lecture ontologique du maillon 11 : « redécrire plutôt que créer »
n'est pas un prédicat que `Perspective`, `Refines` ou `Submodule ℂ (H n)`
peuvent porter. C'est une manière d'interpréter philosophiquement le fait
que le record, le paiement et les poids borniens soient inchangés alors que
le nombre de cellules distinguées augmente. Légitime comme gloss
interprétatif, à condition d'être présenté comme tel et non comme une
conséquence supplémentaire prouvée.

**14.** Rien dans ce dépôt ne mentionne, même en prose de veille, un échec
de normalisation pour le comptage indexé, et rien ne relie un tel échec à
la sensibilité au raffinement — ce sont deux violations d'axiomes distinctes
(`AxNorm` contre `AxGrain`/`RefinementInvariantLocal`) que rien ici
n'identifie l'une à l'autre. C'est la formulation la plus spécifique et la
moins étayée des trois maillons signalés par le prompt de cette session.

**15.** Directement porté par la signature de `born_expectation_of_
invariance`, qui prend `hinv : RefinementInvariantLocal F.V` et
`hNul : AxNul (canonicalWeight F) v` comme deux hypothèses **séparées**, et
par la reclassification déjà actée dans `CLAIM_MATRIX.md`/`docs/
THEOREM_MAP.md`/`docs/SCOPE_AND_LIMITATIONS.md` (reprise du 2026-07-26).
Détail complet au point 2 de la chasse à la surinterprétation.

**16.** `maxExpectation_not_affine` isole exactement ce que l'affinité
exclut : un fonctionnel monotone, normalisé, mais non affine. Complet.

### Chasse à la surinterprétation

1. **« Nous dérivons la règle de Born. »**
   Non licite telle quelle. Phrase autorisée : *« Nous montrons que, pour
   toute famille d'espérance rationnelle sur un espace de dimension
   `n ≥ 3`, l'invariance locale sous raffinement combinée à la nullité du
   poids canonique sur le support de l'état force l'espérance à coïncider
   avec l'espérance de Born. »* La règle de Born n'est jamais dérivée
   inconditionnellement ; elle est dérivée **sous** ces prémisses précises,
   dont deux sont des prémisses-ponts (point 2 ci-dessous) et une est une
   restriction de dimension.

2. **« Une unique prémisse normative. »**
   Faux. Phrase autorisée : *« Le théorème repose sur deux prémisses-ponts
   distinctes : l'invariance locale sous raffinement (`RefinementInvariant
   Local`, purement normative) et la nullité canonique sur le support de
   l'état (`AxNul (canonicalWeight F) v`, un pont normatif-physique, car
   elle référence l'état physique `v` — le seul point d'entrée de `v` dans
   les hypothèses du théorème). `hNul` **fait partie** des prémisses-ponts ;
   elle n'est ni superflue ni purement normative. »* `AxNorm` et `AxPos`,
   en revanche, sont dérivées et ne comptent pas comme prémisses
   supplémentaires.

3. **« Notre prémisse est plus faible que celle de Wallace. »**
   Non. Phrase autorisée : *« Notre prémisse d'invariance locale n'est pas
   plus faible que la* branching indifference *de Wallace : c'est sa
   transposition au cadre projectif, quantifiée sur tous les raffinements
   projectifs, ni plus faible ni plus neutre que l'original. Le dépôt ne
   revendique pas un affaiblissement, mais l'isolement formel de cette
   prémisse et la démonstration qu'elle suffit. »* (`docs/
   SCOPE_AND_LIMITATIONS.md`, verbatim sur ce point.)

4. **« Les raffinements record-neutres sont physiquement réalisables. »**
   Vrai seulement au sens existentiel. Phrase autorisée : *« Il existe au
   moins un raffinement record-neutre physiquement motivé — le témoin de
   `PhysicalRefinement/`, un couplage unitaire interne à `H 3`. Nous ne
   montrons pas que tout raffinement projectif est record-neutre, et la
   prémisse du théorème principal (`RefinementInvariantLocal`, donc
   `AxGrain`) continue de quantifier sur tous les raffinements sans que ce
   fait existentiel ne la justifie physiquement dans le cas général. »*

5. **« Nous réfutons le comptage indexé. »**
   Non licite. Phrase autorisée : *« Nous n'avons ni réfuté ni formalisé le
   comptage indexé de Khawaja. `docs/RIVAL_RULES.md` observe seulement
   qu'il ajoute une donnée (l'indice de redondance) que le type
   `Est : Perspective n → Submodule ℂ (H n) → ℝ` ne porte pas — la règle
   n'est donc pas de la forme que présuppose `AxGrain`, ce qui est un
   décalage de type, pas une preuve qu'elle violerait l'invariance une fois
   convenablement typée. »*

6. **« Le résultat vaut pour les systèmes quantiques. »**
   Trop large. Phrase autorisée : *« Le résultat projectif vaut pour les
   espaces de dimension `n ≥ 3` (le domaine du théorème de Gleason amont).
   Il ne couvre pas le qubit (`n = 2`) : au contraire, nous y exhibons une
   règle non-bornienne cohérente sous les mêmes axiomes de rationalité
   (`grain_does_not_imply_born_at_two`). La route effets, seule capable de
   couvrir potentiellement `n ≥ 1` y compris le qubit, n'est pas construite
   dans ce dépôt (`docs/QUBIT_FEASIBILITY_REPORT.md`). »*

7. **« Le témoin exhibe un couplage d'ancilla. »**
   Interprétation, pas un fait du type. Phrase autorisée : *« Le témoin
   exhibe une rotation unitaire interne sur un bloc de deux vecteurs de
   base de `H 3`. L'appeler un couplage d'ancilla est une interprétation
   physique de cette rotation, développée en prose ; `H 3` ne porte aucune
   factorisation tensorielle système/ancilla, et rien dans le type
   `Submodule ℂ (H 3)` ne distingue une ancilla d'un sous-espace
   quelconque. »* (Voir la section 1 et `AGENTS.md`, règle 13, sur le
   renommage `AncillaNotInRecordAlgebra` → `RefinementNotInRecordAlgebra`
   motivé par cette même distinction.)

8. **« L'espérance rationnelle est une hypothèse neutre. »**
   Faux pour l'affinité. Phrase autorisée : *« L'affinité de
   `RationalExpectationFamily` est une hypothèse substantielle, rejetée par
   les théories de la décision non-espérance (utilité dépendante du rang :
   Quiggin 1982, Yaari 1987). `maxExpectation`, le maximum sur les
   cellules, en est le témoin négatif explicite : monotone et normalisé,
   mais provablement non affine (`maxExpectation_not_affine`). »*

## English

### Release update -- conditional result

The stable chain explicitly adds: P4 calibrates Born weights under NORM and
PHYS--NORM premises; P7 conditionally chooses record credence under SEM; P8b
applies that credence to continuators and obtains normalization, total
expectation, chain, and tower. Proportionality and the interpretation of cells
as continuators are not imposed by unitary dynamics. The exact finite physical
core supports additional constructions but is outside the `v1.x` API guarantee.

### P4, P10, and P11: direction of the chain

```text
derivation/calibration of weights: P4
    ↓
frequency consequences: P10
    ↓
conditional confirmatory use: P11
```

P4 calibrates weights under the already isolated normative and physical
premises. P10 draws frequency consequences: binomial masses, moments,
concentration, and quantified typicality. P11 then uses those masses as
likelihoods in a finite conditional Bayesian model.

| P11 element | Classification |
|---|---|
| prior | epistemic |
| likelihoods | inherited from P4/P10 Born calibration |
| factorization | statistical/modeling |
| nonzero conditions | technical and substantive as applicable |

**What is not proved:** P11 is not a derivation of P4 and cannot be used as a
retroactive justification of P4. It selects no true hypothesis and proves
neither convergence nor consistency.

### Method

Every link receives exactly one status:

- **FORMALISED** — a named declaration establishes it exactly.
- **FORMALISED-WEAKER** — a declaration comes close, but the prose claim
  says strictly more; the gap is stated.
- **LEGITIMATE-PROSE** — the claim is philosophical or interpretive and is
  not meant to be formalized.
- **UNSUPPORTED** — the claim would be made with no support, formal or
  argued.

Whenever there was hesitation between FORMALISED and FORMALISED-WEAKER, the
latter was chosen systematically.

### The claim chain

| # | Claim, as it will appear in prose | Lean declaration carrying it | Status |
|---|---|---|---|
| 1 | The Everettian probability problem splits into a quantitative, a semantic, a normative, a diachronic, and a confirmation problem. | — | LEGITIMATE-PROSE |
| 2 | Acts are modeled as total functions on subspaces. | `Core/Act.lean : Act n := Submodule ℂ (H n) → ℝ` | FORMALISED |
| 3 | A rational expectation family admits canonical weights. | `Preference/Representation.lean : represents`, `weights_unique_on_cells` | FORMALISED |
| 4 | Local invariance under refinement is exactly Grain. | `BornCalibration/RefinementImpliesGrain.lean : refinementInvariantLocal_iff_axGrain` | FORMALISED |
| 5 | Invariance plus null support forces Born weights. | `BornCalibration/BornExpectation.lean : born_expectation_of_invariance` | FORMALISED-WEAKER |
| 6 | The global reading of consequence preservation is vacuous. | `Refinement/GlobalPayoffVacuity.lean : globalPremise_vacuous`, `uniformExpectationFamily_globalPremise_vacuous` | FORMALISED |
| 7 | Grain alone, at `n = 2`, does not imply Born — hence the premise is not the Born rule in disguise. | `BornCalibration/NonCircularity.lean : grain_does_not_imply_born_at_two` | FORMALISED-WEAKER |
| 8 | Naive counting violates Grain. | `Rivals/NaiveBranchCounting.lean : naiveCounting_violates_grain` | FORMALISED |
| 9 | Uniform counting violates (local) invariance. | `Refinement/NonTriviality.lean : uniform_not_refinementInvariantLocal` | FORMALISED |
| 10 | Indexed branch-counting (Khawaja) violates invariance. | — (`docs/RIVAL_RULES.md`: "Not formalized. Watch-list entry.") | UNSUPPORTED |
| 11 | Physically realizable record-neutral refinements exist. | `PhysicalRefinement/RecordNeutralWitness.lean : recordNeutral_refines`, `_record_eq`, `_payoff_eq`, `_bornWeight_eq`, `refinementNotInRecordAlgebra_holds` | FORMALISED-WEAKER |
| 12 | Counting's verdict is not determined by the accessible record; Born's is. | `PhysicalRefinement/NonTriviality.lean : counting_underdetermined_by_accessible_record`; `PhysicalRefinement/Nonvacuity.lean : born_determined_by_accessible_record` | FORMALISED-WEAKER |
| 13 | A record-neutral refinement redescribes successors rather than creating them. | — (interpretive reading of link 11's theorems) | LEGITIMATE-PROSE |
| 14 | Khawaja's cross-branch aggregation fails normalization, and that failure **is** its refinement-sensitivity. | — | UNSUPPORTED |
| 15 | The headline theorem rests on two distinct bridge premises, not a single normative premise. | Signature of `born_expectation_of_invariance` (`hinv` and `hNul` kept separate); `CLAIM_MATRIX.md`, `docs/THEOREM_MAP.md` | FORMALISED |
| 16 | Affinity of the rational expectation family is not a neutral hypothesis. | `Preference/NonTriviality.lean : maxExpectation_not_affine` | FORMALISED |

### Link-by-link commentary

**1.** A taxonomic decomposition of the problem, borrowed from the
literature (Wallace, Saunders, Sebens–Carroll). No Lean type could carry
"semantic problem" or "confirmation problem" as checkable predicates; this
is an outline decision, not a mathematical statement. Legitimate as long as
it stays presented as such.

**2.** Direct, complete match. `Act n` is literally defined as the total
function announced.

**3.** Complete, with a nuance that must survive into the manuscript:
uniqueness is established **only on `D.cells`**, not over every subspace
(`weights_unique_on_cells` says so explicitly, and `ARCHITECTURE_NOTES.md`
documents that the prior, unqualified statement was **false**). If the
manuscript states uniqueness without this qualification, it regresses to
the already-fixed P3 defect.

**4.** Complete and strong: it is an **equivalence**, not just one
direction. The manuscript may legitimately write "if and only if."

**5.** Gap: the prose link, as phrased, omits two restrictions the theorem
explicitly carries. First, `3 ≤ n` — the result holds only for spaces of
dimension at least 3 (the domain of the upstream Gleason theorem); this is
**not** a side clause, it is exactly the boundary that link 7's
counterexample exploits. Second, "null support" is not a raw physical
hypothesis on `v`: it is `AxNul (canonicalWeight F) v`, a constraint on the
*agent's weights as induced by the rational family*, which references `v`
without itself being a physical law. The manuscript must carry both
qualifications at this exact link, or it would state a result for every
`n` under a premise presented as purely physical — see also point 2 of the
overreach hunt.

**7.** The mathematical fact (`grain_does_not_imply_born_at_two`) is
complete and sharp: at `n = 2`, an explicit counterexample exists. But the
clause "hence the premise is not the Born rule in disguise" is an
argumentative inference, not a Lean fact — no type represents "being the
Born rule in disguise." This is legitimate reasoning **resting on** the
formal fact, but it is not itself formalized or formalizable as such. The
manuscript must keep the two apart: the fact (formalized) and the
inference it licenses (argued, not formalized).

**9.** Do not conflate with link 8: these are two distinct rival rules
(`naiveCounting`, which violates Grain; `uniformExpectation`/
`uniformExpectationFamily`, which violates `RefinementInvariantLocal`
directly and separately serves as the nonvacuity witness for
`RationalExpectationFamily` itself). The same object serving as a positive
witness for one structure and a negative witness for a stronger premise is
not a contradiction — it is exactly the intended role.

**10.** As this session's prompt anticipated: no formalization exists.
`docs/RIVAL_RULES.md` documents a weaker, different observation (see
overreach hunt, point 5) — a type mismatch, not a proved invariance
violation.

**11.** Precise gap: "physically realizable" suggests an actual physical
implementation (an effective coupling, Hamiltonian dynamics, decoherence
that designates the record algebra). What the witness establishes is the
existence of **one** consistent Hilbert-space construction — an internal
unitary rotation in `H 3` — satisfying the four required properties, under
a **stipulated** record-algebra designation (`RefinementNotInRecordAlgebra`),
not one derived from an independent tensor factorization or decoherence
dynamics. See also overreach hunt point 4 and
`docs/SCOPE_AND_LIMITATIONS.md`.

**12.** Precise gap: both theorems are proved for **one** fixed payoff
(`payoff`, the indicator of `label1Space`) and **one** fixed pair of
perspectives (`coarsePerspective`/`finePerspective` via
`recordNeutral_refines`). The universal form of `born_determined_by_
accessible_record` (`∀ u w`) is real and notable, but it concerns this
specific payoff, not "every payoff." If the manuscript presents this link
as a general fact about "counting" and "Born" as such, it overreaches what
is proved.

**13.** An ontological reading of link 11: "redescribing rather than
creating" is not a predicate that `Perspective`, `Refines`, or
`Submodule ℂ (H n)` can carry. It is a way of philosophically interpreting
the fact that the record, the payoff, and the Born weights are unchanged
while the number of distinguished cells grows. Legitimate as an
interpretive gloss, provided it is presented as such and not as an
additional proved consequence.

**14.** Nothing in this repository mentions, even as a watch-list note, a
normalization failure for indexed counting, and nothing links such a
failure to refinement-sensitivity — these are two distinct axiom
violations (`AxNorm` versus `AxGrain`/`RefinementInvariantLocal`) that
nothing here identifies with one another. This is the most specific and
least supported of the three links flagged by this session's prompt.

**15.** Directly carried by the signature of `born_expectation_of_
invariance`, which takes `hinv : RefinementInvariantLocal F.V` and
`hNul : AxNul (canonicalWeight F) v` as two **separate** hypotheses, and by
the reclassification already recorded in `CLAIM_MATRIX.md`/`docs/
THEOREM_MAP.md`/`docs/SCOPE_AND_LIMITATIONS.md` (2026-07-26 resumption).
Full detail at overreach hunt point 2.

**16.** `maxExpectation_not_affine` isolates exactly what affinity
excludes: a monotone, normalized, but non-affine functional. Complete.

### Overreach hunt

1. **"We derive the Born rule."**
   Not licensed as stated. Licensed sentence: *"We show that, for every
   rational expectation family on a space of dimension `n ≥ 3`, local
   invariance under refinement combined with null canonical weight on the
   state's support forces the expectation to coincide with Born
   expectation."* The Born rule is never derived unconditionally; it is
   derived **under** these precise premises, two of which are bridge
   premises (point 2 below) and one of which is a dimension restriction.

2. **"A single normative premise."**
   False. Licensed sentence: *"The theorem rests on two distinct bridge
   premises: local invariance under refinement (`RefinementInvariant
   Local`, purely normative) and null canonical weight on the state's
   support (`AxNul (canonicalWeight F) v`, a normative-physical bridge,
   since it references the physical state `v` — the only place `v` enters
   the theorem's hypotheses). `hNul` **is** one of the bridge premises; it
   is neither superfluous nor purely normative."* `AxNorm` and `AxPos`, by
   contrast, are derived and do not count as extra premises.

3. **"Our premise is weaker than Wallace's."**
   No. Licensed sentence: *"Our local-invariance premise is not weaker
   than Wallace's* branching indifference*: it is its transposition to the
   projective setting, quantified over every projective refinement,
   neither weaker nor more neutral than the original. The repository
   claims not a weakening, but the formal isolation of this premise and a
   proof that it suffices."* (`docs/SCOPE_AND_LIMITATIONS.md`, verbatim on
   this point.)

4. **"Record-neutral refinements are physically realizable."**
   True only in the existential sense. Licensed sentence: *"At least one
   physically motivated record-neutral refinement exists — the
   `PhysicalRefinement/` witness, an internal unitary coupling in `H 3`.
   We do not show that every projective refinement is record-neutral, and
   the headline theorem's premise (`RefinementInvariantLocal`, hence
   `AxGrain`) continues to quantify over every refinement without this
   existential fact physically justifying it in general."*

5. **"We refute indexed counting."**
   Not licensed. Licensed sentence: *"We have neither refuted nor
   formalized Khawaja's indexed counting. `docs/RIVAL_RULES.md` only
   observes that it adds a datum (the redundancy index) that the type
   `Est : Perspective n → Submodule ℂ (H n) → ℝ` does not carry — the rule
   is therefore not of the form `AxGrain` presupposes, which is a type
   mismatch, not a proof that it would violate invariance once suitably
   typed."*

6. **"The result holds for quantum systems."**
   Too broad. Licensed sentence: *"The projective result holds for spaces
   of dimension `n ≥ 3` (the domain of the upstream Gleason theorem). It
   does not cover the qubit (`n = 2`): on the contrary, we exhibit there a
   non-Born rule coherent under the same rationality axioms
   (`grain_does_not_imply_born_at_two`). The effect route, the only one
   potentially able to cover `n ≥ 1` including the qubit, is not built in
   this repository (`docs/QUBIT_FEASIBILITY_REPORT.md`)."*

7. **"The witness exhibits an ancilla coupling."**
   Interpretation, not a fact of the type. Licensed sentence: *"The
   witness exhibits an internal unitary rotation on a block of two basis
   vectors of `H 3`. Calling it an ancilla coupling is a physical
   interpretation of that rotation, developed in prose; `H 3` carries no
   system/ancilla tensor factorization, and nothing in the type
   `Submodule ℂ (H 3)` distinguishes an ancilla from any other
   subspace."* (See Section 1 and `AGENTS.md` rule 13 on the
   `AncillaNotInRecordAlgebra` → `RefinementNotInRecordAlgebra` rename
   motivated by this same distinction.)

8. **"Rational expectation is a neutral hypothesis."**
   False for affinity. Licensed sentence: *"Affinity of
   `RationalExpectationFamily` is a substantial hypothesis, rejected by
   non-expected-utility decision theories (rank-dependent utility: Quiggin
   1982, Yaari 1987). `maxExpectation`, the max over cells, is its explicit
   negative witness: monotone and normalized, but provably not affine
   (`maxExpectation_not_affine`)."*
