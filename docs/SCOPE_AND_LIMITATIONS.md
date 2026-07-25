# SCOPE_AND_LIMITATIONS.md

## Français

Ce que ce dépôt **ne** prouve **pas**, dès P1 :

- **Aucune dérivation d'une norme de rationalité à partir de la seule
  dynamique unitaire.** L'invariance sous raffinement
  (`PayoffPreserving`, préservée par la fonctionnelle d'espérance `V`)
  est une **prémisse normative**, assumée comme telle dans
  `Refinement/PayoffPreserving.lean` et `Preference/
  ExpectationFunctional.lean` — jamais dérivée d'une propriété de
  l'évolution unitaire des états.
- **L'affinité du fonctionnel d'espérance est elle-même une hypothèse
  forte.** `RationalExpectationFamily.affine`
  (`Preference/ExpectationFunctional.lean`) postule que l'espérance
  d'une combinaison affine d'actes est la combinaison affine des
  espérances. Les théories de la décision non-espérance (par exemple à
  la Buchak, ou les modèles à aversion à l'ambiguïté non linéaires) la
  rejettent explicitement ; ce dépôt ne prétend pas les réfuter, il
  travaille dans le cadre où elle est acceptée.
- **Lean ne tranche pas la sémantique de l'incertitude personnelle.** Que
  l'espérance rationnelle porte sur une incertitude *de facto*
  (ignorance de la branche réalisée) ou une incertitude au sens de
  Savage (croyance rationnelle sur un futur non déterminé) est une
  question d'interprétation philosophique, hors de portée d'une preuve
  formelle. Le formalisme Lean est neutre sur ce point : il ne prouve
  que des implications logiques entre axiomes.
- **La route projective hérite de `n ≥ 3` (Gleason).** `Core/Interface.
  lean` documente le choix (encore ouvert, décision P0.3) entre cette
  route et la route effets ; tant que la route projective est utilisée
  seule (comme en P1), aucun résultat de ce dépôt ne s'applique au cas
  `n = 2` (qubit) sans passer par l'API `EffectPerspectives`/Busch en
  amont.
- **Aucun théorème scientifique n'est prouvé en P1.** Les sept buts
  ouverts budgétés (`SORRY_BUDGET`, voir `MILESTONES.md`) couvrent
  précisément le contenu mathématique de l'article II ; seule
  l'infrastructure et le squelette compilable sont livrés à ce jalon.

## English

What this repository does **not** prove, as of P1:

- **No derivation of a rationality norm from unitary dynamics alone.**
  Refinement invariance (`PayoffPreserving`, preserved by the
  expectation functional `V`) is a **normative premise**, assumed as
  such in `Refinement/PayoffPreserving.lean` and `Preference/
  ExpectationFunctional.lean` — never derived from a property of the
  unitary evolution of states.
- **The affinity of the expectation functional is itself a strong
  hypothesis.** `RationalExpectationFamily.affine`
  (`Preference/ExpectationFunctional.lean`) postulates that the
  expectation of an affine combination of acts is the affine combination
  of the expectations. Non-expected-utility decision theories (e.g.
  Buchak-style, or nonlinear ambiguity-aversion models) explicitly
  reject it; this repository does not claim to refute them, it works
  within the framework where it is accepted.
- **Lean does not settle the semantics of personal uncertainty.**
  Whether rational expectation is about *de facto* uncertainty (not
  knowing which branch is realized) or Savage-style uncertainty
  (rational belief about an undetermined future) is a question of
  philosophical interpretation, outside the reach of a formal proof. The
  Lean formalism is neutral on this point: it proves only logical
  implications between axioms.
- **The projective route inherits `n ≥ 3` (Gleason).** `Core/Interface.
  lean` documents the choice (still open, decision P0.3) between this
  route and the effect route; as long as the projective route is used
  alone (as in P1), no result in this repository applies to the `n = 2`
  case (qubit) without going through the upstream
  `EffectPerspectives`/Busch API.
- **No scientific theorem is proved in P1.** The seven budgeted open
  goals (`SORRY_BUDGET`, see `MILESTONES.md`) cover precisely the
  mathematical content of paper II; only the infrastructure and the
  compilable skeleton are delivered at this milestone.
