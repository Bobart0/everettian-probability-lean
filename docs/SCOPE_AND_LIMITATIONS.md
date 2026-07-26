# SCOPE_AND_LIMITATIONS.md

## Français

- Aucune norme de rationalité n’est dérivée de la seule dynamique unitaire.
  `RefinementInvariantLocal` est une prémisse normative assumée.
- Le théorème principal (`born_expectation_of_invariance`) repose sur
  **deux** prémisses-ponts, non sur une seule : l’indifférence aux
  raffinements (`RefinementInvariantLocal`, normative pure), et le respect
  du support de l’état (`hNul : AxNul (canonicalWeight F) v`, une
  contrainte sur les poids de l’agent qui référence l’état physique `v` —
  c’est le seul endroit où `v` entre dans les hypothèses du théorème). La
  seconde est défendable — un agent n’affecte pas de valeur à des branches
  d’amplitude nulle — mais elle est **assumée**, non dérivée ; elle n’est
  ni purement normative ni purement physique, mais un pont normatif-physique
  entre les deux. `AxNorm` et `AxPos` sur `canonicalWeight F`, en
  revanche, sont **dérivées** des axiomes de `RationalExpectationFamily`,
  pas assumées séparément.
- La prémisse adoptée quantifie sur **tous** les raffinements projectifs. Elle
  est la *branching indifference* de Wallace transposée au cadre projectif :
  ni plus faible, ni plus neutre. Le dépôt ne revendique pas une prémisse
  affaiblie, mais son isolement, sa formalisation, et la démonstration qu’elle
  suffit.
- L’affinité de `RationalExpectationFamily` est une hypothèse forte. Les
  théories non linéaires de l’utilité espérée (dépendantes du rang :
  Quiggin 1982, Yaari 1987) restent hors de portée — `maxExpectation`
  (`Preference/NonTriviality.lean`), le maximum sur les cellules, en est le
  témoin négatif explicite : monotone et normalisé, mais provablement non
  affine (`maxExpectation_not_affine`).
- Lean ne tranche pas l’interprétation philosophique de l’incertitude
  personnelle ; il vérifie seulement les implications entre prémisses.
- La conclusion projective de Born utilise `3 ≤ n`. La route effets reste
  disponible dans l’interface abstraite, mais n’est pas substituée ici au
  théorème projectif.
- La lecture globale antérieure est formalisée uniquement comme résultat
  négatif dans `GlobalPayoffVacuity.lean`; elle ne sert plus de prémisse.
- **P6a** (`PhysicalRefinement/`) établit qu'un raffinement peut redécrire
  les branches plus finement sans en créer de nouvelles au sens physique
  — un raffinement *record-neutre* est physiquement réalisable par un
  couplage unitaire à un ancilla. C'est une preuve d'**existence**, pas
  d'**universalité** : le témoin montre qu'*au moins un* raffinement de ce
  type existe dans `H 3`, il ne classifie pas tous les raffinements
  projectifs selon qu'ils sont record-neutres, et il ne prétend pas que
  *tout* raffinement admet une telle réalisation physique. `RestrictedRecordSectors`
  n'est pas utilisé, et aucun pont général vers une restriction de
  `RefinementInvariantLocal` aux seuls raffinements record-neutres n'est
  ouvert par ce témoin.
- Le témoin P6a est en outre **schématique** : `H 3` n'a ni factorisation
  tensorielle explicite système/ancilla, ni dynamique temporelle, ni
  décohérence, et la désignation de l'algèbre des records
  (`coarsePerspective.cells`) y est *stipulée* — via l'hypothèse nommée
  `RefinementNotInRecordAlgebra` — plutôt que dérivée d'un principe physique
  indépendant. La brique manquante identifiée pour dépasser ce caractère
  schématique est nommée : une porte de rotation d'amplitude *contrôlée*,
  combinant le contrôle à deux sites de `ControlledBitFlip`
  (`Complexity/Gates/ControlledBitFlip.lean`, amont) avec le mélange
  d'amplitude de `AmplitudeRotation`
  (`Complexity/Gates/AmplitudeRotation.lean`, amont) — à construire et à
  exporter en amont ; elle n'existe pas aujourd'hui sous cette forme
  combinée.

## English

- No rationality norm is derived from unitary dynamics alone.
  `RefinementInvariantLocal` is an assumed normative premise.
- The headline theorem (`born_expectation_of_invariance`) rests on **two**
  bridge premises, not one: indifference to refinement
  (`RefinementInvariantLocal`, purely normative), and respect for the
  state's support (`hNul : AxNul (canonicalWeight F) v`, a constraint on
  the *agent's* weights that references the physical state `v` — the only
  place `v` enters the theorem's hypotheses). The second is defensible —
  an agent assigns no value to zero-amplitude branches — but it is
  **assumed**, not derived; it is neither purely normative nor purely
  physical, but a normative-physical bridge between the two. `AxNorm` and
  `AxPos` on `canonicalWeight F`, by contrast, are **derived** from
  `RationalExpectationFamily`'s axioms, not separately assumed.
- The adopted premise quantifies over **all** projective refinements. It is
  Wallace’s *branching indifference* transposed to the projective setting:
  neither weaker nor more neutral. The repository claims not a weakened
  premise, but its isolation, formalization, and a proof that it suffices.
- Affinity of `RationalExpectationFamily` is a strong assumption. Nonlinear
  (rank-dependent: Quiggin 1982, Yaari 1987) expected-utility theories
  remain outside the scope — `maxExpectation`
  (`Preference/NonTriviality.lean`), the max over cells, is its explicit
  negative witness: monotone and normalized, but provably not affine
  (`maxExpectation_not_affine`).
- Lean does not settle the philosophical interpretation of personal
  uncertainty; it verifies only implications between premises.
- The projective Born conclusion uses `3 ≤ n`. The effect route remains
  available in the abstract interface but is not substituted here for the
  projective theorem.
- The former global reading is formalized only as a negative result in
  `GlobalPayoffVacuity.lean`; it is no longer used as a premise.
- **P6a** (`PhysicalRefinement/`) establishes that a refinement can
  redescribe branches more finely without physically creating new ones —
  a *record-neutral* refinement is physically realizable through a
  unitary ancilla coupling. This is an **existence** proof, not a
  **universality** one: the witness shows that *at least one* refinement
  of this kind exists in `H 3`; it does not classify every projective
  refinement by whether it is record-neutral, and it does not claim that
  *every* refinement admits such a physical realization.
  `RestrictedRecordSectors` is not used, and no general bridge restricting
  `RefinementInvariantLocal` to record-neutral refinements alone is opened
  by this witness.
- The P6a witness is furthermore **schematic**: `H 3` has no explicit
  system/ancilla tensor factorization, no temporal dynamics, no
  decoherence, and the designation of the record algebra
  (`coarsePerspective.cells`) is *stipulated* there — via the named
  hypothesis `RefinementNotInRecordAlgebra` — rather than derived from an
  independent physical principle. The missing brick identified to move
  past this schematic character is named: a *controlled* amplitude-rotation
  gate, combining `ControlledBitFlip`'s two-site control
  (`Complexity/Gates/ControlledBitFlip.lean`, upstream) with
  `AmplitudeRotation`'s amplitude mixing
  (`Complexity/Gates/AmplitudeRotation.lean`, upstream) — to be built and
  exported upstream; it does not exist today in this combined form.
