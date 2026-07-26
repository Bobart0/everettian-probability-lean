# SCOPE_AND_LIMITATIONS.md

## Français

- Aucune norme de rationalité n’est dérivée de la seule dynamique unitaire.
  `RefinementInvariantLocal` est une prémisse normative assumée.
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
- Une restriction future aux raffinements préservant les records demanderait
  le pont de réalisabilité physique P6a. Ce pont n’est ni supposé ni ouvert
  ici, et `RestrictedRecordSectors` n’est pas utilisé.

## English

- No rationality norm is derived from unitary dynamics alone.
  `RefinementInvariantLocal` is an assumed normative premise.
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
- A future restriction to record-preserving refinements would require P6a’s
  physical-realizability bridge. That bridge is neither assumed nor opened
  here, and `RestrictedRecordSectors` is not used.
