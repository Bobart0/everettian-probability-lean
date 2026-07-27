import EverettianProbability.Preference.AbstractExpectationFunctional

/-!
**FR.** # Équivalence locale et invariance, niveau abstrait

L'analogue de `Refinement/PayoffPreserving.lean`'s prémisses (pas de
`bornExpectation` ici : l'espérance de Born est spécifique à la route
projective). `pullbackAct`/`AgreeOn` existent déjà, au niveau abstrait,
dans `Core/Interface.lean` ; ce fichier ajoute la forme locale
(`PayoffEquivalentAt`, `RefinementInvariantLocal`) et son équivalence avec
la forme globale déjà présente (`Abstract.RefinementInvariant`), pour toute
famille d'espérance abstraite.

**EN.** # Local equivalence and invariance, abstract level

The analogue of `Refinement/PayoffPreserving.lean`'s premises (no
`bornExpectation` here: Born expectation is specific to the projective
route). `pullbackAct`/`AgreeOn` already exist, abstractly, in
`Core/Interface.lean`; this file adds the local form
(`PayoffEquivalentAt`, `RefinementInvariantLocal`) and its equivalence with
the already-present global form (`Abstract.RefinementInvariant`), for any
abstract expectation family.
-/

namespace EverettianProbability.Abstract

variable {I : PerspectiveInterface}

/-- **FR.** Deux descriptions attribuent les mêmes conséquences à chaque
branche fine d'un raffinement donné.

**EN.** Two descriptions assign the same consequences to every fine branch
of a given refinement. -/
def PayoffEquivalentAt {fine coarse : I.Perspective} (r : I.Refinement fine coarse)
    (a' a : Act I) : Prop :=
  AgreeOn I fine a' (pullbackAct I r a)

/-- **FR.** `PREMISE` normative, niveau abstrait : invariance sous toute
redescription localement équivalente.

**EN.** Normative `PREMISE`, abstract level: invariance under every
locally equivalent redescription. -/
def RefinementInvariantLocal (V : I.Perspective → Act I → ℝ) : Prop :=
  ∀ {fine coarse : I.Perspective} (r : I.Refinement fine coarse) (a' a : Act I),
    PayoffEquivalentAt r a' a → V fine a' = V coarse a

/-- **FR.** Pour une famille rationnelle abstraite, la forme locale est
équivalente à l'invariance évaluée sur le tiré-en-arrière canonique.

**EN.** For an abstract rational family, the local form is equivalent to
invariance evaluated on the canonical pullback. -/
theorem refinementInvariantLocal_iff_pullback (F : RationalExpectationFamily I) :
    RefinementInvariantLocal F.V ↔ RefinementInvariant I F.V := by
  constructor
  · intro h fine coarse r a
    exact h r (pullbackAct I r a) a (Act.agreeOn_refl fine (pullbackAct I r a))
  · intro h fine coarse r a' a ha
    calc
      F.V fine a' = F.V fine (pullbackAct I r a) := V_congr_of_agreeOn F fine ha
      _ = F.V coarse a := h r a

end EverettianProbability.Abstract
