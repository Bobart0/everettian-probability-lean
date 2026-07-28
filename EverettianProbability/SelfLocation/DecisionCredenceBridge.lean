import EverettianProbability.SelfLocation.UniformCredenceRefinementFailure

/-!
**FR.** # Pont entre valeur décisionnelle et crédence auto-localisante

Ce module formalise un pont opérationnel entre deux rôles probabilistes. Une
famille rationnelle `F` attribue une valeur `F.V D a` à chaque acte, tandis
qu'une famille de crédences `C` attribue une crédence à chaque cellule lorsque
le record n'exclut aucune alternative.

Le pont décisionnel exige que la valeur rationnelle de tout acte soit
l'espérance de ses conséquences calculée avec ces crédences
auto-localisantes. Le théorème de représentation déjà établi implique alors
que ces crédences coïncident avec le poids canonique ; réciproquement,
l'accord avec le poids canonique représente toute la fonctionnelle
décisionnelle.

Ce pont est de type `NORM + SEM` : il identifie les coefficients qui
gouvernent les décisions avec les degrés de croyance de l'agent. Il n'est pas
dérivé de la seule dynamique unitaire.

**EN.** # Bridge between decision value and self-locating credence

This module formalizes an operational bridge between two probabilistic roles.
A rational family `F` assigns a value `F.V D a` to every act, whereas a
credence family `C` assigns a credence to every cell when the accessible record
excludes no alternative.

The decision bridge requires the rational value of every act to equal the
expectation of its consequences computed using those self-locating credences.
The previously established representation theorem then implies that these
credences coincide with canonical weight; conversely, canonical agreement
represents the entire decision functional.

This is a `NORM + SEM` bridge: it identifies the coefficients governing
decisions with the agent's degrees of belief. It is not derived from unitary
dynamics alone.
-/

namespace EverettianProbability.Abstract

open scoped BigOperators Classical

noncomputable section

variable {I : PerspectiveInterface}

namespace RecordCredenceFamily

/-- The unrestricted self-locating credences represent the rational decision
value of every act. Acts are total on the ambient outcome space, while the
sum ranges only over cells of the current perspective.

This is a mixed `NORM + SEM` bridge. -/
def RepresentsUnrestrictedDecisionValue
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I) : Prop :=
  ∀ (D : I.Perspective)
    (_hInj : Function.Injective (@I.outcome D))
    (a : Act I),
    F.V D a =
      ∑ c : I.Cell D,
        C.credence D Finset.univ c *
          a (I.outcome c)

/-- If unrestricted credences represent every decision value, they coincide
with canonical weight on every cell. -/
theorem agreesOnUnrestrictedRecord_of_representsUnrestrictedDecisionValue
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I)
    (hrep :
      C.RepresentsUnrestrictedDecisionValue F) :
    C.AgreesOnUnrestrictedRecord F := by
  intro D hInj c
  have hweights :=
    weights_unique_on_cells
      F
      D
      hInj
      (fun x => C.credence D Finset.univ x)
      (by
        intro a
        exact hrep D hInj a)
  exact hweights c

/-- Canonical agreement on the unrestricted record represents the rational
value of every act. -/
theorem representsUnrestrictedDecisionValue_of_agreesOnUnrestrictedRecord
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I)
    (hagree :
      C.AgreesOnUnrestrictedRecord F) :
    C.RepresentsUnrestrictedDecisionValue F := by
  intro D hInj a
  rw [represents F D hInj a]
  apply Finset.sum_congr rfl
  intro c hc
  rw [hagree D hInj c]

/-- Representing unrestricted decision values is exactly equivalent to
unrestricted canonical agreement. -/
theorem representsUnrestrictedDecisionValue_iff_agreesOnUnrestrictedRecord
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I) :
    C.RepresentsUnrestrictedDecisionValue F ↔
      C.AgreesOnUnrestrictedRecord F := by
  constructor
  · exact
      C.agreesOnUnrestrictedRecord_of_representsUnrestrictedDecisionValue F
  · exact
      C.representsUnrestrictedDecisionValue_of_agreesOnUnrestrictedRecord F

theorem canonicalRecordCredenceFamily_representsUnrestrictedDecisionValue
    (F : RationalExpectationFamily I) :
    (canonicalRecordCredenceFamily F).RepresentsUnrestrictedDecisionValue F := by
  exact
    (canonicalRecordCredenceFamily F).representsUnrestrictedDecisionValue_of_agreesOnUnrestrictedRecord
      F
      (canonicalRecordCredenceFamily_agrees_unrestricted F)

/-- Under the decision bridge, the credence of a cell equals the rational value
of the unit-payoff indicator act for that cell. -/
theorem credence_eq_indicatorDecisionValue_of_representsUnrestrictedDecisionValue
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I)
    (hrep :
      C.RepresentsUnrestrictedDecisionValue F)
    (D : I.Perspective)
    (hInj :
      Function.Injective (@I.outcome D))
    (c : I.Cell D) :
    C.credence D Finset.univ c =
      F.V D (Act.indicator (I.outcome c)) := by
  have hagree :
      C.AgreesOnUnrestrictedRecord F :=
    C.agreesOnUnrestrictedRecord_of_representsUnrestrictedDecisionValue
      F hrep
  calc
    C.credence D Finset.univ c =
        canonicalWeight F D c :=
      hagree D hInj c
    _ = F.V D (Act.indicator (I.outcome c)) := by
      rfl

/-- When canonical weights are nonuniform, the uniform credence rival cannot
represent the same unrestricted decision functional. -/
theorem uniformRecordCredenceFamily_not_representsUnrestrictedDecisionValue_of_canonicalWeight_ne
    (F : RationalExpectationFamily I)
    (D : I.Perspective)
    (hInj :
      Function.Injective (@I.outcome D))
    (c d : I.Cell D)
    (hweights :
      canonicalWeight F D c ≠
        canonicalWeight F D d) :
    ¬ (uniformRecordCredenceFamily I).RepresentsUnrestrictedDecisionValue F := by
  intro hrep
  have hagree :
      (uniformRecordCredenceFamily I).AgreesOnUnrestrictedRecord F :=
    (uniformRecordCredenceFamily I).agreesOnUnrestrictedRecord_of_representsUnrestrictedDecisionValue
      F hrep
  exact
    uniformRecordCredenceFamily_not_agrees_unrestricted_of_canonicalWeight_ne
      F D hInj c d hweights hagree

/-- Decision representation, normalization, and odds invariance under record
restriction uniquely determine canonical conditioned credence. -/
theorem credence_eq_recordConditionedCredence_of_normalized_of_decisionRepresentation_of_oddsInvariant
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I)
    (hnorm :
      C.NormalizedOnNonzeroMass F)
    (hdecision :
      C.RepresentsUnrestrictedDecisionValue F)
    (hodds :
      C.OddsInvariantUnderRecordRestriction F)
    (hInjAll :
      ∀ D : I.Perspective,
        Function.Injective (@I.outcome D))
    (D : I.Perspective)
    (compatible : Finset (I.Cell D))
    (hmass :
      recordCompatibleMass F D compatible ≠ 0)
    (c : I.Cell D) :
    C.credence D compatible c =
      recordConditionedCredence
        F D compatible c := by
  have hagree :
      C.AgreesOnUnrestrictedRecord F :=
    C.agreesOnUnrestrictedRecord_of_representsUnrestrictedDecisionValue
      F hdecision
  exact
    C.credence_eq_recordConditionedCredence_of_normalized_of_agrees_unrestricted_of_oddsInvariant
      F
      hnorm
      hagree
      hodds
      hInjAll
      D
      compatible
      hmass
      c

/-- A normalized record credence family satisfying the decision bridge and
record-restriction odds invariance inherits refinement coherence. -/
theorem refinementCoherent_of_normalized_of_decisionRepresentation_of_oddsInvariant
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I)
    (hnorm :
      C.NormalizedOnNonzeroMass F)
    (hdecision :
      C.RepresentsUnrestrictedDecisionValue F)
    (hodds :
      C.OddsInvariantUnderRecordRestriction F)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll :
      ∀ D : I.Perspective,
        Function.Injective (@I.outcome D)) :
    C.RefinementCoherent F hinv hInjAll := by
  have hagree :
      C.AgreesOnUnrestrictedRecord F :=
    C.agreesOnUnrestrictedRecord_of_representsUnrestrictedDecisionValue
      F hdecision
  intro fine coarse r compatible j hmass
  exact
    RecordCredenceFamily.refinementCoherent_of_normalized_of_agrees_unrestricted_of_oddsInvariant
      C
      F
      hnorm
      hagree
      hodds
      hinv
      hInjAll
      r
      compatible
      j
      hmass

end RecordCredenceFamily

end
end EverettianProbability.Abstract
