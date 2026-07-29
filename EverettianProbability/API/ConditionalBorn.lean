import EverettianProbability.Diachronic.ProjectiveBornContinuators

/-!
**FR.** # API conditionnelle de la regle de Born

Cette facade publique stable regroupe les premisses explicites du resultat
conditionnel : famille d'esperance rationnelle, invariance locale sous
raffinement, dimension au moins trois, etat normalise et nullite sur le
support orthogonal. Sous ces premisses, le poids canonique et la valeur des
actes sont donnes par les poids et l'esperance de Born.

Cette facade ne suppose ni ne prouve la realisabilite physique des
raffinements.

**EN.** # Conditional Born-rule API

This stable public facade packages the explicit conditional premises: a
rational expectation family, local refinement invariance, dimension at least
three, a normalized state, and nullity on orthogonal support. Under these
premises, canonical weight and act value are given by Born weights and Born
expectation.

This facade neither assumes nor proves the physical realizability of
refinements.
-/

namespace EverettianProbability.API.Conditional

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core
open EverettianProbability.Abstract
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : ℕ}

/-- Projective acts used by the conditional public API. -/
abbrev ProjectiveAct (n : ℕ) := Act (Projective.interface n)

/-- Projective rational expectation families used by the conditional public
API. -/
abbrev ProjectiveExpectationFamily (n : ℕ) :=
  RationalExpectationFamily (Projective.interface n)

/-- Explicit premises of the conditional projective Born theorem.

`refinement_invariant` is normative; `null_support` links the canonical
weight to the selected quantum state. -/
structure ProjectiveBornPremises (n : ℕ) where
  F : ProjectiveExpectationFamily n
  state : H n
  dim_ge_three : 3 ≤ n
  refinement_invariant : RefinementInvariantLocal F.V
  normalized : ‖state‖ = 1
  null_support : AxNul
    (EverettianProbability.BornCalibration.canonicalWeight
      (projectiveConcreteExpectationFamily F)) state

namespace ProjectiveBornPremises

/-- Under the conditional premises, projective canonical weight is Born
weight. -/
theorem canonicalWeight_eq_born
    (P : ProjectiveBornPremises n)
    (D : Perspective n)
    (c : (Projective.interface n).Cell D) :
    canonicalWeight P.F D c = ‖projL c.val P.state‖ ^ 2 :=
  projectiveCanonicalWeight_eq_born P.F P.dim_ge_three
    P.refinement_invariant P.normalized P.null_support D c

theorem canonicalWeight_ne_zero_of_bornWeight_ne_zero
    (P : ProjectiveBornPremises n)
    (D : Perspective n)
    (c : (Projective.interface n).Cell D)
    (hc : ‖projL c.val P.state‖ ^ 2 ≠ 0) :
    canonicalWeight P.F D c ≠ 0 := by
  rw [P.canonicalWeight_eq_born D c]
  exact hc

/-- Every act is valued by its Born expectation under the explicit conditional
premises. -/
theorem value_eq_bornExpectation
    (P : ProjectiveBornPremises n)
    (D : Perspective n)
    (a : ProjectiveAct n) :
    P.F.V D a = ∑ c ∈ D.cells, ‖projL c P.state‖ ^ 2 * a c := by
  change (projectiveConcreteExpectationFamily P.F).V D a =
    ∑ c ∈ D.cells, ‖projL c P.state‖ ^ 2 * a c
  exact EverettianProbability.BornCalibration.born_expectation_of_invariance
    (projectiveConcreteExpectationFamily P.F) P.dim_ge_three
    (projectiveRefinementInvariantLocal_toConcrete P.F P.refinement_invariant)
    P.normalized P.null_support D a

theorem canonicalWeight_nonneg
    (P : ProjectiveBornPremises n)
    (D : Perspective n)
    (c : (Projective.interface n).Cell D) :
    0 ≤ canonicalWeight P.F D c :=
  canonicalWeight_axPos P.F D c

theorem sum_canonicalWeight_eq_one
    (P : ProjectiveBornPremises n)
    (D : Perspective n) :
    (∑ c : (Projective.interface n).Cell D, canonicalWeight P.F D c) = 1 :=
  canonicalWeight_axNorm P.F D (by exact Subtype.val_injective)

end ProjectiveBornPremises

end
end EverettianProbability.API.Conditional
