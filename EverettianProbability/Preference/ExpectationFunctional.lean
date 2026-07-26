import EverettianProbability.Core.Act

/-!
**FR.** # Famille d'espérance rationnelle

Une famille d'espérance rationnelle regroupe, pour chaque perspective `D`,
une fonctionnelle `V D : Act n → ℝ` satisfaisant trois axiomes de
rationalité minimale : affinité (l'espérance d'une combinaison affine
d'actes est la combinaison affine des espérances), monotonie (un acte
partout au moins aussi bon rapporte une espérance au moins aussi grande),
et normalisation sur les constantes (l'espérance d'un paiement certain est
ce paiement). L'affinité de la fonctionnelle est elle-même une hypothèse
substantielle, rejetée par les théories de la décision non-espérance :
voir `docs/SCOPE_AND_LIMITATIONS.md`.

**EN.** # Rational expectation family

A rational expectation family bundles, for each perspective `D`, a
functional `V D : Act n → ℝ` satisfying three minimal rationality axioms:
affinity (the expectation of an affine combination of acts is the affine
combination of the expectations), monotonicity (an act at least as good
everywhere yields an expectation at least as large), and normalization on
constants (the expectation of a certain payoff is that payoff). The
affinity of the functional is itself a substantial hypothesis, rejected by
non-expected-utility decision theories: see
`docs/SCOPE_AND_LIMITATIONS.md`.
-/

namespace EverettianProbability.Preference

open QuantumFoundations.BornRule Gleason EverettianProbability.Core

variable {n : ℕ}

/-- A rational expectation family: a per-perspective expectation functional
on acts, affine, monotone, and normalized on constants. -/
structure RationalExpectationFamily (n : ℕ) where
  /-- The expectation functional itself. -/
  V : Perspective n → Act n → ℝ
  /-- Affinity: the expectation of an affine combination of two acts is the
  affine combination of their expectations. -/
  affine : ∀ (D : Perspective n) (t : ℝ) (a b : Act n),
    V D (fun c => t * a c + (1 - t) * b c) = t * V D a + (1 - t) * V D b
  /-- Monotonicity, on the cells of the relevant perspective. -/
  monotone : ∀ (D : Perspective n) (a b : Act n),
    (∀ c ∈ D.cells, a c ≤ b c) → V D a ≤ V D b
  /-- Normalization: the expectation of a certain payoff is that payoff. -/
  normalized_const : ∀ (D : Perspective n) (k : ℝ), V D (Act.const k) = k

/-- **FR.** La monotonie locale force la fonctionnelle à ne dépendre que des
valeurs de l'acte sur les cellules de la perspective.

**EN.** Local monotonicity forces the functional to depend only on the act's
values on the cells of the perspective. -/
theorem V_congr_of_agreeOn (F : RationalExpectationFamily n) (D : Perspective n)
    {a b : Act n} (h : Act.AgreeOn D a b) : F.V D a = F.V D b := by
  apply le_antisymm
  · exact F.monotone D a b fun c hc => (h c hc).le
  · exact F.monotone D b a fun c hc => (h c hc).ge

end EverettianProbability.Preference
