import EverettianProbability.BornCalibration.RefinementImpliesGrain
import QuantumFoundations.ProbabilityAPI

/-!
**FR.** # Espérance de Born

Le résultat de clôture de l'article II : sous les hypothèses de
`refinement_invariant_implies_grain`, plus (Norm), (Pos), (Null) et le
théorème de représentation, la fonctionnelle d'espérance rationnelle `F.V`
coïncide, sur toute perspective, avec l'espérance de Born
`∑ c ∈ D.cells, ‖projL c v‖² * a c`. Énoncé comme but ouvert : résultat
scientifique hors de portée de P1.

L'`example` ci-dessous, en revanche, **compile sans laisser aucun but
ouvert** : c'est le
critère de sortie du jalon P1 (section 8 du prompt de bootstrap). Il ne
dépend d'aucune définition propre à ce dépôt — seulement de
`grainCoherenceTheorem_projector`, déjà prouvé en amont
(`QuantumFoundations.BornRule.Assembly`) — et atteste que le pin Lake vers
`quantum_foundations` expose bien ce théorème avec la signature attendue.

**EN.** # Born expectation

The closing result of paper II: under the hypotheses of
`refinement_invariant_implies_grain`, plus (Norm), (Pos), (Null), and the
representation theorem, the rational expectation functional `F.V`
coincides, on every perspective, with the Born expectation
`∑ c ∈ D.cells, ‖projL c v‖² * a c`. Stated as an open goal: a scientific
result out of scope for P1.

The `example` below, by contrast, **compiles with no goal left open**: this is
the P1 milestone's exit criterion (section 8 of the bootstrap prompt). It
depends on no definition specific to this repository — only on
`grainCoherenceTheorem_projector`, already proved upstream
(`QuantumFoundations.BornRule.Assembly`) — and certifies that the Lake pin
to `quantum_foundations` does expose that theorem with the expected
signature.
-/

namespace EverettianProbability.BornCalibration

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Core EverettianProbability.Preference EverettianProbability.Refinement

variable {n : ℕ}

/-- **FR.** RÉSULTAT PORTANT UNE PRÉMISSE (`PREMISE-BEARING RESULT`). Les
axiomes généraux de rationalité, l'invariance locale normative et la nullité
physique du poids canonique entraînent l'espérance de Born. La positivité et
la normalisation de ce poids sont dérivées, non supposées.

**EN.** `PREMISE-BEARING RESULT`. General rationality axioms, normative local
invariance, and physical null support for the canonical weight entail Born
expectation. Positivity and normalization of that weight are derived rather
than assumed. -/
theorem born_expectation_of_invariance (F : RationalExpectationFamily n) (hn3 : 3 ≤ n)
    (hinv : RefinementInvariantLocal F.V)
    {v : H n} (hv : ‖v‖ = 1) (hNul : AxNul (canonicalWeight F) v)
    (D : Perspective n) (a : Act n) :
    F.V D a = ∑ c ∈ D.cells, ‖projL c v‖ ^ 2 * a c := by
  have hgrain : AxGrain (canonicalWeight F) :=
    refinement_invariant_implies_grain F hinv
  have hborn := grainCoherenceTheorem_projector
    (canonicalWeight F) hn3 hgrain (canonicalWeight_axNorm F)
      (canonicalWeight_axPos F) hv hNul
  rw [represents F D a]
  apply Finset.sum_congr rfl
  intro c hc
  rw [hborn D hc]

/-- **FR.** Corollaire de compatibilité de l'ancienne formulation : les
hypothèses `AxNorm` et `AxPos` explicites sont désormais redondantes, car
elles sont dérivées de `RationalExpectationFamily`.

**EN.** Compatibility corollary for the former formulation: explicit
`AxNorm` and `AxPos` assumptions are now redundant, because they follow from
`RationalExpectationFamily`. -/
theorem born_expectation_formula (F : RationalExpectationFamily n) (hn3 : 3 ≤ n)
    (_hNorm : AxNorm (canonicalWeight F)) (_hPos : AxPos (canonicalWeight F))
    {v : H n} (hv : ‖v‖ = 1) (hNul : AxNul (canonicalWeight F) v)
    (hinv : RefinementInvariantLocal F.V)
    (D : Perspective n) (a : Act n) :
    F.V D a = ∑ c ∈ D.cells, ‖projL c v‖ ^ 2 * a c :=
  born_expectation_of_invariance F hn3 hinv hv hNul D a

/-- Exit-criterion example (P1, section 8): `grainCoherenceTheorem_projector`
is importable from the new repository, through public upstream imports
only, with exactly the expected signature. No goal left open. -/
example {n : ℕ} (Est : Perspective n → Submodule ℂ (H n) → ℝ)
    (hn3 : 3 ≤ n) (hA : AxGrain Est) (hN : AxNorm Est) (hPos : AxPos Est)
    {v : H n} (hv : ‖v‖ = 1) (hNul : AxNul Est v)
    (D : Perspective n) {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
    Est D c = ‖projL c v‖ ^ 2 :=
  grainCoherenceTheorem_projector Est hn3 hA hN hPos hv hNul D hc

end EverettianProbability.BornCalibration
