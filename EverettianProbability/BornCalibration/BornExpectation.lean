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

/-- The rational expectation functional of a refinement-invariant family
coincides with the Born expectation, on every perspective and every act. -/
theorem born_expectation_formula (F : RationalExpectationFamily n) (hn3 : 3 ≤ n)
    (hNorm : AxNorm (contextualWeight F)) (hPos : AxPos (contextualWeight F))
    {v : H n} (hv : ‖v‖ = 1) (hNul : AxNul (contextualWeight F) v)
    (hinv : ∀ {D' D : Perspective n} (r : Refines D' D) (a : Act n),
      PayoffPreserving a → F.V D' (pullbackAct r a) = F.V D a)
    (D : Perspective n) (a : Act n) :
    F.V D a = ∑ c ∈ D.cells, ‖projL c v‖ ^ 2 * a c := by
  sorry

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
