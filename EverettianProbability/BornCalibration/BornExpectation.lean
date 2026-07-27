import EverettianProbability.BornCalibration.RefinementImpliesGrain
import QuantumFoundations.ProbabilityAPI

/-!
**FR.** # Espérance de Born

Le résultat de clôture de l'article II, **prouvé sans but ouvert** depuis
la reprise P3/P4 (voir `MILESTONES.md`) : sous **deux prémisses-ponts**
distinctes — l'invariance locale sous raffinement
(`RefinementInvariantLocal`, purement normative) et la nullité du poids
canonique sur le support de l'état (`AxNul (canonicalWeight F) v`, un pont
normatif-physique, seul point d'entrée de l'état `v` dans les hypothèses)
— plus `RationalExpectationFamily` et **`3 ≤ n`**, la fonctionnelle
d'espérance rationnelle `F.V` coïncide, sur toute perspective, avec
l'espérance de Born `∑ c ∈ D.cells, ‖projL c v‖² * a c`. `AxNorm` et
`AxPos` ne sont pas des hypothèses supplémentaires : elles sont dérivées de
`RationalExpectationFamily` (`canonicalWeight_axNorm`,
`canonicalWeight_axPos`). La restriction `3 ≤ n` n'est pas une formalité :
`grain_does_not_imply_born_at_two` (`NonCircularity.lean`) montre qu'elle
est nécessaire, puisqu'en `n = 2` Grain seul n'implique pas Born.

L'`example` ci-dessous reste, par construction, indépendant de ce résultat :
c'est le critère de sortie du jalon P1 (section 8 du prompt de bootstrap),
toujours valide. Il ne dépend d'aucune définition propre à ce dépôt —
seulement de `grainCoherenceTheorem_projector`, déjà prouvé en amont
(`QuantumFoundations.BornRule.Assembly`) — et atteste que le pin Lake vers
`quantum_foundations` expose bien ce théorème avec la signature attendue.

**EN.** # Born expectation

The closing result of paper II, **proved with no open goal** since the
P3/P4 resumption (see `MILESTONES.md`): under **two distinct bridge
premises** — local invariance under refinement
(`RefinementInvariantLocal`, purely normative) and null canonical weight on
the state's support (`AxNul (canonicalWeight F) v`, a normative-physical
bridge, the only place the state `v` enters the hypotheses) — plus
`RationalExpectationFamily` and **`3 ≤ n`**, the rational expectation
functional `F.V` coincides, on every perspective, with the Born expectation
`∑ c ∈ D.cells, ‖projL c v‖² * a c`. `AxNorm` and `AxPos` are not extra
hypotheses: they are derived from `RationalExpectationFamily`
(`canonicalWeight_axNorm`, `canonicalWeight_axPos`). The `3 ≤ n`
restriction is not a formality: `grain_does_not_imply_born_at_two`
(`NonCircularity.lean`) shows it is necessary, since at `n = 2` Grain alone
does not imply Born.

The `example` below remains, by construction, independent of this result:
it is the P1 milestone's exit criterion (section 8 of the bootstrap
prompt), still valid. It depends on no definition specific to this
repository — only on `grainCoherenceTheorem_projector`, already proved
upstream (`QuantumFoundations.BornRule.Assembly`) — and certifies that the
Lake pin to `quantum_foundations` does expose that theorem with the
expected signature.
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
