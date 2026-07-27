import EverettianProbability.EffectCalibration.EstimationRulePackaging

/-!
**FR.** # Espérance de Born, route effets

L'analogue effets de `BornCalibration/BornExpectation.lean`. Deux
théorèmes, composables plutôt que fondus en un seul :

- `effectExpectation_represents` : toute famille d'espérance rationnelle
  sur l'interface effets s'étend en somme pondérée par le poids canonique
  — aucune restriction de dimension, aucune hypothèse de projectivité.
- `effectWeight_eq_born_of_invariance` : sous l'invariance locale sous
  raffinement et une nullité de support relative à l'état, le poids
  canonique d'**une sortie qui est une projection** égale la valeur de
  Born de cette projection.

**Portée — à lire avant tout emploi.** `effectWeight_eq_born_of_invariance`
ne couvre que les sorties dont l'effet **est** une projection orthogonale
(`hAi : D.effects i = Gleason.projL A`), pas les effets POVM authentiques
(non projectifs). Ce n'est pas une restriction cosmétique : la forme
générale « valeur d'espérance pour un effet quelconque » est explicitement
différée en amont (`EffectPerspectives/Main.lean`, QB8.3 — « not attempted
here... deferred, not silently dropped »), faute d'une identité de trace
publique pour un effet non projectif. Le théorème vaut pour **tout**
`n ≥ 1`, en particulier `n = 2` (le qubit — une mesure de Stern-Gerlach en
spin-1/2, où les deux issues sont précisément des projecteurs orthogonaux,
satisfait cette hypothèse nativement ; voir `EffectCalibration/
QubitWitness.lean`). Et — point qui serait mal compris s'il n'était pas
écrit ici même, dans ce docstring, plutôt que seulement dans les documents
de portée : `BornCalibration.NonCircularity.grain_does_not_imply_born_at_two`
**reste vrai** et ne contredit pas ce résultat. Ce dernier montre que Grain
seul (sans la structure effets — sans le lien `weight ↔ effet` que
`EstimationRule` impose) n'implique pas Born en `n = 2` ; celui-ci montre
que Grain **plus** la structure des effets (`EstimationRule.grain`,
empaquetée avec `nonneg`/`normalized`, puis reliée à un effet-projection
via `contextual_projection_weight_eq_born`) force bien Born, y compris en
`n = 2`. Les deux prémisses ne sont pas la même chose, et seule la seconde
est utilisée ici.

**EN.** # Born expectation, effect route

The effect-side analogue of `BornCalibration/BornExpectation.lean`. Two
theorems, composable rather than fused into one:

- `effectExpectation_represents`: any rational expectation family on the
  effect interface expands as the canonical-weight-weighted sum — no
  dimension restriction, no projectivity hypothesis.
- `effectWeight_eq_born_of_invariance`: under local refinement invariance
  and a state-relative null-support hypothesis, the canonical weight of
  **an outcome that is a projection** equals that projection's Born
  value.

**Scope — read before any use.** `effectWeight_eq_born_of_invariance` only
covers outcomes whose effect **is** an orthogonal projection
(`hAi : D.effects i = Gleason.projL A`), not genuine (non-projective) POVM
effects. This is not a cosmetic restriction: the general "expectation
value for an arbitrary effect" form is explicitly deferred upstream
(`EffectPerspectives/Main.lean`, QB8.3 — "not attempted here... deferred,
not silently dropped"), for want of a public trace identity for a
non-projective effect. The theorem holds for **every** `n ≥ 1`, in
particular `n = 2` (the qubit — a spin-1/2 Stern-Gerlach measurement, whose
two outcomes are precisely orthogonal projectors, satisfies this
hypothesis natively; see `EffectCalibration/QubitWitness.lean`). And — a
point that would be misread if it were written only in the scope
documents and not here, in this very docstring:
`BornCalibration.NonCircularity.grain_does_not_imply_born_at_two`
**remains true** and does not contradict this result. That theorem shows
Grain alone (without the effect structure — without the `weight ↔ effect`
link that `EstimationRule` imposes) does not imply Born at `n = 2`; this
one shows Grain **plus** the effect structure (`EstimationRule.grain`,
bundled with `nonneg`/`normalized`, then connected to a projection-effect
via `contextual_projection_weight_eq_born`) does force Born, including at
`n = 2`. The two premises are not the same thing, and only the second is
used here.
-/

namespace EverettianProbability.Abstract

open scoped BigOperators Classical
open QuantumFoundations.ProbabilityAPI

/-- Effect-side analogue of `represents`: any rational expectation family
on the effect interface expands as the canonical-weight-weighted sum over
a perspective's outcomes. No dimension restriction, no projectivity
hypothesis. -/
theorem effectExpectation_represents {n : ℕ}
    (F : RationalExpectationFamily (Effects.interface n))
    (D : EffectPerspectives.EffectPerspective n) (a : Act (Effects.interface n)) :
    F.V D a = ∑ i : Fin D.outcomes, canonicalWeight F D i * a i :=
  represents F D (outcome_injective_effects n D) a

/-- Effect-side analogue of `born_expectation_of_invariance`, stated per
outcome (see the module docstring for the exact scope: projective outcomes
only, every `n ≥ 1`, and why this does not contradict
`grain_does_not_imply_born_at_two`). -/
theorem effectWeight_eq_born_of_invariance {n : ℕ} (hn : 1 ≤ n)
    (F : RationalExpectationFamily (Effects.interface n))
    (hinv : RefinementInvariantLocal F.V)
    {v : H n} (hv : ‖v‖ = 1)
    (hNull : EffectPerspectives.ContextualNullSupport (canonicalEstimationRule F hinv) v)
    (D : EffectPerspectives.EffectPerspective n) (i : Fin D.outcomes)
    (A : Submodule ℂ (H n))
    (hAi : (D.effects i : H n →ₗ[ℂ] H n) = Gleason.projL A) :
    canonicalWeight F D i = ‖A.starProjection v‖ ^ 2 :=
  EffectPerspectives.contextual_projection_weight_eq_born hn v hv
    (canonicalEstimationRule F hinv) hNull D i A hAi

end EverettianProbability.Abstract
