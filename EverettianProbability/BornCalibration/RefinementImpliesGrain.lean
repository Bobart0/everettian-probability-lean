import EverettianProbability.BornCalibration.ContextualWeight
import EverettianProbability.Refinement.PayoffPreserving

/-!
**FR.** # L'invariance sous raffinement force Grain

Le résultat pivot de l'article II : si la fonctionnelle d'espérance `V`
d'une famille rationnelle est invariante sous raffinement pour tout acte
préservant les conséquences (`PayoffPreserving`), alors le poids contextuel
qu'elle induit satisfait l'axiome `AxGrain` de la caractérisation de mesure
amont. Une fois ce pont établi, `grainCoherenceTheorem_projector`
(`QuantumFoundations.BornRule.Assembly`, déjà prouvé, jamais re-prouvé
ici) transforme cette espérance cohérente en espérance de Born — voir
`BornExpectation.lean`. Énoncé comme but ouvert dans ce jalon P1 : c'est le
premier théorème scientifique du programme, hors de portée de P1
(section 7 du prompt de bootstrap).

**EN.** # Refinement invariance forces Grain

The pivotal result of paper II: if the expectation functional `V` of a
rational family is refinement-invariant for every payoff-preserving act
(`PayoffPreserving`), then the contextual weight it induces satisfies the
upstream measure characterization's `AxGrain` axiom. Once this bridge is
established, `grainCoherenceTheorem_projector`
(`QuantumFoundations.BornRule.Assembly`, already proved, never re-proved
here) turns this coherent expectation into a Born expectation — see
`BornExpectation.lean`. Stated as an open goal in this P1 milestone: this is
the first scientific theorem of the program, out of scope for P1
(section 7 of the bootstrap prompt).
-/

namespace EverettianProbability.BornCalibration

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Core EverettianProbability.Preference EverettianProbability.Refinement

variable {n : ℕ}

/-- If `F.V` is invariant, along every refinement, for every
payoff-preserving act, then `contextualWeight F` satisfies `AxGrain`. -/
theorem refinement_invariant_implies_grain (F : RationalExpectationFamily n)
    (hinv : ∀ {D' D : Perspective n} (r : Refines D' D) (a : Act n),
      PayoffPreserving a → F.V D' (pullbackAct r a) = F.V D a) :
    AxGrain (contextualWeight F) := by
  sorry

end EverettianProbability.BornCalibration
