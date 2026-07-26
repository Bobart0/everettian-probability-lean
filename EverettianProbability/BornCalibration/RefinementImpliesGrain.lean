import EverettianProbability.Preference.Representation
import EverettianProbability.Refinement.PayoffPreserving

/-!
**FR.** # L'invariance sous raffinement force Grain

Le résultat pivot de l'article II : si la fonctionnelle d'espérance `V`
d'une famille rationnelle est invariante sous toute redescription localement
équivalente (`RefinementInvariantLocal`), alors le poids contextuel
qu'elle induit satisfait l'axiome `AxGrain` de la caractérisation de mesure
amont. Une fois ce pont établi, `grainCoherenceTheorem_projector`
(`QuantumFoundations.BornRule.Assembly`, déjà prouvé, jamais re-prouvé
ici) transforme cette espérance cohérente en espérance de Born — voir
`BornExpectation.lean`. Énoncé comme but ouvert dans ce jalon P1 : c'est le
premier théorème scientifique du programme, hors de portée de P1
(section 7 du prompt de bootstrap).

**EN.** # Refinement invariance forces Grain

The pivotal result of paper II: if the expectation functional `V` of a
rational family is invariant under every locally equivalent redescription
(`RefinementInvariantLocal`), then the contextual weight it induces satisfies the
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

private theorem indicator_sum_eq (F : RationalExpectationFamily n)
    (D : Perspective n) {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
    (∑ d ∈ D.cells, canonicalWeight F D d * Act.indicator c d) =
      canonicalWeight F D c := by
  classical
  rw [Finset.sum_eq_single c]
  · simp only [Act.indicator_self, mul_one]
  · intro d hd hdc
    rw [Act.indicator_of_ne hdc, mul_zero]
  · exact fun hnot => (hnot hc).elim

private theorem pullback_indicator_sum_eq (F : RationalExpectationFamily n)
    {D' D : Perspective n} (r : Refines D' D)
    {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
    (∑ c' ∈ D'.cells,
        canonicalWeight F D' c' * pullbackAct r (Act.indicator c) c') =
      ∑ c' ∈ coarseCells D' c, canonicalWeight F D' c' := by
  classical
  rw [coarseCells_eq_fiber_parentOf r hc]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c' hc'
  unfold pullbackAct Act.indicator
  simp only [Function.comp_apply]
  by_cases hp : parentOf r c' = c
  · simp only [hp, if_true, mul_one]
  · simp only [hp, if_false, mul_zero]

/-- **FR.** L'invariance locale sous tous les raffinements force l'axiome
`AxGrain` pour le poids canonique.

**EN.** Local invariance under all refinements forces `AxGrain` for the
canonical weight. -/
theorem refinement_invariant_implies_grain (F : RationalExpectationFamily n)
    (hinv : RefinementInvariantLocal F.V) :
    AxGrain (canonicalWeight F) := by
  apply (axGrain_iff_coarseCells (canonicalWeight F)).2
  intro D' D r c hc
  have h := hinv r (pullbackAct r (Act.indicator c)) (Act.indicator c)
    (Act.agreeOn_refl D' (pullbackAct r (Act.indicator c)))
  rw [represents F D' (pullbackAct r (Act.indicator c)),
    represents F D (Act.indicator c),
    pullback_indicator_sum_eq F r hc, indicator_sum_eq F D hc] at h
  exact h.symm

end EverettianProbability.BornCalibration
