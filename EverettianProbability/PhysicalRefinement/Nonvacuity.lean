import EverettianProbability.PhysicalRefinement.RecordNeutralWitness

/-!
**FR.** # Non-vacuité — `PhysicalRefinement`

Témoin positif concret : l'espérance bornienne, évaluée sur la perspective
fine avec le paiement tiré en arrière, ne dépend que du record accessible
`accessibleRecord`, et non de l'état complet. C'est le pendant bornien du
raffinement record-neutre : le couplage physique change la perspective fine
et l'état, mais l'espérance de Born reste déterminée par ce que l'agent peut
effectivement observer.

**EN.** # Nonvacuity — `PhysicalRefinement`

Concrete positive witness: Born expectation, evaluated on the fine
perspective against the pulled-back payoff, depends only on the accessible
record `accessibleRecord`, not on the full state. This is the Born
counterpart of the record-neutral refinement: the physical coupling changes
the fine perspective and the state, but Born expectation remains determined
by what the agent can actually observe.
-/

namespace EverettianProbability.PhysicalRefinement

open QuantumFoundations.ProbabilityAPI EverettianProbability.Core EverettianProbability.Refinement
open scoped Classical InnerProductSpace

theorem bornExpectation_coarse_payoff (v : H 3) :
    bornExpectation v coarsePerspective payoff = (accessibleRecord v).2 := by
  unfold bornExpectation accessibleRecord
  rw [coarsePerspective_cells_eq,
    Finset.sum_insert (by simpa using label0Line_ne_label1Space), Finset.sum_singleton]
  unfold payoff
  rw [Act.indicator_of_ne label0Line_ne_label1Space, Act.indicator_self]
  ring

/-- Born expectation of the pulled-back payoff on the fine perspective is
exactly the second coordinate of the accessible record, for *any* state —
not merely `psiBefore`/`psiAfter`. -/
theorem bornExpectation_fine_payoff_eq_accessibleRecord_snd (v : H 3) :
    bornExpectation v finePerspective (pullbackAct recordNeutral_refines payoff) =
      (accessibleRecord v).2 := by
  rw [bornExpectation_pullback_eq]
  exact bornExpectation_coarse_payoff v

/-- **FR.** Espérance bornienne insensible au raffinement record-neutre :
même valeur avant et après le couplage.

**EN.** Born expectation is insensitive to the record-neutral refinement:
same value before and after the coupling. -/
theorem born_insensitive_to_recordNeutral_refinement :
    bornExpectation psiBefore finePerspective (pullbackAct recordNeutral_refines payoff) =
      bornExpectation psiAfter finePerspective (pullbackAct recordNeutral_refines payoff) := by
  rw [bornExpectation_fine_payoff_eq_accessibleRecord_snd,
    bornExpectation_fine_payoff_eq_accessibleRecord_snd, recordNeutral_record_eq]

/-- **FR.** Pendant bornien de `counting_underdetermined_by_accessible_record`
(voir `NonTriviality.lean`) : à la différence du comptage naïf, l'espérance
bornienne est *entièrement déterminée* par le record accessible — deux états
au même record donnent la même valeur, pour tout paiement tiré en arrière
sur cette perspective.

**EN.** Born counterpart of `counting_underdetermined_by_accessible_record`
(see `NonTriviality.lean`): unlike naive counting, Born expectation is
*fully determined* by the accessible record — two states with the same
record give the same value, for any payoff pulled back on this
perspective. -/
theorem born_determined_by_accessible_record (u w : H 3)
    (h : accessibleRecord u = accessibleRecord w) :
    bornExpectation u finePerspective (pullbackAct recordNeutral_refines payoff) =
      bornExpectation w finePerspective (pullbackAct recordNeutral_refines payoff) := by
  rw [bornExpectation_fine_payoff_eq_accessibleRecord_snd,
    bornExpectation_fine_payoff_eq_accessibleRecord_snd, h]

end EverettianProbability.PhysicalRefinement
