import EverettianProbability.Refinement.PullbackAct

/-!
**FR.** # Invariance sous raffinement préservant les conséquences

Un acte est « préservant les conséquences sous raffinement » si sa valeur
sur toute cellule fine coïncide avec sa valeur tirée-en-arrière depuis la
perspective grossière : le paiement associé à une conséquence ne dépend pas
de la perspective utilisée pour la décrire, seulement de la branche
effectivement réalisée. C'est la prémisse normative centrale de l'article
II — voir l'encart « Frontière de portée » de `AGENTS.md` et
`docs/SCOPE_AND_LIMITATIONS.md` : cette invariance n'est *dérivée* d'aucune
propriété de la dynamique unitaire, elle est *assumée*.

**EN.** # Refinement invariance preserving consequences

An act is "payoff-preserving under refinement" if its value on every fine
cell coincides with its value pulled back from the coarse perspective: the
payoff attached to a consequence does not depend on the perspective used to
describe it, only on the branch actually realized. This is the central
normative premise of paper II — see the "Scope boundary" box in
`AGENTS.md` and `docs/SCOPE_AND_LIMITATIONS.md`: this invariance is not
*derived* from any property of the unitary dynamics, it is *assumed*.
-/

namespace EverettianProbability.Refinement

open QuantumFoundations.BornRule Gleason EverettianProbability.Core
open scoped Classical

variable {n : ℕ}

/-- An act `a` is payoff-preserving under refinement if, for every
refinement `r : Refines D' D`, `a` agrees with its own pullback along `r`
on the fine perspective `D'`. -/
def PayoffPreserving (a : Act n) : Prop :=
  ∀ {D' D : Perspective n} (r : Refines D' D), Act.AgreeOn D' a (pullbackAct r a)

/-- A family of expectation functionals is invariant under refinement when
evaluating a coarse act or its pullback to any finer perspective gives the
same value. This is a normative premise, not a dynamical theorem. -/
def RefinementInvariant
    (V : Perspective n → Act n → ℝ) : Prop :=
  ∀ {D' D : Perspective n} (r : Refines D' D) (a : Act n),
    V D' (pullbackAct r a) = V D a

/-- Born expectation of an act in the state vector `v`. -/
noncomputable def bornExpectation (v : H n) (D : Perspective n) (a : Act n) : ℝ :=
  ∑ c ∈ D.cells, ‖projL c v‖ ^ 2 * a c

/-- The Born expectation functional is invariant under arbitrary projective
refinement. This is the bridge from upstream measure-level Grain coherence
to downstream expectation functionals on total acts. -/
theorem bornExpectation_pullback_eq
    (v : H n) (D' D : Perspective n) (r : Refines D' D) (a : Act n) :
    bornExpectation v D' (pullbackAct r a) = bornExpectation v D a := by
  unfold bornExpectation pullbackAct
  simp only [Function.comp_apply]
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun c' hc' => parentOf_mem r hc')
    (fun c' => ‖projL c' v‖ ^ 2 * a (parentOf r c'))]
  apply Finset.sum_congr rfl
  intro c hc
  rw [← coarseCells_eq_fiber_parentOf r hc]
  calc
    (∑ c' ∈ coarseCells D' c, ‖projL c' v‖ ^ 2 * a (parentOf r c')) =
        ∑ c' ∈ coarseCells D' c, ‖projL c' v‖ ^ 2 * a c := by
      apply Finset.sum_congr rfl
      intro c' hc'
      obtain ⟨hc'mem, hc'le⟩ := (mem_coarseCells_iff D' c c').mp hc'
      rw [parentOf_eq_of_le r hc'mem hc hc'le]
    _ = (∑ c' ∈ coarseCells D' c, ‖projL c' v‖ ^ 2) * a c := by
      rw [Finset.sum_mul]
    _ = ‖projL c v‖ ^ 2 * a c := by
      have hgrain :=
        (axGrain_iff_coarseCells (QuantumFoundations.ProbabilityAPI.BornRule.E₀ v)).mp
          (QuantumFoundations.ProbabilityAPI.BornRule.E₀_isGrain v) D' D r c hc
      simp only [QuantumFoundations.ProbabilityAPI.BornRule.E₀] at hgrain
      rw [← hgrain]

/-- Strong nonvacuity: Born expectation inhabits the refinement-invariance
premise for every state vector. -/
theorem bornExpectation_refinementInvariant (v : H n) :
    RefinementInvariant (bornExpectation v) := by
  intro D' D r a
  exact bornExpectation_pullback_eq v D' D r a

end EverettianProbability.Refinement
