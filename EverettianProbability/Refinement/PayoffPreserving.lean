import EverettianProbability.Refinement.PullbackAct
import EverettianProbability.Preference.ExpectationFunctional

/-!
**FR.** # Équivalence locale des conséquences

Deux descriptions sont équivalentes à un raffinement donné lorsqu'elles
attribuent le même paiement à chaque cellule fine. L'invariance correspondante
est la prémisse normative centrale de l'article II ; elle n'est dérivée
d'aucune propriété dynamique.

**EN.** # Local payoff equivalence

Two descriptions are equivalent at a given refinement when they assign the
same payoff to every fine cell. The corresponding invariance is the central
normative premise of paper II; it is not derived from any dynamical property.
-/

namespace EverettianProbability.Refinement

open QuantumFoundations.BornRule Gleason EverettianProbability.Core
open EverettianProbability.Preference
open scoped Classical

variable {n : ℕ}

/-- **FR.** Deux descriptions attribuent les mêmes conséquences à chaque
branche fine. Prémisse normative, non théorème dynamique.

**EN.** Two descriptions assign the same consequences to every fine branch.
This is a normative premise, not a dynamical theorem. -/
def PayoffEquivalentAt {D' D : Perspective n} (r : Refines D' D)
    (a' a : Act n) : Prop :=
  Act.AgreeOn D' a' (pullbackAct r a)

/-- A family of expectation functionals is invariant under refinement when
evaluating a coarse act or its pullback to any finer perspective gives the
same value. This is a normative premise, not a dynamical theorem. -/
def RefinementInvariant
    (V : Perspective n → Act n → ℝ) : Prop :=
  ∀ {D' D : Perspective n} (r : Refines D' D) (a : Act n),
    V D' (pullbackAct r a) = V D a

/-- **FR.** `PREMISE` normative : invariance sous toute redescription
localement équivalente.

**EN.** Normative `PREMISE`: invariance under every locally equivalent
redescription. -/
def RefinementInvariantLocal
    (V : Perspective n → Act n → ℝ) : Prop :=
  ∀ {D' D : Perspective n} (r : Refines D' D) (a' a : Act n),
    PayoffEquivalentAt r a' a → V D' a' = V D a

/-- **FR.** Pour une famille rationnelle, la forme locale est équivalente à
l'invariance évaluée sur le tiré-en-arrière canonique.

**EN.** For a rational family, the local form is equivalent to invariance
evaluated on the canonical pullback. -/
theorem refinementInvariantLocal_iff_pullback (F : RationalExpectationFamily n) :
    RefinementInvariantLocal F.V ↔ RefinementInvariant F.V := by
  constructor
  · intro h D' D r a
    exact h r (pullbackAct r a) a (Act.agreeOn_refl D' (pullbackAct r a))
  · intro h D' D r a' a ha
    calc
      F.V D' a' = F.V D' (pullbackAct r a) :=
        V_congr_of_agreeOn F D' ha
      _ = F.V D a := h r a

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

/-- **FR.** Non-vacuité de la prémisse locale : l'espérance bornienne la
satisfait pour tout vecteur d'état.

**EN.** Nonvacuity of the local premise: Born expectation satisfies it for
every state vector. -/
theorem bornExpectation_refinementInvariantLocal (v : H n) :
    RefinementInvariantLocal (bornExpectation v) := by
  intro D' D r a' a ha
  calc
    bornExpectation v D' a' =
        bornExpectation v D' (pullbackAct r a) := by
      unfold bornExpectation
      apply Finset.sum_congr rfl
      intro c hc
      rw [ha c hc]
    _ = bornExpectation v D a := bornExpectation_pullback_eq v D' D r a

end EverettianProbability.Refinement
