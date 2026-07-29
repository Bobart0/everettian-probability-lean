import EverettianProbability.Diachronic.UnitaryRecordOrbit

/-!
**FR.** # Realisation d'un partage fin des poids de Born

Ce module construit un etat cible realisant un partage positif arbitraire
des poids de Born a l'interieur des cellules d'un record present. Des
vecteurs unitaires choisis dans les cellules futures sont ponderes par les
racines carrees des poids prescrits, puis additionnes.

L'orthogonalite rend chaque poids fin exact et Grain reconstruit le record
present. L'unitaire bloc-diagonal obtenu est mathematique : ce module ne
pretend pas encore que tout plan soit une continuation semantiquement ou
physiquement pertinente.

**EN.** # Realization of a fine Born-weight splitting

This module constructs a target state realizing an arbitrary positive
splitting of Born weights inside the cells of a present record. Unit
vectors selected in future cells are weighted by square roots of the
prescribed weights and then summed.

Orthogonality makes every fine weight exact and Grain reconstructs the
present record. The resulting block-diagonal unitary is mathematical: this
module does not yet claim that every plan is semantically or physically
relevant continuation.
-/

namespace EverettianProbability.Abstract

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core
open EverettianProbability.PhysicalRefinement
open scoped BigOperators Classical InnerProductSpace ComplexConjugate

noncomputable section

variable {n : ℕ}

/-- A positive assignment of future Born weights compatible fibrewise with
the present Born record of `x`. -/
structure FineBornWeightPlan
    {future present : Perspective n}
    (r : Refines future present)
    (x : H n) where
  weight : (Projective.interface n).Cell future → ℝ
  nonneg : ∀ i : (Projective.interface n).Cell future, 0 ≤ weight i
  fibre_sum : ∀ c : (Projective.interface n).Cell present,
    (∑ i : (Projective.interface n).Cell future,
      if (Projective.interface n).parentCell r i = c then weight i else 0) =
      bornRecord present x c

namespace FineBornWeightPlan

/-- Every cell of a projective perspective is a nonzero subspace. -/
theorem perspectiveCell_ne_bot
    (D : Perspective n)
    (i : (Projective.interface n).Cell D) :
    i.val ≠ ⊥ :=
  D.nz i.val i.property

/-- Every projective cell contains a unit vector. -/
theorem exists_unitVector_in_perspectiveCell
    (D : Perspective n)
    (i : (Projective.interface n).Cell D) :
    ∃ v : i.val, ‖v‖ = 1 := by
  obtain ⟨w, hwmem, hwne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (perspectiveCell_ne_bot D i)
  refine ⟨⟨(‖w‖⁻¹ : ℂ) • w, i.val.smul_mem _ hwmem⟩, ?_⟩
  change ‖((‖w‖⁻¹ : ℂ) • w : H n)‖ = 1
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg w), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hwne)]

/-- A chosen unit vector internal to each future cell. -/
noncomputable def chosenFutureUnitVector
    (D : Perspective n)
    (i : (Projective.interface n).Cell D) :
    i.val :=
  Classical.choose (exists_unitVector_in_perspectiveCell D i)

@[simp]
theorem chosenFutureUnitVector_norm
    (D : Perspective n)
    (i : (Projective.interface n).Cell D) :
    ‖chosenFutureUnitVector D i‖ = 1 :=
  Classical.choose_spec (exists_unitVector_in_perspectiveCell D i)

theorem chosenFutureUnitVector_mem
    (D : Perspective n)
    (i : (Projective.interface n).Cell D) :
    (chosenFutureUnitVector D i : H n) ∈ i.val :=
  (chosenFutureUnitVector D i).property

/-- Target component carrying the prescribed Born weight of one future cell. -/
noncomputable def fineTargetComponent
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineBornWeightPlan r x)
    (i : (Projective.interface n).Cell future) : H n :=
  ((Real.sqrt (plan.weight i) : ℝ) : ℂ) •
    (chosenFutureUnitVector future i : H n)

theorem fineTargetComponent_mem
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineBornWeightPlan r x)
    (i : (Projective.interface n).Cell future) :
    fineTargetComponent plan i ∈ i.val := by
  exact i.val.smul_mem _ (chosenFutureUnitVector_mem future i)

/-- The squared norm of one target component is exactly its prescribed
weight. -/
theorem fineTargetComponent_norm_sq
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineBornWeightPlan r x)
    (i : (Projective.interface n).Cell future) :
    ‖fineTargetComponent plan i‖ ^ 2 = plan.weight i := by
  unfold fineTargetComponent
  have hunit : ‖(chosenFutureUnitVector future i : H n)‖ = 1 := by
    exact chosenFutureUnitVector_norm future i
  rw [norm_smul, hunit, mul_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (plan.nonneg i)]

/-- Target components belonging to distinct future cells are orthogonal. -/
theorem fineTargetComponents_inner_eq_zero
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineBornWeightPlan r x)
    {i j : (Projective.interface n).Cell future}
    (hij : i ≠ j) :
    ⟪fineTargetComponent plan i, fineTargetComponent plan j⟫_ℂ = 0 := by
  have hperp : fineTargetComponent plan j ∈ i.valᗮ :=
    (Submodule.isOrtho_iff_le.mp
      (perspectiveCells_isOrtho future hij).symm)
      (fineTargetComponent_mem plan j)
  exact
    (Submodule.mem_orthogonal i.val (fineTargetComponent plan j)).mp hperp
      (fineTargetComponent plan i)
      (fineTargetComponent_mem plan i)

/-- Canonical target state realizing a compatible fine Born-weight plan. -/
noncomputable def fineWeightTargetState
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineBornWeightPlan r x) : H n :=
  ∑ i : (Projective.interface n).Cell future, fineTargetComponent plan i

theorem fineWeightTargetState_def
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineBornWeightPlan r x) :
    fineWeightTargetState plan =
      ∑ i : (Projective.interface n).Cell future, fineTargetComponent plan i :=
  rfl

/-- The projection of the target state onto a future cell selects exactly
that cell's target component. -/
theorem projL_fineWeightTargetState
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineBornWeightPlan r x)
    (i : (Projective.interface n).Cell future) :
    projL i.val (fineWeightTargetState plan) = fineTargetComponent plan i := by
  rw [fineWeightTargetState_def, map_sum, Finset.sum_eq_single i]
  · exact
      Submodule.starProjection_eq_self_iff.mpr
        (fineTargetComponent_mem plan i)
  · intro j _ hji
    change i.val.starProjection (fineTargetComponent plan j) = 0
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact
      (Submodule.isOrtho_iff_le.mp
        (perspectiveCells_isOrtho future hji))
        (fineTargetComponent_mem plan j)
  · exact fun hnot => (hnot (Finset.mem_univ i)).elim

/-- The target state realizes every prescribed future Born weight exactly. -/
theorem fineWeightTargetState_bornWeight
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineBornWeightPlan r x)
    (i : (Projective.interface n).Cell future) :
    bornRecord future (fineWeightTargetState plan) i = plan.weight i := by
  unfold bornRecord
  rw [projL_fineWeightTargetState, fineTargetComponent_norm_sq]

/-- The target state's fine Born weights sum fibrewise to the initial present
Born weights. -/
theorem fineWeightTargetState_fibre_sum
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineBornWeightPlan r x)
    (c : (Projective.interface n).Cell present) :
    (∑ i : (Projective.interface n).Cell future,
      if (Projective.interface n).parentCell r i = c then
        bornRecord future (fineWeightTargetState plan) i else 0) =
      bornRecord present x c := by
  calc
    (∑ i : (Projective.interface n).Cell future,
      if (Projective.interface n).parentCell r i = c then
        bornRecord future (fineWeightTargetState plan) i else 0) =
      ∑ i : (Projective.interface n).Cell future,
        if (Projective.interface n).parentCell r i = c then plan.weight i else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hparent : (Projective.interface n).parentCell r i = c
        · rw [if_pos hparent, if_pos hparent,
            fineWeightTargetState_bornWeight]
        · have hsub :
              ¬ (⟨parentOf r i.val, parentOf_mem r i.property⟩ :
                  (Projective.interface n).Cell present) = c := by
              simpa [Projective.interface_parentCell_apply] using hparent
          rw [Projective.interface_parentCell_apply]
          simp only [if_neg hsub]
    _ = bornRecord present x c := plan.fibre_sum c

private theorem bornRecord_eq_fibre_sum
    {future present : Perspective n}
    (r : Refines future present)
    (z : H n)
    (c : (Projective.interface n).Cell present) :
    bornRecord present z c =
      ∑ i : (Projective.interface n).Cell future,
        if (Projective.interface n).parentCell r i = c then
          bornRecord future z i else 0 := by
  have h := Projective.grain_of_axGrain
    (QuantumFoundations.ProbabilityAPI.BornRule.E₀ z)
    (QuantumFoundations.ProbabilityAPI.BornRule.E₀_isGrain z) r c
  simpa only [Projective.interface_weight_apply,
    QuantumFoundations.ProbabilityAPI.BornRule.E₀, bornRecord] using h

/-- The constructed target state has exactly the same present Born record as
the initial state. -/
theorem fineWeightTargetState_sameBornRecord
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineBornWeightPlan r x) :
    SameBornRecord present x (fineWeightTargetState plan) := by
  intro c
  change bornRecord present x c = bornRecord present (fineWeightTargetState plan) c
  rw [bornRecord_eq_fibre_sum r (fineWeightTargetState plan) c]
  exact (fineWeightTargetState_fibre_sum plan c).symm

/-- The target state has the same norm as the initial state. -/
theorem fineWeightTargetState_norm_eq
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineBornWeightPlan r x) :
    ‖fineWeightTargetState plan‖ = ‖x‖ := by
  obtain ⟨U, _, hMap⟩ :=
    projectorCommutingUnitaryOrbit_of_sameBornRecord
      (fineWeightTargetState_sameBornRecord plan)
  rw [← hMap]
  exact U.norm_map x

/-- A target generated from a normalized initial state is normalized. -/
theorem fineWeightTargetState_normalized
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineBornWeightPlan r x)
    (hx : ‖x‖ = 1) :
    ‖fineWeightTargetState plan‖ = 1 := by
  rw [fineWeightTargetState_norm_eq plan, hx]

/-- Every compatible fine Born-weight plan is realized by a global unitary
commuting with all present record projectors. -/
theorem exists_projectorCommutingUnitary_realizing_fineBornWeightPlan
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineBornWeightPlan r x) :
    ∃ U : H n ≃ₗᵢ[ℂ] H n,
      CommutesWithPerspectiveProjectors present U.toLinearEquiv.toLinearMap ∧
      U x = fineWeightTargetState plan ∧
      ∀ i : (Projective.interface n).Cell future,
        bornRecord future (U x) i = plan.weight i := by
  obtain ⟨U, hCommutes, hMap⟩ :=
    (sameBornRecord_iff_exists_projectorCommutingUnitary
      present x (fineWeightTargetState plan)).1
      (fineWeightTargetState_sameBornRecord plan)
  refine ⟨U, hCommutes, hMap, ?_⟩
  intro i
  rw [hMap]
  exact fineWeightTargetState_bornWeight plan i

/-- Explicit state-and-unitary realization form. -/
theorem exists_state_and_unitary_realizing_fineBornWeightPlan
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    (plan : FineBornWeightPlan r x) :
    ∃ y : H n, SameBornRecord present x y ∧
      (∀ i : (Projective.interface n).Cell future,
        bornRecord future y i = plan.weight i) ∧
      ∃ U : H n ≃ₗᵢ[ℂ] H n,
        CommutesWithPerspectiveProjectors present U.toLinearEquiv.toLinearMap ∧ U x = y := by
  refine ⟨fineWeightTargetState plan, fineWeightTargetState_sameBornRecord plan,
    fineWeightTargetState_bornWeight plan, ?_⟩
  obtain ⟨U, hCommutes, hMap, _⟩ :=
    exists_projectorCommutingUnitary_realizing_fineBornWeightPlan plan
  exact ⟨U, hCommutes, hMap⟩

/-- Fine-weight plan extracted from an already existing target state with the
same present Born record. -/
noncomputable def ofTargetState
    {future present : Perspective n}
    (r : Refines future present)
    (x y : H n)
    (hRecord : SameBornRecord present x y) :
    FineBornWeightPlan r x where
  weight := bornRecord future y
  nonneg := by
    intro i
    exact sq_nonneg _
  fibre_sum := by
    intro c
    rw [← bornRecord_eq_fibre_sum r y c]
    exact (hRecord c).symm

@[simp]
theorem ofTargetState_weight
    {future present : Perspective n}
    (r : Refines future present)
    (x y : H n)
    (hRecord : SameBornRecord present x y)
    (i : (Projective.interface n).Cell future) :
    (ofTargetState r x y hRecord).weight i = bornRecord future y i :=
  rfl

/-- Fine Born-weight plan extracted from the concrete record-neutral target. -/
noncomputable def recordNeutralFineBornWeightPlan :
    FineBornWeightPlan recordNeutral_refines psiBefore :=
  ofTargetState recordNeutral_refines psiBefore psiAfter
    ProjectorCommutingProjectiveContinuation.recordNeutral_psiBefore_psiAfter_sameBornRecord

theorem recordNeutralFineBornWeightPlan_label0 :
    recordNeutralFineBornWeightPlan.weight recordNeutralFutureLabel0Cell = 9 / 25 := by
  change ‖projL label0Line psiAfter‖ ^ 2 = 9 / 25
  exact weight_label0_after

theorem recordNeutralFineBornWeightPlan_anc0 :
    recordNeutralFineBornWeightPlan.weight recordNeutralFutureAnc0Cell = 144 / 625 := by
  change ‖projL anc0Line psiAfter‖ ^ 2 = 144 / 625
  exact weight_anc0_after

theorem recordNeutralFineBornWeightPlan_anc1 :
    recordNeutralFineBornWeightPlan.weight recordNeutralFutureAnc1Cell = 256 / 625 := by
  change ‖projL anc1Line psiAfter‖ ^ 2 = 256 / 625
  exact weight_anc1_after

theorem recordNeutralFineWeightTarget_label0 :
    bornRecord finePerspective (fineWeightTargetState recordNeutralFineBornWeightPlan)
      recordNeutralFutureLabel0Cell = 9 / 25 := by
  rw [fineWeightTargetState_bornWeight, recordNeutralFineBornWeightPlan_label0]

theorem recordNeutralFineWeightTarget_anc0 :
    bornRecord finePerspective (fineWeightTargetState recordNeutralFineBornWeightPlan)
      recordNeutralFutureAnc0Cell = 144 / 625 := by
  rw [fineWeightTargetState_bornWeight, recordNeutralFineBornWeightPlan_anc0]

theorem recordNeutralFineWeightTarget_anc1 :
    bornRecord finePerspective (fineWeightTargetState recordNeutralFineBornWeightPlan)
      recordNeutralFutureAnc1Cell = 256 / 625 := by
  rw [fineWeightTargetState_bornWeight, recordNeutralFineBornWeightPlan_anc1]

theorem recordNeutralFineWeightTarget_normalized :
    ‖fineWeightTargetState recordNeutralFineBornWeightPlan‖ = 1 := by
  exact fineWeightTargetState_normalized recordNeutralFineBornWeightPlan psiBefore_norm

/-- A projector-commuting unitary realizes the three concrete target weights. -/
theorem exists_recordNeutralFineWeightRealizingUnitary :
    ∃ U : H 3 ≃ₗᵢ[ℂ] H 3,
      CommutesWithPerspectiveProjectors coarsePerspective U.toLinearEquiv.toLinearMap ∧
      U psiBefore = fineWeightTargetState recordNeutralFineBornWeightPlan ∧
      bornRecord finePerspective (U psiBefore) recordNeutralFutureLabel0Cell = 9 / 25 ∧
      bornRecord finePerspective (U psiBefore) recordNeutralFutureAnc0Cell = 144 / 625 ∧
      bornRecord finePerspective (U psiBefore) recordNeutralFutureAnc1Cell = 256 / 625 := by
  obtain ⟨U, hCommutes, hMap, hWeights⟩ :=
    exists_projectorCommutingUnitary_realizing_fineBornWeightPlan
      recordNeutralFineBornWeightPlan
  refine ⟨U, hCommutes, hMap, ?_, ?_, ?_⟩
  · calc
      bornRecord finePerspective (U psiBefore) recordNeutralFutureLabel0Cell =
          recordNeutralFineBornWeightPlan.weight recordNeutralFutureLabel0Cell :=
        hWeights recordNeutralFutureLabel0Cell
      _ = 9 / 25 := recordNeutralFineBornWeightPlan_label0
  · calc
      bornRecord finePerspective (U psiBefore) recordNeutralFutureAnc0Cell =
          recordNeutralFineBornWeightPlan.weight recordNeutralFutureAnc0Cell :=
        hWeights recordNeutralFutureAnc0Cell
      _ = 144 / 625 := recordNeutralFineBornWeightPlan_anc0
  · calc
      bornRecord finePerspective (U psiBefore) recordNeutralFutureAnc1Cell =
          recordNeutralFineBornWeightPlan.weight recordNeutralFutureAnc1Cell :=
        hWeights recordNeutralFutureAnc1Cell
      _ = 256 / 625 := recordNeutralFineBornWeightPlan_anc1

/-- Integrated exact fine-weight realization witness. -/
theorem recordNeutralFineBornWeightRealization_integratedWitness :
    SameBornRecord coarsePerspective psiBefore
        (fineWeightTargetState recordNeutralFineBornWeightPlan) ∧
    ‖fineWeightTargetState recordNeutralFineBornWeightPlan‖ = 1 ∧
    bornRecord finePerspective (fineWeightTargetState recordNeutralFineBornWeightPlan)
        recordNeutralFutureLabel0Cell = 9 / 25 ∧
    bornRecord finePerspective (fineWeightTargetState recordNeutralFineBornWeightPlan)
        recordNeutralFutureAnc0Cell = 144 / 625 ∧
    bornRecord finePerspective (fineWeightTargetState recordNeutralFineBornWeightPlan)
        recordNeutralFutureAnc1Cell = 256 / 625 ∧
    ∃ U : H 3 ≃ₗᵢ[ℂ] H 3,
      CommutesWithPerspectiveProjectors coarsePerspective U.toLinearEquiv.toLinearMap ∧
      U psiBefore = fineWeightTargetState recordNeutralFineBornWeightPlan := by
  refine ⟨fineWeightTargetState_sameBornRecord recordNeutralFineBornWeightPlan,
    recordNeutralFineWeightTarget_normalized,
    recordNeutralFineWeightTarget_label0,
    recordNeutralFineWeightTarget_anc0,
    recordNeutralFineWeightTarget_anc1, ?_⟩
  obtain ⟨U, hCommutes, hMap, _⟩ := exists_recordNeutralFineWeightRealizingUnitary
  exact ⟨U, hCommutes, hMap⟩

end FineBornWeightPlan

end
end EverettianProbability.Abstract
