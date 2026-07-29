import EverettianProbability.Diachronic.RecordWeightEquivalence

/-!
**FR.** # Preparation cellule par cellule du theoreme d'orbite

Ce module decompose les etats suivant les cellules projectives, isole les
donnees de normes necessaires a une future construction bloc-diagonale et
formalise le sens necessaire de l'orbite isometrique commutante.

**EN.** # Cellwise preparation of the orbit theorem

This module decomposes states along projective cells, isolates the norm data
needed for a future block-diagonal construction, and formalizes the necessary
direction of a commuting isometric orbit.
-/
namespace EverettianProbability.Abstract
open QuantumFoundations.BornRule Gleason QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core EverettianProbability.PhysicalRefinement
open scoped BigOperators Classical InnerProductSpace
noncomputable section
variable {n : Nat}

def cellComponent (D : Perspective n) (c : (Projective.interface n).Cell D) (x : H n) : H n := projL c.val x
@[simp] theorem cellComponent_def (D : Perspective n) (c : (Projective.interface n).Cell D) (x : H n) : cellComponent D c x = projL c.val x := rfl
theorem cellComponent_mem (D : Perspective n) (c : (Projective.interface n).Cell D) (x : H n) : cellComponent D c x ∈ c.val := Submodule.starProjection_apply_mem _ _
theorem cellComponent_norm_sq (D : Perspective n) (c : (Projective.interface n).Cell D) (x : H n) : ‖cellComponent D c x‖ ^ 2 = bornRecord D x c := rfl

theorem cellComponents_inner_eq_zero (D : Perspective n) {c d : (Projective.interface n).Cell D} (hcd : c ≠ d) (x y : H n) : ⟪cellComponent D c x, cellComponent D d y⟫_ℂ = 0 := by
  apply (Submodule.isOrtho_iff_le.mpr (D.ortho d.val d.property c.val c.property (fun h => hcd (Subtype.ext h.symm))))
  · exact cellComponent_mem D d y
  · exact cellComponent_mem D c x
theorem cellComponents_pairwise_inner_eq_zero (D : Perspective n) (x : H n) : Set.Pairwise Set.univ (fun c d : (Projective.interface n).Cell D => ⟪cellComponent D c x, cellComponent D d x⟫_ℂ = 0) := by
  intro c _ d _ h; exact cellComponents_inner_eq_zero D h x x

private theorem sum_cellSubtype_eq_sum_cells
    (D : Perspective n)
    (x : H n) :
    (∑ c : (Projective.interface n).Cell D,
      projL c.val x) =
      ∑ c ∈ D.cells, projL c x := by
  classical
  change
    (∑ c : {c : Submodule ℂ (H n) // c ∈ D.cells},
      projL c.val x) =
      ∑ c ∈ D.cells, projL c x
  symm
  exact
    Finset.sum_subtype D.cells (fun c => Iff.rfl) (fun c => projL c x)

private theorem sum_projL_cells_eq
    (D : Perspective n)
    (x : H n) :
    (∑ c ∈ D.cells, projL c x) = x := by
  have ho : ∀ i ∈ D.cells, ∀ j ∈ D.cells, i ≠ j → i ⟂ j := by
    intro i hi j hj h; exact Submodule.isOrtho_iff_le.mpr (D.ortho i hi j hj h)
  have hs : projL (D.cells.sup id) = ∑ i ∈ D.cells, projL i := projL_sup_of_pairwise_isOrtho D.cells id ho
  rw [Finset.sup_id_eq_sSup, D.span] at hs
  have ht : projL (⊤ : Submodule ℂ (H n)) = LinearMap.id := by unfold projL; rw [Submodule.starProjection_top]; rfl
  rw [ht] at hs
  have ha := congrArg (fun f => f x) hs
  simpa using ha.symm

theorem sum_cellComponents_eq (D : Perspective n) (x : H n) : (∑ c : (Projective.interface n).Cell D, cellComponent D c x) = x := by
  rw [show (∑ c : (Projective.interface n).Cell D, cellComponent D c x) = ∑ c : (Projective.interface n).Cell D, projL c.val x by rfl]
  rw [sum_cellSubtype_eq_sum_cells]
  exact sum_projL_cells_eq D x

theorem sameBornRecord_iff_cellComponent_norm_sq_eq (D : Perspective n) (x y : H n) : SameBornRecord D x y ↔ ∀ c : (Projective.interface n).Cell D, ‖cellComponent D c x‖ ^ 2 = ‖cellComponent D c y‖ ^ 2 := Iff.rfl
theorem sameBornRecord_cellComponent_norm_eq {D : Perspective n} {x y : H n} (h : SameBornRecord D x y) (c : (Projective.interface n).Cell D) : ‖cellComponent D c x‖ = ‖cellComponent D c y‖ := by
  have q := h c; change ‖cellComponent D c x‖ ^ 2 = ‖cellComponent D c y‖ ^ 2 at q
  nlinarith [norm_nonneg (cellComponent D c x), norm_nonneg (cellComponent D c y)]
theorem sameBornRecord_of_cellComponent_norm_eq (D : Perspective n) (x y : H n) (h : ∀ c : (Projective.interface n).Cell D, ‖cellComponent D c x‖ = ‖cellComponent D c y‖) : SameBornRecord D x y := fun c => by change ‖cellComponent D c x‖ ^ 2 = ‖cellComponent D c y‖ ^ 2; rw [h c]
theorem sameBornRecord_iff_cellComponent_norm_eq (D : Perspective n) (x y : H n) : SameBornRecord D x y ↔ ∀ c : (Projective.interface n).Cell D, ‖cellComponent D c x‖ = ‖cellComponent D c y‖ := ⟨fun h c => sameBornRecord_cellComponent_norm_eq h c, sameBornRecord_of_cellComponent_norm_eq D x y⟩
theorem cellComponent_eq_zero_iff_bornRecord_eq_zero (D : Perspective n) (c : (Projective.interface n).Cell D) (x : H n) : cellComponent D c x = 0 ↔ bornRecord D x c = 0 := by
  constructor
  · intro h
    change projL c.val x = 0 at h
    simp [bornRecord, h]
  · intro h
    have q : ‖cellComponent D c x‖ ^ 2 = 0 := by simpa [bornRecord] using h
    have q' : ‖cellComponent D c x‖ = 0 := by nlinarith [norm_nonneg (cellComponent D c x)]
    exact norm_eq_zero.mp q'
theorem sameBornRecord_cellComponent_zero_iff {D : Perspective n} {x y : H n} (h : SameBornRecord D x y) (c : (Projective.interface n).Cell D) : cellComponent D c x = 0 ↔ cellComponent D c y = 0 := by
  rw [cellComponent_eq_zero_iff_bornRecord_eq_zero, cellComponent_eq_zero_iff_bornRecord_eq_zero]
  simpa [bornRecord] using congrArg (fun q => q = 0) (h c)

structure CellwiseEqualNormData (D : Perspective n) (x y : H n) : Prop where
 source_mem : ∀ c : (Projective.interface n).Cell D, cellComponent D c x ∈ c.val
 target_mem : ∀ c : (Projective.interface n).Cell D, cellComponent D c y ∈ c.val
 source_reconstruct : (∑ c : (Projective.interface n).Cell D, cellComponent D c x) = x
 target_reconstruct : (∑ c : (Projective.interface n).Cell D, cellComponent D c y) = y
 component_norm_eq : ∀ c : (Projective.interface n).Cell D, ‖cellComponent D c x‖ = ‖cellComponent D c y‖
theorem cellwiseEqualNormData_of_sameBornRecord {D : Perspective n} {x y : H n} (h : SameBornRecord D x y) : CellwiseEqualNormData D x y := ⟨fun c => cellComponent_mem D c x, fun c => cellComponent_mem D c y, sum_cellComponents_eq D x, sum_cellComponents_eq D y, fun c => sameBornRecord_cellComponent_norm_eq h c⟩

def ProjectorCommutingIsometricOrbit (D : Perspective n) (x y : H n) : Prop := ∃ evolution : H n →ₗ[ℂ] H n, (∀ z : H n, ‖evolution z‖ = ‖z‖) ∧ CommutesWithPerspectiveProjectors D evolution ∧ evolution x = y
theorem ProjectorCommutingIsometricOrbit.refl (D : Perspective n) (x : H n) : ProjectorCommutingIsometricOrbit D x x := ⟨LinearMap.id, fun _ => rfl, commutesWithPerspectiveProjectors_id D, rfl⟩
theorem ProjectorCommutingIsometricOrbit.trans {D : Perspective n} {x y z : H n} (a : ProjectorCommutingIsometricOrbit D x y) (b : ProjectorCommutingIsometricOrbit D y z) : ProjectorCommutingIsometricOrbit D x z := by
  rcases a with ⟨e, he, ce, ex⟩; rcases b with ⟨f, hf, cf, fy⟩
  refine ⟨f.comp e, fun w => by change ‖f (e w)‖ = ‖w‖; rw [hf, he], cf.comp ce, ?_⟩
  change f (e x) = z; rw [ex, fy]
theorem sameBornRecord_of_projectorCommutingIsometricOrbit {D : Perspective n} {x y : H n} (h : ProjectorCommutingIsometricOrbit D x y) : SameBornRecord D x y := by
  rcases h with ⟨e, hi, hc, hm⟩; intro c
  have q := bornWeight_preserved_of_commutesWithProjector e hi c.val (hc c) x
  rwa [hm] at q
theorem cellComponent_map_of_commutes_and_maps (D : Perspective n) (e : H n →ₗ[ℂ] H n) (hc : CommutesWithPerspectiveProjectors D e) {x y : H n} (hm : e x = y) (c : (Projective.interface n).Cell D) : e (cellComponent D c x) = cellComponent D c y := by
  unfold cellComponent; have q := hc c x; rw [hm] at q; exact q.symm
theorem maps_state_of_maps_all_cellComponents (D : Perspective n) (e : H n →ₗ[ℂ] H n) (x y : H n) (h : ∀ c : (Projective.interface n).Cell D, e (cellComponent D c x) = cellComponent D c y) : e x = y := by
  rw [← sum_cellComponents_eq D x, map_sum, ← sum_cellComponents_eq D y]
  exact Finset.sum_congr rfl (fun c _ => h c)
theorem maps_state_iff_maps_all_cellComponents (D : Perspective n) (e : H n →ₗ[ℂ] H n) (hc : CommutesWithPerspectiveProjectors D e) (x y : H n) : e x = y ↔ ∀ c : (Projective.interface n).Cell D, e (cellComponent D c x) = cellComponent D c y := ⟨fun h c => cellComponent_map_of_commutes_and_maps D e hc h c, maps_state_of_maps_all_cellComponents D e x y⟩

theorem recordNeutral_projectorCommutingIsometricOrbit : ProjectorCommutingIsometricOrbit coarsePerspective psiBefore psiAfter := ⟨coupleULin, coupleU_isometry, ProjectorCommutingProjectiveContinuation.coupleU_commutes_coarsePerspectiveProjectors, coupleU_psiBefore⟩
theorem recordNeutralCellwiseOrbitPreparation_integratedWitness : psiBefore ≠ psiAfter ∧ SameBornRecord coarsePerspective psiBefore psiAfter ∧ ProjectorCommutingIsometricOrbit coarsePerspective psiBefore psiAfter ∧ CellwiseEqualNormData coarsePerspective psiBefore psiAfter := ⟨ProjectorCommutingProjectiveContinuation.recordNeutral_psiBefore_ne_psiAfter, ProjectorCommutingProjectiveContinuation.recordNeutral_psiBefore_psiAfter_sameBornRecord, recordNeutral_projectorCommutingIsometricOrbit, cellwiseEqualNormData_of_sameBornRecord ProjectorCommutingProjectiveContinuation.recordNeutral_psiBefore_psiAfter_sameBornRecord⟩
end
end EverettianProbability.Abstract
