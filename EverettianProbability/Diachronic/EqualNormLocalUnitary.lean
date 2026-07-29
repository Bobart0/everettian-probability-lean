import EverettianProbability.Diachronic.CellwiseOrbitPreparation

/-!
**FR.** # Unitaire local entre vecteurs de même norme

Ce module résout le problème local requis par le théorème d'orbite
bloc-diagonale.

Dans tout espace hermitien complexe de dimension finie, deux vecteurs de
même norme sont reliés par une équivalence linéaire isométrique. Le cas
nul est traité par l'identité ; dans le cas non nul, les directions
unitaires des deux vecteurs sont étendues à des bases orthonormées et
l'équivalence envoyant une base sur l'autre fournit l'opérateur requis.

Le résultat est ensuite appliqué au sous-espace de chaque cellule d'une
perspective projective. Deux états ayant le même record bornien
fournissent des composantes cellulaires de mêmes normes ; chaque paire
de composantes est donc reliée par un unitaire interne à sa cellule.

Le module empaquette ces opérateurs en une famille
`CellwiseUnitaryData`. Il ne les assemble pas encore en un opérateur
bloc-diagonal global.

**EN.** # Local unitary between equal-norm vectors

This module solves the local problem required by the block-diagonal
orbit theorem.

In every finite-dimensional complex inner-product space, two vectors of
equal norm are related by a linear isometric equivalence. The zero case
is handled by the identity; in the nonzero case, the two unit directions
are extended to orthonormal bases and the equivalence mapping one basis
to the other supplies the required operator.

The result is then applied to each cell subspace of a projective
perspective. Two states with the same Born record have equal-norm cell
components, so each corresponding pair is related by a unitary internal
to that cell.

The module packages these operators as `CellwiseUnitaryData`. It does
not yet assemble them into a global block-diagonal operator.
-/

namespace EverettianProbability.Abstract

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core
open EverettianProbability.PhysicalRefinement
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : ℕ}

/-- A linear isometric equivalence mapping one specified vector to
another. -/
structure EqualNormUnitaryWitness
    (E : Type*)
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (x y : E) where
  unitary :
    E ≃ₗᵢ[ℂ] E
  map_source :
    unitary x = y

namespace EqualNormUnitaryWitness

/-- A unitary witness necessarily relates vectors of equal norm. -/
theorem norm_eq
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    {x y : E}
    (W : EqualNormUnitaryWitness E x y) :
    ‖x‖ = ‖y‖ := by
  rw [← W.map_source]
  exact (W.unitary.norm_map x).symm

def refl
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (x : E) :
    EqualNormUnitaryWitness E x x where
  unitary :=
    LinearIsometryEquiv.refl ℂ E
  map_source := by
    rfl

def symm
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    {x y : E}
    (W : EqualNormUnitaryWitness E x y) :
    EqualNormUnitaryWitness E y x where
  unitary :=
    W.unitary.symm
  map_source := by
    simpa only [W.map_source] using W.unitary.symm_apply_apply x

def trans
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    {x y z : E}
    (Wxy : EqualNormUnitaryWitness E x y)
    (Wyz : EqualNormUnitaryWitness E y z) :
    EqualNormUnitaryWitness E x z where
  unitary :=
    Wxy.unitary.trans Wyz.unitary
  map_source := by
    rw [LinearIsometryEquiv.trans_apply, Wxy.map_source, Wyz.map_source]

end EqualNormUnitaryWitness

private def normalizedDirection
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (z : E) : E :=
  (‖z‖⁻¹ : ℂ) • z

private theorem norm_normalizedDirection
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (z : E)
    (hz : z ≠ 0) :
    ‖normalizedDirection z‖ = 1 := by
  have hnorm : ‖z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hz
  simp [normalizedDirection, norm_smul, hnorm]

private theorem norm_smul_normalizedDirection
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (z : E)
    (hz : z ≠ 0) :
    (‖z‖ : ℂ) • normalizedDirection z = z := by
  have hnorm : ‖z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hz
  simp [normalizedDirection, hnorm]

private theorem exists_orthonormalBasis_with_zero
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (z : E)
    (hz : ‖z‖ = 1)
    (hfinrank : 0 < Module.finrank ℂ E) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E,
      b ⟨0, hfinrank⟩ = z := by
  let index : Fin (Module.finrank ℂ E) :=
    ⟨0, hfinrank⟩
  let v : Fin (Module.finrank ℂ E) → E :=
    fun i => if i = index then z else 0
  let s : Set (Fin (Module.finrank ℂ E)) := {index}
  have hv : Orthonormal ℂ (s.restrict v) := by
    constructor
    · rintro ⟨i, hi⟩
      have hi_zero : i = index := by
        simpa [s] using hi
      subst i
      simpa [v] using hz
    · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      have hi_zero : i = index := by
        simpa [s] using hi
      have hj_zero : j = index := by
        simpa [s] using hj
      exact
        (hij (Subtype.ext (hi_zero.trans hj_zero.symm))).elim
  obtain ⟨b, hb⟩ :=
    hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨b, ?_⟩
  simpa [v] using hb index (by simp [s])

/-- In a finite-dimensional complex inner-product space, equal-norm
vectors lie in the same unitary orbit. -/
theorem exists_equalNormUnitaryWitness
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (x y : E)
    (hNorm : ‖x‖ = ‖y‖) :
    Nonempty
      (EqualNormUnitaryWitness E x y) := by
  by_cases hx : x = 0
  · subst x
    have hy : y = 0 := by
      apply norm_eq_zero.mp
      simpa using hNorm.symm
    subst y
    exact ⟨EqualNormUnitaryWitness.refl 0⟩
  · have hy : y ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [← hNorm]
      exact norm_ne_zero_iff.mpr hx
    have hfinrank : 0 < Module.finrank ℂ E :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨x, hx⟩
    let index : Fin (Module.finrank ℂ E) :=
      ⟨0, hfinrank⟩
    let ux := normalizedDirection x
    let uy := normalizedDirection y
    have hux : ‖ux‖ = 1 :=
      norm_normalizedDirection x hx
    have huy : ‖uy‖ = 1 :=
      norm_normalizedDirection y hy
    obtain ⟨bx, hbx⟩ :=
      exists_orthonormalBasis_with_zero ux hux hfinrank
    obtain ⟨byBasis, hby⟩ :=
      exists_orthonormalBasis_with_zero uy huy hfinrank
    let U : E ≃ₗᵢ[ℂ] E :=
      bx.equiv byBasis (Equiv.refl (Fin (Module.finrank ℂ E)))
    have hU : U ux = uy := by
      rw [← hbx, ← hby]
      exact
        OrthonormalBasis.equiv_apply_basis
          bx byBasis (Equiv.refl (Fin (Module.finrank ℂ E))) index
    refine ⟨⟨U, ?_⟩⟩
    calc
      U x = U ((‖x‖ : ℂ) • ux) := by
        rw [norm_smul_normalizedDirection x hx]
      _ = (‖x‖ : ℂ) • U ux := by
        rw [map_smul]
      _ = (‖y‖ : ℂ) • uy := by
        rw [hU, hNorm]
      _ = y := by
        rw [norm_smul_normalizedDirection y hy]

/-- Equal-norm vectors admit a linear isometric equivalence taking the
first to the second. -/
theorem exists_linearIsometryEquiv_apply_eq_of_norm_eq
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (x y : E)
    (hNorm : ‖x‖ = ‖y‖) :
    ∃ U : E ≃ₗᵢ[ℂ] E,
      U x = y := by
  obtain ⟨W⟩ :=
    exists_equalNormUnitaryWitness x y hNorm
  exact
    ⟨W.unitary, W.map_source⟩

theorem nonempty_equalNormUnitaryWitness_iff
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (x y : E) :
    Nonempty
        (EqualNormUnitaryWitness E x y) ↔
      ‖x‖ = ‖y‖ := by
  constructor
  · rintro ⟨W⟩
    exact W.norm_eq
  · exact
      exists_equalNormUnitaryWitness x y

/-- Source component bundled as a vector of its own cell subspace. -/
def sourceCellVector
    (D : Perspective n)
    (c : (Projective.interface n).Cell D)
    (x : H n) :
    c.val :=
  ⟨cellComponent D c x,
    cellComponent_mem D c x⟩

/-- Target component bundled as a vector of its own cell subspace. -/
def targetCellVector
    (D : Perspective n)
    (c : (Projective.interface n).Cell D)
    (y : H n) :
    c.val :=
  ⟨cellComponent D c y,
    cellComponent_mem D c y⟩

@[simp]
theorem sourceCellVector_val
    (D : Perspective n)
    (c : (Projective.interface n).Cell D)
    (x : H n) :
    (sourceCellVector D c x : H n) =
      cellComponent D c x := by
  rfl

@[simp]
theorem targetCellVector_val
    (D : Perspective n)
    (c : (Projective.interface n).Cell D)
    (y : H n) :
    (targetCellVector D c y : H n) =
      cellComponent D c y := by
  rfl

/-- Equal Born records give equal norms to the corresponding bundled
cell vectors. -/
theorem sourceCellVector_norm_eq_targetCellVector
    {D : Perspective n}
    {x y : H n}
    (hRecord :
      SameBornRecord D x y)
    (c : (Projective.interface n).Cell D) :
    ‖sourceCellVector D c x‖ =
      ‖targetCellVector D c y‖ := by
  change
    ‖cellComponent D c x‖ =
      ‖cellComponent D c y‖
  exact
    sameBornRecord_cellComponent_norm_eq
      hRecord c

/-- A chosen unitary internal to one cell, mapping the source component
to the target component. -/
noncomputable def localCellUnitary
    {D : Perspective n}
    {x y : H n}
    (hRecord :
      SameBornRecord D x y)
    (c : (Projective.interface n).Cell D) :
    c.val ≃ₗᵢ[ℂ] c.val :=
  Classical.choose
    (exists_linearIsometryEquiv_apply_eq_of_norm_eq
      (sourceCellVector D c x)
      (targetCellVector D c y)
      (sourceCellVector_norm_eq_targetCellVector
        hRecord c))

@[simp]
theorem localCellUnitary_map_source
    {D : Perspective n}
    {x y : H n}
    (hRecord :
      SameBornRecord D x y)
    (c : (Projective.interface n).Cell D) :
    localCellUnitary hRecord c
        (sourceCellVector D c x) =
      targetCellVector D c y := by
  exact
    Classical.choose_spec
      (exists_linearIsometryEquiv_apply_eq_of_norm_eq
        (sourceCellVector D c x)
        (targetCellVector D c y)
        (sourceCellVector_norm_eq_targetCellVector
          hRecord c))

theorem localCellUnitary_norm_map
    {D : Perspective n}
    {x y : H n}
    (hRecord :
      SameBornRecord D x y)
    (c : (Projective.interface n).Cell D)
    (z : c.val) :
    ‖localCellUnitary hRecord c z‖ =
      ‖z‖ := by
  exact
    (localCellUnitary hRecord c).norm_map z

/-- A unitary internal to each cell, mapping every source component to
the corresponding target component. -/
structure CellwiseUnitaryData
    (D : Perspective n)
    (x y : H n) where
  localUnitary :
    ∀ c : (Projective.interface n).Cell D,
      c.val ≃ₗᵢ[ℂ] c.val
  maps_component :
    ∀ c : (Projective.interface n).Cell D,
      localUnitary c
          (sourceCellVector D c x) =
        targetCellVector D c y

/-- Equal Born record supplies a complete family of local cell
unitaries. -/
noncomputable def cellwiseUnitaryData_of_sameBornRecord
    {D : Perspective n}
    {x y : H n}
    (hRecord :
      SameBornRecord D x y) :
    CellwiseUnitaryData D x y where
  localUnitary :=
    localCellUnitary hRecord
  maps_component :=
    localCellUnitary_map_source hRecord

namespace CellwiseUnitaryData

theorem local_norm_map
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y)
    (c : (Projective.interface n).Cell D)
    (z : c.val) :
    ‖W.localUnitary c z‖ =
      ‖z‖ := by
  exact
    (W.localUnitary c).norm_map z

theorem maps_component_val
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y)
    (c : (Projective.interface n).Cell D) :
    ((W.localUnitary c
        (sourceCellVector D c x) : c.val) : H n) =
      cellComponent D c y := by
  rw [W.maps_component c]
  rfl

theorem maps_zero_source_to_zero_target
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y)
    (c : (Projective.interface n).Cell D)
    (hx :
      cellComponent D c x = 0) :
    cellComponent D c y = 0 := by
  have hSource :
      sourceCellVector D c x = 0 := by
    apply Subtype.ext
    exact hx
  have hMap :=
    W.maps_component c
  rw [hSource, map_zero] at hMap
  exact
    (congrArg Subtype.val hMap).symm

theorem maps_zero_target_to_zero_source
    {D : Perspective n}
    {x y : H n}
    (W : CellwiseUnitaryData D x y)
    (c : (Projective.interface n).Cell D)
    (hy :
      cellComponent D c y = 0) :
    cellComponent D c x = 0 := by
  have hTarget :
      targetCellVector D c y = 0 := by
    apply Subtype.ext
    exact hy
  have hSource :
      sourceCellVector D c x = 0 := by
    apply
      (W.localUnitary c).injective
    calc
      W.localUnitary c
          (sourceCellVector D c x) =
          targetCellVector D c y :=
        W.maps_component c
      _ = 0 := hTarget
      _ = W.localUnitary c 0 := by
        symm
        exact map_zero (W.localUnitary c)
  exact
    congrArg Subtype.val hSource

end CellwiseUnitaryData

/-- A complete family of local unitary maps forces equality of the Born
record. -/
theorem sameBornRecord_of_cellwiseUnitaryData
    {D : Perspective n}
    {x y : H n}
    (W :
      CellwiseUnitaryData D x y) :
    SameBornRecord D x y := by
  apply
    sameBornRecord_of_cellComponent_norm_eq
      D x y
  intro c
  change
    ‖sourceCellVector D c x‖ =
      ‖targetCellVector D c y‖
  rw [← W.maps_component c]
  exact
    ((W.localUnitary c).norm_map
      (sourceCellVector D c x)).symm

theorem nonempty_cellwiseUnitaryData_iff_sameBornRecord
    (D : Perspective n)
    (x y : H n) :
    Nonempty
        (CellwiseUnitaryData D x y) ↔
      SameBornRecord D x y := by
  constructor
  · rintro ⟨W⟩
    exact
      sameBornRecord_of_cellwiseUnitaryData W
  · intro hRecord
    exact
      ⟨cellwiseUnitaryData_of_sameBornRecord
        hRecord⟩

/-- Cellwise local unitaries for the concrete record-neutral
before/after states. -/
noncomputable def recordNeutralCellwiseUnitaryData :
    CellwiseUnitaryData
      coarsePerspective
      psiBefore
      psiAfter :=
  cellwiseUnitaryData_of_sameBornRecord
    ProjectorCommutingProjectiveContinuation.recordNeutral_psiBefore_psiAfter_sameBornRecord

theorem recordNeutralCellwiseUnitaryData_maps_label0 :
    recordNeutralCellwiseUnitaryData.localUnitary
        recordNeutralPresentLabel0Cell
        (sourceCellVector
          coarsePerspective
          recordNeutralPresentLabel0Cell
          psiBefore) =
      targetCellVector
        coarsePerspective
        recordNeutralPresentLabel0Cell
        psiAfter := by
  exact
    (recordNeutralCellwiseUnitaryData).maps_component
      recordNeutralPresentLabel0Cell

theorem recordNeutralCellwiseUnitaryData_maps_complement :
    recordNeutralCellwiseUnitaryData.localUnitary
        recordNeutralPresentComplementCell
        (sourceCellVector
          coarsePerspective
          recordNeutralPresentComplementCell
          psiBefore) =
      targetCellVector
        coarsePerspective
        recordNeutralPresentComplementCell
        psiAfter := by
  exact
    (recordNeutralCellwiseUnitaryData).maps_component
      recordNeutralPresentComplementCell

/-- Integrated local-unitary witness.

The distinct record-neutral states have the same Born record and admit
one internal unitary per coarse cell, each mapping the corresponding
source component to the target component. -/
theorem recordNeutralEqualNormLocalUnitary_integratedWitness :
    psiBefore ≠ psiAfter
      ∧
    SameBornRecord
        coarsePerspective
        psiBefore
        psiAfter
      ∧
    Nonempty
      (CellwiseUnitaryData
        coarsePerspective
        psiBefore
        psiAfter)
      ∧
    (∀ c :
        (Projective.interface 3).Cell
          coarsePerspective,
      recordNeutralCellwiseUnitaryData.localUnitary c
          (sourceCellVector
            coarsePerspective c psiBefore) =
        targetCellVector
          coarsePerspective c psiAfter) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      ProjectorCommutingProjectiveContinuation.recordNeutral_psiBefore_ne_psiAfter
  · exact
      ProjectorCommutingProjectiveContinuation.recordNeutral_psiBefore_psiAfter_sameBornRecord
  · exact
      ⟨recordNeutralCellwiseUnitaryData⟩
  · exact
      (recordNeutralCellwiseUnitaryData).maps_component

end
end EverettianProbability.Abstract
