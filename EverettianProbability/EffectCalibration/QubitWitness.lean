import EverettianProbability.EffectCalibration.EffectBornExpectation

/-!
**FR.** # Témoin concret : spin-1/2

Le témoin obligatoire de la route qubit : un état de spin-1/2 à amplitudes
inégales (`3/5`, `4/5`, comme partout ailleurs dans les deux dépôts), une
perspective d'effets explicite à deux issues (les projecteurs orthogonaux
« spin-up » et « spin-down » selon l'axe choisi), et le poids canonique
calculé — exactement `9/25`, la valeur de Born attendue. C'est le fait que
`n ≥ 3` interdisait de citer : un lecteur qui demande « et le qubit ? »
reçoit maintenant un exemple chiffré, pas seulement une clause de portée.

`spinPerspective` est construit directement à partir de `projectionEffect`
et d'un fait hilbertien générique (`Gleason.projL_sup_of_isOrtho` +
`Submodule.sup_orthogonal_of_hasOrthogonalProjection`), et non à partir de
`binaryPerspective`/`complementEffect` amont : `ProbabilityAPI` ne
réexporte actuellement ni l'un ni l'autre. Briques nommées, non reprouvées.

**EN.** # Concrete witness: spin-1/2

The qubit route's mandatory witness: a spin-1/2 state with unequal
amplitudes (`3/5`, `4/5`, as everywhere else in both repositories), an
explicit two-outcome effect perspective (the orthogonal "spin-up" and
"spin-down" projectors along the chosen axis), and the canonical weight
computed — exactly `9/25`, the expected Born value. This is exactly what
`n ≥ 3` used to forbid citing: a reader who asks "what about the qubit?"
now gets a numeric example, not only a scope clause.

`spinPerspective` is built directly from `projectionEffect` and a generic
Hilbert-space fact (`Gleason.projL_sup_of_isOrtho` +
`Submodule.sup_orthogonal_of_hasOrthogonalProjection`), not from upstream's
`binaryPerspective`/`complementEffect`: `ProbabilityAPI` currently
re-exports neither. Named bricks, not reproved.
-/

namespace EverettianProbability.Abstract

open scoped BigOperators Classical InnerProductSpace
open QuantumFoundations.ProbabilityAPI
open QuantumFoundations.Uhlhorn (projL_singleton_unit)

/-- Concrete spin-1/2 state, unequal amplitudes `3/5`, `4/5` (reusing the
same rational profile as `BornCalibration.witnessState` and
`PhysicalRefinement.psiBefore`). -/
noncomputable def spinState : H 2 :=
  EuclideanSpace.single (0 : Fin 2) (3 / 5 : ℂ) + EuclideanSpace.single (1 : Fin 2) (4 / 5 : ℂ)

private theorem spinState_zero : spinState 0 = 3 / 5 := by
  show (EuclideanSpace.single (0 : Fin 2) (3 / 5 : ℂ) +
    EuclideanSpace.single (1 : Fin 2) (4 / 5 : ℂ)) 0 = 3 / 5
  simp

private theorem spinState_one : spinState 1 = 4 / 5 := by
  show (EuclideanSpace.single (0 : Fin 2) (3 / 5 : ℂ) +
    EuclideanSpace.single (1 : Fin 2) (4 / 5 : ℂ)) 1 = 4 / 5
  simp

theorem spinState_norm : ‖spinState‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, spinState_zero, spinState_one]
  norm_num

private theorem spinBasis0_ne_zero : (EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : H 2) ≠ 0 := by
  intro h
  have hnorm : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : H 2)‖ = 1 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]; simp
  rw [h, norm_zero] at hnorm
  norm_num at hnorm

private theorem spinBasis0_norm : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : H 2)‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]; simp

private theorem spinState_inner :
    (inner ℂ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) spinState : ℂ) = 3 / 5 := by
  rw [EuclideanSpace.inner_single_left, spinState_zero]
  simp

/-- The line spanned by the computational-basis state `|0⟩`: the "spin-up"
outcome along the chosen axis. -/
noncomputable def spinLine : Submodule ℂ (H 2) :=
  ℂ ∙ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))

private theorem spinLine_finrank : Module.finrank ℂ spinLine = 1 :=
  finrank_span_singleton spinBasis0_ne_zero

theorem spinLine_ne_bot : spinLine ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  exact ⟨_, Submodule.mem_span_singleton_self _, spinBasis0_ne_zero⟩

theorem spinLine_ne_top : spinLine ≠ ⊤ := by
  intro h
  have h1 := spinLine_finrank
  rw [h, finrank_top] at h1
  simp at h1

private theorem spinLine_projL :
    Gleason.projL spinLine spinState = (3 / 5 : ℂ) • (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) := by
  unfold spinLine
  rw [projL_singleton_unit _ _ spinBasis0_norm, spinState_inner]

/-- `‖projL spinLine spinState‖² = 9/25` — the Born value the effect-side
theorem must reproduce. -/
theorem spinLine_weight : ‖Gleason.projL spinLine spinState‖ ^ 2 = 9 / 25 := by
  rw [spinLine_projL, norm_smul, spinBasis0_norm]
  norm_num

/-- The explicit two-outcome effect perspective on the qubit: the
projection onto `spinLine` (spin-up) and onto its orthogonal complement
(spin-down). -/
noncomputable def spinPerspective : EffectPerspectives.EffectPerspective 2 where
  outcomes := 2
  effects := ![EffectPerspectives.projectionEffect spinLine,
    EffectPerspectives.projectionEffect spinLineᗮ]
  sum_eq_one := by
    rw [Fin.sum_univ_two]
    show (Gleason.projL spinLine : H 2 →ₗ[ℂ] H 2) + (Gleason.projL spinLineᗮ : H 2 →ₗ[ℂ] H 2) = 1
    have hortho : spinLine ⟂ spinLineᗮ := Submodule.isOrtho_orthogonal_right spinLine
    have hsup : spinLine ⊔ spinLineᗮ = ⊤ := Submodule.sup_orthogonal_of_hasOrthogonalProjection
    have h := Gleason.projL_sup_of_isOrtho hortho
    rw [hsup] at h
    rw [← h]
    unfold Gleason.projL
    rw [Submodule.starProjection_top]
    rfl

theorem spinPerspective_effect_zero :
    (spinPerspective.effects (0 : Fin 2) : H 2 →ₗ[ℂ] H 2) = Gleason.projL spinLine := rfl

/-- The pure-state estimation rule at `spinState` — already Grain-coherent
by upstream construction (`Effects.pureState_refinementInvariant`). -/
noncomputable def E0 : EffectPerspectives.EstimationRule 2 :=
  EffectPerspectives.pureStateEstimationRule spinState spinState_norm

/-- The rational expectation family induced by `E0` — the concrete
inhabitant instantiating both `RationalExpectationFamily (Effects.interface
2)` and, below, `RefinementInvariantLocal`. -/
noncomputable def F0 : RationalExpectationFamily (Effects.interface 2) :=
  familyOfEstimationRule E0

/-- **FR.** Témoin de non-vacuité : `F0` satisfait bien l'invariance
locale sous raffinement.

**EN.** Nonvacuity witness: `F0` does satisfy local invariance under
refinement. -/
theorem F0_refinementInvariantLocal : RefinementInvariantLocal F0.V :=
  (refinementInvariantLocal_iff_pullback F0).mpr
    (Effects.pureState_refinementInvariant spinState spinState_norm)

/-- **FR.** Témoin de non-vacuité : la nullité de support relative à
`spinState`, pour la règle empaquetée à partir de `F0`.

**EN.** Nonvacuity witness: null support relative to `spinState`, for the
rule packaged from `F0`. -/
theorem F0_contextualNullSupport :
    EffectPerspectives.ContextualNullSupport
      (canonicalEstimationRule F0 F0_refinementInvariantLocal) spinState := by
  intro D i hzero
  show canonicalWeight F0 D i = 0
  rw [show F0 = familyOfEstimationRule E0 from rfl, canonicalWeight_familyOfEstimationRule]
  exact EffectPerspectives.pureStateEstimationRule_nullSupport spinState spinState_norm D i hzero

/-- **The concrete witness.** The canonical weight of the spin-up outcome,
under a genuine `n = 2` rational expectation family satisfying local
refinement invariance, equals the Born value `9/25` — computed from the
same `(3/5, 4/5)` amplitude profile used throughout this repository.
This is exactly the citation the `3 ≤ n` restriction on
`born_expectation_of_invariance` used to prevent. -/
theorem spinUp_weight_eq_born :
    canonicalWeight F0 spinPerspective (0 : Fin 2) = 9 / 25 := by
  rw [effectWeight_eq_born_of_invariance (by norm_num) F0 F0_refinementInvariantLocal
    spinState_norm F0_contextualNullSupport spinPerspective (0 : Fin 2) spinLine
    spinPerspective_effect_zero]
  exact spinLine_weight

end EverettianProbability.Abstract
