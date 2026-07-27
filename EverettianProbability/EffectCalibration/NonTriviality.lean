import EverettianProbability.EffectCalibration.QubitWitness

/-!
**FR.** # Non-trivialité — `EffectCalibration`

Témoin négatif requis par la règle 12 de `AGENTS.md`, pour
`Abstract.RefinementInvariantLocal` instanciée à `I := Effects.interface 2`.
Le comptage naïf uniforme sur **toutes** les issues d'une perspective
d'effets (pas seulement les issues actives) y est sensible : attacher une
issue fantôme, toujours silencieuse (l'effet nul, qui ne se déclenche
jamais), change la crédence uniforme de « spin-down » de `1/2` à `2/3`,
bien que le paiement sous-jacent soit inchangé — exactement le
`1/2 ≠ 2/3` de `Refinement/NonTriviality.lean`, un niveau plus haut, à
l'interface effets abstraite.

Le raffinement utilisé (`phantomZeroRefines`) est construit directement à
partir des champs de `EffectPerspectives.Refines`, et non à partir des
constructeurs amont `duplicateZeroRefinesBinary`/`binaryPerspective`, que
`ProbabilityAPI` ne réexporte pas actuellement — brique nommée, non
reprouvée.

**EN.** # Nontriviality — `EffectCalibration`

Negative witness required by `AGENTS.md` rule 12, for
`Abstract.RefinementInvariantLocal` instantiated at
`I := Effects.interface 2`. Naive uniform counting over **every** outcome
of an effect perspective (not only the active ones) is sensitive to it:
attaching a silent, always-zero phantom outcome changes the uniform
credence of "spin-down" from `1/2` to `2/3`, although the underlying
payoff is unchanged — exactly `Refinement/NonTriviality.lean`'s
`1/2 ≠ 2/3`, one level up, at the abstract effect interface.

The refinement used (`phantomZeroRefines`) is built directly from
`EffectPerspectives.Refines`'s fields, not from the upstream constructors
`duplicateZeroRefinesBinary`/`binaryPerspective`, which `ProbabilityAPI`
does not currently re-export — a named brick, not reproved.
-/

namespace EverettianProbability.Abstract

open scoped BigOperators Classical InnerProductSpace
open QuantumFoundations.ProbabilityAPI

/-- Every effect perspective on a nontrivial space has at least one
outcome: `sum_eq_one` would force `(0 : H n →ₗ[ℂ] H n) = 1` otherwise,
contradicting nontriviality of `H n`. -/
theorem effectPerspective_outcomes_pos {n : ℕ} (hn : 0 < n)
    (D : EffectPerspectives.EffectPerspective n) : 0 < D.outcomes := by
  rcases Nat.eq_zero_or_pos D.outcomes with h | h
  · exfalso
    haveI hempty : IsEmpty (Fin D.outcomes) := by rw [h]; infer_instance
    have hsum := D.sum_eq_one
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    have hv0 : ((EuclideanSpace.basisFun (Fin n) ℂ) ⟨0, hn⟩ : H n) ≠ 0 := by
      intro hz
      have hnorm := (EuclideanSpace.basisFun (Fin n) ℂ).orthonormal.1 ⟨0, hn⟩
      rw [hz, norm_zero] at hnorm
      norm_num at hnorm
    apply hv0
    have heq := congrFun (congrArg DFunLike.coe hsum.symm)
      ((EuclideanSpace.basisFun (Fin n) ℂ) ⟨0, hn⟩)
    simp only [LinearMap.zero_apply, Module.End.one_apply] at heq
    exact heq
  · exact h

/-- Naive uniform counting over *every* outcome of an effect perspective
(not restricted to active/nonzero-weight outcomes): the rival rule this
witness refutes. -/
noncomputable def effectUniformCredence (D : EffectPerspectives.EffectPerspective n)
    (a : Act (Effects.interface n)) : ℝ :=
  (∑ i : Fin D.outcomes, a i) / (D.outcomes : ℝ)

/-- `effectUniformCredence` satisfies the three `RationalExpectationFamily`
axioms at `n = 2` — it is a legitimate rival rule, which is exactly what
makes its sensitivity to refinement worth exhibiting. -/
noncomputable def effectUniformFamily2 : RationalExpectationFamily (Effects.interface 2) where
  V := effectUniformCredence
  affine := by
    intro D t a b
    unfold effectUniformCredence
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, add_div, mul_div_assoc,
      mul_div_assoc]
  monotone := by
    intro D a b hab
    unfold effectUniformCredence
    have hsum : (∑ i : Fin D.outcomes, a i) ≤ ∑ i : Fin D.outcomes, b i :=
      Finset.sum_le_sum (fun i _ => hab i)
    have hcard : (0:ℝ) ≤ (D.outcomes : ℝ) := Nat.cast_nonneg _
    gcongr
  normalized_const := by
    intro D k
    unfold effectUniformCredence Act.const
    have hpos := effectPerspective_outcomes_pos (n := 2) (by norm_num) D
    have hcard : (D.outcomes : ℝ) ≠ 0 := by positivity
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

/-- **FR.** Un troisième effet, toujours silencieux : l'effet nul, qui ne
se déclenche jamais (valeur de Born nulle en tout état). N'est utilisé que
pour construire un raffinement authentiquement non trivial de
`spinPerspective`.

**EN.** A third, always-silent outcome: the zero effect, which never
fires (Born value zero at every state). Used only to build a genuinely
nontrivial refinement of `spinPerspective`. -/
noncomputable def phantomZeroPerspective : EffectPerspectives.EffectPerspective 2 where
  outcomes := 3
  effects := ![EffectPerspectives.projectionEffect spinLine,
    EffectPerspectives.projectionEffect spinLineᗮ,
    EffectPerspectives.projectionEffect (⊥ : Submodule ℂ (H 2))]
  sum_eq_one := by
    rw [Fin.sum_univ_three]
    show (Gleason.projL spinLine : H 2 →ₗ[ℂ] H 2) + (Gleason.projL spinLineᗮ : H 2 →ₗ[ℂ] H 2)
      + (Gleason.projL (⊥ : Submodule ℂ (H 2)) : H 2 →ₗ[ℂ] H 2) = 1
    have hbot : (Gleason.projL (⊥ : Submodule ℂ (H 2)) : H 2 →ₗ[ℂ] H 2) = 0 := by
      unfold Gleason.projL; rw [Submodule.starProjection_bot]; rfl
    rw [hbot, add_zero]
    have hortho : spinLine ⟂ spinLineᗮ := Submodule.isOrtho_orthogonal_right spinLine
    have hsup : spinLine ⊔ spinLineᗮ = ⊤ := Submodule.sup_orthogonal_of_hasOrthogonalProjection
    have h := Gleason.projL_sup_of_isOrtho hortho
    rw [hsup] at h
    rw [← h]
    unfold Gleason.projL
    rw [Submodule.starProjection_top]
    rfl

/-- Explicit parent map: outcomes 0, 1 map straight through; the phantom
zero outcome 2 collapses onto coarse outcome 1 (spin-down). -/
noncomputable def phantomZeroRefines :
    EffectPerspectives.Refines phantomZeroPerspective spinPerspective where
  parent := ![(0 : Fin 2), (1 : Fin 2), (1 : Fin 2)]
  coarse_eq_fiber_sum := by
    intro j
    fin_cases j
    · show (Gleason.projL spinLine : H 2 →ₗ[ℂ] H 2)
        = ∑ i : Fin 3, if (![(0:Fin 2), 1, 1] i) = (0 : Fin 2)
            then (phantomZeroPerspective.effects i : H 2 →ₗ[ℂ] H 2) else 0
      rw [Fin.sum_univ_three]
      show (Gleason.projL spinLine : H 2 →ₗ[ℂ] H 2) =
        (if (0:Fin 2) = 0 then (EffectPerspectives.projectionEffect spinLine : H 2 →ₗ[ℂ] H 2) else 0)
        + (if (1:Fin 2) = 0 then (EffectPerspectives.projectionEffect spinLineᗮ : H 2 →ₗ[ℂ] H 2) else 0)
        + (if (1:Fin 2) = 0 then (EffectPerspectives.projectionEffect (⊥ : Submodule ℂ (H 2)) : H 2 →ₗ[ℂ] H 2) else 0)
      norm_num
    · show (Gleason.projL spinLineᗮ : H 2 →ₗ[ℂ] H 2)
        = ∑ i : Fin 3, if (![(0:Fin 2), 1, 1] i) = (1 : Fin 2)
            then (phantomZeroPerspective.effects i : H 2 →ₗ[ℂ] H 2) else 0
      rw [Fin.sum_univ_three]
      show (Gleason.projL spinLineᗮ : H 2 →ₗ[ℂ] H 2) =
        (if (0:Fin 2) = 1 then (EffectPerspectives.projectionEffect spinLine : H 2 →ₗ[ℂ] H 2) else 0)
        + (if (1:Fin 2) = 1 then (EffectPerspectives.projectionEffect spinLineᗮ : H 2 →ₗ[ℂ] H 2) else 0)
        + (if (1:Fin 2) = 1 then (EffectPerspectives.projectionEffect (⊥ : Submodule ℂ (H 2)) : H 2 →ₗ[ℂ] H 2) else 0)
      have hbot : (Gleason.projL (⊥ : Submodule ℂ (H 2)) : H 2 →ₗ[ℂ] H 2) = 0 := by
        unfold Gleason.projL; rw [Submodule.starProjection_bot]; rfl
      norm_num [hbot]

/-- General fact: pullback along an effect-side `Refines` composes with
the (explicit, total) parent map, at the level of outcomes. -/
theorem pullbackAct_effects_apply {n : ℕ} {fine coarse : EffectPerspectives.EffectPerspective n}
    (r : EffectPerspectives.Refines fine coarse) (a : Act (Effects.interface n)) (i : Fin fine.outcomes) :
    pullbackAct (Effects.interface n) r a (i : ℕ) = a ((r.parent i : Fin coarse.outcomes) : ℕ) := by
  unfold pullbackAct
  show a ((Effects.interface n).parentOutcome r (i:ℕ)) = a ((r.parent i : ℕ))
  congr 1
  show (if h : (i:ℕ) < fine.outcomes then (r.parent ⟨(i:ℕ), h⟩ : Fin coarse.outcomes).val else 0)
    = (r.parent i).val
  rw [dif_pos i.isLt]

theorem effectUniformCredence_coarse :
    effectUniformCredence spinPerspective (Act.indicator (I := Effects.interface 2) (1 : ℕ)) = 1 / 2 := by
  unfold effectUniformCredence
  show (∑ i : Fin 2, Act.indicator (I := Effects.interface 2) (1 : ℕ) (i : ℕ)) / (2:ℝ) = 1 / 2
  rw [Fin.sum_univ_two]
  norm_num [Act.indicator]

theorem effectUniformCredence_fine :
    effectUniformCredence phantomZeroPerspective
      (pullbackAct (Effects.interface 2) phantomZeroRefines
        (Act.indicator (I := Effects.interface 2) (1 : ℕ))) = 2 / 3 := by
  unfold effectUniformCredence
  show (∑ i : Fin 3, pullbackAct (Effects.interface 2) phantomZeroRefines
    (Act.indicator (I := Effects.interface 2) (1 : ℕ)) (i : ℕ)) / (3:ℝ) = 2 / 3
  rw [Fin.sum_univ_three,
    pullbackAct_effects_apply phantomZeroRefines (Act.indicator (I := Effects.interface 2) (1 : ℕ))
      (show Fin phantomZeroPerspective.outcomes from (0 : Fin 3)),
    pullbackAct_effects_apply phantomZeroRefines (Act.indicator (I := Effects.interface 2) (1 : ℕ))
      (show Fin phantomZeroPerspective.outcomes from (1 : Fin 3)),
    pullbackAct_effects_apply phantomZeroRefines (Act.indicator (I := Effects.interface 2) (1 : ℕ))
      (show Fin phantomZeroPerspective.outcomes from (2 : Fin 3))]
  norm_num [Act.indicator, phantomZeroRefines, Matrix.cons_val_two, Matrix.tail_cons]

/-- **NONTRIVIALITY.** Naive uniform counting over every outcome (not
restricted to active ones) is sensitive to a refinement that attaches a
silent, always-zero phantom outcome: the uniform credence of "spin-down
happened" changes from `1/2` to `2/3`, although the underlying payoff is
unchanged. Mirrors `Refinement/NonTriviality.lean`'s `1/2 ≠ 2/3` finding
one level up, at the abstract effect interface. -/
theorem effectUniform_not_refinementInvariantLocal :
    ¬ RefinementInvariantLocal effectUniformFamily2.V := by
  intro hinv
  have hpe : PayoffEquivalentAt phantomZeroRefines
      (pullbackAct (Effects.interface 2) phantomZeroRefines
        (Act.indicator (I := Effects.interface 2) (1 : ℕ)))
      (Act.indicator (I := Effects.interface 2) (1 : ℕ)) := by
    unfold PayoffEquivalentAt
    exact Act.agreeOn_refl phantomZeroPerspective
      (pullbackAct (Effects.interface 2) phantomZeroRefines
        (Act.indicator (I := Effects.interface 2) (1 : ℕ)))
  have h := hinv phantomZeroRefines
    (pullbackAct (Effects.interface 2) phantomZeroRefines
      (Act.indicator (I := Effects.interface 2) (1 : ℕ)))
    (Act.indicator (I := Effects.interface 2) (1 : ℕ)) hpe
  change effectUniformCredence phantomZeroPerspective
      (pullbackAct (Effects.interface 2) phantomZeroRefines
        (Act.indicator (I := Effects.interface 2) (1 : ℕ)))
      = effectUniformCredence spinPerspective (Act.indicator (I := Effects.interface 2) (1 : ℕ))
    at h
  rw [effectUniformCredence_fine, effectUniformCredence_coarse] at h
  norm_num at h

end EverettianProbability.Abstract
