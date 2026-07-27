import EverettianProbability.Preference.AbstractRepresentation
import EverettianProbability.Refinement.AbstractPayoffPreserving

/-!
**FR.** # L'invariance sous raffinement force Grain, niveau abstrait

L'analogue de `BornCalibration/RefinementImpliesGrain.lean`. Une
différence de forme, favorable : `Abstract.Grain` (`Core/Interface.lean`)
est déjà énoncée sous forme de somme sur la fibre — il n'y a pas, au niveau
abstrait, de détour par un équivalent de `axGrain_iff_coarseCells`. La
conclusion ci-dessous (`canonicalWeight_grain`) porte donc directement
cette identité de somme sur la fibre, plutôt que d'envelopper le résultat
dans `Abstract.Grain I E` pour un `E : I.EstimationRule` — car `EstimationRule`
est un type opaque par instance (une simple fonction côté projectif, une
structure à quatre champs simultanés côté effets, voir
`docs/QUBIT_FEASIBILITY_REPORT.md`) : rien ne garantit qu'un poids
`canonicalWeight F` quelconque puisse s'y emballer sans disposer aussi de
sa positivité et de sa normalisation. L'emballage effectif, côté effets,
est le travail de `EffectCalibration/EstimationRulePackaging.lean`.

**EN.** # Refinement invariance forces Grain, abstract level

The analogue of `BornCalibration/RefinementImpliesGrain.lean`. One
favorable difference in form: `Abstract.Grain` (`Core/Interface.lean`) is
already stated as a fiber sum — there is no abstract-level detour through
an analogue of `axGrain_iff_coarseCells`. The conclusion below
(`canonicalWeight_grain`) therefore carries this fiber-sum identity
directly, rather than wrapping the result in `Abstract.Grain I E` for some
`E : I.EstimationRule` — because `EstimationRule` is an opaque type per
instance (a bare function on the projective side, a four-field bundled
structure on the effect side, see `docs/QUBIT_FEASIBILITY_REPORT.md`):
nothing guarantees an arbitrary `canonicalWeight F` can be packaged into it
without also having its positivity and normalization in hand. That actual
packaging, on the effect side, is the work of
`EffectCalibration/EstimationRulePackaging.lean`.
-/

namespace EverettianProbability.Abstract

open scoped BigOperators Classical

variable {I : PerspectiveInterface}

/-- **FR.** L'invariance locale force l'identité de somme sur la fibre pour
le poids canonique — l'analogue abstrait de `refinement_invariant_implies_
grain`, sous l'hypothèse que `outcome` est injective à toute perspective en
jeu.

**EN.** Local invariance forces the fiber-sum identity for the canonical
weight — the abstract analogue of `refinement_invariant_implies_grain`,
given that `outcome` is injective at every perspective involved. -/
theorem canonicalWeight_grain (F : RationalExpectationFamily I)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll : ∀ D : I.Perspective, Function.Injective (@I.outcome D))
    {fine coarse : I.Perspective} (r : I.Refinement fine coarse) (j : I.Cell coarse) :
    letI := I.cellFintype fine
    canonicalWeight F coarse j =
      ∑ i : I.Cell fine, if I.parentCell r i = j then canonicalWeight F fine i else 0 := by
  letI := I.cellFintype fine
  letI := I.cellFintype coarse
  letI := I.cellDecidableEq coarse
  set a : Act I := Act.indicator (I.outcome j) with ha_def
  have hstep : F.V fine (pullbackAct I r a) = F.V coarse a :=
    hinv r (pullbackAct I r a) a (Act.agreeOn_refl fine (pullbackAct I r a))
  rw [represents F fine (hInjAll fine) (pullbackAct I r a),
    represents F coarse (hInjAll coarse) a] at hstep
  have hrhs : (∑ j' : I.Cell coarse, canonicalWeight F coarse j' * a (I.outcome j'))
      = canonicalWeight F coarse j := by
    rw [Finset.sum_eq_single j]
    · rw [ha_def, Act.indicator_self, mul_one]
    · intro j' _ hj'
      rw [ha_def, Act.indicator_of_ne (fun hh => hj' (hInjAll coarse hh)), mul_zero]
    · exact fun hnot => (hnot (Finset.mem_univ j)).elim
  have hlhs : (∑ i : I.Cell fine, canonicalWeight F fine i * (pullbackAct I r a) (I.outcome i))
      = ∑ i : I.Cell fine, if I.parentCell r i = j then canonicalWeight F fine i else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    have hpc : (pullbackAct I r a) (I.outcome i) = a (I.outcome (I.parentCell r i)) := by
      unfold pullbackAct
      rw [Function.comp_apply, I.parentOutcome_cell]
    rw [hpc, ha_def]
    by_cases hpj : I.parentCell r i = j
    · rw [if_pos hpj, hpj, Act.indicator_self, mul_one]
    · rw [Act.indicator_of_ne (fun hh => hpj (hInjAll coarse hh)), if_neg hpj, mul_zero]
  rw [hlhs, hrhs] at hstep
  exact hstep.symm

end EverettianProbability.Abstract
