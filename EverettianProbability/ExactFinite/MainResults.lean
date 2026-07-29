import EverettianProbability.ExactFinite.PhysicalAdequacy

/-!
**FR.** # Résultats principaux de l'adéquation physique exacte finie

Ce module agrège la couche expérimentale exacte finie en un résultat
principal unique.

Le noyau physique repose seulement sur la compatibilité positive et
fibre par fibre d'un profil de poids futurs. Il fournit une réalisation
unitaire commutant avec les projecteurs présents, conservant le record
présent pour tout vecteur, réalisant exactement les poids futurs et
préservant les conséquences présentes.

Une seconde couche ajoute les prémisses explicites de calibration P4.
Sous ces prémisses, les crédences envers les continuateurs sont les
rapports borniens conditionnels prescrits, sont normalisées sur toute
fibre de poids non nul et reconstruisent les poids fins.

Cette conclusion est exacte, projective et de dimension finie. Elle ne
construit ni Hamiltonien local naturel, ni décohérence approximative, ni
théorie de l'identité personnelle.

**EN.** # Main results of exact finite physical adequacy

This module aggregates the experimental exact-finite layer into one
main result.

The physical core assumes only positive fibrewise compatibility of a
future weight profile. It supplies a unitary realization commuting with
the present projectors, preserving the present record for every vector,
realizing the exact future weights, and preserving present consequences.

A second layer adds the explicit P4 calibration premises. Under these
premises, continuator credences are the prescribed conditional Born
ratios, are normalized on every nonzero-weight fibre, and reconstruct
the fine weights.

The conclusion is exact, projective, and finite-dimensional. It
constructs neither a natural local Hamiltonian, approximate decoherence,
nor a theory of personal identity.
-/

namespace EverettianProbability.ExactFinite

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core
open EverettianProbability.Abstract
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : ℕ}

/-- Canonical chosen physical realization associated with a compatible
fine-weight profile. The choice is mathematical and is not claimed to
be physically unique. -/
noncomputable def canonicalPhysicalRealization
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q) :
    PhysicalRealization r x q :=
  physicalRealizationOfCompatible h

@[simp]
theorem canonicalPhysicalRealization_unitary
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q) :
    (canonicalPhysicalRealization h).unitary =
      (physicalRealizationOfCompatible h).unitary := by
  rfl

/-- Explicit calibration premises for the exact-finite physical
realization.

These premises are not part of the purely physical realization core.
They are required only for identifying canonical continuator credence
with the prescribed conditional Born ratio. -/
structure ExactFiniteCalibrationPremises
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q) where
  F : RationalExpectationFamily (Projective.interface n)
  dim_ge_three : 3 ≤ n
  refinement_invariant : RefinementInvariantLocal F.V
  source_normalized : ‖x‖ = 1
  target_null_support :
    AxNul
      (EverettianProbability.BornCalibration.canonicalWeight
        (projectiveConcreteExpectationFamily F))
      (canonicalPhysicalRealization h).targetState

/-- Exact finite physical core obtained from fibrewise compatibility
alone. -/
structure ExactFiniteCoreResults
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q) : Prop where
  target_same_record :
    SameRecord present x (canonicalPhysicalRealization h).targetState
  target_norm_eq :
    ‖(canonicalPhysicalRealization h).targetState‖ = ‖x‖
  unitary_commutes :
    CommutesWithPerspectiveProjectors
      present
      (canonicalPhysicalRealization h).unitary.toLinearEquiv.toLinearMap
  realizes_future_weights :
    ∀ i : (Projective.interface n).Cell future,
      bornRecord future ((canonicalPhysicalRealization h).unitary x) i = q i
  preserves_present_record :
    PreservesRecordObservable
      (bornRecord present)
      (canonicalPhysicalRealization h).evolution
  physical_ratio_is_prescribed :
    ∀ (c : (Projective.interface n).Cell present)
      (i : (Projective.interface n).Cell future),
      EverettianProbability.Abstract.UniformRecordRespectingProjectiveContinuation.physicalContinuatorBornRatio
          (canonicalPhysicalRealization h).toUniformContinuation x c i =
        prescribedRatio r x q c i
  realizes_payoff_invariance :
    RealizesBornPayoffInvariance
      (canonicalPhysicalRealization h).toUniformContinuation.step
      (canonicalPhysicalRealization h).toUniformContinuation.evolution
  born_expectation_pullback :
    ∀ (z : H n) (a : EverettianProbability.Core.Act n),
      EverettianProbability.Refinement.bornExpectation
          ((canonicalPhysicalRealization h).evolution z)
          future
          (EverettianProbability.Refinement.pullbackAct r a) =
        EverettianProbability.Refinement.bornExpectation z present a

/-- Every compatible fine-weight profile satisfies the full exact
finite physical core. -/
theorem exactFiniteCoreResults
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q) :
    ExactFiniteCoreResults h := by
  let R : PhysicalRealization r x q := canonicalPhysicalRealization h
  refine
    { target_same_record := ?_
      target_norm_eq := ?_
      unitary_commutes := ?_
      realizes_future_weights := ?_
      preserves_present_record := ?_
      physical_ratio_is_prescribed := ?_
      realizes_payoff_invariance := ?_
      born_expectation_pullback := ?_ }
  · apply (sameRecord_iff_exists_recordUnitary present x R.targetState).2
    exact ⟨R.unitary, R.commutes_present, rfl⟩
  · change ‖R.unitary x‖ = ‖x‖
    exact R.unitary.norm_map x
  · exact R.commutes_present
  · intro i
    exact R.realizes_weights i
  · exact R.preserves_presentRecord
  · intro c i
    exact R.physicalRatio_eq_prescribedRatio c i
  · exact R.realizes_payoffInvariance
  · intro z a
    exact R.bornExpectation_pullback_eq z a

/-- Calibrated continuator conclusions for one nonzero present fibre. -/
structure ExactFiniteCalibratedResults
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q)
    (P : ExactFiniteCalibrationPremises h)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0) : Prop where
  target_normalized : ‖(canonicalPhysicalRealization h).targetState‖ = 1
  continuator_credence_is_prescribed :
    ∀ i : (Projective.interface n).Cell future,
      ContinuationStep.continuatorCredence P.F
          (canonicalPhysicalRealization h).toUniformContinuation.step c i =
        prescribedRatio r x q c i
  continuator_credence_normalized :
    (∑ i : (Projective.interface n).Cell future,
      ContinuationStep.continuatorCredence P.F
        (canonicalPhysicalRealization h).toUniformContinuation.step c i) = 1
  parent_weight_recovers_fine_weight :
    ∀ (i : (Projective.interface n).Cell future),
      (Projective.interface n).parentCell r i = c →
        bornRecord present x c *
            ContinuationStep.continuatorCredence P.F
              (canonicalPhysicalRealization h).toUniformContinuation.step c i =
          q i

/-- P4 calibration identifies realized continuator credence with the
prescribed conditional Born ratio. -/
theorem exactFiniteCalibratedResults
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q)
    (P : ExactFiniteCalibrationPremises h)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0) :
    ExactFiniteCalibratedResults h P c hc := by
  let R : PhysicalRealization r x q := canonicalPhysicalRealization h
  refine
    { target_normalized := ?_
      continuator_credence_is_prescribed := ?_
      continuator_credence_normalized := ?_
      parent_weight_recovers_fine_weight := ?_ }
  · change ‖R.unitary x‖ = 1
    calc
      ‖R.unitary x‖ = ‖x‖ := R.unitary.norm_map x
      _ = 1 := P.source_normalized
  · intro i
    exact
      R.continuatorCredence_eq_prescribedRatio
        P.F P.dim_ge_three P.refinement_invariant P.source_normalized
        P.target_null_support c hc i
  · exact
      R.sum_continuatorCredence_eq_one
        h P.F P.dim_ge_three P.refinement_invariant P.source_normalized
        P.target_null_support c hc
  · intro i hparent
    exact
      R.parentWeight_mul_continuatorCredence_eq_fineWeight
        P.F P.dim_ge_three P.refinement_invariant P.source_normalized
        P.target_null_support c hc i hparent

/-- Complete exact-finite result in its explicitly calibrated scope. -/
structure ExactFiniteMainResults
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q)
    (P : ExactFiniteCalibrationPremises h)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0) : Prop where
  core : ExactFiniteCoreResults h
  calibrated : ExactFiniteCalibratedResults h P c hc

/-- Main theorem of exact finite physical adequacy.

Every compatible positive fine-weight profile admits an exact
projector-commuting unitary realization preserving the present record
and present consequences. Under the explicit calibration premises,
continuator credences equal the prescribed conditional Born ratios,
normalize on every nonzero present fibre, and reconstruct the fine
weights. -/
theorem exactFiniteMainResults
    {future present : Perspective n}
    {r : Refines future present}
    {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q)
    (P : ExactFiniteCalibrationPremises h)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0) :
    ExactFiniteMainResults h P c hc :=
  { core := exactFiniteCoreResults h
    calibrated := exactFiniteCalibratedResults h P c hc }

end
end EverettianProbability.ExactFinite
