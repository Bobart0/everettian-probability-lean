import EverettianProbability.ExactFinite.MainResults

/-!
**FR.** # API stable du résultat exact fini

Ce module constitue la façade publique stable de la couche exacte finie à partir
de la version `2.0.0`.

Il expose la caractérisation par orbite unitaire, la réalisation des profils
fins compatibles, le noyau physique exact, les conclusions calibrées et le
traitement explicite des fibres parentes de poids nul.

La compatibilité contient déjà l’accord des sommes de fibres avec le record
bornien présent. Le résultat ne dérive donc pas la règle de Born de la seule
dynamique unitaire.

Les conclusions de crédence restent conditionnelles aux prémisses explicites
de calibration. La réalisation unitaire est existentielle ; ni son unicité, ni
un Hamiltonien local naturel, ni la décohérence approximative ne sont établis.

**EN.** # Stable API for the exact-finite result

This module is the stable public facade of the exact-finite layer from version
`2.0.0` onward.

It exposes the unitary-orbit characterization, realization of compatible fine
profiles, the exact physical core, calibrated conclusions, and explicit
treatment of zero-weight parent fibres.

Compatibility already includes agreement of fibre sums with the present Born
record. The result therefore does not derive the Born rule from unitary
dynamics alone.

Credence conclusions remain conditional on explicit calibration premises. The
unitary realization is existential; neither its uniqueness, a natural local
Hamiltonian, nor approximate decoherence is established.
-/

namespace EverettianProbability.API.ExactFinite

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core
open EverettianProbability.Abstract
open scoped BigOperators Classical InnerProductSpace

noncomputable section

variable {n : ℕ}

abbrev SameRecord (D : Perspective n) (x y : H n) : Prop :=
  EverettianProbability.ExactFinite.SameRecord D x y

abbrev RecordUnitaryOrbit (D : Perspective n) (x y : H n) : Prop :=
  EverettianProbability.ExactFinite.RecordUnitaryOrbit D x y

abbrev FineWeightPlan
    {future present : Perspective n} (r : Refines future present) (x : H n) :=
  EverettianProbability.ExactFinite.FineWeightPlan r x

abbrev CompatibleFineWeights
    {future present : Perspective n} (r : Refines future present) (x : H n)
    (q : (Projective.interface n).Cell future → ℝ) : Prop :=
  EverettianProbability.ExactFinite.CompatibleFineWeights r x q

abbrev UnitaryRealizesFineWeights
    {future present : Perspective n} (r : Refines future present) (x : H n)
    (q : (Projective.interface n).Cell future → ℝ) : Prop :=
  EverettianProbability.ExactFinite.UnitaryRealizesFineWeights r x q

abbrev PhysicalRealization
    {future present : Perspective n} (r : Refines future present) (x : H n)
    (q : (Projective.interface n).Cell future → ℝ) :=
  EverettianProbability.ExactFinite.PhysicalRealization r x q

noncomputable def canonicalTargetState
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineWeightPlan r x) : H n :=
  EverettianProbability.ExactFinite.canonicalTargetState plan

noncomputable def canonicalPhysicalRealization
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q) :
    PhysicalRealization r x q :=
  EverettianProbability.ExactFinite.canonicalPhysicalRealization h

def prescribedRatio
    {future present : Perspective n}
    (r : Refines future present) (x : H n)
    (q : (Projective.interface n).Cell future → ℝ)
    (c : (Projective.interface n).Cell present)
    (i : (Projective.interface n).Cell future) : ℝ :=
  EverettianProbability.ExactFinite.prescribedRatio r x q c i

theorem recordUnitaryOrbit_iff_sameRecord
    (D : Perspective n) (x y : H n) :
    RecordUnitaryOrbit D x y ↔ SameRecord D x y :=
  EverettianProbability.ExactFinite.recordUnitaryOrbit_iff_sameRecord D x y

theorem canonicalTargetState_bornWeight
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineWeightPlan r x) (i : (Projective.interface n).Cell future) :
    bornRecord future (canonicalTargetState plan) i = plan.weight i :=
  EverettianProbability.ExactFinite.canonicalTargetState_bornWeight plan i

theorem canonicalTargetState_sameRecord
    {future present : Perspective n} {r : Refines future present} {x : H n}
    (plan : FineWeightPlan r x) :
    SameRecord present x (canonicalTargetState plan) :=
  EverettianProbability.ExactFinite.canonicalTargetState_sameRecord plan

theorem compatibleFineWeights_iff_unitaryRealizable
    {future present : Perspective n}
    (r : Refines future present) (x : H n)
    (q : (Projective.interface n).Cell future → ℝ) :
    CompatibleFineWeights r x q ↔ UnitaryRealizesFineWeights r x q :=
  EverettianProbability.ExactFinite.compatibleFineWeights_iff_unitaryRealizable r x q

theorem compatibleFineWeights_iff_nonempty_physicalRealization
    {future present : Perspective n}
    (r : Refines future present) (x : H n)
    (q : (Projective.interface n).Cell future → ℝ) :
    CompatibleFineWeights r x q ↔ Nonempty (PhysicalRealization r x q) :=
  EverettianProbability.ExactFinite.compatibleFineWeights_iff_nonempty_physicalRealization r x q

structure ExactFiniteCalibrationPremises
    {future present : Perspective n} {r : Refines future present} {x : H n}
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

namespace ExactFiniteCalibrationPremises

def toInternal
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    {h : CompatibleFineWeights r x q}
    (P : ExactFiniteCalibrationPremises h) :
    EverettianProbability.ExactFinite.ExactFiniteCalibrationPremises h where
  F := P.F
  dim_ge_three := P.dim_ge_three
  refinement_invariant := P.refinement_invariant
  source_normalized := P.source_normalized
  target_null_support := by
    simpa [canonicalPhysicalRealization] using P.target_null_support

end ExactFiniteCalibrationPremises

structure ExactFiniteCoreResults
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q) : Prop where
  target_same_record :
    SameRecord present x (canonicalPhysicalRealization h).targetState
  target_norm_eq :
    ‖(canonicalPhysicalRealization h).targetState‖ = ‖x‖
  unitary_commutes :
    CommutesWithPerspectiveProjectors present
      (canonicalPhysicalRealization h).unitary.toLinearEquiv.toLinearMap
  realizes_future_weights :
    ∀ i : (Projective.interface n).Cell future,
      bornRecord future ((canonicalPhysicalRealization h).unitary x) i = q i
  preserves_present_record :
    PreservesRecordObservable (bornRecord present)
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
          ((canonicalPhysicalRealization h).evolution z) future
          (EverettianProbability.Refinement.pullbackAct r a) =
        EverettianProbability.Refinement.bornExpectation z present a

theorem exactFiniteCoreResults
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q) :
    ExactFiniteCoreResults h := by
  let I := EverettianProbability.ExactFinite.exactFiniteCoreResults h
  exact
    { target_same_record := by
        simpa [canonicalPhysicalRealization] using I.target_same_record
      target_norm_eq := by
        simpa [canonicalPhysicalRealization] using I.target_norm_eq
      unitary_commutes := by
        simpa [canonicalPhysicalRealization] using I.unitary_commutes
      realizes_future_weights := by
        intro i
        simpa [canonicalPhysicalRealization] using I.realizes_future_weights i
      preserves_present_record := by
        simpa [canonicalPhysicalRealization] using I.preserves_present_record
      physical_ratio_is_prescribed := by
        intro c i
        simpa [canonicalPhysicalRealization, prescribedRatio] using
          I.physical_ratio_is_prescribed c i
      realizes_payoff_invariance := by
        simpa [canonicalPhysicalRealization] using I.realizes_payoff_invariance
      born_expectation_pullback := by
        intro z a
        simpa [canonicalPhysicalRealization] using I.born_expectation_pullback z a }

structure ExactFiniteCalibratedResults
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q)
    (P : ExactFiniteCalibrationPremises h)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0) : Prop where
  target_normalized :
    ‖(canonicalPhysicalRealization h).targetState‖ = 1
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

theorem exactFiniteCalibratedResults
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q)
    (P : ExactFiniteCalibrationPremises h)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0) :
    ExactFiniteCalibratedResults h P c hc := by
  let I := EverettianProbability.ExactFinite.exactFiniteCalibratedResults
    h P.toInternal c hc
  exact
    { target_normalized := by
        simpa [canonicalPhysicalRealization] using I.target_normalized
      continuator_credence_is_prescribed := by
        intro i
        simpa [ExactFiniteCalibrationPremises.toInternal,
          canonicalPhysicalRealization, prescribedRatio] using
          I.continuator_credence_is_prescribed i
      continuator_credence_normalized := by
        simpa [ExactFiniteCalibrationPremises.toInternal,
          canonicalPhysicalRealization] using I.continuator_credence_normalized
      parent_weight_recovers_fine_weight := by
        intro i hparent
        simpa [ExactFiniteCalibrationPremises.toInternal,
          canonicalPhysicalRealization] using
          I.parent_weight_recovers_fine_weight i hparent }

structure ExactFiniteNullParentResults
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c = 0) : Prop where
  fine_weights_zero :
    ∀ i : (Projective.interface n).Cell future,
      (Projective.interface n).parentCell r i = c → q i = 0
  prescribed_ratios_zero :
    ∀ i : (Projective.interface n).Cell future,
      prescribedRatio r x q c i = 0
  physical_ratios_zero :
    ∀ i : (Projective.interface n).Cell future,
      EverettianProbability.Abstract.UniformRecordRespectingProjectiveContinuation.physicalContinuatorBornRatio
          (canonicalPhysicalRealization h).toUniformContinuation x c i = 0

theorem exactFiniteNullParentResults
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c = 0) :
    ExactFiniteNullParentResults h c hc := by
  let I := EverettianProbability.ExactFinite.exactFiniteNullParentResults h c hc
  exact
    { fine_weights_zero := by
        intro i hparent
        exact I.fine_weights_zero i hparent
      prescribed_ratios_zero := by
        intro i
        simpa [prescribedRatio] using I.prescribed_ratios_zero i
      physical_ratios_zero := by
        intro i
        simpa [canonicalPhysicalRealization] using I.physical_ratios_zero i }

structure ExactFiniteMainResults
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q)
    (P : ExactFiniteCalibrationPremises h)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0) : Prop where
  core : ExactFiniteCoreResults h
  calibrated : ExactFiniteCalibratedResults h P c hc

/-- Stable aggregate theorem of the exact-finite API. -/
theorem exactFiniteMainResults
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q)
    (P : ExactFiniteCalibrationPremises h)
    (c : (Projective.interface n).Cell present)
    (hc : bornRecord present x c ≠ 0) :
    ExactFiniteMainResults h P c hc :=
  { core := exactFiniteCoreResults h
    calibrated := exactFiniteCalibratedResults h P c hc }

theorem exactPhysicalAdequacy
    {future present : Perspective n} {r : Refines future present} {x : H n}
    {q : (Projective.interface n).Cell future → ℝ}
    (h : CompatibleFineWeights r x q) :
    ∃ U : H n ≃ₗᵢ[ℂ] H n,
      CommutesWithPerspectiveProjectors present U.toLinearEquiv.toLinearMap ∧
      (∀ i : (Projective.interface n).Cell future,
        bornRecord future (U x) i = q i) ∧
      RealizesBornPayoffInvariance (ContinuationStep.mk r)
        U.toLinearEquiv.toLinearMap :=
  EverettianProbability.ExactFinite.exactPhysicalAdequacy h

end
end EverettianProbability.API.ExactFinite
