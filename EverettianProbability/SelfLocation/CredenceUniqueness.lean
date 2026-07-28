import EverettianProbability.SelfLocation.RecordConditionedCredence

/-!
**FR.** # Caractérisation de la crédence conditionnée par un record

Ce module distingue une famille abstraite de crédences des propriétés qui
peuvent lui être ajoutées : normalisation sur les records de masse non nulle,
accord sans restriction, proportionnalité canonique interne et cohérence sous
raffinement.

La proportionnalité interne est une prémisse sémantique (`SEM`) : le record
élimine certaines alternatives, mais ne modifie pas les rapports relatifs entre
celles qui restent compatibles. Le théorème principal montre que support,
normalisation et cette proportionnalité déterminent uniquement la crédence de
`RecordConditionedCredence.lean`. Cette construction conditionnelle ne dérive
pas l'interprétation épistémique du poids de la dynamique unitaire.

**EN.** # Characterization of record-conditioned credence

This module separates an abstract credence family from properties that may be
added to it: normalization on nonzero-mass records, unrestricted agreement,
internal canonical proportionality, and refinement coherence.

Internal proportionality is a semantic (`SEM`) premise: a record eliminates
some alternatives but does not alter the relative weight ratios of the
alternatives that remain compatible. The main theorem shows that support,
normalization, and this proportionality uniquely determine the credence of
`RecordConditionedCredence.lean`. This conditional construction does not
derive the epistemic interpretation of weight from unitary dynamics.
-/

namespace EverettianProbability.Abstract

open scoped BigOperators Classical

noncomputable section

variable {I : PerspectiveInterface}

/-- An abstract family of self-locating credences indexed by a perspective
and a finite set of record-compatible cells. -/
structure RecordCredenceFamily
    (I : PerspectiveInterface) where
  credence :
    (D : I.Perspective) →
      Finset (I.Cell D) →
        I.Cell D →
          ℝ
  zero_of_not_mem :
    ∀ (D : I.Perspective)
      (compatible : Finset (I.Cell D))
      (c : I.Cell D),
      c ∉ compatible →
        credence D compatible c = 0
  nonneg :
    ∀ (D : I.Perspective)
      (compatible : Finset (I.Cell D))
      (c : I.Cell D),
      0 ≤ credence D compatible c

namespace RecordCredenceFamily

/-- Normalization on every record whose canonical compatible mass is
nonzero. -/
def NormalizedOnNonzeroMass
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I) : Prop :=
  ∀ (D : I.Perspective)
    (compatible : Finset (I.Cell D)),
    recordCompatibleMass F D compatible ≠ 0 →
      (∑ c : I.Cell D,
        C.credence D compatible c) = 1

/-- Agreement with canonical weight when the accessible record excludes
no cell. -/
def AgreesOnUnrestrictedRecord
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I) : Prop :=
  ∀ (D : I.Perspective)
    (hInj : Function.Injective (@I.outcome D))
    (c : I.Cell D),
    C.credence D Finset.univ c =
      canonicalWeight F D c

/-- Internal canonical proportionality.

For every compatible record of nonzero canonical mass, all compatible
credences are obtained from canonical weights by one common scale factor.
This is an explicit semantic (`SEM`) premise. -/
def CanonicallyProportionalOnRecords
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I) : Prop :=
  ∀ (D : I.Perspective)
    (compatible : Finset (I.Cell D))
    (hmass :
      recordCompatibleMass F D compatible ≠ 0),
    ∃ scale : ℝ,
      ∀ c : I.Cell D,
        c ∈ compatible →
          C.credence D compatible c =
            scale * canonicalWeight F D c

/-- Refinement coherence for record-conditioned credences. -/
def RefinementCoherent
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll :
      ∀ D : I.Perspective,
        Function.Injective (@I.outcome D)) : Prop :=
  ∀ {fine coarse : I.Perspective}
    (r : I.Refinement fine coarse)
    (compatible : Finset (I.Cell coarse))
    (j : I.Cell coarse)
    (hmass :
      recordCompatibleMass F coarse compatible ≠ 0),
    C.credence coarse compatible j =
      ∑ i : I.Cell fine,
        if I.parentCell r i = j then
          C.credence fine
            (pullbackRecordCells r compatible) i
        else
          0

end RecordCredenceFamily

/-- The canonical record-conditioned credence family. -/
def canonicalRecordCredenceFamily
    (F : RationalExpectationFamily I) :
    RecordCredenceFamily I where
  credence :=
    fun D compatible c =>
      recordConditionedCredence F D compatible c
  zero_of_not_mem := by
    intro D compatible c hc
    exact
      recordConditionedCredence_zero_of_not_mem
        F D compatible c hc
  nonneg := by
    intro D compatible c
    exact
      recordConditionedCredence_nonneg
        F D compatible c

@[simp]
theorem canonicalRecordCredenceFamily_credence
    (F : RationalExpectationFamily I)
    (D : I.Perspective)
    (compatible : Finset (I.Cell D))
    (c : I.Cell D) :
    (canonicalRecordCredenceFamily F).credence D compatible c =
      recordConditionedCredence
        F D compatible c := by
  rfl

theorem canonicalRecordCredenceFamily_normalized
    (F : RationalExpectationFamily I) :
    (canonicalRecordCredenceFamily F).NormalizedOnNonzeroMass F := by
  intro D compatible hmass
  exact
    recordConditionedCredence_normalized
      F D compatible hmass

theorem canonicalRecordCredenceFamily_agrees_unrestricted
    (F : RationalExpectationFamily I) :
    (canonicalRecordCredenceFamily F).AgreesOnUnrestrictedRecord F := by
  intro D hInj c
  exact
    recordConditionedCredence_univ
      F D hInj c

theorem canonicalRecordCredenceFamily_proportional
    (F : RationalExpectationFamily I) :
    (canonicalRecordCredenceFamily F).CanonicallyProportionalOnRecords F := by
  intro D compatible hmass
  refine
    ⟨1 / recordCompatibleMass F D compatible, ?_⟩
  intro c hc
  simp only [
    canonicalRecordCredenceFamily_credence,
    recordConditionedCredence,
    hmass,
    hc,
    if_false,
    if_true
  ]
  ring

theorem canonicalRecordCredenceFamily_refinementCoherent
    (F : RationalExpectationFamily I)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll :
      ∀ D : I.Perspective,
        Function.Injective (@I.outcome D)) :
    (canonicalRecordCredenceFamily F).RefinementCoherent F hinv hInjAll := by
  intro fine coarse r compatible j hmass
  exact
    recordConditionedCredence_refinement_fiber
      F hinv hInjAll
      r compatible j hmass

private theorem sum_credence_eq_sum_compatible
    (C : RecordCredenceFamily I)
    (D : I.Perspective)
    (compatible : Finset (I.Cell D)) :
    (∑ x : I.Cell D,
      C.credence D compatible x) =
      ∑ x ∈ compatible,
        C.credence D compatible x := by
  calc
    (∑ x : I.Cell D, C.credence D compatible x) =
        ∑ x : I.Cell D,
          if x ∈ compatible then C.credence D compatible x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hmem : x ∈ compatible
      · simp [hmem]
      · rw [C.zero_of_not_mem D compatible x hmem]
        simp [hmem]
    _ = ∑ x ∈ Finset.univ.filter (fun x : I.Cell D => x ∈ compatible),
          C.credence D compatible x := by
      exact (Finset.sum_filter _ _).symm
    _ = ∑ x ∈ compatible, C.credence D compatible x := by
      congr 1
      ext x
      simp

/-- Uniqueness of the canonical record-conditioned credence.

On every compatible record of nonzero canonical mass, any abstract
credence family satisfying normalization and internal canonical
proportionality agrees pointwise with `recordConditionedCredence`.

The proportionality premise is semantic (`SEM`); the theorem does not
derive it from unitary dynamics. -/
theorem RecordCredenceFamily.credence_eq_recordConditionedCredence
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I)
    (hnorm :
      C.NormalizedOnNonzeroMass F)
    (hprop :
      C.CanonicallyProportionalOnRecords F)
    (D : I.Perspective)
    (compatible : Finset (I.Cell D))
    (hmass :
      recordCompatibleMass F D compatible ≠ 0)
    (c : I.Cell D) :
    C.credence D compatible c =
      recordConditionedCredence
        F D compatible c := by
  obtain ⟨scale, hscale⟩ :=
    hprop D compatible hmass
  have hsum_support :
      (∑ x : I.Cell D,
        C.credence D compatible x) =
      ∑ x ∈ compatible,
        C.credence D compatible x :=
    sum_credence_eq_sum_compatible C D compatible
  have hsum_proportional :
      (∑ x ∈ compatible,
        C.credence D compatible x) =
      scale *
        recordCompatibleMass F D compatible := by
    unfold recordCompatibleMass
    calc
      (∑ x ∈ compatible,
          C.credence D compatible x) =
        ∑ x ∈ compatible,
          scale * canonicalWeight F D x := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hscale x hx
      _ = scale *
          ∑ x ∈ compatible,
            canonicalWeight F D x := by
              rw [Finset.mul_sum]
  have hscale_mass :
      scale *
          recordCompatibleMass F D compatible =
        1 := by
    rw [← hsum_proportional, ← hsum_support]
    exact hnorm D compatible hmass
  have hscale_eq :
      scale =
        1 / recordCompatibleMass F D compatible := by
    apply (eq_div_iff hmass).2
    simpa [mul_comm] using hscale_mass
  by_cases hc : c ∈ compatible
  · rw [hscale c hc, hscale_eq]
    simp [recordConditionedCredence, hmass, hc]
    ring
  · rw [C.zero_of_not_mem D compatible c hc]
    simp [recordConditionedCredence, hmass, hc]

/-- Any normalized and canonically proportional record credence family
inherits refinement coherence on nonzero compatible records. -/
theorem RecordCredenceFamily.refinementCoherent_of_normalized_of_proportional
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I)
    (hnorm :
      C.NormalizedOnNonzeroMass F)
    (hprop :
      C.CanonicallyProportionalOnRecords F)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll :
      ∀ D : I.Perspective,
        Function.Injective (@I.outcome D)) :
    C.RefinementCoherent F hinv hInjAll := by
  intro fine coarse r compatible j hmass
  have hmass_pullback :
      recordCompatibleMass F fine
          (pullbackRecordCells r compatible) ≠ 0 := by
    rw [recordCompatibleMass_pullback F hinv hInjAll r compatible]
    exact hmass
  rw [
    C.credence_eq_recordConditionedCredence
      F hnorm hprop
      coarse compatible hmass j,
    recordConditionedCredence_refinement_fiber
      F hinv hInjAll
      r compatible j hmass
  ]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hparent :
      I.parentCell r i = j
  · rw [if_pos hparent, if_pos hparent]
    exact
      (C.credence_eq_recordConditionedCredence
        F hnorm hprop
        fine
        (pullbackRecordCells r compatible)
        hmass_pullback
        i).symm
  · simp [hparent]

end
end EverettianProbability.Abstract
