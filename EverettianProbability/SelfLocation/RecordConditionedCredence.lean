import EverettianProbability.Diachronic.Conditioning

/-!
**FR.** # Crédence auto-localisante conditionnée par un record

Ce module ouvre P7 par une construction explicitement conditionnelle.

Pour une perspective `D`, un ensemble fini `S : Finset (I.Cell D)`
représente les alternatives compatibles avec le record accessible à
l'observateur. La crédence candidate d'une cellule compatible est obtenue
en renormalisant le poids canonique sur `S`.

Le choix d'interpréter cette mesure conditionnée comme une crédence
auto-localisante est un pont sémantique (`SEM`). Il n'est pas dérivé de
la dynamique unitaire, de la décohérence ou des seuls axiomes
mathématiques de la mesure de Born.

Le module prouve la positivité, la normalisation lorsque la masse compatible
est non nulle, l'accord avec le poids canonique sans restriction, la
conservation de la masse compatible sous raffinement, et la cohérence sous
subdivision des alternatives compatibles. Aucun temps, continuateur, indexical
personnel ou record physique microscopique n'est formalisé.

**EN.** # Self-locating credence conditioned on a record

This module opens P7 with an explicitly conditional construction.

For a perspective `D`, a finite set `S : Finset (I.Cell D)` represents
the alternatives compatible with the observer's accessible record. The
candidate credence of a compatible cell is obtained by renormalizing the
canonical weight over `S`.

Interpreting this conditioned measure as self-locating credence is a
semantic (`SEM`) bridge. It is not derived from unitary dynamics,
decoherence, or the mathematical Born-measure axioms alone.

The module proves positivity, normalization when compatible mass is nonzero,
agreement with canonical weight without restriction, preservation of
compatible mass under refinement, and coherence under compatible subdivision.
No time, continuator, personal indexical, or microscopic physical record is
formalized.
-/

namespace EverettianProbability.Abstract

open scoped BigOperators Classical

noncomputable section

variable {I : PerspectiveInterface}

/-- Total canonical weight of the cells compatible with an accessible
record. -/
def recordCompatibleMass
    (F : RationalExpectationFamily I)
    (D : I.Perspective)
    (compatible : Finset (I.Cell D)) : ℝ :=
  ∑ c ∈ compatible, canonicalWeight F D c

theorem recordCompatibleMass_nonneg
    (F : RationalExpectationFamily I)
    (D : I.Perspective)
    (compatible : Finset (I.Cell D)) :
    0 ≤ recordCompatibleMass F D compatible := by
  unfold recordCompatibleMass
  exact Finset.sum_nonneg fun c hc =>
    canonicalWeight_axPos F D c

/-- Candidate self-locating credence obtained by normalizing canonical
weight over the record-compatible cells.

This definition is an explicit semantic bridge. It returns zero when
the compatible mass is zero or when the cell is incompatible. -/
def recordConditionedCredence
    (F : RationalExpectationFamily I)
    (D : I.Perspective)
    (compatible : Finset (I.Cell D))
    (c : I.Cell D) : ℝ :=
  if recordCompatibleMass F D compatible = 0 then
    0
  else if c ∈ compatible then
    canonicalWeight F D c /
      recordCompatibleMass F D compatible
  else
    0

theorem recordConditionedCredence_zero_of_not_mem
    (F : RationalExpectationFamily I)
    (D : I.Perspective)
    (compatible : Finset (I.Cell D))
    (c : I.Cell D)
    (hc : c ∉ compatible) :
    recordConditionedCredence F D compatible c = 0 := by
  simp [recordConditionedCredence, hc]

theorem recordConditionedCredence_nonneg
    (F : RationalExpectationFamily I)
    (D : I.Perspective)
    (compatible : Finset (I.Cell D))
    (c : I.Cell D) :
    0 ≤ recordConditionedCredence F D compatible c := by
  unfold recordConditionedCredence
  by_cases hmass : recordCompatibleMass F D compatible = 0
  · simp [hmass]
  · by_cases hc : c ∈ compatible
    · simp only [hmass, hc, if_false, if_true]
      exact div_nonneg
        (canonicalWeight_axPos F D c)
        (recordCompatibleMass_nonneg F D compatible)
    · simp [hmass, hc]

theorem sum_recordConditionedCredence_eq_zero_or_one
    (F : RationalExpectationFamily I)
    (D : I.Perspective)
    (compatible : Finset (I.Cell D)) :
    (∑ c : I.Cell D,
      recordConditionedCredence F D compatible c) =
      if recordCompatibleMass F D compatible = 0 then
        0
      else
        1 := by
  by_cases hmass : recordCompatibleMass F D compatible = 0
  · simp [recordConditionedCredence, hmass]
  · rw [if_neg hmass]
    calc
      (∑ c : I.Cell D, recordConditionedCredence F D compatible c) =
          ∑ c : I.Cell D,
            if c ∈ compatible then
              canonicalWeight F D c /
                recordCompatibleMass F D compatible
            else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        simp [recordConditionedCredence, hmass]
      _ =
          ∑ c ∈ compatible,
            canonicalWeight F D c /
              recordCompatibleMass F D compatible := by
        calc
          (∑ c : I.Cell D,
              if c ∈ compatible then
                canonicalWeight F D c /
                  recordCompatibleMass F D compatible
              else 0) =
              ∑ c ∈ Finset.univ.filter (fun c : I.Cell D => c ∈ compatible),
                canonicalWeight F D c /
                  recordCompatibleMass F D compatible := by
                exact (Finset.sum_filter _ _).symm
          _ = ∑ c ∈ compatible,
                canonicalWeight F D c /
                  recordCompatibleMass F D compatible := by
                congr 1
                ext c
                simp
      _ = recordCompatibleMass F D compatible /
          recordCompatibleMass F D compatible := by
        rw [← Finset.sum_div]
        rfl
      _ = 1 := div_self hmass

theorem recordConditionedCredence_normalized
    (F : RationalExpectationFamily I)
    (D : I.Perspective)
    (compatible : Finset (I.Cell D))
    (hmass :
      recordCompatibleMass F D compatible ≠ 0) :
    (∑ c : I.Cell D,
      recordConditionedCredence F D compatible c) = 1 := by
  simpa [hmass] using
    sum_recordConditionedCredence_eq_zero_or_one
      F D compatible

theorem recordCompatibleMass_univ
    (F : RationalExpectationFamily I)
    (D : I.Perspective)
    (hInj :
      Function.Injective (@I.outcome D)) :
    recordCompatibleMass F D Finset.univ = 1 := by
  unfold recordCompatibleMass
  simpa using canonicalWeight_axNorm F D hInj

theorem recordConditionedCredence_univ
    (F : RationalExpectationFamily I)
    (D : I.Perspective)
    (hInj :
      Function.Injective (@I.outcome D))
    (c : I.Cell D) :
    recordConditionedCredence
        F D Finset.univ c =
      canonicalWeight F D c := by
  rw [recordConditionedCredence]
  rw [recordCompatibleMass_univ F D hInj]
  simp

/-- Fine cells whose parent is compatible with the coarse accessible
record. -/
def pullbackRecordCells
    {fine coarse : I.Perspective}
    (r : I.Refinement fine coarse)
    (compatible : Finset (I.Cell coarse)) :
    Finset (I.Cell fine) :=
  Finset.univ.filter
    (fun i => I.parentCell r i ∈ compatible)

@[simp]
theorem mem_pullbackRecordCells
    {fine coarse : I.Perspective}
    (r : I.Refinement fine coarse)
    (compatible : Finset (I.Cell coarse))
    (i : I.Cell fine) :
    i ∈ pullbackRecordCells r compatible ↔
      I.parentCell r i ∈ compatible := by
  simp [pullbackRecordCells]

private theorem sum_pullbackRecordCells_eq
    {fine coarse : I.Perspective}
    (r : I.Refinement fine coarse)
    (compatible : Finset (I.Cell coarse))
    (w : I.Cell fine → ℝ) :
    (∑ i ∈ pullbackRecordCells r compatible, w i) =
      ∑ j ∈ compatible,
        ∑ i : I.Cell fine,
          if I.parentCell r i = j then w i else 0 := by
  unfold pullbackRecordCells
  rw [Finset.sum_filter, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (if I.parentCell r i ∈ compatible then w i else 0) =
        ∑ j ∈ compatible,
          if I.parentCell r i = j then w i else 0 := by
      symm
      calc
        (∑ j ∈ compatible,
            if I.parentCell r i = j then w i else 0) =
            ∑ j ∈ compatible,
              if j = I.parentCell r i then w i else 0 := by
              apply Finset.sum_congr rfl
              intro j hj
              by_cases hparent : I.parentCell r i = j
              · simp [hparent]
              · have hreverse : ¬ j = I.parentCell r i :=
                  fun h => hparent h.symm
                simp [hparent, hreverse]
        _ = if I.parentCell r i ∈ compatible then w i else 0 := by
              exact Finset.sum_ite_eq' compatible (I.parentCell r i) (fun _ => w i)

theorem recordCompatibleMass_pullback
    (F : RationalExpectationFamily I)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll :
      ∀ D : I.Perspective,
        Function.Injective (@I.outcome D))
    {fine coarse : I.Perspective}
    (r : I.Refinement fine coarse)
    (compatible : Finset (I.Cell coarse)) :
    recordCompatibleMass F fine
        (pullbackRecordCells r compatible) =
      recordCompatibleMass F coarse compatible := by
  unfold recordCompatibleMass
  rw [sum_pullbackRecordCells_eq]
  apply Finset.sum_congr rfl
  intro j hj
  exact (canonicalWeight_grain F hinv hInjAll r j).symm

/-- Record-conditioned self-locating credence is coherent under
refinement: the credence of a coarse compatible alternative equals the
sum of the credences of its fine subdivisions.

This is conditional on the explicit semantic use of canonical weight as
self-locating credence. It formalizes no time or continuator. -/
theorem recordConditionedCredence_refinement_fiber
    (F : RationalExpectationFamily I)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll :
      ∀ D : I.Perspective,
        Function.Injective (@I.outcome D))
    {fine coarse : I.Perspective}
    (r : I.Refinement fine coarse)
    (compatible : Finset (I.Cell coarse))
    (j : I.Cell coarse)
    (hmass :
      recordCompatibleMass F coarse compatible ≠ 0) :
    recordConditionedCredence
        F coarse compatible j =
      ∑ i : I.Cell fine,
        if I.parentCell r i = j then
          recordConditionedCredence
            F fine
            (pullbackRecordCells r compatible)
            i
        else
          0 := by
  have hmass_pullback :
      recordCompatibleMass F fine
          (pullbackRecordCells r compatible) =
        recordCompatibleMass F coarse compatible :=
    recordCompatibleMass_pullback F hinv hInjAll r compatible
  have hmass_fine :
      recordCompatibleMass F fine
          (pullbackRecordCells r compatible) ≠ 0 := by
    rw [hmass_pullback]
    exact hmass
  by_cases hj : j ∈ compatible
  · calc
      recordConditionedCredence F coarse compatible j =
          canonicalWeight F coarse j /
            recordCompatibleMass F coarse compatible := by
        simp [recordConditionedCredence, hmass, hj]
      _ = (∑ i : I.Cell fine,
            if I.parentCell r i = j then canonicalWeight F fine i else 0) /
            recordCompatibleMass F fine (pullbackRecordCells r compatible) := by
        rw [hmass_pullback, ← canonicalWeight_grain F hinv hInjAll r j]
      _ = ∑ i : I.Cell fine,
            if I.parentCell r i = j then
              recordConditionedCredence F fine (pullbackRecordCells r compatible) i
            else 0 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hparent : I.parentCell r i = j
        · have hmem : i ∈ pullbackRecordCells r compatible := by
            simp [hparent, hj]
          simp [hparent, recordConditionedCredence, hmass_fine, hmem]
        · simp [hparent]
  · rw [recordConditionedCredence_zero_of_not_mem F coarse compatible j hj]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hparent : I.parentCell r i = j
    · rw [if_pos hparent]
      apply recordConditionedCredence_zero_of_not_mem
      simp [hparent, hj]
    · simp [hparent]

end
end EverettianProbability.Abstract
