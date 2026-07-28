import EverettianProbability.SelfLocation.RecordRestrictionIndifference

/-!
**FR.** # Concurrent uniforme de la crédence auto-localisante

Ce module construit une famille rivale attribuant une crédence uniforme aux
cellules compatibles avec un record accessible. Elle satisfait la positivité,
le support, la normalisation sur tout ensemble compatible non vide et
l'invariance des cotes relatives sous élimination d'autres alternatives.

Elle ne s'accorde toutefois pas avec le poids canonique sur le record
universel lorsque les poids canoniques sont non uniformes. La normalisation et
l'indifférence à l'élimination d'alternatives ne suffisent donc pas, à elles
seules, à sélectionner la crédence bornienne : l'accord initial avec le poids
canonique est une prémisse sémantique supplémentaire et substantielle.

Ce résultat ne défend ni ne réfute à lui seul l'interprétation épistémique de
Born. Il rend explicite la structure logique de l'argument.

**EN.** # Uniform rival to self-locating credence

This module constructs a rival family assigning uniform credence to the cells
compatible with an accessible record. It satisfies positivity, support,
normalization on every nonempty compatible set, and invariance of relative
odds under elimination of other alternatives.

It nevertheless fails to agree with canonical weight on the unrestricted
record whenever canonical weights are nonuniform. Normalization and
indifference to eliminating alternatives therefore do not by themselves select
Born credence: initial agreement with canonical weight is an additional
substantive semantic premise.

This result neither defends nor refutes the epistemic interpretation of Born
by itself. It makes the logical structure of the argument explicit.
-/

namespace EverettianProbability.Abstract

open scoped BigOperators Classical

noncomputable section

variable {I : PerspectiveInterface}

/-- Credence family assigning equal weight to every record-compatible cell
and zero to every incompatible cell.

The value is total and equals zero when the compatible set is empty. -/
def uniformRecordCredenceFamily
    (I : PerspectiveInterface) :
    RecordCredenceFamily I where
  credence :=
    fun D compatible c =>
      if compatible.card = 0 then
        0
      else if c ∈ compatible then
        1 / (compatible.card : ℝ)
      else
        0
  zero_of_not_mem := by
    intro D compatible c hc
    simp [hc]
  nonneg := by
    intro D compatible c
    by_cases hcard : compatible.card = 0
    · simp [hcard]
    · by_cases hc : c ∈ compatible
      · simp only [hcard, hc, if_false, if_true]
        exact div_nonneg zero_le_one (Nat.cast_nonneg _)
      · simp [hcard, hc]

@[simp]
theorem uniformRecordCredenceFamily_credence
    (D : I.Perspective)
    (compatible : Finset (I.Cell D))
    (c : I.Cell D) :
    (uniformRecordCredenceFamily I).credence D compatible c =
      if compatible.card = 0 then
        0
      else if c ∈ compatible then
        1 / (compatible.card : ℝ)
      else
        0 := by
  rfl

/-- All cells compatible with the same record receive equal uniform
credence. -/
theorem uniformRecordCredenceFamily_equal_on_compatible
    (D : I.Perspective)
    (compatible : Finset (I.Cell D))
    (c d : I.Cell D)
    (hc : c ∈ compatible)
    (hd : d ∈ compatible) :
    (uniformRecordCredenceFamily I).credence D compatible c =
      (uniformRecordCredenceFamily I).credence D compatible d := by
  have hcard : compatible.card ≠ 0 :=
    Finset.card_ne_zero.mpr ⟨c, hc⟩
  simp only [uniformRecordCredenceFamily_credence, hcard, if_false,
    hc, hd, if_true]

private theorem sum_uniformRecordCredenceFamily_eq_sum_compatible
    (D : I.Perspective)
    (compatible : Finset (I.Cell D)) :
    (∑ c : I.Cell D,
      (uniformRecordCredenceFamily I).credence D compatible c) =
      ∑ c ∈ compatible,
        (uniformRecordCredenceFamily I).credence D compatible c := by
  calc
    (∑ c : I.Cell D,
      (uniformRecordCredenceFamily I).credence D compatible c) =
        ∑ c : I.Cell D,
          if c ∈ compatible then
            (uniformRecordCredenceFamily I).credence D compatible c
          else 0 := by
            apply Finset.sum_congr rfl
            intro c hc
            by_cases hmem : c ∈ compatible
            · simp [hmem]
            · rw [(uniformRecordCredenceFamily I).zero_of_not_mem D compatible c hmem]
              simp [hmem]
    _ = ∑ c ∈ Finset.univ.filter (fun c => c ∈ compatible),
          (uniformRecordCredenceFamily I).credence D compatible c := by
          rw [Finset.sum_filter]
    _ = ∑ c ∈ compatible,
          (uniformRecordCredenceFamily I).credence D compatible c := by
          congr 1
          ext c
          simp

/-- Uniform credence sums to one on every nonempty compatible set. -/
theorem sum_uniformRecordCredenceFamily_eq_one_of_nonempty
    (D : I.Perspective)
    (compatible : Finset (I.Cell D))
    (hnonempty : compatible.Nonempty) :
    (∑ c : I.Cell D,
      (uniformRecordCredenceFamily I).credence D compatible c) = 1 := by
  have hcard : compatible.card ≠ 0 :=
    Finset.card_ne_zero.mpr hnonempty
  rw [sum_uniformRecordCredenceFamily_eq_sum_compatible D compatible]
  calc
    (∑ c ∈ compatible,
      (uniformRecordCredenceFamily I).credence D compatible c) =
        ∑ _c ∈ compatible, 1 / (compatible.card : ℝ) := by
          apply Finset.sum_congr rfl
          intro c hc
          simp only [uniformRecordCredenceFamily_credence, hcard, if_false,
            hc, if_true]
    _ = compatible.card • (1 / (compatible.card : ℝ)) := by
          rw [Finset.sum_const]
    _ = 1 := by
          rw [nsmul_eq_mul]
          field_simp [Nat.cast_ne_zero.mpr hcard]

theorem uniformRecordCredenceFamily_normalized
    (F : RationalExpectationFamily I) :
    (uniformRecordCredenceFamily I).NormalizedOnNonzeroMass F := by
  intro D compatible hmass
  have hnonempty : compatible.Nonempty := by
    by_contra h
    have hempty : compatible = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp h
    subst compatible
    simp [recordCompatibleMass] at hmass
  exact
    sum_uniformRecordCredenceFamily_eq_one_of_nonempty
      D compatible hnonempty

/-- Uniform credence satisfies record-restriction odds invariance.

This does not imply canonical agreement. -/
theorem uniformRecordCredenceFamily_oddsInvariantUnderRecordRestriction
    (F : RationalExpectationFamily I) :
    (uniformRecordCredenceFamily I).OddsInvariantUnderRecordRestriction F := by
  intro D smaller larger hsubset hsmaller hlarger c d hc hd
  have hc_large : c ∈ larger :=
    hsubset hc
  have hd_large : d ∈ larger :=
    hsubset hd
  have hsmall_card : smaller.card ≠ 0 :=
    Finset.card_ne_zero.mpr ⟨c, hc⟩
  have hlarge_card : larger.card ≠ 0 :=
    Finset.card_ne_zero.mpr ⟨c, hc_large⟩
  simp [uniformRecordCredenceFamily, hc, hd, hc_large, hd_large]

/-- Uniform credence cannot agree with canonical weight on an unrestricted
record containing two cells with distinct canonical weights. -/
theorem uniformRecordCredenceFamily_not_agrees_unrestricted_of_canonicalWeight_ne
    (F : RationalExpectationFamily I)
    (D : I.Perspective)
    (hInj :
      Function.Injective (@I.outcome D))
    (c d : I.Cell D)
    (hweights :
      canonicalWeight F D c ≠
        canonicalWeight F D d) :
    ¬ (uniformRecordCredenceFamily I).AgreesOnUnrestrictedRecord F := by
  intro hagree
  have hc := hagree D hInj c
  have hd := hagree D hInj d
  have huniform :
      (uniformRecordCredenceFamily I).credence D Finset.univ c =
        (uniformRecordCredenceFamily I).credence D Finset.univ d := by
    exact
      uniformRecordCredenceFamily_equal_on_compatible
        D Finset.univ c d
        (Finset.mem_univ c)
        (Finset.mem_univ d)
  apply hweights
  calc
    canonicalWeight F D c =
        (uniformRecordCredenceFamily I).credence D Finset.univ c := hc.symm
    _ =
        (uniformRecordCredenceFamily I).credence D Finset.univ d := huniform
    _ = canonicalWeight F D d := hd

/-- Normalization and odds invariance under record restriction do not imply
unrestricted canonical agreement whenever canonical weights are nonuniform.

The uniform family is an explicit counterexample. -/
theorem normalized_and_oddsInvariant_do_not_imply_agrees_unrestricted
    (F : RationalExpectationFamily I)
    (D : I.Perspective)
    (hInj :
      Function.Injective (@I.outcome D))
    (c d : I.Cell D)
    (hweights :
      canonicalWeight F D c ≠
        canonicalWeight F D d) :
    ∃ C : RecordCredenceFamily I,
      C.NormalizedOnNonzeroMass F ∧
      C.OddsInvariantUnderRecordRestriction F ∧
      ¬ C.AgreesOnUnrestrictedRecord F := by
  refine ⟨uniformRecordCredenceFamily I, ?_, ?_, ?_⟩
  · exact uniformRecordCredenceFamily_normalized F
  · exact uniformRecordCredenceFamily_oddsInvariantUnderRecordRestriction F
  · exact
      uniformRecordCredenceFamily_not_agrees_unrestricted_of_canonicalWeight_ne
        F D hInj c d hweights

/-- The primitive characterization theorem genuinely needs unrestricted
canonical agreement: normalization and restriction odds invariance alone admit
the uniform rival. -/
theorem unrestricted_agreement_is_independent_of_normalization_and_oddsInvariant
    (F : RationalExpectationFamily I)
    (D : I.Perspective)
    (hInj :
      Function.Injective (@I.outcome D))
    (c d : I.Cell D)
    (hweights :
      canonicalWeight F D c ≠
        canonicalWeight F D d) :
    ¬ ∀ C : RecordCredenceFamily I,
        C.NormalizedOnNonzeroMass F →
        C.OddsInvariantUnderRecordRestriction F →
        C.AgreesOnUnrestrictedRecord F := by
  intro hall
  have hagree :=
    hall
      (uniformRecordCredenceFamily I)
      (uniformRecordCredenceFamily_normalized F)
      (uniformRecordCredenceFamily_oddsInvariantUnderRecordRestriction F)
  exact
    uniformRecordCredenceFamily_not_agrees_unrestricted_of_canonicalWeight_ne
      F D hInj c d hweights hagree

end
end EverettianProbability.Abstract
