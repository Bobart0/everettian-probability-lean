import EverettianProbability.PhysicalRefinement.RecordNeutralWitness

/-!
**FR.** # Non-trivialité — `PhysicalRefinement`

Témoin négatif concret : le comptage uniforme *restreint aux cellules
actives* (celles de poids bornien non nul — un comptage sur toutes les
cellules de la perspective fine serait aveugle à ce témoin, car
`finePerspective` a trois cellules avant comme après le couplage) donne des
verdicts différents avant et après un raffinement record-neutre, bien que le
record accessible soit inchangé. Le comptage exige donc une information —
laquelle des cellules d'ancilla est effectivement peuplée — dont
`AncillaNotInRecordAlgebra` prive précisément l'agent.

**EN.** # Nontriviality — `PhysicalRefinement`

Concrete negative witness: uniform counting *restricted to active cells*
(those with nonzero Born weight — counting over all cells of the fine
perspective would be blind to this witness, since `finePerspective` has
three cells both before and after the coupling) gives different verdicts
before and after a record-neutral refinement, even though the accessible
record is unchanged. Counting therefore requires information — which
ancilla cell is actually populated — that `AncillaNotInRecordAlgebra`
precisely denies the agent.
-/

namespace EverettianProbability.PhysicalRefinement

open QuantumFoundations.ProbabilityAPI EverettianProbability.Core EverettianProbability.Refinement
open scoped Classical InnerProductSpace

/-- Cells of `D` on which the state `x` has nonzero Born weight — the
branches actually accessible to a counting rule, as opposed to every cell
`D` happens to distinguish. -/
noncomputable def activeCells (D : Perspective 3) (x : H 3) : Finset (Submodule ℂ (H 3)) :=
  D.cells.filter (fun c => projL c x ≠ 0)

/-- Naive rival rule restricted to active cells: uniform credence over the
branches with nonzero Born weight. -/
noncomputable def uniformCredence (D : Perspective 3) (x : H 3) : ℝ :=
  1 / (activeCells D x).card

theorem projL_ne_zero_of_weight_ne_zero {c : Submodule ℂ (H 3)} {x : H 3}
    (h : ‖projL c x‖ ^ 2 ≠ 0) : projL c x ≠ 0 := by
  intro he; apply h; rw [he]; simp

theorem projL_eq_zero_of_weight_eq_zero {c : Submodule ℂ (H 3)} {x : H 3}
    (h : ‖projL c x‖ ^ 2 = 0) : projL c x = 0 := by
  have h2 : ‖projL c x‖ = 0 := by nlinarith [norm_nonneg (projL c x), sq_nonneg (‖projL c x‖)]
  exact norm_eq_zero.mp h2

theorem activeCells_fine_before :
    activeCells finePerspective psiBefore = {label0Line, anc0Line} := by
  apply Finset.ext
  intro x
  unfold activeCells
  rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hxmem, hxne⟩
    unfold finePerspective QuantumFoundations.BornRule.basisPerspective at hxmem
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hxmem
    obtain ⟨i, rfl⟩ := hxmem
    fin_cases i
    · left; rfl
    · right; rfl
    · exfalso; apply hxne
      exact projL_eq_zero_of_weight_eq_zero weight_anc1_before
  · rintro (rfl | rfl)
    · exact ⟨label0Line_mem_fine,
        projL_ne_zero_of_weight_ne_zero (by rw [weight_label0_before]; norm_num)⟩
    · exact ⟨anc0Line_mem_fine,
        projL_ne_zero_of_weight_ne_zero (by rw [weight_anc0_before]; norm_num)⟩

theorem activeCells_fine_after :
    activeCells finePerspective psiAfter = {label0Line, anc0Line, anc1Line} := by
  apply Finset.ext
  intro x
  unfold activeCells
  rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hxmem, _⟩
    unfold finePerspective QuantumFoundations.BornRule.basisPerspective at hxmem
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hxmem
    obtain ⟨i, rfl⟩ := hxmem
    fin_cases i
    · left; rfl
    · right; left; rfl
    · right; right; rfl
  · rintro (rfl | rfl | rfl)
    · exact ⟨label0Line_mem_fine,
        projL_ne_zero_of_weight_ne_zero (by rw [weight_label0_after]; norm_num)⟩
    · exact ⟨anc0Line_mem_fine,
        projL_ne_zero_of_weight_ne_zero (by rw [weight_anc0_after]; norm_num)⟩
    · exact ⟨anc1Line_mem_fine,
        projL_ne_zero_of_weight_ne_zero (by rw [weight_anc1_after]; norm_num)⟩

theorem activeCells_fine_before_card : (activeCells finePerspective psiBefore).card = 2 := by
  rw [activeCells_fine_before,
    Finset.card_insert_of_notMem (by simpa using label0Line_ne_anc0Line), Finset.card_singleton]

theorem anc0Line_ne_anc1Line : anc0Line ≠ anc1Line := by
  intro h
  have hmem : (b 1 : H 3) ∈ anc1Line := h ▸ Submodule.mem_span_singleton_self _
  unfold anc1Line at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have h12 : (⟪(b 2 : H 3), (b 1 : H 3)⟫_ℂ) = 0 := by
    have h21 : (⟪(b 1 : H 3), (b 2 : H 3)⟫_ℂ) = 0 := b.orthonormal.2 (by decide)
    rw [← inner_conj_symm, h21]; simp
  have h22 : (⟪(b 2 : H 3), (b 2 : H 3)⟫_ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast; rw [b2_unit]; norm_num
  rw [← hc, inner_smul_right, h22, mul_one] at h12
  have hb1 : (b 1 : H 3) = 0 := by rw [← hc, h12, zero_smul]
  have : ‖(b 1 : H 3)‖ = 0 := by rw [hb1]; simp
  rw [b1_unit] at this
  norm_num at this

theorem activeCells_fine_after_card : (activeCells finePerspective psiAfter).card = 3 := by
  rw [activeCells_fine_after, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem
    (by simpa using anc0Line_ne_anc1Line), Finset.card_singleton]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  push_neg
  exact ⟨label0Line_ne_anc0Line, label0Line_ne_anc1Line⟩

/-- **FR.** Le comptage sur les branches actives distingue avant et après le
couplage (`1/2 ≠ 1/3`), alors que le record accessible ne change pas
(`recordNeutral_record_eq`). Contrairement à `naiveCounting`
(`Rivals/NaiveBranchCounting.lean`, qui compte toutes les cellules d'une
perspective fixe), ce témoin isole l'effet du raffinement lui-même : c'est le
nombre de branches actives, pas le nombre de cellules distinguées par la
perspective, qui varie.

**EN.** Counting over active branches discriminates before and after the
coupling (`1/2 ≠ 1/3`), even though the accessible record is unchanged
(`recordNeutral_record_eq`). Unlike `naiveCounting`
(`Rivals/NaiveBranchCounting.lean`, which counts every cell of a fixed
perspective), this witness isolates the effect of the refinement itself: it
is the number of *active* branches, not the number of cells the perspective
distinguishes, that changes. -/
theorem counting_sensitive_to_recordNeutral_refinement :
    uniformCredence finePerspective psiBefore ≠ uniformCredence finePerspective psiAfter := by
  unfold uniformCredence
  rw [activeCells_fine_before_card, activeCells_fine_after_card]
  norm_num

/-- **FR.** Forme existentielle demandée : deux états `u`, `w` (ici
`psiBefore` et `w = coupleU u = psiAfter`) au même record accessible, mais à
des verdicts de comptage actif différents. Le reste découle de
`recordNeutral_record_eq`.

**EN.** Requested existential form: two states `u`, `w` (here `psiBefore`
and `w = coupleU u = psiAfter`) with the same accessible record, but
different active-counting verdicts. The rest follows from
`recordNeutral_record_eq`. -/
theorem counting_underdetermined_by_accessible_record :
    ∃ u w : H 3, accessibleRecord u = accessibleRecord w ∧
      uniformCredence finePerspective u ≠ uniformCredence finePerspective w :=
  ⟨psiBefore, psiAfter, recordNeutral_record_eq, counting_sensitive_to_recordNeutral_refinement⟩

end EverettianProbability.PhysicalRefinement
