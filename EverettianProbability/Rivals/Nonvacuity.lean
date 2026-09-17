import EverettianProbability.Rivals.BornAgreement
import EverettianProbability.Refinement.GlobalPayoffVacuity

/-!
**FR.** # Non-vacuité — `Rivals`

Témoin concret : le comptage naïf satisfait bien `AxPos` (positivité), pour
tout `n` — c'est une règle rivale légitime au sens où elle satisfait *une
partie* des axiomes de cohérence, ce qui la rend intéressante à réfuter
précisément (elle échoue sur `AxGrain`, pas trivialement sur `AxPos`).
Preuve complète, aucun but ouvert.

**EN.** # Nonvacuity — `Rivals`

Concrete witness: naive counting does satisfy `AxPos` (positivity), for
every `n` — it is a legitimate rival rule in the sense that it satisfies
*some* of the coherence axioms, which is what makes it interesting to
refute precisely (it fails on `AxGrain`, not trivially on `AxPos`). Full
proof, no goal left open.
-/

namespace EverettianProbability.Rivals

open QuantumFoundations.BornRule Gleason
open QuantumFoundations.ProbabilityAPI
open EverettianProbability.PhysicalRefinement
open scoped Classical

variable {n : ℕ}

theorem naiveCounting_axPos : AxPos (naiveCounting n) := by
  intro D c _
  unfold naiveCounting
  exact div_nonneg zero_le_one (Nat.cast_nonneg _)

noncomputable def agreementPerspective : Perspective 3 :=
  EverettianProbability.Refinement.singletonTopPerspective (by norm_num)

theorem renormalizedFourthPower_agreement_witness :
    ∀ c ∈ agreementPerspective.cells,
      renormalizedFourthPower psiBefore agreementPerspective c =
        bornWeight psiBefore agreementPerspective c := by
  apply (renormalizedFourthPower_agrees_iff psiBefore_norm agreementPerspective).mpr
  intro c₁ hc₁ c₂ hc₂ hne₁ hne₂
  simp only [agreementPerspective,
    EverettianProbability.Refinement.singletonTopPerspective,
    Finset.mem_singleton] at hc₁ hc₂
  subst c₁
  subst c₂
  rfl

theorem renormalizedFourthPower_disagreement_witness :
    renormalizedFourthPower psiAfter coarsePerspective label0Line = (81 / 337 : ℝ) ∧
      bornWeight psiAfter coarsePerspective label0Line = (9 / 25 : ℝ) ∧
      renormalizedFourthPower psiAfter coarsePerspective label0Line -
          bornWeight psiAfter coarsePerspective label0Line = (-1008 / 8425 : ℝ) := by
  have hlabel0_fourth : ‖projL label0Line psiAfter‖ ^ 4 = (81 / 625 : ℝ) := by
    calc
      ‖projL label0Line psiAfter‖ ^ 4 =
          (‖projL label0Line psiAfter‖ ^ 2) ^ 2 := by ring
      _ = (9 / 25 : ℝ) ^ 2 := by rw [weight_label0_after]
      _ = 81 / 625 := by norm_num
  have hlabel1_fourth : ‖projL label1Space psiAfter‖ ^ 4 = (256 / 625 : ℝ) := by
    calc
      ‖projL label1Space psiAfter‖ ^ 4 =
          (‖projL label1Space psiAfter‖ ^ 2) ^ 2 := by ring
      _ = (16 / 25 : ℝ) ^ 2 := by rw [weight_label1Space_after]
      _ = 256 / 625 := by norm_num
  have hden : fourthPowerDenominator psiAfter coarsePerspective = (337 / 625 : ℝ) := by
    unfold fourthPowerDenominator
    rw [coarsePerspective_cells_eq,
      Finset.sum_insert (by simpa using label0Line_ne_label1Space),
      Finset.sum_singleton, hlabel0_fourth, hlabel1_fourth]
    norm_num
  have hrenorm :
      renormalizedFourthPower psiAfter coarsePerspective label0Line = (81 / 337 : ℝ) := by
    unfold renormalizedFourthPower
    rw [hden, hlabel0_fourth]
    norm_num
  have hborn : bornWeight psiAfter coarsePerspective label0Line = (9 / 25 : ℝ) := by
    unfold bornWeight
    exact weight_label0_after
  refine ⟨hrenorm, hborn, ?_⟩
  rw [hrenorm, hborn]
  norm_num

end EverettianProbability.Rivals
