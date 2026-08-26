import QuantumFoundations.Uhlhorn.Assembly

namespace EverettianProbability.Audit

open QuantumFoundations.Uhlhorn
open Gleason
open scoped Classical InnerProductSpace

noncomputable section

/-- Orthogonal complement, bundled again as a rank-one projection in `H 2`. -/
def orthogonalProj1Two (P : Proj1 2) : Proj1 2 :=
  ⟨(P : Submodule ℂ (H 2))ᗮ, by
    have h := Submodule.finrank_add_finrank_orthogonal
      (P : Submodule ℂ (H 2))
    have hP : Module.finrank ℂ (P : Submodule ℂ (H 2)) = 1 := P.2
    have hH : Module.finrank ℂ (H 2) = 2 := by simp
    omega⟩

@[simp]
theorem orthogonalProj1Two_involutive (P : Proj1 2) :
    orthogonalProj1Two (orthogonalProj1Two P) = P := by
  apply Subtype.ext
  simp [orthogonalProj1Two]

private theorem orthogonalProj1Two_ne_self (P : Proj1 2) :
    orthogonalProj1Two P ≠ P := by
  intro h
  have hval : (P : Submodule ℂ (H 2))ᗮ = (P : Submodule ℂ (H 2)) :=
    congrArg Subtype.val h
  have hself : (P : Submodule ℂ (H 2)) ⟂ (P : Submodule ℂ (H 2)) := by
    have horth := Submodule.isOrtho_orthogonal_right
      (P : Submodule ℂ (H 2))
    rwa [hval] at horth
  have hbot : (P : Submodule ℂ (H 2)) = ⊥ :=
    Submodule.isOrtho_self.mp hself
  have hfin := P.2
  rw [hbot] at hfin
  simp at hfin

/-- In `H 2`, orthogonality determines the other rank-one projection uniquely. -/
theorem proj1Two_eq_orthogonal_of_isOrtho (P Q : Proj1 2)
    (hPQ : (P : Submodule ℂ (H 2)) ⟂ (Q : Submodule ℂ (H 2))) :
    Q = orthogonalProj1Two P := by
  apply Subtype.ext
  have hle : (Q : Submodule ℂ (H 2)) ≤
      (P : Submodule ℂ (H 2))ᗮ := hPQ.ge
  apply Submodule.eq_of_le_of_finrank_eq hle
  exact Q.2.trans (orthogonalProj1Two P).2.symm

private def l2e0 : H 2 := EuclideanSpace.single (0 : Fin 2) (1 : ℂ)
private def l2e1 : H 2 := EuclideanSpace.single (1 : Fin 2) (1 : ℂ)

private theorem l2e0_ne_zero : l2e0 ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : H 2 => x (0 : Fin 2)) h
  norm_num [l2e0] at h0

private theorem l2e0_add_l2e1_ne_zero : l2e0 + l2e1 ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : H 2 => x (0 : Fin 2)) h
  norm_num [l2e0, l2e1,
    show (0 : Fin 2) ≠ (1 : Fin 2) by decide] at h0

private def l2A : Proj1 2 :=
  ⟨ℂ ∙ l2e0, finrank_span_singleton l2e0_ne_zero⟩

private def l2B : Proj1 2 :=
  ⟨ℂ ∙ (l2e0 + l2e1), finrank_span_singleton l2e0_add_l2e1_ne_zero⟩

private def l2Aorth : Proj1 2 := orthogonalProj1Two l2A
private def l2Borth : Proj1 2 := orthogonalProj1Two l2B

private theorem l2A_ne_l2B : l2A ≠ l2B := by
  intro hAB
  have hsub : (ℂ ∙ l2e0 : Submodule ℂ (H 2)) =
      ℂ ∙ (l2e0 + l2e1) := congrArg Subtype.val hAB
  have hmem : l2e0 + l2e1 ∈ (ℂ ∙ l2e0 : Submodule ℂ (H 2)) := by
    rw [hsub]
    exact Submodule.mem_span_singleton_self (l2e0 + l2e1)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  have h1 := congrArg (fun x : H 2 => x (1 : Fin 2)) ha
  norm_num [l2e0, l2e1,
    show (1 : Fin 2) ≠ (0 : Fin 2) by decide] at h1

private theorem inner_l2e0_l2e0 :
    ⟪l2e0, l2e0⟫_ℂ = 1 := by
  unfold l2e0
  rw [EuclideanSpace.inner_single_left]
  norm_num

private theorem inner_l2e1_l2e0 :
    ⟪l2e1, l2e0⟫_ℂ = 0 := by
  unfold l2e1 l2e0
  rw [EuclideanSpace.inner_single_left]
  norm_num [show (1 : Fin 2) ≠ (0 : Fin 2) by decide]

private theorem inner_l2e0_add_l2e1_l2e0 :
    ⟪l2e0 + l2e1, l2e0⟫_ℂ = 1 := by
  rw [inner_add_left, inner_l2e0_l2e0, inner_l2e1_l2e0]
  norm_num

private theorem l2A_ne_l2Borth : l2A ≠ l2Borth := by
  intro hABo
  have hval := congrArg Subtype.val hABo
  have hsub : (l2A : Submodule ℂ (H 2)) =
      (l2B : Submodule ℂ (H 2))ᗮ := by
    simpa [l2Borth, orthogonalProj1Two] using hval
  have he0A : l2e0 ∈ (l2A : Submodule ℂ (H 2)) := by
    exact Submodule.mem_span_singleton_self l2e0
  have he0orthB : l2e0 ∈ (l2B : Submodule ℂ (H 2))ᗮ := by
    rw [← hsub]
    exact he0A
  have he0orth : l2e0 ∈
      (ℂ ∙ (l2e0 + l2e1) : Submodule ℂ (H 2))ᗮ := by
    simpa [l2B] using he0orthB
  have hz : ⟪l2e0 + l2e1, l2e0⟫_ℂ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp he0orth
  rw [inner_l2e0_add_l2e1_l2e0] at hz
  norm_num at hz

/-- Collapse one orthogonal pair onto another while respecting complements. -/
private def l2Collapse (P : Proj1 2) : Proj1 2 :=
  if P = l2B then l2A
  else if P = l2Borth then l2Aorth
  else P

private theorem l2Collapse_B : l2Collapse l2B = l2A := by
  simp [l2Collapse]

private theorem l2Collapse_Borth : l2Collapse l2Borth = l2Aorth := by
  have hBoB : l2Borth ≠ l2B := by
    exact orthogonalProj1Two_ne_self l2B
  simp [l2Collapse, hBoB]

private theorem l2Collapse_eq_self {P : Proj1 2}
    (hB : P ≠ l2B) (hBo : P ≠ l2Borth) :
    l2Collapse P = P := by
  simp [l2Collapse, hB, hBo]

private theorem orthogonal_l2Borth :
    orthogonalProj1Two l2Borth = l2B := by
  simp [l2Borth]

private theorem orthogonal_l2Aorth :
    orthogonalProj1Two l2Aorth = l2A := by
  simp [l2Aorth]

private theorem l2Collapse_commutes_orthogonal (P : Proj1 2) :
    l2Collapse (orthogonalProj1Two P) =
      orthogonalProj1Two (l2Collapse P) := by
  by_cases hB : P = l2B
  · subst P
    change l2Collapse l2Borth = orthogonalProj1Two (l2Collapse l2B)
    rw [l2Collapse_Borth, l2Collapse_B]
    rfl
  · by_cases hBo : P = l2Borth
    · subst P
      rw [orthogonal_l2Borth, l2Collapse_B, l2Collapse_Borth,
        orthogonal_l2Aorth]
    · have horth_ne_B : orthogonalProj1Two P ≠ l2B := by
        intro h
        apply hBo
        calc
          P = orthogonalProj1Two (orthogonalProj1Two P) :=
            (orthogonalProj1Two_involutive P).symm
          _ = orthogonalProj1Two l2B := congrArg orthogonalProj1Two h
          _ = l2Borth := rfl
      have horth_ne_Borth : orthogonalProj1Two P ≠ l2Borth := by
        intro h
        apply hB
        calc
          P = orthogonalProj1Two (orthogonalProj1Two P) :=
            (orthogonalProj1Two_involutive P).symm
          _ = orthogonalProj1Two l2Borth := congrArg orthogonalProj1Two h
          _ = l2B := orthogonal_l2Borth
      rw [l2Collapse_eq_self horth_ne_B horth_ne_Borth,
        l2Collapse_eq_self hB hBo]

private theorem l2Collapse_preservesOrthogonality :
    PreservesOrthogonality l2Collapse := by
  intro P Q hPQ
  have hQ : Q = orthogonalProj1Two P :=
    proj1Two_eq_orthogonal_of_isOrtho P Q hPQ
  subst Q
  change (l2Collapse P : Submodule ℂ (H 2)) ⟂
    (l2Collapse (orthogonalProj1Two P) : Submodule ℂ (H 2))
  rw [l2Collapse_commutes_orthogonal]
  exact Submodule.isOrtho_orthogonal_right
    (l2Collapse P : Submodule ℂ (H 2))

private theorem l2Collapse_not_injective :
    ¬ Function.Injective l2Collapse := by
  intro hinj
  apply l2A_ne_l2B
  apply hinj
  rw [l2Collapse_eq_self l2A_ne_l2B l2A_ne_l2Borth,
    l2Collapse_B]

/--
In dimension two, one-way preservation of orthogonality does not force
injectivity: an orthogonal pair can be collapsed onto a distinct orthogonal
pair while commuting with orthogonal complementation.
-/
theorem dimensionTwo_orthogonality_not_injective :
    ∃ φ : Proj1 2 → Proj1 2,
      PreservesOrthogonality φ ∧ ¬ Function.Injective φ := by
  exact ⟨l2Collapse, l2Collapse_preservesOrthogonality,
    l2Collapse_not_injective⟩

end
end EverettianProbability.Audit
