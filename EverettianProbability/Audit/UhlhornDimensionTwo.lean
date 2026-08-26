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

end
end EverettianProbability.Audit
