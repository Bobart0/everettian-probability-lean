import QuantumFoundations.Uhlhorn.Assembly

/-!
# Dimension-two witness for the published Uhlhorn interface

This file audits the lower-dimensional boundary of
`QuantumFoundations.Uhlhorn.uhlhorn_finite_dim` without changing the upstream
library. The upstream theorem assumes only one-direction preservation of
orthogonality on `Proj1 n`; injectivity and surjectivity are not premises.

In dimension two every rank-one subspace has a unique rank-one orthogonal
partner. We exploit that pairing to collapse one orthogonal pair onto another
while fixing all remaining lines. The resulting map preserves orthogonality
but is not injective.

The claim is deliberately interface-specific: this is a countermodel to
injectivity following from the weak `PreservesOrthogonality` interface in
`Proj1 2`, not a general formulation of the classical dimension-two
obstruction for every version of Uhlhorn's theorem.
-/

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

private theorem orthogonalProj1Two_injective :
    Function.Injective orthogonalProj1Two := by
  intro P Q hPQ
  calc
    P = orthogonalProj1Two (orthogonalProj1Two P) :=
      (orthogonalProj1Two_involutive P).symm
    _ = orthogonalProj1Two (orthogonalProj1Two Q) :=
      congrArg orthogonalProj1Two hPQ
    _ = Q := orthogonalProj1Two_involutive Q

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
  have h0 := congrFun h (0 : Fin 2)
  norm_num [l2e0] at h0

private theorem l2e0_add_l2e1_ne_zero : l2e0 + l2e1 ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 2)
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
  have h1 := congrFun ha (1 : Fin 2)
  norm_num [l2e0, l2e1,
    show (1 : Fin 2) ≠ (0 : Fin 2) by decide] at h1

private theorem l2A_ne_l2Borth : l2A ≠ l2Borth := by
  intro hABo
  have hsub : (ℂ ∙ l2e0 : Submodule ℂ (H 2)) =
      (ℂ ∙ (l2e0 + l2e1) : Submodule ℂ (H 2))ᗮ := by
    change (l2A : Submodule ℂ (H 2)) =
      (l2B : Submodule ℂ (H 2))ᗮ
    exact congrArg Subtype.val hABo
  have he0orth : l2e0 ∈
      (ℂ ∙ (l2e0 + l2e1) : Submodule ℂ (H 2))ᗮ := by
    rw [← hsub]
    exact Submodule.mem_span_singleton_self l2e0
  have hz := ((ℂ ∙ (l2e0 + l2e1) : Submodule ℂ (H 2)).mem_orthogonal l2e0).mp
      he0orth (l2e0 + l2e1)
      (Submodule.mem_span_singleton_self (l2e0 + l2e1))
  norm_num [l2e0, l2e1,
    show (0 : Fin 2) ≠ (1 : Fin 2) by decide] at hz

private theorem l2B_ne_l2Borth : l2B ≠ l2Borth := by
  unfold l2Borth
  exact (orthogonalProj1Two_ne_self l2B).symm

/-- Collapse the orthogonal pair `B, Bᗮ` onto `A, Aᗮ`, fixing every other
rank-one projection. -/
def l2OrthogonalityCollapse (P : Proj1 2) : Proj1 2 :=
  if P = l2B then l2A
  else if P = l2Borth then l2Aorth
  else P

@[simp]
private theorem l2OrthogonalityCollapse_B :
    l2OrthogonalityCollapse l2B = l2A := by
  simp [l2OrthogonalityCollapse]

@[simp]
private theorem l2OrthogonalityCollapse_Borth :
    l2OrthogonalityCollapse l2Borth = l2Aorth := by
  simp [l2OrthogonalityCollapse, l2B_ne_l2Borth]

@[simp]
private theorem l2OrthogonalityCollapse_A :
    l2OrthogonalityCollapse l2A = l2A := by
  simp [l2OrthogonalityCollapse, l2A_ne_l2B, l2A_ne_l2Borth]

/-- The collapse preserves orthogonality in exactly the one-direction sense of
`QuantumFoundations.Uhlhorn.PreservesOrthogonality`. -/
theorem l2OrthogonalityCollapse_preservesOrthogonality :
    PreservesOrthogonality l2OrthogonalityCollapse := by
  intro P Q hPQ
  have hQorth : Q = orthogonalProj1Two P :=
    proj1Two_eq_orthogonal_of_isOrtho P Q hPQ
  by_cases hPB : P = l2B
  · subst P
    have hQ : Q = l2Borth := by
      simpa [l2Borth] using hQorth
    subst Q
    rw [l2OrthogonalityCollapse_B, l2OrthogonalityCollapse_Borth]
    exact Submodule.isOrtho_orthogonal_right (l2A : Submodule ℂ (H 2))
  · by_cases hPBo : P = l2Borth
    · subst P
      have hQ : Q = l2B := by
        calc
          Q = orthogonalProj1Two l2Borth := hQorth
          _ = l2B := by
            simp [l2Borth]
      subst Q
      rw [l2OrthogonalityCollapse_Borth, l2OrthogonalityCollapse_B]
      exact Submodule.isOrtho_orthogonal_left (l2A : Submodule ℂ (H 2))
    · have hQB : Q ≠ l2B := by
        intro h
        subst Q
        have h := hQorth
        have hh := congrArg orthogonalProj1Two h
        simp [l2Borth] at hh
        exact hPBo hh.symm
      have hQBo : Q ≠ l2Borth := by
        intro h
        subst Q
        have h := hQorth
        have hh := congrArg orthogonalProj1Two h
        simp [l2Borth] at hh
        exact hPB hh.symm
      simp [l2OrthogonalityCollapse, hPB, hPBo, hQB, hQBo]
      exact hPQ

/-- The same map is not injective: both `A` and `B` are sent to `A`. -/
theorem l2OrthogonalityCollapse_not_injective :
    ¬ Function.Injective l2OrthogonalityCollapse := by
  intro hinj
  apply l2A_ne_l2B
  apply hinj
  rw [l2OrthogonalityCollapse_A, l2OrthogonalityCollapse_B]

/-- L2 audit witness: in dimension two, the weak one-direction orthogonality
interface admits a non-injective endomap of rank-one projections. -/
theorem exists_noninjective_preservesOrthogonality_proj1_two :
    ∃ φ : Proj1 2 → Proj1 2,
      PreservesOrthogonality φ ∧ ¬ Function.Injective φ := by
  exact ⟨l2OrthogonalityCollapse,
    l2OrthogonalityCollapse_preservesOrthogonality,
    l2OrthogonalityCollapse_not_injective⟩

#print axioms exists_noninjective_preservesOrthogonality_proj1_two

end

end EverettianProbability.Audit
