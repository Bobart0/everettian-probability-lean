import EverettianProbability.Preference.ExpectationFunctional

/-!
# L3 formulation-minimality audit

Two interface simplifications that were previously stated only in prose are
made kernel-checkable here.

* Under Grain coherence, normalization on every perspective is equivalent to
  one scalar normalization equation on the singleton-top perspective (for
  nonzero ambient dimension).
* For a raw valuation satisfying the released affine law, normalization on
  every constant act is equivalent to normalization only at constants `0`
  and `1`.

The second statement is deliberately formulated before bundling into
`RationalExpectationFamily`: otherwise `normalized_const` would already be a
constitutive field of the input type and the reduction would be circular as an
interface audit.
-/

namespace EverettianProbability.Audit

open QuantumFoundations.BornRule
open Gleason
open EverettianProbability.Core
open scoped Classical InnerProductSpace

noncomputable section

/-- The one-cell perspective `{⊤}` in every nonzero finite dimension. -/
def singletonTopPerspective (n : ℕ) (hn : 0 < n) : Perspective n where
  cells := {⊤}
  nz := by
    intro c hc
    simp only [Finset.mem_singleton] at hc
    subst c
    intro htopbot
    let i : Fin n := ⟨0, hn⟩
    let e : H n := EuclideanSpace.single i (1 : ℂ)
    have heTop : e ∈ (⊤ : Submodule ℂ (H n)) := by trivial
    have heBot : e ∈ (⊥ : Submodule ℂ (H n)) := by
      rw [← htopbot]
      exact heTop
    have heZero : e = 0 := by simpa using heBot
    have hcoord := congrArg (fun x : H n => x i) heZero
    simp [e] at hcoord
  ortho := by
    intro c hc c' hc' hne
    simp only [Finset.mem_singleton] at hc hc'
    subst c
    subst c'
    exact (hne rfl).elim
  span := by
    simp

@[simp]
theorem top_mem_singletonTopPerspective (n : ℕ) (hn : 0 < n) :
    (⊤ : Submodule ℂ (H n)) ∈ (singletonTopPerspective n hn).cells := by
  simp [singletonTopPerspective]

/-- Under Grain coherence, normalization on every perspective reduces to the
single scalar equation on the singleton-top perspective. -/
theorem axNorm_iff_singletonTop_of_axGrain {n : ℕ} (hn : 0 < n)
    (Est : Perspective n → Submodule ℂ (H n) → ℝ)
    (hGrain : AxGrain Est) :
    AxNorm Est ↔ Est (singletonTopPerspective n hn) ⊤ = 1 := by
  constructor
  · intro hNorm
    have h := hNorm (singletonTopPerspective n hn)
    change (∑ c ∈ ({⊤} : Finset (Submodule ℂ (H n))),
      Est (singletonTopPerspective n hn) c) = 1 at h
    simpa using h
  · intro hTop D
    have hRef : Refines D (singletonTopPerspective n hn) := by
      intro c hc
      exact ⟨⊤, top_mem_singletonTopPerspective n hn, le_top⟩
    have h := hGrain D (singletonTopPerspective n hn) hRef
      ⊤ (top_mem_singletonTopPerspective n hn)
    have hfilter :
        D.cells.filter (· ≤ (⊤ : Submodule ℂ (H n))) = D.cells := by
      ext c
      simp
    rw [hfilter] at h
    calc
      (∑ c ∈ D.cells, Est D c) =
          Est (singletonTopPerspective n hn) ⊤ := h.symm
      _ = 1 := hTop

/-- For an affine raw valuation, normalization on all constant acts is
completely determined by the constants `0` and `1`. -/
theorem normalizedConst_iff_zero_one_of_affine {n : ℕ}
    (V : Perspective n → Act n → ℝ)
    (hAffine : ∀ (D : Perspective n) (t : ℝ) (a b : Act n),
      V D (fun c => t * a c + (1 - t) * b c) =
        t * V D a + (1 - t) * V D b) :
    (∀ (D : Perspective n) (k : ℝ), V D (Act.const k) = k) ↔
      ((∀ D : Perspective n, V D (Act.const 0) = 0) ∧
       (∀ D : Perspective n, V D (Act.const 1) = 1)) := by
  constructor
  · intro hNorm
    exact ⟨fun D => hNorm D 0, fun D => hNorm D 1⟩
  · rintro ⟨hZero, hOne⟩ D k
    have h := hAffine D k (Act.const 1) (Act.const 0)
    rw [hOne D, hZero D] at h
    simpa [Act.const] using h

end
end EverettianProbability.Audit
