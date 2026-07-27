import QuantumFoundations.ProbabilityAPI

/-!
**FR.** # Cellules de fréquence par poids de Hamming — noyau P10

Une configuration de `R` répétitions binaires est une fonction
`Fin R → Fin 2`. Son poids de Hamming est le nombre de sites portant la
valeur `1`. Pour chaque entier `k`, `frequencySitesCell R k` est le
sous-espace engendré par les configurations de poids `k`; `frequencyCell`
est son transport vers `H (2 ^ R)`.

Ce module est purement structurel. Il ne définit aucun état i.i.d., aucune
mesure de Born sur les fréquences, aucune typicalité et aucune loi des
grands nombres.

**EN.** # Hamming-weight frequency cells — P10 kernel

A configuration of `R` binary repetitions is a function `Fin R → Fin 2`.
Its Hamming weight is the number of sites carrying value `1`. For each
integer `k`, `frequencySitesCell R k` is the subspace spanned by
configurations of weight `k`; `frequencyCell` transports it to `H (2 ^ R)`.

This module is purely structural. It defines no i.i.d. state, Born measure
over frequencies, typicality statement, or law of large numbers.
-/

namespace EverettianProbability.Frequency

open QuantumFoundations.ProbabilityAPI
open QuantumFoundations.ProbabilityAPI.Repetition
open scoped Classical InnerProductSpace

noncomputable section

/-- Number of sites whose value is `1`. -/
def hammingWeight {R : ℕ} (g : Fin R → Fin 2) : ℕ :=
  (Finset.univ.filter (fun r => g r = 1)).card

/-- Span, in the site representation, of configurations having Hamming
weight `k`. -/
def frequencySitesCell (R k : ℕ) : Submodule ℂ (Sites R 2) :=
  Submodule.span ℂ
    (configurationBasis '' {g : Fin R → Fin 2 | hammingWeight g = k})

theorem configurationBasis_mem_frequencySitesCell {R : ℕ}
    (g : Fin R → Fin 2) :
    configurationBasis g ∈ frequencySitesCell R (hammingWeight g) :=
  Submodule.subset_span ⟨g, rfl, rfl⟩

theorem frequencySitesCell_ortho {R k l : ℕ} (hkl : k ≠ l) :
    frequencySitesCell R k ⟂ frequencySitesCell R l := by
  unfold frequencySitesCell
  rw [Submodule.isOrtho_span]
  rintro u ⟨g, hg, rfl⟩ v ⟨h, hh, rfl⟩
  have hgh : g ≠ h := by
    intro e
    apply hkl
    calc
      k = hammingWeight g := hg.symm
      _ = hammingWeight h := congrArg (fun x => hammingWeight x) e
      _ = l := hh
  unfold configurationBasis
  rw [EuclideanSpace.inner_single_left]
  simp [hgh.symm]

/-- Frequency cell transported to the standard Hilbert model. -/
def frequencyCell (R k : ℕ) : Submodule ℂ (H (2 ^ R)) :=
  (frequencySitesCell R k).map
    (sitesEquivR R).symm.toLinearEquiv.toLinearMap

/-- Computational configuration branch, reconstructed only from exported
ProbabilityAPI primitives. -/
def configurationBranch (R : ℕ) (g : Fin R → Fin 2) : H (2 ^ R) :=
  (sitesEquivR R).symm (configurationBasis g)

theorem configurationBranch_norm (R : ℕ) (g : Fin R → Fin 2) :
    ‖configurationBranch R g‖ = 1 := by
  simp [configurationBranch, configurationBasis]

theorem configurationBranch_ne_zero (R : ℕ) (g : Fin R → Fin 2) :
    configurationBranch R g ≠ 0 :=
  ne_zero_of_norm_ne_zero (by
    rw [configurationBranch_norm]
    norm_num)

theorem configurationBranch_inner_eq_zero_of_ne
    {R : ℕ} {g h : Fin R → Fin 2} (hgh : g ≠ h) :
    ⟪configurationBranch R g, configurationBranch R h⟫_ℂ = 0 := by
  simp [configurationBranch, configurationBasis,
    EuclideanSpace.inner_single_left, hgh]

theorem configurationBranch_mem_frequencyCell
    {R : ℕ} (g : Fin R → Fin 2) :
    configurationBranch R g ∈ frequencyCell R (hammingWeight g) := by
  refine ⟨configurationBasis g,
    configurationBasis_mem_frequencySitesCell g, ?_⟩
  rfl

theorem frequencyCell_ortho {R k l : ℕ} (hkl : k ≠ l) :
    frequencyCell R k ⟂ frequencyCell R l := by
  exact (frequencySitesCell_ortho hkl).map
    (sitesEquivR R).symm.toLinearIsometry

end
end EverettianProbability.Frequency
