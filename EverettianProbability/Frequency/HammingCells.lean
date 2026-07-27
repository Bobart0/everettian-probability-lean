import Mathlib.Data.Fintype.Fin
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

/-- **FR.** Les sous-espaces de poids de Hamming couvrent tout l'espace des
configurations par sites. L'index est ici `ℕ`; les indices supérieurs à `R`
seront éliminés dans un sous-jalon ultérieur.

**EN.** The Hamming-weight subspaces cover the whole site-configuration
space. The index is currently `ℕ`; indices greater than `R` will be
eliminated in a later sub-milestone. -/
theorem frequencySitesCell_iSup (R : ℕ) :
    (⨆ k : ℕ, frequencySitesCell R k) = ⊤ := by
  apply top_unique
  have hspan :
      Submodule.span ℂ (Set.range (configurationBasis :
        (Fin R → Fin 2) → Sites R 2)) = ⊤ := by
    have heq :
        (configurationBasis :
          (Fin R → Fin 2) → Sites R 2) =
          ⇑(EuclideanSpace.basisFun (Fin R → Fin 2) ℂ).toBasis := by
      funext g
      rw [OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_apply]
      rfl
    rw [heq]
    exact (EuclideanSpace.basisFun
      (Fin R → Fin 2) ℂ).toBasis.span_eq
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro x ⟨g, rfl⟩
  exact
    (le_iSup (fun k : ℕ => frequencySitesCell R k)
      (hammingWeight g))
      (configurationBasis_mem_frequencySitesCell g)

/-- **FR.** Après transport par `sitesEquivR`, les cellules de fréquence
couvrent tout l'espace standard `H (2 ^ R)`.

**EN.** After transport along `sitesEquivR`, the frequency cells cover the
whole standard space `H (2 ^ R)`. -/
theorem frequencyCell_iSup (R : ℕ) :
    (⨆ k : ℕ, frequencyCell R k) = ⊤ := by
  unfold frequencyCell
  rw [← Submodule.map_iSup, frequencySitesCell_iSup]
  rw [Submodule.map_top,
    LinearMap.range_eq_top.mpr (sitesEquivR R).symm.surjective]

/-- **FR.** Le poids de Hamming d'une configuration de `R` sites est au
plus `R`.

**EN.** The Hamming weight of a configuration on `R` sites is at most
`R`. -/
theorem hammingWeight_le {R : ℕ} (g : Fin R → Fin 2) :
    hammingWeight g ≤ R := by
  unfold hammingWeight
  have hsub :
      Finset.univ.filter (fun r : Fin R => g r = 1) ⊆ Finset.univ :=
    Finset.filter_subset _ _
  simpa using Finset.card_le_card hsub

/-- **FR.** Une cellule de fréquence d'indice strictement supérieur au
nombre de sites est nulle dans la représentation par sites.

**EN.** A frequency cell whose index is strictly greater than the number
of sites is zero in the site representation. -/
theorem frequencySitesCell_eq_bot_of_lt {R k : ℕ} (hRk : R < k) :
    frequencySitesCell R k = ⊥ := by
  unfold frequencySitesCell
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨g, hg, rfl⟩
    have hle := hammingWeight_le g
    change hammingWeight g = k at hg
    exfalso
    omega
  · exact bot_le

/-- **FR.** La même nullité après transport vers `H (2 ^ R)`.

**EN.** The same vanishing result after transport to `H (2 ^ R)`. -/
theorem frequencyCell_eq_bot_of_lt {R k : ℕ} (hRk : R < k) :
    frequencyCell R k = ⊥ := by
  simp [frequencyCell, frequencySitesCell_eq_bot_of_lt hRk]

/-- **FR.** Les `R + 1` cellules physiquement possibles, indexées par
`Fin (R + 1)`, couvrent l'espace des configurations par sites.

**EN.** The `R + 1` physically possible cells, indexed by `Fin (R + 1)`,
cover the site-configuration space. -/
theorem frequencySitesCell_iSup_fin (R : ℕ) :
    (⨆ k : Fin (R + 1), frequencySitesCell R k) = ⊤ := by
  apply top_unique
  have hspan :
      Submodule.span ℂ
          (Set.range
            (configurationBasis :
              (Fin R → Fin 2) → Sites R 2)) = ⊤ := by
    have heq :
        (configurationBasis :
          (Fin R → Fin 2) → Sites R 2) =
          ⇑(EuclideanSpace.basisFun
            (Fin R → Fin 2) ℂ).toBasis := by
      funext g
      rw [OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_apply]
      rfl
    rw [heq]
    exact
      (EuclideanSpace.basisFun
        (Fin R → Fin 2) ℂ).toBasis.span_eq
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro x ⟨g, rfl⟩
  let k : Fin (R + 1) :=
    ⟨hammingWeight g,
      Nat.lt_succ_iff.mpr (hammingWeight_le g)⟩
  exact
    (le_iSup
      (fun j : Fin (R + 1) =>
        frequencySitesCell R j) k)
      (by
        simpa [k] using
          configurationBasis_mem_frequencySitesCell g)

/-- **FR.** Les `R + 1` cellules transportées couvrent `H (2 ^ R)`.

**EN.** The transported `R + 1` cells cover `H (2 ^ R)`. -/
theorem frequencyCell_iSup_fin (R : ℕ) :
    (⨆ k : Fin (R + 1), frequencyCell R k) = ⊤ := by
  unfold frequencyCell
  rw [← Submodule.map_iSup, frequencySitesCell_iSup_fin]
  rw [Submodule.map_top,
    LinearMap.range_eq_top.mpr
      (sitesEquivR R).symm.surjective]

/-- **FR.** Configuration canonique dont les `k` premiers sites valent `1`
et les autres `0`.

**EN.** Canonical configuration whose first `k` sites are `1` and whose
remaining sites are `0`. -/
def prefixConfiguration (R : ℕ) (k : Fin (R + 1)) : Fin R → Fin 2 :=
  fun r => if r.val < k.val then 1 else 0

/-- **FR.** La configuration canonique possède exactement le poids de
Hamming `k`.

**EN.** The canonical configuration has Hamming weight exactly `k`. -/
theorem hammingWeight_prefixConfiguration
    (R : ℕ) (k : Fin (R + 1)) :
    hammingWeight (prefixConfiguration R k) = k.val := by
  have hk : k.val ≤ R := Nat.lt_succ_iff.mp k.isLt
  unfold hammingWeight
  have hfilter :
      Finset.univ.filter
          (fun r : Fin R => prefixConfiguration R k r = 1) =
        Finset.univ.filter
          (fun r : Fin R => r.val < k.val) := by
    apply Finset.filter_congr
    intro r hr
    unfold prefixConfiguration
    by_cases h : r.val < k.val <;> simp [h]
  rw [hfilter, Fin.card_filter_val_lt, Nat.min_eq_right hk]

/-- **FR.** Chaque cellule de fréquence d'indice physiquement possible est
non nulle. Le témoin est la branche de configuration associée à
`prefixConfiguration R k`.

**EN.** Every physically possible frequency cell is nonzero. The witness
is the configuration branch associated with `prefixConfiguration R k`. -/
theorem frequencyCell_ne_bot
    (R : ℕ) (k : Fin (R + 1)) :
    frequencyCell R k.val ≠ ⊥ := by
  intro hbot
  have hmem :=
    configurationBranch_mem_frequencyCell
      (prefixConfiguration R k)
  rw [hammingWeight_prefixConfiguration] at hmem
  rw [hbot] at hmem
  exact
    (configurationBranch_ne_zero R
      (prefixConfiguration R k))
      (by simpa using hmem)

end
end EverettianProbability.Frequency
