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

/-- **FR.** Deux indices de fréquence distincts définissent deux cellules
distinctes.

**EN.** Distinct frequency indices define distinct cells. -/
theorem frequencyCell_injective (R : ℕ) :
    Function.Injective
      (fun k : Fin (R + 1) => frequencyCell R k.val) := by
  intro k l hEq
  change frequencyCell R k.val = frequencyCell R l.val at hEq
  by_contra hkl
  have hval : k.val ≠ l.val := by
    intro h
    exact hkl (Fin.ext h)
  have horth :
      frequencyCell R l.val ⟂ frequencyCell R l.val := by
    have h :=
      frequencyCell_ortho
        (R := R) (k := k.val) (l := l.val) hval
    rwa [hEq] at h
  have hbot :
      frequencyCell R l.val = ⊥ :=
    Submodule.isOrtho_self.mp horth
  exact frequencyCell_ne_bot R l hbot

/-- **FR.** Les cellules de poids de Hamming possibles, indexées par
`Fin (R + 1)`, forment une perspective projective finie.

**EN.** The possible Hamming-weight cells, indexed by `Fin (R + 1)`,
form a finite projective perspective. -/
noncomputable def frequencyPerspective (R : ℕ) :
    Perspective (2 ^ R) where
  cells :=
    Finset.univ.image
      (fun k : Fin (R + 1) => frequencyCell R k.val)
  nz := by
    intro c hc
    simp only [
      Finset.mem_image,
      Finset.mem_univ,
      true_and
    ] at hc
    obtain ⟨k, rfl⟩ := hc
    exact frequencyCell_ne_bot R k
  ortho := by
    intro c hc d hd hcd
    simp only [
      Finset.mem_image,
      Finset.mem_univ,
      true_and
    ] at hc hd
    obtain ⟨k, rfl⟩ := hc
    obtain ⟨l, rfl⟩ := hd
    have hkl : k ≠ l := by
      intro h
      apply hcd
      rw [h]
    have hval : k.val ≠ l.val := by
      intro h
      exact hkl (Fin.ext h)
    exact
      (frequencyCell_ortho
        (R := R) (k := k.val) (l := l.val) hval).le
  span := by
    show
      sSup
        ((Finset.univ.image
          (fun k : Fin (R + 1) =>
            frequencyCell R k.val) :
          Finset (Submodule ℂ (H (2 ^ R)))) :
          Set (Submodule ℂ (H (2 ^ R)))) = ⊤
    have himage :
        ((Finset.univ.image
          (fun k : Fin (R + 1) =>
            frequencyCell R k.val) :
          Finset (Submodule ℂ (H (2 ^ R)))) :
          Set (Submodule ℂ (H (2 ^ R)))) =
        Set.range
          (fun k : Fin (R + 1) =>
            frequencyCell R k.val) := by
      ext c
      simp [Set.mem_range]
    rw [himage, sSup_range, frequencyCell_iSup_fin]

/-- **FR.** Chaque cellule finiment indexée appartient à la perspective de
fréquence.

**EN.** Every finitely indexed cell belongs to the frequency perspective. -/
theorem frequencyCell_mem_frequencyPerspective
    (R : ℕ) (k : Fin (R + 1)) :
    frequencyCell R k.val ∈
      (frequencyPerspective R).cells := by
  simp [frequencyPerspective]

/-- **FR.** La perspective de fréquence contient exactement `R + 1`
cellules.

**EN.** The frequency perspective contains exactly `R + 1` cells. -/
theorem frequencyPerspective_cells_card (R : ℕ) :
    (frequencyPerspective R).cells.card = R + 1 := by
  unfold frequencyPerspective
  rw [Finset.card_image_of_injective]
  · simp
  · exact frequencyCell_injective R

end
end EverettianProbability.Frequency
