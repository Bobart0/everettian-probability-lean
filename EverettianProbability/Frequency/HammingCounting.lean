import EverettianProbability.Frequency.HammingCells
import Mathlib.Data.Fintype.Powerset

/-!
**FR.** # Dénombrement des configurations de poids de Hamming

Une configuration binaire est équivalente au finset des sites où elle vaut
`1`. Sous cette équivalence, le poids de Hamming devient le cardinal du
finset. Le nombre de configurations de poids `k` est donc `Nat.choose R k`.

Ce module est exclusivement combinatoire. Il n'introduit aucun poids de
Born, aucun état probabiliste et aucune notion de typicalité.

**EN.** # Counting Hamming-weight configurations

A binary configuration is equivalent to the finset of sites where it takes
the value `1`. Under this equivalence, Hamming weight becomes finset
cardinality. Hence the number of configurations of weight `k` is
`Nat.choose R k`.

This module is exclusively combinatorial. It introduces no Born weight,
probabilistic state, or notion of typicality.
-/

namespace EverettianProbability.Frequency

open scoped Classical

noncomputable section

/-- **FR.** Ensemble fini des sites auxquels une configuration attribue
la valeur `1`.

**EN.** Finite set of sites to which a configuration assigns the value
`1`. -/
def onesFinset {R : ℕ} (g : Fin R → Fin 2) : Finset (Fin R) :=
  Finset.univ.filter (fun r => g r = 1)

@[simp]
theorem mem_onesFinset {R : ℕ} (g : Fin R → Fin 2) (r : Fin R) :
    r ∈ onesFinset g ↔ g r = 1 := by
  simp [onesFinset]

/-- **FR.** Configuration indicatrice associée à un finset de sites.

**EN.** Indicator configuration associated with a finset of sites. -/
def configurationOfOnes {R : ℕ} (s : Finset (Fin R)) :
    Fin R → Fin 2 :=
  fun r => if r ∈ s then 1 else 0

@[simp]
theorem onesFinset_configurationOfOnes
    {R : ℕ} (s : Finset (Fin R)) :
    onesFinset (configurationOfOnes s) = s := by
  ext r
  simp [onesFinset, configurationOfOnes]

private theorem fin2_cases (x : Fin 2) :
    x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

@[simp]
theorem configurationOfOnes_onesFinset
    {R : ℕ} (g : Fin R → Fin 2) :
    configurationOfOnes (onesFinset g) = g := by
  funext r
  rcases fin2_cases (g r) with hzero | hone
  · simp [configurationOfOnes, onesFinset, hzero]
  · simp [configurationOfOnes, onesFinset, hone]

/-- **FR.** Équivalence entre configurations binaires et finsets de
positions égales à `1`.

**EN.** Equivalence between binary configurations and finsets of
positions equal to `1`. -/
def configurationFinsetEquiv (R : ℕ) :
    (Fin R → Fin 2) ≃ Finset (Fin R) where
  toFun := onesFinset
  invFun := configurationOfOnes
  left_inv := configurationOfOnes_onesFinset
  right_inv := onesFinset_configurationOfOnes

/-- **FR.** L'équivalence précédente se restreint aux configurations de
poids `k` et aux finsets de cardinal `k`.

**EN.** The preceding equivalence restricts to configurations of weight
`k` and finsets of cardinality `k`. -/
def hammingWeightFiberEquiv (R k : ℕ) :
    {g : Fin R → Fin 2 // hammingWeight g = k} ≃
      {s : Finset (Fin R) // s.card = k} where
  toFun g :=
    ⟨onesFinset g.1, by
      change hammingWeight g.1 = k
      exact g.2⟩
  invFun s :=
    ⟨configurationOfOnes s.1, by
      change
        (onesFinset
          (configurationOfOnes s.1)).card = k
      rw [onesFinset_configurationOfOnes]
      exact s.2⟩
  left_inv g := by
    apply Subtype.ext
    exact configurationOfOnes_onesFinset g.1
  right_inv s := by
    apply Subtype.ext
    exact onesFinset_configurationOfOnes s.1

/-- **FR.** Le nombre de configurations binaires de longueur `R` et de
poids de Hamming `k` est le coefficient binomial `R choose k`.

**EN.** The number of binary configurations of length `R` and Hamming
weight `k` is the binomial coefficient `R choose k`. -/
theorem hammingWeight_fiber_card (R k : ℕ) :
    Fintype.card
        {g : Fin R → Fin 2 // hammingWeight g = k} =
      Nat.choose R k := by
  calc
    Fintype.card
        {g : Fin R → Fin 2 // hammingWeight g = k} =
        Fintype.card
          {s : Finset (Fin R) // s.card = k} :=
      Fintype.card_congr
        (hammingWeightFiberEquiv R k)
    _ = Nat.choose (Fintype.card (Fin R)) k :=
      Fintype.card_finset_len (α := Fin R) k
    _ = Nat.choose R k := by
      simp

/-- **FR.** Finset de toutes les configurations de poids `k`.

**EN.** Finset of all configurations of weight `k`. -/
def configurationsOfWeight (R k : ℕ) :
    Finset (Fin R → Fin 2) :=
  Finset.univ.filter (fun g => hammingWeight g = k)

/-- **FR.** Le finset des configurations de poids `k` contient exactement
`R choose k` éléments.

**EN.** The finset of configurations of weight `k` contains exactly
`R choose k` elements. -/
theorem configurationsOfWeight_card (R k : ℕ) :
    (configurationsOfWeight R k).card =
      Nat.choose R k := by
  calc
    (configurationsOfWeight R k).card =
        Fintype.card
          {g : Fin R → Fin 2 //
            hammingWeight g = k} := by
      symm
      exact
        Fintype.card_of_subtype
          (configurationsOfWeight R k)
          (by
            intro g
            simp [configurationsOfWeight])
    _ = Nat.choose R k :=
      hammingWeight_fiber_card R k

/-- **FR.** L'image du poids de Hamming sur toutes les configurations
binaires de longueur `R` est exactement `{0, ..., R}`.

**EN.** The image of Hamming weight over all binary configurations of
length `R` is exactly `{0, ..., R}`. -/
theorem hammingWeight_image_univ (R : ℕ) :
    Finset.univ.image
        (hammingWeight :
          (Fin R → Fin 2) → ℕ) =
      Finset.range (R + 1) := by
  ext k
  constructor
  · intro hk
    obtain ⟨g, hg, rfl⟩ :=
      Finset.mem_image.mp hk
    exact
      Finset.mem_range.mpr
        (Nat.lt_succ_of_le (hammingWeight_le g))
  · intro hk
    have hkR : k ≤ R :=
      Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hk)
    let j : Fin (R + 1) :=
      ⟨k, Nat.lt_succ_iff.mpr hkR⟩
    refine
      Finset.mem_image.mpr
        ⟨prefixConfiguration R j,
          Finset.mem_univ _, ?_⟩
    simpa [j] using
      hammingWeight_prefixConfiguration R j

end
end EverettianProbability.Frequency
