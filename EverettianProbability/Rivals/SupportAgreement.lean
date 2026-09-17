import EverettianProbability.Rivals.BornAgreement

/-!
**FR.** # Égalité des supports et invariance d'échelle

Pour tout état non nul, la règle de Born et la règle à puissance quatrième
renormalisée s'annulent exactement sur les mêmes cellules. La seconde est en
outre invariante par multiplication de l'état par un scalaire non nul, tandis
que le poids de Born est multiplié par le carré de sa norme.

Ces faits sont structurels : la renormalisation rend la règle rivale
normalisée sur tout état non nul, alors que la règle de Born est normalisée
sur les états unitaires.

**EN.** # Support agreement and scale invariance

For every nonzero state, the Born rule and the renormalized fourth-power rule
vanish on exactly the same cells. The latter is also invariant under
multiplication of the state by a nonzero scalar, whereas the Born weight is
multiplied by the square of that scalar's norm.

These facts are structural: renormalization makes the rival rule normalized
on every nonzero state, whereas the Born rule is normalized on unit states.
-/

namespace EverettianProbability.Rivals

open QuantumFoundations.BornRule
open QuantumFoundations.ProbabilityAPI
open Gleason
open scoped Classical

theorem renormalizedFourthPower_eq_zero_iff_bornWeight_eq_zero
    {n : ℕ} {v : H n} (hv : v ≠ 0) (D : Perspective n)
    {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
    renormalizedFourthPower v D c = 0 ↔ bornWeight v D c = 0 := by
  have hden : fourthPowerDenominator v D ≠ 0 :=
    ne_of_gt (fourthPowerDenominator_pos hv D)
  constructor
  · intro hzero
    have hnum : ‖projL c v‖ ^ 4 = 0 := by
      unfold renormalizedFourthPower at hzero
      exact (div_eq_zero_iff.mp hzero).resolve_right hden
    have hnorm : ‖projL c v‖ = 0 :=
      eq_zero_of_pow_eq_zero hnum
    unfold bornWeight
    rw [hnorm]
    norm_num
  · intro hzero
    have hnorm : ‖projL c v‖ = 0 := by
      unfold bornWeight at hzero
      exact eq_zero_of_pow_eq_zero hzero
    unfold renormalizedFourthPower
    rw [hnorm]
    norm_num

theorem renormalizedFourthPower_ne_zero_iff_bornWeight_ne_zero
    {n : ℕ} {v : H n} (hv : v ≠ 0) (D : Perspective n)
    {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
    renormalizedFourthPower v D c ≠ 0 ↔ bornWeight v D c ≠ 0 := by
  exact not_congr (renormalizedFourthPower_eq_zero_iff_bornWeight_eq_zero hv D hc)

private theorem fourthPowerDenominator_smul
    {n : ℕ} {t : ℂ} {v : H n} (D : Perspective n) :
    fourthPowerDenominator (t • v) D = ‖t‖ ^ 4 * fourthPowerDenominator v D := by
  unfold fourthPowerDenominator
  calc
    (∑ c ∈ D.cells, ‖projL c (t • v)‖ ^ 4) =
        ∑ c ∈ D.cells, ‖t‖ ^ 4 * ‖projL c v‖ ^ 4 := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [map_smul, norm_smul]
          ring
    _ = ‖t‖ ^ 4 * ∑ c ∈ D.cells, ‖projL c v‖ ^ 4 := by
      rw [Finset.mul_sum]

theorem renormalizedFourthPower_smul
    {n : ℕ} {t : ℂ} (ht : t ≠ 0) (v : H n) (D : Perspective n)
    (c : Submodule ℂ (H n)) :
    renormalizedFourthPower (t • v) D c = renormalizedFourthPower v D c := by
  have ht_norm : ‖t‖ ^ 4 ≠ 0 :=
    pow_ne_zero 4 (norm_ne_zero_iff.mpr ht)
  unfold renormalizedFourthPower
  rw [fourthPowerDenominator_smul]
  rw [map_smul, norm_smul]
  field_simp [ht_norm]

theorem bornWeight_smul
    {n : ℕ} {t : ℂ} (v : H n) (D : Perspective n)
    (c : Submodule ℂ (H n)) :
    bornWeight (t • v) D c = ‖t‖ ^ 2 * bornWeight v D c := by
  unfold bornWeight
  rw [map_smul, norm_smul]
  ring

end EverettianProbability.Rivals
