import EverettianProbability.Frequency.Moments

/-!
**FR.** # Concentration finie des fréquences

Ce module définit la masse projective des cellules dont la fréquence
relative s'écarte d'au moins `ε` d'un centre réel `p`.

Il établit une version entièrement finie de l'inégalité de Chebyshev.
Pour le centre bornien `p = ‖β‖²`, sous normalisation élémentaire et pour
`R > 0`, la masse des cellules atypiques est majorée par

`‖β‖² (1 - ‖β‖²) / (R ε²)`.

Aucune limite asymptotique n'est utilisée. Les cellules typiques ne sont
pas encore regroupées en un sous-espace projectif unique et aucun énoncé
de typicalité asymptotique n'est encore formulé.

**EN.** # Finite concentration of frequencies

This module defines the projective mass of cells whose relative frequency
deviates by at least `ε` from a real center `p`.

It proves a fully finite version of Chebyshev's inequality. For the Born
center `p = ‖β‖²`, under elementary normalization and for `R > 0`, the
mass of atypical cells is bounded by

`‖β‖² (1 - ‖β‖²) / (R ε²)`.

No asymptotic limit is used. Typical cells are not yet grouped into a
single projective subspace, and no asymptotic typicality statement is
formulated yet.
-/

namespace EverettianProbability.Frequency

open scoped Classical BigOperators

noncomputable section

/-- **FR.** Second moment pondéré de l'écart entre la fréquence relative
et un centre réel `p`.

**EN.** Weighted second moment of the deviation between relative
frequency and a real center `p`. -/
def frequencyRelativeDeviationSecondMoment
    (R : ℕ) (α β : ℂ) (p : ℝ) : ℝ :=
  ∑ k : Fin (R + 1),
    (frequencyRelativeValue R k - p) ^ 2 *
      frequencyMass R α β k

/-- **FR.** Le second moment de l'écart est non négatif.

**EN.** The deviation second moment is nonnegative. -/
theorem frequencyRelativeDeviationSecondMoment_nonneg
    (R : ℕ) (α β : ℂ) (p : ℝ) :
    0 ≤ frequencyRelativeDeviationSecondMoment R α β p := by
  unfold frequencyRelativeDeviationSecondMoment
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg
      (sq_nonneg
        (frequencyRelativeValue R k - p))
      (frequencyMass_nonneg R α β k)

/-- **FR.** Développement algébrique du second moment centré.

**EN.** Algebraic expansion of the centered second moment. -/
theorem frequencyRelativeDeviationSecondMoment_eq
    (R : ℕ) (α β : ℂ) (p : ℝ) :
    frequencyRelativeDeviationSecondMoment R α β p =
      frequencyRelativeSecondMoment R α β -
        2 * p * frequencyRelativeFirstMoment R α β +
        p ^ 2 *
          (∑ k : Fin (R + 1),
            frequencyMass R α β k) := by
  unfold frequencyRelativeDeviationSecondMoment
  unfold frequencyRelativeSecondMoment
  unfold frequencyRelativeFirstMoment
  calc
    (∑ k : Fin (R + 1),
        (frequencyRelativeValue R k - p) ^ 2 *
          frequencyMass R α β k) =
        ∑ k : Fin (R + 1),
          ((frequencyRelativeValue R k) ^ 2 *
            frequencyMass R α β k -
            (2 * p) *
              (frequencyRelativeValue R k *
                frequencyMass R α β k) +
            p ^ 2 * frequencyMass R α β k) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ =
        (∑ k : Fin (R + 1),
          (frequencyRelativeValue R k) ^ 2 *
            frequencyMass R α β k) -
          (∑ k : Fin (R + 1),
            (2 * p) *
              (frequencyRelativeValue R k *
                frequencyMass R α β k)) +
          ∑ k : Fin (R + 1),
            p ^ 2 * frequencyMass R α β k := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ =
        (∑ k : Fin (R + 1),
          (frequencyRelativeValue R k) ^ 2 *
            frequencyMass R α β k) -
          2 * p *
            (∑ k : Fin (R + 1),
              frequencyRelativeValue R k *
                frequencyMass R α β k) +
          p ^ 2 *
            (∑ k : Fin (R + 1),
              frequencyMass R α β k) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- **FR.** Sous normalisation élémentaire et pour `R > 0`, le second
moment de l'écart au centre bornien `‖β‖²` est exactement la variance de
la fréquence relative.

**EN.** Under elementary normalization and for `R > 0`, the second moment
of the deviation from the Born center `‖β‖²` is exactly the variance of
the relative frequency. -/
theorem frequencyRelativeDeviationSecondMoment_eq_variance
    (R : ℕ) (α β : ℂ)
    (hR : 0 < R)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    frequencyRelativeDeviationSecondMoment
        R α β (‖β‖ ^ 2) =
      frequencyRelativeVariance R α β := by
  unfold frequencyRelativeVariance
  rw [
    frequencyRelativeDeviationSecondMoment_eq,
    frequencyRelativeFirstMoment_eq R α β hR hnorm,
    sum_frequencyMass_eq_one R α β hnorm
  ]
  ring

/-- **FR.** Masse des cellules dont la fréquence relative s'écarte d'au
moins `ε` du centre `p`.

La définition par indicatrice évite toute nouvelle structure de mesure.

**EN.** Mass of cells whose relative frequency deviates by at least `ε`
from the center `p`.

The indicator-style definition avoids introducing any new measure
structure. -/
def frequencyAtypicalMass
    (R : ℕ) (α β : ℂ) (p ε : ℝ) : ℝ :=
  ∑ k : Fin (R + 1),
    if ε ≤ |frequencyRelativeValue R k - p| then
      frequencyMass R α β k
    else 0

/-- **FR.** La masse atypique est non négative.

**EN.** The atypical mass is nonnegative. -/
theorem frequencyAtypicalMass_nonneg
    (R : ℕ) (α β : ℂ) (p ε : ℝ) :
    0 ≤ frequencyAtypicalMass R α β p ε := by
  unfold frequencyAtypicalMass
  apply Finset.sum_nonneg
  intro k hk
  split_ifs
  · exact frequencyMass_nonneg R α β k
  · exact le_rfl

/-- **FR.** Forme multiplicative de l'inégalité de Chebyshev finie :
`ε²` fois la masse atypique est majorée par le second moment de l'écart.

**EN.** Multiplicative form of the finite Chebyshev inequality:
`ε²` times the atypical mass is bounded by the deviation second moment. -/
theorem epsilon_sq_mul_frequencyAtypicalMass_le_deviationSecondMoment
    (R : ℕ) (α β : ℂ) (p ε : ℝ)
    (hε : 0 ≤ ε) :
    ε ^ 2 * frequencyAtypicalMass R α β p ε ≤
      frequencyRelativeDeviationSecondMoment R α β p := by
  unfold frequencyAtypicalMass
  unfold frequencyRelativeDeviationSecondMoment
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  by_cases hdev :
      ε ≤ |frequencyRelativeValue R k - p|
  · rw [if_pos hdev]
    have hsqAbs :
        ε ^ 2 ≤
          |frequencyRelativeValue R k - p| ^ 2 := by
      nlinarith [
        abs_nonneg
          (frequencyRelativeValue R k - p)
      ]
    have hsq :
        ε ^ 2 ≤
          (frequencyRelativeValue R k - p) ^ 2 := by
      simpa using hsqAbs
    exact
      mul_le_mul_of_nonneg_right
        hsq
        (frequencyMass_nonneg R α β k)
  · rw [if_neg hdev]
    simp only [mul_zero]
    exact
      mul_nonneg
        (sq_nonneg
          (frequencyRelativeValue R k - p))
        (frequencyMass_nonneg R α β k)

/-- **FR.** Forme divisée de Chebyshev pour `ε > 0`.

**EN.** Divided form of Chebyshev's inequality for `ε > 0`. -/
theorem frequencyAtypicalMass_le_deviationSecondMoment_div
    (R : ℕ) (α β : ℂ) (p ε : ℝ)
    (hε : 0 < ε) :
    frequencyAtypicalMass R α β p ε ≤
      frequencyRelativeDeviationSecondMoment R α β p /
        ε ^ 2 := by
  have hεsq : 0 < ε ^ 2 := by
    positivity
  apply (le_div_iff₀ hεsq).2
  simpa [mul_comm] using
    (epsilon_sq_mul_frequencyAtypicalMass_le_deviationSecondMoment
      R α β p ε hε.le)

/-- **FR.** Borne de Chebyshev finie pour les poids projectifs des
cellules de fréquence :

`mass{|k/R - ‖β‖²| ≥ ε}
   ≤ ‖β‖²(1-‖β‖²)/(R ε²)`.

**EN.** Finite Chebyshev bound for the projective weights of frequency
cells:

`mass{|k/R - ‖β‖²| ≥ ε}
   ≤ ‖β‖²(1-‖β‖²)/(R ε²)`. -/
theorem frequencyAtypicalMass_le_chebyshev
    (R : ℕ) (α β : ℂ) (ε : ℝ)
    (hR : 0 < R)
    (hε : 0 < ε)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    frequencyAtypicalMass
        R α β (‖β‖ ^ 2) ε ≤
      (‖β‖ ^ 2) * (1 - ‖β‖ ^ 2) /
        ((R : ℝ) * ε ^ 2) := by
  have h :=
    frequencyAtypicalMass_le_deviationSecondMoment_div
      R α β (‖β‖ ^ 2) ε hε
  rw [
    frequencyRelativeDeviationSecondMoment_eq_variance
      R α β hR hnorm,
    frequencyRelativeVariance_eq R α β hR hnorm
  ] at h
  calc
    frequencyAtypicalMass
        R α β (‖β‖ ^ 2) ε ≤
        ((‖β‖ ^ 2) * (1 - ‖β‖ ^ 2) /
          (R : ℝ)) / ε ^ 2 := h
    _ =
        (‖β‖ ^ 2) * (1 - ‖β‖ ^ 2) /
          ((R : ℝ) * ε ^ 2) := by
      field_simp [
        show (R : ℝ) ≠ 0 by
          exact_mod_cast (Nat.ne_of_gt hR),
        ne_of_gt hε
      ]

end
end EverettianProbability.Frequency
