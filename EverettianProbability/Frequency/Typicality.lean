import EverettianProbability.Frequency.Concentration

/-!
**FR.** # Typicalité finie des fréquences

Ce module définit la masse projective des cellules dont la fréquence
relative se trouve strictement à moins de `ε` d'un centre réel `p`.

Cette masse typique est exactement complémentaire de la masse atypique
définie par la condition opposée

`ε ≤ |frequency - p|`.

Sous normalisation élémentaire, la somme des masses typique et atypique
vaut donc exactement `1`. La borne de Chebyshev fournit alors une borne
inférieure explicite pour la masse typique autour du centre bornien
`‖β‖²`.

Le résultat final est entièrement fini : si la borne de Chebyshev est au
plus `δ`, alors la masse typique est au moins `1 - δ`. Aucune limite
asymptotique n'est encore utilisée.

**EN.** # Finite typicality of frequencies

This module defines the projective mass of cells whose relative frequency
lies strictly within `ε` of a real center `p`.

This typical mass is exactly complementary to the atypical mass defined
by the opposite condition

`ε ≤ |frequency - p|`.

Under elementary normalization, the typical and atypical masses therefore
sum exactly to `1`. Chebyshev's bound then yields an explicit lower bound
for the typical mass around the Born center `‖β‖²`.

The final result is entirely finite: if the Chebyshev bound is at most
`δ`, then the typical mass is at least `1 - δ`. No asymptotic limit is
used yet.
-/

namespace EverettianProbability.Frequency

open scoped Classical BigOperators

noncomputable section

/-- **FR.** Masse des cellules dont la fréquence relative se trouve
strictement à moins de `ε` du centre `p`.

**EN.** Mass of cells whose relative frequency lies strictly within `ε`
of the center `p`. -/
def frequencyTypicalMass
    (R : ℕ) (α β : ℂ) (p ε : ℝ) : ℝ :=
  ∑ k : Fin (R + 1),
    if |frequencyRelativeValue R k - p| < ε then
      frequencyMass R α β k
    else 0

/-- **FR.** La masse typique est non négative.

**EN.** The typical mass is nonnegative. -/
theorem frequencyTypicalMass_nonneg
    (R : ℕ) (α β : ℂ) (p ε : ℝ) :
    0 ≤ frequencyTypicalMass R α β p ε := by
  unfold frequencyTypicalMass
  apply Finset.sum_nonneg
  intro k hk
  split_ifs
  · exact frequencyMass_nonneg R α β k
  · exact le_rfl

/-- **FR.** Les conditions typique et atypique partitionnent exactement
les cellules : leur somme est la masse totale.

**EN.** The typical and atypical conditions exactly partition the cells:
their sum is the total mass. -/
theorem frequencyTypicalMass_add_frequencyAtypicalMass_eq_totalMass
    (R : ℕ) (α β : ℂ) (p ε : ℝ) :
    frequencyTypicalMass R α β p ε +
        frequencyAtypicalMass R α β p ε =
      ∑ k : Fin (R + 1),
        frequencyMass R α β k := by
  unfold frequencyTypicalMass
  unfold frequencyAtypicalMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases htyp :
      |frequencyRelativeValue R k - p| < ε
  · have hatyp :
        ¬ ε ≤ |frequencyRelativeValue R k - p| :=
      not_le.mpr htyp
    simp [htyp, hatyp]
  · have hatyp :
        ε ≤ |frequencyRelativeValue R k - p| :=
      le_of_not_gt htyp
    simp [htyp, hatyp]

/-- **FR.** Sous normalisation élémentaire, les masses typique et atypique
somment exactement à `1`.

**EN.** Under elementary normalization, the typical and atypical masses
sum exactly to `1`. -/
theorem frequencyTypicalMass_add_frequencyAtypicalMass_eq_one
    (R : ℕ) (α β : ℂ) (p ε : ℝ)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    frequencyTypicalMass R α β p ε +
        frequencyAtypicalMass R α β p ε = 1 := by
  rw [
    frequencyTypicalMass_add_frequencyAtypicalMass_eq_totalMass,
    sum_frequencyMass_eq_one R α β hnorm
  ]

/-- **FR.** Sous normalisation élémentaire, la masse typique est
exactement `1` moins la masse atypique.

**EN.** Under elementary normalization, the typical mass is exactly `1`
minus the atypical mass. -/
theorem frequencyTypicalMass_eq_one_sub_frequencyAtypicalMass
    (R : ℕ) (α β : ℂ) (p ε : ℝ)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    frequencyTypicalMass R α β p ε =
      1 - frequencyAtypicalMass R α β p ε := by
  have h :=
    frequencyTypicalMass_add_frequencyAtypicalMass_eq_one
      R α β p ε hnorm
  linarith

/-- **FR.** Sous normalisation élémentaire, la masse typique est au plus
`1`.

**EN.** Under elementary normalization, the typical mass is at most `1`.
-/
theorem frequencyTypicalMass_le_one
    (R : ℕ) (α β : ℂ) (p ε : ℝ)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    frequencyTypicalMass R α β p ε ≤ 1 := by
  have hsum :=
    frequencyTypicalMass_add_frequencyAtypicalMass_eq_one
      R α β p ε hnorm
  have hatyp :=
    frequencyAtypicalMass_nonneg R α β p ε
  linarith

/-- **FR.** Borne inférieure de Chebyshev pour la masse typique autour du
centre bornien :

`1 - ‖β‖²(1-‖β‖²)/(R ε²) ≤ typicalMass`.

**EN.** Chebyshev lower bound for the typical mass around the Born
center:

`1 - ‖β‖²(1-‖β‖²)/(R ε²) ≤ typicalMass`. -/
theorem one_sub_chebyshev_le_frequencyTypicalMass
    (R : ℕ) (α β : ℂ) (ε : ℝ)
    (hR : 0 < R)
    (hε : 0 < ε)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    1 -
        (‖β‖ ^ 2) * (1 - ‖β‖ ^ 2) /
          ((R : ℝ) * ε ^ 2) ≤
      frequencyTypicalMass
        R α β (‖β‖ ^ 2) ε := by
  have hsum :=
    frequencyTypicalMass_add_frequencyAtypicalMass_eq_one
      R α β (‖β‖ ^ 2) ε hnorm
  have hatyp :=
    frequencyAtypicalMass_le_chebyshev
      R α β ε hR hε hnorm
  linarith

/-- **FR.** Typicalité finie quantitative.

Si la borne de Chebyshev est au plus `δ`, alors la masse des cellules
dont la fréquence relative est à moins de `ε` de `‖β‖²` est au moins
`1 - δ`.

**EN.** Quantitative finite typicality.

If the Chebyshev bound is at most `δ`, then the mass of cells whose
relative frequency lies within `ε` of `‖β‖²` is at least `1 - δ`. -/
theorem one_sub_delta_le_frequencyTypicalMass
    (R : ℕ) (α β : ℂ) (ε δ : ℝ)
    (hR : 0 < R)
    (hε : 0 < ε)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1)
    (hδ :
      (‖β‖ ^ 2) * (1 - ‖β‖ ^ 2) /
          ((R : ℝ) * ε ^ 2) ≤ δ) :
    1 - δ ≤
      frequencyTypicalMass
        R α β (‖β‖ ^ 2) ε := by
  have htyp :=
    one_sub_chebyshev_le_frequencyTypicalMass
      R α β ε hR hε hnorm
  linarith

end
end EverettianProbability.Frequency
