import EverettianProbability.Frequency.Typicality
import Mathlib.Algebra.Order.Archimedean.Defs

/-!
**FR.** # Typicalité asymptotique sous forme quantifiée

Ce module transforme la borne finie de Chebyshev en un énoncé
asymptotique explicite ne faisant intervenir aucune théorie des limites.

Pour tous `ε > 0` et `δ > 0`, il existe un entier strictement positif
`N` tel que, pour tout nombre de répétitions `R ≥ N` :

* la masse des cellules dont la fréquence relative s'écarte d'au moins
  `ε` du centre bornien `‖β‖²` est au plus `δ`;
* la masse des cellules dont la fréquence relative reste strictement à
  moins de `ε` de ce centre est au moins `1 - δ`.

La preuve choisit `N` par la propriété archimédienne des réels et
réutilise exclusivement la borne finie déjà établie.

**EN.** # Asymptotic typicality in quantified form

This module turns the finite Chebyshev bound into an explicit asymptotic
statement without invoking any theory of limits.

For every `ε > 0` and `δ > 0`, there exists a strictly positive integer
`N` such that, for every number of repetitions `R ≥ N`:

* the mass of cells whose relative frequency deviates by at least `ε`
  from the Born center `‖β‖²` is at most `δ`;
* the mass of cells whose relative frequency remains strictly within
  `ε` of that center is at least `1 - δ`.

The proof chooses `N` by the Archimedean property of the reals and uses
only the previously established finite bound.
-/

namespace EverettianProbability.Frequency

open scoped Classical BigOperators

noncomputable section

/-- **FR.** Une borne inférieure suffisamment grande sur `R` rend la
borne de Chebyshev inférieure ou égale à `δ`.

**EN.** A sufficiently large lower bound on `R` makes the Chebyshev
bound at most `δ`. -/
theorem chebyshevBound_le_delta_of_large_repetitions
    (R : ℕ) (β : ℂ) (ε δ : ℝ)
    (hR : 0 < R)
    (hε : 0 < ε)
    (hδ : 0 < δ)
    (hlarge :
      (‖β‖ ^ 2) * (1 - ‖β‖ ^ 2) /
          (ε ^ 2 * δ) <
        (R : ℝ)) :
    (‖β‖ ^ 2) * (1 - ‖β‖ ^ 2) /
        ((R : ℝ) * ε ^ 2) ≤ δ := by
  have hRreal : 0 < (R : ℝ) := by
    exact_mod_cast hR
  have hεsq : 0 < ε ^ 2 := by
    exact pow_pos hε 2
  have hden : 0 < ε ^ 2 * δ :=
    mul_pos hεsq hδ
  have hcross :
      (‖β‖ ^ 2) * (1 - ‖β‖ ^ 2) <
        (R : ℝ) * (ε ^ 2 * δ) :=
    (div_lt_iff₀ hden).mp hlarge
  have hRε : 0 < (R : ℝ) * ε ^ 2 :=
    mul_pos hRreal hεsq
  apply (div_le_iff₀ hRε).2
  nlinarith

/-- **FR.** Sous la même condition de taille, la masse atypique est au
plus `δ`.

**EN.** Under the same size condition, the atypical mass is at most
`δ`. -/
theorem frequencyAtypicalMass_le_delta_of_large_repetitions
    (R : ℕ) (α β : ℂ) (ε δ : ℝ)
    (hR : 0 < R)
    (hε : 0 < ε)
    (hδ : 0 < δ)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1)
    (hlarge :
      (‖β‖ ^ 2) * (1 - ‖β‖ ^ 2) /
          (ε ^ 2 * δ) <
        (R : ℝ)) :
    frequencyAtypicalMass
        R α β (‖β‖ ^ 2) ε ≤ δ := by
  exact
    (frequencyAtypicalMass_le_chebyshev
      R α β ε hR hε hnorm).trans
        (chebyshevBound_le_delta_of_large_repetitions
          R β ε δ hR hε hδ hlarge)

/-- **FR.** Sous la même condition de taille, la masse typique est au
moins `1 - δ`.

**EN.** Under the same size condition, the typical mass is at least
`1 - δ`. -/
theorem one_sub_delta_le_frequencyTypicalMass_of_large_repetitions
    (R : ℕ) (α β : ℂ) (ε δ : ℝ)
    (hR : 0 < R)
    (hε : 0 < ε)
    (hδ : 0 < δ)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1)
    (hlarge :
      (‖β‖ ^ 2) * (1 - ‖β‖ ^ 2) /
          (ε ^ 2 * δ) <
        (R : ℝ)) :
    1 - δ ≤
      frequencyTypicalMass
        R α β (‖β‖ ^ 2) ε := by
  apply
    one_sub_delta_le_frequencyTypicalMass
      R α β ε δ hR hε hnorm
  exact
    chebyshevBound_le_delta_of_large_repetitions
      R β ε δ hR hε hδ hlarge

/-- **FR.** Typicalité asymptotique explicite.

Pour tous `ε > 0` et `δ > 0`, il existe un seuil strictement positif
`N` au-delà duquel la masse atypique est au plus `δ` et la masse typique
est au moins `1 - δ`.

Cet énoncé est la forme quantifiée `ε`–`δ` de la concentration des
fréquences autour du poids bornien. Il ne repose sur aucune construction
topologique ou mesurée supplémentaire.

**EN.** Explicit asymptotic typicality.

For every `ε > 0` and `δ > 0`, there exists a strictly positive threshold
`N` beyond which the atypical mass is at most `δ` and the typical mass is
at least `1 - δ`.

This is the quantified `ε`–`δ` form of frequency concentration around
the Born weight. It uses no additional topological or measure-theoretic
construction. -/
theorem exists_frequencyTypicality_threshold
    (α β : ℂ) (ε δ : ℝ)
    (hε : 0 < ε)
    (hδ : 0 < δ)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    ∃ N : ℕ,
      0 < N ∧
        ∀ R : ℕ, N ≤ R →
          frequencyAtypicalMass
              R α β (‖β‖ ^ 2) ε ≤ δ ∧
            1 - δ ≤
              frequencyTypicalMass
                R α β (‖β‖ ^ 2) ε := by
  have hp0 : 0 ≤ ‖β‖ ^ 2 :=
    sq_nonneg ‖β‖
  have ha0 : 0 ≤ ‖α‖ ^ 2 :=
    sq_nonneg ‖α‖
  have hp1 : ‖β‖ ^ 2 ≤ 1 := by
    nlinarith [hnorm]
  have hnum :
      0 ≤ (‖β‖ ^ 2) * (1 - ‖β‖ ^ 2) :=
    mul_nonneg hp0 (sub_nonneg.mpr hp1)
  have hεsq : 0 < ε ^ 2 := by
    exact pow_pos hε 2
  have hden : 0 < ε ^ 2 * δ :=
    mul_pos hεsq hδ
  have hratio_nonneg :
      0 ≤
        (‖β‖ ^ 2) * (1 - ‖β‖ ^ 2) /
          (ε ^ 2 * δ) :=
    div_nonneg hnum hden.le
  obtain ⟨N, hN⟩ :=
    exists_nat_gt
      ((‖β‖ ^ 2) * (1 - ‖β‖ ^ 2) /
        (ε ^ 2 * δ))
  have hNposReal : (0 : ℝ) < (N : ℝ) :=
    lt_of_le_of_lt hratio_nonneg hN
  have hNpos : 0 < N := by
    exact_mod_cast hNposReal
  refine ⟨N, hNpos, ?_⟩
  intro R hNR
  have hR : 0 < R :=
    lt_of_lt_of_le hNpos hNR
  have hNRreal : (N : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast hNR
  have hlarge :
      (‖β‖ ^ 2) * (1 - ‖β‖ ^ 2) /
          (ε ^ 2 * δ) <
        (R : ℝ) :=
    hN.trans_le hNRreal
  constructor
  · exact
      frequencyAtypicalMass_le_delta_of_large_repetitions
        R α β ε δ hR hε hδ hnorm hlarge
  · exact
      one_sub_delta_le_frequencyTypicalMass_of_large_repetitions
        R α β ε δ hR hε hδ hnorm hlarge

end
end EverettianProbability.Frequency
