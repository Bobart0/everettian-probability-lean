import EverettianProbability.Frequency.RepetitionVector

/-!
**FR.** # Projection du vecteur de répétition sur une cellule de fréquence

La composante projetée est explicitement construite et possède sa formule
binomiale exacte. Sous l'hypothèse de normalisation élémentaire, les poids des
cellules de la perspective somment à 1. La concentration et la typicalité
restent ouvertes.

**EN.** # Projection of the repetition vector onto a frequency cell

The projected component is explicitly constructed and has its exact binomial
formula. Under the elementary normalization hypothesis, the perspective-cell
weights sum to 1. Concentration and typicality remain open.
-/

namespace EverettianProbability.Frequency

open QuantumFoundations.ProbabilityAPI
open QuantumFoundations.ProbabilityAPI.Repetition
open scoped Classical InnerProductSpace

noncomputable section

/-- **FR.** Composante par sites du vecteur de répétition de poids k.

**EN.** Site-space component of the repetition vector of weight k. -/
def repetitionFrequencySitesComponent (R k : ℕ) (α β : ℂ) : Sites R 2 :=
  (WithLp.equiv 2 ((Fin R → Fin 2) → ℂ)).symm
    (fun g => if hammingWeight g = k then repetitionAmplitude R α β g else 0)

@[simp] theorem repetitionFrequencySitesComponent_apply
    (R k : ℕ) (α β : ℂ) (g : Fin R → Fin 2) :
    repetitionFrequencySitesComponent R k α β g =
      if hammingWeight g = k then repetitionAmplitude R α β g else 0 := by
  simp [repetitionFrequencySitesComponent]

theorem repetitionFrequencySitesComponent_eq_sum
    (R k : ℕ) (α β : ℂ) :
    repetitionFrequencySitesComponent R k α β =
      ∑ g ∈ configurationsOfWeight R k,
        repetitionAmplitude R α β g • configurationBasis g := by
  ext h
  simp [repetitionFrequencySitesComponent, configurationsOfWeight,
    configurationBasis, Pi.single_apply]

theorem repetitionSitesVector_eq_sum_configurationBasis
    (R : ℕ) (α β : ℂ) :
    repetitionSitesVector R α β =
      ∑ g : Fin R → Fin 2, repetitionAmplitude R α β g • configurationBasis g := by
  ext h
  simp [repetitionSitesVector_apply, configurationBasis, Pi.single_apply]

theorem frequencySitesCell_starProjection_repetitionSitesVector
    (R k : ℕ) (α β : ℂ) :
    (frequencySitesCell R k).starProjection (repetitionSitesVector R α β) =
      repetitionFrequencySitesComponent R k α β := by
  rw [repetitionSitesVector_eq_sum_configurationBasis, map_sum,
    repetitionFrequencySitesComponent_eq_sum]
  simp [configurationsOfWeight,
    frequencySitesCell_starProjection_configurationBasis]
  rw [Finset.sum_filter]

def repetitionFrequencyComponent
    (R k : ℕ) (α β : ℂ) : H (2 ^ R) :=
  (sitesEquivR R).symm (repetitionFrequencySitesComponent R k α β)

@[simp] theorem sitesEquivR_repetitionFrequencyComponent
    (R k : ℕ) (α β : ℂ) :
    sitesEquivR R (repetitionFrequencyComponent R k α β) =
      repetitionFrequencySitesComponent R k α β := by
  simp [repetitionFrequencyComponent]

theorem projL_frequencyCell_repetitionVector
    (R k : ℕ) (α β : ℂ) :
    projL (frequencyCell R k) (repetitionVector R α β) =
      repetitionFrequencyComponent R k α β := by
  change (frequencyCell R k).starProjection (repetitionVector R α β) =
    repetitionFrequencyComponent R k α β
  unfold frequencyCell repetitionVector
  rw [Submodule.starProjection_map_apply]
  simp [repetitionFrequencyComponent,
    frequencySitesCell_starProjection_repetitionSitesVector]

theorem repetitionFrequencyComponent_mem_frequencyCell
    (R k : ℕ) (α β : ℂ) :
    repetitionFrequencyComponent R k α β ∈ frequencyCell R k := by
  rw [← projL_frequencyCell_repetitionVector]
  exact Submodule.starProjection_apply_mem
    (frequencyCell R k) (repetitionVector R α β)

/-- **FR.** Le carré de la norme de la composante par sites de poids k est
la somme des poids scalaires de toutes les configurations de cette fibre.

**EN.** The squared norm of the site-space weight-k component is the sum
of scalar weights of all configurations in that Hamming fiber. -/
theorem repetitionFrequencySitesComponent_norm_sq_eq_sum
    (R k : ℕ) (α β : ℂ) :
    ‖repetitionFrequencySitesComponent R k α β‖ ^ 2 =
      ∑ g ∈ configurationsOfWeight R k,
        repetitionConfigurationWeight R α β g := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold configurationsOfWeight
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro g hg
  by_cases h : hammingWeight g = k <;>
    simp [repetitionFrequencySitesComponent_apply,
      repetitionConfigurationWeight, h]

/-- **FR.** Après transport isométrique, le carré de la norme de la
composante de fréquence est la même somme sur la fibre de Hamming.

**EN.** After isometric transport, the squared norm of the frequency
component is the same sum over the Hamming fiber. -/
theorem repetitionFrequencyComponent_norm_sq_eq_sum
    (R k : ℕ) (α β : ℂ) :
    ‖repetitionFrequencyComponent R k α β‖ ^ 2 =
      ∑ g ∈ configurationsOfWeight R k,
        repetitionConfigurationWeight R α β g := by
  simpa [repetitionFrequencyComponent] using
    (repetitionFrequencySitesComponent_norm_sq_eq_sum R k α β)

/-- **FR.** Le poids projectif brut de la cellule de fréquence k est la
somme des poids de toutes les configurations de poids k.

**EN.** The raw projective weight of frequency cell k is the sum of weights
of all configurations of weight k. -/
theorem projL_frequencyCell_repetitionVector_norm_sq_eq_sum
    (R k : ℕ) (α β : ℂ) :
    ‖projL (frequencyCell R k) (repetitionVector R α β)‖ ^ 2 =
      ∑ g ∈ configurationsOfWeight R k,
        repetitionConfigurationWeight R α β g := by
  rw [projL_frequencyCell_repetitionVector]
  exact repetitionFrequencyComponent_norm_sq_eq_sum R k α β

/-- **FR.** La somme des poids de la fibre de Hamming est son cardinal
binomial multiplié par son poids commun.

**EN.** The sum of Hamming-fiber weights is its binomial cardinality times
its common weight. -/
theorem sum_repetitionConfigurationWeight_configurationsOfWeight
    (R k : ℕ) (α β : ℂ) :
    (∑ g ∈ configurationsOfWeight R k,
        repetitionConfigurationWeight R α β g) =
      (Nat.choose R k : ℝ) *
        ((‖α‖ ^ 2) ^ (R - k) * (‖β‖ ^ 2) ^ k) := by
  let w : ℝ := (‖α‖ ^ 2) ^ (R - k) * (‖β‖ ^ 2) ^ k
  have hconst :
      ∀ g ∈ configurationsOfWeight R k,
        repetitionConfigurationWeight R α β g = w := by
    intro g hg
    have hweight : hammingWeight g = k := by
      simpa [configurationsOfWeight] using hg
    rw [repetitionConfigurationWeight_eq_norm_sq_powers, hweight]
  calc
    (∑ g ∈ configurationsOfWeight R k,
        repetitionConfigurationWeight R α β g) =
        (configurationsOfWeight R k).card • w :=
      Finset.sum_eq_card_nsmul hconst
    _ = (Nat.choose R k : ℝ) *
          ((‖α‖ ^ 2) ^ (R - k) * (‖β‖ ^ 2) ^ k) := by
      rw [configurationsOfWeight_card]
      simp [w, nsmul_eq_mul]

/-- **FR.** La composante par sites possède la formule binomiale exacte.

**EN.** The site-space component has the exact binomial formula. -/
theorem repetitionFrequencySitesComponent_norm_sq_eq_binomial
    (R k : ℕ) (α β : ℂ) :
    ‖repetitionFrequencySitesComponent R k α β‖ ^ 2 =
      (Nat.choose R k : ℝ) *
        ((‖α‖ ^ 2) ^ (R - k) * (‖β‖ ^ 2) ^ k) := by
  rw [repetitionFrequencySitesComponent_norm_sq_eq_sum]
  exact sum_repetitionConfigurationWeight_configurationsOfWeight R k α β

/-- **FR.** La composante transportée possède la formule binomiale exacte.

**EN.** The transported component has the exact binomial formula. -/
theorem repetitionFrequencyComponent_norm_sq_eq_binomial
    (R k : ℕ) (α β : ℂ) :
    ‖repetitionFrequencyComponent R k α β‖ ^ 2 =
      (Nat.choose R k : ℝ) *
        ((‖α‖ ^ 2) ^ (R - k) * (‖β‖ ^ 2) ^ k) := by
  rw [repetitionFrequencyComponent_norm_sq_eq_sum]
  exact sum_repetitionConfigurationWeight_configurationsOfWeight R k α β

/-- **FR.** Formule binomiale centrale du poids projectif brut de la cellule
contenant exactement k résultats 1 parmi R répétitions.

**EN.** Central binomial formula for the raw projective weight of the cell
containing exactly k outcomes equal to 1 among R repetitions. -/
theorem projL_frequencyCell_repetitionVector_norm_sq_eq_binomial
    (R k : ℕ) (α β : ℂ) :
    ‖projL (frequencyCell R k) (repetitionVector R α β)‖ ^ 2 =
      (Nat.choose R k : ℝ) *
        ((‖α‖ ^ 2) ^ (R - k) * (‖β‖ ^ 2) ^ k) := by
  rw [projL_frequencyCell_repetitionVector_norm_sq_eq_sum]
  exact sum_repetitionConfigurationWeight_configurationsOfWeight R k α β

/-- **FR.** La somme indexée des poids projectifs de fréquence est la
puissance R de la somme des poids élémentaires.

**EN.** The indexed sum of frequency projective weights is the R-th power
of the elementary-weight sum. -/
theorem sum_projL_frequencyCell_repetitionVector_norm_sq_eq_elementary_sum_pow
    (R : ℕ) (α β : ℂ) :
    (∑ k : Fin (R + 1),
        ‖projL (frequencyCell R k.val)
            (repetitionVector R α β)‖ ^ 2) =
      (‖α‖ ^ 2 + ‖β‖ ^ 2) ^ R := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k => ‖projL (frequencyCell R k)
      (repetitionVector R α β)‖ ^ 2) (R + 1)]
  simp_rw [projL_frequencyCell_repetitionVector_norm_sq_eq_binomial]
  exact (repetitionVector_norm_sq_eq_binomial_sum R α β).symm.trans
    (repetitionVector_norm_sq_eq_elementary_sum_pow R α β)

/-- **FR.** Sous normalisation élémentaire, la somme indexée vaut 1.

**EN.** Under elementary normalization, the indexed sum is 1. -/
theorem sum_projL_frequencyCell_repetitionVector_norm_sq_eq_one
    (R : ℕ) (α β : ℂ)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    (∑ k : Fin (R + 1),
        ‖projL (frequencyCell R k.val)
            (repetitionVector R α β)‖ ^ 2) = 1 := by
  rw [sum_projL_frequencyCell_repetitionVector_norm_sq_eq_elementary_sum_pow,
    hnorm, one_pow]

/-- **FR.** La somme sur les cellules de frequencyPerspective a la même
valeur que la somme indexée.

**EN.** The sum over frequencyPerspective cells equals the indexed sum. -/
theorem sum_frequencyPerspective_repetitionVector_norm_sq_eq_elementary_sum_pow
    (R : ℕ) (α β : ℂ) :
    (∑ c ∈ (frequencyPerspective R).cells,
        ‖projL c (repetitionVector R α β)‖ ^ 2) =
      (‖α‖ ^ 2 + ‖β‖ ^ 2) ^ R := by
  calc
    (∑ c ∈ (frequencyPerspective R).cells,
        ‖projL c (repetitionVector R α β)‖ ^ 2) =
        ∑ k : Fin (R + 1),
          ‖projL (frequencyCell R k.val)
              (repetitionVector R α β)‖ ^ 2 := by
      unfold frequencyPerspective
      rw [Finset.sum_image
        (s := Finset.univ)
        (g := fun k : Fin (R + 1) => frequencyCell R k.val)
        (frequencyCell_injective R).injOn]
    _ = (‖α‖ ^ 2 + ‖β‖ ^ 2) ^ R :=
      sum_projL_frequencyCell_repetitionVector_norm_sq_eq_elementary_sum_pow R α β

/-- **FR.** Sous normalisation élémentaire, les poids de la perspective
de fréquence somment à 1.

**EN.** Under elementary normalization, the frequency-perspective weights
sum to 1. -/
theorem sum_frequencyPerspective_repetitionVector_norm_sq_eq_one
    (R : ℕ) (α β : ℂ)
    (hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    (∑ c ∈ (frequencyPerspective R).cells,
        ‖projL c (repetitionVector R α β)‖ ^ 2) = 1 := by
  rw [sum_frequencyPerspective_repetitionVector_norm_sq_eq_elementary_sum_pow,
    hnorm, one_pow]

end
end EverettianProbability.Frequency
