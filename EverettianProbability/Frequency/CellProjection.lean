import EverettianProbability.Frequency.RepetitionVector

/-!
**FR.** # Projection du vecteur de répétition sur une cellule de fréquence

La composante de poids de Hamming k est explicitement construite dans la
représentation par sites, puis transportée vers H (2 ^ R). Elle est égale à
la projection orthogonale sur frequencyCell R k, et le carré de sa norme est
la somme des poids de la fibre de Hamming. La simplification de cette somme
en poids binomial reste à établir.

**EN.** # Projection of the repetition vector onto a frequency cell

The Hamming-weight k component is explicitly constructed in the site
representation and transported to H (2 ^ R). It equals the orthogonal
projection onto frequencyCell R k, and its squared norm is the sum of the
Hamming-fiber weights. Simplifying that sum to the binomial weight remains
to be proved.
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

end
end EverettianProbability.Frequency
