import EverettianProbability.Frequency.RepetitionVector

/-!
**FR.** # Projection du vecteur de répétition sur une cellule de fréquence

La composante de poids de Hamming k annule les coordonnées des autres poids
dans la représentation par sites, puis est transportée vers H (2 ^ R).
Elle est exactement la projection orthogonale sur frequencyCell R k.
Ce module ne calcule pas encore sa norme ni le poids bornien binomial.

**EN.** # Projection of the repetition vector onto a frequency cell

The Hamming-weight k component zeros other coordinates in the site
representation and is transported to H (2 ^ R). It is exactly the
orthogonal projection onto frequencyCell R k. This module does not yet
compute its norm or the binomial Born weight.
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

end
end EverettianProbability.Frequency
