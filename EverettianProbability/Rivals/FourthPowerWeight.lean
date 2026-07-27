import EverettianProbability.PhysicalRefinement.RecordNeutralWitness

/-!
**FR.** # Règle rivale à puissance quatrième — témoin P9

Ce module formalise uniquement le cas concret `q = 4` de la règle rivale
`c ↦ ‖projL c v‖ ^ q`. Il ne formalise ni un exposant réel arbitraire ni
l'affirmation générale pour tout `q ≠ 2`.

La règle à puissance quatrième est positive, mais elle échoue déjà à
`AxNorm` sur l'état unitaire `psiBefore` et la perspective binaire
`coarsePerspective`. Les deux poids borniens sont `9/25` et `16/25`, donc
la somme quartique vaut `337/625 ≠ 1`.

**EN.** # Fourth-power rival rule — P9 witness

This module formalizes only the concrete `q = 4` case of the rival rule
`c ↦ ‖projL c v‖ ^ q`. It formalizes neither an arbitrary real exponent nor
the general claim for every `q ≠ 2`.

The fourth-power rule is positive, but already fails `AxNorm` on the unit
state `psiBefore` and the binary perspective `coarsePerspective`. The two
Born weights are `9/25` and `16/25`, so their fourth-power sum is
`337/625 ≠ 1`.
-/

namespace EverettianProbability.Rivals

open QuantumFoundations.ProbabilityAPI
open EverettianProbability.PhysicalRefinement
open scoped Classical

/-- **FR.** Poids à puissance quatrième : carré du poids bornien
`‖projL c v‖²`. La perspective est conservée dans le type d'une règle
d'estimation, mais la valeur ne dépend ici que de `c` et de `v`.

**EN.** Fourth-power weight: the square of the Born weight
`‖projL c v‖²`. The perspective remains in the estimation-rule type, but
the value here depends only on `c` and `v`. -/
noncomputable def fourthPowerWeight {n : ℕ} (v : H n) :
    Perspective n → Submodule ℂ (H n) → ℝ :=
  fun _ c => (‖projL c v‖ ^ 2) ^ 2

/-- **FR.** La règle à puissance quatrième satisfait `AxPos`.

**EN.** The fourth-power rule satisfies `AxPos`. -/
theorem fourthPowerWeight_axPos {n : ℕ} (v : H n) :
    AxPos (fourthPowerWeight v) := by
  intro D c hc
  unfold fourthPowerWeight
  positivity

/-- **FR.** Sur le témoin unitaire `psiBefore` et la perspective grossière,
la somme des poids à puissance quatrième vaut exactement `337/625`.

**EN.** On the unit witness `psiBefore` and the coarse perspective, the
fourth-power weights sum exactly to `337/625`. -/
theorem fourthPowerWeight_coarse_sum :
    ∑ c ∈ coarsePerspective.cells,
      fourthPowerWeight psiBefore coarsePerspective c = (337 / 625 : ℝ) := by
  rw [coarsePerspective_cells_eq,
    Finset.sum_insert (by simpa using label0Line_ne_label1Space),
    Finset.sum_singleton]
  unfold fourthPowerWeight
  rw [weight_label0_before, weight_label1Space_before]
  norm_num

/-- **FR.** La règle à puissance quatrième échoue à `AxNorm`, directement
par `337/625 ≠ 1`. L'échec ne provient pas d'un état non normalisé :
`psiBefore_norm` établit `‖psiBefore‖ = 1`.

**EN.** The fourth-power rule fails `AxNorm`, directly through
`337/625 ≠ 1`. The failure is not caused by an unnormalized state:
`psiBefore_norm` proves `‖psiBefore‖ = 1`. -/
theorem fourthPowerWeight_not_axNorm :
    ¬ AxNorm (fourthPowerWeight psiBefore) := by
  intro hNorm
  have h := hNorm coarsePerspective
  rw [fourthPowerWeight_coarse_sum] at h
  norm_num at h

end EverettianProbability.Rivals
