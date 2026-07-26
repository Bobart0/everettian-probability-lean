import EverettianProbability.Preference.ExpectationFunctional

/-!
**FR.** # Poids contextuel canonique

Le poids contextuel est défini directement comme la valeur de l'acte
indicateur. Il est nul hors des cellules de la perspective. Cette définition
canonique évite tout choix d'un représentant d'une classe de fonctions qui ne
sont observées que sur `D.cells`.

**EN.** # Canonical contextual weight

The contextual weight is defined directly as the value of the indicator act.
It is zero outside the perspective's cells. This canonical definition avoids
choosing a representative from functions that are observed only on `D.cells`.
-/

namespace EverettianProbability.BornCalibration

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Core EverettianProbability.Preference

variable {n : ℕ}

/-- **FR.** Le poids canonique : la valeur de l'acte indicateur, nulle hors
`D.cells`.

**EN.** The canonical weight: the value of the indicator act, zero outside
`D.cells`. -/
noncomputable def canonicalWeight (F : RationalExpectationFamily n) :
    Perspective n → Submodule ℂ (H n) → ℝ :=
  fun D c => if c ∈ D.cells then F.V D (Act.indicator c) else 0

/-- **FR.** Le poids canonique est nul hors des cellules de la perspective.

**EN.** The canonical weight vanishes outside the perspective's cells. -/
theorem canonicalWeight_zero_outside (F : RationalExpectationFamily n)
    (D : Perspective n) {c : Submodule ℂ (H n)} (hc : c ∉ D.cells) :
    canonicalWeight F D c = 0 := by
  simp only [canonicalWeight, if_neg hc]

end EverettianProbability.BornCalibration
