import EverettianProbability.BornCalibration.ContextualWeight
import EverettianProbability.Preference.Nonvacuity

/-!
**FR.** # Non-vacuité — poids canonique

Le poids canonique est défini sans choix abstrait et s'applique directement au
témoin concret `uniformExpectationFamily` en dimension trois.

**EN.** # Nonvacuity — canonical weight

The canonical weight is defined without an abstract choice and applies directly
to the concrete dimension-three witness `uniformExpectationFamily`.
-/

namespace EverettianProbability.BornCalibration

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Core EverettianProbability.Preference

/-- **FR.** Le poids canonique produit un réel concret pour le témoin uniforme.

**EN.** The canonical weight produces a concrete real for the uniform witness. -/
noncomputable example (D : Perspective 3) (c : Submodule ℂ (H 3)) : ℝ :=
  canonicalWeight uniformExpectationFamily D c

end EverettianProbability.BornCalibration
