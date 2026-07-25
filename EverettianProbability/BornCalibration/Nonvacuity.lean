import EverettianProbability.BornCalibration.ContextualWeight
import EverettianProbability.Preference.Nonvacuity

/-!
**FR.** # Non-vacuité — `BornCalibration`

`contextualWeight` est applicable au témoin concret de `Preference/
Nonvacuity.lean` (`uniformExpectationFamily`, à `n = 3`) et produit un réel
concret pour toute perspective et toute cellule — la définition n'est pas
vacueuse, même si son comportement (satisfait-elle `AxGrain`, `AxPos`,
etc. ?) reste ouvert tant que `Preference.exists_unique_weights` est
lui-même un but ouvert (voir `MILESTONES.md`). Aucune preuve d'axiome n'est tentée ici :
ce serait anticiper sur `RefinementImpliesGrain.lean`.

**EN.** # Nonvacuity — `BornCalibration`

`contextualWeight` applies to the concrete witness from `Preference/
Nonvacuity.lean` (`uniformExpectationFamily`, at `n = 3`) and produces a
concrete real number for any perspective and any cell — the definition is
not vacuous, even though its behavior (does it satisfy `AxGrain`,
`AxPos`, etc.?) remains open as long as `Preference.exists_unique_weights`
is itself an open goal (see `MILESTONES.md`). No axiom proof is attempted here: that
would pre-empt `RefinementImpliesGrain.lean`.
-/

namespace EverettianProbability.BornCalibration

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Core EverettianProbability.Preference

/-- `contextualWeight` is usable on the concrete `uniformExpectationFamily`
witness: it type-checks and produces a concrete real number. -/
noncomputable example (D : Perspective 3) (c : Submodule ℂ (H 3)) : ℝ :=
  contextualWeight uniformExpectationFamily D c

end EverettianProbability.BornCalibration
