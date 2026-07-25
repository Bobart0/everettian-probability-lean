import EverettianProbability.Preference.Representation

/-!
**FR.** # Poids contextuel

Le poids contextuel associé à une famille d'espérance rationnelle `F` est
le témoin de poids `p_D` fourni par le théorème de représentation
(`Preference.exists_unique_weights`), vu comme une fonction des deux
arguments `(D, c)`. Son type est **exactement**
`Perspective n → Submodule ℂ (H n) → ℝ` : c'est le type de `Est` dans
`AxGrain`/`AxNorm`/`AxPos`/`AxNul` et dans
`grainCoherenceTheorem_projector`, en amont
(`QuantumFoundations.BornRule.Assembly`). Ce choix de type — décision
consignée dans `ARCHITECTURE_NOTES.md` — permet de brancher directement le
théorème amont sur `contextualWeight F`, sans adaptateur.

**EN.** # Contextual weight

The contextual weight attached to a rational expectation family `F` is the
weight witness `p_D` furnished by the representation theorem
(`Preference.exists_unique_weights`), viewed as a function of both
arguments `(D, c)`. Its type is **exactly**
`Perspective n → Submodule ℂ (H n) → ℝ`: this is the type of `Est` in
`AxGrain`/`AxNorm`/`AxPos`/`AxNul` and in `grainCoherenceTheorem_projector`
upstream (`QuantumFoundations.BornRule.Assembly`). This type choice —
decision recorded in `ARCHITECTURE_NOTES.md` — lets the upstream theorem
be applied directly to `contextualWeight F`, with no adapter.
-/

namespace EverettianProbability.BornCalibration

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Core EverettianProbability.Preference

variable {n : ℕ}

/-- The contextual weight of a rational expectation family: the
representing-weight function, of type `Perspective n → Submodule ℂ (H n) →
ℝ`, ready to be checked against `AxGrain`/`AxNorm`/`AxPos`/`AxNul`. -/
noncomputable def contextualWeight (F : RationalExpectationFamily n) :
    Perspective n → Submodule ℂ (H n) → ℝ :=
  fun D => Classical.choose (exists_unique_weights F D)

end EverettianProbability.BornCalibration
