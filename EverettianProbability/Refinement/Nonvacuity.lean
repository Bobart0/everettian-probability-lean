import EverettianProbability.Refinement.PayoffPreserving

/-!
**FR.** # Non-vacuité — `Refinement`

Témoin concret : tout acte constant est préservant les conséquences sous
raffinement, pour n'importe quelle perspective et n'importe quel
raffinement — la composition par `parent r` ne change rien à une fonction
constante. Preuve complète, aucun but ouvert.

**EN.** # Nonvacuity — `Refinement`

Concrete witness: every constant act is payoff-preserving under
refinement, for any perspective and any refinement — composing with
`parent r` does not change a constant function. Full proof, no goal left
open.
-/

namespace EverettianProbability.Refinement

open QuantumFoundations.BornRule Gleason EverettianProbability.Core

variable {n : ℕ}

theorem const_payoffPreserving (k : ℝ) : PayoffPreserving (Act.const k : Act n) := by
  intro D' D r c' _hc'
  rfl

end EverettianProbability.Refinement
