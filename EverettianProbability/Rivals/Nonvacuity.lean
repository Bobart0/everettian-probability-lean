import EverettianProbability.Rivals.NaiveBranchCounting

/-!
**FR.** # Non-vacuité — `Rivals`

Témoin concret : le comptage naïf satisfait bien `AxPos` (positivité), pour
tout `n` — c'est une règle rivale légitime au sens où elle satisfait *une
partie* des axiomes de cohérence, ce qui la rend intéressante à réfuter
précisément (elle échoue sur `AxGrain`, pas trivialement sur `AxPos`).
Preuve complète, aucun but ouvert.

**EN.** # Nonvacuity — `Rivals`

Concrete witness: naive counting does satisfy `AxPos` (positivity), for
every `n` — it is a legitimate rival rule in the sense that it satisfies
*some* of the coherence axioms, which is what makes it interesting to
refute precisely (it fails on `AxGrain`, not trivially on `AxPos`). Full
proof, no goal left open.
-/

namespace EverettianProbability.Rivals

open QuantumFoundations.BornRule Gleason

variable {n : ℕ}

theorem naiveCounting_axPos : AxPos (naiveCounting n) := by
  intro D c _
  unfold naiveCounting
  exact div_nonneg zero_le_one (Nat.cast_nonneg _)

end EverettianProbability.Rivals
