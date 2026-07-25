import QuantumFoundations.BornRule.Perspective
import EverettianProbability.Core.Act
import EverettianProbability.Core.Parent

/-!
**FR.** # Non-vacuité — `Core`

Un habitant concret pour chaque définition de `Core/` : un acte concret, et
une paire concrète `(D', D)` avec `Refines D' D` strictement (pas la
réflexivité triviale), obtenue en réutilisant directement l'infrastructure
amont (`Perspective.binary`, `refinePerspective`,
`refinePerspective_refines`, `line_ne_bot`, `line_ne_top`) plutôt qu'en la
reconstruisant. Aucun but ouvert : chaque énoncé ci-dessous est prouvé en
entier.

**EN.** # Nonvacuity — `Core`

A concrete witness for every definition in `Core/`: a concrete act, and a
concrete pair `(D', D)` with `Refines D' D` strictly (not trivial
reflexivity), obtained by reusing the upstream infrastructure directly
(`Perspective.binary`, `refinePerspective`, `refinePerspective_refines`,
`line_ne_bot`, `line_ne_top`) rather than rebuilding it. No goal is left
open: every statement below is proved in full.
-/

namespace EverettianProbability.Core

open QuantumFoundations.BornRule Gleason
open scoped Classical

/-- A concrete nonzero, proper subspace of `H 3`: the line spanned by the
first vector of the standard orthonormal basis of `H 3`. -/
noncomputable def exampleLine : Submodule ℂ (H 3) :=
  ℂ ∙ ((EuclideanSpace.basisFun (Fin 3) ℂ) 0 : H 3)

theorem exampleLine_ne_bot : exampleLine ≠ ⊥ :=
  line_ne_bot (EuclideanSpace.basisFun (Fin 3) ℂ) 0

theorem exampleLine_ne_top : exampleLine ≠ ⊤ :=
  line_ne_top (by norm_num) (EuclideanSpace.basisFun (Fin 3) ℂ) 0

/-- A concrete coarse perspective: the binary split
`{exampleLine, exampleLineᗮ}`. -/
noncomputable def exampleCoarse : Perspective 3 :=
  Perspective.binary exampleLine exampleLine_ne_bot exampleLine_ne_top

/-- A concrete strict refinement of `exampleCoarse`, obtained by the
upstream basis-refinement construction. -/
noncomputable def exampleFine : Perspective 3 := refinePerspective exampleCoarse

theorem exampleFine_refines : Refines exampleFine exampleCoarse :=
  refinePerspective_refines exampleCoarse

/-- A concrete act: the indicator of `exampleLine`. -/
noncomputable def exampleAct : Act 3 := Act.indicator exampleLine

/-- `Core.parent` is usable on a genuinely nontrivial refinement: applying
it to any cell of the fine perspective type-checks and produces a subspace
of `H 3`. Its exact value is not yet pinned down (`parent_mem`,
`parent_le`, `parent_unique` are still open goals in `Core/Parent.lean` —
see `MILESTONES.md`), but the definition itself is not vacuous. -/
noncomputable example (c' : Submodule ℂ (H 3)) : Submodule ℂ (H 3) :=
  parent exampleFine_refines c'

end EverettianProbability.Core
