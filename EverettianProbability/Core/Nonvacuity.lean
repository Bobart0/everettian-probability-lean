import QuantumFoundations.ProbabilityAPI
import EverettianProbability.Core.Act

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

open QuantumFoundations.ProbabilityAPI
open scoped Classical

/-- A concrete nonzero, proper subspace of `H 3`: the line spanned by the
first vector of the standard orthonormal basis of `H 3`. -/
noncomputable def exampleLine : Submodule ℂ (H 3) :=
  ℂ ∙ ((EuclideanSpace.basisFun (Fin 3) ℂ) 0 : H 3)

theorem exampleLine_ne_bot : exampleLine ≠ ⊥ :=
  QuantumFoundations.BornRule.line_ne_bot (EuclideanSpace.basisFun (Fin 3) ℂ) 0

theorem exampleLine_ne_top : exampleLine ≠ ⊤ :=
  QuantumFoundations.BornRule.line_ne_top (by norm_num)
    (EuclideanSpace.basisFun (Fin 3) ℂ) 0

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

/-- Upstream `parentOf` is usable on a genuinely nontrivial refinement:
applying it to any cell of the fine perspective type-checks and produces a
subspace of `H 3`. Its governing lemmas (`parentOf_mem`, `parentOf_le`,
`parentOf_eq_of_le`) are proved upstream and imported directly, not
reproved here. The local `Core/Parent.lean` this docstring once pointed to
(a P1-era scaffold carrying `parent_mem`/`parent_le`/`parent_unique` as
open goals) was deleted once the API junction adopted upstream `parentOf`
directly; every pullback in `EverettianProbability` now uses it as is (see
`ARCHITECTURE_NOTES.md`). -/
noncomputable example (c' : Submodule ℂ (H 3)) : Submodule ℂ (H 3) :=
  parentOf exampleFine_refines c'

theorem exampleLine_mem_exampleCoarse : exampleLine ∈ exampleCoarse.cells := by
  simp only [exampleCoarse, Perspective.binary, Finset.mem_insert, Finset.mem_singleton,
    true_or]

theorem exampleAct_at_exampleLine : exampleAct exampleLine = 1 := by
  simp only [exampleAct, Act.indicator_self]

theorem exampleConst_at_exampleLine : (Act.const 7 : Act 3) exampleLine = 7 := rfl

end EverettianProbability.Core
