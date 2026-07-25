import QuantumFoundations.BornRule.Perspective
import EverettianProbability.Core.Act

/-!
**FR.** # Carte parent

`Refines D' D` (défini en amont, `QuantumFoundations.BornRule.Perspective`)
est une relation `∀∃` : chaque cellule fine possède *un* parent, sans que
cette relation fournisse de fonction. `parent` construit cette fonction par
`Classical.choice`, dans le patron « définition totale + valeur poubelle +
lemmes de spécification sous hypothèse » utilisé partout en amont (voir
`AGENTS.md`). Les trois lemmes de spécification (`parent_mem`, `parent_le`,
`parent_unique`) sont énoncés mais laissés comme buts ouverts dans ce jalon P1 :
leur contenu est immédiat une fois déballé (`Classical.choose_spec` plus
`Perspective.unique_parent`), mais leur fermeture est différée pour garder
P1 strictement infrastructurel.

**EN.** # Parent map

`Refines D' D` (defined upstream, `QuantumFoundations.BornRule.Perspective`)
is a `∀∃` relation: every fine cell has *a* parent, without the relation
itself providing a function. `parent` builds that function via
`Classical.choice`, following the "total definition + junk value + spec
lemmas under hypothesis" pattern used throughout upstream (see
`AGENTS.md`). The three specification lemmas (`parent_mem`, `parent_le`,
`parent_unique`) are stated but left as open goals in this P1 milestone: their
content is immediate once unpacked (`Classical.choose_spec` plus
`Perspective.unique_parent`), but closing them is deferred to keep P1
strictly infrastructural.
-/

namespace EverettianProbability.Core

open QuantumFoundations.BornRule Gleason
open scoped Classical

variable {n : ℕ}

/-- The parent cell of a fine cell `c'` under a refinement `r : Refines D' D`:
the cell of `D` containing `c'`, obtained by `Classical.choice` on the
existential furnished by `Refines`. Total, with junk value `⊥` for cells
outside `D'.cells`. -/
noncomputable def parent {D' D : Perspective n} (r : Refines D' D)
    (c' : Submodule ℂ (H n)) : Submodule ℂ (H n) :=
  if hc' : c' ∈ D'.cells then
    Classical.choose (r c' hc')
  else
    ⊥

/-- Specification: `parent r c'` is a genuine cell of the coarse
perspective `D`. -/
theorem parent_mem {D' D : Perspective n} (r : Refines D' D)
    {c' : Submodule ℂ (H n)} (hc' : c' ∈ D'.cells) :
    parent r c' ∈ D.cells := by
  sorry

/-- Specification: the fine cell `c'` is genuinely contained in its
parent. -/
theorem parent_le {D' D : Perspective n} (r : Refines D' D)
    {c' : Submodule ℂ (H n)} (hc' : c' ∈ D'.cells) :
    c' ≤ parent r c' := by
  sorry

/-- Specification: `parent r c'` is *the* cell of `D` containing `c'`
— any other cell `c` of `D` with `c' ≤ c` must coincide with it, by
`Perspective.unique_parent` applied with the nonvacuity witness `D'.nz`. -/
theorem parent_unique {D' D : Perspective n} (r : Refines D' D)
    {c' c : Submodule ℂ (H n)} (hc' : c' ∈ D'.cells) (hc : c ∈ D.cells)
    (hle : c' ≤ c) : parent r c' = c := by
  sorry

end EverettianProbability.Core
