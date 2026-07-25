import QuantumFoundations.BornRule.Perspective

/-!
**FR.** # Actes

Un acte est une **fonction totale** `Submodule ℂ (H n) → ℝ`, jamais un
sous-type dépendant d'une perspective. Sa valeur sur une cellule qui n'est
pas dans la perspective effectivement considérée est une valeur poubelle,
sans signification : seule sa restriction aux cellules d'une perspective `D`
donnée (`AgreeOn D`) porte un contenu décisionnel. Ce choix (fonction totale
plutôt que sous-type indexé par une perspective) est documenté dans
`ARCHITECTURE_NOTES.md`.

Ce fichier ne contient que des définitions : aucune preuve n'est nécessaire,
et il ne laisse donc aucun but ouvert.

**EN.** # Acts

An act is a **total function** `Submodule ℂ (H n) → ℝ`, never a subtype
depending on a perspective. Its value on a cell outside the perspective
actually under consideration is junk, carrying no meaning: only its
restriction to the cells of a given perspective `D` (`AgreeOn D`) carries
decision-theoretic content. This choice (total function rather than a
perspective-indexed subtype) is documented in `ARCHITECTURE_NOTES.md`.

This file contains definitions only: no proof is required, hence no
goal is left open.
-/

namespace EverettianProbability.Core

open QuantumFoundations.BornRule Gleason
open scoped Classical

variable {n : ℕ}

/-- An act: a total real-valued payoff function on the subspaces of `H n`.
Values outside the perspective under consideration are junk. -/
def Act (n : ℕ) := Submodule ℂ (H n) → ℝ

namespace Act

/-- Two acts agree on (the cells of) a perspective `D`: the only sense in
which two acts can be compared meaningfully. -/
def AgreeOn (D : Perspective n) (a b : Act n) : Prop :=
  ∀ c ∈ D.cells, a c = b c

/-- The constant act, paying `k` regardless of the realized cell. -/
def const (k : ℝ) : Act n := fun _ => k

/-- The indicator act of a subspace `c₀`: pays `1` on `c₀`, `0` elsewhere. -/
noncomputable def indicator (c₀ : Submodule ℂ (H n)) : Act n :=
  fun c => if c = c₀ then 1 else 0

/-- Pointwise order on acts. Deliberately not registered as a Mathlib `LE`
instance: `Act n` is a `def`, not an `abbrev`, precisely so that no order
instance is picked up implicitly (see `ARCHITECTURE_NOTES.md`). -/
def PointwiseLE (a b : Act n) : Prop := ∀ c, a c ≤ b c

/-- Convex combination of two acts, pointwise. -/
noncomputable def convComb (t : ℝ) (a b : Act n) : Act n :=
  fun c => t * a c + (1 - t) * b c

end Act
end EverettianProbability.Core
