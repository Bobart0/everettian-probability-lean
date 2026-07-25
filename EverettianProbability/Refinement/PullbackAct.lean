import EverettianProbability.Core.Parent

/-!
**FR.** # Tiré-en-arrière d'un acte

`pullbackAct r a` réévalue un acte `a`, défini au niveau de la perspective
grossière `D`, au niveau de la perspective fine `D'`, en composant par la
carte parent. Les deux lemmes de compatibilité ci-dessous sont prouvés
**en entier** (aucun but ouvert dans ce fichier) : `pullbackAct_const` est
immédiat par calcul, et `pullbackAct_agree_of_agree` ne fait qu'appliquer
la spécification `parent_mem` de `Core/Parent.lean` — laquelle est,
elle, encore un but ouvert à ce stade. S'appuyer sur une spécification
amont encore ouverte est légitime (patron « squelette d'abord, preuves
ensuite ») et ne fait apparaître aucun nouveau but ouvert dans ce fichier ;
`#print axioms` sur `pullbackAct_agree_of_agree` révèle la dépendance
résiduelle à l'axiome interne des buts admis (voir
`Audit/MainResults.lean`).

**EN.** # Pullback of an act

`pullbackAct r a` re-evaluates an act `a`, defined at the level of the
coarse perspective `D`, at the level of the fine perspective `D'`, by
composing with the parent map. The two compatibility lemmas below are
proved **in full** (no goal left open in this file): `pullbackAct_const` is
immediate by computation, and `pullbackAct_agree_of_agree` merely applies
the `parent_mem` specification from `Core/Parent.lean` — which is itself
still an open goal at this stage. Relying on a still-open upstream
specification is legitimate (the "skeleton first, proofs later" pattern)
and introduces no new open goal in this file; `#print axioms` on
`pullbackAct_agree_of_agree` reveals the residual dependency on the
admitted-open-goal marker (see `Audit/MainResults.lean`).
-/

namespace EverettianProbability.Refinement

open QuantumFoundations.BornRule Gleason EverettianProbability.Core

variable {n : ℕ}

/-- Pulling an act back along a refinement: re-express `a`, defined on the
coarse perspective, as an act on the fine one, by routing every fine cell
through its parent. -/
noncomputable def pullbackAct {D' D : Perspective n} (r : Refines D' D) (a : Act n) : Act n :=
  a ∘ parent r

/-- A constant act is unaffected by any pullback. -/
theorem pullbackAct_const {D' D : Perspective n} (r : Refines D' D) (k : ℝ) :
    pullbackAct r (Act.const k) = Act.const k := rfl

/-- Pulling back preserves agreement: if `a` and `b` agree on the coarse
perspective `D`, their pullbacks agree on the fine perspective `D'`. -/
theorem pullbackAct_agree_of_agree {D' D : Perspective n} (r : Refines D' D)
    {a b : Act n} (h : Act.AgreeOn D a b) :
    Act.AgreeOn D' (pullbackAct r a) (pullbackAct r b) := by
  intro c' hc'
  show a (parent r c') = b (parent r c')
  exact h (parent r c') (parent_mem r hc')

end EverettianProbability.Refinement
