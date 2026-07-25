import EverettianProbability.Refinement.PullbackAct

/-!
**FR.** # Invariance sous raffinement préservant les conséquences

Un acte est « préservant les conséquences sous raffinement » si sa valeur
sur toute cellule fine coïncide avec sa valeur tirée-en-arrière depuis la
perspective grossière : le paiement associé à une conséquence ne dépend pas
de la perspective utilisée pour la décrire, seulement de la branche
effectivement réalisée. C'est la prémisse normative centrale de l'article
II — voir l'encart « Frontière de portée » de `AGENTS.md` et
`docs/SCOPE_AND_LIMITATIONS.md` : cette invariance n'est *dérivée* d'aucune
propriété de la dynamique unitaire, elle est *assumée*.

**EN.** # Refinement invariance preserving consequences

An act is "payoff-preserving under refinement" if its value on every fine
cell coincides with its value pulled back from the coarse perspective: the
payoff attached to a consequence does not depend on the perspective used to
describe it, only on the branch actually realized. This is the central
normative premise of paper II — see the "Scope boundary" box in
`AGENTS.md` and `docs/SCOPE_AND_LIMITATIONS.md`: this invariance is not
*derived* from any property of the unitary dynamics, it is *assumed*.
-/

namespace EverettianProbability.Refinement

open QuantumFoundations.BornRule Gleason EverettianProbability.Core

variable {n : ℕ}

/-- An act `a` is payoff-preserving under refinement if, for every
refinement `r : Refines D' D`, `a` agrees with its own pullback along `r`
on the fine perspective `D'`. -/
def PayoffPreserving (a : Act n) : Prop :=
  ∀ {D' D : Perspective n} (r : Refines D' D), Act.AgreeOn D' a (pullbackAct r a)

end EverettianProbability.Refinement
