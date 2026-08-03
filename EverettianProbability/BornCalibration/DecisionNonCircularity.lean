import EverettianProbability.BornCalibration.NonCircularity
import EverettianProbability.BornCalibration.RefinementImpliesGrain

/-!
**FR.** # Non-circularité, niveau décision — témoin en `n = 2`

`grain_does_not_imply_born_at_two` (`NonCircularity.lean`) réfute la
non-circularité au niveau du POIDS : une règle d'estimation cohérente sous
`AxGrain`/`AxNorm`/`AxPos`/`AxNul` qui n'est pas `‖·‖²`. Mais les prémisses de
DÉCISION employées ailleurs dans ce dépôt (`RefinementInvariantLocal F.V`,
`AxNul (canonicalWeight F) v`) portent sur une `RationalExpectationFamily`,
pas directement sur un poids : rien ne garantit a priori qu'une famille
d'espérance rationnelle EXISTE dont le poids canonique induit reproduit
`skewWeight`. Ce module construit cette famille explicitement
(`skewExpectationFamily`), établit que son poids canonique coïncide avec
`skewWeight witnessState`, transporte à travers cette égalité les axiomes déjà
prouvés côté poids, et conclut le contre-modèle de DÉCISION analogue :
les prémisses normatives employées par `born_expectation_of_invariance`
n'impliquent pas, à elles seules, les poids de Born en dimension 2.

Ne réétablit ni ne redémontre la construction géométrique de
`NonCircularity.lean` (`perspective_two_cases`, `skewF`, etc.) : seules ses
déclarations publiques sont réutilisées, plus un unique lemme numérique
public supplémentaire (`witnessLine_skewWeight_ne_born`) ajouté à ce fichier
dans le même correctif, pour éviter d'exposer la construction privée
`skewF`.

**EN.** # Non-circularity, decision level — witness at `n = 2`

`grain_does_not_imply_born_at_two` (`NonCircularity.lean`) refutes
non-circularity at the WEIGHT level: a coherent estimation rule under
`AxGrain`/`AxNorm`/`AxPos`/`AxNul` that is not `‖·‖²`. But the DECISION-level
premises used elsewhere in this repository (`RefinementInvariantLocal F.V`,
`AxNul (canonicalWeight F) v`) are stated about a `RationalExpectationFamily`,
not directly about a weight: nothing a priori guarantees that a rational
expectation family EXISTS whose induced canonical weight reproduces
`skewWeight`. This module builds that family explicitly
(`skewExpectationFamily`), establishes that its canonical weight coincides
with `skewWeight witnessState`, transports the already-proved weight-level
axioms across that equality, and concludes the analogous DECISION-level
countermodel: the normative premises used by `born_expectation_of_invariance`
do not, by themselves, imply Born weights in dimension 2.

Does not re-establish or re-prove `NonCircularity.lean`'s geometric
construction (`perspective_two_cases`, `skewF`, etc.): only its public
declarations are reused, plus a single additional public numeric lemma
(`witnessLine_skewWeight_ne_born`) added to that file in the same fix, to
avoid exposing the private `skewF` construction.
-/

namespace EverettianProbability.BornCalibration

open QuantumFoundations.ProbabilityAPI
open EverettianProbability.Core
open EverettianProbability.Preference
open EverettianProbability.Refinement
open scoped Classical

noncomputable section

/-- **FR.** La famille d'espérance rationnelle induite par le poids rival
`skewWeight witnessState` : l'espérance d'un acte est la somme, pondérée par
`skewWeight witnessState`, de ses valeurs sur les cellules de la perspective.
Affinité et normalisation sur les constantes découlent de la linéarité de la
somme finie ; la monotonie découle de la positivité de `skewWeight`
(`skewWeight_axPos`) ; la normalisation découle de `skewWeight_axNorm`.

**EN.** The rational expectation family induced by the rival weight
`skewWeight witnessState`: the expectation of an act is the sum, weighted by
`skewWeight witnessState`, of its values on the perspective's cells.
Affinity and normalization on constants follow from linearity of the finite
sum; monotonicity follows from the positivity of `skewWeight`
(`skewWeight_axPos`); normalization follows from `skewWeight_axNorm`. -/
def skewExpectationFamily : RationalExpectationFamily 2 where
  V D a := ∑ c ∈ D.cells, skewWeight witnessState D c * a c
  affine D t a b := by
    show ∑ c ∈ D.cells, skewWeight witnessState D c * (t * a c + (1 - t) * b c)
        = t * ∑ c ∈ D.cells, skewWeight witnessState D c * a c
          + (1 - t) * ∑ c ∈ D.cells, skewWeight witnessState D c * b c
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    ring
  monotone D a b hab := by
    show ∑ c ∈ D.cells, skewWeight witnessState D c * a c
        ≤ ∑ c ∈ D.cells, skewWeight witnessState D c * b c
    apply Finset.sum_le_sum
    intro c hc
    exact mul_le_mul_of_nonneg_left (hab c hc) (skewWeight_axPos witnessState D c hc)
  normalized_const D k := by
    show ∑ c ∈ D.cells, skewWeight witnessState D c * k = k
    rw [← Finset.sum_mul, skewWeight_axNorm witnessState witnessState_norm D, one_mul]

/-- **FR.** Le poids canonique de `skewExpectationFamily` coïncide avec
`skewWeight witnessState` sur les cellules de la perspective : l'acte
indicateur d'une cellule `c ∈ D.cells` isole exactement le terme `c` de la
somme définissant `V`.

**EN.** The canonical weight of `skewExpectationFamily` coincides with
`skewWeight witnessState` on the perspective's cells: the indicator act of a
cell `c ∈ D.cells` isolates exactly the `c` term of the sum defining `V`. -/
theorem skewExpectationFamily_canonicalWeight_eq
    {D : Perspective 2} {c : Submodule ℂ (H 2)} (hc : c ∈ D.cells) :
    canonicalWeight skewExpectationFamily D c = skewWeight witnessState D c := by
  show (if c ∈ D.cells then skewExpectationFamily.V D (Act.indicator c) else 0)
      = skewWeight witnessState D c
  rw [if_pos hc]
  show ∑ c' ∈ D.cells, skewWeight witnessState D c' * Act.indicator c c'
      = skewWeight witnessState D c
  rw [Finset.sum_eq_single c]
  · rw [Act.indicator_self, mul_one]
  · intro c' _ hne
    rw [Act.indicator_of_ne hne, mul_zero]
  · intro h
    exact absurd hc h

/-- **FR.** `AxGrain` du poids canonique de `skewExpectationFamily`, transporté
depuis `skewWeight_axGrain` à travers l'égalité de poids canonique ci-dessus.

**EN.** `AxGrain` of `skewExpectationFamily`'s canonical weight, transported
from `skewWeight_axGrain` across the canonical-weight equality above. -/
theorem skewExpectationFamily_axGrain :
    AxGrain (canonicalWeight skewExpectationFamily) := by
  intro D' D hRefines c hc
  rw [skewExpectationFamily_canonicalWeight_eq hc,
      skewWeight_axGrain witnessState witnessState_norm D' D hRefines c hc]
  apply Finset.sum_congr rfl
  intro c' hc'
  exact (skewExpectationFamily_canonicalWeight_eq (Finset.mem_filter.mp hc').1).symm

/-- **FR.** **Théorème d'invariance sous raffinement du témoin de décision.**
`skewExpectationFamily.V` satisfait la prémisse normative
`RefinementInvariantLocal`, via `refinementInvariantLocal_iff_axGrain` et
`skewExpectationFamily_axGrain`.

**EN.** **Refinement-invariance theorem for the decision witness.**
`skewExpectationFamily.V` satisfies the normative premise
`RefinementInvariantLocal`, via `refinementInvariantLocal_iff_axGrain` and
`skewExpectationFamily_axGrain`. -/
theorem skewExpectationFamily_refinementInvariantLocal :
    RefinementInvariantLocal skewExpectationFamily.V :=
  (refinementInvariantLocal_iff_axGrain skewExpectationFamily).mpr
    skewExpectationFamily_axGrain

/-- `AxNul` of `skewExpectationFamily`'s canonical weight at `witnessState`,
transported from `skewWeight_axNul` across the canonical-weight equality. -/
theorem skewExpectationFamily_axNul :
    AxNul (canonicalWeight skewExpectationFamily) witnessState := by
  intro D c hc hv
  rw [skewExpectationFamily_canonicalWeight_eq hc]
  exact skewWeight_axNul witnessState D c hc hv

/-- **FR.** `DECISION-LEVEL COUNTERMODEL`. En dimension 2, les prémisses
normatives employées par `born_expectation_of_invariance`
(invariance locale sous raffinement d'une famille d'espérance rationnelle,
plus nullité physique de son poids canonique sur un état unitaire) n'impliquent
PAS, à elles seules, les poids de Born : `skewExpectationFamily` en est un
contre-exemple concret, dont le poids canonique diffère effectivement de Born
sur la cellule `witnessLine` de la perspective binaire explicite. Cet énoncé
n'affirme ni `3 ≤ 2`, ni la satisfaction du paquet complet
`ProjectiveBornPremises` : il isole la restriction de dimension comme
hypothèse substantielle, distincte des prémisses normatives elles-mêmes.

**EN.** `DECISION-LEVEL COUNTERMODEL`. In dimension 2, the normative premises
used by `born_expectation_of_invariance` (local refinement invariance of a
rational expectation family, plus physical null support of its canonical
weight at a unit state) do NOT, by themselves, imply Born weights:
`skewExpectationFamily` is a concrete counterexample, whose canonical weight
genuinely differs from Born on the `witnessLine` cell of the explicit binary
perspective. This statement asserts neither `3 ≤ 2` nor satisfaction of the
full `ProjectiveBornPremises` bundle: it isolates the dimension restriction
as a substantial hypothesis, distinct from the normative premises
themselves. -/
theorem decision_premises_do_not_imply_born_at_two :
    ∃ (F : RationalExpectationFamily 2) (v : H 2),
      ‖v‖ = 1 ∧
      RefinementInvariantLocal F.V ∧
      AxNul (canonicalWeight F) v ∧
      ∃ (D : Perspective 2) (c : Submodule ℂ (H 2)),
        c ∈ D.cells ∧
        canonicalWeight F D c ≠ ‖projL c v‖ ^ 2 := by
  refine ⟨skewExpectationFamily, witnessState, witnessState_norm,
    skewExpectationFamily_refinementInvariantLocal,
    skewExpectationFamily_axNul,
    Perspective.binary witnessLine witnessLine_ne_bot witnessLine_ne_top, witnessLine,
    Finset.mem_insert_self _ _, ?_⟩
  rw [skewExpectationFamily_canonicalWeight_eq (Finset.mem_insert_self _ _ :
    witnessLine ∈
      (Perspective.binary witnessLine witnessLine_ne_bot witnessLine_ne_top).cells)]
  exact witnessLine_skewWeight_ne_born

end

end EverettianProbability.BornCalibration
