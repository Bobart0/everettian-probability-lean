import EverettianProbability.BornCalibration.AbstractRefinementImpliesGrain

/-!
**FR.** # Empaquetage en règle d'estimation d'effets

Ce répertoire (`EffectCalibration/`, jalon route qubit) instancie la levée
abstraite (`Core/AbstractAct.lean`, `Preference/AbstractExpectationFunctional.
lean`, `Preference/AbstractRepresentation.lean`, `BornCalibration/
AbstractRefinementImpliesGrain.lean`) à `I := Effects.interface n` et la
relie à l'API amont `EffectPerspectives`, ce qui lève la restriction
`n ≥ 3` du théorème principal projectif : `Effects.interface` ne porte
aucune contrainte de dimension.

Ce fichier fait le pont entre deux mondes qui ne se ressemblent qu'en
apparence. Côté abstrait, `canonicalWeight F` est une simple fonction
`(D) → I.Cell D → ℝ` ; côté effets amont,
`EffectPerspectives.EstimationRule n` est une **structure** empaquetant
`weight`, `nonneg`, `normalized` et `grain` **simultanément** — on ne peut
pas exhiber une fonction satisfaisant Grain sans disposer, au même moment,
de sa positivité et de sa normalisation (voir `docs/QUBIT_FEASIBILITY_
REPORT.md`, section 2). `canonicalEstimationRule` fait exactement cet
empaquetage, à partir des trois ingrédients déjà prouvés abstraitement.

Dans l'autre sens, `familyOfEstimationRule` part d'un
`EstimationRule` déjà construit et lui associe la fonctionnelle
d'espérance abstraite `expectation` qu'il induit — automatiquement une
`RationalExpectationFamily` (l'affinité est un fait algébrique pur,
la monotonie vient de `nonneg`, la normalisation de `normalized`).
`canonicalWeight_familyOfEstimationRule` referme la boucle : le poids
canonique de la famille ainsi induite est exactement le poids d'origine.

**EN.** # Packaging into an effect estimation rule

This directory (`EffectCalibration/`, the qubit-route milestone)
instantiates the abstract lift (`Core/AbstractAct.lean`, `Preference/
AbstractExpectationFunctional.lean`, `Preference/AbstractRepresentation.
lean`, `BornCalibration/AbstractRefinementImpliesGrain.lean`) at
`I := Effects.interface n` and connects it to the upstream
`EffectPerspectives` API, which lifts the projective headline theorem's
`n ≥ 3` restriction: `Effects.interface` carries no dimension constraint.

This file bridges two worlds that only look alike. Abstractly,
`canonicalWeight F` is a bare function `(D) → I.Cell D → ℝ`; on the
upstream effect side, `EffectPerspectives.EstimationRule n` is a
**structure** bundling `weight`, `nonneg`, `normalized`, and `grain`
**simultaneously** — one cannot exhibit a function satisfying Grain without
also having, at the same time, its positivity and normalization (see
`docs/QUBIT_FEASIBILITY_REPORT.md`, section 2). `canonicalEstimationRule`
performs exactly this packaging, from the three ingredients already proved
abstractly.

In the other direction, `familyOfEstimationRule` starts from an already
built `EstimationRule` and associates to it the abstract `expectation`
functional it induces — automatically a `RationalExpectationFamily` (
affinity is pure algebra, monotonicity comes from `nonneg`, normalization
from `normalized`). `canonicalWeight_familyOfEstimationRule` closes the
loop: the canonical weight of the family thus induced is exactly the
original weight.
-/

namespace EverettianProbability.Abstract

open scoped BigOperators Classical
open QuantumFoundations.ProbabilityAPI

/-- `outcome` is injective on every effect perspective's cells: `Fin.val`
is injective. -/
theorem outcome_injective_effects (n : ℕ) (D : (Effects.interface n).Perspective) :
    Function.Injective (@(Effects.interface n).outcome D) := Fin.val_injective

/-- The packaged effect-side estimation rule: canonical weight, bundled
with the three facts an `EstimationRule` needs simultaneously
(`canonicalWeight_axPos`, `canonicalWeight_axNorm`, `canonicalWeight_grain`). -/
noncomputable def canonicalEstimationRule {n : ℕ}
    (F : RationalExpectationFamily (Effects.interface n))
    (hinv : RefinementInvariantLocal F.V) :
    EffectPerspectives.EstimationRule n where
  weight := canonicalWeight F
  nonneg := canonicalWeight_axPos F
  normalized := fun D => canonicalWeight_axNorm F D (outcome_injective_effects n D)
  grain := fun r j => canonicalWeight_grain F hinv (outcome_injective_effects n) r j

/-- Every effect-side estimation rule induces a rational expectation
family via the abstract-interface `expectation` functional: affinity is
pure algebra, monotonicity uses `nonneg`, normalization uses `normalized`. -/
noncomputable def familyOfEstimationRule {n : ℕ} (E : EffectPerspectives.EstimationRule n) :
    RationalExpectationFamily (Effects.interface n) where
  V := expectation (Effects.interface n) E
  affine := by
    intro D t a b
    letI := (Effects.interface n).cellFintype D
    show (∑ x : Fin D.outcomes, E.weight D x * (t * a x + (1 - t) * b x))
      = t * (∑ c : Fin D.outcomes, E.weight D c * a c) + (1 - t) * (∑ c : Fin D.outcomes, E.weight D c * b c)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  monotone := by
    intro D a b hab
    letI := (Effects.interface n).cellFintype D
    show (∑ i : Fin D.outcomes, E.weight D i * a i) ≤ ∑ i : Fin D.outcomes, E.weight D i * b i
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hab i) (E.nonneg D i)
  normalized_const := by
    intro D k
    letI := (Effects.interface n).cellFintype D
    show (∑ i : Fin D.outcomes, E.weight D i * k) = k
    rw [← Finset.sum_mul, E.normalized D, one_mul]

/-- **FR.** Aller-retour : le poids canonique de la famille induite par une
règle d'estimation retrouve exactement cette règle.

**EN.** Roundtrip: the canonical weight of the family induced by an
estimation rule recovers exactly that rule. -/
theorem canonicalWeight_familyOfEstimationRule {n : ℕ} (E : EffectPerspectives.EstimationRule n)
    (D : EffectPerspectives.EffectPerspective n) (i : Fin D.outcomes) :
    canonicalWeight (familyOfEstimationRule E) D i = E.weight D i := by
  letI := (Effects.interface n).cellFintype D
  show (∑ c : Fin D.outcomes, E.weight D c * Act.indicator (I := Effects.interface n) i c) = E.weight D i
  rw [Finset.sum_eq_single i]
  · rw [Act.indicator_self, mul_one]
  · intro d _ hdi
    rw [Act.indicator_of_ne (fun hh => hdi (Fin.val_injective hh)), mul_zero]
  · exact fun hnot => (hnot (Finset.mem_univ i)).elim

end EverettianProbability.Abstract
