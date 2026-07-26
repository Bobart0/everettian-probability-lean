import EverettianProbability.Preference.Representation
import EverettianProbability.Refinement.PayoffPreserving

/-!
**FR.** # L'invariance sous raffinement force Grain

Le résultat pivot de l'article II : si la fonctionnelle d'espérance `V`
d'une famille rationnelle est invariante sous toute redescription localement
équivalente (`RefinementInvariantLocal`), alors le poids contextuel
qu'elle induit satisfait l'axiome `AxGrain` de la caractérisation de mesure
amont. Une fois ce pont établi, `grainCoherenceTheorem_projector`
(`QuantumFoundations.BornRule.Assembly`, déjà prouvé, jamais re-prouvé
ici) transforme cette espérance cohérente en espérance de Born — voir
`BornExpectation.lean`. Énoncé comme but ouvert dans ce jalon P1 : c'est le
premier théorème scientifique du programme, hors de portée de P1
(section 7 du prompt de bootstrap).

**EN.** # Refinement invariance forces Grain

The pivotal result of paper II: if the expectation functional `V` of a
rational family is invariant under every locally equivalent redescription
(`RefinementInvariantLocal`), then the contextual weight it induces satisfies the
upstream measure characterization's `AxGrain` axiom. Once this bridge is
established, `grainCoherenceTheorem_projector`
(`QuantumFoundations.BornRule.Assembly`, already proved, never re-proved
here) turns this coherent expectation into a Born expectation — see
`BornExpectation.lean`. Stated as an open goal in this P1 milestone: this is
the first scientific theorem of the program, out of scope for P1
(section 7 of the bootstrap prompt).
-/

namespace EverettianProbability.BornCalibration

open QuantumFoundations.BornRule Gleason
open EverettianProbability.Core EverettianProbability.Preference EverettianProbability.Refinement

variable {n : ℕ}

private theorem indicator_sum_eq (F : RationalExpectationFamily n)
    (D : Perspective n) {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
    (∑ d ∈ D.cells, canonicalWeight F D d * Act.indicator c d) =
      canonicalWeight F D c := by
  classical
  rw [Finset.sum_eq_single c]
  · simp only [Act.indicator_self, mul_one]
  · intro d hd hdc
    rw [Act.indicator_of_ne hdc, mul_zero]
  · exact fun hnot => (hnot hc).elim

private theorem pullback_indicator_sum_eq (F : RationalExpectationFamily n)
    {D' D : Perspective n} (r : Refines D' D)
    {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
    (∑ c' ∈ D'.cells,
        canonicalWeight F D' c' * pullbackAct r (Act.indicator c) c') =
      ∑ c' ∈ coarseCells D' c, canonicalWeight F D' c' := by
  classical
  rw [coarseCells_eq_fiber_parentOf r hc]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c' hc'
  unfold pullbackAct Act.indicator
  simp only [Function.comp_apply]
  by_cases hp : parentOf r c' = c
  · simp only [hp, if_true, mul_one]
  · simp only [hp, if_false, mul_zero]

/-- **FR.** L'invariance locale sous tous les raffinements force l'axiome
`AxGrain` pour le poids canonique.

**EN.** Local invariance under all refinements forces `AxGrain` for the
canonical weight. -/
theorem refinement_invariant_implies_grain (F : RationalExpectationFamily n)
    (hinv : RefinementInvariantLocal F.V) :
    AxGrain (canonicalWeight F) := by
  apply (axGrain_iff_coarseCells (canonicalWeight F)).2
  intro D' D r c hc
  have h := hinv r (pullbackAct r (Act.indicator c)) (Act.indicator c)
    (Act.agreeOn_refl D' (pullbackAct r (Act.indicator c)))
  rw [represents F D' (pullbackAct r (Act.indicator c)),
    represents F D (Act.indicator c),
    pullback_indicator_sum_eq F r hc, indicator_sum_eq F D hc] at h
  exact h.symm

/-- **FR.** Pour toute règle d'estimation cohérente sous Grain, la somme
pondérée d'un acte tiré-en-arrière égale la somme pondérée de l'acte sur la
perspective grossière — la même identité de sommation que
`bornExpectation_pullback_eq`, mais pour un poids `Est` arbitraire satisfaisant
`AxGrain`, pas seulement pour le poids bornien.

**EN.** For any Grain-coherent estimation rule, the weighted sum of a
pulled-back act equals the weighted sum of the act on the coarse
perspective — the same summation identity as `bornExpectation_pullback_eq`,
but for an arbitrary `Est` satisfying `AxGrain`, not only the Born weight. -/
private theorem grain_pullback_sum_eq
    (Est : Perspective n → Submodule ℂ (H n) → ℝ) (hEst : AxGrain Est)
    {D' D : Perspective n} (r : Refines D' D) (a : Act n) :
    (∑ c' ∈ D'.cells, Est D' c' * pullbackAct r a c') =
      ∑ c ∈ D.cells, Est D c * a c := by
  unfold pullbackAct
  simp only [Function.comp_apply]
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun c' hc' => parentOf_mem r hc')
    (fun c' => Est D' c' * a (parentOf r c'))]
  apply Finset.sum_congr rfl
  intro c hc
  rw [← coarseCells_eq_fiber_parentOf r hc]
  calc
    (∑ c' ∈ coarseCells D' c, Est D' c' * a (parentOf r c')) =
        ∑ c' ∈ coarseCells D' c, Est D' c' * a c := by
      apply Finset.sum_congr rfl
      intro c' hc'
      obtain ⟨hc'mem, hc'le⟩ := (mem_coarseCells_iff D' c c').mp hc'
      rw [parentOf_eq_of_le r hc'mem hc hc'le]
    _ = (∑ c' ∈ coarseCells D' c, Est D' c') * a c := by rw [Finset.sum_mul]
    _ = Est D c * a c := by
      have hgrain := (axGrain_iff_coarseCells Est).mp hEst D' D r c hc
      rw [← hgrain]

/-- **FR.** `EQUIVALENCE`. La prémisse normative d'invariance locale sous
raffinement est **exactement** l'axiome `AxGrain` sur le poids canonique : ni
plus forte, ni plus faible. Le sens direct est
`refinement_invariant_implies_grain` ; la réciproque combine `represents` (la
fonctionnelle rationnelle est la somme pondérée par son poids canonique) avec
`grain_pullback_sum_eq` (Grain fait coïncider les deux sommes pondérées de part
et d'autre d'un raffinement), puis retombe sur la forme locale via
`refinementInvariantLocal_iff_pullback`.

**EN.** `EQUIVALENCE`. The normative premise of local refinement invariance
is **exactly** `AxGrain` on the canonical weight: neither stronger nor
weaker. The forward direction is `refinement_invariant_implies_grain`;
the converse combines `represents` (the rational functional is the sum
weighted by its canonical weight) with `grain_pullback_sum_eq` (Grain makes
the two weighted sums coincide across a refinement), then falls back to the
local form via `refinementInvariantLocal_iff_pullback`. -/
theorem refinementInvariantLocal_iff_axGrain (F : RationalExpectationFamily n) :
    RefinementInvariantLocal F.V ↔ AxGrain (canonicalWeight F) := by
  constructor
  · exact refinement_invariant_implies_grain F
  · intro hGrain
    rw [refinementInvariantLocal_iff_pullback]
    intro D' D r a
    rw [represents F D' (pullbackAct r a), represents F D a]
    exact grain_pullback_sum_eq (canonicalWeight F) hGrain r a

end EverettianProbability.BornCalibration
