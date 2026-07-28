import EverettianProbability.SelfLocation.CredenceUniqueness

/-!
**FR.** # Indifférence à l'élimination d'alternatives incompatibles

Ce module remplace la prémisse directe de proportionnalité canonique par une
condition sémantique plus primitive. Lorsqu'un record accessible devient plus
informatif, il peut éliminer certaines alternatives, sans modifier les cotes
relatives entre celles qui restent compatibles.

La propriété est formulée par produit croisé, sans division :
`C_S(c) C_T(d) = C_S(d) C_T(c)`, où `S ⊆ T` et `c,d ∈ S`. Avec l'accord sur
le record non restreint, elle implique la proportionnalité canonique ; la
normalisation redonne alors l'unique crédence conditionnée précédente.

L'invariance des rapports est une prémisse sémantique (`SEM`). Elle n'est pas
dérivée de la dynamique unitaire, de la décohérence ou de la seule structure
hilbertienne.

**EN.** # Indifference to eliminating incompatible alternatives

This module replaces the direct canonical-proportionality premise with a more
primitive semantic condition. When an accessible record becomes more
informative, it may eliminate alternatives without changing the relative odds
among the alternatives that remain compatible.

The property is stated by cross multiplication, without division:
`C_S(c) C_T(d) = C_S(d) C_T(c)`, where `S ⊆ T` and `c,d ∈ S`. Together with
agreement on the unrestricted record, it implies canonical proportionality;
normalization then recovers the unique previous conditioned credence.

Odds invariance is a semantic (`SEM`) premise. It is not derived from unitary
dynamics, decoherence, or Hilbert-space structure alone.
-/

namespace EverettianProbability.Abstract

open scoped BigOperators Classical

noncomputable section

variable {I : PerspectiveInterface}

namespace RecordCredenceFamily

/-- Relative odds among surviving alternatives are invariant when an
accessible record is restricted.

The cross-multiplication form avoids division by an individual credence. It
does not assert indifference between the two cells; it says only that removing
other alternatives leaves their relative odds unchanged. This is an explicit
semantic (`SEM`) premise. -/
def OddsInvariantUnderRecordRestriction
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I) : Prop :=
  ∀ (D : I.Perspective)
    (smaller larger : Finset (I.Cell D))
    (hsubset : smaller ⊆ larger)
    (hsmaller :
      recordCompatibleMass F D smaller ≠ 0)
    (hlarger :
      recordCompatibleMass F D larger ≠ 0)
    (c d : I.Cell D),
    c ∈ smaller →
    d ∈ smaller →
      C.credence D smaller c *
          C.credence D larger d =
        C.credence D smaller d *
          C.credence D larger c

theorem canonicalRecordCredenceFamily_oddsInvariantUnderRecordRestriction
    (F : RationalExpectationFamily I) :
    (canonicalRecordCredenceFamily F).OddsInvariantUnderRecordRestriction F := by
  intro D smaller larger hsubset hsmaller hlarger c d hc hd
  have hc_large : c ∈ larger :=
    hsubset hc
  have hd_large : d ∈ larger :=
    hsubset hd
  simp only [canonicalRecordCredenceFamily_credence]
  simp [
    recordConditionedCredence,
    hsmaller,
    hlarger,
    hc,
    hd,
    hc_large,
    hd_large
  ]
  field_simp [hsmaller, hlarger]

private theorem exists_mem_canonicalWeight_ne_zero_of_recordCompatibleMass_ne_zero
    (F : RationalExpectationFamily I)
    (D : I.Perspective)
    (compatible : Finset (I.Cell D))
    (hmass :
      recordCompatibleMass F D compatible ≠ 0) :
    ∃ c : I.Cell D,
      c ∈ compatible ∧
        canonicalWeight F D c ≠ 0 := by
  by_contra hexists
  apply hmass
  unfold recordCompatibleMass
  apply Finset.sum_eq_zero
  intro c hc
  by_contra hweight
  apply hexists
  exact ⟨c, hc, hweight⟩

/-- Agreement on the unrestricted record and invariance of relative odds
under record restriction imply canonical proportionality on every nonzero-mass
record. The implication is mathematical; its odds-invariance premise remains
semantic (`SEM`). -/
theorem canonicallyProportionalOnRecords_of_agrees_unrestricted_of_oddsInvariant
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I)
    (hagree :
      C.AgreesOnUnrestrictedRecord F)
    (hodds :
      C.OddsInvariantUnderRecordRestriction F)
    (hInjAll :
      ∀ D : I.Perspective,
        Function.Injective (@I.outcome D)) :
    C.CanonicallyProportionalOnRecords F := by
  intro D compatible hmass
  obtain ⟨reference, href_mem, href_weight⟩ :=
    exists_mem_canonicalWeight_ne_zero_of_recordCompatibleMass_ne_zero
      F D compatible hmass
  refine
    ⟨C.credence D compatible reference /
        canonicalWeight F D reference, ?_⟩
  intro c hc
  have huniv_mass :
      recordCompatibleMass F D Finset.univ ≠ 0 := by
    rw [recordCompatibleMass_univ F D (hInjAll D)]
    norm_num
  have hcross :=
    hodds
      D
      compatible
      Finset.univ
      (by
        intro x hx
        simp)
      hmass
      huniv_mass
      c
      reference
      hc
      href_mem
  rw [
    hagree D (hInjAll D) c,
    hagree D (hInjAll D) reference
  ] at hcross
  field_simp [href_weight]
  simpa [mul_assoc, mul_comm, mul_left_comm] using hcross

/-- Primitive characterization of canonical record-conditioned credence.

Normalization, unrestricted canonical agreement, and odds invariance under
record restriction uniquely determine canonical conditioned credence on every
nonzero-mass record. -/
theorem credence_eq_recordConditionedCredence_of_normalized_of_agrees_unrestricted_of_oddsInvariant
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I)
    (hnorm :
      C.NormalizedOnNonzeroMass F)
    (hagree :
      C.AgreesOnUnrestrictedRecord F)
    (hodds :
      C.OddsInvariantUnderRecordRestriction F)
    (hInjAll :
      ∀ D : I.Perspective,
        Function.Injective (@I.outcome D))
    (D : I.Perspective)
    (compatible : Finset (I.Cell D))
    (hmass :
      recordCompatibleMass F D compatible ≠ 0)
    (c : I.Cell D) :
    C.credence D compatible c =
      recordConditionedCredence
        F D compatible c := by
  have hprop :
      C.CanonicallyProportionalOnRecords F :=
    C.canonicallyProportionalOnRecords_of_agrees_unrestricted_of_oddsInvariant
      F hagree hodds hInjAll
  exact
    C.credence_eq_recordConditionedCredence
      F hnorm hprop
      D compatible hmass c

/-- Any normalized record credence family satisfying unrestricted canonical
agreement and record-restriction odds invariance inherits refinement
coherence. -/
theorem refinementCoherent_of_normalized_of_agrees_unrestricted_of_oddsInvariant
    (C : RecordCredenceFamily I)
    (F : RationalExpectationFamily I)
    (hnorm :
      C.NormalizedOnNonzeroMass F)
    (hagree :
      C.AgreesOnUnrestrictedRecord F)
    (hodds :
      C.OddsInvariantUnderRecordRestriction F)
    (hinv : RefinementInvariantLocal F.V)
    (hInjAll :
      ∀ D : I.Perspective,
        Function.Injective (@I.outcome D)) :
    C.RefinementCoherent F hinv hInjAll := by
  have hprop :
      C.CanonicallyProportionalOnRecords F :=
    C.canonicallyProportionalOnRecords_of_agrees_unrestricted_of_oddsInvariant
      F hagree hodds hInjAll
  intro fine coarse r compatible j hmass
  exact
    C.refinementCoherent_of_normalized_of_proportional
      F hnorm hprop hinv hInjAll r compatible j hmass

end RecordCredenceFamily

end
end EverettianProbability.Abstract
