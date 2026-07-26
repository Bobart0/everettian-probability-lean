import EverettianProbability.Refinement.PayoffPreserving
import EverettianProbability.BornCalibration.ContextualWeight
import EverettianProbability.Preference.Nonvacuity
import EverettianProbability.Rivals.NaiveBranchCounting

/-!
**FR.** # Vacuité de la lecture globale

Cette définition est conservée exclusivement comme résultat négatif. Exiger
qu'un même acte total coïncide avec son propre tiré-en-arrière pour tous les
raffinements le force à être constant sur toutes les cellules accessibles.
L'invariance filtrée par cette condition est donc satisfaite par toute famille
rationnelle et ne doit pas servir de prémisse normative.

**EN.** # Vacuity of the global reading

This definition is retained exclusively as a negative result. Requiring one
total act to agree with its own pullback along every refinement forces it to be
constant on every accessible cell. Invariance filtered by this condition is
therefore satisfied by every rational family and must not be used as a
normative premise.
-/

namespace EverettianProbability.Refinement

open QuantumFoundations.BornRule Gleason EverettianProbability.Core
open EverettianProbability.Preference
open EverettianProbability.BornCalibration EverettianProbability.Rivals
open scoped Classical

variable {n : ℕ}

/-- **FR.** Ancienne lecture globale, conservée uniquement pour formaliser sa
vacuité ; elle ne doit pas être employée comme prémisse.

**EN.** Former global reading, retained only to formalize its vacuity; it must
not be used as a premise. -/
def GloballyPayoffPreserving (a : Act n) : Prop :=
  ∀ {D' D : Perspective n} (r : Refines D' D),
    Act.AgreeOn D' a (pullbackAct r a)

private noncomputable def emptyPerspective : Perspective 0 where
  cells := ∅
  nz := by simp
  ortho := by simp
  span := by
    rw [Finset.coe_empty, sSup_empty]
    exact Subsingleton.elim _ _

private theorem dimension_pos_of_family (F : RationalExpectationFamily n) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  have hle := F.monotone emptyPerspective (Act.const 1) (Act.const 0) (by
    intro c hc
    exact False.elim (by simpa [emptyPerspective] using hc))
  rw [F.normalized_const emptyPerspective 1,
    F.normalized_const emptyPerspective 0] at hle
  norm_num at hle

private theorem top_ne_bot_of_pos (hn : 0 < n) :
    (⊤ : Submodule ℂ (H n)) ≠ ⊥ := by
  intro h
  have hfin : Module.finrank ℂ (⊤ : Submodule ℂ (H n)) = n := by
    rw [finrank_top]
    simp
  rw [h] at hfin
  simp at hfin
  omega

/-- **FR.** La perspective singleton explicite `{⊤}` en dimension non nulle.

**EN.** The explicit singleton perspective `{⊤}` in nonzero dimension. -/
noncomputable def singletonTopPerspective (hn : 0 < n) : Perspective n where
  cells := {⊤}
  nz := by
    intro c hc
    rw [Finset.mem_singleton] at hc
    subst c
    exact top_ne_bot_of_pos hn
  ortho := by
    intro c hc c' hc' hne
    simp only [Finset.mem_singleton] at hc hc'
    exact (hne (hc.trans hc'.symm)).elim
  span := by simp

private theorem refines_singletonTop (hn : 0 < n) (D : Perspective n) :
    Refines D (singletonTopPerspective hn) := by
  intro c hc
  refine ⟨⊤, ?_, le_top⟩
  simp only [singletonTopPerspective, Finset.mem_singleton]

/-- **FR.** Un acte globalement préservant est constant, de valeur `a ⊤`, sur
toutes les cellules de toutes les perspectives accessibles.

**EN.** A globally preserving act is constant, with value `a ⊤`, on all cells
of all accessible perspectives. -/
theorem globallyPayoffPreserving_const (hn : 0 < n) (a : Act n)
    (ha : GloballyPayoffPreserving a) :
    ∀ (D : Perspective n) (c : Submodule ℂ (H n)), c ∈ D.cells → a c = a ⊤ := by
  intro D c hc
  let r : Refines D (singletonTopPerspective hn) := refines_singletonTop hn D
  have h := ha r c hc
  have hp : parentOf r c = (⊤ : Submodule ℂ (H n)) := by
    have := parentOf_mem r hc
    simpa only [singletonTopPerspective, Finset.mem_singleton] using this
  change a c = a (parentOf r c) at h
  rwa [hp] at h

/-- **FR.** Sur une fibre propre, l'indicatrice du parent n'est pas
globalement préservante.

**EN.** On a proper fiber, the parent's indicator is not globally preserving. -/
theorem not_globallyPayoffPreserving_indicator
    {D' D : Perspective n} (r : Refines D' D)
    {c' c : Submodule ℂ (H n)} (hc' : c' ∈ D'.cells) (hc : c ∈ D.cells)
    (hle : c' ≤ c) (hne : c' ≠ c) :
    ¬ GloballyPayoffPreserving (Act.indicator c) := by
  intro hglobal
  have h := hglobal r c' hc'
  have hp := parentOf_eq_of_le r hc' hc hle
  change Act.indicator c c' = Act.indicator c (parentOf r c') at h
  rw [hp, Act.indicator_self, Act.indicator_of_ne hne] at h
  norm_num at h

/-- **FR.** La prémisse globale filtrée est sans force : toute famille
rationnelle la satisfait.

**EN.** The filtered global premise has no force: every rational family
satisfies it. -/
theorem globalPremise_vacuous (F : RationalExpectationFamily n) :
    ∀ {D' D : Perspective n} (r : Refines D' D) (a : Act n),
      GloballyPayoffPreserving a → F.V D' (pullbackAct r a) = F.V D a := by
  intro D' D r a ha
  have hn := dimension_pos_of_family F
  calc
    F.V D' (pullbackAct r a) = F.V D' (Act.const (a ⊤)) := by
      apply V_congr_of_agreeOn F D'
      intro c' hc'
      change a (parentOf r c') = a ⊤
      exact globallyPayoffPreserving_const hn a ha D (parentOf r c') (parentOf_mem r hc')
    _ = a ⊤ := F.normalized_const D' (a ⊤)
    _ = F.V D (Act.const (a ⊤)) := (F.normalized_const D (a ⊤)).symm
    _ = F.V D a := by
      apply V_congr_of_agreeOn F D
      intro c hc
      exact (globallyPayoffPreserving_const hn a ha D c hc).symm

private theorem canonicalWeight_uniform_on_cells (D : Perspective 3)
    {c : Submodule ℂ (H 3)} (hc : c ∈ D.cells) :
    canonicalWeight uniformExpectationFamily D c = naiveCounting 3 D c := by
  classical
  unfold canonicalWeight uniformExpectationFamily uniformExpectation naiveCounting
  simp only [if_pos hc]
  rw [Finset.sum_eq_single c]
  · simp only [Act.indicator_self, one_div]
  · intro d hd hdc
    rw [Act.indicator_of_ne hdc]
  · exact fun hnot => (hnot hc).elim

private theorem uniformCanonicalWeight_violates_grain :
    ¬ AxGrain (canonicalWeight uniformExpectationFamily) := by
  intro hcanonical
  apply naiveCounting_violates_grain
  apply (axGrain_iff_coarseCells (naiveCounting 3)).2
  intro D' D r c hc
  have hgrain := (axGrain_iff_coarseCells
    (canonicalWeight uniformExpectationFamily)).1 hcanonical D' D r c hc
  calc
    naiveCounting 3 D c = canonicalWeight uniformExpectationFamily D c :=
      (canonicalWeight_uniform_on_cells D hc).symm
    _ = ∑ c' ∈ coarseCells D' c,
        canonicalWeight uniformExpectationFamily D' c' := hgrain
    _ = ∑ c' ∈ coarseCells D' c, naiveCounting 3 D' c' := by
      apply Finset.sum_congr rfl
      intro c' hc'
      exact canonicalWeight_uniform_on_cells D'
        ((mem_coarseCells_iff D' c c').mp hc').1

/-- **FR.** Témoin nommé de la vacuité : la famille uniforme satisfait la
prémisse globale filtrée, alors que son poids canonique viole `AxGrain`.

**EN.** Named witness of vacuity: the uniform family satisfies the filtered
global premise while its canonical weight violates `AxGrain`. -/
theorem uniformExpectationFamily_globalPremise_vacuous :
    (∀ {D' D : Perspective 3} (r : Refines D' D) (a : Act 3),
      GloballyPayoffPreserving a →
        uniformExpectationFamily.V D' (pullbackAct r a) =
          uniformExpectationFamily.V D a) ∧
      ¬ AxGrain (canonicalWeight uniformExpectationFamily) :=
  ⟨globalPremise_vacuous uniformExpectationFamily,
    uniformCanonicalWeight_violates_grain⟩

end EverettianProbability.Refinement
