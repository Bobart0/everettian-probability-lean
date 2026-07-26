import EverettianProbability.BornCalibration.ContextualWeight

/-!
**FR.** # Théorème de représentation canonique

Sur une perspective finie, une fonctionnelle rationnelle est représentée par
ses valeurs sur les actes indicateurs. Le représentant est fixé canoniquement à
zéro hors des cellules ; l'unicité mathématiquement pertinente est l'unicité
sur `D.cells`.

**EN.** # Canonical representation theorem

On a finite perspective, a rational functional is represented by its values on
indicator acts. The representative is canonically fixed to zero outside the
cells; the mathematically relevant uniqueness is uniqueness on `D.cells`.
-/

namespace EverettianProbability.Preference

open QuantumFoundations.BornRule Gleason EverettianProbability.Core
open EverettianProbability.BornCalibration

variable {n : ℕ}

private theorem V_zero (F : RationalExpectationFamily n) (D : Perspective n) :
    F.V D (Act.const 0) = 0 :=
  F.normalized_const D 0

private theorem V_smul (F : RationalExpectationFamily n) (D : Perspective n)
    (t : ℝ) (a : Act n) :
    F.V D (fun c => t * a c) = t * F.V D a := by
  have h := F.affine D t a (Act.const 0)
  rw [F.normalized_const D 0] at h
  simpa only [Act.const, mul_zero, add_zero] using h

private theorem V_add (F : RationalExpectationFamily n) (D : Perspective n)
    (a b : Act n) :
    F.V D (fun c => a c + b c) = F.V D a + F.V D b := by
  calc
    F.V D (fun c => a c + b c) =
        F.V D (fun c => (1 / 2 : ℝ) * (2 * a c) +
          (1 - (1 / 2 : ℝ)) * (2 * b c)) := by
            congr 2
            funext c
            ring
    _ = (1 / 2 : ℝ) * F.V D (fun c => 2 * a c) +
        (1 - (1 / 2 : ℝ)) * F.V D (fun c => 2 * b c) :=
      F.affine D (1 / 2 : ℝ) (fun c => 2 * a c) (fun c => 2 * b c)
    _ = F.V D a + F.V D b := by
      rw [V_smul F D 2 a, V_smul F D 2 b]
      ring

private theorem V_sum {ι : Type*} (F : RationalExpectationFamily n)
    (D : Perspective n) (s : Finset ι) (f : ι → Act n) :
    F.V D (fun c => s.sum fun i => f i c) = s.sum fun i => F.V D (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change F.V D (Act.const 0) = 0
      exact V_zero F D
  | @insert i s hi ih =>
      calc
        F.V D (fun c => (insert i s).sum fun j => f j c) =
            F.V D (fun c => f i c + s.sum fun j => f j c) := by
          congr 2
          funext c
          rw [Finset.sum_insert hi]
        _ = F.V D (f i) + F.V D (fun c => s.sum fun j => f j c) :=
          V_add F D (f i) (fun c => s.sum fun j => f j c)
        _ = F.V D (f i) + s.sum fun j => F.V D (f j) := by rw [ih]
        _ = (insert i s).sum fun j => F.V D (f j) := by
          rw [Finset.sum_insert hi]

/-- **FR.** Toute fonctionnelle rationnelle est la somme finie pondérée par
son poids canonique sur les cellules de la perspective.

**EN.** Every rational functional is the finite sum weighted by its canonical
weight on the perspective's cells. -/
theorem represents (F : RationalExpectationFamily n) (D : Perspective n)
    (a : Act n) :
    F.V D a = ∑ c ∈ D.cells, canonicalWeight F D c * a c := by
  classical
  calc
    F.V D a = F.V D (Act.indicatorExpansion D a) :=
      V_congr_of_agreeOn F D (Act.agreeOn_indicatorExpansion D a)
    _ = F.V D (fun x => ∑ c ∈ D.cells, (fun y => a c * Act.indicator c y) x) := rfl
    _ = ∑ c ∈ D.cells, F.V D (fun y => a c * Act.indicator c y) :=
      V_sum F D D.cells fun c y => a c * Act.indicator c y
    _ = ∑ c ∈ D.cells, a c * F.V D (Act.indicator c) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact V_smul F D (a c) (Act.indicator c)
    _ = ∑ c ∈ D.cells, canonicalWeight F D c * a c := by
      apply Finset.sum_congr rfl
      intro c hc
      simp only [canonicalWeight, if_pos hc]
      ring

/-- **FR.** Tout autre système représentant la fonctionnelle coïncide avec le
poids canonique sur les cellules, et seulement cette restriction est requise.

**EN.** Every other system representing the functional agrees with the
canonical weight on the cells, and only this restriction is required. -/
theorem weights_unique_on_cells (F : RationalExpectationFamily n)
    (D : Perspective n) (p : Submodule ℂ (H n) → ℝ)
    (hp : ∀ a : Act n, F.V D a = ∑ c ∈ D.cells, p c * a c) :
    ∀ c ∈ D.cells, p c = canonicalWeight F D c := by
  classical
  intro c hc
  have h := hp (Act.indicator c)
  rw [Finset.sum_eq_single c] at h
  · simpa only [Act.indicator_self, mul_one, canonicalWeight, if_pos hc] using h.symm
  · intro d hd hdc
    rw [Act.indicator_of_ne hdc, mul_zero]
  · exact fun hnot => (hnot hc).elim

/-- **FR.** La positivité du poids canonique est dérivée de la monotonie
locale : l'indicatrice d'une cellule domine l'acte constant nul sur les
cellules de la perspective.

**EN.** Positivity of the canonical weight follows from local monotonicity:
a cell indicator dominates the zero constant on the perspective's cells. -/
theorem canonicalWeight_axPos (F : RationalExpectationFamily n) :
    AxPos (canonicalWeight F) := by
  intro D c hc
  rw [show canonicalWeight F D c = F.V D (Act.indicator c) by
    simp only [canonicalWeight, if_pos hc]]
  rw [← F.normalized_const D 0]
  apply F.monotone D (Act.const 0) (Act.indicator c)
  intro d hd
  unfold Act.const Act.indicator
  split_ifs <;> norm_num

/-- **FR.** La normalisation du poids canonique est dérivée de la
normalisation des actes constants, via la représentation appliquée à l'acte
constant unitaire.

**EN.** Normalization of the canonical weight follows from normalization of
constant acts, via representation applied to the unit constant act. -/
theorem canonicalWeight_axNorm (F : RationalExpectationFamily n) :
    AxNorm (canonicalWeight F) := by
  intro D
  have h := represents F D (Act.const 1)
  rw [F.normalized_const D 1] at h
  simpa only [Act.const, mul_one] using h.symm

end EverettianProbability.Preference
