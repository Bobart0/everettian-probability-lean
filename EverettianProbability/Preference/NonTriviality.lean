import EverettianProbability.Preference.ExpectationFunctional
import EverettianProbability.Preference.Nonvacuity
import EverettianProbability.Core.Nonvacuity

/-!
**FR.** # Non-trivialité — `RationalExpectationFamily`

Témoin négatif requis par la règle 12 de `AGENTS.md` : un fonctionnel qui
satisfait la monotonie et la normalisation sur les constantes, mais viole
l'affinité, et ne peut donc **pas** compléter une `RationalExpectationFamily`.
Le plus instructif n'est pas un objet arbitraire, mais le représentant le
plus simple de ce que l'affinité exclut réellement : le maximum sur les
cellules, `maxExpectation D a := max_{c ∈ D.cells} a c`, cas dégénéré des
fonctionnels de type dépendant du rang (Quiggin 1982, Yaari 1987 ; ici, un
poids `1` sur la meilleure conséquence, `0` ailleurs, plutôt qu'une
pondération probabiliste fixe) — précisément la classe de théories de la
décision non-espérance que `docs/SCOPE_AND_LIMITATIONS.md` signale comme
rejetant l'affinité.

**EN.** # Nontriviality — `RationalExpectationFamily`

Negative witness required by rule 12 of `AGENTS.md`: a functional that
satisfies monotonicity and normalization on constants, but violates
affinity, and therefore **cannot** complete a `RationalExpectationFamily`.
The most instructive choice is not an arbitrary object, but the simplest
representative of what affinity actually excludes: the maximum over cells,
`maxExpectation D a := max_{c ∈ D.cells} a c`, a degenerate case of
rank-dependent-utility functionals (Quiggin 1982, Yaari 1987; here, weight
`1` on the best consequence, `0` elsewhere, rather than a fixed
probabilistic weighting) — precisely the class of non-expected-utility
decision theories that `docs/SCOPE_AND_LIMITATIONS.md` flags as rejecting
affinity.
-/

namespace EverettianProbability.Preference

open QuantumFoundations.BornRule Gleason EverettianProbability.Core

/-- **FR.** Le maximum d'un acte sur les cellules d'une perspective, à
`n = 3` fixé (même dimension que `uniformExpectationFamily`, pour rester
comparable). Bien définie car `D.cells` est non vide
(`Preference.cells_nonempty`).

**EN.** The maximum of an act over a perspective's cells, at fixed `n = 3`
(same dimension as `uniformExpectationFamily`, to stay comparable).
Well-defined because `D.cells` is nonempty (`Preference.cells_nonempty`). -/
noncomputable def maxExpectation (D : Perspective 3) (a : Act 3) : ℝ :=
  D.cells.sup' (cells_nonempty D) a

theorem maxExpectation_monotone (D : Perspective 3) (a b : Act 3)
    (h : ∀ c ∈ D.cells, a c ≤ b c) : maxExpectation D a ≤ maxExpectation D b :=
  Finset.sup'_mono_fun h

theorem maxExpectation_normalized_const (D : Perspective 3) (k : ℝ) :
    maxExpectation D (Act.const k) = k :=
  Finset.sup'_const (cells_nonempty D) k

private theorem exampleLine_ne_orth : exampleLine ≠ exampleLineᗮ := by
  intro heq
  apply exampleLine_ne_bot
  have hd := Submodule.orthogonal_disjoint exampleLine
  rw [← heq] at hd
  exact disjoint_self.mp hd

/-- **FR.** `NONTRIVIALITY`. Sur la perspective binaire explicite
`{exampleLine, exampleLineᗮ}`, le maximum des deux indicatrices vaut `1`
chacun, mais le maximum de leur moyenne (l'acte constant `1/2` sur ces deux
cellules) vaut `1/2 ≠ (1/2)·1 + (1/2)·1 = 1` : `maxExpectation` viole
l'affinité, malgré sa monotonie et sa normalisation. Elle ne peut donc pas
compléter une `RationalExpectationFamily`.

**EN.** `NONTRIVIALITY`. On the explicit binary perspective
`{exampleLine, exampleLineᗮ}`, the maximum of the two indicators is `1`
each, but the maximum of their average (the act constantly `1/2` on these
two cells) is `1/2 ≠ (1/2)·1 + (1/2)·1 = 1`: `maxExpectation` violates
affinity, despite its monotonicity and normalization. It therefore cannot
complete a `RationalExpectationFamily`. -/
theorem maxExpectation_not_affine :
    ¬ (∀ (D : Perspective 3) (t : ℝ) (a b : Act 3),
        maxExpectation D (fun c => t * a c + (1 - t) * b c) =
          t * maxExpectation D a + (1 - t) * maxExpectation D b) := by
  intro haffine
  have h := haffine exampleCoarse (1 / 2)
    (Act.indicator exampleLine) (Act.indicator exampleLineᗮ)
  have hL : exampleLine ∈ exampleCoarse.cells := exampleLine_mem_exampleCoarse
  have hLorth : exampleLineᗮ ∈ exampleCoarse.cells := by
    simp only [exampleCoarse, Perspective.binary, Finset.mem_insert, Finset.mem_singleton,
      or_true]
  have hmaxA : maxExpectation exampleCoarse (Act.indicator exampleLine) = 1 := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro c hc
      unfold Act.indicator
      split_ifs <;> norm_num
    · rw [show (1 : ℝ) = Act.indicator exampleLine exampleLine from (Act.indicator_self _).symm]
      exact Finset.le_sup' _ hL
  have hmaxB : maxExpectation exampleCoarse (Act.indicator exampleLineᗮ) = 1 := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro c hc
      unfold Act.indicator
      split_ifs <;> norm_num
    · rw [show (1 : ℝ) = Act.indicator exampleLineᗮ exampleLineᗮ from (Act.indicator_self _).symm]
      exact Finset.le_sup' _ hLorth
  have hconst : ∀ c ∈ exampleCoarse.cells,
      (1 / 2 : ℝ) * Act.indicator exampleLine c + (1 - 1 / 2) * Act.indicator exampleLineᗮ c
        = 1 / 2 := by
    intro c hc
    simp only [exampleCoarse, Perspective.binary, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · rw [Act.indicator_self, Act.indicator_of_ne exampleLine_ne_orth]
      norm_num
    · rw [Act.indicator_self, Act.indicator_of_ne (Ne.symm exampleLine_ne_orth)]
      norm_num
  have hmaxAvg : maxExpectation exampleCoarse
      (fun c => (1 / 2 : ℝ) * Act.indicator exampleLine c
        + (1 - 1 / 2) * Act.indicator exampleLineᗮ c) = 1 / 2 := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro c hc
      rw [hconst c hc]
    · have hle := Finset.le_sup'
        (fun c => (1 / 2 : ℝ) * Act.indicator exampleLine c
          + (1 - 1 / 2) * Act.indicator exampleLineᗮ c) hL
      rwa [hconst exampleLine hL] at hle
  rw [hmaxAvg, hmaxA, hmaxB] at h
  norm_num at h

end EverettianProbability.Preference
