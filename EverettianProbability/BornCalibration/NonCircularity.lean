import QuantumFoundations.ProbabilityAPI

/-!
**FR.** # Non-circularité — témoin en `n = 2`

Le placeholder de P1 attendait précisément ce contenu : un témoin, en
dimension 2 (le cas qubit, hors de portée du théorème de Gleason et donc
hors de portée de `grainCoherenceTheorem_projector`), d'une règle
d'estimation `Perspective 2 → Submodule ℂ (H 2) → ℝ` **non bornienne**,
satisfaisant pourtant `AxGrain`, `AxNorm`, `AxPos` et `AxNul`.

Ce témoin réfute précisément l'objection selon laquelle la prémisse
d'invariance sous raffinement (`RefinementInvariantLocal`, préservée par
`F.V`) *serait*, déguisée, la règle de Born elle-même : puisqu'il existe une
règle d'estimation cohérente sous Grain qui n'est *pas* `‖·‖²`, la
conclusion « Grain + Norm + Pos + Null ⟹ Born » côté mesure (qui échoue
précisément en dimension 2, où le théorème de Gleason ne s'applique pas)
n'absorbe pas silencieusement la prémisse normative côté décision — celle-ci
fait un travail non trivial, indépendant du contenu hilbertien qui produit
Born en dimension `≥ 3`.

**Construction.** `perspective_two_cases` établit le fait structurel qui
rend tout le reste possible : en dimension 2, toute perspective est soit le
singleton `{⊤}`, soit une paire `{L, Lᗮ}` — aucune perspective n'a plus de
deux cellules. `skewWeight v D c := f (‖projL c v‖²)`, avec
`f x = x² / (x² + (1-x)²)`, ne dépend pas de `D` et vaut `f(0)=0`,
`f(1)=1`, `f(x)+f(1-x)=1` : ces trois faits suffisent, combinés à
`perspective_two_cases`, à établir `AxPos`, `AxNul`, `AxNorm` et `AxGrain`
pour `skewWeight v`, dès que `‖v‖=1`. Le témoin explicite
`witnessState := (3/5, 4/5)` (base computationnelle, amplitudes inégales)
donne `‖projL witnessLine witnessState‖² = 9/25`, et
`f(9/25) = 81/337 ≠ 9/25` : la règle diffère effectivement de Born sur ce
témoin concret.

**EN.** # Non-circularity — witness at `n = 2`

The P1 placeholder was waiting for exactly this content: a witness, in
dimension 2 (the qubit case, out of reach of Gleason's theorem and
therefore of `grainCoherenceTheorem_projector`), of an estimation rule
`Perspective 2 → Submodule ℂ (H 2) → ℝ` that is **not** Born-based, yet
satisfies `AxGrain`, `AxNorm`, `AxPos`, and `AxNul`.

This witness refutes precisely the objection that the refinement-invariance
premise (`RefinementInvariantLocal`, preserved by `F.V`) *is*, in disguise,
the Born rule itself: since a Grain-coherent estimation rule exists that is
*not* `‖·‖²`, the measurement-side conclusion "Grain + Norm + Pos + Null ⟹
Born" (which fails precisely in dimension 2, where Gleason's theorem does
not apply) does not silently absorb the decision-side normative premise —
the latter does nontrivial work, independent of the Hilbert-space content
that produces Born in dimension `≥ 3`.

**Construction.** `perspective_two_cases` establishes the structural fact
that makes everything else possible: in dimension 2, every perspective is
either the singleton `{⊤}` or a pair `{L, Lᗮ}` — no perspective has more
than two cells. `skewWeight v D c := f (‖projL c v‖²)`, with
`f x = x² / (x² + (1-x)²)`, does not depend on `D` and satisfies `f(0)=0`,
`f(1)=1`, `f(x)+f(1-x)=1`: these three facts, combined with
`perspective_two_cases`, suffice to establish `AxPos`, `AxNul`, `AxNorm`,
and `AxGrain` for `skewWeight v`, as soon as `‖v‖=1`. The explicit witness
`witnessState := (3/5, 4/5)` (computational basis, unequal amplitudes)
gives `‖projL witnessLine witnessState‖² = 9/25`, and
`f(9/25) = 81/337 ≠ 9/25`: the rule genuinely differs from Born on this
concrete witness.
-/

namespace EverettianProbability.BornCalibration

open QuantumFoundations.ProbabilityAPI
open QuantumFoundations.Uhlhorn (projL_singleton_unit)
open scoped Classical

/-! ## Structural classification of perspectives in `H 2` -/

private theorem top_ne_bot_H2 : (⊤ : Submodule ℂ (H 2)) ≠ ⊥ := by
  intro h
  have h1 : Module.finrank ℂ (⊤ : Submodule ℂ (H 2)) = 2 := by rw [finrank_top]; simp
  rw [h] at h1
  simp at h1

private theorem cells_nonempty_two (D : Perspective 2) : D.cells.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  apply top_ne_bot_H2
  rw [← D.span, hempty]
  simp

private theorem proper_nonzero_finrank_eq_one {c : Submodule ℂ (H 2)} (h0 : c ≠ ⊥) (h2 : c ≠ ⊤) :
    Module.finrank ℂ c = 1 := by
  have hlt1 := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.mpr h0)
  have hlt2 := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr h2)
  have htop : Module.finrank ℂ (⊤ : Submodule ℂ (H 2)) = 2 := by rw [finrank_top]; simp
  rw [finrank_bot] at hlt1
  rw [htop] at hlt2
  omega

private theorem orthogonal_finrank_eq_one {c : Submodule ℂ (H 2)} (h0 : c ≠ ⊥) (h2 : c ≠ ⊤) :
    Module.finrank ℂ cᗮ = 1 := by
  have hsum : Module.finrank ℂ c + Module.finrank ℂ cᗮ = Module.finrank ℂ (H 2) :=
    Submodule.finrank_add_finrank_orthogonal c
  have hc1 := proper_nonzero_finrank_eq_one h0 h2
  have h2dim : Module.finrank ℂ (H 2) = 2 := by simp
  omega

private theorem ne_orthogonal_of_proper {L : Submodule ℂ (H 2)} (h0 : L ≠ ⊥) (_h2 : L ≠ ⊤) :
    L ≠ Lᗮ := by
  intro heq
  apply h0
  have hd := Submodule.orthogonal_disjoint L
  rw [← heq] at hd
  exact disjoint_self.mp hd

/-- **FR.** En dimension 2, toute perspective est soit le singleton `{⊤}`,
soit une paire `{L, Lᗮ}` avec `L` propre et non nul : aucune perspective
n'a plus de deux cellules. C'est le fait structurel qui rend possible tout
le reste de ce fichier — `Grain`, à la différence de `Norm`/`Pos`/`Null`,
ne se transporte pas trivialement de la somme `∑ x_c` à la somme
`∑ f(x_c)` pour `f` non linéaire dès que plus de deux cellules sont en jeu ;
en dimension 2, ce problème ne se pose jamais.

**EN.** In dimension 2, every perspective is either the singleton `{⊤}` or
a pair `{L, Lᗮ}` with `L` proper and nonzero: no perspective has more than
two cells. This is the structural fact that makes the rest of this file
possible — `Grain`, unlike `Norm`/`Pos`/`Null`, does not trivially
transport from the sum `∑ x_c` to the sum `∑ f(x_c)` for nonlinear `f` once
more than two cells are involved; in dimension 2, that problem never
arises. -/
theorem perspective_two_cases (D : Perspective 2) :
    D.cells = {⊤} ∨ ∃ L : Submodule ℂ (H 2), L ≠ ⊥ ∧ L ≠ ⊤ ∧ D.cells = {L, Lᗮ} := by
  by_cases htop : (⊤ : Submodule ℂ (H 2)) ∈ D.cells
  · exact Or.inl (D.singleton_of_mem_top htop)
  · right
    obtain ⟨c₀, hc₀⟩ := cells_nonempty_two D
    have hc₀0 : c₀ ≠ ⊥ := D.nz c₀ hc₀
    have hc₀2 : c₀ ≠ ⊤ := fun h => htop (h ▸ hc₀)
    have hfin0 : Module.finrank ℂ c₀ = 1 := proper_nonzero_finrank_eq_one hc₀0 hc₀2
    have hfinorth : Module.finrank ℂ c₀ᗮ = 1 := orthogonal_finrank_eq_one hc₀0 hc₀2
    have hexists_other : ∃ c₁ ∈ D.cells, c₁ ≠ c₀ := by
      by_contra hcon
      push Not at hcon
      apply hc₀2
      have hsingleton : D.cells = {c₀} :=
        Finset.eq_singleton_iff_unique_mem.mpr ⟨hc₀, fun c hc => hcon c hc⟩
      have hspan := D.span
      rw [hsingleton] at hspan
      simpa using hspan
    obtain ⟨c₁, hc₁mem, hc₁ne⟩ := hexists_other
    have hc₁le : c₁ ≤ c₀ᗮ := D.ortho c₁ hc₁mem c₀ hc₀ hc₁ne
    have hc₁0 : c₁ ≠ ⊥ := D.nz c₁ hc₁mem
    have hc₁2 : c₁ ≠ ⊤ := fun h => htop (h ▸ hc₁mem)
    have hfin1 : Module.finrank ℂ c₁ = 1 := proper_nonzero_finrank_eq_one hc₁0 hc₁2
    have heq1 : c₁ = c₀ᗮ := Submodule.eq_of_le_of_finrank_le hc₁le (by omega)
    refine ⟨c₀, hc₀0, hc₀2, ?_⟩
    apply Finset.ext
    intro x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      by_cases hxc0 : x = c₀
      · exact Or.inl hxc0
      · right
        have hxle : x ≤ c₀ᗮ := D.ortho x hx c₀ hc₀ hxc0
        have hx0 : x ≠ ⊥ := D.nz x hx
        have hx2 : x ≠ ⊤ := fun h => htop (h ▸ hx)
        have hfinx : Module.finrank ℂ x = 1 := proper_nonzero_finrank_eq_one hx0 hx2
        exact Submodule.eq_of_le_of_finrank_le hxle (by omega)
    · intro hx
      rcases hx with rfl | rfl
      · exact hc₀
      · rw [← heq1]; exact hc₁mem

/-! ## The skew weight function -/

/-- **FR.** `f x = x² / (x² + (1-x)²)`. Le dénominateur ne s'annule jamais
(`2(x²+(1-x)²) = (2x-1)² + 1 ≥ 1`), et `f` n'est **pas** l'identité : elle
coïncide avec elle en `x = 0`, `x = 1/2`, `x = 1` seulement (racines de
`2x²-3x+1 = (2x-1)(x-1)`), et en diffère ailleurs — c'est précisément ce
qu'exploite le témoin final.

**EN.** `f x = x² / (x² + (1-x)²)`. The denominator never vanishes
(`2(x²+(1-x)²) = (2x-1)² + 1 ≥ 1`), and `f` is **not** the identity: it
coincides with it only at `x = 0`, `x = 1/2`, `x = 1` (roots of
`2x²-3x+1 = (2x-1)(x-1)`), and differs from it elsewhere — this is exactly
what the final witness exploits. -/
private noncomputable def skewF (x : ℝ) : ℝ := x ^ 2 / (x ^ 2 + (1 - x) ^ 2)

private theorem skewF_denom_pos (x : ℝ) : 0 < x ^ 2 + (1 - x) ^ 2 := by
  nlinarith [sq_nonneg (2 * x - 1)]

private theorem skewF_nonneg (x : ℝ) : 0 ≤ skewF x :=
  div_nonneg (sq_nonneg x) (le_of_lt (skewF_denom_pos x))

private theorem skewF_zero : skewF 0 = 0 := by unfold skewF; norm_num

private theorem skewF_one : skewF 1 = 1 := by unfold skewF; norm_num

private theorem skewF_add_symm (x : ℝ) : skewF x + skewF (1 - x) = 1 := by
  unfold skewF
  have hd : (1 - x) ^ 2 + (1 - (1 - x)) ^ 2 = x ^ 2 + (1 - x) ^ 2 := by ring
  rw [hd, ← add_div, div_self (ne_of_gt (skewF_denom_pos x))]

/-- **FR.** La règle d'estimation rivale : `f` appliquée au carré de la
norme de la projection bornienne. Ignore délibérément son premier argument
(la perspective), tout comme `E₀` en amont.

**EN.** The rival estimation rule: `f` applied to the squared norm of the
Born projection. Deliberately ignores its first argument (the
perspective), exactly as upstream `E₀` does. -/
noncomputable def skewWeight (v : H 2) : Perspective 2 → Submodule ℂ (H 2) → ℝ :=
  fun _ c => skewF (‖projL c v‖ ^ 2)

theorem skewWeight_axPos (v : H 2) : AxPos (skewWeight v) := by
  intro D c _
  exact skewF_nonneg _

theorem skewWeight_axNul (v : H 2) : AxNul (skewWeight v) v := by
  intro D c _ hv
  show skewF (‖projL c v‖ ^ 2) = 0
  have hzero : projL c v = 0 := by
    unfold projL
    rw [ContinuousLinearMap.coe_coe, (Submodule.starProjection_apply_eq_zero_iff c).mpr hv]
  rw [hzero]
  simp [skewF_zero]

private theorem projL_top_id : projL (⊤ : Submodule ℂ (H 2)) = LinearMap.id := by
  unfold projL
  rw [Submodule.starProjection_top]
  rfl

theorem skewWeight_axNorm (v : H 2) (hv : ‖v‖ = 1) : AxNorm (skewWeight v) := by
  intro D
  have htop : D.cells.sup id = (⊤ : Submodule ℂ (H 2)) := by
    rw [Finset.sup_id_eq_sSup]; exact D.span
  have hpyth := QuantumFoundations.BornRule.sum_sq_projL_of_pairwise_isOrtho D.cells D.ortho v
  rw [htop, projL_top_id] at hpyth
  simp only [LinearMap.id_coe, id_eq, hv, one_pow] at hpyth
  rcases perspective_two_cases D with hsingle | ⟨L, hL0, hL2, hLL⟩
  · show ∑ c ∈ D.cells, skewF (‖projL c v‖ ^ 2) = 1
    rw [hsingle, Finset.sum_singleton]
    rw [hsingle, Finset.sum_singleton] at hpyth
    rw [← hpyth, skewF_one]
  · show ∑ c ∈ D.cells, skewF (‖projL c v‖ ^ 2) = 1
    have hLne : L ≠ Lᗮ := ne_orthogonal_of_proper hL0 hL2
    rw [hLL, Finset.sum_insert (by simpa using hLne), Finset.sum_singleton]
    rw [hLL, Finset.sum_insert (by simpa using hLne), Finset.sum_singleton] at hpyth
    rw [show ‖projL Lᗮ v‖ ^ 2 = 1 - ‖projL L v‖ ^ 2 from by linarith [hpyth]]
    exact skewF_add_symm _

private theorem finrank_pos_of_ne_bot {c : Submodule ℂ (H 2)} (h : c ≠ ⊥) :
    0 < Module.finrank ℂ c := by
  have := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.mpr h)
  rwa [finrank_bot] at this

private theorem Lorth_ne_top {L : Submodule ℂ (H 2)} (hL0 : L ≠ ⊥) (_hL2 : L ≠ ⊤) : Lᗮ ≠ ⊤ := by
  intro h
  apply hL0
  have hcong := congrArg Submodule.orthogonal h
  rwa [Submodule.orthogonal_orthogonal, Submodule.top_orthogonal_eq_bot] at hcong

/-- **FR.** `Grain` par `perspective_two_cases` : le seul raffinement non
trivial en dimension 2 est `{L, Lᗮ}` raffinant `{⊤}` (cas où la condition se
réduit à `Norm`, déjà établi) ; toute autre paire de perspectives non
triviales est forcée, par égalité de dimension, à porter exactement les
mêmes deux cellules — la fibre de raffinement y est alors le singleton
`{c}`, et `Grain` y est immédiat puisque `skewWeight` ne dépend pas de la
perspective.

**EN.** `Grain` via `perspective_two_cases`: the only nontrivial refinement
in dimension 2 is `{L, Lᗮ}` refining `{⊤}` (the case where the condition
reduces to `Norm`, already established); any other pair of nontrivial
perspectives is forced, by dimension equality, to carry exactly the same
two cells — the refinement fiber is then the singleton `{c}`, and `Grain`
is immediate there since `skewWeight` does not depend on the perspective. -/
theorem skewWeight_axGrain (v : H 2) (hv : ‖v‖ = 1) : AxGrain (skewWeight v) := by
  apply (axGrain_iff_coarseCells (skewWeight v)).2
  intro D' D r c hc
  rcases perspective_two_cases D with hDsingle | ⟨L, hL0, hL2, hDLL⟩
  · have hc_top : c = ⊤ := by
      rw [hDsingle, Finset.mem_singleton] at hc; exact hc
    subst hc_top
    have hcoarse_eq : coarseCells D' (⊤ : Submodule ℂ (H 2)) = D'.cells := by
      apply Finset.ext
      intro x
      rw [mem_coarseCells_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, le_top⟩⟩
    rw [hcoarse_eq]
    show skewWeight v D (⊤ : Submodule ℂ (H 2)) = ∑ c' ∈ D'.cells, skewWeight v D' c'
    rw [skewWeight_axNorm v hv D']
    show skewF (‖projL (⊤ : Submodule ℂ (H 2)) v‖ ^ 2) = 1
    rw [projL_top_id]
    simp [hv, skewF_one]
  · have hLorth2 : Lᗮ ≠ ⊤ := Lorth_ne_top hL0 hL2
    have hLne : L ≠ Lᗮ := ne_orthogonal_of_proper hL0 hL2
    have hsub : D'.cells ⊆ ({L, Lᗮ} : Finset (Submodule ℂ (H 2))) := by
      intro c' hc'mem
      obtain ⟨c'', hc''mem, hc''le⟩ := r c' hc'mem
      rw [hDLL, Finset.mem_insert, Finset.mem_singleton] at hc''mem
      have hfinc'' : Module.finrank ℂ c'' = 1 := by
        rcases hc''mem with rfl | rfl
        · exact proper_nonzero_finrank_eq_one hL0 hL2
        · exact orthogonal_finrank_eq_one hL0 hL2
      have hc'0 : c' ≠ ⊥ := D'.nz c' hc'mem
      have hfinc'pos : 0 < Module.finrank ℂ c' := finrank_pos_of_ne_bot hc'0
      have hfinc'le : Module.finrank ℂ c' ≤ Module.finrank ℂ c'' :=
        Submodule.finrank_mono hc''le
      have heqc' : c' = c'' := Submodule.eq_of_le_of_finrank_le hc''le (by omega)
      rw [Finset.mem_insert, Finset.mem_singleton, heqc']
      exact hc''mem
    rcases perspective_two_cases D' with hD'single | ⟨M, hM0, hM2, hD'MM⟩
    · exfalso
      have htopmem : (⊤ : Submodule ℂ (H 2)) ∈ D'.cells := by
        rw [hD'single]; exact Finset.mem_singleton_self _
      have hmem := hsub htopmem
      rw [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact hL2 h.symm
      · exact hLorth2 h.symm
    · have hMne : M ≠ Mᗮ := ne_orthogonal_of_proper hM0 hM2
      have hcardL : ({L, Lᗮ} : Finset (Submodule ℂ (H 2))).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simpa using hLne), Finset.card_singleton]
      have hcardM : D'.cells.card = 2 := by
        rw [hD'MM, Finset.card_insert_of_notMem (by simpa using hMne), Finset.card_singleton]
      have hcard : ({L, Lᗮ} : Finset (Submodule ℂ (H 2))).card ≤ D'.cells.card := by
        rw [hcardL, hcardM]
      have hD'eq : D'.cells = ({L, Lᗮ} : Finset (Submodule ℂ (H 2))) :=
        Finset.eq_of_subset_of_card_le hsub hcard
      have hcoarse_eq : coarseCells D' c = {c} := by
        apply Finset.ext
        intro x
        rw [mem_coarseCells_iff, Finset.mem_singleton]
        constructor
        · rintro ⟨hxmem, hxle⟩
          rw [hD'eq, Finset.mem_insert, Finset.mem_singleton] at hxmem
          rw [hDLL, Finset.mem_insert, Finset.mem_singleton] at hc
          have hfinx : Module.finrank ℂ x = 1 := by
            rcases hxmem with rfl | rfl
            · exact proper_nonzero_finrank_eq_one hL0 hL2
            · exact orthogonal_finrank_eq_one hL0 hL2
          have hfinc : Module.finrank ℂ c = 1 := by
            rcases hc with rfl | rfl
            · exact proper_nonzero_finrank_eq_one hL0 hL2
            · exact orthogonal_finrank_eq_one hL0 hL2
          exact Submodule.eq_of_le_of_finrank_le hxle (by omega)
        · intro hxc
          subst hxc
          refine ⟨?_, le_refl x⟩
          rw [hD'eq, ← hDLL]
          exact hc
      rw [hcoarse_eq, Finset.sum_singleton]
      rfl

/-! ## An explicit non-Born witness -/

/-- The state `(3/5, 4/5)` in the computational basis of `H 2`: unequal
amplitudes, unit norm (a 3-4-5 rational Pythagorean triple, chosen to keep
every computation exact and rational). -/
noncomputable def witnessState : H 2 :=
  EuclideanSpace.single (0 : Fin 2) (3 / 5 : ℂ) + EuclideanSpace.single (1 : Fin 2) (4 / 5 : ℂ)

private theorem witnessState_zero : witnessState 0 = 3 / 5 := by
  show (EuclideanSpace.single (0 : Fin 2) (3 / 5 : ℂ) +
    EuclideanSpace.single (1 : Fin 2) (4 / 5 : ℂ)) 0 = 3 / 5
  simp

private theorem witnessState_one : witnessState 1 = 4 / 5 := by
  show (EuclideanSpace.single (0 : Fin 2) (3 / 5 : ℂ) +
    EuclideanSpace.single (1 : Fin 2) (4 / 5 : ℂ)) 1 = 4 / 5
  simp

theorem witnessState_norm : ‖witnessState‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, witnessState_zero, witnessState_one]
  norm_num

private theorem basis0_ne_zero : (EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : H 2) ≠ 0 := by
  intro h
  have hnorm : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : H 2)‖ = 1 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp
  rw [h, norm_zero] at hnorm
  norm_num at hnorm

private theorem basis0_norm : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : H 2)‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp

private theorem witness_inner :
    (inner ℂ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) witnessState : ℂ) = 3 / 5 := by
  rw [EuclideanSpace.inner_single_left, witnessState_zero]
  simp

/-- The computational-basis line spanned by the first basis vector. -/
noncomputable def witnessLine : Submodule ℂ (H 2) := ℂ ∙ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))

private theorem witnessLine_finrank : Module.finrank ℂ witnessLine = 1 :=
  finrank_span_singleton basis0_ne_zero

theorem witnessLine_ne_bot : witnessLine ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  exact ⟨_, Submodule.mem_span_singleton_self _, basis0_ne_zero⟩

theorem witnessLine_ne_top : witnessLine ≠ ⊤ := by
  intro h
  have h1 := witnessLine_finrank
  rw [h, finrank_top] at h1
  simp at h1

private theorem witness_projL :
    projL witnessLine witnessState = (3 / 5 : ℂ) • (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) := by
  unfold witnessLine
  rw [projL_singleton_unit _ _ basis0_norm, witness_inner]

/-- `‖projL witnessLine witnessState‖² = 9/25`: a genuine partial overlap,
neither `0` nor `1/2` nor `1` — the three values where `skewF` happens to
agree with the identity (see `skewF`'s docstring). -/
theorem witness_x : ‖projL witnessLine witnessState‖ ^ 2 = 9 / 25 := by
  rw [witness_projL, norm_smul, basis0_norm]
  norm_num

/-- **FR.** `NON-CIRCULARITY WITNESS`. En dimension 2, où le théorème de
Gleason échoue, `AxGrain`, `AxNorm`, `AxPos` et `AxNul` n'impliquent pas les
poids de Born. La prémisse d'invariance sous raffinement n'est donc pas la
règle de Born déguisée : `skewWeight witnessState` est un contre-exemple
concret, cohérent sous les quatre axiomes, qui diffère effectivement de
Born sur la cellule `witnessLine` de la perspective binaire explicite.

**EN.** `NON-CIRCULARITY WITNESS`. In dimension 2, where Gleason's theorem
fails, `AxGrain`, `AxNorm`, `AxPos`, and `AxNul` do not imply Born weights.
The refinement-invariance premise is therefore not the Born rule in
disguise: `skewWeight witnessState` is a concrete counterexample, coherent
under all four axioms, that genuinely differs from Born on the
`witnessLine` cell of the explicit binary perspective. -/
theorem grain_does_not_imply_born_at_two :
    ∃ (v : H 2) (_ : ‖v‖ = 1),
      AxGrain (skewWeight v) ∧ AxNorm (skewWeight v) ∧
      AxPos (skewWeight v) ∧ AxNul (skewWeight v) v ∧
      ∃ (D : Perspective 2) (c : Submodule ℂ (H 2)),
        c ∈ D.cells ∧ skewWeight v D c ≠ ‖projL c v‖ ^ 2 := by
  refine ⟨witnessState, witnessState_norm,
    skewWeight_axGrain witnessState witnessState_norm,
    skewWeight_axNorm witnessState witnessState_norm,
    skewWeight_axPos witnessState,
    skewWeight_axNul witnessState,
    Perspective.binary witnessLine witnessLine_ne_bot witnessLine_ne_top, witnessLine,
    ?_, ?_⟩
  · exact Finset.mem_insert_self _ _
  · show skewF (‖projL witnessLine witnessState‖ ^ 2) ≠ ‖projL witnessLine witnessState‖ ^ 2
    rw [witness_x]
    unfold skewF
    norm_num

end EverettianProbability.BornCalibration
