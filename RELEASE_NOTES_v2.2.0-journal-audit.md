# Release notes — v2.2.0-journal-audit

**EN.** Release notes for the coordinated pre-journal audit release, the
third (downstream) link of the `gleason-theorem-lean →
quantum-foundations-lean → everettian-probability-lean` chain.

## Identification

- Selected release tag: `v2.2.0-journal-audit`
- Starting commit SHA (before this release's changes):
  `a92a07746a509c8740c1702fcff8ce3a1dabf0aa` (also the commit tagged
  `v2.1.0`; this release does not move or replace that tag)
- Upstream `quantum_foundations` dependency: tag `v1.3.0-journal-audit`,
  resolved commit `747d8f441b5cd7beaa579662a535366030efe322`
- Transitive `gleason` dependency: tag `v1.1.0-journal-audit`, resolved
  commit `5c5bc40d2e4a31a0d1b3112fcc9a3e92b2000ec5` (identical to the direct
  pin in `quantum-foundations-lean` itself — verified by `preflight.sh`)
- Lean toolchain: `leanprover/lean4:v4.32.0-rc1`
- Mathlib commit: `8bba4200986270d3b30be2bb2f8840af47a7854f`

The final tagged commit's own SHA is intentionally not recorded here, since
this file is itself part of the commit that produces it; see the execution
report for that value.

## Version numbering note

An existing tag `v2.1.0` already points at this release's starting commit
(`a92a077`, `chore(release): prepare v2.1.0`). To avoid reusing that version
number for a different released state, this release bumps to `2.2.0`
(a minor version, consistent with the new public declarations it adds)
rather than `2.1.0-journal-audit`. `v2.1.0` is untouched.

## New declarations: decision-level non-Born countermodel

**EN.** `grain_does_not_imply_born_at_two` (pre-existing,
`BornCalibration/NonCircularity.lean`) refutes non-circularity at the
**weight** level: a coherent estimation rule under
`AxGrain`/`AxNorm`/`AxPos`/`AxNul` that is not `‖·‖²`, at `n = 2`. This
release adds the analogous **decision**-level countermodel, stated directly
on the premises used by `born_expectation_of_invariance`
(`BornCalibration/DecisionNonCircularity.lean`, new file):

- `skewExpectationFamily : RationalExpectationFamily 2` — the rational
  expectation family induced by the rival weight `skewWeight witnessState`
  (already public in `NonCircularity.lean`).
- `skewExpectationFamily_canonicalWeight_eq {D c} (hc : c ∈ D.cells) :
  canonicalWeight skewExpectationFamily D c = skewWeight witnessState D c`
  — the canonical-weight equality theorem.
- `skewExpectationFamily_refinementInvariantLocal :
  RefinementInvariantLocal skewExpectationFamily.V` — the refinement-
  invariance theorem, obtained via `refinementInvariantLocal_iff_axGrain`
  after transporting `skewWeight_axGrain` through the equality above.
- `decision_premises_do_not_imply_born_at_two : ∃ F v, ‖v‖ = 1 ∧
  RefinementInvariantLocal F.V ∧ AxNul (canonicalWeight F) v ∧ ∃ D c, c ∈
  D.cells ∧ canonicalWeight F D c ≠ ‖projL c v‖ ^ 2` — the application-level
  countermodel. Does not claim `3 ≤ n` or the bundled `ProjectiveBornPremises`.

A single small public lemma, `witnessLine_skewWeight_ne_born`, was added to
`NonCircularity.lean` itself (and reused to simplify
`grain_does_not_imply_born_at_two`'s own proof) so the new file could reuse
the concrete numeric inequality without exposing the private `skewF`
construction or duplicating `NonCircularity.lean`'s geometric argument.

## Claim corrections

- **Weight-level vs. decision-level countermodels**, now explicitly
  distinguished in `README.md`, `CLAIM_MATRIX.md`,
  `docs/CONDITIONAL_BORN_SCOPE.md`, and `docs/SCOPE_AND_LIMITATIONS.md`.
- **Bundled vs. separate premises**: `ProjectiveBornPremises`
  (`API/ConditionalBorn.lean`, unchanged fields) is documented as an API
  design choice, not a logical necessity; no field is claimed irreducible.
  The two countermodels above rely on the separate theorem-level arguments,
  which the bundled structure does not itself provide.

## New focused publication audit

`EverettianProbability/Audit/JournalCore.lean`: `#check`s the public
contract and runs `#print axioms` on the representation infrastructure
(`represents`, `canonicalWeight_axPos`, `canonicalWeight_axNorm`), the Grain
bridge (`refinementInvariantLocal_iff_axGrain`,
`born_expectation_of_invariance`), both countermodels, the rival-weight
witnesses (`globalPremise_vacuous`,
`uniformExpectationFamily_globalPremise_vacuous`,
`naiveCounting_violates_grain`, `fourthPowerWeight_not_axNorm`), and the
unchanged stable conditional API aggregate (`conditionalBornMainResults`).
Added to `.github/workflows/lean.yml` alongside the existing consolidated
axiom audit (neither removed nor weakened).

## Scope protection

No file under `EverettianProbability/ExactFinite/`,
`EverettianProbability/Frequency/`, or `EverettianProbability/Confirmation/`
was changed by this release (`git diff --name-only <START_SHA>..HEAD --
EverettianProbability/ExactFinite EverettianProbability/Frequency
EverettianProbability/Confirmation` returns no path).

## Trust boundary

Expected for every declaration audited above:

```
[propext, Classical.choice, Quot.sound]
```

No project-specific axiom, no `sorry`, no `native_decide`,
`SORRY_COUNT ≤ SORRY_BUDGET` (both `0`).

## Verification commands

```bash
lake exe cache get
bash scripts/preflight.sh
lake build
bash scripts/guard.sh
lake env lean EverettianProbability/Audit/JournalCore.lean
lake env lean EverettianProbability/Audit/ConditionalAPIContract.lean
lake env lean EverettianProbability/Audit/ExactFiniteAPIContract.lean
lake env lean EverettianProbability/Audit/MainResults.lean
git diff --check
```
