# Release notes — v2.4.0-journal-audit

Release date: 2026-08-26

This release freezes the downstream Lean developments added for the Journal of
Automated Reasoning major-revision campaign. It does not change the stable
conditional or exact-finite APIs and it does not change the upstream dependency
pins.

## Journal-revision additions

### L0 — typed relative-necessity campaign

`EverettianProbability/Audit/PremiseNecessity.lean` audits the exact interfaces
used in the revised manuscript.

- `W0` gives the dimension-two boundary witness.
- `W1`–`W5` delete, one at a time, the separately exposed weight-level premises
  while retaining the other premises and falsifying the exact Born conclusion.
- `D1`–`D3` lift the relevant deletion tests to the public
  `RationalExpectationFamily` interface.

These are relative-necessity witnesses for fixed theorem interfaces, not a
claim of absolute pairwise independence or a globally minimal axiomatization.

### L2 — dimension-two Uhlhorn boundary

`EverettianProbability/Audit/UhlhornDimensionTwo.lean` proves
`dimensionTwo_orthogonality_not_injective`: there exists a map on `Proj1 2`
that preserves orthogonality in the public one-way sense but is not injective.
The theorem is a sharp boundary witness for that non-bijective interface; it is
not a classification of all dimension-two orthogonality preservers.

### L3 — formulation minimality

`EverettianProbability/Audit/Minimality.lean` proves:

- `axNorm_iff_singletonTop_of_axGrain`, reducing all-perspective weight
  normalization to the singleton-top perspective under Grain;
- `normalizedConst_iff_zero_one_of_affine`, reducing full constant
  normalization of a raw affine valuation to constants `0` and `1`.

The second theorem intentionally works before bundling into
`RationalExpectationFamily`, where normalization on constants is already a
constitutive field.

## Publication-facing audit

`EverettianProbability/Audit/JournalCore.lean` now checks and prints axioms for
the earlier journal-audit declarations and for all L0/L2/L3 publication-facing
declarations above. The Lean GitHub Actions workflow fails if this consolidated
journal audit reports `sorryAx`.

## Trust and reproducibility

The release uses the repository's pinned Lean toolchain and dependency
revisions. Reproduce the journal-facing audit with:

```sh
lake build EverettianProbability
lake env lean EverettianProbability/Audit/PremiseNecessity.lean
lake env lean EverettianProbability/Audit/UhlhornDimensionTwo.lean
lake env lean EverettianProbability/Audit/JournalCore.lean
bash scripts/guard.sh
```

The expected project-specific result is that no audited declaration depends on
`sorryAx`; ordinary Lean/Mathlib logical axioms reported by `#print axioms` are
not project axioms.

## Upstream pins

Unchanged from the preceding coordinated journal-audit release:

- Quantum Foundations: `v1.3.1-journal-audit`, commit
  `f773ed5694c610af055b82427da27a69d528b776`.
- Gleason: `v1.1.0-journal-audit`, commit
  `5c5bc40d2e4a31a0d1b3112fcc9a3e92b2000ec5` (transitive through Quantum
  Foundations).

The record-to-interference gate-count theorem used as Contribution 3 of the
revised manuscript remains in the already-pinned Quantum Foundations release;
this downstream EP release does not duplicate or modify it.

## Archival metadata

`CITATION.cff` and `.zenodo.json` are prepared for version `2.4.0` and tag
`v2.4.0-journal-audit`. The version-specific Zenodo DOI is intentionally not
hard-coded before the archive is minted.
