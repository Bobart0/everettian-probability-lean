# Everettian Probability in Lean

This Lean 4 / Mathlib repository contains a conditional probability and
decision-theoretic layer built on the finite-dimensional quantum-foundations
library.  The release used by the theorem-centered representation article is a
frozen maintenance snapshot; later research on the default branch is not part
of that artifact.

## Publication-facing witnesses

The article uses this repository for:

- a non-representable projection measure in dimension two;
- a noninjective one-way orthogonality preserver on `Proj1 2`;
- a dimension-two refinement-coherent weight countermodel;
- the W1--W5 deletion witnesses for the separated projective weight
  assumptions.

The neutral audit entry point is:

```sh
bash scripts/verify_publication.sh
```

or directly:

```sh
lake env lean EverettianProbability/Audit/PublicationCore.lean
```

## Dependency chain

Release **v2.4.1** is based on the scientific source tree of v2.4.0 and
repins its upstream dependency to journal-neutral
`quantum-foundations-lean` **v1.4.3**, which in turn pins
`gleason-theorem-lean` **v1.1.2**.  No EverettianProbability theorem source
is changed by this maintenance release.

## Stable APIs

The broader repository also exposes:

```lean
import EverettianProbability.API.ConditionalMainResults
import EverettianProbability.API.ExactFiniteMainResults
```

These APIs are outside the main theorem chain of the representation article
except where explicitly cited.

## Citation

See `CITATION.cff`.  The recommended neutral maintenance snapshot for the
article is version **2.4.1** (tag `v2.4.1`).

## License

Apache License 2.0.
