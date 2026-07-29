# Everettian Probability in Lean v1.0.0
## Stable Conditional Born API

This release stabilizes the first conditional formal result: under explicit
finite-projective `MATH`, `NORM`, `PHYS–NORM`, and `SEM` premises, canonical
weight is Born weight and continuator credence is conditional Born weight.

Recommended public import:

```lean
import EverettianProbability.API.ConditionalMainResults
```

`ProjectiveBornPremises` packages a rational expectation family, normalized
state, `3 ≤ n`, local refinement invariance, and the explicit `AxNul` bridge.
The stable results cover static Born representation, normalized continuator
credence on nonzero fibres, conditional future-act expectation, diachronic
total expectation, chain and tower laws, and admissible-credence uniqueness.

The exact scope is finite and projective. This release does not derive
rationality from unitary dynamics, provide approximate decoherence, a realistic
Hamiltonian, infinite-dimensional dynamics, or complete personal identity.
The pinned `quantum-foundations-lean` dependency remains upstream. The exact
finite physical API is included in the repository but experimental and outside
the `v1.x` stability contract. No DOI is asserted here.

Reproduce validation with:

```sh
lake env lean EverettianProbability/Audit/ConditionalAPIContract.lean
lake env lean EverettianProbability/Audit/MainResults.lean
lake build
bash scripts/guard.sh
```
