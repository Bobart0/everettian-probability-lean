# Everettian Probability in Lean v2.0.0
## Stable Conditional and Exact-Finite APIs

## Français

Cette release conserve l'API conditionnelle stable de v1.0.0 et ajoute la
façade exacte finie stable :

    import EverettianProbability.API.ConditionalMainResults
    import EverettianProbability.API.ExactFiniteMainResults

La seconde expose l'orbite unitaire des records, la réalisation exacte de
profils de poids fins compatibles, la séparation CORE/CALIBRATED et le cas
d'une fibre parente nulle. Les conclusions calibrées exigent les prémisses P4
explicites. Le résultat est projectif et fini ; aucune décohérence
approximative, aucun Hamiltonien local naturel et aucune théorie complète de
l'identité personnelle ne sont fournis.

Reproductibilité : `lake env lean EverettianProbability/Audit/ConditionalAPIContract.lean`,
`lake env lean EverettianProbability/Audit/ExactFiniteAPIContract.lean`,
`lake env lean EverettianProbability/Audit/MainResults.lean`, `lake build`,
et `bash scripts/guard.sh`. La dépendance `quantum-foundations-lean` est
épinglée. Aucun DOI n'est inventé.

## English

This release preserves the v1.0.0 conditional stable API and adds the stable
exact-finite facade:

    import EverettianProbability.API.ConditionalMainResults
    import EverettianProbability.API.ExactFiniteMainResults

The latter exposes record unitary orbits, exact realization of compatible
fine-weight profiles, the CORE/CALIBRATED separation, and the zero-parent
fibre case. Calibrated credence conclusions require explicit P4 premises. The
result is projective and finite; it provides no approximate decoherence,
natural local Hamiltonian, or complete personal-identity theory.

The reproducibility commands above use the pinned quantum-foundations-lean
dependency. No DOI is invented.
