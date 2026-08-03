# Everettian Probability in Lean v2.1.0
## Stable upstream quantum-foundations boundary

## Français

Cette release met a jour la dependance `quantum-foundations-lean` vers
`v1.2.1-everettian-api` et ajoute la frontiere locale stable :

    import EverettianProbability.API.UpstreamQuantumFoundations

Cette frontiere reexporte le paquet public amont
`QuantumFoundations.EverettianAPI` sans recopier de definitions ni creer une
API locale plate. Son contrat verifie les declarations publiques de probabilite,
de factorisation tensorielle, de pont des selecteurs et d'implementation
Naimark. Elle n'identifie ni `NSNC1`, ni la neutralite d'ancilla, ni la
neutralite residuelle, et ne derive aucune factorisation tensorielle preferee.

Les API publiques conditionnelle et exacte-finie existantes, ainsi que les
resultats scientifiques, restent inchanges. Aucune nouvelle conclusion sur la
dynamique, la decoherence ou la probabilite n'est revendiquee.

Reproductibilite : `lake build`,
`lake env lean EverettianProbability/Audit/UpstreamQuantumFoundationsAPI.lean`,
et `bash scripts/guard.sh`. Aucun DOI ni GitHub Release n'est cree.

## English

This release updates the `quantum-foundations-lean` dependency to
`v1.2.1-everettian-api` and adds the stable local boundary:

    import EverettianProbability.API.UpstreamQuantumFoundations

The boundary re-exports the public upstream
`QuantumFoundations.EverettianAPI` bundle without copying definitions or
creating a flat local API. Its contract checks the public probability,
finite-tensor, selector-bridge, and Naimark-implementation declarations. It
does not identify `NSNC1`, ancilla neutrality, and residual neutrality, and it
derives no preferred tensor factorization.

The existing conditional and exact-finite public APIs, as well as the
scientific results, remain unchanged. No new claim about dynamics, decoherence,
or probability is made.

Reproducibility: `lake build`,
`lake env lean EverettianProbability/Audit/UpstreamQuantumFoundationsAPI.lean`,
and `bash scripts/guard.sh`. No DOI or GitHub Release is created.