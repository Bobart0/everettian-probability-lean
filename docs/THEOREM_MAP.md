# THEOREM_MAP.md

## Français

Ce document enregistrera, pour chaque théorème utilisé substantiellement
dans l'article II, sa déclaration Lean exacte, son module, son statut
mathématique, ses dépendances principales, ses hypothèses de dimension,
son exactitude, le statut de son audit d'axiomes, et sa limite de portée —
sur le modèle de `quantum-foundations-lean/docs/FOP_THEOREM_MAP.md`. **Vide
en P1** : aucun théorème scientifique n'y est encore prouvé (voir
`MILESTONES.md`).

Catégories de statut utilisées (reprises telles quelles de l'amont) :

- **résultat original** — un théorème dont l'énoncé et la preuve sont
  originaux à ce développement formel.
- **théorème de connexion** — un théorème qui relie deux développements
  jusque-là séparés, sans re-prouver ni l'un ni l'autre.
- **nouvelle réduction à un théorème connu** — un théorème qui réduit une
  nouvelle hypothèse ou un nouveau cadre à un théorème déjà formalisé,
  sans le re-prouver.
- **formalisation d'un théorème connu** — une formalisation Lean directe
  d'un théorème déjà établi dans la littérature.
- **théorème opérationnel auxiliaire** — un résultat de soutien établissant
  une réalisation opérationnelle, pas lui-même un théorème de
  représentation ou de poids.
- **contraste conceptuel** — une formalisation présentée pour contraster
  avec le développement branchial, pas comme une prémisse de celui-ci.
- **témoin de non-vacuité** — un habitant concret établissant qu'une
  structure d'hypothèses n'est pas vacueuse.

*(Table à remplir au fil des jalons P2–P11.)*

## English

This document will record, for every theorem used substantively in paper
II, its exact Lean declaration, module, mathematical status, principal
dependencies, dimension assumptions, exactness, axiom-audit status, and
scope limitation — following the pattern of
`quantum-foundations-lean/docs/FOP_THEOREM_MAP.md`. **Empty at P1**: no
scientific theorem is proved here yet (see `MILESTONES.md`).

Status categories used (carried over as-is from upstream):

- **original result** — a theorem whose statement and proof are original
  to this formal development.
- **connection theorem** — a theorem that connects two previously
  separate developments without reproving either.
- **new reduction to a known theorem** — a theorem that reduces a new
  hypothesis or setting to an already-formalized theorem, without
  reproving that theorem.
- **formalization of a known theorem** — a direct Lean formalization of a
  theorem already established in the literature.
- **auxiliary operational theorem** — a supporting result establishing an
  operational realization, not itself a representation or weight
  theorem.
- **conceptual contrast** — a formalization presented to contrast with
  the branch-theoretic development, not as a premise of it.
- **nonvacuity witness** — a concrete inhabitant establishing that a
  hypothesis structure is not vacuous.

*(Table to be filled in as milestones P2–P11 close.)*
