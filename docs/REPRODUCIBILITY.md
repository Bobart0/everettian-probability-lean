# REPRODUCIBILITY.md

## Français

### Épinglages exacts

- Toolchain Lean : `leanprover/lean4:v4.32.0-rc1` (`lean-toolchain`).
- `quantum_foundations` : tag `v1.1.1-probability-api`
  (`https://github.com/Bobart0/quantum-foundations-lean.git`).
- `gleason` et `mathlib` : résolus **transitivement** par Lake à travers
  `quantum_foundations`, jamais redéclarés dans `lakefile.toml` de ce
  dépôt. Révisions exactes visibles dans `lake-manifest.json` une fois
  généré (`lake exe cache get`).

### Construire depuis un clone propre — POSIX (bash/zsh)

```sh
git clone https://github.com/Bobart0/everettian-probability-lean.git
cd everettian-probability-lean
bash setup.sh
```

`setup.sh` exécute, dans l'ordre : `scripts/preflight.sh` (vérification du
pin), `lake exe cache get` (cache Mathlib précompilé — indispensable,
sinon plusieurs heures de compilation), `lake build`, puis active les
hooks git partagés (`git config core.hooksPath .githooks`).

### Construire depuis un clone propre — PowerShell

```powershell
git clone https://github.com/Bobart0/everettian-probability-lean.git
cd everettian-probability-lean
bash scripts/preflight.sh
lake exe cache get
lake build
git config core.hooksPath .githooks
```

(`bash` reste nécessaire pour `preflight.sh`/`guard.sh`, disponibles via
Git Bash sur Windows ; `lake`/`lean` eux-mêmes sont natifs PowerShell.)

### Audit des axiomes

```sh
lake env lean EverettianProbability/Audit/MainResults.lean
```

Chaque `#print axioms` de ce fichier doit afficher soit exactement
`[propext, Classical.choice, Quot.sound]` (déclaration sans but ouvert),
soit ces trois axiomes plus `sorryAx` (déclaration avec un but ouvert
budgété, voir `MILESTONES.md`). Toute autre dépendance signale une
régression.

### Garde anti-régression

```sh
bash scripts/guard.sh
```

Doit afficher `GUARD_RESULT=PASS`, avec `AXIOM_HITS=0`,
`NATIVE_DECIDE_HITS=0`, `MAXHEARTBEATS_ZERO_HITS=0`, et
`SORRY_COUNT` inférieur ou égal à `SORRY_BUDGET`.

## English

### Exact pins

- Lean toolchain: `leanprover/lean4:v4.32.0-rc1` (`lean-toolchain`).
- `quantum_foundations`: tag `v1.1.1-probability-api`
  (`https://github.com/Bobart0/quantum-foundations-lean.git`).
- `gleason` and `mathlib`: resolved **transitively** by Lake through
  `quantum_foundations`, never redeclared in this repository's
  `lakefile.toml`. Exact revisions visible in `lake-manifest.json` once
  generated (`lake exe cache get`).

### Building from a clean clone — POSIX (bash/zsh)

```sh
git clone https://github.com/Bobart0/everettian-probability-lean.git
cd everettian-probability-lean
bash setup.sh
```

`setup.sh` runs, in order: `scripts/preflight.sh` (pin check),
`lake exe cache get` (precompiled Mathlib cache — mandatory, otherwise
several hours of compilation), `lake build`, then activates the shared
git hooks (`git config core.hooksPath .githooks`).

### Building from a clean clone — PowerShell

```powershell
git clone https://github.com/Bobart0/everettian-probability-lean.git
cd everettian-probability-lean
bash scripts/preflight.sh
lake exe cache get
lake build
git config core.hooksPath .githooks
```

(`bash` is still needed for `preflight.sh`/`guard.sh`, available via Git
Bash on Windows; `lake`/`lean` themselves are native PowerShell.)

### Axiom audit

```sh
lake env lean EverettianProbability/Audit/MainResults.lean
```

Every `#print axioms` in this file must show either exactly
`[propext, Classical.choice, Quot.sound]` (a declaration with no open
goal), or those three axioms plus `sorryAx` (a declaration with a
budgeted open goal, see `MILESTONES.md`). Any other dependency signals a
regression.

### Anti-regression guard

```sh
bash scripts/guard.sh
```

Must show `GUARD_RESULT=PASS`, with `AXIOM_HITS=0`,
`NATIVE_DECIDE_HITS=0`, `MAXHEARTBEATS_ZERO_HITS=0`, and `SORRY_COUNT`
less than or equal to `SORRY_BUDGET`.
