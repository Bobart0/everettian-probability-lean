#!/usr/bin/env bash
# **FR.** Garde-fou anti-régression : compte les axiomes, les `native_decide`,
# les `maxHeartbeats 0` et les buts encore ouverts (`sorry`) dans l'arbre
# source intégré (`EverettianProbability` et `EverettianProbability.lean`).
# Contrairement à `quantum-foundations-lean` (dont le budget est figé à
# zéro), ce dépôt démarre en mode « squelette d'abord, preuves ensuite » :
# les `sorry` sont autorisés, mais strictement plafonnés par le fichier
# `SORRY_BUDGET` à la racine. Toute augmentation de ce plafond doit faire
# l'objet d'un commit dédié, justifié dans `MILESTONES.md` — jamais d'un
# ajustement silencieux pour faire passer la CI.
#
# **EN.** Anti-regression guard: counts axioms, `native_decide` calls,
# `maxHeartbeats 0` occurrences, and still-open goals (`sorry`) in the
# integrated source tree (`EverettianProbability` and
# `EverettianProbability.lean`). Unlike `quantum-foundations-lean` (whose
# budget is fixed at zero), this repository starts in "skeleton first,
# proofs later" mode: `sorry` is allowed, but strictly capped by the
# `SORRY_BUDGET` file at the repository root. Any increase of that cap must
# be its own dedicated commit, justified in `MILESTONES.md` — never a
# silent adjustment made just to get CI to pass.
set -euo pipefail
cd "$(dirname "$0")/.."

SRC_DIRS=(EverettianProbability EverettianProbability.lean)

# **FR.** Chaque comptage est protégé par `|| true` : sous `pipefail`, un
# `grep` sans correspondance (code de sortie 1) ne doit jamais interrompre
# le script avant l'affichage du résultat final.
# **EN.** Each count is guarded with `|| true`: under `pipefail`, a `grep`
# with no match (exit code 1) must never abort the script before the final
# result is printed.
AXIOM_HITS=$(grep -rnE '(^|[^[:alnum:]_])axiom[[:space:]]' "${SRC_DIRS[@]}" 2>/dev/null | wc -l | tr -d ' ' || true)
NATIVE_DECIDE_HITS=$(grep -rn 'native_decide' "${SRC_DIRS[@]}" 2>/dev/null | wc -l | tr -d ' ' || true)
MAXHEARTBEATS_ZERO_HITS=$(grep -rnE 'maxHeartbeats[[:space:]]+0\b' "${SRC_DIRS[@]}" 2>/dev/null | wc -l | tr -d ' ' || true)
SORRY_COUNT=$(grep -rno '\bsorry\b' "${SRC_DIRS[@]}" 2>/dev/null | wc -l | tr -d ' ' || true)

if [ -f SORRY_BUDGET ]; then
  SORRY_BUDGET_VALUE=$(tr -d '[:space:]' < SORRY_BUDGET)
else
  SORRY_BUDGET_VALUE=0
fi

echo "AXIOM_HITS=${AXIOM_HITS}"
echo "NATIVE_DECIDE_HITS=${NATIVE_DECIDE_HITS}"
echo "MAXHEARTBEATS_ZERO_HITS=${MAXHEARTBEATS_ZERO_HITS}"
echo "SORRY_COUNT=${SORRY_COUNT}"
echo "SORRY_BUDGET=${SORRY_BUDGET_VALUE}"

if [ "${AXIOM_HITS}" -eq 0 ] && [ "${NATIVE_DECIDE_HITS}" -eq 0 ] \
  && [ "${MAXHEARTBEATS_ZERO_HITS}" -eq 0 ] \
  && [ "${SORRY_COUNT}" -le "${SORRY_BUDGET_VALUE}" ]; then
  echo "GUARD_RESULT=PASS"
  exit 0
else
  echo "GUARD_RESULT=FAIL"
  exit 1
fi
