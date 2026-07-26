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
SORRY_ANNOTATION_MISSING=0
while IFS=: read -r sorry_file sorry_line _; do
  [ -n "${sorry_file}" ] || continue
  previous_line=$(sed -n "$((sorry_line - 1))p" "${sorry_file}")
  if ! printf '%s\n' "${previous_line}" | grep -qE '^[[:space:]]*--[[:space:]]+SATISFIABILITY:'; then
    echo "UNANNOTATED_SORRY=${sorry_file}:${sorry_line}"
    SORRY_ANNOTATION_MISSING=$((SORRY_ANNOTATION_MISSING + 1))
  fi
done < <(grep -rn '\bsorry\b' "${SRC_DIRS[@]}" 2>/dev/null || true)

# **FR.** Discipline de non-trivialité, actuellement en observation : une
# définition propositionnelle dont le docstring porte le marqueur `PREMISE`
# doit avoir une entrée nommée dans `NonTriviality.lean` du même répertoire.
# Ces écarts sont volontairement des avertissements, pas encore des échecs de
# CI, afin de mesurer les faux positifs avant de rendre la règle bloquante.
#
# **EN.** Nontriviality discipline, currently in observation mode: a
# propositional definition whose docstring carries the `PREMISE` marker must
# have a named entry in `NonTriviality.lean` in the same directory. These
# discrepancies are deliberately warnings, not CI failures yet, so that false
# positives can be measured before the rule becomes blocking.
NONTRIVIALITY_WARNINGS=0
while IFS=: read -r premise_file premise_name; do
  [ -n "${premise_file}" ] || continue
  premise_dir=$(dirname "${premise_file}")
  witness_file="${premise_dir}/NonTriviality.lean"
  if [ ! -f "${witness_file}" ] || ! grep -qF "${premise_name}" "${witness_file}"; then
    echo "NONTRIVIALITY_MISSING=${premise_file}:${premise_name}"
    NONTRIVIALITY_WARNINGS=$((NONTRIVIALITY_WARNINGS + 1))
  fi
done < <(
  find EverettianProbability -name '*.lean' -type f -exec awk '
    /\/--/ {
      in_doc = 1
      has_premise = index($0, "PREMISE") > 0
    }
    in_doc {
      if (index($0, "PREMISE") > 0) has_premise = 1
      if (index($0, "-/") > 0) {
        in_doc = 0
        if (has_premise) awaiting_def = 1
      }
      next
    }
    awaiting_def {
      if ($0 ~ /^[[:space:]]*$/) next
      if ($0 ~ /^[[:space:]]*(noncomputable[[:space:]]+)?def[[:space:]]+/) {
        line = $0
        sub(/^[[:space:]]*/, "", line)
        sub(/^noncomputable[[:space:]]+/, "", line)
        sub(/^def[[:space:]]+/, "", line)
        split(line, pieces, /[^[:alnum:]_\047]/)
        def_name = pieces[1]
        def_signature = $0
        awaiting_def = 0
        in_def = 1
      } else {
        awaiting_def = 0
      }
      next
    }
    in_def {
      def_signature = def_signature " " $0
      if (index($0, ":=") > 0) {
        if (def_signature ~ /:[[:space:]]*Prop/) print FILENAME ":" def_name
        in_def = 0
      }
    }
  ' {} +
)

if [ -f SORRY_BUDGET ]; then
  SORRY_BUDGET_VALUE=$(tr -d '[:space:]' < SORRY_BUDGET)
else
  SORRY_BUDGET_VALUE=0
fi

echo "AXIOM_HITS=${AXIOM_HITS}"
echo "NATIVE_DECIDE_HITS=${NATIVE_DECIDE_HITS}"
echo "MAXHEARTBEATS_ZERO_HITS=${MAXHEARTBEATS_ZERO_HITS}"
echo "SORRY_COUNT=${SORRY_COUNT}"
echo "SORRY_ANNOTATION_MISSING=${SORRY_ANNOTATION_MISSING}"
echo "NONTRIVIALITY_WARNINGS=${NONTRIVIALITY_WARNINGS}"
echo "SORRY_BUDGET=${SORRY_BUDGET_VALUE}"

if [ "${AXIOM_HITS}" -eq 0 ] && [ "${NATIVE_DECIDE_HITS}" -eq 0 ] \
  && [ "${MAXHEARTBEATS_ZERO_HITS}" -eq 0 ] \
  && [ "${SORRY_ANNOTATION_MISSING}" -eq 0 ] \
  && [ "${SORRY_COUNT}" -le "${SORRY_BUDGET_VALUE}" ]; then
  echo "GUARD_RESULT=PASS"
  exit 0
else
  echo "GUARD_RESULT=FAIL"
  exit 1
fi
