#!/usr/bin/env bash
# **FR.** Garde anti-regression pour les axiomes, `native_decide`,
# `maxHeartbeats 0`, les buts ouverts et la frontiere d'import de l'API
# conditionnelle stable. Le budget de buts ouverts est fixe a zero.
#
# **EN.** Anti-regression guard for axioms, `native_decide`,
# `maxHeartbeats 0`, open goals, and the stable conditional API import
# boundary. The open-goal budget is fixed at zero.
set -euo pipefail
cd "$(dirname "$0")/.."

SRC_DIRS=(EverettianProbability EverettianProbability.lean)

# A missing grep match must not stop the report under `pipefail`.
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

# Nontriviality remains observational until its false-positive rate is known.
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

if bash scripts/check_conditional_api_boundary.sh; then
  CONDITIONAL_API_BOUNDARY_RESULT=PASS
else
  CONDITIONAL_API_BOUNDARY_RESULT=FAIL
fi

if bash scripts/check_exact_finite_layering.sh; then
  EXACT_FINITE_LAYERING_RESULT=PASS
else
  EXACT_FINITE_LAYERING_RESULT=FAIL
fi

if bash scripts/check_repository_terminology.sh; then
  REPOSITORY_TERMINOLOGY_RESULT=PASS
else
  REPOSITORY_TERMINOLOGY_RESULT=FAIL
fi

if bash scripts/check_exact_finite_api_boundary.sh; then
  EXACT_FINITE_API_BOUNDARY_RESULT=PASS
else
  EXACT_FINITE_API_BOUNDARY_RESULT=FAIL
fi

echo "AXIOM_HITS=${AXIOM_HITS}"
echo "NATIVE_DECIDE_HITS=${NATIVE_DECIDE_HITS}"
echo "MAXHEARTBEATS_ZERO_HITS=${MAXHEARTBEATS_ZERO_HITS}"
echo "SORRY_COUNT=${SORRY_COUNT}"
echo "SORRY_ANNOTATION_MISSING=${SORRY_ANNOTATION_MISSING}"
echo "NONTRIVIALITY_WARNINGS=${NONTRIVIALITY_WARNINGS}"
echo "SORRY_BUDGET=${SORRY_BUDGET_VALUE}"
echo "CONDITIONAL_API_BOUNDARY_RESULT=${CONDITIONAL_API_BOUNDARY_RESULT}"
echo "EXACT_FINITE_LAYERING_RESULT=${EXACT_FINITE_LAYERING_RESULT}"
echo "REPOSITORY_TERMINOLOGY_RESULT=${REPOSITORY_TERMINOLOGY_RESULT}"
echo "EXACT_FINITE_API_BOUNDARY_RESULT=${EXACT_FINITE_API_BOUNDARY_RESULT}"

if [ "${AXIOM_HITS}" -eq 0 ] && [ "${NATIVE_DECIDE_HITS}" -eq 0 ] \
  && [ "${MAXHEARTBEATS_ZERO_HITS}" -eq 0 ] \
  && [ "${SORRY_ANNOTATION_MISSING}" -eq 0 ] \
  && [ "${SORRY_COUNT}" -le "${SORRY_BUDGET_VALUE}" ] \
  && [ "${CONDITIONAL_API_BOUNDARY_RESULT}" = "PASS" ] \
  && [ "${EXACT_FINITE_LAYERING_RESULT}" = "PASS" ] \
  && [ "${REPOSITORY_TERMINOLOGY_RESULT}" = "PASS" ] \
  && [ "${EXACT_FINITE_API_BOUNDARY_RESULT}" = "PASS" ]; then
  echo "GUARD_RESULT=PASS"
  exit 0
else
  echo "GUARD_RESULT=FAIL"
  exit 1
fi
