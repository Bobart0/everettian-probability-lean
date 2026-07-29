#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

failed=0

check_imports() {
  local file="$1"
  shift
  local expected=("$@")
  local actual=()
  mapfile -t actual < <(grep -E '^import ' "$file" || true)
  if [ "${#actual[@]}" -ne "${#expected[@]}" ]; then
    echo "EXACT_FINITE_API_BOUNDARY_DIAGNOSTIC=${file}: expected ${#expected[@]} imports, found ${#actual[@]}"
    failed=1
    return
  fi
  local index
  for index in "${!expected[@]}"; do
    if [ "${actual[$index]}" != "${expected[$index]}" ]; then
      echo "EXACT_FINITE_API_BOUNDARY_DIAGNOSTIC=${file}: import $((index + 1)) differs"
      failed=1
    fi
  done
}

facade=EverettianProbability/API/ExactFiniteMainResults.lean
contract=EverettianProbability/Audit/ExactFiniteAPIContract.lean

check_imports "$facade" \
  'import EverettianProbability.ExactFinite.MainResults'
check_imports "$contract" \
  'import EverettianProbability.API.ExactFiniteMainResults'

if grep -E '^import EverettianProbability\.(Diachronic|API\.Conditional|API\.ExactFinitePhysicalRichness|PhysicalRefinement)' "$facade" >/dev/null; then
  echo 'EXACT_FINITE_API_BOUNDARY_DIAGNOSTIC=ExactFiniteMainResults.lean: forbidden direct implementation import'
  failed=1
fi

for file in \
  EverettianProbability/API/ConditionalBorn.lean \
  EverettianProbability/API/DiachronicBorn.lean \
  EverettianProbability/API/ConditionalMainResults.lean; do
  if grep -E '^import EverettianProbability\.API\.ExactFiniteMainResults' "$file" >/dev/null; then
    echo "EXACT_FINITE_API_BOUNDARY_DIAGNOSTIC=${file}: imports exact-finite stable facade"
    failed=1
  fi
done

if grep -E '^import EverettianProbability\.API\.(ConditionalBorn|DiachronicBorn|ConditionalMainResults)' "$facade" >/dev/null; then
  echo 'EXACT_FINITE_API_BOUNDARY_DIAGNOSTIC=ExactFiniteMainResults.lean: imports conditional stable facade'
  failed=1
fi

if [ "$failed" -eq 0 ]; then
  echo 'EXACT_FINITE_API_BOUNDARY=PASS'
else
  echo 'EXACT_FINITE_API_BOUNDARY=FAIL'
  exit 1
fi
