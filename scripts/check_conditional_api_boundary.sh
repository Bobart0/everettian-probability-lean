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
    echo "CONDITIONAL_API_BOUNDARY_DIAGNOSTIC=${file}: expected ${#expected[@]} imports, found ${#actual[@]}"
    failed=1
    return
  fi
  local index
  for index in "${!expected[@]}"; do
    if [ "${actual[$index]}" != "${expected[$index]}" ]; then
      echo "CONDITIONAL_API_BOUNDARY_DIAGNOSTIC=${file}: import $((index + 1)) differs"
      failed=1
    fi
  done
}

check_imports EverettianProbability/API/ConditionalBorn.lean \
  'import EverettianProbability.Diachronic.ProjectiveBornContinuators'
check_imports EverettianProbability/API/DiachronicBorn.lean \
  'import EverettianProbability.API.ConditionalBorn' \
  'import EverettianProbability.Diachronic.TowerProperty'
check_imports EverettianProbability/API/ConditionalMainResults.lean \
  'import EverettianProbability.API.ConditionalBorn' \
  'import EverettianProbability.API.DiachronicBorn'
check_imports EverettianProbability/Audit/ConditionalAPIContract.lean \
  'import EverettianProbability.API.ConditionalMainResults'

for file in \
  EverettianProbability/API/ConditionalBorn.lean \
  EverettianProbability/API/DiachronicBorn.lean \
  EverettianProbability/API/ConditionalMainResults.lean; do
  if grep -E '^import .*\b(ExactFinite|PhysicalFinePlan|FineBornWeight|UnitaryRecordOrbit|BlockDiagonal|CellwiseOrbit|EqualNormLocalUnitary|RecordWeightEquivalence|PhysicalPayoffInvariance|ProjectorCommutingContinuation|UniformRecordRespectingContinuation|RecordNeutralPhysicalContinuation)' "$file" >/dev/null; then
    echo "CONDITIONAL_API_BOUNDARY_DIAGNOSTIC=${file}: forbidden facade import"
    failed=1
  fi
done

if [ "$failed" -eq 0 ]; then
  echo 'CONDITIONAL_API_BOUNDARY=PASS'
else
  echo 'CONDITIONAL_API_BOUNDARY=FAIL'
  exit 1
fi
