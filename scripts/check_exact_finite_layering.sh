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
    echo "EXACT_FINITE_LAYERING_DIAGNOSTIC=${file}: expected ${#expected[@]} imports, found ${#actual[@]}"
    failed=1
    return
  fi
  local index
  for index in "${!expected[@]}"; do
    if [ "${actual[$index]}" != "${expected[$index]}" ]; then
      echo "EXACT_FINITE_LAYERING_DIAGNOSTIC=${file}: import $((index + 1)) differs"
      failed=1
    fi
  done
}

check_imports EverettianProbability/ExactFinite/RecordOrbit.lean \
  'import EverettianProbability.Diachronic.UnitaryRecordOrbit'
check_imports EverettianProbability/ExactFinite/RefinementRealization.lean \
  'import EverettianProbability.ExactFinite.RecordOrbit' \
  'import EverettianProbability.Diachronic.FineBornWeightRealization'
check_imports EverettianProbability/ExactFinite/PhysicalAdequacy.lean \
  'import EverettianProbability.ExactFinite.RefinementRealization' \
  'import EverettianProbability.API.ExactFinitePhysicalRichness'
check_imports EverettianProbability/ExactFinite/MainResults.lean \
  'import EverettianProbability.ExactFinite.PhysicalAdequacy'
check_imports EverettianProbability/Audit/ExactFiniteArchitectureContract.lean \
  'import EverettianProbability.ExactFinite.PhysicalAdequacy'
check_imports EverettianProbability/Audit/ExactFiniteCompletenessAudit.lean \
  'import EverettianProbability.ExactFinite.MainResults'
check_imports EverettianProbability/Audit/ExactFiniteContradictoryAudit.lean \
  'import EverettianProbability.ExactFinite.MainResults'

for file in \
  EverettianProbability/ExactFinite/RecordOrbit.lean \
  EverettianProbability/ExactFinite/RefinementRealization.lean \
  EverettianProbability/ExactFinite/PhysicalAdequacy.lean; do
  if grep -E '^import EverettianProbability\.API\.(ConditionalBorn|DiachronicBorn|ConditionalMainResults)' "$file" >/dev/null; then
    echo "EXACT_FINITE_LAYERING_DIAGNOSTIC=${file}: direct conditional API import"
    failed=1
  fi
done

if grep -E '^import EverettianProbability\.(Diachronic|API\.Conditional)' \
  EverettianProbability/ExactFinite/MainResults.lean >/dev/null; then
  echo 'EXACT_FINITE_LAYERING_DIAGNOSTIC=MainResults.lean: bypasses PhysicalAdequacy facade'
  failed=1
fi

if grep -E '^import EverettianProbability\.(Diachronic|API\.Conditional|API\.ExactFinitePhysicalRichness)' \
  EverettianProbability/Audit/ExactFiniteContradictoryAudit.lean >/dev/null; then
  echo 'EXACT_FINITE_LAYERING_DIAGNOSTIC=ExactFiniteContradictoryAudit.lean: bypasses MainResults facade'
  failed=1
fi

for file in \
  EverettianProbability/API/ConditionalBorn.lean \
  EverettianProbability/API/DiachronicBorn.lean \
  EverettianProbability/API/ConditionalMainResults.lean; do
  if grep -E '^import EverettianProbability\.ExactFinite' "$file" >/dev/null; then
    echo "EXACT_FINITE_LAYERING_DIAGNOSTIC=${file}: imports ExactFinite"
    failed=1
  fi
done

if [ "$failed" -eq 0 ]; then
  echo 'EXACT_FINITE_LAYERING=PASS'
else
  echo 'EXACT_FINITE_LAYERING=FAIL'
  exit 1
fi
