#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

FRENCH_PATTERN='saint[[:space:]_-]*g''raal'
ENGLISH_PATTERN='holy[[:space:]_-]*g''rail'

if rg -n -i \
  --glob '!/.git/**' \
  --glob '!/.lake/**' \
  --glob '!lake-packages/**' \
  --glob '!build/**' \
  --glob '!**/*.olean' \
  --glob '!**/*.ilean' \
  "${FRENCH_PATTERN}|${ENGLISH_PATTERN}" \
  README.md \
  MILESTONES.md \
  CLAIM_MATRIX.md \
  ARCHITECTURE_NOTES.md \
  CHANGELOG.md \
  RELEASE_NOTES_v1.0.0.md \
  CITATION.cff \
  EverettianProbability.lean \
  EverettianProbability \
  docs \
  scripts; then
  echo 'REPOSITORY_TERMINOLOGY=FAIL'
  exit 1
fi

echo 'REPOSITORY_TERMINOLOGY=PASS'
