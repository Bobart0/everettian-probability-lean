#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake exe cache get
lake build EverettianProbability
lake env lean EverettianProbability/Audit/PublicationCore.lean
bash scripts/guard.sh
git diff --check
echo "[publication] PASS"
