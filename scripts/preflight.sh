#!/usr/bin/env bash
# **FR.** Vérifications de cohérence du pin, avant tout `lake build`. Un pin
# incorrect ou dérivé casse le build de façon opaque (voir `AGENTS.md`,
# section « Épinglage ») ; ce script transforme ce mode d'échec silencieux
# en échec explicite, avec un message clair sur ce qui diverge.
#
# **EN.** Pin-consistency checks, run before any `lake build`. An incorrect
# or drifted pin breaks the build in an opaque way (see `AGENTS.md`,
# "Pinning" section); this script turns that silent failure mode into an
# explicit one, with a clear message about what diverges.
set -euo pipefail
cd "$(dirname "$0")/.."

EXPECTED_TOOLCHAIN="leanprover/lean4:v4.32.0-rc1"
EXPECTED_UPSTREAM_REV="v1.0.1-fop-companion"
FAIL=0

fail() {
  echo "PREFLIGHT_FAIL: $1"
  FAIL=1
}

# 1. lean-toolchain
if [ ! -f lean-toolchain ]; then
  fail "lean-toolchain is missing"
else
  ACTUAL_TOOLCHAIN=$(tr -d '[:space:]' < lean-toolchain)
  if [ "${ACTUAL_TOOLCHAIN}" != "${EXPECTED_TOOLCHAIN}" ]; then
    fail "lean-toolchain is '${ACTUAL_TOOLCHAIN}', expected '${EXPECTED_TOOLCHAIN}'"
  fi
fi

# 2. lakefile.toml pins quantum_foundations on the expected tag
if [ ! -f lakefile.toml ]; then
  fail "lakefile.toml is missing"
else
  if ! grep -q "name = \"quantum_foundations\"" lakefile.toml; then
    fail "lakefile.toml does not require 'quantum_foundations'"
  fi
  if ! grep -q "rev = \"${EXPECTED_UPSTREAM_REV}\"" lakefile.toml; then
    fail "lakefile.toml does not pin quantum_foundations to '${EXPECTED_UPSTREAM_REV}'"
  fi
fi

# 3. lake-manifest.json exists and references gleason and mathlib
if [ ! -f lake-manifest.json ]; then
  fail "lake-manifest.json is missing (run 'lake exe cache get' first)"
else
  if ! grep -q '"name": "gleason"' lake-manifest.json; then
    fail "lake-manifest.json does not reference 'gleason'"
  fi
  if ! grep -q '"name": "mathlib"' lake-manifest.json; then
    fail "lake-manifest.json does not reference 'mathlib'"
  fi
fi

# 4. No divergence between the local toolchain and the resolved
#    quantum_foundations package's toolchain in .lake/packages/.
UPSTREAM_TOOLCHAIN_FILE=".lake/packages/quantum_foundations/lean-toolchain"
if [ -f "${UPSTREAM_TOOLCHAIN_FILE}" ]; then
  UPSTREAM_TOOLCHAIN=$(tr -d '[:space:]' < "${UPSTREAM_TOOLCHAIN_FILE}")
  if [ -f lean-toolchain ]; then
    LOCAL_TOOLCHAIN=$(tr -d '[:space:]' < lean-toolchain)
    if [ "${LOCAL_TOOLCHAIN}" != "${UPSTREAM_TOOLCHAIN}" ]; then
      fail "local lean-toolchain ('${LOCAL_TOOLCHAIN}') diverges from resolved quantum_foundations toolchain ('${UPSTREAM_TOOLCHAIN}')"
    fi
  fi
else
  echo "PREFLIGHT_NOTE: ${UPSTREAM_TOOLCHAIN_FILE} not found yet (run 'lake exe cache get' first); skipping divergence check"
fi

if [ "${FAIL}" -eq 0 ]; then
  echo "PREFLIGHT_RESULT=PASS"
  exit 0
else
  echo "PREFLIGHT_RESULT=FAIL"
  exit 1
fi
