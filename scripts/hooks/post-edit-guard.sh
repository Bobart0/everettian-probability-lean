#!/usr/bin/env bash
# **FR.** Hook Claude Code `PostToolUse` sur les outils `Write`/`Edit`. Si
# le fichier touché est un `.lean`, refuse (code de sortie 2, avec message)
# s'il introduit un `axiom`, un `native_decide`, un `maxHeartbeats 0`, ou
# s'il dépasse 1500 lignes. Ne peut pas annuler l'écriture déjà effectuée
# (limite documentée des hooks `PostToolUse`) : le rôle de ce hook est de
# renvoyer un signal fort et immédiat, à corriger dans le tour suivant.
# Lit le JSON de l'événement sur l'entrée standard (`tool_input.file_path`).
#
# **EN.** Claude Code `PostToolUse` hook on the `Write`/`Edit` tools. If
# the touched file is a `.lean` file, refuses (exit code 2, with a
# message) if it introduces an `axiom`, a `native_decide`, a
# `maxHeartbeats 0`, or exceeds 1500 lines. Cannot undo the write that
# already happened (a documented limitation of `PostToolUse` hooks): this
# hook's role is to return a strong, immediate signal, to be fixed on the
# next turn. Reads the event JSON from standard input
# (`tool_input.file_path`).
set -euo pipefail

INPUT="$(cat)"

FILE_PATH="$(node -e '
let data = "";
process.stdin.on("data", (d) => { data += d; });
process.stdin.on("end", () => {
  try {
    const j = JSON.parse(data);
    process.stdout.write((j.tool_input && j.tool_input.file_path) || "");
  } catch (e) {
    process.stdout.write("");
  }
});
' <<< "${INPUT}")"

if [ -z "${FILE_PATH}" ]; then
  exit 0
fi

case "${FILE_PATH}" in
  *.lean) ;;
  *) exit 0 ;;
esac

if [ ! -f "${FILE_PATH}" ]; then
  exit 0
fi

AXIOM_HITS=$(grep -cE '(^|[^[:alnum:]_])axiom[[:space:]]' "${FILE_PATH}" 2>/dev/null || true)
NATIVE_DECIDE_HITS=$(grep -c 'native_decide' "${FILE_PATH}" 2>/dev/null || true)
MAXHEARTBEATS_ZERO_HITS=$(grep -cE 'maxHeartbeats[[:space:]]+0\b' "${FILE_PATH}" 2>/dev/null || true)
LINE_COUNT=$(wc -l < "${FILE_PATH}" | tr -d ' ')

if [ "${AXIOM_HITS:-0}" -gt 0 ]; then
  echo "post-edit-guard: blocked — ${FILE_PATH} introduces an 'axiom' declaration, which is forbidden project-wide." >&2
  exit 2
fi

if [ "${NATIVE_DECIDE_HITS:-0}" -gt 0 ]; then
  echo "post-edit-guard: blocked — ${FILE_PATH} uses 'native_decide', which is forbidden project-wide." >&2
  exit 2
fi

if [ "${MAXHEARTBEATS_ZERO_HITS:-0}" -gt 0 ]; then
  echo "post-edit-guard: blocked — ${FILE_PATH} sets 'maxHeartbeats 0'; use a finite, locally-scoped value instead." >&2
  exit 2
fi

if [ "${LINE_COUNT:-0}" -gt 1500 ]; then
  echo "post-edit-guard: blocked — ${FILE_PATH} has ${LINE_COUNT} lines (> 1500); split it into smaller files." >&2
  exit 2
fi

exit 0
