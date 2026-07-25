#!/usr/bin/env bash
# **FR.** Hook Claude Code `PreToolUse` sur l'outil `Bash`. Bloque (code de
# sortie 2, avec message explicite) toute commande contenant `git push
# --force`, `git push -f`, `lake update`, `rm -rf`, ou une tentative de
# modification de `lean-toolchain` / `lakefile.toml` — les points de
# défaillance n°1 de ce dépôt (voir `AGENTS.md`, section « Épinglage »).
# Lit le JSON de l'événement sur l'entrée standard (`tool_input.command`).
#
# **EN.** Claude Code `PreToolUse` hook on the `Bash` tool. Blocks (exit
# code 2, with an explicit message) any command containing `git push
# --force`, `git push -f`, `lake update`, `rm -rf`, or an attempt to
# modify `lean-toolchain` / `lakefile.toml` — this repository's #1 failure
# point (see `AGENTS.md`, "Pinning" section). Reads the event JSON from
# standard input (`tool_input.command`).
set -euo pipefail

INPUT="$(cat)"

COMMAND="$(node -e '
let data = "";
process.stdin.on("data", (d) => { data += d; });
process.stdin.on("end", () => {
  try {
    const j = JSON.parse(data);
    process.stdout.write((j.tool_input && j.tool_input.command) || "");
  } catch (e) {
    process.stdout.write("");
  }
});
' <<< "${INPUT}")"

if [ -z "${COMMAND}" ]; then
  exit 0
fi

block() {
  echo "pre-bash-guard: blocked — $1" >&2
  exit 2
}

case "${COMMAND}" in
  *"git push --force"*|*"git push -f"*|*"git push --force-with-lease"*)
    block "force-push is not allowed without explicit human confirmation." ;;
esac

case "${COMMAND}" in
  *"lake update"*)
    if [ "${ALLOW_PIN_BUMP:-}" = "1" ] && [ "${COMMAND}" = "lake update quantum_foundations" ]; then
      printf '\n<!-- PIN_BUMP_AUDIT: **FR.** Mise à jour ciblée de `quantum_foundations` autorisée par `ALLOW_PIN_BUMP=1`. **EN.** Targeted `quantum_foundations` update authorized by `ALLOW_PIN_BUMP=1`. -->\n' >> MILESTONES.md
    else
      block "'lake update' is allowed only as the exact command 'lake update quantum_foundations' with ALLOW_PIN_BUMP=1; unscoped updates would drift pinned revisions." 
    fi ;;
esac

case "${COMMAND}" in
  *"rm -rf"*)
    block "'rm -rf' is not allowed from an automated command; use a narrower, reviewable deletion." ;;
esac

case "${COMMAND}" in
  *"lean-toolchain"*|*"lakefile.toml"*)
    case "${COMMAND}" in
      *">"*|*"sed -i"*|*"mv "*|*"cp "*|*"rm "*|*"tee "*)
        if [ "${ALLOW_PIN_BUMP:-}" = "1" ] && [ "${COMMAND}" = "lake update quantum_foundations" ]; then
          :
        else
          block "commands that write to 'lean-toolchain' or 'lakefile.toml' are not allowed; these pins change only via an explicit, reviewed edit." 
        fi ;;
    esac
    ;;
esac

exit 0
