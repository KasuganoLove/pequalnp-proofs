#!/usr/bin/env bash
set -euo pipefail
if [[ $# != 1 ]]; then
  echo "Usage: $0 /path/to/compatible/pequalnp-proofs/lean" >&2
  exit 2
fi
proof_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
lean_dir=$(cd -- "$1" && pwd)
[[ -f "$lean_dir/PEqualNP/Defs.lean" ]] || { echo "PEqualNP/Defs.lean missing" >&2; exit 2; }
cd -- "$lean_dir"
lake env lean -j1 -R "$proof_dir" -o "$proof_dir/Pnp650TransferCore.olean"   "$proof_dir/Pnp650TransferCore.lean" > "$proof_dir/core-ordinary.log" 2>&1
lake env bash -c 'export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"; lean -j1 -R "$1" -o "$1/Pnp650SingleMixer.olean" "$1/Pnp650SingleMixer.lean"'   pnp "$proof_dir" > "$proof_dir/single-mixer-ordinary.log" 2>&1
lake env bash -c 'export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"; lean -j1 -R "$1" "$1/Pnp650SingleMixerAxioms.lean"'   pnp "$proof_dir" > "$proof_dir/single-mixer-axioms.log" 2>&1
printf '%s\n' "Ordinary Lean checks complete. This is not the official strict checker."
