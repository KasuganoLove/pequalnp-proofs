#!/usr/bin/env bash
set -euo pipefail
if [[ $# -ne 1 ]]; then
  echo "Usage: bash reproduce_helpers.sh /absolute/path/to/isolated/pequalnp-proofs" >&2
  exit 2
fi
task_checkout="$(cd -- "$1" && pwd)"
task_here="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
task_archive="$(cd -- "$task_here/../.." && pwd)"
task_expected=57164c3618362178843e2ea37bd01613f4037ae2
if [[ "$(git -C "$task_checkout" rev-parse HEAD)" != "$task_expected" ]]; then
  echo "Checkout must be pinned to $task_expected" >&2
  exit 2
fi
task_temp="$(mktemp -d)"
trap 'rm -rf -- "$task_temp"' EXIT
for task_module in Core SplitCore FiniteBridge States BlockBridge; do
  task_name="Pnp11315$task_module.lean"
  task_relative="L-meta-11315/formalization/$task_name"
  if [[ "$task_module" == Core ]]; then
    task_relative="L-meta-11315/formalization/broad-tactic/$task_name"
  fi
  python3 "$task_archive/restore_file.py" "$task_relative" "$task_temp/$task_name"
  task_target="$task_checkout/lean/$task_name"
  if [[ -e "$task_target" ]] && ! cmp -s -- "$task_temp/$task_name" "$task_target"; then
    echo "Refusing to overwrite differing $task_target" >&2
    exit 2
  fi
done
for task_module in Core SplitCore FiniteBridge States BlockBridge; do
  cp -- "$task_temp/Pnp11315$task_module.lean" "$task_checkout/lean/Pnp11315$task_module.lean"
done
cd -- "$task_checkout/lean"
mkdir -p .lake/build/lib/lean
for task_module in Core SplitCore FiniteBridge States BlockBridge; do
  lake env lean -j1 -o ".lake/build/lib/lean/Pnp11315$task_module.olean" "Pnp11315$task_module.lean"
done
