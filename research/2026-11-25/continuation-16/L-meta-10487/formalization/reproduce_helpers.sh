#!/usr/bin/env bash
set -euo pipefail
if [[ $# -ne 1 ]]; then
  echo "Usage: bash reproduce_helpers.sh /absolute/path/to/isolated/pequalnp-proofs" >&2
  exit 2
fi
task_checkout="$(cd -- "$1" && pwd)"
task_archive="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
task_expected=57164c3618362178843e2ea37bd01613f4037ae2
if [[ "$(git -C "$task_checkout" rev-parse HEAD)" != "$task_expected" ]]; then
  echo "Checkout must be pinned to $task_expected" >&2
  exit 2
fi
for task_module in Pnp10486LiteralCore Pnp10486SplitCore Pnp10486FiniteBridge; do
  task_source="$task_archive/$task_module.lean"
  if [[ "$task_module" == Pnp10486LiteralCore ]]; then
    task_source="$task_archive/narrow-import/$task_module.lean"
  fi
  task_target="$task_checkout/lean/$task_module.lean"
  if [[ -e "$task_target" ]] && ! cmp -s -- "$task_source" "$task_target"; then
    echo "Refusing to overwrite differing $task_target" >&2
    exit 2
  fi
done
for task_module in Pnp10486LiteralCore Pnp10486SplitCore Pnp10486FiniteBridge; do
  task_source="$task_archive/$task_module.lean"
  if [[ "$task_module" == Pnp10486LiteralCore ]]; then
    task_source="$task_archive/narrow-import/$task_module.lean"
  fi
  cp -- "$task_source" "$task_checkout/lean/$task_module.lean"
done
cd -- "$task_checkout/lean"
mkdir -p .lake/build/lib/lean
for task_module in Pnp10486LiteralCore Pnp10486SplitCore Pnp10486FiniteBridge; do
  lake env lean -j1 -o ".lake/build/lib/lean/$task_module.olean" "$task_module.lean"
done
