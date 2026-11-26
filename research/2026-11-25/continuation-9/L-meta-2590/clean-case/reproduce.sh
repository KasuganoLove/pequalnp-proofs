#!/usr/bin/env bash
# Ordinary reproduction of frozen L2590 clean-case research; not an official proof check.
# Run only while authorized to perform this research. This script has no lease or remote operations.
set -euo pipefail

pnp_die() { printf 'ERROR: %s\n' "$*" >&2; exit 1; }
pnp_usage() {
  printf 'Usage: %s FRESH_CHECKOUT [FROZEN_CONTINUATION8_DIRECTORY]\n' "$0"
  printf 'Requires checkout 259523a5b265318b84f9377f2feb965fd213f898, cached Lean 4.36.0, and all pinned package checkouts/cache.\n'
}
if [[ ${1:-} == --help ]]; then pnp_usage; exit 0; fi
[[ $# -ge 1 && $# -le 2 ]] || { pnp_usage >&2; exit 2; }
for pnp_command in git python3 sha256sum cmp mktemp; do
  command -v "$pnp_command" >/dev/null || pnp_die "Missing command: $pnp_command"
done

pnp_pin=259523a5b265318b84f9377f2feb965fd213f898
pnp_script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
pnp_checkout=$(cd -- "$1" && pwd -P)
pnp_git_root=$(git -C "$pnp_checkout" rev-parse --show-toplevel)
[[ "$pnp_checkout" == "$pnp_git_root" ]] || pnp_die 'Argument must name the repository root.'
[[ $(git -C "$pnp_checkout" rev-parse HEAD) == "$pnp_pin" ]] || pnp_die "Checkout HEAD must be exactly $pnp_pin. Use a separate detached worktree."
git -C "$pnp_checkout" diff --quiet -- || pnp_die 'Tracked working-tree changes exist; use a fresh worktree.'
git -C "$pnp_checkout" diff --cached --quiet -- || pnp_die 'Staged tracked changes exist; use a fresh worktree.'
pnp_lean_dir="$pnp_checkout/lean"
[[ $(cat "$pnp_lean_dir/lean-toolchain") == leanprover/lean4:v4.36.0 ]] || pnp_die 'Unexpected toolchain pin.'
[[ -z ${ELAN_TOOLCHAIN:-} || ${ELAN_TOOLCHAIN} == leanprover/lean4:v4.36.0 ]] || pnp_die 'Unset the conflicting ELAN_TOOLCHAIN override.'
pnp_toolchain="${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---v4.36.0"
[[ -x "$pnp_toolchain/bin/lake" && -x "$pnp_toolchain/bin/lean" ]] || pnp_die 'Lean 4.36.0 must already be installed in the existing elan cache; this script does not install it.'
[[ -x "$pnp_checkout/tools/bin/lake" ]] || pnp_die 'Missing project lake wrapper.'
[[ ! -L "$pnp_lean_dir/.lake" && ! -L "$pnp_lean_dir/.lake/build" ]] || pnp_die 'Do not share the project .lake directory or its build directory; share only .lake/packages.'

if [[ $# == 2 ]]; then
  pnp_cont8=$(cd -- "$2" && pwd -P)
else
  pnp_probe="$pnp_script_dir"
  pnp_cont8=''
  while [[ "$pnp_probe" != / ]]; do
    if [[ -d "$pnp_probe/continuation-8/dependencies" && -d "$pnp_probe/continuation-8/lean" ]]; then
      pnp_cont8="$pnp_probe/continuation-8"
      break
    fi
    pnp_probe=$(dirname -- "$pnp_probe")
  done
  [[ -n "$pnp_cont8" ]] || pnp_die 'Cannot locate continuation-8; provide its directory as argument 2.'
fi

# Require the existing pinned dependencies rather than fetching/updating them.
python3 - "$pnp_lean_dir" <<'PYCHECK'
from pathlib import Path
import json, subprocess, sys
lean = Path(sys.argv[1])
manifest = json.loads((lean / 'lake-manifest.json').read_text())
packages = lean / manifest.get('packagesDir', '.lake/packages')
mathlib_pin = 'fc4f59e577feb1a4956671bc04ac18aaaf8cd842'
for package in manifest['packages']:
    name, rev = package['name'], package['rev']
    package_dir = packages / name
    if not package_dir.is_dir():
        raise SystemExit(f'Missing cached package: {package_dir}')
    actual = subprocess.check_output(['git', '-C', str(package_dir), 'rev-parse', 'HEAD'], text=True).strip()
    if actual != rev:
        raise SystemExit(f'Wrong cached revision for {name}: {actual}, expected {rev}')
    for args in (['diff', '--quiet', '--'], ['diff', '--cached', '--quiet', '--']):
        if subprocess.run(['git', '-C', str(package_dir), *args], check=False).returncode:
            raise SystemExit(f'Tracked cached-package changes in {name}; use the verified pinned cache')
    if name == 'mathlib' and rev != mathlib_pin:
        raise SystemExit('Unexpected Mathlib manifest pin')
if not (packages / 'mathlib/.lake/build/lib/lean/Mathlib.olean').is_file():
    raise SystemExit('The existing full pinned Mathlib olean cache is required for the frozen upstream helpers')
print('Pinned package sources and Mathlib cache preflight passed.')
PYCHECK

# Source kind | frozen relative path | destination relative to lean/ | expected SHA256.
# This is the minimal imported research dependency closure, in build order.
pnp_specs=(
  "c8|dependencies/Pnp2343Pruning.lean|Pnp2343Pruning.lean|4f080984395e3362d5164a3ca1528beee970f42ca58b651130aa6c817098cb5d"
  "c8|dependencies/L_meta_1501.lean|PEqualNP/Outside/L_meta_1501.lean|d59441b3eaa88603ebbc72ee6b4f59d1a0512ab559a39cc2f53b1430af608dcc"
  "c8|dependencies/L_meta_2235.lean|PEqualNP/Outside/L_meta_2235.lean|fe68d9e33c8e6369bce3fce31f9a703b42f0c3f160c9056d485f8654a87c1bbf"
  "c8|lean/Pnp4201OrBudget.lean|Pnp4201OrBudget.lean|e2b63e64080ec8919a421d0c64e8fc0d679546e858cd479190cb794189e70858"
  "c8|lean/Pnp4201BudgetTopForm.lean|Pnp4201BudgetTopForm.lean|4a6c8b5140f99a7c6730080441636ff51f76f3f33b286f6271fdd27c1d8c59d9"
  "c8|lean/Pnp4201CleanBudgetTopForm.lean|Pnp4201CleanBudgetTopForm.lean|48e7d9aa2a5ddd8b8be6a118903cb74c8e4e0b36d7cc22e74bedc5568cd465fc"
  "c8|lean/Pnp4201CleanNormalize.lean|Pnp4201CleanNormalize.lean|550c6a6f4160184c8e5b71c9e4e4080e6909c93a465a3cef769fa8c03569578d"
  "c8|lean/Pnp4201CleanOrCount.lean|Pnp4201CleanOrCount.lean|171665a973dec6ebe230ad3daca21d98a8065ef73f412f87028b32c7f1a202fd"
  "self|Pnp2590Graph.lean|Pnp2590Graph.lean|deb90e3f1ebcf96e6143539be60105bd1ec1f930ae65258d975a659a5394f70d"
  "self|Pnp2590CleanBound.lean|Pnp2590CleanBound.lean|841942f7dc4fe48f250d1e9b2dd1c5fd6b2d92500f7a8b862e72861bae392d07"
  "self|Pnp2590CleanBoundAudit.lean|Pnp2590CleanBoundAudit.lean|043aec1380cdfd6813e39d92d450c6471b64e14b91cd3479518538e26cb0ccc7"
)
pnp_sources=()
pnp_destinations=()
for pnp_spec in "${pnp_specs[@]}"; do
  IFS='|' read -r pnp_kind pnp_rel pnp_dest pnp_sha <<< "$pnp_spec"
  if [[ "$pnp_kind" == c8 ]]; then pnp_src="$pnp_cont8/$pnp_rel"; else pnp_src="$pnp_script_dir/$pnp_rel"; fi
  [[ -f "$pnp_src" ]] || pnp_die "Missing frozen source: $pnp_src"
  pnp_actual=$(sha256sum -- "$pnp_src")
  pnp_actual=${pnp_actual%% *}
  [[ "$pnp_actual" == "$pnp_sha" ]] || pnp_die "Frozen source hash mismatch: $pnp_src"
  pnp_dst="$pnp_lean_dir/$pnp_dest"
  [[ ! -L "$pnp_dst" ]] || pnp_die "Refusing source-file symlink destination: $pnp_dst"
  if [[ -e "$pnp_dst" ]]; then
    [[ -f "$pnp_dst" ]] || pnp_die "Destination is not a regular file: $pnp_dst"
    cmp -s -- "$pnp_src" "$pnp_dst" || pnp_die "Refusing to overwrite different file: $pnp_dst. Use a fresh worktree."
  fi
  pnp_sources+=("$pnp_src")
  pnp_destinations+=("$pnp_dest")
done
# No proof source is written until every source and destination has passed preflight.
for pnp_i in "${!pnp_sources[@]}"; do
  pnp_dst="$pnp_lean_dir/${pnp_destinations[$pnp_i]}"
  mkdir -p -- "$(dirname -- "$pnp_dst")"
  [[ -e "$pnp_dst" ]] || cp -- "${pnp_sources[$pnp_i]}" "$pnp_dst"
done

pnp_logs=$(mktemp -d "$pnp_checkout/pnp2590-reproduction-XXXXXX")
cd -- "$pnp_lean_dir"
pnp_lake() {
  PEQUALNP_REAL_LAKE="$pnp_toolchain/bin/lake" "$pnp_checkout/tools/bin/lake" "$@"
}
printf 'Ordinary reproduction only. Logs: %s\n' "$pnp_logs"
if ! pnp_lake build PEqualNP.Defs > "$pnp_logs/Defs-build.log" 2>&1; then
  cat "$pnp_logs/Defs-build.log" >&2
  pnp_die 'Defs setup build failed; no cache download or update was attempted by this script.'
fi
for pnp_rel in "${pnp_destinations[@]}"; do
  pnp_label=$(basename -- "$pnp_rel" .lean)
  pnp_log="$pnp_logs/$pnp_label.log"
  if [[ "$pnp_rel" == Pnp2590CleanBoundAudit.lean ]]; then
    if ! pnp_lake env lean -j1 "$pnp_rel" > "$pnp_log" 2>&1; then cat "$pnp_log" >&2; pnp_die "Axiom audit failed: $pnp_label"; fi
    cat "$pnp_log"
  else
    pnp_olean=".lake/build/lib/lean/${pnp_rel%.lean}.olean"
    mkdir -p -- "$(dirname -- "$pnp_olean")"
    if ! pnp_lake env lean -j1 -o "$pnp_olean" "$pnp_rel" > "$pnp_log" 2>&1; then cat "$pnp_log" >&2; pnp_die "Ordinary Lean check failed: $pnp_label"; fi
    printf 'PASS ordinary Lean: %s\n' "$pnp_label"
  fi
done
printf 'Completed ordinary clean-case reproduction. L-meta-2590 is not proved by this package. Logs: %s\n' "$pnp_logs"
