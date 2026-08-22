#!/usr/bin/env bash
# Typecheck every `.ard` file in `src/` in dependency order (leaves first,
# fully-imported files last). Reports per-module success/failure and exits
# non-zero if any module fails.
#
# Project-internal imports are detected by checking whether an imported module
# name (e.g. `lib.gmap_cmra`) corresponds to a file under `src/`
# (`src/lib/gmap_cmra.ard`). Imports of external libraries (arend-lib's
# `Logic`, `Paths`, `Data.List`, …) are ignored.
#
# Avoids bashisms beyond POSIX-friendly bash 3.2 (no associative arrays, no
# `mapfile`) so it runs on stock macOS `/bin/bash`.
set -eu

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SRC="$ROOT/src"
# IRIS requires Arend 1.12 plus the argument-first conversion fix from PR #132.
# The canonical checker is the locally built patched master. Keep AREND_JAR
# overridable for reproducible checks against another explicit build.
JAR="${AREND_JAR:-$HOME/Projects/Arend/cli/build/libs/cli-1.12.0-full.jar}"
LIBDIR="${AREND_LIBDIR:-$HOME/.arend/libs}"

typecheck_flags=()
[ "${AREND_SERIALIZE:-0}" = "1" ] && typecheck_flags+=(--serialize)
[ "${AREND_RECOMPILE:-0}" = "1" ] && typecheck_flags+=(-r)
start_after="${AREND_START_AFTER:-}"
stop_on_error="${AREND_STOP_ON_ERROR:-0}"

if [ ! -f "$JAR" ]; then
  echo "Arend CLI jar not found at: $JAR" >&2
  exit 1
fi

AREND_JAR="$JAR" "$ROOT/scripts/build-proofmode-extension.sh"

# Map an absolute file path to an Arend module name:
#   src/ofe.ard              -> ofe
#   src/lib/gmap_cmra.ard    -> lib.gmap_cmra
#   src/example/fact.ard     -> example.fact
path_to_module() {
  rel="${1#"$SRC"/}"
  rel="${rel%.ard}"
  printf '%s\n' "${rel//\//.}"
}

module_to_file() {
  printf '%s/%s.ard\n' "$SRC" "${1//.//}"
}

ALL_FILES=$(find "$SRC" -type f -name '*.ard' | sort)
if [ -z "$ALL_FILES" ]; then
  echo "No .ard files under $SRC" >&2
  exit 1
fi

# Build the dependency edge list for `tsort`.
#
# Each project import in module M creates an edge `dep M`, where `dep`
# precedes `M` in the topological order. We also emit a phantom edge
# `__START__ M` so every module appears in `tsort`'s output even if it has
# no other incoming edges (purely-leaf modules).
edges_file=$(mktemp)
order_file=$(mktemp)
tsort_err=$(mktemp)
trap 'rm -f "$edges_file" "$order_file" "$tsort_err"' EXIT

echo "$ALL_FILES" | while IFS= read -r f; do
  mod=$(path_to_module "$f")
  printf '__START__ %s\n' "$mod" >>"$edges_file"
  # Extract the second token from `\import` lines, stripping any selective
  # import parenthesis (e.g. `\import lib.pmap (Pos, xH)` -> `lib.pmap`).
  awk '/^\\import / { print $2 }' "$f" \
    | sed 's/[()].*//' \
    | while IFS= read -r dep; do
        if [ -n "$dep" ] && [ -f "$(module_to_file "$dep")" ]; then
          printf '%s %s\n' "$dep" "$mod"
        fi
      done >>"$edges_file"
done

# Topologically sort. `tsort` emits every node even when there are cycles —
# it picks an arbitrary order for nodes inside a cycle and reports the cycle
# on stderr. Arend itself handles mutually-recursive modules, so we warn but
# do not fail when cycles are present.
tsort "$edges_file" >"$order_file" 2>"$tsort_err" || true
if grep -qi 'cycle' "$tsort_err"; then
  echo "Warning: cycle(s) in module imports (Arend handles them internally):" >&2
  grep -v '^tsort: cycle in data' "$tsort_err" \
    | sed 's/^tsort: /  /' >&2
fi

# Total module count (excluding the phantom sentinel).
total=$(grep -cv '^__START__$' "$order_file" || true)
if [ -n "$start_after" ] && ! grep -qx "$start_after" "$order_file"; then
  echo "Module named by AREND_START_AFTER was not found: $start_after" >&2
  exit 1
fi

cd "$ROOT"
errors=0
holes=0
i=0
started=1
[ -n "$start_after" ] && started=0

while IFS= read -r mod; do
  [ "$mod" = "__START__" ] && continue
  i=$((i + 1))
  if [ "$started" -eq 0 ]; then
    [ "$mod" = "$start_after" ] && started=1
    continue
  fi
  printf '\n[%d/%d] %s\n' "$i" "$total" "$mod"
  out=$(java -Xmx16g -jar "$JAR" -L "$LIBDIR" "${typecheck_flags[@]}" "$mod" 2>&1) || true
  has_error=0
  has_goal=0
  printf '%s\n' "$out" | grep -qE '^\[ERROR\]' && has_error=1
  printf '%s\n' "$out" | grep -qE '^\[GOAL\]'  && has_goal=1
  timing=$(printf '%s\n' "$out" | grep -oE 'Done \([0-9]+ms\)' | tail -1 || true)
  if [ "$has_error" -eq 1 ]; then
    printf '%s\n' "$out" | grep -E '^\[ERROR\]' | sed 's/^/  /' | head -10
    printf '  FAIL  %s  %s\n' "$mod" "${timing:-}"
    errors=$((errors + 1))
    [ "$stop_on_error" = "1" ] && break
  elif [ "$has_goal" -eq 1 ]; then
    n=$(printf '%s\n' "$out" | grep -cE '^\[GOAL\]')
    printf '  HOLE  %s  (%d unfilled goal(s))  %s\n' "$mod" "$n" "${timing:-}"
    holes=$((holes + 1))
  else
    printf '  ok    %s  %s\n' "$mod" "${timing:-}"
  fi
done <"$order_file"

printf '\n=== summary ===\n'
printf '%d module(s) checked' "$total"
[ "$holes"  -gt 0 ] && printf ', %d with unfilled holes' "$holes"
[ "$errors" -gt 0 ] && printf ', %d with errors' "$errors"
printf '\n'
if [ "$errors" -ne 0 ]; then
  echo "FAILED" >&2
  exit 1
fi
echo "OK"
