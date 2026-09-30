#!/usr/bin/env bash
set -eu

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
JAR="${AREND_JAR:-$HOME/Projects/Arend/cli/build/libs/cli-1.12.0-full.jar}"
SRC="$ROOT/proofmode-extension/src/main/java"
OUT="$ROOT/ext"

if [ ! -f "$JAR" ]; then
  echo "Arend CLI jar not found at: $JAR" >&2
  exit 1
fi

mkdir -p "$OUT"
find "$OUT" -type f -name '*.class' -delete
javac --release 21 -cp "$JAR" -d "$OUT" $(find "$SRC" -type f -name '*.java' | sort)
