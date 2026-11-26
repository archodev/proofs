#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

lake env lean --version
mapfile -t modules < <(
  find C5 OAI Erdos173 -name '*.lean' -exec awk '
    $1 == "import" && $2 ~ /^Mathlib([.]|$)/ { print $2 }
    $1 == "public" && $2 == "import" && $3 ~ /^Mathlib([.]|$)/ { print $3 }
  ' {} + | sort -u
)
lake exe cache get "${modules[@]}"
lake build C5
audit=$(mktemp)
trap 'rm -f "$audit"' EXIT
lake env lean Audit.lean | tee "$audit"
diff -u axioms.txt "$audit"
