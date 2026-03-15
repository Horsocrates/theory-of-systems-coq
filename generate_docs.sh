#!/bin/bash
# generate_docs.sh — auto-generate FILE_MAP.md
# Run from repo root: bash generate_docs.sh

set -e

echo "# File Map" > docs/FILE_MAP.md
echo "" >> docs/FILE_MAP.md
echo "Auto-generated: $(date '+%Y-%m-%d %H:%M')" >> docs/FILE_MAP.md
echo "" >> docs/FILE_MAP.md

total_qed=0
total_admitted=0
total_files=0

for section in "src/*.v:Core" "src/analysis/*.v:Analysis" "src/process/*.v:P4 Process Mathematics" "src/stdlib/*.v:Stdlib" "src/gauge/*.v:Gauge Theory" "src/navier_stokes/*.v:Navier-Stokes" "src/linalg/*.v:Linear Algebra" "src/physics/*.v:Physics" "src/projective/*.v:Projective Systems" "src/experimental/*.v:Experimental Verification" "src/zeta/*.v:Zeta Function" "Architecture_of_Reasoning/*.v:Architecture of Reasoning"; do
  pattern="${section%%:*}"
  label="${section##*:}"

  echo "## $label" >> docs/FILE_MAP.md
  echo "" >> docs/FILE_MAP.md
  echo "| File | Qed | Admitted | Key Imports |" >> docs/FILE_MAP.md
  echo "|------|-----|---------|-------------|" >> docs/FILE_MAP.md

  for f in $pattern; do
    [ -f "$f" ] || continue
    name=$(basename "$f")
    qed=$(grep -c 'Qed\.' "$f" 2>/dev/null | tr -d '\r\n' || echo 0)
    admitted=$(grep -E '^\s*Admitted\.' "$f" 2>/dev/null | wc -l | tr -d ' \r\n' || echo 0)
    # Default to 0 if empty
    [ -z "$qed" ] && qed=0
    [ -z "$admitted" ] && admitted=0
    imports=$(grep 'From ToS' "$f" 2>/dev/null | sed 's/From ToS Require Import //' | sed 's/From ToS_Arch Require Import //' | sed 's/\.//' | tr -d '\r' | tr '\n' ', ' | sed 's/,$//' | head -c 60)

    echo "| \`$name\` | $qed | $admitted | $imports |" >> docs/FILE_MAP.md

    total_qed=$((total_qed + qed))
    total_admitted=$((total_admitted + admitted))
    total_files=$((total_files + 1))
  done

  echo "" >> docs/FILE_MAP.md
done

echo "## Totals" >> docs/FILE_MAP.md
echo "" >> docs/FILE_MAP.md
echo "| Metric | Count |" >> docs/FILE_MAP.md
echo "|--------|-------|" >> docs/FILE_MAP.md
echo "| Files | $total_files |" >> docs/FILE_MAP.md
echo "| Qed | $total_qed |" >> docs/FILE_MAP.md
echo "| Admitted | $total_admitted |" >> docs/FILE_MAP.md

echo "Generated docs/FILE_MAP.md: $total_files files, $total_qed Qed, $total_admitted Admitted"
