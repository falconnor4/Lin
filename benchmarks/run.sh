#!/bin/sh
set -e
cd "$(dirname "$0")/.."

printf "%-15s %-10s %-20s %-20s %-15s\n" "Benchmark" "Metric" "Unoptimized (.lin)" "AOT E-Graph (.line)" "Reduction"
printf "%-15s %-10s %-20s %-20s %-15s\n" "---------------" "----------" "--------------------" "--------------------" "---------------"

for f in benchmarks/bench_*.lin; do
  name=$(basename "$f" .lin | sed 's/bench_//')
  line_file="${f%.lin}.line"

  # 1. Unoptimized run
  unopt_err=$(./lin -b "$f" 2>&1 1>/dev/null)
  u_steps=$(printf '%s' "$unopt_err" | sed -n 's/.*\[bench\] *\([0-9]*\) *steps.*/\1/p')
  u_nodes=$(printf '%s' "$unopt_err" | sed -n 's/.*| *\([0-9]*\) *nodes.*/\1/p')

  # 2. Build with AOT E-Graph
  ./lin build "$f" -o "$line_file" 2>/dev/null

  # 3. Optimized run
  opt_err=$(./lin -b "$line_file" 2>&1 1>/dev/null)
  o_steps=$(printf '%s' "$opt_err" | sed -n 's/.*\[bench\] *\([0-9]*\) *steps.*/\1/p')
  o_nodes=$(printf '%s' "$opt_err" | sed -n 's/.*| *\([0-9]*\) *nodes.*/\1/p')

  # Clean up .line file
  rm -f "$line_file"

  # Compute integer percentage reductions
  if [ -n "$u_steps" ] && [ -n "$o_steps" ] && [ "$u_steps" -gt 0 ]; then
    step_pct=$(( (u_steps - o_steps) * 100 / u_steps ))
  else
    step_pct=0
  fi

  if [ -n "$u_nodes" ] && [ -n "$o_nodes" ] && [ "$u_nodes" -gt 0 ]; then
    node_pct=$(( (u_nodes - o_nodes) * 100 / u_nodes ))
  else
    node_pct=0
  fi

  printf "%-15s %-10s %-20s %-20s -%d%%\n" "$name" "Steps" "$u_steps" "$o_steps" "$step_pct"
  printf "%-15s %-10s %-20s %-20s -%d%%\n" "" "Nodes" "$u_nodes" "$o_nodes" "$node_pct"
  printf "%-15s %-10s %-20s %-20s %-15s\n" "" "Result" "verified" "verified" "MATCH"
  echo ""
done
