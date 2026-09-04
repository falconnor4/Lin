#!/usr/bin/env python3
"""Traveling salesperson problem (TSP) benchmark."""

import subprocess
import time
import tempfile
import os

def generate_tsp_lin(budget):
    # 4-city instance:
    # Tour A (0,0): cost 27
    # Tour B (0,1): cost 24 (Optimal)
    # Tour C (1,0): cost 33
    conds = []
    if budget >= 27:
        conds.append("(and (not b0) (not b1))") # Tour A
    if budget >= 24:
        conds.append("(and (not b0) b1)")       # Tour B (optimal)
    if budget >= 33:
        conds.append("(and b0 (not b1))")       # Tour C
        
    if not conds:
        predicate = "false"
    elif len(conds) == 1:
        predicate = conds[0]
    elif len(conds) == 2:
        predicate = f"(or {conds[0]} {conds[1]})"
    else:
        predicate = f"(or {conds[0]} (or {conds[1]} {conds[2]}))"
        
    return f"""(load "std/sat.lin")
(load "std/list.lin")
(load "std/pair.lin")

(define decode_tour
  (\\w
    (ifl (fst w)
      (\\_ (cons 0 (cons 2 (cons 1 (cons 3 (cons 0 nil))))))
      (\\_ (ifl (snd w)
            (\\_ (cons 0 (cons 1 (cons 3 (cons 2 (cons 0 nil))))))
            (\\_ (cons 0 (cons 1 (cons 2 (cons 3 (cons 0 nil)))))))))))

(define tour_cost
  (\\w
    (ifl (fst w)
      (\\_ 33)
      (\\_ (ifl (snd w)
            (\\_ 24)
            (\\_ 27))))))

(define tsp_formula
  (\\b0 (\\b1
    {predicate})))

(define model (probe2 tsp_formula))
(fst model)
(define witness (snd model))
(fst witness)
(snd witness)
(verify2 tsp_formula witness)
(tour_cost witness)
(define tour (decode_tour witness))
(first tour)
(second tour)
(third tour)
(fourth tour)
(fifth tour)
"""

def run_bench():
    print(f"{'Budget':>8} {'Status':>8} {'Cost':>6} {'Steps':>8} {'Time (ms)':>10}  {'Witness Tour'}")
    print("-" * 68)
    
    budgets = [15, 20, 23, 24, 25, 28, 30, 35]
    for b in budgets:
        code = generate_tsp_lin(b)
        with tempfile.NamedTemporaryFile("w", suffix=".lin", delete=False) as tf:
            tf.write(code)
            tpath = tf.name
            
        try:
            t0 = time.perf_counter()
            res = subprocess.run(
                ["./lin", "-b", tpath],
                capture_output=True,
                text=True
            )
            elapsed_ms = (time.perf_counter() - t0) * 1000
            lines = res.stdout.strip().splitlines()
            bench_lines = [l for l in res.stderr.splitlines() if "[bench]" in l]
            
            total_steps = 0
            for bl in bench_lines:
                try:
                    parts = bl.split()
                    idx = parts.index("steps")
                    total_steps += int(parts[idx - 1])
                except (ValueError, IndexError):
                    pass
            
            is_sat = "true" in lines[0] if lines else False
            if is_sat:
                status = "SAT"
                b0 = "true" in lines[1]
                b1 = "true" in lines[2]
                cost = lines[4].replace("=> ", "").strip()
                path = [l.replace("=> ", "").strip() for l in lines[5:10]]
                tour_str = " -> ".join(path)
            else:
                status = "UNSAT"
                tour_str = "None (No path <= B)"
                cost = "-"
                
            print(f"{b:>8d} {status:>8} {cost:>6} {total_steps:>8d} {elapsed_ms:>10.2f}  {tour_str}")
        finally:
            if os.path.exists(tpath):
                os.remove(tpath)

if __name__ == "__main__":
    run_bench()
