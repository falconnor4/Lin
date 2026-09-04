#!/usr/bin/env python3
"""Tseitin parity expander benchmark."""

import subprocess
import time
import tempfile
import os

def generate_tseitin_lin(n):
    # Construct 3-regular graph: ring + cross
    edges = []
    for i in range(n):
        edges.append((i, (i + 1) % n))
    for i in range(n // 2):
        edges.append((i, (i + n // 2) % n))
    
    edge_map = {}
    for idx, (u, v) in enumerate(edges, 1):
        edge_map[(u, v)] = idx
        edge_map[(v, u)] = idx
    num_edges = len(edges)
    
    clauses = []
    for v in range(n):
        nbrs = [(v + 1) % n, (v - 1 + n) % n, (v + n // 2) % n]
        e1, e2, e3 = [edge_map[(v, u)] for u in nbrs]
        v1, v2, v3 = f"e{e1}", f"e{e2}", f"e{e3}"
        charge = 1 if v == 0 else 0
        if charge == 1:
            c_specs = [
                (v1, v2, v3),
                (v1, f"(not {v2})", f"(not {v3})"),
                (f"(not {v1})", v2, f"(not {v3})"),
                (f"(not {v1})", f"(not {v2})", v3),
            ]
        else:
            c_specs = [
                (v1, v2, f"(not {v3})"),
                (v1, f"(not {v2})", v3),
                (f"(not {v1})", v2, v3),
                (f"(not {v1})", f"(not {v2})", f"(not {v3})"),
            ]
        for a, b, c in c_specs:
            clauses.append(f"(or3 {a} {b} {c})")
    
    body = clauses[0]
    for c in clauses[1:]:
        body = f"((and {body}) {c})"
    for i in range(num_edges, 0, -1):
        body = f"(exists (\\e{i} {body}))"
        
    return f"""(define! tru bool (\\t (\\f t)))
(define! fls bool (\\t (\\f f)))
(define! or (bool -> bool -> bool) (\\a (\\b ((a tru) b))))
(define! and (bool -> bool -> bool) (\\a (\\b ((a b) fls))))
(define! not (bool -> bool) (\\b (\\t (\\f ((b f) t)))))
(define! exists ((bool -> bool) -> bool) (\\p ((or (p tru)) (p fls))))
(define or3 (\\a (\\b (\\c ((or ((or a) b)) c)))))

{body}
"""

def run_bench():
    print(f"{'Vertices':>8} {'Edges':>8} {'Clauses':>8} {'Space':>10} {'Steps':>8} {'Expected':>10} {'Time (ms)':>10}")
    print("-" * 68)
    
    sizes = [4, 6, 8, 10, 12, 14, 16, 20]
    for n in sizes:
        num_edges = (3 * n) // 2
        num_clauses = 4 * n
        code = generate_tseitin_lin(n)
        
        with tempfile.NamedTemporaryFile("w", suffix=".lin", delete=False) as tf:
            tf.write(code)
            tpath = tf.name
            
        try:
            t0 = time.perf_counter()
            res = subprocess.run(
                ["./lin", tpath],
                capture_output=True,
                text=True,
                env={**os.environ, "LIN_TRACE": "1"}
            )
            elapsed_ms = (time.perf_counter() - t0) * 1000
            steps = len(res.stderr.splitlines())
            expected_steps = 82 * num_edges - 3
            space_str = f"2^{num_edges}"
            print(f"{n:>8d} {num_edges:>8d} {num_clauses:>8d} {space_str:>10} {steps:>8d} {expected_steps:>10d} {elapsed_ms:>10.2f}")
        finally:
            if os.path.exists(tpath):
                os.remove(tpath)

if __name__ == "__main__":
    run_bench()
