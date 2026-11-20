#!/usr/bin/env python3
"""Independent checker for the F3 lift-chain excluded sets in evidence.json.

Shares no code with the Rust implementation. For each depth M it:

1. builds the transition graph G_M by applying the accelerated Collatz map
   T directly to the integer representatives u and u + 2^M of every residue
   u mod 2^M (no bit-twiddling successor formula);
2. computes, for the active vertex set V_M minus S, the least non-negative
   potential phi with  phi(u) >= q*odd(u) - p + phi(v)  on every active edge
   u -> v (the F3 condition  q*odd(u) + phi(v) - phi(u) <= p) by
   label-correcting longest paths. If no positive-weight cycle exists the
   values are bounded by (q - p) * (number of active vertices); exceeding
   that bound proves infeasibility;
3. re-checks every active edge against the final potential, and checks the
   recorded counts (|S|, even count, monotone density |S_M| <= 2 |S_{M-1}|).

Exit status 0 iff every requested depth passes. This is a finite check of
the recorded sets only; it says nothing about optimality or the limit of
the density.
"""

import argparse
import json
import sys
import time
from collections import deque

P, Q = 63, 100


def collatz_t(n: int) -> int:
    return (3 * n + 1) // 2 if n % 2 else n // 2


def check_depth(m: int, excluded: list[int]) -> dict:
    n = 1 << m
    active = bytearray([1]) * n
    for u in excluded:
        active[u] = 0
    succ0 = [0] * n
    succ1 = [0] * n
    preds: list[list[int]] = [[] for _ in range(n)]
    for u in range(n):
        a = collatz_t(u) % n
        b = collatz_t(u + n) % n
        succ0[u], succ1[u] = a, b
        if active[u]:
            if active[a]:
                preds[a].append(u)
            if active[b] and b != a:
                preds[b].append(u)
    weight = [Q * (u & 1) - P for u in range(n)]
    n_active = n - len(excluded)
    cap = (Q - P) * n_active
    phi = [0] * n
    queue = deque(u for u in range(n) if active[u])
    queued = bytearray(active)
    relaxations = 0
    while queue:
        u = queue.popleft()
        queued[u] = 0
        best = 0
        w = weight[u]
        a, b = succ0[u], succ1[u]
        if active[a]:
            best = max(best, w + phi[a])
        if active[b]:
            best = max(best, w + phi[b])
        if best > phi[u]:
            phi[u] = best
            relaxations += 1
            if best > cap:
                return {"M": m, "feasible": False, "reason": "potential exceeded cap"}
            for v in preds[u]:
                if not queued[v]:
                    queued[v] = 1
                    queue.append(v)
    edges = 0
    for u in range(n):
        if not active[u]:
            continue
        for v in {succ0[u], succ1[u]}:
            if active[v]:
                edges += 1
                if Q * (u & 1) + phi[v] - phi[u] > P:
                    return {"M": m, "feasible": False, "reason": f"edge {u}->{v} fails"}
    return {
        "M": m,
        "feasible": True,
        "excluded": len(excluded),
        "active_edges": edges,
        "max_phi": max(phi[u] for u in range(n) if active[u]),
        "relaxations": relaxations,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--evidence", default="research/lyapunov-lift/evidence.json")
    ap.add_argument("--min-m", type=int, default=1)
    ap.add_argument("--max-m", type=int, default=None)
    args = ap.parse_args()
    data = json.load(open(args.evidence))
    if (data["target_p"], data["target_q"]) != (P, Q) or 3**P >= 2**Q:
        print("unexpected contraction target", file=sys.stderr)
        return 1
    ok = True
    prev = None
    for row in data["rows"]:
        m = row["modulus_bits"]
        s = row["chain_excluded"]
        if prev is not None and len(s) > 2 * prev:
            print(f"M={m}: density increased", file=sys.stderr)
            ok = False
        prev = len(s)
        if m < args.min_m or (args.max_m is not None and m > args.max_m):
            continue
        if (
            len(s) != row["chain_count"]
            or len(set(s)) != len(s)
            or any(not 0 <= u < (1 << m) for u in s)
            or sum(1 for u in s if u % 2 == 0) != row["chain_even_count"]
            or (m >= 2 and row["chain_active_edges"] == 0)
        ):
            print(f"M={m}: recorded counts inconsistent", file=sys.stderr)
            ok = False
            continue
        t0 = time.time()
        res = check_depth(m, s)
        res["seconds"] = round(time.time() - t0, 1)
        if res["feasible"] and res["active_edges"] != row["chain_active_edges"]:
            res["feasible"] = False
            res["reason"] = "active edge count differs from evidence"
        ok &= res["feasible"]
        print(json.dumps(res), flush=True)
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
