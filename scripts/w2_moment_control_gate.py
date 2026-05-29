#!/usr/bin/env python3
"""
P1 viability gate (session 10): does plain (K=1, loopless, W^1) multigraph
hom-count equivalence CONTROL the enriched W^2 moment  w2[i] = sum_t W_t^2 B(i,t)?

Equivalent linear-algebra question: is the vector w2 in the linear span V of
plain rooted-multigraph eval vectors  (i |-> evalK1(M, i))  over vertices i?

Because tupleEquivMulti = "agree on all plain evals" = "agree on all of V":
  - w2 in V   <=>  (tupleEquivMulti  =>  w2 agreement)            [route may proceed]
  - w2 not V  =>  V is a proper subalgebra of orbit-invariant
              =>  plain multigraph evals do NOT separate orbits
              =>  multiEval_separates_orbits is FALSE for that (B,W).

We also report dim V vs #vertex-orbits (dim V = #orbits  <=>  separation holds
at this enumeration depth, since V is a unital subalgebra of orbit-invariants).
"""

import itertools
import numpy as np
from adjacency_span import make_test_cases, compute_automorphisms


def vertex_orbit_count(auts, T):
    """Number of orbits of the automorphism group acting on vertices {0..T-1}.
    `auts` is a list of permutations (perm[i] = image of i)."""
    parent = list(range(T))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    for perm in auts:
        for i in range(T):
            union(i, int(perm[i]))
    return len({find(i) for i in range(T)})


def eval_k1(n, mult, B, W, i):
    """Rooted (K=1) multigraph eval. Vertices: 0=root(color i), 1..n unlabeled.
    mult: dict {(a,b): m} with 0<=a<b<=n. Loopless (no (a,a))."""
    T = B.shape[0]
    total = 0.0
    for sigma in itertools.product(range(T), repeat=n):
        col = (i,) + sigma
        w = 1.0
        for v in range(1, n + 1):
            w *= W[col[v]]
        ok = True
        for (a, b), m in mult.items():
            if m:
                w *= B[col[a], col[b]] ** m
        total += w
    return total


def enumerate_multigraphs(n, maxmult):
    """All loopless multiplicity assignments on pairs among {0..n}."""
    pairs = [(a, b) for a in range(n + 1) for b in range(a + 1, n + 1)]
    for combo in itertools.product(range(maxmult + 1), repeat=len(pairs)):
        yield {pairs[k]: combo[k] for k in range(len(pairs))}


def span_matrix(B, W, max_unlabeled, maxmult):
    T = B.shape[0]
    rows = []
    for n in range(max_unlabeled + 1):
        for mult in enumerate_multigraphs(n, maxmult):
            rows.append([eval_k1(n, mult, B, W, i) for i in range(T)])
    return np.array(rows)


def in_rowspace(E, v, tol=1e-8):
    # Normalize each row to unit max-norm so the (relative) rank test is robust to
    # the large magnitudes produced by high edge multiplicities / products.
    def norm_rows(M):
        s = np.abs(M).max(axis=1, keepdims=True)
        s[s == 0] = 1.0
        return M / s
    En = norm_rows(E)
    r1 = np.linalg.matrix_rank(En, tol=tol)
    r2 = np.linalg.matrix_rank(norm_rows(np.vstack([E, v[None, :]])), tol=tol)
    return r1 == r2, r1


def analyze(B, W, name, max_unlabeled=3, maxmult=3, tol=1e-8):
    T = B.shape[0]
    E = span_matrix(B, W, max_unlabeled, maxmult)
    w2 = np.array([sum(W[t] ** 2 * B[i, t] for t in range(T)) for i in range(T)])
    w2_in, dimV = in_rowspace(E, w2, tol)
    auts = compute_automorphisms(B, W, tol=tol)
    n_orb = vertex_orbit_count(auts, T)
    sep = (dimV == n_orb)
    print(f"[{'w2 IN V ' if w2_in else 'w2 NOT V'}] {name}")
    print(f"    T={T}  dim V={dimV}  #orbits={n_orb}  "
          f"separation(dimV==#orb)={sep}  (max_unlab={max_unlabeled},maxmult={maxmult})")
    return w2_in, dimV, n_orb


def random_search(trials=400, seed=0, Ts=(3, 4), vals=(0, 1, 2, 3),
                  max_unlabeled=2, maxmult=3, tol=1e-8):
    rng = np.random.default_rng(seed)
    found = 0
    for _ in range(trials):
        T = int(rng.choice(Ts))
        # random symmetric B with small integer entries (incl. diagonal)
        M = rng.choice(vals, size=(T, T))
        B = np.triu(M) + np.triu(M, 1).T
        B = B.astype(float)
        # twin-free check: distinct rows
        rows = {tuple(B[i]) for i in range(T)}
        if len(rows) != T:
            continue
        W = rng.choice([1, 2, 3, 4], size=T).astype(float)  # non-uniform positive
        E = span_matrix(B, W, max_unlabeled, maxmult)
        w2 = np.array([sum(W[t] ** 2 * B[i, t] for t in range(T)) for i in range(T)])
        w2_in, dimV = in_rowspace(E, w2, tol)
        auts = compute_automorphisms(B, W, tol=tol)
        n_orb = vertex_orbit_count(auts, T)
        if (not w2_in) or (dimV < n_orb):
            found += 1
            print(f"  *** CANDIDATE: T={T} dimV={dimV} #orb={n_orb} w2_in={w2_in}")
            print(f"      B={B.tolist()}")
            print(f"      W={W.tolist()}")
            if found >= 10:
                break
    if found == 0:
        print(f"  no counterexample in {trials} trials "
              f"(max_unlab={max_unlabeled},maxmult={maxmult}): w2 always in V and dimV==#orb")


if __name__ == "__main__":
    print("=== test cases ===")
    for tc in make_test_cases():
        try:
            analyze(tc.B, tc.W, tc.name)
        except Exception as e:
            print(f"  error on {tc.name}: {e}")
    print("\n=== random search for counterexample (w2 not in V, or dimV<#orb) ===")
    random_search()
