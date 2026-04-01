#!/usr/bin/env python3
"""
Inspect edgeFreeIndist, fullIndist, and orbit classes on small cases.

For each test case:
1. Compute edgeFreeIndist classes (pairs agreeing on all edge-free evaluations)
2. Compute fullIndist classes (edgeFreeIndist + same edge value)
3. Compute orbit classes (pairs related by Aut(B,W))
4. Compare: fullIndist should equal orbit (CT-1 hard direction)
5. For any non-orbit pair with same edge value, find separating edge-free graph
"""

import numpy as np
from itertools import permutations
from adjacency_span import (
    make_test_cases, labeled_eval2, enumerate_simple_graphs,
    compute_automorphisms
)


def compute_edgefree_eval_vectors(B, W, max_unlabeled=2):
    """Compute evaluation vectors for all edge-free 2-labeled graphs."""
    T = B.shape[0]
    vectors = []
    graph_labels = []
    for n in range(max_unlabeled + 1):
        n_verts = n + 2
        for idx, adj in enumerate(enumerate_simple_graphs(n_verts)):
            # Check edge-free: no edge between vertices 0 and 1
            if adj[0][1] == 1:
                continue
            vec = np.zeros(T * T)
            for i in range(T):
                for j in range(T):
                    vec[i * T + j] = labeled_eval2(n, adj, B, W, i, j)
            vectors.append(vec)
            n_edges = adj.sum() // 2
            graph_labels.append(f"n={n},idx={idx},edges={n_edges}")
    return vectors, graph_labels


def compute_classes(T, equiv_fn):
    """Compute equivalence classes of pairs under equiv_fn."""
    parent = {}
    def find(x):
        while parent.get(x, x) != x:
            parent[x] = parent.get(parent[x], parent[x])
            x = parent[x]
        return x
    def union(x, y):
        px, py = find(x), find(y)
        if px != py:
            parent[px] = py

    pairs = [(i, j) for i in range(T) for j in range(T)]
    for p in pairs:
        for q in pairs:
            if equiv_fn(p, q):
                union(p, q)

    classes = {}
    for p in pairs:
        root = find(p)
        classes.setdefault(root, []).append(p)
    return list(classes.values())


def run_check():
    cases = make_test_cases()

    for tc in cases:
        T = tc.B.shape[0]
        B, W = tc.B, tc.W
        max_unlab = 2

        # Compute edge-free evaluation vectors
        ef_vecs, ef_labels = compute_edgefree_eval_vectors(B, W, max_unlabeled=max_unlab)

        # Edge-free indist: pairs where ALL edge-free evaluations agree
        def edgefree_indist(p, q):
            pi, pj = p
            qi, qj = q
            for vec in ef_vecs:
                if abs(vec[pi * T + pj] - vec[qi * T + qj]) > 1e-10:
                    return False
            return True

        # Full indist: edge-free indist + same edge value
        def full_indist(p, q):
            return edgefree_indist(p, q) and abs(B[p[0]][p[1]] - B[q[0]][q[1]]) < 1e-10

        # Orbit relation
        auts = compute_automorphisms(B, W)
        def orbit_rel(p, q):
            for perm in auts:
                if perm[p[0]] == q[0] and perm[p[1]] == q[1]:
                    return True
            return False

        ef_classes = compute_classes(T, edgefree_indist)
        full_classes = compute_classes(T, full_indist)
        orbit_classes = compute_classes(T, orbit_rel)

        # Compare
        full_match_orbit = len(full_classes) == len(orbit_classes)
        status = "PASS" if full_match_orbit else "FAIL"

        print(f"[{status}] {tc.name}")
        print(f"       T={T}  |Aut|={len(auts)}"
              f"  ef_classes={len(ef_classes)}"
              f"  full_classes={len(full_classes)}"
              f"  orbit_classes={len(orbit_classes)}")

        if not full_match_orbit:
            print(f"       *** MISMATCH: fullIndist has {len(full_classes)} classes"
                  f" but orbit has {len(orbit_classes)} ***")
            # Find a fullIndist pair that's NOT in the same orbit
            for cls in full_classes:
                if len(cls) > 1:
                    for i, p in enumerate(cls):
                        for q in cls[i+1:]:
                            if not orbit_rel(p, q):
                                print(f"       Counterexample: {p} fullIndist {q}"
                                      f" but NOT same orbit")
                                print(f"         B{p}={B[p[0]][p[1]]:.4f},"
                                      f" B{q}={B[q[0]][q[1]]:.4f}")

        # Show class structure
        if len(ef_classes) <= 10:
            print(f"       Edge-free classes:")
            for cls in sorted(ef_classes, key=lambda c: c[0]):
                edge_vals = sorted(set(round(B[p[0]][p[1]], 6) for p in cls))
                n_splits = len(edge_vals)
                print(f"         {cls} -> edge vals {edge_vals}"
                      f" (splits into {n_splits} full classes)")
        print()


if __name__ == "__main__":
    run_check()
