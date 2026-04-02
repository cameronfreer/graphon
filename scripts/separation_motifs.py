#!/usr/bin/env python3
"""
Targeted falsification and motif analysis for edgeFreeIndist_implies_pairOrbitRel.

For each test case:
1. Find all non-orbit pairs
2. For each non-orbit pair, find the SMALLEST edge-free graph that separates them
3. Categorize the separating graphs by structure (path, star, tree, etc.)
4. Test edgeFreeIndist → edge_eq specifically
"""

import numpy as np
from itertools import permutations
import sys
sys.path.insert(0, 'scripts')
from adjacency_span import (
    labeled_eval2, enumerate_simple_graphs, compute_automorphisms
)


def classify_graph(adj, n_verts):
    """Classify a small graph by structure."""
    n_edges = adj.sum() // 2
    has_label_edge = bool(adj[0][1])
    if has_label_edge:
        return f"HAS_LABEL_EDGE"
    if n_edges == 0:
        return "empty"
    if n_edges == 1:
        # Find the edge
        for i in range(n_verts):
            for j in range(i+1, n_verts):
                if adj[i][j]:
                    if i < 2 and j >= 2:
                        return f"star-{i}"  # star from label i
                    elif i >= 2 and j >= 2:
                        return "internal-edge"
                    else:
                        return f"edge-{i}-{j}"
    if n_edges == 2:
        edges = []
        for i in range(n_verts):
            for j in range(i+1, n_verts):
                if adj[i][j]:
                    edges.append((i, j))
        # Path 0-v-1?
        if len(edges) == 2:
            e1, e2 = edges
            if (0 in e1 and 1 in e2) or (1 in e1 and 0 in e2):
                return "path-0-v-1"
            elif 0 in e1 and 0 in e2:
                return "star-0-double"
            elif 1 in e1 and 1 in e2:
                return "star-1-double"
            else:
                return f"2-edge-other"
    return f"{n_edges}-edges"


def find_smallest_separator(T, B, W, p, q, max_unlabeled=3):
    """Find the smallest edge-free graph separating pairs p and q."""
    for n in range(max_unlabeled + 1):
        n_verts = n + 2
        for idx, adj in enumerate(enumerate_simple_graphs(n_verts)):
            if adj[0][1]:  # skip non-edge-free
                continue
            vp = labeled_eval2(n, adj, B, W, p[0], p[1])
            vq = labeled_eval2(n, adj, B, W, q[0], q[1])
            if abs(vp - vq) > 1e-10:
                cls = classify_graph(adj, n_verts)
                return n, idx, cls, vp, vq
    return None


def run_analysis():
    rng = np.random.RandomState(123)

    test_configs = []

    # Systematic: all T=2,3,4 with random matrices
    for trial in range(10):
        for T in [2, 3, 4]:
            A = rng.uniform(0.1, 0.9, (T, T))
            B = (A + A.T) / 2
            W = rng.uniform(0.1, 0.9, T)
            W = W / W.sum()
            test_configs.append((T, B, W, f"T={T},trial={trial}"))

    # Also try T=5 (smaller number of trials due to cost)
    for trial in range(3):
        T = 5
        A = rng.uniform(0.1, 0.9, (T, T))
        B = (A + A.T) / 2
        W = rng.uniform(0.1, 0.9, T)
        W = W / W.sum()
        test_configs.append((T, B, W, f"T={T},trial={trial}"))

    # Structured cases with nontrivial automorphisms
    # Z/2 on T=4
    B_z2 = np.array([[0.3, 0.7, 0.5, 0.5],
                      [0.7, 0.3, 0.5, 0.5],
                      [0.5, 0.5, 0.4, 0.6],
                      [0.5, 0.5, 0.6, 0.4]])
    W_z2 = np.array([0.25, 0.25, 0.25, 0.25])
    test_configs.append((4, B_z2, W_z2, "T=4,Z2xZ2"))

    # S3 on T=4
    B_s3 = np.array([[0.2, 0.8, 0.8, 0.5],
                      [0.8, 0.2, 0.8, 0.5],
                      [0.8, 0.8, 0.2, 0.5],
                      [0.5, 0.5, 0.5, 0.3]])
    W_s3 = np.array([0.25, 0.25, 0.25, 0.25])
    test_configs.append((4, B_s3, W_s3, "T=4,S3"))

    motif_counts = {}
    any_fail = False

    for T, B, W, label in test_configs:
        auts = compute_automorphisms(B, W)

        # Find all non-orbit pairs
        non_orbit_pairs = []
        for i1 in range(T):
            for j1 in range(T):
                for i2 in range(T):
                    for j2 in range(T):
                        if (i1, j1) >= (i2, j2):
                            continue
                        same_orbit = any(p[i1]==i2 and p[j1]==j2 for p in auts)
                        if not same_orbit:
                            non_orbit_pairs.append(((i1,j1), (i2,j2)))

        if not non_orbit_pairs:
            continue

        # For each non-orbit pair, find smallest separator
        max_n_needed = 0
        for p, q in non_orbit_pairs:
            result = find_smallest_separator(T, B, W, p, q, max_unlabeled=2)
            if result is None:
                print(f"[FAIL] {label}: no separator found for {p} vs {q} with ≤2 unlabeled!")
                any_fail = True
            else:
                n, idx, cls, vp, vq = result
                max_n_needed = max(max_n_needed, n)
                motif_counts[cls] = motif_counts.get(cls, 0) + 1

        if max_n_needed <= 1:
            complexity = "≤1 unlabeled"
        else:
            complexity = f"≤{max_n_needed} unlabeled"

    print("=== Motif separation summary ===")
    print(f"Total non-orbit pairs tested: {sum(motif_counts.values())}")
    print(f"Any failure: {any_fail}")
    print()
    print("Separating motif distribution:")
    for cls, count in sorted(motif_counts.items(), key=lambda x: -x[1]):
        print(f"  {cls}: {count}")


if __name__ == "__main__":
    run_analysis()
