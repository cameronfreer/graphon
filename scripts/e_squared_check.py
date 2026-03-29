#!/usr/bin/env python3
"""
E² checkpoint: verify that B(i,j)² lies in the linear span of actual
2-labeled simple graph evaluations, for each test case.

Also check: which specific graphs contribute to expressing E²?
"""

import numpy as np
from adjacency_span import (
    make_test_cases, labeled_eval2, enumerate_simple_graphs,
    compute_automorphisms, count_orbits_direct
)


def check_e_squared(B, W, max_unlabeled=2, tol=1e-10):
    """Check if B(i,j)² is in the span of graph evaluations."""
    T = B.shape[0]
    e_sq = (B ** 2).flatten()  # E²(i,j) = B(i,j)²

    # Build matrix of all graph evaluation vectors
    vectors = []
    graph_labels = []
    for n in range(max_unlabeled + 1):
        n_verts = n + 2
        for idx, adj in enumerate(enumerate_simple_graphs(n_verts)):
            vec = np.zeros(T * T)
            for i in range(T):
                for j in range(T):
                    vec[i * T + j] = labeled_eval2(n, adj, B, W, i, j)
            vectors.append(vec)
            # Check if this graph has the label edge {0,1}
            has_label_edge = bool(adj[0][1])
            n_edges = adj.sum() // 2
            graph_labels.append(f"n={n},idx={idx},edges={n_edges},label01={has_label_edge}")

    if not vectors:
        return False, None

    mat = np.vstack(vectors)

    # Check if E² is in the span
    # Solve: mat.T @ coeffs = e_sq (least squares)
    result = np.linalg.lstsq(mat.T, e_sq, rcond=None)
    coeffs = result[0]
    residual = np.linalg.norm(mat.T @ coeffs - e_sq)
    in_span = residual < tol

    # Find which graphs contribute (nonzero coefficients)
    contributors = []
    for idx, c in enumerate(coeffs):
        if abs(c) > tol:
            contributors.append((graph_labels[idx], c))

    return in_span, contributors


def run_check():
    cases = make_test_cases()

    for tc in cases:
        T = tc.B.shape[0]
        max_unlab = 2

        in_span, contributors = check_e_squared(tc.B, tc.W, max_unlabeled=max_unlab)

        status = "PASS" if in_span else "FAIL"
        print(f"[{status}] {tc.name}")
        print(f"       T={T}  E² in span(graphEval≤{max_unlab}): {in_span}")
        if contributors:
            print(f"       Nonzero coefficients: {len(contributors)}")
            for label, coeff in sorted(contributors, key=lambda x: -abs(x[1]))[:5]:
                print(f"         {coeff:+.6f}  {label}")
        print()


if __name__ == "__main__":
    run_check()
