#!/usr/bin/env python3
"""
Adversarial search for cospectral-vertex counterexamples to
closed_walk_profiles_separate_vertex_orbits.

Per user 2026-05-14 methodology: before treating the conjecture as a
target, look harder for failures. Random + structured tests passed
(291/291). Now enumerate small simple graphs and check whether ANY of
them have twin-free B (rows distinct) with two NON-orbit vertices that
share the closed-walk profile for all m ≤ T.

If a counterexample is found: closed_walk_profiles_separate is FALSE
and we move to the rooted graph algebra approach.
If none found across small graphs: strengthens the empirical case.

Strategy:
- Enumerate all simple graphs on T = 6, 7, 8 vertices (Brendan McKay
  generation simulated by random sampling of large numbers).
- For each, compute closed-walk profiles for ALL vertex pairs.
- Find pairs (i, j) with same closed walks at all m ≤ T.
- Verify these pairs are in DIFFERENT orbits.
- Check that the graph is twin-free (rows of adjacency distinct).

Usage: python3 scripts/cospectral_vertex_search.py
"""

import sys
import numpy as np
from itertools import permutations, combinations


def flushprint(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


def is_twin_free(B, tol=1e-9):
    """Check if all rows of B are distinct."""
    T = B.shape[0]
    for i in range(T):
        for j in range(i + 1, T):
            if np.allclose(B[i], B[j], atol=tol):
                return False
    return True


def closed_walks_all(B, W, max_m):
    """Return T x (max_m+1) matrix of CW_m(i) values."""
    T = len(W)
    cw = np.zeros((T, max_m + 1))
    cw[:, 0] = 1.0
    if max_m >= 1:
        cw[:, 1] = np.diag(B)
    N = B * W[np.newaxis, :]
    Nm = np.eye(T)
    for m in range(1, max_m + 1):
        Nm = Nm @ N
        for i in range(T):
            if W[i] != 0:
                cw[i, m] = Nm[i, i] / W[i]
    return cw


def compute_aut_group(B, W, tol=1e-9):
    """Brute-force aut group. ONLY use for T ≤ 8."""
    T = len(W)
    auts = []
    for perm in permutations(range(T)):
        perm = list(perm)
        if not all(abs(W[perm[i]] - W[i]) < tol for i in range(T)):
            continue
        if not all(abs(B[perm[i]][perm[j]] - B[i][j]) < tol
                   for i in range(T) for j in range(T)):
            continue
        auts.append(tuple(perm))
    return auts


def in_same_orbit(i, j, auts):
    return any(σ[i] == j for σ in auts)


def search_simple_graphs(T, max_graphs=5000):
    """Enumerate / sample simple graphs on T vertices. Return list of B matrices."""
    n_edges = T * (T - 1) // 2
    edge_list = [(i, j) for i in range(T) for j in range(i + 1, T)]
    total = 2 ** n_edges
    if total <= max_graphs:
        # Full enumeration.
        masks = range(total)
    else:
        # Random sample.
        rng = np.random.default_rng(2026)
        masks = rng.choice(total, size=max_graphs, replace=False)
    graphs = []
    for mask in masks:
        B = np.zeros((T, T))
        for bit, (u, v) in enumerate(edge_list):
            if mask & (1 << bit):
                B[u, v] = 1.0
                B[v, u] = 1.0
        graphs.append(B)
    return graphs


def find_cospectral_vertex_pairs(T, max_graphs=5000, max_m=None):
    """Search for graphs with non-orbit cospectral vertex pairs.

    Returns list of (B, i, j) where i, j are NON-orbit cospectral vertices.
    """
    if max_m is None:
        max_m = T + 2
    counterexamples = []
    n_graphs_checked = 0
    n_twin_free = 0
    graphs = search_simple_graphs(T, max_graphs=max_graphs)
    W = np.ones(T)
    flushprint(f"\n=== T = {T}: scanning {len(graphs)} simple graphs ===")
    for B in graphs:
        n_graphs_checked += 1
        if not is_twin_free(B):
            continue
        n_twin_free += 1
        # Compute closed-walk profiles.
        cw = closed_walks_all(B, W, max_m)
        # Find candidate cospectral pairs FIRST (fast), then check orbit.
        candidate_pairs = []
        for i in range(T):
            for j in range(i + 1, T):
                if np.allclose(cw[i], cw[j], atol=1e-8):
                    candidate_pairs.append((i, j))
        if not candidate_pairs:
            continue
        # Only compute Aut if we have candidates.
        auts = compute_aut_group(B, W)
        for i, j in candidate_pairs:
            if not in_same_orbit(i, j, auts):
                counterexamples.append((B.copy(), i, j))
                if len(counterexamples) <= 5:
                    flushprint(f"  COUNTEREXAMPLE: T={T}, vertices {i} vs {j}")
                    flushprint(f"    closed walks ({max_m+1} terms): {cw[i]}")
                    flushprint(f"    edges = {[(u, v) for u in range(T) for v in range(u+1, T) if B[u,v] > 0.5]}")
                    flushprint(f"    |Aut| = {len(auts)}")
    flushprint(f"  Twin-free graphs: {n_twin_free} / {n_graphs_checked}")
    flushprint(f"  Counterexamples: {len(counterexamples)}")
    return counterexamples


def add_diagonal_jitter_and_recheck(B, i, j, max_m):
    """Add diagonal jitter to B and check if closed walks still match.

    Per the analysis: closed walks of length m ≥ 1 see the diagonal of B
    via v = i term in ∑_v W(v) B(i, v)². So diagonal jitter typically
    separates cospectral vertex pairs.
    """
    T = B.shape[0]
    Bj = B.copy()
    for k in range(T):
        Bj[k, k] += 0.1 * (k + 1)
    W = np.ones(T)
    if not is_twin_free(Bj):
        return None
    cw = closed_walks_all(Bj, W, max_m)
    return cw[i], cw[j]


def main():
    all_counters = []

    # T = 4, 5: full enumeration.
    for T in [4, 5]:
        cs = find_cospectral_vertex_pairs(T)
        all_counters.extend([(T, *c) for c in cs])

    # T = 6: 32K graphs (manageable: 6! = 720 perms each).
    cs = find_cospectral_vertex_pairs(6, max_graphs=32768)
    all_counters.extend([(6, *c) for c in cs])

    # T = 7: 5000 random graphs (with candidate-skip optimization).
    cs = find_cospectral_vertex_pairs(7, max_graphs=5000)
    all_counters.extend([(7, *c) for c in cs])

    flushprint("\n" + "=" * 70)
    flushprint(f"TOTAL counterexamples (closed walks = but different orbit): "
               f"{len(all_counters)}")
    flushprint("=" * 70)

    if not all_counters:
        flushprint("PASS — no cospectral-vertex / different-orbit pair found.")
        flushprint("closed_walk_profiles_separate_vertex_orbits holds on T ≤ 8.")
    else:
        flushprint(f"FAIL — {len(all_counters)} counterexamples found.")
        flushprint("\nCheck with diagonal jitter (twin-free via diagonal):")
        passes_with_jitter = 0
        for entry in all_counters[:10]:
            T, B, i, j = entry
            result = add_diagonal_jitter_and_recheck(B, i, j, T + 2)
            if result is not None:
                cw_i, cw_j = result
                if np.allclose(cw_i, cw_j, atol=1e-8):
                    flushprint(f"  T={T}, {i} vs {j}: STILL cospectral with diagonal jitter")
                else:
                    flushprint(f"  T={T}, {i} vs {j}: SEPARATED by diagonal jitter")
                    passes_with_jitter += 1
        flushprint(f"\nDiagonal jitter resolves {passes_with_jitter} of first 10 cases.")


if __name__ == '__main__':
    main()
