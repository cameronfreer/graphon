#!/usr/bin/env python3
"""
Focused falsification for closed_walk_profiles_separate_vertex_orbits
on WEIGHTED twin-free symmetric matrices with UNEQUAL POSITIVE weights.

Per user 2026-05-16 directive: prior empirical evidence was for simple
graphs (W = 1, 0-1 B) or random uniform W. #77 is stated for general
weighted setting. This script targets adversarial weighted cases.

Test corpus:
- Random twin-free symmetric B with entries in [-2, 2] and W ∈ [0.1, 5.0].
- Diagonal-rescaled cycle adjacencies (component sizes detected by edge weights).
- W-perturbed regular graphs (vertex-transitive base + W breaking transitivity).
- Block-diagonal B with varying block weights.

Usage: python3 scripts/closed_walk_weighted_search.py
"""

import sys
import numpy as np
from itertools import permutations


def flushprint(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


def is_twin_free(B, tol=1e-9):
    T = B.shape[0]
    for i in range(T):
        for j in range(i + 1, T):
            if np.allclose(B[i], B[j], atol=tol):
                return False
    return True


def closed_walks_all(B, W, max_m):
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
    T = len(W)
    if T > 8:
        return None  # too large
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


def make_weighted_random(T, rng, b_scale=2.0, w_low=0.1, w_high=5.0):
    """Random twin-free B + UNEQUAL W with wide value range."""
    B = rng.uniform(-b_scale, b_scale, (T, T))
    B = (B + B.T) / 2
    for k in range(T):
        B[k, k] += 0.3 * (k + 1)  # diagonal jitter
    W = rng.uniform(w_low, w_high, T)
    return B, W


def make_w_perturbed_cycle(n, rng):
    """C_n with non-uniform W to break vertex transitivity."""
    T = n
    B = np.zeros((T, T))
    for i in range(n):
        j = (i + 1) % n
        B[i, j] = 1.0
        B[j, i] = 1.0
    W = rng.uniform(0.5, 2.0, T)
    return B, W


def make_w_perturbed_complete(n, rng):
    """K_n with non-uniform W."""
    T = n
    B = np.ones((T, T)) - np.eye(T)
    W = rng.uniform(0.5, 2.0, T)
    return B, W


def make_w_perturbed_petersen(rng):
    """Petersen graph (10 vertices, 3-regular) with non-uniform W."""
    T = 10
    # Petersen as Kneser K(5,2): vertices = 2-subsets of {0,..,4}, adj iff disjoint.
    edges = [(0, 6), (0, 7), (0, 5), (1, 8), (1, 9), (1, 5), (2, 7), (2, 9), (2, 5),
             (3, 8), (3, 6), (3, 5),  # standard Petersen edges
             (0, 1), (1, 2), (2, 3), (3, 4), (4, 0),  # outer 5-cycle
             (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]  # inner star pentagon
    B = np.zeros((T, T))
    for u, v in edges:
        B[u, v] = 1.0
        B[v, u] = 1.0
    W = rng.uniform(0.5, 2.0, T)
    return B, W


def make_block_diagonal_weighted(sizes, rng):
    """Block-diagonal B with each block being a complete graph; varying W."""
    T = sum(sizes)
    B = np.zeros((T, T))
    offset = 0
    for n in sizes:
        for i in range(n):
            for j in range(i + 1, n):
                B[offset + i, offset + j] = rng.uniform(0.5, 1.5)
                B[offset + j, offset + i] = B[offset + i, offset + j]
        offset += n
    W = rng.uniform(0.5, 2.0, T)
    return B, W


def check(label, B, W, max_m=None, vertex_transitive_base=False):
    T = B.shape[0]
    if max_m is None:
        max_m = T + 3
    flushprint(f"\n=== {label} (T = {T}) ===")
    if not is_twin_free(B):
        flushprint("  NOT twin-free; skipping.")
        return 0
    cw = closed_walks_all(B, W, max_m)
    auts = compute_aut_group(B, W)
    if auts is None:
        flushprint("  T > 8; aut enumeration skipped, marking all pairs distinct orbits.")
        auts = [tuple(range(T))]
    flushprint(f"  |Aut| = {len(auts)}")
    counter = 0
    for i in range(T):
        for j in range(i + 1, T):
            # Compare walks of length 3..max_m (matches Lean bridge requirement).
            if np.allclose(cw[i][3:], cw[j][3:], atol=1e-8):
                if not in_same_orbit(i, j, auts):
                    counter += 1
                    if counter <= 5:
                        flushprint(f"  COUNTEREXAMPLE: {i} vs {j} cospectral, different orbits")
                        flushprint(f"    CW[3:] = {cw[i][3:]}")
    if counter == 0:
        flushprint("  PASS — no cospectral non-orbit pairs.")
    return counter


def main():
    rng = np.random.default_rng(2026)
    total = 0

    flushprint("=== RANDOM WEIGHTED TWIN-FREE ===")
    for T in [3, 4, 5, 6, 7, 8]:
        for trial in range(5):
            B, W = make_weighted_random(T, rng)
            total += check(f"random T={T} trial={trial}", B, W)

    flushprint("\n=== W-PERTURBED CYCLES (breaks vertex-transitivity) ===")
    for n in [3, 4, 5, 6, 7, 8]:
        for trial in range(3):
            B, W = make_w_perturbed_cycle(n, rng)
            # Cycle base graph; W-perturbation may make rows distinct.
            total += check(f"C_{n} W-perturbed trial={trial}", B, W)

    flushprint("\n=== W-PERTURBED COMPLETE GRAPHS ===")
    for n in [3, 4, 5, 6]:
        for trial in range(3):
            B, W = make_w_perturbed_complete(n, rng)
            total += check(f"K_{n} W-perturbed trial={trial}", B, W)

    flushprint("\n=== BLOCK-DIAGONAL WEIGHTED ===")
    for sizes in [[3, 3], [2, 4], [3, 4], [2, 2, 2], [3, 3, 3]]:
        for trial in range(3):
            B, W = make_block_diagonal_weighted(sizes, rng)
            label = "_".join(map(str, sizes))
            total += check(f"blocks_{label} trial={trial}", B, W)

    flushprint("\n=== W-PERTURBED PETERSEN ===")
    for trial in range(3):
        B, W = make_w_perturbed_petersen(rng)
        total += check(f"Petersen W-perturbed trial={trial}", B, W,
                       vertex_transitive_base=True)

    flushprint("\n" + "=" * 70)
    flushprint(f"TOTAL counterexamples: {total}")
    flushprint("=" * 70)
    if total == 0:
        flushprint("PASS — closed_walk_profiles_separate holds on weighted corpus.")
    else:
        flushprint("FAIL — counterexamples found; #77 needs refinement.")


if __name__ == '__main__':
    main()
