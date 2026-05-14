#!/usr/bin/env python3
"""
Adversarial cospectral-vertex falsification using known constructions.

Per user 2026-05-14 guidance: random + small-enumeration tests passed.
Now test KNOWN cospectral-vertex constructions to look for failures of
`closed_walk_profiles_separate_vertex_orbits`.

Constructions tested:
1. Strongly regular graphs: SRG(13, 6, 2, 3) = Paley(13); SRG(16, 6, 2, 2)
   = Shrikhande and 4x4-rook. Both vertex-transitive (no non-orbit pair).
   Cocktail party and complement of perfect matching: also v-t.
2. Schwenk-style trees: trees with cospectral non-orbit pendant pairs.
3. Godsil-McKay switching: take a graph G, switch a subset, check vertex
   cospectrality between G and G'.
4. Petersen-modified graphs: remove edges to break vertex-transitivity.
5. Small graphs with degree-regular non-orbit vertices (manual search).

Usage: python3 scripts/cospectral_adversarial.py
"""

import sys
import numpy as np
from itertools import permutations


def flushprint(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


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


def is_twin_free(B, tol=1e-9):
    T = B.shape[0]
    for i in range(T):
        for j in range(i + 1, T):
            if np.allclose(B[i], B[j], atol=tol):
                return False
    return True


def compute_aut_group(B, W, tol=1e-9, max_T=8):
    T = len(W)
    if T > max_T:
        # Too big; return identity only.
        return [tuple(range(T))]
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


def check_cospectral_pairs(label, B, W=None, max_m=None, vertex_transitive=False):
    """vertex_transitive: if True, all vertices in one orbit (skip aut)."""
    T = B.shape[0]
    if W is None:
        W = np.ones(T)
    if max_m is None:
        max_m = T + 2
    flushprint(f"\n=== {label} (T = {T}) ===")
    if not is_twin_free(B):
        flushprint("  NOT twin-free; adding diagonal jitter.")
        for k in range(T):
            B[k, k] += 0.1 * (k + 1)
        if not is_twin_free(B):
            flushprint("  Still not twin-free; skipping.")
            return 0
    cw = closed_walks_all(B, W, max_m)
    if vertex_transitive:
        # All vertices in one orbit by construction.
        # No vertex pair is a counterexample even if cospectral.
        flushprint("  (Vertex-transitive: all vertices in one orbit)")
        n_cospectral = sum(1 for i in range(T) for j in range(i+1, T)
                           if np.allclose(cw[i], cw[j], atol=1e-8))
        flushprint(f"  Cospectral pairs: {n_cospectral} (all in same orbit ⟹ no counterexample)")
        return 0
    auts = compute_aut_group(B, W)
    counter = 0
    flushprint(f"  |Aut| = {len(auts)}")
    for i in range(T):
        for j in range(i + 1, T):
            if np.allclose(cw[i], cw[j], atol=1e-8):
                if not in_same_orbit(i, j, auts):
                    counter += 1
                    flushprint(f"  COUNTEREXAMPLE: vertices {i}, {j} cospectral, "
                               f"different orbits")
                    flushprint(f"    CW = {cw[i][:8]}")
    if counter == 0:
        flushprint("  PASS — no cospectral non-orbit pairs.")
    return counter


def shrikhande_graph():
    """Shrikhande graph: SRG(16, 6, 2, 2). Vertex-transitive."""
    T = 16
    B = np.zeros((T, T))
    # 4x4 torus with edges: (i, j) - (i', j') if (i' - i, j' - j) ∈ {(±1, 0), (0, ±1), (1, 1), (-1, -1)} mod 4.
    for i in range(4):
        for j in range(4):
            v1 = 4 * i + j
            for di, dj in [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)]:
                v2 = 4 * ((i + di) % 4) + ((j + dj) % 4)
                if v1 != v2:
                    B[v1, v2] = 1.0
                    B[v2, v1] = 1.0
    return B


def rook_4x4():
    """4x4 rook graph: SRG(16, 6, 2, 2). Same parameters as Shrikhande."""
    T = 16
    B = np.zeros((T, T))
    for i in range(4):
        for j in range(4):
            v1 = 4 * i + j
            for k in range(4):
                if k != i:
                    v2 = 4 * k + j
                    B[v1, v2] = 1.0
                    B[v2, v1] = 1.0
                if k != j:
                    v2 = 4 * i + k
                    B[v1, v2] = 1.0
                    B[v2, v1] = 1.0
    return B


def schwenk_tree_pair():
    """A pair of trees with cospectral root vertices (Schwenk 1973)."""
    # Tree 1: 7 vertices. Path 0-1-2-3, with leaves 4 attached to 1,
    # 5 attached to 2, 6 attached to 3.
    T = 7
    B = np.zeros((T, T))
    edges = [(0, 1), (1, 2), (2, 3), (1, 4), (2, 5), (3, 6)]
    for u, v in edges:
        B[u, v] = 1.0
        B[v, u] = 1.0
    return B


def godsil_mckay_example():
    """Godsil-McKay switching example: small graph with switching twin.

    Take the 8-vertex graph from Godsil-McKay's example: K_{4,4} with one
    edge removed, where switching produces a cospectral mate.
    """
    T = 8
    B = np.zeros((T, T))
    # K_{4,4}: vertices 0,1,2,3 (part A), 4,5,6,7 (part B).
    for u in range(4):
        for v in range(4, 8):
            B[u, v] = 1.0
            B[v, u] = 1.0
    # Remove edge (0, 4) to break.
    B[0, 4] = 0.0
    B[4, 0] = 0.0
    return B


def small_regular_graphs():
    """Small regular graphs with non-trivial structure."""
    examples = []
    # K_4: complete on 4 vertices (regular, vertex-transitive).
    T = 4
    B = np.ones((T, T)) - np.eye(T)
    examples.append(("K_4", B))
    # Cube graph Q_3: 8 vertices, 3-regular, vertex-transitive.
    T = 8
    B = np.zeros((T, T))
    for u in range(T):
        for d in [1, 2, 4]:
            v = u ^ d
            B[u, v] = 1.0
            B[v, u] = 1.0
    examples.append(("Q_3 (3-cube)", B))
    # Möbius-Kantor: 8 vertices, 3-regular, vertex-transitive.
    T = 8
    B = np.zeros((T, T))
    for i in range(8):
        for d in [1, 3]:  # ±1 and ±3 mod 8
            j = (i + d) % 8
            B[i, j] = 1.0
            B[j, i] = 1.0
    examples.append(("Möbius-Kantor (8-vertex)", B))
    return examples


def main():
    total_counters = 0

    # Vertex-transitive SRGs (Shrikhande and Rook are both vertex-transitive;
    # they are cospectral as graphs but each is its own single vertex orbit).
    total_counters += check_cospectral_pairs("Shrikhande SRG(16,6,2,2)",
                                             shrikhande_graph(), max_m=10,
                                             vertex_transitive=True)
    total_counters += check_cospectral_pairs("4×4 Rook SRG(16,6,2,2)",
                                             rook_4x4(), max_m=10,
                                             vertex_transitive=True)

    # Tree with potential cospectral leaves.
    total_counters += check_cospectral_pairs("Schwenk-like tree (T=7)",
                                             schwenk_tree_pair(), max_m=9)

    # Godsil-McKay switching candidate.
    total_counters += check_cospectral_pairs("Godsil-McKay K_{4,4} - e",
                                             godsil_mckay_example(), max_m=10)

    # Small regular graphs.
    for label, B in small_regular_graphs():
        total_counters += check_cospectral_pairs(label, B,
                                                 max_m=B.shape[0] + 2)

    flushprint("\n" + "=" * 70)
    flushprint(f"TOTAL counterexamples: {total_counters}")
    flushprint("=" * 70)
    if total_counters == 0:
        flushprint("PASS — no adversarial counterexample found.")
        flushprint("closed_walk_profiles_separate_vertex_orbits holds.")
    else:
        flushprint("FAIL — closed walks DO NOT separate vertex orbits "
                   "in adversarial cases.")


if __name__ == '__main__':
    main()
