#!/usr/bin/env python3
"""
Focused validation for the orbit-upgrade step of #77 spectral closing.

Per user 2026-05-18 directive: before committing to a Lean proof of
`same_diag_powers_imp_vertex_orbit`, validate that "equal diagonal
moments of S = D^{1/2} B D^{1/2} + twin-free B + W > 0" forces
orbit relation.

Risk: classical cospectral vertex constructions exist for non-twin-free
graphs. The conjecture is that twin-free + positivity is enough.

Test plan:
1. Constructive cospectral-vertex families (Schwenk-style, tree pins).
2. Weighted variants (uniform W, integer W, perturbed W).
3. General symmetric real B (not just 0/1).
4. If a twin-free counterexample exists, #77 needs revision.

Two vertices i, j are SPECTRALLY EQUIVALENT (cospectral) iff
   (S^m)[i, i] = (S^m)[j, j] for all m,
where S[a, b] = sqrt(W[a]) * B[a, b] * sqrt(W[b]).

Equivalently (by Cayley-Hamilton): for all m = 0..T-1.

Usage: python3 scripts/spectral_orbit_validation.py
"""

import sys
import numpy as np
from itertools import permutations


def flushprint(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


def make_S(B, W):
    """S = D^{1/2} B D^{1/2}."""
    sqrtW = np.sqrt(W)
    return np.outer(sqrtW, sqrtW) * B


def diag_powers(S, max_m):
    """Compute (S^m)[i, i] for m = 0..max_m and each vertex i."""
    T = S.shape[0]
    out = np.zeros((T, max_m + 1))
    out[:, 0] = 1.0
    M = np.eye(T)
    for m in range(1, max_m + 1):
        M = M @ S
        out[:, m] = np.diag(M)
    return out


def is_twin_free(B, tol=1e-9):
    T = B.shape[0]
    for i in range(T):
        for j in range(i + 1, T):
            if np.allclose(B[i], B[j], atol=tol):
                return False
    return True


def compute_aut(B, W, tol=1e-9, max_T=9):
    T = len(W)
    if T > max_T:
        return None
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


def check(label, B, W, vertex_transitive=False, max_m=None):
    T = B.shape[0]
    if max_m is None:
        max_m = T + 2
    flushprint(f"\n=== {label} (T = {T}) ===")
    if not is_twin_free(B):
        flushprint("  NOT twin-free; skipping.")
        return 0
    S = make_S(B, W)
    moments = diag_powers(S, max_m)
    if vertex_transitive:
        flushprint("  (Vertex-transitive: single orbit)")
        return 0
    auts = compute_aut(B, W)
    if auts is None:
        flushprint(f"  T > 9, skipping aut enumeration.")
        return 0
    counter = 0
    for i in range(T):
        for j in range(i + 1, T):
            # Spectral measure equivalence: equal diagonal moments for all m.
            if np.allclose(moments[i], moments[j], atol=1e-8):
                if not in_same_orbit(i, j, auts):
                    counter += 1
                    flushprint(f"  *** COUNTEREXAMPLE: vertices {i}, {j} spectrally equivalent, different orbits")
                    flushprint(f"      S-diag moments[i] = {moments[i][:6]}")
                    flushprint(f"      S-diag moments[j] = {moments[j][:6]}")
                    flushprint(f"      |Aut| = {len(auts)}")
    if counter == 0:
        flushprint("  PASS — no cospectral non-orbit pairs.")
    return counter


def make_schwenk_pinned_tree():
    """Two trees with cospectral non-orbit pins:
    T1: 0-1-2-3 (path) with leaf 4 at vertex 1.
    T2: 0-1-2-3 (path) with leaf 4 at vertex 2.
    Glue at common vertex 5.

    Actually: build a tree where two pendant attachments yield
    cospectral non-orbit pendants. Standard Schwenk construction.
    """
    # Tree on 8 vertices: pin two cospectral subtrees at a central vertex.
    T = 8
    B = np.zeros((T, T))
    # Subtree A: 0-1-2 (path), with 3 attached to 1.
    # Subtree B: 4-5-6 (path), with 7 attached to 6.
    # Glue at vertex 2 = 4 (renumber).
    # Edges: 0-1, 1-2, 1-3, 4-5, 5-6, 6-7, 2-4 (glue), but let's just enumerate.
    edges = [(0, 1), (1, 2), (1, 3), (4, 5), (5, 6), (6, 7), (2, 4)]
    for u, v in edges:
        B[u, v] = 1.0
        B[v, u] = 1.0
    W = np.ones(T)
    return B, W


def make_double_pin_tree():
    """Tree with two cospectral non-orbit pendant vertices."""
    # 9-vertex example. Center 0, two "arms" of length 2 each (1-2-3 and 4-5-6),
    # plus two leaves attached differently to break symmetry.
    T = 9
    B = np.zeros((T, T))
    edges = [(0, 1), (1, 2), (2, 3),  # arm 1
             (0, 4), (4, 5), (5, 6),  # arm 2
             (3, 7),  # leaf on arm 1
             (4, 8)]  # leaf on arm 2 (closer to center, breaks symmetry)
    for u, v in edges:
        B[u, v] = 1.0
        B[v, u] = 1.0
    W = np.ones(T)
    return B, W


def make_weighted_perturbation(T, rng, sym=True, b_range=(-2, 2), w_range=(0.1, 5)):
    """Random symmetric twin-free B with positive W."""
    B = rng.uniform(b_range[0], b_range[1], (T, T))
    if sym:
        B = (B + B.T) / 2
    for k in range(T):
        B[k, k] += 0.3 * (k + 1)
    W = rng.uniform(w_range[0], w_range[1], T)
    return B, W


def main():
    rng = np.random.default_rng(2026)
    total = 0

    flushprint("=" * 70)
    flushprint("Validation: spectral measure equality ⟹ orbit (under twin-free + W > 0)")
    flushprint("=" * 70)

    # Constructive: Schwenk-style pinned tree.
    flushprint("\n--- Constructive cospectral attempts ---")
    total += check("Schwenk-style pinned tree (T=8)", *make_schwenk_pinned_tree())
    total += check("Double-pin tree (T=9)", *make_double_pin_tree())

    # Random weighted symmetric B (general, not just 0/1).
    flushprint("\n--- Random general weighted twin-free ---")
    for T in [3, 4, 5, 6, 7, 8]:
        for trial in range(5):
            B, W = make_weighted_perturbation(T, rng)
            total += check(f"random T={T} trial={trial}", B, W)

    # Random with integer W.
    flushprint("\n--- Integer W ---")
    for T in [4, 5, 6, 7]:
        for trial in range(3):
            B, _ = make_weighted_perturbation(T, rng)
            W = rng.integers(1, 4, T).astype(float)
            if is_twin_free(B):
                total += check(f"intW T={T} trial={trial}", B, W)

    # Uniform W = 1 with random symmetric B.
    flushprint("\n--- Uniform W ---")
    for T in [4, 5, 6, 7]:
        for trial in range(3):
            B, _ = make_weighted_perturbation(T, rng)
            W = np.ones(T)
            if is_twin_free(B):
                total += check(f"uniform W T={T} trial={trial}", B, W)

    flushprint("\n" + "=" * 70)
    flushprint(f"TOTAL counterexamples: {total}")
    flushprint("=" * 70)
    if total == 0:
        flushprint("PASS — orbit-upgrade conjecture survives this validation pass.")
        flushprint("Constructive Schwenk-style attempts did not produce a twin-free")
        flushprint("counterexample. Empirical support for #77 strengthened.")
    else:
        flushprint(f"FAIL — {total} counterexample(s) found.")
        flushprint("The orbit-upgrade step does NOT follow from twin-free + W > 0 alone.")
        flushprint("#77 needs revision; the conjecture should use stronger data")
        flushprint("(e.g., full rooted profiles instead of just closed walks).")


if __name__ == '__main__':
    main()
