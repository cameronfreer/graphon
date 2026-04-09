#!/usr/bin/env python3
"""
Test whether adding motifs beyond (star0, tri0) makes subclaim (L) hold with
a *richer* invariant set. Goal: find the minimal extension that makes (L)
provable by moment-type reasoning.

Motifs tested:
- star0(i) = ∑_m W(m) B(i,m)                                          — linear
- tri0(i)  = ∑_{m₁,m₂} W(m₁) W(m₂) B(i,m₁) B(i,m₂) B(m₁,m₂)            — quadratic
- Lr0(i)   = ∑_m W(m) B(i,m) * star0(m)                               — "degree-weighted" linear
- star0²(i) = (∑_m W(m) B(i,m))²                                       — product of star0 with itself
- tri0²(i) = tri0(i)²                                                  — redundant but listed
- quad0(i) = ∑_{m₁,m₂} W(m₁) W(m₂) B(i,m₁) B(m₁,m₂)²                  — different quadratic

Observation: for twin-free B, the question is whether (star0, tri0) alone
suffice, or whether we need a richer invariant. If (star0, tri0, Lr0) fails
on a test case but (star0, tri0, Lr0, quad0) passes, we have a candidate
for a 4-motif refinement.
"""

import numpy as np
import sys

sys.path.insert(0, 'scripts')
from adjacency_span import compute_automorphisms


def is_twin_free(B, W, T):
    for a in range(T):
        for b in range(a + 1, T):
            if np.allclose(B[a], B[b]):
                return False
    return True


def star0(B, W, T, i):
    return sum(W[m] * B[i][m] for m in range(T))


def tri0(B, W, T, i):
    return sum(
        W[m1] * W[m2] * B[i][m1] * B[i][m2] * B[m1][m2]
        for m1 in range(T)
        for m2 in range(T)
    )


def Lr0(B, W, T, i):
    """Left-adjoint of star0 at i: ∑_m W(m) B(i,m) star0(m)."""
    r = [star0(B, W, T, m) for m in range(T)]
    return sum(W[m] * B[i][m] * r[m] for m in range(T))


def quad0(B, W, T, i):
    """Alternate quadratic: ∑_m W(m) B(i,m) * (∑_a W(a) B(m,a)²)."""
    return sum(
        W[m] * B[i][m] * sum(W[a] * B[m][a] ** 2 for a in range(T))
        for m in range(T)
    )


def vertex_orbit_map(auts, T):
    rep = list(range(T))
    for v in range(T):
        orbit = {perm[v] for perm in auts}
        rep[v] = min(orbit)
    return rep


def test_invariant_set(T, B, W, label, invariants, name):
    """Check if the given invariant tuple separates non-orbit vertex pairs."""
    if not is_twin_free(B, W, T):
        return None
    auts = compute_automorphisms(B, W)
    orbit_rep = vertex_orbit_map(auts, T)
    failures = []
    for i1 in range(T):
        for i2 in range(i1 + 1, T):
            if orbit_rep[i1] == orbit_rep[i2]:
                continue  # same orbit, no need to separate
            # Different orbits: check if any invariant distinguishes
            sep = False
            for inv in invariants:
                if abs(inv(B, W, T, i1) - inv(B, W, T, i2)) > 1e-9:
                    sep = True
                    break
            if not sep:
                failures.append((i1, i2))
    return failures


def run():
    configs = []

    rng = np.random.RandomState(42)
    for trial in range(20):
        for T in [3, 4, 5, 6, 7, 8]:
            A = rng.uniform(0.1, 0.9, (T, T))
            B = (A + A.T) / 2
            W = rng.uniform(0.1, 0.9, T)
            W /= W.sum()
            configs.append((T, B, W, f"rand-T{T}-{trial}"))

    # Structured twin-free cases
    B_z2 = np.array(
        [
            [0.3, 0.7, 0.5, 0.5],
            [0.7, 0.4, 0.5, 0.5],
            [0.5, 0.5, 0.3, 0.7],
            [0.5, 0.5, 0.7, 0.4],
        ]
    )
    configs.append((4, B_z2, np.ones(4) / 4, "Z2xZ2-twinfree"))

    B_s3 = np.array(
        [
            [0.2, 0.8, 0.8, 0.5],
            [0.8, 0.2, 0.8, 0.5],
            [0.8, 0.8, 0.2, 0.5],
            [0.5, 0.5, 0.5, 0.3],
        ]
    )
    configs.append((4, B_s3, np.ones(4) / 4, "S3+1"))

    B_2s3 = np.full((6, 6), 0.5)
    for i in range(3):
        for j in range(3):
            B_2s3[i, j] = 0.8 if i != j else 0.2
    for i in range(3, 6):
        for j in range(3, 6):
            B_2s3[i, j] = 0.7 if i != j else 0.3
    configs.append((6, B_2s3, np.ones(6) / 6, "S3+S3"))

    B_2s5 = np.full((10, 10), 0.5)
    for i in range(5):
        for j in range(5):
            B_2s5[i, j] = 0.8 if i != j else 0.2
    for i in range(5, 10):
        for j in range(5, 10):
            B_2s5[i, j] = 0.7 if i != j else 0.3
    configs.append((10, B_2s5, np.ones(10) / 10, "2xS5"))

    invariant_sets = [
        ([star0], "star0 only"),
        ([star0, tri0], "star0 + tri0 (current L)"),
        ([star0, tri0, Lr0], "star0 + tri0 + Lr0"),
        ([star0, tri0, Lr0, quad0], "star0 + tri0 + Lr0 + quad0"),
    ]

    for inv_set, name in invariant_sets:
        print(f"\n=== {name} ===")
        total_failures = 0
        for T, B, W, label in configs:
            fails = test_invariant_set(T, B, W, label, inv_set, name)
            if fails is None:
                continue
            total_failures += len(fails)
            if fails:
                print(f"  [FAIL] {label:20s} T={T}: {len(fails)} unseparated pairs")
        if total_failures == 0:
            print(f"  [OK]  {name}: no counterexamples")
        else:
            print(f"  total failures across tested configs: {total_failures}")


if __name__ == "__main__":
    run()
