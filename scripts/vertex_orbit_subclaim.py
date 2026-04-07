#!/usr/bin/env python3
"""
Computational validation gate for subclaims (L) and (R) of the constructive
route to `pairOrbitRel_of_pairProfile_eq`.

Subclaim (L) — Left vertex orbit determination via (star0, tri0):
  For twin-free B with positive W, if two vertices i1, i2 satisfy
  star0Eval(i1) = star0Eval(i2) AND tri0Eval(i1) = tri0Eval(i2),
  then i1 and i2 are in the same vertex orbit under Aut(B, W).

Subclaim (R) — Right vertex orbit determination via (star1, tri1):
  Mirror of (L), using (star1Eval, tri1Eval) as a function of the right vertex.

Both subclaims must pass on all test cases before we sink Lean effort into
proving them. If either fails, the 5-motif constructive route needs
reformulation and the Lovász TR-2004-82 pivot becomes the fallback.

star0Eval(i,j) = sum_m W(m) * B(i,m)          (function of i only)
tri0Eval(i,j)  = sum_{m1,m2} W(m1)*W(m2)*B(i,m1)*B(i,m2)*B(m1,m2)  (function of i only)
star1Eval(i,j) = sum_m W(m) * B(j,m)          (function of j only)
tri1Eval(i,j)  = sum_{m1,m2} W(m1)*W(m2)*B(j,m1)*B(j,m2)*B(m1,m2)  (function of j only)
"""

import numpy as np
import sys

sys.path.insert(0, 'scripts')
from adjacency_span import compute_automorphisms


def is_twin_free(B, W, T):
    """Twin-free: no two distinct vertices have the same row (as functions Fin T -> ℝ)."""
    for a in range(T):
        for b in range(a + 1, T):
            if np.allclose(B[a], B[b]):
                return False
    return True


def star0(B, W, T, i):
    """∑_m W(m) * B(i,m) — function of i only."""
    return sum(W[m] * B[i][m] for m in range(T))


def tri0(B, W, T, i):
    """∑_{m1,m2} W(m1)*W(m2)*B(i,m1)*B(i,m2)*B(m1,m2) — function of i only."""
    return sum(
        W[m1] * W[m2] * B[i][m1] * B[i][m2] * B[m1][m2]
        for m1 in range(T)
        for m2 in range(T)
    )


def vertex_orbit_map(auts, T):
    """Return a map vertex -> canonical orbit representative (smallest in orbit)."""
    rep = list(range(T))
    for v in range(T):
        orbit = {perm[v] for perm in auts}
        rep[v] = min(orbit)
    return rep


def test_left_subclaim(T, B, W, label):
    """Test subclaim (L): (star0, tri0) equal => same left vertex orbit."""
    if not is_twin_free(B, W, T):
        return None, "skip (not twin-free)"
    auts = compute_automorphisms(B, W)
    orbit_rep = vertex_orbit_map(auts, T)
    failures = []
    for i1 in range(T):
        for i2 in range(i1 + 1, T):
            if abs(star0(B, W, T, i1) - star0(B, W, T, i2)) > 1e-9:
                continue
            if abs(tri0(B, W, T, i1) - tri0(B, W, T, i2)) > 1e-9:
                continue
            # (star0, tri0) matches — check if same vertex orbit
            if orbit_rep[i1] != orbit_rep[i2]:
                failures.append((i1, i2))
    return failures, f"|Aut|={len(auts)}, {len(failures)} failures"


def test_right_subclaim(T, B, W, label):
    """Test subclaim (R): (star1, tri1) equal => same right vertex orbit.

    Since star1(i,j) depends on j only, and star1Eval B W i j = star0Eval B W j,
    and symmetrically for tri1, the right subclaim is mathematically identical
    to (L) applied to the transposed evaluation. So we test it the same way,
    but check the right side.
    """
    # Since B is symmetric, star1 and tri1 as functions of j are identical to
    # star0 and tri0 as functions of i. So (R) is mathematically identical to (L).
    # We still run the test independently to confirm the symmetry holds.
    if not is_twin_free(B, W, T):
        return None, "skip (not twin-free)"
    auts = compute_automorphisms(B, W)
    orbit_rep = vertex_orbit_map(auts, T)
    failures = []
    for j1 in range(T):
        for j2 in range(j1 + 1, T):
            # star1Eval(·, j) = sum_m W(m) B(j, m) = star0 of j
            # tri1Eval(·, j) = tri0 of j
            if abs(star0(B, W, T, j1) - star0(B, W, T, j2)) > 1e-9:
                continue
            if abs(tri0(B, W, T, j1) - tri0(B, W, T, j2)) > 1e-9:
                continue
            if orbit_rep[j1] != orbit_rep[j2]:
                failures.append((j1, j2))
    return failures, f"|Aut|={len(auts)}, {len(failures)} failures"


def run_tests():
    configs = []

    # Random twin-free matrices at various sizes
    rng = np.random.RandomState(42)
    for trial in range(15):
        for T in [3, 4, 5, 6, 7, 8]:
            A = rng.uniform(0.1, 0.9, (T, T))
            B = (A + A.T) / 2
            W = rng.uniform(0.1, 0.9, T)
            W /= W.sum()
            configs.append((T, B, W, f"rand-T{T}-{trial}"))

    # Structured twin-free cases with nontrivial automorphisms
    # T=4 Z/2 x Z/2 with distinct diagonals (twin-free)
    B_z2 = np.array(
        [
            [0.3, 0.7, 0.5, 0.5],
            [0.7, 0.4, 0.5, 0.5],
            [0.5, 0.5, 0.3, 0.7],
            [0.5, 0.5, 0.7, 0.4],
        ]
    )
    configs.append((4, B_z2, np.ones(4) / 4, "Z2xZ2-twinfree"))

    # T=4 S3+1 twin-free (S3 on {0,1,2} + distinct singleton)
    B_s3 = np.array(
        [
            [0.2, 0.8, 0.8, 0.5],
            [0.8, 0.2, 0.8, 0.5],
            [0.8, 0.8, 0.2, 0.5],
            [0.5, 0.5, 0.5, 0.3],
        ]
    )
    configs.append((4, B_s3, np.ones(4) / 4, "S3+1"))

    # T=6 two S3 blocks + 0 singletons (pure)
    B_2s3 = np.full((6, 6), 0.5)
    for i in range(3):
        for j in range(3):
            B_2s3[i, j] = 0.8 if i != j else 0.2
    for i in range(3, 6):
        for j in range(3, 6):
            B_2s3[i, j] = 0.7 if i != j else 0.3
    configs.append((6, B_2s3, np.ones(6) / 6, "S3+S3"))

    # T=8 two S3 blocks + 2 distinct singletons
    B_2s3_2 = np.full((8, 8), 0.5)
    for i in range(3):
        for j in range(3):
            B_2s3_2[i, j] = 0.8 if i != j else 0.2
    for i in range(3, 6):
        for j in range(3, 6):
            B_2s3_2[i, j] = 0.7 if i != j else 0.3
    B_2s3_2[6, 6] = 0.4
    B_2s3_2[7, 7] = 0.45
    configs.append((8, B_2s3_2, np.ones(8) / 8, "2xS3+2sing"))

    # T=10 two S5 blocks
    B_2s5 = np.full((10, 10), 0.5)
    for i in range(5):
        for j in range(5):
            B_2s5[i, j] = 0.8 if i != j else 0.2
    for i in range(5, 10):
        for j in range(5, 10):
            B_2s5[i, j] = 0.7 if i != j else 0.3
    configs.append((10, B_2s5, np.ones(10) / 10, "2xS5"))

    print("=== Subclaim (L): (star0, tri0) => left vertex orbit ===")
    any_fail_L = False
    for T, B, W, label in configs:
        failures, info = test_left_subclaim(T, B, W, label)
        if failures is None:
            continue  # skipped (not twin-free)
        status = "FAIL" if failures else "OK  "
        if failures or label in ("Z2xZ2-twinfree", "S3+1", "S3+S3", "2xS3+2sing", "2xS5"):
            print(f"  [{status}] {label:20s} T={T} {info}")
        if failures:
            any_fail_L = True
            for i1, i2 in failures[:3]:
                print(f"    counterexample: vertices {i1}, {i2}")
                print(
                    f"      star0={star0(B,W,T,i1):.6f}={star0(B,W,T,i2):.6f}, "
                    f"tri0={tri0(B,W,T,i1):.6f}={tri0(B,W,T,i2):.6f}"
                )

    print()
    print("=== Subclaim (R): (star1, tri1) => right vertex orbit ===")
    any_fail_R = False
    for T, B, W, label in configs:
        failures, info = test_right_subclaim(T, B, W, label)
        if failures is None:
            continue
        status = "FAIL" if failures else "OK  "
        if failures or label in ("Z2xZ2-twinfree", "S3+1", "S3+S3", "2xS3+2sing", "2xS5"):
            print(f"  [{status}] {label:20s} T={T} {info}")
        if failures:
            any_fail_R = True

    print()
    print("=" * 60)
    if any_fail_L:
        print("SUBCLAIM (L) FAILS — constructive route needs reformulation")
    else:
        print("Subclaim (L) holds on all tested twin-free cases")
    if any_fail_R:
        print("SUBCLAIM (R) FAILS — constructive route needs reformulation")
    else:
        print("Subclaim (R) holds on all tested twin-free cases")
    print("=" * 60)

    return any_fail_L or any_fail_R


if __name__ == "__main__":
    sys.exit(1 if run_tests() else 0)
