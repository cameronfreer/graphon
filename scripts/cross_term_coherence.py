#!/usr/bin/env python3
"""
Computational validation gate for subclaim (C) of the constructive route to
`pairOrbitRel_of_pairProfile_eq`.

Subclaim (C) — Cross-term coherence:
  For twin-free B with positive W, given two pairs (i1,j1), (i2,j2) such that:
    - i1 and i2 are in the same vertex orbit (exists σ_L with σ_L i1 = i2)
    - j1 and j2 are in the same vertex orbit (exists σ_R with σ_R j1 = j2)
    - pathEval B W i1 j1 = pathEval B W i2 j2
  then (i1,j1) and (i2,j2) are in the same pair orbit under Aut(B, W).

Equivalently (contrapositive test):
  If (i1,j1), (i2,j2) are NOT in the same pair orbit, but i1 ∼ i2 and j1 ∼ j2
  individually, then pathEval should distinguish them.

If there exists any twin-free case where a non-orbit pair has matching path
values AND individually orbit-related endpoints, subclaim (C) is false as
stated and the cross-term construction needs reformulation.

pathEval(i,j) = ∑_m W(m) * B(i,m) * B(m,j)
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


def path_eval(B, W, T, i, j):
    return sum(W[m] * B[i][m] * B[m][j] for m in range(T))


def build_vertex_orbits(auts, T):
    """Return list of sets: each set is a vertex orbit."""
    seen = set()
    orbits = []
    for v in range(T):
        if v in seen:
            continue
        orbit = {perm[v] for perm in auts}
        orbits.append(orbit)
        seen.update(orbit)
    return orbits


def vertex_orbit_of(v, orbits):
    for i, orbit in enumerate(orbits):
        if v in orbit:
            return i
    raise RuntimeError(f"vertex {v} not in any orbit")


def test_cross_term(T, B, W, label):
    """Find non-orbit pairs (p, q) where:
       - p.1 ~ q.1 (same vertex orbit)
       - p.2 ~ q.2 (same vertex orbit)
       - pathEval(p) = pathEval(q)

       If any exist, subclaim (C) is FALSE for this B,W.
    """
    if not is_twin_free(B, W, T):
        return None, "skip (not twin-free)"
    auts = compute_automorphisms(B, W)
    v_orbits = build_vertex_orbits(auts, T)

    # Enumerate all pair orbits by computing them
    pair_orbit_rep = {}
    for i in range(T):
        for j in range(T):
            if (i, j) in pair_orbit_rep:
                continue
            orbit = {(perm[i], perm[j]) for perm in auts}
            rep = min(orbit)
            for (a, b) in orbit:
                pair_orbit_rep[(a, b)] = rep

    failures = []
    for i1 in range(T):
        for j1 in range(T):
            for i2 in range(T):
                for j2 in range(T):
                    if (i1, j1) >= (i2, j2):
                        continue
                    # Skip if already in same pair orbit
                    if pair_orbit_rep[(i1, j1)] == pair_orbit_rep[(i2, j2)]:
                        continue
                    # Check if components are individually vertex-orbit-related
                    if vertex_orbit_of(i1, v_orbits) != vertex_orbit_of(i2, v_orbits):
                        continue
                    if vertex_orbit_of(j1, v_orbits) != vertex_orbit_of(j2, v_orbits):
                        continue
                    # Both endpoints vertex-orbit-related, but different pair orbits.
                    # Subclaim (C) needs pathEval to distinguish them.
                    p1 = path_eval(B, W, T, i1, j1)
                    p2 = path_eval(B, W, T, i2, j2)
                    if abs(p1 - p2) < 1e-9:
                        failures.append(((i1, j1), (i2, j2), p1, p2))
    return failures, f"|Aut|={len(auts)}, {len(failures)} failures"


def run_tests():
    configs = []

    rng = np.random.RandomState(42)
    for trial in range(15):
        for T in [3, 4, 5, 6, 7, 8]:
            A = rng.uniform(0.1, 0.9, (T, T))
            B = (A + A.T) / 2
            W = rng.uniform(0.1, 0.9, T)
            W /= W.sum()
            configs.append((T, B, W, f"rand-T{T}-{trial}"))

    # Structured twin-free cases with nontrivial automorphisms
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

    # T=6 two S3 blocks
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

    print("=== Subclaim (C): endpoints individually vertex-orbit-related + equal pathEval => pair orbit ===")
    any_fail = False
    for T, B, W, label in configs:
        failures, info = test_cross_term(T, B, W, label)
        if failures is None:
            continue
        status = "FAIL" if failures else "OK  "
        if failures or label in (
            "Z2xZ2-twinfree",
            "S3+1",
            "S3+S3",
            "2xS3+2sing",
            "2xS5",
        ):
            print(f"  [{status}] {label:20s} T={T} {info}")
        if failures:
            any_fail = True
            for (p, q, v1, v2) in failures[:3]:
                print(f"    counterexample: {p} vs {q}")
                print(f"      pathEval={v1:.6f}={v2:.6f}")

    print()
    print("=" * 60)
    if any_fail:
        print("SUBCLAIM (C) FAILS — constructive route needs reformulation")
    else:
        print("Subclaim (C) holds on all tested twin-free cases")
    print("=" * 60)

    return any_fail


if __name__ == "__main__":
    sys.exit(1 if run_tests() else 0)
