#!/usr/bin/env python3
"""
Closed-walk / rooted-cycle profile falsification.

Per user 2026-05-14 directive: after path-profile route failed,
test whether closed-walk (rooted-cycle) profiles separate vertex
orbits.

Closed walk of length m at root i:
  CW_m(i) := ∑_{v_1,...,v_{m-1}} W(v_1)...W(v_{m-1}) *
             B(i, v_1) B(v_1, v_2) ... B(v_{m-1}, i).

Equivalently the rooted m-cycle simpleEvalAt at root i.

Cycle-distinguishing for C_5 ⊔ C_6: CW_5(C_5 vertex) = 2, CW_5(C_6
vertex) = 0.

Usage: python3 scripts/closed_walk_search.py
"""

import sys
import numpy as np
from itertools import permutations, product as cartprod


def flushprint(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


def make_test_matrix(T, rng, trial_idx=0):
    B = rng.uniform(-1.0, 1.0, (T, T))
    B = (B + B.T) / 2
    for i in range(T):
        B[i, i] += 0.1 * (i + 1 + 0.01 * trial_idx)
    W = rng.uniform(0.5, 1.5, T)
    return B, W


def make_cycle_disjoint_union(sizes):
    T = sum(sizes)
    B = np.zeros((T, T))
    offset = 0
    for n in sizes:
        for i in range(n):
            j = (i + 1) % n
            B[offset + i, offset + j] = 1.0
            B[offset + j, offset + i] = 1.0
        offset += n
    return B, np.ones(T)


def compute_aut_group(B, W, tol=1e-9):
    """Brute-force aut enumeration. ONLY for small T (≤7)."""
    T = len(W)
    if T > 7:
        raise ValueError(f"T={T} too large for brute-force aut enumeration")
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


def cycle_disjoint_union_orbits(sizes):
    """Analytic orbit structure for disjoint union of cycles.

    Each component C_n is vertex-transitive: all n vertices form one orbit.
    Cross-component: vertices in C_n and C_m are in the same orbit iff
    component sizes are equal (then components can be swapped) — but
    since C_n and C_m have different sizes typically, the orbits are
    exactly the connected components (one orbit per cycle size class).

    Returns list of orbit reps (one vertex from each cycle component,
    deduplicated by size class).
    """
    orbits_by_size = {}
    offset = 0
    for n in sizes:
        if n not in orbits_by_size:
            orbits_by_size[n] = []
        orbits_by_size[n].append(offset)  # rep of this component
        offset += n
    # For each size class: all components of that size are in one orbit
    # (cycle automorphisms allow swapping any pair).
    # So orbit reps = one per size class.
    orbit_reps = []
    for n, reps in orbits_by_size.items():
        orbit_reps.append(reps[0])  # one rep per size class
    return orbit_reps


def closed_walk_profile(i, m, B, W):
    """Closed walk of length m at root i, via numpy matrix matmul.

    Define N[a, b] := W[b] * B[a, b]. Then:
      N^m[i, i] = W[i] * CW_m(i).
    So CW_m(i) = N^m[i, i] / W[i].

    For m = 0: trivially 1.
    For m = 1: B(i, i) (self-loop), 0 for simple graphs without diagonal.
    """
    if m == 0:
        return 1.0
    N = B * W[np.newaxis, :]  # broadcast W along columns.
    Nm = np.linalg.matrix_power(N, m)
    return Nm[i, i] / W[i]


def closed_walks_separate(i, j, B, W, max_m=7, tol=1e-8):
    """Check if some closed walk profile of length ≤ max_m separates i and j."""
    for m in range(2, max_m + 1):
        c_i = closed_walk_profile(i, m, B, W)
        c_j = closed_walk_profile(j, m, B, W)
        if not np.isclose(c_i, c_j, atol=tol, rtol=1e-7):
            return m, c_i, c_j
    return None


def run_family(label, B, W, orbit_reps, max_m=7):
    """Run closed-walk pair separation for given orbit reps."""
    T = len(W)
    flushprint(f"\n[{label}] T={T}, #orbit-reps tested={len(orbit_reps)}")
    n_pairs = 0
    n_separated = 0
    failures = []
    for x in range(len(orbit_reps)):
        for y in range(x + 1, len(orbit_reps)):
            i, j = orbit_reps[x], orbit_reps[y]
            n_pairs += 1
            result = closed_walks_separate(i, j, B, W, max_m=max_m)
            if result is not None:
                m, c_i, c_j = result
                n_separated += 1
                if n_separated <= 3:
                    flushprint(f"  {i} vs {j}: separated at m={m} "
                               f"(CW_{m}({i})={c_i:.3f}, CW_{m}({j})={c_j:.3f})")
            else:
                failures.append((i, j))
    flushprint(f"  Non-orbit pairs: {n_pairs}; "
               f"separated by some closed walk of length ≤ {max_m}: {n_separated}")
    if failures:
        flushprint(f"  CLOSED-WALK FAILURES: {len(failures)}")
        for i, j in failures[:5]:
            flushprint(f"    {i} vs {j}: NO closed walk of length ≤ {max_m} separates")
    return n_pairs, n_separated, failures


def main():
    rng = np.random.default_rng(2026)
    total_pairs = 0
    total_separated = 0
    total_failures = []

    # Small random matrices (brute-force aut OK for T ≤ 5).
    flushprint("=== RANDOM TWIN-FREE FAMILIES ===")
    for T in [2, 3, 4, 5]:
        for trial in range(3):
            B, W = make_test_matrix(T, rng, trial_idx=trial)
            auts = compute_aut_group(B, W)
            # Compute orbit reps.
            visited = set()
            orbits = []
            for i in range(T):
                if i in visited:
                    continue
                orbit = set()
                for σ in auts:
                    orbit.add(σ[i])
                orbits.append(orbit)
                visited.update(orbit)
            orbit_reps = [next(iter(o)) for o in orbits]
            np_, ns, f = run_family(f"random T={T} trial {trial}", B, W,
                                     orbit_reps, max_m=6)
            total_pairs += np_
            total_separated += ns
            total_failures.extend(f)

    # Adversarial cycle disjoint unions (use analytic orbit structure).
    flushprint("\n=== CYCLE DISJOINT UNIONS (analytic orbits) ===")
    cycle_families = [[5, 6], [3, 4], [4, 5], [3, 5], [3, 3, 3], [4, 6],
                      [3, 6], [5, 7], [3, 7], [4, 7], [6, 7], [3, 4, 5]]
    for sizes in cycle_families:
        label = f"C_{' ⊔ C_'.join(map(str, sizes))}"
        B, W = make_cycle_disjoint_union(sizes)
        orbit_reps = cycle_disjoint_union_orbits(sizes)
        max_m = max(sizes) + 2
        np_, ns, f = run_family(label, B, W, orbit_reps, max_m=max_m)
        total_pairs += np_
        total_separated += ns
        total_failures.extend(f)

    # Random matrices with diagonal-jitter, larger T (skip aut entirely —
    # treat each vertex as its own orbit rep).
    flushprint("\n=== LARGE RANDOM TWIN-FREE (one rep per vertex) ===")
    for T in [6, 7, 8, 10]:
        for trial in range(2):
            B, W = make_test_matrix(T, rng, trial_idx=trial)
            # For diagonal-jittered random B, vertex orbits are typically
            # singletons. Treat each vertex as its own rep.
            orbit_reps = list(range(T))
            np_, ns, f = run_family(f"random T={T} trial {trial}", B, W,
                                     orbit_reps, max_m=8)
            total_pairs += np_
            total_separated += ns
            total_failures.extend(f)

    flushprint("\n" + "=" * 70)
    flushprint(f"TOTAL non-orbit pairs: {total_pairs}")
    flushprint(f"Separated by closed walks: {total_separated}")
    flushprint(f"Closed-walk failures: {len(total_failures)}")
    flushprint("=" * 70)
    if not total_failures:
        flushprint("PASS — closed walks separate vertex orbits in all tested cases.")
        flushprint("Closed-walk-Krylov route may work.")
    else:
        flushprint("FAIL — some vertex orbit pairs not separated by closed walks.")


if __name__ == '__main__':
    main()
