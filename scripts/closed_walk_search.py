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

import numpy as np
from itertools import permutations, product as cartprod


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


def vertex_orbit_classes(B, W, auts):
    T = len(W)
    visited = set()
    orbits = []
    for i in range(T):
        if i in visited:
            continue
        orbit = set()
        for σ in auts:
            orbit.add(σ[i])
        orbits.append(frozenset(orbit))
        visited.update(orbit)
    return orbits


def closed_walk_profile(i, m, B, W):
    """Closed walk of length m at root i, via numpy matrix matmul.

    Define N[a, b] := W[b] * B[a, b]. Then:
      N^m[i, i] = ∑_{v_1,...,v_{m-1}, v_m=i} W[v_1] W[v_2] ... W[v_{m-1}] W[i] *
                  B[i, v_1] B[v_1, v_2] ... B[v_{m-1}, i]
                = W[i] * CW_m(i).
    So CW_m(i) = N^m[i, i] / W[i].

    For m = 0: trivially 1 (no edges, single root).
    For m = 1: requires B(i, i) (self-loop), absent in simple graphs.
      Returns 0.
    """
    if m == 0:
        return 1.0
    if m == 1:
        return 0.0
    N = (B.T * W).T  # N[a, b] = W[b] * B[a, b]; via broadcasting.
    # Actually we want N[a, b] = W[b] * B[a, b].
    # B is T x T, W is T. We want each column b scaled by W[b].
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


def run_family(label, B, W, max_m=7):
    auts = compute_aut_group(B, W)
    orbits = vertex_orbit_classes(B, W, auts)
    print(f"\n[{label}] T={len(W)}, |Aut|={len(auts)}, #vertex-orbits={len(orbits)}")
    n_pairs = 0
    n_separated = 0
    failures = []
    orbit_reps = [next(iter(o)) for o in orbits]
    for x in range(len(orbit_reps)):
        for y in range(x + 1, len(orbit_reps)):
            i, j = orbit_reps[x], orbit_reps[y]
            n_pairs += 1
            result = closed_walks_separate(i, j, B, W, max_m=max_m)
            if result is not None:
                m, c_i, c_j = result
                n_separated += 1
                if n_separated <= 3:
                    print(f"  {i} vs {j}: separated at m={m} "
                          f"(CW_{m}({i})={c_i:.3f}, CW_{m}({j})={c_j:.3f})")
            else:
                failures.append((i, j))
    print(f"  Non-orbit pairs: {n_pairs}; "
          f"separated by some closed walk of length ≤ {max_m}: {n_separated}")
    if failures:
        print(f"  CLOSED-WALK FAILURES: {len(failures)}")
        for i, j in failures[:5]:
            print(f"    {i} vs {j}: NO closed walk of length ≤ {max_m} separates")
    return n_pairs, n_separated, failures


def main():
    rng = np.random.default_rng(2026)
    total_pairs = 0
    total_separated = 0
    total_failures = []

    # Random small.
    for T in [2, 3, 4, 5]:
        for trial in range(3):
            B, W = make_test_matrix(T, rng, trial_idx=trial)
            np_, ns, f = run_family(f"random T={T} trial {trial}", B, W, max_m=6)
            total_pairs += np_
            total_separated += ns
            total_failures.extend(f)

    # Adversarial structured.
    for sizes in [[5, 6], [3, 4], [4, 5], [3, 5], [3, 3, 3], [4, 6], [3, 6], [5, 7]]:
        label = f"C_{' ⊔ C_'.join(map(str, sizes))}"
        B, W = make_cycle_disjoint_union(sizes)
        # Use max_m = max cycle size + 2 to be safe.
        max_m = max(sizes) + 2
        np_, ns, f = run_family(label, B, W, max_m=max_m)
        total_pairs += np_
        total_separated += ns
        total_failures.extend(f)

    print("\n" + "=" * 70)
    print(f"TOTAL non-orbit pairs: {total_pairs}")
    print(f"Separated by closed walks: {total_separated}")
    print(f"Closed-walk failures: {len(total_failures)}")
    print("=" * 70)
    if not total_failures:
        print("PASS — closed walks separate vertex orbits in all tested cases.")
        print("Closed-walk-Krylov route may work.")
    else:
        print("FAIL — some vertex orbit pairs not separated by closed walks.")


if __name__ == '__main__':
    main()
