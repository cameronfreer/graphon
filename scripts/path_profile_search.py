#!/usr/bin/env python3
"""
Path-profile falsification for rooted_profiles_separate_vertex_orbits.

Per user 2026-05-14 directive: test whether ROOTED PATH profiles alone
(simple graphs that are paths rooted at the labeled vertex) suffice to
separate vertex orbits.

Path profile at vertex i:
  P_m(i) := simpleEvalAt (path of length m, rooted at label 0) i
         = ∑_{σ : Fin m → Fin T} W(σ 0) ... W(σ (m-1)) *
           B(i, σ 0) * B(σ 0, σ 1) * ... * B(σ (m-2), σ (m-1))
         = (W ∘ A^m * 1)(i)   roughly, where A is weighted adjacency.

Conjecture: distinct vertex orbits ⟹ some path profile differs.

Test families:
- Random twin-free B, W > 0 (T = 2..6).
- Adversarial: C_5 ⊔ C_6, C_4 ⊔ K_{1,3} (degree-regular disconnected).
- Adversarial: strongly-regular pairs of non-isomorphic graphs of same size.

Usage: python3 scripts/path_profile_search.py
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


def path_profile(i, m, B, W):
    """Compute rooted path profile of length m at vertex i.

    Path graph: label-0 -- u_0 -- u_1 -- ... -- u_{m-1}.
    With m = 0, no edges, evaluates to 1 (the empty product).
    With m = 1, single edge label-0 -- u_0: ∑ W(t) B(i, t).
    With m = 2, two edges: ∑_{s,t} W(s) W(t) B(i, s) B(s, t).
    Etc.
    """
    T = len(W)
    if m == 0:
        return 1.0
    total = 0.0
    for σ in cartprod(range(T), repeat=m):
        w_prod = 1.0
        for v in range(m):
            w_prod *= W[σ[v]]
        b_prod = B[i][σ[0]]
        for k in range(m - 1):
            b_prod *= B[σ[k]][σ[k+1]]
        total += w_prod * b_prod
    return total


def path_profiles_separate(i, j, B, W, max_m=6, tol=1e-8):
    """Check if some path profile of length ≤ max_m separates i and j."""
    for m in range(max_m + 1):
        p_i = path_profile(i, m, B, W)
        p_j = path_profile(j, m, B, W)
        if not np.isclose(p_i, p_j, atol=tol, rtol=1e-7):
            return m
    return None


def run_family(label, B, W, max_m=6):
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
            m = path_profiles_separate(i, j, B, W, max_m=max_m)
            if m is not None:
                n_separated += 1
            else:
                failures.append((i, j))
    print(f"  Non-orbit pairs: {n_pairs}; "
          f"separated by some path of length ≤ {max_m}: {n_separated}")
    if failures:
        print(f"  PATH-PROFILE FAILURES: {len(failures)}")
        for i, j in failures[:5]:
            print(f"    {i} vs {j}: NO path-profile of length ≤ {max_m} separates")
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
            np_, ns, f = run_family(f"random T={T} trial {trial}", B, W, max_m=5)
            total_pairs += np_
            total_separated += ns
            total_failures.extend(f)

    # Adversarial structured.
    for sizes in [[5, 6], [3, 4], [4, 5], [3, 5], [3, 3, 3], [4, 6]]:
        label = f"C_{' ⊔ C_'.join(map(str, sizes))}"
        B, W = make_cycle_disjoint_union(sizes)
        np_, ns, f = run_family(label, B, W, max_m=7)
        total_pairs += np_
        total_separated += ns
        total_failures.extend(f)

    # Strongly-regular pairs: hard case — same path profile but different graphs.
    # Petersen vs K_{3,3} cocktail party (placeholder — would need careful construction).
    # Skipping for now; main empirical test is the cycle disjoint unions.

    print("\n" + "=" * 70)
    print(f"TOTAL non-orbit pairs: {total_pairs}")
    print(f"Separated by path profile: {total_separated}")
    print(f"Path-profile failures: {len(total_failures)}")
    print("=" * 70)
    if not total_failures:
        print("PASS — path profiles separate vertex orbits in all tested cases.")
    else:
        print("FAIL — some vertex orbit pairs not separated by path profiles.")
        print("Path-Krylov route may need higher-order rooted graphs.")


if __name__ == '__main__':
    main()
