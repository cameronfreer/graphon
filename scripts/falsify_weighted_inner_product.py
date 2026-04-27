#!/usr/bin/env python3
"""
Falsification gate for `weightedInnerProduct_descends` (MatrixDetermination.lean:8207).

Statement: for symmetric B, weight W (no positivity), and lists L1, L2
of (K+1)-labeled simple graphs, if `tupleEquiv B W ξ ξ'` at level K then

    ∑ t, W[t] * connCol(L1, ξ, t) * connCol(L2, ξ, t) =
    ∑ t, W[t] * connCol(L1, ξ', t) * connCol(L2, ξ', t).

Where connCol(L, ξ, t) = ∏_{(n,F) ∈ L} labeledEvalK(F, n, K+1, B, W, snoc(ξ, t)).

Goal: test whether the statement holds for signed/zero weights, or
whether positivity hW is required. Per user directive.

Usage: python3 scripts/falsify_weighted_inner_product.py
"""

import numpy as np
from itertools import permutations, product as cartprod


def labeled_eval_K(F_edges, n_unlabeled, K_labeled, B, W, phi):
    """labeledEvalK in the Lean convention: vertices [0, n) are unlabeled
    (summed with weight W), vertices [n, n+K) are labeled (set to phi).

    F_edges: list of (u, v), u < v, in [n + K_labeled].
    phi: tuple of length K_labeled with values in [0, T).
    """
    T = len(W)
    total = 0.0
    for sigma in cartprod(range(T), repeat=n_unlabeled):
        tau = list(sigma) + list(phi)
        weight_prod = 1.0
        for v in range(n_unlabeled):
            weight_prod *= W[sigma[v]]
        edge_prod = 1.0
        for (u, v) in F_edges:
            edge_prod *= B[tau[u]][tau[v]]
        total += weight_prod * edge_prod
    return total


def enumerate_graphs(n, K):
    """Enumerate all simple graphs on n+K vertices as edge lists."""
    n_total = n + K
    all_possible = [(i, j) for i in range(n_total) for j in range(i+1, n_total)]
    n_e = len(all_possible)
    graphs = []
    for mask in range(2 ** n_e):
        edges = []
        for bit in range(n_e):
            if mask & (1 << bit):
                edges.append(all_possible[bit])
        graphs.append(edges)
    return graphs


def is_tuple_equiv(B, W, K, phi, phi_prime, max_n=2):
    """Heuristic test: tupleEquiv B W phi phi'.

    Check labeledEvalK for all (n, F) with n <= max_n. If they all agree,
    declare tupleEquiv (good enough for small T, K).
    """
    for n in range(max_n + 1):
        for F_edges in enumerate_graphs(n, K):
            v1 = labeled_eval_K(F_edges, n, K, B, W, phi)
            v2 = labeled_eval_K(F_edges, n, K, B, W, phi_prime)
            if not np.isclose(v1, v2, atol=1e-9, rtol=1e-7):
                return False
    return True


def conn_col(L, B, W, K, xi, t):
    """connCol B W L xi t."""
    snoc = list(xi) + [t]
    val = 1.0
    for (n, F_edges) in L:
        val *= labeled_eval_K(F_edges, n, K + 1, B, W, snoc)
    return val


def weighted_inner_product(L1, L2, B, W, K, xi):
    """∑ t, W[t] * connCol(L1, xi, t) * connCol(L2, xi, t)."""
    T = len(W)
    total = 0.0
    for t in range(T):
        total += W[t] * conn_col(L1, B, W, K, xi, t) * conn_col(L2, B, W, K, xi, t)
    return total


def find_tuple_equiv_pairs(B, W, K, max_n=2):
    """Enumerate all tupleEquiv pairs (xi, xi') with xi != xi'."""
    T = len(W)
    pairs = []
    seen = set()
    for xi in cartprod(range(T), repeat=K):
        for xi_p in cartprod(range(T), repeat=K):
            if xi == xi_p:
                continue
            key = (xi, xi_p) if xi < xi_p else (xi_p, xi)
            if key in seen:
                continue
            if is_tuple_equiv(B, W, K, xi, xi_p, max_n=max_n):
                pairs.append((xi, xi_p))
                seen.add(key)
    return pairs


def is_orbit_pair(B, W, xi, xi_p, tol=1e-9):
    """Check whether (xi, xi') are in the same Aut(B,W)-orbit."""
    T = len(W)
    K = len(xi)
    for perm in permutations(range(T)):
        # Aut check
        if not all(abs(W[perm[i]] - W[i]) < tol for i in range(T)):
            continue
        if not all(abs(B[perm[i]][perm[j]] - B[i][j]) < tol
                   for i in range(T) for j in range(T)):
            continue
        # Apply perm to xi
        xi_perm = tuple(perm[xi[k]] for k in range(K))
        if xi_perm == tuple(xi_p):
            return True
    return False


def run_trial(B, W, K, label, max_n=2, max_L_len=2, max_graph_unlabeled=1, verbose=False):
    """Run one trial: find tupleEquiv pairs, test inner product on small L1, L2."""
    T = len(W)
    pairs = find_tuple_equiv_pairs(B, W, K, max_n=max_n)
    non_orbit_pairs = [
        (xi, xi_p) for (xi, xi_p) in pairs
        if not is_orbit_pair(B, W, xi, xi_p)
    ]

    # Build small graph family at level K+1
    small_graphs = []
    for n in range(max_graph_unlabeled + 1):
        for F in enumerate_graphs(n, K + 1):
            small_graphs.append((n, F))
    # Limit complexity: drop very-large graphs
    small_graphs = [g for g in small_graphs if len(g[1]) <= 3]

    fail_count = 0
    test_count = 0
    first_failures = []

    # For each tupleEquiv pair, sample L1, L2 of length 2
    # (full enumeration explodes; subsample)
    rng = np.random.default_rng(42)

    for xi, xi_p in pairs:
        # Use a finite test set: every pair of single-graph "L"s with up to 2 entries
        for g1 in small_graphs:
            for g2 in small_graphs:
                # Test L1 = [g1, g1], L2 = [g2, g2] (length 2 each)
                for (L1, L2, name) in [
                    ([g1, g2], [g1, g2], "L1=L2=[g1,g2]"),
                    ([g1, g1], [g2, g2], "L1=[g1,g1] L2=[g2,g2]"),
                    ([g1], [g2], "L1=[g1] L2=[g2]"),
                    ([g1, g2], [], "L1=[g1,g2] L2=[]"),
                ]:
                    v1 = weighted_inner_product(L1, L2, B, W, K, xi)
                    v2 = weighted_inner_product(L1, L2, B, W, K, xi_p)
                    test_count += 1
                    if not np.isclose(v1, v2, atol=1e-7, rtol=1e-6):
                        fail_count += 1
                        if len(first_failures) < 3:
                            first_failures.append({
                                'label': label,
                                'xi': xi, 'xi_p': xi_p,
                                'orbit_pair': (xi, xi_p) not in [(p1, p2) for (p1, p2) in non_orbit_pairs],
                                'L1': L1, 'L2': L2, 'name': name,
                                'v1': v1, 'v2': v2, 'diff': v1 - v2,
                            })

    return {
        'label': label,
        'B': B, 'W': W,
        'pairs': pairs,
        'non_orbit_pairs': non_orbit_pairs,
        'tests': test_count,
        'fails': fail_count,
        'first_failures': first_failures,
    }


def main():
    rng = np.random.default_rng(2026)
    Ks_to_test = [1, 2]

    print("=" * 70)
    print("Falsification gate: weightedInnerProduct_descends")
    print("=" * 70)
    print(f"Levels K={Ks_to_test}, testing T=2..4 with various B, W patterns.")
    print()
    K = Ks_to_test[-1]  # main coverage at K=2; K=1 added below

    all_fail = 0
    all_test = 0
    all_failures = []

    # Pattern 1: positive W, symmetric B (both signed)
    for trial in range(5):
        T = rng.integers(2, 4 + 1)
        B = rng.uniform(-1.0, 1.0, (T, T))
        B = (B + B.T) / 2
        W = rng.uniform(0.1, 1.0, T)  # positive
        result = run_trial(B, W, K, label=f"pos-W trial {trial} T={T}")
        all_fail += result['fails']
        all_test += result['tests']
        all_failures.extend(result['first_failures'])
        print(f"[pos-W   T={T} trial {trial}] pairs={len(result['pairs'])} "
              f"non-orbit={len(result['non_orbit_pairs'])} "
              f"tests={result['tests']} fails={result['fails']}")

    # Pattern 2: signed W
    for trial in range(5):
        T = rng.integers(2, 4 + 1)
        B = rng.uniform(-1.0, 1.0, (T, T))
        B = (B + B.T) / 2
        W = rng.uniform(-1.0, 1.0, T)  # signed
        result = run_trial(B, W, K, label=f"signed-W trial {trial} T={T}")
        all_fail += result['fails']
        all_test += result['tests']
        all_failures.extend(result['first_failures'])
        print(f"[sgn-W   T={T} trial {trial}] pairs={len(result['pairs'])} "
              f"non-orbit={len(result['non_orbit_pairs'])} "
              f"tests={result['tests']} fails={result['fails']}")

    # Pattern 3: W with zeros
    for trial in range(5):
        T = rng.integers(3, 4 + 1)
        B = rng.uniform(-1.0, 1.0, (T, T))
        B = (B + B.T) / 2
        W = rng.uniform(0.1, 1.0, T)
        # Zero out one entry
        zero_idx = rng.integers(0, T)
        W[zero_idx] = 0.0
        result = run_trial(B, W, K, label=f"zero-W trial {trial} T={T}")
        all_fail += result['fails']
        all_test += result['tests']
        all_failures.extend(result['first_failures'])
        print(f"[zero-W  T={T} trial {trial}] pairs={len(result['pairs'])} "
              f"non-orbit={len(result['non_orbit_pairs'])} "
              f"tests={result['tests']} fails={result['fails']}")

    # Pattern 4: NON-twin-free B with signed/zero W (most likely to falsify)
    # Construct a B with twin rows: B[i] = B[j] for some i != j.
    for trial in range(8):
        T = rng.integers(3, 4 + 1)
        B = rng.uniform(-1.0, 1.0, (T, T))
        B = (B + B.T) / 2
        # Make rows 0 and 1 identical (twin)
        B[0, :] = B[1, :].copy()
        B[:, 0] = B[:, 1].copy()
        B[0, 0] = B[1, 1]  # ensure symmetric
        B = (B + B.T) / 2
        # Try signed W and zero W
        if trial % 3 == 0:
            W = rng.uniform(-1.0, 1.0, T)
            wlabel = "signed"
        elif trial % 3 == 1:
            W = rng.uniform(0.1, 1.0, T)
            W[0] = 0.0
            wlabel = "zero@0"
        else:
            W = rng.uniform(0.1, 1.0, T)  # positive
            wlabel = "positive"
        result = run_trial(B, W, K, label=f"twin-B {wlabel} trial {trial} T={T}")
        all_fail += result['fails']
        all_test += result['tests']
        all_failures.extend(result['first_failures'])
        print(f"[twin-B  T={T} trial {trial} W={wlabel}] pairs={len(result['pairs'])} "
              f"non-orbit={len(result['non_orbit_pairs'])} "
              f"tests={result['tests']} fails={result['fails']}")

    # Pattern 5: K=1 with twin-B
    K1 = 1
    for trial in range(8):
        T = rng.integers(3, 4 + 1)
        B = rng.uniform(-1.0, 1.0, (T, T))
        B = (B + B.T) / 2
        B[0, :] = B[1, :].copy()
        B[:, 0] = B[:, 1].copy()
        B[0, 0] = B[1, 1]
        B = (B + B.T) / 2
        if trial % 3 == 0:
            W = rng.uniform(-1.0, 1.0, T); wlabel = "signed"
        elif trial % 3 == 1:
            W = rng.uniform(0.1, 1.0, T); W[0] = 0.0; wlabel = "zero@0"
        else:
            W = rng.uniform(0.1, 1.0, T); wlabel = "positive"
        result = run_trial(B, W, K1, label=f"K=1 twin-B {wlabel} trial {trial} T={T}")
        all_fail += result['fails']
        all_test += result['tests']
        all_failures.extend(result['first_failures'])
        print(f"[K=1 twn T={T} trial {trial} W={wlabel}] pairs={len(result['pairs'])} "
              f"non-orbit={len(result['non_orbit_pairs'])} "
              f"tests={result['tests']} fails={result['fails']}")

    # Pattern 6: highly degenerate (all-zero W or all-zero B)
    for trial in range(2):
        T = 3
        if trial == 0:
            B = rng.uniform(-1, 1, (T, T)); B = (B + B.T) / 2
            W = np.zeros(T)
            wlabel = "all-zero W"
        else:
            B = np.zeros((T, T))
            W = rng.uniform(-1, 1, T)
            wlabel = "all-zero B"
        result = run_trial(B, W, 2, label=f"degen {wlabel} T={T}")
        all_fail += result['fails']
        all_test += result['tests']
        all_failures.extend(result['first_failures'])
        print(f"[degen T={T} {wlabel}] pairs={len(result['pairs'])} "
              f"non-orbit={len(result['non_orbit_pairs'])} "
              f"tests={result['tests']} fails={result['fails']}")

    print()
    print("=" * 70)
    print(f"TOTAL: {all_test} tests, {all_fail} failures")
    print("=" * 70)
    if all_fail == 0:
        print("PASS — no failure under any tested W (pos / signed / zero, twin-free or twin-B).")
        print("Statement appears to hold without hW positivity.")
    else:
        print(f"FAIL — {all_fail} counterexamples. Sample failures:")
        for fail in all_failures[:5]:
            print(f"\n  {fail['label']} ({fail['name']})")
            print(f"    orbit pair: {fail['orbit_pair']}")
            print(f"    xi={fail['xi']}  xi'={fail['xi_p']}")
            print(f"    L1={fail['L1']}")
            print(f"    L2={fail['L2']}")
            print(f"    v1={fail['v1']:.6e}  v2={fail['v2']:.6e}  diff={fail['diff']:.2e}")


if __name__ == '__main__':
    main()
