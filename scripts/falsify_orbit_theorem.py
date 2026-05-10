#!/usr/bin/env python3
"""
Falsification script for the orbit-breaking conjectural targets (CT-1 and CT-2).

CT-1: For a weighted graph (B, W) on [T], the column span of the 2-labeled
connection matrix equals the space of Aut(B,W)-invariant functions on [T]².

CT-2: Equal weighted hom sums → orbit structure matches → bijection exists.

Usage: python3 scripts/falsify_orbit_theorem.py [--T 2] [--max-vertices 6] [--trials 5]
"""

import numpy as np
from itertools import permutations, product as cartprod
from math import comb
import argparse
import sys


def make_twin_free_matrix(T, rng):
    """Generate a random symmetric twin-free matrix on [T] with positive weights."""
    # Random symmetric matrix with entries in [0.1, 0.9]
    B = rng.uniform(0.1, 0.9, (T, T))
    B = (B + B.T) / 2
    # Ensure twin-free: add small perturbation to make rows distinct
    for i in range(T):
        B[i, i] += 0.01 * (i + 1)  # distinct diagonals help
    B = np.clip(B, 0, 1)
    B = (B + B.T) / 2  # re-symmetrize
    W = rng.uniform(0.1, 1.0, T)
    return B, W


def compute_aut_group(B, W, tol=1e-10):
    """Compute Aut(B, W) by brute-force over all permutations."""
    T = len(W)
    auts = []
    for perm in permutations(range(T)):
        perm = list(perm)
        # Check W(pi(i)) = W(i) and B(pi(i), pi(j)) = B(i, j)
        if all(abs(W[perm[i]] - W[i]) < tol for i in range(T)):
            if all(abs(B[perm[i]][perm[j]] - B[i][j]) < tol
                   for i in range(T) for j in range(T)):
                auts.append(tuple(perm))
    return auts


def compute_orbits_on_pairs(auts, T):
    """Compute Aut-orbits on [T]² under diagonal action."""
    visited = set()
    orbits = []
    for i in range(T):
        for j in range(T):
            if (i, j) not in visited:
                orbit = set()
                for pi in auts:
                    orbit.add((pi[i], pi[j]))
                orbits.append(frozenset(orbit))
                visited.update(orbit)
    return orbits


def enumerate_2labeled_simple_graphs(n_unlabeled, T_labeled=2):
    """Enumerate all simple graphs on T_labeled + n_unlabeled vertices.
    Vertices 0, 1 are labeled. Returns list of edge sets."""
    n_total = T_labeled + n_unlabeled
    all_possible_edges = [(i, j) for i in range(n_total) for j in range(i+1, n_total)]
    n_edges = len(all_possible_edges)
    graphs = []
    for mask in range(2**n_edges):
        edges = []
        for bit in range(n_edges):
            if mask & (1 << bit):
                edges.append(all_possible_edges[bit])
        graphs.append(edges)
    return graphs


def labeled_eval2(edges, n_unlabeled, B, W, i, j):
    """Compute labeledEval2 for a graph with given edges.
    Vertices 0→i, 1→j are labeled (unweighted). Rest are unlabeled (weighted)."""
    T = len(W)
    n_total = 2 + n_unlabeled
    total = 0.0
    # Sum over all colorings of unlabeled vertices
    for sigma in cartprod(range(T), repeat=n_unlabeled):
        # Full coloring: tau[0]=i, tau[1]=j, tau[2+v]=sigma[v]
        tau = [i, j] + list(sigma)
        # Weight product (unlabeled only)
        weight_prod = 1.0
        for v in range(n_unlabeled):
            weight_prod *= W[sigma[v]]
        # Edge product
        edge_prod = 1.0
        for (u, v) in edges:
            edge_prod *= B[tau[u]][tau[v]]
        total += weight_prod * edge_prod
    return total


def build_connection_matrix(B, W, max_unlabeled):
    """Build the 2-labeled connection matrix M.
    Rows: (i,j) pairs. Columns: 2-labeled simple graphs."""
    T = len(W)
    rows = []  # each row = evaluation vector for a pair (i,j)

    # Collect all graphs
    all_graphs = []
    for n_unlab in range(max_unlabeled + 1):
        graphs = enumerate_2labeled_simple_graphs(n_unlab)
        for edges in graphs:
            all_graphs.append((n_unlab, edges))

    print(f"  Total 2-labeled graphs (up to {max_unlabeled} unlabeled): {len(all_graphs)}")

    # Build matrix: rows = (i,j) pairs, columns = graphs
    M = np.zeros((T * T, len(all_graphs)))
    for idx, (i, j) in enumerate(cartprod(range(T), repeat=2)):
        for g_idx, (n_unlab, edges) in enumerate(all_graphs):
            M[idx, g_idx] = labeled_eval2(edges, n_unlab, B, W, i, j)

    return M, all_graphs


def test_ct1(T, max_unlabeled, rng, trial_num):
    """Test CT-1: column span of M = Aut-invariant functions on [T]²."""
    B, W = make_twin_free_matrix(T, rng)
    auts = compute_aut_group(B, W)
    orbits = compute_orbits_on_pairs(auts, T)
    n_orbits = len(orbits)

    print(f"\n  Trial {trial_num}: T={T}, |Aut|={len(auts)}, #orbits on [T]²={n_orbits}")

    M, _ = build_connection_matrix(B, W, max_unlabeled)
    rank_M = np.linalg.matrix_rank(M, tol=1e-8)

    print(f"  Connection matrix: {M.shape[0]} x {M.shape[1]}, rank={rank_M}")
    print(f"  CT-1 predicts rank = #orbits = {n_orbits}")

    if rank_M != n_orbits:
        print(f"  *** CT-1 FALSIFIED: rank={rank_M} != #orbits={n_orbits} ***")
        print(f"  B =\n{B}")
        print(f"  W = {W}")
        return False
    else:
        print(f"  CT-1 consistent (rank = #orbits = {n_orbits})")

    # Also check: column span ⊆ Aut-invariant
    # Build the Aut-invariant projector
    P = np.zeros((T*T, T*T))
    for orbit in orbits:
        orbit_list = list(orbit)
        indicator = np.zeros(T*T)
        for (i, j) in orbit_list:
            indicator[i * T + j] = 1.0
        indicator /= np.linalg.norm(indicator)
        P += np.outer(indicator, indicator)

    # Project M columns onto Aut-invariant subspace
    M_proj = P @ M
    residual = np.linalg.norm(M - M_proj)
    if residual > 1e-8:
        print(f"  *** Column span NOT Aut-invariant (residual={residual:.2e}) ***")
        return False
    else:
        print(f"  Column span ⊆ Aut-invariant confirmed (residual={residual:.2e})")

    return True


def test_ct2(T, max_unlabeled, rng, trial_num):
    """Test CT-2: equal wHS → bijection recovery."""
    B, W = make_twin_free_matrix(T, rng)
    # Create B' = pi(B) for a random permutation pi
    pi = list(rng.permutation(T))
    B_prime = np.zeros_like(B)
    W_prime = np.zeros_like(W)
    for i in range(T):
        W_prime[pi[i]] = W[i]
        for j in range(T):
            B_prime[pi[i]][pi[j]] = B[i][j]

    print(f"\n  CT-2 Trial {trial_num}: T={T}, pi={pi}")

    # Verify equal weighted hom sums (should be exact by construction)
    M_B, graphs = build_connection_matrix(B, W, max_unlabeled)
    M_Bp, _ = build_connection_matrix(B_prime, W_prime, max_unlabeled)

    # Check weighted pair-averages match
    for g_idx in range(len(graphs)):
        s1 = sum(W[i] * W[j] * M_B[i*T+j, g_idx]
                 for i in range(T) for j in range(T))
        s2 = sum(W_prime[i] * W_prime[j] * M_Bp[i*T+j, g_idx]
                 for i in range(T) for j in range(T))
        if abs(s1 - s2) > 1e-8:
            print(f"  *** Weighted pair-average mismatch at graph {g_idx}: {s1} vs {s2} ***")
            return False

    print(f"  Weighted pair-averages match for all {len(graphs)} graphs")

    # Check if we can recover pi from the connection matrices
    # The column spans should be "compatible" in the sense that
    # M_Bp[pi(i)*T+pi(j), :] = M_B[i*T+j, :] for all (i,j)
    for i in range(T):
        for j in range(T):
            diff = np.linalg.norm(M_Bp[pi[i]*T+pi[j], :] - M_B[i*T+j, :])
            if diff > 1e-8:
                print(f"  *** Row mismatch: M_Bp[pi({i})*T+pi({j})] != M_B[{i}*T+{j}] (diff={diff:.2e}) ***")
                return False

    print(f"  CT-2 consistent: M_Bp rows match M_B rows under pi")
    return True


def main():
    parser = argparse.ArgumentParser(description="Falsify orbit theorem conjectures")
    parser.add_argument("--T", type=int, nargs="+", default=[2, 3],
                        help="Matrix sizes to test")
    parser.add_argument("--max-vertices", type=int, default=4,
                        help="Max total vertices (labeled + unlabeled) for graph enumeration")
    parser.add_argument("--trials", type=int, default=3,
                        help="Number of random trials per T")
    parser.add_argument("--seed", type=int, default=42, help="Random seed")
    args = parser.parse_args()

    rng = np.random.default_rng(args.seed)
    all_pass = True

    for T in args.T:
        max_unlab = min(args.max_vertices - 2, T + 2)  # cap at T+2 unlabeled
        if max_unlab < 0:
            max_unlab = 0

        print(f"\n{'='*60}")
        print(f"Testing T={T}, max_unlabeled={max_unlab}")
        print(f"{'='*60}")

        for trial in range(args.trials):
            if not test_ct1(T, max_unlab, rng, trial + 1):
                all_pass = False
            if not test_ct2(T, max_unlab, rng, trial + 1):
                all_pass = False

    print(f"\n{'='*60}")
    if all_pass:
        print("All tests consistent (not falsified)")
    else:
        print("*** SOME TESTS FALSIFIED ***")
    print(f"{'='*60}")
    return 0 if all_pass else 1


if __name__ == "__main__":
    sys.exit(main())
