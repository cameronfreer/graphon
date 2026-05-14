#!/usr/bin/env python3
"""
Separator search for orbit_separation_by_simple_graph (Lovász §3).

Per user directive: before attacking the theorem formally, run a
computational pass to classify what kinds of simple graphs serve as
separators for non-orbit tuple pairs.

For each small (B, W) twin-free + W > 0 and each K:
  - Compute aut group and orbit classes of Fin K → Fin T tuples.
  - For each non-orbit pair (ξ, ξ'):
    - Search for the minimal separating simple graph F at level K.
    - Record edge structure: shape, vertex/edge count, connectivity.

Goal: determine whether separators are always rooted trees / paths /
small connected graphs, or if some non-orbit pairs require products
or larger constructions.

Usage: python3 scripts/separator_search.py
"""

import numpy as np
from itertools import permutations, product as cartprod, combinations
import sys


def make_test_matrix(T, rng, trial_idx=0):
    """Generate a small twin-free symmetric B with positive W."""
    B = rng.uniform(-1.0, 1.0, (T, T))
    B = (B + B.T) / 2
    # Add diagonal jitter to ensure twin-free.
    for i in range(T):
        B[i, i] += 0.1 * (i + 1 + 0.01 * trial_idx)
    # Verify twin-free.
    is_twin_free = True
    for i in range(T):
        for j in range(i+1, T):
            if np.allclose(B[i], B[j], atol=1e-10):
                is_twin_free = False
                break
    if not is_twin_free:
        # Add row-distinguishing perturbation.
        for i in range(T):
            B[i, :] += 0.01 * (i + 1) * np.arange(T)
        B = (B + B.T) / 2
    W = rng.uniform(0.5, 1.5, T)
    return B, W


def compute_aut_group(B, W, tol=1e-9):
    """Brute-force aut group: permutations σ with W(σ i) = W(i) and B(σ i, σ j) = B(i, j)."""
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


def compute_orbit_classes(K, auts, T):
    """Compute Aut-orbits on Fin K → Fin T tuples."""
    visited = set()
    orbits = []
    for ξ in cartprod(range(T), repeat=K):
        if ξ in visited:
            continue
        orbit = set()
        for σ in auts:
            σξ = tuple(σ[ξ[k]] for k in range(K))
            orbit.add(σξ)
        orbits.append(frozenset(orbit))
        visited.update(orbit)
    return orbits


def enumerate_simple_graphs(n_total):
    """Enumerate all simple graphs on n_total vertices as edge sets."""
    edges_all = [(i, j) for i in range(n_total) for j in range(i+1, n_total)]
    n_e = len(edges_all)
    for mask in range(2 ** n_e):
        edges = []
        for bit in range(n_e):
            if mask & (1 << bit):
                edges.append(edges_all[bit])
        yield edges


def simple_eval_at(edges, n_unlabeled, K, B, W, ξ):
    """Compute simpleEvalAt for K-labeled simple graph with n_unlabeled vertices.

    Vertices: 0..K-1 = labels (mapped via ξ), K..K+n_unlabeled-1 = unlabeled (summed).
    """
    T = len(W)
    total = 0.0
    for σ in cartprod(range(T), repeat=n_unlabeled):
        τ = [ξ[v] if v < K else σ[v - K] for v in range(K + n_unlabeled)]
        weight_prod = 1.0
        for v in range(n_unlabeled):
            weight_prod *= W[σ[v]]
        edge_prod = 1.0
        for (u, v) in edges:
            edge_prod *= B[τ[u]][τ[v]]
        total += weight_prod * edge_prod
    return total


def classify_graph(edges, K, n_unlabeled):
    """Classify a separator by structure."""
    n_total = K + n_unlabeled
    if not edges:
        return ("empty", 0)
    n_edges = len(edges)
    if n_edges == 1:
        u, v = edges[0]
        # Single edge: label-label, label-unlabeled, or unlabeled-unlabeled.
        if u < K and v < K:
            return ("single-LL", 1)
        elif u < K or v < K:
            return ("single-LU", 1)
        else:
            return ("single-UU", 1)
    # Compute degree sequence at label vertices.
    deg = [0] * n_total
    for (u, v) in edges:
        deg[u] += 1
        deg[v] += 1
    # Check if connected (use BFS).
    if not edges:
        is_connected = (n_total == 0)
    else:
        # Vertices that have edges.
        active = set()
        for (u, v) in edges:
            active.add(u)
            active.add(v)
        # BFS from first active.
        start = next(iter(active))
        visited = {start}
        queue = [start]
        while queue:
            x = queue.pop()
            for (u, v) in edges:
                if u == x and v not in visited:
                    visited.add(v); queue.append(v)
                elif v == x and u not in visited:
                    visited.add(u); queue.append(u)
        is_connected = (visited == active)
    # Check shape: star (one center), path (all degrees ≤ 2 + path-like), tree, etc.
    label_degs = [deg[v] for v in range(K)]
    unlabeled_degs = [deg[v] for v in range(K, n_total)]

    # Path detection: connected, all degrees ≤ 2, exactly 2 endpoints with degree 1
    is_path = (is_connected and all(d <= 2 for d in deg) and
               sum(1 for d in deg if d == 1) == 2)
    # Star detection: one center vertex with degree n-1, others degree 1
    if any(deg[v] == n_edges and all(deg[w] == 1 for w in range(n_total) if w != v and deg[w] > 0)
           for v in range(n_total)):
        is_star = True
    else:
        is_star = False
    # Tree: connected + n_edges = n_active_vertices - 1
    active_v = sum(1 for d in deg if d > 0)
    is_tree = is_connected and n_edges == active_v - 1

    if is_path:
        return ("path", n_edges)
    if is_star:
        return ("star", n_edges)
    if is_tree:
        return ("tree", n_edges)
    if is_connected:
        return ("connected", n_edges)
    return ("disconnected", n_edges)


def find_minimal_separator(ξ, ξ_prime, K, B, W, max_n=2, max_edges=4):
    """Find a minimal simple graph separating ξ from ξ_prime."""
    T = len(W)
    # Search by increasing complexity: (n_unlabeled, n_edges).
    for n_unlabeled in range(max_n + 1):
        n_total = K + n_unlabeled
        all_possible_edges = [(i, j) for i in range(n_total) for j in range(i+1, n_total)]
        n_e_max = len(all_possible_edges)
        # For each edge count, try all combinations.
        for n_edges in range(min(max_edges + 1, n_e_max + 1)):
            for edge_combo in combinations(all_possible_edges, n_edges):
                edges = list(edge_combo)
                v1 = simple_eval_at(edges, n_unlabeled, K, B, W, ξ)
                v2 = simple_eval_at(edges, n_unlabeled, K, B, W, ξ_prime)
                if not np.isclose(v1, v2, atol=1e-8, rtol=1e-7):
                    shape, _ = classify_graph(edges, K, n_unlabeled)
                    return {
                        'edges': edges,
                        'n_unlabeled': n_unlabeled,
                        'n_edges': n_edges,
                        'shape': shape,
                        'v1': v1,
                        'v2': v2,
                    }
    return None


def main():
    rng = np.random.default_rng(2026)
    shape_stats = {}
    no_separator_found = []
    pair_count = 0

    for T in [2, 3, 4, 5]:
        for K in [1, 2, 3]:
            for trial in range(2):
                B, W = make_test_matrix(T, rng, trial_idx=trial)
                auts = compute_aut_group(B, W)
                orbits = compute_orbit_classes(K, auts, T)
                n_orbits = len(orbits)

                print(f"\nT={T}, K={K}, trial {trial}: |Aut|={len(auts)}, #orbits={n_orbits}")

                # For each pair of orbit reps in DIFFERENT orbits.
                orbit_reps = [next(iter(o)) for o in orbits]
                for i, ξ in enumerate(orbit_reps):
                    for j in range(i + 1, len(orbit_reps)):
                        ξ_prime = orbit_reps[j]
                        pair_count += 1
                        sep = find_minimal_separator(ξ, ξ_prime, K, B, W,
                                                     max_n=2, max_edges=4)
                        if sep is None:
                            # Try harder.
                            sep = find_minimal_separator(ξ, ξ_prime, K, B, W,
                                                         max_n=3, max_edges=5)
                        if sep is None:
                            no_separator_found.append((T, K, trial, ξ, ξ_prime))
                            print(f"  NO SEPARATOR for {ξ} vs {ξ_prime} (search up to n=3, e=5)")
                        else:
                            key = (sep['shape'], sep['n_unlabeled'], sep['n_edges'])
                            shape_stats[key] = shape_stats.get(key, 0) + 1
                            print(f"  {ξ} vs {ξ_prime}: {sep['shape']} "
                                  f"(n_unlabeled={sep['n_unlabeled']}, "
                                  f"n_edges={sep['n_edges']}, edges={sep['edges']})")

    print("\n" + "=" * 70)
    print(f"TOTAL pairs: {pair_count}")
    print(f"Separators found: {pair_count - len(no_separator_found)}")
    print(f"No separator found (search up to n=3, e=5): {len(no_separator_found)}")
    print("=" * 70)
    print("\nSEPARATOR SHAPE DISTRIBUTION:")
    for (shape, n_un, n_e), count in sorted(shape_stats.items(), key=lambda x: -x[1]):
        print(f"  {shape:15s} (n_unlabeled={n_un}, n_edges={n_e}): {count}")

    if no_separator_found:
        print("\nUNSEPARATED PAIRS (need larger search or genuine obstruction):")
        for entry in no_separator_found:
            print(f"  {entry}")


if __name__ == '__main__':
    main()


def cycle_separator_search():
    """Search for the minimal separator for C_5 ⊔ C_6 at K=1, ξ=(0,) vs ξ'=(5,)."""
    import numpy as np
    sizes = [5, 6]
    T = sum(sizes)
    B = np.zeros((T, T))
    offset = 0
    for n in sizes:
        for i in range(n):
            j = (i + 1) % n
            B[offset + i, offset + j] = 1.0
            B[offset + j, offset + i] = 1.0
        offset += n
    W = np.ones(T)
    K = 1
    ξ = (0,)   # vertex in C_5
    ξ_prime = (5,)  # vertex in C_6

    print("\n" + "=" * 70)
    print("C_5 ⊔ C_6 separator search at K=1, ξ=(0,) vs ξ'=(5,)")
    print("=" * 70)

    # Search by increasing n_unlabeled, then by edge count.
    for n_unlabeled in range(0, 5):
        n_total = K + n_unlabeled
        all_possible_edges = [(i, j) for i in range(n_total) for j in range(i+1, n_total)]
        n_e_max = len(all_possible_edges)
        for n_edges in range(0, n_e_max + 1):
            for edge_combo in combinations(all_possible_edges, n_edges):
                edges = list(edge_combo)
                v1 = simple_eval_at(edges, n_unlabeled, K, B, W, ξ)
                v2 = simple_eval_at(edges, n_unlabeled, K, B, W, ξ_prime)
                if not np.isclose(v1, v2, atol=1e-8, rtol=1e-7):
                    print(f"SEPARATOR FOUND: n_unlabeled={n_unlabeled}, "
                          f"n_edges={n_edges}, edges={edges}")
                    print(f"  v(C_5 vertex) = {v1:.4f}")
                    print(f"  v(C_6 vertex) = {v2:.4f}")
                    return edges, n_unlabeled
    print("No separator found in search range (n_unlabeled ≤ 4).")
    return None, None


if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'cycles':
    cycle_separator_search()
