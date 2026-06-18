"""Falsification search for `rootedProfileEquiv i j  ==>  W i = W j`.

#70 (vertexOrbitRel_of_rootedProfileEquiv) needs this as a PRIOR sub-fact:
a weighted automorphism preserves W, so orbit(i,j) forces W i = W j; hence if
rooted-profile-equivalent vertices can have unequal root weights, the theorem is
FALSE as stated.

rootedProfile B W i F = sum over assignments sigma : (unlabeled vertices) -> [T]
  of  prod_{u unlabeled} W[sigma_u] * prod_{(p,q) edge of F} B[a_p][a_q],
where the root (vertex 0) is pinned to i and unlabeled vertex v to sigma_v.
The root carries NO weight.

We approximate `rootedProfileEquiv i j` by equality of rooted profiles over the
battery of ALL simple rooted graphs with up to N_UNLAB unlabeled vertices. If two
vertices match on the whole battery but have W i != W j, that is a candidate
counterexample (we then re-test with a larger battery).

B is real symmetric, zero diagonal (non-Boolean entries), twin-free; W > 0.
"""
import itertools
import numpy as np

rng = np.random.default_rng(20260618)

def rooted_profiles_for_graph(B, W, edges, n_unlab, T):
    """Return length-T vector of rooted profiles (one per root vertex i)."""
    # a_0 = root = i ; a_{v} = sigma[v-1] for v in 1..n_unlab
    out = np.zeros(T)
    assignments = list(itertools.product(range(T), repeat=n_unlab))
    # Precompute weight products for each assignment
    wprods = np.array([np.prod([W[s] for s in sigma]) if sigma else 1.0
                       for sigma in assignments])
    for i in range(T):
        total = 0.0
        for sigma, wp in zip(assignments, wprods):
            a = (i,) + sigma
            prod = 1.0
            for (p, q) in edges:
                prod *= B[a[p]][a[q]]
                if prod == 0.0:
                    break
            total += wp * prod
        out[i] = total
    return out

def all_rooted_graph_edge_sets(n_unlab):
    """All simple rooted graphs on vertices {0=root,1..n_unlab}: every subset of
    the C(n_unlab+1,2) possible edges."""
    V = n_unlab + 1
    possible = [(p, q) for p in range(V) for q in range(p + 1, V)]
    for r in range(len(possible) + 1):
        for combo in itertools.combinations(possible, r):
            yield list(combo)

def profile_matrix(B, W, T, max_unlab):
    """Stack rooted-profile vectors across the whole battery -> (n_graphs, T)."""
    cols = []
    for n_unlab in range(0, max_unlab + 1):
        for edges in all_rooted_graph_edge_sets(n_unlab):
            cols.append(rooted_profiles_for_graph(B, W, edges, n_unlab, T))
    return np.array(cols)  # (n_graphs, T)

def twin_free(B, tol=1e-9):
    T = B.shape[0]
    for i in range(T):
        for j in range(i + 1, T):
            if np.allclose(B[i], B[j], atol=tol):
                return False
    return True

def search(T, n_instances, max_unlab=3, tol=1e-7):
    found = []
    for _ in range(n_instances):
        M = rng.normal(size=(T, T))
        B = (M + M.T) / 2
        np.fill_diagonal(B, 0.0)
        if not twin_free(B):
            continue
        W = rng.uniform(0.3, 3.0, size=T)
        P = profile_matrix(B, W, T, max_unlab)  # (n_graphs, T)
        for i in range(T):
            for j in range(i + 1, T):
                if np.allclose(P[:, i], P[:, j], atol=tol):
                    if abs(W[i] - W[j]) > 1e-6:
                        found.append((B, W, i, j))
    return found

if __name__ == "__main__":
    for T in (3, 4, 5):
        for mu in (2, 3):
            hits = search(T, n_instances=4000 // T, max_unlab=mu)
            print(f"T={T}, max_unlab={mu}: {len(hits)} candidate(s) "
                  f"(rpe-match on battery but W i != W j)")
            if hits:
                B, W, i, j = hits[0]
                print("  W =", np.round(W, 4), " i,j =", i, j,
                      " Wi,Wj =", round(W[i], 4), round(W[j], 4))
                # Re-test with a richer battery (more unlabeled vertices).
                P2 = profile_matrix(B, W, B.shape[0], mu + 1)
                print("  still matches at max_unlab =", mu + 1, ":",
                      bool(np.allclose(P2[:, i], P2[:, j], atol=1e-6)))
