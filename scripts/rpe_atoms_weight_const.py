"""Test: is W constant on the rpe-atoms of (B,W)?

`rpe i j => W i = W j`  <=>  W is constant on each rpe-class  <=>  W in the
rooted-profile span.  Because the atoms DEPEND on W, the conjecture is that when
W breaks a B-symmetry the atoms refine to compensate, so W is always atom-const.

We stress this with the hardest case: B symmetric under a permutation tau, but W
NOT tau-invariant.  Compute rpe-atoms via the battery of all simple rooted graphs
with <= MU unlabeled vertices, then check W is constant on every atom.

A FAILURE (some atom with non-constant W) would be a counterexample to
rpe => W i = W j, hence to vertexOrbitRel_of_rootedProfileEquiv.
"""
import itertools
import numpy as np

rng = np.random.default_rng(7)

def all_rooted_graph_edge_sets(n_unlab):
    V = n_unlab + 1
    possible = [(p, q) for p in range(V) for q in range(p + 1, V)]
    for r in range(len(possible) + 1):
        for combo in itertools.combinations(possible, r):
            yield list(combo)

def profile_matrix(B, W, MU):
    T = B.shape[0]
    cols = []
    for n_unlab in range(0, MU + 1):
        assigns = list(itertools.product(range(T), repeat=n_unlab))
        wprods = [np.prod([W[s] for s in sig]) if sig else 1.0 for sig in assigns]
        for edges in all_rooted_graph_edge_sets(n_unlab):
            col = np.zeros(T)
            for i in range(T):
                tot = 0.0
                for sig, wp in zip(assigns, wprods):
                    a = (i,) + sig
                    pr = 1.0
                    for (p, q) in edges:
                        pr *= B[a[p]][a[q]]
                        if pr == 0.0:
                            break
                    tot += wp * pr
                col[i] = tot
            cols.append(col)
    return np.array(cols)  # (n_graphs, T)

def atoms_of(P, tol=1e-7):
    T = P.shape[1]
    seen, atoms = [], []
    for i in range(T):
        placed = False
        for idx, rep in enumerate(seen):
            if np.allclose(P[:, i], P[:, rep], atol=tol):
                atoms[idx].append(i); placed = True; break
        if not placed:
            seen.append(i); atoms.append([i])
    return atoms

def twin_free(B, tol=1e-9):
    T = B.shape[0]
    return all(not np.allclose(B[i], B[j], atol=tol)
               for i in range(T) for j in range(i + 1, T))

def W_const_on_atoms(atoms, W, tol=1e-6):
    return all(max(W[a] for a in at) - min(W[a] for a in at) < tol for at in atoms)

def random_tau_symmetric_B(T, tau):
    """Random symmetric B with B[tau x][tau y] = B[x][y], zero diagonal."""
    B = np.zeros((T, T))
    for x in range(T):
        for y in range(x + 1, T):
            orb = set()
            xx, yy = x, y
            for _ in range(2 * T):
                orb.add((min(xx, yy), max(xx, yy)))
                xx, yy = tau[xx], tau[yy]
            if all(B[p][q] == 0.0 for (p, q) in orb):
                val = rng.normal()
                for (p, q) in orb:
                    B[p][q] = B[q][p] = val
    return B

def run(T, MU, n_instances):
    fails, nontrivial, total = 0, 0, 0
    worst = None
    for _ in range(n_instances):
        # random permutation tau (often a transposition or 3-cycle) to seed symmetry
        tau = np.arange(T)
        k = rng.integers(2, T + 1)
        cyc = rng.permutation(T)[:k]
        for a in range(k):
            tau[cyc[a]] = cyc[(a + 1) % k]
        B = random_tau_symmetric_B(T, tau)
        if not twin_free(B):
            continue
        W = rng.uniform(0.3, 3.0, size=T)   # generic, NOT tau-invariant
        P = profile_matrix(B, W, MU)
        atoms = atoms_of(P)
        total += 1
        if any(len(at) > 1 for at in atoms):
            nontrivial += 1
        if not W_const_on_atoms(atoms, W):
            fails += 1
            spread = max(max(W[a] for a in at) - min(W[a] for a in at) for at in atoms)
            if worst is None or spread > worst[0]:
                worst = (spread, B.copy(), W.copy(), atoms)
    return total, nontrivial, fails, worst

if __name__ == "__main__":
    for T in (4, 5, 6):
        for MU in (3, 4):
            total, nontrivial, fails, worst = run(T, MU, n_instances=300)
            print(f"T={T} MU={MU}: instances={total}, "
                  f"with-nontrivial-atom={nontrivial}, "
                  f"W-NONCONST-on-atom (counterexamples)={fails}")
            if worst:
                print("   !!! counterexample spread =", round(worst[0], 5),
                      "W =", np.round(worst[2], 3), "atoms =", worst[3])
