"""Targeted search: minimize battery rooted-profile mismatch between two vertices
i=0, j=1 while PUSHING W0 != W1 and keeping B twin-free, symmetric, zero-diagonal.

If we can drive the profile mismatch to ~0 with |W0 - W1| bounded away from 0,
that is a numerical counterexample to  rpe i j => W i = W j  (hence to
vertexOrbitRel_of_rootedProfileEquiv).  Conversely, persistent inability to do so
(mismatch cannot vanish unless W0->W1) is evidence the implication holds.
"""
import itertools
import numpy as np
from scipy.optimize import minimize

def all_rooted_graph_edge_sets(n_unlab):
    V = n_unlab + 1
    possible = [(p, q) for p in range(V) for q in range(p + 1, V)]
    for r in range(len(possible) + 1):
        for combo in itertools.combinations(possible, r):
            yield list(combo)

BATTERY = {}
def battery(T, MU):
    if (T, MU) in BATTERY:
        return BATTERY[(T, MU)]
    graphs = []
    for n_unlab in range(0, MU + 1):
        assigns = list(itertools.product(range(T), repeat=n_unlab))
        for edges in all_rooted_graph_edge_sets(n_unlab):
            graphs.append((n_unlab, assigns, edges))
    BATTERY[(T, MU)] = graphs
    return graphs

def profile_pair(B, W, T, MU, i, j):
    """Return concatenated (profile_i - profile_j) over the battery."""
    diffs = []
    for n_unlab, assigns, edges in battery(T, MU):
        for root in (i, j):
            pass
    out = []
    for n_unlab, assigns, edges in battery(T, MU):
        vals = {}
        for root in (i, j):
            tot = 0.0
            for sig in assigns:
                a = (root,) + sig
                wp = 1.0
                for s in sig:
                    wp *= W[s]
                pr = wp
                for (p, q) in edges:
                    pr *= B[a[p]][a[q]]
                    if pr == 0.0:
                        break
                tot += pr
            vals[root] = tot
        out.append(vals[i] - vals[j])
    return np.array(out)

def pack(B, W, T):
    iu = np.triu_indices(T, k=1)
    return np.concatenate([B[iu], W])

def unpack(x, T):
    iu = np.triu_indices(T, k=1)
    B = np.zeros((T, T))
    nB = len(iu[0])
    B[iu] = x[:nB]
    B = B + B.T
    W = x[nB:]
    return B, W

def run(T=4, MU=3, gap=0.7, restarts=40, seed=0):
    rng = np.random.default_rng(seed)
    i, j = 0, 1
    best = None
    for _ in range(restarts):
        x0 = np.concatenate([rng.normal(size=T * (T - 1) // 2),
                             rng.uniform(0.5, 2.5, size=T)])
        def obj(x):
            B, W = unpack(x, T)
            d = profile_pair(B, W, T, MU, i, j)
            mism = np.sum(d * d)
            # push W0 - W1 to be at least `gap`; penalize W<=0
            wpen = (max(0.0, gap - (W[0] - W[1])) ** 2)
            negpen = np.sum(np.minimum(W - 0.05, 0.0) ** 2) * 10
            return mism + 5.0 * wpen + negpen
        res = minimize(obj, x0, method="Nelder-Mead",
                       options=dict(maxiter=20000, xatol=1e-9, fatol=1e-12))
        B, W = unpack(res.x, T)
        d = profile_pair(B, W, T, MU, i, j)
        mism = float(np.sum(d * d))
        # twin-free check
        rows = [tuple(np.round(B[r], 6)) for r in range(T)]
        tf = len(set(rows)) == T
        wpos = bool(np.all(W > 0.02))
        cand = (mism, abs(W[0] - W[1]), tf, wpos, B.copy(), W.copy())
        if tf and wpos and (best is None or mism < best[0]):
            best = cand
    return best

if __name__ == "__main__":
    for gap in (0.5, 1.0):
        b = run(T=4, MU=3, gap=gap, restarts=60, seed=1)
        if b:
            mism, dw, tf, wpos, B, W = b
            print(f"gap>={gap}: best battery-mismatch(sum sq) = {mism:.3e}, "
                  f"|W0-W1| = {dw:.4f}, twinfree={tf}, Wpos={wpos}")
            if mism < 1e-10 and dw > 0.1:
                print("  *** NUMERICAL COUNTEREXAMPLE ***")
                print("  B =", np.round(B, 4).tolist())
                print("  W =", np.round(W, 4).tolist())
        else:
            print(f"gap>={gap}: no twin-free/positive candidate found")
