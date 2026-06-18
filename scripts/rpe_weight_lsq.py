"""Stronger counterexample search for  rpe i j => W i = W j.

Fix W0 - W1 = GAP (so the two root weights are forced unequal), then use
least-squares to drive the battery rooted-profile mismatch between vertices 0,1
to zero, over variables (B off-diagonal entries, W with W0 := W1 + GAP).

If residual -> ~0 with a twin-free B and positive W, that is a numerical
counterexample (profiles at 0 and 1 agree on the whole battery yet W0 != W1).
"""
import itertools
import numpy as np
from scipy.optimize import least_squares

def edge_sets(n):
    V = n + 1
    poss = [(p, q) for p in range(V) for q in range(p + 1, V)]
    for r in range(len(poss) + 1):
        for c in itertools.combinations(poss, r):
            yield list(c)

def battery(T, MU):
    g = []
    for n in range(MU + 1):
        assigns = list(itertools.product(range(T), repeat=n))
        for e in edge_sets(n):
            g.append((assigns, e))
    return g

def resid_profiles(B, W, T, BAT, i, j):
    out = []
    for assigns, edges in BAT:
        v = [0.0, 0.0]
        for ridx, root in enumerate((i, j)):
            tot = 0.0
            for sig in assigns:
                a = (root,) + sig
                pr = 1.0
                for s in sig:
                    pr *= W[s]
                for (p, q) in edges:
                    pr *= B[a[p]][a[q]]
                    if pr == 0.0:
                        break
                tot += pr
            v[ridx] = tot
        out.append(v[0] - v[1])
    return np.array(out)

def run(T, MU, GAP, restarts, seed):
    rng = np.random.default_rng(seed)
    BAT = battery(T, MU)
    iu = np.triu_indices(T, k=1)
    nB = len(iu[0])
    i, j = 0, 1
    best = None
    for _ in range(restarts):
        # variables: B offdiag (nB), W1..W_{T-1} positive-ish (T-1); W0 = W1 + GAP
        x0 = np.concatenate([rng.normal(scale=1.0, size=nB),
                             rng.uniform(0.5, 2.0, size=T - 1)])
        def residual(x):
            B = np.zeros((T, T)); B[iu] = x[:nB]; B = B + B.T
            Wrest = x[nB:]
            W = np.empty(T)
            W[1:] = Wrest
            W[0] = W[1] + GAP
            r = resid_profiles(B, W, T, BAT, i, j)
            # soft barrier keeping weights positive
            barr = np.maximum(0.05 - W, 0.0) * 3.0
            return np.concatenate([r, barr])
        sol = least_squares(residual, x0, method="lm", max_nfev=4000)
        x = sol.x
        B = np.zeros((T, T)); B[iu] = x[:nB]; B = B + B.T
        W = np.empty(T); W[1:] = x[nB:]; W[0] = W[1] + GAP
        rp = resid_profiles(B, W, T, BAT, i, j)
        mism = float(np.sum(rp * rp))
        rows = [tuple(np.round(B[r], 6)) for r in range(T)]
        tf = len(set(rows)) == T
        wpos = bool(np.all(W > 0.03))
        if tf and wpos and (best is None or mism < best[0]):
            best = (mism, B.copy(), W.copy())
    return best

if __name__ == "__main__":
    for T in (4, 5):
        for GAP in (0.5, 1.0):
            best = run(T, MU=3, GAP=GAP, restarts=120, seed=T * 100 + int(GAP * 10))
            if best is None:
                print(f"T={T} GAP={GAP}: no twinfree/positive candidate", flush=True)
                continue
            mism, B, W = best
            tag = "  *** COUNTEREXAMPLE ***" if mism < 1e-9 else ""
            print(f"T={T} GAP={GAP}: min battery-mismatch = {mism:.3e}  "
                  f"(W0={W[0]:.3f},W1={W[1]:.3f}){tag}", flush=True)
            if mism < 1e-9:
                print("   B =", np.round(B, 5).tolist(), flush=True)
                print("   W =", np.round(W, 5).tolist(), flush=True)
