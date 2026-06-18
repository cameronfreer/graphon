"""FAST counterexample search for  rpe i j => W i = W j  (einsum profiles).

Fix W0 - W1 = GAP and least-squares-drive the battery rooted-profile mismatch
between vertices 0 and 1 to zero over (B offdiag, W[1:]).  Battery = all simple
rooted graphs with <= MU unlabeled vertices.  A residual ~0 with twin-free B and
positive W is a counterexample to the unweighted-root #70 statement.
"""
import itertools
import numpy as np
from scipy.optimize import least_squares

LETTERS = ['b', 'c', 'd', 'e', 'f']

def edge_sets(n):
    V = n + 1
    poss = [(p, q) for p in range(V) for q in range(p + 1, V)]
    for r in range(len(poss) + 1):
        for c in itertools.combinations(poss, r):
            yield list(c)

def build_battery(MU):
    """list of (n, edges, einsum_spec) where einsum_spec tells how to contract."""
    bat = []
    for n in range(MU + 1):
        for edges in edge_sets(n):
            bat.append((n, edges))
    return bat

def graph_profile(B, w, n, edges, T):
    """Vector over roots r in [T] of the rooted profile."""
    if n == 0:
        return np.ones(T)
    subs, ops = [], []
    for k in range(1, n + 1):
        ops.append(w); subs.append(LETTERS[k - 1])
    has_root = False
    for (p, q) in edges:
        if p == 0:
            ops.append(B); subs.append('a' + LETTERS[q - 1]); has_root = True
        elif q == 0:
            ops.append(B); subs.append('a' + LETTERS[p - 1]); has_root = True
        else:
            ops.append(B); subs.append(LETTERS[p - 1] + LETTERS[q - 1])
    if has_root:
        spec = ','.join(subs) + '->a'
        return np.einsum(spec, *ops, optimize=True)
    else:
        spec = ','.join(subs) + '->'
        val = np.einsum(spec, *ops, optimize=True)
        return np.full(T, float(val))

def residual_vec(B, w, T, BAT, i, j):
    out = np.empty(len(BAT))
    for idx, (n, edges) in enumerate(BAT):
        p = graph_profile(B, w, n, edges, T)
        out[idx] = p[i] - p[j]
    return out

def run(T, MU, GAP, restarts, seed):
    rng = np.random.default_rng(seed)
    BAT = build_battery(MU)
    iu = np.triu_indices(T, k=1)
    nB = len(iu[0])
    i, j = 0, 1
    best = None
    for _ in range(restarts):
        x0 = np.concatenate([rng.normal(size=nB), rng.uniform(0.5, 2.0, size=T - 1)])
        def f(x):
            B = np.zeros((T, T)); B[iu] = x[:nB]; B = B + B.T
            w = np.empty(T); w[1:] = x[nB:]; w[0] = w[1] + GAP
            r = residual_vec(B, w, T, BAT, i, j)
            barr = np.maximum(0.05 - w, 0.0) * 5.0
            return np.concatenate([r, barr])
        sol = least_squares(f, x0, method="lm", max_nfev=6000)
        x = sol.x
        B = np.zeros((T, T)); B[iu] = x[:nB]; B = B + B.T
        w = np.empty(T); w[1:] = x[nB:]; w[0] = w[1] + GAP
        rp = residual_vec(B, w, T, BAT, i, j)
        mism = float(rp @ rp)
        rows = {tuple(np.round(B[r], 6)) for r in range(T)}
        tf = len(rows) == T
        wpos = bool(np.all(w > 0.03))
        if tf and wpos and (best is None or mism < best[0]):
            best = (mism, B.copy(), w.copy())
    return best

if __name__ == "__main__":
    for T in (4, 5, 6):
        for MU in (3,):
            for GAP in (0.4, 1.0):
                best = run(T, MU, GAP, restarts=200, seed=T * 17 + int(GAP * 10))
                if best is None:
                    print(f"T={T} MU={MU} GAP={GAP}: no twinfree/positive cand", flush=True)
                    continue
                mism, B, w = best
                ce = mism < 1e-9
                print(f"T={T} MU={MU} GAP={GAP}: min mismatch = {mism:.3e}  "
                      f"W0={w[0]:.3f} W1={w[1]:.3f}{'  *** COUNTEREXAMPLE ***' if ce else ''}",
                      flush=True)
                if ce:
                    print("   B =", np.round(B, 5).tolist(), flush=True)
                    print("   W =", np.round(w, 5).tolist(), flush=True)
