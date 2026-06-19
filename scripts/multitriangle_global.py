"""GLOBAL test (the correct one): can simple-profile equivalence coexist with a
NONZERO internal-multi-edge gap?

    gap_c = sum_{s,t} W_s W_t (B(i,s)-B(j,s)) B(s,t)^c (B(i,t)+B(j,t))   (i=0,j=1)

Pin gap_c ~ 1 and least-squares-drive the battery simple-profile mismatch
(P_F(0)-P_F(1) over all simple rooted graphs with <= MU unlabeled vertices) to 0,
over FREE (B offdiag, W).  A solution with mismatch ~ 0, twin-free B, W>0 is a
candidate counterexample (rpe up to depth MU, yet gap_c != 0).  Survivors are
re-tested at MU+1, MU+2 (the W_i=W_j gate showed MU=2 artifacts that split at MU=3).

Decision:
  - mismatch stays bounded away from 0  => gap_c FORCED at this depth (descent holds);
  - mismatch -> 0 and SURVIVES higher MU => genuine counterexample (descent false
    at bounded depth => needs global machinery).
"""
import itertools
import numpy as np
from scipy.optimize import least_squares
from rpe_weight_fast import build_battery, graph_profile, residual_vec

def gap_c(B, W, T, i, j, c):
    eps = B[i] - B[j]
    u = B[i] + B[j]
    Bc = B ** c
    return float((W * eps) @ (Bc @ (W * u)))

def run(T, MU, c, restarts, seed, lam=3.0):
    rng = np.random.default_rng(seed)
    BAT = build_battery(MU)
    iu = np.triu_indices(T, k=1)
    nB = len(iu[0])
    i, j = 0, 1
    best = None
    for _ in range(restarts):
        x0 = np.concatenate([rng.normal(size=nB), rng.uniform(0.5, 2.0, size=T)])
        def f(x):
            B = np.zeros((T, T)); B[iu] = x[:nB]; B = B + B.T
            W = x[nB:]
            r = residual_vec(B, W, T, BAT, i, j)
            g = gap_c(B, W, T, i, j, c)
            barr = np.maximum(0.05 - W, 0.0) * 5.0
            return np.concatenate([r, [np.sqrt(lam) * (g - 1.0)], barr])
        sol = least_squares(f, x0, method="lm", max_nfev=8000)
        x = sol.x
        B = np.zeros((T, T)); B[iu] = x[:nB]; B = B + B.T
        W = x[nB:]
        mism = float(residual_vec(B, W, T, BAT, i, j) @ residual_vec(B, W, T, BAT, i, j))
        g = gap_c(B, W, T, i, j, c)
        tf = len({tuple(np.round(B[r], 6)) for r in range(T)}) == T
        wpos = bool(np.all(W > 0.03))
        # candidate: profiles match (small mism) AND gap nonzero
        if tf and wpos and abs(g) > 0.3 and (best is None or mism < best[0]):
            best = (mism, abs(g), B.copy(), W.copy())
    return best, iu, nB

if __name__ == "__main__":
    for c in (2, 3):
        for T in (4, 5):
            for MU in (3,):
                best, iu, nB = run(T, MU, c, restarts=200, seed=T * 7 + c)
                if best is None:
                    print(f"c={c} T={T} MU={MU}: no candidate (could not pin gap)", flush=True)
                    continue
                mism, g, B, W = best
                # re-test at higher MU
                higher = {}
                for MU2 in (MU + 1, MU + 2):
                    BAT2 = build_battery(MU2)
                    r = residual_vec(B, W, T, BAT2, 0, 1)
                    higher[MU2] = float(r @ r)
                surv = mism < 1e-9 and all(v < 1e-7 for v in higher.values())
                print(f"c={c} T={T} MU={MU}: best mismatch@MU{MU}={mism:.2e} |gap|={g:.3f} "
                      f"| mismatch@MU{MU+1}={higher[MU+1]:.2e} @MU{MU+2}={higher[MU+2]:.2e} "
                      f"| SURVIVES(real CE)={surv}", flush=True)
