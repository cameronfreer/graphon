"""Is gap_c a LINEAR COMBINATION of simple-profile differences (a finite identity)?

    gap_c(x) =? sum_F alpha_F (P_F(0,x) - P_F(1,x))   for constants alpha_F, all x,

where gap_c(B,W) = sum_{s,t} W_s W_t (B(0,s)-B(1,s)) B(s,t)^c (B(0,t)+B(1,t))
is the polarized internal-multi-edge (multi-triangle) difference.

If such constant alpha exist, then rpe (all P_F(0)=P_F(1)) forces gap_c=0 -- a
finite, constructive identity at battery depth MU.  Tested by sampling N >> #graphs
random (B,W) and least-squares fitting; rel-residual ~0 (overdetermined system)
=> the identity holds.  GLOBAL, FUNCTIONAL, and NOT vacuous (random non-symmetric
points; gap and profile-diffs are generically nonzero).
"""
import numpy as np
from rpe_weight_fast import build_battery, residual_vec

def gap_c(B, W, T, i, j, c):
    eps = B[i] - B[j]
    u = B[i] + B[j]
    return float((W * eps) @ ((B ** c) @ (W * u)))

def run(T, MU, c, nsamp, seed):
    rng = np.random.default_rng(seed)
    BAT = build_battery(MU)
    D = np.empty((nsamp, len(BAT)))
    y = np.empty(nsamp)
    for s in range(nsamp):
        M = rng.normal(size=(T, T)); B = (M + M.T) / 2; np.fill_diagonal(B, 0.0)
        W = rng.uniform(0.3, 3.0, size=T)
        D[s] = residual_vec(B, W, T, BAT, 0, 1)
        y[s] = gap_c(B, W, T, 0, 1, c)
    alpha, _, _, _ = np.linalg.lstsq(D, y, rcond=None)
    resid = float(np.linalg.norm(D @ alpha - y) / (np.linalg.norm(y) + 1e-30))
    order = np.argsort(-np.abs(alpha))
    top = [(BAT[k], round(float(alpha[k]), 4)) for k in order[:5] if abs(alpha[k]) > 1e-6]
    return resid, top, len(BAT)

if __name__ == "__main__":
    for c in (2, 3):
        for T in (4, 5):
            for MU in (2, 3, 4):
                resid, top, ng = run(T, MU, c, nsamp=500, seed=T * 23 + MU + c)
                forced = resid < 1e-6
                print(f"c={c} T={T} MU={MU} (#graphs={ng}): linfit rel-residual={resid:.2e}  => "
                      f"{'LINEAR COMBO of simple profiles (FORCED)' if forced else 'NOT in simple-profile span'}",
                      flush=True)
                if forced and top:
                    print(f"    separators: {top}", flush=True)
