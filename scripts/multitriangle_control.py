"""Control for multitriangle_probe.py: is the 'gap_c is forced' result MEANINGFUL,
or is rowspace(J) already the whole tau-odd space (=> every tau-odd observable
trivially 'forced'; test vacuous)?

At a tau=(0 1)-symmetric twin-free point with W0=W1 (i~j via tau), we compare,
against rowspace(J) (J = Jacobian of the simple-profile-difference battery):
  - residual of grad(gap_c)              [the multi-triangle observable]
  - residual of RANDOM tau-odd directions [control]
  - rank(J) vs dim(tau-odd subspace of x)

If random tau-odd directions have LARGE residual while grad(gap_c) ~ 0, the test
discriminates and gap_c is genuinely captured by the simple-profile battery.
If random tau-odd also ~ 0, rowspace(J) = full tau-odd space and the result is
vacuous.
"""
import itertools
import numpy as np
from multitriangle_probe import (build_battery, profile_diff_vec, gap_c,
                                  fd_jacobian, fd_grad, tau_ij_symmetric_B)

def tau_perm_on_x(T, i, j, iu):
    """Permutation of the x=(B offdiag, W) coordinates induced by tau=(i j)."""
    tau = list(range(T)); tau[i], tau[j] = j, i
    pairs = list(zip(iu[0].tolist(), iu[1].tolist()))
    index = {(a, b): k for k, (a, b) in enumerate(pairs)}
    nB = len(pairs)
    perm = np.empty(nB + T, dtype=int)
    for k, (a, b) in enumerate(pairs):
        ta, tb = tau[a], tau[b]
        perm[k] = index[(min(ta, tb), max(ta, tb))]
    for a in range(T):
        perm[nB + a] = nB + tau[a]
    return perm

def residual_vs_rowspace(J, g):
    alpha, *_ = np.linalg.lstsq(J.T, g, rcond=None)
    return float(np.linalg.norm(J.T @ alpha - g) / (np.linalg.norm(g) + 1e-30))

def run(T, MU, c, trials, seed):
    rng = np.random.default_rng(seed)
    BAT = build_battery(MU)
    iu = np.triu_indices(T, k=1)
    nB = len(iu[0]); nvar = nB + T
    i, j = 0, 1
    perm = tau_perm_on_x(T, i, j, iu)
    gap_res, ctrl_res, ranks, odd_dims = [], [], [], []
    for _ in range(trials):
        B = tau_ij_symmetric_B(T, i, j, rng)
        if len({tuple(np.round(B[r], 6)) for r in range(T)}) != T:
            continue
        W = rng.uniform(0.5, 2.5, size=T); W[j] = W[i]
        x = np.concatenate([B[iu], W])
        if np.max(np.abs(profile_diff_vec(x, T, BAT, iu, nB, i, j))) > 1e-6:
            continue
        J = fd_jacobian(lambda y: profile_diff_vec(y, T, BAT, iu, nB, i, j), x, len(BAT))
        g = fd_grad(lambda y: gap_c(y, T, iu, nB, i, j, c), x)
        gap_res.append(residual_vs_rowspace(J, g))
        # dim of tau-odd subspace of x: eigenvalue -1 multiplicity of perm matrix
        odd_dim = sum(1 for k in range(nvar) if perm[k] != k) // 2
        odd_dims.append(odd_dim)
        ranks.append(int(np.linalg.matrix_rank(J, tol=1e-7)))
        # control: random tau-odd directions
        for _ in range(3):
            v = rng.normal(size=nvar)
            v_odd = 0.5 * (v - v[perm])   # antisymmetrize under tau
            if np.linalg.norm(v_odd) < 1e-9:
                continue
            ctrl_res.append(residual_vs_rowspace(J, v_odd))
    return (np.array(gap_res), np.array(ctrl_res),
            np.array(ranks), np.array(odd_dims))

if __name__ == "__main__":
    for c in (2, 3):
        for T in (4, 5):
            for MU in (3, 4):
                gap_res, ctrl_res, ranks, odd_dims = run(T, MU, c, trials=30,
                                                         seed=T * 31 + MU + c)
                if len(gap_res) == 0:
                    print(f"c={c} T={T} MU={MU}: no valid points", flush=True)
                    continue
                print(f"c={c} T={T} MU={MU}: rank(J)~{int(ranks.mean())} "
                      f"dim(tau-odd)~{int(odd_dims.mean())}  "
                      f"gap-residual={gap_res.mean():.2e}  "
                      f"RANDOM-tau-odd-residual mean={ctrl_res.mean():.3f} "
                      f"min={ctrl_res.min():.3f}", flush=True)
