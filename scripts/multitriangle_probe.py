"""Probe: does bounded simple-profile equivalence force the internal-multi-edge
(multi-triangle) gap to vanish?

    gap_c(i,j) = sum_{s,t} W_s W_t * (B(i,s)-B(j,s)) * B(s,t)^c * (B(i,t)+B(j,t))
               = <eps, M^(c) u>_W ,   M^(c) f (s) = sum_t W_t B(s,t)^c f(t).

This is the polarized difference of the multi-triangle probe
sum_{s,t} W_s W_t B(i,s) B(i,t) B(s,t)^c (the simplest probe with an INTERNAL
multi-edge, mult c >= 2).  #70 (Lovasz) implies it must vanish under FULL rpe;
the question is whether a BOUNDED simple-profile battery already forces it
(=> finite identity => constructive Lean target) or only the full closure does.

Method (linearized rigidity, decisive for the W_i=W_j gate):
At a tau=(i j)-symmetric twin-free B with W_i=W_j (so i~j EXACTLY, gap_c=0),
form the Jacobian J of the battery profile-difference map d/dx [P_F(i)-P_F(j)]
over variables x=(B offdiag, W).  Then:
  - if grad(gap_c) lies in row-space(J)  => gap_c is a linear combination of
    simple-profile gradients => LOCALLY FORCED by the battery (residual ~ 0);
  - the least-squares coefficients alpha (grad gap_c = sum_F alpha_F grad P_F)
    name the ACTIVE SEPARATOR graphs.
  - if residual stays away from 0 => not forced at this depth => need bigger
    battery / global machinery.
"""
import itertools
import numpy as np

LETTERS = ['b', 'c', 'd', 'e', 'f', 'g', 'h']

def edge_sets(n):
    V = n + 1
    poss = [(p, q) for p in range(V) for q in range(p + 1, V)]
    for r in range(len(poss) + 1):
        for combo in itertools.combinations(poss, r):
            yield list(combo)

def build_battery(MU):
    bat = []
    for n in range(MU + 1):
        for edges in edge_sets(n):
            bat.append((n, edges))
    return bat

def graph_profile(B, w, n, edges, T):
    if n == 0:
        return np.ones(T)
    subs, ops, has_root = [], [], False
    for k in range(1, n + 1):
        ops.append(w); subs.append(LETTERS[k - 1])
    for (p, q) in edges:
        if p == 0:
            ops.append(B); subs.append('a' + LETTERS[q - 1]); has_root = True
        elif q == 0:
            ops.append(B); subs.append('a' + LETTERS[p - 1]); has_root = True
        else:
            ops.append(B); subs.append(LETTERS[p - 1] + LETTERS[q - 1])
    if has_root:
        return np.einsum(','.join(subs) + '->a', *ops, optimize=True)
    return np.full(T, float(np.einsum(','.join(subs) + '->', *ops, optimize=True)))

def profile_diff_vec(x, T, BAT, iu, nB, i, j):
    B = np.zeros((T, T)); B[iu] = x[:nB]; B = B + B.T
    w = x[nB:]
    out = np.empty(len(BAT))
    for idx, (n, edges) in enumerate(BAT):
        p = graph_profile(B, w, n, edges, T)
        out[idx] = p[i] - p[j]
    return out

def gap_c(x, T, iu, nB, i, j, c):
    B = np.zeros((T, T)); B[iu] = x[:nB]; B = B + B.T
    w = x[nB:]
    eps = B[i] - B[j]
    u = B[i] + B[j]
    Bc = B ** c
    return float((w * eps) @ (Bc @ (w * u)))

def fd_jacobian(fun, x, m, eps=1e-6):
    f0 = fun(x)
    J = np.empty((m, len(x)))
    for k in range(len(x)):
        xp = x.copy(); xp[k] += eps
        J[:, k] = (fun(xp) - f0) / eps
    return J

def fd_grad(fun, x, eps=1e-6):
    f0 = fun(x)
    g = np.empty(len(x))
    for k in range(len(x)):
        xp = x.copy(); xp[k] += eps
        g[k] = (fun(xp) - f0) / eps
    return g

def tau_ij_symmetric_B(T, i, j, rng):
    """B symmetric under tau=(i j): B[tau x][tau y] = B[x][y], zero diagonal."""
    tau = list(range(T)); tau[i], tau[j] = j, i
    B = np.zeros((T, T))
    for x in range(T):
        for y in range(x + 1, T):
            orb = {(min(x, y), max(x, y)),
                   (min(tau[x], tau[y]), max(tau[x], tau[y]))}
            if all(B[p][q] == 0.0 for (p, q) in orb):
                v = rng.normal()
                for (p, q) in orb:
                    B[p][q] = B[q][p] = v
    return B

def run(T, MU, c, trials, seed):
    rng = np.random.default_rng(seed)
    BAT = build_battery(MU)
    iu = np.triu_indices(T, k=1)
    nB = len(iu[0])
    i, j = 0, 1
    resids, names = [], []
    for _ in range(trials):
        B = tau_ij_symmetric_B(T, i, j, rng)
        if len({tuple(np.round(B[r], 6)) for r in range(T)}) != T:
            continue  # not twin-free
        W = rng.uniform(0.5, 2.5, size=T); W[j] = W[i]  # W_i = W_j
        x = np.concatenate([B[iu], W])
        # sanity: i~j exactly on the battery, and gap_c=0 here
        if np.max(np.abs(profile_diff_vec(x, T, BAT, iu, nB, i, j))) > 1e-6:
            continue
        J = fd_jacobian(lambda y: profile_diff_vec(y, T, BAT, iu, nB, i, j), x, len(BAT))
        g = fd_grad(lambda y: gap_c(y, T, iu, nB, i, j, c), x)
        # is g in row-space(J)?  solve  J^T alpha ~= g
        alpha, *_ = np.linalg.lstsq(J.T, g, rcond=None)
        resid = float(np.linalg.norm(J.T @ alpha - g) / (np.linalg.norm(g) + 1e-30))
        resids.append(resid)
        if resid < 1e-4:  # g IS captured: record dominant active separators
            order = np.argsort(-np.abs(alpha))
            top = [(BAT[k], round(float(alpha[k]), 3)) for k in order[:4]]
            names.append(top)
    return resids, names

if __name__ == "__main__":
    for c in (2, 3):
        for T in (4, 5):
            for MU in (3, 4):
                resids, names = run(T, MU, c, trials=40, seed=T * 13 + MU + c)
                if not resids:
                    print(f"c={c} T={T} MU={MU}: no valid symmetric twinfree point", flush=True)
                    continue
                arr = np.array(resids)
                forced = float((arr < 1e-4).mean())
                print(f"c={c} T={T} MU={MU}: pts={len(arr)}  "
                      f"rel-residual of grad(gap) vs profile-gradients: "
                      f"mean={arr.mean():.2e} max={arr.max():.2e}  "
                      f"FORCED-fraction={forced:.2f}", flush=True)
                if names:
                    print(f"    active separators (graph, coeff): {names[0]}", flush=True)
