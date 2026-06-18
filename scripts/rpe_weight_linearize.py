"""Local rigidity test for  rpe 0 1 => W0 = W1.

Take a tau=(0 1)-symmetric twin-free B with W0=W1 (so 0~1 holds exactly).
Linearize the constraint  stuff_0(F) - stuff_1(F) = 0  over the battery in the
variables (delta B offdiag, delta W).  Build the Jacobian J of the residual map
at this point.  The null space of J = first-order moves preserving rpe(0,1).

If every null vector has dW0 = dW1, then W0=W1 is locally forced (rigid).
If some null vector has dW0 != dW1, a counterexample exists arbitrarily close.

We report, over the null space, the max achievable |dW0 - dW1| at unit step.
"""
import itertools
import numpy as np

LETTERS = ['b', 'c', 'd', 'e', 'f']

def edge_sets(n):
    V = n + 1
    poss = [(p, q) for p in range(V) for q in range(p + 1, V)]
    for r in range(len(poss) + 1):
        for c in itertools.combinations(poss, r):
            yield list(c)

def build_battery(MU):
    return [(n, edges) for n in range(MU + 1) for edges in edge_sets(n)]

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

def residual(x, T, BAT, iu, nB, i, j):
    B = np.zeros((T, T)); B[iu] = x[:nB]; B = B + B.T
    w = x[nB:]
    out = np.empty(len(BAT))
    for idx, (n, edges) in enumerate(BAT):
        p = graph_profile(B, w, n, edges, T)
        out[idx] = p[i] - p[j]
    return out

def jacobian(x, T, BAT, iu, nB, i, j, eps=1e-6):
    f0 = residual(x, T, BAT, iu, nB, i, j)
    J = np.empty((len(f0), len(x)))
    for c in range(len(x)):
        xp = x.copy(); xp[c] += eps
        J[:, c] = (residual(xp, T, BAT, iu, nB, i, j) - f0) / eps
    return J, f0

def tau01_symmetric_B(T, rng):
    """B with B(tau x, tau y)=B(x,y) for tau=(0 1); zero diagonal; twin-free-ish."""
    B = np.zeros((T, T))
    B[0, 1] = B[1, 0] = rng.normal()           # the (0,1) edge (its own orbit)
    for k in range(2, T):                       # B(0,k)=B(1,k) forced
        v = rng.normal()
        B[0, k] = B[k, 0] = v
        B[1, k] = B[k, 1] = v
    for p in range(2, T):                        # free symmetric part on {2..}
        for q in range(p + 1, T):
            v = rng.normal()
            B[p, q] = B[q, p] = v
    return B

def run(T, MU, trials, seed):
    rng = np.random.default_rng(seed)
    BAT = build_battery(MU)
    iu = np.triu_indices(T, k=1)
    nB = len(iu[0])
    i, j = 0, 1
    # variable layout: x = [B offdiag (nB)] + [W (T)]
    nvar = nB + T
    # index of W0 and W1 in x:
    w0_idx, w1_idx = nB + 0, nB + 1
    results = []
    for _ in range(trials):
        B = tau01_symmetric_B(T, rng)
        rows = {tuple(np.round(B[r], 6)) for r in range(T)}
        if len(rows) != T:
            continue  # not twin-free
        Wsym = rng.uniform(0.5, 2.5, size=T)
        Wsym[1] = Wsym[0]  # W0 = W1 (tau-symmetric weight) so 0~1 holds
        x = np.concatenate([B[iu], Wsym])
        f0 = residual(x, T, BAT, iu, nB, i, j)
        if np.max(np.abs(f0)) > 1e-6:
            continue  # 0~1 should hold exactly; skip if not (numerical)
        J, _ = jacobian(x, T, BAT, iu, nB, i, j)
        # null space of J
        u, s, vt = np.linalg.svd(J)
        tol = 1e-7 * max(1.0, s[0]) if len(s) else 1e-7
        null_mask = np.array([(s[k] < tol) if k < len(s) else True
                              for k in range(nvar)])
        null = vt[null_mask]  # rows = null basis vectors (length nvar)
        if null.shape[0] == 0:
            results.append(0.0); continue
        # maximize |dW0 - dW1| over unit-norm null vectors:
        # = norm of projection of (e_{w0} - e_{w1}) onto null space
        target = np.zeros(nvar); target[w0_idx] = 1.0; target[w1_idx] = -1.0
        coeffs = null @ target              # components along each null basis vec
        proj = null.T @ coeffs              # projection of target onto null space
        max_dw = float(np.linalg.norm(proj))   # max (dW0-dW1) at unit step in null
        results.append(max_dw)
    return results

if __name__ == "__main__":
    for T in (4, 5, 6):
        for MU in (3, 4):
            res = run(T, MU, trials=60, seed=T * 11 + MU)
            if not res:
                print(f"T={T} MU={MU}: no valid tau-symmetric twinfree point", flush=True)
                continue
            arr = np.array(res)
            print(f"T={T} MU={MU}: valid points={len(arr)}  "
                  f"max |dW0-dW1| over null space: mean={arr.mean():.2e} "
                  f"max={arr.max():.2e}  (0 => locally RIGID => W0=W1 forced)",
                  flush=True)
