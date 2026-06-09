#!/usr/bin/env python3
"""
Falsification search for `classwise_sqMoment_descends` (Graphon/SimpleRank.lean, #70).

CONJECTURE under test (K=1 simple rank theorem residue):
  If vertices i, j of a weighted graph (B symmetric real, W > 0, twin-free)
  are ROOTED-PROFILE EQUIVALENT (equal rooted simple-graph evaluations
  P_F(v) = sum_{sigma} prod_u W(sigma_u) * prod_{(a,b) in F} B(tau_a, tau_b)
  for ALL rooted simple graphs F), then their W-weighted square moments agree:
      sum_t W_t * B[i,t]^2  =  sum_t W_t * B[j,t]^2
  (and classwise within each profile-atom).

NOTE the relation is the PROFILE-ATOM partition, NOT the orbit partition.
For 0/1 matrices B the conjecture is already a theorem (B^2 = B makes
simple = multigraph evaluations, and the multigraph Lemma 2.4 chain is
proved), so the search focuses on NON-Boolean real B, including negatives.

Search strategy (generic random instances have singleton atoms, which test
nothing): numerically OPTIMIZE (B, W) so that a fixed vertex pair (0, 1)
agrees on every rooted connected simple-graph observable with <= OPT_M
unlabeled vertices, while keeping the square-moment gap >= margin and the
pair twin-free. A successful optimum is then re-verified against the larger
observable family (<= VERIFY_M unlabeled). Outcomes:

  - eq -> 0 with gap >= margin AND survives verification: COUNTEREXAMPLE
    candidate (=> #70 as stated false or needs stronger hypotheses).
  - eq -> 0 at OPT_M but a VERIFY_M observable separates the pair: that
    observable is exactly the "missing algebraic identity" data (report it).
  - eq bounded away from 0 across all starts: evidence the conjecture holds.

Usage: python3 scripts/falsify_classwise_sqmoment.py [--T 5] [--starts 20]
       [--opt-m 3] [--verify-m 4] [--seed 0] [--maxiter 250]
"""

import argparse
import sys
from itertools import permutations

import numpy as np
from scipy.optimize import least_squares, minimize


def flushprint(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


# ---------------------------------------------------------------- graphs

def _connected(n_verts, edges):
    if n_verts == 1:
        return True
    adj = [[] for _ in range(n_verts)]
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    seen = {0}
    stack = [0]
    while stack:
        u = stack.pop()
        for v in adj[u]:
            if v not in seen:
                seen.add(v)
                stack.append(v)
    return len(seen) == n_verts


def rooted_graphs(max_m):
    """All connected rooted simple graphs with m <= max_m unlabeled vertices.

    Vertex 0 is the root; vertices 1..m are unlabeled. Returns a list of
    (m, edges). Isomorphic duplicates are kept (harmless: identical rows).
    Disconnected graphs are omitted: components without the root contribute
    a root-independent constant factor, and root-gluings multiply profiles,
    so connected graphs already determine the separation behaviour.
    """
    out = [(0, [])]  # empty graph: constant observable 1
    for m in range(1, max_m + 1):
        nv = m + 1
        pairs = [(a, b) for a in range(nv) for b in range(a + 1, nv)]
        for mask in range(1, 1 << len(pairs)):
            edges = [pairs[k] for k in range(len(pairs)) if (mask >> k) & 1]
            if _connected(nv, edges):
                out.append((m, edges))
    return out


_SIG_CACHE = {}


def _assignments(T, m):
    key = (T, m)
    if key not in _SIG_CACHE:
        _SIG_CACHE[key] = np.array(list(np.ndindex(*([T] * m))), dtype=np.intp)
    return _SIG_CACHE[key]


def rooted_profiles(B, W, graphs, T):
    """Observable matrix O[g, v] = P_{F_g}(v), vectorized over assignments."""
    rows = []
    for m, edges in graphs:
        if m == 0:
            rows.append(np.ones(T))
            continue
        sig = _assignments(T, m)            # (T^m, m)
        wprod = np.prod(W[sig], axis=1)     # (T^m,)
        scal = np.ones(len(sig))
        rootfac = np.ones((len(sig), T))
        for a, b in edges:
            if a == 0:
                rootfac *= B[:, sig[:, b - 1]].T
            else:
                scal *= B[sig[:, a - 1], sig[:, b - 1]]
        rows.append((wprod * scal) @ rootfac)
    return np.array(rows)


# ---------------------------------------------------------------- structure

def atom_partition(O, tol=1e-8):
    """Partition vertices by near-equality of all observable columns."""
    T = O.shape[1]
    scale = 1.0 + np.abs(O).max(axis=1, keepdims=True)
    On = O / scale
    atoms = []
    assigned = [False] * T
    for v in range(T):
        if assigned[v]:
            continue
        cls = [v]
        assigned[v] = True
        for w in range(v + 1, T):
            if not assigned[w] and np.max(np.abs(On[:, v] - On[:, w])) < tol:
                cls.append(w)
                assigned[w] = True
        atoms.append(cls)
    return atoms


def orbit_partition(B, W, tol=1e-9):
    """Aut(B, W)-orbits by brute force over permutations (T <= 7)."""
    T = len(W)
    parent = list(range(T))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for perm in permutations(range(T)):
        p = np.array(perm)
        if np.max(np.abs(W[p] - W)) > tol:
            continue
        if np.max(np.abs(B[np.ix_(p, p)] - B)) > tol:
            continue
        for v in range(T):
            a, b = find(v), find(perm[v])
            if a != b:
                parent[a] = b
    classes = {}
    for v in range(T):
        classes.setdefault(find(v), []).append(v)
    return list(classes.values())


def classwise_sq_report(B, W, atoms):
    """Max within-atom square-moment discrepancy over all atoms/pairs."""
    worst = 0.0
    detail = None
    for C in atoms:
        for cls in atoms:
            for idx in range(len(cls)):
                for jdx in range(idx + 1, len(cls)):
                    i, j = cls[idx], cls[jdx]
                    mi = sum(W[t] * B[i, t] ** 2 for t in C)
                    mj = sum(W[t] * B[j, t] ** 2 for t in C)
                    if abs(mi - mj) > worst:
                        worst = abs(mi - mj)
                        detail = (i, j, C, mi, mj)
    return worst, detail


def min_row_distance(B, pair=None):
    T = B.shape[0]
    d = np.inf
    for a in range(T):
        for b in range(a + 1, T):
            if pair is not None and (a, b) != pair:
                continue
            d = min(d, np.max(np.abs(B[a] - B[b])))
    return d


# ---------------------------------------------------------------- optimizer

def unpack(x, T):
    nb = T * (T + 1) // 2
    Bv, W = x[:nb], x[nb:]
    B = np.zeros((T, T))
    iu = np.triu_indices(T)
    B[iu] = Bv
    B = B + B.T - np.diag(np.diag(B))
    return B, W


def pack(B, W, T):
    iu = np.triu_indices(T)
    return np.concatenate([B[iu], W])


def objective(x, T, graphs, margin, lam, twin_floor):
    B, W = unpack(x, T)
    O = rooted_profiles(B, W, graphs, T)
    scale = 1.0 + np.abs(O[:, 0]) + np.abs(O[:, 1])
    eq = float(np.sum(((O[:, 0] - O[:, 1]) / scale) ** 2))
    gap = float(np.sum(W * B[0] ** 2) - np.sum(W * B[1] ** 2))
    pen_gap = max(0.0, margin - abs(gap)) ** 2
    pen_twin = max(0.0, twin_floor - min_row_distance(B)) ** 2
    return eq + lam * pen_gap + 100.0 * pen_twin


def run_optimize(T, graphs_opt, graphs_verify, starts, maxiter, seed,
                 margin=0.5, lam=10.0, twin_floor=0.05):
    rng = np.random.default_rng(seed)
    nb = T * (T + 1) // 2
    bounds = [(-1.5, 1.5)] * nb + [(0.3, 3.0)] * T
    best = None
    for s in range(starts):
        B0 = rng.uniform(-1.0, 1.0, (T, T))
        B0 = (B0 + B0.T) / 2
        W0 = rng.uniform(0.5, 2.0, T)
        x0 = pack(B0, W0, T)
        res = minimize(objective, x0, args=(T, graphs_opt, margin, lam, twin_floor),
                       method='L-BFGS-B', bounds=bounds,
                       options={'maxiter': maxiter, 'maxfun': 10 * maxiter * len(x0)})
        B, W = unpack(res.x, T)
        O = rooted_profiles(B, W, graphs_opt, T)
        scale = 1.0 + np.abs(O[:, 0]) + np.abs(O[:, 1])
        eq = float(np.sum(((O[:, 0] - O[:, 1]) / scale) ** 2))
        gap = float(np.sum(W * B[0] ** 2) - np.sum(W * B[1] ** 2))
        rec = (eq, abs(gap), res.fun, B, W)
        if best is None or (eq, -abs(gap)) < (best[0], -best[1]):
            best = rec
        flushprint(f"  start {s:3d}: eq-residual {eq:.3e}  |sq-gap| {abs(gap):.4f}  "
                   f"obj {res.fun:.3e}")
        if eq < 1e-14 and abs(gap) > 0.9 * margin:
            flushprint("  *** optimizer reached profile equality with sq gap "
                       "— verifying against larger observable family ***")
            verify_candidate(B, W, graphs_verify, T)
    if best is not None:
        flushprint(f"  BEST over {starts} starts: eq-residual {best[0]:.3e}  "
                   f"|sq-gap| {best[1]:.4f}")
        if best[0] > 1e-10:
            flushprint("  -> no candidate found at this size: profile-equality "
                       "constraints resist the square-moment gap (evidence FOR "
                       "the conjecture).")
    return best


def verify_candidate(B, W, graphs_verify, T):
    """Re-test a candidate pair (0,1) against the larger family; report the
    separating observable if one exists (= the missing-identity data)."""
    O = rooted_profiles(B, W, graphs_verify, T)
    scale = 1.0 + np.abs(O[:, 0]) + np.abs(O[:, 1])
    diffs = np.abs(O[:, 0] - O[:, 1]) / scale[:, 0] if scale.ndim > 1 \
        else np.abs(O[:, 0] - O[:, 1]) / scale
    worst = int(np.argmax(diffs))
    flushprint(f"    verification: max normalized profile diff over "
               f"{len(graphs_verify)} observables = {diffs[worst]:.3e}")
    if diffs[worst] > 1e-7:
        m, edges = graphs_verify[worst]
        flushprint(f"    SEPARATED by observable #{worst}: m={m}, edges={edges}")
        flushprint("    -> not a counterexample; this graph is the missing-"
                   "identity witness for this instance.")
        return False
    atoms = atom_partition(O)
    orbits = orbit_partition(B, W)
    worst_sq, det = classwise_sq_report(B, W, atoms)
    flushprint(f"    COUNTEREXAMPLE CANDIDATE: atoms {atoms} orbits {orbits}")
    flushprint(f"    max classwise sq discrepancy {worst_sq:.6f} detail {det}")
    flushprint(f"    B=\n{np.array2string(B, precision=6)}\n    W={W}")
    return True


def lm_residuals(x, T, graphs, want_gap):
    """Residual vector for least_squares: normalized profile diffs at the
    pair (0, 1), plus (gap - want_gap) when want_gap is not None."""
    B, W = unpack(x, T)
    O = rooted_profiles(B, W, graphs, T)
    sc = 1.0 + np.abs(O[:, 0]) + np.abs(O[:, 1])
    r = (O[:, 0] - O[:, 1]) / sc
    if want_gap is not None:
        gap = float(np.sum(W * B[0] ** 2) - np.sum(W * B[1] ** 2))
        r = np.append(r, gap - want_gap)
    return r


def lm_solve(T, working, want_gap, x0, lo, hi, max_nfev=2000):
    """Levenberg-Marquardt-style solve of the equality system. Returns
    (profile-equality residual sum of squares, solution point). Calibration:
    with want_gap=None (solutions exist, e.g. automorphism points) this
    reaches ~1e-30; an L-BFGS penalty formulation stalls at ~1e-7, which is
    why the LM engine is the search instrument of record."""
    res = least_squares(lm_residuals, x0, args=(T, working, want_gap),
                        bounds=(lo, hi), method='trf', xtol=3e-16, ftol=3e-16,
                        gtol=3e-16, max_nfev=max_nfev)
    eq = float(np.sum(res.fun[:len(working)] ** 2))
    return eq, res.x


def run_adversarial(T, graphs_opt, graphs_verify, rounds, starts, seed,
                    want_gap=0.5, w_lo=0.05, eq_zero=1e-22, eq_stuck=1e-18):
    """LM cutting-plane loop: solve the equality system on a working set,
    verify on the full family, add the worst separating observable, repeat.

    EMPIRICAL FINDING (2026-06-09, T=4/T=5): the m<=3 system WITH the
    square-moment gap is exactly solvable (eq ~ 1e-30) — small observable
    families do NOT pin the square moment — but every solution found is
    separated by some CYCLIC m=4 observable (never a tree, consistent with
    `first_moment_descends_of_rootedProfileEquiv`). The loop decides whether
    the full m<=4 family pins it.

    Outcomes: 'infeasible' (residual stuck above eq_stuck after extra
    restarts: evidence FOR the conjecture, with the working-set size at
    onset), 'candidate' (survives the whole verification family: check at
    m=5 next), or 'exhausted-rounds'."""
    rng = np.random.default_rng(seed)
    nb = T * (T + 1) // 2
    lo = np.array([-1.5] * nb + [w_lo] * T)
    hi = np.array([1.5] * nb + [3.0] * T)
    working = list(graphs_opt)
    x_warm = None
    for rd in range(rounds):
        best = None
        for s in range(starts):
            if x_warm is not None and s == 0:
                x0 = x_warm
            else:
                B0 = rng.uniform(-1.0, 1.0, (T, T))
                B0 = (B0 + B0.T) / 2
                W0 = rng.uniform(0.5, 2.0, T)
                x0 = pack(B0, W0, T)
            eq, x = lm_solve(T, working, want_gap, x0, lo, hi)
            if best is None or eq < best[0]:
                best = (eq, x)
            if eq < eq_zero:
                break
        eq, x = best
        if eq > eq_stuck:
            # harder attempt before declaring infeasibility
            for _ in range(3 * starts):
                B0 = rng.uniform(-1.0, 1.0, (T, T))
                B0 = (B0 + B0.T) / 2
                W0 = rng.uniform(0.5, 2.0, T)
                eq2, x2 = lm_solve(T, working, want_gap, pack(B0, W0, T),
                                   lo, hi, max_nfev=4000)
                if eq2 < eq:
                    eq, x = eq2, x2
                if eq < eq_zero:
                    break
        x_warm = x
        B, W = unpack(x, T)
        if eq > eq_stuck:
            flushprint(f"  round {rd}: STUCK at eq {eq:.3e} with "
                       f"{len(working)} constraints — infeasibility onset "
                       "(evidence FOR the conjecture)")
            return ('infeasible', rd, len(working), eq)
        gap = float(np.sum(W * B[0] ** 2) - np.sum(W * B[1] ** 2))
        Ov = rooted_profiles(B, W, graphs_verify, T)
        sc = 1.0 + np.abs(Ov[:, 0]) + np.abs(Ov[:, 1])
        diffs = np.abs(Ov[:, 0] - Ov[:, 1]) / sc
        worst = int(np.argmax(diffs))
        flushprint(f"  round {rd:3d}: working {len(working):4d}  eq {eq:.3e}  "
                   f"|gap| {abs(gap):.3f}  mindist {min_row_distance(B):.3f}  "
                   f"worst-verify {diffs[worst]:.3e}  "
                   f"(m={graphs_verify[worst][0]}, "
                   f"{len(graphs_verify[worst][1])} edges)")
        if diffs[worst] < 1e-9:
            flushprint("  *** survives the full verification family — "
                       "COUNTEREXAMPLE CANDIDATE ***")
            np.save('/tmp/cand_B.npy', B)
            np.save('/tmp/cand_W.npy', W)
            verify_candidate(B, W, graphs_verify, T)
            return ('candidate', rd, len(working), B, W)
        working.append(graphs_verify[worst])
    flushprint("  adversarial loop exhausted its round budget without a "
               "surviving candidate or a proof of infeasibility.")
    return ('exhausted-rounds', rounds, len(working), None)


# ---------------------------------------------------------------- modes

def run_sanity(T, graphs, seed):
    """Instance with a forced automorphism (swap 0,1): the pair must land in
    one atom and the classwise square moments must agree."""
    rng = np.random.default_rng(seed)
    B = rng.uniform(-1.0, 1.0, (T, T))
    B = (B + B.T) / 2
    p = np.arange(T)
    p[0], p[1] = 1, 0
    B = (B + B[np.ix_(p, p)]) / 2
    W = rng.uniform(0.5, 2.0, T)
    W = (W + W[p]) / 2
    O = rooted_profiles(B, W, graphs, T)
    atoms = atom_partition(O)
    orbits = orbit_partition(B, W)
    worst, det = classwise_sq_report(B, W, atoms)
    in_same = any(0 in C and 1 in C for C in atoms)
    flushprint(f"  atoms {atoms}  orbits {orbits}")
    flushprint(f"  pair (0,1) same atom: {in_same};  "
               f"max classwise sq discrepancy {worst:.2e}")
    assert in_same and worst < 1e-8, "sanity failure!"
    flushprint("  sanity OK (orbit pair => atom pair => classwise sq equal)")


def run_random(T, graphs, trials, seed):
    """Generic random instances: expect singleton atoms (vacuous pass)."""
    rng = np.random.default_rng(seed)
    nontrivial = 0
    for _ in range(trials):
        B = rng.uniform(-1.0, 1.0, (T, T))
        B = (B + B.T) / 2
        W = rng.uniform(0.5, 2.0, T)
        O = rooted_profiles(B, W, graphs, T)
        atoms = atom_partition(O)
        worst, det = classwise_sq_report(B, W, atoms)
        if any(len(C) > 1 for C in atoms):
            nontrivial += 1
            flushprint(f"  nontrivial atoms {atoms}  worst sq diff {worst:.2e}")
            if worst > 1e-7:
                flushprint(f"  !!! VIOLATION on random instance: {det}")
    flushprint(f"  {trials} random instances, {nontrivial} with nontrivial atoms "
               "(generic instances are expected to have singleton atoms)")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--T', type=int, default=5)
    ap.add_argument('--starts', type=int, default=20)
    ap.add_argument('--opt-m', type=int, default=3)
    ap.add_argument('--verify-m', type=int, default=4)
    ap.add_argument('--maxiter', type=int, default=250)
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--random-trials', type=int, default=200)
    ap.add_argument('--adv-rounds', type=int, default=12)
    args = ap.parse_args()

    graphs_opt = rooted_graphs(args.opt_m)
    graphs_verify = rooted_graphs(args.verify_m)
    flushprint(f"observables: {len(graphs_opt)} (m<={args.opt_m}) for optimization, "
               f"{len(graphs_verify)} (m<={args.verify_m}) for verification")

    flushprint(f"\n=== sanity (T={args.T}) ===")
    run_sanity(args.T, graphs_opt, args.seed)

    flushprint(f"\n=== random scan (T={args.T}) ===")
    run_random(args.T, graphs_opt, args.random_trials, args.seed + 1)

    flushprint(f"\n=== LM adversarial cutting-plane search (T={args.T}, pair (0,1)) ===")
    run_adversarial(args.T, graphs_opt, graphs_verify, args.adv_rounds,
                    max(4, args.starts // 4), args.seed + 3)


if __name__ == '__main__':
    main()
