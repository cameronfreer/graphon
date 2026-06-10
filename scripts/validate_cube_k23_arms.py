#!/usr/bin/env python3
"""
Numerical validation of the K_{2,3}-ARMS proof of cube-moment descent
(#70, `cubeMoment_descends_of_rootedProfileEquiv` in Graphon/CycleKrylov.lean).

THEOREM (discovered & validated 2026-06-10; formalization pending; mechanism
uniform in k — at k = 2 it specializes to the PROVED rooted-cycle argument).
Let B be symmetric, W > 0, i ~rpe j. With eps = B i - B j, u = B i + B j,
M = B D_W (self-adjoint wrt <.,.>_W), T3(f,g,h) = sum_t W t f g h:

1. POLARIZATION + ARMS IDENTITY: for the rooted K_{2,3}-with-arms graph
   (root adjacent to anchors t1,t2,t3; internal hub y; arm l a path of
   length a_l >= 1 from t_l to y — a SIMPLE graph),
     P(i) - P(j) = (1/4) * sum_{|S| odd} T3(slots: M^{a_l} eps for l in S,
                                                  M^{a_l} u   for l not in S),
   exactly. Hence rpe kills these for all arm lengths.
2. COMMON EXPANSION (direct-sum trick): (eps, u) lies in Im(M (+) M), which is
   self-adjoint, so by the k=2 projection lemma applied to E (+) E there are
   COMMON coefficients c_q with  eps = sum_{q>=1} c_q M^q eps  AND
   u = sum_{q>=1} c_q M^q u  simultaneously.
3. RECONSTRUCTION: gap_3 = (1/4) sum_{|S| odd} T3(eps[S], u[S^c])
   = sum_{a1,a2,a3 >= 1} c_{a1} c_{a2} c_{a3} * ObsDiff(a1,a2,a3) = 0.  QED

This bypasses the wedge/theta "residual branch" entirely: the right family is
K_{2,k}-with-arms, found empirically as the top m=4 separator (the four
isomorphic rooted K_{2,3}'s) of an exact m<=3 cube-gap solution at T=5.

Usage: python3 scripts/validate_cube_k23_arms.py [--T 5] [--seed 271]
"""

import argparse
import sys
from itertools import product as iproduct

import numpy as np
from scipy.optimize import least_squares

sys.path.insert(0, 'scripts')
from falsify_classwise_sqmoment import (rooted_graphs, rooted_profiles, unpack,
                                        pack, flushprint)


def residuals(x, T, graphs, want_gap):
    B, W = unpack(x, T)
    O = rooted_profiles(B, W, graphs, T)
    sc = 1.0 + np.abs(O[:, 0]) + np.abs(O[:, 1])
    r = (O[:, 0] - O[:, 1]) / sc
    gap = float(np.sum(W * B[0] ** 3) - np.sum(W * B[1] ** 3))
    return np.append(r, gap - want_gap)


def k23_graph(a):
    """Rooted K_{2,3} with arm lengths a = (a1,a2,a3): root 0, anchors 1..3,
    hub 4, arm internals appended."""
    edges = [(0, 1), (0, 2), (0, 3)]
    nxt = 5
    for l, al in enumerate(a):
        prev = 1 + l
        for _ in range(al - 1):
            edges.append(tuple(sorted((prev, nxt))))
            prev = nxt
            nxt += 1
        edges.append(tuple(sorted((prev, 4))))
    return (nxt - 1, sorted(set(edges)))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--T', type=int, default=5)
    ap.add_argument('--seed', type=int, default=271)
    ap.add_argument('--starts', type=int, default=15)
    args = ap.parse_args()
    T = args.T

    # find an m<=3-exact instance with CUBE gap pinned to 0.5
    graphs3 = rooted_graphs(3)
    rng = np.random.default_rng(args.seed)
    nb = T * (T + 1) // 2
    lo = np.array([-1.5] * nb + [0.05] * T)
    hi = np.array([1.5] * nb + [3.0] * T)
    sol = None
    for _ in range(args.starts):
        B0 = rng.uniform(-1.0, 1.0, (T, T))
        B0 = (B0 + B0.T) / 2
        res = least_squares(residuals, pack(B0, rng.uniform(0.5, 2.0, T), T),
                            args=(T, graphs3, 0.5), bounds=(lo, hi),
                            method='trf', xtol=3e-16, ftol=3e-16, gtol=3e-16,
                            max_nfev=6000)
        if float(np.sum(res.fun[:len(graphs3)] ** 2)) < 1e-24:
            sol = res.x
            break
    assert sol is not None, "no exact m<=3 cube-gap instance found; raise --starts"
    B, W = unpack(sol, T)
    eps = B[0] - B[1]
    u = B[0] + B[1]
    M = B * W[None, :]

    def T3(f, g, h):
        return float(np.sum(W * f * g * h))

    def Mq(q, f):
        out = f.copy()
        for _ in range(q):
            out = M @ out
        return out

    def obsdiff_formula(a):
        tot = 0.0
        for S in [(0,), (1,), (2,), (0, 1, 2)]:
            tot += T3(*[Mq(a[l], eps if l in S else u) for l in range(3)])
        return 0.25 * tot

    gap3 = float(np.sum(W * (B[0] ** 3 - B[1] ** 3)))
    flushprint(f"instance found: m<=3-exact, cube gap = {gap3:.6f}")

    # 1) arms identity vs ground-truth rooted profiles
    for a in [(1, 1, 1), (1, 1, 2), (1, 2, 2), (2, 2, 2), (1, 1, 3)]:
        m, edges = k23_graph(a)
        O = rooted_profiles(B, W, [(m, edges)], T)
        d_direct = float(O[0, 0] - O[0, 1])
        d_form = obsdiff_formula(a)
        mism = abs(d_direct - d_form)
        flushprint(f"  arms {a} (m={m}): graph {d_direct:+.6e}  "
                   f"formula {d_form:+.6e}  |mismatch| {mism:.1e}")
        assert mism < 1e-10 * (1 + abs(d_direct)), "arms identity FAILED"

    # 2) common expansion via the direct sum
    Qmax = 2 * T
    A = np.column_stack([np.concatenate([Mq(q, eps), Mq(q, u)])
                         for q in range(1, Qmax + 1)])
    target = np.concatenate([eps, u])
    c, _, rank, _ = np.linalg.lstsq(A, target, rcond=None)
    rel = float(np.sum((A @ c - target) ** 2) / np.sum(target ** 2))
    flushprint(f"common expansion (eps,u) in span((M^q eps, M^q u)): "
               f"rel residual {rel:.3e} (rank {rank})")
    assert rel < 1e-16, "common expansion FAILED"

    # 3) gap reconstruction
    tot = sum(c[a[0] - 1] * c[a[1] - 1] * c[a[2] - 1] * obsdiff_formula(a)
              for a in iproduct(range(1, Qmax + 1), repeat=3))
    flushprint(f"gap3 reconstructed from K_2,3-arms data: {tot:.6f} "
               f"(pinned {gap3:.4f})")
    assert abs(tot - gap3) < 1e-6, "reconstruction FAILED"
    flushprint("VALIDATION PASSED: rpe kills every K_2,3-arms difference, and "
               "those span the cube gap — cube-moment descent is forced.")


if __name__ == '__main__':
    main()
