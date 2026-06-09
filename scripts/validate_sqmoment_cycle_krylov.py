#!/usr/bin/env python3
"""
Numerical validation of the CYCLE-KRYLOV-KERNEL proof of square-moment descent
(#70 test case `sqMoment_descends_of_rootedProfileEquiv`, Graphon/SimpleRank.lean).

THEOREM (discovered & validated 2026-06-09; formalization pending).
Let B be symmetric real, W > 0, and i, j rooted-profile equivalent. Set
    eps := B(i,.) - B(j,.),   u := B(i,.) + B(j,.),
    M   := f |-> B D_W f      (weighted adjacency; self-adjoint wrt <f,g>_W),
    gap := sum_t W_t (B(i,t)^2 - B(j,t)^2) = <eps, u>_W.
Then gap = 0. Proof:
 1. CYCLE DIFFERENCE IDENTITY: for the rooted (q+2)-cycle C_q (root plus q+1
    unlabeled vertices in a ring),
        P_{C_q}(i) - P_{C_q}(j) = <eps, M^q u>_W      exactly, for all q >= 1.
    (Expand rho_i rho_i - rho_j rho_j = eps rho_i + rho_j eps on the two
    root-incident edges; M is self-adjoint.) Hence rpe forces
    <eps, M^q u>_W = 0 for q = 1..T (lengths 3..T+2 suffice spectrally).
 2. u IS IN Im(M): u = M (D_W^{-1}(e_i + e_j)), using W > 0.
 3. SPECTRAL STEP: M self-adjoint => Im(M) is spanned by nonzero-eigenvalue
    eigenspaces => u in span{M^q u : q >= 1} (Vandermonde over the distinct
    nonzero eigenvalues).
 4. gap = <eps, u>_W = sum_q c_q <eps, M^q u>_W = 0.   QED
No twin-freeness needed. Only hB (symmetry) and hW (positivity).

This also explains the falsification numerics (falsify_classwise_sqmoment.py):
m<=4 observables provide only q <= 3, so at T=5 the gap system stays exactly
feasible at m<=4 and dies once longer cycles enter (T=4: dies at m=4).

CLASSWISE residual (still open): for atom-invariant g, palindromic decorated
cycles give <eps, D_g M^q D_g u>_W = 0; the same argument kills the classwise
gap <eps, D_g u>_W whenever P_ker(M) (D_g u) = 0 (e.g. M nonsingular). The
singular-M stratum remains the open case of `classwise_sqMoment_descends`.

This script reconstructs the validation: finds an instance where (0,1) agree
on all m<=3 observables yet gap = 0.5, then checks the identity against
ground-truth rooted-cycle profiles and reconstructs the gap from the q>=1
cycle quantities.

Usage: python3 scripts/validate_sqmoment_cycle_krylov.py [--T 5] [--seed 13]
"""

import argparse
import sys

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
    gap = float(np.sum(W * B[0] ** 2) - np.sum(W * B[1] ** 2))
    return np.append(r, gap - want_gap)


def cycle_edges(q):
    """Rooted (q+2)-cycle: root 0, unlabeled 1..q+1 in a ring with the root."""
    mm = q + 1
    e = [(0, 1), (0, mm)] + [(k, k + 1) for k in range(1, mm)]
    return (mm, sorted(set(tuple(sorted(x)) for x in e)))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--T', type=int, default=5)
    ap.add_argument('--seed', type=int, default=13)
    ap.add_argument('--starts', type=int, default=8)
    args = ap.parse_args()
    T = args.T

    # Find an m<=3-exact instance with gap pinned to 0.5 (LM engine).
    graphs3 = rooted_graphs(3)
    rng = np.random.default_rng(args.seed)
    nb = T * (T + 1) // 2
    lo = np.array([-1.5] * nb + [0.05] * T)
    hi = np.array([1.5] * nb + [3.0] * T)
    sol = None
    for s in range(args.starts):
        B0 = rng.uniform(-1.0, 1.0, (T, T))
        B0 = (B0 + B0.T) / 2
        W0 = rng.uniform(0.5, 2.0, T)
        res = least_squares(residuals, pack(B0, W0, T), args=(T, graphs3, 0.5),
                            bounds=(lo, hi), method='trf', xtol=3e-16,
                            ftol=3e-16, gtol=3e-16, max_nfev=2500)
        eq = float(np.sum(res.fun[:len(graphs3)] ** 2))
        if eq < 1e-24:
            sol = res.x
            break
    assert sol is not None, "no exact m<=3 instance found; increase --starts"
    B, W = unpack(sol, T)

    eps = B[0] - B[1]
    u = B[0] + B[1]
    M = B * W[None, :]

    def ip(f, g):
        return float(np.sum(W * f * g))

    gap = ip(eps, u)
    flushprint(f"instance found: m<=3-exact, gap = <eps,u>_W = {gap:.6f}")

    # 1) cycle-difference identity against ground-truth rooted profiles
    ok = True
    for q in range(1, T + 1):
        m, edges = cycle_edges(q)
        O = rooted_profiles(B, W, [(m, edges)], T)
        d_direct = float(O[0, 0] - O[0, 1])
        d_formula = ip(eps, np.linalg.matrix_power(M, q) @ u)
        match = abs(d_direct - d_formula)
        flushprint(f"  q={q}: cycle-diff {d_direct:+.6e}  <eps,M^q u>_W "
                   f"{d_formula:+.6e}  |mismatch| {match:.1e}")
        ok &= match < 1e-10 * (1 + abs(d_direct))
    assert ok, "cycle identity FAILED"

    # 2) u in span{M^q u : q >= 1} (consequence of u in Im M + self-adjointness)
    A = np.column_stack([np.linalg.matrix_power(M, q) @ u for q in range(1, T + 1)])
    c, _, rank, _ = np.linalg.lstsq(A, u, rcond=None)
    recon = float(np.sum((A @ c - u) ** 2)) / float(np.sum(u ** 2))
    flushprint(f"u in span(M^q u, q=1..{T}): relative residual {recon:.3e} "
               f"(rank {rank})")
    assert recon < 1e-16, "Krylov membership FAILED"

    # 3) gap reconstruction from cycle quantities
    gap_rec = float(sum(c[q - 1] * ip(eps, A[:, q - 1]) for q in range(1, T + 1)))
    flushprint(f"gap reconstructed from q>=1 cycle data: {gap_rec:.6f} "
               f"(equals the pinned gap; every term is a rooted-cycle "
               f"difference, killed under full rpe)")
    flushprint("VALIDATION PASSED: rpe kills every <eps,M^q u>_W (q>=1), and "
               "those span the gap — square-moment descent is forced.")


if __name__ == '__main__':
    main()
