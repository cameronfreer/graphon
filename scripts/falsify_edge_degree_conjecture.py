#!/usr/bin/env python3
"""
Falsification: same_edge_and_degree_profile_implies_orbit.

Conjecture: under twin-free B + W > 0,
  (∀ a ≠ b : Fin K, B(ξ a, ξ b) = B(ξ' a, ξ' b))
  ∧ (∀ a : Fin K, ∑ t, W(t) * B(ξ a, t) = ∑ t, W(t) * B(ξ' a, t))
  ⟹ tupleOrbitRel B W ξ ξ'

Counterexample = (B, W, ξ, ξ') with matching profile but no aut σ : Fin T ≃ Fin T
preserving (B, W) and conjugating ξ to ξ'.

Per user directive: explicitly include repeated tuple coordinates to
expose any diagonal-ambiguity issues.

Usage: python3 scripts/falsify_edge_degree_conjecture.py
"""

import numpy as np
from itertools import permutations, product as cartprod
import sys


def make_twin_free_matrix(T, rng, trial_idx=0):
    """Generate twin-free symmetric B with positive W."""
    B = rng.uniform(-1.0, 1.0, (T, T))
    B = (B + B.T) / 2
    for i in range(T):
        B[i, i] += 0.1 * (i + 1 + 0.01 * trial_idx)
    # Verify twin-free, perturb if needed.
    is_twin_free = True
    for i in range(T):
        for j in range(i+1, T):
            if np.allclose(B[i], B[j], atol=1e-10):
                is_twin_free = False
                break
    if not is_twin_free:
        for i in range(T):
            B[i, :] += 0.01 * (i + 1) * np.arange(T)
        B = (B + B.T) / 2
    W = rng.uniform(0.5, 1.5, T)
    return B, W


def compute_aut_group(B, W, tol=1e-9):
    T = len(W)
    auts = []
    for perm in permutations(range(T)):
        perm = list(perm)
        if not all(abs(W[perm[i]] - W[i]) < tol for i in range(T)):
            continue
        if not all(abs(B[perm[i]][perm[j]] - B[i][j]) < tol
                   for i in range(T) for j in range(T)):
            continue
        auts.append(tuple(perm))
    return auts


def in_same_orbit(ξ, ξ_prime, auts):
    for σ in auts:
        σξ = tuple(σ[ξ[k]] for k in range(len(ξ)))
        if σξ == tuple(ξ_prime):
            return True
    return False


def matches_edge_profile(ξ, ξ_prime, B, K, tol=1e-9):
    """Check ∀ a ≠ b, B(ξ a, ξ b) = B(ξ' a, ξ' b)."""
    for a in range(K):
        for b in range(K):
            if a == b:
                continue
            if not np.isclose(B[ξ[a]][ξ[b]], B[ξ_prime[a]][ξ_prime[b]], atol=tol):
                return False
    return True


def matches_degree_profile(ξ, ξ_prime, B, W, K, tol=1e-9):
    """Check ∀ a, ∑ t W(t) B(ξ a, t) = ∑ t W(t) B(ξ' a, t)."""
    T = len(W)
    for a in range(K):
        s1 = sum(W[t] * B[ξ[a]][t] for t in range(T))
        s2 = sum(W[t] * B[ξ_prime[a]][t] for t in range(T))
        if not np.isclose(s1, s2, atol=tol):
            return False
    return True


def make_cycle_disjoint_union(sizes):
    """Build B = adjacency matrix of disjoint union of cycles of given sizes.
    Returns (B, W) with uniform W = 1.
    """
    T = sum(sizes)
    B = np.zeros((T, T))
    offset = 0
    for n in sizes:
        for i in range(n):
            j = (i + 1) % n
            B[offset + i, offset + j] = 1.0
            B[offset + j, offset + i] = 1.0
        offset += n
    W = np.ones(T)
    return B, W


def main():
    rng = np.random.default_rng(2026)
    counterexamples = []
    total_pairs = 0
    matched_profile = 0
    profile_implies_orbit = 0

    # **ADVERSARIAL CASE**: C_5 ⊔ C_6 (per 2026-05-14 user analysis).
    # vertex 0 in C_5 and vertex 5 in C_6 both have weighted degree 2;
    # at K = 1 edge profile is vacuous; but no aut sends them to each
    # other (component preservation).
    print("=" * 70)
    print("Adversarial: C_5 ⊔ C_6, K = 1")
    print("=" * 70)
    B_adv, W_adv = make_cycle_disjoint_union([5, 6])
    auts_adv = compute_aut_group(B_adv, W_adv)
    print(f"|Aut(C_5 ⊔ C_6)| = {len(auts_adv)} (expected D_5 × D_6 = 10 × 12 = 120)")
    for K in [1]:
        for ξ in cartprod(range(11), repeat=K):
            for ξ_prime in cartprod(range(11), repeat=K):
                total_pairs += 1
                if not matches_edge_profile(ξ, ξ_prime, B_adv, K):
                    continue
                if not matches_degree_profile(ξ, ξ_prime, B_adv, W_adv, K):
                    continue
                matched_profile += 1
                if in_same_orbit(ξ, ξ_prime, auts_adv):
                    profile_implies_orbit += 1
                else:
                    counterexamples.append({
                        'B_family': 'C_5 ⊔ C_6',
                        'T': 11, 'K': K,
                        'ξ': ξ, 'ξ_prime': ξ_prime,
                        '|Aut|': len(auts_adv),
                    })

    for T in [2, 3, 4, 5]:
        for K in [1, 2, 3]:
            for trial in range(3):
                B, W = make_twin_free_matrix(T, rng, trial_idx=trial)
                auts = compute_aut_group(B, W)

                for ξ in cartprod(range(T), repeat=K):
                    for ξ_prime in cartprod(range(T), repeat=K):
                        total_pairs += 1
                        # Check profile match.
                        if not matches_edge_profile(ξ, ξ_prime, B, K):
                            continue
                        if not matches_degree_profile(ξ, ξ_prime, B, W, K):
                            continue
                        matched_profile += 1
                        # Profile matches. Is orbit?
                        if in_same_orbit(ξ, ξ_prime, auts):
                            profile_implies_orbit += 1
                        else:
                            # COUNTEREXAMPLE!
                            counterexamples.append({
                                'T': T, 'K': K, 'trial': trial,
                                'ξ': ξ, 'ξ_prime': ξ_prime,
                                'B': B.tolist(), 'W': W.tolist(),
                                '|Aut|': len(auts),
                            })
                            if len(counterexamples) <= 3:
                                print(f"\nCOUNTEREXAMPLE: T={T}, K={K}, trial={trial}")
                                print(f"  ξ = {ξ}, ξ' = {ξ_prime}")
                                print(f"  Profile matches but orbits differ.")
                                print(f"  |Aut(B,W)| = {len(auts)}")
                                print(f"  B =\n{B}")
                                print(f"  W = {W}")

    print("\n" + "=" * 70)
    print(f"Total ξ,ξ' pairs checked: {total_pairs}")
    print(f"Pairs with matching edge+degree profile: {matched_profile}")
    print(f"Profile-matching pairs that ARE in same orbit: {profile_implies_orbit}")
    print(f"COUNTEREXAMPLES (profile match but different orbits): "
          f"{len(counterexamples)}")
    print("=" * 70)

    if not counterexamples:
        print("PASS — no counterexample found in this search range.")
        print("Conjecture appears to hold; safe to attempt Lean proof.")
    else:
        print(f"FAIL — {len(counterexamples)} counterexamples found.")
        print("Conjecture is FALSE as stated; needs refinement.")
        print("\nSample analyses:")
        for c in counterexamples[:3]:
            print(c)


if __name__ == '__main__':
    main()
