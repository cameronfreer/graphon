/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Counting
import Graphon.Compactness

/-!
# Inverse Counting Lemma

This file proves the inverse counting lemma: if two graphons have similar
homomorphism densities for all graphs, then they are close in cut distance.

## Main results

* `Graphon.cutDistance_le_of_homDensity_close` - The inverse counting lemma

## Implementation notes

The counting lemma (in `Counting.lean`) shows:
  small cut distance ⟹ similar homomorphism densities

The inverse counting lemma shows the converse:
  similar homomorphism densities ⟹ small cut distance

Together, these establish that cut distance convergence is equivalent to
convergence of all homomorphism densities.

The proof uses:
1. Regularity lemma to approximate by step graphons
2. Counting lemma for step graphons
3. Compactness argument

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Section 10.6
-/

open MeasureTheory Set Filter Finset

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

/-! ### Inverse counting lemma -/

section InverseCounting

variable [IsProbabilityMeasure μ]

/-- Two graphons with equal homomorphism densities for all graphs have
    cut distance zero (are weakly isomorphic).

This is the strong form of the inverse counting lemma. -/
theorem cutDistance_zero_of_homDensity_eq
    (U W : Graphon α μ)
    (h : ∀ (V : Type*) [Fintype V] [DecidableEq V] (F : SimpleGraph V) [DecidableRel F.Adj],
         homDensity F U = homDensity F W) :
    cutDistance U W = 0 := by
  -- The proof uses:
  -- 1. Approximate U and W by step graphons
  -- 2. Step graphons with same hom densities are equal
  -- 3. Take limits using regularity
  sorry

/-- The inverse counting lemma: similar homomorphism densities imply
    small cut distance.

For any ε > 0, there exists δ > 0 and a finite set of graphs F₁,...,Fₖ
such that if |t(Fᵢ, U) - t(Fᵢ, W)| < δ for all i, then δ□(U, W) < ε. -/
theorem cutDistance_le_of_homDensity_close (ε : ℝ) (hε : ε > 0) :
    ∃ (δ : ℝ) (_ : δ > 0) (k : ℕ),
    ∀ (U W : Graphon α μ),
      (∀ (F : SimpleGraph (Fin k)) [DecidableRel F.Adj], |homDensity F U - homDensity F W| < δ) →
      cutDistance U W < ε := by
  -- The proof uses compactness:
  -- 1. The space of graphons is compact
  -- 2. The function W ↦ cutDistance W₀ W is continuous
  -- 3. By compactness, a finite number of hom densities suffice
  sorry

/-- Corollary: a sequence converges in cut distance iff all homomorphism
    densities converge.

This is the fundamental characterization of graph limit convergence. -/
theorem cutDistance_tendsto_iff_homDensity_tendsto
    (W : ℕ → Graphon α μ) (V : Graphon α μ) :
    (∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W n) V < ε) ↔
    (∀ (F : SimpleGraph (Fin 2)) [DecidableRel F.Adj],
     ∀ ε > 0, ∃ N, ∀ n ≥ N, |homDensity F (W n) - homDensity F V| < ε) := by
  constructor
  · -- Forward: counting lemma
    intro hconv F _ ε hε
    sorry
  · -- Backward: inverse counting lemma
    intro hhom ε hε
    sorry

end InverseCounting

/-! ### Uniqueness of limits -/

section Uniqueness

variable [IsProbabilityMeasure μ]

/-- If a sequence converges to two limits, they are weakly isomorphic.

Limits in the graphon space are unique up to weak isomorphism.

**Hypothesis**: Requires `[StandardBorelSpace α]` for the triangle inequality. -/
theorem limit_unique_upto_weakIso [StandardBorelSpace α]
    (W : ℕ → Graphon α μ) (U V : Graphon α μ)
    (hU : ∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W n) U < ε)
    (hV : ∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W n) V < ε) :
    WeaklyIsomorphic U V := by
  -- By triangle inequality: δ□(U, V) ≤ δ□(U, Wₙ) + δ□(Wₙ, V)
  -- Both terms → 0 as n → ∞
  unfold WeaklyIsomorphic
  apply le_antisymm
  · -- cutDistance U V ≤ 0
    -- By triangle inequality: δ□(U, V) ≤ δ□(U, Wₙ) + δ□(Wₙ, V)
    -- Both terms can be made arbitrarily small
    -- Get N₁, N₂ such that Wₙ is close to both U and V
    -- Take n = max N₁ N₂, show δ□(U, V) < ε for any ε > 0
    sorry
  · exact cutDistance_nonneg U V

/-- Homomorphism densities determine the graphon up to weak isomorphism.

If two graphons have identical homomorphism densities for all graphs,
they are weakly isomorphic. -/
theorem weaklyIsomorphic_of_homDensity_eq
    (U W : Graphon α μ)
    (h : ∀ (V : Type*) [Fintype V] [DecidableEq V] (F : SimpleGraph V) [DecidableRel F.Adj],
         homDensity F U = homDensity F W) :
    WeaklyIsomorphic U W :=
  cutDistance_zero_of_homDensity_eq U W h

end Uniqueness

end Graphon
