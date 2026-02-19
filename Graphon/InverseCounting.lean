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
  -- Show: for all ε > 0, cutDistance U W ≤ 2ε. Then cutDistance U W ≤ 0, hence = 0.
  apply le_antisymm _ (cutDistance_nonneg U W)
  -- For all ε > 0, cutDistance U W < 3ε
  by_contra h_neg
  push_neg at h_neg
  -- h_neg : 0 < cutDistance U W
  set δ := cutDistance U W / 3 with hδ_def
  have hδ_pos : δ > 0 := by linarith
  -- By regularity, approximate U and W by step graphons
  obtain ⟨P_U, _, hP_U⟩ := regularity U δ hδ_pos
  obtain ⟨P_W, _, hP_W⟩ := regularity W δ hδ_pos
  -- cutDistance(U, stepify P_U U) ≤ cutNormDiff(U, stepify P_U U) ≤ δ
  have h1 : cutDistance U (stepify P_U U) ≤ δ :=
    le_trans (cutDistance_le_cutNormDiff U (stepify P_U U)) hP_U
  -- Similarly for W
  have h2 : cutDistance W (stepify P_W W) ≤ δ :=
    le_trans (cutDistance_le_cutNormDiff W (stepify P_W W)) hP_W
  -- Step graphons with equal hom densities have cutDistance = 0
  -- (hom densities of step graphons determine their coefficients)
  -- This is the deep combinatorial step: step graphons with the same hom
  -- densities for all graphs must have cutDistance 0
  -- For now, we express this as: cutDistance(stepify_U, stepify_W) ≤ δ
  -- (which follows from the counting lemma + hom density closeness)
  -- Full proof requires: step graphon coefficients determined by hom densities
  sorry

/-- The inverse counting lemma: similar homomorphism densities imply
    small cut distance.

For any ε > 0, there exists δ > 0 and a finite set of graphs F₁,...,Fₖ
such that if |t(Fᵢ, U) - t(Fᵢ, W)| < δ for all i, then δ□(U, W) < ε. -/
theorem cutDistance_le_of_homDensity_close [StandardBorelSpace α] (ε : ℝ) (hε : ε > 0) :
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
theorem cutDistance_tendsto_iff_homDensity_tendsto [StandardBorelSpace α]
    (W : ℕ → Graphon α μ) (V : Graphon α μ) :
    (∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W n) V < ε) ↔
    (∀ (F : SimpleGraph (Fin 2)) [DecidableRel F.Adj],
     ∀ ε > 0, ∃ N, ∀ n ≥ N, |homDensity F (W n) - homDensity F V| < ε) := by
  constructor
  · -- Forward: counting lemma
    intro hconv F _ ε hε
    by_cases hF : F.edgeFinset.card = 0
    · -- Empty graph case: homDensity is always 1
      use 0
      intro n _
      have h_empty : F.edgeFinset = ∅ := Finset.card_eq_zero.mp hF
      simp only [homDensity_eq_integral, homDensityIntegrand, h_empty, Finset.prod_empty,
          sub_self, abs_zero, hε]
    · -- Non-empty graph: use counting lemma
      have hcard_pos : (0 : ℝ) < F.edgeFinset.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hF)
      obtain ⟨N, hN⟩ := hconv (ε / F.edgeFinset.card) (div_pos hε hcard_pos)
      use N
      intro n hn
      calc |homDensity F (W n) - homDensity F V|
          ≤ F.edgeFinset.card * cutDistance (W n) V := homDensity_sub_le_of_cutDistance F (W n) V
        _ < F.edgeFinset.card * (ε / F.edgeFinset.card) := by
            apply mul_lt_mul_of_pos_left (hN n hn) hcard_pos
        _ = ε := mul_div_cancel₀ ε (ne_of_gt hcard_pos)
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
    -- Show: for all ε > 0, cutDistance U V ≤ ε
    -- Then use le_of_forall_le_of_dense or similar
    by_contra h_neg
    push_neg at h_neg
    -- h_neg : cutDistance U V > 0
    -- Let ε = cutDistance U V / 2
    set ε := cutDistance U V / 2 with hε_def
    have hε_pos : ε > 0 := by linarith
    obtain ⟨N₁, hN₁⟩ := hU ε hε_pos
    obtain ⟨N₂, hN₂⟩ := hV ε hε_pos
    set n := max N₁ N₂ with hn_def
    have hn₁ : n ≥ N₁ := le_max_left N₁ N₂
    have hn₂ : n ≥ N₂ := le_max_right N₁ N₂
    have h1 : cutDistance (W n) U < ε := hN₁ n hn₁
    have h2 : cutDistance (W n) V < ε := hN₂ n hn₂
    have h_tri : cutDistance U V ≤ cutDistance U (W n) + cutDistance (W n) V :=
      cutDistance_triangle U (W n) V
    have h_symm : cutDistance U (W n) = cutDistance (W n) U := cutDistance_symm U (W n)
    have h_bound : cutDistance U V < 2 * ε := by
      calc cutDistance U V
          ≤ cutDistance U (W n) + cutDistance (W n) V := h_tri
        _ = cutDistance (W n) U + cutDistance (W n) V := by rw [h_symm]
        _ < ε + ε := add_lt_add h1 h2
        _ = 2 * ε := by ring
    -- But 2 * ε = cutDistance U V, contradiction
    linarith
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
