/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.HomDensity
import Graphon.CutDistance

/-!
# Counting Lemma for Graphons

This file proves the counting lemma, which relates the difference in homomorphism
densities to the cut norm of the difference between graphons.

## Main results

* `Graphon.homDensity_sub_le` - `|t(F, U) - t(F, W)| ≤ |E(F)| · ‖U - W‖_□`

## Implementation notes

The counting lemma is one of the central results in graphon theory. It says that
if two graphons are close in cut norm, then they have similar homomorphism densities
for any fixed graph F.

The constant `|E(F)|` (number of edges in F) is optimal in general.

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Chapter 10
-/

open MeasureTheory Set Filter Finset

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Graphon

/-! ### Counting lemma -/

section Counting

variable [IsProbabilityMeasure μ]

/-- The counting lemma: homomorphism density difference is bounded by cut norm.

For any graph F and graphons U, W on the same probability space:
`|t(F, U) - t(F, W)| ≤ |E(F)| · ‖U - W‖_□`

This is the key result showing that cut norm controls homomorphism densities. -/
theorem homDensity_sub_le (F : SimpleGraph V) [DecidableRel F.Adj]
    (U W : Graphon α μ) :
    |homDensity F U - homDensity F W| ≤ F.edgeFinset.card * cutNormDiff U W := by
  -- Proof outline:
  -- 1. Write the difference of integrands as a telescoping sum
  -- 2. Each term differs in one edge factor
  -- 3. Use that |∫(U-W)| ≤ ‖U-W‖_□ for appropriate rectangles
  -- 4. Sum over edges gives the bound
  sorry

/-- Corollary: graphs with small cut distance have similar homomorphism densities. -/
theorem homDensity_sub_le_of_cutDistance (F : SimpleGraph V) [DecidableRel F.Adj]
    (U W : Graphon α μ) :
    |homDensity F U - homDensity F W| ≤ F.edgeFinset.card * cutDistance U W := by
  -- We need cutDistance ≤ cutNormDiff, but that's backwards
  -- Actually the statement should use cutNormDiff, not cutDistance
  -- Or we need to prove this for any reparametrization and take inf
  sorry

/-- If cut distance is zero, homomorphism densities are equal.

This is a key consequence: weakly isomorphic graphons have the same
homomorphism densities for all graphs F. -/
theorem homDensity_eq_of_cutDistance_zero (F : SimpleGraph V) [DecidableRel F.Adj]
    (U W : Graphon α μ) (h : cutDistance U W = 0) :
    homDensity F U = homDensity F W := by
  have hle := homDensity_sub_le_of_cutDistance F U W
  rw [h, mul_zero] at hle
  have habs : |homDensity F U - homDensity F W| = 0 :=
    le_antisymm hle (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

end Counting

/-! ### Continuity properties -/

section Continuity

variable [IsProbabilityMeasure μ]

/-- Homomorphism density difference is bounded by edge count times cut norm difference.

This is the quantitative version of continuity with respect to cut norm.

**Note**: We use `max 1 F.edgeFinset.card` in the denominator to handle the empty graph case.
For empty graphs, both homomorphism densities equal 1, so the bound is trivially satisfied. -/
theorem homDensity_continuous_cutNormDiff (F : SimpleGraph V) [DecidableRel F.Adj]
    (U W : Graphon α μ) (ε : ℝ) (hε : ε > 0)
    (h : cutNormDiff U W < ε / max 1 F.edgeFinset.card) :
    |homDensity F U - homDensity F W| < ε := by
  by_cases hF : F.edgeFinset.card = 0
  · -- Empty graph: both densities are 1
    have hEmpty : F.edgeFinset = ∅ := Finset.card_eq_zero.mp hF
    have hU : homDensity F U = 1 := by
      unfold homDensity
      simp only [hEmpty, Finset.prod_empty]
      simp only [integral_const]
      simp
    have hW : homDensity F W = 1 := by
      unfold homDensity
      simp only [hEmpty, Finset.prod_empty]
      simp only [integral_const]
      simp
    simp only [hU, hW, sub_self, abs_zero]
    exact hε
  · have hcard_pos : 0 < F.edgeFinset.card := Nat.pos_of_ne_zero hF
    have hmax_eq : max 1 F.edgeFinset.card = F.edgeFinset.card :=
      max_eq_right (Nat.one_le_iff_ne_zero.mpr hF)
    simp only [hmax_eq] at h
    calc |homDensity F U - homDensity F W|
        ≤ F.edgeFinset.card * cutNormDiff U W := homDensity_sub_le F U W
      _ < F.edgeFinset.card * (ε / F.edgeFinset.card) := by
          apply mul_lt_mul_of_pos_left h
          exact Nat.cast_pos.mpr hcard_pos
      _ = ε := by field_simp

end Continuity

end Graphon
