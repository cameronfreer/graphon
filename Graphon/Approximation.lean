/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Step
import Graphon.CutDistance

/-!
# Approximation of Graphons by Step Functions

This file develops the theory of approximating graphons by step functions,
which is central to the regularity lemma and compactness of graphon space.

## Main definitions

* `Graphon.rectAverage` - Average value of a graphon over a rectangle
* `Graphon.Refines` - Partition refinement relation

## Main results

* `Graphon.rectAverage_mem_Icc` - Rectangle averages are in [0, 1]
* `Graphon.rectAverage_symm` - Rectangle averages are symmetric

## Implementation notes

Given a measurable partition P of α, the stepified graphon takes the average value
on each rectangle S × T for S, T ∈ P:
`(stepify P W)(x, y) = (1/(μ(S)μ(T))) ∫_{S×T} W dμ×μ` for x ∈ S, y ∈ T

The full stepification construction requires building an AEEqFun from piecewise
definitions, which is deferred to future work.

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Section 9.2-9.3
-/

open MeasureTheory Set Filter Finset

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

/-! ### Rectangle averages -/

section RectAverage

variable [IsProbabilityMeasure μ]

/-- The average value of a graphon over a rectangle S × T.

This is the building block for stepification:
`rectAverage W S T = (1/(μ(S)μ(T))) ∫_{S×T} W dμ×μ` -/
noncomputable def rectAverage (W : Graphon α μ) (S T : Set α) : ℝ :=
  if hS : μ S = 0 then 0
  else if hT : μ T = 0 then 0
  else (μ S).toReal⁻¹ * (μ T).toReal⁻¹ *
    ∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ)

/-- The rectangle average is in [0, 1] for graphons. -/
theorem rectAverage_mem_Icc (W : Graphon α μ) (S T : Set α) :
    rectAverage W S T ∈ Set.Icc 0 1 := by
  unfold rectAverage
  split_ifs with hS hT
  · exact ⟨le_refl 0, zero_le_one⟩
  · exact ⟨le_refl 0, zero_le_one⟩
  · -- The integral is between 0 and μ(S)μ(T), so the average is in [0,1]
    -- Since W ∈ [0,1] a.e., we have 0 ≤ ∫_{S×T} W ≤ μ(S×T) = μ(S)μ(T)
    sorry

/-- The rectangle average is symmetric. -/
theorem rectAverage_symm (W : Graphon α μ) (S T : Set α)
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    rectAverage W S T = rectAverage W T S := by
  unfold rectAverage
  split_ifs with h1 h2 h3 h4
  · rfl
  · rfl
  · rfl
  · -- Use symmetry of W
    rw [mul_comm (μ S).toReal⁻¹ (μ T).toReal⁻¹]
    congr 1
    -- The integral over S × T equals the integral over T × S by symmetry of W
    sorry

/-- Rectangle average of zero graphon is zero. -/
theorem rectAverage_zero (S T : Set α) : rectAverage (zero : Graphon α μ) S T = 0 := by
  unfold rectAverage
  split_ifs with hS hT
  · rfl
  · rfl
  · simp only [mul_eq_zero]
    right
    -- The integral of 0 is 0
    sorry

/-- Rectangle average of one graphon is one (for positive measure sets). -/
theorem rectAverage_one {S T : Set α} (hS : μ S ≠ 0) (hT : μ T ≠ 0)
    (hSm : MeasurableSet S) (hTm : MeasurableSet T) :
    rectAverage (one : Graphon α μ) S T = 1 := by
  unfold rectAverage
  simp only [hS, hT, dite_false]
  -- The integral of 1 over S × T is μ(S) * μ(T)
  sorry

end RectAverage

/-! ### Refinement -/

section Refinement

variable [IsProbabilityMeasure μ]

/-- A partition Q refines P if every part of Q is contained in some part of P. -/
def Refines (Q P : MeasurablePartition α μ) : Prop :=
  ∀ T ∈ Q.parts, ∃ S ∈ P.parts, T ⊆ S

/-- Refinement is reflexive. -/
theorem Refines.refl (P : MeasurablePartition α μ) : Refines P P :=
  fun T hT => ⟨T, hT, Subset.refl T⟩

/-- Refinement is transitive. -/
theorem Refines.trans {P Q R : MeasurablePartition α μ}
    (hPQ : Refines Q P) (hQR : Refines R Q) : Refines R P := by
  intro T hT
  obtain ⟨S, hS, hTS⟩ := hQR T hT
  obtain ⟨U, hU, hSU⟩ := hPQ S hS
  exact ⟨U, hU, hTS.trans hSU⟩

end Refinement

/-! ### Stepification (to be developed)

The full stepification construction requires:
1. Building an AEEqFun that is piecewise constant on partition rectangles
2. Showing this is measurable and symmetric
3. Proving it takes values in [0,1] a.e.

This will be developed in future phases when the machinery for
piecewise-defined graphons is established.
-/

end Graphon
