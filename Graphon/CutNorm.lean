/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Cut Norm for Graphons

This file defines the cut norm (also called rectangle norm) for graphons and
signed kernels, and proves basic properties.

## Main definitions

* `SymmKernel.rectIntegral` - Integral over a rectangle S × T
* `SymmKernel.cutNorm` - The cut norm ‖W‖_□ = sup_{S,T} |∫_{S×T} W|

## Main results

* `SymmKernel.cutNorm_nonneg` - Cut norm is non-negative
* `SymmKernel.cutNorm_le_one` - Cut norm of a graphon is at most 1

## Implementation notes

The cut norm is crucial for graphon convergence theory. It measures how well
a graphon can be approximated by step functions.

For a graphon W ∈ [0,1], we have 0 ≤ ‖W‖_□ ≤ 1.

The cut distance δ_□(U, W) = inf_φ ‖U - W^φ‖_□ will be defined in CutDistance.lean.

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Section 8.2.1
-/

open MeasureTheory Set Filter

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace SymmKernel

/-! ### Rectangle integrals -/

section RectIntegral

variable [IsProbabilityMeasure μ]

/-- The integral of a symmetric kernel over a measurable rectangle S × T.

This is the key building block for the cut norm:
`rectIntegral W S T = ∫∫_{S×T} W(x,y) dμ(x) dμ(y)` -/
noncomputable def rectIntegral (W : SymmKernel α μ) (S T : Set α) : ℝ :=
  ∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ)

/-- Rectangle integral is symmetric by symmetry of W. -/
theorem rectIntegral_symm (W : SymmKernel α μ) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    rectIntegral W S T = rectIntegral W T S := by
  simp only [rectIntegral]
  -- Use Fubini and symmetry of W: W(x,y) = W(y,x) a.e.
  -- ∫_{S×T} W(x,y) = ∫_{T×S} W(y,x) = ∫_{T×S} W(x,y)
  sorry

/-- Rectangle integral over empty set is zero. -/
theorem rectIntegral_empty_left (W : SymmKernel α μ) (T : Set α) :
    rectIntegral W ∅ T = 0 := by
  simp only [rectIntegral, empty_prod, setIntegral_empty]

/-- Rectangle integral over empty set is zero. -/
theorem rectIntegral_empty_right (W : SymmKernel α μ) (S : Set α) :
    rectIntegral W S ∅ = 0 := by
  simp only [rectIntegral, prod_empty, setIntegral_empty]

/-- Rectangle integral over the full space. -/
theorem rectIntegral_univ (W : SymmKernel α μ) :
    rectIntegral W univ univ = ∫ p, W.toAEEqFun p ∂(μ.prod μ) := by
  simp only [rectIntegral, univ_prod_univ, setIntegral_univ]

end RectIntegral

/-! ### Cut norm -/

section CutNorm

variable [IsProbabilityMeasure μ]

/-- The cut norm of a symmetric kernel.

`‖W‖_□ = sup_{S,T measurable} |∫_{S×T} W dμ×μ|`

This measures the "discrepancy" of the kernel - how far it deviates from
being constant on rectangles. -/
noncomputable def cutNorm (W : SymmKernel α μ) : ℝ :=
  ⨆ (S : Set α) (hS : MeasurableSet S) (T : Set α) (hT : MeasurableSet T),
    |rectIntegral W S T|

/-- Cut norm is non-negative (follows from abs being non-negative). -/
theorem cutNorm_nonneg (W : SymmKernel α μ) : 0 ≤ cutNorm W := by
  unfold cutNorm
  -- The supremum of non-negative values is non-negative
  -- We show 0 is a lower bound for the range
  apply Real.iSup_nonneg
  intro S
  apply Real.iSup_nonneg
  intro _
  apply Real.iSup_nonneg
  intro T
  apply Real.iSup_nonneg
  intro _
  exact abs_nonneg _

/-- Cut norm bounds individual rectangle integrals. -/
theorem abs_rectIntegral_le_cutNorm (W : SymmKernel α μ) {S T : Set α}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    |rectIntegral W S T| ≤ cutNorm W := by
  unfold cutNorm
  -- The value is in the range of the supremum
  sorry

/-- Cut norm for graphons is bounded by 1.

Since graphon values are in [0,1], the rectangle integral over any S × T
is at most μ(S) * μ(T) ≤ 1. -/
theorem cutNorm_le_one (W : Graphon α μ) : cutNorm W.toSymmKernel ≤ 1 := by
  -- For any S, T: |∫_{S×T} W| ≤ ∫_{S×T} |W| ≤ ∫_{S×T} 1 = μ(S×T) ≤ 1
  sorry

end CutNorm

end SymmKernel

namespace Graphon

/-- Cut norm of a graphon, via its symmetric kernel. -/
noncomputable def cutNorm (W : Graphon α μ) [IsProbabilityMeasure μ] : ℝ :=
  SymmKernel.cutNorm W.toSymmKernel

/-- Graphon cut norm is non-negative. -/
theorem cutNorm_nonneg (W : Graphon α μ) [IsProbabilityMeasure μ] : 0 ≤ cutNorm W :=
  SymmKernel.cutNorm_nonneg W.toSymmKernel

/-- Graphon cut norm is at most 1. -/
theorem cutNorm_le_one (W : Graphon α μ) [IsProbabilityMeasure μ] : cutNorm W ≤ 1 :=
  SymmKernel.cutNorm_le_one W

end Graphon
