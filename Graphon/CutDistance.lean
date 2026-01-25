/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.CutNorm
import Graphon.Pullback

/-!
# Cut Distance for Graphons

This file defines the cut distance (also called cut metric) between graphons,
which is the fundamental metric for graphon convergence theory.

## Main definitions

* `Graphon.cutNormDiff` - The cut norm of the difference `‖U - W‖_□`
* `Graphon.cutDistance` - The cut distance `δ□(U, W) = inf_φ ‖U - W^φ‖_□`

## Main results

* `Graphon.cutDistance_self` - `δ□(W, W) = 0`
* `Graphon.cutDistance_nonneg` - `0 ≤ δ□(U, W)`

## Implementation notes

The cut distance is defined as an infimum over measure-preserving maps. In general,
one needs to consider maps from a common probability space to both graphons.

The cut distance is a pseudometric: `δ□(U, W) = 0` does not imply `U = W`, but
rather that U and W are weakly isomorphic (differ only by measure-preserving
reparametrization).

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Section 8.2.2
-/

open MeasureTheory Set Filter

open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}

namespace Graphon

/-! ### Rectangle integral of difference -/

section RectIntegralDiff

variable [IsProbabilityMeasure μ]

/-- The integral of the difference of two graphons over a measurable rectangle S × T. -/
noncomputable def rectIntegralDiff (U W : Graphon α μ) (S T : Set α) : ℝ :=
  ∫ p in S ×ˢ T, (U.toAEEqFun p - W.toAEEqFun p) ∂(μ.prod μ)

/-- Rectangle integral of difference equals difference of rectangle integrals. -/
theorem rectIntegralDiff_eq (U W : Graphon α μ) (S T : Set α) :
    rectIntegralDiff U W S T =
      SymmKernel.rectIntegral U.toSymmKernel S T - SymmKernel.rectIntegral W.toSymmKernel S T := by
  unfold rectIntegralDiff SymmKernel.rectIntegral
  rw [← integral_sub]
  -- Integrability conditions
  all_goals sorry

end RectIntegralDiff

/-! ### Cut norm of difference -/

section CutNormDiff

variable [IsProbabilityMeasure μ]

/-- The cut norm of the difference of two graphons.

`‖U - W‖_□ = sup_{S,T measurable} |∫_{S×T} (U - W)|`

Since graphons take values in [0,1], their difference takes values in [-1,1]. -/
noncomputable def cutNormDiff (U W : Graphon α μ) : ℝ :=
  ⨆ (S : Set α) (hS : MeasurableSet S) (T : Set α) (hT : MeasurableSet T),
    |rectIntegralDiff U W S T|

/-- Cut norm difference is non-negative. -/
theorem cutNormDiff_nonneg (U W : Graphon α μ) : 0 ≤ cutNormDiff U W := by
  unfold cutNormDiff
  -- The supremum of absolute values is ≥ 0
  sorry

/-- Cut norm difference with self is zero. -/
theorem cutNormDiff_self (W : Graphon α μ) : cutNormDiff W W = 0 := by
  unfold cutNormDiff rectIntegralDiff
  -- W - W = 0, so all rectangle integrals are 0
  simp only [sub_self, integral_zero, abs_zero]
  -- The supremum of constant 0 is 0
  sorry

/-- Cut norm difference is symmetric. -/
theorem cutNormDiff_symm (U W : Graphon α μ) : cutNormDiff U W = cutNormDiff W U := by
  unfold cutNormDiff rectIntegralDiff
  -- |∫(U-W)| = |∫(W-U)| since |x| = |-x|
  congr 1
  ext S
  congr 1
  ext hS
  congr 1
  ext T
  congr 1
  ext hT
  rw [show (∫ p in S ×ˢ T, (U.toAEEqFun p - W.toAEEqFun p) ∂(μ.prod μ)) =
          -(∫ p in S ×ˢ T, (W.toAEEqFun p - U.toAEEqFun p) ∂(μ.prod μ)) by
    rw [← integral_neg]
    congr 1
    ext p
    ring]
  rw [abs_neg]

/-- Cut norm difference is bounded by 2.

Since U, W ∈ [0,1], we have U - W ∈ [-1,1], so |∫(U-W)| ≤ μ(S×T) ≤ 1.
Actually the bound is 1, not 2. -/
theorem cutNormDiff_le_one (U W : Graphon α μ) : cutNormDiff U W ≤ 1 := by
  -- For any S, T: |∫_{S×T} (U-W)| ≤ ∫_{S×T} |U-W| ≤ ∫_{S×T} 1 = μ(S×T) ≤ 1
  sorry

end CutNormDiff

/-! ### Cut distance -/

section CutDistance

variable [IsProbabilityMeasure μ]

/-- The cut distance between two graphons on the same probability space.

`δ□(U, W) = inf_φ ‖U - W^φ‖_□`

where the infimum is over all measure-preserving maps `φ : α → α`. -/
noncomputable def cutDistance (U W : Graphon α μ) : ℝ :=
  sInf {d : ℝ | ∃ (φ : α → α) (hφ : MeasurePreserving φ μ μ), d = cutNormDiff U (pullback W φ hφ)}

/-- Cut distance is non-negative. -/
theorem cutDistance_nonneg (U W : Graphon α μ) : 0 ≤ cutDistance U W := by
  unfold cutDistance
  apply Real.sInf_nonneg
  intro d ⟨φ, hφ, hd⟩
  rw [hd]
  exact cutNormDiff_nonneg U (pullback W φ hφ)

/-- The set defining cut distance is nonempty (identity map always works). -/
theorem cutDistance_set_nonempty (U W : Graphon α μ) :
    {d : ℝ | ∃ (φ : α → α) (hφ : MeasurePreserving φ μ μ), d = cutNormDiff U (pullback W φ hφ)}.Nonempty :=
  ⟨cutNormDiff U (pullback W id (MeasurePreserving.id μ)), id, MeasurePreserving.id μ, rfl⟩

/-- Cut distance of a graphon to itself is zero. -/
theorem cutDistance_self (W : Graphon α μ) : cutDistance W W = 0 := by
  unfold cutDistance
  apply le_antisymm
  · -- Upper bound: use identity map
    apply csInf_le
    · -- Bounded below by 0
      use 0
      intro d ⟨φ, hφ, hd⟩
      rw [hd]
      exact cutNormDiff_nonneg W (pullback W φ hφ)
    · -- Identity gives 0
      refine ⟨id, MeasurePreserving.id μ, ?_⟩
      rw [pullback_id]
      exact (cutNormDiff_self W).symm
  · exact cutDistance_nonneg W W

/-- Cut distance is bounded by 1. -/
theorem cutDistance_le_one (U W : Graphon α μ) : cutDistance U W ≤ 1 := by
  unfold cutDistance
  have h_bdd : BddBelow {d : ℝ | ∃ (φ : α → α) (hφ : MeasurePreserving φ μ μ),
      d = cutNormDiff U (pullback W φ hφ)} := by
    use 0
    intro d ⟨φ, hφ, hd⟩
    rw [hd]
    exact cutNormDiff_nonneg U (pullback W φ hφ)
  -- The identity map gives cutNormDiff U W which is ≤ 1
  have h_in_set : cutNormDiff U W ∈ {d : ℝ | ∃ (φ : α → α) (hφ : MeasurePreserving φ μ μ),
      d = cutNormDiff U (pullback W φ hφ)} := by
    refine ⟨id, MeasurePreserving.id μ, ?_⟩
    rw [pullback_id]
  calc sInf {d : ℝ | ∃ (φ : α → α) (hφ : MeasurePreserving φ μ μ),
        d = cutNormDiff U (pullback W φ hφ)}
      ≤ cutNormDiff U W := csInf_le h_bdd h_in_set
    _ ≤ 1 := cutNormDiff_le_one U W

end CutDistance

end Graphon
