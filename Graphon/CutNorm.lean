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
  -- Step 1: Change of variables via swap
  -- ∫_{S×T} W(p) = ∫_{T×S} W(p.swap)
  rw [← setIntegral_prod_swap S T W.toAEEqFun]
  -- Step 2: Use symmetry W(p.swap) = W(p) a.e.
  apply setIntegral_congr_ae (hT.prod hS)
  -- Need to show: ∀ᵐ p ∂(μ.prod μ), p ∈ T ×ˢ S → W(p.swap) = W(p)
  have h_symm := W.symm'
  -- W.symm' says W(p.swap) = W(p) a.e., which is exactly what we need
  filter_upwards [h_symm] with p hp _
  exact hp

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

/-- Graphon values are bounded by 1 in absolute value. -/
theorem graphon_abs_le_one (W : Graphon α μ) :
    ∀ᵐ p ∂(μ.prod μ), |W.toAEEqFun p| ≤ 1 := by
  filter_upwards [W.ae_mem_Icc] with p hp
  rw [abs_le]
  exact ⟨by linarith [hp.1], hp.2⟩

/-- Graphons are integrable on probability spaces. -/
theorem graphon_integrable (W : Graphon α μ) : Integrable W.toAEEqFun (μ.prod μ) := by
  apply Integrable.of_mem_Icc 0 1
  · exact W.toAEEqFun.aemeasurable
  · exact W.ae_mem_Icc

/-- Rectangle integral of a graphon is bounded by 1. -/
theorem abs_rectIntegral_le_one (W : Graphon α μ) (S T : Set α) :
    |rectIntegral W.toSymmKernel S T| ≤ 1 := by
  simp only [rectIntegral]
  calc |∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ)|
      ≤ ∫ p in S ×ˢ T, |W.toAEEqFun p| ∂(μ.prod μ) := abs_integral_le_integral_abs
    _ ≤ ∫ _ in S ×ˢ T, (1 : ℝ) ∂(μ.prod μ) := by
        apply setIntegral_mono_ae_restrict
        · exact (graphon_integrable W).abs.integrableOn
        · exact integrable_const 1
        · exact ae_restrict_of_ae (graphon_abs_le_one W)
    _ = ((μ.prod μ) (S ×ˢ T)).toReal := by
        rw [setIntegral_const, smul_eq_mul, mul_one]
        rfl
    _ ≤ 1 := by
        have h_prob : IsProbabilityMeasure (μ.prod μ) := inferInstance
        have h_le : (μ.prod μ) (S ×ˢ T) ≤ ENNReal.ofReal 1 := by
          simp only [ENNReal.ofReal_one]
          calc (μ.prod μ) (S ×ˢ T) ≤ (μ.prod μ) univ := measure_mono (subset_univ _)
            _ = 1 := h_prob.measure_univ
        exact ENNReal.toReal_le_of_le_ofReal (by norm_num) h_le

/-- Cut norm bounds individual rectangle integrals.

For graphons this follows from boundedness of the function (values in [0,1]).
The proof requires showing the supremum is over a bounded-above set, which
follows from the graphon value bounds. -/
theorem abs_rectIntegral_le_cutNorm (W : Graphon α μ) {S T : Set α}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    |rectIntegral W.toSymmKernel S T| ≤ cutNorm W.toSymmKernel := by
  unfold cutNorm
  -- The rectangle integral is one of the terms in the supremum
  -- The set is bounded above by 1 (from abs_rectIntegral_le_one)
  have h_bound : ∀ S' T', |rectIntegral W.toSymmKernel S' T'| ≤ 1 :=
    fun S' T' => abs_rectIntegral_le_one W S' T'
  -- Extract the BddAbove property for nested iSup
  have hbS : BddAbove (Set.range fun S' =>
      ⨆ (_ : MeasurableSet S'), ⨆ T', ⨆ (_ : MeasurableSet T'), |rectIntegral W.toSymmKernel S' T'|) := by
    use 1
    rintro _ ⟨S', rfl⟩
    apply Real.iSup_le _ (by norm_num : (0:ℝ) ≤ 1)
    intro _
    apply Real.iSup_le _ (by norm_num : (0:ℝ) ≤ 1)
    intro T'
    apply Real.iSup_le _ (by norm_num : (0:ℝ) ≤ 1)
    intro _
    exact h_bound S' T'
  apply le_ciSup_of_le hbS S
  have hbhS : BddAbove (Set.range fun _ : MeasurableSet S =>
      ⨆ T', ⨆ (_ : MeasurableSet T'), |rectIntegral W.toSymmKernel S T'|) := by
    use 1
    rintro _ ⟨_, rfl⟩
    apply Real.iSup_le _ (by norm_num : (0:ℝ) ≤ 1)
    intro T'
    apply Real.iSup_le _ (by norm_num : (0:ℝ) ≤ 1)
    intro _
    exact h_bound S T'
  apply le_ciSup_of_le hbhS hS
  have hbT : BddAbove (Set.range fun T' =>
      ⨆ (_ : MeasurableSet T'), |rectIntegral W.toSymmKernel S T'|) := by
    use 1
    rintro _ ⟨T', rfl⟩
    apply Real.iSup_le _ (by norm_num : (0:ℝ) ≤ 1)
    intro _
    exact h_bound S T'
  apply le_ciSup_of_le hbT T
  have hbhT : BddAbove (Set.range fun _ : MeasurableSet T =>
      |rectIntegral W.toSymmKernel S T|) := by
    use 1
    rintro _ ⟨_, rfl⟩
    exact h_bound S T
  exact le_ciSup hbhT hT

/-- Cut norm for graphons is bounded by 1.

Since graphon values are in [0,1], the rectangle integral over any S × T
is at most μ(S) * μ(T) ≤ 1. -/
theorem cutNorm_le_one (W : Graphon α μ) : cutNorm W.toSymmKernel ≤ 1 := by
  unfold cutNorm
  apply Real.iSup_le _ (by norm_num : (0:ℝ) ≤ 1)
  intro S
  apply Real.iSup_le _ (by norm_num : (0:ℝ) ≤ 1)
  intro hS
  apply Real.iSup_le _ (by norm_num : (0:ℝ) ≤ 1)
  intro T
  apply Real.iSup_le _ (by norm_num : (0:ℝ) ≤ 1)
  intro hT
  -- For graphons: |∫_{S×T} W| ≤ ∫_{S×T} |W| ≤ ∫_{S×T} 1 = μ(S×T) ≤ 1
  simp only [rectIntegral]
  calc |∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ)|
      ≤ ∫ p in S ×ˢ T, |W.toAEEqFun p| ∂(μ.prod μ) := abs_integral_le_integral_abs
    _ ≤ ∫ _ in S ×ˢ T, (1 : ℝ) ∂(μ.prod μ) := by
        apply setIntegral_mono_ae_restrict
        · -- Integrability of |W|
          exact (graphon_integrable W).abs.integrableOn
        · -- Integrability of constant 1
          exact integrable_const 1
        · -- |W| ≤ 1 a.e. on S ×ˢ T
          have h_ae := graphon_abs_le_one W
          exact ae_restrict_of_ae h_ae
    _ = ((μ.prod μ) (S ×ˢ T)).toReal := by
        rw [setIntegral_const, smul_eq_mul, mul_one]
        rfl
    _ ≤ 1 := by
        have h_prob : IsProbabilityMeasure (μ.prod μ) := inferInstance
        have h_le : (μ.prod μ) (S ×ˢ T) ≤ 1 := by
          calc (μ.prod μ) (S ×ˢ T) ≤ (μ.prod μ) univ := measure_mono (subset_univ _)
            _ = 1 := h_prob.measure_univ
        have h_le' : (μ.prod μ) (S ×ˢ T) ≤ ENNReal.ofReal 1 := by
          simp only [ENNReal.ofReal_one]
          exact h_le
        exact ENNReal.toReal_le_of_le_ofReal (by norm_num) h_le'

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

/-! ### Weighted integrals and cut norm -/

section WeightedIntegral

variable [IsProbabilityMeasure μ]

/-- The key lemma for the counting lemma: weighted integrals are bounded by cut norm.

For f, g : α → [0, 1] measurable and K a graphon:
|∫∫ f(x) g(y) K(x,y) dμ(x) dμ(y)| ≤ ‖K‖_□

The proof approximates f and g by simple functions (linear combinations of
indicator functions of measurable sets). Since ‖K‖_□ bounds each rectangle
integral, it bounds the weighted sum by triangle inequality.

**Note**: This is Lemma 10.21 in Lovász [2012]. -/
theorem abs_weighted_integral_le_cutNorm (K : Graphon α μ) (f g : α → ℝ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_bound : ∀ x, f x ∈ Set.Icc 0 1) (hg_bound : ∀ x, g x ∈ Set.Icc 0 1) :
    |∫ x, ∫ y, f x * g y * K.toAEEqFun (x, y) ∂μ ∂μ| ≤ cutNorm K := by
  -- Strategy: Simple function approximation + dominated convergence.
  -- 1. For indicator functions 1_S, 1_T: the integral is rectIntegral K S T
  -- 2. For simple functions: by linearity, bounded by |coeff| * cutNorm K
  -- 3. General f, g: approximate by simple functions, use dominated convergence
  --
  -- The bound for indicators follows from weighted_integral_indicator below:
  --   |∫∫ 1_S 1_T K| = |rectIntegral K S T| ≤ cutNorm K
  --
  -- For simple functions f = Σᵢ aᵢ 1_{Sᵢ}, g = Σⱼ bⱼ 1_{Tⱼ}:
  --   ∫∫ f g K = Σᵢⱼ aᵢ bⱼ rectIntegral K Sᵢ Tⱼ
  --   |...| ≤ Σᵢⱼ |aᵢ| |bⱼ| |rectIntegral K Sᵢ Tⱼ|
  --        ≤ Σᵢⱼ |aᵢ| |bⱼ| cutNorm K
  --        = (Σᵢ |aᵢ|)(Σⱼ |bⱼ|) cutNorm K
  --
  -- When f, g ∈ [0,1], their L¹ norms are ≤ 1, so bound is cutNorm K.
  --
  -- The dominated convergence step uses:
  -- - Simple functions approximate measurable functions
  -- - The integrand is bounded by 1 (graphon bound)
  --
  -- This is Lemma 10.21 in Lovász [2012].
  sorry

/-- Special case: indicator functions give rectangle integrals.

This connects the weighted integral form to the rectangle integral definition. -/
theorem weighted_integral_indicator (K : Graphon α μ) (S T : Set α)
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ∫ x, ∫ y, S.indicator (fun _ => (1:ℝ)) x * T.indicator (fun _ => (1:ℝ)) y *
      K.toAEEqFun (x, y) ∂μ ∂μ = SymmKernel.rectIntegral K.toSymmKernel S T := by
  simp only [SymmKernel.rectIntegral]
  -- Step 1: Rewrite with indicator pulled into inner integral
  have h1 : ∀ x, ∫ y, S.indicator (fun _ => (1:ℝ)) x * T.indicator (fun _ => (1:ℝ)) y *
      K.toAEEqFun (x, y) ∂μ =
      S.indicator (fun x => ∫ y, T.indicator (fun _ => (1:ℝ)) y * K.toAEEqFun (x, y) ∂μ) x := by
    intro x
    by_cases hx : x ∈ S
    · simp only [indicator_of_mem hx, one_mul]
    · simp only [Set.indicator_of_notMem hx, zero_mul, integral_zero]
  simp_rw [h1]
  -- Step 2: Apply integral_indicator for outer integral
  rw [MeasureTheory.integral_indicator hS]
  -- Step 3: Deal with inner integral indicator
  have h2 : ∀ x, ∫ y, T.indicator (fun _ => (1:ℝ)) y * K.toAEEqFun (x, y) ∂μ =
      ∫ y in T, K.toAEEqFun (x, y) ∂μ := by
    intro x
    rw [← MeasureTheory.integral_indicator hT]
    congr 1
    ext y
    by_cases hy : y ∈ T
    · simp [indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  simp_rw [h2]
  -- Step 4: Apply setIntegral_prod (Fubini for set integrals)
  have h_int : IntegrableOn K.toAEEqFun (S ×ˢ T) (μ.prod μ) :=
    (SymmKernel.graphon_integrable K).integrableOn
  -- setIntegral_prod: ∫_{S×T} f z d(μ×ν) = ∫_S (∫_T f(x,y) dν) dμ
  exact (MeasureTheory.setIntegral_prod K.toAEEqFun h_int).symm

end WeightedIntegral

end Graphon
