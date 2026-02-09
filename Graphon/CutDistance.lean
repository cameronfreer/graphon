/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.CutNorm
import Graphon.Pullback
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Cut Distance for Graphons

This file defines the cut distance (also called cut metric) between graphons,
which is the fundamental metric for graphon convergence theory.

## Main definitions

* `Graphon.cutNormDiff` - The cut norm of the difference `‖U - W‖_□`
* `Graphon.cutDistance` - The cut distance `δ□(U, W) = inf_{φ,ψ} ‖U^φ - W^ψ‖_□` (two-sided)

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
  · -- Integrability of U on the rectangle
    exact (SymmKernel.graphon_integrable U).integrableOn
  · -- Integrability of W on the rectangle
    exact (SymmKernel.graphon_integrable W).integrableOn

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
  apply Real.iSup_nonneg
  intro S
  apply Real.iSup_nonneg
  intro _
  apply Real.iSup_nonneg
  intro T
  apply Real.iSup_nonneg
  intro _
  exact abs_nonneg _

/-- Helper: absolute value of rectangle integral difference is bounded by 1. -/
theorem abs_rectIntegralDiff_le_one (U W : Graphon α μ) (S T : Set α) :
    |rectIntegralDiff U W S T| ≤ 1 := by
  unfold rectIntegralDiff
  calc |∫ p in S ×ˢ T, (U.toAEEqFun p - W.toAEEqFun p) ∂(μ.prod μ)|
      ≤ ∫ p in S ×ˢ T, |U.toAEEqFun p - W.toAEEqFun p| ∂(μ.prod μ) := abs_integral_le_integral_abs
    _ ≤ ∫ _ in S ×ˢ T, (1 : ℝ) ∂(μ.prod μ) := by
        apply setIntegral_mono_ae_restrict
        · exact (SymmKernel.graphon_integrable U).sub (SymmKernel.graphon_integrable W) |>.abs.integrableOn
        · exact integrable_const 1
        · have hU_bound := U.ae_mem_Icc
          have hW_bound := W.ae_mem_Icc
          have h_diff_bound : ∀ᵐ p ∂(μ.prod μ), |U.toAEEqFun p - W.toAEEqFun p| ≤ 1 := by
            filter_upwards [hU_bound, hW_bound] with p hU_p hW_p
            rw [abs_le]
            constructor
            · linarith [hU_p.1, hW_p.2]
            · linarith [hU_p.2, hW_p.1]
          exact ae_restrict_of_ae h_diff_bound
    _ ≤ 1 := by
        rw [setIntegral_const, smul_eq_mul, mul_one]
        have h_prob : IsProbabilityMeasure (μ.prod μ) := inferInstance
        have h_le : (μ.prod μ) (S ×ˢ T) ≤ 1 := by
          calc (μ.prod μ) (S ×ˢ T) ≤ (μ.prod μ) univ := measure_mono (subset_univ _)
            _ = 1 := h_prob.measure_univ
        exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simp only [ENNReal.ofReal_one]; exact h_le)

/-- Rectangle integral difference is bounded by cut norm difference. -/
theorem abs_rectIntegralDiff_le (U W : Graphon α μ) {S T : Set α}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    |rectIntegralDiff U W S T| ≤ cutNormDiff U W := by
  unfold cutNormDiff
  -- Build bddAbove proofs using abs_rectIntegralDiff_le_one
  have h_bddS : BddAbove (Set.range fun S' =>
      ⨆ (_ : MeasurableSet S'), ⨆ T', ⨆ (_ : MeasurableSet T'), |rectIntegralDiff U W S' T'|) := by
    use 1
    rintro _ ⟨S', rfl⟩
    apply Real.iSup_le _ (by norm_num : (0:ℝ) ≤ 1)
    intro _
    apply Real.iSup_le _ (by norm_num : (0:ℝ) ≤ 1)
    intro T'
    apply Real.iSup_le _ (by norm_num : (0:ℝ) ≤ 1)
    intro _
    exact abs_rectIntegralDiff_le_one U W S' T'
  apply le_ciSup_of_le h_bddS S
  have h_bdd_hS : BddAbove (Set.range fun _ : MeasurableSet S =>
      ⨆ T', ⨆ (_ : MeasurableSet T'), |rectIntegralDiff U W S T'|) := by
    use 1
    rintro _ ⟨_, rfl⟩
    apply Real.iSup_le _ (by norm_num : (0:ℝ) ≤ 1)
    intro T'
    apply Real.iSup_le _ (by norm_num : (0:ℝ) ≤ 1)
    intro _
    exact abs_rectIntegralDiff_le_one U W S T'
  apply le_ciSup_of_le h_bdd_hS hS
  have h_bddT : BddAbove (Set.range fun T' =>
      ⨆ (_ : MeasurableSet T'), |rectIntegralDiff U W S T'|) := by
    use 1
    rintro _ ⟨T', rfl⟩
    apply Real.iSup_le _ (by norm_num : (0:ℝ) ≤ 1)
    intro _
    exact abs_rectIntegralDiff_le_one U W S T'
  apply le_ciSup_of_le h_bddT T
  have h_bddT' : BddAbove (Set.range fun _ : MeasurableSet T => |rectIntegralDiff U W S T|) := by
    use 1
    rintro x ⟨_, rfl⟩
    exact abs_rectIntegralDiff_le_one U W S T
  exact le_ciSup h_bddT' hT

/-- Cut norm difference with self is zero. -/
theorem cutNormDiff_self (W : Graphon α μ) : cutNormDiff W W = 0 := by
  unfold cutNormDiff rectIntegralDiff
  -- W - W = 0, so all rectangle integrals are 0
  simp only [sub_self, integral_zero, abs_zero]
  -- The supremum of constant 0 is 0
  apply le_antisymm
  · apply Real.iSup_le _ (le_refl 0)
    intro S
    apply Real.iSup_le _ (le_refl 0)
    intro _
    apply Real.iSup_le _ (le_refl 0)
    intro T
    apply Real.iSup_le _ (le_refl 0)
    intro _
    exact le_refl 0
  · apply Real.iSup_nonneg
    intro S
    apply Real.iSup_nonneg
    intro _
    apply Real.iSup_nonneg
    intro T
    apply Real.iSup_nonneg
    intro _
    exact le_refl 0

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

/-- Cut norm difference is bounded by 1.

Since U, W ∈ [0,1], we have U - W ∈ [-1,1], so |∫(U-W)| ≤ μ(S×T) ≤ 1. -/
theorem cutNormDiff_le_one (U W : Graphon α μ) : cutNormDiff U W ≤ 1 := by
  unfold cutNormDiff
  apply Real.iSup_le _ (by norm_num : (0:ℝ) ≤ 1)
  intro S
  apply Real.iSup_le _ (by norm_num : (0:ℝ) ≤ 1)
  intro _
  apply Real.iSup_le _ (by norm_num : (0:ℝ) ≤ 1)
  intro T
  apply Real.iSup_le _ (by norm_num : (0:ℝ) ≤ 1)
  intro _
  -- |∫_{S×T} (U-W)| ≤ ∫_{S×T} |U-W| ≤ ∫_{S×T} 1 = μ(S×T) ≤ 1
  simp only [rectIntegralDiff]
  -- Step 1: |∫ (U-W)| ≤ ∫ |U-W|
  calc |∫ p in S ×ˢ T, (U.toAEEqFun p - W.toAEEqFun p) ∂(μ.prod μ)|
      ≤ ∫ p in S ×ˢ T, |U.toAEEqFun p - W.toAEEqFun p| ∂(μ.prod μ) := abs_integral_le_integral_abs
    _ ≤ ∫ _ in S ×ˢ T, (1 : ℝ) ∂(μ.prod μ) := by
        -- |U - W| ≤ 1 a.e. since U, W ∈ [0,1]
        apply setIntegral_mono_ae_restrict
        · -- Integrability of |U - W|
          have hU := SymmKernel.graphon_integrable U
          have hW := SymmKernel.graphon_integrable W
          exact (hU.sub hW).abs.integrableOn
        · exact integrable_const 1
        · -- |U(p) - W(p)| ≤ 1 a.e.
          have hU_bound := U.ae_mem_Icc
          have hW_bound := W.ae_mem_Icc
          have h_diff_bound : ∀ᵐ p ∂(μ.prod μ), |U.toAEEqFun p - W.toAEEqFun p| ≤ 1 := by
            filter_upwards [hU_bound, hW_bound] with p hU_p hW_p
            rw [abs_le]
            constructor
            · linarith [hU_p.1, hW_p.2]
            · linarith [hU_p.2, hW_p.1]
          exact ae_restrict_of_ae h_diff_bound
    _ = ((μ.prod μ) (S ×ˢ T)).toReal := by
        rw [setIntegral_const, smul_eq_mul, mul_one]; rfl
    _ ≤ 1 := by
        have h_prob : IsProbabilityMeasure (μ.prod μ) := inferInstance
        have h_le : (μ.prod μ) (S ×ˢ T) ≤ 1 := by
          calc (μ.prod μ) (S ×ˢ T) ≤ (μ.prod μ) univ := measure_mono (subset_univ _)
            _ = 1 := h_prob.measure_univ
        exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simp only [ENNReal.ofReal_one]; exact h_le)

/-- Rectangle integral difference satisfies the triangle inequality. -/
theorem rectIntegralDiff_triangle (U V W : Graphon α μ) (S T : Set α) :
    |rectIntegralDiff U W S T| ≤ |rectIntegralDiff U V S T| + |rectIntegralDiff V W S T| := by
  unfold rectIntegralDiff
  -- (U - W) = (U - V) + (V - W), so |∫(U-W)| ≤ |∫(U-V)| + |∫(V-W)|
  have h_decomp : ∀ p, U.toAEEqFun p - W.toAEEqFun p =
      (U.toAEEqFun p - V.toAEEqFun p) + (V.toAEEqFun p - W.toAEEqFun p) := by
    intro p; ring
  have h_eq : ∫ p in S ×ˢ T, (U.toAEEqFun p - W.toAEEqFun p) ∂(μ.prod μ) =
      ∫ p in S ×ˢ T, ((U.toAEEqFun p - V.toAEEqFun p) + (V.toAEEqFun p - W.toAEEqFun p)) ∂(μ.prod μ) := by
    congr 1
    ext p
    exact h_decomp p
  rw [h_eq, integral_add]
  · exact abs_add_le _ _
  · exact (SymmKernel.graphon_integrable U).sub (SymmKernel.graphon_integrable V) |>.integrableOn
  · exact (SymmKernel.graphon_integrable V).sub (SymmKernel.graphon_integrable W) |>.integrableOn

/-- Cut norm difference satisfies the triangle inequality. -/
theorem cutNormDiff_triangle (U V W : Graphon α μ) :
    cutNormDiff U W ≤ cutNormDiff U V + cutNormDiff V W := by
  have hUV := cutNormDiff_nonneg U V
  have hVW := cutNormDiff_nonneg V W
  have hsum : 0 ≤ cutNormDiff U V + cutNormDiff V W := by linarith
  unfold cutNormDiff
  -- The supremum of |rect U W| is bounded by sup of |rect U V| + sup of |rect V W|
  -- For each rectangle, use rectIntegralDiff_triangle
  apply Real.iSup_le _ hsum
  intro S
  apply Real.iSup_le _ hsum
  intro hS
  apply Real.iSup_le _ hsum
  intro T
  apply Real.iSup_le _ hsum
  intro hT
  calc |rectIntegralDiff U W S T|
      ≤ |rectIntegralDiff U V S T| + |rectIntegralDiff V W S T| := rectIntegralDiff_triangle U V W S T
    _ ≤ cutNormDiff U V + cutNormDiff V W := by
        apply add_le_add
        · exact abs_rectIntegralDiff_le U V hS hT
        · exact abs_rectIntegralDiff_le V W hS hT

/-! ### Weighted integrals of differences -/

/-- Layer cake identity: For a ∈ [0,1], a = ∫_{(0,1]} 1_{s ≤ a} ds.

This is the pointwise version of the layer cake formula. -/
private lemma layer_cake_Icc (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    a = ∫ s in Set.Ioc 0 1, Set.indicator (Set.Iic a) (fun _ => (1:ℝ)) s := by
  rw [setIntegral_indicator measurableSet_Iic]
  have h_inter : Set.Ioc (0:ℝ) 1 ∩ Set.Iic a = Set.Ioc 0 (min a 1) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic]
    constructor
    · intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, le_min h3 h2⟩
    · intro ⟨h1, h2⟩
      have ht_le_1 : t ≤ 1 := h2.trans (min_le_right a 1)
      exact ⟨⟨h1, ht_le_1⟩, (min_le_left a 1).trans' h2⟩
  rw [h_inter, min_eq_left ha.2]
  by_cases ha0 : a ≤ 0
  · rw [le_antisymm ha0 ha.1, Set.Ioc_self]; simp
  · push_neg at ha0
    rw [setIntegral_const, smul_eq_mul, mul_one]
    unfold Measure.real
    rw [Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal ha0.le]

/-- Weighted integral of graphon difference bounded by cut norm difference (indicator case).

For measurable sets S, T:
|∫∫ 1_S(x) 1_T(y) (U(x,y) - W(x,y)) dμ(x) dμ(y)| ≤ ‖U - W‖_□

This follows directly from the cut norm definition. -/
theorem abs_weighted_integral_diff_indicator_le (U W : Graphon α μ) (S T : Set α)
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    |∫ x, ∫ y, S.indicator (fun _ => (1:ℝ)) x * T.indicator (fun _ => (1:ℝ)) y *
      (U.toAEEqFun (x, y) - W.toAEEqFun (x, y)) ∂μ ∂μ| ≤ cutNormDiff U W := by
  -- First, simplify the integral to a set integral
  -- Using similar logic to weighted_integral_indicator in CutNorm.lean
  have h1 : ∀ x, ∫ y, S.indicator (fun _ => (1:ℝ)) x * T.indicator (fun _ => (1:ℝ)) y *
      (U.toAEEqFun (x, y) - W.toAEEqFun (x, y)) ∂μ =
      S.indicator (fun x => ∫ y, T.indicator (fun _ => (1:ℝ)) y *
        (U.toAEEqFun (x, y) - W.toAEEqFun (x, y)) ∂μ) x := by
    intro x
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx, one_mul]
    · simp only [Set.indicator_of_notMem hx, zero_mul, integral_zero]
  simp_rw [h1]
  rw [MeasureTheory.integral_indicator hS]
  have h2 : ∀ x, ∫ y, T.indicator (fun _ => (1:ℝ)) y *
      (U.toAEEqFun (x, y) - W.toAEEqFun (x, y)) ∂μ =
      ∫ y in T, (U.toAEEqFun (x, y) - W.toAEEqFun (x, y)) ∂μ := by
    intro x
    rw [← MeasureTheory.integral_indicator hT]
    congr 1
    ext y
    by_cases hy : y ∈ T
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  simp_rw [h2]
  -- Now we have |∫_S ∫_T (U - W)| = |rectIntegralDiff U W S T|
  have h_int : IntegrableOn (fun p => U.toAEEqFun p - W.toAEEqFun p) (S ×ˢ T) (μ.prod μ) :=
    ((SymmKernel.graphon_integrable U).sub (SymmKernel.graphon_integrable W)).integrableOn
  rw [← MeasureTheory.setIntegral_prod _ h_int]
  -- This is exactly rectIntegralDiff
  have h_eq : ∫ p in S ×ˢ T, (U.toAEEqFun p - W.toAEEqFun p) ∂(μ.prod μ) = rectIntegralDiff U W S T := rfl
  rw [h_eq]
  exact abs_rectIntegralDiff_le U W hS hT

/-- Helper: For simple function g = Σⱼ cⱼ 1_{Tⱼ}, the weighted integral equals
an integral over [0,1] of rectangle integrals.

This is the layer cake formula for simple functions:
Σⱼ cⱼ · rectIntegralDiff S Tⱼ = ∫₀¹ rectIntegralDiff S {g ≥ t} dt

For simple functions, this is a finite sum computation (algebraic, no Fubini). -/
private lemma layer_cake_simple_eq (U W : Graphon α μ) (S : Set α) (hS : MeasurableSet S)
    (g : α → ℝ) (hg_meas : Measurable g) (hg_bound : ∀ y, g y ∈ Set.Icc 0 1)
    (hg_simple : ∃ (n : ℕ) (c : Fin n → ℝ) (T : Fin n → Set α),
      (∀ i, MeasurableSet (T i)) ∧ (∀ i, c i ∈ Set.Icc 0 1) ∧
      (∀ y, g y = ∑ i, c i * (T i).indicator (fun _ => (1:ℝ)) y) ∧
      (∀ i j, i ≠ j → Disjoint (T i) (T j))) :
    ∫ p, S.indicator (fun _ => (1:ℝ)) p.1 * g p.2 *
      (U.toAEEqFun p - W.toAEEqFun p) ∂(μ.prod μ) =
    ∫ t in Set.Ioc 0 1, rectIntegralDiff U W S {y | t ≤ g y} := by
  -- Both sides equal ∑ i, c i * rectIntegralDiff U W S (T i).
  obtain ⟨n, c, T, hT_meas, hc_bound, hg_eq, hT_disj⟩ := hg_simple
  set K : α × α → ℝ := fun p => U.toAEEqFun p - W.toAEEqFun p with hK_def
  have hK_int : Integrable K (μ.prod μ) :=
    (SymmKernel.graphon_integrable U).sub (SymmKernel.graphon_integrable W)
  -- Key helper: g(y) = c j for y ∈ T j
  have hg_val : ∀ j, ∀ y ∈ T j, g y = c j := by
    intro j y hy
    rw [hg_eq y, Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · simp [Set.indicator_of_mem hy]
    · intro i _ hi
      have : y ∉ T i := Set.disjoint_right.mp (hT_disj i j hi) hy
      simp [Set.indicator_of_notMem this]
  -- ===== LHS = ∑ i, c i * rectIntegralDiff U W S (T i) =====
  have h_term : ∀ p : α × α, S.indicator (fun _ => (1:ℝ)) p.1 * g p.2 * K p =
      ∑ i : Fin n, c i * (S ×ˢ T i).indicator K p := by
    intro p
    rw [hg_eq p.2]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    congr 1; ext i
    have h1 : S.indicator (fun _ => (1:ℝ)) p.1 *
        (c i * (T i).indicator (fun _ => (1:ℝ)) p.2) * K p =
        c i * (S.indicator (fun _ => (1:ℝ)) p.1 *
        (T i).indicator (fun _ => (1:ℝ)) p.2 * K p) := by ring
    rw [h1]; congr 1
    by_cases hp : p ∈ S ×ˢ T i
    · rw [Set.indicator_of_mem hp]
      obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
      simp [Set.indicator_of_mem hp1, Set.indicator_of_mem hp2]
    · rw [Set.indicator_of_notMem hp]
      rw [Set.mem_prod, not_and_or] at hp
      rcases hp with hp1 | hp2
      · simp [Set.indicator_of_notMem hp1]
      · simp [Set.indicator_of_notMem hp2]
  have h_lhs_eq : ∫ p, S.indicator (fun _ => (1:ℝ)) p.1 * g p.2 * K p ∂(μ.prod μ) =
      ∫ p, ∑ i : Fin n, c i * (S ×ˢ T i).indicator K p ∂(μ.prod μ) :=
    integral_congr_ae (Filter.Eventually.of_forall (fun p => h_term p))
  rw [h_lhs_eq]
  have h_lhs : ∫ p, ∑ i : Fin n, c i * (S ×ˢ T i).indicator K p ∂(μ.prod μ) =
      ∑ i : Fin n, c i * rectIntegralDiff U W S (T i) := by
    rw [integral_finset_sum]
    · congr 1; ext i
      rw [integral_const_mul, integral_indicator (hS.prod (hT_meas i))]
      rfl
    · intro i _
      exact (hK_int.indicator (hS.prod (hT_meas i))).const_mul _
  rw [h_lhs]
  -- ===== RHS = ∑ i, c i * rectIntegralDiff U W S (T i) =====
  -- Step 1: Level set decomposition: for t > 0, {y | t ≤ g y} = ⋃ (i with t ≤ c i), T i
  -- (outside ⋃ T i, g y = 0 so t ≤ g y fails for t > 0)
  have h_level : ∀ t : ℝ, 0 < t →
      {y | t ≤ g y} = ⋃ (i : Fin n) (_ : t ≤ c i), T i := by
    intro t ht
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hty
      -- g y ≥ t > 0, so g y > 0, so y must be in some T j, and c j ≥ t
      by_contra h_none
      push_neg at h_none
      -- h_none : ∀ i, t ≤ c i → y ∉ T i
      -- We'll show g y = 0, contradicting t ≤ g y with t > 0
      have hgy0 : g y = 0 := by
        rw [hg_eq]
        apply Finset.sum_eq_zero
        intro i _
        by_cases hy : y ∈ T i
        · -- y ∈ T i, so g y = c i ≥ t, but h_none says y ∉ T i
          exfalso
          exact h_none i (hty.trans (le_of_eq (hg_val i y hy))) hy
        · simp [Set.indicator_of_notMem hy]
      linarith
    · intro ⟨i, hci, hyi⟩
      rw [hg_val i y hyi]
      exact hci
  -- Step 2: rectIntegralDiff over union = sum (for each t > 0)
  have h_rect_union : ∀ t : ℝ, 0 < t →
      rectIntegralDiff U W S (⋃ (i : Fin n) (_ : t ≤ c i), T i) =
      ∑ i : Fin n, if t ≤ c i then rectIntegralDiff U W S (T i) else 0 := by
    intro t ht
    -- Rewrite the biUnion as a finset biUnion for easier manipulation
    have h_eq_union : (⋃ (i : Fin n) (_ : t ≤ c i), T i) =
        ⋃ i ∈ Finset.univ.filter (fun i => t ≤ c i), T i := by
      ext y; simp [Finset.mem_filter]
    rw [h_eq_union]
    unfold rectIntegralDiff
    rw [Set.prod_iUnion₂]
    have h_disj : Set.Pairwise
        (Finset.univ.filter (fun i => t ≤ c i) : Set (Fin n)) (fun i j => Disjoint (S ×ˢ T i) (S ×ˢ T j)) := by
      intro i _ j _ hij
      exact (hT_disj i j hij).set_prod_right S S
    rw [integral_biUnion_finset _ (fun i _ => hS.prod (hT_meas i)) h_disj
        (fun i _ => hK_int.integrableOn)]
    rw [Finset.sum_filter]
  -- Step 3: Rewrite RHS integral using level sets
  -- For t ∈ Ioc 0 1, t > 0 so we can use h_level
  have h_rhs_eq : ∫ t in Set.Ioc 0 1, rectIntegralDiff U W S {y | t ≤ g y} =
      ∫ t in Set.Ioc 0 1, ∑ i : Fin n,
        if t ≤ c i then rectIntegralDiff U W S (T i) else 0 := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [h_level t ht.1, h_rect_union t ht.1]
  rw [h_rhs_eq]
  -- Step 4: Swap integral and finite sum
  rw [integral_finset_sum]
  · -- Step 5: Compute each inner integral
    congr 1; ext i
    -- ∫ t in Ioc 0 1, (if t ≤ c i then R_i else 0) dt = c_i * R_i
    have h_ite_eq : ∀ t : ℝ,
        (if t ≤ c i then rectIntegralDiff U W S (T i) else 0) =
        (Set.Iic (c i)).indicator (fun _ => rectIntegralDiff U W S (T i)) t := by
      intro t
      by_cases h : t ≤ c i
      · simp [Set.mem_Iic.mpr h, h]
      · have : t ∉ Set.Iic (c i) := by simp [Set.mem_Iic]; linarith [not_le.mp h]
        simp [this, h]
    simp_rw [h_ite_eq]
    rw [setIntegral_indicator measurableSet_Iic]
    rw [Set.Ioc_inter_Iic, min_eq_right (hc_bound i).2]
    by_cases hci0 : c i ≤ 0
    · rw [le_antisymm hci0 (hc_bound i).1, Set.Ioc_self, setIntegral_empty, zero_mul]
    · push_neg at hci0
      rw [setIntegral_const, smul_eq_mul]
      congr 1
      unfold Measure.real
      rw [Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hci0.le]
  · intro i _
    have : (fun t => if t ≤ c i then rectIntegralDiff U W S (T i) else 0) =
        (Set.Iic (c i)).indicator (fun _ => rectIntegralDiff U W S (T i)) := by
      ext t; by_cases h : t ≤ c i
      · simp [Set.mem_Iic.mpr h, h]
      · have : t ∉ Set.Iic (c i) := by simp [Set.mem_Iic]; linarith [not_le.mp h]
        simp [this, h]
    rw [this]
    exact (integrable_const _).indicator measurableSet_Iic

/-- Helper: Indicator times general weight is bounded by cutNormDiff.

For measurable S and g : α → [0,1]:
|∫∫ 1_S(x) g(y) (U-W)(x,y) dμ²| ≤ cutNormDiff U W

This uses 1-fold layer cake on g:
∫∫ 1_S g (U-W) = ∫₀¹ rectIntegralDiff U W S {g≥t} dt -/
private lemma abs_weighted_integral_diff_indicator_general_le (U W : Graphon α μ)
    (S : Set α) (hS : MeasurableSet S) (g : α → ℝ)
    (hg_meas : Measurable g) (hg_bound : ∀ y, g y ∈ Set.Icc 0 1) :
    |∫ x, ∫ y, S.indicator (fun _ => (1:ℝ)) x * g y *
      (U.toAEEqFun (x, y) - W.toAEEqFun (x, y)) ∂μ ∂μ| ≤ cutNormDiff U W := by
  -- Level sets of g are measurable
  have hT_meas : ∀ t, MeasurableSet {y | t ≤ g y} := fun t => hg_meas measurableSet_Ici
  -- For each t, |rectIntegralDiff U W S {g≥t}| ≤ cutNormDiff
  have h_rect_bound : ∀ t, |rectIntegralDiff U W S {y | t ≤ g y}| ≤ cutNormDiff U W :=
    fun t => abs_rectIntegralDiff_le U W hS (hT_meas t)
  -- The integral ∫∫ 1_S g (U-W) = ∫₀¹ rectIntegralDiff U W S {g≥t} dt
  -- by layer cake on g.
  --
  -- Integrability setup
  have h_diff_int : Integrable (fun p => U.toAEEqFun p - W.toAEEqFun p) (μ.prod μ) :=
    (SymmKernel.graphon_integrable U).sub (SymmKernel.graphon_integrable W)
  have h_1g_bound : ∀ p : α × α, ‖S.indicator (fun _ => (1:ℝ)) p.1 * g p.2‖ ≤ 1 := fun p => by
    rw [Real.norm_eq_abs]
    by_cases hx : p.1 ∈ S
    · simp only [Set.indicator_of_mem hx]
      rw [one_mul, abs_of_nonneg (hg_bound p.2).1]
      exact (hg_bound p.2).2
    · simp only [Set.indicator_of_notMem hx, zero_mul, abs_zero, zero_le_one]
  have h_int : Integrable (fun p => S.indicator (fun _ => (1:ℝ)) p.1 * g p.2 *
      (U.toAEEqFun p - W.toAEEqFun p)) (μ.prod μ) := by
    apply Integrable.bdd_mul h_diff_int
    · exact ((measurable_const.indicator hS).comp measurable_fst).mul
        (hg_meas.comp measurable_snd) |>.aestronglyMeasurable
    · exact Filter.Eventually.of_forall h_1g_bound
  -- Convert to product measure
  have h_fubini : ∫ x, ∫ y, S.indicator (fun _ => (1:ℝ)) x * g y *
      (U.toAEEqFun (x, y) - W.toAEEqFun (x, y)) ∂μ ∂μ =
      ∫ p, S.indicator (fun _ => (1:ℝ)) p.1 * g p.2 * (U.toAEEqFun p - W.toAEEqFun p) ∂(μ.prod μ) :=
    (integral_prod _ h_int).symm
  rw [h_fubini]
  -- Strategy: Layer cake + Fubini, then triangle inequality.
  -- Define K = U - W and the layer cake integrand F(t, p) = 1_S(p.1) * 1_{t≤g(p.2)} * K(p).
  set K : α × α → ℝ := fun p => U.toAEEqFun p - W.toAEEqFun p with hK_def
  set F : ℝ → α × α → ℝ :=
    fun t p => S.indicator (fun _ => (1:ℝ)) p.1 *
      ({y : α | t ≤ g y}).indicator (fun _ => (1:ℝ)) p.2 * K p with hF_def
  -- Helper: |indicator of {0,1}-valued function| ≤ 1
  have abs_ind_le_one : ∀ (A : Set α) (x : α),
      |A.indicator (fun _ => (1:ℝ)) x| ≤ 1 := by
    intro A x
    by_cases hx : x ∈ A
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  -- |F(t,p)| ≤ |K(p)| for all t, p
  have hF_le_K : ∀ t p, |F t p| ≤ |K p| := by
    intro t p; simp only [hF_def]; rw [abs_mul, abs_mul]
    calc |S.indicator (fun _ => (1:ℝ)) p.1| *
          |({y : α | t ≤ g y}).indicator (fun _ => (1:ℝ)) p.2| * |K p|
        ≤ 1 * 1 * |K p| := by
          gcongr; exact abs_ind_le_one _ _; exact abs_ind_le_one _ _
      _ = |K p| := by ring
  -- K is integrable on μ²
  have hK_int : Integrable K (μ.prod μ) := h_diff_int
  -- Measurability of uncurry F
  -- uncurry F (t, p) = 1_S(p.1) * 1_{t ≤ g(p.2)} * K(p)
  -- The indicator 1_{t ≤ g(p.2)} as function of (t, p) is indicator of {q | q.1 ≤ g q.2.2}
  have hF_meas : Measurable (Function.uncurry F) := by
    simp only [hF_def]
    apply Measurable.mul
    · apply Measurable.mul
      · -- 1_S(p.1) as function of (t, p): measurable_const.indicator hS composed with snd.fst
        exact (measurable_const.indicator hS).comp (measurable_fst.comp measurable_snd)
      · -- 1_{t ≤ g(p.2)} as function of (t, p):
        -- This is the indicator of {(t, p) | t ≤ g(p.2)} = {q | q.1 ≤ g q.2.2}
        apply measurable_const.indicator
        exact measurableSet_le measurable_fst (hg_meas.comp (measurable_snd.comp measurable_snd))
    · exact (U.toAEEqFun.measurable.sub W.toAEEqFun.measurable).comp measurable_snd
  -- Integrability of uncurry F on (vol.restrict Ioc 0 1) × (μ.prod μ)
  have hF_int : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioc (0:ℝ) 1)).prod (μ.prod μ)) := by
    rw [integrable_prod_iff hF_meas.aestronglyMeasurable]
    constructor
    · -- For a.e. t, F(t, ·) is integrable on μ²
      apply Filter.Eventually.of_forall
      intro t
      apply Integrable.bdd_mul hK_int
      · exact ((measurable_const.indicator hS).comp measurable_fst).mul
            ((measurable_const.indicator (hT_meas t)).comp measurable_snd)
          |>.aestronglyMeasurable
      · apply Filter.Eventually.of_forall
        intro p; rw [Real.norm_eq_abs, abs_mul]
        calc |S.indicator (fun _ => (1:ℝ)) p.1| *
              |({y | t ≤ g y}).indicator (fun _ => (1:ℝ)) p.2|
            ≤ 1 * 1 := by gcongr; exact abs_ind_le_one _ _; exact abs_ind_le_one _ _
          _ = 1 := one_mul 1
    · -- ∫ ‖F(t, p)‖ dμ² is integrable in t on Ioc 0 1
      -- Since |F(t,p)| ≤ |K(p)| and K integrable, ∫ |F(t,·)| dμ² ≤ ∫ |K| dμ² (a constant).
      -- A bounded AEStronglyMeasurable function is integrable on a finite measure space.
      have hF_norm_bound : ∀ t : ℝ,
          ∫ p, ‖Function.uncurry F (t, p)‖ ∂(μ.prod μ) ≤ ∫ p, |K p| ∂(μ.prod μ) := by
        intro t
        apply integral_mono_of_nonneg
        · apply Filter.Eventually.of_forall; intro p; exact norm_nonneg _
        · exact hK_int.abs
        · apply Filter.Eventually.of_forall; intro p
          simp only [Function.uncurry, Real.norm_eq_abs]
          exact hF_le_K t p
      -- The function t ↦ ∫ ‖F(t,·)‖ is AEStronglyMeasurable
      have hF_norm_aesm : AEStronglyMeasurable
          (fun t => ∫ p, ‖Function.uncurry F (t, p)‖ ∂(μ.prod μ))
          (volume.restrict (Set.Ioc 0 1)) :=
        hF_meas.norm.aestronglyMeasurable.integral_prod_right'
      exact Integrable.of_bound hF_norm_aesm (∫ p, |K p| ∂(μ.prod μ))
        (Filter.Eventually.of_forall (fun t => by
          rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun p => norm_nonneg _))]
          exact hF_norm_bound t))
  -- Fubini: swap order of integration
  -- integral_integral_swap gives:
  --   ∫ t, (∫ p, F t p ∂μ²) ∂vol.restrict = ∫ p, (∫ t, F t p ∂vol.restrict) ∂μ²
  have h_swap : ∫ t, ∫ p, F t p ∂(μ.prod μ) ∂(volume.restrict (Set.Ioc 0 1)) =
      ∫ p, ∫ t, F t p ∂(volume.restrict (Set.Ioc 0 1)) ∂(μ.prod μ) :=
    integral_integral_swap hF_int
  -- Inner integral over t gives 1_S * g * K (by layer cake pointwise)
  have h_inner_t : ∀ p, ∫ t, F t p ∂(volume.restrict (Set.Ioc 0 1)) =
      S.indicator (fun _ => (1:ℝ)) p.1 * g p.2 * K p := by
    intro p; simp only [hF_def]
    -- Show: ∫ t in Ioc 0 1, 1_S(p.1) * 1_{t≤g}(p.2) * K(p) = 1_S(p.1) * g(p.2) * K(p)
    -- Factor out constants (1_S(p.1) and K(p)) from the integral
    rw [show (fun t => S.indicator (fun _ => (1:ℝ)) p.1 *
        ({y | t ≤ g y}).indicator (fun _ => (1:ℝ)) p.2 * K p) =
        (fun t => (S.indicator (fun _ => (1:ℝ)) p.1 * K p) *
        ({y | t ≤ g y}).indicator (fun _ => (1:ℝ)) p.2) from funext (fun t => by ring)]
    rw [integral_const_mul]
    -- Goal: (1_S * K) * ∫ 1_{t≤g} dt = 1_S * g * K
    -- The integral ∫ 1_{t ≤ g(p.2)} dt = g(p.2) by layer_cake_Icc
    have h_gp : g p.2 ∈ Set.Icc 0 1 := hg_bound p.2
    have h_layer : ∫ t in Set.Ioc 0 1,
        ({y : α | t ≤ g y}).indicator (fun _ => (1:ℝ)) p.2 = g p.2 := by
      -- Key: ({y | t ≤ g y}).indicator (fun _ => 1) p.2 equals 1 iff t ≤ g(p.2)
      -- which is the same as (Iic (g p.2)).indicator (fun _ => 1) t
      have h_ind_eq : (fun t : ℝ => ({y : α | t ≤ g y}).indicator (fun _ => (1:ℝ)) p.2) =
          (fun t : ℝ => (Set.Iic (g p.2)).indicator (fun _ => (1:ℝ)) t) := by
        funext t
        by_cases h : t ≤ g p.2
        · simp [Set.indicator_of_mem (show p.2 ∈ {y : α | t ≤ g y} from h),
                Set.indicator_of_mem (Set.mem_Iic.mpr h)]
        · push_neg at h
          simp [Set.indicator_of_notMem (show p.2 ∉ {y : α | t ≤ g y} from not_le.mpr h),
                Set.indicator_of_notMem (show t ∉ Set.Iic (g p.2) from not_le.mpr h)]
      rw [h_ind_eq]
      exact (layer_cake_Icc (g p.2) h_gp).symm
    rw [h_layer]; ring
  -- Inner integral over p gives rectIntegralDiff
  have h_inner_p : ∀ t, ∫ p, F t p ∂(μ.prod μ) =
      rectIntegralDiff U W S {y | t ≤ g y} := by
    intro t
    -- F(t, p) = 1_S(p.1) * 1_{t≤g}(p.2) * K(p) = (S ×ˢ {y|t≤g y}).indicator K p
    have h_eq : F t = (S ×ˢ {y | t ≤ g y}).indicator K := by
      ext p
      simp only [hF_def]
      by_cases hpS : p.1 ∈ S <;> by_cases hpT : p.2 ∈ {y | t ≤ g y}
      · simp [Set.indicator_of_mem hpS, Set.indicator_of_mem hpT,
              Set.indicator_of_mem (Set.mem_prod.mpr ⟨hpS, hpT⟩)]
      · have : p ∉ S ×ˢ {y | t ≤ g y} := by
              rw [Set.mem_prod, not_and_or]; exact Or.inr hpT
        simp [Set.indicator_of_mem hpS, Set.indicator_of_notMem hpT,
              Set.indicator_of_notMem this]
      · have : p ∉ S ×ˢ {y | t ≤ g y} := by
              rw [Set.mem_prod, not_and_or]; exact Or.inl hpS
        simp [Set.indicator_of_notMem hpS, Set.indicator_of_notMem this]
      · have : p ∉ S ×ˢ {y | t ≤ g y} := by
              rw [Set.mem_prod, not_and_or]; exact Or.inl hpS
        simp [Set.indicator_of_notMem hpS, Set.indicator_of_notMem this]
    rw [h_eq, integral_indicator (hS.prod (hT_meas t))]
    rfl
  -- Main argument: rewrite LHS via Fubini, then bound
  -- The key chain:
  --   ∫ p, 1_S*g*K ∂μ² = ∫ p, (∫ t in Ioc 0 1, F t p) ∂μ²  (by h_inner_t)
  --                      = ∫ t in Ioc 0 1, (∫ p, F t p ∂μ²)  (by h_swap, Fubini)
  --                      = ∫ t in Ioc 0 1, rectIntegralDiff   (by h_inner_p)
  have h_eq_layer : ∫ p, S.indicator (fun _ => (1:ℝ)) p.1 * g p.2 * K p ∂(μ.prod μ) =
      ∫ t in Set.Ioc 0 1, rectIntegralDiff U W S {y | t ≤ g y} := by
    have h1 : ∫ p, S.indicator (fun _ => (1:ℝ)) p.1 * g p.2 * K p ∂(μ.prod μ) =
        ∫ p, (∫ t, F t p ∂(volume.restrict (Set.Ioc 0 1))) ∂(μ.prod μ) := by
      congr 1; ext p; exact (h_inner_t p).symm
    rw [h1, ← h_swap]
    congr 1; ext t; exact h_inner_p t
  -- The goal is |∫ p, 1_S*g*(U-W)| ≤ cutNormDiff. Since set K := U-W, unfold:
  change |∫ p, S.indicator (fun _ => (1:ℝ)) p.1 * g p.2 * K p ∂(μ.prod μ)| ≤ _
  rw [h_eq_layer]
  -- Goal: |∫ t in Ioc 0 1, rectIntegralDiff U W S {y | t ≤ g y}| ≤ cutNormDiff U W
  have h_vol_Ioc : (volume (Set.Ioc (0:ℝ) 1)).toReal = 1 := by
    rw [Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1)]
  have h_Ioc_finite : (volume (Set.Ioc (0:ℝ) 1)) < ⊤ := by
    rw [Real.volume_Ioc, sub_zero]; exact ENNReal.ofReal_lt_top
  calc |∫ t in Set.Ioc 0 1, rectIntegralDiff U W S {y | t ≤ g y}|
      = ‖∫ t in Set.Ioc 0 1, rectIntegralDiff U W S {y | t ≤ g y}‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ cutNormDiff U W * (volume (Set.Ioc (0:ℝ) 1)).toReal :=
        norm_setIntegral_le_of_norm_le_const h_Ioc_finite
          (fun t _ => by rw [Real.norm_eq_abs]; exact h_rect_bound t)
    _ = cutNormDiff U W * 1 := by rw [h_vol_Ioc]
    _ = cutNormDiff U W := mul_one _

/-- General weighted integral of graphon difference bounded by cut norm difference.

For f, g : α → [0, 1] measurable and graphons U, W:
|∫∫ f(x) g(y) (U(x,y) - W(x,y)) dμ(x) dμ(y)| ≤ ‖U - W‖_□

Uses nested layer cake: first on f (reducing to indicator case), then on g.
This is Lemma 10.21 in Lovász [2012]. -/
theorem abs_weighted_integral_diff_le (U W : Graphon α μ) (f g : α → ℝ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_bound : ∀ x, f x ∈ Set.Icc 0 1) (hg_bound : ∀ x, g x ∈ Set.Icc 0 1) :
    |∫ x, ∫ y, f x * g y * (U.toAEEqFun (x, y) - W.toAEEqFun (x, y)) ∂μ ∂μ| ≤
      cutNormDiff U W := by
  -- Level sets are measurable
  have hS_meas : ∀ s, MeasurableSet {x | s ≤ f x} := fun s => hf_meas measurableSet_Ici
  have hT_meas : ∀ t, MeasurableSet {y | t ≤ g y} := fun t => hg_meas measurableSet_Ici
  -- The indicator bound (already proven) gives:
  -- |∫∫ 1_{f≥s} 1_{g≥t} (U-W)| ≤ cutNormDiff U W for all s, t
  have h_indicator_bound : ∀ s t, |rectIntegralDiff U W {x | s ≤ f x} {y | t ≤ g y}| ≤
      cutNormDiff U W := fun s t => abs_rectIntegralDiff_le U W (hS_meas s) (hT_meas t)
  -- Step 1: Convert to product measure form
  have h_diff_int : Integrable (fun p => U.toAEEqFun p - W.toAEEqFun p) (μ.prod μ) :=
    (SymmKernel.graphon_integrable U).sub (SymmKernel.graphon_integrable W)
  have h_fg_bound : ∀ p : α × α, ‖f p.1 * g p.2‖ ≤ 1 := fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf_bound p.1).1 (hg_bound p.2).1)]
    exact mul_le_one₀ (hf_bound p.1).2 (hg_bound p.2).1 (hg_bound p.2).2
  have h_fgK_int : Integrable (fun p => f p.1 * g p.2 * (U.toAEEqFun p - W.toAEEqFun p)) (μ.prod μ) := by
    apply Integrable.bdd_mul h_diff_int
    · exact (hf_meas.comp measurable_fst).mul (hg_meas.comp measurable_snd) |>.aestronglyMeasurable
    · exact Filter.Eventually.of_forall h_fg_bound
  have h_fubini : ∫ x, ∫ y, f x * g y * (U.toAEEqFun (x, y) - W.toAEEqFun (x, y)) ∂μ ∂μ =
      ∫ p, f p.1 * g p.2 * (U.toAEEqFun p - W.toAEEqFun p) ∂(μ.prod μ) := (integral_prod _ h_fgK_int).symm
  rw [h_fubini]
  -- Step 2: Layer cake decomposition (Lovász Lemma 10.21)
  --
  -- **Key identity**: For a ∈ [0,1], a = ∫_{(0,1]} 1_{s ≤ a} ds (see `layer_cake_Icc`)
  --
  -- **Product**: f(x)*g(y) = ∫∫_{(0,1]²} 1_{s ≤ f(x)} 1_{t ≤ g(y)} ds dt
  --
  -- **Main decomposition** (applying Fubini on (α×α) × ([0,1]×[0,1])):
  --   ∫_{α²} f(x) g(y) K(x,y) dμ² = ∫_{(0,1]²} rectIntegral K {f≥s} {g≥t} ds dt
  --
  -- For K = U - W:
  --   ∫_{α²} fg(U-W) = ∫_{(0,1]²} rectIntegralDiff U W {f≥s} {g≥t} ds dt
  --
  -- **Bound**:
  --   |...| ≤ ∫_{(0,1]²} |rectIntegralDiff U W {f≥s} {g≥t}| ds dt
  --       ≤ ∫_{(0,1]²} cutNormDiff U W ds dt
  --       = cutNormDiff U W (since volume([0,1]²) = 1)
  --
  -- **Technical justification for Fubini**:
  -- 1. Measurability: The integrand (x,y,s,t) ↦ 1_{s≤f(x)} 1_{t≤g(y)} (U-W)(x,y)
  --    is measurable on (α×α) × (ℝ×ℝ) as composition of measurable maps.
  -- 2. σ-finiteness: μ.prod μ (probability) and volume|_{(0,1]²} are σ-finite.
  -- 3. Integrability: |integrand| ≤ 2 on a finite measure space.
  --
  -- The 4-fold Fubini interchange is a standard but technical construction.
  -- This lemma corresponds to Lovász [2012], Lemma 10.21.
  sorry

end CutNormDiff

/-! ### Cut distance -/

section CutDistance

variable [IsProbabilityMeasure μ]

/-- The cut distance between two graphons on the same probability space.

`δ□(U, W) = inf_{φ,ψ} ‖U^φ - W^ψ‖_□`

where the infimum is over all measure-preserving maps `φ, ψ : α → α`.

**Design note**: This two-sided definition reparametrizes BOTH graphons, making symmetry
trivial by construction (swap φ and ψ). This matches the standard definition in Lovász
which uses measure-preserving maps from a common probability space to both graphon spaces.

The one-sided definition `inf_φ ‖U - W^φ‖_□` requires `[StandardBorelSpace α]` to prove
symmetry (via invertibility of measure-preserving maps). The two-sided definition avoids
this requirement while giving the same value on standard Borel spaces. -/
noncomputable def cutDistance (U W : Graphon α μ) : ℝ :=
  sInf {d : ℝ | ∃ (φ ψ : α → α) (hφ : MeasurePreserving φ μ μ) (hψ : MeasurePreserving ψ μ μ),
        d = cutNormDiff (pullback U φ hφ) (pullback W ψ hψ)}

/-- Cut distance is non-negative. -/
theorem cutDistance_nonneg (U W : Graphon α μ) : 0 ≤ cutDistance U W := by
  unfold cutDistance
  apply Real.sInf_nonneg
  intro d ⟨φ, ψ, hφ, hψ, hd⟩
  rw [hd]
  exact cutNormDiff_nonneg (pullback U φ hφ) (pullback W ψ hψ)

/-- The set defining cut distance is nonempty (identity maps always work). -/
theorem cutDistance_set_nonempty (U W : Graphon α μ) :
    {d : ℝ | ∃ (φ ψ : α → α) (hφ : MeasurePreserving φ μ μ) (hψ : MeasurePreserving ψ μ μ),
        d = cutNormDiff (pullback U φ hφ) (pullback W ψ hψ)}.Nonempty :=
  ⟨cutNormDiff (pullback U id (MeasurePreserving.id μ)) (pullback W id (MeasurePreserving.id μ)),
   id, id, MeasurePreserving.id μ, MeasurePreserving.id μ, rfl⟩

/-- Cut distance of a graphon to itself is zero. -/
theorem cutDistance_self (W : Graphon α μ) : cutDistance W W = 0 := by
  unfold cutDistance
  apply le_antisymm
  · -- Upper bound: use identity maps for both
    apply csInf_le
    · -- Bounded below by 0
      use 0
      intro d ⟨φ, ψ, hφ, hψ, hd⟩
      rw [hd]
      exact cutNormDiff_nonneg (pullback W φ hφ) (pullback W ψ hψ)
    · -- Both identity maps give 0
      refine ⟨id, id, MeasurePreserving.id μ, MeasurePreserving.id μ, ?_⟩
      simp only [pullback_id]
      exact (cutNormDiff_self W).symm
  · exact cutDistance_nonneg W W

/-- Cut distance is bounded by 1. -/
theorem cutDistance_le_one (U W : Graphon α μ) : cutDistance U W ≤ 1 := by
  unfold cutDistance
  have h_bdd : BddBelow {d : ℝ | ∃ (φ ψ : α → α) (hφ : MeasurePreserving φ μ μ)
      (hψ : MeasurePreserving ψ μ μ), d = cutNormDiff (pullback U φ hφ) (pullback W ψ hψ)} := by
    use 0
    intro d ⟨φ, ψ, hφ, hψ, hd⟩
    rw [hd]
    exact cutNormDiff_nonneg (pullback U φ hφ) (pullback W ψ hψ)
  -- Identity maps give cutNormDiff U W which is ≤ 1
  have h_in_set : cutNormDiff U W ∈ {d : ℝ | ∃ (φ ψ : α → α) (hφ : MeasurePreserving φ μ μ)
      (hψ : MeasurePreserving ψ μ μ), d = cutNormDiff (pullback U φ hφ) (pullback W ψ hψ)} := by
    refine ⟨id, id, MeasurePreserving.id μ, MeasurePreserving.id μ, ?_⟩
    rw [pullback_id, pullback_id]
  calc sInf {d : ℝ | ∃ (φ ψ : α → α) (hφ : MeasurePreserving φ μ μ)
        (hψ : MeasurePreserving ψ μ μ), d = cutNormDiff (pullback U φ hφ) (pullback W ψ hψ)}
      ≤ cutNormDiff U W := csInf_le h_bdd h_in_set
    _ ≤ 1 := cutNormDiff_le_one U W

/-- Triangle inequality for cut distance on standard Borel spaces.

δ□(U, W) ≤ δ□(U, V) + δ□(V, W)

This is the key property making cut distance a pseudometric.

**Hypothesis**: Requires `[StandardBorelSpace α]` for the "common representation"
trick where measure-preserving maps can be aligned via Rokhlin's theorem.

**Proof sketch** (Lovász, Section 8.2):
1. For any ε > 0, choose (φ₁, ψ₁) with cutNormDiff(U^φ₁, V^ψ₁) < δ□(U,V) + ε/2
2. Choose (φ₂, ψ₂) with cutNormDiff(V^φ₂, W^ψ₂) < δ□(V,W) + ε/2
3. On StandardBorel, by Rokhlin's theorem, there exists a measure-preserving χ
   such that V^ψ₁ and V^φ₂ have a common representation V^χ up to a.e. equality
4. By cutNormDiff_triangle:
   cutNormDiff(U^φ₁', W^ψ₂') ≤ cutNormDiff(U^φ₁', V^χ) + cutNormDiff(V^χ, W^ψ₂')
5. With appropriate compositions φ₁' = φ₁ and ψ₂' = ψ₂:
   ≤ (δ□(U,V) + ε/2) + (δ□(V,W) + ε/2) = δ□(U,V) + δ□(V,W) + ε
6. Taking inf over all (φ, ψ) and ε → 0 gives the result. -/
theorem cutDistance_triangle [StandardBorelSpace α] (U V W : Graphon α μ) :
    cutDistance U W ≤ cutDistance U V + cutDistance V W := by
  -- Full proof requires formalizing the common representation trick,
  -- which uses Rokhlin's theorem for measure-preserving maps on StandardBorel.
  sorry

/-- Cut distance is symmetric.

δ□(U, W) = δ□(W, U)

With the two-sided definition, this is immediate by swapping φ and ψ
and using the symmetry of cutNormDiff. No StandardBorelSpace needed! -/
theorem cutDistance_symm (U W : Graphon α μ) : cutDistance U W = cutDistance W U := by
  unfold cutDistance
  congr 1
  ext d
  constructor
  · rintro ⟨φ, ψ, hφ, hψ, hd⟩
    exact ⟨ψ, φ, hψ, hφ, by rw [hd, cutNormDiff_symm]⟩
  · rintro ⟨ψ, φ, hψ, hφ, hd⟩
    exact ⟨φ, ψ, hφ, hψ, by rw [hd, cutNormDiff_symm]⟩

end CutDistance

end Graphon
