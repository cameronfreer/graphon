/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.CutNorm
import Graphon.Pullback
import Graphon.MeasureIso
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

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
@[blueprint "def:cutNormDiff"
  (title := /-- Cut norm difference -/)]
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
  · push Not at ha0
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
    rw [integral_finsetSum]
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
      push Not at h_none
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
  rw [integral_finsetSum]
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
    · push Not at hci0
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
        · push Not at h
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
  --
  -- Proof: Layer cake on f, reducing to the indicator case (already proved).
  set K : α × α → ℝ := fun p => U.toAEEqFun p - W.toAEEqFun p with hK_def
  -- F(s, p) = 1_{s≤f(p.1)} * g(p.2) * K(p)
  set F : ℝ → α × α → ℝ :=
    fun s p => ({x : α | s ≤ f x}).indicator (fun _ => (1:ℝ)) p.1 * g p.2 * K p with hF_def
  -- Helper: |indicator| ≤ 1
  have abs_ind_le_one : ∀ (A : Set α) (x : α),
      |A.indicator (fun _ => (1:ℝ)) x| ≤ 1 := by
    intro A x
    by_cases hx : x ∈ A
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  -- |F(s,p)| ≤ |g(p.2)| * |K(p)| ≤ |K(p)|
  have hF_le_K : ∀ s p, |F s p| ≤ |K p| := by
    intro s p; simp only [hF_def]; rw [abs_mul, abs_mul]
    calc |({x : α | s ≤ f x}).indicator (fun _ => (1:ℝ)) p.1| * |g p.2| * |K p|
        ≤ 1 * 1 * |K p| := by
          gcongr
          · exact abs_ind_le_one _ _
          · rw [abs_of_nonneg (hg_bound p.2).1]; exact (hg_bound p.2).2
      _ = |K p| := by ring
  -- K is integrable on μ²
  have hK_int : Integrable K (μ.prod μ) := h_diff_int
  -- Measurability of uncurry F
  have hF_meas : Measurable (Function.uncurry F) := by
    simp only [hF_def]
    apply Measurable.mul
    · apply Measurable.mul
      · -- 1_{s ≤ f(p.1)} as function of (s, p):
        -- This is the indicator of {(s, p) | s ≤ f(p.1)} = {q | q.1 ≤ f q.2.1}
        apply measurable_const.indicator
        exact measurableSet_le measurable_fst (hf_meas.comp (measurable_fst.comp measurable_snd))
      · -- g(p.2) as function of (s, p)
        exact hg_meas.comp (measurable_snd.comp measurable_snd)
    · exact (U.toAEEqFun.measurable.sub W.toAEEqFun.measurable).comp measurable_snd
  -- Integrability of uncurry F on (vol.restrict Ioc 0 1) × (μ.prod μ)
  have hF_int : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioc (0:ℝ) 1)).prod (μ.prod μ)) := by
    rw [integrable_prod_iff hF_meas.aestronglyMeasurable]
    constructor
    · -- For a.e. s, F(s, ·) is integrable on μ²
      apply Filter.Eventually.of_forall
      intro s
      apply Integrable.bdd_mul hK_int
      · exact ((measurable_const.indicator (hS_meas s)).comp measurable_fst).mul
            (hg_meas.comp measurable_snd)
          |>.aestronglyMeasurable
      · apply Filter.Eventually.of_forall
        intro p; rw [Real.norm_eq_abs, abs_mul]
        calc |({x | s ≤ f x}).indicator (fun _ => (1:ℝ)) p.1| * |g p.2|
            ≤ 1 * 1 := by
              gcongr
              · exact abs_ind_le_one _ _
              · rw [abs_of_nonneg (hg_bound p.2).1]; exact (hg_bound p.2).2
          _ = 1 := one_mul 1
    · -- ∫ ‖F(s, p)‖ dμ² is integrable in s on Ioc 0 1
      have hF_norm_bound : ∀ s : ℝ,
          ∫ p, ‖Function.uncurry F (s, p)‖ ∂(μ.prod μ) ≤ ∫ p, |K p| ∂(μ.prod μ) := by
        intro s
        apply integral_mono_of_nonneg
        · apply Filter.Eventually.of_forall; intro p; exact norm_nonneg _
        · exact hK_int.abs
        · apply Filter.Eventually.of_forall; intro p
          simp only [Function.uncurry, Real.norm_eq_abs]
          exact hF_le_K s p
      have hF_norm_aesm : AEStronglyMeasurable
          (fun s => ∫ p, ‖Function.uncurry F (s, p)‖ ∂(μ.prod μ))
          (volume.restrict (Set.Ioc 0 1)) :=
        hF_meas.norm.aestronglyMeasurable.integral_prod_right'
      exact Integrable.of_bound hF_norm_aesm (∫ p, |K p| ∂(μ.prod μ))
        (Filter.Eventually.of_forall (fun s => by
          rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun p => norm_nonneg _))]
          exact hF_norm_bound s))
  -- Fubini: swap order of integration
  have h_swap : ∫ s, ∫ p, F s p ∂(μ.prod μ) ∂(volume.restrict (Set.Ioc 0 1)) =
      ∫ p, ∫ s, F s p ∂(volume.restrict (Set.Ioc 0 1)) ∂(μ.prod μ) :=
    integral_integral_swap hF_int
  -- Inner integral over s gives f(p.1) * g(p.2) * K(p) by layer cake
  have h_inner_s : ∀ p, ∫ s, F s p ∂(volume.restrict (Set.Ioc 0 1)) =
      f p.1 * g p.2 * K p := by
    intro p; simp only [hF_def]
    -- Factor out g(p.2) and K(p)
    rw [show (fun s => ({x | s ≤ f x}).indicator (fun _ => (1:ℝ)) p.1 * g p.2 * K p) =
        (fun s => (g p.2 * K p) *
        ({x | s ≤ f x}).indicator (fun _ => (1:ℝ)) p.1) from funext (fun s => by ring)]
    rw [integral_const_mul]
    -- The integral ∫ 1_{s ≤ f(p.1)} ds = f(p.1) by layer_cake_Icc
    have h_fp : f p.1 ∈ Set.Icc 0 1 := hf_bound p.1
    have h_layer : ∫ s in Set.Ioc 0 1,
        ({x : α | s ≤ f x}).indicator (fun _ => (1:ℝ)) p.1 = f p.1 := by
      have h_ind_eq : (fun s : ℝ => ({x : α | s ≤ f x}).indicator (fun _ => (1:ℝ)) p.1) =
          (fun s : ℝ => (Set.Iic (f p.1)).indicator (fun _ => (1:ℝ)) s) := by
        funext s
        by_cases h : s ≤ f p.1
        · simp [Set.indicator_of_mem (show p.1 ∈ {x : α | s ≤ f x} from h),
                Set.indicator_of_mem (Set.mem_Iic.mpr h)]
        · push Not at h
          simp [Set.indicator_of_notMem (show p.1 ∉ {x : α | s ≤ f x} from not_le.mpr h),
                Set.indicator_of_notMem (show s ∉ Set.Iic (f p.1) from not_le.mpr h)]
      rw [h_ind_eq]
      exact (layer_cake_Icc (f p.1) h_fp).symm
    rw [h_layer]; ring
  -- Each inner integral over p, when bounded, uses abs_weighted_integral_diff_indicator_general_le
  -- First, integrability of each F(s, ·)
  have hF_s_int : ∀ s, Integrable (F s) (μ.prod μ) := by
    intro s
    apply Integrable.bdd_mul hK_int
    · exact ((measurable_const.indicator (hS_meas s)).comp measurable_fst).mul
          (hg_meas.comp measurable_snd)
        |>.aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro p; rw [Real.norm_eq_abs, abs_mul]
      calc |({x | s ≤ f x}).indicator (fun _ => (1:ℝ)) p.1| * |g p.2|
          ≤ 1 * 1 := by
            gcongr
            · exact abs_ind_le_one _ _
            · rw [abs_of_nonneg (hg_bound p.2).1]; exact (hg_bound p.2).2
        _ = 1 := one_mul 1
  -- Convert inner integral over p from product to iterated form, then bound
  have h_bound_s : ∀ s, |∫ p, F s p ∂(μ.prod μ)| ≤ cutNormDiff U W := by
    intro s
    -- F(s, p) = 1_{s≤f}(p.1) * g(p.2) * K(p)
    -- ∫ p, F(s, p) d(μ²) = ∫ x, ∫ y, 1_{s≤f}(x) * g(y) * K(x,y) dμ dμ  (by Fubini)
    have h_fubini_s : ∫ p, F s p ∂(μ.prod μ) =
        ∫ x, ∫ y, ({x : α | s ≤ f x}).indicator (fun _ => (1:ℝ)) x * g y *
          (U.toAEEqFun (x, y) - W.toAEEqFun (x, y)) ∂μ ∂μ := by
      rw [integral_prod _ (hF_s_int s)]
    rw [h_fubini_s]
    exact abs_weighted_integral_diff_indicator_general_le U W _ (hS_meas s) g hg_meas hg_bound
  -- Main argument: rewrite LHS via Fubini, then bound
  have h_eq_layer : ∫ p, f p.1 * g p.2 * K p ∂(μ.prod μ) =
      ∫ s in Set.Ioc 0 1, (∫ p, F s p ∂(μ.prod μ)) := by
    have h1 : ∫ p, f p.1 * g p.2 * K p ∂(μ.prod μ) =
        ∫ p, (∫ s, F s p ∂(volume.restrict (Set.Ioc 0 1))) ∂(μ.prod μ) := by
      congr 1; ext p; exact (h_inner_s p).symm
    rw [h1, ← h_swap]
  change |∫ p, f p.1 * g p.2 * K p ∂(μ.prod μ)| ≤ _
  rw [h_eq_layer]
  -- Goal: |∫ s in Ioc 0 1, (∫ p, F s p ∂μ²)| ≤ cutNormDiff U W
  have h_vol_Ioc : (volume (Set.Ioc (0:ℝ) 1)).toReal = 1 := by
    rw [Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1)]
  have h_Ioc_finite : (volume (Set.Ioc (0:ℝ) 1)) < ⊤ := by
    rw [Real.volume_Ioc, sub_zero]; exact ENNReal.ofReal_lt_top
  calc |∫ s in Set.Ioc 0 1, ∫ p, F s p ∂(μ.prod μ)|
      = ‖∫ s in Set.Ioc 0 1, ∫ p, F s p ∂(μ.prod μ)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ cutNormDiff U W * (volume (Set.Ioc (0:ℝ) 1)).toReal :=
        norm_setIntegral_le_of_norm_le_const h_Ioc_finite
          (fun s _ => by rw [Real.norm_eq_abs]; exact h_bound_s s)
    _ = cutNormDiff U W * 1 := by rw [h_vol_Ioc]
    _ = cutNormDiff U W := mul_one _

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
@[blueprint "def:cutDistance"
  (title := /-- Cut distance -/)]
noncomputable def cutDistance (U W : Graphon α μ) : ℝ :=
  sInf {d : ℝ | ∃ (φ ψ : α → α) (hφ : MeasurePreserving φ μ μ) (hψ : MeasurePreserving ψ μ μ),
        d = cutNormDiff (pullback U φ hφ) (pullback W ψ hψ)}

/-- Cut distance is non-negative. -/
@[blueprint "thm:cutDistance-nonneg"
  (title := /-- Non-negativity of cut distance -/)]
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
@[blueprint "thm:cutDistance-self"
  (title := /-- Cut distance to self is zero -/)]
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

/-- Cut distance is bounded by cut norm difference (using identity maps). -/
theorem cutDistance_le_cutNormDiff (U W : Graphon α μ) :
    cutDistance U W ≤ cutNormDiff U W := by
  unfold cutDistance
  apply csInf_le
  · use 0
    intro d ⟨φ, ψ, hφ, hψ, hd⟩
    rw [hd]
    exact cutNormDiff_nonneg (pullback U φ hφ) (pullback W ψ hψ)
  · exact ⟨id, id, MeasurePreserving.id μ, MeasurePreserving.id μ, by rw [pullback_id, pullback_id]⟩

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

/-! ### Scoping: the former `exists_common_extension` monolith was unprovable as stated

See `docs/rokhlin-scoping.md`. The old monolithic Rokhlin stub bundled three conjuncts, **two
of which are false as written**; it has now been **deleted** and replaced by four corrected,
consumer-shaped cores (`exists_common_coupling_maps`, `cutNormDiff_pullback_le`,
`exists_controlled_cell_alignment` in this file; `exists_mpEquiv_cutNormDiff_lt_add` in
`Graphon/Overlay.lean`, whose overlay proof needs the downstream regularity lemma), each a
standard consequence of the atomless standard-Borel measure-isomorphism theorem. All four are
now **proved** (campaigns R2 + R3). The two lemmas below
certify the "measure-obvious" necessity facts that forced those corrections; the historical
counterexamples:

* **Map alignment via bijections is FALSE.** `(α, μ) = ([0,1], λ)`, `ψ₁ = id`, `φ₂ = ` the
  doubling map `x ↦ 2x mod 1`: the demanded a.e.-injective `χ₁` with `χ₁ =ᵐ φ₂ ∘ χ₂` cannot
  equal the essentially 2-to-1 `φ₂ ∘ χ₂`. The honest fact is a coupling with measure-preserving
  *maps* (`exists_common_coupling_maps`), used with the pullback contraction
  `cutNormDiff_pullback_le`.
* **Arbitrary-partition alignment is FALSE** unless the cell measures match — certified by
  `mp_align_forces_equal_measure`. The honest form is equal-measure cell alignment
  (`exists_controlled_cell_alignment`, `[NoAtoms μ]`).
* **Controlled cell alignment needs `[NoAtoms μ]`** (atom counterexample; one-sided necessity
  by `mp_maps_into_forces_measure_le`).

* **Conjunct 1 (map alignment via bijections) is FALSE.** Take `(α, μ) = ([0,1], λ)`,
  `ψ₁ = id`, `φ₂ = ` the doubling map `x ↦ 2x mod 1` (both measure-preserving). The
  conclusion demands a measurable-equiv (a.e.-injective) `χ₁` with `χ₁ =ᵐ φ₂ ∘ χ₂`, but
  `φ₂ ∘ χ₂` is essentially 2-to-1, so on the conull agreement set a positive-measure set of
  collision pairs contradicts injectivity. The classical fact is a *coupling* statement with
  measure-preserving maps (not automorphisms of `α`). The doubling counterexample is left as
  prose (formalizing the doubling map's 2-to-1-ness is not cheap and off the critical path).

* **Conjunct 2 (arbitrary-partition alignment) is FALSE** unless the cell measures match —
  certified by `mp_align_forces_equal_measure` below. Counterexample: `P = {A, Aᶜ}` with
  `μ A = 1/2` and `Q = trivialPartition` (whose only cell has measure `1`).

* **Conjunct 3 (controlled cell alignment) needs `[NoAtoms μ]`.** With atoms it fails even at
  equal measures: on `{a,b,c}` with `μ = (1/2, 1/4, 1/4)`, no measure-preserving bijection
  maps the two-atom cell `{b,c}` into the one-atom cell `{a}`. `mp_maps_into_forces_measure_le`
  certifies the one-sided measure necessity that underlies the cell-matching hypotheses. -/

/-- **Refutation support (conjunct 2).** A measure-preserving `e` that aligns `S` with `T`
symmetrically (`μ(S \ e⁻¹T) = 0` and `μ(e⁻¹T \ S) = 0`) forces `μ S = μ T`. Hence partition
alignment is impossible unless the two partitions have matching cell measures. -/
theorem mp_align_forces_equal_measure
    {e : α ≃ᵐ α} (he : MeasurePreserving e μ μ) {S T : Set α} (hT : MeasurableSet T)
    (h1 : μ (S \ e ⁻¹' T) = 0) (h2 : μ (e ⁻¹' T \ S) = 0) :
    μ S = μ T := by
  have hae : S =ᵐ[μ] e ⁻¹' T := by rw [ae_eq_set]; exact ⟨h1, h2⟩
  rw [measure_congr hae, he.measure_preimage hT.nullMeasurableSet]

/-- **Refutation support (conjunct 3).** If a measure-preserving `e` maps `S` a.e. into `T`,
then `μ S ≤ μ T`. For injective cell families whose measures sum to the whole space this forces
equality; with atoms present, equal measures are not enough to realize the map (see the scoping
note above), which is why the corrected cell-alignment lemma assumes `[NoAtoms μ]`. -/
theorem mp_maps_into_forces_measure_le
    {e : α ≃ᵐ α} (he : MeasurePreserving e μ μ) {S T : Set α} (hT : MeasurableSet T)
    (h : ∀ᵐ x ∂μ, x ∈ S → e x ∈ T) :
    μ S ≤ μ T := by
  have hsub : S ≤ᵐ[μ] e ⁻¹' T := h
  calc μ S ≤ μ (e ⁻¹' T) := measure_mono_ae hsub
    _ = μ T := he.measure_preimage hT.nullMeasurableSet

open ProbabilityTheory Graphon.MeasureIso in
/-- **Common coupling of two measure-preserving maps (corrected Rokhlin consequence 1).**
Given measure-preserving maps `ψ₁, φ₂ : α → α` on an *atomless* standard Borel probability
space, there are measure-preserving **maps** `χ₁, χ₂ : α → α` with `ψ₁ ∘ χ₁ =ᵐ φ₂ ∘ χ₂`.

This replaces the false `exists_common_extension_maps`: demanding `χ₁, χ₂` be **bijections**
is unprovable (take `ψ₁ = id`, `φ₂ = ` doubling — a bijection cannot equal an essentially
2-to-1 map a.e.; see the scoping note). The honest statement is a coupling: build the
relatively-independent joining of `ψ₁, φ₂` over their common factor on `α × α`, then re-type
it onto `α` via the measure-isomorphism theorem — which needs `[NoAtoms μ]`. Interface for
`cutDistance_triangle` (used together with the pullback contraction
`cutNormDiff_pullback_le`, since `χ₁, χ₂` are maps, not measure-preserving bijections). -/
@[blueprint "thm:coupling-maps"
  (title := /-- Common coupling by measure-preserving maps -/)]
theorem MeasurePreserving.exists_common_coupling_maps [StandardBorelSpace α] [NoAtoms μ]
    (ψ₁ : α → α) (hψ₁ : MeasurePreserving ψ₁ μ μ)
    (φ₂ : α → α) (hφ₂ : MeasurePreserving φ₂ μ μ) :
    ∃ (χ₁ χ₂ : α → α)
      (hχ₁ : MeasurePreserving χ₁ μ μ) (hχ₂ : MeasurePreserving χ₂ μ μ),
      ψ₁ ∘ χ₁ =ᵐ[μ] φ₂ ∘ χ₂ := by
  classical
  haveI : Nonempty α := by
    by_contra h
    simp only [not_nonempty_iff] at h
    exact zero_ne_one (by rw [← measure_univ (μ := μ), Set.univ_eq_empty_iff.mpr h, measure_empty])
  -- graph maps and graph measures
  set g₁ : α → α × α := fun x ↦ (ψ₁ x, x) with hg₁def
  set g₂ : α → α × α := fun x ↦ (φ₂ x, x) with hg₂def
  have hg₁ : Measurable g₁ := hψ₁.measurable.prodMk measurable_id
  have hg₂ : Measurable g₂ := hφ₂.measurable.prodMk measurable_id
  set G₁ : Measure (α × α) := μ.map g₁ with hG₁
  set G₂ : Measure (α × α) := μ.map g₂ with hG₂
  haveI : IsProbabilityMeasure G₁ := Measure.isProbabilityMeasure_map hg₁.aemeasurable
  haveI : IsProbabilityMeasure G₂ := Measure.isProbabilityMeasure_map hg₂.aemeasurable
  -- marginals of graph measures
  have hfst1 : G₁.fst = μ := by
    rw [hG₁, Measure.fst, Measure.map_map measurable_fst hg₁, hg₁def]; exact hψ₁.map_eq
  have hfst2 : G₂.fst = μ := by
    rw [hG₂, Measure.fst, Measure.map_map measurable_fst hg₂, hg₂def]; exact hφ₂.map_eq
  have hsnd1 : G₁.snd = μ := by
    rw [hG₁, Measure.snd, Measure.map_map measurable_snd hg₁, hg₁def]; exact Measure.map_id
  have hsnd2 : G₂.snd = μ := by
    rw [hG₂, Measure.snd, Measure.map_map measurable_snd hg₂, hg₂def]; exact Measure.map_id
  -- conditional kernels
  set κ₁ : Kernel α α := G₁.condKernel with hκ₁
  set κ₂ : Kernel α α := G₂.condKernel with hκ₂
  haveI : IsMarkovKernel κ₁ := by rw [hκ₁]; infer_instance
  haveI : IsMarkovKernel κ₂ := by rw [hκ₂]; infer_instance
  have hdis1 : μ ⊗ₘ κ₁ = G₁ := by rw [← hfst1]; exact Measure.disintegrate G₁ κ₁
  have hdis2 : μ ⊗ₘ κ₂ = G₂ := by rw [← hfst2]; exact Measure.disintegrate G₂ κ₂
  -- support facts
  have hmeasset1 : MeasurableSet {q : α × α | ψ₁ q.2 = q.1} :=
    measurableSet_eq_fun (hψ₁.measurable.comp measurable_snd) measurable_fst
  have hmeasset2 : MeasurableSet {q : α × α | φ₂ q.2 = q.1} :=
    measurableSet_eq_fun (hφ₂.measurable.comp measurable_snd) measurable_fst
  have hG1supp : ∀ᵐ q ∂G₁, ψ₁ q.2 = q.1 := by
    rw [hG₁, ae_map_iff hg₁.aemeasurable hmeasset1]
    exact ae_of_all _ fun x ↦ rfl
  have hG2supp : ∀ᵐ q ∂G₂, φ₂ q.2 = q.1 := by
    rw [hG₂, ae_map_iff hg₂.aemeasurable hmeasset2]
    exact ae_of_all _ fun x ↦ rfl
  have hκ1supp : ∀ᵐ v ∂μ, ∀ᵐ b ∂κ₁ v, ψ₁ b = v := by
    have h : ∀ᵐ q ∂(μ ⊗ₘ κ₁), ψ₁ q.2 = q.1 := by rw [hdis1]; exact hG1supp
    exact (Measure.ae_compProd_iff hmeasset1).mp h
  have hκ2supp : ∀ᵐ v ∂μ, ∀ᵐ b ∂κ₂ v, φ₂ b = v := by
    have h : ∀ᵐ q ∂(μ ⊗ₘ κ₂), φ₂ q.2 = q.1 := by rw [hdis2]; exact hG2supp
    exact (Measure.ae_compProd_iff hmeasset2).mp h
  -- fiber product
  set Ω : Measure (α × (α × α)) := μ ⊗ₘ (κ₁ ×ₖ κ₂) with hΩ
  haveI : IsProbabilityMeasure Ω := by rw [hΩ]; infer_instance
  set ρ : Measure (α × α) := Ω.snd with hρ
  haveI : IsProbabilityMeasure ρ := by rw [hρ]; infer_instance
  -- kernel marginal facts
  have hkfst : (κ₁ ×ₖ κ₂).map Prod.fst = κ₁ := by rw [← Kernel.fst_eq]; exact Kernel.fst_prod κ₁ κ₂
  have hksnd : (κ₁ ×ₖ κ₂).map Prod.snd = κ₂ := by rw [← Kernel.snd_eq]; exact Kernel.snd_prod κ₁ κ₂
  -- marginals of ρ
  have marg1 : Ω.map (fun q : α × (α × α) ↦ q.2.1) = μ := by
    have e1 : Ω.map (Prod.map id Prod.fst) = G₁ := by
      rw [hΩ, ← Measure.compProd_map measurable_fst, hkfst, hdis1]
    calc Ω.map (fun q : α × (α × α) ↦ q.2.1)
        = (Ω.map (Prod.map id Prod.fst)).map Prod.snd := by
          rw [Measure.map_map measurable_snd (measurable_id.prodMap measurable_fst)]; rfl
      _ = G₁.map Prod.snd := by rw [e1]
      _ = μ := hsnd1
  have marg2 : Ω.map (fun q : α × (α × α) ↦ q.2.2) = μ := by
    have e2 : Ω.map (Prod.map id Prod.snd) = G₂ := by
      rw [hΩ, ← Measure.compProd_map measurable_snd, hksnd, hdis2]
    calc Ω.map (fun q : α × (α × α) ↦ q.2.2)
        = (Ω.map (Prod.map id Prod.snd)).map Prod.snd := by
          rw [Measure.map_map measurable_snd (measurable_id.prodMap measurable_snd)]; rfl
      _ = G₂.map Prod.snd := by rw [e2]
      _ = μ := hsnd2
  have hρfst : ρ.fst = μ := by
    rw [hρ]
    show (Ω.map Prod.snd).map Prod.fst = μ
    rw [Measure.map_map measurable_fst measurable_snd]; exact marg1
  have hρsnd : ρ.snd = μ := by
    rw [hρ]
    show (Ω.map Prod.snd).map Prod.snd = μ
    rw [Measure.map_map measurable_snd measurable_snd]; exact marg2
  -- ρ is atomless
  haveI : NoAtoms ρ := by
    refine ⟨fun p ↦ ?_⟩
    have hle : ρ {p} ≤ ρ.fst {p.1} := by
      rw [Measure.fst_apply (measurableSet_singleton p.1)]
      exact measure_mono (by rintro q rfl; exact rfl)
    rw [hρfst] at hle
    exact le_antisymm (hle.trans (measure_singleton p.1).le) bot_le
  -- support of ρ
  have hmeassetρ : MeasurableSet {w : α × α | ψ₁ w.1 = φ₂ w.2} :=
    measurableSet_eq_fun (hψ₁.measurable.comp measurable_fst) (hφ₂.measurable.comp measurable_snd)
  have hΩsupp : ∀ᵐ q ∂Ω, ψ₁ q.2.1 = φ₂ q.2.2 := by
    have hmeassetΩ : MeasurableSet {q : α × (α × α) | ψ₁ q.2.1 = φ₂ q.2.2} :=
      measurableSet_eq_fun (hψ₁.measurable.comp (measurable_fst.comp measurable_snd))
        (hφ₂.measurable.comp (measurable_snd.comp measurable_snd))
    rw [hΩ, Measure.ae_compProd_iff hmeassetΩ]
    filter_upwards [hκ1supp, hκ2supp] with v hv1 hv2
    rw [Kernel.prod_apply]
    have ha1 : ∀ᵐ w ∂(κ₁ v).prod (κ₂ v), ψ₁ w.1 = v :=
      Measure.quasiMeasurePreserving_fst.ae hv1
    have ha2 : ∀ᵐ w ∂(κ₁ v).prod (κ₂ v), φ₂ w.2 = v :=
      Measure.quasiMeasurePreserving_snd.ae hv2
    filter_upwards [ha1, ha2] with w hw1 hw2
    rw [hw1, hw2]
  have hρsupp : ∀ᵐ w ∂ρ, ψ₁ w.1 = φ₂ w.2 := by
    rw [hρ, Measure.snd, ae_map_iff measurable_snd.aemeasurable hmeassetρ]
    exact hΩsupp
  -- transport to (α, μ) via the measure-isomorphism theorem
  obtain ⟨eα⟩ := atomless_standardBorel_mod0MeasureIso_unitInterval α μ
  obtain ⟨eρ⟩ := atomless_standardBorel_mod0MeasureIso_unitInterval (α × α) ρ
  let eρsymm : Mod0MeasureIso ℝ (α × α) (volume.restrict (Set.Icc 0 1)) ρ :=
    ⟨eρ.invFun, eρ.toFun, eρ.measurable_invFun, eρ.measurable_toFun,
      eρ.map_invFun, eρ.map_toFun, eρ.right_inv_ae, eρ.left_inv_ae⟩
  let tiso : Mod0MeasureIso α (α × α) μ ρ := eα.trans eρsymm
  set t : α → α × α := tiso.toFun with htdef
  have htmeas : Measurable t := tiso.measurable_toFun
  have htmap : Measure.map t μ = ρ := tiso.map_toFun
  refine ⟨fun x ↦ (t x).1, fun x ↦ (t x).2, ?_, ?_, ?_⟩
  · refine ⟨measurable_fst.comp htmeas, ?_⟩
    rw [show (fun x ↦ (t x).1) = Prod.fst ∘ t from rfl,
      ← Measure.map_map measurable_fst htmeas, htmap, ← Measure.fst, hρfst]
  · refine ⟨measurable_snd.comp htmeas, ?_⟩
    rw [show (fun x ↦ (t x).2) = Prod.snd ∘ t from rfl,
      ← Measure.map_map measurable_snd htmeas, htmap, ← Measure.snd, hρsnd]
  · have htqmp : Measure.QuasiMeasurePreserving t μ ρ := ⟨htmeas, by rw [htmap]⟩
    filter_upwards [htqmp.ae hρsupp] with x hx
    exact hx

section Mod0Alignment
open Graphon.MeasureIso

/-- **Step 1 for `exists_mod0_self_iso_aligning_cells`.** For measurable `A B` of equal measure,
the restricted measures `μ.restrict A` and `μ.restrict B` are isomorphic mod 0 by an ambient
self-map of `α`. If `μ A = 0` both restrictions vanish and the identity works; otherwise
normalize each to a probability measure (dividing by the common mass `μ A`) and transport through
`[0,1]` via `atomless_standardBorel_mod0MeasureIso_unitInterval`, then unnormalize — pushforwards
and a.e. relations are invariant under the common nonzero, finite scalar. -/
private lemma equalMeasure_restrict_mod0iso [StandardBorelSpace α] [NoAtoms μ]
    {A B : Set α} (hAB : μ A = μ B) :
    Nonempty (Mod0MeasureIso α α (μ.restrict A) (μ.restrict B)) := by
  rcases eq_or_ne (μ A) 0 with hA0 | hApos
  · have hB0 : μ B = 0 := hAB ▸ hA0
    have hrA : μ.restrict A = 0 := Measure.restrict_eq_zero.mpr hA0
    have hrB : μ.restrict B = 0 := Measure.restrict_eq_zero.mpr hB0
    refine ⟨⟨id, id, measurable_id, measurable_id, ?_, ?_,
      Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩⟩
    · rw [Measure.map_id, hrA, hrB]
    · rw [Measure.map_id, hrB, hrA]
  · have hmtop : μ A ≠ ∞ := measure_ne_top μ A
    set νA := (μ A)⁻¹ • μ.restrict A with hνAdef
    set νB := (μ A)⁻¹ • μ.restrict B with hνBdef
    haveI : IsProbabilityMeasure νA := by
      refine ⟨?_⟩
      rw [hνAdef, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
      exact ENNReal.inv_mul_cancel hApos hmtop
    haveI : IsProbabilityMeasure νB := by
      refine ⟨?_⟩
      rw [hνBdef, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, ← hAB]
      exact ENNReal.inv_mul_cancel hApos hmtop
    haveI : NoAtoms νA := by
      refine ⟨fun x => ?_⟩
      rw [hνAdef, Measure.smul_apply, Measure.restrict_apply (measurableSet_singleton x),
        smul_eq_mul, measure_mono_null Set.inter_subset_left (measure_singleton x), mul_zero]
    haveI : NoAtoms νB := by
      refine ⟨fun x => ?_⟩
      rw [hνBdef, Measure.smul_apply, Measure.restrict_apply (measurableSet_singleton x),
        smul_eq_mul, measure_mono_null Set.inter_subset_left (measure_singleton x), mul_zero]
    obtain ⟨eA⟩ := atomless_standardBorel_mod0MeasureIso_unitInterval α νA
    obtain ⟨eB⟩ := atomless_standardBorel_mod0MeasureIso_unitInterval α νB
    let eBsymm : Mod0MeasureIso ℝ α (volume.restrict (Set.Icc 0 1)) νB :=
      ⟨eB.invFun, eB.toFun, eB.measurable_invFun, eB.measurable_toFun,
        eB.map_invFun, eB.map_toFun, eB.right_inv_ae, eB.left_inv_ae⟩
    let σ0 : Mod0MeasureIso α α νA νB := eA.trans eBsymm
    have hinv0 : (μ A)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hmtop
    refine ⟨⟨σ0.toFun, σ0.invFun, σ0.measurable_toFun, σ0.measurable_invFun,
      ?_, ?_, ?_, ?_⟩⟩
    · have h : (μ A)⁻¹ • Measure.map σ0.toFun (μ.restrict A) = (μ A)⁻¹ • μ.restrict B := by
        rw [← Measure.map_smul]; exact σ0.map_toFun
      have h2 := congrArg (fun ν => (μ A) • ν) h
      simpa only [smul_smul, ENNReal.mul_inv_cancel hApos hmtop, one_smul] using h2
    · have h : (μ A)⁻¹ • Measure.map σ0.invFun (μ.restrict B) = (μ A)⁻¹ • μ.restrict A := by
        rw [← Measure.map_smul]; exact σ0.map_invFun
      have h2 := congrArg (fun ν => (μ A) • ν) h
      simpa only [smul_smul, ENNReal.mul_inv_cancel hApos hmtop, one_smul] using h2
    · have h := σ0.left_inv_ae
      rw [show (ae νA) = ae (μ.restrict A) from
        Measure.ae_ennreal_smul_measure_eq hinv0 (μ.restrict A)] at h
      exact h
    · have h := σ0.right_inv_ae
      rw [show (ae νB) = ae (μ.restrict B) from
        Measure.ae_ennreal_smul_measure_eq hinv0 (μ.restrict B)] at h
      exact h

/-- Helper for `exists_controlled_cell_alignment` (the one-mod-0-self-iso route). Given the
equal-measure matched cell families, a mod-0 self-isomorphism of `(α, μ)` whose forward map
sends each source cell **a.e. into** its target cell (a.e., not pointwise: a null source cell may
be matched to an empty target cell, so the pointwise form is false — and a.e. is all the main
theorem needs). Built from per-cell equal-measure mod-0 isos
(each pair `ι_S i, ι_T i` and the leftover `(⋃ ι_S)ᶜ ↔ (⋃ ι_T)ᶜ`, all equal measure) assembled
over the disjoint cells; the everywhere-bijection difficulty is then discharged once by
`Mod0MeasureIso.toMeasurableEquiv` in the main theorem. -/
private theorem exists_mod0_self_iso_aligning_cells [StandardBorelSpace α] [NoAtoms μ]
    (P Q : MeasurablePartition α μ) {k : ℕ} (ι_S ι_T : Fin k → Set α)
    (hS : ∀ i, ι_S i ∈ P.parts) (hT : ∀ i, ι_T i ∈ Q.parts)
    (hS_inj : Function.Injective ι_S) (hT_inj : Function.Injective ι_T)
    (h_meas : ∀ i, μ (ι_S i) = μ (ι_T i)) :
    ∃ f : Graphon.MeasureIso.Mod0MeasureIso α α μ μ,
      ∀ i, ∀ᵐ x ∂μ, x ∈ ι_S i → f.toFun x ∈ ι_T i := by
  classical
  have hmeasS : ∀ i, MeasurableSet (ι_S i) := fun i => P.measurable_parts _ (hS i)
  have hmeasT : ∀ i, MeasurableSet (ι_T i) := fun i => Q.measurable_parts _ (hT i)
  have hdisjS : Pairwise (Function.onFun Disjoint ι_S) := fun i j hij =>
    P.pairwiseDisjoint (Finset.mem_coe.mpr (hS i)) (Finset.mem_coe.mpr (hS j))
      (fun h => hij (hS_inj h))
  have hdisjT : Pairwise (Function.onFun Disjoint ι_T) := fun i j hij =>
    Q.pairwiseDisjoint (Finset.mem_coe.mpr (hT i)) (Finset.mem_coe.mpr (hT j))
      (fun h => hij (hT_inj h))
  set S : Option (Fin k) → Set α := fun o => o.elim ((⋃ i, ι_S i)ᶜ) ι_S with hSdef
  set T : Option (Fin k) → Set α := fun o => o.elim ((⋃ i, ι_T i)ᶜ) ι_T with hTdef
  have hSn : S none = (⋃ i, ι_S i)ᶜ := rfl
  have hSs : ∀ i, S (some i) = ι_S i := fun _ => rfl
  have hTn : T none = (⋃ i, ι_T i)ᶜ := rfl
  have hTs : ∀ i, T (some i) = ι_T i := fun _ => rfl
  have hSmeas : ∀ o, MeasurableSet (S o) := by
    rintro (_ | i)
    · rw [hSn]; exact (MeasurableSet.iUnion hmeasS).compl
    · rw [hSs]; exact hmeasS i
  have hTmeas : ∀ o, MeasurableSet (T o) := by
    rintro (_ | i)
    · rw [hTn]; exact (MeasurableSet.iUnion hmeasT).compl
    · rw [hTs]; exact hmeasT i
  have hReq : μ ((⋃ i, ι_S i)ᶜ) = μ ((⋃ i, ι_T i)ᶜ) := by
    rw [measure_compl (MeasurableSet.iUnion hmeasS) (measure_ne_top _ _),
      measure_compl (MeasurableSet.iUnion hmeasT) (measure_ne_top _ _),
      measure_iUnion hdisjS hmeasS, measure_iUnion hdisjT hmeasT, tsum_congr h_meas]
  have hmeasEq : ∀ o, μ (S o) = μ (T o) := by
    rintro (_ | i)
    · rw [hSn, hTn]; exact hReq
    · rw [hSs, hTs]; exact h_meas i
  let σ : ∀ o, Mod0MeasureIso α α (μ.restrict (S o)) (μ.restrict (T o)) :=
    fun o => (equalMeasure_restrict_mod0iso (hmeasEq o)).some
  let Gf : List (Fin k) → α → α := fun l =>
    List.foldr (fun i acc => (ι_S i).piecewise (σ (some i)).toFun acc) (σ none).toFun l
  let G : α → α := Gf (List.finRange k)
  let G'f : List (Fin k) → α → α := fun l =>
    List.foldr (fun i acc => (ι_T i).piecewise (σ (some i)).invFun acc) (σ none).invFun l
  let G' : α → α := G'f (List.finRange k)
  have hGfmeas : ∀ l, Measurable (Gf l) := by
    intro l; induction l with
    | nil => exact (σ none).measurable_toFun
    | cons i t ih => exact Measurable.piecewise (hmeasS i) (σ (some i)).measurable_toFun ih
  have hG'fmeas : ∀ l, Measurable (G'f l) := by
    intro l; induction l with
    | nil => exact (σ none).measurable_invFun
    | cons i t ih => exact Measurable.piecewise (hmeasT i) (σ (some i)).measurable_invFun ih
  have hGmeas : Measurable G := hGfmeas _
  have hG'meas : Measurable G' := hG'fmeas _
  have hGmem : ∀ (l : List (Fin k)) (x : α) (j : Fin k), j ∈ l → x ∈ ι_S j →
      Gf l x = (σ (some j)).toFun x := by
    intro l
    induction l with
    | nil => intro x j hj _; simp at hj
    | cons i t ih =>
      intro x j hj hxj
      show (ι_S i).piecewise (σ (some i)).toFun (Gf t) x = _
      by_cases hij : i = j
      · subst hij; exact Set.piecewise_eq_of_mem _ _ _ hxj
      · have hxi : x ∉ ι_S i := Set.disjoint_right.mp (hdisjS hij) hxj
        rw [Set.piecewise_eq_of_notMem _ _ _ hxi]
        exact ih x j ((List.mem_cons.mp hj).resolve_left (fun h => hij h.symm)) hxj
  have hGnot : ∀ (l : List (Fin k)) (x : α), (∀ j, x ∉ ι_S j) →
      Gf l x = (σ none).toFun x := by
    intro l x hx
    induction l with
    | nil => rfl
    | cons i t ih =>
      show (ι_S i).piecewise (σ (some i)).toFun (Gf t) x = _
      rw [Set.piecewise_eq_of_notMem _ _ _ (hx i)]; exact ih
  have hG'mem : ∀ (l : List (Fin k)) (y : α) (j : Fin k), j ∈ l → y ∈ ι_T j →
      G'f l y = (σ (some j)).invFun y := by
    intro l
    induction l with
    | nil => intro y j hj _; simp at hj
    | cons i t ih =>
      intro y j hj hyj
      show (ι_T i).piecewise (σ (some i)).invFun (G'f t) y = _
      by_cases hij : i = j
      · subst hij; exact Set.piecewise_eq_of_mem _ _ _ hyj
      · have hyi : y ∉ ι_T i := Set.disjoint_right.mp (hdisjT hij) hyj
        rw [Set.piecewise_eq_of_notMem _ _ _ hyi]
        exact ih y j ((List.mem_cons.mp hj).resolve_left (fun h => hij h.symm)) hyj
  have hG'not : ∀ (l : List (Fin k)) (y : α), (∀ j, y ∉ ι_T j) →
      G'f l y = (σ none).invFun y := by
    intro l y hy
    induction l with
    | nil => rfl
    | cons i t ih =>
      show (ι_T i).piecewise (σ (some i)).invFun (G'f t) y = _
      rw [Set.piecewise_eq_of_notMem _ _ _ (hy i)]; exact ih
  have hGeqS : ∀ o, ∀ x ∈ S o, G x = (σ o).toFun x := by
    rintro (_ | i) x hx
    · have hx' : ∀ j, x ∉ ι_S j := by
        intro j hj; rw [hSn] at hx; exact hx (Set.mem_iUnion.mpr ⟨j, hj⟩)
      exact hGnot _ x hx'
    · rw [hSs] at hx; exact hGmem _ x i (List.mem_finRange i) hx
  have hGeqT : ∀ o, ∀ y ∈ T o, G' y = (σ o).invFun y := by
    rintro (_ | i) y hy
    · have hy' : ∀ j, y ∉ ι_T j := by
        intro j hj; rw [hTn] at hy; exact hy (Set.mem_iUnion.mpr ⟨j, hj⟩)
      exact hG'not _ y hy'
    · rw [hTs] at hy; exact hG'mem _ y i (List.mem_finRange i) hy
  have hmapG : ∀ o, Measure.map G (μ.restrict (S o)) = μ.restrict (T o) := by
    intro o
    have hcongr : G =ᵐ[μ.restrict (S o)] (σ o).toFun :=
      (ae_restrict_iff' (hSmeas o)).mpr (Filter.Eventually.of_forall (hGeqS o))
    rw [Measure.map_congr hcongr, (σ o).map_toFun]
  have hmapG' : ∀ o, Measure.map G' (μ.restrict (T o)) = μ.restrict (S o) := by
    intro o
    have hcongr : G' =ᵐ[μ.restrict (T o)] (σ o).invFun :=
      (ae_restrict_iff' (hTmeas o)).mpr (Filter.Eventually.of_forall (hGeqT o))
    rw [Measure.map_congr hcongr, (σ o).map_invFun]
  have hmapCell : ∀ i, Measure.map G (μ.restrict (ι_S i)) = μ.restrict (ι_T i) := by
    intro i; have := hmapG (some i); rwa [hSs i, hTs i] at this
  have hSpwd : Pairwise (Function.onFun Disjoint S) := by
    rintro (_ | i) (_ | j) hne
    · exact absurd rfl hne
    · simp only [Function.onFun, hSn, hSs]
      exact (disjoint_compl_right_iff_subset.mpr (Set.subset_iUnion ι_S j)).symm
    · simp only [Function.onFun, hSn, hSs]
      exact disjoint_compl_right_iff_subset.mpr (Set.subset_iUnion ι_S i)
    · simp only [Function.onFun, hSs]
      exact hdisjS (fun h => hne (by rw [h]))
  have hTpwd : Pairwise (Function.onFun Disjoint T) := by
    rintro (_ | i) (_ | j) hne
    · exact absurd rfl hne
    · simp only [Function.onFun, hTn, hTs]
      exact (disjoint_compl_right_iff_subset.mpr (Set.subset_iUnion ι_T j)).symm
    · simp only [Function.onFun, hTn, hTs]
      exact disjoint_compl_right_iff_subset.mpr (Set.subset_iUnion ι_T i)
    · simp only [Function.onFun, hTs]
      exact hdisjT (fun h => hne (by rw [h]))
  have hμS : μ = Measure.sum (fun o => μ.restrict (S o)) := by
    have hcov : (⋃ o, S o) = Set.univ := by
      rw [Set.iUnion_option]
      show (⋃ i, ι_S i)ᶜ ∪ (⋃ i, ι_S i) = Set.univ
      exact compl_union_self _
    have h := Measure.restrict_iUnion (μ := μ) hSpwd hSmeas
    rw [hcov, Measure.restrict_univ] at h
    exact h
  have hμT : μ = Measure.sum (fun o => μ.restrict (T o)) := by
    have hcov : (⋃ o, T o) = Set.univ := by
      rw [Set.iUnion_option]
      show (⋃ i, ι_T i)ᶜ ∪ (⋃ i, ι_T i) = Set.univ
      exact compl_union_self _
    have h := Measure.restrict_iUnion (μ := μ) hTpwd hTmeas
    rw [hcov, Measure.restrict_univ] at h
    exact h
  have hmapGμ : Measure.map G μ = μ := by
    calc Measure.map G μ
        = Measure.map G (Measure.sum (fun o => μ.restrict (S o))) := by rw [← hμS]
      _ = Measure.sum (fun o => Measure.map G (μ.restrict (S o))) :=
          Measure.map_sum hGmeas.aemeasurable
      _ = Measure.sum (fun o => μ.restrict (T o)) := by rw [funext hmapG]
      _ = μ := hμT.symm
  have hmapG'μ : Measure.map G' μ = μ := by
    calc Measure.map G' μ
        = Measure.map G' (Measure.sum (fun o => μ.restrict (T o))) := by rw [← hμT]
      _ = Measure.sum (fun o => Measure.map G' (μ.restrict (T o))) :=
          Measure.map_sum hG'meas.aemeasurable
      _ = Measure.sum (fun o => μ.restrict (S o)) := by rw [funext hmapG']
      _ = μ := hμS.symm
  refine ⟨⟨G, G', hGmeas, hG'meas, hmapGμ, hmapG'μ, ?_, ?_⟩, ?_⟩
  · show (fun x => G' (G x)) =ᵐ[μ] id
    have key : ∀ o, ∀ᵐ x ∂(μ.restrict (S o)), G' (G x) = x := by
      intro o
      have h1 : ∀ᵐ x ∂(μ.restrict (S o)), G x = (σ o).toFun x :=
        (ae_restrict_iff' (hSmeas o)).mpr (Filter.Eventually.of_forall (hGeqS o))
      have h2 : ∀ᵐ x ∂(μ.restrict (S o)), (σ o).toFun x ∈ T o := by
        have hnull : (μ.restrict (S o)) {a | (σ o).toFun a ∉ T o} = 0 := by
          have hpre : {a | (σ o).toFun a ∉ T o} = (σ o).toFun ⁻¹' (T o)ᶜ := rfl
          rw [hpre, ← Measure.map_apply (σ o).measurable_toFun (hTmeas o).compl, (σ o).map_toFun,
            Measure.restrict_apply (hTmeas o).compl, Set.compl_inter_self, measure_empty]
        rw [ae_iff]; exact hnull
      have h3 : ∀ᵐ x ∂(μ.restrict (S o)), (σ o).invFun ((σ o).toFun x) = x := (σ o).left_inv_ae
      filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
      rw [hx1, hGeqT o _ hx2]; exact hx3
    have hfull : ∀ᵐ x ∂μ, G' (G x) = x := by
      rw [hμS, Measure.ae_sum_iff]; exact key
    exact hfull
  · show (fun y => G (G' y)) =ᵐ[μ] id
    have key : ∀ o, ∀ᵐ y ∂(μ.restrict (T o)), G (G' y) = y := by
      intro o
      have h1 : ∀ᵐ y ∂(μ.restrict (T o)), G' y = (σ o).invFun y :=
        (ae_restrict_iff' (hTmeas o)).mpr (Filter.Eventually.of_forall (hGeqT o))
      have h2 : ∀ᵐ y ∂(μ.restrict (T o)), (σ o).invFun y ∈ S o := by
        have hnull : (μ.restrict (T o)) {a | (σ o).invFun a ∉ S o} = 0 := by
          have hpre : {a | (σ o).invFun a ∉ S o} = (σ o).invFun ⁻¹' (S o)ᶜ := rfl
          rw [hpre, ← Measure.map_apply (σ o).measurable_invFun (hSmeas o).compl, (σ o).map_invFun,
            Measure.restrict_apply (hSmeas o).compl, Set.compl_inter_self, measure_empty]
        rw [ae_iff]; exact hnull
      have h3 : ∀ᵐ y ∂(μ.restrict (T o)), (σ o).toFun ((σ o).invFun y) = y := (σ o).right_inv_ae
      filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
      rw [hy1, hGeqS o _ hy2]; exact hy3
    have hfull : ∀ᵐ y ∂μ, G (G' y) = y := by
      rw [hμT, Measure.ae_sum_iff]; exact key
    exact hfull
  · intro i
    rw [ae_iff]
    have hset : {x | ¬ (x ∈ ι_S i → G x ∈ ι_T i)} = ι_S i ∩ G ⁻¹' (ι_T i)ᶜ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff]
      tauto
    rw [hset, Set.inter_comm, ← Measure.restrict_apply (hGmeas (hmeasT i).compl),
      ← Measure.map_apply hGmeas (hmeasT i).compl, hmapCell i,
      Measure.restrict_apply (hmeasT i).compl, Set.compl_inter_self, measure_empty]

end Mod0Alignment

/-- **Controlled cell alignment (corrected Rokhlin consequence 3).** Given injective indexed
families of cells from two partitions with *matching measures*, over an *atomless* standard
Borel probability space, there is a measure-preserving bijection mapping each cell `ι_S i`
a.e. into `ι_T i`.

This is the honest, true form of the third conjunct of the old `exists_common_extension`
stub: it adds `[NoAtoms μ]` (necessary — see the atom counterexample in the scoping note and
`mp_maps_into_forces_measure_le`) and is now a standalone obligation resting only on the
measure-isomorphism theorem (campaign phase R1), not on the unprovable monolithic stub. It is
the sole cell-matching interface used by the inverse-counting route. -/
@[blueprint "thm:cell-alignment"
  (title := /-- Controlled cell alignment (equal-measure cells) -/)]
theorem MeasurePreserving.exists_controlled_cell_alignment [StandardBorelSpace α] [NoAtoms μ]
    (P Q : MeasurablePartition α μ)
    {k : ℕ} (ι_S ι_T : Fin k → Set α)
    (hS : ∀ i, ι_S i ∈ P.parts) (hT : ∀ i, ι_T i ∈ Q.parts)
    (hS_inj : Function.Injective ι_S) (hT_inj : Function.Injective ι_T)
    (h_meas : ∀ i, μ (ι_S i) = μ (ι_T i)) :
    ∃ (e : α ≃ᵐ α) (he : MeasurePreserving e μ μ),
      ∀ i, ∀ᵐ x ∂μ, x ∈ ι_S i → e x ∈ ι_T i := by
  obtain ⟨f, hf⟩ :=
    exists_mod0_self_iso_aligning_cells P Q ι_S ι_T hS hT hS_inj hT_inj h_meas
  obtain ⟨e, he, hae, _⟩ := f.toMeasurableEquiv
  refine ⟨e, he, fun i => ?_⟩
  filter_upwards [hae, hf i] with x hx hbound hmem
  rw [hx]; exact hbound hmem

/-- Cut norm difference is invariant under applying the same MeasurableEquiv to both graphons.

If e : α ≃ᵐ α is measure-preserving, then
‖U^e − W^e‖_□ = ‖U − W‖_□

The key insight: applying bijectivity of e, the sup over measurable S, T
of |∫_{S×T} (U^e − W^e)| equals the sup over measurable S', T' (images under e)
of |∫_{S'×T'} (U − W)|, which ranges over all measurable sets. -/
theorem cutNormDiff_pullback_measurableEquiv (U W : Graphon α μ)
    (e : α ≃ᵐ α) (he : MeasurePreserving e μ μ) :
    cutNormDiff (pullback U e he) (pullback W e he) = cutNormDiff U W := by
  -- Key tools: product measure-preserving map and measurable embedding
  have hee : MeasurePreserving (Prod.map (⇑e) (⇑e)) (μ.prod μ) (μ.prod μ) := he.prod he
  have hemb : MeasurableEmbedding (Prod.map (⇑e) (⇑e)) :=
    e.measurableEmbedding.prodMap e.measurableEmbedding
  -- Key identity: for measurable S, T,
  -- rectIntegralDiff (pullback U) (pullback W) S T = rectIntegralDiff U W (e '' S) (e '' T)
  have rect_eq : ∀ {S T : Set α}, MeasurableSet S → MeasurableSet T →
      rectIntegralDiff (pullback U e he) (pullback W e he) S T =
      rectIntegralDiff U W (e '' S) (e '' T) := by
    intro S T hS hT
    unfold rectIntegralDiff
    -- Step 1: a.e. rewrite the integrand using pullback_ae
    have h_integrand_ae : ∀ᵐ p ∂(μ.prod μ), p ∈ S ×ˢ T →
        ((pullback U e he).toAEEqFun p - (pullback W e he).toAEEqFun p) =
        (U.toAEEqFun (Prod.map e e p) - W.toAEEqFun (Prod.map e e p)) := by
      filter_upwards [pullback_ae U (⇑e) he, pullback_ae W (⇑e) he] with p hpU hpW _
      simp only [Prod.map, hpU, hpW]
    rw [setIntegral_congr_ae (hS.prod hT) h_integrand_ae]
    -- Step 2: change of variables via setIntegral_image_emb
    rw [show (e '' S) ×ˢ (e '' T) = Prod.map (⇑e) (⇑e) '' (S ×ˢ T) from
        (Set.prodMap_image_prod (⇑e) (⇑e) S T).symm]
    exact (hee.setIntegral_image_emb hemb
      (fun p => U.toAEEqFun p - W.toAEEqFun p) (S ×ˢ T)).symm
  apply le_antisymm
  · -- ≤ direction: for each measurable S, T,
    -- |rect pullback S T| = |rect U W (e '' S) (e '' T)| ≤ cutNormDiff U W
    unfold cutNormDiff
    apply Real.iSup_le _ (cutNormDiff_nonneg U W)
    intro S; apply Real.iSup_le _ (cutNormDiff_nonneg U W)
    intro hS; apply Real.iSup_le _ (cutNormDiff_nonneg U W)
    intro T; apply Real.iSup_le _ (cutNormDiff_nonneg U W)
    intro hT
    rw [rect_eq hS hT]
    exact abs_rectIntegralDiff_le U W
      (e.measurableEmbedding.measurableSet_image.mpr hS)
      (e.measurableEmbedding.measurableSet_image.mpr hT)
  · -- ≥ direction: for each measurable S, T,
    -- set S₀ = e ⁻¹' S, T₀ = e ⁻¹' T (measurable)
    -- rect U W S T = rect pullback S₀ T₀ ≤ cutNormDiff pullback
    unfold cutNormDiff
    apply Real.iSup_le _ (cutNormDiff_nonneg (pullback U e he) (pullback W e he))
    intro S; apply Real.iSup_le _ (cutNormDiff_nonneg (pullback U e he) (pullback W e he))
    intro hS; apply Real.iSup_le _ (cutNormDiff_nonneg (pullback U e he) (pullback W e he))
    intro T; apply Real.iSup_le _ (cutNormDiff_nonneg (pullback U e he) (pullback W e he))
    intro hT
    -- Use preimages
    have hS₀ : MeasurableSet (e ⁻¹' S) := e.measurable hS
    have hT₀ : MeasurableSet (e ⁻¹' T) := e.measurable hT
    rw [show S = e '' (e ⁻¹' S) from (e.surjective.image_preimage S).symm,
        show T = e '' (e ⁻¹' T) from (e.surjective.image_preimage T).symm,
        ← rect_eq hS₀ hT₀]
    exact abs_rectIntegralDiff_le (pullback U e he) (pullback W e he) hS₀ hT₀

/-- **Pullback contracts the cut norm.** For a measure-preserving *map* `φ` (not necessarily a
bijection), `‖U^φ − W^φ‖_□ ≤ ‖U − W‖_□`.

Unlike `cutNormDiff_pullback_measurableEquiv` (equality, for bijections), this only requires
`φ` to be measure-preserving. Proof idea: writing the rectangle integrals of the pulled-back
kernels via the disintegration of `μ` along `φ`, each indicator `1_S` becomes the conditional
probability `E[1_S ∣ φ] ∈ [0,1]`, so the pulled-back cut norm is a *weighted* cut norm with
`[0,1]`-weights, which the cut norm dominates (`abs_weighted_integral_diff_le`). This is the
map-level companion the corrected coupling triangle needs; it rests on the standard-Borel
disintegration (campaign phase R1/R2). -/
@[blueprint "thm:pullback-contraction"
  (title := /-- Cut-norm contraction under measure-preserving pullback -/)]
theorem cutNormDiff_pullback_le [StandardBorelSpace α] (U W : Graphon α μ)
    (φ : α → α) (hφ : MeasurePreserving φ μ μ) :
    cutNormDiff (pullback U φ hφ) (pullback W φ hφ) ≤ cutNormDiff U W := by
  classical
  -- Reduce to a fixed rectangle S × T.
  unfold cutNormDiff
  apply Real.iSup_le _ (cutNormDiff_nonneg U W)
  intro S; apply Real.iSup_le _ (cutNormDiff_nonneg U W)
  intro hS; apply Real.iSup_le _ (cutNormDiff_nonneg U W)
  intro T; apply Real.iSup_le _ (cutNormDiff_nonneg U W)
  intro hT
  -- The graphon difference as a (strongly measurable, integrable) function.
  set D : α × α → ℝ := fun q ↦ U.toAEEqFun q - W.toAEEqFun q with hD
  have hD_sm : StronglyMeasurable D :=
    U.toAEEqFun.stronglyMeasurable.sub W.toAEEqFun.stronglyMeasurable
  have hD_int : Integrable D (μ.prod μ) :=
    (SymmKernel.graphon_integrable U).sub (SymmKernel.graphon_integrable W)
  -- Step 1: rewrite the pulled-back rectangle integral through `pullback_ae`.
  have hstep1 : rectIntegralDiff (pullback U φ hφ) (pullback W φ hφ) S T =
      ∫ p in S ×ˢ T, D (φ p.1, φ p.2) ∂(μ.prod μ) := by
    unfold rectIntegralDiff
    apply setIntegral_congr_ae (hS.prod hT)
    filter_upwards [pullback_ae U φ hφ, pullback_ae W φ hφ] with p hU hW _
    rw [hU, hW]
  -- The conditional-probability weight measures: pushforwards of the restricted measures.
  set νS : Measure α := Measure.map φ (μ.restrict S) with hνS
  set νT : Measure α := Measure.map φ (μ.restrict T) with hνT
  -- Each weight measure is dominated by μ.
  have hle : ∀ R : Set α, Measure.map φ (μ.restrict R) ≤ μ := by
    intro R
    refine Measure.le_iff.mpr fun E hE ↦ ?_
    rw [Measure.map_apply hφ.measurable hE, Measure.restrict_apply (hφ.measurable hE)]
    calc μ (φ ⁻¹' E ∩ R) ≤ μ (φ ⁻¹' E) := measure_mono Set.inter_subset_left
      _ = μ E := hφ.measure_preimage hE.nullMeasurableSet
  have hleS : νS ≤ μ := hνS ▸ hle S
  have hleT : νT ≤ μ := hνT ▸ hle T
  have hacS : νS ≪ μ := Measure.absolutelyContinuous_of_le hleS
  have hacT : νT ≪ μ := Measure.absolutelyContinuous_of_le hleT
  haveI : IsFiniteMeasure νS := ⟨lt_of_le_of_lt (hleS Set.univ) (measure_lt_top μ _)⟩
  haveI : IsFiniteMeasure νT := ⟨lt_of_le_of_lt (hleT Set.univ) (measure_lt_top μ _)⟩
  -- The [0,1]-valued Radon–Nikodym weights (= the conditional probabilities E[1_S ∣ φ]).
  set f0 : α → ℝ := fun a ↦ (νS.rnDeriv μ a).toReal with hf0
  set g0 : α → ℝ := fun b ↦ (νT.rnDeriv μ b).toReal with hg0
  have hf0_meas : Measurable f0 := (Measure.measurable_rnDeriv νS μ).ennreal_toReal
  have hg0_meas : Measurable g0 := (Measure.measurable_rnDeriv νT μ).ennreal_toReal
  have hf0_le : ∀ᵐ a ∂μ, f0 a ≤ 1 := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hleS] with a ha
    calc (νS.rnDeriv μ a).toReal ≤ (1 : ℝ≥0∞).toReal :=
          ENNReal.toReal_mono ENNReal.one_ne_top ha
      _ = 1 := ENNReal.toReal_one
  have hg0_le : ∀ᵐ b ∂μ, g0 b ≤ 1 := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hleT] with b hb
    calc (νT.rnDeriv μ b).toReal ≤ (1 : ℝ≥0∞).toReal :=
          ENNReal.toReal_mono ENNReal.one_ne_top hb
      _ = 1 := ENNReal.toReal_one
  -- Step 2: the change of variables, at the product level.
  have hkey : ∫ p in S ×ˢ T, D (φ p.1, φ p.2) ∂(μ.prod μ) =
      ∫ x, ∫ y, f0 x * g0 y * D (x, y) ∂μ ∂μ := by
    have hΦmeas : Measurable (Prod.map φ φ) := hφ.measurable.prodMap hφ.measurable
    -- pushforward of the restricted product measure = product of the weight measures
    have hmapΦ : Measure.map (Prod.map φ φ) ((μ.prod μ).restrict (S ×ˢ T)) = νS.prod νT := by
      rw [← Measure.prod_restrict, ← Measure.map_prod_map _ _ hφ.measurable hφ.measurable]
    -- integrability of the weighted integrand over μ.prod μ
    have hF_int : Integrable (fun q : α × α ↦ f0 q.1 * g0 q.2 * D q) (μ.prod μ) := by
      refine Integrable.mono' hD_int.abs
        ((((hf0_meas.comp measurable_fst).mul (hg0_meas.comp measurable_snd)).mul
          hD_sm.measurable).aestronglyMeasurable) ?_
      have h1 : ∀ᵐ q ∂(μ.prod μ), f0 q.1 ≤ 1 :=
        Measure.quasiMeasurePreserving_fst.ae hf0_le
      have h2 : ∀ᵐ q ∂(μ.prod μ), g0 q.2 ≤ 1 :=
        Measure.quasiMeasurePreserving_snd.ae hg0_le
      filter_upwards [h1, h2] with q hq1 hq2
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |f0 q.1| * |g0 q.2| * |D q| ≤ 1 * 1 * |D q| := by
            gcongr
            · exact ((abs_of_nonneg ENNReal.toReal_nonneg).le.trans hq1)
            · exact ((abs_of_nonneg ENNReal.toReal_nonneg).le.trans hq2)
        _ = |D q| := by ring
    calc ∫ p in S ×ˢ T, D (φ p.1, φ p.2) ∂(μ.prod μ)
        = ∫ p, D (Prod.map φ φ p) ∂((μ.prod μ).restrict (S ×ˢ T)) := rfl
      _ = ∫ q, D q ∂(Measure.map (Prod.map φ φ) ((μ.prod μ).restrict (S ×ˢ T))) :=
          (integral_map hΦmeas.aemeasurable hD_sm.aestronglyMeasurable).symm
      _ = ∫ q, D q ∂(νS.prod νT) := by rw [hmapΦ]
      _ = ∫ q, D q
            ∂((μ.prod μ).withDensity fun q ↦ νS.rnDeriv μ q.1 * νT.rnDeriv μ q.2) := by
          rw [← MeasureTheory.prod_withDensity (Measure.measurable_rnDeriv νS μ)
              (Measure.measurable_rnDeriv νT μ),
            Measure.withDensity_rnDeriv_eq νS μ hacS, Measure.withDensity_rnDeriv_eq νT μ hacT]
      _ = ∫ q, (νS.rnDeriv μ q.1 * νT.rnDeriv μ q.2).toReal • D q ∂(μ.prod μ) := by
          refine integral_withDensity_eq_integral_toReal_smul
            (((Measure.measurable_rnDeriv νS μ).comp measurable_fst).mul
              ((Measure.measurable_rnDeriv νT μ).comp measurable_snd)) ?_ D
          have h1 : ∀ᵐ q ∂(μ.prod μ), νS.rnDeriv μ q.1 < ∞ :=
            Measure.quasiMeasurePreserving_fst.ae (Measure.rnDeriv_lt_top νS μ)
          have h2 : ∀ᵐ q ∂(μ.prod μ), νT.rnDeriv μ q.2 < ∞ :=
            Measure.quasiMeasurePreserving_snd.ae (Measure.rnDeriv_lt_top νT μ)
          filter_upwards [h1, h2] with q hq1 hq2
          exact ENNReal.mul_lt_top hq1 hq2
      _ = ∫ q : α × α, f0 q.1 * g0 q.2 * D q ∂(μ.prod μ) := by
          congr 1; funext q
          rw [smul_eq_mul, ENNReal.toReal_mul]
      _ = ∫ x, ∫ y, f0 x * g0 y * D (x, y) ∂μ ∂μ := integral_prod _ hF_int
  -- Step 3: truncate the weights to land pointwise in [0,1].
  set f : α → ℝ := fun a ↦ min (f0 a) 1 with hf
  set g : α → ℝ := fun b ↦ min (g0 b) 1 with hg
  have hf_meas : Measurable f := hf0_meas.min measurable_const
  have hg_meas : Measurable g := hg0_meas.min measurable_const
  have hf_bound : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := fun x ↦
    ⟨le_min ENNReal.toReal_nonneg zero_le_one, min_le_right _ _⟩
  have hg_bound : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1 := fun x ↦
    ⟨le_min ENNReal.toReal_nonneg zero_le_one, min_le_right _ _⟩
  have hf_ae : (f : α → ℝ) =ᵐ[μ] f0 := by
    filter_upwards [hf0_le] with a ha using min_eq_left ha
  have hg_ae : (g : α → ℝ) =ᵐ[μ] g0 := by
    filter_upwards [hg0_le] with b hb using min_eq_left hb
  have hcongr : ∫ x, ∫ y, f0 x * g0 y * D (x, y) ∂μ ∂μ =
      ∫ x, ∫ y, f x * g y * D (x, y) ∂μ ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf_ae] with x hx
    apply integral_congr_ae
    filter_upwards [hg_ae] with y hy
    rw [hx, hy]
  -- Conclude via the weighted cut-norm bound.
  calc |rectIntegralDiff (pullback U φ hφ) (pullback W φ hφ) S T|
      = |∫ x, ∫ y, f x * g y * (U.toAEEqFun (x, y) - W.toAEEqFun (x, y)) ∂μ ∂μ| := by
        rw [hstep1, hkey, hcongr]
    _ ≤ cutNormDiff U W :=
        abs_weighted_integral_diff_le U W f g hf_meas hg_meas hf_bound hg_bound

/- NOTE (R3): the fourth corrected Rokhlin core, `exists_mpEquiv_cutNormDiff_lt_add`
("an MP bijection nearly achieves the cut distance"), lives in `Graphon/Overlay.lean` —
its proof (the overlay argument) needs the Frieze–Kannan regularity lemma and the atomless
carving primitives of `Graphon/Regularity.lean`, which sit downstream of this file. -/

/-- Cut distance from a graphon to its pullback by a MP bijection is zero.

For any graphon V and measure-preserving bijection e, `δ□(V, V^e) = 0`.

**Proof**: Use φ = id and ψ = e⁻¹ as witnesses in the cutDistance infimum.
Then `V^id = V` and `(V^e)^{e⁻¹} = V^{e ∘ e⁻¹} = V^id = V`,
so `‖V − V‖_□ = 0`. -/
@[blueprint "thm:cutDistance-pullback-eq-zero"
  (title := /-- Pullback invariance of cut distance -/)]
theorem cutDistance_pullback_eq_zero (V : Graphon α μ) (e : α ≃ᵐ α)
    (he : MeasurePreserving e μ μ) :
    cutDistance V (pullback V e he) = 0 := by
  have he_symm : MeasurePreserving e.symm μ μ := he.symm e
  apply le_antisymm
  · have h_comp_eq : pullback V (↑e ∘ ↑e.symm) (he.comp he_symm) = V := by
      apply Graphon.ext; apply SymmKernel.ext; apply AEEqFun.ext
      filter_upwards [pullback_ae V (↑e ∘ ↑e.symm) (he.comp he_symm)] with p hp
      rw [hp]; simp
    unfold cutDistance
    apply csInf_le
    · use 0; intro d ⟨φ, ψ, hφ, hψ, hd⟩; rw [hd]; exact cutNormDiff_nonneg _ _
    · refine ⟨id, ↑e.symm, MeasurePreserving.id μ, he_symm, ?_⟩
      rw [pullback_id, pullback_pullback V (↑e) he (↑e.symm) he_symm, h_comp_eq,
          cutNormDiff_self]
  · exact cutDistance_nonneg _ _

/-- For any ε > 0, there exist measure-preserving maps achieving cutDistance + ε. -/
theorem cutDistance_lt_add_of_pos (U W : Graphon α μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (φ ψ : α → α) (hφ : MeasurePreserving φ μ μ) (hψ : MeasurePreserving ψ μ μ),
      cutNormDiff (pullback U φ hφ) (pullback W ψ hψ) < cutDistance U W + ε := by
  unfold cutDistance
  have h_ne := cutDistance_set_nonempty U W
  have h_bdd : BddBelow {d : ℝ | ∃ (φ ψ : α → α) (hφ : MeasurePreserving φ μ μ)
      (hψ : MeasurePreserving ψ μ μ), d = cutNormDiff (pullback U φ hφ) (pullback W ψ hψ)} := by
    use 0; intro d ⟨φ, ψ, hφ, hψ, hd⟩; rw [hd]; exact cutNormDiff_nonneg _ _
  obtain ⟨d, hd_mem, hd_lt⟩ := exists_lt_of_csInf_lt h_ne (by linarith : sInf _ < sInf _ + ε)
  obtain ⟨φ, ψ, hφ, hψ, rfl⟩ := hd_mem
  exact ⟨φ, ψ, hφ, hψ, hd_lt⟩

/-- Triangle inequality for cut distance on standard Borel spaces.

δ□(U, W) ≤ δ□(U, V) + δ□(V, W)

This is the key property making cut distance a pseudometric.

**Proof**: For any ε > 0:
1. Choose (φ₁, ψ₁) with ‖U^φ₁ − V^ψ₁‖_□ < d(U,V) + ε
2. Choose (φ₂, ψ₂) with ‖V^φ₂ − W^ψ₂‖_□ < d(V,W) + ε
3. By Rokhlin's theorem, align ψ₁ and φ₂ via bijections χ₁, χ₂
4. Compose maps and use cutNormDiff_triangle to get
   d(U,W) ≤ d(U,V) + d(V,W) + 2ε
5. Take ε → 0.

**Depends on**: `MeasurePreserving.exists_common_coupling_maps` (corrected coupling, needs
`[NoAtoms μ]`) and `cutNormDiff_pullback_le` (pullback contraction). -/
@[blueprint "thm:cutDistance-triangle"
  (title := /-- Triangle inequality for cut distance -/)]
theorem cutDistance_triangle [StandardBorelSpace α] [NoAtoms μ] (U V W : Graphon α μ) :
    cutDistance U W ≤ cutDistance U V + cutDistance V W := by
  -- Suffices to show: for all ε > 0, d(U,W) ≤ d(U,V) + d(V,W) + ε
  rw [← sub_nonneg]
  by_contra h_neg
  push Not at h_neg
  -- h_neg : cutDistance U V + cutDistance V W - cutDistance U W < 0
  set δ := cutDistance U W - cutDistance U V - cutDistance V W with hδ_def
  have hδ_pos : δ > 0 := by linarith
  -- Choose near-optimal maps for d(U,V) and d(V,W) with error δ/2
  obtain ⟨φ₁, ψ₁, hφ₁, hψ₁, h_UV⟩ := cutDistance_lt_add_of_pos U V (half_pos hδ_pos)
  obtain ⟨φ₂, ψ₂, hφ₂, hψ₂, h_VW⟩ := cutDistance_lt_add_of_pos V W (half_pos hδ_pos)
  -- Coupling alignment — find MP maps χ₁, χ₂ with ψ₁ ∘ χ₁ =ᵐ φ₂ ∘ χ₂
  obtain ⟨χ₁, χ₂, hχ₁, hχ₂, h_align⟩ :=
    MeasurePreserving.exists_common_coupling_maps ψ₁ hψ₁ φ₂ hφ₂
  -- Compose maps: (φ₁ ∘ χ₁, ψ₂ ∘ χ₂) are measure-preserving
  have hφ₁χ₁ : MeasurePreserving (φ₁ ∘ χ₁) μ μ := hφ₁.comp hχ₁
  have hψ₂χ₂ : MeasurePreserving (ψ₂ ∘ χ₂) μ μ := hψ₂.comp hχ₂
  -- d(U,W) ≤ ‖U^(φ₁∘χ₁) − W^(ψ₂∘χ₂)‖_□ (definition of inf)
  have h_inf_le : cutDistance U W ≤
      cutNormDiff (pullback U (φ₁ ∘ χ₁) hφ₁χ₁) (pullback W (ψ₂ ∘ χ₂) hψ₂χ₂) := by
    unfold cutDistance
    apply csInf_le
    · use 0; intro d ⟨φ, ψ, hφ, hψ, hd⟩; rw [hd]; exact cutNormDiff_nonneg _ _
    · exact ⟨φ₁ ∘ χ₁, ψ₂ ∘ χ₂, hφ₁χ₁, hψ₂χ₂, rfl⟩
  -- Triangle inequality for cutNormDiff
  have hψ₁χ₁ : MeasurePreserving (ψ₁ ∘ χ₁) μ μ := hψ₁.comp hχ₁
  have hφ₂χ₂ : MeasurePreserving (φ₂ ∘ χ₂) μ μ := hφ₂.comp hχ₂
  -- V^(ψ₁∘χ₁) = V^(φ₂∘χ₂) by alignment
  have h_V_ae : pullback V (ψ₁ ∘ χ₁) hψ₁χ₁ = pullback V (φ₂ ∘ χ₂) hφ₂χ₂ := by
    apply Graphon.ext; apply SymmKernel.ext; apply AEEqFun.ext
    have h1 := pullback_ae V (ψ₁ ∘ χ₁) hψ₁χ₁
    have h2 := pullback_ae V (φ₂ ∘ χ₂) hφ₂χ₂
    have h_prod_ae : ∀ᵐ p ∂(μ.prod μ),
        (ψ₁ (χ₁ p.1), ψ₁ (χ₁ p.2)) = (φ₂ (χ₂ p.1), φ₂ (χ₂ p.2)) := by
      have h_fst : ∀ᵐ p ∂(μ.prod μ), ψ₁ (χ₁ p.1) = φ₂ (χ₂ p.1) :=
        Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst h_align
      have h_snd : ∀ᵐ p ∂(μ.prod μ), ψ₁ (χ₁ p.2) = φ₂ (χ₂ p.2) :=
        Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd h_align
      filter_upwards [h_fst, h_snd] with p hp1 hp2
      exact Prod.ext hp1 hp2
    filter_upwards [h1, h2, h_prod_ae] with p hp1 hp2 hp_eq
    rw [hp1, hp2]; simp only [Function.comp_apply] at hp_eq ⊢; rw [hp_eq]
  -- Key bounds using pullback_pullback and the pullback CONTRACTION (χ₁, χ₂ are maps)
  -- Term 1: ‖U^(φ₁∘χ₁) − V^(ψ₁∘χ₁)‖ = ‖(U^φ₁)^χ₁ − (V^ψ₁)^χ₁‖ ≤ ‖U^φ₁ − V^ψ₁‖
  have h1 : cutNormDiff (pullback U (φ₁ ∘ χ₁) hφ₁χ₁) (pullback V (ψ₁ ∘ χ₁) hψ₁χ₁) ≤
      cutNormDiff (pullback U φ₁ hφ₁) (pullback V ψ₁ hψ₁) := by
    rw [show pullback U (φ₁ ∘ χ₁) hφ₁χ₁ = pullback (pullback U φ₁ hφ₁) χ₁ hχ₁ from
        (pullback_pullback U φ₁ hφ₁ χ₁ hχ₁).symm,
      show pullback V (ψ₁ ∘ χ₁) hψ₁χ₁ = pullback (pullback V ψ₁ hψ₁) χ₁ hχ₁ from
        (pullback_pullback V ψ₁ hψ₁ χ₁ hχ₁).symm]
    exact cutNormDiff_pullback_le _ _ χ₁ hχ₁
  -- Term 2: ‖V^(ψ₁∘χ₁) − W^(ψ₂∘χ₂)‖ = ‖V^(φ₂∘χ₂) − W^(ψ₂∘χ₂)‖
  --       = ‖(V^φ₂)^χ₂ − (W^ψ₂)^χ₂‖ ≤ ‖V^φ₂ − W^ψ₂‖
  have h2 : cutNormDiff (pullback V (ψ₁ ∘ χ₁) hψ₁χ₁) (pullback W (ψ₂ ∘ χ₂) hψ₂χ₂) ≤
      cutNormDiff (pullback V φ₂ hφ₂) (pullback W ψ₂ hψ₂) := by
    rw [h_V_ae,
      show pullback V (φ₂ ∘ χ₂) hφ₂χ₂ = pullback (pullback V φ₂ hφ₂) χ₂ hχ₂ from
        (pullback_pullback V φ₂ hφ₂ χ₂ hχ₂).symm,
      show pullback W (ψ₂ ∘ χ₂) hψ₂χ₂ = pullback (pullback W ψ₂ hψ₂) χ₂ hχ₂ from
        (pullback_pullback W ψ₂ hψ₂ χ₂ hχ₂).symm]
    exact cutNormDiff_pullback_le _ _ χ₂ hχ₂
  -- Combine via cutNormDiff triangle and the inf bound
  have h_tri := cutNormDiff_triangle
    (pullback U (φ₁ ∘ χ₁) hφ₁χ₁) (pullback V (ψ₁ ∘ χ₁) hψ₁χ₁) (pullback W (ψ₂ ∘ χ₂) hψ₂χ₂)
  -- Now: d(U,W) ≤ ‖...‖ ≤ ‖U^(φ₁χ₁) − V^(ψ₁χ₁)‖ + ‖V^(ψ₁χ₁) − W^(ψ₂χ₂)‖
  --            ≤ ‖U^φ₁ − V^ψ₁‖ + ‖V^φ₂ − W^ψ₂‖ < (d(U,V) + δ/2) + (d(V,W) + δ/2)
  -- But δ = d(U,W) − d(U,V) − d(V,W), so d(U,W) < d(U,W), contradiction.
  linarith

/-- Cut distance is symmetric.

δ□(U, W) = δ□(W, U)

With the two-sided definition, this is immediate by swapping φ and ψ
and using the symmetry of cutNormDiff. No StandardBorelSpace needed! -/
@[blueprint "thm:cutDistance-symm"
  (title := /-- Symmetry of cut distance -/)]
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
