/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.CutNorm
import Graphon.Pullback
import Mathlib.MeasureTheory.Constructions.Polish.Basic

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

/-- General weighted integral of graphon difference bounded by cut norm difference.

For f, g : α → [0, 1] measurable and graphons U, W:
|∫∫ f(x) g(y) (U(x,y) - W(x,y)) dμ(x) dμ(y)| ≤ ‖U - W‖_□

**Proof strategy**: Same layer cake approach as `abs_weighted_integral_le_cutNorm`:
- f(x) = ∫₀¹ 1{f(x) ≥ s} ds
- g(y) = ∫₀¹ 1{g(y) ≥ t} dt
- The product integral becomes ∫₀¹ ∫₀¹ rectIntegralDiff U W {f≥s} {g≥t} ds dt
- Each rectIntegralDiff is bounded by cutNormDiff U W
- Integrating over [0,1]² gives the bound -/
theorem abs_weighted_integral_diff_le (U W : Graphon α μ) (f g : α → ℝ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_bound : ∀ x, f x ∈ Set.Icc 0 1) (hg_bound : ∀ x, g x ∈ Set.Icc 0 1) :
    |∫ x, ∫ y, f x * g y * (U.toAEEqFun (x, y) - W.toAEEqFun (x, y)) ∂μ ∂μ| ≤
      cutNormDiff U W := by
  -- **Proof via layer cake representation** (Lovász, Lemma 10.21):
  --
  -- For f, g ∈ [0,1], the layer cake identity gives:
  --   f(x) = ∫₀¹ 1{f(x) ≥ s} ds  and  g(y) = ∫₀¹ 1{g(y) ≥ t} dt
  --
  -- The key calculation (via Fubini 4-fold interchange):
  --   ∫∫ f(x) g(y) (U-W)(x,y) dμ² = ∫₀¹ ∫₀¹ rectIntegralDiff U W {f≥s} {g≥t} ds dt
  --
  -- Taking absolute value:
  --   |...| ≤ ∫₀¹ ∫₀¹ |rectIntegralDiff| ds dt ≤ ∫₀¹ ∫₀¹ cutNormDiff ds dt = cutNormDiff
  --
  -- Step 1: Set up integrability
  have h_diff_int : Integrable (fun p => U.toAEEqFun p - W.toAEEqFun p) (μ.prod μ) :=
    (SymmKernel.graphon_integrable U).sub (SymmKernel.graphon_integrable W)
  have h_fg_bound : ∀ p : α × α, ‖f p.1 * g p.2‖ ≤ 1 := fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf_bound p.1).1 (hg_bound p.2).1)]
    exact mul_le_one₀ (hf_bound p.1).2 (hg_bound p.2).1 (hg_bound p.2).2
  have h_fgD_int : Integrable (fun p => f p.1 * g p.2 * (U.toAEEqFun p - W.toAEEqFun p)) (μ.prod μ) :=
    h_diff_int.bdd_mul ((hf_meas.comp measurable_fst).mul (hg_meas.comp measurable_snd)).aestronglyMeasurable
      (Filter.Eventually.of_forall h_fg_bound)
  -- Step 2: Convert iterated integral to product integral
  have h_fubini : ∫ x, ∫ y, f x * g y * (U.toAEEqFun (x, y) - W.toAEEqFun (x, y)) ∂μ ∂μ =
      ∫ p, f p.1 * g p.2 * (U.toAEEqFun p - W.toAEEqFun p) ∂(μ.prod μ) :=
    (integral_prod _ h_fgD_int).symm
  rw [h_fubini]
  -- Step 3: Apply absolute value bound
  calc |∫ p, f p.1 * g p.2 * (U.toAEEqFun p - W.toAEEqFun p) ∂(μ.prod μ)|
      ≤ ∫ p, |f p.1 * g p.2 * (U.toAEEqFun p - W.toAEEqFun p)| ∂(μ.prod μ) :=
        abs_integral_le_integral_abs
    _ = ∫ p, f p.1 * g p.2 * |U.toAEEqFun p - W.toAEEqFun p| ∂(μ.prod μ) := by
        congr 1; ext p
        rw [abs_mul, abs_of_nonneg (mul_nonneg (hf_bound p.1).1 (hg_bound p.2).1)]
    _ ≤ cutNormDiff U W := by
        -- This is where the layer cake representation is used
        -- The full proof requires expressing:
        --   f(x) g(y) = ∫_{(0,1]²} 1_{f≥s}(x) 1_{g≥t}(y) ds dt
        -- and then using Fubini to interchange with the (U-W) integral.
        --
        -- For now, we use the weaker bound that ∫|U-W| ≤ 1 and cutNormDiff ≤ 1:
        -- ∫ f g |U-W| ≤ ∫ |U-W| ≤ ... (but this doesn't give cutNormDiff directly)
        --
        -- The correct layer cake proof:
        -- ∫ f g |U-W| ≤ ∫∫_{(0,1]²} 1_{f≥s} 1_{g≥t} |U-W| ds dt (by Fubini)
        --            ≤ ∫∫_{(0,1]²} |rectIntegralDiff U W {f≥s} {g≥t}| ds dt (by Fubini again)
        --            ≤ ∫∫_{(0,1]²} cutNormDiff U W ds dt = cutNormDiff U W
        --
        -- TODO: Formalize the layer cake + Fubini interchange
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
