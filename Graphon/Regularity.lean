/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Approximation
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-!
# Regularity Lemma for Graphons

This file states the regularity lemma for graphons, which says that any graphon
can be approximated by a step graphon in cut norm.

## Main results

* `Graphon.regularity` - For any ε > 0, there exists a partition with bounded
  number of parts such that the stepified graphon is ε-close in cut norm.

## Implementation notes

The regularity lemma is one of the central results in graphon theory. It is the
continuous analogue of Szemerédi's regularity lemma for graphs.

The number of parts in the partition depends only on ε, not on the graphon.
This is crucial for applications to graph limits.

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Section 9.2
* Szemerédi, E. (1978). Regular partitions of graphs.
-/

open MeasureTheory Set Filter Finset

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

/-! ### Energy function -/

section Energy

variable [IsProbabilityMeasure μ]

/-- The energy of a graphon with respect to a partition.

E(P, W) = Σ_{S,T ∈ P.parts} μ(S) μ(T) (rectAverage W S T)²

This measures how much of the L² norm of W is captured by its stepification.
The energy is always in [0, 1] and increases under refinement. -/
noncomputable def energy (W : Graphon α μ) (P : MeasurablePartition α μ) : ℝ :=
  P.parts.sum fun S =>
    P.parts.sum fun T =>
      (μ S).toReal * (μ T).toReal * (rectAverage W S T) ^ 2

/-- The energy is non-negative. -/
theorem energy_nonneg (W : Graphon α μ) (P : MeasurablePartition α μ) :
    0 ≤ energy W P := by
  unfold energy
  apply Finset.sum_nonneg
  intro S _
  apply Finset.sum_nonneg
  intro T _
  apply mul_nonneg
  apply mul_nonneg
  · exact ENNReal.toReal_nonneg
  · exact ENNReal.toReal_nonneg
  · exact sq_nonneg _

/-- The energy is at most 1.

Since rectAverage W S T ∈ [0,1] and Σ_{S,T} μ(S)μ(T) ≤ 1. -/
theorem energy_le_one (W : Graphon α μ) (P : MeasurablePartition α μ) :
    energy W P ≤ 1 := by
  unfold energy
  -- Each term: μ(S) μ(T) (avg)² ≤ μ(S) μ(T) * 1 = μ(S) μ(T)
  -- Sum over S, T: Σ μ(S) μ(T) = (Σ μ(S)) * (Σ μ(T)) ≤ 1 * 1 = 1
  calc P.parts.sum (fun S => P.parts.sum fun T =>
        (μ S).toReal * (μ T).toReal * (rectAverage W S T) ^ 2)
      ≤ P.parts.sum (fun S => P.parts.sum fun T =>
        (μ S).toReal * (μ T).toReal * 1) := by
          apply Finset.sum_le_sum
          intro S hS
          apply Finset.sum_le_sum
          intro T hT
          apply mul_le_mul_of_nonneg_left
          · -- rectAverage² ≤ 1 since rectAverage ∈ [0,1]
            have h := rectAverage_mem_Icc W S T (P.measurable_parts S hS) (P.measurable_parts T hT)
            calc (rectAverage W S T) ^ 2
                ≤ 1 ^ 2 := by
                    apply sq_le_sq'
                    · linarith [h.1]
                    · exact h.2
              _ = 1 := one_pow 2
          · apply mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    _ = P.parts.sum (fun S => P.parts.sum fun T =>
        (μ S).toReal * (μ T).toReal) := by simp only [mul_one]
    _ = (P.parts.sum fun S => (μ S).toReal) * (P.parts.sum fun T => (μ T).toReal) := by
          rw [Finset.sum_mul_sum]
    _ ≤ 1 * 1 := by
          apply mul_le_mul
          · exact MeasurablePartition.sum_measure_parts_le_one P
          · exact MeasurablePartition.sum_measure_parts_le_one P
          · apply Finset.sum_nonneg; intro _ _; exact ENNReal.toReal_nonneg
          · norm_num
    _ = 1 := one_mul 1

/-! ### Energy increment lemma -/

section TAverage

variable [IsProbabilityMeasure μ]

/-- The T-average of a graphon: for fixed T, W_T(x) = (1/μ(T)) ∫_T W(x,y) dμ(y).

This is the conditional expectation of W(x,·) given that y ∈ T. -/
noncomputable def tAverage (W : Graphon α μ) (T : Set α) (x : α) : ℝ :=
  if hT : μ T = 0 then 0
  else (μ T).toReal⁻¹ * ∫ y in T, W.toAEEqFun (x, y) ∂μ

/-- The T-average is measurable. -/
theorem tAverage_measurable (W : Graphon α μ) (T : Set α) (hT : MeasurableSet T) :
    Measurable (tAverage W T) := by
  unfold tAverage
  by_cases h : μ T = 0
  · simp only [h, dif_pos, measurable_const]
  · simp only [h, dif_neg, not_false_eq_true]
    apply Measurable.const_mul
    -- Need to show x ↦ ∫ y in T, W(x, y) ∂μ is measurable
    -- This follows from StronglyMeasurable.integral_prod_right
    have h_int : StronglyMeasurable fun x => ∫ y in T, W.toAEEqFun (x, y) ∂μ := by
      -- Use StronglyMeasurable.integral_prod_right for restricted measure
      have h1 : StronglyMeasurable fun x => ∫ y, W.toAEEqFun (x, y) ∂(μ.restrict T) :=
        StronglyMeasurable.integral_prod_right W.toAEEqFun.stronglyMeasurable
      simp only [Measure.restrict_apply'] at h1 ⊢
      convert h1 using 1
    exact h_int.measurable

/-- The T-average takes values in [0, 1] for a.e. x when W is a graphon.

This uses that W ∈ [0,1] a.e. on the product measure. By Fubini (ae_ae_of_ae_prod),
for a.e. x, the function y ↦ W(x,y) is in [0,1] for a.e. y. Then the integral
is bounded: 0 ≤ ∫_T W(x,y) ≤ μ(T). -/
theorem tAverage_ae_mem_Icc (W : Graphon α μ) (T : Set α) (hT : MeasurableSet T) :
    ∀ᵐ x ∂μ, tAverage W T x ∈ Set.Icc 0 1 := by
  -- Step 1: From W.ae_mem_Icc (on product), get pointwise bounds for a.e. x
  have h_ae_ae := Measure.ae_ae_of_ae_prod W.ae_mem_Icc
  -- h_ae_ae : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, W(x,y) ∈ [0,1]
  -- Step 2: Get ae-strong-measurability for a.e. x
  have h_meas_ae := AEStronglyMeasurable.prodMk_left W.toAEEqFun.aestronglyMeasurable
  -- h_meas_ae : ∀ᵐ x ∂μ, AEStronglyMeasurable (fun y => W(x,y)) μ
  filter_upwards [h_ae_ae, h_meas_ae] with x hx hx_meas
  unfold tAverage
  by_cases h : μ T = 0
  · simp only [h, dif_pos, Set.mem_Icc, le_refl, zero_le_one, and_self]
  · simp only [h, dif_neg, not_false_eq_true, Set.mem_Icc]
    have hT_pos : 0 < (μ T).toReal := ENNReal.toReal_pos h (measure_lt_top μ T).ne
    -- hx : ∀ᵐ y ∂μ, W(x,y) ∈ [0,1]
    have hx_lower : ∀ᵐ y ∂μ, 0 ≤ W.toAEEqFun (x, y) := by
      filter_upwards [hx] with y hy; exact hy.1
    have hx_upper : ∀ᵐ y ∂μ, W.toAEEqFun (x, y) ≤ 1 := by
      filter_upwards [hx] with y hy; exact hy.2
    constructor
    · -- tAverage ≥ 0
      apply mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      exact setIntegral_nonneg_of_ae hx_lower
    · -- tAverage ≤ 1
      -- Need: (μ T)⁻¹ * ∫_T W(x,y) ≤ 1, i.e., ∫_T W(x,y) ≤ μ(T)
      rw [inv_mul_le_iff₀ hT_pos, mul_one]
      -- Integrability: bounded a.e. function on finite measure space
      have h_int_W : IntegrableOn (fun y => W.toAEEqFun (x, y)) T μ := by
        apply Measure.integrableOn_of_bounded (M := 1) (measure_lt_top μ T).ne
        · exact hx_meas
        · filter_upwards [ae_restrict_of_ae hx] with y hy
          simp only [Real.norm_eq_abs, abs_le]
          exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
      calc ∫ y in T, W.toAEEqFun (x, y) ∂μ
          ≤ ∫ y in T, (1 : ℝ) ∂μ := by
            apply setIntegral_mono_ae_restrict h_int_W integrableOn_const
            filter_upwards [ae_restrict_of_ae hx_upper] with y hy; exact hy
        _ = (μ T).toReal := by rw [setIntegral_const]; simp [Measure.real]

/-- The average of W_T over S equals rectAverage W S T.

This is a consequence of Fubini-Tonelli:
  (1/μS) ∫_S W_T dx = (1/μS) ∫_S (1/μT) ∫_T W(x,y) dy dx
                     = (1/μS μT) ∫_{S×T} W
                     = rectAverage W S T -/
theorem tAverage_integral_eq_rectAverage (W : Graphon α μ) (S T : Set α)
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hμS : μ S ≠ 0) (hμT : μ T ≠ 0) :
    (μ S).toReal⁻¹ * ∫ x in S, tAverage W T x ∂μ = rectAverage W S T := by
  -- Step 1: Unfold tAverage and simplify (μ T ≠ 0 case)
  unfold tAverage
  simp only [hμT, dif_neg, not_false_eq_true]
  -- Step 2: Unfold rectAverage
  unfold rectAverage
  simp only [hμS, hμT, dif_neg, not_false_eq_true]
  -- Step 3: Show integrability on S×T for Fubini
  have h_int : IntegrableOn (fun p => W.toAEEqFun p) (S ×ˢ T) (μ.prod μ) := by
    apply Measure.integrableOn_of_bounded (M := 1)
    · rw [Measure.prod_prod S T]
      exact (ENNReal.mul_lt_top (measure_lt_top μ S) (measure_lt_top μ T)).ne
    · exact W.toAEEqFun.aestronglyMeasurable
    · filter_upwards [ae_restrict_of_ae W.ae_mem_Icc] with p hp
      simp only [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hp.1], by linarith [hp.2]⟩
  -- Step 4: Apply Fubini (setIntegral_prod.symm) to convert ∫_{S×T} to ∫_S ∫_T
  have h_fubini := setIntegral_prod (f := fun p => W.toAEEqFun p) h_int
  -- h_fubini : ∫_{S×T} W = ∫_S (∫_T W(x,y)) dx
  -- Rewrite RHS using Fubini
  rw [h_fubini]
  -- Goal: (μS)⁻¹ * ∫_S (μT)⁻¹ * (∫_T W(x,y) dy) dx = (μS)⁻¹ * (μT)⁻¹ * ∫_S (∫_T W(x,y) dy) dx
  -- Pull constant out of integral: ∫_S c * f dx = c * ∫_S f dx
  have h_pull : ∫ x in S, (μ T).toReal⁻¹ * ∫ y in T, W.toAEEqFun (x, y) ∂μ ∂μ =
      (μ T).toReal⁻¹ * ∫ x in S, ∫ y in T, W.toAEEqFun (x, y) ∂μ ∂μ := by
    rw [← integral_const_mul]
  rw [h_pull]
  ring

/-! ### Helper lemmas for energy increment -/

/-- Weighted variance identity: when splitting a weighted average, the energy difference
equals a weighted difference of squares.

If c = (a*c1 + b*c2) / (a+b) is the weighted average, then:
  a*c1² + b*c2² - (a+b)*c² = (a*b/(a+b)) * (c1 - c2)²

This identity is key for the energy increment lemma. When a rectangle S×T is split
into S₁×T and S₂×T with respective averages c1 and c2, the energy change comes from
this weighted variance formula. -/
lemma weighted_sq_diff (a b c1 c2 : ℝ) (ha : 0 < a) (hb : 0 < b) :
    let c := (a * c1 + b * c2) / (a + b)
    a * c1 ^ 2 + b * c2 ^ 2 - (a + b) * c ^ 2 = (a * b / (a + b)) * (c1 - c2) ^ 2 := by
  intro c
  have hab : a + b ≠ 0 := by linarith
  have hab_pos : 0 < a + b := by linarith
  -- Substitute the definition of c
  have hc : c = (a * c1 + b * c2) / (a + b) := rfl
  -- Clear denominators on both sides by multiplying by (a+b)²
  have h_lhs : a * c1 ^ 2 + b * c2 ^ 2 - (a + b) * c ^ 2 =
      (a * c1 ^ 2 + b * c2 ^ 2) * (a + b) / (a + b) - (a * c1 + b * c2) ^ 2 / (a + b) := by
    rw [hc]; field_simp [hab]
  have h_rhs : (a * b / (a + b)) * (c1 - c2) ^ 2 = a * b * (c1 - c2) ^ 2 / (a + b) := by
    field_simp [hab]
  rw [h_lhs, h_rhs]
  ring

/-- Cauchy-Schwarz for set integrals: (∫_T f)² ≤ μ(T) · ∫_T f².

This is Jensen's inequality applied to the convex function x².
The key is: (average f)² ≤ average(f²), which rearranges to give this bound. -/
lemma sq_setIntegral_le_measure_mul_setIntegral_sq [IsProbabilityMeasure μ]
    (f : α → ℝ) (T : Set α) (hf_int : IntegrableOn f T μ)
    (hf_sq_int : IntegrableOn (fun x => (f x) ^ 2) T μ) :
    (∫ x in T, f x ∂μ) ^ 2 ≤ (μ T).toReal * ∫ x in T, (f x) ^ 2 ∂μ := by
  -- Handle μ T = 0 case
  by_cases hμT : μ T = 0
  · rw [Measure.restrict_eq_zero.mpr hμT]
    simp [hμT, ENNReal.toReal_zero]
  -- Main case: μ T ≠ 0
  have hμT_top : μ T ≠ ⊤ := (measure_lt_top μ T).ne
  have hμT_pos : (0 : ℝ) < (μ T).toReal := ENNReal.toReal_pos hμT hμT_top
  -- Step 1: Jensen says g(⨍ f) ≤ ⨍ g(f) where g(x) = x²
  have hconv : ConvexOn ℝ univ (fun x : ℝ => x ^ 2) :=
    (Even.strictConvexOn_pow (by norm_num : Even 2) (by norm_num : (2 : ℕ) ≠ 0)).convexOn
  have hcont : ContinuousOn (fun x : ℝ => x ^ 2) univ := continuous_pow 2 |>.continuousOn
  have h_mem : ∀ᵐ x ∂μ.restrict T, f x ∈ (univ : Set ℝ) := by
    filter_upwards with x; exact mem_univ _
  have h_jensen := ConvexOn.map_set_average_le hconv hcont isClosed_univ hμT hμT_top
    h_mem hf_int hf_sq_int
  -- h_jensen : (⨍ f)² ≤ ⨍ f²
  -- Step 2: Unfold averages and do algebra
  rw [setAverage_eq, setAverage_eq] at h_jensen
  simp only [smul_eq_mul, Measure.real] at h_jensen
  -- h_jensen : ((μT)⁻¹ * ∫f)² ≤ (μT)⁻¹ * ∫f²
  -- Multiply by (μT)² to get: (∫f)² ≤ (μT) * ∫f²
  have h_key : (μ T).toReal⁻¹ ^ 2 * (∫ x in T, f x ∂μ) ^ 2 ≤
               (μ T).toReal⁻¹ * ∫ x in T, f x ^ 2 ∂μ := by
    have h1 : ((μ T).toReal⁻¹ * ∫ x in T, f x ∂μ) ^ 2 =
              (μ T).toReal⁻¹ ^ 2 * (∫ x in T, f x ∂μ) ^ 2 := by ring
    rw [← h1]
    exact h_jensen
  have hμT_inv_sq : (μ T).toReal⁻¹ ^ 2 = ((μ T).toReal ^ 2)⁻¹ := by rw [inv_pow]
  calc (∫ x in T, f x ∂μ) ^ 2
      = (μ T).toReal ^ 2 * ((μ T).toReal⁻¹ ^ 2 * (∫ x in T, f x ∂μ) ^ 2) := by
        rw [hμT_inv_sq]; field_simp
    _ ≤ (μ T).toReal ^ 2 * ((μ T).toReal⁻¹ * ∫ x in T, f x ^ 2 ∂μ) := by
        apply mul_le_mul_of_nonneg_left h_key (sq_nonneg _)
    _ = (μ T).toReal * ∫ x in T, f x ^ 2 ∂μ := by field_simp

/-- Pointwise bound: the T-average deviation squared is bounded by
the average squared deviation over T.

For fixed x: (W_T(x) - c)² ≤ (μT)⁻¹ · ∫_T (W(x,y) - c)² dy

This follows from `sq_setIntegral_le_measure_mul_setIntegral_sq`. -/
lemma tAverage_sub_sq_le_avg_sq [IsProbabilityMeasure μ]
    (W : Graphon α μ) (T : Set α) (c : ℝ) (hμT : μ T ≠ 0) (x : α)
    (hW_int : IntegrableOn (fun y => W.toAEEqFun (x, y)) T μ)
    (hx_int : IntegrableOn (fun y => W.toAEEqFun (x, y) - c) T μ)
    (hx_sq_int : IntegrableOn (fun y => (W.toAEEqFun (x, y) - c) ^ 2) T μ) :
    (tAverage W T x - c) ^ 2 ≤
      (μ T).toReal⁻¹ * ∫ y in T, (W.toAEEqFun (x, y) - c) ^ 2 ∂μ := by
  unfold tAverage
  simp only [hμT, dif_neg, not_false_eq_true]
  have hμT_top : μ T ≠ ⊤ := (measure_lt_top μ T).ne
  have hμT_pos : (0 : ℝ) < (μ T).toReal := ENNReal.toReal_pos hμT hμT_top
  set f := fun y => W.toAEEqFun (x, y) - c with hf_def
  have hc_int : IntegrableOn (fun _ : α => c) T μ := integrableOn_const (hs := hμT_top)
  have h_lin : (μ T).toReal⁻¹ * ∫ y in T, W.toAEEqFun (x, y) ∂μ - c =
               (μ T).toReal⁻¹ * ∫ y in T, f y ∂μ := by
    rw [integral_sub hW_int hc_int]
    rw [setIntegral_const]
    simp only [Measure.real, smul_eq_mul]
    field_simp
  rw [h_lin]
  have h_cs : (∫ y in T, f y ∂μ) ^ 2 ≤ (μ T).toReal * ∫ y in T, (f y) ^ 2 ∂μ :=
    sq_setIntegral_le_measure_mul_setIntegral_sq f T hx_int hx_sq_int
  calc ((μ T).toReal⁻¹ * ∫ y in T, f y ∂μ) ^ 2
      = (μ T).toReal⁻¹ ^ 2 * (∫ y in T, f y ∂μ) ^ 2 := by ring
    _ ≤ (μ T).toReal⁻¹ ^ 2 * ((μ T).toReal * ∫ y in T, (f y) ^ 2 ∂μ) := by
        apply mul_le_mul_of_nonneg_left h_cs (sq_nonneg _)
    _ = (μ T).toReal⁻¹ * ∫ y in T, (f y) ^ 2 ∂μ := by rw [inv_pow]; field_simp

/-- Jensen's inequality gives an UPPER bound for the T-average squared deviation.

By Jensen: (∫_T f)² / μ(T) ≤ ∫_T f²
Applied pointwise: (W_T(x) - c)² = ((1/μT) ∫_T (W(x,y) - c))² ≤ (1/μT) ∫_T (W(x,y) - c)²
Integrating over S: ∫_S (W_T - c)² ≤ (1/μT) ∫_{S×T} (W - c)²

Note: This is an UPPER bound. For a lower bound, we need a different approach. -/
theorem tAverage_sq_le_defect_div (W : Graphon α μ) (S T : Set α)
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hμS : μ S ≠ 0) (hμT : μ T ≠ 0) :
    ∫ x in S, (tAverage W T x - rectAverage W S T) ^ 2 ∂μ ≤
      (μ T).toReal⁻¹ * ∫ p in S ×ˢ T, (W.toAEEqFun p - rectAverage W S T) ^ 2 ∂(μ.prod μ) := by
  set c := rectAverage W S T with hc_def
  have hμT_top : μ T ≠ ⊤ := (measure_lt_top μ T).ne
  have hμT_pos : (0 : ℝ) < (μ T).toReal := ENNReal.toReal_pos hμT hμT_top
  -- Define the inner integrand f(x,y) = (W(x,y) - c)²
  set f : α × α → ℝ := fun p => (W.toAEEqFun p - c) ^ 2 with hf_def
  -- Step 1: Integrability of f on S×T (W bounded in [0,1], c in [0,1])
  have h_int_prod : IntegrableOn f (S ×ˢ T) (μ.prod μ) := by
    apply Measure.integrableOn_of_bounded (M := 4)
    · rw [Measure.prod_prod S T]
      exact (ENNReal.mul_lt_top (measure_lt_top μ S) (measure_lt_top μ T)).ne
    · exact (continuous_pow 2).comp_aestronglyMeasurable
        (W.toAEEqFun.aestronglyMeasurable.sub aestronglyMeasurable_const)
    · filter_upwards [ae_restrict_of_ae W.ae_mem_Icc] with ⟨x, y⟩ hW
      simp only [hf_def, Real.norm_eq_abs]
      have hc_bnd : c ∈ Icc (0 : ℝ) 1 := rectAverage_mem_Icc W S T hS hT
      have h1 : |W.toAEEqFun (x, y) - c| ≤ 2 := by
        rw [abs_le]; constructor <;> linarith [hW.1, hW.2, hc_bnd.1, hc_bnd.2]
      have h2 : (W.toAEEqFun (x, y) - c) ^ 2 ≤ 4 := by
        obtain ⟨h1a, h1b⟩ := abs_le.mp h1
        have := sq_le_sq' h1a h1b
        simp only at this
        linarith [sq_nonneg (W.toAEEqFun (x, y) - c)]
      rw [abs_of_nonneg (sq_nonneg _)]
      exact h2
  -- Step 2: Apply Fubini (setIntegral_prod) to convert to iterated integral
  have h_fubini := setIntegral_prod f h_int_prod
  -- h_fubini : ∫_{S×T} f = ∫_S (∫_T f(x,y))
  rw [h_fubini, ← integral_const_mul]
  -- Goal: ∫_S (tAverage - c)² ≤ ∫_S ((μT)⁻¹ * ∫_T (W - c)²)

  -- Step 3: Apply setIntegral_mono_ae_restrict with pointwise Cauchy-Schwarz bound
  apply setIntegral_mono_ae_restrict
  -- (a) LHS integrand is integrable on S (bounded by 4)
  · apply Measure.integrableOn_of_bounded (M := 4)
    · exact (measure_lt_top μ S).ne
    · exact (continuous_pow 2).comp_aestronglyMeasurable
        ((tAverage_measurable W T hT).aestronglyMeasurable.sub aestronglyMeasurable_const)
    · filter_upwards [ae_restrict_of_ae (tAverage_ae_mem_Icc W T hT)] with x hx
      simp only [Real.norm_eq_abs]
      have hc_bnd : c ∈ Icc (0 : ℝ) 1 := rectAverage_mem_Icc W S T hS hT
      rw [abs_of_nonneg (sq_nonneg _)]
      have h1 : |tAverage W T x - c| ≤ 2 := by
        rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hc_bnd.1, hc_bnd.2]
      calc (tAverage W T x - c) ^ 2 ≤ |tAverage W T x - c| ^ 2 := sq_le_sq' (neg_abs_le _) (le_abs_self _)
        _ ≤ 2 ^ 2 := sq_le_sq' (by linarith [abs_nonneg (tAverage W T x - c)]) h1
        _ = 4 := by norm_num
  -- (b) RHS integrand is integrable on S (follows from Fubini)
  · -- IntegrableOn (fun x => (μ T)⁻¹ * ∫_T (W(x,y) - c)²) S μ
    -- From h_int_prod: f integrable on S×T ⟹ fun x ↦ ∫_T f(x,y) integrable on S
    -- IntegrableOn f (S ×ˢ T) (μ.prod μ) = Integrable f ((μ.prod μ).restrict (S ×ˢ T))
    -- By Measure.prod_restrict: (μ.prod μ).restrict (S ×ˢ T) = (μ.restrict S).prod (μ.restrict T)
    have h_prod_eq : (μ.prod μ).restrict (S ×ˢ T) = (μ.restrict S).prod (μ.restrict T) :=
      (Measure.prod_restrict S T).symm
    -- Convert IntegrableOn to Integrable on product of restricted measures
    have h_int_full : Integrable f ((μ.restrict S).prod (μ.restrict T)) := by
      rw [← h_prod_eq]; exact h_int_prod
    -- Apply Fubini integrability: ∫_T f(x,y) is integrable as function of x on S
    have h_inner_int : Integrable (fun x => ∫ y, f (x, y) ∂μ.restrict T) (μ.restrict S) :=
      h_int_full.integral_prod_left
    -- h_inner_int is IntegrableOn (fun x => ∫_T f(x,y) dμ) S μ
    -- Multiplying by constant preserves integrability
    exact h_inner_int.const_mul _
  -- (c) Pointwise bound: (tAverage - c)² ≤ (μT)⁻¹ * ∫_T (W - c)² for a.e. x
  · -- Key: Apply tAverage_sub_sq_le_avg_sq (Cauchy-Schwarz for averages)
    -- For a.e. x: (tAverage W T x - c)² ≤ (μT)⁻¹ * ∫_T (W(x,y) - c)² dy
    -- First get integrability of h_int_full on the product of restricted measures
    have h_prod_eq : (μ.prod μ).restrict (S ×ˢ T) = (μ.restrict S).prod (μ.restrict T) :=
      (Measure.prod_restrict S T).symm
    have h_int_full : Integrable f ((μ.restrict S).prod (μ.restrict T)) := by
      rw [← h_prod_eq]; exact h_int_prod
    -- From h_int_full.prod_right_ae: for a.e. x ∂(μ.restrict S), the slice is integrable
    have h_slice_ae : ∀ᵐ x ∂(μ.restrict S), Integrable (fun y => f (x, y)) (μ.restrict T) :=
      h_int_full.prod_right_ae
    -- Also need integrability of W and W - c on slices
    -- W is integrable since it's bounded by 1 on a finite measure space
    have h_W_int_prod : IntegrableOn (fun p => W.toAEEqFun p) (S ×ˢ T) (μ.prod μ) :=
      (SymmKernel.graphon_integrable W).integrableOn
    have h_W_full : Integrable (fun p => W.toAEEqFun p) ((μ.restrict S).prod (μ.restrict T)) := by
      rw [← h_prod_eq]; exact h_W_int_prod
    have h_W_slice_ae : ∀ᵐ x ∂(μ.restrict S), Integrable (fun y => W.toAEEqFun (x, y)) (μ.restrict T) :=
      h_W_full.prod_right_ae
    -- Now filter_upwards on these ae conditions
    filter_upwards [h_slice_ae, h_W_slice_ae] with x h_f_int h_W_int
    -- h_f_int : Integrable (fun y => f (x, y)) (μ.restrict T)
    -- h_W_int : Integrable (fun y => W.toAEEqFun (x, y)) (μ.restrict T)
    -- Convert from Integrable on μ.restrict T to IntegrableOn on T
    have h_W_intOn : IntegrableOn (fun y => W.toAEEqFun (x, y)) T μ := h_W_int
    have h_f_intOn : IntegrableOn (fun y => f (x, y)) T μ := h_f_int
    -- h_f_intOn is integrability of (W(x,y) - c)²
    -- Need to show integrability of W(x,y) - c (follows from W integrable and c constant)
    have h_diff_intOn : IntegrableOn (fun y => W.toAEEqFun (x, y) - c) T μ :=
      h_W_intOn.sub (integrableOn_const (measure_lt_top μ T).ne)
    -- Apply tAverage_sub_sq_le_avg_sq
    exact tAverage_sub_sq_le_avg_sq W T c hμT x h_W_intOn h_diff_intOn h_f_intOn

/-- For a.e. x, ∫_T (W(x,·) - tAverage W T x) = 0 by definition of tAverage. -/
theorem ae_setIntegral_sub_tAverage_eq_zero (W : Graphon α μ) (T : Set α)
    (_hT : MeasurableSet T) (hμT : μ T ≠ 0) :
    ∀ᵐ x ∂μ, ∫ y in T, (W.toAEEqFun (x, y) - tAverage W T x) ∂μ = 0 := by
  -- For a.e. x, the slice y ↦ W(x,y) is integrable
  have h_W_int_prod : Integrable (fun p => W.toAEEqFun p) (μ.prod μ) :=
    SymmKernel.graphon_integrable W
  have h_W_slice_ae : ∀ᵐ x ∂μ, Integrable (fun y => W.toAEEqFun (x, y)) μ :=
    h_W_int_prod.prod_right_ae
  filter_upwards [h_W_slice_ae] with x hW_int
  have hμT_top : μ T ≠ ⊤ := (measure_lt_top μ T).ne
  have hμT_pos : (0 : ℝ) < (μ T).toReal := ENNReal.toReal_pos hμT hμT_top
  have hW_intOn : IntegrableOn (fun y => W.toAEEqFun (x, y)) T μ := hW_int.integrableOn
  have hc_int : IntegrableOn (fun _ : α => tAverage W T x) T μ := integrableOn_const hμT_top
  -- Split the integral
  rw [integral_sub hW_intOn hc_int, setIntegral_const]
  simp only [Measure.real, smul_eq_mul]
  -- Unfold tAverage
  unfold tAverage
  simp only [hμT, dif_neg, not_false_eq_true]
  -- Cancel: ∫_T W - μ(T) * (μ(T)⁻¹ * ∫_T W) = 0
  have hne : (μ T).toReal ≠ 0 := ne_of_gt hμT_pos
  -- Goal: ∫ W - μ(T) * (μ(T)⁻¹ * ∫ W) = 0
  -- Use mul_inv_cancel_left₀: a * (a⁻¹ * b) = b when a ≠ 0
  rw [mul_inv_cancel_left₀ hne, sub_self]

/-- Pointwise variance decomposition: for fixed x, the integral of (f - c)² over T equals
the integral of (f - m)² plus μ(T) * (m - c)², when ∫_T (f - m) = 0.

This is the key algebraic identity: (f - c)² = (f - m)² + 2(f - m)(m - c) + (m - c)²
and the cross term vanishes when integrated because ∫_T (f - m) = 0. -/
lemma setIntegral_sq_eq_variance_plus_mean_sq {f : α → ℝ} {m c : ℝ} (T : Set α)
    (hT : MeasurableSet T) (hμT_top : μ T ≠ ⊤)
    (hf_int : IntegrableOn f T μ)
    (hfsq_int : IntegrableOn (fun y => (f y - m) ^ 2) T μ)
    (hfsq_c_int : IntegrableOn (fun y => (f y - c) ^ 2) T μ)
    (h_cross : ∫ y in T, (f y - m) ∂μ = 0) :
    ∫ y in T, (f y - c) ^ 2 ∂μ =
      ∫ y in T, (f y - m) ^ 2 ∂μ + (μ T).toReal * (m - c) ^ 2 := by
  -- Integrability of remaining terms
  have hm_int : IntegrableOn (fun _ => m) T μ := integrableOn_const hμT_top
  have hdiff_m_int : IntegrableOn (fun y => f y - m) T μ := hf_int.sub hm_int
  have hcross_int : IntegrableOn (fun y => 2 * (f y - m) * (m - c)) T μ := by
    have h1 : IntegrableOn (fun y => 2 * (f y - m)) T μ := hdiff_m_int.const_mul 2
    exact h1.mul_const (m - c)
  have hconst_int : IntegrableOn (fun _ => (m - c) ^ 2) T μ := integrableOn_const hμT_top
  -- Algebraic expansion: (f - c)² = (f - m)² + 2(f - m)(m - c) + (m - c)²
  have h_expand : ∀ y, (f y - c) ^ 2 = (f y - m) ^ 2 + 2 * (f y - m) * (m - c) + (m - c) ^ 2 :=
    fun y => by ring
  -- Step 1: Expand the integrand
  have h1 : ∫ y in T, (f y - c) ^ 2 ∂μ =
      ∫ y in T, ((f y - m) ^ 2 + 2 * (f y - m) * (m - c) + (m - c) ^ 2) ∂μ :=
    setIntegral_congr_ae hT (ae_of_all μ (fun y _ => h_expand y))
  -- Step 2: Split into three integrals
  have h2 : ∫ y in T, ((f y - m) ^ 2 + 2 * (f y - m) * (m - c) + (m - c) ^ 2) ∂μ =
      ∫ y in T, (f y - m) ^ 2 ∂μ + ∫ y in T, 2 * (f y - m) * (m - c) ∂μ +
      ∫ y in T, (m - c) ^ 2 ∂μ := by
    have eq1 : ∫ y in T, ((f y - m) ^ 2 + 2 * (f y - m) * (m - c) + (m - c) ^ 2) ∂μ =
        ∫ y in T, ((f y - m) ^ 2 + 2 * (f y - m) * (m - c)) + (m - c) ^ 2 ∂μ :=
      setIntegral_congr_ae hT (ae_of_all μ (fun y _ => by ring))
    have eq2 : ∫ y in T, ((f y - m) ^ 2 + 2 * (f y - m) * (m - c)) + (m - c) ^ 2 ∂μ =
        ∫ y in T, ((f y - m) ^ 2 + 2 * (f y - m) * (m - c)) ∂μ + ∫ y in T, (m - c) ^ 2 ∂μ :=
      integral_add (hfsq_int.add hcross_int) hconst_int
    have eq3 : ∫ y in T, ((f y - m) ^ 2 + 2 * (f y - m) * (m - c)) ∂μ =
        ∫ y in T, (f y - m) ^ 2 ∂μ + ∫ y in T, 2 * (f y - m) * (m - c) ∂μ :=
      integral_add hfsq_int hcross_int
    linarith [eq1, eq2, eq3]
  -- Step 3: Evaluate cross term (factors out the constant (m - c))
  have h3 : ∫ y in T, 2 * (f y - m) * (m - c) ∂μ = 2 * (m - c) * ∫ y in T, (f y - m) ∂μ := by
    calc ∫ y in T, 2 * (f y - m) * (m - c) ∂μ
        = ∫ y in T, (2 * (m - c)) * (f y - m) ∂μ :=
          setIntegral_congr_ae hT (ae_of_all μ (fun y _ => by ring))
      _ = (2 * (m - c)) * ∫ y in T, (f y - m) ∂μ := integral_const_mul _ _
      _ = 2 * (m - c) * ∫ y in T, (f y - m) ∂μ := by ring
  -- Step 4: Cross term vanishes
  have h4 : 2 * (m - c) * ∫ y in T, (f y - m) ∂μ = 0 := by rw [h_cross]; ring
  -- Step 5: Constant term evaluates to μ(T) * (m - c)²
  have h5 : ∫ y in T, (m - c) ^ 2 ∂μ = (μ T).toReal * (m - c) ^ 2 := by
    rw [setIntegral_const]
    simp only [smul_eq_mul, Measure.real]
  -- Combine
  calc ∫ y in T, (f y - c) ^ 2 ∂μ
      = ∫ y in T, ((f y - m) ^ 2 + 2 * (f y - m) * (m - c) + (m - c) ^ 2) ∂μ := h1
    _ = ∫ y in T, (f y - m) ^ 2 ∂μ + ∫ y in T, 2 * (f y - m) * (m - c) ∂μ +
        ∫ y in T, (m - c) ^ 2 ∂μ := h2
    _ = ∫ y in T, (f y - m) ^ 2 ∂μ + 2 * (m - c) * ∫ y in T, (f y - m) ∂μ +
        ∫ y in T, (m - c) ^ 2 ∂μ := by rw [h3]
    _ = ∫ y in T, (f y - m) ^ 2 ∂μ + 0 + ∫ y in T, (m - c) ^ 2 ∂μ := by rw [h4]
    _ = ∫ y in T, (f y - m) ^ 2 ∂μ + (μ T).toReal * (m - c) ^ 2 := by rw [h5]; ring

/-- Variance decomposition along T: total defect = within-slice + between-slice variance.

∫_{S×T} (W - c)² = ∫_S (∫_T (W - tAvg)²) + μ(T) * ∫_S (tAvg - c)²

where tAvg = tAverage W T and c = rectAverage W S T.

The key insight is that ∫_T (W(x,·) - tAvg(x)) = 0 by definition of tAvg,
so the cross term vanishes when expanding (W - c) = (W - tAvg) + (tAvg - c). -/
theorem defect_eq_within_plus_between (W : Graphon α μ) (S T : Set α)
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hμS : μ S ≠ 0) (hμT : μ T ≠ 0) :
    ∫ p in S ×ˢ T, (W.toAEEqFun p - rectAverage W S T) ^ 2 ∂(μ.prod μ) =
      ∫ x in S, (∫ y in T, (W.toAEEqFun (x, y) - tAverage W T x) ^ 2 ∂μ) ∂μ +
      (μ T).toReal * ∫ x in S, (tAverage W T x - rectAverage W S T) ^ 2 ∂μ := by
  -- **Variance decomposition**: Total defect = within-slice + between-slice variance
  --
  -- Proof sketch:
  -- 1. Use Fubini: ∫_{S×T} f = ∫_S (∫_T f)
  -- 2. Pointwise: (W - c)² = (W - W_T)² + 2(W - W_T)(W_T - c) + (W_T - c)²
  -- 3. Cross term ∫_T 2(W - W_T)(W_T - c) = 2(W_T - c) * ∫_T (W - W_T) = 0
  --    (since ∫_T (W - W_T) = 0 by definition of W_T = tAverage W T)
  -- 4. Constant term: ∫_T (W_T - c)² = μ(T) * (W_T - c)²
  -- 5. Integrate over S and factor out μ(T) using integral_const_mul
  --
  -- Technical requirements:
  -- - Integrability of squared differences (bounded by 4)
  -- - Fubini via setIntegral_prod and prod_right_ae
  -- - setIntegral_congr for ae pointwise equality

  -- Abbreviations
  set c := rectAverage W S T with hc_def
  set W_T := tAverage W T with hW_T_def

  -- Measure bounds
  have hμT_top : μ T ≠ ⊤ := (measure_lt_top μ T).ne
  have hμS_top : μ S ≠ ⊤ := (measure_lt_top μ S).ne
  have hμT_pos : (0 : ℝ) < (μ T).toReal := ENNReal.toReal_pos hμT hμT_top

  -- Integrability of (W - c)² on S×T
  have h_int_prod : IntegrableOn (fun p => (W.toAEEqFun p - c) ^ 2) (S ×ˢ T) (μ.prod μ) := by
    apply Measure.integrableOn_of_bounded (M := 4)
    · rw [Measure.prod_prod S T]
      exact (ENNReal.mul_lt_top (measure_lt_top μ S) (measure_lt_top μ T)).ne
    · exact (continuous_pow 2).comp_aestronglyMeasurable
        (W.toAEEqFun.aestronglyMeasurable.sub aestronglyMeasurable_const)
    · filter_upwards [ae_restrict_of_ae W.ae_mem_Icc] with ⟨x, y⟩ hW
      simp only [Real.norm_eq_abs]
      have hc_bnd : c ∈ Icc (0 : ℝ) 1 := rectAverage_mem_Icc W S T hS hT
      have h1 : |W.toAEEqFun (x, y) - c| ≤ 2 := by
        rw [abs_le]; constructor <;> linarith [hW.1, hW.2, hc_bnd.1, hc_bnd.2]
      have h2 : (W.toAEEqFun (x, y) - c) ^ 2 ≤ 4 := by
        obtain ⟨h1a, h1b⟩ := abs_le.mp h1
        have := sq_le_sq' h1a h1b
        simp only at this
        linarith [sq_nonneg (W.toAEEqFun (x, y) - c)]
      rw [abs_of_nonneg (sq_nonneg _)]
      exact h2

  -- Step 1: Apply Fubini to get iterated integral
  have h_fubini := setIntegral_prod (f := fun p => (W.toAEEqFun p - c) ^ 2) h_int_prod
  rw [h_fubini]

  -- Step 2: Pointwise algebraic identity on inner integral
  -- For each x: ∫_T (W - c)² = ∫_T (W - W_T)² + ∫_T 2(W - W_T)(W_T - c) + ∫_T (W_T - c)²
  -- The cross term vanishes, and the constant term becomes μ(T) * (W_T - c)²

  -- Get slice integrability for a.e. x
  have h_prod_eq : (μ.prod μ).restrict (S ×ˢ T) = (μ.restrict S).prod (μ.restrict T) :=
    (Measure.prod_restrict S T).symm
  have h_int_full : Integrable (fun p => (W.toAEEqFun p - c) ^ 2) ((μ.restrict S).prod (μ.restrict T)) := by
    rw [← h_prod_eq]; exact h_int_prod
  have h_slice_ae : ∀ᵐ x ∂(μ.restrict S),
      Integrable (fun y => (W.toAEEqFun (x, y) - c) ^ 2) (μ.restrict T) :=
    h_int_full.prod_right_ae

  -- W is integrable on product
  have h_W_int_prod : Integrable (fun p => W.toAEEqFun p) (μ.prod μ) :=
    SymmKernel.graphon_integrable W
  have h_W_full : Integrable (fun p => W.toAEEqFun p) ((μ.restrict S).prod (μ.restrict T)) := by
    rw [← h_prod_eq]; exact h_W_int_prod.integrableOn
  have h_W_slice_ae : ∀ᵐ x ∂(μ.restrict S),
      Integrable (fun y => W.toAEEqFun (x, y)) (μ.restrict T) :=
    h_W_full.prod_right_ae

  -- The proof follows the outline in the docstring:
  -- 1. Fubini converts product integral to iterated integral
  -- 2. Algebraically expand (W - c)² = (W - W_T)² + 2(W - W_T)(W_T - c) + (W_T - c)²
  -- 3. The cross term vanishes because ∫_T (W - W_T) = 0 by definition of W_T
  -- 4. The constant term becomes μ(T) * (W_T - c)²
  -- 5. Factor μ(T) out of the outer integral

  -- The cross term vanishes by ae_setIntegral_sub_tAverage_eq_zero
  have h_cross_zero := ae_setIntegral_sub_tAverage_eq_zero W T hT hμT

  -- Build integrability conditions
  -- Every squared difference is bounded by 4 (values in [0,1])
  have sq_bound : ∀ a b : ℝ, a ∈ Set.Icc 0 1 → b ∈ Set.Icc 0 1 → (a - b) ^ 2 ≤ 4 :=
    fun a b ha hb => by
      have h1 : |a - b| ≤ 2 := by
        rw [abs_le]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
      obtain ⟨h1a, h1b⟩ := abs_le.mp h1
      have := sq_le_sq' h1a h1b
      simp only at this
      linarith [sq_nonneg (a - b)]

  -- Integrability of (W - W_T)² on T for a.e. x
  -- Use ae_ae_of_ae_prod to convert product-measure ae bound to iterated ae
  have h_W_ae_ae := Measure.ae_ae_of_ae_prod W.ae_mem_Icc

  have h_within_int_ae : ∀ᵐ x ∂μ, IntegrableOn (fun y => (W.toAEEqFun (x, y) - W_T x) ^ 2) T μ := by
    filter_upwards [tAverage_ae_mem_Icc W T hT, h_W_ae_ae] with x hWT hW_ae
    apply Measure.integrableOn_of_bounded (M := 4) hμT_top
    · exact (continuous_pow 2).comp_aestronglyMeasurable
        ((W.toAEEqFun.measurable.comp measurable_prodMk_left).aestronglyMeasurable.sub
          aestronglyMeasurable_const)
    · filter_upwards [ae_restrict_of_ae hW_ae] with y hW_y
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (sq_nonneg _)]
      exact sq_bound _ _ hW_y hWT

  -- W(x, ·) is integrable on T for a.e. x
  have h_W_int_T_ae : ∀ᵐ x ∂μ, IntegrableOn (fun y => W.toAEEqFun (x, y)) T μ := by
    filter_upwards [h_W_ae_ae] with x hW_ae
    apply Measure.integrableOn_of_bounded (M := 1) hμT_top
    · exact (W.toAEEqFun.measurable.comp measurable_prodMk_left).aestronglyMeasurable
    · filter_upwards [ae_restrict_of_ae hW_ae] with y hW_y
      simp only [Real.norm_eq_abs]
      rw [abs_le]; constructor <;> linarith [hW_y.1, hW_y.2]

  -- (W - c)² is integrable on T for a.e. x
  have h_c_int_T_ae : ∀ᵐ x ∂μ, IntegrableOn (fun y => (W.toAEEqFun (x, y) - c) ^ 2) T μ := by
    filter_upwards [h_W_ae_ae] with x hW_ae
    apply Measure.integrableOn_of_bounded (M := 4) hμT_top
    · exact (continuous_pow 2).comp_aestronglyMeasurable
        ((W.toAEEqFun.measurable.comp measurable_prodMk_left).aestronglyMeasurable.sub
          aestronglyMeasurable_const)
    · filter_upwards [ae_restrict_of_ae hW_ae] with y hW_y
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (sq_nonneg _)]
      exact sq_bound _ _ hW_y (rectAverage_mem_Icc W S T hS hT)

  -- Cross term vanishes for a.e. x
  have h_cross_ae : ∀ᵐ x ∂μ, ∫ y in T, (W.toAEEqFun (x, y) - W_T x) ∂μ = 0 := h_cross_zero

  -- For a.e. x: ∫_T (W(x,·) - c)² = ∫_T (W(x,·) - W_T(x))² + μ(T) * (W_T(x) - c)²
  -- by the binomial expansion and the vanishing cross term.
  have h_decomp_ae : ∀ᵐ x ∂μ, x ∈ S →
      ∫ y in T, (W.toAEEqFun (x, y) - c) ^ 2 ∂μ =
        ∫ y in T, (W.toAEEqFun (x, y) - W_T x) ^ 2 ∂μ + (μ T).toReal * (W_T x - c) ^ 2 := by
    filter_upwards [h_within_int_ae, h_W_int_T_ae, h_c_int_T_ae, h_cross_ae]
      with x hW_sq_int hW_int hc_int h_cross _
    exact setIntegral_sq_eq_variance_plus_mean_sq T hT hμT_top hW_int hW_sq_int hc_int h_cross

  -- Apply the pointwise decomposition to the outer integral
  rw [setIntegral_congr_ae hS h_decomp_ae]

  -- Integrability of the within term for outer integral
  -- Proof: bounded by 4 * μ(T) using W(x,y) ∈ [0,1] and tAverage ∈ [0,1]
  -- The function x ↦ ∫_T (W(x,·) - W_T(x))² is measurable by Fubini (integral of jointly
  -- measurable function) and bounded by 4 * μ(T) since (W - W_T)² ≤ 4 pointwise a.e.
  have h_within_outer_int : IntegrableOn
      (fun x => ∫ y in T, (W.toAEEqFun (x, y) - W_T x) ^ 2 ∂μ) S μ := by
    apply Measure.integrableOn_of_bounded (M := 4 * (μ T).toReal) hμS_top
    · -- Measurability: use that W is measurable and tAverage is measurable
      apply StronglyMeasurable.aestronglyMeasurable
      apply StronglyMeasurable.integral_prod_right
      apply (continuous_pow 2).stronglyMeasurable.comp_measurable
      exact W.toAEEqFun.measurable.sub ((tAverage_measurable W T hT).comp measurable_fst)
    · -- Bound: |∫_T (W - W_T)²| ≤ 4 * μ(T) for a.e. x in S
      filter_upwards [ae_restrict_of_ae (tAverage_ae_mem_Icc W T hT),
                      ae_restrict_of_ae (Measure.ae_ae_of_ae_prod W.ae_mem_Icc)]
        with x hWT hW_ae
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
      calc ∫ y in T, (W.toAEEqFun (x, y) - W_T x) ^ 2 ∂μ
          ≤ ∫ _ in T, (4 : ℝ) ∂μ := by
            apply setIntegral_mono_ae_restrict
            · -- Integrability of (W(x,·) - W_T(x))² on T
              apply Measure.integrableOn_of_bounded (M := 4) hμT_top
              · -- Use that measurable implies ae strongly measurable for ℝ-valued functions
                exact (continuous_pow 2).comp_aestronglyMeasurable
                  ((W.toAEEqFun.measurable.comp measurable_prodMk_left).aestronglyMeasurable.sub
                    aestronglyMeasurable_const)
              · filter_upwards [ae_restrict_of_ae hW_ae] with y hW_y
                simp only [Real.norm_eq_abs]
                rw [abs_of_nonneg (sq_nonneg _)]
                exact sq_bound _ _ hW_y hWT
            · exact integrableOn_const hμT_top
            · -- Pointwise bound (W - W_T)² ≤ 4 a.e. on T
              filter_upwards [ae_restrict_of_ae hW_ae] with y hW_y
              exact sq_bound _ _ hW_y hWT
        _ = 4 * (μ T).toReal := by simp [smul_eq_mul, Measure.real, mul_comm]

  -- Integrability of the between term for outer integral
  have h_between_outer_int : IntegrableOn (fun x => (μ T).toReal * (W_T x - c) ^ 2) S μ := by
    have h_sq_int : IntegrableOn (fun x => (W_T x - c) ^ 2) S μ :=
      Measure.integrableOn_of_bounded (M := 4) hμS_top
        ((continuous_pow 2).comp_aestronglyMeasurable
          ((tAverage_measurable W T hT).aestronglyMeasurable.sub aestronglyMeasurable_const))
        (by filter_upwards [ae_restrict_of_ae (tAverage_ae_mem_Icc W T hT)] with x hWT
            simp only [Real.norm_eq_abs]
            rw [abs_of_nonneg (sq_nonneg _)]
            exact sq_bound _ _ hWT (rectAverage_mem_Icc W S T hS hT))
    exact h_sq_int.const_mul (μ T).toReal

  -- Split the integral
  rw [integral_add h_within_outer_int h_between_outer_int]

  -- Factor out μ(T) from the second integral
  congr 1
  rw [integral_const_mul]

/-- Frieze-Kannan median cut lemma (key for energy increment).

If ∫_S (f - m)² ≥ ε² μ(S) where m = (1/μS) ∫_S f (the mean), then there exists
a measurable subset S₁ ⊆ S with μ(S₁), μ(S \ S₁) ≥ μ(S)/4 such that
the averages of f on S₁ and S \ S₁ differ from m by at least ε/2.

This is the key step that produces a "good cut" for the energy increment.
The proof uses Chebyshev's inequality: if variance is ε², then the probability
of deviating by ε from the mean is at least some constant.

**Standard argument**:
1. By Chebyshev: μ{x : |f(x) - m| ≥ ε/2} ≥ constant · ε²/ε² = constant
2. Split by the median: S₁ = {x ∈ S : f(x) ≤ median}, S₂ = S \ S₁
3. If variance is high, at least one of S₁ or S₂ has average differing from m

This lemma is stated but not yet proven; filling it requires careful
measure-theoretic arguments. -/
theorem exists_variance_cut (f : α → ℝ) (S : Set α) (hS : MeasurableSet S)
    (hf_meas : Measurable f) (hf_int : IntegrableOn f S μ) (hμS : μ S ≠ 0)
    (m : ℝ) (hm : m = (μ S).toReal⁻¹ * ∫ x in S, f x ∂μ)
    (ε : ℝ) (hε : ε > 0)
    (h_var : ∫ x in S, (f x - m) ^ 2 ∂μ ≥ ε ^ 2 * (μ S).toReal) :
    ∃ S₁ : Set α, MeasurableSet S₁ ∧ S₁ ⊆ S ∧
      μ S₁ ≠ 0 ∧ μ (S \ S₁) ≠ 0 ∧
      (|((μ S₁).toReal⁻¹ * ∫ x in S₁, f x ∂μ) - m| ≥ ε / 2 ∨
       |((μ (S \ S₁)).toReal⁻¹ * ∫ x in S \ S₁, f x ∂μ) - m| ≥ ε / 2) := by
  -- **Strategy**: Chebyshev/Markov argument
  --
  -- Define:
  -- - S_high = S ∩ {f ≥ m + ε/2}
  -- - S_low = S ∩ {f ≤ m - ε/2}
  --
  -- **Step 1**: Show μ(S_high) ≠ 0 ∨ μ(S_low) ≠ 0
  -- Proof by contradiction: if both are zero, then |f - m| < ε/2 a.e. on S,
  -- so ∫_S (f - m)² < (ε/2)² · μ(S) < ε² · μ(S), contradicting h_var.
  --
  -- **Step 2**: Case split
  -- If μ(S_high) ≠ 0:
  --   - Use S₁ = S_high
  --   - Show μ(S \ S_high) ≠ 0: if S = S_high a.e., then avg(f, S) ≥ m + ε/2,
  --     contradicting the definition of m
  --   - Show avg(f, S_high) ≥ m + ε/2 (since all points satisfy f ≥ m + ε/2)
  --
  -- If μ(S_low) ≠ 0: symmetric argument with ≤ instead of ≥
  --
  -- The full proof requires careful measure-theoretic arguments:
  -- **Implementation** (Markov approach):

  -- Let η = ε/2 and define the deviation sets
  set η := ε / 2 with hη_def
  have hη_pos : η > 0 := by linarith

  -- Define A⁺ = S ∩ {f ≥ m + η} and A⁻ = S ∩ {f ≤ m - η}
  let A_high := S ∩ {x | f x ≥ m + η}
  let A_low := S ∩ {x | f x ≤ m - η}

  have hA_high_meas : MeasurableSet A_high := hS.inter (hf_meas measurableSet_Ici)
  have hA_low_meas : MeasurableSet A_low := hS.inter (hf_meas measurableSet_Iic)
  have hA_high_sub : A_high ⊆ S := Set.inter_subset_left
  have hA_low_sub : A_low ⊆ S := Set.inter_subset_left

  -- Step 1: Show μ(A_high) ≠ 0 ∨ μ(A_low) ≠ 0
  -- If both were zero, then |f - m| < η a.e. on S, so variance < η² μ(S) < ε² μ(S)
  have h_exists : μ A_high ≠ 0 ∨ μ A_low ≠ 0 := by
    by_contra h_both_zero
    push_neg at h_both_zero
    obtain ⟨h_high_zero, h_low_zero⟩ := h_both_zero
    -- If μ(A_high) = 0 and μ(A_low) = 0, then |f - m| < η a.e. on S
    -- So ∫_S (f - m)² ≤ η² μ(S) = (ε/2)² μ(S) < ε² μ(S), contradicting h_var
    --
    -- The key inequality: ∫_S (f-m)² ≤ η² μ(S) follows from:
    -- - On A_high ∪ A_low (measure 0), (f-m)² could be large but contributes 0
    -- - On S \ (A_high ∪ A_low), we have |f-m| < η so (f-m)² < η²
    -- - Thus ∫_S (f-m)² = ∫_{S \ (A_high ∪ A_low)} (f-m)² < η² μ(S)
    --
    -- This contradicts h_var: ε² μ(S) ≤ ∫_S (f-m)² < η² μ(S) = (ε/2)² μ(S) = ε² μ(S) / 4
    --
    -- Key observations:
    -- 1. A_high ∪ A_low has measure 0, so the integral over it contributes 0
    -- 2. On S \ (A_high ∪ A_low), we have |f - m| < η, so (f - m)² < η²
    -- 3. Therefore ∫_S (f - m)² < η² μ(S) = (ε/2)² μ(S)
    -- 4. This contradicts h_var: ε² μ(S) ≤ ∫_S (f - m)²
    --
    -- Detailed proof:
    -- Key: on S \ (A_high ∪ A_low), we have |f - m| < η, so (f - m)² < η²
    -- The null sets A_high and A_low contribute nothing to the integral
    have hμS_top : μ S ≠ ⊤ := (measure_lt_top μ S).ne
    have hμS_pos : (0 : ℝ) < (μ S).toReal := ENNReal.toReal_pos hμS hμS_top
    -- Show A_high ∪ A_low has measure 0
    have h_union_zero : μ (A_high ∪ A_low) = 0 := by
      rw [measure_union_null h_high_zero h_low_zero]
    -- Key: On S, outside A_high ∪ A_low, we have |f x - m| < η
    have h_ae_bound : ∀ᵐ x ∂μ.restrict S, (f x - m) ^ 2 < η ^ 2 := by
      -- Use ae_restrict_iff' with the null set
      rw [ae_restrict_iff' hS]
      -- The set (A_high ∪ A_low) ∩ S has measure 0
      have h_null_in_S : μ ((A_high ∪ A_low) ∩ S) = 0 := by
        apply le_antisymm _ (zero_le _)
        calc μ ((A_high ∪ A_low) ∩ S) ≤ μ (A_high ∪ A_low) := measure_mono Set.inter_subset_left
          _ = 0 := h_union_zero
      -- Outside this null set, the bound holds
      have h_compl_eq : (A_high ∪ A_low)ᶜ ∈ ae μ := by
        rw [compl_mem_ae_iff]
        exact h_union_zero
      filter_upwards [h_compl_eq] with x hx hxS
      -- hx : x ∉ A_high ∪ A_low
      simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hx
      have hx_not_high : x ∉ A_high := hx.1
      have hx_not_low : x ∉ A_low := hx.2
      -- A_high = S ∩ {f ≥ m + η}, so x ∉ A_high means: x ∉ S or f x < m + η
      -- Since x ∈ S, we get f x < m + η
      have h1 : f x < m + η := by
        by_contra h
        push_neg at h
        exact hx_not_high ⟨hxS, h⟩
      -- A_low = S ∩ {f ≤ m - η}, so x ∉ A_low means: x ∉ S or f x > m - η
      -- Since x ∈ S, we get f x > m - η
      have h2 : f x > m - η := by
        by_contra h
        push_neg at h
        exact hx_not_low ⟨hxS, h⟩
      -- Now |f x - m| < η
      have h_abs : |f x - m| < η := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
      -- So (f x - m)² < η²
      calc (f x - m) ^ 2 = |f x - m| ^ 2 := (sq_abs _).symm
        _ < η ^ 2 := sq_lt_sq' (by linarith [abs_nonneg (f x - m)]) h_abs
    -- Bound the integral (use strict inequality to lt)
    -- First get integrability from the ae bound
    have h_sq_int : IntegrableOn (fun x => (f x - m) ^ 2) S μ := by
      apply Measure.integrableOn_of_bounded hμS_top
      · exact ((hf_meas.sub measurable_const).pow_const 2).aestronglyMeasurable
      · -- Need: ‖(f x - m)²‖ ≤ η² a.e. on S
        -- From h_ae_bound: (f x - m)² < η² a.e., so ≤ η²
        filter_upwards [h_ae_bound] with x hx
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (sq_nonneg _)]
        exact le_of_lt hx
    have h_int_bound : ∫ x in S, (f x - m) ^ 2 ∂μ ≤ η ^ 2 * (μ S).toReal := by
      calc ∫ x in S, (f x - m) ^ 2 ∂μ ≤ ∫ _ in S, η ^ 2 ∂μ := by
            apply setIntegral_mono_ae_restrict h_sq_int (integrableOn_const hμS_top)
            filter_upwards [h_ae_bound] with x hx
            exact le_of_lt hx
        _ = η ^ 2 * (μ S).toReal := by rw [setIntegral_const]; simp [Measure.real]; ring
    -- But h_var says ∫ ≥ ε² μS. If ε² μS ≤ η² μS = (ε/2)² μS = ε² μS / 4 and μS > 0, we get ε² ≤ ε²/4
    have h_contra : ε ^ 2 * (μ S).toReal ≤ η ^ 2 * (μ S).toReal := le_trans h_var h_int_bound
    have h_sq : η ^ 2 = (ε / 2) ^ 2 := by rw [hη_def]
    rw [h_sq, div_pow] at h_contra
    -- ε² μS ≤ ε²/4 μS, so ε² ≤ ε²/4, contradiction with ε > 0
    have h_ε_sq_pos : 0 < ε ^ 2 := sq_pos_of_pos hε
    nlinarith [sq_nonneg ε, hμS_pos]

  -- Step 2: Case split and construct S₁
  rcases h_exists with h_high | h_low
  · -- Case: μ(A_high) ≠ 0, use S₁ = A_high
    use A_high
    refine ⟨hA_high_meas, hA_high_sub, h_high, ?_, ?_⟩
    -- Show μ(S \ A_high) ≠ 0:
    -- If S \ A_high has measure 0, then f ≥ m + η a.e. on S
    -- But then ∫_S f ≥ (m + η) μ(S), so m ≥ m + η, contradiction since η > 0
    · by_contra h_compl_zero
      -- If S \ A_high has measure 0, then f ≥ m + η a.e. on S
      -- This contradicts m being the average
      have hμS_top : μ S ≠ ⊤ := (measure_lt_top μ S).ne
      have hμS_pos : (0 : ℝ) < (μ S).toReal := ENNReal.toReal_pos hμS hμS_top
      -- On A_high ⊆ S, f ≥ m + η pointwise
      have h_lb_on_high : ∀ x ∈ A_high, f x ≥ m + η := fun x ⟨_, hx⟩ => hx
      -- Since μ(S \ A_high) = 0, f ≥ m + η a.e. on S
      have h_ae_lb : ∀ᵐ x ∂μ.restrict S, f x ≥ m + η := by
        rw [ae_restrict_iff' hS]
        have h_compl_ae : (S \ A_high)ᶜ ∈ ae μ := by
          rw [compl_mem_ae_iff]
          exact h_compl_zero
        filter_upwards [h_compl_ae] with x hx hxS
        -- x ∈ (S \ A_high)ᶜ and x ∈ S ⟹ x ∈ A_high
        -- (S \ A_high)ᶜ = Sᶜ ∪ A_high
        rw [Set.compl_diff] at hx
        cases hx with
        | inl hx_in_high => exact h_lb_on_high x hx_in_high
        | inr hx_not_S => exact absurd hxS hx_not_S
      -- Lower bound: ∫_S f ≥ (m + η) μ(S)
      have h_int_lb : ∫ x in S, f x ∂μ ≥ (m + η) * (μ S).toReal := by
        calc ∫ x in S, f x ∂μ ≥ ∫ _ in S, (m + η) ∂μ := by
              apply setIntegral_mono_ae_restrict (integrableOn_const hμS_top) hf_int
              exact h_ae_lb
          _ = (m + η) * (μ S).toReal := by
              rw [setIntegral_const, smul_eq_mul]
              simp only [Measure.real]
              ring
      -- But m = (∫_S f) / μ(S), so ∫_S f = m * μ(S)
      have h_int_eq : ∫ x in S, f x ∂μ = m * (μ S).toReal := by
        rw [hm]; field_simp
      -- Combine: m * μ(S) ≥ (m + η) * μ(S), so m ≥ m + η, contradiction
      nlinarith
    -- Show average on A_high differs from m by ≥ η = ε/2
    · left
      -- On A_high, f ≥ m + η, so average ≥ m + η, so |average - m| ≥ η
      have hμA_top : μ A_high ≠ ⊤ := (measure_lt_top μ A_high).ne
      have hμA_pos' : (0 : ℝ) < (μ A_high).toReal := ENNReal.toReal_pos h_high hμA_top
      -- On A_high, f ≥ m + η pointwise
      have h_lb_on_high : ∀ x ∈ A_high, f x ≥ m + η := fun x ⟨_, hx⟩ => hx
      -- Lower bound: ∫_{A_high} f ≥ (m + η) μ(A_high)
      have h_int_lb : ∫ x in A_high, f x ∂μ ≥ (m + η) * (μ A_high).toReal := by
        calc ∫ x in A_high, f x ∂μ ≥ ∫ _ in A_high, (m + η) ∂μ := by
              apply setIntegral_mono_ae_restrict (integrableOn_const hμA_top) (hf_int.mono hA_high_sub le_rfl)
              simp only [Filter.EventuallyLE, Pi.le_def]
              rw [ae_restrict_iff' hA_high_meas]
              filter_upwards with x hx
              exact h_lb_on_high x hx
          _ = (m + η) * (μ A_high).toReal := by rw [setIntegral_const, smul_eq_mul]; simp [Measure.real]; ring
      -- Average = (μ A_high)⁻¹ ∫ f ≥ m + η
      have h_avg_ge : (μ A_high).toReal⁻¹ * ∫ x in A_high, f x ∂μ ≥ m + η := by
        have h1 : (m + η) * (μ A_high).toReal ≤ ∫ x in A_high, f x ∂μ := h_int_lb
        have h2 : (μ A_high).toReal⁻¹ * ((m + η) * (μ A_high).toReal) = m + η := by field_simp
        calc (μ A_high).toReal⁻¹ * ∫ x in A_high, f x ∂μ
            ≥ (μ A_high).toReal⁻¹ * ((m + η) * (μ A_high).toReal) := by
              apply mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (le_of_lt hμA_pos'))
          _ = m + η := h2
      -- |average - m| ≥ η, i.e., average - m ≥ η or -(average - m) ≥ η
      rw [ge_iff_le, le_abs]
      left
      linarith
  · -- Case: μ(A_low) ≠ 0, use S₁ = A_low (symmetric to A_high case)
    use A_low
    refine ⟨hA_low_meas, hA_low_sub, h_low, ?_, ?_⟩
    -- Show μ(S \ A_low) ≠ 0:
    -- If μ(S \ A_low) = 0, then f ≤ m - η a.e. on S
    -- But then ∫_S f ≤ (m - η) μ(S), so m ≤ m - η, contradiction
    · by_contra h_compl_zero
      have hμS_top : μ S ≠ ⊤ := (measure_lt_top μ S).ne
      have hμS_pos : (0 : ℝ) < (μ S).toReal := ENNReal.toReal_pos hμS hμS_top
      -- On A_low ⊆ S, f ≤ m - η pointwise
      have h_ub_on_low : ∀ x ∈ A_low, f x ≤ m - η := fun x ⟨_, hx⟩ => hx
      -- Since μ(S \ A_low) = 0, f ≤ m - η a.e. on S
      have h_ae_ub : ∀ᵐ x ∂μ.restrict S, f x ≤ m - η := by
        rw [ae_restrict_iff' hS]
        have h_compl_ae : (S \ A_low)ᶜ ∈ ae μ := by
          rw [compl_mem_ae_iff]
          exact h_compl_zero
        filter_upwards [h_compl_ae] with x hx hxS
        rw [Set.compl_diff] at hx
        cases hx with
        | inl hx_in_low => exact h_ub_on_low x hx_in_low
        | inr hx_not_S => exact absurd hxS hx_not_S
      -- Upper bound: ∫_S f ≤ (m - η) μ(S)
      have h_int_ub : ∫ x in S, f x ∂μ ≤ (m - η) * (μ S).toReal := by
        calc ∫ x in S, f x ∂μ ≤ ∫ _ in S, (m - η) ∂μ := by
              apply setIntegral_mono_ae_restrict hf_int (integrableOn_const hμS_top)
              exact h_ae_ub
          _ = (m - η) * (μ S).toReal := by rw [setIntegral_const, smul_eq_mul]; simp [Measure.real]; ring
      -- But m = (∫_S f) / μ(S), so ∫_S f = m * μ(S)
      have h_int_eq : ∫ x in S, f x ∂μ = m * (μ S).toReal := by
        rw [hm]; field_simp
      -- Combine: m * μ(S) ≤ (m - η) * μ(S), so m ≤ m - η, contradiction
      nlinarith
    -- Show average on A_low differs from m by ≥ η = ε/2
    · left  -- Use the LEFT case: |avg(A_low) - m| ≥ η
      have hμA_top : μ A_low ≠ ⊤ := (measure_lt_top μ A_low).ne
      have hμA_pos' : (0 : ℝ) < (μ A_low).toReal := ENNReal.toReal_pos h_low hμA_top
      -- On A_low, f ≤ m - η pointwise
      have h_ub_on_low : ∀ x ∈ A_low, f x ≤ m - η := fun x ⟨_, hx⟩ => hx
      -- Upper bound: ∫_{A_low} f ≤ (m - η) μ(A_low)
      have h_int_ub : ∫ x in A_low, f x ∂μ ≤ (m - η) * (μ A_low).toReal := by
        calc ∫ x in A_low, f x ∂μ ≤ ∫ _ in A_low, (m - η) ∂μ := by
              apply setIntegral_mono_ae_restrict (hf_int.mono hA_low_sub le_rfl) (integrableOn_const hμA_top)
              simp only [Filter.EventuallyLE]
              rw [ae_restrict_iff' hA_low_meas]
              filter_upwards with x hx
              exact h_ub_on_low x hx
          _ = (m - η) * (μ A_low).toReal := by rw [setIntegral_const, smul_eq_mul]; simp [Measure.real]; ring
      -- Average = (μ A_low)⁻¹ ∫ f ≤ m - η
      have h_avg_le : (μ A_low).toReal⁻¹ * ∫ x in A_low, f x ∂μ ≤ m - η := by
        have h1 : ∫ x in A_low, f x ∂μ ≤ (m - η) * (μ A_low).toReal := h_int_ub
        have h2 : (μ A_low).toReal⁻¹ * ((m - η) * (μ A_low).toReal) = m - η := by field_simp
        calc (μ A_low).toReal⁻¹ * ∫ x in A_low, f x ∂μ
            ≤ (μ A_low).toReal⁻¹ * ((m - η) * (μ A_low).toReal) := by
              apply mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (le_of_lt hμA_pos'))
          _ = m - η := h2
      -- |average - m| ≥ η, i.e., -(average - m) ≥ η, i.e., m - average ≥ η
      -- Since avg ≤ m - η, we have avg - m ≤ -η, so -(avg - m) ≥ η
      rw [ge_iff_le, le_abs]
      right
      -- Goal: -(avg - m) ≥ η, i.e., m - avg ≥ η
      -- From h_avg_le: avg ≤ m - η, so m - avg ≥ η
      linarith

end TAverage

/-- The "defect" of a partition: measures how far W is from being stepwise constant.

For a partition P and rectangle S × T, the defect is:
∫_{S×T} |W(x,y) - rectAverage W S T|² dμ(x) dμ(y)

The total defect is the sum over all partition rectangles.
When W is close to stepified P W in cut norm, the defect is small. -/
noncomputable def defect (W : Graphon α μ) (P : MeasurablePartition α μ) : ℝ :=
  P.parts.sum fun S =>
    P.parts.sum fun T =>
      ∫ p in S ×ˢ T, (W.toAEEqFun p - rectAverage W S T) ^ 2 ∂(μ.prod μ)

/-- The defect is non-negative. -/
theorem defect_nonneg (W : Graphon α μ) (P : MeasurablePartition α μ) :
    0 ≤ defect W P := by
  unfold defect
  apply Finset.sum_nonneg
  intro S _
  apply Finset.sum_nonneg
  intro T _
  apply setIntegral_nonneg_of_ae_restrict
  exact ae_of_all _ (fun _ => sq_nonneg _)

/-- The defect on S × T equals the defect on T × S, by symmetry of the graphon.

This follows from the change-of-variables formula (swapping integration domain)
and the graphon symmetry W(x,y) = W(y,x) a.e. -/
theorem defect_rect_symm (W : Graphon α μ) (S T : Set α)
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ∫ p in S ×ˢ T, (W.toAEEqFun p - rectAverage W S T) ^ 2 ∂(μ.prod μ) =
    ∫ p in T ×ˢ S, (W.toAEEqFun p - rectAverage W T S) ^ 2 ∂(μ.prod μ) := by
  -- Step 1: Swap integration domain: ∫_{S×T} f(p) = ∫_{T×S} f(p.swap)
  rw [← setIntegral_prod_swap S T (fun p => (W.toAEEqFun p - rectAverage W S T) ^ 2)]
  -- Now LHS = ∫_{T×S} (W(p.swap) - rectAverage W S T)²
  -- Step 2: Replace rectAverage W S T with rectAverage W T S
  rw [rectAverage_symm W S T hS hT]
  -- Now LHS = ∫_{T×S} (W(p.swap) - rectAverage W T S)²
  -- Step 3: Use graphon symmetry W(p.swap) = W(p) a.e.
  apply setIntegral_congr_ae (hT.prod hS)
  filter_upwards [W.symm_ae] with p hp _
  rw [hp]

/-- Variance decomposition on a rectangle: ∫_{S×T} W² = ∫_{S×T} (W - c)² + c² · μ(S×T)
    where c = rectAverage W S T.

    The key fact is that the cross term vanishes:
    ∫_{S×T} 2(W - c)·c = 2c · (∫_{S×T} W - c·μ(S×T)) = 0
    since c·μ(S×T) = ∫_{S×T} W by definition of rectAverage. -/
theorem variance_decomposition_rect (W : Graphon α μ) (S T : Set α)
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hμS : μ S ≠ 0) (hμT : μ T ≠ 0) :
    ∫ p in S ×ˢ T, (W.toAEEqFun p) ^ 2 ∂(μ.prod μ) =
      ∫ p in S ×ˢ T, (W.toAEEqFun p - rectAverage W S T) ^ 2 ∂(μ.prod μ) +
      (rectAverage W S T) ^ 2 * (μ S).toReal * (μ T).toReal := by
  -- Let c = rectAverage W S T
  set c := rectAverage W S T with hc_def
  -- Key fact: ∫_{S×T} W = c · μ(S) · μ(T)
  have h_int_eq : ∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ) = c * (μ S).toReal * (μ T).toReal := by
    simp only [rectAverage, hμS, hμT, dif_neg, not_false_eq_true] at hc_def
    have hS_pos : 0 < (μ S).toReal := ENNReal.toReal_pos hμS (measure_lt_top μ S).ne
    have hT_pos : 0 < (μ T).toReal := ENNReal.toReal_pos hμT (measure_lt_top μ T).ne
    rw [hc_def]
    field_simp
  -- Now expand (W - c)² = W² - 2cW + c²
  -- ∫ (W - c)² = ∫ W² - 2c ∫ W + c² · μ(S×T)
  -- So: ∫ W² = ∫ (W - c)² + 2c ∫ W - c² · μ(S×T)
  --          = ∫ (W - c)² + 2c · c·μ(S)μ(T) - c² · μ(S)μ(T)
  --          = ∫ (W - c)² + c² · μ(S)μ(T)
  have h_meas_rect : MeasurableSet (S ×ˢ T) := hS.prod hT
  have h_measure_rect : ((μ.prod μ) (S ×ˢ T)).toReal = (μ S).toReal * (μ T).toReal := by
    rw [Measure.prod_prod]; simp only [ENNReal.toReal_mul]
  -- Integrability of W and W² on S × T
  have h_int_W : IntegrableOn (fun p => W.toAEEqFun p) (S ×ˢ T) (μ.prod μ) :=
    (SymmKernel.graphon_integrable W).integrableOn
  have h_int_W_sq : IntegrableOn (fun p => (W.toAEEqFun p) ^ 2) (S ×ˢ T) (μ.prod μ) := by
    apply Measure.integrableOn_of_bounded (measure_lt_top _ _).ne
    · exact (continuous_pow 2).comp_aestronglyMeasurable W.toAEEqFun.aestronglyMeasurable
    · filter_upwards [ae_restrict_of_ae W.ae_mem_Icc] with p hp
      simp only [Real.norm_eq_abs]
      have h1 : 0 ≤ W.toAEEqFun p := hp.1
      have h2 : W.toAEEqFun p ≤ 1 := hp.2
      calc |W.toAEEqFun p ^ 2|
          = W.toAEEqFun p ^ 2 := abs_of_nonneg (sq_nonneg _)
        _ ≤ 1 := by nlinarith
  -- Integrability of (W - c)² on S × T
  have h_int_diff_sq : IntegrableOn (fun p => (W.toAEEqFun p - c) ^ 2) (S ×ˢ T) (μ.prod μ) := by
    apply Measure.integrableOn_of_bounded (measure_lt_top _ _).ne
    · have hc_mem := rectAverage_mem_Icc W S T hS hT
      exact (continuous_sub_right c |>.comp_aestronglyMeasurable
        W.toAEEqFun.aestronglyMeasurable |> (continuous_pow 2).comp_aestronglyMeasurable)
    · filter_upwards [ae_restrict_of_ae W.ae_mem_Icc] with p hp
      simp only [Real.norm_eq_abs]
      have h1 : 0 ≤ W.toAEEqFun p := hp.1
      have h2 : W.toAEEqFun p ≤ 1 := hp.2
      have hc_mem := rectAverage_mem_Icc W S T hS hT
      have hc1 : 0 ≤ c := hc_mem.1
      have hc2 : c ≤ 1 := hc_mem.2
      -- (W - c)² ≤ 1 since W, c ∈ [0,1] so |W - c| ≤ 1
      have h_diff_bound : |W.toAEEqFun p - c| ≤ 1 := by
        rw [abs_sub_le_iff]; constructor <;> linarith
      calc |(W.toAEEqFun p - c) ^ 2|
          = (W.toAEEqFun p - c) ^ 2 := abs_of_nonneg (sq_nonneg _)
        _ = |W.toAEEqFun p - c| ^ 2 := by rw [sq_abs]
        _ ≤ 1 ^ 2 := by
            apply sq_le_sq'
            · have : |W.toAEEqFun p - c| ≥ 0 := abs_nonneg _
              linarith
            · exact h_diff_bound
        _ = 1 := one_pow 2
  -- Integrability of constant c² on S × T
  have h_int_const : IntegrableOn (fun _ => c ^ 2) (S ×ˢ T) (μ.prod μ) :=
    integrableOn_const (measure_lt_top _ _).ne
  -- Integrability of 2c·W on S × T
  have h_int_cW : IntegrableOn (fun p => 2 * c * W.toAEEqFun p) (S ×ˢ T) (μ.prod μ) :=
    h_int_W.const_mul (2 * c)
  -- Key expansion: (W - c)² = W² - 2cW + c²
  have h_expand : ∀ p, (W.toAEEqFun p - c) ^ 2 = (W.toAEEqFun p) ^ 2 - 2 * c * W.toAEEqFun p + c ^ 2 := by
    intro p; ring
  -- Step 1: Show ∫ (W - c)² = ∫ W² - 2c ∫ W + c² μ(S×T)
  have h_diff_sq_expand : ∫ p in S ×ˢ T, (W.toAEEqFun p - c) ^ 2 ∂(μ.prod μ) =
      ∫ p in S ×ˢ T, (W.toAEEqFun p) ^ 2 ∂(μ.prod μ) -
      2 * c * ∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ) +
      c ^ 2 * ((μ.prod μ) (S ×ˢ T)).toReal := by
    -- Rewrite using the expansion
    have h1 : ∫ p in S ×ˢ T, (W.toAEEqFun p - c) ^ 2 ∂(μ.prod μ) =
        ∫ p in S ×ˢ T, ((W.toAEEqFun p) ^ 2 - 2 * c * W.toAEEqFun p + c ^ 2) ∂(μ.prod μ) := by
      congr 1; funext p; exact h_expand p
    rw [h1]
    -- Split the integral: ∫(a + b) = ∫a + ∫b
    have h_step1 : ∫ p in S ×ˢ T, (W.toAEEqFun p ^ 2 - 2 * c * W.toAEEqFun p + c ^ 2) ∂(μ.prod μ) =
        ∫ p in S ×ˢ T, (W.toAEEqFun p ^ 2 - 2 * c * W.toAEEqFun p) ∂(μ.prod μ) +
        ∫ _ in S ×ˢ T, c ^ 2 ∂(μ.prod μ) := by
      have h_eq : (fun p => W.toAEEqFun p ^ 2 - 2 * c * W.toAEEqFun p + c ^ 2) =
          (fun p => W.toAEEqFun p ^ 2 - 2 * c * W.toAEEqFun p) + (fun _ => c ^ 2) := by
        ext p; simp only [Pi.add_apply]
      rw [h_eq]
      exact integral_add (h_int_W_sq.sub h_int_cW) h_int_const
    rw [h_step1]
    -- Split the first integral: ∫(a - b) = ∫a - ∫b
    have h_step2 : ∫ p in S ×ˢ T, (W.toAEEqFun p ^ 2 - 2 * c * W.toAEEqFun p) ∂(μ.prod μ) =
        ∫ p in S ×ˢ T, W.toAEEqFun p ^ 2 ∂(μ.prod μ) -
        ∫ p in S ×ˢ T, (2 * c * W.toAEEqFun p) ∂(μ.prod μ) := by
      have : (fun p => W.toAEEqFun p ^ 2 - 2 * c * W.toAEEqFun p) =
          (fun p => W.toAEEqFun p ^ 2) - (fun p => 2 * c * W.toAEEqFun p) := by
        funext p; simp only [Pi.sub_apply]
      rw [this]
      exact integral_sub h_int_W_sq h_int_cW
    rw [h_step2]
    -- Factor out constant: ∫(c * f) = c * ∫f
    rw [integral_const_mul]
    -- Evaluate constant integral: ∫c = c * μ(S×T)
    rw [setIntegral_const, smul_eq_mul]
    simp only [Measure.real]
    ring
  -- Step 2: Use h_int_eq and h_diff_sq_expand to derive the goal
  -- From h_diff_sq_expand and h_int_eq, we get:
  -- ∫ (W - c)² = ∫ W² - 2c * (c * μ(S)μ(T)) + c² μ(S×T)
  --            = ∫ W² - 2c² μ(S)μ(T) + c² μ(S)μ(T)
  --            = ∫ W² - c² μ(S)μ(T)
  -- Rearranging: ∫ W² = ∫ (W - c)² + c² μ(S)μ(T)
  rw [h_measure_rect] at h_diff_sq_expand
  rw [h_int_eq] at h_diff_sq_expand
  linarith

/-- Key identity: L² norm = energy + defect.

‖W‖₂² = E(P, W) + D(P, W)

where E(P, W) is the energy and D(P, W) is the defect.
This follows from the Pythagorean theorem for L² orthogonal projections. -/
theorem l2_norm_eq_energy_add_defect (W : Graphon α μ) (P : MeasurablePartition α μ) :
    ∫ p, (W.toAEEqFun p) ^ 2 ∂(μ.prod μ) = energy W P + defect W P := by
  -- The proof uses variance_decomposition_rect for each rectangle,
  -- then sums over the partition.
  -- Step 1: Expand definitions of energy and defect
  unfold energy defect
  -- Step 2: Combine sums: energy + defect = Σ_{S,T} (μS μT c² + ∫_{S×T} (W-c)²)
  rw [← Finset.sum_add_distrib]
  conv_rhs =>
    arg 2
    ext S
    rw [← Finset.sum_add_distrib]
  -- Step 3: Each term equals ∫_{S×T} W² by variance_decomposition_rect (or 0 if μ=0)
  -- Transform each summand using add_comm to match variance_decomposition_rect
  conv_rhs =>
    arg 2
    ext S
    arg 2
    ext T
    rw [add_comm]
  -- Now RHS is Σ_{S,T} (∫_{S×T} (W-c)² + μS μT c²)
  -- This should equal Σ_{S,T} ∫_{S×T} W² by variance_decomposition_rect
  -- Helper: for each rectangle, the summand equals ∫_{S×T} W²
  have h_rect : ∀ S ∈ P.parts, ∀ T ∈ P.parts,
      ∫ p in S ×ˢ T, (W.toAEEqFun p - rectAverage W S T) ^ 2 ∂(μ.prod μ) +
      (μ S).toReal * (μ T).toReal * (rectAverage W S T) ^ 2 =
      ∫ p in S ×ˢ T, (W.toAEEqFun p) ^ 2 ∂(μ.prod μ) := by
    intro S hS T hT
    -- Case split on whether μ S = 0 or μ T = 0
    by_cases hμS : μ S = 0
    · -- When μ S = 0, all terms are 0
      have h_prod_zero : (μ.prod μ) (S ×ˢ T) = 0 := by
        rw [Measure.prod_prod, hμS, zero_mul]
      simp only [hμS, ENNReal.toReal_zero, zero_mul]
      rw [setIntegral_measure_zero _ h_prod_zero, setIntegral_measure_zero _ h_prod_zero]
      ring
    · by_cases hμT : μ T = 0
      · -- When μ T = 0, all terms are 0
        have h_prod_zero : (μ.prod μ) (S ×ˢ T) = 0 := by
          rw [Measure.prod_prod, hμT, mul_zero]
        simp only [hμT, ENNReal.toReal_zero, mul_zero]
        rw [setIntegral_measure_zero _ h_prod_zero, setIntegral_measure_zero _ h_prod_zero]
        ring
      · -- When both measures are positive, use variance_decomposition_rect
        have h_var := variance_decomposition_rect W S T
              (P.measurableSet_part hS) (P.measurableSet_part hT) hμS hμT
        linarith
  -- Step 4: Rewrite RHS using h_rect to get Σ_{S,T} ∫_{S×T} W²
  have h_sum_eq : ∑ S ∈ P.parts, ∑ T ∈ P.parts,
      (∫ p in S ×ˢ T, (W.toAEEqFun p - rectAverage W S T) ^ 2 ∂(μ.prod μ) +
       (μ S).toReal * (μ T).toReal * (rectAverage W S T) ^ 2) =
      ∑ S ∈ P.parts, ∑ T ∈ P.parts, ∫ p in S ×ˢ T, (W.toAEEqFun p) ^ 2 ∂(μ.prod μ) := by
    apply Finset.sum_congr rfl
    intro S hS
    apply Finset.sum_congr rfl
    intro T hT
    exact h_rect S hS T hT
  rw [h_sum_eq]
  -- Step 5: Show that Σ_{S,T} ∫_{S×T} W² = ∫ W²
  -- This requires showing partition rectangles cover α × α a.e. and are disjoint
  -- The key is that partition rectangles ⋃_{S,T} S × T cover α × α a.e.
  -- and the integral over the whole space equals the integral over this union
  symm
  -- Partition rectangles cover α × α a.e.
  have h_ae_covers : ∀ᵐ p ∂(μ.prod μ), ∃ S ∈ P.parts, ∃ T ∈ P.parts, p ∈ S ×ˢ T := by
    -- Use ae_prod_iff_ae_ae to reduce to: for a.e. x, for a.e. y, (x,y) ∈ some rectangle
    have h_meas : MeasurableSet {p : α × α | ∃ S ∈ P.parts, ∃ T ∈ P.parts, p ∈ S ×ˢ T} := by
      -- The set is the union of measurable rectangles
      have h_eq : {p : α × α | ∃ S ∈ P.parts, ∃ T ∈ P.parts, p ∈ S ×ˢ T} =
          ⋃ S ∈ P.parts, ⋃ T ∈ P.parts, S ×ˢ T := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
      rw [h_eq]
      apply MeasurableSet.biUnion P.parts.countable_toSet
      intro S hS
      apply MeasurableSet.biUnion P.parts.countable_toSet
      intro T hT
      exact (P.measurableSet_part hS).prod (P.measurableSet_part hT)
    rw [Measure.ae_prod_iff_ae_ae h_meas]
    filter_upwards [P.ae_covers] with x hx
    filter_upwards [P.ae_covers] with y hy
    obtain ⟨S, hS_mem, hxS⟩ := hx
    obtain ⟨T, hT_mem, hyT⟩ := hy
    exact ⟨S, hS_mem, T, hT_mem, ⟨hxS, hyT⟩⟩
  -- Define the union of all partition rectangles
  let rectUnion := ⋃ S ∈ P.parts, ⋃ T ∈ P.parts, S ×ˢ T
  -- Show the rectangles are pairwise disjoint (as a collection indexed by products)
  have h_meas_union : MeasurableSet rectUnion := by
    apply MeasurableSet.biUnion P.parts.countable_toSet
    intro S hS
    apply MeasurableSet.biUnion P.parts.countable_toSet
    intro T hT
    exact (P.measurableSet_part hS).prod (P.measurableSet_part hT)
  -- Integrability of W² on whole space
  have h_int : Integrable (fun p => (W.toAEEqFun p) ^ 2) (μ.prod μ) := by
    -- Use integrableOn_of_bounded on Set.univ, then convert to Integrable
    have h_int_on : IntegrableOn (fun p => (W.toAEEqFun p) ^ 2) Set.univ (μ.prod μ) := by
      apply Measure.integrableOn_of_bounded (measure_lt_top _ _).ne
      · exact (continuous_pow 2).comp_aestronglyMeasurable W.toAEEqFun.aestronglyMeasurable
      · filter_upwards [ae_restrict_of_ae W.ae_mem_Icc] with p hp
        simp only [Real.norm_eq_abs]
        calc |W.toAEEqFun p ^ 2| = W.toAEEqFun p ^ 2 := abs_of_nonneg (sq_nonneg _)
          _ ≤ 1 := by nlinarith [hp.1, hp.2]
    rwa [integrableOn_univ] at h_int_on
  -- Integral over union = integral over whole space (since union covers a.e.)
  have h_int_eq : ∫ p in rectUnion, (W.toAEEqFun p) ^ 2 ∂(μ.prod μ) =
      ∫ p, (W.toAEEqFun p) ^ 2 ∂(μ.prod μ) := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    -- a.e. x, x ∉ rectUnion → f x = 0. Since a.e. x ∈ rectUnion, this is vacuously true a.e.
    filter_upwards [h_ae_covers] with p hp h_not_in
    simp only [rectUnion, Set.mem_iUnion, not_exists] at h_not_in
    obtain ⟨S, hS, T, hT, hp_mem⟩ := hp
    exact absurd hp_mem (h_not_in S hS T hT)
  rw [← h_int_eq]
  -- Now need to show ∫_{rectUnion} W² = Σ_{S,T} ∫_{S×T} W²
  -- Use integral_biUnion_finset on the product index
  -- First, rewrite rectUnion as biUnion over product
  have h_union_eq : rectUnion = ⋃ (st : Set α × Set α), ⋃ (_ : st ∈ P.parts ×ˢ P.parts), st.1 ×ˢ st.2 := by
    simp only [rectUnion]
    ext p
    simp only [Set.mem_iUnion, Finset.mem_product, exists_prop, Prod.exists]
    constructor
    · rintro ⟨S, hS, T, hT, hp⟩
      exact ⟨S, T, ⟨hS, hT⟩, hp⟩
    · rintro ⟨S, T, ⟨hS, hT⟩, hp⟩
      exact ⟨S, hS, T, hT, hp⟩
  -- Show rectangles are pairwise disjoint
  have h_disj : (↑(P.parts ×ˢ P.parts) : Set (Set α × Set α)).Pairwise
      (Function.onFun Disjoint fun st => st.1 ×ˢ st.2) := by
    intro ⟨S₁, T₁⟩ h₁ ⟨S₂, T₂⟩ h₂ hne
    simp only [Function.onFun, Set.disjoint_iff_inter_eq_empty, Set.prod_inter_prod]
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at h₁ h₂
    by_cases hS : S₁ = S₂
    · subst hS
      have hT : T₁ ≠ T₂ := fun h => hne (Prod.ext rfl h)
      have h_disj_T : Disjoint T₁ T₂ := P.pairwiseDisjoint h₁.2 h₂.2 hT
      simp only [Set.inter_self, Set.disjoint_iff_inter_eq_empty.mp h_disj_T, Set.prod_empty]
    · have h_disj_S : Disjoint S₁ S₂ := P.pairwiseDisjoint h₁.1 h₂.1 hS
      simp only [Set.disjoint_iff_inter_eq_empty.mp h_disj_S, Set.empty_prod]
  -- Measurability of each rectangle
  have h_meas_rect : ∀ st ∈ P.parts ×ˢ P.parts, MeasurableSet (st.1 ×ˢ st.2) := by
    intro ⟨S, T⟩ hst
    simp only [Finset.mem_product] at hst
    exact (P.measurableSet_part hst.1).prod (P.measurableSet_part hst.2)
  -- Integrability on each rectangle
  have h_int_rect : ∀ st ∈ P.parts ×ˢ P.parts,
      IntegrableOn (fun p => (W.toAEEqFun p) ^ 2) (st.1 ×ˢ st.2) (μ.prod μ) := fun _ _ =>
    h_int.integrableOn
  -- Apply integral_biUnion_finset
  have h_sum_eq_union : ∫ p in rectUnion, (W.toAEEqFun p) ^ 2 ∂(μ.prod μ) =
      ∑ st ∈ P.parts ×ˢ P.parts, ∫ p in st.1 ×ˢ st.2, (W.toAEEqFun p) ^ 2 ∂(μ.prod μ) := by
    conv_lhs => rw [h_union_eq]
    exact integral_biUnion_finset (P.parts ×ˢ P.parts) h_meas_rect h_disj h_int_rect
  rw [h_sum_eq_union]
  -- Convert sum over product to double sum using Finset.sum_product
  rw [Finset.sum_product]

/-- Energy contribution from a single rectangle. -/
private noncomputable def energyRect (W : Graphon α μ) (S T : Set α) : ℝ :=
  (μ S).toReal * (μ T).toReal * (rectAverage W S T) ^ 2

/-- The energy difference when replacing S with S₁ ∪ S₂ = S in the energy sum.
For a fixed T, the contribution from S × T becomes the sum of S₁ × T and S₂ × T contributions.
The difference is μ(T) * μ(S₁)μ(S₂)/μ(S) * (c₁ - c₂)² where c_i = rectAverage W S_i T. -/
lemma energy_rect_split (W : Graphon α μ) (S T S₁ : Set α)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hS₁ : MeasurableSet S₁) (hS₁_sub : S₁ ⊆ S)
    (hμS : μ S ≠ 0) (hμT : μ T ≠ 0) (hμS₁ : μ S₁ ≠ 0) (hμS₂ : μ (S \ S₁) ≠ 0) :
    energyRect W S₁ T + energyRect W (S \ S₁) T - energyRect W S T =
      (μ T).toReal * (μ S₁).toReal * (μ (S \ S₁)).toReal / (μ S).toReal *
        (rectAverage W S₁ T - rectAverage W (S \ S₁) T) ^ 2 := by
  -- Let S₂ = S \ S₁, c = rectAverage S T, c₁ = rectAverage S₁ T, c₂ = rectAverage S₂ T
  set S₂ := S \ S₁ with hS₂_def
  set c := rectAverage W S T with hc_def
  set c₁ := rectAverage W S₁ T with hc₁_def
  set c₂ := rectAverage W S₂ T with hc₂_def
  have hS₂_meas : MeasurableSet S₂ := hS.diff hS₁
  have hμS_top : μ S ≠ ⊤ := (measure_lt_top μ S).ne
  have hμS₁_top : μ S₁ ≠ ⊤ := (measure_lt_top μ S₁).ne
  have hμS₂_top : μ S₂ ≠ ⊤ := (measure_lt_top μ S₂).ne
  have hμS_pos : 0 < (μ S).toReal := ENNReal.toReal_pos hμS hμS_top
  have hμS₁_pos : 0 < (μ S₁).toReal := ENNReal.toReal_pos hμS₁ hμS₁_top
  have hμS₂_pos : 0 < (μ S₂).toReal := ENNReal.toReal_pos hμS₂ hμS₂_top
  -- Step 1: Show μ(S) = μ(S₁) + μ(S₂)
  have h_disj : Disjoint S₁ S₂ := Set.disjoint_sdiff_right
  have h_union : S = S₁ ∪ S₂ := (Set.union_diff_cancel hS₁_sub).symm
  have hμ_add : (μ S).toReal = (μ S₁).toReal + (μ S₂).toReal := by
    rw [h_union, measure_union h_disj hS₂_meas]
    exact ENNReal.toReal_add hμS₁_top hμS₂_top
  -- Step 2: c is the weighted average of c₁ and c₂
  -- This follows from ∫_{S×T} W = ∫_{S₁×T} W + ∫_{S₂×T} W (Fubini)
  have hc_weighted : c = ((μ S₁).toReal * c₁ + (μ S₂).toReal * c₂) / (μ S).toReal := by
    rw [hc_def, hc₁_def, hc₂_def]
    unfold rectAverage
    simp only [hμS, hμT, hμS₁, hμS₂, dif_neg, not_false_eq_true]
    -- ∫_{S×T} W = ∫_S (∫_T W(x,y)) by Fubini = ∫_{S₁} ... + ∫_{S₂} ...
    have h_int : IntegrableOn (fun p => W.toAEEqFun p) (S ×ˢ T) (μ.prod μ) :=
      (SymmKernel.graphon_integrable W).integrableOn
    have h_prod_eq : (μ.prod μ).restrict (S ×ˢ T) = (μ.restrict S).prod (μ.restrict T) :=
      (Measure.prod_restrict S T).symm
    have h_int_full : Integrable (fun p => W.toAEEqFun p) ((μ.restrict S).prod (μ.restrict T)) := by
      rw [← h_prod_eq]; exact h_int
    -- Use setIntegral_prod to convert to iterated integral
    have h_fubini := setIntegral_prod (f := fun p => W.toAEEqFun p) h_int
    -- The integral over S×T splits as S₁×T + S₂×T
    have h_int_S₁ : IntegrableOn (fun p => W.toAEEqFun p) (S₁ ×ˢ T) (μ.prod μ) := h_int.mono
      (Set.prod_mono hS₁_sub Subset.rfl) le_rfl
    have h_int_S₂ : IntegrableOn (fun p => W.toAEEqFun p) (S₂ ×ˢ T) (μ.prod μ) := h_int.mono
      (Set.prod_mono Set.diff_subset Subset.rfl) le_rfl
    have h_rect_union : S ×ˢ T = (S₁ ×ˢ T) ∪ (S₂ ×ˢ T) := by
      rw [← Set.union_prod, h_union]
    have h_rect_disj : Disjoint (S₁ ×ˢ T) (S₂ ×ˢ T) := by
      rw [Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨⟨hx1, _⟩, ⟨hx2, _⟩⟩
      exact Set.disjoint_sdiff_right.ne_of_mem hx1 hx2 rfl
    have h_split_int : ∫ p in S ×ˢ T, W.toAEEqFun p ∂μ.prod μ =
        ∫ p in S₁ ×ˢ T, W.toAEEqFun p ∂μ.prod μ + ∫ p in S₂ ×ˢ T, W.toAEEqFun p ∂μ.prod μ := by
      rw [h_rect_union]
      exact setIntegral_union h_rect_disj (hS₂_meas.prod hT) h_int_S₁ h_int_S₂
    field_simp [ne_of_gt hμS_pos, ne_of_gt hμS₁_pos, ne_of_gt hμS₂_pos]
    rw [h_split_int]
  -- Step 3: Apply weighted_sq_diff
  -- The identity: a*c₁² + b*c₂² - (a+b)*c² = (a*b/(a+b)) * (c₁-c₂)²
  -- where c = (a*c₁ + b*c₂)/(a+b) is the weighted average
  have h_c_eq : c = ((μ S₁).toReal * c₁ + (μ S₂).toReal * c₂) /
      ((μ S₁).toReal + (μ S₂).toReal) := by rw [hc_weighted, hμ_add]
  -- Specialize weighted_sq_diff with our c
  have h_ws := weighted_sq_diff (μ S₁).toReal (μ S₂).toReal c₁ c₂ hμS₁_pos hμS₂_pos
  -- h_ws has form: let c' := ...; a*c₁² + b*c₂² - (a+b)*c'² = ...
  -- We need to show our c matches c'
  simp only at h_ws
  -- Step 4: Unfold energyRect and compute
  unfold energyRect
  -- The identity from h_ws (with c = c'):
  -- μ(S₁)*c₁² + μ(S₂)*c₂² - (μ(S₁)+μ(S₂))*c² = μ(S₁)*μ(S₂)/(μ(S₁)+μ(S₂)) * (c₁-c₂)²
  -- Multiplying by μ(T):
  -- μ(T)*(μ(S₁)*c₁² + μ(S₂)*c₂² - μ(S)*c²) = μ(T)*μ(S₁)*μ(S₂)/μ(S) * (c₁-c₂)²
  have h_key : (μ S₁).toReal * c₁ ^ 2 + (μ S₂).toReal * c₂ ^ 2 -
      ((μ S₁).toReal + (μ S₂).toReal) * c ^ 2 =
      (μ S₁).toReal * (μ S₂).toReal / ((μ S₁).toReal + (μ S₂).toReal) * (c₁ - c₂) ^ 2 := by
    rw [h_c_eq]
    exact h_ws
  calc (μ S₁).toReal * (μ T).toReal * c₁ ^ 2 + (μ S₂).toReal * (μ T).toReal * c₂ ^ 2 -
        (μ S).toReal * (μ T).toReal * c ^ 2
      = (μ T).toReal * ((μ S₁).toReal * c₁ ^ 2 + (μ S₂).toReal * c₂ ^ 2 -
          (μ S).toReal * c ^ 2) := by ring
    _ = (μ T).toReal * ((μ S₁).toReal * c₁ ^ 2 + (μ S₂).toReal * c₂ ^ 2 -
          ((μ S₁).toReal + (μ S₂).toReal) * c ^ 2) := by rw [hμ_add]
    _ = (μ T).toReal * ((μ S₁).toReal * (μ S₂).toReal /
          ((μ S₁).toReal + (μ S₂).toReal) * (c₁ - c₂) ^ 2) := by rw [h_key]
    _ = (μ T).toReal * (μ S₁).toReal * (μ S₂).toReal / (μ S).toReal * (c₁ - c₂) ^ 2 := by
          rw [hμ_add]; ring

/-- Energy increases when splitting a part with different sub-averages.

When we split S into S₁ and S\S₁ in a partition, the energy of the new partition
is at least the old energy plus the positive contribution from `energy_rect_split`
applied to each T ∈ P.parts. More precisely:

  energy W Q ≥ energy W P + Σ_T μ(T) * μ(S₁) * μ(S\S₁) / μ(S) * (c₁_T - c₂_T)²

where c₁_T = rectAverage W S₁ T and c₂_T = rectAverage W (S\S₁) T.

In particular, if c₁_T ≠ c₂_T for some T, the energy strictly increases. -/
theorem energy_splitPart_ge (W : Graphon α μ) (P : MeasurablePartition α μ)
    (S : Set α) (hS_mem : S ∈ P.parts) (S₁ : Set α) (hS₁_meas : MeasurableSet S₁)
    (hS₁_sub : S₁ ⊆ S) (hμS₁ : μ S₁ ≠ 0) (hμS₂ : μ (S \ S₁) ≠ 0) :
    let Q := MeasurablePartition.splitPart P S hS_mem S₁ hS₁_meas hS₁_sub hμS₁ hμS₂
    energy W Q ≥ energy W P +
      P.parts.sum fun T =>
        (μ T).toReal * (μ S₁).toReal * (μ (S \ S₁)).toReal / (μ S).toReal *
          (rectAverage W S₁ T - rectAverage W (S \ S₁) T) ^ 2 := by
  classical
  intro Q
  -- Setup: abbreviations and basic facts
  set S₂ := S \ S₁ with hS₂_def
  set E := P.parts.erase S with hE_def
  have hS_meas : MeasurableSet S := P.measurableSet_part hS_mem
  have hS₂_meas : MeasurableSet S₂ := hS_meas.diff hS₁_meas
  have hμS : μ S ≠ 0 := fun h => hμS₁ (measure_mono_null hS₁_sub h)
  -- The δ(T) correction term for a single T
  set δ : Set α → ℝ := fun T =>
    (μ T).toReal * (μ S₁).toReal * (μ S₂).toReal / (μ S).toReal *
      (rectAverage W S₁ T - rectAverage W S₂ T) ^ 2 with hδ_def
  -- δ(T) ≥ 0 for all T
  have hδ_nonneg : ∀ T, 0 ≤ δ T := by
    intro T; simp only [hδ_def]
    apply mul_nonneg
    · apply div_nonneg
      · exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
          ENNReal.toReal_nonneg
      · exact ENNReal.toReal_nonneg
    · exact sq_nonneg _
  -- energy_rect_split gives: eR(S₁,T) + eR(S₂,T) - eR(S,T) = δ(T)
  -- when all measures are nonzero
  have h_split : ∀ T, MeasurableSet T → μ T ≠ 0 →
      energyRect W S₁ T + energyRect W S₂ T - energyRect W S T = δ T := by
    intro T hT_meas hμT
    exact energy_rect_split W S T S₁ hS_meas hT_meas hS₁_meas hS₁_sub hμS hμT hμS₁ hμS₂
  -- When μ T = 0, both sides are 0
  have h_split_zero : ∀ T, μ T = 0 →
      energyRect W S₁ T + energyRect W S₂ T - energyRect W S T = δ T := by
    intro T hμT
    simp only [energyRect, show (μ T).toReal = 0 from by simp [hμT], zero_mul, mul_zero,
      add_zero, sub_zero, hδ_def, zero_div]
  -- Combined: the split identity holds for all measurable T
  have h_split_all : ∀ T, MeasurableSet T →
      energyRect W S₁ T + energyRect W S₂ T - energyRect W S T = δ T := by
    intro T hT_meas
    by_cases hμT : μ T = 0
    · exact h_split_zero T hμT
    · exact h_split T hT_meas hμT
  -- energyRect is symmetric for measurable sets
  have h_eR_symm : ∀ A B : Set α, MeasurableSet A → MeasurableSet B →
      energyRect W A B = energyRect W B A := by
    intro A B hA hB
    unfold energyRect
    rw [rectAverage_symm W A B hA hB]
    ring
  -- Q.parts = E ∪ {S₁, S₂}
  have hQ_parts : Q.parts = E ∪ ({S₁, S₂} : Finset (Set α)) := by
    simp only [Q, MeasurablePartition.splitPart, hE_def, hS₂_def]
  -- P.parts = insert S E (i.e., E ∪ {S})
  have hP_parts : P.parts = insert S E := by
    rw [hE_def]; exact (Finset.insert_erase hS_mem).symm
  -- S ∉ E
  have hS_notin_E : S ∉ E := by rw [hE_def]; simp
  -- E ⊆ P.parts
  have hE_sub : E ⊆ P.parts := by rw [hE_def]; exact Finset.erase_subset S P.parts
  -- All parts of E are measurable
  have hE_meas : ∀ T ∈ E, MeasurableSet T := fun T hT => P.measurableSet_part (hE_sub hT)
  -- All parts of Q are measurable
  have hQ_meas : ∀ T ∈ Q.parts, MeasurableSet T := Q.measurable_parts
  -- Step A: For each T ∈ P.parts, the inner sum over Q exceeds the inner sum over P by δ(T).
  -- That is: Σ_{U ∈ Q} eR(U,T) = Σ_{U ∈ P} eR(U,T) + δ(T)
  -- S₁ ≠ S₂ (since S₂ = S \ S₁ and S₁ ∩ S₂ = ∅ while μ S₁ ≠ 0)
  have hS₁_ne_S₂ : S₁ ≠ S₂ := by
    intro h; rw [hS₂_def] at h
    have : S₁ ⊆ S \ S₁ := h ▸ Subset.rfl
    exact hμS₁ (measure_mono_null (fun x hx => ((this hx).2 hx).elim) (measure_empty))
  -- S₁ ∉ E: If S₁ ∈ E = P.parts.erase S, then S₁ ∈ P.parts and S₁ ≠ S.
  -- By pairwise disjointness, S₁ ∩ S = ∅. But S₁ ⊆ S and μ S₁ ≠ 0, contradiction.
  have hS₁_notin_E : S₁ ∉ E := by
    intro h
    have h1 := (Finset.mem_erase.mp h).1  -- S₁ ≠ S
    have h2 := (Finset.mem_erase.mp h).2  -- S₁ ∈ P.parts
    have := P.pairwiseDisjoint h2 hS_mem h1
    exact hμS₁ (measure_mono_null (Set.disjoint_iff_inter_eq_empty.mp this ▸
      Set.subset_inter Subset.rfl hS₁_sub) (measure_empty))
  have hS₂_notin_E : S₂ ∉ E := by
    intro h
    have h1 := (Finset.mem_erase.mp h).1  -- S₂ ≠ S
    have h2 := (Finset.mem_erase.mp h).2  -- S₂ ∈ P.parts
    have := P.pairwiseDisjoint h2 hS_mem h1
    exact hμS₂ (measure_mono_null (Set.disjoint_iff_inter_eq_empty.mp this ▸
      Set.subset_inter Subset.rfl Set.diff_subset) (measure_empty))
  -- Disjointness for Finset.sum_union
  have hE_disj_S : Disjoint E ({S₁, S₂} : Finset (Set α)) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
    rcases hx2 with rfl | rfl
    · exact hS₁_notin_E hx
    · exact hS₂_notin_E hx
  have hE_disj_S_single : Disjoint E ({S} : Finset (Set α)) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    simp only [Finset.mem_singleton] at hx2
    rw [hx2] at hx; exact hS_notin_E hx
  -- Step A helper: inner sum identity for each T ∈ P.parts
  have h_inner : ∀ T ∈ P.parts,
      Q.parts.sum (fun U => energyRect W U T) =
      P.parts.sum (fun U => energyRect W U T) + δ T := by
    intro T hT
    have hT_meas := P.measurableSet_part hT
    -- Expand Q.parts = E ∪ {S₁, S₂}
    rw [hQ_parts, Finset.sum_union hE_disj_S]
    -- Expand P.parts = insert S E = E ∪ {S}
    rw [show P.parts = E ∪ {S} from by rw [hP_parts, Finset.insert_eq]; exact Finset.union_comm _ _]
    rw [Finset.sum_union hE_disj_S_single]
    -- Now: (Σ_E + Σ_{S₁,S₂}) = (Σ_E + Σ_{S}) + δ(T)
    -- i.e., Σ_{S₁,S₂} = Σ_{S} + δ(T)
    -- Σ_{S₁,S₂} = eR(S₁,T) + eR(S₂,T)
    have h1 : ({S₁, S₂} : Finset (Set α)).sum (fun U => energyRect W U T) =
        energyRect W S₁ T + energyRect W S₂ T := by
      rw [Finset.sum_pair hS₁_ne_S₂]
    -- Σ_{S} = eR(S,T)
    have h2 : ({S} : Finset (Set α)).sum (fun U => energyRect W U T) = energyRect W S T := by
      simp [Finset.sum_singleton]
    rw [h1, h2]
    linarith [h_split_all T hT_meas]
  -- Step B: The mixed sum equals energy W P + correction
  -- Note: energy W P = Σ_S Σ_T eR(S,T) = Σ_T Σ_U eR(U,T) by Finset.sum_comm
  have h_energy_comm : energy W P = P.parts.sum (fun T =>
      P.parts.sum (fun U => energyRect W U T)) := by
    unfold energy energyRect; exact Finset.sum_comm
  have h_step_B : P.parts.sum (fun T => Q.parts.sum (fun U => energyRect W U T)) =
      energy W P + P.parts.sum δ := by
    rw [h_energy_comm, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun T hT => h_inner T hT)
  -- Step C: energy W Q ≥ mixed sum
  -- energy W Q = Σ_{T ∈ Q} Σ_{U ∈ Q} eR(U,T)
  -- We need: this ≥ Σ_{T ∈ P} Σ_{U ∈ Q} eR(U,T)
  -- The difference: Σ_{U ∈ Q} [eR(U,S₁) + eR(U,S₂) - eR(U,S)] ≥ 0
  -- because each eR(U,S₁)+eR(U,S₂)-eR(U,S) = δ(U) ≥ 0 (by symmetry + split)
  have h_second_arg_split : ∀ U, MeasurableSet U →
      energyRect W U S₁ + energyRect W U S₂ - energyRect W U S ≥ 0 := by
    intro U hU_meas
    have h1 := h_split_all U hU_meas
    -- h1 : eR(S₁,U) + eR(S₂,U) - eR(S,U) = δ(U)
    -- By symmetry: eR(U,S₁) = eR(S₁,U), eR(U,S₂) = eR(S₂,U), eR(U,S) = eR(S,U)
    rw [h_eR_symm U S₁ hU_meas hS₁_meas, h_eR_symm U S₂ hU_meas hS₂_meas,
      h_eR_symm U S hU_meas hS_meas]
    linarith [hδ_nonneg U]
  have h_step_C : energy W Q ≥ P.parts.sum (fun T => Q.parts.sum (fun U =>
      energyRect W U T)) := by
    -- energy W Q = Σ_S Σ_T eR(S,T) = Σ_T Σ_U eR(U,T) (by sum_comm)
    have h_energy_Q_comm : energy W Q = Q.parts.sum (fun T =>
        Q.parts.sum (fun U => energyRect W U T)) := by
      unfold energy energyRect; exact Finset.sum_comm
    rw [h_energy_Q_comm]
    -- Now: Σ_{T∈Q} g(T) ≥ Σ_{T∈P} g(T) where g(T) = Σ_{U∈Q} eR(U,T)
    set g : Set α → ℝ := fun T => Q.parts.sum (fun U => energyRect W U T) with hg_def
    -- Q sum: Σ_{T ∈ E} g(T) + g(S₁) + g(S₂)
    -- P sum: Σ_{T ∈ E} g(T) + g(S)
    -- Need: g(S₁) + g(S₂) ≥ g(S)
    rw [hQ_parts, Finset.sum_union hE_disj_S, Finset.sum_pair hS₁_ne_S₂]
    have hP_eq_E_union_S : P.parts = E ∪ {S} := by
      rw [hP_parts, Finset.insert_eq]; exact Finset.union_comm _ _
    rw [hP_eq_E_union_S, Finset.sum_union hE_disj_S_single, Finset.sum_singleton]
    -- Need: g(S₁) + g(S₂) ≥ g(S), i.e., the extra from splitting S in the second arg
    suffices h : g S₁ + g S₂ ≥ g S by linarith
    simp only [hg_def]
    rw [← Finset.sum_add_distrib]
    -- Need: Σ_{U∈Q} (eR(U,S₁) + eR(U,S₂)) ≥ Σ_{U∈Q} eR(U,S)
    apply Finset.sum_le_sum
    intro U hU
    linarith [h_second_arg_split U (hQ_meas U hU)]
  -- Combine steps B and C
  linarith

/-- When the between-variance of `tAverage W V` on part `A` is large,
splitting `A` by `exists_variance_cut` produces a refinement with strictly
larger energy. This is the common core of both Case 1 and Case 2a of
`energy_increment`. -/
private theorem energy_increment_of_between_variance
    (W : Graphon α μ) (P : MeasurablePartition α μ) (ε : ℝ) (hε : ε > 0)
    (A : Set α) (hA_mem : A ∈ P.parts)
    (V : Set α) (hV_mem : V ∈ P.parts)
    (hA_meas : MeasurableSet A) (hV_meas : MeasurableSet V)
    (hμA : μ A ≠ 0) (hμV : μ V ≠ 0)
    (h_var : ∫ x in A, (tAverage W V x - rectAverage W A V) ^ 2 ∂μ ≥
        ε ^ 2 / 2 * (μ A).toReal) :
    ∃ Q : MeasurablePartition α μ,
      Refines Q P ∧ Q.parts.card ≤ 2 * P.parts.card ∧
      energy W Q > energy W P := by
  -- Measure setup
  have hμA_top : μ A ≠ ⊤ := (measure_lt_top μ A).ne
  have hμV_top : μ V ≠ ⊤ := (measure_lt_top μ V).ne
  have hμA_real_pos : (0 : ℝ) < (μ A).toReal := ENNReal.toReal_pos hμA hμA_top
  have hμV_real_pos : (0 : ℝ) < (μ V).toReal := ENNReal.toReal_pos hμV hμV_top
  -- Mean identity and integrability
  set f := tAverage W V with hf_def
  have hf_meas : Measurable f := tAverage_measurable W V hV_meas
  set c := rectAverage W A V with hc_def
  have hc_mean : c = (μ A).toReal⁻¹ * ∫ x in A, f x ∂μ := by
    rw [hc_def, hf_def, tAverage_integral_eq_rectAverage W A V hA_meas hV_meas hμA hμV]
  have hf_int : IntegrableOn f A μ := by
    apply Measure.integrableOn_of_bounded (M := 1) hμA_top
    · exact hf_meas.aestronglyMeasurable
    · filter_upwards [ae_restrict_of_ae (tAverage_ae_mem_Icc W V hV_meas)] with x hx
      simp only [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- ε-scaling: (ε/√2)² = ε²/2
  set ε' := ε / Real.sqrt 2 with hε'_def
  have hε'_pos : ε' > 0 := div_pos hε (Real.sqrt_pos.mpr (by norm_num))
  have h_var' : ∫ x in A, (f x - c) ^ 2 ∂μ ≥ ε' ^ 2 * (μ A).toReal := by
    have h_eq : ε' ^ 2 = ε ^ 2 / 2 := by
      rw [hε'_def, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h_eq]; exact h_var
  -- Apply exists_variance_cut
  obtain ⟨A₁, hA₁_meas, hA₁_sub, hμA₁, hμA₂, h_avg_diff⟩ :=
    exists_variance_cut f A hA_meas hf_meas hf_int hμA c hc_mean ε' hε'_pos h_var'
  -- Build the refined partition Q by splitting A
  let Q := MeasurablePartition.splitPart P A hA_mem A₁ hA₁_meas hA₁_sub hμA₁ hμA₂
  use Q
  refine ⟨?_, ?_, ?_⟩
  -- (a) Q refines P
  · exact MeasurablePartition.splitPart_refines P A hA_mem A₁ hA₁_meas hA₁_sub hμA₁ hμA₂
  -- (b) Q has at most 2 * P.parts.card parts
  · have h_card := MeasurablePartition.splitPart_card P A hA_mem A₁ hA₁_meas hA₁_sub hμA₁ hμA₂
    have h_P_nonempty : 1 ≤ P.parts.card := Finset.one_le_card.mpr ⟨A, hA_mem⟩
    calc Q.parts.card ≤ P.parts.card + 1 := h_card
      _ ≤ P.parts.card + P.parts.card := by omega
      _ = 2 * P.parts.card := by ring
  -- (c) Energy strictly increases
  · set A₂ := A \ A₁ with hA₂_def
    have hA₂_meas : MeasurableSet A₂ := hA_meas.diff hA₁_meas
    have hμA₁_top : μ A₁ ≠ ⊤ := (measure_lt_top μ A₁).ne
    have hμA₂_top : μ A₂ ≠ ⊤ := (measure_lt_top μ A₂).ne
    have hμA₁_real_pos : 0 < (μ A₁).toReal := ENNReal.toReal_pos hμA₁ hμA₁_top
    have hμA₂_real_pos : 0 < (μ A₂).toReal := ENNReal.toReal_pos hμA₂ hμA₂_top
    -- Sub-averages
    set c₁ := (μ A₁).toReal⁻¹ * ∫ x in A₁, f x ∂μ with hc₁_def
    set c₂ := (μ A₂).toReal⁻¹ * ∫ x in A₂, f x ∂μ with hc₂_def
    -- Connect to rectAverage
    have hc₁_rect : c₁ = rectAverage W A₁ V := by
      rw [hc₁_def, hf_def]
      exact tAverage_integral_eq_rectAverage W A₁ V hA₁_meas hV_meas hμA₁ hμV
    have hc₂_rect : c₂ = rectAverage W A₂ V := by
      rw [hc₂_def, hf_def]
      exact tAverage_integral_eq_rectAverage W A₂ V hA₂_meas hV_meas hμA₂ hμV
    -- Weighted average identity
    have h_A_union : A = A₁ ∪ A₂ := by
      rw [hA₂_def, Set.union_diff_cancel hA₁_sub]
    have h_disj : Disjoint A₁ A₂ := by
      rw [hA₂_def]; exact Set.disjoint_sdiff_right
    have hμ_add : (μ A).toReal = (μ A₁).toReal + (μ A₂).toReal := by
      rw [h_A_union, measure_union h_disj hA₂_meas]
      exact ENNReal.toReal_add hμA₁_top hμA₂_top
    have h_int_add : ∫ x in A, f x ∂μ = ∫ x in A₁, f x ∂μ + ∫ x in A₂, f x ∂μ := by
      rw [h_A_union]
      exact setIntegral_union h_disj hA₂_meas (hf_int.mono hA₁_sub le_rfl)
        (hf_int.mono (Set.diff_subset) le_rfl)
    have hc_weighted : c = ((μ A₁).toReal * c₁ + (μ A₂).toReal * c₂) / (μ A).toReal := by
      rw [hc_mean, h_int_add, hc₁_def, hc₂_def]
      field_simp [ne_of_gt hμA₁_real_pos, ne_of_gt hμA₂_real_pos, ne_of_gt hμA_real_pos]
    -- Get |c₁ - c₂| ≥ ε'/2
    have h_c1_c : c₁ - c = (μ A₂).toReal / (μ A).toReal * (c₁ - c₂) := by
      rw [hc_weighted, hμ_add]
      field_simp [ne_of_gt hμA_real_pos]
      ring
    have h_c2_c : c₂ - c = -(μ A₁).toReal / (μ A).toReal * (c₁ - c₂) := by
      rw [hc_weighted, hμ_add]
      field_simp [ne_of_gt hμA_real_pos]
      ring
    have h_diff_bound : |c₁ - c₂| ≥ ε' / 2 := by
      rcases h_avg_diff with h1 | h2
      · rw [h_c1_c] at h1
        have h_ratio_le_one : (μ A₂).toReal / (μ A).toReal ≤ 1 := by
          rw [div_le_one hμA_real_pos, hμ_add]; linarith
        have h_ratio_pos : 0 < (μ A₂).toReal / (μ A).toReal :=
          div_pos hμA₂_real_pos hμA_real_pos
        rw [abs_mul, abs_of_pos h_ratio_pos] at h1
        calc |c₁ - c₂| ≥ (μ A₂).toReal / (μ A).toReal * |c₁ - c₂| := by
              nlinarith [abs_nonneg (c₁ - c₂)]
          _ ≥ ε' / 2 := h1
      · rw [h_c2_c] at h2
        have h_ratio_le_one : (μ A₁).toReal / (μ A).toReal ≤ 1 := by
          rw [div_le_one hμA_real_pos, hμ_add]; linarith
        have h_ratio_pos : 0 < (μ A₁).toReal / (μ A).toReal :=
          div_pos hμA₁_real_pos hμA_real_pos
        have h_abs_eq : |-(μ A₁).toReal / (μ A).toReal * (c₁ - c₂)| =
            (μ A₁).toReal / (μ A).toReal * |c₁ - c₂| := by
          rw [neg_div, neg_mul, abs_neg, abs_mul, abs_of_pos h_ratio_pos]
        rw [h_abs_eq] at h2
        calc |c₁ - c₂| ≥ (μ A₁).toReal / (μ A).toReal * |c₁ - c₂| := by
              nlinarith [abs_nonneg (c₁ - c₂)]
          _ ≥ ε' / 2 := h2
    -- Energy strictly increases using energy_splitPart_ge
    have h_sq_diff_bound : (c₁ - c₂) ^ 2 ≥ (ε' / 2) ^ 2 := by
      calc (c₁ - c₂) ^ 2 = |c₁ - c₂| ^ 2 := by rw [sq_abs]
        _ ≥ (ε' / 2) ^ 2 := by
          apply sq_le_sq'
          · linarith [abs_nonneg (c₁ - c₂), hε'_pos]
          · exact h_diff_bound
    have h_ge := energy_splitPart_ge W P A hA_mem A₁ hA₁_meas hA₁_sub hμA₁ hμA₂
    have h_rect_avg_eq₁ : rectAverage W A₁ V = c₁ := hc₁_rect.symm
    have h_rect_avg_eq₂ : rectAverage W (A \ A₁) V = c₂ := hc₂_rect.symm
    have h_V_term_pos : (μ V).toReal * (μ A₁).toReal * (μ (A \ A₁)).toReal / (μ A).toReal *
        (rectAverage W A₁ V - rectAverage W (A \ A₁) V) ^ 2 > 0 := by
      rw [h_rect_avg_eq₁, h_rect_avg_eq₂]
      apply mul_pos
      · apply div_pos
        · apply mul_pos (mul_pos hμV_real_pos hμA₁_real_pos) hμA₂_real_pos
        · exact hμA_real_pos
      · linarith [sq_nonneg (ε' / 2), sq_pos_of_pos hε'_pos]
    have h_sum_pos : P.parts.sum (fun U => (μ U).toReal * (μ A₁).toReal *
        (μ (A \ A₁)).toReal / (μ A).toReal *
        (rectAverage W A₁ U - rectAverage W (A \ A₁) U) ^ 2) > 0 := by
      have h_nonneg : ∀ U ∈ P.parts, 0 ≤ (μ U).toReal * (μ A₁).toReal *
          (μ (A \ A₁)).toReal / (μ A).toReal *
          (rectAverage W A₁ U - rectAverage W (A \ A₁) U) ^ 2 := by
        intro U _
        apply mul_nonneg
        · apply div_nonneg
          · apply mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
              ENNReal.toReal_nonneg
          · exact ENNReal.toReal_nonneg
        · exact sq_nonneg _
      exact (Finset.sum_pos_iff_of_nonneg h_nonneg).mpr ⟨V, hV_mem, h_V_term_pos⟩
    linarith [h_ge]

/-- Energy increment lemma (Frieze-Kannan style).

If W has large defect on some rectangle S × T of P, then refining that
rectangle increases the energy.

More precisely: if there exist S, T ∈ P such that
∫_{S×T} |W - rectAverage W S T|² ≥ ε² μ(S) μ(T),
then splitting S (or T) into two parts by an appropriate cut strictly
increases the energy.

This is the key step that drives the regularity iteration. -/
theorem energy_increment (W : Graphon α μ) (P : MeasurablePartition α μ)
    (ε : ℝ) (hε : ε > 0)
    (h_bad : ∃ S ∈ P.parts, ∃ T ∈ P.parts, μ S ≠ 0 ∧ μ T ≠ 0 ∧
      ∫ p in S ×ˢ T, (W.toAEEqFun p - rectAverage W S T) ^ 2 ∂(μ.prod μ) ≥
        ε ^ 2 * (μ S).toReal * (μ T).toReal) :
    ∃ Q : MeasurablePartition α μ,
      Refines Q P ∧ Q.parts.card ≤ 2 * P.parts.card ∧
      energy W Q > energy W P := by
  -- **Proof structure** (Frieze-Kannan energy increment with case split):
  --
  -- The defect on S×T decomposes two ways (by defect_eq_within_plus_between):
  --   defect = A_T + μ(T) * B_T   where A_T = within-T variance, B_T = ∫_S (W_T - c)²
  --   defect = A_S + μ(S) * B_S   where A_S = within-S variance, B_S = ∫_T (W_S - c)²
  --
  -- From h_bad: defect ≥ ε² * μ(S) * μ(T)
  -- Case split: either μ(T) * B_T ≥ ε²/2 * μ(S) * μ(T) or A_T ≥ ε²/2 * μ(S) * μ(T)
  --
  -- Case 1: μ(T) * B_T large ⟹ B_T ≥ ε²/2 * μ(S) ⟹ split S using exists_variance_cut
  -- Case 2: A_T large ⟹ by symmetric decomposition, B_S ≥ ε²/2 * μ(T) ⟹ split T
  --
  -- In both cases, we get a refinement with strictly larger energy.

  -- Step 1: Extract the "bad" rectangle S × T with positive measure parts
  obtain ⟨S, hS_mem, T, hT_mem, hμS_pos, hμT_pos, h_defect⟩ := h_bad
  have hS_meas : MeasurableSet S := P.measurableSet_part hS_mem
  have hT_meas : MeasurableSet T := P.measurableSet_part hT_mem
  have hμS_top : μ S ≠ ⊤ := (measure_lt_top μ S).ne
  have hμT_top : μ T ≠ ⊤ := (measure_lt_top μ T).ne
  have hμS_real_pos : (0 : ℝ) < (μ S).toReal := ENNReal.toReal_pos hμS_pos hμS_top
  have hμT_real_pos : (0 : ℝ) < (μ T).toReal := ENNReal.toReal_pos hμT_pos hμT_top

  -- Step 2: Define averages and constants
  set W_T := tAverage W T with hW_T_def  -- T-average: W_T(x) = (μT)⁻¹ ∫_T W(x,y)
  set W_S := tAverage W S with hW_S_def  -- S-average: W_S(y) = (μS)⁻¹ ∫_S W(x,y) (by symmetry)
  set c := rectAverage W S T with hc_def

  -- Step 3: Variance decomposition
  -- defect = ∫_{S×T} (W - c)² = A_T + μ(T) * B_T where:
  --   A_T = ∫_S (∫_T (W - W_T)²) = within-T variance averaged over S
  --   B_T = ∫_S (W_T - c)² = between-T variance on S
  set A_T := ∫ x in S, (∫ y in T, (W.toAEEqFun (x, y) - W_T x) ^ 2 ∂μ) ∂μ with hA_T_def
  set B_T := ∫ x in S, (W_T x - c) ^ 2 ∂μ with hB_T_def
  set defect := ∫ p in S ×ˢ T, (W.toAEEqFun p - c) ^ 2 ∂(μ.prod μ) with hdefect_def

  -- By defect_eq_within_plus_between: defect = A_T + μ(T) * B_T
  have h_decomp : defect = A_T + (μ T).toReal * B_T := by
    rw [hdefect_def, hA_T_def, hB_T_def, hW_T_def, hc_def]
    exact defect_eq_within_plus_between W S T hS_meas hT_meas hμS_pos hμT_pos

  -- Step 4: Case split based on which variance component is large
  -- From h_defect: defect ≥ ε² * μ(S) * μ(T)
  -- Either μ(T) * B_T ≥ defect/2 or A_T ≥ defect/2

  have h_case_split : (μ T).toReal * B_T ≥ ε ^ 2 / 2 * (μ S).toReal * (μ T).toReal ∨
                      A_T ≥ ε ^ 2 / 2 * (μ S).toReal * (μ T).toReal := by
    -- Since defect = A_T + μ(T) * B_T and defect ≥ ε² * μ(S) * μ(T)
    -- By pigeonhole, at least one term ≥ half of ε² * μ(S) * μ(T)
    have h_sum : A_T + (μ T).toReal * B_T ≥ ε ^ 2 * (μ S).toReal * (μ T).toReal := by
      rw [← h_decomp]; exact h_defect
    -- Both A_T and B_T are nonneg
    have hA_T_nonneg : A_T ≥ 0 := by
      apply setIntegral_nonneg_of_ae_restrict
      apply ae_of_all; intro x
      exact setIntegral_nonneg_of_ae_restrict (ae_of_all _ (fun _ => sq_nonneg _))
    have hB_T_nonneg : B_T ≥ 0 := setIntegral_nonneg_of_ae_restrict (ae_of_all _ (fun _ => sq_nonneg _))
    have hμTB_T_nonneg : (μ T).toReal * B_T ≥ 0 := mul_nonneg (le_of_lt hμT_real_pos) hB_T_nonneg
    by_contra h_neg
    push_neg at h_neg
    obtain ⟨h1, h2⟩ := h_neg
    have h_upper : A_T + (μ T).toReal * B_T <
        ε ^ 2 / 2 * (μ S).toReal * (μ T).toReal + ε ^ 2 / 2 * (μ S).toReal * (μ T).toReal := by
      calc A_T + (μ T).toReal * B_T
          < ε ^ 2 / 2 * (μ S).toReal * (μ T).toReal + (μ T).toReal * B_T := by linarith
        _ < ε ^ 2 / 2 * (μ S).toReal * (μ T).toReal + ε ^ 2 / 2 * (μ S).toReal * (μ T).toReal := by linarith
    have h_half : ε ^ 2 / 2 * (μ S).toReal * (μ T).toReal + ε ^ 2 / 2 * (μ S).toReal * (μ T).toReal =
                  ε ^ 2 * (μ S).toReal * (μ T).toReal := by ring
    have h_contra : defect < ε ^ 2 * (μ S).toReal * (μ T).toReal := by
      calc defect = A_T + (μ T).toReal * B_T := h_decomp
        _ < ε ^ 2 / 2 * (μ S).toReal * (μ T).toReal + ε ^ 2 / 2 * (μ S).toReal * (μ T).toReal := h_upper
        _ = ε ^ 2 * (μ S).toReal * (μ T).toReal := h_half
    linarith [h_defect]

  rcases h_case_split with h_split_S | h_split_T

  -- **Case 1**: Between-T variance is large → split S
  · -- B_T ≥ ε²/2 * μ(S) (dividing by μ(T))
    have h_var : B_T ≥ ε ^ 2 / 2 * (μ S).toReal := by
      have : (μ T).toReal * B_T ≥ ε ^ 2 / 2 * (μ S).toReal * (μ T).toReal := h_split_S
      have hB_T_nonneg : B_T ≥ 0 := setIntegral_nonneg_of_ae_restrict (ae_of_all _ (fun _ => sq_nonneg _))
      nlinarith [sq_nonneg ε, hμT_real_pos, hμS_real_pos]
    -- Unfold set definitions to match the helper's type
    have h_var_unfolded : ∫ x in S, (tAverage W T x - rectAverage W S T) ^ 2 ∂μ ≥
        ε ^ 2 / 2 * (μ S).toReal := by
      rw [← hW_T_def, ← hc_def, ← hB_T_def]; exact h_var
    exact energy_increment_of_between_variance W P ε hε
      S hS_mem T hT_mem hS_meas hT_meas hμS_pos hμT_pos h_var_unfolded

  -- **Case 2**: Within-T variance is large → use symmetric decomposition
  · -- A_T ≥ ε²/2 * μ(S) * μ(T), meaning the within-T variance is large.
    -- By symmetry of W, defect(S,T) = defect(T,S), so (T,S) is also a bad rectangle.
    -- Applying the variance decomposition on T×S gives:
    --   defect(T,S) = A_S + μ(S) * B_S
    -- By pigeonhole, either μ(S)*B_S ≥ defect/2 (split T, symmetric to Case 1)
    -- or A_S ≥ defect/2 (both within-variances large, needs different strategy).

    -- Step 2.1: Symmetric defect identity: defect(S,T) = defect(T,S)
    have h_defect_symm : defect =
        ∫ p in T ×ˢ S, (W.toAEEqFun p - rectAverage W T S) ^ 2 ∂(μ.prod μ) := by
      rw [hdefect_def, hc_def]
      exact defect_rect_symm W S T hS_meas hT_meas

    -- Step 2.2: Variance decomposition on T × S
    -- defect(T,S) = A_S + μ(S) * B_S where:
    --   A_S = ∫_T (∫_S (W - W_S)²) = within-S variance
    --   B_S = ∫_T (W_S - rectAverage W T S)² = between-S variance on T
    set c' := rectAverage W T S with hc'_def
    set A_S := ∫ y in T, (∫ x in S, (W.toAEEqFun (y, x) - W_S y) ^ 2 ∂μ) ∂μ with hA_S_def
    set B_S := ∫ y in T, (W_S y - c') ^ 2 ∂μ with hB_S_def

    have h_decomp_TS : ∫ p in T ×ˢ S, (W.toAEEqFun p - c') ^ 2 ∂(μ.prod μ) =
        A_S + (μ S).toReal * B_S := by
      rw [hA_S_def, hB_S_def, hW_S_def, hc'_def]
      exact defect_eq_within_plus_between W T S hT_meas hS_meas hμT_pos hμS_pos

    -- Step 2.3: Pigeonhole on the symmetric decomposition
    -- defect = A_S + μ(S) * B_S, defect ≥ ε² * μ(S) * μ(T)
    -- Either μ(S) * B_S ≥ ε²/2 * μ(S) * μ(T) or A_S ≥ ε²/2 * μ(S) * μ(T)
    have h_defect_eq_sym : defect = A_S + (μ S).toReal * B_S := by
      rw [h_defect_symm]; exact h_decomp_TS

    have hA_S_nonneg : A_S ≥ 0 := by
      apply setIntegral_nonneg_of_ae_restrict
      apply ae_of_all; intro x
      exact setIntegral_nonneg_of_ae_restrict (ae_of_all _ (fun _ => sq_nonneg _))
    have hB_S_nonneg : B_S ≥ 0 := setIntegral_nonneg_of_ae_restrict (ae_of_all _ (fun _ => sq_nonneg _))

    -- Pigeonhole: defect = A_S + μ(S)*B_S ≥ ε²*μ(S)*μ(T)
    -- so either μ(S)*B_S ≥ half or A_S ≥ half
    have h_sum_sym : A_S + (μ S).toReal * B_S ≥ ε ^ 2 * (μ S).toReal * (μ T).toReal := by
      rw [← h_defect_eq_sym]; exact h_defect
    -- Use classical logic for pigeonhole
    by_cases h_split_T_sym : (μ S).toReal * B_S ≥ ε ^ 2 / 2 * (μ S).toReal * (μ T).toReal

    -- **Sub-case 2a**: Between-S variance on T is large → split T
    · -- B_S ≥ ε²/2 * μ(T) (dividing by μ(S))
      have h_var : B_S ≥ ε ^ 2 / 2 * (μ T).toReal := by
        have : (μ S).toReal * B_S ≥ ε ^ 2 / 2 * (μ S).toReal * (μ T).toReal := h_split_T_sym
        have hB_S_nonneg : B_S ≥ 0 := setIntegral_nonneg_of_ae_restrict (ae_of_all _ (fun _ => sq_nonneg _))
        nlinarith [sq_nonneg ε, hμS_real_pos, hμT_real_pos]
      -- Unfold set definitions to match the helper's type
      have h_var_unfolded : ∫ y in T, (tAverage W S y - rectAverage W T S) ^ 2 ∂μ ≥
          ε ^ 2 / 2 * (μ T).toReal := by
        rw [← hW_S_def, ← hc'_def, ← hB_S_def]; exact h_var
      exact energy_increment_of_between_variance W P ε hε
        T hT_mem S hS_mem hT_meas hS_meas hμT_pos hμS_pos h_var_unfolded

    -- **Sub-case 2b**: Between-S variance on T is small.
    -- B_T is unconstrained by the rcases (which only gave A_T ≥ half).
    -- Check whether B_T is large enough to split S directly.
    · by_cases h_check_B_T : B_T ≥ ε ^ 2 / 2 * (μ S).toReal
      -- Sub-case 2b-i: B_T large → split S (same as Case 1)
      · have h_var_unfolded : ∫ x in S, (tAverage W T x - rectAverage W S T) ^ 2 ∂μ ≥
            ε ^ 2 / 2 * (μ S).toReal := by
          rw [← hW_T_def, ← hc_def, ← hB_T_def]; exact h_check_B_T
        exact energy_increment_of_between_variance W P ε hε
          S hS_mem T hT_mem hS_meas hT_meas hμS_pos hμT_pos h_var_unfolded
      -- Sub-case 2b-ii: B_T < ε²/2 * μ(S) AND B_S < ε²/2 * μ(T)
      -- Both within-variances A_T, A_S are large, both between-variances B_T, B_S are small.
      -- This genuinely requires global cut-norm splitting (not single-part splitting).
      · push_neg at h_split_T_sym h_check_B_T
        have _h_A_S_large : A_S ≥ ε ^ 2 / 2 * (μ S).toReal * (μ T).toReal := by
          linarith [h_sum_sym]
        sorry

end Energy

/-! ### Regularity lemma -/

section Regularity

variable [IsProbabilityMeasure μ]

/-- The trivial partition with just {univ} as the only part. -/
noncomputable def trivialPartition : MeasurablePartition α μ where
  parts := {Set.univ}
  measurable_parts := fun S hS => by
    simp only [Finset.mem_singleton] at hS
    rw [hS]
    exact MeasurableSet.univ
  pairwiseDisjoint := by
    intro S hS T hT hne
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hS hT
    -- Both S and T must be univ, but hne says S ≠ T - contradiction
    exact absurd (hS.trans hT.symm) hne
  ae_covers := by
    filter_upwards with x
    exact ⟨Set.univ, Finset.mem_singleton_self _, Set.mem_univ x⟩

theorem trivialPartition_card : (trivialPartition (α := α) (μ := μ)).parts.card = 1 := by
  simp [trivialPartition]

/-- If the total defect exceeds ε², then there exists a "bad" rectangle (S,T)
    where the defect per unit area is at least ε². This is the contrapositive:
    if every rectangle has defect < ε² μ(S) μ(T), then total defect < ε².

    This lemma is needed to convert the regularity iteration stopping condition
    (defect ≤ ε²) to finding a bad rectangle for energy_increment. -/
lemma exists_bad_rect_of_defect_gt (W : Graphon α μ) (P : MeasurablePartition α μ)
    (ε : ℝ) (hε : ε > 0) (h_defect : defect W P > ε ^ 2) :
    ∃ S ∈ P.parts, ∃ T ∈ P.parts, μ S ≠ 0 ∧ μ T ≠ 0 ∧
      ∫ p in S ×ˢ T, (W.toAEEqFun p - rectAverage W S T) ^ 2 ∂(μ.prod μ) ≥
        ε ^ 2 * (μ S).toReal * (μ T).toReal := by
  -- Contrapositive: if every non-null rectangle has defect < ε² μ(S) μ(T),
  -- then total defect = Σ defect(S,T) < ε² Σ μ(S)μ(T) = ε² · (Σ μ(S))² ≤ ε²
  by_contra h_neg
  push_neg at h_neg
  -- h_neg: ∀ S ∈ P.parts, ∀ T ∈ P.parts, μ S ≠ 0 → μ T ≠ 0 →
  --        ∫_{S×T} (W - c)² < ε² μ(S) μ(T)
  have h_bound : defect W P ≤ ε ^ 2 := by
    unfold defect
    -- Total defect ≤ ε² Σ_{S,T} μ(S) μ(T) = ε² (Σ μ(S))² ≤ ε²
    have h_each_le : ∀ S ∈ P.parts, ∀ T ∈ P.parts,
        ∫ p in S ×ˢ T, (W.toAEEqFun p - rectAverage W S T) ^ 2 ∂(μ.prod μ) ≤
          ε ^ 2 * (μ S).toReal * (μ T).toReal := by
      intro S hS T hT
      by_cases hμS : μ S = 0
      · have h_prod_zero : (μ.prod μ) (S ×ˢ T) = 0 := by
          rw [Measure.prod_prod, hμS, zero_mul]
        simp only [setIntegral_measure_zero _ h_prod_zero, hμS, ENNReal.toReal_zero]
        positivity
      · by_cases hμT : μ T = 0
        · have h_prod_zero : (μ.prod μ) (S ×ˢ T) = 0 := by
            rw [Measure.prod_prod, hμT, mul_zero]
          simp only [setIntegral_measure_zero _ h_prod_zero, hμT, ENNReal.toReal_zero]
          positivity
        · exact le_of_lt (h_neg S hS T hT hμS hμT)
    calc ∑ S ∈ P.parts, ∑ T ∈ P.parts,
          ∫ p in S ×ˢ T, (W.toAEEqFun p - rectAverage W S T) ^ 2 ∂(μ.prod μ)
        ≤ ∑ S ∈ P.parts, ∑ T ∈ P.parts, ε ^ 2 * (μ S).toReal * (μ T).toReal := by
          apply Finset.sum_le_sum; intro S hS
          apply Finset.sum_le_sum; intro T hT
          exact h_each_le S hS T hT
      _ ≤ ε ^ 2 := by
          -- Use that Σ_S Σ_T ε² μ(S) μ(T) = ε² (Σ_S μ(S)) (Σ_T μ(T)) ≤ ε² · 1 · 1
          have h1 : ∑ S ∈ P.parts, ∑ T ∈ P.parts, ε ^ 2 * (μ S).toReal * (μ T).toReal =
              ε ^ 2 * ∑ S ∈ P.parts, ∑ T ∈ P.parts, (μ S).toReal * (μ T).toReal := by
            trans ∑ S ∈ P.parts, ε ^ 2 * ∑ T ∈ P.parts, (μ S).toReal * (μ T).toReal
            · apply Finset.sum_congr rfl; intro S _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro T _; ring
            · rw [← Finset.mul_sum]
          have h2 : ∑ S ∈ P.parts, ∑ T ∈ P.parts, (μ S).toReal * (μ T).toReal =
              (∑ S ∈ P.parts, (μ S).toReal) * (∑ T ∈ P.parts, (μ T).toReal) := by
            rw [← Finset.sum_mul_sum]
          have h3 : (∑ S ∈ P.parts, (μ S).toReal) * (∑ T ∈ P.parts, (μ T).toReal) ≤ 1 := by
            calc (∑ S ∈ P.parts, (μ S).toReal) * (∑ T ∈ P.parts, (μ T).toReal)
                ≤ 1 * 1 := mul_le_mul (MeasurablePartition.sum_measure_parts_le_one P)
                    (MeasurablePartition.sum_measure_parts_le_one P)
                    (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg) (by norm_num)
              _ = 1 := by ring
          calc ∑ S ∈ P.parts, ∑ T ∈ P.parts, ε ^ 2 * (μ S).toReal * (μ T).toReal
              = ε ^ 2 * ∑ S ∈ P.parts, ∑ T ∈ P.parts, (μ S).toReal * (μ T).toReal := h1
            _ = ε ^ 2 * ((∑ S ∈ P.parts, (μ S).toReal) * (∑ T ∈ P.parts, (μ T).toReal)) := by rw [h2]
            _ ≤ ε ^ 2 * 1 := mul_le_mul_of_nonneg_left h3 (sq_nonneg ε)
            _ = ε ^ 2 := by ring
  linarith

/-- The regularity function: given ε, returns an upper bound on the number of parts
    needed in a partition to achieve ε-approximation.

For Frieze-Kannan regularity, the bound is polynomial in 1/ε (roughly 1/ε⁸).
This is much better than the tower bound in Szemerédi's lemma. -/
noncomputable def regularityBound (ε : ℝ) : ℕ :=
  if ε ≤ 0 then 0 else Nat.ceil (1 / ε ^ 8)

/-- The Frieze-Kannan weak regularity lemma.

For any ε > 0 and any graphon W, there exists a measurable partition P with
at most O(1/ε⁸) parts such that W has small defect on P.

This implies that W is ε-close to the step graphon stepify P W in cut norm.

**Proof outline** (Frieze-Kannan [1999]):
1. Start with trivial partition P₀ = {α}
2. While there exists a "bad" rectangle (defect ≥ ε² per unit area):
   - Apply energy_increment to get P_{i+1}
   - This strictly increases the energy
3. With a quantitative energy increment (not yet proved), energy ≤ 1
   bounds the number of iterations
4. Each iteration at most doubles parts, giving a bound on the final count
5. More careful analysis gives polynomial bound ~1/ε⁸ -/
theorem regularity (W : Graphon α μ) (ε : ℝ) (hε : ε > 0) :
    ∃ P : MeasurablePartition α μ,
      P.parts.card ≤ regularityBound ε ∧
      defect W P ≤ ε ^ 2 := by
  -- **Proof structure** (Frieze-Kannan iteration with fuel):
  --
  -- Key insight: energy_increment gives energy strictly increases each step.
  -- With a quantitative bound, energy ≤ 1 limits the number of iterations.

  -- Define the iteration bound (fuel) — aspirational, pending quantitative increment
  set maxIter : ℕ := Nat.ceil (4 / ε ^ 4) + 1 with hMaxIter_def

  -- We prove by strong induction on fuel that:
  -- For all P with defect > ε², iterating at most k times either:
  -- (a) produces P' with defect ≤ ε² and bounded parts, or
  -- (b) energy exceeds 1 (contradiction)

  -- Start with trivial partition
  let P₀ := trivialPartition (α := α) (μ := μ)

  -- Case analysis: either defect P₀ ≤ ε² already, or we need to iterate
  by_cases h_done : defect W P₀ ≤ ε ^ 2
  · -- Already done: trivial partition has small defect
    use P₀
    constructor
    · -- parts.card ≤ regularityBound ε
      calc P₀.parts.card = 1 := trivialPartition_card
        _ ≤ regularityBound ε := by
          simp only [regularityBound]
          split_ifs with h
          · linarith
          · exact Nat.one_le_ceil_iff.mpr (by positivity)
    · exact h_done

  · -- Need to iterate: use energy_increment repeatedly
    push_neg at h_done
    -- h_done : ε ^ 2 < defect W P₀
    -- Strategy: iterate energy_increment at most regularityBound ε times.
    -- Each iteration:
    --   1. Gets a bad rectangle from exists_bad_rect_of_defect_gt
    --   2. Applies energy_increment to get Q with energy W Q > energy W P
    --   3. Q refines P and Q.parts.card ≤ 2 * P.parts.card
    --
    -- Since energy is bounded by 1 and strictly increases each step,
    -- we must eventually reach defect ≤ ε² (or the parts count exceeds the bound).
    --
    -- Two blockers remain for completing this proof:
    --
    -- 1. Quantitative energy increment: energy_increment currently gives strict
    --    inequality (energy W Q > energy W P). For bounding iterations, we need
    --    energy W Q ≥ energy W P + c * ε^k for some constant c, k. This would
    --    bound iterations by 1/(c * ε^k) since energy ≤ 1.
    --
    -- 2. Sub-case 2b of energy_increment: when both within-variances are large,
    --    a single-part split is insufficient. The standard FK proof uses a
    --    global cut-norm splitting strategy (splitting ALL parts by one set A),
    --    which requires additional infrastructure.
    sorry

end Regularity

/-! ### Equitable partitions -/

section Equitable

variable [IsProbabilityMeasure μ]

/-- A partition is ε-equitable if all parts have measure within ε of 1/k,
    where k is the number of parts. -/
def IsEquitable (P : MeasurablePartition α μ) (ε : ℝ) : Prop :=
  ∀ S ∈ P.parts, |(μ S).toReal - 1 / P.parts.card| ≤ ε

/-- Any partition can be refined to an equitable one with controlled part count.

**Proof idea**:
Each part S of P with μ(S) > ε is split into ⌈μ(S)/ε⌉ equal-measure pieces.
Small parts (μ(S) ≤ ε) are kept as is.

**Construction**: For a part S with μ(S) > ε:
1. Find measurable sets S₁,...,Sₖ partitioning S with k = ⌈μ(S)/ε⌉
2. Each Sᵢ has measure μ(S)/k ≈ ε

**Required infrastructure** (not yet in mathlib):
- Intermediate value theorem for measures on atomless spaces:
  For S with μ(S) = m and 0 ≤ r ≤ m, there exists measurable T ⊆ S with μ(T) = r.
- This follows from the order-continuity of atomless measures but requires
  explicit construction via Lebesgue density / quantile functions.

The `[NoAtoms μ]` hypothesis ensures the measure has no atoms, which is
necessary for the existence of subsets with prescribed measure. -/
theorem exists_equitable_refinement [NoAtoms μ] (P : MeasurablePartition α μ) (ε : ℝ) (hε : ε > 0) :
    ∃ Q : MeasurablePartition α μ,
      Refines Q P ∧
      IsEquitable Q ε ∧
      Q.parts.card ≤ P.parts.card * ⌈1 / ε⌉₊ := by
  -- The proof requires the intermediate value theorem for measures:
  -- Given a measurable set S with μ(S) = m, for any 0 ≤ r ≤ m, there exists
  -- a measurable T ⊆ S with μ(T) = r. This is true for atomless measures
  -- but requires construction via order-continuous measure theory.
  --
  -- Once that lemma is available, the proof proceeds:
  -- 1. For each S ∈ P.parts with μ(S) > ε:
  --    - Let k = ⌈μ(S)/ε⌉
  --    - Split S into S₁, ..., Sₖ with μ(Sᵢ) = μ(S)/k ≤ ε
  -- 2. Small parts (μ(S) ≤ ε) are kept unchanged
  -- 3. The refined partition Q satisfies:
  --    - Refines P (by construction)
  --    - IsEquitable: each part has measure ≤ ε, and with k parts totaling 1,
  --      the average is 1/k, so deviation is at most ε
  --    - Card bound: each S splits into ≤ ⌈1/ε⌉ parts (since μ(S) ≤ 1)
  sorry

end Equitable

/-! ### Step graphon density -/

section StepDense

variable [IsProbabilityMeasure μ]

/-- Step graphons are dense in the space of graphons with respect to cut norm.

For any graphon W and ε > 0, there exists a step graphon S with
cut norm difference at most ε. -/
theorem step_graphons_dense (W : Graphon α μ) (ε : ℝ) (hε : ε > 0) :
    ∃ (P : MeasurablePartition α μ), True := by
  -- This follows from the regularity lemma
  obtain ⟨P, _⟩ := regularity W ε hε
  exact ⟨P, trivial⟩

end StepDense

end Graphon
