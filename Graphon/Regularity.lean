/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.Approximation
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-!
# Regularity Lemma for Graphons

This file proves the regularity lemma for graphons, which says that any graphon
can be approximated by a step graphon in cut norm.

## Main results

* `Graphon.regularity` - For any ε > 0, there exists a partition with bounded
  number of parts such that the stepified graphon is ε-close in cut norm.

## Implementation notes

The Frieze–Kannan weak regularity lemma is one of the central results in graphon
theory. It provides a step-function approximation in cut norm with single-exponential
bounds on the number of parts (better than the tower-type bounds from Szemerédi's
strong regularity lemma).

The number of parts in the partition depends only on ε, not on the graphon.
This is crucial for applications to graph limits.

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Corollary 9.13
* Frieze, A. & Kannan, R. (1999). Quick approximation to matrices and applications.
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

Proof: Uses a Chebyshev-type argument to find a measurable cut. -/
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

set_option maxHeartbeats 1600000 in
/-- FK global cut lemma for the case where both within-variances are large.

When the within-T variance ∫_S ∫_T (W - W_T)² is large but the between-T
variance ∫_S (W_T - c)² is small (and symmetrically for S), a single-part
split is insufficient. Instead, we find a nontrivial cut of T and use
two sequential splits. -/
private theorem energy_increment_of_within_variance
    (W : Graphon α μ) (P : MeasurablePartition α μ) (ε : ℝ) (hε : ε > 0)
    (S : Set α) (hS_mem : S ∈ P.parts)
    (T : Set α) (hT_mem : T ∈ P.parts)
    (hS_meas : MeasurableSet S) (hT_meas : MeasurableSet T)
    (hμS : μ S ≠ 0) (hμT : μ T ≠ 0)
    (h_within_T_large : ∫ x in S, (∫ y in T,
        (W.toAEEqFun (x, y) - tAverage W T x) ^ 2 ∂μ) ∂μ ≥
        ε ^ 2 / 2 * (μ S).toReal * (μ T).toReal) :
    ∃ Q : MeasurablePartition α μ,
      Refines Q P ∧ Q.parts.card ≤ 2 * P.parts.card ∧
      energy W Q > energy W P := by
  -- Strategy: case split on whether between-variances are positive.
  -- If B_T > 0 or B_S > 0, delegate to energy_increment_of_between_variance.
  -- If both are zero, use ae_eq_zero_restrict to find a good cut.
  have hμS_top : μ S ≠ ⊤ := (measure_lt_top μ S).ne
  have hμT_top : μ T ≠ ⊤ := (measure_lt_top μ T).ne
  have hμS_real_pos : (0 : ℝ) < (μ S).toReal := ENNReal.toReal_pos hμS hμS_top
  have hμT_real_pos : (0 : ℝ) < (μ T).toReal := ENNReal.toReal_pos hμT hμT_top
  -- Define the between-T variance on S: B_T = ∫_S (W_T(x) - c)²
  set c := rectAverage W S T with hc_def
  set B_T := ∫ x in S, (tAverage W T x - c) ^ 2 ∂μ with hB_T_def
  -- Case 1: B_T > 0 → delegate to energy_increment_of_between_variance
  by_cases hB_T_pos : B_T > 0
  · -- Set ε' = √(2 * B_T / μS) > 0 so that ε'²/2 * μS = B_T
    set ε' := Real.sqrt (2 * B_T / (μ S).toReal) with hε'_def
    have hε'_pos : ε' > 0 := Real.sqrt_pos.mpr (div_pos (mul_pos two_pos hB_T_pos) hμS_real_pos)
    have h_var : ∫ x in S, (tAverage W T x - rectAverage W S T) ^ 2 ∂μ ≥
        ε' ^ 2 / 2 * (μ S).toReal := by
      rw [hε'_def, Real.sq_sqrt (le_of_lt (div_pos (mul_pos two_pos hB_T_pos) hμS_real_pos))]
      rw [← hc_def, ← hB_T_def]
      rw [ge_iff_le, ← sub_nonneg]
      have : (μ S).toReal ≠ 0 := ne_of_gt hμS_real_pos
      field_simp
      linarith [hB_T_pos, hμS_real_pos]
    exact energy_increment_of_between_variance W P ε' hε'_pos
      S hS_mem T hT_mem hS_meas hT_meas hμS hμT h_var
  · -- B_T = 0: the between-T variance vanishes
    push_neg at hB_T_pos
    have hB_T_nonneg : B_T ≥ 0 :=
      setIntegral_nonneg_of_ae_restrict (ae_of_all _ (fun _ => sq_nonneg _))
    have hB_T_zero : B_T = 0 := le_antisymm hB_T_pos hB_T_nonneg
    -- Symmetric decomposition: defect(S,T) = defect(T,S), apply variance decomp on T×S
    set c' := rectAverage W T S with hc'_def
    set B_S := ∫ y in T, (tAverage W S y - c') ^ 2 ∂μ with hB_S_def
    -- Case 2: B_S > 0 → delegate to energy_increment_of_between_variance with swapped roles
    by_cases hB_S_pos : B_S > 0
    · set ε' := Real.sqrt (2 * B_S / (μ T).toReal) with hε'_def
      have hε'_pos : ε' > 0 := Real.sqrt_pos.mpr (div_pos (mul_pos two_pos hB_S_pos) hμT_real_pos)
      have h_var : ∫ y in T, (tAverage W S y - rectAverage W T S) ^ 2 ∂μ ≥
          ε' ^ 2 / 2 * (μ T).toReal := by
        rw [hε'_def, Real.sq_sqrt (le_of_lt (div_pos (mul_pos two_pos hB_S_pos) hμT_real_pos))]
        rw [← hc'_def, ← hB_S_def]
        rw [ge_iff_le, ← sub_nonneg]
        have : (μ T).toReal ≠ 0 := ne_of_gt hμT_real_pos
        field_simp
        linarith [hB_S_pos, hμT_real_pos]
      exact energy_increment_of_between_variance W P ε' hε'_pos
        T hT_mem S hS_mem hT_meas hS_meas hμT hμS h_var
    · -- Case 3: B_T = 0 AND B_S = 0 (hard case)
      -- W_T = c a.e. on S and W_S = c' a.e. on T, but within-T variance is large.
      -- Need to find a global cut that simultaneously splits S and T.
      push_neg at hB_S_pos
      have hB_S_nonneg : B_S ≥ 0 :=
        setIntegral_nonneg_of_ae_restrict (ae_of_all _ (fun _ => sq_nonneg _))
      have hB_S_zero : B_S = 0 := le_antisymm hB_S_pos hB_S_nonneg
      -- Step 1: tAvg_T = c a.e. on S (from B_T = 0)
      have h_tAvg_T_ae : tAverage W T =ᵐ[μ.restrict S] fun _ => c := by
        have h_sq_zero := hB_T_zero
        rw [hB_T_def] at h_sq_zero
        have h_nonneg : 0 ≤ᵐ[μ.restrict S] fun x => (tAverage W T x - c) ^ 2 :=
          ae_of_all _ (fun _ => sq_nonneg _)
        have h_int : IntegrableOn (fun x => (tAverage W T x - c) ^ 2) S μ := by
          apply Measure.integrableOn_of_bounded (measure_lt_top μ S).ne
          · exact ((tAverage_measurable W T hT_meas).sub measurable_const).pow_const 2
              |>.aestronglyMeasurable
          · filter_upwards [ae_restrict_of_ae (tAverage_ae_mem_Icc W T hT_meas)] with x hx
            simp only [Real.norm_eq_abs]
            have hc_mem := rectAverage_mem_Icc W S T hS_meas hT_meas
            calc |((tAverage W T x) - c) ^ 2|
                = ((tAverage W T x) - c) ^ 2 := abs_of_nonneg (sq_nonneg _)
              _ ≤ 1 := by nlinarith [hx.1, hx.2, hc_mem.1, hc_mem.2]
        have h_ae_zero := (setIntegral_eq_zero_iff_of_nonneg_ae h_nonneg h_int).mp h_sq_zero
        filter_upwards [h_ae_zero] with x hx
        simp only [Pi.zero_apply] at hx
        linarith [sq_eq_zero_iff.mp hx]
      -- Step 2: c' = c (by rectAverage_symm)
      have hc'_eq_c : c' = c := by
        rw [hc'_def, hc_def]
        exact rectAverage_symm W T S hT_meas hS_meas
      -- Step 3: tAvg_S = c a.e. on T (from B_S = 0 and c' = c)
      have h_tAvg_S_ae : tAverage W S =ᵐ[μ.restrict T] fun _ => c := by
        have h_sq_zero := hB_S_zero
        rw [hB_S_def] at h_sq_zero
        have h_nonneg : 0 ≤ᵐ[μ.restrict T] fun y => (tAverage W S y - c') ^ 2 :=
          ae_of_all _ (fun _ => sq_nonneg _)
        have h_int : IntegrableOn (fun y => (tAverage W S y - c') ^ 2) T μ := by
          apply Measure.integrableOn_of_bounded (measure_lt_top μ T).ne
          · exact ((tAverage_measurable W S hS_meas).sub measurable_const).pow_const 2
              |>.aestronglyMeasurable
          · filter_upwards [ae_restrict_of_ae (tAverage_ae_mem_Icc W S hS_meas)] with y hy
            simp only [Real.norm_eq_abs]
            have hc'_mem := rectAverage_mem_Icc W T S hT_meas hS_meas
            calc |((tAverage W S y) - c') ^ 2|
                = ((tAverage W S y) - c') ^ 2 := abs_of_nonneg (sq_nonneg _)
              _ ≤ 1 := by nlinarith [hy.1, hy.2, hc'_mem.1, hc'_mem.2]
        have h_ae_zero := (setIntegral_eq_zero_iff_of_nonneg_ae h_nonneg h_int).mp h_sq_zero
        filter_upwards [h_ae_zero] with y hy
        simp only [Pi.zero_apply] at hy
        have := sq_eq_zero_iff.mp hy
        linarith [this, hc'_eq_c]
      -- Step 4: The within-T variance with c substituted
      -- Since tAvg_T = c a.e. on S, we can replace tAvg_T(x) by c in the integral
      have h_within_c : ∫ x in S, (∫ y in T,
          (W.toAEEqFun (x, y) - c) ^ 2 ∂μ) ∂μ ≥
          ε ^ 2 / 2 * (μ S).toReal * (μ T).toReal := by
        calc ε ^ 2 / 2 * (μ S).toReal * (μ T).toReal
            ≤ ∫ x in S, (∫ y in T,
              (W.toAEEqFun (x, y) - tAverage W T x) ^ 2 ∂μ) ∂μ := h_within_T_large
          _ = ∫ x in S, (∫ y in T,
              (W.toAEEqFun (x, y) - c) ^ 2 ∂μ) ∂μ := by
            apply setIntegral_congr_ae hS_meas
            have := (ae_restrict_iff' hS_meas).mp h_tAvg_T_ae
            filter_upwards [this] with x hx hxS
            have hx' := hx hxS
            simp only [hx']
      have h_within_pos : (0 : ℝ) < ∫ x in S, (∫ y in T,
          (W.toAEEqFun (x, y) - c) ^ 2 ∂μ) ∂μ :=
        lt_of_lt_of_le (by positivity) h_within_c
      -- Step 5: Case split on S = T
      by_cases hST : S = T
      · -- Sub-case S = T: B_T = 0, B_S = 0, within-variance large on S×S
        subst hST
        -- Part 1: Find nontrivial B ⊆ S with rectAvg(B,B) ≠ c.
        -- By contradiction: if all nontrivial B ⊆ S have rectAvg(B,B) = c, then
        -- ∫_{B×B} (W-c) = 0 for all nontrivial B. By polarization + W.symm_ae,
        -- ∫_{A×B} (W-c) = 0 for all measurable A,B ⊆ S. By π-λ, W = c a.e. on S×S,
        -- contradicting h_within_pos.
        have h_good_cut : ∃ B : Set α, MeasurableSet B ∧ B ⊆ S ∧ μ B ≠ 0 ∧ μ (S \ B) ≠ 0 ∧
            rectAverage W B B ≠ c := by
          by_contra h_neg
          push_neg at h_neg
          exfalso
          -- Shorthand for the product measure restricted to S × S
          set ν := (μ.restrict S).prod (μ.restrict S) with hν_def
          -- Helper: integrability of W-c on any product of subsets
          have h_Wc_int_prod : ∀ A B : Set α, MeasurableSet A → MeasurableSet B →
              IntegrableOn (fun p => W.toAEEqFun p - c) (A ×ˢ B) (μ.prod μ) := by
            intro A B hA_meas hB_meas
            apply Measure.integrableOn_of_bounded (M := 1)
            · rw [Measure.prod_prod]; exact (ENNReal.mul_lt_top (measure_lt_top μ A)
                  (measure_lt_top μ B)).ne
            · exact (W.toAEEqFun.measurable.sub measurable_const).aestronglyMeasurable
            · filter_upwards [ae_restrict_of_ae W.ae_mem_Icc] with p hp
              simp only [Real.norm_eq_abs, abs_le]
              have hc_mem := rectAverage_mem_Icc W S S hS_meas hS_meas
              constructor <;> nlinarith [hp.1, hp.2, hc_mem.1, hc_mem.2]
          -- Step A: ∫_{B'×B'} (W-c) = 0 for nontrivial B' ⊆ S (from h_neg)
          have h_diag_zero : ∀ B' : Set α, MeasurableSet B' → B' ⊆ S →
              μ B' ≠ 0 → μ (S \ B') ≠ 0 →
              ∫ p in B' ×ˢ B', (W.toAEEqFun p - c) ∂(μ.prod μ) = 0 := by
            intro B' hB'_meas hB'_sub hμB' hμSB'
            have h_ra := h_neg B' hB'_meas hB'_sub hμB' hμSB'
            unfold rectAverage at h_ra
            simp only [hμB', dif_neg, not_false_eq_true] at h_ra
            have hμB'_pos : (0 : ℝ) < (μ B').toReal :=
              ENNReal.toReal_pos hμB' (measure_lt_top μ B').ne
            have h_eq : ∫ p in B' ×ˢ B', W.toAEEqFun p ∂(μ.prod μ) =
                c * (μ B').toReal * (μ B').toReal := by
              field_simp [ne_of_gt hμB'_pos] at h_ra ⊢; linarith
            -- ∫_{B'×B'} (W-c) = ∫_{B'×B'} W - ∫_{B'×B'} c = c*μ²-c*μ² = 0
            have h_int_W : IntegrableOn (fun p => W.toAEEqFun p) (B' ×ˢ B') (μ.prod μ) :=
              (SymmKernel.graphon_integrable W).integrableOn
            have h_int_c : IntegrableOn (fun (_ : α × α) => c) (B' ×ˢ B') (μ.prod μ) :=
              integrableOn_const
            have h_split : ∫ p in B' ×ˢ B', (W.toAEEqFun p - c) ∂(μ.prod μ) =
                ∫ p in B' ×ˢ B', W.toAEEqFun p ∂(μ.prod μ) -
                ∫ p in B' ×ˢ B', c ∂(μ.prod μ) :=
              integral_sub h_int_W h_int_c
            have h_const : ∫ (_ : α × α) in B' ×ˢ B', c ∂(μ.prod μ) =
                c * (μ B').toReal * (μ B').toReal := by
              rw [setIntegral_const c, smul_eq_mul, Measure.real, Measure.prod_prod,
                ENNReal.toReal_mul]; ring
            linarith
          -- Step B: ∫_{A×S} (W-c) = 0 for all measurable A ⊆ S (from h_tAvg_T_ae)
          have h_W_ae_ae := Measure.ae_ae_of_ae_prod W.ae_mem_Icc
          have h_slice_int : ∀ᵐ x ∂μ, ∀ B' : Set α, MeasurableSet B' →
              IntegrableOn (fun y => W.toAEEqFun (x, y)) B' μ := by
            filter_upwards [h_W_ae_ae,
              AEStronglyMeasurable.prodMk_left W.toAEEqFun.aestronglyMeasurable]
              with x hx hx_meas
            intro B' hB'_meas
            exact Measure.integrableOn_of_bounded (M := 1) (measure_lt_top μ B').ne hx_meas
              (by filter_upwards [ae_restrict_of_ae hx] with y hy
                  simp only [Real.norm_eq_abs, abs_le]
                  exact ⟨by linarith [hy.1], by linarith [hy.2]⟩)
          have h_row_S_zero : ∀ A : Set α, MeasurableSet A → A ⊆ S →
              ∫ p in A ×ˢ S, (W.toAEEqFun p - c) ∂(μ.prod μ) = 0 := by
            intro A hA_meas hA_sub
            rw [setIntegral_prod _ (h_Wc_int_prod A S hA_meas hS_meas)]
            -- Inner integral: ∫_S (W(x,y)-c) dy = 0 for a.e. x ∈ S (from h_tAvg_T_ae)
            have h_inner : (fun x => ∫ y in S, (W.toAEEqFun (x, y) - c) ∂μ)
                =ᵐ[μ.restrict S] 0 := by
              filter_upwards [h_tAvg_T_ae, ae_restrict_of_ae h_slice_int] with x hx hx_int
              simp only [Pi.zero_apply]
              unfold tAverage at hx
              simp only [hμS, dif_neg, not_false_eq_true] at hx
              have h1 : ∫ y in S, W.toAEEqFun (x, y) ∂μ = c * (μ S).toReal := by
                field_simp [ne_of_gt hμS_real_pos] at hx ⊢; linarith
              rw [integral_sub (hx_int S hS_meas)
                  (integrableOn_const (measure_lt_top μ S).ne)]
              rw [h1, setIntegral_const]; simp [Measure.real]; ring
            have h_ae_A : (fun x => ∫ y in S, (W.toAEEqFun (x, y) - c) ∂μ)
                =ᵐ[μ.restrict A] 0 :=
              h_inner.filter_mono (ae_mono (Measure.restrict_mono hA_sub le_rfl))
            exact integral_eq_zero_of_ae h_ae_A
          -- Step C: ∫_{A×B} (W-c) = 0 for all measurable A,B ⊆ S
          -- Sub-step: for disjoint nontrivial A ⊆ S: ∫_{A×(S\A)} = 0
          -- Proof: ∫_{A×S} = ∫_{A×A} + ∫_{A×(S\A)} (by additivity)
          -- ∫_{A×S} = 0 (Step B), ∫_{A×A} = 0 (Step A, if nontrivial). So ∫_{A×(S\A)} = 0.
          have h_rect_zero : ∀ A B : Set α, MeasurableSet A → MeasurableSet B →
              A ⊆ S → B ⊆ S →
              ∫ p in A ×ˢ B, (W.toAEEqFun p - c) ∂(μ.prod μ) = 0 := by
            intro A B hA_meas hB_meas hA_sub hB_sub
            -- Decompose: A×B = (A∩B)×(A∩B) ∪ (A∩B)×(B\A) ∪ (A\B)×(A∩B) ∪ (A\B)×(B\A)
            -- Each piece has ∫ = 0.
            -- For self-pieces (C×C where C ⊆ S nontrivial): use h_diag_zero.
            -- For cross-pieces (C×D where C,D disjoint, both ⊆ S, nontrivial):
            --   ∫_{C×S} = ∫_{C×C} + ∫_{C×(S\C)} = 0 + ∫_{C×(S\C)} = 0
            --   Since ∫_{C×S} = 0 (Step B), ∫_{C×(S\C)} = 0.
            --   D ⊆ S\C, so ∫_{C×D} ⊆ ∫_{C×(S\C)} can be decomposed further.
            --   Actually, ∫_{C×(S\C)} = 0 and D ⊆ S\C doesn't directly give ∫_{C×D} = 0.
            --   But: decompose S\C into D' = D∩(S\C) and (S\C)\D'. If D ⊆ S\C, D' = D.
            --   ∫_{C×D} + ∫_{C×((S\C)\D)} = ∫_{C×(S\C)} = 0.
            --   Hmm, both could be nonzero.
            -- Better approach: use polarization on the square integral condition.
            -- For disjoint C,D ⊆ S with C,D nontrivial and μ(S\(C∪D)) > 0:
            --   ∫_{(C∪D)×(C∪D)} = 0 (from h_diag_zero, since C∪D ⊆ S nontrivial with complement)
            --   = ∫_{C×C} + ∫_{C×D} + ∫_{D×C} + ∫_{D×D}
            --   = 0 + ∫_{C×D} + ∫_{D×C} + 0
            --   By W symmetry: ∫_{D×C} = ∫_{C×D} (swap + W(x,y)=W(y,x) a.e.)
            --   So 2∫_{C×D} = 0, hence ∫_{C×D} = 0.
            -- For C∪D = S (complement empty):
            --   ∫_{C×S} = ∫_{C×C} + ∫_{C×D} = 0 + ∫_{C×D} = 0 (from Step B)
            --   So ∫_{C×D} = 0.
            -- For zero-measure cases: ∫ over zero measure = 0.
            -- We handle all cases by splitting A×B into 4 pieces using A∩B and its complements.
            -- The 4 pieces are: (A∩B)×(A∩B), (A∩B)×(B\A), (A\B)×(A∩B), (A\B)×(B\A)
            -- These are disjoint and cover A×B.
            have hAB := hA_meas.inter hB_meas
            have hAdB := hA_meas.diff hB_meas
            have hBdA := hB_meas.diff hA_meas
            -- Helper: ∫_{C×D} = 0 for disjoint C,D ⊆ S with both nontrivial
            have h_disj_zero : ∀ C D : Set α, MeasurableSet C → MeasurableSet D →
                C ⊆ S → D ⊆ S → Disjoint C D → μ C ≠ 0 → μ D ≠ 0 →
                ∫ p in C ×ˢ D, (W.toAEEqFun p - c) ∂(μ.prod μ) = 0 := by
              intro C D hC_meas hD_meas hC_sub hD_sub hCD_disj hμC hμD
              by_cases hμSC : μ (S \ C) = 0
              · -- C =ᵐ S, so D has zero measure (D ⊆ S\C up to null set)
                have : μ D = 0 := by
                  apply measure_mono_null (fun x hxD => _)
                  · exact hμSC
                  · intro x hxD
                    exact ⟨hD_sub hxD, fun hxC => Set.disjoint_iff.mp hCD_disj ⟨hxC, hxD⟩⟩
                exact absurd this hμD
              · -- C nontrivial with complement: ∫_{C×C} = 0
                by_cases hμSD : μ (S \ D) = 0
                · -- D =ᵐ S: C has zero measure
                  have : μ C = 0 := by
                    apply measure_mono_null (fun x hxC => _)
                    · exact hμSD
                    · intro x hxC
                      exact ⟨hC_sub hxC, fun hxD => Set.disjoint_iff.mp hCD_disj ⟨hxC, hxD⟩⟩
                  exact absurd this hμC
                · -- Both C and D are nontrivial subsets of S with nontrivial complement
                  -- Use ∫_{C×S} = 0 and ∫_{C×C} = 0
                  have h1 := h_row_S_zero C hC_meas hC_sub
                  have h2 := h_diag_zero C hC_meas hC_sub hμC hμSC
                  -- ∫_{C×S} = ∫_{C×C} + ∫_{C×(S\C)}
                  have h_union : C ×ˢ S = (C ×ˢ C) ∪ (C ×ˢ (S \ C)) := by
                    rw [← Set.prod_union, Set.union_diff_cancel hC_sub]
                  have h_disj_prod : Disjoint (C ×ˢ C) (C ×ˢ (S \ C)) := by
                    rw [Set.disjoint_iff]; intro ⟨x, y⟩ ⟨⟨_, hy1⟩, ⟨_, hy2⟩⟩
                    exact hy2.2 hy1
                  have h3 : ∫ p in C ×ˢ (S \ C), (W.toAEEqFun p - c) ∂(μ.prod μ) = 0 := by
                    have := setIntegral_union h_disj_prod (hC_meas.prod (hS_meas.diff hC_meas))
                      (h_Wc_int_prod C C hC_meas hC_meas)
                      (h_Wc_int_prod C (S \ C) hC_meas (hS_meas.diff hC_meas))
                    rw [h_union] at h1; linarith
                  -- D ⊆ S\C, so ∫_{C×D} is part of ∫_{C×(S\C)}
                  -- Decompose S\C = D ∪ ((S\C)\D)
                  have hD_sub_SC : D ⊆ S \ C := by
                    intro x hxD
                    exact ⟨hD_sub hxD, fun hxC => Set.disjoint_iff.mp hCD_disj ⟨hxC, hxD⟩⟩
                  -- ∫_{C×(S\C)} = ∫_{C×D} + ∫_{C×((S\C)\D)}
                  have h_union2 : C ×ˢ (S \ C) = (C ×ˢ D) ∪ (C ×ˢ ((S \ C) \ D)) := by
                    rw [← Set.prod_union, Set.union_diff_cancel hD_sub_SC]
                  -- But we can't separate ∫_{C×D} from ∫_{C×((S\C)\D)} without more info.
                  -- Instead, use symmetry of W:
                  -- ∫_{D×C} (W(x,y)-c) = ∫_{C×D} (W(y,x)-c) (by swap)
                  -- = ∫_{C×D} (W(x,y)-c) (by W symmetry a.e.)
                  -- So ∫_{D×C} = ∫_{C×D}.
                  -- Also ∫_{D×S} = 0 (Step B), ∫_{D×D} = 0 (Step A).
                  -- ∫_{D×C} is part of ∫_{D×(S\D)}.
                  -- ∫_{D×S} = ∫_{D×D} + ∫_{D×(S\D)} = 0 + ∫_{D×(S\D)} = 0.
                  -- So ∫_{D×(S\D)} = 0. And C ⊆ S\D.
                  -- Similarly to above, ∫_{D×C} is part of ∫_{D×(S\D)} = 0, but we can't extract it.
                  -- NEW IDEA: Use polarization with the union C∪D.
                  by_cases hμSCUD : μ (S \ (C ∪ D)) = 0
                  · -- C ∪ D =ᵐ S
                    -- ∫_{C×D} = ∫_{C×S} - ∫_{C×C} - ∫_{C×(S\(C∪D))}
                    -- Since μ(S\(C∪D)) = 0, ∫_{C×(S\(C∪D))} = 0.
                    -- And ∫_{C×S} = 0, ∫_{C×C} = 0.
                    -- But ∫_{C×S} = ∫_{C×C} + ∫_{C×D} + ∫_{C×(S\(C∪D))}
                    -- Actually, S = C ∪ D ∪ (S\(C∪D)) up to null set.
                    -- S\C = D ∪ (S\(C∪D)) \ ... hmm, (S\C) = D ∪ ((S\C)\D) since D ⊆ S\C.
                    -- And ((S\C)\D) = S\(C∪D).
                    -- So ∫_{C×(S\C)} = ∫_{C×D} + ∫_{C×(S\(C∪D))}.
                    -- Since μ(S\(C∪D)) = 0: ∫_{C×(S\(C∪D))} = 0 (by measure zero).
                    -- And ∫_{C×(S\C)} = 0 (from h3).
                    -- So ∫_{C×D} = 0.
                    have h_rest_zero : ∫ p in C ×ˢ (S \ (C ∪ D)),
                        (W.toAEEqFun p - c) ∂(μ.prod μ) = 0 :=
                      setIntegral_measure_zero _ (by
                        rw [Measure.prod_prod]; simp [hμSCUD])
                    have h_eq_SC_D : (S \ C) \ D = S \ (C ∪ D) := by
                      ext x; simp [Set.mem_diff, Set.mem_union]; tauto
                    rw [h_eq_SC_D] at h_union2
                    have h_disj3 : Disjoint (C ×ˢ D) (C ×ˢ (S \ (C ∪ D))) := by
                      rw [Set.disjoint_iff]; intro ⟨_, y⟩ ⟨hy1, hy2⟩
                      exact hy2.2.2 (Or.inr hy1.2)
                    have := setIntegral_union h_disj3
                      (hC_meas.prod (hS_meas.diff (hC_meas.union hD_meas)))
                      (h_Wc_int_prod C D hC_meas hD_meas)
                      (h_Wc_int_prod C (S \ (C ∪ D)) hC_meas (hS_meas.diff (hC_meas.union hD_meas)))
                    rw [h_union2] at h3; linarith
                  · -- μ(S\(C∪D)) > 0: use polarization
                    -- C∪D is nontrivial subset of S with nontrivial complement
                    have hμCUD : μ (C ∪ D) ≠ 0 := by
                      intro h; exact hμC (measure_mono_null Set.subset_union_left h)
                    have hμSCUD' : μ (S \ (C ∪ D)) ≠ 0 := hμSCUD
                    have hCUD_sub : C ∪ D ⊆ S := Set.union_subset hC_sub hD_sub
                    have h_CUD := h_diag_zero (C ∪ D)
                      (hC_meas.union hD_meas) hCUD_sub hμCUD hμSCUD'
                    -- ∫_{(C∪D)×(C∪D)} = ∫_{C×C} + ∫_{C×D} + ∫_{D×C} + ∫_{D×D}
                    have h_expand : (C ∪ D) ×ˢ (C ∪ D) =
                        (C ×ˢ C) ∪ (C ×ˢ D) ∪ (D ×ˢ C) ∪ (D ×ˢ D) := by
                      ext ⟨x, y⟩; simp [Set.mem_prod, Set.mem_union]; tauto
                    -- The 4 pieces are pairwise disjoint (since C and D are disjoint)
                    have h_CC_int := h_Wc_int_prod C C hC_meas hC_meas
                    have h_CD_int := h_Wc_int_prod C D hC_meas hD_meas
                    have h_DC_int := h_Wc_int_prod D C hD_meas hC_meas
                    have h_DD_int := h_Wc_int_prod D D hD_meas hD_meas
                    -- Integral over union of 4 disjoint pieces
                    have h_sum : ∫ p in (C ∪ D) ×ˢ (C ∪ D), (W.toAEEqFun p - c) ∂(μ.prod μ) =
                        ∫ p in C ×ˢ C, (W.toAEEqFun p - c) ∂(μ.prod μ) +
                        ∫ p in C ×ˢ D, (W.toAEEqFun p - c) ∂(μ.prod μ) +
                        ∫ p in D ×ˢ C, (W.toAEEqFun p - c) ∂(μ.prod μ) +
                        ∫ p in D ×ˢ D, (W.toAEEqFun p - c) ∂(μ.prod μ) := by
                      rw [h_expand]
                      have d1 : Disjoint (C ×ˢ C) (C ×ˢ D) := by
                        rw [Set.disjoint_iff]; intro ⟨_, y⟩ ⟨⟨_, hy1⟩, ⟨_, hy2⟩⟩
                        exact Set.disjoint_iff.mp hCD_disj ⟨hy1, hy2⟩
                      have d2 : Disjoint (C ×ˢ C ∪ C ×ˢ D) (D ×ˢ C) := by
                        rw [Set.disjoint_iff]; intro ⟨x, _⟩ ⟨hx1, hx2⟩
                        rcases hx1 with ⟨hxC, _⟩ | ⟨hxC, _⟩ <;>
                          exact Set.disjoint_iff.mp hCD_disj ⟨hxC, hx2.1⟩
                      have d3 : Disjoint (C ×ˢ C ∪ C ×ˢ D ∪ D ×ˢ C) (D ×ˢ D) := by
                        rw [Set.disjoint_iff]; intro ⟨x, y⟩ ⟨hx1, hx2⟩
                        rcases hx1 with (⟨hxC, _⟩ | ⟨hxC, _⟩) | ⟨_, hyC⟩
                        · exact Set.disjoint_iff.mp hCD_disj ⟨hxC, hx2.1⟩
                        · exact Set.disjoint_iff.mp hCD_disj ⟨hxC, hx2.1⟩
                        · exact Set.disjoint_iff.mp hCD_disj ⟨hyC, hx2.2⟩
                      conv_lhs => rw [setIntegral_union d3 (hD_meas.prod hD_meas)
                        ((h_CC_int.union h_CD_int).union h_DC_int) h_DD_int]
                      conv_lhs => rw [setIntegral_union d2 (hD_meas.prod hC_meas)
                        (h_CC_int.union h_CD_int) h_DC_int]
                      conv_lhs => rw [setIntegral_union d1 (hC_meas.prod hD_meas) h_CC_int h_CD_int]
                    -- ∫_{D×C} = ∫_{C×D} by W symmetry
                    have h_swap : ∫ p in D ×ˢ C, (W.toAEEqFun p - c) ∂(μ.prod μ) =
                        ∫ p in C ×ˢ D, (W.toAEEqFun p - c) ∂(μ.prod μ) := by
                      rw [← setIntegral_prod_swap]
                      refine setIntegral_congr_ae (hC_meas.prod hD_meas) ?_
                      filter_upwards [W.symm_ae] with p hp _
                      rw [hp]
                    -- From h_sum, h2, h_diag_zero D, and h_swap:
                    have h_CC := h2
                    have hμSD : μ (S \ D) ≠ 0 := by
                      intro h; exact hμC (measure_mono_null (show C ⊆ S \ D from
                        fun x hx => ⟨hC_sub hx,
                        fun hxD => Set.disjoint_iff.mp hCD_disj ⟨hx, hxD⟩⟩) h)
                    have h_DD := h_diag_zero D hD_meas hD_sub hμD hμSD
                    rw [h_CC, h_DD, h_swap] at h_sum
                    linarith [h_CUD]
            -- Now prove the rectangle identity for general subsets
            -- Decompose A×B using A∩B, A\B, B\A
            -- A×B = (A∩B)×(A∩B) ∪ (A∩B)×(B\A) ∪ (A\B)×(A∩B) ∪ (A\B)×(B\A)
            -- For each piece: either μ = 0 (trivial) or use h_disj_zero / h_diag_zero
            -- Set pieces
            set AB := A ∩ B with hAB_def_local
            set AdB := A \ B with hAdB_def_local
            set BdA := B \ A with hBdA_def_local
            -- Each piece ⊆ S
            have hAB_sub : AB ⊆ S := fun x hx => hA_sub hx.1
            have hAdB_sub : AdB ⊆ S := fun x hx => hA_sub hx.1
            have hBdA_sub : BdA ⊆ S := fun x hx => hB_sub hx.1
            -- Disjointness conditions
            have h_AB_BdA_disj : Disjoint AB BdA := by
              rw [Set.disjoint_iff]; intro x ⟨hx1, hx2⟩; exact hx2.2 hx1.1
            have h_AdB_AB_disj : Disjoint AdB AB := by
              rw [Set.disjoint_iff]; intro x ⟨hx1, hx2⟩; exact hx1.2 hx2.2
            have h_AdB_BdA_disj : Disjoint AdB BdA := by
              rw [Set.disjoint_iff]; intro x ⟨hx1, hx2⟩; exact hx2.2 hx1.1
            -- A×B = AB×AB ∪ AB×BdA ∪ AdB×AB ∪ AdB×BdA
            have h_decomp : A ×ˢ B = (AB ×ˢ AB) ∪ (AB ×ˢ BdA) ∪ (AdB ×ˢ AB) ∪ (AdB ×ˢ BdA) := by
              ext ⟨x, y⟩
              simp only [Set.mem_prod, Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
              constructor
              · intro ⟨hxA, hyB⟩
                by_cases hxB : x ∈ B
                · by_cases hyA : y ∈ A
                  · exact Or.inl (Or.inl (Or.inl ⟨⟨hxA, hxB⟩, hyA, hyB⟩))
                  · exact Or.inl (Or.inl (Or.inr ⟨⟨hxA, hxB⟩, hyB, hyA⟩))
                · by_cases hyA : y ∈ A
                  · exact Or.inl (Or.inr ⟨⟨hxA, hxB⟩, hyA, hyB⟩)
                  · exact Or.inr ⟨⟨hxA, hxB⟩, hyB, hyA⟩
              · intro h
                rcases h with ((⟨⟨hxA, _⟩, _, hyB⟩ | ⟨⟨hxA, _⟩, hyB, _⟩) |
                    ⟨⟨hxA, _⟩, _, hyB⟩) | ⟨⟨hxA, _⟩, hyB, _⟩ <;> exact ⟨hxA, hyB⟩
            -- Helper for integral over each piece
            have h_piece_zero : ∀ C D : Set α, MeasurableSet C → MeasurableSet D →
                C ⊆ S → D ⊆ S → Disjoint C D →
                ∫ p in C ×ˢ D, (W.toAEEqFun p - c) ∂(μ.prod μ) = 0 := by
              intro C D hC_meas hD_meas hC_sub hD_sub hCD_disj
              by_cases hμC : μ C = 0
              · exact setIntegral_measure_zero _ (by rw [Measure.prod_prod]; simp [hμC])
              · by_cases hμD : μ D = 0
                · exact setIntegral_measure_zero _ (by rw [Measure.prod_prod]; simp [hμD])
                · exact h_disj_zero C D hC_meas hD_meas hC_sub hD_sub hCD_disj hμC hμD
            have h_self_zero : ∀ C : Set α, MeasurableSet C → C ⊆ S →
                ∫ p in C ×ˢ C, (W.toAEEqFun p - c) ∂(μ.prod μ) = 0 := by
              intro C hC_meas hC_sub
              by_cases hμC : μ C = 0
              · exact setIntegral_measure_zero _ (by rw [Measure.prod_prod]; simp [hμC])
              · by_cases hμSC : μ (S \ C) = 0
                · -- C =ᵐ S: ∫_{C×C} = ∫_{S×S} (up to null set)
                  have hC_ae_S : C =ᵐ[μ] S :=
                    ae_eq_set.mpr ⟨by simp [Set.diff_eq_empty.mpr hC_sub], hμSC⟩
                  have h_ae : C ×ˢ C =ᵐ[μ.prod μ] S ×ˢ S :=
                    Measure.set_prod_ae_eq hC_ae_S hC_ae_S
                  rw [setIntegral_congr_set h_ae]
                  exact h_row_S_zero S hS_meas Subset.rfl
                · exact h_diag_zero C hC_meas hC_sub hμC hμSC
            -- Combine the 4 pieces
            have d1 : Disjoint (AB ×ˢ AB) (AB ×ˢ BdA) := by
              rw [Set.disjoint_iff]; intro ⟨_, y⟩ ⟨⟨_, hy1⟩, ⟨_, hy2⟩⟩
              exact hy2.2 hy1.1
            have d2 : Disjoint (AB ×ˢ AB ∪ AB ×ˢ BdA) (AdB ×ˢ AB) := by
              rw [Set.disjoint_iff]; intro ⟨x, _⟩ ⟨hx1, hx2⟩
              rcases hx1 with ⟨hxAB, _⟩ | ⟨hxAB, _⟩ <;> exact hx2.1.2 hxAB.2
            have d3 : Disjoint (AB ×ˢ AB ∪ AB ×ˢ BdA ∪ AdB ×ˢ AB) (AdB ×ˢ BdA) := by
              rw [Set.disjoint_iff]; intro ⟨x, y⟩ ⟨hx1, hx2⟩
              rcases hx1 with (⟨hxAB, _⟩ | ⟨hxAB, _⟩) | ⟨_, hyAB⟩
              · exact hx2.1.2 hxAB.2
              · exact hx2.1.2 hxAB.2
              · exact hx2.2.2 hyAB.1
            rw [h_decomp]
            rw [setIntegral_union d3 (hAdB.prod hBdA)
              (((h_Wc_int_prod AB AB hAB hAB).union
                (h_Wc_int_prod AB BdA hAB hBdA)).union
                (h_Wc_int_prod AdB AB hAdB hAB))
              (h_Wc_int_prod AdB BdA hAdB hBdA)]
            rw [setIntegral_union d2 (hAdB.prod hAB)
              ((h_Wc_int_prod AB AB hAB hAB).union
                (h_Wc_int_prod AB BdA hAB hBdA))
              (h_Wc_int_prod AdB AB hAdB hAB)]
            rw [setIntegral_union d1 (hAB.prod hBdA)
              (h_Wc_int_prod AB AB hAB hAB) (h_Wc_int_prod AB BdA hAB hBdA)]
            rw [h_self_zero AB hAB hAB_sub,
                h_piece_zero AB BdA hAB hBdA hAB_sub hBdA_sub h_AB_BdA_disj,
                h_piece_zero AdB AB hAdB hAB hAdB_sub hAB_sub h_AdB_AB_disj,
                h_piece_zero AdB BdA hAdB hBdA hAdB_sub hBdA_sub h_AdB_BdA_disj]
            ring
          -- Step D: Apply π-λ to show W = c a.e. on S × S
          -- ∫_{A×B} (W-c) dν = 0 for all measurable A, B (restricted to S)
          have h_rect_bochner_zero : ∀ A B : Set α, MeasurableSet A → MeasurableSet B →
              ∫ p in A ×ˢ B, (W.toAEEqFun p - c) ∂ν = 0 := by
            intro A B hA_meas hB_meas
            rw [hν_def, Measure.prod_restrict]
            rw [Measure.restrict_restrict (hA_meas.prod hB_meas)]
            rw [Set.prod_inter_prod]
            exact h_rect_zero (A ∩ S) (B ∩ S) (hA_meas.inter hS_meas) (hB_meas.inter hS_meas)
              Set.inter_subset_right Set.inter_subset_right
          -- W = c a.e. on ν (same π-λ argument as S≠T case)
          have h_ae_zero : (fun p => W.toAEEqFun p - c) =ᵐ[ν] 0 := by
            have h_f_int : Integrable (fun p => W.toAEEqFun p - c) ν := by
              rw [hν_def, Measure.prod_restrict]
              apply Measure.integrableOn_of_bounded (M := 1)
              · rw [Measure.prod_prod S S]
                exact (ENNReal.mul_lt_top (measure_lt_top μ S) (measure_lt_top μ S)).ne
              · exact (W.toAEEqFun.measurable.sub measurable_const).aestronglyMeasurable
              · filter_upwards [ae_restrict_of_ae W.ae_mem_Icc] with p hp
                simp only [Real.norm_eq_abs, abs_le]
                have hc_mem := rectAverage_mem_Icc W S S hS_meas hS_meas
                constructor <;> nlinarith [hp.1, hp.2, hc_mem.1, hc_mem.2]
            apply h_f_int.ae_eq_zero_of_forall_setIntegral_eq_zero
            intro E hE _
            set C := {s : Set α | MeasurableSet s}
            have h_gen : (inferInstance : MeasurableSpace (α × α)) =
                MeasurableSpace.generateFrom (Set.image2 (· ×ˢ ·) C C) :=
              (generateFrom_eq_prod
                MeasurableSpace.generateFrom_measurableSet
                MeasurableSpace.generateFrom_measurableSet
                isCountablySpanning_measurableSet isCountablySpanning_measurableSet).symm
            have h_pi : IsPiSystem (Set.image2 (· ×ˢ ·) C C) :=
              IsPiSystem.prod
                (fun _ ha _ hb _ => MeasurableSet.inter ha hb)
                (fun _ ha _ hb _ => MeasurableSet.inter ha hb)
            exact MeasurableSpace.induction_on_inter h_gen h_pi
              (by simp only [Measure.restrict_empty, integral_zero_measure])
              (fun E' hE' => by
                obtain ⟨A, hA, B, hB, rfl⟩ := Set.mem_image2.mp hE'
                exact h_rect_bochner_zero A B hA hB)
              (fun E' hE'_meas hE'_zero => by
                have h_total : ∫ p, (W.toAEEqFun p - c) ∂ν = 0 := by
                  rw [hν_def, Measure.prod_restrict]
                  exact h_row_S_zero S hS_meas Subset.rfl
                have := integral_add_compl hE'_meas h_f_int; linarith)
              (fun s hs_disj hs_meas hs_zero => by
                rw [integral_iUnion hs_meas hs_disj h_f_int.integrableOn]; simp [hs_zero])
              E hE
          -- Step E: ∫_S ∫_S (W-c)² = 0, contradicting h_within_pos
          have h_sq_zero : ∫ x in S, (∫ y in S, (W.toAEEqFun (x, y) - c) ^ 2 ∂μ) ∂μ = 0 := by
            have h_sq_ae : (fun p => (W.toAEEqFun p - c) ^ 2) =ᵐ[ν] 0 := by
              filter_upwards [h_ae_zero] with p hp
              simp only [Pi.zero_apply] at hp ⊢; rw [hp]; ring
            have h_int : Integrable (fun p => (W.toAEEqFun p - c) ^ 2) ν := by
              rw [hν_def, Measure.prod_restrict]
              apply Measure.integrableOn_of_bounded (M := 1)
              · rw [Measure.prod_prod S S]
                exact (ENNReal.mul_lt_top (measure_lt_top μ S) (measure_lt_top μ S)).ne
              · exact (W.toAEEqFun.measurable.sub measurable_const).pow_const 2
                  |>.aestronglyMeasurable
              · filter_upwards [ae_restrict_of_ae W.ae_mem_Icc] with p hp
                simp only [Real.norm_eq_abs]
                rw [abs_of_nonneg (sq_nonneg _)]
                have hc_mem := rectAverage_mem_Icc W S S hS_meas hS_meas
                nlinarith [hp.1, hp.2, hc_mem.1, hc_mem.2]
            have h_int_zero : ∫ p, (W.toAEEqFun p - c) ^ 2 ∂ν = 0 :=
              integral_eq_zero_of_ae h_sq_ae
            rw [show ∫ x in S, (∫ y in S, (W.toAEEqFun (x, y) - c) ^ 2 ∂μ) ∂μ =
                ∫ p, (W.toAEEqFun p - c) ^ 2 ∂ν from
              (integral_prod _ h_int).symm]
            exact h_int_zero
          linarith
        -- Part 2: Build Q = splitPart P S B and show energy increase
        obtain ⟨B, hB_meas, hB_sub, hμB, hμSB, h_rectAvg_ne⟩ := h_good_cut
        -- Q = splitPart P S B
        let Q := MeasurablePartition.splitPart P S hS_mem B hB_meas hB_sub hμB hμSB
        use Q
        refine ⟨?_, ?_, ?_⟩
        -- (a) Q refines P
        · exact MeasurablePartition.splitPart_refines P S hS_mem B hB_meas hB_sub hμB hμSB
        -- (b) Q.parts.card ≤ 2 * P.parts.card
        · have h_card : Q.parts.card ≤ P.parts.card + 1 :=
            MeasurablePartition.splitPart_card P S hS_mem B hB_meas hB_sub hμB hμSB
          have h_P_nonempty : 1 ≤ P.parts.card := Finset.one_le_card.mpr ⟨S, hS_mem⟩
          omega
        -- (c) Energy strictly increases
        -- The correction from energy_splitPart_ge gives >= but the correction sum may be 0.
        -- We prove strict inequality using the column-split Jensen contribution.
        -- Key facts: rectAvg(B,S) = c and rectAvg(S\B,S) = c (from tAvg_S = c a.e. on S),
        -- so the T=S term in the correction is 0. But the column-split contribution
        -- includes the term eR(B,B) + eR(B,S\B) - eR(B,S) = delta'(B) > 0
        -- (since rectAvg(B,B) ≠ rectAvg(S\B,B), which follows from rectAvg(B,B) ≠ c).
        · -- Step 1: energy(Q) ≥ energy(P) + correction_row
          have h_ge := energy_splitPart_ge W P S hS_mem B hB_meas hB_sub hμB hμSB
          -- Step 2: The correction_row ≥ 0 (and may equal 0)
          have h_corr_nonneg : P.parts.sum (fun T =>
              (μ T).toReal * (μ B).toReal * (μ (S \ B)).toReal / (μ S).toReal *
                (rectAverage W B T - rectAverage W (S \ B) T) ^ 2) ≥ 0 := by
            apply Finset.sum_nonneg; intro T _
            apply mul_nonneg
            · exact div_nonneg (mul_nonneg (mul_nonneg ENNReal.toReal_nonneg
                ENNReal.toReal_nonneg) ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
            · exact sq_nonneg _
          -- Step 3: Show column-split gives strictly positive contribution
          -- By energy_rect_split: eR(B,T) + eR(S\B,T) - eR(S,T) = delta(T)
          -- The column-split version: eR(U,B) + eR(U,S\B) - eR(U,S) = delta'(U)
          -- where delta'(U) = mu(U)*mu(B)*mu(S\B)/mu(S)*(rectAvg(U,B)-rectAvg(U,S\B))^2
          -- For U=B: delta'(B) = mu(B)^2*mu(S\B)/mu(S)*(rectAvg(B,B)-rectAvg(B,S\B))^2
          -- We need rectAvg(B,B) ≠ rectAvg(B,S\B), which follows from rectAvg(B,B) ≠ c.
          -- Proof: rectAvg(B,S) = c (from tAvg_S=c a.e. on S).
          -- rectAvg(B,S) = (mu(B)*rectAvg(B,B) + mu(S\B)*rectAvg(B,S\B)) / mu(S)
          -- (by splitting the integral over S = B ∪ (S\B)).
          -- If rectAvg(B,B) = rectAvg(B,S\B) = d, then d = c, contradicting rectAvg(B,B) ≠ c.
          set S₂ := S \ B with hS₂_def_local
          have hS₂_meas : MeasurableSet S₂ := hS_meas.diff hB_meas
          have hμS_top_local : μ S ≠ ⊤ := (measure_lt_top μ S).ne
          have hμB_top : μ B ≠ ⊤ := (measure_lt_top μ B).ne
          have hμS₂_top : μ S₂ ≠ ⊤ := (measure_lt_top μ S₂).ne
          have hμB_real_pos : (0 : ℝ) < (μ B).toReal := ENNReal.toReal_pos hμB hμB_top
          have hμS₂_real_pos : (0 : ℝ) < (μ S₂).toReal := ENNReal.toReal_pos hμSB hμS₂_top
          -- rectAvg(B,S) = c
          have h_rectAvg_BS : rectAverage W B S = c := by
            -- tAvg_S = c a.e. on S, B ⊆ S, so rectAvg(B,S) = (μB)⁻¹ ∫_B tAvg_S = c
            rw [show rectAverage W B S = (μ B).toReal⁻¹ * ∫ x in B, tAverage W S x ∂μ from
              (tAverage_integral_eq_rectAverage W B S hB_meas hS_meas hμB hμS).symm]
            have h_ae_B : tAverage W S =ᵐ[μ.restrict B] fun _ => c :=
              h_tAvg_S_ae.filter_mono (ae_mono (Measure.restrict_mono hB_sub le_rfl))
            rw [integral_congr_ae h_ae_B, setIntegral_const, smul_eq_mul]
            simp [Measure.real]; field_simp [ne_of_gt hμB_real_pos]
          -- rectAvg(B,B) ≠ rectAvg(B,S\B)
          have h_ne : rectAverage W B B ≠ rectAverage W B S₂ := by
            intro h_eq
            -- If rectAvg(B,B) = rectAvg(B,S\B) = d, then d = rectAvg(B,S) = c
            -- by splitting: ∫_{B×S} W = ∫_{B×B} W + ∫_{B×S₂} W
            -- ⟹ μ(S)*rectAvg(B,S) = μ(B)*rectAvg(B,B) + μ(S₂)*rectAvg(B,S₂)
            -- ⟹ μ(S)*c = μ(B)*d + μ(S₂)*d = (μ(B)+μ(S₂))*d = μ(S)*d
            -- ⟹ d = c, contradicting rectAvg(B,B) ≠ c.
            apply h_rectAvg_ne
            -- Show rectAvg(B,B) = c from h_eq and h_rectAvg_BS
            have h_split : (μ S).toReal * rectAverage W B S =
                (μ B).toReal * rectAverage W B B + (μ S₂).toReal * rectAverage W B S₂ := by
              rw [show rectAverage W B S = (μ B).toReal⁻¹ * (μ S).toReal⁻¹ *
                  ∫ p in B ×ˢ S, W.toAEEqFun p ∂(μ.prod μ) from by
                unfold rectAverage; simp [hμB, hμS, dif_neg]]
              rw [show rectAverage W B B = (μ B).toReal⁻¹ * (μ B).toReal⁻¹ *
                  ∫ p in B ×ˢ B, W.toAEEqFun p ∂(μ.prod μ) from by
                unfold rectAverage; simp [hμB, dif_neg]]
              rw [show rectAverage W B S₂ = (μ B).toReal⁻¹ * (μ S₂).toReal⁻¹ *
                  ∫ p in B ×ˢ S₂, W.toAEEqFun p ∂(μ.prod μ) from by
                unfold rectAverage; simp [hμB, hμSB, dif_neg]]
              have h_union : B ×ˢ S = (B ×ˢ B) ∪ (B ×ˢ S₂) := by
                rw [← Set.prod_union, Set.union_diff_cancel hB_sub]
              have h_disj : Disjoint (B ×ˢ B) (B ×ˢ S₂) := by
                rw [Set.disjoint_iff]; intro ⟨_, y⟩ ⟨⟨_, hy1⟩, ⟨_, hy2⟩⟩; exact hy2.2 hy1
              rw [h_union, setIntegral_union h_disj (hB_meas.prod hS₂_meas)
                (SymmKernel.graphon_integrable W).integrableOn
                (SymmKernel.graphon_integrable W).integrableOn]
              field_simp [ne_of_gt hμB_real_pos, ne_of_gt hμS₂_real_pos,
                ne_of_gt hμS_real_pos]
            rw [h_rectAvg_BS, ← h_eq] at h_split
            have hμ_add : (μ S).toReal = (μ B).toReal + (μ S₂).toReal := by
              rw [show S = B ∪ S₂ from (Set.union_diff_cancel hB_sub).symm]
              rw [measure_union Set.disjoint_sdiff_right hS₂_meas]
              exact ENNReal.toReal_add hμB_top hμS₂_top
            -- h_split: μS * c = μB * rectAvg(B,B) + μS₂ * rectAvg(B,B)
            -- = (μB + μS₂) * rectAvg(B,B) = μS * rectAvg(B,B)
            -- h_split (after rw): μS * c = μB * rectAvg(B,B) + μS₂ * rectAvg(B,B)
            -- = (μB + μS₂) * rectAvg(B,B) = μS * rectAvg(B,B)
            -- Substitute hμ_add into h_split to get linear equation
            have h_rhs : (μ B).toReal * rectAverage W B B + (μ S₂).toReal * rectAverage W B B =
                (μ S).toReal * rectAverage W B B := by rw [hμ_add]; ring
            have hμS_pos_local : (0 : ℝ) < (μ S).toReal := by rw [hμ_add]; linarith
            have h_eq2 : (μ S).toReal * c = (μ S).toReal * rectAverage W B B := by linarith
            exact (mul_left_cancel₀ (ne_of_gt hμS_pos_local) h_eq2).symm
          -- rectAvg(B,B) ≠ rectAvg(S\B,B) (by symmetry and the above)
          have h_ne' : rectAverage W B B ≠ rectAverage W S₂ B := by
            intro h_eq
            apply h_ne
            -- rectAvg(B,S₂) = rectAvg(S₂,B) by symmetry = rectAvg(B,B) by h_eq
            rw [rectAverage_symm W B S₂ hB_meas hS₂_meas]; exact h_eq
          -- The column-split delta for U=B and splitting S (second arg) into B and S\B:
          -- eR(B,B) + eR(S\B,B) - eR(S,B) = delta_col(B) > 0
          -- This equals mu(B)*mu(B)*mu(S\B)/mu(S)*(rectAvg(B,B)-rectAvg(S\B,B))^2
          have h_delta_col_B := energy_rect_split W S B B hS_meas hB_meas hB_meas hB_sub
            hμS hμB hμB hμSB
          -- delta_col(B) > 0
          have h_delta_col_pos : (μ B).toReal * (μ B).toReal * (μ S₂).toReal /
              (μ S).toReal * (rectAverage W B B - rectAverage W S₂ B) ^ 2 > 0 := by
            apply mul_pos
            · exact div_pos (mul_pos (mul_pos hμB_real_pos hμB_real_pos) hμS₂_real_pos)
                hμS_real_pos
            · exact sq_pos_of_ne_zero (sub_ne_zero.mpr h_ne')
          -- Prove energy(Q) > energy(P) by showing the column-split contribution
          -- includes a strictly positive term.
          -- We replicate the structure of energy_splitPart_ge but extract the
          -- step C (column correction) contribution, which includes delta_col(B) > 0.
          -- Setup (matching energy_splitPart_ge proof structure)
          classical
          set E := P.parts.erase S with hE_def
          have hS_notin_E : S ∉ E := by rw [hE_def]; simp
          have hE_sub : E ⊆ P.parts := by rw [hE_def]; exact Finset.erase_subset S P.parts
          have hP_parts : P.parts = insert S E := by
            rw [hE_def]; exact (Finset.insert_erase hS_mem).symm
          have hP_eq : P.parts = E ∪ {S} := by
            rw [hP_parts, Finset.insert_eq]; exact Finset.union_comm _ _
          -- B ≠ S₂
          have hB_ne_S₂ : B ≠ S₂ := by
            intro h; rw [hS₂_def_local] at h
            have : B ⊆ S \ B := h ▸ Subset.rfl
            exact hμB (measure_mono_null (fun x hx => ((this hx).2 hx).elim) (measure_empty))
          -- B, S₂ ∉ E
          have hB_notin_E : B ∉ E := by
            intro h
            have h1 := (Finset.mem_erase.mp h).1; have h2 := (Finset.mem_erase.mp h).2
            exact hμB (measure_mono_null (Set.disjoint_iff_inter_eq_empty.mp
              (P.pairwiseDisjoint h2 hS_mem h1) ▸ Set.subset_inter Subset.rfl hB_sub)
              (measure_empty))
          have hS₂_notin_E : S₂ ∉ E := by
            intro h
            have h1 := (Finset.mem_erase.mp h).1; have h2 := (Finset.mem_erase.mp h).2
            exact hμSB (measure_mono_null (Set.disjoint_iff_inter_eq_empty.mp
              (P.pairwiseDisjoint h2 hS_mem h1) ▸ Set.subset_inter Subset.rfl Set.diff_subset)
              (measure_empty))
          have hE_disj_S : Disjoint E ({B, S₂} : Finset (Set α)) := by
            rw [Finset.disjoint_left]; intro x hx hx2
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
            rcases hx2 with rfl | rfl; exact hB_notin_E hx; exact hS₂_notin_E hx
          have hE_disj_S_single : Disjoint E ({S} : Finset (Set α)) := by
            rw [Finset.disjoint_left]; intro x hx hx2
            simp only [Finset.mem_singleton] at hx2; rw [hx2] at hx; exact hS_notin_E hx
          have hQ_parts : Q.parts = E ∪ ({B, S₂} : Finset (Set α)) := by
            simp only [Q, MeasurablePartition.splitPart, hE_def, hS₂_def_local]
          have hQ_meas : ∀ T ∈ Q.parts, MeasurableSet T := Q.measurable_parts
          -- eR symmetry
          have h_eR_symm : ∀ A' B' : Set α, MeasurableSet A' → MeasurableSet B' →
              energyRect W A' B' = energyRect W B' A' := by
            intro A' B' hA' hB'; unfold energyRect
            rw [rectAverage_symm W A' B' hA' hB']; ring
          -- Row split identity: eR(B,T) + eR(S₂,T) - eR(S,T) = delta_row(T)
          have h_split_all : ∀ T, MeasurableSet T →
              energyRect W B T + energyRect W S₂ T - energyRect W S T =
              (μ T).toReal * (μ B).toReal * (μ S₂).toReal / (μ S).toReal *
                (rectAverage W B T - rectAverage W S₂ T) ^ 2 := by
            intro T hT_meas
            by_cases hμT : μ T = 0
            · simp only [energyRect, show (μ T).toReal = 0 from by simp [hμT], zero_mul,
                mul_zero, add_zero, sub_zero, zero_div]
            · exact energy_rect_split W S T B hS_meas hT_meas hB_meas hB_sub hμS hμT hμB hμSB
          -- Column split: eR(U,B) + eR(U,S₂) - eR(U,S) ≥ 0 for all measurable U
          have h_col_nonneg : ∀ U, MeasurableSet U →
              energyRect W U B + energyRect W U S₂ - energyRect W U S ≥ 0 := by
            intro U hU_meas
            rw [h_eR_symm U B hU_meas hB_meas, h_eR_symm U S₂ hU_meas hS₂_meas,
              h_eR_symm U S hU_meas hS_meas]
            have := h_split_all U hU_meas
            linarith [mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg
              (show (0 : ℝ) ≤ (μ U).toReal from ENNReal.toReal_nonneg)
              (show (0 : ℝ) ≤ (μ B).toReal from ENNReal.toReal_nonneg))
              (show (0 : ℝ) ≤ (μ S₂).toReal from ENNReal.toReal_nonneg))
              (show (0 : ℝ) ≤ (μ S).toReal from ENNReal.toReal_nonneg))
              (sq_nonneg (rectAverage W B U - rectAverage W S₂ U))]
          -- g(T) = Σ_{U∈Q} eR(U,T)
          set g : Set α → ℝ := fun T => Q.parts.sum (fun U => energyRect W U T) with hg_def
          -- energy(Q) = Σ_{T∈Q} g(T) (by sum_comm)
          have h_energy_Q : energy W Q = Q.parts.sum g := by
            show Q.parts.sum (fun S => Q.parts.sum (fun T =>
              (μ S).toReal * (μ T).toReal * (rectAverage W S T) ^ 2)) =
              Q.parts.sum (fun T => Q.parts.sum (fun U =>
              (μ U).toReal * (μ T).toReal * (rectAverage W U T) ^ 2))
            exact Finset.sum_comm
          -- energy(P) = Σ_{T∈P} Σ_{U∈P} eR(U,T) (by sum_comm)
          have h_energy_P : energy W P = P.parts.sum (fun T =>
              P.parts.sum (fun U => energyRect W U T)) := by
            show P.parts.sum (fun S => P.parts.sum (fun T =>
              (μ S).toReal * (μ T).toReal * (rectAverage W S T) ^ 2)) =
              P.parts.sum (fun T => P.parts.sum (fun U =>
              (μ U).toReal * (μ T).toReal * (rectAverage W U T) ^ 2))
            exact Finset.sum_comm
          -- Inner sum identity: Σ_{U∈Q} eR(U,T) = Σ_{U∈P} eR(U,T) + delta_row(T) for T ∈ P
          have h_inner : ∀ T' ∈ P.parts,
              Q.parts.sum (fun U => energyRect W U T') =
              P.parts.sum (fun U => energyRect W U T') +
              (μ T').toReal * (μ B).toReal * (μ S₂).toReal / (μ S).toReal *
                (rectAverage W B T' - rectAverage W S₂ T') ^ 2 := by
            intro T' hT'
            have hT'_meas := P.measurableSet_part hT'
            rw [hQ_parts, Finset.sum_union hE_disj_S, Finset.sum_insert (show B ∉ ({S₂} : Finset _) by simp [hB_ne_S₂]),
                Finset.sum_singleton]
            rw [hP_eq, Finset.sum_union hE_disj_S_single, Finset.sum_singleton]
            linarith [h_split_all T' hT'_meas]
          -- Σ_{T∈P} g(T) = energy(P) + correction_row
          have h_step_B : P.parts.sum g = energy W P +
              P.parts.sum (fun T' => (μ T').toReal * (μ B).toReal * (μ S₂).toReal /
                (μ S).toReal * (rectAverage W B T' - rectAverage W S₂ T') ^ 2) := by
            rw [h_energy_P, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun T' hT' => h_inner T' hT')
          -- energy(Q) = Σ_{T∈P} g(T) + [g(B) + g(S₂) - g(S)]
          have h_energy_decomp : energy W Q = P.parts.sum g + (g B + g S₂ - g S) := by
            rw [h_energy_Q, hQ_parts, Finset.sum_union hE_disj_S, Finset.sum_insert (show B ∉ ({S₂} : Finset _) by simp [hB_ne_S₂]),
                Finset.sum_singleton]
            rw [show P.parts.sum g = (E.sum g) + g S from by
              rw [hP_eq, Finset.sum_union hE_disj_S_single, Finset.sum_singleton]]
            ring
          -- g(B) + g(S₂) - g(S) ≥ delta_col(B) (extract the B-term from the sum)
          have h_col_sum : g B + g S₂ - g S =
              Q.parts.sum (fun U => energyRect W U B + energyRect W U S₂ - energyRect W U S) := by
            simp only [hg_def]; rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          -- B ∈ Q.parts
          have hB_in_Q : B ∈ Q.parts := by
            simp only [Q, MeasurablePartition.splitPart]
            exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
          -- The B-term in the column sum is delta_col(B) > 0
          have h_B_col_term : energyRect W B B + energyRect W B S₂ - energyRect W B S > 0 := by
            rw [h_eR_symm B S₂ hB_meas hS₂_meas, h_eR_symm B S hB_meas hS_meas]
            linarith [h_delta_col_B]
          -- The sum is ≥ the B-term (other terms are non-negative)
          have h_col_ge : g B + g S₂ - g S > 0 := by
            rw [h_col_sum]
            have h_nonneg : ∀ U ∈ Q.parts,
                0 ≤ energyRect W U B + energyRect W U S₂ - energyRect W U S := by
              intro U hU
              linarith [h_col_nonneg U (hQ_meas U hU)]
            linarith [(Finset.sum_pos_iff_of_nonneg h_nonneg).mpr ⟨B, hB_in_Q, by linarith⟩]
          -- Combine: energy(Q) > energy(P)
          rw [h_energy_decomp, h_step_B]
          linarith [h_corr_nonneg]
      · -- Sub-case S ≠ T
        -- Step 5a: Find a nontrivial measurable cut B ⊆ T with positive between-B variance.
        -- This combines existence of a nontrivial cut with its having positive I_B.
        --
        -- Mathematical argument:
        -- By contradiction, assume for all nontrivial B ⊆ T, I_B = ∫_S (tAvg_B - c)² = 0.
        -- Then for each B, tAvg_B(x) = c for a.e. x ∈ S, so ∫_B (W(x,y) - c) dy = 0 a.e.
        -- For finitely many B₁,...,Bₙ, the intersection of the full-measure sets still has
        -- full measure, so ∫_{Bᵢ} (W(x,y)-c) dy = 0 simultaneously for a.e. x.
        -- Since simple functions on T (with support in T) span a dense subspace of L²(T,μ|_T),
        -- and L²(T,μ|_T) is separable (finite measure), taking a countable dense set of
        -- simple functions and intersecting countably many full-measure sets:
        -- for a.e. x ∈ S, ⟨W(x,·)-c, φ⟩ = 0 for all φ ∈ L²(T), hence W(x,·) = c a.e. on T.
        -- This gives ∫_S ∫_T (W-c)² = 0, contradicting h_within_pos.
        have h_good_cut : ∃ B : Set α, MeasurableSet B ∧ B ⊆ T ∧ μ B ≠ 0 ∧ μ (T \ B) ≠ 0 ∧
            ∫ x in S, (tAverage W B x - c) ^ 2 ∂μ > 0 := by
          -- By contradiction: assume for all nontrivial B ⊆ T, the between-B variance is ≤ 0.
          by_contra h_neg
          push_neg at h_neg
          -- For all nontrivial B ⊆ T, tAvg_B = c a.e. on S (variance = 0)
          have h_tAvg_eq : ∀ B : Set α, MeasurableSet B → B ⊆ T → μ B ≠ 0 → μ (T \ B) ≠ 0 →
              tAverage W B =ᵐ[μ.restrict S] fun _ => c := by
            intro B hB_meas hB_sub hμB hμTB
            have h_le := h_neg B hB_meas hB_sub hμB hμTB
            have h_ge : ∫ x in S, (tAverage W B x - c) ^ 2 ∂μ ≥ 0 :=
              setIntegral_nonneg_of_ae_restrict (ae_of_all _ (fun _ => sq_nonneg _))
            have h_eq : ∫ x in S, (tAverage W B x - c) ^ 2 ∂μ = 0 := le_antisymm h_le h_ge
            have h_nonneg : 0 ≤ᵐ[μ.restrict S] fun x => (tAverage W B x - c) ^ 2 :=
              ae_of_all _ (fun _ => sq_nonneg _)
            have h_int : IntegrableOn (fun x => (tAverage W B x - c) ^ 2) S μ := by
              apply Measure.integrableOn_of_bounded (measure_lt_top μ S).ne
              · exact ((tAverage_measurable W B hB_meas).sub measurable_const).pow_const 2
                  |>.aestronglyMeasurable
              · filter_upwards [ae_restrict_of_ae (tAverage_ae_mem_Icc W B hB_meas)] with x hx
                simp only [Real.norm_eq_abs]
                have hc_mem := rectAverage_mem_Icc W S T hS_meas hT_meas
                calc |((tAverage W B x) - c) ^ 2|
                    = ((tAverage W B x) - c) ^ 2 := abs_of_nonneg (sq_nonneg _)
                  _ ≤ 1 := by nlinarith [hx.1, hx.2, hc_mem.1, hc_mem.2]
            have h_ae_zero := (setIntegral_eq_zero_iff_of_nonneg_ae h_nonneg h_int).mp h_eq
            filter_upwards [h_ae_zero] with x hx
            simp only [Pi.zero_apply] at hx
            linarith [sq_eq_zero_iff.mp hx]
          -- Integrability of W-slice: for a.e. x, W(x,·) is integrable on any set of finite measure
          have h_W_ae_ae := Measure.ae_ae_of_ae_prod W.ae_mem_Icc
          -- h_W_ae_ae : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, W(x,y) ∈ Icc 0 1
          -- Helper: W(x,·) is integrable on B' for a.e. x
          have h_slice_int : ∀ᵐ x ∂μ, ∀ B' : Set α, MeasurableSet B' →
              IntegrableOn (fun y => W.toAEEqFun (x, y)) B' μ := by
            filter_upwards [h_W_ae_ae,
              AEStronglyMeasurable.prodMk_left W.toAEEqFun.aestronglyMeasurable]
              with x hx hx_meas
            intro B' hB'_meas
            exact Measure.integrableOn_of_bounded (M := 1) (measure_lt_top μ B').ne hx_meas
              (by filter_upwards [ae_restrict_of_ae hx] with y hy
                  simp only [Real.norm_eq_abs, abs_le]
                  exact ⟨by linarith [hy.1], by linarith [hy.2]⟩)
          -- Key claim: ∫_T (W(x,y)-c) dy = 0 for a.e. x ∈ S
          have h_T_inner_zero :
              (fun x => ∫ y in T, (W.toAEEqFun (x, y) - c) ∂μ) =ᵐ[μ.restrict S] 0 := by
            filter_upwards [h_tAvg_T_ae, ae_restrict_of_ae h_slice_int] with x hx hx_int
            simp only [Pi.zero_apply]
            unfold tAverage at hx
            simp only [hμT, dif_neg, not_false_eq_true] at hx
            have h1 : ∫ y in T, W.toAEEqFun (x, y) ∂μ = c * (μ T).toReal := by
              field_simp [ne_of_gt hμT_real_pos] at hx ⊢; linarith
            rw [integral_sub (hx_int T hT_meas)
                (integrableOn_const (measure_lt_top μ T).ne)]
            rw [h1, setIntegral_const]; simp [Measure.real]; ring
          -- For all measurable B' ⊆ T, ∫_{B'} (W(x,y)-c) dy = 0 for a.e. x ∈ S
          have h_inner_zero : ∀ B' : Set α, MeasurableSet B' → B' ⊆ T →
              (fun x => ∫ y in B', (W.toAEEqFun (x, y) - c) ∂μ) =ᵐ[μ.restrict S] 0 := by
            intro B' hB'_meas hB'_sub
            by_cases hμB' : μ B' = 0
            · -- μ B' = 0: integral vanishes
              filter_upwards with x; simp only [Pi.zero_apply]
              exact setIntegral_measure_zero _ hμB'
            · by_cases hμTB' : μ (T \ B') = 0
              · -- B' =ᵐ T: use setIntegral_congr_set
                have h_ae_eq : B' =ᵐ[μ] T :=
                  ae_eq_set.mpr ⟨by simp [Set.diff_eq_empty.mpr hB'_sub], hμTB'⟩
                filter_upwards [h_T_inner_zero] with x hx
                simp only [Pi.zero_apply] at hx ⊢
                rwa [setIntegral_congr_set h_ae_eq]
              · -- Nontrivial: from h_tAvg_eq, tAvg_{B'} = c a.e., so ∫_{B'} (W-c) = 0 a.e.
                have h_ae := h_tAvg_eq B' hB'_meas hB'_sub hμB' hμTB'
                have hμB'_pos : (0 : ℝ) < (μ B').toReal :=
                  ENNReal.toReal_pos hμB' (measure_lt_top μ B').ne
                filter_upwards [h_ae, ae_restrict_of_ae h_slice_int] with x hx hx_int
                simp only [Pi.zero_apply]
                unfold tAverage at hx
                simp only [hμB', dif_neg, not_false_eq_true] at hx
                have h1 : ∫ y in B', W.toAEEqFun (x, y) ∂μ = c * (μ B').toReal := by
                  field_simp [ne_of_gt hμB'_pos] at hx ⊢; linarith
                rw [integral_sub (hx_int B' hB'_meas)
                    (integrableOn_const (measure_lt_top μ B').ne)]
                rw [h1, setIntegral_const]; simp [Measure.real]; ring
          -- Now apply π-λ to show W = c a.e. on S × T
          -- Define f₊ = ofReal(max(W-c, 0)) and f₋ = ofReal(max(c-W, 0))
          -- on the restricted product measure ν = (μ.restrict S).prod (μ.restrict T)
          set ν := (μ.restrict S).prod (μ.restrict T) with hν_def
          -- Step A: ∫_{A×B} (W-c) dν = 0 for all measurable A, B
          -- This follows from Fubini + h_inner_zero
          have h_rect_bochner_zero : ∀ A B : Set α, MeasurableSet A → MeasurableSet B →
              ∫ p in A ×ˢ B, (W.toAEEqFun p - c) ∂ν = 0 := by
            intro A B hA_meas hB_meas
            -- Rewrite using prod_restrict: ν = (μ.prod μ).restrict (S ×ˢ T)
            rw [hν_def, Measure.prod_restrict]
            rw [Measure.restrict_restrict (hA_meas.prod hB_meas)]
            rw [Set.prod_inter_prod]
            -- Now the integral is over (A ∩ S) ×ˢ (B ∩ T) w.r.t. μ.prod μ
            -- Apply Fubini
            have h_int : IntegrableOn (fun p => W.toAEEqFun p - c)
                ((A ∩ S) ×ˢ (B ∩ T)) (μ.prod μ) := by
              have h_meas_prod : (μ.prod μ) ((A ∩ S) ×ˢ (B ∩ T)) ≠ ⊤ := by
                rw [Measure.prod_prod (A ∩ S) (B ∩ T)]
                exact (ENNReal.mul_lt_top (measure_lt_top μ (A ∩ S))
                    (measure_lt_top μ (B ∩ T))).ne
              apply Measure.integrableOn_of_bounded (M := 1) h_meas_prod
              · exact (W.toAEEqFun.measurable.sub measurable_const).aestronglyMeasurable
              · filter_upwards [ae_restrict_of_ae W.ae_mem_Icc] with p hp
                simp only [Real.norm_eq_abs, abs_le]
                have hc_mem := rectAverage_mem_Icc W S T hS_meas hT_meas
                constructor <;> nlinarith [hp.1, hp.2, hc_mem.1, hc_mem.2]
            rw [setIntegral_prod _ h_int]
            -- ∫_{A∩S} [∫_{B∩T} (W(x,y)-c) dy] dx = 0
            -- The inner integral is 0 for a.e. x ∈ S (by h_inner_zero)
            have h_inner_ae := h_inner_zero (B ∩ T)
              (hB_meas.inter hT_meas) Set.inter_subset_right
            -- h_inner_ae : (fun x => ∫ y in B∩T, (W(x,y)-c) ∂μ) =ᵐ[μ.restrict S] 0
            -- Since A ∩ S ⊆ S, the a.e. statement restricts to A ∩ S
            have h_ae_AS : (fun x => ∫ y in B ∩ T, (W.toAEEqFun (x, y) - c) ∂μ)
                =ᵐ[μ.restrict (A ∩ S)] 0 :=
              h_inner_ae.filter_mono (ae_mono (Measure.restrict_mono Set.inter_subset_right le_rfl))
            exact integral_eq_zero_of_ae h_ae_AS
          -- Step B: Convert to ℝ≥0∞ and apply ae_eq_of_setLIntegral_prod_eq
          have h_ae_zero : (fun p => W.toAEEqFun p - c) =ᵐ[ν] 0 := by
            -- f is integrable w.r.t. ν
            have h_f_int : Integrable (fun p => W.toAEEqFun p - c) ν := by
              rw [hν_def, Measure.prod_restrict]
              apply Measure.integrableOn_of_bounded (M := 1)
              · rw [Measure.prod_prod S T]
                exact (ENNReal.mul_lt_top (measure_lt_top μ S) (measure_lt_top μ T)).ne
              · exact (W.toAEEqFun.measurable.sub measurable_const).aestronglyMeasurable
              · filter_upwards [ae_restrict_of_ae W.ae_mem_Icc] with p hp
                simp only [Real.norm_eq_abs, abs_le]
                have hc_mem := rectAverage_mem_Icc W S T hS_meas hT_meas
                constructor <;> nlinarith [hp.1, hp.2, hc_mem.1, hc_mem.2]
            -- ∫ f dν = 0 (from rectangle with A = B = univ)
            have h_total : ∫ p, (W.toAEEqFun p - c) ∂ν = 0 := by
              have := h_rect_bochner_zero Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
              simp [Set.univ_prod_univ] at this; exact this
            -- Apply ae_eq_zero via π-λ: rectangles generate the product σ-algebra
            apply h_f_int.ae_eq_zero_of_forall_setIntegral_eq_zero
            intro E hE _
            set C := {s : Set α | MeasurableSet s}
            have h_gen : (inferInstance : MeasurableSpace (α × α)) =
                MeasurableSpace.generateFrom (Set.image2 (· ×ˢ ·) C C) :=
              (generateFrom_eq_prod
                MeasurableSpace.generateFrom_measurableSet
                MeasurableSpace.generateFrom_measurableSet
                isCountablySpanning_measurableSet isCountablySpanning_measurableSet).symm
            have h_pi : IsPiSystem (Set.image2 (· ×ˢ ·) C C) :=
              IsPiSystem.prod
                (fun _ ha _ hb _ => MeasurableSet.inter ha hb)
                (fun _ ha _ hb _ => MeasurableSet.inter ha hb)
            exact MeasurableSpace.induction_on_inter h_gen h_pi
              (by simp only [Measure.restrict_empty, integral_zero_measure])
              (fun E' hE' => by
                obtain ⟨A, hA, B, hB, rfl⟩ := Set.mem_image2.mp hE'
                exact h_rect_bochner_zero A B hA hB)
              (fun E' hE'_meas hE'_zero => by
                have := integral_add_compl hE'_meas h_f_int; linarith)
              (fun s hs_disj hs_meas hs_zero => by
                rw [integral_iUnion hs_meas hs_disj h_f_int.integrableOn]; simp [hs_zero])
              E hE
          -- Step C: ∫_S ∫_T (W-c)² = 0, contradicting h_within_pos
          have h_sq_zero : ∫ x in S, (∫ y in T, (W.toAEEqFun (x, y) - c) ^ 2 ∂μ) ∂μ = 0 := by
            -- W = c a.e. on S × T (w.r.t. ν), so (W-c)² = 0 a.e.
            have h_sq_ae : (fun p => (W.toAEEqFun p - c) ^ 2) =ᵐ[ν] 0 := by
              filter_upwards [h_ae_zero] with p hp
              simp only [Pi.zero_apply] at hp ⊢; rw [hp]; ring
            -- The iterated integral equals the integral w.r.t. ν
            -- ∫ x in S, (∫ y in T, f(x,y) ∂μ) ∂μ = ∫ f dν (by Fubini)
            have h_int : Integrable (fun p => (W.toAEEqFun p - c) ^ 2) ν := by
              rw [hν_def, Measure.prod_restrict]
              apply Measure.integrableOn_of_bounded (M := 1)
              · rw [Measure.prod_prod S T]
                exact (ENNReal.mul_lt_top (measure_lt_top μ S) (measure_lt_top μ T)).ne
              · exact (W.toAEEqFun.measurable.sub measurable_const).pow_const 2
                  |>.aestronglyMeasurable
              · filter_upwards [ae_restrict_of_ae W.ae_mem_Icc] with p hp
                simp only [Real.norm_eq_abs]
                rw [abs_of_nonneg (sq_nonneg _)]
                have hc_mem := rectAverage_mem_Icc W S T hS_meas hT_meas
                nlinarith [hp.1, hp.2, hc_mem.1, hc_mem.2]
            -- ∫ f dν = 0 since f = 0 a.e. w.r.t. ν
            have h_int_zero : ∫ p, (W.toAEEqFun p - c) ^ 2 ∂ν = 0 :=
              integral_eq_zero_of_ae h_sq_ae
            -- ∫ f dν = ∫ x in S, (∫ y in T, f(x,y) ∂μ) ∂μ by Fubini
            rw [show ∫ x in S, (∫ y in T, (W.toAEEqFun (x, y) - c) ^ 2 ∂μ) ∂μ =
                ∫ p, (W.toAEEqFun p - c) ^ 2 ∂ν from
              (integral_prod _ h_int).symm]
            exact h_int_zero
          linarith
        obtain ⟨A, hA_meas, hA_sub, hμA, hμTA, hIA_pos⟩ := h_good_cut
        have h_one_pos : ∫ x in S, (tAverage W A x - c) ^ 2 ∂μ > 0 ∨
            ∫ x in S, (tAverage W (T \ A) x - c) ^ 2 ∂μ > 0 := Or.inl hIA_pos
        -- Step 5c: Build the refinement using two sequential splits
        -- Split T by A → Q₁ (S survives since S ≠ T)
        -- Then split S using between-A variance → Q₂
        -- energy(Q₂) > energy(Q₁) ≥ energy(P)
        -- Helper: rectAvg(S, A') = c for any measurable A' ⊆ T with μ(A') > 0
        have h_rectAvg_eq_c : ∀ A' : Set α, MeasurableSet A' → A' ⊆ T → μ A' ≠ 0 →
            rectAverage W S A' = c := by
          intro A' hA'_meas hA'_sub hμA'
          -- rectAvg(S, A') = rectAvg(A', S) by symmetry = (μA')⁻¹ ∫_{A'} tAvg_S(y) dy
          -- Since tAvg_S = c a.e. on T and A' ⊆ T, this equals c.
          rw [rectAverage_symm W S A' hS_meas hA'_meas]
          -- rectAvg(A', S) = (μA')⁻¹ * (μS)⁻¹ * ∫_{A'×S} W = (μA')⁻¹ ∫_{A'} tAvg_S
          -- Use tAverage_integral_eq_rectAverage in reverse
          have h := tAverage_integral_eq_rectAverage W A' S hA'_meas hS_meas hμA' hμS
          -- h : (μ A')⁻¹ * ∫ y in A', tAvg_S y = rectAvg(A', S)
          rw [← h]
          -- Now show (μA')⁻¹ * ∫_{A'} tAvg_S = (μA')⁻¹ * ∫_{A'} c = c
          have hμA'_top : μ A' ≠ ⊤ := (measure_lt_top μ A').ne
          have hμA'_pos : (0 : ℝ) < (μ A').toReal := ENNReal.toReal_pos hμA' hμA'_top
          have h_int_c : ∫ y in A', tAverage W S y ∂μ = c * (μ A').toReal := by
            have h_ae_c := h_tAvg_S_ae
            -- tAvg_S = c a.e. on T, and A' ⊆ T
            have h_ae_A' : tAverage W S =ᵐ[μ.restrict A'] fun _ => c :=
              h_ae_c.filter_mono (ae_mono (Measure.restrict_mono hA'_sub le_rfl))
            calc ∫ y in A', tAverage W S y ∂μ
                = ∫ y in A', c ∂μ := integral_congr_ae h_ae_A'
              _ = c * (μ A').toReal := by
                  rw [setIntegral_const, smul_eq_mul]; simp [Measure.real]; ring
          rw [h_int_c]
          field_simp [ne_of_gt hμA'_pos]
        -- Helper: S ∈ Q₁.parts after splitting T
        -- Since S ≠ T, S survives in Q₁ = splitPart P T ...
        -- The key construction for both cases
        -- We parameterize by the "good" subset B ⊆ T and the variance bound I_B > 0
        suffices h_main : ∀ B : Set α, MeasurableSet B → B ⊆ T → μ B ≠ 0 → μ (T \ B) ≠ 0 →
            ∫ x in S, (tAverage W B x - c) ^ 2 ∂μ > 0 →
            ∃ Q : MeasurablePartition α μ,
              Refines Q P ∧ Q.parts.card ≤ 2 * P.parts.card ∧
              energy W Q > energy W P by
          rcases h_one_pos with hIA_pos | hITA_pos
          · exact h_main A hA_meas hA_sub hμA hμTA hIA_pos
          · exact h_main (T \ A) (hT_meas.diff hA_meas) Set.diff_subset hμTA
              (by rwa [Set.diff_diff_cancel_left hA_sub]) hITA_pos
        -- Prove the main construction
        intro B hB_meas hB_sub hμB hμTB hI_B_pos
        -- Step A: Build Q₁ = splitPart P T B
        let Q₁ := MeasurablePartition.splitPart P T hT_mem B hB_meas hB_sub hμB hμTB
        have hQ₁_refines : Refines Q₁ P :=
          MeasurablePartition.splitPart_refines P T hT_mem B hB_meas hB_sub hμB hμTB
        have hQ₁_card : Q₁.parts.card ≤ P.parts.card + 1 :=
          MeasurablePartition.splitPart_card P T hT_mem B hB_meas hB_sub hμB hμTB
        have hQ₁_energy : energy W Q₁ ≥ energy W P := by
          have := energy_splitPart_ge W P T hT_mem B hB_meas hB_sub hμB hμTB
          linarith [Finset.sum_nonneg (fun V _ =>
            mul_nonneg (div_nonneg
              (mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
                ENNReal.toReal_nonneg) ENNReal.toReal_nonneg) (sq_nonneg _) : ∀ V ∈ P.parts,
              (0 : ℝ) ≤ (μ V).toReal * (μ B).toReal * (μ (T \ B)).toReal / (μ T).toReal *
                (rectAverage W B V - rectAverage W (T \ B) V) ^ 2)]
        -- Step B: Show S ∈ Q₁.parts (since S ≠ T)
        have hS_in_Q₁ : S ∈ Q₁.parts := by
          classical
          simp only [Q₁, MeasurablePartition.splitPart]
          exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hST, hS_mem⟩)
        -- B ∈ Q₁.parts
        have hB_in_Q₁ : B ∈ Q₁.parts := by
          classical
          simp only [Q₁, MeasurablePartition.splitPart]
          exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
        -- Step C: Apply exists_variance_cut to tAvg_B on S
        set I_B := ∫ x in S, (tAverage W B x - c) ^ 2 ∂μ with hI_B_def
        set ε₁ := Real.sqrt (2 * I_B / (μ S).toReal) with hε₁_def
        have hε₁_pos : ε₁ > 0 :=
          Real.sqrt_pos.mpr (div_pos (mul_pos two_pos hI_B_pos) hμS_real_pos)
        have h_rect_S_B : rectAverage W S B = c := h_rectAvg_eq_c B hB_meas hB_sub hμB
        have h_var_B : ∫ x in S, (tAverage W B x - rectAverage W S B) ^ 2 ∂μ ≥
            ε₁ ^ 2 / 2 * (μ S).toReal := by
          rw [h_rect_S_B, hε₁_def,
            Real.sq_sqrt (le_of_lt (div_pos (mul_pos two_pos hI_B_pos) hμS_real_pos))]
          rw [← hI_B_def, ge_iff_le, ← sub_nonneg]
          have : (μ S).toReal ≠ 0 := ne_of_gt hμS_real_pos
          field_simp; linarith [hI_B_pos, hμS_real_pos]
        -- Apply exists_variance_cut
        set f_B := tAverage W B with hf_B_def
        have hf_B_meas : Measurable f_B := tAverage_measurable W B hB_meas
        have hc_B_mean : rectAverage W S B =
            (μ S).toReal⁻¹ * ∫ x in S, f_B x ∂μ := by
          rw [hf_B_def]
          exact (tAverage_integral_eq_rectAverage W S B hS_meas hB_meas hμS hμB).symm
        have hf_B_int : IntegrableOn f_B S μ := by
          apply Measure.integrableOn_of_bounded (measure_lt_top μ S).ne
          · exact hf_B_meas.aestronglyMeasurable
          · filter_upwards [ae_restrict_of_ae (tAverage_ae_mem_Icc W B hB_meas)] with x hx
            show ‖f_B x‖ ≤ 1
            rw [hf_B_def, Real.norm_eq_abs, abs_le]
            exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
        set ε₁' := ε₁ / Real.sqrt 2 with hε₁'_def
        have hε₁'_pos : ε₁' > 0 := div_pos hε₁_pos (Real.sqrt_pos.mpr (by norm_num))
        have h_var_B' : ∫ x in S, (f_B x - rectAverage W S B) ^ 2 ∂μ ≥
            ε₁' ^ 2 * (μ S).toReal := by
          have h_eq : ε₁' ^ 2 = ε₁ ^ 2 / 2 := by
            rw [hε₁'_def, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          rw [h_eq]; exact h_var_B
        obtain ⟨S₁, hS₁_meas, hS₁_sub, hμS₁, hμS₂, h_avg_diff⟩ :=
          exists_variance_cut f_B S hS_meas hf_B_meas hf_B_int hμS
            (rectAverage W S B) hc_B_mean ε₁' hε₁'_pos h_var_B'
        -- Step D: Build Q₂ = splitPart Q₁ S S₁
        let Q₂ := MeasurablePartition.splitPart Q₁ S hS_in_Q₁ S₁ hS₁_meas hS₁_sub hμS₁ hμS₂
        use Q₂
        refine ⟨?_, ?_, ?_⟩
        -- (a) Q₂ refines P
        · exact Refines.trans hQ₁_refines
            (MeasurablePartition.splitPart_refines Q₁ S hS_in_Q₁ S₁ hS₁_meas hS₁_sub hμS₁ hμS₂)
        -- (b) Q₂.parts.card ≤ 2 * P.parts.card
        · have hQ₂_card : Q₂.parts.card ≤ Q₁.parts.card + 1 :=
            MeasurablePartition.splitPart_card Q₁ S hS_in_Q₁ S₁ hS₁_meas hS₁_sub hμS₁ hμS₂
          have hP_card_ge_2 : 2 ≤ P.parts.card :=
            Finset.one_lt_card.mpr ⟨S, hS_mem, T, hT_mem, hST⟩
          omega
        -- (c) energy W Q₂ > energy W P
        · -- energy(Q₂) > energy(Q₁) ≥ energy(P)
          -- Use energy_splitPart_ge on Q₁ for splitting S by S₁
          have h_ge := energy_splitPart_ge W Q₁ S hS_in_Q₁ S₁ hS₁_meas hS₁_sub hμS₁ hμS₂
          -- The correction term for V = B is positive
          -- Need: (μB) * (μS₁) * (μ(S\S₁)) / (μS) * (rectAvg(S₁,B) - rectAvg(S\S₁,B))² > 0
          set S₂ := S \ S₁ with hS₂_def_local
          have hS₂_meas_local : MeasurableSet S₂ := hS_meas.diff hS₁_meas
          have hμS₁_top : μ S₁ ≠ ⊤ := (measure_lt_top μ S₁).ne
          have hμS₂_top : μ S₂ ≠ ⊤ := (measure_lt_top μ S₂).ne
          have hμS₁_real_pos : 0 < (μ S₁).toReal := ENNReal.toReal_pos hμS₁ hμS₁_top
          have hμS₂_real_pos : 0 < (μ S₂).toReal := ENNReal.toReal_pos hμS₂ hμS₂_top
          have hμB_top : μ B ≠ ⊤ := (measure_lt_top μ B).ne
          have hμB_real_pos : 0 < (μ B).toReal := ENNReal.toReal_pos hμB hμB_top
          -- Sub-averages
          set c₁ := (μ S₁).toReal⁻¹ * ∫ x in S₁, f_B x ∂μ with hc₁_def
          set c₂ := (μ S₂).toReal⁻¹ * ∫ x in S₂, f_B x ∂μ with hc₂_def
          -- Connect to rectAverage
          have hc₁_rect : c₁ = rectAverage W S₁ B :=
            tAverage_integral_eq_rectAverage W S₁ B hS₁_meas hB_meas hμS₁ hμB
          have hc₂_rect : c₂ = rectAverage W S₂ B :=
            tAverage_integral_eq_rectAverage W S₂ B hS₂_meas_local hB_meas hμS₂ hμB
          -- Weighted average
          have h_S_union : S = S₁ ∪ S₂ := by
            rw [hS₂_def_local, Set.union_diff_cancel hS₁_sub]
          have h_disj : Disjoint S₁ S₂ := by
            rw [hS₂_def_local]; exact Set.disjoint_sdiff_right
          have hμ_add : (μ S).toReal = (μ S₁).toReal + (μ S₂).toReal := by
            rw [h_S_union, measure_union h_disj hS₂_meas_local]
            exact ENNReal.toReal_add hμS₁_top hμS₂_top
          have h_int_add : ∫ x in S, f_B x ∂μ =
              ∫ x in S₁, f_B x ∂μ + ∫ x in S₂, f_B x ∂μ := by
            rw [h_S_union]
            exact setIntegral_union h_disj hS₂_meas_local
              (hf_B_int.mono hS₁_sub le_rfl) (hf_B_int.mono Set.diff_subset le_rfl)
          have hc_B_weighted : rectAverage W S B =
              ((μ S₁).toReal * c₁ + (μ S₂).toReal * c₂) / (μ S).toReal := by
            rw [hc_B_mean, h_int_add, hc₁_def, hc₂_def]
            field_simp [ne_of_gt hμS₁_real_pos, ne_of_gt hμS₂_real_pos,
              ne_of_gt hμS_real_pos]
          -- Get |c₁ - c₂| ≥ ε₁'/2 (same calculation as energy_increment_of_between_variance)
          have h_c1_c : c₁ - rectAverage W S B =
              (μ S₂).toReal / (μ S).toReal * (c₁ - c₂) := by
            rw [hc_B_weighted, hμ_add]
            field_simp [ne_of_gt hμS_real_pos]; ring
          have h_c2_c : c₂ - rectAverage W S B =
              -(μ S₁).toReal / (μ S).toReal * (c₁ - c₂) := by
            rw [hc_B_weighted, hμ_add]
            field_simp [ne_of_gt hμS_real_pos]; ring
          have h_diff_bound : |c₁ - c₂| ≥ ε₁' / 2 := by
            rcases h_avg_diff with h1 | h2
            · rw [h_c1_c] at h1
              have h_ratio_le : (μ S₂).toReal / (μ S).toReal ≤ 1 := by
                rw [div_le_one hμS_real_pos, hμ_add]; linarith
              have h_ratio_pos : 0 < (μ S₂).toReal / (μ S).toReal :=
                div_pos hμS₂_real_pos hμS_real_pos
              rw [abs_mul, abs_of_pos h_ratio_pos] at h1
              calc |c₁ - c₂| ≥ (μ S₂).toReal / (μ S).toReal * |c₁ - c₂| := by
                    nlinarith [abs_nonneg (c₁ - c₂)]
                _ ≥ ε₁' / 2 := h1
            · rw [h_c2_c] at h2
              have h_ratio_le : (μ S₁).toReal / (μ S).toReal ≤ 1 := by
                rw [div_le_one hμS_real_pos, hμ_add]; linarith
              have h_ratio_pos : 0 < (μ S₁).toReal / (μ S).toReal :=
                div_pos hμS₁_real_pos hμS_real_pos
              have h_abs_eq : |-(μ S₁).toReal / (μ S).toReal * (c₁ - c₂)| =
                  (μ S₁).toReal / (μ S).toReal * |c₁ - c₂| := by
                rw [neg_div, neg_mul, abs_neg, abs_mul, abs_of_pos h_ratio_pos]
              rw [h_abs_eq] at h2
              calc |c₁ - c₂| ≥ (μ S₁).toReal / (μ S).toReal * |c₁ - c₂| := by
                    nlinarith [abs_nonneg (c₁ - c₂)]
                _ ≥ ε₁' / 2 := h2
          have h_sq_diff : (c₁ - c₂) ^ 2 ≥ (ε₁' / 2) ^ 2 := by
            calc (c₁ - c₂) ^ 2 = |c₁ - c₂| ^ 2 := by rw [sq_abs]
              _ ≥ (ε₁' / 2) ^ 2 := by
                apply sq_le_sq'; · linarith [abs_nonneg (c₁ - c₂), hε₁'_pos]
                · exact h_diff_bound
          -- The B-term in the correction sum of energy_splitPart_ge is positive
          have h_rect_eq₁ : rectAverage W S₁ B = c₁ := hc₁_rect.symm
          have h_rect_eq₂ : rectAverage W (S \ S₁) B = c₂ := hc₂_rect.symm
          have h_B_term_pos : (μ B).toReal * (μ S₁).toReal * (μ (S \ S₁)).toReal /
              (μ S).toReal * (rectAverage W S₁ B - rectAverage W (S \ S₁) B) ^ 2 > 0 := by
            rw [h_rect_eq₁, h_rect_eq₂]
            apply mul_pos
            · apply div_pos
              · exact mul_pos (mul_pos hμB_real_pos hμS₁_real_pos) hμS₂_real_pos
              · exact hμS_real_pos
            · linarith [sq_nonneg (ε₁' / 2), sq_pos_of_pos hε₁'_pos]
          have h_sum_pos : Q₁.parts.sum (fun U => (μ U).toReal * (μ S₁).toReal *
              (μ (S \ S₁)).toReal / (μ S).toReal *
              (rectAverage W S₁ U - rectAverage W (S \ S₁) U) ^ 2) > 0 := by
            have h_nonneg : ∀ U ∈ Q₁.parts, 0 ≤ (μ U).toReal * (μ S₁).toReal *
                (μ (S \ S₁)).toReal / (μ S).toReal *
                (rectAverage W S₁ U - rectAverage W (S \ S₁) U) ^ 2 := by
              intro U _
              apply mul_nonneg
              · apply div_nonneg
                · exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
                    ENNReal.toReal_nonneg
                · exact ENNReal.toReal_nonneg
              · exact sq_nonneg _
            exact (Finset.sum_pos_iff_of_nonneg h_nonneg).mpr ⟨B, hB_in_Q₁, h_B_term_pos⟩
          linarith [h_ge, hQ₁_energy]

/-- Energy increment lemma (Frieze-Kannan style).

If W has large defect on some rectangle S × T of P, then refining that
rectangle increases the energy.

More precisely: if there exist S, T ∈ P such that
∫_{S×T} |W - rectAverage W S T|² ≥ ε² μ(S) μ(T),
then splitting S (or T) into two parts by an appropriate cut strictly
increases the energy.

This is the key step that drives the regularity iteration. -/
@[blueprint "thm:energy-increment"
  (title := /-- Energy increment lemma -/)]
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
      -- Apply the FK global cut lemma (uses splitAllParts).
      · push_neg at h_split_T_sym h_check_B_T
        have h_A_T_large : A_T ≥ ε ^ 2 / 2 * (μ S).toReal * (μ T).toReal := h_split_T
        have h_within_unfolded : ∫ x in S, (∫ y in T,
            (W.toAEEqFun (x, y) - tAverage W T x) ^ 2 ∂μ) ∂μ ≥
            ε ^ 2 / 2 * (μ S).toReal * (μ T).toReal := by
          rw [← hW_T_def, ← hA_T_def]; exact h_A_T_large
        exact energy_increment_of_within_variance W P ε hε
          S hS_mem T hT_mem hS_meas hT_meas hμS_pos hμT_pos h_within_unfolded

end Energy

/-! ### Regularity lemma -/

section Regularity

variable [IsProbabilityMeasure μ]

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

/-- Weighted Cauchy-Schwarz for finite sums: if w_i >= 0 and sum w_i <= 1,
then (sum w_i d_i)^2 <= sum w_i d_i^2. -/
private lemma sq_weighted_sum_le {ι : Type*} (s : Finset ι) (w d : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : s.sum w ≤ 1) :
    (s.sum fun i => w i * d i) ^ 2 ≤ s.sum fun i => w i * d i ^ 2 := by
  -- Use sum_mul_sq_le_sq_mul_sq with f(i) = sqrt(w i), g(i) = sqrt(w i) * d i
  set f : ι → ℝ := fun i => Real.sqrt (w i)
  set g : ι → ℝ := fun i => Real.sqrt (w i) * d i
  have h_cs := Finset.sum_mul_sq_le_sq_mul_sq s f g
  -- f * g = sqrt(w) * (sqrt(w) * d) = w * d
  have h_fg : (s.sum fun i => f i * g i) = s.sum fun i => w i * d i := by
    apply Finset.sum_congr rfl; intro i hi
    show Real.sqrt (w i) * (Real.sqrt (w i) * d i) = w i * d i
    rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
  -- f^2 = w
  have h_f2 : (s.sum fun i => f i ^ 2) = s.sum w := by
    apply Finset.sum_congr rfl; intro i hi
    show Real.sqrt (w i) ^ 2 = w i
    exact Real.sq_sqrt (hw i hi)
  -- g^2 = w * d^2
  have h_g2 : (s.sum fun i => g i ^ 2) = s.sum fun i => w i * d i ^ 2 := by
    apply Finset.sum_congr rfl; intro i hi
    show (Real.sqrt (w i) * d i) ^ 2 = w i * d i ^ 2
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  rw [h_fg, h_f2, h_g2] at h_cs
  calc (s.sum fun i => w i * d i) ^ 2
      ≤ (s.sum w) * (s.sum fun i => w i * d i ^ 2) := h_cs
    _ ≤ 1 * (s.sum fun i => w i * d i ^ 2) :=
        mul_le_mul_of_nonneg_right hW (Finset.sum_nonneg fun i hi =>
          mul_nonneg (hw i hi) (sq_nonneg _))
    _ = s.sum fun i => w i * d i ^ 2 := one_mul _

/-- Weighted Cauchy-Schwarz for double finite sums: if w_i, v_j >= 0 and
sum w_i <= 1, sum v_j <= 1, then (sum_{i,j} w_i v_j d_{ij})^2 <= sum_{i,j} w_i v_j d_{ij}^2. -/
private lemma sq_weighted_double_sum_le {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (w : ι → ℝ) (v : κ → ℝ) (d : ι → κ → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hv : ∀ j ∈ t, 0 ≤ v j)
    (hW : s.sum w ≤ 1) (hV : t.sum v ≤ 1) :
    (s.sum fun i => t.sum fun j => w i * v j * d i j) ^ 2 ≤
    s.sum fun i => t.sum fun j => w i * v j * (d i j) ^ 2 := by
  -- Rewrite each inner sum: sum_j w_i * v_j * d_{ij} = w_i * sum_j v_j * d_{ij}
  have h_inner_eq : (s.sum fun i => t.sum fun j => w i * v j * d i j) =
      s.sum fun i => w i * (t.sum fun j => v j * d i j) := by
    apply Finset.sum_congr rfl; intro i _
    have : (t.sum fun j => w i * v j * d i j) =
        t.sum fun j => w i * (v j * d i j) :=
      Finset.sum_congr rfl (fun j _ => by ring)
    rw [this, ← Finset.mul_sum]
  have h_inner_eq2 : (s.sum fun i => t.sum fun j => w i * v j * (d i j) ^ 2) =
      s.sum fun i => w i * (t.sum fun j => v j * (d i j) ^ 2) := by
    apply Finset.sum_congr rfl; intro i _
    have : (t.sum fun j => w i * v j * (d i j) ^ 2) =
        t.sum fun j => w i * (v j * (d i j) ^ 2) :=
      Finset.sum_congr rfl (fun j _ => by ring)
    rw [this, ← Finset.mul_sum]
  rw [h_inner_eq, h_inner_eq2]
  -- Now (sum_i w_i * D_i)^2 where D_i = sum_j v_j d_{ij}
  -- By sq_weighted_sum_le: <= sum_i w_i * D_i^2
  have step1 := sq_weighted_sum_le s w (fun i => t.sum fun j => v j * d i j) hw hW
  -- For each i: D_i^2 <= sum_j v_j d_{ij}^2 by sq_weighted_sum_le
  have step2 : ∀ i ∈ s, w i * (t.sum fun j => v j * d i j) ^ 2 ≤
      w i * (t.sum fun j => v j * (d i j) ^ 2) := by
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (hw i hi)
    exact sq_weighted_sum_le t v (d i) hv hV
  linarith [Finset.sum_le_sum step2]

/-- Decomposition of a full-space integral into a double sum over partition cells.
This is the measure-theoretic fact that partition cells cover α × α a.e. -/
private lemma integral_eq_sum_parts (P : MeasurablePartition α μ)
    (f : α × α → ℝ) (hf : Integrable f (μ.prod μ)) :
    ∫ p, f p ∂(μ.prod μ) =
      ∑ S ∈ P.parts, ∑ T ∈ P.parts, ∫ p in S ×ˢ T, f p ∂(μ.prod μ) := by
  -- Partition rectangles cover α × α a.e.
  let rectUnion := ⋃ (st : Set α × Set α), ⋃ (_ : st ∈ P.parts ×ˢ P.parts), st.1 ×ˢ st.2
  -- Measurability and disjointness
  have h_meas_rect : ∀ st ∈ P.parts ×ˢ P.parts, MeasurableSet (st.1 ×ˢ st.2) := by
    intro ⟨S, T⟩ hst; simp only [Finset.mem_product] at hst
    exact (P.measurableSet_part hst.1).prod (P.measurableSet_part hst.2)
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
  -- Cover a.e.
  have h_ae_covers : ∀ᵐ p ∂(μ.prod μ), ∃ S ∈ P.parts, ∃ T ∈ P.parts, p ∈ S ×ˢ T := by
    have h_meas : MeasurableSet {p : α × α | ∃ S ∈ P.parts, ∃ T ∈ P.parts, p ∈ S ×ˢ T} := by
      have h_eq : {p : α × α | ∃ S ∈ P.parts, ∃ T ∈ P.parts, p ∈ S ×ˢ T} =
          ⋃ S ∈ P.parts, ⋃ T ∈ P.parts, S ×ˢ T := by
        ext p; simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
      rw [h_eq]; exact MeasurableSet.biUnion P.parts.countable_toSet
        (fun S hS => MeasurableSet.biUnion P.parts.countable_toSet
          (fun T hT => (P.measurableSet_part hS).prod (P.measurableSet_part hT)))
    rw [Measure.ae_prod_iff_ae_ae h_meas]
    filter_upwards [P.ae_covers] with x hx
    filter_upwards [P.ae_covers] with y hy
    obtain ⟨S, hS, hxS⟩ := hx; obtain ⟨T, hT, hyT⟩ := hy
    exact ⟨S, hS, T, hT, ⟨hxS, hyT⟩⟩
  -- Define the union of all partition rectangles
  let rectUnion := ⋃ S ∈ P.parts, ⋃ T ∈ P.parts, S ×ˢ T
  -- ∫ f = ∫_{rectUnion} f
  have h_int_eq : ∫ p, f p ∂(μ.prod μ) = ∫ p in rectUnion, f p ∂(μ.prod μ) := by
    symm; apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [h_ae_covers] with p hp h_not_in
    simp only [rectUnion, Set.mem_iUnion, not_exists] at h_not_in
    obtain ⟨S, hS, T, hT, hp_mem⟩ := hp
    exact absurd hp_mem (h_not_in S hS T hT)
  -- Rewrite rectUnion as biUnion over product
  have h_union_eq : rectUnion = ⋃ (st : Set α × Set α),
      ⋃ (_ : st ∈ P.parts ×ˢ P.parts), st.1 ×ˢ st.2 := by
    ext p; simp only [rectUnion, Set.mem_iUnion, Finset.mem_product, exists_prop, Prod.exists]
    constructor
    · rintro ⟨S, hS, T, hT, hp⟩; exact ⟨S, T, ⟨hS, hT⟩, hp⟩
    · rintro ⟨S, T, ⟨hS, hT⟩, hp⟩; exact ⟨S, hS, T, hT, hp⟩
  -- ∫_{rectUnion} f = ∑ ∫_{SxT} f
  rw [h_int_eq, h_union_eq,
    integral_biUnion_finset _ h_meas_rect h_disj (fun _ _ => hf.integrableOn),
    Finset.sum_product]

/-- The integral of (stepify P W) * g decomposes as a weighted sum over partition cells,
where each weight is rectAverage W S T. This follows from the fact that stepify P W
is a.e. equal to rectAverage W S T on each cell S × T. -/
private lemma integral_stepify_mul_eq_sum (W : Graphon α μ) (P : MeasurablePartition α μ)
    (g : α × α → ℝ) (hg : Integrable g (μ.prod μ)) :
    ∫ p, (stepify P W).toAEEqFun p * g p ∂(μ.prod μ) =
      ∑ S ∈ P.parts, ∑ T ∈ P.parts,
        rectAverage W S T * ∫ p in S ×ˢ T, g p ∂(μ.prod μ) := by
  -- Decompose integral into sum over partition cells
  have hfg : Integrable (fun p => (stepify P W).toAEEqFun p * g p) (μ.prod μ) := by
    apply hg.bdd_mul (stepify P W).toAEEqFun.aestronglyMeasurable
    filter_upwards [(stepify P W).ae_mem_Icc] with p hp
    rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨by linarith [hp.1], hp.2⟩
  rw [integral_eq_sum_parts P _ hfg]
  -- On each cell, stepify P W = rectAverage a.e.
  apply Finset.sum_congr rfl; intro S hS
  apply Finset.sum_congr rfl; intro T hT
  have hS_meas := P.measurableSet_part hS
  have hT_meas := P.measurableSet_part hT
  -- stepify P W = rectAverage W S T a.e. on S × T
  have h_ae : ∀ᵐ p ∂(μ.prod μ),
      p ∈ S ×ˢ T → (stepify P W).toAEEqFun p = rectAverage W S T := by
    filter_upwards [stepify_ae P W] with p hp hmem
    rw [hp]; exact stepifyFun_eq_rectAverage P W hS hT hmem
  rw [setIntegral_congr_ae (hS_meas.prod hT_meas)
    (h_ae.mono fun p hp hmem => by rw [hp hmem])]
  exact integral_const_mul _ _

/-- When ∫_{S×T} g = ∫_{S×T} W for all partition cells, the integral of
(stepify P W) * g equals energy W P. -/
private lemma integral_stepify_mul_eq_energy (W : Graphon α μ) (P : MeasurablePartition α μ)
    (g : α × α → ℝ) (hg : Integrable g (μ.prod μ))
    (h_eq : ∀ S ∈ P.parts, ∀ T ∈ P.parts,
      ∫ p in S ×ˢ T, g p ∂(μ.prod μ) = ∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ)) :
    ∫ p, (stepify P W).toAEEqFun p * g p ∂(μ.prod μ) = energy W P := by
  rw [integral_stepify_mul_eq_sum W P g hg]
  unfold energy
  apply Finset.sum_congr rfl; intro S hS
  apply Finset.sum_congr rfl; intro T hT
  rw [h_eq S hS T hT]
  by_cases hμS : μ S = 0
  · have : (μ.prod μ) (S ×ˢ T) = 0 := by rw [Measure.prod_prod, hμS, zero_mul]
    simp [setIntegral_measure_zero _ this, hμS]
  by_cases hμT : μ T = 0
  · have : (μ.prod μ) (S ×ˢ T) = 0 := by rw [Measure.prod_prod, hμT, mul_zero]
    simp [setIntegral_measure_zero _ this, hμT]
  -- Both measures nonzero: ∫W = rectAverage * μS * μT
  have ha : rectAverage W S T = (μ S).toReal⁻¹ * (μ T).toReal⁻¹ *
      ∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ) := by
    unfold rectAverage; simp [hμS, hμT]
  rw [ha]
  have hμS_pos : (μ S).toReal ≠ 0 := ne_of_gt (ENNReal.toReal_pos hμS (measure_lt_top μ _).ne)
  have hμT_pos : (μ T).toReal ≠ 0 := ne_of_gt (ENNReal.toReal_pos hμT (measure_lt_top μ _).ne)
  field_simp

/-- Variance shift: ∫_{S×T} (W - c)² = ∫_{S×T} (W - a)² + (a - c)² μ(S)μ(T),
where a = rectAverage W S T. Derives from variance_decomposition_rect. -/
private lemma integral_sq_shift (W : Graphon α μ) (S T : Set α)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (c : ℝ) :
    ∫ p in S ×ˢ T, (W.toAEEqFun p - c) ^ 2 ∂(μ.prod μ) =
      ∫ p in S ×ˢ T, (W.toAEEqFun p - rectAverage W S T) ^ 2 ∂(μ.prod μ) +
      (μ S).toReal * (μ T).toReal * (rectAverage W S T - c) ^ 2 := by
  by_cases hμS : μ S = 0
  · have h_zero : (μ.prod μ) (S ×ˢ T) = 0 := by rw [Measure.prod_prod, hμS, zero_mul]
    simp [setIntegral_measure_zero _ h_zero, hμS]
  by_cases hμT : μ T = 0
  · have h_zero : (μ.prod μ) (S ×ˢ T) = 0 := by rw [Measure.prod_prod, hμT, mul_zero]
    simp [setIntegral_measure_zero _ h_zero, hμT]
  -- Both measures nonzero. Use variance_decomposition_rect twice.
  -- For c = 0: ∫ W² = ∫ (W - a)² + a² μS μT  (from variance_decomposition_rect)
  -- For general c: ∫ (W-c)² = ∫ W² - 2c ∫ W + c² μ(S×T)
  -- Combined: ∫ (W-c)² = ∫ (W-a)² + (a² - 2ac + c²) μS μT = ∫ (W-a)² + (a-c)² μS μT
  have h_var := variance_decomposition_rect W S T hS hT hμS hμT
  -- ∫ W = a * μS * μT
  have hS_pos : 0 < (μ S).toReal := ENNReal.toReal_pos hμS (measure_lt_top μ S).ne
  have hT_pos : 0 < (μ T).toReal := ENNReal.toReal_pos hμT (measure_lt_top μ T).ne
  have h_int_W : ∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ) =
      rectAverage W S T * (μ S).toReal * (μ T).toReal := by
    have ha : rectAverage W S T = (μ S).toReal⁻¹ * (μ T).toReal⁻¹ *
        ∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ) := by
      unfold rectAverage; simp [hμS, hμT]
    rw [ha]; field_simp
  have hμST : ((μ.prod μ) (S ×ˢ T)).toReal = (μ S).toReal * (μ T).toReal := by
    rw [Measure.prod_prod, ENNReal.toReal_mul]
  -- Strategy: expand ∫(W-c)² = ∫W² - 2c∫W + c²μ(S×T), then substitute
  -- h_var (∫W² = ∫(W-a)² + a²μSμT) and h_int_W (∫W = a*μS*μT).
  -- Integrability facts (mirroring variance_decomposition_rect)
  have h_int_W2 : IntegrableOn (fun p => W.toAEEqFun p) (S ×ˢ T) (μ.prod μ) :=
    (SymmKernel.graphon_integrable W).integrableOn
  have h_int_W_sq : IntegrableOn (fun p => (W.toAEEqFun p) ^ 2) (S ×ˢ T) (μ.prod μ) := by
    apply Measure.integrableOn_of_bounded (measure_lt_top _ _).ne
    · exact (continuous_pow 2).comp_aestronglyMeasurable W.toAEEqFun.aestronglyMeasurable
    · filter_upwards [ae_restrict_of_ae W.ae_mem_Icc] with p hp
      simp only [Real.norm_eq_abs]
      calc |W.toAEEqFun p ^ 2| = W.toAEEqFun p ^ 2 := abs_of_nonneg (sq_nonneg _)
        _ ≤ 1 := by nlinarith [hp.1, hp.2]
  have h_int_cW : IntegrableOn (fun p => 2 * c * W.toAEEqFun p) (S ×ˢ T) (μ.prod μ) :=
    h_int_W2.const_mul (2 * c)
  have h_int_const_c : IntegrableOn (fun _ => c ^ 2) (S ×ˢ T) (μ.prod μ) :=
    integrableOn_const (measure_lt_top _ _).ne
  -- Expansion: ∫(W-c)² = ∫W² - 2c∫W + c²μ(S×T)
  have h_expand : ∫ p in S ×ˢ T, (W.toAEEqFun p - c) ^ 2 ∂(μ.prod μ) =
      ∫ p in S ×ˢ T, (W.toAEEqFun p) ^ 2 ∂(μ.prod μ) -
      2 * c * ∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ) +
      c ^ 2 * ((μ.prod μ) (S ×ˢ T)).toReal := by
    have h1 : ∫ p in S ×ˢ T, (W.toAEEqFun p - c) ^ 2 ∂(μ.prod μ) =
        ∫ p in S ×ˢ T, ((W.toAEEqFun p) ^ 2 - 2 * c * W.toAEEqFun p + c ^ 2) ∂(μ.prod μ) := by
      congr 1; funext p; ring
    rw [h1]
    have h_step1 : ∫ p in S ×ˢ T, (W.toAEEqFun p ^ 2 - 2 * c * W.toAEEqFun p + c ^ 2) ∂(μ.prod μ) =
        ∫ p in S ×ˢ T, (W.toAEEqFun p ^ 2 - 2 * c * W.toAEEqFun p) ∂(μ.prod μ) +
        ∫ _ in S ×ˢ T, c ^ 2 ∂(μ.prod μ) := by
      have h_eq : (fun p => W.toAEEqFun p ^ 2 - 2 * c * W.toAEEqFun p + c ^ 2) =
          (fun p => W.toAEEqFun p ^ 2 - 2 * c * W.toAEEqFun p) + (fun _ => c ^ 2) := by
        ext p; simp only [Pi.add_apply]
      rw [h_eq]
      exact integral_add (h_int_W_sq.sub h_int_cW) h_int_const_c
    rw [h_step1]
    have h_step2 : ∫ p in S ×ˢ T, (W.toAEEqFun p ^ 2 - 2 * c * W.toAEEqFun p) ∂(μ.prod μ) =
        ∫ p in S ×ˢ T, W.toAEEqFun p ^ 2 ∂(μ.prod μ) -
        ∫ p in S ×ˢ T, (2 * c * W.toAEEqFun p) ∂(μ.prod μ) := by
      have : (fun p => W.toAEEqFun p ^ 2 - 2 * c * W.toAEEqFun p) =
          (fun p => W.toAEEqFun p ^ 2) - (fun p => 2 * c * W.toAEEqFun p) := by
        funext p; simp only [Pi.sub_apply]
      rw [this]
      exact integral_sub h_int_W_sq h_int_cW
    rw [h_step2, integral_const_mul, setIntegral_const, smul_eq_mul]
    simp only [Measure.real]
    ring
  -- Substitute h_var and h_int_W into the expansion
  rw [Measure.prod_prod, ENNReal.toReal_mul] at h_expand
  rw [h_int_W] at h_expand
  -- h_var: ∫W² = ∫(W-a)² + a²μSμT (rectAverage W S T)²
  -- h_expand: ∫(W-c)² = ∫W² - 2c·a·μSμT + c²·μSμT
  -- Combining gives ∫(W-c)² = ∫(W-a)² + (a-c)²μSμT
  linarith

/-- On any Q-cell U×V, the integral of stepify Q W equals the integral of W.
This is the conditional expectation property: stepify Q W has the same integral
as W on each Q-cell. -/
private lemma setIntegral_stepify_eq_on_cell
    (W : Graphon α μ) (Q : MeasurablePartition α μ) (U V : Set α)
    (hU : U ∈ Q.parts) (hV : V ∈ Q.parts) :
    ∫ p in U ×ˢ V, (stepify Q W).toAEEqFun p ∂(μ.prod μ) =
    ∫ p in U ×ˢ V, W.toAEEqFun p ∂(μ.prod μ) := by
  by_cases hμU : μ U = 0
  · have h0 : (μ.prod μ) (U ×ˢ V) = 0 := by rw [Measure.prod_prod, hμU, zero_mul]
    rw [setIntegral_measure_zero _ h0, setIntegral_measure_zero _ h0]
  by_cases hμV : μ V = 0
  · have h0 : (μ.prod μ) (U ×ˢ V) = 0 := by rw [Measure.prod_prod, hμV, mul_zero]
    rw [setIntegral_measure_zero _ h0, setIntegral_measure_zero _ h0]
  -- Both measures nonzero: stepify Q W = avg_Q(U,V) a.e. on U×V
  have hU_meas := Q.measurableSet_part hU
  have hV_meas := Q.measurableSet_part hV
  have h_ae : ∀ᵐ p ∂(μ.prod μ),
      p ∈ U ×ˢ V → (stepify Q W).toAEEqFun p = rectAverage W U V := by
    filter_upwards [stepify_ae Q W] with p hp hmem
    rw [hp]
    exact stepifyFun_eq_rectAverage Q W hU hV hmem
  rw [setIntegral_congr_ae (hU_meas.prod hV_meas) h_ae, setIntegral_const, smul_eq_mul]
  -- ∫ W = rectAverage * μ(U) * μ(V) by definition
  have ha : rectAverage W U V = (μ U).toReal⁻¹ * (μ V).toReal⁻¹ *
      ∫ p in U ×ˢ V, W.toAEEqFun p ∂(μ.prod μ) := by
    unfold rectAverage; simp [hμU, hμV]
  rw [ha]
  have hμU_pos : (μ U).toReal ≠ 0 := ne_of_gt (ENNReal.toReal_pos hμU (measure_lt_top μ _).ne)
  have hμV_pos : (μ V).toReal ≠ 0 := ne_of_gt (ENNReal.toReal_pos hμV (measure_lt_top μ _).ne)
  simp only [Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
  field_simp

set_option maxHeartbeats 3200000 in
/-- For a refinement Q of P, the integral of stepify Q W on any P-cell S×T
equals the integral of W on S×T. This is the conditional expectation property:
the stepification preserves integrals on any cell of the coarser partition. -/
private lemma setIntegral_stepify_eq_on_refines_cell
    (W : Graphon α μ) (P Q : MeasurablePartition α μ) (hQP : Refines Q P)
    (S T : Set α) (hS : S ∈ P.parts) (hT : T ∈ P.parts) :
    ∫ p in S ×ˢ T, (stepify Q W).toAEEqFun p ∂(μ.prod μ) =
    ∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ) := by
  -- The Q-parts within S and T
  haveI : DecidablePred (· ⊆ S) := Classical.decPred _
  haveI : DecidablePred (· ⊆ T) := Classical.decPred _
  set QS := Q.parts.filter (· ⊆ S) with hQS_def
  set QT := Q.parts.filter (· ⊆ T) with hQT_def
  -- Every Q-part in QS is a Q-part
  have hQS_sub : ∀ U ∈ QS, U ∈ Q.parts := fun U hU => (Finset.mem_filter.mp hU).1
  have hQT_sub : ∀ V ∈ QT, V ∈ Q.parts := fun V hV => (Finset.mem_filter.mp hV).1
  -- Every Q-part in QS is a subset of S
  have hQS_subset : ∀ U ∈ QS, U ⊆ S := fun U hU => (Finset.mem_filter.mp hU).2
  have hQT_subset : ∀ V ∈ QT, V ⊆ T := fun V hV => (Finset.mem_filter.mp hV).2
  -- Measurability
  have hS_meas := P.measurableSet_part hS
  have hT_meas := P.measurableSet_part hT
  -- Step 1: The Q-cells in QS × QT are pairwise disjoint
  have h_cells_disj : (↑(QS ×ˢ QT) : Set (Set α × Set α)).Pairwise
      (Function.onFun Disjoint fun st => st.1 ×ˢ st.2) := by
    intro ⟨U₁, V₁⟩ h₁ ⟨U₂, V₂⟩ h₂ hne
    simp only [Function.onFun]
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at h₁ h₂
    by_cases hU : U₁ = U₂
    · subst hU
      have hV : V₁ ≠ V₂ := fun h => hne (Prod.ext rfl h)
      exact Disjoint.mono (Set.prod_mono_right Subset.rfl)
        (Set.prod_mono_right Subset.rfl)
        (Set.disjoint_left.mpr fun p hp1 hp2 =>
          Set.disjoint_left.mp
            (Q.pairwiseDisjoint (hQT_sub V₁ h₁.2) (hQT_sub V₂ h₂.2) hV)
            (Set.mem_prod.mp hp1).2 (Set.mem_prod.mp hp2).2)
    · exact Disjoint.mono (Set.prod_mono_left Subset.rfl)
        (Set.prod_mono_left Subset.rfl)
        (Set.disjoint_left.mpr fun p hp1 hp2 =>
          Set.disjoint_left.mp
            (Q.pairwiseDisjoint (hQS_sub U₁ h₁.1) (hQS_sub U₂ h₂.1) hU)
            (Set.mem_prod.mp hp1).1 (Set.mem_prod.mp hp2).1)
  -- Step 2: Measurability of cells
  have h_cells_meas : ∀ st ∈ QS ×ˢ QT, MeasurableSet (st.1 ×ˢ st.2) := by
    intro ⟨U, V⟩ hst
    simp only [Finset.mem_product] at hst
    exact (Q.measurableSet_part (hQS_sub U hst.1)).prod
      (Q.measurableSet_part (hQT_sub V hst.2))
  -- Step 3: S × T is a.e. equal to the union of Q-cell products
  set cellUnion := ⋃ st ∈ QS ×ˢ QT, st.1 ×ˢ st.2
  have h_sub : cellUnion ⊆ S ×ˢ T := by
    intro p hp
    simp only [cellUnion, Set.mem_iUnion] at hp
    obtain ⟨⟨U, V⟩, hst, hp_mem⟩ := hp
    simp only [Finset.mem_coe, Finset.mem_product] at hst
    exact Set.mem_prod.mpr
      ⟨hQS_subset U hst.1 (Set.mem_prod.mp hp_mem).1,
       hQT_subset V hst.2 (Set.mem_prod.mp hp_mem).2⟩
  have h_cellUnion_meas : MeasurableSet cellUnion :=
    MeasurableSet.biUnion (QS ×ˢ QT).countable_toSet h_cells_meas
  -- Show a.e. coverage: every point in S × T is a.e. in some Q-cell within S × T
  have h_cover : ∀ᵐ p ∂(μ.prod μ).restrict (S ×ˢ T),
      p ∈ cellUnion := by
    rw [ae_restrict_iff' (hS_meas.prod hT_meas)]
    filter_upwards [Measure.QuasiMeasurePreserving.ae
        Measure.quasiMeasurePreserving_fst Q.ae_covers,
      Measure.QuasiMeasurePreserving.ae
        Measure.quasiMeasurePreserving_snd Q.ae_covers] with p h1 h2 hp
    obtain ⟨U, hU_mem, hpU⟩ := h1
    obtain ⟨V, hV_mem, hpV⟩ := h2
    -- U ⊆ S (because Q refines P and p ∈ U ∩ S)
    have hU_sub_S : U ⊆ S := by
      obtain ⟨S', hS'_mem, hU_sub⟩ := hQP U hU_mem
      have hp1S' : p.1 ∈ S' := hU_sub hpU
      have : S = S' := by
        by_contra h
        exact Set.disjoint_left.mp (P.pairwiseDisjoint hS hS'_mem h)
          ((Set.mem_prod.mp hp).1) hp1S'
      rw [this]; exact hU_sub
    have hV_sub_T : V ⊆ T := by
      obtain ⟨T', hT'_mem, hV_sub⟩ := hQP V hV_mem
      have hp2T' : p.2 ∈ T' := hV_sub hpV
      have : T = T' := by
        by_contra h
        exact Set.disjoint_left.mp (P.pairwiseDisjoint hT hT'_mem h)
          ((Set.mem_prod.mp hp).2) hp2T'
      rw [this]; exact hV_sub
    simp only [cellUnion, Set.mem_iUnion, Finset.mem_coe, Finset.mem_product]
    exact ⟨⟨U, V⟩, ⟨Finset.mem_filter.mpr ⟨hU_mem, hU_sub_S⟩,
                      Finset.mem_filter.mpr ⟨hV_mem, hV_sub_T⟩⟩,
           Set.mem_prod.mpr ⟨hpU, hpV⟩⟩
  -- S × T =ᵐ cellUnion
  have h_ae_eq : S ×ˢ T =ᵐ[μ.prod μ] cellUnion := by
    rw [ae_eq_set]
    refine ⟨?_, by rw [Set.diff_eq_empty.mpr h_sub]; exact measure_empty⟩
    have h0 : (μ.prod μ).restrict (S ×ˢ T) cellUnionᶜ = 0 := ae_iff.mp h_cover
    rwa [Measure.restrict_apply h_cellUnion_meas.compl, Set.inter_comm] at h0
  -- Integrability of both integrands on each cell
  have h_int_stepify : ∀ st ∈ QS ×ˢ QT,
      IntegrableOn (fun p => (stepify Q W).toAEEqFun p) (st.1 ×ˢ st.2) (μ.prod μ) :=
    fun _ _ => (SymmKernel.graphon_integrable (stepify Q W)).integrableOn
  have h_int_W : ∀ st ∈ QS ×ˢ QT,
      IntegrableOn (fun p => W.toAEEqFun p) (st.1 ×ˢ st.2) (μ.prod μ) :=
    fun _ _ => (SymmKernel.graphon_integrable W).integrableOn
  -- Step 4: Decompose and apply setIntegral_stepify_eq_on_cell
  calc ∫ p in S ×ˢ T, (stepify Q W).toAEEqFun p ∂(μ.prod μ)
      = ∫ p in cellUnion, (stepify Q W).toAEEqFun p ∂(μ.prod μ) :=
        setIntegral_congr_set h_ae_eq
    _ = ∑ st ∈ QS ×ˢ QT, ∫ p in st.1 ×ˢ st.2, (stepify Q W).toAEEqFun p ∂(μ.prod μ) :=
        integral_biUnion_finset _ h_cells_meas h_cells_disj h_int_stepify
    _ = ∑ st ∈ QS ×ˢ QT, ∫ p in st.1 ×ˢ st.2, W.toAEEqFun p ∂(μ.prod μ) := by
        apply Finset.sum_congr rfl
        intro ⟨U, V⟩ hst
        simp only [Finset.mem_product] at hst
        exact setIntegral_stepify_eq_on_cell W Q U V (hQS_sub U hst.1) (hQT_sub V hst.2)
    _ = ∫ p in cellUnion, W.toAEEqFun p ∂(μ.prod μ) :=
        (integral_biUnion_finset _ h_cells_meas h_cells_disj h_int_W).symm
    _ = ∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ) :=
        (setIntegral_congr_set h_ae_eq).symm

set_option maxHeartbeats 6400000 in
/-- The energy gain from a double split (by S₀ and T₀) is at least the square
of the rectangle integral of the difference W − stepify_P(W) over S₀ × T₀.

This is the core inequality behind the Frieze-Kannan weak regularity lemma.

Strategy: Jensen's inequality on ∫_{S₀×T₀} (W - stepify P W) combined with
monotonicity of energy under refinement and the L² identity energy + defect = ∫∫ W². -/
private lemma energy_doubleSplit_ge_sq
    (W : Graphon α μ) (P : MeasurablePartition α μ)
    (S₀ : Set α) (hS₀ : MeasurableSet S₀) (T₀ : Set α) (hT₀ : MeasurableSet T₀) :
    energy W (MeasurablePartition.splitAllParts (MeasurablePartition.splitAllParts P S₀ hS₀) T₀ hT₀) ≥
      energy W P + (rectIntegralDiff W (stepify P W) S₀ T₀) ^ 2 := by
  -- Step 1: By Jensen, (rectIntegralDiff)² ≤ ∫_{S₀×T₀} (W - stepify P W)²
  -- Step 2: ∫_{S₀×T₀} (W - stepify P W)² ≤ ∫∫ (W - stepify P W)² = defect P
  -- Step 3: defect P = ∫∫ W² - energy P, energy Q ≤ ∫∫ W² (since defect Q ≥ 0)
  -- Combining: (rectIntegralDiff)² ≤ defect P ≤ energy Q - energy P + defect Q
  -- This doesn't directly work. We need the stronger bound via Cauchy-Schwarz on partition cells.
  -- Use the combinatorial approach with weighted Cauchy-Schwarz.
  classical
  set Q := MeasurablePartition.splitAllParts (MeasurablePartition.splitAllParts P S₀ hS₀) T₀ hT₀
  -- Abbreviations for the weight and difference functions
  set w : Set α → ℝ := fun S => (μ (S ∩ S₀)).toReal
  set v : Set α → ℝ := fun T => (μ (T ∩ T₀)).toReal
  set dd : Set α → Set α → ℝ := fun S T =>
    if (μ (S ∩ S₀) = 0 ∨ μ (T ∩ T₀) = 0) then 0
    else rectAverage W (S ∩ S₀) (T ∩ T₀) - rectAverage W S T
  -- Key property: when either measure is 0, the weighted product is 0
  have h_wvd : ∀ S ∈ P.parts, ∀ T ∈ P.parts,
      w S * v T * dd S T =
      (μ (S ∩ S₀)).toReal * (μ (T ∩ T₀)).toReal *
        (rectAverage W (S ∩ S₀) (T ∩ T₀) - rectAverage W S T) := by
    intro S _ T _; simp only [w, v, dd]
    by_cases h1 : μ (S ∩ S₀) = 0 <;> by_cases h2 : μ (T ∩ T₀) = 0 <;> simp [h1, h2]
  -- ===== Step A: Decompose rectIntegralDiff =====
  -- rectIntegralDiff = Σ_{S,T} μ(S∩S₀)μ(T∩T₀)(a_{S∩S₀,T∩T₀} - a_{S,T})
  have h_integral_decomp : rectIntegralDiff W (stepify P W) S₀ T₀ =
      P.parts.sum fun S => P.parts.sum fun T => w S * v T * dd S T := by
    -- Suffices to show = Σ μ(S∩S₀)·μ(T∩T₀)·(a_{S∩S₀,T∩T₀} - a_{S,T})
    suffices h_main : rectIntegralDiff W (stepify P W) S₀ T₀ =
        ∑ S ∈ P.parts, ∑ T ∈ P.parts,
          (μ (S ∩ S₀)).toReal * (μ (T ∩ T₀)).toReal *
            (rectAverage W (S ∩ S₀) (T ∩ T₀) - rectAverage W S T) by
      rw [h_main]
      apply Finset.sum_congr rfl; intro S hS
      apply Finset.sum_congr rfl; intro T hT
      exact (h_wvd S hS T hT).symm
    -- Unfold rectIntegralDiff
    unfold rectIntegralDiff
    -- Integrability
    have h_int_diff : IntegrableOn (fun p => W.toAEEqFun p - (stepify P W).toAEEqFun p)
        (S₀ ×ˢ T₀) (μ.prod μ) :=
      ((SymmKernel.graphon_integrable W).integrableOn).sub
        ((SymmKernel.graphon_integrable (stepify P W)).integrableOn)
    -- The cells (S∩S₀)×(T∩T₀) are pairwise disjoint
    have h_cells_disj : (↑(P.parts ×ˢ P.parts) : Set (Set α × Set α)).Pairwise
        (Function.onFun Disjoint fun st => (st.1 ∩ S₀) ×ˢ (st.2 ∩ T₀)) := by
      intro ⟨S₁, T₁⟩ h₁ ⟨S₂, T₂⟩ h₂ hne
      simp only [Function.onFun]
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at h₁ h₂
      by_cases hS : S₁ = S₂
      · subst hS
        have hT : T₁ ≠ T₂ := fun h => hne (Prod.ext rfl h)
        have h_disj_T := P.pairwiseDisjoint h₁.2 h₂.2 hT
        exact Disjoint.mono (Set.prod_mono_right Set.inter_subset_left)
          (Set.prod_mono_right Set.inter_subset_left)
          (Set.disjoint_left.mpr fun p hp1 hp2 =>
            Set.disjoint_left.mp h_disj_T (Set.mem_prod.mp hp1).2 (Set.mem_prod.mp hp2).2)
      · have h_disj_S := P.pairwiseDisjoint h₁.1 h₂.1 hS
        exact Disjoint.mono (Set.prod_mono_left Set.inter_subset_left)
          (Set.prod_mono_left Set.inter_subset_left)
          (Set.disjoint_left.mpr fun p hp1 hp2 =>
            Set.disjoint_left.mp h_disj_S (Set.mem_prod.mp hp1).1 (Set.mem_prod.mp hp2).1)
    -- Measurability of cells
    have h_cells_meas : ∀ st ∈ P.parts ×ˢ P.parts,
        MeasurableSet ((st.1 ∩ S₀) ×ˢ (st.2 ∩ T₀)) := by
      intro ⟨S, T⟩ hst
      simp only [Finset.mem_product] at hst
      exact ((P.measurableSet_part hst.1).inter hS₀).prod
        ((P.measurableSet_part hst.2).inter hT₀)
    -- Integrability on each cell
    have h_int_cells : ∀ st ∈ P.parts ×ˢ P.parts,
        IntegrableOn (fun p => W.toAEEqFun p - (stepify P W).toAEEqFun p)
          ((st.1 ∩ S₀) ×ˢ (st.2 ∩ T₀)) (μ.prod μ) := fun _ _ =>
      h_int_diff.mono (Set.prod_mono Set.inter_subset_right Set.inter_subset_right) le_rfl
    -- The cells cover S₀ × T₀ a.e.
    have h_cover : ∀ᵐ p ∂(μ.prod μ).restrict (S₀ ×ˢ T₀),
        p ∈ ⋃ st ∈ P.parts ×ˢ P.parts, (st.1 ∩ S₀) ×ˢ (st.2 ∩ T₀) := by
      rw [ae_restrict_iff' (hS₀.prod hT₀)]
      filter_upwards [Measure.QuasiMeasurePreserving.ae
          Measure.quasiMeasurePreserving_fst P.ae_covers,
        Measure.QuasiMeasurePreserving.ae
          Measure.quasiMeasurePreserving_snd P.ae_covers] with p h1 h2 hp
      obtain ⟨S, hS, hpS⟩ := h1
      obtain ⟨T, hT, hpT⟩ := h2
      simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_product, Prod.exists]
      exact ⟨S, T, ⟨hS, hT⟩, Set.mem_prod.mpr
        ⟨⟨hpS, (Set.mem_prod.mp hp).1⟩, ⟨hpT, (Set.mem_prod.mp hp).2⟩⟩⟩
    -- Decompose the integral over S₀×T₀ into sum over cells
    -- The union of cells ⊆ S₀×T₀, and S₀×T₀ \ cells is null, so the sets are ae equal
    set cellUnion := ⋃ st ∈ P.parts ×ˢ P.parts, (st.1 ∩ S₀) ×ˢ (st.2 ∩ T₀)
    have h_sub : cellUnion ⊆ S₀ ×ˢ T₀ := by
      intro p hp
      simp only [cellUnion, Set.mem_iUnion, Finset.mem_coe] at hp
      obtain ⟨⟨S, T⟩, _, hp_mem⟩ := hp
      exact Set.mem_prod.mpr ⟨(Set.mem_prod.mp hp_mem).1.2, (Set.mem_prod.mp hp_mem).2.2⟩
    have h_cellUnion_meas : MeasurableSet cellUnion :=
      MeasurableSet.biUnion (P.parts ×ˢ P.parts).countable_toSet h_cells_meas
    have h_ae_eq : S₀ ×ˢ T₀ =ᵐ[μ.prod μ] cellUnion := by
      rw [ae_eq_set]
      refine ⟨?_, by rw [Set.diff_eq_empty.mpr h_sub]; exact measure_empty⟩
      -- μ((S₀×T₀) \ cellUnion) = 0
      -- h_cover gives (μ.prod μ).restrict (S₀×T₀) {p | p ∉ cellUnion} = 0
      have h0 : (μ.prod μ).restrict (S₀ ×ˢ T₀) cellUnionᶜ = 0 :=
        ae_iff.mp h_cover
      rwa [Measure.restrict_apply h_cellUnion_meas.compl, Set.inter_comm] at h0
    have h_eq_union :
        ∫ p in S₀ ×ˢ T₀, (W.toAEEqFun p - (stepify P W).toAEEqFun p) ∂(μ.prod μ) =
        ∫ p in cellUnion, (W.toAEEqFun p - (stepify P W).toAEEqFun p) ∂(μ.prod μ) :=
      setIntegral_congr_set h_ae_eq
    rw [h_eq_union, integral_biUnion_finset _ h_cells_meas h_cells_disj h_int_cells,
      Finset.sum_product]
    -- Show each cell integral equals the corresponding term
    apply Finset.sum_congr rfl; intro S hS
    apply Finset.sum_congr rfl; intro T hT
    by_cases hμS0 : μ (S ∩ S₀) = 0
    · have h_prod_zero : (μ.prod μ) ((S ∩ S₀) ×ˢ (T ∩ T₀)) = 0 := by
        rw [Measure.prod_prod, hμS0, zero_mul]
      rw [setIntegral_measure_zero _ h_prod_zero]; simp [hμS0]
    by_cases hμT0 : μ (T ∩ T₀) = 0
    · have h_prod_zero : (μ.prod μ) ((S ∩ S₀) ×ˢ (T ∩ T₀)) = 0 := by
        rw [Measure.prod_prod, hμT0, mul_zero]
      rw [setIntegral_measure_zero _ h_prod_zero]; simp [hμT0]
    -- Both measures nonzero: use the pre-computed h_cell_integral
    -- (The goal after by_cases has (S, T).1 and (S, T).2 which are definitionally S and T,
    --  but we avoid the issue by using the pre-proved lemma directly.)
    show ∫ p in (S ∩ S₀) ×ˢ (T ∩ T₀), (W.toAEEqFun p - (stepify P W).toAEEqFun p) ∂(μ.prod μ) =
      (μ (S ∩ S₀)).toReal * (μ (T ∩ T₀)).toReal * (rectAverage W (S ∩ S₀) (T ∩ T₀) - rectAverage W S T)
    -- Split integral
    rw [integral_sub
      (SymmKernel.graphon_integrable W).integrableOn
      (SymmKernel.graphon_integrable (stepify P W)).integrableOn]
    -- ∫ stepify on cell = rectAverage W S T · μ(S∩S₀) · μ(T∩T₀)
    have h_stepify_cell :
        ∫ p in (S ∩ S₀) ×ˢ (T ∩ T₀), (stepify P W).toAEEqFun p ∂(μ.prod μ) =
        rectAverage W S T * (μ (S ∩ S₀)).toReal * (μ (T ∩ T₀)).toReal := by
      have h_ae_eq : ∀ᵐ p ∂(μ.prod μ),
          p ∈ (S ∩ S₀) ×ˢ (T ∩ T₀) → (stepify P W).toAEEqFun p = rectAverage W S T := by
        filter_upwards [stepify_ae P W] with p h_step hp
        rw [h_step]
        exact stepifyFun_eq_rectAverage P W hS hT
          (Set.prod_mono Set.inter_subset_left Set.inter_subset_left hp)
      rw [setIntegral_congr_ae (((P.measurableSet_part hS).inter hS₀).prod
        ((P.measurableSet_part hT).inter hT₀)) h_ae_eq,
        setIntegral_const, smul_eq_mul]
      simp only [Measure.real, Measure.prod_prod, ENNReal.toReal_mul]; ring
    -- ∫ W on cell = rectAverage W (S∩S₀) (T∩T₀) · μ(S∩S₀) · μ(T∩T₀)
    have h_W_cell :
        ∫ p in (S ∩ S₀) ×ˢ (T ∩ T₀), W.toAEEqFun p ∂(μ.prod μ) =
        rectAverage W (S ∩ S₀) (T ∩ T₀) * (μ (S ∩ S₀)).toReal * (μ (T ∩ T₀)).toReal := by
      have ha : rectAverage W (S ∩ S₀) (T ∩ T₀) = (μ (S ∩ S₀)).toReal⁻¹ * (μ (T ∩ T₀)).toReal⁻¹ *
          ∫ p in (S ∩ S₀) ×ˢ (T ∩ T₀), W.toAEEqFun p ∂(μ.prod μ) := by
        unfold rectAverage; simp [hμS0, hμT0]
      rw [ha]
      have hμS_pos : (μ (S ∩ S₀)).toReal ≠ 0 :=
        ne_of_gt (ENNReal.toReal_pos hμS0 (measure_lt_top μ _).ne)
      have hμT_pos : (μ (T ∩ T₀)).toReal ≠ 0 :=
        ne_of_gt (ENNReal.toReal_pos hμT0 (measure_lt_top μ _).ne)
      field_simp
    rw [h_stepify_cell, h_W_cell]; ring
  -- ===== Step B: Pythagorean identity + Jensen =====
  -- We prove energy Q - energy P ≥ (rectIntegralDiff)² directly using:
  -- (1) energy Q - energy P = defect P - defect Q  (from L² identity)
  -- (2) defect P ≥ defect Q + (rid)²  (per-cell integral_sq_shift)
  --
  -- Part (2) uses: for each P-cell (S,T), the defect on S×T decomposes
  -- (via integral_sq_shift on the sub-rectangle (S∩S₀)×(T∩T₀))
  -- into a residual variance plus a correction ≥ w·v·dd².
  -- Summing and applying Cauchy-Schwarz gives (rid)².
  -- The residual variances collectively bound defect Q from below.
  --
  -- Actually, we use a simpler approach:
  -- (rid)² ≤ Σ w·v·dd² (by Cauchy-Schwarz)
  -- Σ w·v·dd² ≤ defect P (by per-cell integral_sq_shift)
  -- So (rid)² ≤ defect P
  -- Combined with energy Q - energy P = defect P - defect Q
  -- we get energy Q - energy P = defect P - defect Q
  -- But defect Q ≥ 0 means defect P - defect Q ≤ defect P, not ≥ rid².
  -- THIS APPROACH IS INSUFFICIENT.
  --
  -- Instead, we prove the result directly via setIntegral_stepify_eq_on_cell.
  -- Key identity: ∫_{S₀×T₀} stepify Q W = ∫_{S₀×T₀} W
  -- (since S₀×T₀ can be decomposed into Q-cells).
  -- This gives: rectIntegralDiff W (stepify P W) S₀ T₀
  --           = ∫_{S₀×T₀} (W - stepify P W) = ∫_{S₀×T₀} (stepify Q W - stepify P W)
  -- Then: (rid)² = (∫_{S₀×T₀} (stepify Q W - stepify P W))²
  --             ≤ ∫ (stepify Q W - stepify P W)²  (by Jensen/probability measure)
  --             = defect P - defect Q  (by Pythagorean identity)
  --             = energy Q - energy P
  --
  -- Step B.1: ∫_{S₀×T₀} stepify Q W = ∫_{S₀×T₀} W
  -- Decompose S₀×T₀ into cells (S∩S₀)×(T∩T₀) for S,T ∈ P.parts.
  -- Each such cell is a union of Q-cells, and integral is preserved on each.
  -- We use h_integral_decomp which already handles the decomposition.
  -- Specifically, rid = Σ w·v·dd = Σ μ(S∩S₀)μ(T∩T₀)(avg(S∩S₀,T∩T₀) - avg_P(S,T))
  -- This equals ∫_{S₀×T₀} (W - stepify P W) (already proved).
  --
  -- Step B.2: Per-cell bound using integral_sq_shift
  -- For each P-cell (S,T):
  -- ∫_{S×T}(W - avg_P)² ≥ ∫_{(S∩S₀)×(T∩T₀)}(W-avg_P)²
  --                      = ∫_{(S∩S₀)×(T∩T₀)}(W-avg')² + μ(S∩S₀)μ(T∩T₀)(avg'-avg_P)²
  -- where avg' = rectAverage W (S∩S₀) (T∩T₀).
  -- So defect_rect(P,S,T) ≥ w·v·dd² and defect P ≥ Σ w·v·dd².
  --
  -- Step B.3: Cauchy-Schwarz: (Σ w·v·dd)² ≤ Σ w·v·dd² (weighted)
  -- This gives (rid)² ≤ Σ w·v·dd² ≤ defect P.
  --
  -- Step B.4: Energy identity: energy Q - energy P = defect P - defect Q.
  -- So energy Q ≥ energy P + (rid)² requires defect P - defect Q ≥ (rid)².
  -- Since (rid)² ≤ defect P and defect Q ≥ 0, we only get defect P - defect Q ≥ (rid)² - defect Q.
  -- THIS IS STILL NOT ENOUGH without defect Q ≤ 0.
  --
  -- THE FIX: Use setIntegral_stepify_eq_on_cell and the Pythagorean identity.
  -- ∫(W - stepify P W)² = ∫(W - stepify Q W)² + ∫(stepify Q W - stepify P W)²
  --                      + 2∫(W - stepify Q W)(stepify Q W - stepify P W)
  -- Cross term vanishes (proved via setIntegral_stepify_eq_on_cell).
  -- So defect P = defect Q + ∫(stepify Q W - stepify P W)²
  -- and ∫(stepify Q W - stepify P W)² ≥ (∫_{S₀×T₀}(stepify Q W - stepify P W))²
  --                                    = (∫_{S₀×T₀}(W - stepify P W))² = (rid)²
  -- Therefore: defect P - defect Q ≥ (rid)² and energy Q - energy P ≥ (rid)².
  --
  -- IMPLEMENTATION: We prove (rid)² ≤ defect P - defect Q directly.
  -- L² identity
  have h_l2_P := l2_norm_eq_energy_add_defect W P
  have h_l2_Q := l2_norm_eq_energy_add_defect W Q
  -- energy Q - energy P = defect P - defect Q
  have h_ediff : energy W Q - energy W P = defect W P - defect W Q := by linarith
  -- defect P ≥ (rid)²: Jensen on S₀ × T₀
  -- Integrability
  have hW_int : Integrable W.toAEEqFun (μ.prod μ) := SymmKernel.graphon_integrable W
  have hfP_int : Integrable (stepify P W).toAEEqFun (μ.prod μ) :=
    SymmKernel.graphon_integrable (stepify P W)
  have h_diff_int : Integrable (fun p => W.toAEEqFun p - (stepify P W).toAEEqFun p) (μ.prod μ) :=
    hW_int.sub hfP_int
  -- defect P = ∫(W - stepify P W)²  (integral over full space)
  -- This follows from l2_norm_eq_energy_add_defect + algebraic manipulation.
  -- Actually, defect P is defined as a sum over P-cells of ∫(W - avg)², which equals ∫(W - f_P)²
  -- where f_P is the stepification, since f_P = avg on each cell a.e.
  -- For now, we use the per-cell bound to get defect P ≥ (rid)²:
  -- Per-cell bound: defect_rect(P,S,T) ≥ w·v·dd² by integral_sq_shift
  have h_per_cell : ∀ S ∈ P.parts, ∀ T ∈ P.parts,
      ∫ p in S ×ˢ T, (W.toAEEqFun p - rectAverage W S T) ^ 2 ∂(μ.prod μ) ≥
        w S * v T * dd S T ^ 2 := by
    intro S hS T hT
    by_cases hμS0 : μ (S ∩ S₀) = 0
    · have : w S = 0 := by simp [w, hμS0]
      simp [this]
      exact setIntegral_nonneg_of_ae_restrict (ae_of_all _ (fun _ => sq_nonneg _))
    by_cases hμT0 : μ (T ∩ T₀) = 0
    · have : v T = 0 := by simp [v, hμT0]
      simp [this]
      exact setIntegral_nonneg_of_ae_restrict (ae_of_all _ (fun _ => sq_nonneg _))
    have hS_meas := P.measurableSet_part hS
    have hT_meas := P.measurableSet_part hT
    have h_shift := integral_sq_shift W (S ∩ S₀) (T ∩ T₀)
      (hS_meas.inter hS₀) (hT_meas.inter hT₀) (rectAverage W S T)
    have h_mono : ∫ p in (S ∩ S₀) ×ˢ (T ∩ T₀),
        (W.toAEEqFun p - rectAverage W S T) ^ 2 ∂(μ.prod μ) ≤
        ∫ p in S ×ˢ T, (W.toAEEqFun p - rectAverage W S T) ^ 2 ∂(μ.prod μ) := by
      apply setIntegral_mono_set
      · apply Measure.integrableOn_of_bounded (measure_lt_top _ _).ne
        · exact ((continuous_pow 2).comp_aestronglyMeasurable
            ((SymmKernel.graphon_integrable W).sub
              (integrable_const (rectAverage W S T))).aestronglyMeasurable)
        · have hIcc := rectAverage_mem_Icc W S T hS_meas hT_meas
          filter_upwards [ae_restrict_of_ae W.ae_mem_Icc] with p hp
          simp only [Real.norm_eq_abs]
          rw [show |(W.toAEEqFun p - rectAverage W S T) ^ 2| =
            (W.toAEEqFun p - rectAverage W S T) ^ 2 from abs_of_nonneg (sq_nonneg _)]
          exact (sq_le_one_iff_abs_le_one _).mpr
            (abs_sub_le_iff.mpr ⟨by linarith [hp.2, hIcc.1], by linarith [hIcc.2, hp.1]⟩)
      · exact ae_of_all _ fun _ => sq_nonneg _
      · exact ae_of_all _ fun p hp =>
          Set.prod_mono Set.inter_subset_left Set.inter_subset_left hp
    have h_corr : (μ (S ∩ S₀)).toReal * (μ (T ∩ T₀)).toReal *
        (rectAverage W (S ∩ S₀) (T ∩ T₀) - rectAverage W S T) ^ 2 =
        w S * v T * dd S T ^ 2 := by simp [w, v, dd, hμS0, hμT0]
    have h_res_nonneg : ∫ p in (S ∩ S₀) ×ˢ (T ∩ T₀),
        (W.toAEEqFun p - rectAverage W (S ∩ S₀) (T ∩ T₀)) ^ 2 ∂(μ.prod μ) ≥ 0 :=
      setIntegral_nonneg_of_ae_restrict (ae_of_all _ (fun _ => sq_nonneg _))
    linarith
  -- Step B.2: defect P ≥ Σ w·v·dd²
  have h_defect_ge_sum : defect W P ≥
      P.parts.sum fun S => P.parts.sum fun T => w S * v T * dd S T ^ 2 := by
    unfold defect
    apply Finset.sum_le_sum; intro S hS
    apply Finset.sum_le_sum; intro T hT
    exact h_per_cell S hS T hT
  -- Step B.3: Cauchy-Schwarz: (Σ w·v·dd)² ≤ Σ w·v·dd²
  have hw : ∀ S ∈ P.parts, 0 ≤ w S := fun _ _ => ENNReal.toReal_nonneg
  have hv : ∀ T ∈ P.parts, 0 ≤ v T := fun _ _ => ENNReal.toReal_nonneg
  have hW : P.parts.sum w ≤ 1 := by
    show P.parts.sum (fun S => (μ (S ∩ S₀)).toReal) ≤ 1
    have h_disj : (P.parts : Set (Set α)).PairwiseDisjoint (fun S => S ∩ S₀) :=
      fun S hS T hT hne =>
        (P.pairwiseDisjoint hS hT hne).mono Set.inter_subset_left Set.inter_subset_left
    calc P.parts.sum (fun S => (μ (S ∩ S₀)).toReal)
        = (μ (⋃ S ∈ P.parts, S ∩ S₀)).toReal := by
          rw [measure_biUnion_finset (fun S hS T hT hne => h_disj hS hT hne)
            (fun S hS => (P.measurableSet_part hS).inter hS₀)]
          exact (ENNReal.toReal_sum (fun _ _ => measure_ne_top μ _)).symm
      _ ≤ (μ Set.univ).toReal :=
          ENNReal.toReal_mono (measure_ne_top μ Set.univ) (measure_mono (Set.subset_univ _))
      _ = 1 := by rw [measure_univ]; simp
  have hV : P.parts.sum v ≤ 1 := by
    show P.parts.sum (fun T => (μ (T ∩ T₀)).toReal) ≤ 1
    have h_disj : (P.parts : Set (Set α)).PairwiseDisjoint (fun T => T ∩ T₀) :=
      fun S hS T hT hne =>
        (P.pairwiseDisjoint hS hT hne).mono Set.inter_subset_left Set.inter_subset_left
    calc P.parts.sum (fun T => (μ (T ∩ T₀)).toReal)
        = (μ (⋃ T ∈ P.parts, T ∩ T₀)).toReal := by
          rw [measure_biUnion_finset (fun S hS T hT hne => h_disj hS hT hne)
            (fun T hT => (P.measurableSet_part hT).inter hT₀)]
          exact (ENNReal.toReal_sum (fun _ _ => measure_ne_top μ _)).symm
      _ ≤ (μ Set.univ).toReal :=
          ENNReal.toReal_mono (measure_ne_top μ Set.univ) (measure_mono (Set.subset_univ _))
      _ = 1 := by rw [measure_univ]; simp
  have h_cs := sq_weighted_double_sum_le P.parts P.parts w v dd hw hv hW hV
  -- (rid)² ≤ Σ w·v·dd² ≤ defect P
  have h_rid_le_defect : (rectIntegralDiff W (stepify P W) S₀ T₀) ^ 2 ≤ defect W P := by
    rw [h_integral_decomp]; linarith
  -- defect Q ≥ 0
  have h_defect_Q_nonneg := defect_nonneg W Q
  -- ===== Pythagorean approach =====
  -- Step 1: Key fact: ∫_{S₀×T₀} stepify Q W = ∫_{S₀×T₀} W
  -- This follows from the conditional expectation property of stepify:
  -- S₀×T₀ is (a.e.) a union of cells (S∩S₀)×(T∩T₀) for S,T ∈ P.parts,
  -- and each such cell is (a.e.) a union of Q-cells, on which the stepify integral
  -- equals the W integral.
  -- Since we already proved (in Step A) that the integral decomposition gives
  -- rid = Σ w·v·dd = ∫_{S₀×T₀}(W - stepify P W), we just need:
  -- ∫_{S₀×T₀} stepify Q W = ∫_{S₀×T₀} W.
  -- Equivalently, ∫_{S₀×T₀} (stepify Q W - W) = 0.
  -- Q refines P (transitively via P')
  set P' := MeasurablePartition.splitAllParts P S₀ hS₀
  have hQP' : Refines Q P' := MeasurablePartition.splitAllParts_refines P' T₀ hT₀
  have hP'P : Refines P' P := MeasurablePartition.splitAllParts_refines P S₀ hS₀
  have hQP : Refines Q P := hP'P.trans hQP'
  have h_stepify_Q_preserves : ∫ p in S₀ ×ˢ T₀,
      (stepify Q W).toAEEqFun p ∂(μ.prod μ) =
      ∫ p in S₀ ×ˢ T₀, W.toAEEqFun p ∂(μ.prod μ) := by
    -- For each S, T ∈ P.parts, the integral on the sub-cell (S∩S₀)×(T∩T₀) is preserved.
    -- We show this by decomposing into Q-cell products and applying
    -- setIntegral_stepify_eq_on_cell.
    -- Step 1: Decompose S₀×T₀ into (S∩S₀)×(T∩T₀) cells.
    -- (Same decomposition as Step A.)
    -- pairwise disjointness of cells
    have h_cells_disj' : (↑(P.parts ×ˢ P.parts) : Set (Set α × Set α)).Pairwise
        (Function.onFun Disjoint fun st => (st.1 ∩ S₀) ×ˢ (st.2 ∩ T₀)) := by
      intro ⟨S₁, T₁⟩ h₁ ⟨S₂, T₂⟩ h₂ hne
      simp only [Function.onFun]
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at h₁ h₂
      by_cases hS : S₁ = S₂
      · subst hS
        have hT : T₁ ≠ T₂ := fun h => hne (Prod.ext rfl h)
        exact Disjoint.mono (Set.prod_mono_right Set.inter_subset_left)
          (Set.prod_mono_right Set.inter_subset_left)
          (Set.disjoint_left.mpr fun p hp1 hp2 =>
            Set.disjoint_left.mp (P.pairwiseDisjoint h₁.2 h₂.2 hT)
              (Set.mem_prod.mp hp1).2 (Set.mem_prod.mp hp2).2)
      · exact Disjoint.mono (Set.prod_mono_left Set.inter_subset_left)
          (Set.prod_mono_left Set.inter_subset_left)
          (Set.disjoint_left.mpr fun p hp1 hp2 =>
            Set.disjoint_left.mp (P.pairwiseDisjoint h₁.1 h₂.1 hS)
              (Set.mem_prod.mp hp1).1 (Set.mem_prod.mp hp2).1)
    -- measurability of cells
    have h_cells_meas' : ∀ st ∈ P.parts ×ˢ P.parts,
        MeasurableSet ((st.1 ∩ S₀) ×ˢ (st.2 ∩ T₀)) := by
      intro ⟨S, T⟩ hst
      simp only [Finset.mem_product] at hst
      exact ((P.measurableSet_part hst.1).inter hS₀).prod
        ((P.measurableSet_part hst.2).inter hT₀)
    -- cell union
    set cellU := ⋃ st ∈ P.parts ×ˢ P.parts, (st.1 ∩ S₀) ×ˢ (st.2 ∩ T₀)
    have h_sub' : cellU ⊆ S₀ ×ˢ T₀ := by
      intro p hp
      simp only [cellU, Set.mem_iUnion] at hp
      obtain ⟨⟨S, T⟩, _, hp_mem⟩ := hp
      exact Set.mem_prod.mpr ⟨(Set.mem_prod.mp hp_mem).1.2, (Set.mem_prod.mp hp_mem).2.2⟩
    have h_cellU_meas : MeasurableSet cellU :=
      MeasurableSet.biUnion (P.parts ×ˢ P.parts).countable_toSet h_cells_meas'
    have h_cover' : ∀ᵐ p ∂(μ.prod μ).restrict (S₀ ×ˢ T₀), p ∈ cellU := by
      rw [ae_restrict_iff' (hS₀.prod hT₀)]
      filter_upwards [Measure.QuasiMeasurePreserving.ae
          Measure.quasiMeasurePreserving_fst P.ae_covers,
        Measure.QuasiMeasurePreserving.ae
          Measure.quasiMeasurePreserving_snd P.ae_covers] with p h1 h2 hp
      obtain ⟨S, hS, hpS⟩ := h1; obtain ⟨T, hT, hpT⟩ := h2
      simp only [cellU, Set.mem_iUnion, Finset.mem_coe, Finset.mem_product, Prod.exists]
      exact ⟨S, T, ⟨hS, hT⟩, Set.mem_prod.mpr
        ⟨⟨hpS, (Set.mem_prod.mp hp).1⟩, ⟨hpT, (Set.mem_prod.mp hp).2⟩⟩⟩
    have h_ae_eq' : S₀ ×ˢ T₀ =ᵐ[μ.prod μ] cellU := by
      rw [ae_eq_set]
      refine ⟨?_, by rw [Set.diff_eq_empty.mpr h_sub']; exact measure_empty⟩
      have h0 : (μ.prod μ).restrict (S₀ ×ˢ T₀) cellUᶜ = 0 := ae_iff.mp h_cover'
      rwa [Measure.restrict_apply h_cellU_meas.compl, Set.inter_comm] at h0
    -- integrability on each cell
    have h_int_stepQ : ∀ st ∈ P.parts ×ˢ P.parts,
        IntegrableOn (fun p => (stepify Q W).toAEEqFun p) ((st.1 ∩ S₀) ×ˢ (st.2 ∩ T₀)) (μ.prod μ) :=
      fun _ _ => (SymmKernel.graphon_integrable (stepify Q W)).integrableOn
    have h_int_W' : ∀ st ∈ P.parts ×ˢ P.parts,
        IntegrableOn (fun p => W.toAEEqFun p) ((st.1 ∩ S₀) ×ˢ (st.2 ∩ T₀)) (μ.prod μ) :=
      fun _ _ => (SymmKernel.graphon_integrable W).integrableOn
    -- Step 2: On each cell (S∩S₀)×(T∩T₀), the Q-cell products cover it a.e.
    -- and setIntegral_stepify_eq_on_cell gives the equality.
    have h_cell_eq : ∀ S ∈ P.parts, ∀ T ∈ P.parts,
        ∫ p in (S ∩ S₀) ×ˢ (T ∩ T₀), (stepify Q W).toAEEqFun p ∂(μ.prod μ) =
        ∫ p in (S ∩ S₀) ×ˢ (T ∩ T₀), W.toAEEqFun p ∂(μ.prod μ) := by
      intro S hS T hT
      -- The Q-parts within S∩S₀ and T∩T₀
      haveI : DecidablePred (· ⊆ S ∩ S₀) := Classical.decPred _
      haveI : DecidablePred (· ⊆ T ∩ T₀) := Classical.decPred _
      set QA := Q.parts.filter (· ⊆ S ∩ S₀)
      set QB := Q.parts.filter (· ⊆ T ∩ T₀)
      have hQA_sub : ∀ U ∈ QA, U ∈ Q.parts := fun U hU => (Finset.mem_filter.mp hU).1
      have hQB_sub : ∀ V ∈ QB, V ∈ Q.parts := fun V hV => (Finset.mem_filter.mp hV).1
      have hQA_subset : ∀ U ∈ QA, U ⊆ S ∩ S₀ := fun U hU => (Finset.mem_filter.mp hU).2
      have hQB_subset : ∀ V ∈ QB, V ⊆ T ∩ T₀ := fun V hV => (Finset.mem_filter.mp hV).2
      -- Pairwise disjointness of Q-cells
      have h_disj : (↑(QA ×ˢ QB) : Set (Set α × Set α)).Pairwise
          (Function.onFun Disjoint fun st => st.1 ×ˢ st.2) := by
        intro ⟨U₁, V₁⟩ h₁ ⟨U₂, V₂⟩ h₂ hne
        simp only [Function.onFun, Finset.coe_product, Set.mem_prod, Finset.mem_coe] at h₁ h₂ ⊢
        by_cases hU : U₁ = U₂
        · subst hU; have hV : V₁ ≠ V₂ := fun h => hne (Prod.ext rfl h)
          exact Disjoint.mono (Set.prod_mono_right Subset.rfl) (Set.prod_mono_right Subset.rfl)
            (Set.disjoint_left.mpr fun p hp1 hp2 =>
              Set.disjoint_left.mp (Q.pairwiseDisjoint (hQB_sub V₁ h₁.2) (hQB_sub V₂ h₂.2) hV)
                (Set.mem_prod.mp hp1).2 (Set.mem_prod.mp hp2).2)
        · exact Disjoint.mono (Set.prod_mono_left Subset.rfl) (Set.prod_mono_left Subset.rfl)
            (Set.disjoint_left.mpr fun p hp1 hp2 =>
              Set.disjoint_left.mp (Q.pairwiseDisjoint (hQA_sub U₁ h₁.1) (hQA_sub U₂ h₂.1) hU)
                (Set.mem_prod.mp hp1).1 (Set.mem_prod.mp hp2).1)
      -- Measurability
      have h_meas : ∀ st ∈ QA ×ˢ QB, MeasurableSet (st.1 ×ˢ st.2) := by
        intro ⟨U, V⟩ hst; simp only [Finset.mem_product] at hst
        exact (Q.measurableSet_part (hQA_sub U hst.1)).prod (Q.measurableSet_part (hQB_sub V hst.2))
      -- Q-cells cover (S∩S₀)×(T∩T₀) a.e.
      set qUnion := ⋃ st ∈ QA ×ˢ QB, st.1 ×ˢ st.2
      have h_qsub : qUnion ⊆ (S ∩ S₀) ×ˢ (T ∩ T₀) := by
        intro p hp; simp only [qUnion, Set.mem_iUnion] at hp
        obtain ⟨⟨U, V⟩, hst, hp_mem⟩ := hp
        simp only [Finset.mem_coe, Finset.mem_product] at hst
        exact Set.mem_prod.mpr ⟨hQA_subset U hst.1 (Set.mem_prod.mp hp_mem).1,
          hQB_subset V hst.2 (Set.mem_prod.mp hp_mem).2⟩
      have h_qmeas : MeasurableSet qUnion :=
        MeasurableSet.biUnion (QA ×ˢ QB).countable_toSet h_meas
      have h_qcover : ∀ᵐ p ∂(μ.prod μ).restrict ((S ∩ S₀) ×ˢ (T ∩ T₀)), p ∈ qUnion := by
        rw [ae_restrict_iff' (((P.measurableSet_part hS).inter hS₀).prod
          ((P.measurableSet_part hT).inter hT₀))]
        filter_upwards [Measure.QuasiMeasurePreserving.ae
            Measure.quasiMeasurePreserving_fst Q.ae_covers,
          Measure.QuasiMeasurePreserving.ae
            Measure.quasiMeasurePreserving_snd Q.ae_covers] with p h1 h2 hp
        obtain ⟨U, hU_mem, hpU⟩ := h1; obtain ⟨V, hV_mem, hpV⟩ := h2
        -- U ⊆ S ∩ S₀: By refinement Q → P', U ⊆ some P'-part.
        -- Since p.1 ∈ U and p.1 ∈ S∩S₀ (a P'-part), by P'.pairwiseDisjoint U ⊆ S∩S₀.
        have hU_sub : U ⊆ S ∩ S₀ := by
          obtain ⟨S'', hS''_mem, hU_sub⟩ := hQP' U hU_mem
          have hp1_S'' : p.1 ∈ S'' := hU_sub hpU
          -- S ∩ S₀ is a P'-part
          have hSS0_mem : S ∩ S₀ ∈ P'.parts := by
            simp only [P', MeasurablePartition.splitAllParts]
            exact Finset.mem_biUnion.mpr ⟨S, hS, Finset.mem_insert_self _ _⟩
          have hSS0_eq : S ∩ S₀ = S'' := by
            by_contra h
            exact Set.disjoint_left.mp (P'.pairwiseDisjoint hSS0_mem hS''_mem h)
              ((Set.mem_prod.mp hp).1) hp1_S''
          rw [hSS0_eq]; exact hU_sub
        -- V ⊆ T ∩ T₀: Q = splitAllParts P' T₀, so V = U'∩T₀ or U'\T₀ for some U' ∈ P'.parts.
        -- Since p.2 ∈ V ∩ T₀, V = U'∩T₀ ⊆ T₀. Also U' ⊆ T' for some T'∈P, and p.2∈T, so T'=T.
        have hV_sub : V ⊆ T ∩ T₀ := by
          -- V ∈ Q.parts = P'.parts.biUnion (fun U' => {U' ∩ T₀, U' \ T₀})
          simp only [Q, MeasurablePartition.splitAllParts] at hV_mem
          rw [Finset.mem_biUnion] at hV_mem
          obtain ⟨U', hU'_mem, hV_in⟩ := hV_mem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hV_in
          rcases hV_in with rfl | rfl
          · -- V = U' ∩ T₀, so V ⊆ T₀
            -- Also U' ∈ P'.parts, and P' refines P, so U' ⊆ T' for some T'∈P
            intro y hy
            obtain ⟨T', hT'_mem, hU'_sub⟩ := hP'P U' hU'_mem
            have hp2_T' : p.2 ∈ T' := hU'_sub hpV.1
            have hT_eq : T = T' := by
              by_contra h; exact Set.disjoint_left.mp (P.pairwiseDisjoint hT hT'_mem h)
                ((Set.mem_prod.mp hp).2.1) hp2_T'
            exact ⟨hT_eq ▸ hU'_sub hy.1, hy.2⟩
          · -- V = U' \ T₀; but p.2 ∈ V and p.2 ∈ T₀ (from hp), contradiction
            exfalso
            exact hpV.2 (Set.mem_prod.mp hp).2.2
        simp only [qUnion, Set.mem_iUnion, Finset.mem_coe, Finset.mem_product]
        exact ⟨⟨U, V⟩, ⟨Finset.mem_filter.mpr ⟨hU_mem, hU_sub⟩,
          Finset.mem_filter.mpr ⟨hV_mem, hV_sub⟩⟩, Set.mem_prod.mpr ⟨hpU, hpV⟩⟩
      have h_qae : (S ∩ S₀) ×ˢ (T ∩ T₀) =ᵐ[μ.prod μ] qUnion := by
        rw [ae_eq_set]
        refine ⟨?_, by rw [Set.diff_eq_empty.mpr h_qsub]; exact measure_empty⟩
        have h0 : (μ.prod μ).restrict ((S ∩ S₀) ×ˢ (T ∩ T₀)) qUnionᶜ = 0 := ae_iff.mp h_qcover
        rwa [Measure.restrict_apply h_qmeas.compl, Set.inter_comm] at h0
      -- Integrability on each Q-cell
      have hI1 : ∀ st ∈ QA ×ˢ QB,
          IntegrableOn (fun p => (stepify Q W).toAEEqFun p) (st.1 ×ˢ st.2) (μ.prod μ) :=
        fun _ _ => (SymmKernel.graphon_integrable (stepify Q W)).integrableOn
      have hI2 : ∀ st ∈ QA ×ˢ QB,
          IntegrableOn (fun p => W.toAEEqFun p) (st.1 ×ˢ st.2) (μ.prod μ) :=
        fun _ _ => (SymmKernel.graphon_integrable W).integrableOn
      -- Conclude
      calc ∫ p in (S ∩ S₀) ×ˢ (T ∩ T₀), (stepify Q W).toAEEqFun p ∂(μ.prod μ)
          = ∫ p in qUnion, (stepify Q W).toAEEqFun p ∂(μ.prod μ) :=
            setIntegral_congr_set h_qae
        _ = ∑ st ∈ QA ×ˢ QB, ∫ p in st.1 ×ˢ st.2, (stepify Q W).toAEEqFun p ∂(μ.prod μ) :=
            integral_biUnion_finset _ h_meas h_disj hI1
        _ = ∑ st ∈ QA ×ˢ QB, ∫ p in st.1 ×ˢ st.2, W.toAEEqFun p ∂(μ.prod μ) := by
            apply Finset.sum_congr rfl; intro ⟨U, V⟩ hst
            simp only [Finset.mem_product] at hst
            exact setIntegral_stepify_eq_on_cell W Q U V (hQA_sub U hst.1) (hQB_sub V hst.2)
        _ = ∫ p in qUnion, W.toAEEqFun p ∂(μ.prod μ) :=
            (integral_biUnion_finset _ h_meas h_disj hI2).symm
        _ = ∫ p in (S ∩ S₀) ×ˢ (T ∩ T₀), W.toAEEqFun p ∂(μ.prod μ) :=
            (setIntegral_congr_set h_qae).symm
    -- Step 3: Sum up
    calc ∫ p in S₀ ×ˢ T₀, (stepify Q W).toAEEqFun p ∂(μ.prod μ)
        = ∫ p in cellU, (stepify Q W).toAEEqFun p ∂(μ.prod μ) :=
          setIntegral_congr_set h_ae_eq'
      _ = ∑ st ∈ P.parts ×ˢ P.parts,
            ∫ p in (st.1 ∩ S₀) ×ˢ (st.2 ∩ T₀), (stepify Q W).toAEEqFun p ∂(μ.prod μ) :=
          integral_biUnion_finset _ h_cells_meas' h_cells_disj' h_int_stepQ
      _ = ∑ st ∈ P.parts ×ˢ P.parts,
            ∫ p in (st.1 ∩ S₀) ×ˢ (st.2 ∩ T₀), W.toAEEqFun p ∂(μ.prod μ) := by
          apply Finset.sum_congr rfl; intro ⟨S, T⟩ hst
          simp only [Finset.mem_product] at hst
          exact h_cell_eq S hst.1 T hst.2
      _ = ∫ p in cellU, W.toAEEqFun p ∂(μ.prod μ) :=
          (integral_biUnion_finset _ h_cells_meas' h_cells_disj' h_int_W').symm
      _ = ∫ p in S₀ ×ˢ T₀, W.toAEEqFun p ∂(μ.prod μ) :=
          (setIntegral_congr_set h_ae_eq').symm
  -- Step 2: rid = ∫_{S₀×T₀}(stepify Q W - stepify P W)
  have h_rid_eq : rectIntegralDiff W (stepify P W) S₀ T₀ =
      ∫ p in S₀ ×ˢ T₀, ((stepify Q W).toAEEqFun p - (stepify P W).toAEEqFun p) ∂(μ.prod μ) := by
    unfold rectIntegralDiff
    rw [integral_sub (SymmKernel.graphon_integrable W).integrableOn
        (SymmKernel.graphon_integrable (stepify P W)).integrableOn,
      integral_sub (SymmKernel.graphon_integrable (stepify Q W)).integrableOn
        (SymmKernel.graphon_integrable (stepify P W)).integrableOn]
    linarith
  -- Step 3: (rid)² ≤ ∫(stepify Q W - stepify P W)² (Jensen + integral over subset)
  -- Step 3a: (rid)² ≤ μ(S₀×T₀) · ∫_{S₀×T₀}(f_Q-f_P)² (Jensen on product measure)
  -- Step 3b: μ(S₀×T₀) ≤ 1 (probability measure)
  -- Step 3c: ∫_{S₀×T₀}(f_Q-f_P)² ≤ ∫(f_Q-f_P)² (integral over subset ≤ whole space)
  -- For Jensen, use sq_setIntegral_le_measure_mul_setIntegral_sq on μ.prod μ.
  have h_fQfP_int : IntegrableOn
      (fun p => (stepify Q W).toAEEqFun p - (stepify P W).toAEEqFun p) (S₀ ×ˢ T₀) (μ.prod μ) :=
    ((SymmKernel.graphon_integrable (stepify Q W)).sub
      (SymmKernel.graphon_integrable (stepify P W))).integrableOn
  have h_fQfP_sq_int : IntegrableOn
      (fun p => ((stepify Q W).toAEEqFun p - (stepify P W).toAEEqFun p) ^ 2)
      (S₀ ×ˢ T₀) (μ.prod μ) := by
    apply Measure.integrableOn_of_bounded (measure_lt_top _ _).ne
    · exact ((continuous_pow 2).comp_aestronglyMeasurable
        ((SymmKernel.graphon_integrable (stepify Q W)).sub
          (SymmKernel.graphon_integrable (stepify P W))).aestronglyMeasurable)
    · filter_upwards [ae_restrict_of_ae (stepify Q W).ae_mem_Icc,
        ae_restrict_of_ae (stepify P W).ae_mem_Icc] with p hQ hP
      simp only [Real.norm_eq_abs]
      rw [show |((stepify Q W).toAEEqFun p - (stepify P W).toAEEqFun p) ^ 2| =
        ((stepify Q W).toAEEqFun p - (stepify P W).toAEEqFun p) ^ 2 from
        abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_one_iff_abs_le_one _).mpr
        (abs_sub_le_iff.mpr ⟨by linarith [hQ.2, hP.1], by linarith [hP.2, hQ.1]⟩)
  -- Jensen on product measure (which is also a probability measure)
  haveI : IsProbabilityMeasure (μ.prod μ) := Measure.prod.instIsProbabilityMeasure μ μ
  have h_jensen := sq_setIntegral_le_measure_mul_setIntegral_sq
    (μ := μ.prod μ)
    (fun p => (stepify Q W).toAEEqFun p - (stepify P W).toAEEqFun p)
    (S₀ ×ˢ T₀) h_fQfP_int h_fQfP_sq_int
  -- μ(S₀×T₀) ≤ 1
  have h_meas_le_one : ((μ.prod μ) (S₀ ×ˢ T₀)).toReal ≤ 1 := by
    rw [Measure.prod_prod, ENNReal.toReal_mul]
    calc (μ S₀).toReal * (μ T₀).toReal
        ≤ 1 * 1 := by
          apply mul_le_mul
          · exact ENNReal.toReal_le_of_le_ofReal one_pos.le (by rw [ENNReal.ofReal_one]; exact prob_le_one)
          · exact ENNReal.toReal_le_of_le_ofReal one_pos.le (by rw [ENNReal.ofReal_one]; exact prob_le_one)
          · exact ENNReal.toReal_nonneg
          · linarith
      _ = 1 := mul_one 1
  -- ∫_{S₀×T₀}(f_Q-f_P)² ≤ ∫(f_Q-f_P)²
  -- Integrability of (f_Q - f_P)^2 on the full space
  have h_fQfP_sq_integrable : Integrable
      (fun p => ((stepify Q W).toAEEqFun p - (stepify P W).toAEEqFun p) ^ 2) (μ.prod μ) := by
    rw [← integrableOn_univ]
    apply Measure.integrableOn_of_bounded (measure_lt_top _ _).ne
    · exact ((continuous_pow 2).comp_aestronglyMeasurable
        ((SymmKernel.graphon_integrable (stepify Q W)).sub
          (SymmKernel.graphon_integrable (stepify P W))).aestronglyMeasurable)
    · filter_upwards [ae_restrict_of_ae (stepify Q W).ae_mem_Icc,
        ae_restrict_of_ae (stepify P W).ae_mem_Icc] with p hQ hP
      simp only [Real.norm_eq_abs]
      rw [show |((stepify Q W).toAEEqFun p - (stepify P W).toAEEqFun p) ^ 2| =
        ((stepify Q W).toAEEqFun p - (stepify P W).toAEEqFun p) ^ 2 from
        abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_one_iff_abs_le_one _).mpr
        (abs_sub_le_iff.mpr ⟨by linarith [hQ.2, hP.1], by linarith [hP.2, hQ.1]⟩)
  have h_sub_integral : ∫ p in S₀ ×ˢ T₀,
      ((stepify Q W).toAEEqFun p - (stepify P W).toAEEqFun p) ^ 2 ∂(μ.prod μ) ≤
      ∫ p, ((stepify Q W).toAEEqFun p - (stepify P W).toAEEqFun p) ^ 2 ∂(μ.prod μ) := by
    apply setIntegral_le_integral h_fQfP_sq_integrable
    exact ae_of_all _ fun _ => sq_nonneg _
  -- Step 4: ∫(f_Q-f_P)² = defect P - defect Q (Pythagorean identity)
  have h_pythagorean : ∫ p,
      ((stepify Q W).toAEEqFun p - (stepify P W).toAEEqFun p) ^ 2 ∂(μ.prod μ) =
      defect W P - defect W Q := by
    -- Use integral_stepify_mul_eq_energy to compute each component.
    -- Key identities:
    --   ∫f_P² = energy P
    --   ∫f_Q² = energy Q
    --   ∫f_P·f_Q = energy P (since Q refines P, integrals are preserved on P-cells)
    -- Then ∫(f_Q-f_P)² = energy Q - 2·energy P + energy P = energy Q - energy P
    --                   = defect P - defect Q (by h_ediff)
    rw [← h_ediff]
    -- Abbreviations
    set fP := (stepify P W).toAEEqFun with hfP_def
    set fQ := (stepify Q W).toAEEqFun with hfQ_def
    have hfQ_int : Integrable fQ (μ.prod μ) := SymmKernel.graphon_integrable (stepify Q W)
    -- The three integral identities
    have h_fP_sq : ∫ p, fP p * fP p ∂(μ.prod μ) = energy W P :=
      integral_stepify_mul_eq_energy W P _ hfP_int
        (fun S hS T hT => setIntegral_stepify_eq_on_cell W P S T hS hT)
    have h_fQ_sq : ∫ p, fQ p * fQ p ∂(μ.prod μ) = energy W Q :=
      integral_stepify_mul_eq_energy W Q _ hfQ_int
        (fun U hU V hV => setIntegral_stepify_eq_on_cell W Q U V hU hV)
    have h_cross : ∫ p, fP p * fQ p ∂(μ.prod μ) = energy W P :=
      integral_stepify_mul_eq_energy W P _ hfQ_int
        (fun S hS T hT => setIntegral_stepify_eq_on_refines_cell W P Q hQP S T hS hT)
    -- Integrability facts
    have h_int_qq : Integrable (fun p => fQ p * fQ p) (μ.prod μ) := by
      apply hfQ_int.bdd_mul fQ.aestronglyMeasurable
      filter_upwards [(stepify Q W).ae_mem_Icc] with p hp
      rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨by linarith [hp.1], hp.2⟩
    have h_int_pp : Integrable (fun p => fP p * fP p) (μ.prod μ) := by
      apply hfP_int.bdd_mul fP.aestronglyMeasurable
      filter_upwards [(stepify P W).ae_mem_Icc] with p hp
      rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨by linarith [hp.1], hp.2⟩
    have h_int_pq : Integrable (fun p => fP p * fQ p) (μ.prod μ) := by
      apply hfQ_int.bdd_mul fP.aestronglyMeasurable
      filter_upwards [(stepify P W).ae_mem_Icc] with p hp
      rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨by linarith [hp.1], hp.2⟩
    -- Compute ∫(f_Q-f_P)² directly
    -- Expand ∫(f_Q-f_P)² = ∫f_Q² + ∫f_P² - 2∫(f_P·f_Q)
    have h_int_result : ∫ p, (fQ p - fP p) ^ 2 ∂(μ.prod μ) =
        ∫ p, fQ p * fQ p ∂(μ.prod μ) + ∫ p, fP p * fP p ∂(μ.prod μ) -
        2 * ∫ p, fP p * fQ p ∂(μ.prod μ) := by
      -- Rewrite (a-b)^2 as a*a + b*b - 2*(a*b)
      have h1 : ∫ p, (fQ p - fP p) ^ 2 ∂(μ.prod μ) =
          ∫ p, (fQ p * fQ p + fP p * fP p - 2 * (fP p * fQ p)) ∂(μ.prod μ) := by
        congr 1; ext p; ring
      rw [h1]
      -- Split ∫(a + b - c) = ∫(a + b) - ∫c
      have h_step1 : ∫ p, (fQ p * fQ p + fP p * fP p - 2 * (fP p * fQ p)) ∂(μ.prod μ) =
          ∫ p, (fQ p * fQ p + fP p * fP p) ∂(μ.prod μ) -
          ∫ p, 2 * (fP p * fQ p) ∂(μ.prod μ) := by
        have : (fun p => fQ p * fQ p + fP p * fP p - 2 * (fP p * fQ p)) =
            (fun p => fQ p * fQ p + fP p * fP p) - (fun p => 2 * (fP p * fQ p)) := by
          ext p; simp [Pi.sub_apply]
        rw [this]; exact integral_sub (h_int_qq.add h_int_pp) (h_int_pq.const_mul 2)
      -- Split ∫(a + b) = ∫a + ∫b
      have h_step2 : ∫ p, (fQ p * fQ p + fP p * fP p) ∂(μ.prod μ) =
          ∫ p, fQ p * fQ p ∂(μ.prod μ) + ∫ p, fP p * fP p ∂(μ.prod μ) := by
        have : (fun p => fQ p * fQ p + fP p * fP p) =
            (fun p => fQ p * fQ p) + (fun p => fP p * fP p) := by
          ext p; simp [Pi.add_apply]
        rw [this]; exact integral_add h_int_qq h_int_pp
      -- Pull out constant 2
      have h_step3 : ∫ p, 2 * (fP p * fQ p) ∂(μ.prod μ) =
          2 * ∫ p, fP p * fQ p ∂(μ.prod μ) := integral_const_mul _ _
      linarith
    rw [h_int_result, h_fQ_sq, h_fP_sq, h_cross]; ring
  -- Combine: (rid)² ≤ defect P - defect Q = energy Q - energy P
  have h_rid_le_diff : (rectIntegralDiff W (stepify P W) S₀ T₀) ^ 2 ≤ defect W P - defect W Q := by
    rw [h_rid_eq]
    calc (∫ p in S₀ ×ˢ T₀,
            ((stepify Q W).toAEEqFun p - (stepify P W).toAEEqFun p) ∂(μ.prod μ)) ^ 2
        ≤ ((μ.prod μ) (S₀ ×ˢ T₀)).toReal *
          ∫ p in S₀ ×ˢ T₀,
            ((stepify Q W).toAEEqFun p - (stepify P W).toAEEqFun p) ^ 2 ∂(μ.prod μ) := h_jensen
      _ ≤ 1 * ∫ p in S₀ ×ˢ T₀,
            ((stepify Q W).toAEEqFun p - (stepify P W).toAEEqFun p) ^ 2 ∂(μ.prod μ) := by
          apply mul_le_mul_of_nonneg_right h_meas_le_one
          exact setIntegral_nonneg_of_ae_restrict (ae_of_all _ fun _ => sq_nonneg _)
      _ = ∫ p in S₀ ×ˢ T₀,
            ((stepify Q W).toAEEqFun p - (stepify P W).toAEEqFun p) ^ 2 ∂(μ.prod μ) := one_mul _
      _ ≤ ∫ p, ((stepify Q W).toAEEqFun p - (stepify P W).toAEEqFun p) ^ 2 ∂(μ.prod μ) :=
          h_sub_integral
      _ = defect W P - defect W Q := h_pythagorean
  linarith [h_ediff]

/-- If `cutNormDiff U W > c`, there exist measurable S, T with
|rectIntegralDiff U W S T| > c. Follows from the definition of cutNormDiff
as a supremum. -/
private lemma exists_rectIntegralDiff_gt_of_cutNormDiff_gt
    (U W : Graphon α μ) (c : ℝ)
    (h : c < cutNormDiff U W) :
    ∃ (S : Set α), MeasurableSet S ∧ ∃ (T : Set α), MeasurableSet T ∧
      c < |rectIntegralDiff U W S T| := by
  by_contra h_neg
  push_neg at h_neg
  have hc : 0 ≤ c := le_trans (abs_nonneg _) (h_neg ∅ MeasurableSet.empty ∅ MeasurableSet.empty)
  have h_le : cutNormDiff U W ≤ c := by
    unfold cutNormDiff
    apply Real.iSup_le _ hc
    intro S
    apply Real.iSup_le _ hc
    intro hS
    apply Real.iSup_le _ hc
    intro T
    apply Real.iSup_le _ hc
    intro hT
    exact h_neg S hS T hT
  linarith

/-- Quantitative energy increment via cut norm (Frieze-Kannan).

If the step graphon approximation of W on partition P has cut norm difference > ε,
then splitting all parts by the witnessing rectangle (S₀ for rows, T₀ for columns)
yields a refinement Q with energy gain ≥ ε².

Uses double splitting: Q = splitAllParts(splitAllParts(P, S₀), T₀), giving
at most 4 × |P.parts| parts. The energy gain follows from:
- The conditional variance identity (energy gain = Σ μ·(a − a_parent)²)
- Cauchy-Schwarz: (∫_{S₀×T₀} (W − stepify))² ≤ energy gain -/
private theorem energy_increment_quantitative
    (W : Graphon α μ) (P : MeasurablePartition α μ) (ε : ℝ) (hε : ε > 0)
    (h_bad : ε < cutNormDiff W (stepify P W)) :
    ∃ Q : MeasurablePartition α μ,
      Refines Q P ∧ Q.parts.card ≤ 4 * P.parts.card ∧
      energy W Q ≥ energy W P + ε ^ 2 := by
  -- Step 1: Extract witnessing sets S₀, T₀ from cutNormDiff > ε
  obtain ⟨S₀, hS₀, T₀, hT₀, h_integral⟩ :=
    exists_rectIntegralDiff_gt_of_cutNormDiff_gt W (stepify P W) ε h_bad
  -- Step 2: Build Q by splitting all parts first by S₀, then by T₀
  set Q₁ := MeasurablePartition.splitAllParts P S₀ hS₀ with hQ₁_def
  set Q := MeasurablePartition.splitAllParts Q₁ T₀ hT₀ with hQ_def
  refine ⟨Q, ?_, ?_, ?_⟩
  -- (a) Q refines P
  · exact Refines.trans (MeasurablePartition.splitAllParts_refines P S₀ hS₀) (MeasurablePartition.splitAllParts_refines Q₁ T₀ hT₀)
  -- (b) Q has at most 4 * P.parts.card parts
  · calc Q.parts.card
        ≤ 2 * Q₁.parts.card := MeasurablePartition.splitAllParts_card Q₁ T₀ hT₀
      _ ≤ 2 * (2 * P.parts.card) := Nat.mul_le_mul_left 2 (MeasurablePartition.splitAllParts_card P S₀ hS₀)
      _ = 4 * P.parts.card := by ring
  -- (c) Energy gain ≥ ε²
  · have h_energy := energy_doubleSplit_ge_sq W P S₀ hS₀ T₀ hT₀
    have h_abs_gt : ε < |rectIntegralDiff W (stepify P W) S₀ T₀| := h_integral
    -- ε² ≤ |integral|² = integral²
    have h_sq : ε ^ 2 ≤ (rectIntegralDiff W (stepify P W) S₀ T₀) ^ 2 := by
      have h1 : ε ^ 2 < |rectIntegralDiff W (stepify P W) S₀ T₀| ^ 2 := by
        exact sq_lt_sq' (by linarith [abs_nonneg (rectIntegralDiff W (stepify P W) S₀ T₀)]) h_abs_gt
      have h2 : |rectIntegralDiff W (stepify P W) S₀ T₀| ^ 2 =
          (rectIntegralDiff W (stepify P W) S₀ T₀) ^ 2 := by
        rw [sq_abs]
      linarith
    linarith

/-- **Pair energy increment**: If `cutNormDiff U (stepify P U) > δ`, then there exists
a refinement Q of P with at most 4 times as many parts such that:
1. `energy U Q ≥ energy U P + δ²` (the graphon that triggered the refinement gains energy)
2. `energy V Q ≥ energy V P` for any other graphon V (energy is monotone under refinement)

This is the key lemma for simultaneous regularity: we can refine for one graphon
while ensuring the other's energy does not decrease. -/
theorem energy_increment_pair
    (U : Graphon α μ) (P : MeasurablePartition α μ) (δ : ℝ) (hδ : δ > 0)
    (h_bad : δ < cutNormDiff U (stepify P U)) :
    ∃ Q : MeasurablePartition α μ,
      Refines Q P ∧ Q.parts.card ≤ 4 * P.parts.card ∧
      energy U Q ≥ energy U P + δ ^ 2 ∧
      ∀ V : Graphon α μ, energy V Q ≥ energy V P := by
  obtain ⟨S₀, hS₀, T₀, hT₀, h_integral⟩ :=
    exists_rectIntegralDiff_gt_of_cutNormDiff_gt U (stepify P U) δ h_bad
  set Q₁ := MeasurablePartition.splitAllParts P S₀ hS₀ with hQ₁_def
  set Q := MeasurablePartition.splitAllParts Q₁ T₀ hT₀ with hQ_def
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · exact Refines.trans (MeasurablePartition.splitAllParts_refines P S₀ hS₀)
      (MeasurablePartition.splitAllParts_refines Q₁ T₀ hT₀)
  · calc Q.parts.card
        ≤ 2 * Q₁.parts.card := MeasurablePartition.splitAllParts_card Q₁ T₀ hT₀
      _ ≤ 2 * (2 * P.parts.card) :=
          Nat.mul_le_mul_left 2 (MeasurablePartition.splitAllParts_card P S₀ hS₀)
      _ = 4 * P.parts.card := by ring
  · have h_energy := energy_doubleSplit_ge_sq U P S₀ hS₀ T₀ hT₀
    have h_abs_gt : δ < |rectIntegralDiff U (stepify P U) S₀ T₀| := h_integral
    have h_sq : δ ^ 2 ≤ (rectIntegralDiff U (stepify P U) S₀ T₀) ^ 2 := by
      have h1 : δ ^ 2 < |rectIntegralDiff U (stepify P U) S₀ T₀| ^ 2 :=
        sq_lt_sq' (by linarith [abs_nonneg (rectIntegralDiff U (stepify P U) S₀ T₀)]) h_abs_gt
      linarith [sq_abs (rectIntegralDiff U (stepify P U) S₀ T₀)]
    linarith
  · intro V
    have h_V := energy_doubleSplit_ge_sq V P S₀ hS₀ T₀ hT₀
    linarith [sq_nonneg (rectIntegralDiff V (stepify P V) S₀ T₀)]

/-- The regularity function: given ε, returns an upper bound on the number of parts
    needed in a partition to achieve ε-approximation.

The bound is exponential in 1/ε², following the Frieze-Kannan approach which gives
single-exponential bounds (better than the tower-type bounds from Szemerédi's proof).

Uses base 4 because each FK step doubles in both row and column dimensions. -/
noncomputable def regularityBound (ε : ℝ) : ℕ :=
  if ε ≤ 0 then 0 else 4 ^ (Nat.ceil (1 / ε ^ 2) + 1)

/-- The Frieze-Kannan weak regularity lemma.

For any ε > 0 and any graphon W, there exists a measurable partition P with
bounded number of parts such that the step graphon approximation of W on P
has small cut norm difference from W.

**Proof** (Frieze-Kannan [1999]):
1. Start with trivial partition P₀ = {α}
2. While `cutNormDiff W (stepify P W) > ε`:
   - Apply energy_increment_quantitative to get P_{i+1}
   - Energy increases by ≥ ε²
3. Since energy ≤ 1, at most ⌈1/ε²⌉ iterations
4. Each iteration at most quadruples parts (double split): final count ≤ 4^(iterations+1) -/
@[blueprint "thm:regularity"
  (title := /-- Frieze–Kannan weak regularity lemma -/)]
theorem regularity (W : Graphon α μ) (ε : ℝ) (hε : ε > 0) :
    ∃ P : MeasurablePartition α μ,
      P.parts.card ≤ regularityBound ε ∧
      cutNormDiff W (stepify P W) ≤ ε := by
  -- N = max number of iterations before energy exceeds 1
  set N : ℕ := Nat.ceil (1 / ε ^ 2) + 1 with hN_def

  -- Energy gain per step
  have h_delta_pos : ε ^ 2 > 0 := by positivity
  set δ := ε ^ 2 with hδ_def

  -- Main iteration claim: if we can take n more steps from P,
  -- and P has ≤ 4^(N-n) parts, then either we find a good partition
  -- with ≤ 4^N parts, or energy W P + n*δ ≤ 1 is violated.
  suffices h_iter : ∀ n : ℕ, n ≤ N → ∀ P : MeasurablePartition α μ,
      P.parts.card ≤ 4 ^ (N - n) →
      ∃ Q : MeasurablePartition α μ,
        Q.parts.card ≤ 4 ^ N ∧
        (cutNormDiff W (stepify Q W) ≤ ε ∨ energy W Q ≥ energy W P + n * δ) by
    -- Start with trivial partition
    let P₀ := trivialPartition (α := α) (μ := μ)
    have hP₀_card : P₀.parts.card ≤ 4 ^ (N - N) := by
      rw [Nat.sub_self, pow_zero, trivialPartition_card]
    obtain ⟨Q, hQ_card, hQ_result⟩ := h_iter N le_rfl P₀ hP₀_card
    rcases hQ_result with hQ_good | hQ_energy
    · -- Found good partition
      refine ⟨Q, ?_, hQ_good⟩
      have h_bound : regularityBound ε = 4 ^ N := by
        unfold regularityBound
        rw [if_neg (by linarith), hN_def]
      omega
    · -- Energy too high — contradiction
      exfalso
      have h_energy_le : energy W Q ≤ 1 := energy_le_one W Q
      have h_energy_P₀ : energy W P₀ ≥ 0 := energy_nonneg W P₀
      have h_N_bound : (N : ℝ) * δ > 1 := by
        rw [hδ_def, hN_def]
        have h_ceil : (↑(Nat.ceil (1 / ε ^ 2)) : ℝ) ≥ 1 / ε ^ 2 :=
          Nat.le_ceil _
        calc (↑(Nat.ceil (1 / ε ^ 2) + 1) : ℝ) * ε ^ 2
            = (↑(Nat.ceil (1 / ε ^ 2)) + 1) * ε ^ 2 := by push_cast; ring
          _ > (1 / ε ^ 2) * ε ^ 2 := by nlinarith
          _ = 1 := by field_simp
      linarith

  -- Prove the iteration by induction on n (remaining fuel)
  intro n
  induction n with
  | zero =>
    intro _hn P hP_card
    -- No fuel left: return P as is (with vacuous energy bound)
    exact ⟨P, by
      calc P.parts.card ≤ 4 ^ (N - 0) := hP_card
        _ = 4 ^ N := by simp
      , Or.inr (by simp)⟩
  | succ n ih =>
    intro hn P hP_card
    -- Check if cut norm is already small
    by_cases h_done : cutNormDiff W (stepify P W) ≤ ε
    · exact ⟨P, by
        calc P.parts.card ≤ 4 ^ (N - (n + 1)) := hP_card
          _ ≤ 4 ^ N := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le N _)
        , Or.inl h_done⟩
    · -- Cut norm > ε: apply energy_increment_quantitative
      push_neg at h_done
      obtain ⟨Q, _hQ_ref, hQ_card_le, hQ_energy⟩ :=
        energy_increment_quantitative W P ε hε h_done
      -- Q.parts.card ≤ 4 * P.parts.card ≤ 4 * 4^(N-(n+1)) = 4^(N-n)
      have hQ_card : Q.parts.card ≤ 4 ^ (N - n) := by
        have h1 : N - n = (N - (n + 1)) + 1 := by omega
        calc Q.parts.card
            ≤ 4 * P.parts.card := hQ_card_le
          _ ≤ 4 * 4 ^ (N - (n + 1)) := Nat.mul_le_mul_left 4 hP_card
          _ = 4 ^ ((N - (n + 1)) + 1) := by ring_nf
          _ = 4 ^ (N - n) := by rw [← h1]
      -- Apply IH with n remaining fuel
      obtain ⟨R, hR_card, hR_result⟩ := ih (by omega) Q hQ_card
      refine ⟨R, hR_card, ?_⟩
      rcases hR_result with hR_good | hR_energy
      · exact Or.inl hR_good
      · right
        have : (↑(n + 1) : ℝ) = ↑n + 1 := by push_cast; ring
        calc energy W R ≥ energy W Q + ↑n * δ := hR_energy
          _ ≥ (energy W P + δ) + ↑n * δ := by linarith
          _ = energy W P + (↑n + 1) * δ := by ring
          _ = energy W P + ↑(n + 1) * δ := by rw [this]

end Regularity

/-! ### Equitable partitions -/

section Equitable

variable [IsProbabilityMeasure μ]

/-- A partition is ε-equitable if all parts have measure within ε of 1/k,
    where k is the number of parts. -/
def IsEquitable (P : MeasurablePartition α μ) (ε : ℝ) : Prop :=
  ∀ S ∈ P.parts, |(μ S).toReal - 1 / P.parts.card| ≤ ε

omit [IsProbabilityMeasure μ] in
/-- Helper for Sierpinski's theorem: greedy binary thinning of a set.
At each step, either include or exclude the n-th separating set,
choosing whichever keeps the accumulated measure ≤ r. -/
private noncomputable def ivtStep (μ : Measure α) (S : Set α) (C : ℕ → Set α) (r : ℝ≥0∞) :
    ℕ → ℝ≥0∞ × Set α
  | 0 => (0, S)
  | n + 1 =>
    let prev := ivtStep μ S C r n
    if prev.1 + μ (prev.2 ∩ C n) ≤ r then
      (prev.1 + μ (prev.2 ∩ C n), prev.2 \ C n)
    else
      (prev.1, prev.2 ∩ C n)

set_option maxHeartbeats 800000

/-- IVT for atomless measures: any measurable set can be split at any prescribed measure.
This is a standard result (Sierpinski's theorem). Given `[StandardBorelSpace α]`,
we use a countable separating sequence to greedily construct the desired subset. -/
theorem exists_measurable_subset_of_measure [StandardBorelSpace α] [NoAtoms μ]
    {S : Set α} (hS : MeasurableSet S) {r : ℝ≥0∞} (hr : r ≤ μ S) :
    ∃ T : Set α, MeasurableSet T ∧ T ⊆ S ∧ μ T = r := by
  -- Obtain a countable separating sequence of measurable sets
  obtain ⟨C, hC_meas, hC_sep⟩ := exists_seq_separating α (p := MeasurableSet)
    (s₀ := univ) MeasurableSet.univ (t := univ)
  -- Use the greedy iterator
  set step := ivtStep μ S C r with step_def
  -- Extract the accumulator and remainder
  let acc (n : ℕ) : ℝ≥0∞ := (step n).1
  let R (n : ℕ) : Set α := (step n).2
  -- Basic step equations
  have step_zero : step 0 = (0, S) := by simp [step_def, ivtStep]
  have step_succ : ∀ n, step (n + 1) =
    if (step n).1 + μ ((step n).2 ∩ C n) ≤ r then
      ((step n).1 + μ ((step n).2 ∩ C n), (step n).2 \ C n)
    else
      ((step n).1, (step n).2 ∩ C n) := fun n => by simp [step_def, ivtStep]
  -- Invariants: R n is measurable, R n ⊆ S, acc n ≤ r, r - acc n ≤ μ (R n)
  have inv : ∀ n, MeasurableSet (R n) ∧ R n ⊆ S ∧ acc n ≤ r ∧ r - acc n ≤ μ (R n) := by
    intro n
    induction n with
    | zero =>
      have h0 : step 0 = (0, S) := step_zero
      refine ⟨?_, ?_, ?_, ?_⟩
      · show MeasurableSet (step 0).2; rw [h0]; exact hS
      · show (step 0).2 ⊆ S; rw [h0]
      · show (step 0).1 ≤ r; rw [h0]; exact zero_le r
      · show r - (step 0).1 ≤ μ (step 0).2; rw [h0]; simpa using hr
    | succ n ih =>
      obtain ⟨hR_meas, hR_sub, hacc_le, hgap⟩ := ih
      -- Determine which branch step (n+1) takes
      by_cases hcond : (step n).1 + μ ((step n).2 ∩ C n) ≤ r
      · -- Case: include C n in the selection
        have hR_eq : R (n + 1) = R n \ C n := by
          show (step (n + 1)).2 = (step n).2 \ C n
          rw [step_succ]; simp [hcond]
        have hacc_eq : acc (n + 1) = acc n + μ (R n ∩ C n) := by
          show (step (n + 1)).1 = (step n).1 + μ ((step n).2 ∩ C n)
          rw [step_succ]; simp [hcond]
        rw [show R (n + 1) = R n \ C n from hR_eq,
            show acc (n + 1) = acc n + μ (R n ∩ C n) from hacc_eq]
        refine ⟨hR_meas.diff (hC_meas n), diff_subset.trans hR_sub, hcond, ?_⟩
        have h_split := measure_inter_add_diff (μ := μ) (R n) (hC_meas n)
        rw [tsub_le_iff_right, add_comm (μ _)]
        calc r ≤ μ (R n) + acc n := tsub_le_iff_right.mp hgap
          _ = (μ (R n ∩ C n) + μ (R n \ C n)) + acc n := by rw [h_split]
          _ = (acc n + μ (R n ∩ C n)) + μ (R n \ C n) := by ring
      · -- Case: exclude C n from the selection
        have hR_eq : R (n + 1) = R n ∩ C n := by
          show (step (n + 1)).2 = (step n).2 ∩ C n
          rw [step_succ]; simp [hcond]
        have hacc_eq : acc (n + 1) = acc n := by
          show (step (n + 1)).1 = (step n).1
          rw [step_succ]; simp [hcond]
        rw [show R (n + 1) = R n ∩ C n from hR_eq,
            show acc (n + 1) = acc n from hacc_eq]
        push_neg at hcond
        refine ⟨hR_meas.inter (hC_meas n), inter_subset_left.trans hR_sub, hacc_le, ?_⟩
        exact tsub_le_iff_right.mpr (le_of_lt (by rwa [add_comm] at hcond))
  -- R is antitone: at each step, we take either a diff or intersection (both subsets)
  have hR_step_le : ∀ n, R (n + 1) ⊆ R n := by
    intro n
    show (step (n + 1)).2 ⊆ (step n).2
    rw [step_succ]
    split
    · exact diff_subset
    · exact inter_subset_left
  have hR_anti : Antitone R := antitone_nat_of_succ_le hR_step_le
  -- Points in ⋂ R agree on all C n, hence are equal by separation
  have hR_inter_sub : Set.Subsingleton (⋂ n, R n) := by
    intro x hx y hy
    apply hC_sep x (mem_univ _) y (mem_univ _)
    intro n
    have hx_succ : x ∈ (step (n + 1)).2 := mem_iInter.mp hx (n + 1)
    have hy_succ : y ∈ (step (n + 1)).2 := mem_iInter.mp hy (n + 1)
    rw [step_succ] at hx_succ hy_succ
    split at hx_succ
    · -- Case: R (n+1) = R n \ C n, so x ∉ C n
      split at hy_succ
      · exact iff_of_false hx_succ.2 hy_succ.2
      · -- Contradiction: the if condition can't both hold and not hold
        contradiction
    · -- Case: R (n+1) = R n ∩ C n, so x ∈ C n
      split at hy_succ
      · contradiction
      · exact iff_of_true hx_succ.2 hy_succ.2
  -- μ(⋂ R) = 0 by NoAtoms + subsingleton
  have hR_inter_zero : μ (⋂ n, R n) = 0 := hR_inter_sub.measure_zero μ
  -- μ(R n) → 0
  have hR_tendsto : Filter.Tendsto (μ ∘ R) Filter.atTop (nhds 0) := by
    rw [← hR_inter_zero]
    exact tendsto_measure_iInter_atTop
      (fun n => (inv n).1.nullMeasurableSet) hR_anti
      ⟨0, by show μ (step 0).2 ≠ ⊤; rw [step_zero]; exact measure_ne_top μ S⟩
  -- ⨆ acc n = r
  have hacc_sup : ⨆ n, acc n = r := by
    apply le_antisymm
    · exact iSup_le fun n => (inv n).2.2.1
    · apply ENNReal.le_of_forall_pos_le_add
      intro ε hε _
      rw [ENNReal.tendsto_atTop_zero] at hR_tendsto
      obtain ⟨N, hN⟩ := hR_tendsto ε (ENNReal.coe_pos.mpr hε)
      have hN' := hN N (le_refl _)
      have hacc_le_r := (inv N).2.2.1
      have hgap := (inv N).2.2.2
      calc r = (r - acc N) + acc N := (tsub_add_cancel_of_le hacc_le_r).symm
        _ ≤ μ (R N) + acc N := by gcongr
        _ ≤ ↑ε + acc N := by gcongr; exact hN'
        _ ≤ ↑ε + ⨆ n, acc n := by gcongr; exact le_iSup acc N
        _ = (⨆ n, acc n) + ↑ε := add_comm _ _
  -- Define the selected pieces
  let sel (n : ℕ) : Set α :=
    if (step n).1 + μ ((step n).2 ∩ C n) ≤ r then (step n).2 ∩ C n else ∅
  -- sel pieces are measurable
  have hsel_meas : ∀ n, MeasurableSet (sel n) := by
    intro n; simp only [sel]; split
    · exact (inv n).1.inter (hC_meas n)
    · exact MeasurableSet.empty
  -- sel n ⊆ R n
  have hsel_sub_R : ∀ n, sel n ⊆ R n := by
    intro n; simp only [sel]; split
    · exact inter_subset_left
    · exact empty_subset _
  -- sel n ⊆ S
  have hsel_sub_S : ∀ n, sel n ⊆ S := fun n => (hsel_sub_R n).trans (inv n).2.1
  -- Disjointness: sel n ⊆ R n, and R (n+1) is disjoint from sel n
  have hsel_disj_R : ∀ n, Disjoint (sel n) (R (n + 1)) := by
    intro n
    simp only [sel]
    split
    · case isTrue h =>
      -- sel n = R n ∩ C n, and in this case R (n+1) = R n \ C n
      have hR_next : (step (n + 1)).2 = (step n).2 \ C n := by
        rw [step_succ]; simp [h]
      show Disjoint ((step n).2 ∩ C n) (step (n + 1)).2
      rw [hR_next]
      exact disjoint_of_subset_left inter_subset_right disjoint_sdiff_right
    · -- sel n = ∅
      exact empty_disjoint _
  -- sel pieces are pairwise disjoint
  have hsel_pairwise : Pairwise fun i j => Disjoint (sel i) (sel j) := by
    intro m n hmn
    rcases Nat.lt_or_gt_of_ne hmn with h | h
    · exact Disjoint.mono_right (hsel_sub_R n)
        (Disjoint.mono_right (hR_anti (Nat.succ_le_of_lt h)) (hsel_disj_R m))
    · exact (Disjoint.mono_right (hsel_sub_R m)
        (Disjoint.mono_right (hR_anti (Nat.succ_le_of_lt h)) (hsel_disj_R n))).symm
  -- Accumulator equation: acc (n+1) = acc n + μ(sel n)
  have hacc_step : ∀ n, acc (n + 1) = acc n + μ (sel n) := by
    intro n
    show (step (n + 1)).1 = (step n).1 + μ (sel n)
    rw [step_succ]
    simp only [sel]
    split
    · rfl
    · simp [measure_empty]
  -- Set T = ⋃ n, sel n
  refine ⟨⋃ n, sel n, MeasurableSet.iUnion hsel_meas,
    iUnion_subset hsel_sub_S, ?_⟩
  -- μ(T) = ∑ μ(sel n) = ⨆ acc n = r
  rw [measure_iUnion (fun i j hij => hsel_pairwise hij) hsel_meas]
  have : ∑' n, μ (sel n) = ⨆ n, acc n := by
    have hpartial : ∀ n, ∑ i ∈ Finset.range n, μ (sel i) = acc n := by
      intro n
      induction n with
      | zero =>
        simp only [Finset.range_zero, Finset.sum_empty]
        show (0 : ℝ≥0∞) = (step 0).1
        rw [step_zero]
      | succ n ih =>
        rw [Finset.sum_range_succ, ih, hacc_step]
    rw [ENNReal.tsum_eq_iSup_nat]
    congr 1; ext n; exact hpartial n
  rw [this, hacc_sup]

/-- Split a measurable set into exactly n pairwise disjoint measurable pieces of equal measure.

Given a measurable set S in an atomless measure space and n ≥ 1, there exist
n pairwise disjoint measurable subsets of S, each of measure μ(S)/n, that cover S.
This follows from iterated application of the IVT for atomless measures. -/
private theorem exists_equal_measure_partition [StandardBorelSpace α] [NoAtoms μ]
    {S : Set α} (hS : MeasurableSet S) (hfin : μ S ≠ ⊤) (hne : μ S ≠ 0)
    {n : ℕ} (hn : 0 < n) :
    ∃ pieces : Finset (Set α),
      pieces.card = n ∧
      (∀ T ∈ pieces, MeasurableSet T) ∧
      (∀ T ∈ pieces, T ⊆ S) ∧
      (pieces : Set (Set α)).PairwiseDisjoint id ∧
      (∀ T ∈ pieces, μ T = μ S / n) ∧
      (∀ᵐ x ∂μ, x ∈ S → ∃ T ∈ pieces, x ∈ T) := by
  -- Set q = μ S / n, the target measure for each piece
  set q := μ S / (n : ℝ≥0∞) with hq_def
  have hn_ne : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  have hn_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hq_ne_top : q ≠ ⊤ := ENNReal.div_ne_top hfin hn_ne
  have hq_pos : 0 < q := ENNReal.div_pos hne hn_top
  -- Helper: carve m equal-measure pieces from a remainder R with μ R = m * q
  suffices h_helper : ∀ (m : ℕ) (R : Set α),
      MeasurableSet R → R ⊆ S → μ R = ↑m * q →
      ∃ pieces : Finset (Set α),
        pieces.card = m ∧
        (∀ T ∈ pieces, MeasurableSet T) ∧
        (∀ T ∈ pieces, T ⊆ R) ∧
        (pieces : Set (Set α)).PairwiseDisjoint id ∧
        (∀ T ∈ pieces, μ T = q) ∧
        (∀ᵐ x ∂μ, x ∈ R → ∃ T ∈ pieces, x ∈ T) by
    -- Invoke helper with m = n, R = S
    have hmuS : μ S = ↑n * q := (ENNReal.mul_div_cancel hn_ne hn_top).symm
    obtain ⟨pieces, hcard, hmeas, hsub, hdisj, hmu, hcov⟩ := h_helper n S hS Subset.rfl hmuS
    exact ⟨pieces, hcard, hmeas, hsub, hdisj, hmu, hcov⟩
  intro m
  induction m with
  | zero =>
    intro R hR_meas _hR_sub hR_mu
    refine ⟨∅, Finset.card_empty, by simp, by simp, by simp, by simp, ?_⟩
    -- μ R = 0 * q = 0, so R is null → AE coverage is trivial
    simp only [Nat.cast_zero, zero_mul] at hR_mu
    rw [ae_iff]
    apply measure_mono_null (fun x (hx : ¬ _) => ?_) (by rw [hR_mu])
    exact (_root_.not_imp.mp hx).1
  | succ m ih =>
    intro R hR_meas hR_sub hR_mu
    -- Show q ≤ μ R (since μ R = (m+1) * q ≥ q)
    have hq_le : q ≤ μ R := by
      rw [hR_mu]
      exact le_mul_of_one_le_left (zero_le q)
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero m))
    -- Apply IVT oracle to get a piece T ⊆ R with μ T = q
    obtain ⟨T, hT_meas, hT_sub, hT_mu⟩ := exists_measurable_subset_of_measure hR_meas hq_le
    -- Set R' = R \ T
    set R' := R \ T with hR'_def
    have hR'_meas : MeasurableSet R' := hR_meas.diff hT_meas
    have hR'_sub : R' ⊆ S := diff_subset.trans hR_sub
    -- Compute μ R' = m * q
    have hT_mu_ne_top : μ T ≠ ⊤ := by rw [hT_mu]; exact hq_ne_top
    have hR'_mu : μ R' = ↑m * q := by
      have h_diff := measure_diff hT_sub hT_meas.nullMeasurableSet hT_mu_ne_top
      rw [h_diff, hR_mu, hT_mu]
      rw [show (↑(m + 1) : ℝ≥0∞) = ↑m + 1 from by push_cast; ring]
      rw [add_mul, one_mul]
      exact ENNReal.add_sub_cancel_right hq_ne_top
    -- Apply IH to R' to get m pieces
    obtain ⟨pieces_old, hcard_old, hmeas_old, hsub_old, hdisj_old, hmu_old, hcov_old⟩ :=
      ih R' hR'_meas hR'_sub hR'_mu
    -- Show T ∉ pieces_old
    have hT_notin : T ∉ pieces_old := by
      intro hT_in
      have hT_sub_R' : T ⊆ R' := hsub_old T hT_in
      have hT_ne : μ T ≠ 0 := by rw [hT_mu]; exact ne_of_gt hq_pos
      have hT_nonempty : T.Nonempty := nonempty_of_measure_ne_zero hT_ne
      obtain ⟨x, hx⟩ := hT_nonempty
      exact (hT_sub_R' hx).2 hx
    -- Build pieces = {T} ∪ pieces_old via Finset.cons
    refine ⟨Finset.cons T pieces_old hT_notin, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- card
      rw [Finset.card_cons, hcard_old]
    · -- measurable
      intro U hU
      rw [Finset.mem_cons] at hU
      rcases hU with rfl | hU
      · exact hT_meas
      · exact hmeas_old U hU
    · -- subset of R
      intro U hU
      rw [Finset.mem_cons] at hU
      rcases hU with rfl | hU
      · exact hT_sub
      · exact (hsub_old U hU).trans diff_subset
    · -- pairwise disjoint
      intro U₁ hU₁ U₂ hU₂ hne₁₂
      rw [Finset.mem_coe, Finset.mem_cons] at hU₁ hU₂
      rcases hU₁ with rfl | hU₁ <;> rcases hU₂ with rfl | hU₂
      · exact absurd rfl hne₁₂
      · -- T vs U₂ ∈ pieces_old: U₂ ⊆ R' = R \ T, so Disjoint T U₂
        exact disjoint_sdiff_self_right.mono_right (hsub_old U₂ hU₂)
      · -- U₁ ∈ pieces_old vs T: symmetric
        exact (disjoint_sdiff_self_right.mono_right (hsub_old U₁ hU₁)).symm
      · -- Both in pieces_old: from IH
        exact hdisj_old (Finset.mem_coe.mpr hU₁) (Finset.mem_coe.mpr hU₂) hne₁₂
    · -- measure
      intro U hU
      rw [Finset.mem_cons] at hU
      rcases hU with rfl | hU
      · exact hT_mu
      · exact hmu_old U hU
    · -- AE coverage: x ∈ R → x ∈ T or x ∈ some piece from old
      have hcov_old' := hcov_old
      rw [ae_iff] at hcov_old' ⊢
      apply measure_mono_null (fun x (hx : ¬ _) => ?_) hcov_old'
      -- hx : ¬(x ∈ R → ∃ T ∈ cons ..., x ∈ T)
      -- goal : ¬(x ∈ R' → ∃ T ∈ pieces_old, x ∈ T)
      have ⟨hxR, hx_none⟩ := _root_.not_imp.mp hx
      apply _root_.not_imp.mpr
      exact ⟨⟨hxR, fun hxT => hx_none ⟨T, Finset.mem_cons_self T pieces_old, hxT⟩⟩,
        fun ⟨U, hU, hxU⟩ => hx_none ⟨U, Finset.mem_cons_of_mem hU, hxU⟩⟩

/-- Construct an equitable refinement of a partition.

Given a partition P and ε > 0, in an atomless measure space we can refine P
to an equitable partition Q by splitting each part into ⌈1/ε⌉₊ equal-measure
sub-pieces. The resulting partition Q satisfies:
- Refines P (each sub-piece is contained in its parent part)
- IsEquitable Q ε (each sub-piece has measure within ε of the average 1/Q.card)
- Q.parts.card ≤ P.parts.card * ⌈1/ε⌉₊

The construction requires assembling sub-pieces from all parts into a single
MeasurablePartition, verifying pairwise disjointness across different parent
parts (inherited from P's pairwise disjointness), and the equitability bound
(each sub-piece has measure μ(S)/m where m = ⌈1/ε⌉₊, and the deviation from
1/(n*m) is controlled by ε since |μ(S)/m - 1/(n*m)| = |μ(S) - 1/n|/m ≤ ε
when the original parts already have measure ≤ 1). -/
private theorem exists_equitable_refinement_construction [StandardBorelSpace α] [NoAtoms μ]
    (P : MeasurablePartition α μ) (ε : ℝ) (hε : ε > 0) :
    ∃ Q : MeasurablePartition α μ,
      Refines Q P ∧
      IsEquitable Q ε ∧
      Q.parts.card ≤ P.parts.card * ⌈1 / ε⌉₊ := by
  -- Let m = ⌈1/ε⌉₊, so m ≥ 1
  set m := ⌈1 / ε⌉₊ with hm_def
  have hm_pos : 0 < m := by
    rw [hm_def]; exact Nat.ceil_pos.mpr (div_pos one_pos hε)
  -- Key bound: 1/m ≤ ε
  have hm_inv_le : (1 : ℝ) / m ≤ ε := by
    rw [div_le_iff₀ (Nat.cast_pos.mpr hm_pos)]
    calc (1 : ℝ) = (1 / ε) * ε := by field_simp
      _ ≤ ↑m * ε := by
        apply mul_le_mul_of_nonneg_right _ hε.le
        exact Nat.le_ceil (1 / ε)
      _ = ε * ↑m := by ring
  classical
  -- For each S ∈ P.parts with μ S ≠ 0, split into m equal-measure pieces
  have h_split_pos : ∀ S ∈ P.parts, μ S ≠ 0 → ∃ pieces : Finset (Set α),
      pieces.card = m ∧
      (∀ T ∈ pieces, MeasurableSet T) ∧
      (∀ T ∈ pieces, T ⊆ S) ∧
      (pieces : Set (Set α)).PairwiseDisjoint id ∧
      (∀ T ∈ pieces, μ T = μ S / m) ∧
      (∀ᵐ x ∂μ, x ∈ S → ∃ T ∈ pieces, x ∈ T) := by
    intro S hS hμS
    exact exists_equal_measure_partition (P.measurableSet_part hS)
      (measure_ne_top μ S) hμS hm_pos
  choose gp hgp_card hgp_meas hgp_sub hgp_disj hgp_measure hgp_covers
    using h_split_pos
  -- Define g: for μ S = 0 use {S}, for μ S ≠ 0 use m-piece partition
  let g : (S : Set α) → S ∈ P.parts → Finset (Set α) :=
    fun S hS => if hμS : μ S = 0 then {S} else gp S hS hμS
  -- Properties of g (split by μ S = 0 or not)
  have hg_meas : ∀ S (hS : S ∈ P.parts), ∀ T ∈ g S hS, MeasurableSet T := by
    intro S hS T hT
    by_cases hμS : μ S = 0
    · simp only [g, dif_pos hμS, Finset.mem_singleton] at hT; subst hT
      exact P.measurableSet_part hS
    · exact hgp_meas S hS hμS T (by simp only [g, dif_neg hμS] at hT; exact hT)
  have hg_sub : ∀ S (hS : S ∈ P.parts), ∀ T ∈ g S hS, T ⊆ S := by
    intro S hS T hT
    by_cases hμS : μ S = 0
    · simp only [g, dif_pos hμS, Finset.mem_singleton] at hT; subst hT; exact Set.Subset.rfl
    · exact hgp_sub S hS hμS T (by simp only [g, dif_neg hμS] at hT; exact hT)
  have hg_disj : ∀ S (hS : S ∈ P.parts),
      ((g S hS : Set (Set α)).PairwiseDisjoint id) := by
    intro S hS
    by_cases hμS : μ S = 0
    · simp only [g, dif_pos hμS]; intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_singleton] at ha hb
      exact absurd (ha.trans hb.symm) hab
    · simp only [g, dif_neg hμS]; exact hgp_disj S hS hμS
  have hg_measure : ∀ S (hS : S ∈ P.parts), ∀ T ∈ g S hS, μ T = μ S / m := by
    intro S hS T hT
    by_cases hμS : μ S = 0
    · simp only [g, dif_pos hμS, Finset.mem_singleton] at hT; subst hT
      rw [hμS]; simp only [ENNReal.zero_div]
    · exact hgp_measure S hS hμS T (by simp only [g, dif_neg hμS] at hT; exact hT)
  have hg_covers : ∀ S (hS : S ∈ P.parts),
      ∀ᵐ x ∂μ, x ∈ S → ∃ T ∈ g S hS, x ∈ T := by
    intro S hS
    by_cases hμS : μ S = 0
    · simp only [g, dif_pos hμS]
      filter_upwards with x hxS
      exact ⟨S, Finset.mem_singleton_self S, hxS⟩
    · simp only [g, dif_neg hμS]; exact hgp_covers S hS hμS
  have hg_card_le : ∀ S (hS : S ∈ P.parts), (g S hS).card ≤ m := by
    intro S hS
    by_cases hμS : μ S = 0
    · simp only [g, dif_pos hμS, Finset.card_singleton]; omega
    · simp only [g, dif_neg hμS]; exact le_of_eq (hgp_card S hS hμS)
  -- Create a non-dependent wrapper for biUnion
  let f : Set α → Finset (Set α) := fun S => if h : S ∈ P.parts then g S h else ∅
  have hf_eq : ∀ S (hS : S ∈ P.parts), f S = g S hS := fun S hS => dif_pos hS
  -- Build Q as the biUnion of all piece-finsets
  refine ⟨{
    parts := P.parts.biUnion f
    measurable_parts := ?_
    pairwiseDisjoint := ?_
    ae_covers := ?_
  }, ?_, ?_, ?_⟩
  -- measurable_parts
  · intro T hT
    rw [Finset.mem_biUnion] at hT
    obtain ⟨S, hS, hTf⟩ := hT
    rw [hf_eq S hS] at hTf
    exact hg_meas S hS T hTf
  -- pairwiseDisjoint
  · intro T₁ hT₁ T₂ hT₂ hne
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe] at hT₁ hT₂
    obtain ⟨S₁, hS₁, hT₁f⟩ := hT₁
    obtain ⟨S₂, hS₂, hT₂f⟩ := hT₂
    rw [hf_eq S₁ hS₁] at hT₁f
    rw [hf_eq S₂ hS₂] at hT₂f
    by_cases hS : S₁ = S₂
    · subst hS
      exact hg_disj S₁ hS₁ hT₁f hT₂f hne
    · exact (P.pairwiseDisjoint hS₁ hS₂ hS).mono
        (hg_sub S₁ hS₁ T₁ hT₁f) (hg_sub S₂ hS₂ T₂ hT₂f)
  -- ae_covers
  · have h_ae_list : ∀ S ∈ P.parts,
        ∀ᵐ x ∂μ, x ∈ S → ∃ T ∈ P.parts.biUnion f, x ∈ T := by
      intro S hS
      filter_upwards [hg_covers S hS] with x hx hxS
      obtain ⟨T, hTf, hxT⟩ := hx hxS
      exact ⟨T, Finset.mem_biUnion.mpr ⟨S, hS, by rw [hf_eq S hS]; exact hTf⟩, hxT⟩
    filter_upwards [P.ae_covers, (Filter.eventually_all_finset P.parts).mpr h_ae_list]
        with x ⟨S, hS, hxS⟩ h_all
    exact h_all S hS hxS
  -- Refines
  · intro T hT
    rw [Finset.mem_biUnion] at hT
    obtain ⟨S, hS, hTf⟩ := hT
    rw [hf_eq S hS] at hTf
    exact ⟨S, hS, hg_sub S hS T hTf⟩
  -- IsEquitable
  · intro T hT
    rw [Finset.mem_biUnion] at hT
    obtain ⟨S, hS, hTf⟩ := hT
    rw [hf_eq S hS] at hTf
    -- Both μ(T).toReal and 1/Q.parts.card are in [0, 1/m], so |a - b| ≤ 1/m ≤ ε
    have hT_meas_le : (μ T).toReal ≤ 1 / (m : ℝ) := by
      rw [hg_measure S hS T hTf, ENNReal.toReal_div, ENNReal.toReal_natCast]
      apply div_le_div_of_nonneg_right _ (Nat.cast_pos.mpr hm_pos).le
      calc (μ S).toReal ≤ (μ Set.univ).toReal :=
            ENNReal.toReal_mono (measure_ne_top μ _) (μ.mono (Set.subset_univ _))
        _ = 1 := by simp [measure_univ]
    have hT_meas_nonneg : 0 ≤ (μ T).toReal := ENNReal.toReal_nonneg
    have hcard_ge_m : m ≤ (P.parts.biUnion f).card := by
      obtain ⟨S₀, hS₀, hμS₀⟩ : ∃ S₀ ∈ P.parts, μ S₀ ≠ 0 := by
        by_contra h_all; push_neg at h_all
        have h_not_in : ∀ S ∈ P.parts, ∀ᵐ x ∂μ, x ∉ S := by
          intro S' hS'
          rw [ae_iff, show ({x : α | ¬x ∉ S'} : Set α) = S' from Set.ext (fun _ => not_not)]
          exact h_all S' hS'
        have h_false : ∀ᵐ x ∂μ, False := by
          filter_upwards [P.ae_covers,
            (Filter.eventually_all_finset P.parts).mpr h_not_in]
            with x ⟨S', hS', hxS'⟩ h_all'
          exact h_all' S' hS' hxS'
        rw [ae_iff, show ({x : α | ¬False} : Set α) = Set.univ from
          Set.ext (fun _ => ⟨fun _ => trivial, fun _ => not_false⟩),
          measure_univ] at h_false
        exact one_ne_zero h_false
      calc m = (f S₀).card := by
              rw [hf_eq S₀ hS₀]; simp only [g, dif_neg hμS₀]
              exact (hgp_card S₀ hS₀ hμS₀).symm
        _ ≤ (P.parts.biUnion f).card :=
          Finset.card_le_card (Finset.subset_biUnion_of_mem f hS₀)
    have hinv_card_le : 1 / ((P.parts.biUnion f).card : ℝ) ≤ 1 / (m : ℝ) := by
      exact div_le_div_of_nonneg_left one_pos.le (Nat.cast_pos.mpr hm_pos)
        (Nat.cast_le.mpr hcard_ge_m)
    have hinv_card_nonneg : 0 ≤ 1 / ((P.parts.biUnion f).card : ℝ) := by positivity
    -- |a - b| ≤ max(a, b) for nonneg a, b; then max(a, b) ≤ 1/m ≤ ε
    rw [abs_le]
    constructor
    · linarith
    · linarith
  -- card bound
  · calc (P.parts.biUnion f).card
        ≤ P.parts.sum (fun S => (f S).card) := Finset.card_biUnion_le
      _ ≤ P.parts.sum (fun _ => m) :=
          Finset.sum_le_sum (fun S hS => by rw [hf_eq S hS]; exact hg_card_le S hS)
      _ = P.parts.card * m := by simp [Finset.sum_const]

/-- Any partition can be refined to an equitable one with controlled part count.

**Proof idea**:
Each part S of P is split into m = ⌈1/ε⌉₊ equal-measure pieces using the
intermediate value theorem for atomless measures. The resulting partition has
at most n * m parts (where n = P.parts.card) and each part has measure within
ε of the average 1/(n*m).

The intermediate value theorem for atomless measures (Sierpinski's theorem) is
proved above as `exists_measurable_subset_of_measure`.

The `[NoAtoms μ]` hypothesis ensures the measure has no atoms, which is
necessary for the existence of subsets with prescribed measure. -/
theorem exists_equitable_refinement [StandardBorelSpace α] [NoAtoms μ] (P : MeasurablePartition α μ) (ε : ℝ) (hε : ε > 0) :
    ∃ Q : MeasurablePartition α μ,
      Refines Q P ∧
      IsEquitable Q ε ∧
      Q.parts.card ≤ P.parts.card * ⌈1 / ε⌉₊ :=
  exists_equitable_refinement_construction P ε hε

end Equitable

end Graphon
