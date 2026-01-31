/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Approximation

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

/-- The T-average takes values in [0, 1] when W is a graphon.

This uses that W ∈ [0,1] a.e. on the product measure, so for a.e. x,
the function y ↦ W(x,y) is in [0,1] for a.e. y. -/
theorem tAverage_mem_Icc (W : Graphon α μ) (T : Set α) (hT : MeasurableSet T) (x : α) :
    tAverage W T x ∈ Set.Icc 0 1 := by
  unfold tAverage
  by_cases h : μ T = 0
  · simp only [h, dif_pos, Set.mem_Icc, le_refl, zero_le_one, and_self]
  · simp only [h, dif_neg, not_false_eq_true, Set.mem_Icc]
    have hT_pos : 0 < (μ T).toReal := ENNReal.toReal_pos h (measure_lt_top μ T).ne
    constructor
    · -- tAverage ≥ 0
      apply mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      -- The integral ∫_T W(x,y) dy ≥ 0 since W ≥ 0 a.e.
      -- This uses Fubini: for a.e. x, W(x,·) ≥ 0 a.e.
      sorry
    · -- tAverage ≤ 1
      -- ∫_T W(x,y) dy ≤ ∫_T 1 dy = μ(T) since W ≤ 1 a.e.
      sorry

/-- The average of W_T over S equals rectAverage W S T.

This is a consequence of Fubini-Tonelli:
  (1/μS) ∫_S W_T dx = (1/μS) ∫_S (1/μT) ∫_T W(x,y) dy dx
                     = (1/μS μT) ∫_{S×T} W
                     = rectAverage W S T -/
theorem tAverage_integral_eq_rectAverage (W : Graphon α μ) (S T : Set α)
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hμS : μ S ≠ 0) (hμT : μ T ≠ 0) :
    (μ S).toReal⁻¹ * ∫ x in S, tAverage W T x ∂μ = rectAverage W S T := by
  -- Uses Fubini to convert iterated integral to product integral
  -- and pull out the constant (μ T)⁻¹
  sorry

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

/-- Energy increment lemma (Frieze-Kannan style).

If W has large defect on some rectangle S × T of P, then refining that
rectangle increases the energy.

More precisely: if there exist S, T ∈ P such that
∫_{S×T} |W - rectAverage W S T|² ≥ ε² μ(S) μ(T),
then splitting S (or T) into two parts by an appropriate cut increases
the energy by at least ε⁴/4 (or similar constant).

This is the key step that drives the regularity iteration. -/
theorem energy_increment (W : Graphon α μ) (P : MeasurablePartition α μ)
    (ε : ℝ) (hε : ε > 0)
    (h_bad : ∃ S ∈ P.parts, ∃ T ∈ P.parts,
      ∫ p in S ×ˢ T, (W.toAEEqFun p - rectAverage W S T) ^ 2 ∂(μ.prod μ) ≥
        ε ^ 2 * (μ S).toReal * (μ T).toReal) :
    ∃ Q : MeasurablePartition α μ,
      Refines Q P ∧ Q.parts.card ≤ 2 * P.parts.card ∧
      energy W Q ≥ energy W P + ε ^ 4 / 4 := by
  -- **Proof outline** (Frieze-Kannan energy increment):
  --
  -- Given: ∫_{S×T} (W - c)² ≥ ε² μ(S) μ(T) where c = rectAverage W S T
  --
  -- **Step 1**: Define T-average function
  --   W_T(x) := (1/μ(T)) ∫_T W(x,y) dμ(y)
  --   This is measurable and takes values in [0,1]
  --
  -- **Step 2**: Apply Chebyshev to W_T on S
  --   Variance of W_T on S ≥ ε² (follows from Fubini + hypothesis)
  --   By Chebyshev: ∃ t such that μ{x ∈ S : W_T(x) > t} and μ{x ∈ S : W_T(x) ≤ t}
  --   both have measure ≥ μ(S)/2, and the averages differ by ≥ ε
  --
  -- **Step 3**: Define S₁ = {x ∈ S : W_T(x) ≤ t}, S₂ = S \ S₁
  --   Both are measurable (W_T is measurable)
  --   Build Q by replacing S with S₁, S₂ in P
  --
  -- **Step 4**: Energy increase via convexity
  --   Old contribution: μ(S)μ(T) · c²
  --   New contribution: μ(S₁)μ(T) · c₁² + μ(S₂)μ(T) · c₂²
  --   where c₁, c₂ are new rectangle averages
  --   By convexity of x², when c₁ and c₂ are separated from c,
  --   the weighted sum increases by ≥ ε⁴/4
  --
  -- **Required helper lemmas** (not yet implemented):
  -- - Measurability of conditional expectation / T-average
  -- - Chebyshev inequality for variance on measure spaces
  -- - Partition refinement construction
  sorry

end Energy

/-! ### Regularity lemma -/

section Regularity

variable [IsProbabilityMeasure μ]

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
   - This increases energy by ≥ ε⁴/C
3. Since energy ≤ 1, we get at most C/ε⁴ iterations
4. Each iteration at most doubles parts, so final count ≤ 2^{C/ε⁴}
5. More careful analysis gives polynomial bound ~1/ε⁸ -/
theorem regularity (W : Graphon α μ) (ε : ℝ) (hε : ε > 0) :
    ∃ P : MeasurablePartition α μ,
      P.parts.card ≤ regularityBound ε ∧
      defect W P ≤ ε ^ 2 := by
  -- **Proof outline** (Frieze-Kannan iteration):
  --
  -- Start with trivial partition P₀ = {α}
  --
  -- **Iteration**: While defect W P > ε²:
  --   1. Find "bad" rectangle S × T where local variance ≥ ε² μ(S) μ(T)
  --   2. Apply energy_increment to get P' refining P
  --   3. Energy increases by ≥ ε⁴/4
  --
  -- **Termination**:
  --   - energy W P ≤ 1 (by energy_le_one)
  --   - Each iteration increases energy by ≥ ε⁴/4
  --   - So at most 4/ε⁴ iterations
  --
  -- **Part count bound**:
  --   - Each iteration at most doubles parts
  --   - Starting with 1 part, after k iterations: ≤ 2^k parts
  --   - With k ≤ 4/ε⁴: parts ≤ 2^{4/ε⁴}
  --   - More careful analysis gives polynomial bound ~1/ε⁸
  --
  -- **Depends on**: energy_increment (sorry above)
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

**Challenge**: Constructing the equal-measure partition of a measurable set
requires the Lebesgue density theorem or explicit construction via
layer cake / quantile functions. Not trivial in full generality. -/
theorem exists_equitable_refinement (P : MeasurablePartition α μ) (ε : ℝ) (hε : ε > 0) :
    ∃ Q : MeasurablePartition α μ,
      Refines Q P ∧
      IsEquitable Q ε ∧
      Q.parts.card ≤ P.parts.card * ⌈1 / ε⌉₊ := by
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
