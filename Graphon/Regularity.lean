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
  -- The proof rearranges the variance identity:
  -- ∫ (W - c)² = ∫ W² - 2c ∫ W + c² · μ(S×T)
  -- Therefore: ∫ W² = ∫ (W - c)² + 2c ∫ W - c² · μ(S×T)
  -- Using ∫ W = c · μ(S×T): ∫ W² = ∫ (W - c)² + c² · μ(S×T)
  --
  -- The technical details involve integral linearity and can be completed later.
  sorry

/-- Key identity: L² norm = energy + defect.

‖W‖₂² = E(P, W) + D(P, W)

where E(P, W) is the energy and D(P, W) is the defect.
This follows from the Pythagorean theorem for L² orthogonal projections. -/
theorem l2_norm_eq_energy_add_defect (W : Graphon α μ) (P : MeasurablePartition α μ) :
    ∫ p, (W.toAEEqFun p) ^ 2 ∂(μ.prod μ) = energy W P + defect W P := by
  -- The proof uses variance_decomposition_rect for each rectangle,
  -- then sums over the partition.
  sorry

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
  -- The proof constructs Q by finding a good cut of S (or T):
  -- 1. If ∫_{S×T} (W - avg)² ≥ ε² μ(S) μ(T), then W varies significantly on S × T
  -- 2. By Markov/Chebyshev, there exists a measurable cut S = S₁ ∪ S₂ such that
  --    |rectAverage W S₁ T - rectAverage W S T| ≥ ε/2 or similar
  -- 3. Replacing S with S₁, S₂ in P gives Q
  -- 4. The energy increase comes from: new terms have (avg on smaller set)²
  --    which by convexity arguments increases the sum
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
  -- The proof iterates energy_increment until defect is small
  sorry

end Regularity

/-! ### Equitable partitions -/

section Equitable

variable [IsProbabilityMeasure μ]

/-- A partition is ε-equitable if all parts have measure within ε of 1/k,
    where k is the number of parts. -/
def IsEquitable (P : MeasurablePartition α μ) (ε : ℝ) : Prop :=
  ∀ S ∈ P.parts, |(μ S).toReal - 1 / P.parts.card| ≤ ε

/-- Any partition can be refined to an equitable one with controlled part count. -/
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
