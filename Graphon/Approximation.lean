/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Step
import Graphon.CutDistance

/-!
# Approximation of Graphons by Step Functions

This file develops the theory of approximating graphons by step functions,
which is central to the regularity lemma and compactness of graphon space.

## Main definitions

* `Graphon.rectAverage` - Average value of a graphon over a rectangle
* `Graphon.Refines` - Partition refinement relation

## Main results

* `Graphon.rectAverage_mem_Icc` - Rectangle averages are in [0, 1]
* `Graphon.rectAverage_symm` - Rectangle averages are symmetric

## Implementation notes

Given a measurable partition P of α, the stepified graphon takes the average value
on each rectangle S × T for S, T ∈ P:
`(stepify P W)(x, y) = (1/(μ(S)μ(T))) ∫_{S×T} W dμ×μ` for x ∈ S, y ∈ T

The full stepification construction requires building an AEEqFun from piecewise
definitions, which is deferred to future work.

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Section 9.2-9.3
-/

open MeasureTheory Set Filter Finset

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

/-! ### Rectangle averages -/

section RectAverage

variable [IsProbabilityMeasure μ]

/-- The average value of a graphon over a rectangle S × T.

This is the building block for stepification:
`rectAverage W S T = (1/(μ(S)μ(T))) ∫_{S×T} W dμ×μ` -/
noncomputable def rectAverage (W : Graphon α μ) (S T : Set α) : ℝ :=
  if hS : μ S = 0 then 0
  else if hT : μ T = 0 then 0
  else (μ S).toReal⁻¹ * (μ T).toReal⁻¹ *
    ∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ)

/-- The rectangle average is in [0, 1] for graphons. -/
theorem rectAverage_mem_Icc (W : Graphon α μ) (S T : Set α)
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    rectAverage W S T ∈ Set.Icc 0 1 := by
  unfold rectAverage
  split_ifs with hμS_zero hμT_zero
  · exact ⟨le_refl 0, zero_le_one⟩
  · exact ⟨le_refl 0, zero_le_one⟩
  · -- The integral is between 0 and μ(S)μ(T), so the average is in [0,1]
    -- Since W ∈ [0,1] a.e., we have 0 ≤ ∫_{S×T} W ≤ μ(S×T) = μ(S)μ(T)
    have hS_pos : 0 < (μ S).toReal := ENNReal.toReal_pos hμS_zero (measure_lt_top μ S).ne
    have hT_pos : 0 < (μ T).toReal := ENNReal.toReal_pos hμT_zero (measure_lt_top μ T).ne
    -- Bounds on the integral
    have h_int_nonneg : 0 ≤ ∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ) := by
      apply setIntegral_nonneg_of_ae_restrict
      exact ae_restrict_of_ae (W.ae_mem_Icc.mono fun p hp => hp.1)
    have h_int_le : ∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ) ≤ (μ S).toReal * (μ T).toReal := by
      calc ∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ)
          ≤ ∫ _ in S ×ˢ T, (1 : ℝ) ∂(μ.prod μ) := by
            apply setIntegral_mono_ae_restrict
            · exact (SymmKernel.graphon_integrable W).integrableOn
            · exact integrable_const 1
            · exact ae_restrict_of_ae (W.ae_mem_Icc.mono fun p hp => hp.2)
        _ = ((μ.prod μ) (S ×ˢ T)).toReal := by
            rw [setIntegral_const, smul_eq_mul, mul_one]; rfl
        _ = (μ S).toReal * (μ T).toReal := by
            rw [Measure.prod_prod]; simp only [ENNReal.toReal_mul]
    constructor
    · -- Lower bound: 0
      apply mul_nonneg
      apply mul_nonneg (inv_nonneg.mpr hS_pos.le) (inv_nonneg.mpr hT_pos.le)
      exact h_int_nonneg
    · -- Upper bound: 1
      calc (μ S).toReal⁻¹ * (μ T).toReal⁻¹ * ∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ)
          ≤ (μ S).toReal⁻¹ * (μ T).toReal⁻¹ * ((μ S).toReal * (μ T).toReal) := by
            apply mul_le_mul_of_nonneg_left h_int_le
            apply mul_nonneg (inv_nonneg.mpr hS_pos.le) (inv_nonneg.mpr hT_pos.le)
        _ = 1 := by field_simp

/-- The rectangle average is symmetric. -/
theorem rectAverage_symm (W : Graphon α μ) (S T : Set α)
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    rectAverage W S T = rectAverage W T S := by
  unfold rectAverage
  split_ifs with h1 h2 h3 _
  · rfl
  · rfl
  · rfl
  · -- Use symmetry of W
    rw [mul_comm (μ S).toReal⁻¹ (μ T).toReal⁻¹]
    congr 1
    -- The integral over S × T equals the integral over T × S by symmetry of W
    exact SymmKernel.rectIntegral_symm W.toSymmKernel hS hT

/-- Rectangle average of zero graphon is zero. -/
theorem rectAverage_zero (S T : Set α) : rectAverage (zero : Graphon α μ) S T = 0 := by
  unfold rectAverage
  split_ifs with hS hT
  · rfl
  · rfl
  · simp only [mul_eq_zero]
    right
    -- The integral of 0 is 0
    apply setIntegral_eq_zero_of_ae_eq_zero
    have h : ∀ᵐ p ∂(μ.prod μ), (zero : Graphon α μ).toAEEqFun p = 0 :=
      (AEEqFun.coeFn_const (α × α) (0 : ℝ))
    exact h.mono fun p hp _ => hp

/-- Rectangle average of one graphon is one (for positive measure sets). -/
theorem rectAverage_one {S T : Set α} (hS : μ S ≠ 0) (hT : μ T ≠ 0)
    (hSm : MeasurableSet S) (hTm : MeasurableSet T) :
    rectAverage (one : Graphon α μ) S T = 1 := by
  unfold rectAverage
  simp only [hS, hT, dite_false]
  -- The one graphon has toAEEqFun = 1 a.e.
  have h_one : ∀ᵐ p ∂(μ.prod μ), (one : Graphon α μ).toAEEqFun p = 1 :=
    (AEEqFun.coeFn_const (α × α) (1 : ℝ))
  -- Use setIntegral_congr_ae to replace toAEEqFun with 1
  conv_lhs => rw [setIntegral_congr_ae (hSm.prod hTm) (h_one.mono fun p hp _ => hp)]
  -- Now we have ∫ p in S ×ˢ T, 1 = (μ.prod μ)(S ×ˢ T)
  rw [MeasureTheory.setIntegral_one_eq_measureReal, MeasureTheory.measureReal_prod_prod]
  -- The result follows by field arithmetic: (μ S)⁻¹ * (μ T)⁻¹ * (μ S * μ T) = 1
  simp only [Measure.real, ENNReal.toReal]
  have hS_nnreal : (0 : ℝ) < (μ S).toNNReal := ENNReal.toNNReal_pos hS (measure_lt_top μ S).ne
  have hT_nnreal : (0 : ℝ) < (μ T).toNNReal := ENNReal.toNNReal_pos hT (measure_lt_top μ T).ne
  field_simp [hS_nnreal.ne', hT_nnreal.ne']

end RectAverage

/-! ### Refinement -/

section Refinement

variable [IsProbabilityMeasure μ]

/-- A partition Q refines P if every part of Q is contained in some part of P. -/
def Refines (Q P : MeasurablePartition α μ) : Prop :=
  ∀ T ∈ Q.parts, ∃ S ∈ P.parts, T ⊆ S

/-- Refinement is reflexive. -/
theorem Refines.refl (P : MeasurablePartition α μ) : Refines P P :=
  fun T hT => ⟨T, hT, Subset.refl T⟩

/-- Refinement is transitive. -/
theorem Refines.trans {P Q R : MeasurablePartition α μ}
    (hPQ : Refines Q P) (hQR : Refines R Q) : Refines R P := by
  intro T hT
  obtain ⟨S, hS, hTS⟩ := hQR T hT
  obtain ⟨U, hU, hSU⟩ := hPQ S hS
  exact ⟨U, hU, hTS.trans hSU⟩

end Refinement

/-! ### Stepification (to be developed)

The full stepification construction requires:
1. Building an AEEqFun that is piecewise constant on partition rectangles
2. Showing this is measurable and symmetric
3. Proving it takes values in [0,1] a.e.

This will be developed in future phases when the machinery for
piecewise-defined graphons is established.
-/

end Graphon
