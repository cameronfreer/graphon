/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Regularity
import Mathlib.Order.Partition.Finpartition

/-!
# Finpartition adapter for analytic graphon regularity

This file connects Mathlib's `Finpartition (Set.univ : Set α)` to the measurable partitions used by
the graphon regularity development.  A `Finpartition` excludes the empty set, but a nonempty part
may still have measure zero.  Such parts are retained by the adapter.

The null-cell convention is therefore part of the API: `Graphon.rectAverage` agrees exactly with
Mathlib's set average, and both assign value zero to a rectangle when either side has measure zero.
Consequently every null-cell contribution to the partition energy is zero.  No positive-measure
hypothesis on partition parts is needed.

## Main results

* `Finpartition.toMeasurablePartition`: the exact-cover adapter;
* `Graphon.rectAverage_eq_setAverage`: compatibility with Mathlib's set-average convention;
* `Graphon.rectAverage_eq_zero_of_measure_eq_zero_left` and
  `Graphon.rectAverage_eq_zero_of_measure_eq_zero_right`: the null-cell convention;
* `Graphon.energy_toMeasurablePartition`: the adapted energy is the same finite block sum.
-/

open MeasureTheory Set

namespace Finpartition

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Regard a measurable `Finpartition` of `Set.univ` as the graphon development's measurable
partition.  The finite partition covers exactly, hence in particular almost everywhere. -/
noncomputable def toMeasurablePartition (P : Finpartition (Set.univ : Set α))
    (hP : ∀ S ∈ P.parts, MeasurableSet S) : MeasurablePartition α μ where
  parts := P.parts
  measurable_parts := hP
  pairwiseDisjoint := P.disjoint
  ae_covers := Filter.Eventually.of_forall fun x => by
    have hx : x ∈ P.parts.sup id := by
      rw [P.sup_parts]
      exact Set.mem_univ x
    simp only [Finset.sup_set_eq_biUnion, Set.mem_iUnion] at hx
    obtain ⟨S, hS, hxS⟩ := hx
    exact ⟨S, hS, hxS⟩

@[simp]
theorem toMeasurablePartition_parts (P : Finpartition (Set.univ : Set α))
    (hP : ∀ S ∈ P.parts, MeasurableSet S) :
    (P.toMeasurablePartition (μ := μ) hP).parts = P.parts := by
  simp [toMeasurablePartition]

end Finpartition

namespace Graphon

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

/-- The project's rectangle average is exactly Mathlib's set average on the rectangle.  In
particular this identifies the zero-denominator convention rather than merely proving an a.e.
statement about the resulting step graphon. -/
theorem rectAverage_eq_setAverage (W : Graphon α μ) (S T : Set α) :
    rectAverage W S T =
      ⨍ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ) := by
  rw [MeasureTheory.setAverage_eq]
  unfold rectAverage
  rw [MeasureTheory.measureReal_def, Measure.prod_prod S T, ENNReal.toReal_mul]
  by_cases hμS : μ S = 0
  · simp [hμS]
  by_cases hμT : μ T = 0
  · simp [hμT]
  simp only [hμS, hμT, ↓reduceDIte]
  ring

omit [IsProbabilityMeasure μ] in
/-- A rectangle with a null left side has average zero. -/
theorem rectAverage_eq_zero_of_measure_eq_zero_left (W : Graphon α μ) (S T : Set α)
    (hS : μ S = 0) : rectAverage W S T = 0 := by
  simp [rectAverage, hS]

omit [IsProbabilityMeasure μ] in
/-- A rectangle with a null right side has average zero. -/
theorem rectAverage_eq_zero_of_measure_eq_zero_right (W : Graphon α μ) (S T : Set α)
    (hT : μ T = 0) : rectAverage W S T = 0 := by
  simp [rectAverage, hT]

omit [IsProbabilityMeasure μ] in
/-- The energy of a measurable `Finpartition` is the same finite block sum used by the native
measurable-partition API.  In particular the adapter introduces no normalization factor. -/
theorem energy_toMeasurablePartition (W : Graphon α μ)
    (P : Finpartition (Set.univ : Set α)) (hP : ∀ S ∈ P.parts, MeasurableSet S) :
    energy W (P.toMeasurablePartition (μ := μ) hP) =
      P.parts.sum fun S => P.parts.sum fun T =>
        (μ S).toReal * (μ T).toReal * (rectAverage W S T) ^ 2 := by
  simp [energy, Finpartition.toMeasurablePartition]

end Graphon
