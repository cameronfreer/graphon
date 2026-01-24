/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Graphons

A graphon is a symmetric measurable function `W : [0,1]² → [0,1]` that represents
the limit of a convergent sequence of dense graphs.

## Main definitions

* `Graphon` - the type of graphons

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012]
-/

open MeasureTheory

/-- A graphon is a symmetric measurable function from the unit square to [0,1]. -/
structure Graphon where
  /-- The underlying function -/
  toFun : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 → ℝ
  /-- The function takes values in [0,1] -/
  le_one : ∀ x y, toFun x y ≤ 1
  /-- The function is nonnegative -/
  nonneg : ∀ x y, 0 ≤ toFun x y
  /-- The function is symmetric -/
  symm : ∀ x y, toFun x y = toFun y x
  /-- The function is measurable -/
  measurable : Measurable (fun p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1 => toFun p.1 p.2)

namespace Graphon

instance : CoeFun Graphon (fun _ => Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 → ℝ) :=
  ⟨toFun⟩

/-- The constant zero graphon. -/
def zero : Graphon where
  toFun _ _ := 0
  le_one _ _ := zero_le_one
  nonneg _ _ := le_refl 0
  symm _ _ := rfl
  measurable := measurable_const

/-- The constant one graphon (complete graph limit). -/
def one : Graphon where
  toFun _ _ := 1
  le_one _ _ := le_refl 1
  nonneg _ _ := zero_le_one
  symm _ _ := rfl
  measurable := measurable_const

end Graphon
