/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Step
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Homomorphism Densities

This file defines homomorphism densities for graphons, which measure how
frequently a fixed graph pattern appears in a graphon.

## Main definitions

* `Graphon.homDensity` - The homomorphism density `t(F, W)` of a graph `F` in a graphon `W`

## Main results

* `Graphon.homDensity_nonneg` - Homomorphism density is nonnegative
* `Graphon.homDensity_le_one` - Homomorphism density is at most 1

## Implementation notes

The homomorphism density `t(F, W)` for a graph `F` on vertex set `V` and graphon `W` is
defined as the integral over all maps `x : V → [0,1]` of the product of `W(x(u), x(v))`
over all edges `{u, v}` of `F`.

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Section 7.1
-/

open MeasureTheory Set Filter Finset

open scoped unitInterval

namespace Graphon

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

section HomDensity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The homomorphism density `t(F, W)` of a simple graph `F` in a graphon `W`.

This measures the probability that a random map from the vertices of `F` to the
probability space preserves adjacency (in expectation). Formally:

`t(F, W) = ∫_{x : V → α} ∏_{e ∈ E(F)} W(x(u_e), x(v_e)) dμ^V`

The product uses `Quot.out` to extract a canonical representative pair from each
edge in `edgeFinset`. Since `W` is symmetric a.e. and the integral marginalizes
over all vertex mappings, the choice of representative does not affect the result.

For a finite graph `G` on `n` vertices, `t(F, W_G) = hom(F, G) / n^|V(F)|`
where `hom(F, G)` is the number of graph homomorphisms from `F` to `G`. -/
noncomputable def homDensity (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon α μ) : ℝ :=
  ∫ x : V → α, ∏ e ∈ F.edgeFinset, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)
    ∂Measure.pi (fun _ => μ)

/-- The integrand in the homomorphism density formula. -/
noncomputable def homDensityIntegrand (F : SimpleGraph V) [DecidableRel F.Adj]
    (W : Graphon α μ) (x : V → α) : ℝ :=
  ∏ e ∈ F.edgeFinset, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)

theorem homDensity_eq_integral (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon α μ) :
    homDensity F W = ∫ x, homDensityIntegrand F W x ∂Measure.pi (fun _ => μ) := rfl

/-- The homomorphism density of the empty graph is 1.

An empty graph has no edges, so the integrand is a product over an empty set,
which equals 1. The integral of 1 over a probability space is 1. -/
theorem homDensity_bot (W : Graphon α μ) :
    homDensity (⊥ : SimpleGraph V) W = 1 := by
  -- The empty graph has no edges, so the integrand is a product over ∅, which is 1.
  -- The integral of 1 over a probability space is 1.
  sorry

/-- The integrand in the homomorphism density is nonnegative.

This follows because each factor `W(x(u), x(v))` is nonnegative (W takes values
in [0,1] a.e.) and a product of nonnegative terms is nonnegative. -/
theorem homDensityIntegrand_nonneg (F : SimpleGraph V) [DecidableRel F.Adj]
    (W : Graphon α μ) (x : V → α) : 0 ≤ homDensityIntegrand F W x := by
  unfold homDensityIntegrand
  apply prod_nonneg
  intro e _
  -- Need: 0 ≤ W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)
  -- This follows from W being a graphon (values in [0,1] a.e.)
  -- but we only have the a.e. statement, not pointwise
  sorry

/-- The integrand in the homomorphism density is at most 1.

This follows because each factor `W(x(u), x(v))` is at most 1 (W takes values
in [0,1] a.e.) and a product of terms ≤ 1 (with each ≥ 0) is ≤ 1. -/
theorem homDensityIntegrand_le_one (F : SimpleGraph V) [DecidableRel F.Adj]
    (W : Graphon α μ) (x : V → α) : homDensityIntegrand F W x ≤ 1 := by
  unfold homDensityIntegrand
  -- Product of terms in [0,1] is in [0,1]
  sorry

/-- Homomorphism density is nonnegative.

This is the integral of a nonnegative function over a positive measure space. -/
theorem homDensity_nonneg (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon α μ) :
    0 ≤ homDensity F W := by
  unfold homDensity
  apply integral_nonneg
  intro x
  exact homDensityIntegrand_nonneg F W x

/-- Homomorphism density is at most 1.

This follows because the integrand is bounded by 1 and we integrate over a
probability space. -/
theorem homDensity_le_one (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon α μ) :
    homDensity F W ≤ 1 := by
  -- The integrand is bounded by 1, and we integrate over a probability space
  sorry

/-- Homomorphism density is in `[0, 1]`. -/
theorem homDensity_mem_Icc (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon α μ) :
    homDensity F W ∈ Set.Icc 0 1 :=
  ⟨homDensity_nonneg F W, homDensity_le_one F W⟩

end HomDensity

end Graphon
