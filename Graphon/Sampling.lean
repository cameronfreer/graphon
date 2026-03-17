/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.HomDensity
import Graphon.CutNorm

/-!
# Sampling Random Graphs from Graphons

This file defines expected edge density for graphon sampling. Concentration
bounds and the full random graph sampling API are future work.

**Experimental**: Concentration bounds and the full random graph sampling API
are future work.

## Main definitions

* `Graphon.sampleGraphExpectedDensity` — Expected edge density of sampled graph

## Main results

* `Graphon.sampleGraphExpectedDensity_eq` — Expected density equals ∫∫ W
* `Graphon.sampleGraphExpectedDensity_mem_Icc` — Expected density is in [0, 1]

## Implementation notes

The sampling process for G(n, W) is:
1. Sample n i.i.d. points x₁, ..., xₙ uniformly from [0,1]
2. Connect vertices i and j (i < j) independently with probability W(xᵢ, xⱼ)

This is a two-level randomness: first the positions, then the edges.

The key result established here is that the expected edge density equals the
integral of the graphon. Concentration and convergence results are future work.

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Section 10.2-10.3
-/

open MeasureTheory Set Filter Finset

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

/-! ### Sampling definition -/

section Sampling

variable [IsProbabilityMeasure μ]

/-- The expected edge density of a graph sampled from a graphon.

For a graphon W, if we sample n points x₁,...,xₙ and connect i~j with
probability W(xᵢ,xⱼ), the expected edge density is ∫∫ W(x,y) dμ(x) dμ(y).

Note: This is the expected density over both the position randomness and
the edge randomness. -/
noncomputable def sampleGraphExpectedDensity (W : Graphon α μ) : ℝ :=
  ∫ p, W.toAEEqFun p ∂(μ.prod μ)

/-- The expected edge density equals the double integral of the graphon. -/
theorem sampleGraphExpectedDensity_eq (W : Graphon α μ) :
    sampleGraphExpectedDensity W = ∫ x, (∫ y, W.toAEEqFun (x, y) ∂μ) ∂μ := by
  unfold sampleGraphExpectedDensity
  -- Apply Fubini's theorem
  exact integral_prod W.toAEEqFun (SymmKernel.graphon_integrable W)

/-- The expected edge density is in [0,1]. -/
theorem sampleGraphExpectedDensity_mem_Icc (W : Graphon α μ) :
    sampleGraphExpectedDensity W ∈ Set.Icc 0 1 := by
  constructor
  · -- Nonnegativity from W ≥ 0 a.e.
    unfold sampleGraphExpectedDensity
    apply integral_nonneg_of_ae
    filter_upwards [W.ae_mem_Icc] with p hp
    exact hp.1
  · -- Upper bound from W ≤ 1 a.e. and μ being probability measure
    unfold sampleGraphExpectedDensity
    -- ∫ W ≤ ∫ 1 = 1 since W ≤ 1 a.e. and μ is probability measure
    calc ∫ p, W.toAEEqFun p ∂(μ.prod μ)
        ≤ ∫ _, (1 : ℝ) ∂(μ.prod μ) := by
          apply integral_mono_ae (SymmKernel.graphon_integrable W) (integrable_const 1)
          filter_upwards [W.ae_mem_Icc] with p hp
          exact hp.2
      _ = ((μ.prod μ) univ).toReal := by rw [integral_const, smul_eq_mul, mul_one]; rfl
      _ = 1 := by
          have h_prob : IsProbabilityMeasure (μ.prod μ) := inferInstance
          simp [h_prob.measure_univ]

end Sampling

end Graphon
