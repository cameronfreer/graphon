/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.InfiniteExchangeability
import Graphon.Sampling
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Sym.Sym2.Order

/-!
# The explicit infinite sampler for a fixed graphon (issue #51, sources + sampler)

Reusable i.i.d. product sources via `Measure.infinitePi`, and the explicit measurable
sampler from those sources to the infinite graph space:

* `InfiniteGraph.vertexSource` — i.i.d. vertex positions `ℕ → α` with law `μ`;
* `InfiniteGraph.edgeSource` — i.i.d. edge uniforms on `[0,1]`, indexed by `EdgeIndex`;
* `InfiniteGraph.sampleInfinite W` — one uniform per unordered edge, compared against
  `W` at the (order-canonical) endpoint positions: measurable in the sources.

The finite marginal identification with `samplePMF W k` and the A2-uniqueness
conclusion `map (sampleInfinite W) source = infiniteLaw (sampleExchangeableLaw W)`
are the next bricks of issue #51.
-/

open MeasureTheory

open scoped Classical

namespace InfiniteGraph

/-- The uniform distribution on `[0,1]`. -/
noncomputable def uniform01 : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure uniform01 :=
  ⟨by rw [uniform01, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Icc]; norm_num⟩

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- **The vertex source**: i.i.d. positions `ℕ → α` with law `μ`. -/
noncomputable def vertexSource : Measure (ℕ → α) :=
  Measure.infinitePi fun _ : ℕ => μ

/-- **The edge source**: i.i.d. uniforms on `[0,1]`, one per unordered edge. -/
noncomputable def edgeSource : Measure (EdgeIndex → ℝ) :=
  Measure.infinitePi fun _ : EdgeIndex => uniform01

instance [IsProbabilityMeasure μ] : IsProbabilityMeasure (vertexSource μ) := by
  rw [vertexSource]; infer_instance

instance : IsProbabilityMeasure (edgeSource) := by
  rw [edgeSource]; infer_instance

/-- **The sampler source**: independent vertex positions and edge uniforms. -/
noncomputable def samplerSource : Measure ((ℕ → α) × (EdgeIndex → ℝ)) :=
  (vertexSource μ).prod edgeSource

instance [IsProbabilityMeasure μ] : IsProbabilityMeasure (samplerSource μ) := by
  rw [samplerSource]; infer_instance

variable {μ}

/-- **The explicit infinite sampler**: include the edge `e` exactly when its uniform
falls below `W` evaluated at the order-canonical endpoint positions. -/
noncomputable def sampleInfinite (W : Graphon α μ) (ω : (ℕ → α) × (EdgeIndex → ℝ)) :
    InfiniteGraph :=
  coordEquiv.symm fun e =>
    if ω.2 e ≤ W.toAEEqFun (ω.1 (Sym2.inf (e : Sym2 ℕ)), ω.1 (Sym2.sup (e : Sym2 ℕ))) then true else false

/-- The edge coordinates of a sample, unfolded. -/
theorem coordEquiv_sampleInfinite (W : Graphon α μ) (ω : (ℕ → α) × (EdgeIndex → ℝ))
    (e : EdgeIndex) :
    coordEquiv (sampleInfinite W ω) e =
      if ω.2 e ≤ W.toAEEqFun (ω.1 (Sym2.inf (e : Sym2 ℕ)), ω.1 (Sym2.sup (e : Sym2 ℕ))) then true
      else false := by
  rw [sampleInfinite, Equiv.apply_symm_apply]

/-- **The sampler is measurable** in the sources: each edge coordinate is a measurable
comparison. -/
theorem measurable_sampleInfinite (W : Graphon α μ) :
    Measurable (sampleInfinite W) := by
  have hsymm : Measurable (coordEquiv.symm : (EdgeIndex → Bool) → InfiniteGraph) :=
    coordHomeomorph.symm.continuous.measurable
  refine hsymm.comp ?_
  rw [measurable_pi_iff]
  intro e
  have hW : Measurable fun ω : (ℕ → α) × (EdgeIndex → ℝ) =>
      W.toAEEqFun (ω.1 (Sym2.inf (e : Sym2 ℕ)), ω.1 (Sym2.sup (e : Sym2 ℕ))) :=
    W.toAEEqFun.stronglyMeasurable.measurable.comp
      (((measurable_pi_apply _).comp measurable_fst).prodMk
        ((measurable_pi_apply _).comp measurable_fst))
  have hu : Measurable fun ω : (ℕ → α) × (EdgeIndex → ℝ) => ω.2 e :=
    (measurable_pi_apply e).comp measurable_snd
  have hset : MeasurableSet {ω : (ℕ → α) × (EdgeIndex → ℝ) |
      ω.2 e ≤ W.toAEEqFun (ω.1 (Sym2.inf (e : Sym2 ℕ)), ω.1 (Sym2.sup (e : Sym2 ℕ)))} :=
    measurableSet_le hu hW
  exact Measurable.ite hset measurable_const measurable_const

end InfiniteGraph
