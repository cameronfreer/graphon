/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.InfiniteExchangeability
import Graphon.Sampling
import Mathlib.Probability.ProductMeasure

/-!
# The explicit infinite sampler for a fixed graphon (issue #51, sources + sampler)

Reusable i.i.d. product sources via `Measure.infinitePi`, and the explicit measurable
sampler from those sources to the infinite graph space:

* `InfiniteGraph.vertexSource` — i.i.d. vertex positions `ℕ → α` with law `μ`;
* `InfiniteGraph.edgeSource` — i.i.d. edge uniforms on `[0,1]`, indexed by `EdgeIndex`;
* `InfiniteGraph.clampedRep W` — the everywhere-`[0,1]`-valued clamped representative
  of the graphon (a.e. equal to it);
* `InfiniteGraph.sampleInfinite W` — one uniform per unordered edge, compared against
  the clamped graphon value at the `Quot.out`-representative endpoint positions
  (matching `sampleIntegrand`'s orientation): measurable in the sources.

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

/-- The clamped `[0,1]`-valued representative of a graphon: an everywhere-valid edge
probability (the graphon is only a.e. `[0,1]`-valued; clamping isolates the eventual
a.e.-congruence argument). -/
noncomputable def clampedRep (W : Graphon α μ) (p : α × α) : ℝ :=
  min 1 (max 0 (W.toAEEqFun p))

theorem clampedRep_mem_Icc (W : Graphon α μ) (p : α × α) :
    clampedRep W p ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_min zero_le_one (le_max_left 0 _), min_le_left 1 _⟩

theorem measurable_clampedRep (W : Graphon α μ) : Measurable (clampedRep W) :=
  measurable_const.min (measurable_const.max W.toAEEqFun.stronglyMeasurable.measurable)

/-- The clamped representative agrees with the graphon almost everywhere. -/
theorem clampedRep_ae_eq (W : Graphon α μ) :
    ∀ᵐ p ∂(μ.prod μ), clampedRep W p = W.toAEEqFun p := by
  filter_upwards [W.ae_mem_Icc] with p hp
  rw [clampedRep, max_eq_right hp.1, min_eq_right hp.2]

/-- **The explicit infinite sampler**: include the edge `e` exactly when its uniform
falls below the clamped graphon value at the `Quot.out`-representative endpoint
positions (matching the orientation convention of `sampleIntegrand`, which eliminates
the a.e.-symmetry orientation juggling in the marginal identification). -/
noncomputable def sampleInfinite (W : Graphon α μ) (ω : (ℕ → α) × (EdgeIndex → ℝ)) :
    InfiniteGraph :=
  coordEquiv.symm fun e =>
    if ω.2 e ≤ clampedRep W (ω.1 (Quot.out (e : Sym2 ℕ)).1, ω.1 (Quot.out (e : Sym2 ℕ)).2)
    then true else false

/-- The edge coordinates of a sample, unfolded. -/
theorem coordEquiv_sampleInfinite (W : Graphon α μ) (ω : (ℕ → α) × (EdgeIndex → ℝ))
    (e : EdgeIndex) :
    coordEquiv (sampleInfinite W ω) e =
      if ω.2 e ≤ clampedRep W (ω.1 (Quot.out (e : Sym2 ℕ)).1, ω.1 (Quot.out (e : Sym2 ℕ)).2)
      then true else false := by
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
      clampedRep W (ω.1 (Quot.out (e : Sym2 ℕ)).1, ω.1 (Quot.out (e : Sym2 ℕ)).2) :=
    (measurable_clampedRep W).comp
      (((measurable_pi_apply _).comp measurable_fst).prodMk
        ((measurable_pi_apply _).comp measurable_fst))
  have hu : Measurable fun ω : (ℕ → α) × (EdgeIndex → ℝ) => ω.2 e :=
    (measurable_pi_apply e).comp measurable_snd
  have hset : MeasurableSet {ω : (ℕ → α) × (EdgeIndex → ℝ) |
      ω.2 e ≤ clampedRep W (ω.1 (Quot.out (e : Sym2 ℕ)).1, ω.1 (Quot.out (e : Sym2 ℕ)).2)} :=
    measurableSet_le hu hW
  exact Measurable.ite hset measurable_const measurable_const

end InfiniteGraph
