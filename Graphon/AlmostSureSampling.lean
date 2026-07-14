/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.SampleExposure
import Graphon.InfiniteSamplingConvergence
import Graphon.InverseCounting

/-!
# Almost-sure convergence of the sampled empirical graphons (issue #71)

The empirical graphons of an explicit `W`-random infinite graph converge to the class
of `W` **almost surely** — the pathwise strengthening of the convergence in probability
of `Graphon/InfiniteSamplingConvergence.lean` (issue #57), via Route A of issue #71
(coordinatewise hom-density concentration, Lovász Prop 11.32):

* `InfiniteGraph.ae_tendsto_homDensity_restrictFin` — **per-coordinate Borel–Cantelli**:
  for each fixed finite graph `F`, the summability bridge
  `InfiniteGraph.tsum_samplerSource_homDensity_tail_ne_top` (issue #72, item 1) at each
  tolerance `1/(m+1)` feeds `MeasureTheory.ae_eventually_notMem`, so almost surely the
  hom-densities of the initial restrictions converge to `t(F, W)`;
* `InfiniteGraph.sampledEmpiricalGraphon_tendsto_ae` — **almost-sure convergence**:
  intersecting over the countable family `Σ q, SimpleGraph (Fin q)` gives a full-measure
  set on which every hom-density converges; the convergence equivalence
  `Graphon.cutDistance_tendsto_iff_homDensity_tendsto` (the counting/inverse-counting
  characterization) upgrades this pathwise to cut-distance convergence, hence to
  convergence in the graphon space via `GraphonSpace.dist_mk`.
-/

open MeasureTheory InfiniteGraph Filter

namespace InfiniteGraph

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ]

/-- **Per-coordinate Borel–Cantelli** (issue #71, Route A, steps 1–3): for each fixed
finite graph `F`, almost every sampled infinite graph has the hom-densities of its
initial restrictions converging to `t(F, W)` — the deviation events at tolerance
`1/(m+1)` have summable probabilities by the concentration tail of issue #72, item 1. -/
theorem ae_tendsto_homDensity_restrictFin (W : Graphon α μ)
    {q : ℕ} (F : SimpleGraph (Fin q)) [DecidableRel F.Adj] :
    ∀ᵐ ω ∂(samplerSource μ),
      Filter.Tendsto (fun n => Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α)
          (μ := μ) (restrictFin (n + 1) (sampleInfinite W ω)))) Filter.atTop
        (nhds (Graphon.homDensity F W)) := by
  -- Borel–Cantelli at each tolerance `1/(m+1)`, intersected over `m`.
  have key : ∀ᵐ ω ∂(samplerSource μ), ∀ m : ℕ, ∀ᶠ n in Filter.atTop,
      ω ∉ {ω' : (ℕ → α) × (EdgeIndex → ℝ) | 1 / ((m : ℝ) + 1) ≤
        |Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
          (restrictFin (n + 1) (sampleInfinite W ω'))) - Graphon.homDensity F W|} :=
    MeasureTheory.ae_all_iff.mpr fun m =>
      MeasureTheory.ae_eventually_notMem
        (tsum_samplerSource_homDensity_tail_ne_top W F
          (ε := 1 / ((m : ℝ) + 1)) (by positivity))
  filter_upwards [key] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hω m)
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  rw [not_le] at h
  rw [Real.dist_eq]
  exact h.trans hm

/-- **Almost-sure convergence of the sampled empirical graphons** (issue #71, part 2):
almost every `W`-random infinite graph has its empirical graphons converging to the
class of `W` in the graphon space. Route A: intersect the per-coordinate Borel–Cantelli
over the countable family of finite graphs, then upgrade pathwise via the convergence
equivalence (counting + inverse counting). -/
@[blueprint "thm:sampler-almost-sure"
  (title := /-- Almost-sure convergence of the sampled empirical graphons -/)]
theorem sampledEmpiricalGraphon_tendsto_ae (W : Graphon α μ) :
    ∀ᵐ ω ∂(samplerSource μ),
      Filter.Tendsto (fun n => sampledEmpiricalGraphon W n ω) Filter.atTop
        (nhds (GraphonSpace.mk W)) := by
  classical
  -- Step 4: intersect over the countable family `Σ q, SimpleGraph (Fin q)`.
  have key : ∀ᵐ ω ∂(samplerSource μ), ∀ p : (Σ q : ℕ, SimpleGraph (Fin q)),
      Filter.Tendsto (fun n => Graphon.homDensity p.2 (Graphon.ofSimpleGraphOn (α := α)
          (μ := μ) (restrictFin (n + 1) (sampleInfinite W ω)))) Filter.atTop
        (nhds (Graphon.homDensity p.2 W)) :=
    MeasureTheory.ae_all_iff.mpr fun p => ae_tendsto_homDensity_restrictFin W p.2
  filter_upwards [key] with ω hω
  -- Step 5: pathwise, every hom-density converges (any `DecidableRel` instance).
  have hhom : ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [inst : DecidableRel F.Adj], ∀ ε > 0,
      ∃ N, ∀ n ≥ N,
        |Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
          (restrictFin (n + 1) (sampleInfinite W ω))) - Graphon.homDensity F W| < ε := by
    intro k F inst ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hω ⟨k, F⟩) ε hε
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [Real.dist_eq] at h
    rw [Graphon.homDensity_congr_decRel F inst (Classical.decRel _),
      Graphon.homDensity_congr_decRel F inst (Classical.decRel _) W]
    exact h
  -- Step 6: the convergence equivalence upgrades to cut-distance convergence.
  have hcut := (Graphon.cutDistance_tendsto_iff_homDensity_tendsto
      (fun n => Graphon.ofSimpleGraphOn (α := α) (μ := μ)
        (restrictFin (n + 1) (sampleInfinite W ω))) W).mpr hhom
  -- Step 7: transfer to the metric of the graphon space.
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hcut ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hrepr : sampledEmpiricalGraphon W n ω =
      GraphonSpace.mk (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
        (restrictFin (n + 1) (sampleInfinite W ω))) := rfl
  rw [hrepr, GraphonSpace.dist_mk]
  exact hN n hn

end InfiniteGraph
