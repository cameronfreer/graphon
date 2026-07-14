/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.InfiniteSampler
import Graphon.EmpiricalGraphon
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Convergence in probability for the fixed-graphon sampler (issue #57, part 1)

The empirical graphons of an explicit `W`-random infinite graph converge to the class
of `W` in probability:

* `InfiniteGraph.sampledEmpiricalGraphon W n ω` — the empirical graphon of the sampled
  infinite graph at level `n + 1` (measurable in the sources);
* `InfiniteGraph.sampledEmpiricalGraphon_tendstoInMeasure` — **convergence in
  probability**: for every `ε > 0` the probability that the empirical graphon is
  `ε`-far from `mk W` tends to `0`. The bad event is the pullback of the complement of
  the `sampleGoodMassOn` event; its measure is `1 − sampleGoodMassOn W (n+1) ε` by the
  marginal identification, and the project's `first_sampling_lemma_of_large_k` (the
  manuscript's Second Sampling Lemma, Lovász Lemma 10.16 — see the crosswalk in
  issue #18) drives it to zero.

The almost-sure strengthening (issue #71, the manuscript's Proposition 11.32) is proved
in `Graphon/AlmostSureSampling.lean`, via the exponential hom-density concentration of
`Graphon/SampleExposure.lean` and Borel–Cantelli.
-/

open MeasureTheory InfiniteGraph Filter

namespace InfiniteGraph

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ]

/-- **The sampled empirical graphon** at level `n + 1`: sample a `W`-random infinite
graph, restrict to the first `n + 1` vertices, take its graphon class. -/
noncomputable def sampledEmpiricalGraphon (W : Graphon α μ) (n : ℕ)
    (ω : (ℕ → α) × (EdgeIndex → ℝ)) : GraphonSpace α μ :=
  GraphonSpace.empiricalGraphon n (sampleInfinite W ω)

theorem measurable_sampledEmpiricalGraphon (W : Graphon α μ) (n : ℕ) :
    Measurable (sampledEmpiricalGraphon (α := α) (μ := μ) W n) :=
  (GraphonSpace.measurable_empiricalGraphon n).comp (measurable_sampleInfinite W)

/-- **Convergence in probability of the sampled empirical graphons** (issue #57,
part 1): the empirical graphons of a `W`-random infinite graph tend to the class of `W`
in measure. -/
@[blueprint "thm:sampler-convergence-in-probability"
  (title := /-- The sampled empirical graphons converge in probability -/)]
theorem sampledEmpiricalGraphon_tendstoInMeasure (W : Graphon α μ) :
    TendstoInMeasure (samplerSource μ) (sampledEmpiricalGraphon W) atTop
      (fun _ => GraphonSpace.mk W) := by
  classical
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  -- the bad event at level n is a finite-marginal event
  have hbad : ∀ n : ℕ, {ω : (ℕ → α) × (EdgeIndex → ℝ) |
      ε ≤ dist (sampledEmpiricalGraphon W n ω) (GraphonSpace.mk W)} =
        (restrictFin (n + 1) ∘ sampleInfinite W) ⁻¹'
          {G : SimpleGraph (Fin (n + 1)) |
            ε ≤ Graphon.cutDistance W (Graphon.ofSimpleGraphOn G)} := by
    intro n
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Function.comp_apply,
      sampledEmpiricalGraphon, GraphonSpace.empiricalGraphon, GraphonSpace.graphClass,
      GraphonSpace.dist_mk]
    rw [Graphon.cutDistance_symm]
  -- whose probability is the bad sample mass
  have hmass : ∀ n : ℕ, samplerSource μ ((restrictFin (n + 1) ∘ sampleInfinite W) ⁻¹'
      {G : SimpleGraph (Fin (n + 1)) |
        ε ≤ Graphon.cutDistance W (Graphon.ofSimpleGraphOn G)}) =
      ENNReal.ofReal (1 - Graphon.sampleGoodMassOn W (n + 1) ε) := by
    intro n
    rw [← Measure.map_apply ((measurable_restrictFin (n + 1)).comp
        (measurable_sampleInfinite W)) ((Set.to_countable _).measurableSet),
      map_sampleInfinite_restrictFin, PMF.toMeasure_apply
        (hs := (Set.to_countable _).measurableSet), tsum_fintype,
      Graphon.one_sub_sampleGoodMassOn, ENNReal.ofReal_sum_of_nonneg (fun G _ => by
        split
        · exact Graphon.sampleMass_nonneg W G
        · exact le_rfl)]
    refine Finset.sum_congr rfl fun G _ => ?_
    simp only [Set.indicator_apply, Set.mem_setOf_eq, Graphon.samplePMF_apply]
    split
    · rfl
    · exact ENNReal.ofReal_zero.symm
  simp only [hbad, hmass]
  -- first_sampling_lemma_of_large_k (the manuscript's Second Sampling Lemma)
  -- drives the bad mass to zero
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ⊤ with rfl | hηtop
  · exact Filter.Eventually.of_forall fun n => le_top
  have hηpos : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
  obtain ⟨K, hK⟩ := Graphon.first_sampling_lemma_of_large_k (α := α) (μ := μ) ε η.toReal hε hηpos
  filter_upwards [Filter.eventually_ge_atTop K] with n hn
  have hgood := hK (n + 1) (le_trans hn (Nat.le_succ n)) inferInstance W
  calc ENNReal.ofReal (1 - Graphon.sampleGoodMassOn W (n + 1) ε)
      ≤ ENNReal.ofReal η.toReal := ENNReal.ofReal_le_ofReal (by linarith)
    _ = η := ENNReal.ofReal_toReal hηtop

end InfiniteGraph
