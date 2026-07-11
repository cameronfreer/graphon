/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.MixtureKernel
import Graphon.AlmostSureSampling

/-!
# The universal measurable empirical limit (issue #58)

One measure-independent limit function for the empirical graphons of an infinite graph,
stated at the canonical instance (`α := unitInterval`, `μ := volume`, codomain
`StandardGraphonSpace`):

* `GraphonSpace.empiricalConvergenceSet` — the (measurable, measure-independent) set of
  infinite graphs whose empirical graphons converge in the standard graphon space
  (`measurableSet_empiricalConvergenceSet`, via
  `MeasureTheory.measurableSet_exists_tendsto`);
* `GraphonSpace.limitGraphon` — **the universal empirical limit**: the unique limit on
  the convergence set, the explicit zero-graphon class off it; measurable everywhere
  (`measurable_limitGraphon`: metrizable-limit measurability on the convergence-set
  subtype, glued with the constant on the measurable complement);
* `GraphonSpace.ae_tendsto_empiricalGraphon_infiniteSampleLaw` — **the per-class fiber
  theorem**: under the canonical infinite law of EVERY class `x`, the empirical
  graphons converge to `x` almost surely (the almost-sure sampling theorem of issue
  #71, transported along the explicit-sampler realization of issue #51);
* under any infinite exchangeable law `M`, the convergence set is conull
  (`ae_mem_empiricalConvergenceSet`, via the barycenter identification of issue #54)
  and the empirical graphons converge to `limitGraphon` almost surely
  (`ae_tendsto_empiricalGraphon_limitGraphon`);
* `GraphonSpace.map_limitGraphon_law` — **the distributional identification**: the law
  of `limitGraphon` under `M` is exactly the representing mixing measure
  `infiniteMixtureLawEquiv.symm M` — the empirical limit realizes the mixture
  coordinate as a genuine random variable.

Pointwise finite-permutation invariance of `limitGraphon` is deferred to issue #59: it
needs isomorphism-invariance of the finite graph classes (`graphClass ∘ comap` by a
`Fin`-permutation), which is not yet in the library.
-/

open MeasureTheory InfiniteGraph Filter

namespace GraphonSpace

/-- **The empirical convergence set**: the infinite graphs whose empirical graphons
converge in the standard graphon space. Measure-independent — the domain of the
universal empirical limit `limitGraphon`. -/
def empiricalConvergenceSet : Set InfiniteGraph :=
  {G | ∃ x : StandardGraphonSpace,
    Filter.Tendsto (fun n => empiricalGraphon n G) Filter.atTop (nhds x)}

/-- The empirical convergence set is measurable (the codomain is completely metrizable
and second countable). -/
theorem measurableSet_empiricalConvergenceSet :
    MeasurableSet empiricalConvergenceSet :=
  MeasureTheory.measurableSet_exists_tendsto fun n =>
    measurable_empiricalGraphon (α := unitInterval) (μ := volume) n

section
open Classical

/-- **The universal empirical limit**: the limit of the empirical graphons on the
convergence set, the class of the zero graphon (the explicit canonical default, not an
arbitrary inhabitant) off it. Measure-independent — one function for all exchangeable
laws at once. -/
noncomputable def limitGraphon (G : InfiniteGraph) : StandardGraphonSpace :=
  if h : G ∈ empiricalConvergenceSet then h.choose
  else mk (Graphon.constGraphon 0)

end

/-- The universal empirical limit computes any actual limit (limits are unique in the
Hausdorff graphon space). -/
theorem limitGraphon_eq_of_tendsto {G : InfiniteGraph} {x : StandardGraphonSpace}
    (h : Filter.Tendsto (fun n => empiricalGraphon n G) Filter.atTop (nhds x)) :
    limitGraphon G = x := by
  have hG : G ∈ empiricalConvergenceSet := ⟨x, h⟩
  rw [limitGraphon, dif_pos hG]
  exact tendsto_nhds_unique hG.choose_spec h

/-- **The universal empirical limit is measurable**: on the convergence-set subtype it
is a pointwise limit of measurable functions into a metrizable space; on the measurable
complement it is constant. -/
theorem measurable_limitGraphon : Measurable limitGraphon := by
  refine measurable_of_restrict_of_restrict_compl
    measurableSet_empiricalConvergenceSet ?_ ?_
  · -- On the convergence set: pointwise limit of the restricted empirical graphons.
    refine measurable_of_tendsto_metrizable
      (f := fun n => empiricalConvergenceSet.restrict fun G => empiricalGraphon n G)
      (fun n => (measurable_empiricalGraphon n).comp measurable_subtype_coe)
      (tendsto_pi_nhds.mpr fun G => ?_)
    obtain ⟨x, hx⟩ := G.2
    show Filter.Tendsto (fun n => empiricalGraphon n ↑G) Filter.atTop
      (nhds (limitGraphon ↑G))
    rw [limitGraphon_eq_of_tendsto hx]
    exact hx
  · -- On the complement: the constant zero-graphon class.
    have h0 : (empiricalConvergenceSetᶜ.restrict limitGraphon) =
        fun _ => mk (Graphon.constGraphon 0) :=
      funext fun G => dif_neg G.2
    rw [h0]
    exact measurable_const

/-- **The per-class fiber theorem** (every class, not just almost every): under the
canonical infinite law of ANY graphon class `x`, the empirical graphons converge to `x`
almost surely — the almost-sure sampling theorem (issue #71) transported along the
explicit-sampler realization (issue #51) of the fiber law. -/
theorem ae_tendsto_empiricalGraphon_infiniteSampleLaw (x : StandardGraphonSpace) :
    ∀ᵐ G ∂(infiniteSampleLaw x : Measure InfiniteGraph),
      Filter.Tendsto (fun n => empiricalGraphon n G) Filter.atTop (nhds x) := by
  obtain ⟨W, rfl⟩ := surjective_mk x
  rw [← InfiniteGraph.map_sampleInfinite_eq_infiniteSampleLaw_mk W,
    MeasureTheory.ae_map_iff (InfiniteGraph.measurable_sampleInfinite W).aemeasurable
      (measurableSet_tendsto (nhds (mk W)) fun n => measurable_empiricalGraphon n)]
  exact InfiniteGraph.sampledEmpiricalGraphon_tendsto_ae W

/-- The barycenter form of an infinite exchangeable law at the canonical instance:
`M.law` is the mixture of the canonical fiber laws over the representing mixing
measure `infiniteMixtureLawEquiv.symm M` (the coerced form of the barycenter
identification `mixtureInfiniteLaw_eq` of issue #54). -/
theorem law_eq_bind_infiniteSampleLaw (M : Graphon.InfiniteExchangeableGraphLaw) :
    (M.law : Measure InfiniteGraph) =
      ((infiniteMixtureLawEquiv (α := unitInterval) (μ := volume)).symm M :
          Measure StandardGraphonSpace).bind
        fun x => (infiniteSampleLaw x : Measure InfiniteGraph) := by
  have h : mixtureInfiniteLaw
      ((infiniteMixtureLawEquiv (α := unitInterval) (μ := volume)).symm M) = M.law := by
    rw [mixtureInfiniteLaw_eq, Equiv.apply_symm_apply]
  rw [← h, mixtureInfiniteLaw_coe]

/-- **The convergence set is conull under every infinite exchangeable law**: by the
barycenter identification, its complement has zero mass in every fiber (the per-class
fiber theorem), hence zero mass in the mixture. -/
theorem ae_mem_empiricalConvergenceSet (M : Graphon.InfiniteExchangeableGraphLaw) :
    ∀ᵐ G ∂(M.law : Measure InfiniteGraph), G ∈ empiricalConvergenceSet := by
  have hmem : ∀ x : StandardGraphonSpace,
      ∀ᵐ G ∂(infiniteSampleLaw x : Measure InfiniteGraph),
        G ∈ empiricalConvergenceSet := fun x =>
    (ae_tendsto_empiricalGraphon_infiniteSampleLaw x).mono fun G hG => ⟨x, hG⟩
  have hzero : ∀ x : StandardGraphonSpace,
      (infiniteSampleLaw x : Measure InfiniteGraph) empiricalConvergenceSetᶜ = 0 :=
    fun x => by simpa using mem_ae_iff.mp (hmem x)
  rw [ae_iff, law_eq_bind_infiniteSampleLaw M,
    show {G : InfiniteGraph | ¬G ∈ empiricalConvergenceSet} =
      empiricalConvergenceSetᶜ from rfl,
    Measure.bind_apply measurableSet_empiricalConvergenceSet.compl
      measurable_infiniteSampleLaw_toMeasure.aemeasurable]
  simp only [hzero]
  exact lintegral_zero

/-- **Almost-sure convergence to the universal limit**: under every infinite
exchangeable law, the empirical graphons converge to `limitGraphon` almost surely. -/
theorem ae_tendsto_empiricalGraphon_limitGraphon (M : Graphon.InfiniteExchangeableGraphLaw) :
    ∀ᵐ G ∂(M.law : Measure InfiniteGraph),
      Filter.Tendsto (fun n => empiricalGraphon n G) Filter.atTop
        (nhds (limitGraphon G)) := by
  filter_upwards [ae_mem_empiricalConvergenceSet M] with G hG
  obtain ⟨x, hx⟩ := hG
  rw [limitGraphon_eq_of_tendsto hx]
  exact hx

/-- **The distributional identification** (issue #58): under any infinite exchangeable
law `M`, the law of the universal empirical limit is exactly the representing mixing
measure `infiniteMixtureLawEquiv.symm M`. Fiberwise, the limit is almost surely the
fiber point, so each fiber gives the preimage of a measurable set indicator mass; the
barycenter integrates the indicator back to the mixing measure. -/
@[blueprint "thm:limit-graphon"
  (title := /-- The empirical graphon limit as a random variable -/)]
theorem map_limitGraphon_law (M : Graphon.InfiniteExchangeableGraphLaw) :
    M.law.map measurable_limitGraphon.aemeasurable =
      (infiniteMixtureLawEquiv (α := unitInterval) (μ := volume)).symm M := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  ext S hS
  rw [Measure.map_apply measurable_limitGraphon hS, law_eq_bind_infiniteSampleLaw M,
    Measure.bind_apply (measurable_limitGraphon hS)
      measurable_infiniteSampleLaw_toMeasure.aemeasurable]
  have hfiber : ∀ x : StandardGraphonSpace,
      (infiniteSampleLaw x : Measure InfiniteGraph) (limitGraphon ⁻¹' S) =
        S.indicator 1 x := by
    intro x
    have hlim : ∀ᵐ G ∂(infiniteSampleLaw x : Measure InfiniteGraph),
        limitGraphon G = x :=
      (ae_tendsto_empiricalGraphon_infiniteSampleLaw x).mono fun G hG =>
        limitGraphon_eq_of_tendsto hG
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Pi.one_apply]
      refine (prob_compl_eq_zero_iff (measurable_limitGraphon hS)).mp ?_
      have hae : ∀ᵐ G ∂(infiniteSampleLaw x : Measure InfiniteGraph),
          G ∈ limitGraphon ⁻¹' S := hlim.mono fun G hG => by
        rw [Set.mem_preimage, hG]; exact hx
      exact mem_ae_iff.mp hae
    · rw [Set.indicator_of_notMem hx]
      have hae : ∀ᵐ G ∂(infiniteSampleLaw x : Measure InfiniteGraph),
          G ∈ (limitGraphon ⁻¹' S)ᶜ := hlim.mono fun G hG => by
        rw [Set.mem_compl_iff, Set.mem_preimage, hG]; exact hx
      exact compl_mem_ae_iff.mp hae
  rw [lintegral_congr hfiber, lintegral_indicator_one hS]

/-- The distributional identification, as an equality of raw pushforward measures. -/
theorem map_limitGraphon_law_coe (M : Graphon.InfiniteExchangeableGraphLaw) :
    (M.law : Measure InfiniteGraph).map limitGraphon =
      ((infiniteMixtureLawEquiv (α := unitInterval) (μ := volume)).symm M :
        Measure StandardGraphonSpace) := by
  rw [← ProbabilityMeasure.toMeasure_map M.law measurable_limitGraphon.aemeasurable,
    map_limitGraphon_law M]

end GraphonSpace
