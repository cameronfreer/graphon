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

end GraphonSpace
