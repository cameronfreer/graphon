/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.InfiniteRepresentation

/-!
# Empirical graphons of an infinite exchangeable graph (issue #56)

Cashing out the empirical convergence theorem at the infinite level:

* `GraphonSpace.empiricalGraphon n G` — the graphon class of the first `n + 1` vertices
  of an infinite graph (successor indexing discharges `NeZero`);
* `GraphonSpace.map_empiricalGraphon` — its law under an infinite exchangeable law `M`
  is exactly the empirical mixing measure of `M`'s finite marginals;
* `GraphonSpace.empiricalGraphon_tendsto` — **the empirical graphons converge in
  distribution to the representing measure** `infiniteMixtureLawEquiv.symm M`
  (immediate from `empiricalMixing_tendsto_representingMeasure`).
-/

open MeasureTheory InfiniteGraph Filter

namespace GraphonSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

/-- **The empirical graphon** at level `n + 1`: the graphon class of the restriction of
an infinite graph to its first `n + 1` vertices. -/
noncomputable def empiricalGraphon (n : ℕ) (G : InfiniteGraph) : GraphonSpace α μ :=
  graphClass (restrictFin (n + 1) G)

theorem measurable_empiricalGraphon (n : ℕ) :
    Measurable (empiricalGraphon (α := α) (μ := μ) n) :=
  (measurable_of_countable (graphClass (α := α) (μ := μ))).comp
    (measurable_restrictFin (n + 1))

/-- **The law of the empirical graphon is the empirical mixing measure** of the finite
marginals. -/
theorem map_empiricalGraphon (M : Graphon.InfiniteExchangeableGraphLaw) (n : ℕ) :
    (M.law : Measure InfiniteGraph).map (empiricalGraphon (α := α) (μ := μ) n) =
      (empiricalMixing (α := α) (μ := μ) M.toExchangeableGraphLaw (n + 1) :
        Measure (GraphonSpace α μ)) := by
  rw [empiricalMixing_coe, Graphon.InfiniteExchangeableGraphLaw.toExchangeableGraphLaw_law,
    Measure.map_map (measurable_of_countable _) (measurable_restrictFin (n + 1))]
  rfl

/-- **Empirical graphons converge in distribution to the representing measure**: the
distributional cash-out of the empirical convergence theorem at the infinite level. -/
theorem empiricalGraphon_tendsto (M : Graphon.InfiniteExchangeableGraphLaw) :
    Tendsto (fun n => M.law.map
        (measurable_empiricalGraphon (α := α) (μ := μ) n).aemeasurable) atTop
      (nhds ((infiniteMixtureLawEquiv (α := α) (μ := μ)).symm M)) := by
  have hb : ∀ n, M.law.map (measurable_empiricalGraphon (α := α) (μ := μ) n).aemeasurable =
      empiricalMixing (α := α) (μ := μ) M.toExchangeableGraphLaw (n + 1) := fun n =>
    ProbabilityMeasure.toMeasure_injective (by
      rw [ProbabilityMeasure.toMeasure_map]
      exact map_empiricalGraphon M n)
  rw [show (fun n => M.law.map
      (measurable_empiricalGraphon (α := α) (μ := μ) n).aemeasurable) =
    fun n => empiricalMixing (α := α) (μ := μ) M.toExchangeableGraphLaw (n + 1) from
    funext hb]
  have hlim : (mixtureExchangeableLawEquiv (α := α) (μ := μ)).symm
      M.toExchangeableGraphLaw = (infiniteMixtureLawEquiv (α := α) (μ := μ)).symm M := by
    apply (mixtureExchangeableLawEquiv (α := α) (μ := μ)).injective
    rw [Equiv.apply_symm_apply]
    have : (infiniteMixtureLawEquiv (α := α) (μ := μ)).symm M =
        (mixtureExchangeableLawEquiv (α := α) (μ := μ)).symm
          (Graphon.exchangeableGraphLawEquivInfinite.symm M) := rfl
    rw [this, Equiv.apply_symm_apply]
    rfl
  rw [← hlim]
  exact empiricalMixing_tendsto_representingMeasure M.toExchangeableGraphLaw

end GraphonSpace
