/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Graphon.InfiniteLaw

/-!
# The canonical infinite law of a graphon class (issue #52)

The infinite exchangeable law descends to graphon space, abstractly — no explicit
sampler required (issue #51 later supplies a raw realization):

* `GraphonSpace.infiniteSampleLaw` — the canonical law of a graphon class on the
  infinite graph space, descended through the quotient (well-defined by the joining
  theorem);
* `GraphonSpace.infiniteSampleLaw_mk` — on classes, it is the infinite extension of the
  fixed-graphon sample law;
* `GraphonSpace.infiniteSampleLaw_map_restrictFin` — its finite restrictions are the
  finite sample laws;
* `GraphonSpace.continuous_infiniteSampleLaw` — weak continuity, by subsequential
  extraction and marginal identification (compactness + uniqueness);
* `GraphonSpace.injective_infiniteSampleLaw` and
  `GraphonSpace.isClosedEmbedding_infiniteSampleLaw` — the graphon space embeds as a
  compact set of probability laws on `InfiniteGraph`.

This removes representatives from all subsequent law-level arguments.
-/

open MeasureTheory InfiniteGraph Filter

namespace GraphonSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ]

/-- **The canonical infinite law of a graphon class**: the infinite extension of the
sample laws, descended through the quotient (well-defined by the joining theorem). -/
noncomputable def infiniteSampleLaw : GraphonSpace α μ → ProbabilityMeasure InfiniteGraph :=
  SeparationQuotient.lift
    (fun W => Graphon.ExchangeableGraphLaw.infiniteLaw (Graphon.sampleExchangeableLaw W))
    fun U W h => by
      have hpmf := (Graphon.samplePMF_eq_all_iff_weaklyIsomorphic U W).mpr
        (Metric.inseparable_iff.mp h)
      have : Graphon.sampleExchangeableLaw U = Graphon.sampleExchangeableLaw W :=
        Graphon.ExchangeableGraphLaw.ext fun k => hpmf k
      rw [this]

@[simp] theorem infiniteSampleLaw_mk (W : Graphon α μ) :
    infiniteSampleLaw (mk W) =
      Graphon.ExchangeableGraphLaw.infiniteLaw (Graphon.sampleExchangeableLaw W) := rfl

/-- **The finite restrictions of the canonical infinite law are the finite sample
laws.** -/
theorem infiniteSampleLaw_map_restrictFin (x : GraphonSpace α μ) (k : ℕ) :
    (infiniteSampleLaw x : Measure InfiniteGraph).map (restrictFin k) =
      (finiteSampleLaw k x).toMeasure := by
  obtain ⟨W, rfl⟩ := surjective_mk x
  rw [infiniteSampleLaw_mk, Graphon.ExchangeableGraphLaw.infiniteLaw_map_restrictFin]
  rfl

/-- The finite sample laws, bundled as probability measures on the finite graph
types. -/
private noncomputable def bundledFiniteSampleLaw (k : ℕ) (x : GraphonSpace α μ) :
    ProbabilityMeasure (SimpleGraph (Fin k)) :=
  ⟨(finiteSampleLaw k x).toMeasure, inferInstance⟩

/-- The bundled finite sample laws are weakly continuous in the graphon class (finite
sums of the continuous mass coordinates). -/
private theorem continuous_bundledFiniteSampleLaw (k : ℕ) :
    Continuous (bundledFiniteSampleLaw (α := α) (μ := μ) k) := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  rw [ContinuousAt, ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hint : ∀ x : GraphonSpace α μ,
      (∫ G, f G ∂(bundledFiniteSampleLaw k x : Measure (SimpleGraph (Fin k)))) =
        ∑ G : SimpleGraph (Fin k), sampleMassCoord G x • f G := by
    intro x
    rw [show (bundledFiniteSampleLaw k x : Measure (SimpleGraph (Fin k))) =
      (finiteSampleLaw k x).toMeasure from rfl, PMF.integral_eq_sum]
    exact Finset.sum_congr rfl fun G _ => by rw [sampleMassCoord_eq_toReal]
  simp only [hint]
  exact ((continuous_finsetSum _ fun G _ =>
    (continuous_sampleMassCoord G).smul continuous_const).tendsto x₀)

/-- **Weak continuity of the canonical infinite law**: subsequential Prokhorov
extraction plus marginal identification (compactness and uniqueness). -/
theorem continuous_infiniteSampleLaw :
    Continuous (infiniteSampleLaw : GraphonSpace α μ → ProbabilityMeasure InfiniteGraph) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  rw [ContinuousAt]
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨Q, ψ, hψ, hconv⟩ := InfiniteGraph.exists_subseq_tendsto
    (fun m => infiniteSampleLaw (ns m))
  have hcomp : Tendsto (fun m => infiniteSampleLaw (ns (ψ m))) atTop (nhds Q) := by
    simpa only [Function.comp_def] using hconv
  refine ⟨ψ, ?_⟩
  have hQ : Q = infiniteSampleLaw x := by
    apply InfiniteGraph.probabilityMeasure_ext_of_map_restrictFin
    intro k
    -- pushforwards of the subsequence converge to Q's restriction
    have h1 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hcomp
      (continuous_restrictFin k)
    -- and each pushforward is exactly the bundled finite sample law
    have h2 : ∀ m, (infiniteSampleLaw (ns (ψ m))).map
        (continuous_restrictFin k).measurable.aemeasurable =
          bundledFiniteSampleLaw k (ns (ψ m)) := by
      intro m
      apply ProbabilityMeasure.toMeasure_injective
      rw [ProbabilityMeasure.toMeasure_map]
      exact infiniteSampleLaw_map_restrictFin (ns (ψ m)) k
    -- which converges to the bundled law at x, by continuity
    have h3 : Tendsto (fun m => bundledFiniteSampleLaw (α := α) (μ := μ) k (ns (ψ m)))
        atTop (nhds (bundledFiniteSampleLaw k x)) :=
      ((continuous_bundledFiniteSampleLaw k).tendsto x).comp
        (hns.comp hψ.tendsto_atTop)
    rw [show (fun m => (infiniteSampleLaw (ns (ψ m))).map
      (continuous_restrictFin k).measurable.aemeasurable) = fun m =>
        bundledFiniteSampleLaw (α := α) (μ := μ) k (ns (ψ m)) from funext h2] at h1
    have h4 := tendsto_nhds_unique h1 h3
    have h5 := congrArg (fun ν : ProbabilityMeasure (SimpleGraph (Fin k)) =>
      (ν : Measure (SimpleGraph (Fin k)))) h4
    rw [ProbabilityMeasure.toMeasure_map] at h5
    rw [h5, infiniteSampleLaw_map_restrictFin]
    rfl
  exact hQ ▸ hcomp

/-- **Injectivity**: the canonical infinite law determines the graphon class (finite
restrictions recover the sample laws, which separate points). -/
theorem injective_infiniteSampleLaw :
    Function.Injective
      (infiniteSampleLaw : GraphonSpace α μ → ProbabilityMeasure InfiniteGraph) := by
  intro x y h
  rw [← finiteSampleLaw_eq_all_iff]
  intro k
  apply PMF.toMeasure_injective
  rw [← infiniteSampleLaw_map_restrictFin x k, ← infiniteSampleLaw_map_restrictFin y k, h]

/-- **The graphon space embeds as a compact set of probability laws on
`InfiniteGraph`**: continuous injection from a compact space into a Hausdorff space
(the infinite analogue of the finite coordinate embedding
`isClosedEmbedding_sampleCoordinates`; the image consists of exchangeable laws, but the
codomain is `ProbabilityMeasure InfiniteGraph`). -/
@[blueprint "thm:infinite-sample-law-embedding"
  (title := /-- The graphon space embeds into laws on infinite graphs -/)]
theorem isClosedEmbedding_infiniteSampleLaw :
    Topology.IsClosedEmbedding
      (infiniteSampleLaw : GraphonSpace α μ → ProbabilityMeasure InfiniteGraph) :=
  continuous_infiniteSampleLaw.isClosedEmbedding injective_infiniteSampleLaw

end GraphonSpace
