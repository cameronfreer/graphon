/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.InfiniteSampleLaw
import Graphon.InfiniteRepresentation

/-!
# The barycenter interpretation of the infinite mixture (issue #54)

The represented infinite law of a mixing measure really is the mixture of the
fiber laws, as a `Measure.bind` construction:

* `GraphonSpace.measurable_infiniteSampleLaw_toMeasure` — the canonical infinite law is
  a measurable family of measures (Dynkin induction over the cylinder π-system, using
  the measurable finite sample-law masses);
* `GraphonSpace.mixtureInfiniteLaw` — the barycenter
  `(P : Measure _).bind (fun x => infiniteSampleLaw x)`, bundled as a probability
  measure and characterized on measurable sets by
  `mixtureInfiniteLaw_apply : ... = ∫⁻ x, infiniteSampleLaw x A ∂P`;
* `GraphonSpace.mixtureInfiniteLaw_eq` — **the barycenter identification**:
  `mixtureInfiniteLaw P = (infiniteMixtureLawEquiv P).law` (every cylinder marginal is
  the mixture marginal `mixturePMF P k`, and finite-restriction extensionality
  concludes).
-/

open MeasureTheory InfiniteGraph

namespace GraphonSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ]

/-- **The canonical infinite law is a measurable family of measures**: measurability of
each evaluation, by Dynkin induction over the generating cylinder π-system, where the
masses are the (measurable) finite sample-law masses. -/
theorem measurable_infiniteSampleLaw_toMeasure :
    Measurable fun x : GraphonSpace α μ =>
      (infiniteSampleLaw x : Measure InfiniteGraph) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro s hs
  induction s, hs using MeasurableSpace.induction_on_inter
    (h_eq := generateFrom_cylinders_eq.symm) (h_inter := isPiSystem_cylinders) with
  | empty => simp
  | basic t ht =>
    simp only [cylinders, Set.mem_iUnion, Set.mem_range] at ht
    obtain ⟨k, S, rfl⟩ := ht
    have hmeas : ∀ x : GraphonSpace α μ,
        (infiniteSampleLaw x : Measure InfiniteGraph) (restrictFin k ⁻¹' S) =
          ∑' G : SimpleGraph (Fin k),
            S.indicator (fun G' => finiteSampleLaw k x G') G := by
      intro x
      rw [← Measure.map_apply (measurable_restrictFin k) ((Set.to_countable S).measurableSet),
        infiniteSampleLaw_map_restrictFin, PMF.toMeasure_apply]
      exact (Set.to_countable S).measurableSet
    simp only [hmeas]
    refine Measurable.tsum fun G => ?_
    by_cases hG : G ∈ S
    · simpa only [Set.indicator_of_mem hG] using measurable_finiteSampleLaw_apply k G
    · simpa only [Set.indicator_of_notMem hG] using measurable_const
  | compl t htm iht =>
    have hval : ∀ x : GraphonSpace α μ,
        (infiniteSampleLaw x : Measure InfiniteGraph) tᶜ =
          1 - (infiniteSampleLaw x : Measure InfiniteGraph) t := by
      intro x
      rw [measure_compl htm (measure_ne_top _ t), measure_univ]
    simp only [hval]
    exact measurable_const.sub iht
  | iUnion f hdisj hfm ihf =>
    have hval : ∀ x : GraphonSpace α μ,
        (infiniteSampleLaw x : Measure InfiniteGraph) (⋃ i, f i) =
          ∑' i, (infiniteSampleLaw x : Measure InfiniteGraph) (f i) := fun x =>
      measure_iUnion hdisj hfm
    simp only [hval]
    exact Measurable.tsum ihf

/-- **The barycenter of the canonical infinite laws** over a mixing measure, as a
probability measure. -/
noncomputable def mixtureInfiniteLaw (P : ProbabilityMeasure (GraphonSpace α μ)) :
    ProbabilityMeasure InfiniteGraph :=
  ⟨(P : Measure (GraphonSpace α μ)).bind
      fun x => (infiniteSampleLaw x : Measure InfiniteGraph), by
    constructor
    rw [Measure.bind_apply MeasurableSet.univ
      measurable_infiniteSampleLaw_toMeasure.aemeasurable]
    simp [measure_univ]⟩

@[simp] theorem mixtureInfiniteLaw_coe (P : ProbabilityMeasure (GraphonSpace α μ)) :
    (mixtureInfiniteLaw P : Measure InfiniteGraph) =
      (P : Measure (GraphonSpace α μ)).bind
        fun x => (infiniteSampleLaw x : Measure InfiniteGraph) := rfl

/-- The barycenter, characterized on measurable sets. -/
theorem mixtureInfiniteLaw_apply (P : ProbabilityMeasure (GraphonSpace α μ))
    {A : Set InfiniteGraph} (hA : MeasurableSet A) :
    (mixtureInfiniteLaw P : Measure InfiniteGraph) A =
      ∫⁻ x, (infiniteSampleLaw x : Measure InfiniteGraph) A
        ∂(P : Measure (GraphonSpace α μ)) :=
  Measure.bind_apply hA measurable_infiniteSampleLaw_toMeasure.aemeasurable

/-- **The barycenter identification** (issue #54): the represented infinite law of a
mixing measure is the mixture of the canonical fiber laws — every cylinder marginal is
the mixture marginal, and finite-restriction extensionality concludes. -/
@[blueprint "thm:mixture-barycenter"
  (title := /-- The infinite mixture is the barycenter of the fiber laws -/)]
theorem mixtureInfiniteLaw_eq (P : ProbabilityMeasure (GraphonSpace α μ)) :
    mixtureInfiniteLaw P = (infiniteMixtureLawEquiv (α := α) (μ := μ) P).law := by
  apply InfiniteGraph.probabilityMeasure_ext_of_map_restrictFin
  intro k
  show ((mixtureInfiniteLaw P : Measure InfiniteGraph)).map (restrictFin k) = _
  rw [show ((infiniteMixtureLawEquiv (α := α) (μ := μ) P).law :
    Measure InfiniteGraph).map (restrictFin k) = (mixturePMF P k).toMeasure from
    infiniteMixtureLawEquiv_law_map_restrictFin P k]
  ext S hS
  rw [Measure.map_apply (measurable_restrictFin k) hS,
    mixtureInfiniteLaw_apply P ((measurable_restrictFin k) hS),
    PMF.toMeasure_apply (hs := hS)]
  have hfiber : ∀ x : GraphonSpace α μ,
      (infiniteSampleLaw x : Measure InfiniteGraph) (restrictFin k ⁻¹' S) =
        ∑' G : SimpleGraph (Fin k),
          S.indicator (fun G' => finiteSampleLaw k x G') G := by
    intro x
    rw [← Measure.map_apply (measurable_restrictFin k) hS,
      infiniteSampleLaw_map_restrictFin, PMF.toMeasure_apply (hs := hS)]
  simp only [hfiber]
  classical
  have hmeas : ∀ G : SimpleGraph (Fin k), AEMeasurable
      (fun x : GraphonSpace α μ => S.indicator (fun G' => finiteSampleLaw k x G') G)
      (P : Measure (GraphonSpace α μ)) := by
    intro G
    by_cases hG : G ∈ S
    · simpa only [Set.indicator_of_mem hG] using
        (measurable_finiteSampleLaw_apply k G).aemeasurable
    · simpa only [Set.indicator_of_notMem hG] using aemeasurable_const
  rw [lintegral_tsum hmeas]
  refine tsum_congr fun G => ?_
  by_cases hG : G ∈ S
  · simp only [Set.indicator_of_mem hG]
    exact (mixturePMF_apply P k G).symm
  · simp [Set.indicator_of_notMem hG]
