/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.VertexTail
import Graphon.InfiniteExtremality
import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne
import Mathlib.Probability.Independence.ZeroOne

/-!
# Toward the five-way extremality theorem (Diaconis–Janson Theorem 5.5, issue #91)

The vertex-tail formulation of extremality: the empirical limit is vertex-tail
measurable (`Graphon/VertexTail.lean`), so a law with a trivial vertex-tail σ-algebra
has a Dirac representing measure, hence is dissociated.

* `Graphon.InfiniteExchangeableGraphLaw.VertexTailTrivial` — the vertex-tail σ-algebra
  is `M.law`-trivial;
* `Graphon.InfiniteExchangeableGraphLaw.law_map_drop` — the law is invariant under the
  tail shift (consistency of the finite marginals);
* `GraphonSpace.isDissociated_of_vertexTailTrivial` — **vertex-tail triviality implies
  dissociation**: the representing measure has all-`0`/`1` masses (its coordinates
  factor through the tail-measurable `limitGraphon`), hence is Dirac.
-/

open MeasureTheory Set Filter Topology

/-! ### The initial and vertex-tail σ-algebras and their laws -/

namespace InfiniteGraph

/-- The initial σ-algebra: events depending only on the first `k` vertices. -/
@[reducible] noncomputable def initialAlgebra (k : ℕ) : MeasurableSpace InfiniteGraph :=
  MeasurableSpace.comap (restrictFin k) inferInstance

theorem initialAlgebra_le (k : ℕ) :
    initialAlgebra k ≤ (inferInstance : MeasurableSpace InfiniteGraph) :=
  measurable_iff_comap_le.mp (measurable_restrictFin k)

/-- The initial σ-algebras are monotone in the number of vertices. -/
theorem initialAlgebra_mono : Monotone initialAlgebra := by
  intro k l h
  refine measurable_iff_comap_le.mp ?_
  rw [show restrictFin k = (fun H : SimpleGraph (Fin l) => H.comap (Fin.castLEEmb h)) ∘
      restrictFin l from funext fun G => restrictFin_comap h G]
  exact (SimpleGraph.measurable_comap _).comp
    (@Measurable.of_comap_le _ _ (initialAlgebra l) _ (restrictFin l) le_rfl)

/-- **The initial σ-algebras generate the Borel σ-algebra**: the initial cylinders are
a generating family. -/
theorem iSup_initialAlgebra_eq :
    (⨆ k, initialAlgebra k) = (inferInstance : MeasurableSpace InfiniteGraph) := by
  refine le_antisymm (iSup_le initialAlgebra_le) ?_
  rw [← generateFrom_cylinders_eq]
  refine MeasurableSpace.generateFrom_le fun t ht => ?_
  simp only [cylinders, Set.mem_iUnion, Set.mem_range] at ht
  obtain ⟨k, S, rfl⟩ := ht
  exact le_iSup initialAlgebra k _
    (MeasurableSpace.measurableSet_comap.mpr ⟨S, (Set.to_countable S).measurableSet, rfl⟩)

end InfiniteGraph

namespace Graphon.InfiniteExchangeableGraphLaw

/-- **The law is invariant under the tail shift**: deleting the first `k` vertices does
not change the law (consistency of the finite marginals under the `addNat` injections). -/
theorem law_map_drop (M : Graphon.InfiniteExchangeableGraphLaw) (k : ℕ) :
    (M.law : Measure InfiniteGraph).map (InfiniteGraph.drop k) =
      (M.law : Measure InfiniteGraph) := by
  refine InfiniteGraph.ext_of_map_restrictFin fun m => ?_
  haveI : ∀ j, IsProbabilityMeasure
      ((M.law : Measure InfiniteGraph).map (InfiniteGraph.restrictFin j)) :=
    fun j => Measure.isProbabilityMeasure_map (InfiniteGraph.measurable_restrictFin j).aemeasurable
  rw [Measure.map_map (InfiniteGraph.measurable_restrictFin m) (InfiniteGraph.measurable_drop k),
    show InfiniteGraph.restrictFin m ∘ InfiniteGraph.drop k =
        (fun H : SimpleGraph (Fin (m + k)) => H.comap (Fin.addNatEmb k)) ∘
          InfiniteGraph.restrictFin (m + k)
      from funext fun G => InfiniteGraph.restrictFin_drop m k G,
    ← Measure.map_map (SimpleGraph.measurable_comap _)
      (InfiniteGraph.measurable_restrictFin (m + k)),
    ← M.toExchangeableGraphLaw_law (m + k),
    PMF.toMeasure_map _ _ (SimpleGraph.measurable_comap _),
    M.toExchangeableGraphLaw.consistent (Fin.addNatEmb k),
    M.toExchangeableGraphLaw_law m]

/-- **Vertex-tail triviality**: every event in the vertex-tail σ-algebra
`⋂ₖ σ(G|{k,k+1,…})` has `M.law`-measure `0` or `1`. -/
def VertexTailTrivial (M : Graphon.InfiniteExchangeableGraphLaw) : Prop :=
  ∀ s, MeasurableSet[InfiniteGraph.vertexTailAlgebra] s →
    (M.law : Measure InfiniteGraph) s = 0 ∨ (M.law : Measure InfiniteGraph) s = 1

open ProbabilityTheory in
/-- **Restriction independence**: for every `k`, the graph on the first `k` vertices is
independent of the graph on the remaining vertices. -/
def RestrictionIndependent (M : Graphon.InfiniteExchangeableGraphLaw) : Prop :=
  ∀ k, Indep (InfiniteGraph.initialAlgebra k) (InfiniteGraph.tailAlgebra k)
    (M.law : Measure InfiniteGraph)

open ProbabilityTheory in
/-- **Restriction independence implies vertex-tail triviality**: a vertex-tail event is
independent of every initial σ-algebra, hence — the initial σ-algebras generating the
Borel σ-algebra — independent of itself, so has measure `0` or `1`. -/
theorem vertexTailTrivial_of_restrictionIndependent
    {M : Graphon.InfiniteExchangeableGraphLaw} (hM : M.RestrictionIndependent) :
    M.VertexTailTrivial := by
  haveI : IsProbabilityMeasure (M.law : Measure InfiniteGraph) := M.law.2
  intro s hs
  -- the vertex-tail σ-algebra is independent of every initial σ-algebra
  have hindep : ∀ k, Indep (InfiniteGraph.initialAlgebra k)
      InfiniteGraph.vertexTailAlgebra (M.law : Measure InfiniteGraph) := fun k =>
    indep_of_indep_of_le_right (hM k) (InfiniteGraph.vertexTailAlgebra_le_tailAlgebra k)
  -- hence independent of their supremum, which is the whole Borel σ-algebra
  have hsup : Indep (⨆ k, InfiniteGraph.initialAlgebra k)
      InfiniteGraph.vertexTailAlgebra (M.law : Measure InfiniteGraph) :=
    indep_iSup_of_directed_le hindep InfiniteGraph.initialAlgebra_le
      InfiniteGraph.vertexTailAlgebra_le
      (Monotone.directed_le InfiniteGraph.initialAlgebra_mono)
  rw [InfiniteGraph.iSup_initialAlgebra_eq] at hsup
  -- restrict to the vertex-tail σ-algebra: it is independent of itself
  have hself : Indep InfiniteGraph.vertexTailAlgebra InfiniteGraph.vertexTailAlgebra
      (M.law : Measure InfiniteGraph) :=
    indep_of_indep_of_le_left hsup InfiniteGraph.vertexTailAlgebra_le
  exact measure_eq_zero_or_one_of_indep_self hself hs

end Graphon.InfiniteExchangeableGraphLaw

/-! ### Vertex-tail triviality implies dissociation -/

namespace GraphonSpace

/-- **Vertex-tail triviality implies a Dirac representing measure**: the representing
measure's Borel masses factor through the tail-measurable `limitGraphon`, so they are
all `0` or `1`, forcing a Dirac. -/
theorem representing_dirac_of_vertexTailTrivial
    {M : Graphon.InfiniteExchangeableGraphLaw} (hM : M.VertexTailTrivial) :
    ∃ x : StandardGraphonSpace,
      (infiniteMixtureLawEquiv (α := unitInterval) (μ := volume)).symm M = diracProba x := by
  set P := (infiniteMixtureLawEquiv (α := unitInterval) (μ := volume)).symm M with hP
  haveI : IsProbabilityMeasure (P : Measure StandardGraphonSpace) := P.2
  -- every Borel mass of the representing measure factors through the tail-measurable
  -- `limitGraphon`, hence is `0` or `1`
  haveI hzo : IsZeroOneMeasure (P : Measure StandardGraphonSpace) := by
    refine ⟨fun s hs => ?_⟩
    have hpre : (M.law : Measure InfiniteGraph) (limitGraphon ⁻¹' s) =
        (P : Measure StandardGraphonSpace) s := by
      rw [hP, ← map_limitGraphon_law_coe M, Measure.map_apply measurable_limitGraphon hs]
    rw [← hpre]
    exact hM _ (measurable_limitGraphon_vertexTailAlgebra hs)
  haveI : NeZero (P : Measure StandardGraphonSpace) :=
    ⟨IsProbabilityMeasure.ne_zero _⟩
  obtain ⟨x, hx⟩ := IsZeroOneMeasure.exists_eq_dirac (μ := (P : Measure StandardGraphonSpace))
  refine ⟨x, ProbabilityMeasure.toMeasure_injective ?_⟩
  rw [hx, show ((diracProba x : ProbabilityMeasure StandardGraphonSpace) :
    Measure StandardGraphonSpace) = Measure.dirac x from rfl]

/-- **Vertex-tail triviality implies dissociation** (a Diaconis–Janson Theorem 5.5
arc): a law whose vertex-tail σ-algebra is trivial is dissociated. -/
@[blueprint "thm:vertex-tail-dissociation"
  (title := /-- Vertex-tail triviality implies dissociation -/)]
theorem isDissociated_of_vertexTailTrivial
    {M : Graphon.InfiniteExchangeableGraphLaw} (hM : M.VertexTailTrivial) :
    M.IsDissociated :=
  (isDissociated_iff_representing_dirac (α := unitInterval) (μ := volume) M).mpr
    (representing_dirac_of_vertexTailTrivial hM)

end GraphonSpace
