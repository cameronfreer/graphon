/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.EmpiricalGraphon
import Graphon.LimitGraphon
import Graphon.SamplingFinite

/-!
# Vertex-tail infrastructure (issue #97, Campaign A, PR 2)

Tail restriction of infinite graphs, finite-deletion stability of empirical-graphon
limits, and tail measurability of the universal empirical limit:

* `GraphonSpace.graphClass_comap_perm` — the graphon class of a finite graph is
  invariant under vertex permutations (hom densities are map averages, and
  precomposition by a permutation is a bijection on maps);
* `InfiniteGraph.drop` — the tail restriction: the graph induced on `{k, k+1, …}`,
  reindexed to `ℕ`; continuous and measurable, with the window identity
  `restrictFin_drop`;
* `InfiniteGraph.tailAlgebra` / `InfiniteGraph.vertexTailAlgebra` — the σ-algebra of
  events depending only on the graph on `{k, k+1, …}`, and their infimum over `k`;
* `GraphonSpace.abs_homDensity_drop_window_sub_le` — **the counting comparison**: the
  hom density of a window of the `k`-tail differs from that of the enlarged window of
  the original graph by at most `q·k/(n+1)`;
* `GraphonSpace.tendsto_empiricalGraphon_drop_iff` — **finite-deletion stability**:
  the empirical graphons of the `k`-tail converge to `x` iff those of the original
  graph do;
* `GraphonSpace.limitGraphon_drop` — the universal empirical limit is invariant under
  tail restriction, pointwise everywhere;
* `GraphonSpace.measurable_limitGraphon_vertexTailAlgebra` — **the empirical limit is
  vertex-tail measurable** — the key input for the tail-triviality step of issue #91.
-/

open MeasureTheory InfiniteGraph Filter

open scoped Classical

/-! ### Permutation invariance of the finite graph classes -/

namespace GraphonSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

/-- **Permutation invariance of the graphon class of a finite graph**: relabeling the
vertices by a permutation does not change the graphon class. Hom densities in an
embedded finite graph are map averages (`homDensity_ofSimpleGraphOn`), and
precomposition by a permutation is a bijection on vertex maps. -/
theorem graphClass_comap_perm {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n))
    (H : SimpleGraph (Fin n)) :
    graphClass (α := α) (μ := μ) (H.comap σ) = graphClass H := by
  refine (mk_eq_mk_iff _ _).mpr
    (Graphon.weaklyIsomorphic_of_homDensity_eq _ _ fun k F _ => ?_)
  rw [Graphon.homDensity_ofSimpleGraphOn, Graphon.homDensity_ofSimpleGraphOn]
  congr 1
  refine Fintype.sum_equiv (Equiv.piCongrRight fun _ : Fin k => σ) _ _ fun f => ?_
  rw [SimpleGraph.comap_comap]
  rfl

end GraphonSpace

/-! ### Tail restriction and the vertex-tail σ-algebra -/

namespace InfiniteGraph

/-- **Tail restriction**: the graph induced on the vertices `{k, k+1, …}`, reindexed
to `ℕ`. -/
def drop (k : ℕ) (G : InfiniteGraph) : InfiniteGraph :=
  ((G : SimpleGraph ℕ).comap (· + k) : SimpleGraph ℕ)

@[simp] theorem drop_adj (k : ℕ) (G : InfiniteGraph) (a b : ℕ) :
    (drop k G : SimpleGraph ℕ).Adj a b ↔ (G : SimpleGraph ℕ).Adj (a + k) (b + k) :=
  Iff.rfl

@[simp] theorem drop_zero (G : InfiniteGraph) : drop 0 G = G := by
  show ((G : SimpleGraph ℕ).comap (· + 0) : SimpleGraph ℕ) = (G : SimpleGraph ℕ)
  ext a b
  simp

/-- Tail restrictions compose additively. -/
theorem drop_drop (k l : ℕ) (G : InfiniteGraph) :
    drop k (drop l G) = drop (k + l) G := by
  show (((G : SimpleGraph ℕ).comap (· + l)).comap (· + k) : SimpleGraph ℕ) =
    (G : SimpleGraph ℕ).comap (· + (k + l))
  ext a b
  simp

/-- Edge membership under tail restriction, in `Sym2` form. -/
theorem mem_edgeSet_drop (k : ℕ) (G : InfiniteGraph) (s : Sym2 ℕ) :
    s ∈ (drop k G : SimpleGraph ℕ).edgeSet ↔
      Sym2.map (· + k) s ∈ (G : SimpleGraph ℕ).edgeSet := by
  induction s using Sym2.ind with
  | _ a b => simp [SimpleGraph.mem_edgeSet, drop]

/-- The edge-index action of the tail shift. -/
def dropEdgeIndexMap (k : ℕ) (e : EdgeIndex) : EdgeIndex :=
  ⟨Sym2.map (· + k) (e : Sym2 ℕ), by
    obtain ⟨s, hs⟩ := e
    induction s using Sym2.ind with
    | _ a b =>
      simp only [Sym2.map_mk, Sym2.mk_isDiag_iff] at hs ⊢
      omega⟩

/-- Tail restriction is continuous: each output edge coordinate is an input edge
coordinate. -/
theorem continuous_drop (k : ℕ) : Continuous (drop k) := by
  rw [continuous_induced_rng]
  rw [show (coordEquiv ∘ drop k : InfiniteGraph → EdgeIndex → Bool) =
      fun G e => coordEquiv G (dropEdgeIndexMap k e) from
    funext fun G => funext fun e => by
      simp only [Function.comp_apply, coordEquiv_apply, dropEdgeIndexMap,
        mem_edgeSet_drop]]
  exact continuous_pi fun e =>
    (continuous_apply (dropEdgeIndexMap k e)).comp coordHomeomorph.continuous

theorem measurable_drop (k : ℕ) : Measurable (drop k) :=
  (continuous_drop k).measurable

/-- **The window identity**: the first `m` vertices of the `k`-tail form the graph
induced on the vertices `{k, …, m + k − 1}` of the original graph. -/
theorem restrictFin_drop (m k : ℕ) (G : InfiniteGraph) :
    restrictFin m (drop k G) = (restrictFin (m + k) G).comap (Fin.addNatEmb k) := by
  ext a b
  simp [restrictFin, drop, SimpleGraph.comap_adj]

/-- **The tail σ-algebra at level `k`**: events depending only on the graph induced on
the vertices `{k, k+1, …}` (the tail restriction `drop k` sees exactly the tail-induced
subgraph, reindexed). -/
@[reducible] noncomputable def tailAlgebra (k : ℕ) : MeasurableSpace InfiniteGraph :=
  MeasurableSpace.comap (drop k) inferInstance

/-- Each tail σ-algebra is a sub-σ-algebra of the Borel σ-algebra. -/
theorem tailAlgebra_le (k : ℕ) :
    tailAlgebra k ≤ (inferInstance : MeasurableSpace InfiniteGraph) :=
  measurable_iff_comap_le.mp (measurable_drop k)

/-- **The vertex-tail σ-algebra** `⋂ₖ σ(G|{k, k+1, …})`: events depending only on
arbitrarily late vertex tails. -/
@[reducible] noncomputable def vertexTailAlgebra : MeasurableSpace InfiniteGraph :=
  ⨅ k, tailAlgebra k

theorem vertexTailAlgebra_le_tailAlgebra (k : ℕ) :
    vertexTailAlgebra ≤ tailAlgebra k :=
  iInf_le _ k

theorem vertexTailAlgebra_le :
    vertexTailAlgebra ≤ (inferInstance : MeasurableSpace InfiniteGraph) :=
  (vertexTailAlgebra_le_tailAlgebra 0).trans (tailAlgebra_le 0)

end InfiniteGraph
