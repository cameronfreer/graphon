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
