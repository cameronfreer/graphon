/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.LimitGraphon
import Graphon.VertexTail

/-!
# The finite-permutation action and its invariant σ-algebra (issue #59, part 1)

Infrastructure for the ergodic-decomposition form of extremality: the empirical limit
`limitGraphon` is invariant under every finitely supported relabeling of `ℕ`, hence is
measurable with respect to the permutation-invariant σ-algebra.
-/

open MeasureTheory Filter Topology

namespace InfiniteGraph

/-- A permutation of `ℕ` is finitely supported if it fixes all sufficiently large
naturals. -/
def FinSupp (σ : Equiv.Perm ℕ) : Prop := ∃ N, ∀ x, N ≤ x → σ x = x

/-- A finitely supported permutation maps `[0, N)` into itself. -/
private theorem lt_of_finSupp {σ : Equiv.Perm ℕ} {N : ℕ} (hN : ∀ x, N ≤ x → σ x = x)
    {x : ℕ} (hx : x < N) : σ x < N := by
  by_contra h
  push Not at h
  have := σ.injective (hN (σ x) h)
  omega

/-- A finitely supported permutation, restricted to a large enough initial segment, as a
permutation of `Fin (n+1)`. -/
noncomputable def relabelFin (σ : Equiv.Perm ℕ) (N n : ℕ) (hN : ∀ x, N ≤ x → σ x = x)
    (hn : N ≤ n + 1) : Equiv.Perm (Fin (n + 1)) where
  toFun a := ⟨σ a, by
    rcases lt_or_ge (a : ℕ) N with h | h
    · exact lt_of_lt_of_le (lt_of_finSupp hN h) hn
    · rw [hN a h]; exact a.2⟩
  invFun a := ⟨σ.symm a, by
    have hNsymm : ∀ x, N ≤ x → σ.symm x = x := fun x hx =>
      calc σ.symm x = σ.symm (σ x) := by rw [hN x hx]
        _ = x := σ.symm_apply_apply x
    rcases lt_or_ge (a : ℕ) N with h | h
    · exact lt_of_lt_of_le (lt_of_finSupp hNsymm h) hn
    · rw [hNsymm a h]; exact a.2⟩
  left_inv a := by ext; simp
  right_inv a := by ext; simp

@[simp] theorem relabelFin_apply (σ : Equiv.Perm ℕ) (N n : ℕ) (hN : ∀ x, N ≤ x → σ x = x)
    (hn : N ≤ n + 1) (a : Fin (n + 1)) : (relabelFin σ N n hN hn a : ℕ) = σ a := rfl

/-- The restriction of a relabeled infinite graph is the relabeled restriction (for a
window past the support). -/
theorem restrictFin_relabel_eq_comap (σ : Equiv.Perm ℕ) {N : ℕ}
    (hN : ∀ x, N ≤ x → σ x = x) {n : ℕ} (hn : N ≤ n + 1) (G : InfiniteGraph) :
    restrictFin (n + 1) (relabel σ G) =
      (restrictFin (n + 1) G).comap (relabelFin σ N n hN hn) := by
  ext a b
  simp only [restrictFin, SimpleGraph.comap_adj, relabel_adj, relabelFin_apply]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ]

/-- **The empirical graphon is invariant under a finite relabeling**, past its support. -/
theorem empiricalGraphon_relabel (σ : Equiv.Perm ℕ) {N : ℕ}
    (hN : ∀ x, N ≤ x → σ x = x) {n : ℕ} (hn : N ≤ n + 1) (G : InfiniteGraph) :
    GraphonSpace.empiricalGraphon (α := α) (μ := μ) n (relabel σ G) =
      GraphonSpace.empiricalGraphon n G := by
  rw [GraphonSpace.empiricalGraphon, GraphonSpace.empiricalGraphon,
    restrictFin_relabel_eq_comap σ hN hn, GraphonSpace.graphClass_comap_perm]

/-- **The permutation-invariant σ-algebra**: Borel events fixed by every finitely
supported relabeling. -/
def invariantAlgebra : MeasurableSpace InfiniteGraph where
  MeasurableSet' A := MeasurableSet A ∧ ∀ σ : Equiv.Perm ℕ, FinSupp σ → relabel σ ⁻¹' A = A
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ => by simp⟩
  measurableSet_compl A hA :=
    ⟨hA.1.compl, fun σ hσ => by rw [Set.preimage_compl, hA.2 σ hσ]⟩
  measurableSet_iUnion f hf :=
    ⟨MeasurableSet.iUnion fun i => (hf i).1, fun σ hσ => by
      rw [Set.preimage_iUnion]; exact Set.iUnion_congr fun i => (hf i).2 σ hσ⟩

theorem invariantAlgebra_le :
    invariantAlgebra ≤ (inferInstance : MeasurableSpace InfiniteGraph) := fun _ hA => hA.1

end InfiniteGraph

namespace GraphonSpace

/-- Convergence of the empirical graphons is invariant under a finite relabeling. -/
theorem tendsto_empiricalGraphon_relabel_iff {σ : Equiv.Perm ℕ}
    (hfs : InfiniteGraph.FinSupp σ) (G : InfiniteGraph) (x : StandardGraphonSpace) :
    Tendsto (fun n => empiricalGraphon n (InfiniteGraph.relabel σ G)) atTop (nhds x) ↔
      Tendsto (fun n => empiricalGraphon n G) atTop (nhds x) := by
  obtain ⟨N, hN⟩ := hfs
  refine tendsto_congr' ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  exact InfiniteGraph.empiricalGraphon_relabel σ hN (le_trans hn (Nat.le_succ n)) G

theorem mem_empiricalConvergenceSet_relabel_iff {σ : Equiv.Perm ℕ}
    (hfs : InfiniteGraph.FinSupp σ) (G : InfiniteGraph) :
    InfiniteGraph.relabel σ G ∈ empiricalConvergenceSet ↔ G ∈ empiricalConvergenceSet := by
  simp only [empiricalConvergenceSet, Set.mem_setOf_eq]
  exact exists_congr fun x => tendsto_empiricalGraphon_relabel_iff hfs G x

/-- **The empirical limit is invariant under every finite relabeling** — pointwise. -/
theorem limitGraphon_relabel {σ : Equiv.Perm ℕ} (hfs : InfiniteGraph.FinSupp σ)
    (G : InfiniteGraph) :
    limitGraphon (InfiniteGraph.relabel σ G) = limitGraphon G := by
  by_cases hG : G ∈ empiricalConvergenceSet
  · obtain ⟨x, hx⟩ := hG
    rw [limitGraphon_eq_of_tendsto ((tendsto_empiricalGraphon_relabel_iff hfs G x).mpr hx),
      limitGraphon_eq_of_tendsto hx]
  · have hG' : InfiniteGraph.relabel σ G ∉ empiricalConvergenceSet := fun h =>
      hG ((mem_empiricalConvergenceSet_relabel_iff hfs G).mp h)
    simp only [limitGraphon, dif_neg hG, dif_neg hG']

/-- **The empirical limit is invariant-measurable**: its preimages are Borel events
fixed by every finite relabeling (`limitGraphon_relabel`). -/
theorem measurable_limitGraphon_invariantAlgebra :
    @Measurable InfiniteGraph StandardGraphonSpace InfiniteGraph.invariantAlgebra _
      limitGraphon := fun S hS =>
  ⟨measurable_limitGraphon hS, fun σ hσ => by
    ext G
    simp only [Set.mem_preimage]
    rw [limitGraphon_relabel hσ]⟩

end GraphonSpace

namespace Graphon.InfiniteExchangeableGraphLaw

/-- **Ergodicity**: every permutation-invariant Borel event has `M.law`-measure `0` or
`1`. -/
def IsErgodic (M : Graphon.InfiniteExchangeableGraphLaw) : Prop :=
  ∀ s, MeasurableSet[InfiniteGraph.invariantAlgebra] s →
    (M.law : Measure InfiniteGraph) s = 0 ∨ (M.law : Measure InfiniteGraph) s = 1

end Graphon.InfiniteExchangeableGraphLaw
