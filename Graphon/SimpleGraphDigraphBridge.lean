/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.InfiniteDigraph
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The simple-graph / finite-digraph bridge (#94, shared infrastructure)

The symmetric loopless embedding of simple graphs into finite digraphs, in its own module so
the foundational relational/directed carrier `Graphon.InfiniteDigraph` (D1) does not depend on
`SimpleGraph`. Used by the graphon-embedding sampler law (D3c) and the directed
`t`/`t_inj`/`t_ind` interlude (#94).

* `SimpleGraph.toFiniteDigraph` — the embedding, with its `@[simp]` coordinate lemma;
* `SimpleGraph.toFiniteDigraph_injective` — injectivity;
* `SimpleGraph.exists_toFiniteDigraph_eq_iff` — range classification: the embedded digraphs
  are exactly the loopless symmetric ones.
-/

open RelSignature

namespace SimpleGraph

open scoped Classical in
/-- The symmetric loopless embedding of a simple graph as a finite digraph. -/
noncomputable def toFiniteDigraph {k : ℕ} (G : SimpleGraph (Fin k)) : FiniteDigraph k :=
  fun c => decide (G.Adj (c.2 0) (c.2 1))

open scoped Classical in
/-- The ordered-pair coordinates of the embedded digraph read the (classically decided)
adjacency of the simple graph. -/
@[simp] theorem toFiniteDigraph_coord {k : ℕ} (G : SimpleGraph (Fin k)) (a b : Fin k) :
    G.toFiniteDigraph (digraphCoord a b) = decide (G.Adj a b) := rfl

/-- The symmetric loopless embedding is injective. -/
theorem toFiniteDigraph_injective {k : ℕ} :
    Function.Injective (toFiniteDigraph (k := k)) := by
  intro G G' h
  ext a b
  have hc := congrFun h (digraphCoord a b)
  rw [toFiniteDigraph_coord, toFiniteDigraph_coord] at hc
  exact decide_eq_decide.mp hc

/-- **Classification of the range of the embedding**: a finite digraph is an embedded simple
graph iff its coordinates are loopless and symmetric. -/
theorem exists_toFiniteDigraph_eq_iff {k : ℕ} (D : FiniteDigraph k) :
    (∃ G : SimpleGraph (Fin k), G.toFiniteDigraph = D) ↔
      ((∀ i, D (digraphCoord i i) = false) ∧
        ∀ i j : Fin k, D (digraphCoord i j) = D (digraphCoord j i)) := by
  classical
  constructor
  · rintro ⟨G, rfl⟩
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · rw [toFiniteDigraph_coord]
      exact decide_eq_false G.irrefl
    · rw [toFiniteDigraph_coord, toFiniteDigraph_coord]
      exact decide_eq_decide.mpr (G.adj_comm i j)
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun i j => D (digraphCoord i j) = true ∧ i ≠ j,
      ⟨fun i j hij => ⟨(h2 j i).trans hij.1, hij.2.symm⟩⟩,
      ⟨fun i hii => hii.2 rfl⟩⟩, ?_⟩
    refine digraphStructure_ext_iff.mpr fun a b => ?_
    rw [toFiniteDigraph_coord]
    by_cases hab : a = b
    · subst hab
      rw [h1 a, decide_eq_false_iff_not]
      exact fun hcon => hcon.2 rfl
    · rcases hDc : D (digraphCoord a b) with _ | _
      · rw [decide_eq_false_iff_not]
        exact fun hcon => Bool.false_ne_true (hDc ▸ hcon.1)
      · exact @decide_eq_true _ (Classical.propDecidable _) ⟨hDc, hab⟩

end SimpleGraph
