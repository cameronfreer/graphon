/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelationalTopology
import Mathlib.Combinatorics.Digraph.Basic

/-!
# The infinite digraph space as an R1 instance (directed umbrella #84, D1 / issue #85)

Directed graphs are the **one-sort, single binary relation, ordered-arguments,
diagonal-permitted** case of the generic relational carrier (R1). Rather than re-derive the
topology / measurable structure, this file instantiates it: `InfiniteDigraph` is defined as
the relational structure over `digraphSig`, so it inherits — with no new proofs — the
Boolean-product topology, the compact / Polish / standard-Borel instances, the measurable
finite restrictions, the cylinder π-system, and the finite-restriction measure
extensionality of R1b. It then bridges to Mathlib's `Digraph ℕ` by an explicit measurable
equivalence (`Prop ≃ Bool` classically), per #109.

* `digraphSig` — the one-sort binary signature (arity `2`, `NoNullary`);
* `InfiniteDigraph` — `RelStructure digraphSig (Vinfinite digraphSig)`, with the inherited
  `CompactSpace` / `StandardBorelSpace` and `InfiniteDigraph.Adj` reading off adjacency;
* `InfiniteDigraph.coordPairEquiv` — coordinates are ordered pairs `ℕ × ℕ` (full square,
  including the diagonal);
* `InfiniteDigraph.digraphEquiv` — the measurable equivalence with Mathlib's `Digraph ℕ`;
* `InfiniteDigraph.restrictFin` and `InfiniteDigraph.ext_of_map_restrictFin` — the R1b finite
  restriction and measure extensionality, specialized.

The projective extension / exchangeable-law theory is **not** here — that is D2 (#86), a thin
specialization of R2.
-/

open RelSignature MeasureTheory

/-- The **one-sort, single binary relation** signature: `arity 2`, ordered arguments, the
diagonal permitted (loops allowed). Reducible so the coordinate carrier reduces to `ℕ × ℕ`
and the R1b countability instances fire. -/
abbrev digraphSig : RelSignature where
  Srt := Unit
  Rel := Unit
  arity := fun _ => 2
  argSort := fun _ _ => ()

theorem digraphSig_noNullary : NoNullary digraphSig := fun _ => Nat.succ_pos 1

/-- **The infinite digraph space**: the relational structure over `digraphSig` with vertex
set `ℕ`. Inherits the entire R1 topological / measurable structure. -/
abbrev InfiniteDigraph : Type := RelStructure digraphSig (Vinfinite digraphSig)

namespace InfiniteDigraph

-- The R1b instances are inherited with no new proofs.
example : CompactSpace InfiniteDigraph := inferInstance
example : StandardBorelSpace InfiniteDigraph := inferInstance

/-- The **coordinate at an ordered vertex pair** `(a, b)`. -/
abbrev coord (a b : ℕ) : RelCoord digraphSig (Vinfinite digraphSig) := ⟨(), ![a, b]⟩

/-- **Adjacency** in the infinite digraph: whether the ordered pair `(a, b)` stands in the
relation. -/
def Adj (G : InfiniteDigraph) (a b : ℕ) : Bool := G (coord a b)

@[simp] theorem Adj_def (G : InfiniteDigraph) (a b : ℕ) : G.Adj a b = G (coord a b) := rfl

/-- **Coordinates are ordered vertex pairs** (full square, diagonal included). -/
def coordPairEquiv : RelCoord digraphSig (Vinfinite digraphSig) ≃ (ℕ × ℕ) where
  toFun c := (c.2 0, c.2 1)
  invFun p := coord p.1 p.2
  left_inv c := by
    obtain ⟨_, w⟩ := c
    refine Sigma.ext rfl (heq_of_eq ?_)
    funext i; fin_cases i <;> rfl
  right_inv _ := rfl

/-! ### Bridge to Mathlib's `Digraph ℕ` -/

open Classical in
/-- **The measurable equivalence with Mathlib's `Digraph ℕ`** (`Prop ≃ Bool` classically).
An infinite digraph is exactly an arbitrary `Bool` assignment to ordered vertex pairs, which
is exactly a `Digraph`'s adjacency relation. -/
noncomputable def digraphEquiv : InfiniteDigraph ≃ Digraph ℕ where
  toFun G := ⟨fun a b => G.Adj a b⟩
  invFun D := fun c => decide (D.Adj (c.2 0) (c.2 1))
  left_inv G := by
    funext c
    have hc : coord (c.2 0) (c.2 1) = c := coordPairEquiv.left_inv c
    simp [Adj_def, hc]
  right_inv D := by
    ext a b
    simp [Adj_def]

@[simp] theorem digraphEquiv_adj (G : InfiniteDigraph) (a b : ℕ) :
    (digraphEquiv G).Adj a b ↔ G.Adj a b := Iff.rfl

/-! ### Inherited finite restriction and measure extensionality -/

/-- Finite restriction of an infinite digraph to the first `n` vertices (the R1b
`restrictFin`, specialized). -/
abbrev restrictFin (n : ℕ) : InfiniteDigraph → RelStructure digraphSig (Vfinite fun _ => n) :=
  RelStructure.restrictFin (S := digraphSig) fun _ => n

theorem measurable_restrictFin (n : ℕ) : Measurable (restrictFin n) :=
  RelSignature.measurable_restrictFin (S := digraphSig) _

/-- **Finite-restriction measure extensionality for infinite digraphs** (R1b, specialized):
two finite measures agree once their finite-restriction pushforwards agree. -/
theorem ext_of_map_restrictFin {μ ν : Measure InfiniteDigraph} [IsFiniteMeasure μ]
    (h : ∀ n : Unit → ℕ, μ.map (RelStructure.restrictFin (S := digraphSig) n) =
      ν.map (RelStructure.restrictFin (S := digraphSig) n)) : μ = ν :=
  RelStructure.ext_of_map_restrictFin h

end InfiniteDigraph
