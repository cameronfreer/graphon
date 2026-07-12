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
compact / Polish / standard-Borel instances, the measurable finite restrictions, the
cylinder π-system, and the finite-restriction measure extensionality of R1b. **All topology
lives on `InfiniteDigraph`**; the bridge to Mathlib's `Digraph` is a plain **carrier
equivalence** (`Prop ≃ Bool` classically), generic over the vertex type, so it yields both
the infinite and the finite bridges (the latter for D2).

* `digraphSig` — the one-sort binary signature (arity `2`, `NoNullary`);
* `digraphStructureEquiv V` — the carrier equivalence
  `RelStructure digraphSig (fun _ => V) ≃ Digraph V`, generic over `V`;
* `InfiniteDigraph` / `FiniteDigraph n` and the derived `digraphEquiv` / `finiteDigraphEquiv`;
* `InfiniteDigraph.Adj` (Prop, matching Mathlib graph APIs) and `InfiniteDigraph.adjBit`
  (Bool), reading adjacency off the ordered-pair coordinate;
* `InfiniteDigraph.restrictFin` and `InfiniteDigraph.ext_of_map_restrictFin` — the R1b finite
  restriction and measure extensionality, specialized (public statement over `n : ℕ`).

The projective extension / exchangeable-law theory is **not** here — that is D2 (#86) and R2.
-/

open RelSignature MeasureTheory

/-- The **one-sort, single binary relation** signature: `arity 2`, ordered arguments, the
diagonal permitted (loops allowed). -/
abbrev digraphSig : RelSignature where
  Srt := Unit
  Rel := Unit
  arity := fun _ => 2
  argSort := fun _ _ => ()

theorem digraphSig_noNullary : NoNullary digraphSig := fun _ => Nat.succ_pos 1

/-- The **coordinate at an ordered vertex pair** `(a, b)`, over any vertex type. -/
abbrev digraphCoord {V : Type*} (a b : V) : RelCoord digraphSig (fun _ => V) := ⟨(), ![a, b]⟩

/-- **Coordinates are ordered vertex pairs** (full square, diagonal included). -/
def digraphCoordEquiv (V : Type*) : RelCoord digraphSig (fun _ => V) ≃ (V × V) where
  toFun c := (c.2 0, c.2 1)
  invFun p := digraphCoord p.1 p.2
  left_inv c := by
    obtain ⟨_, w⟩ := c
    refine Sigma.ext rfl (heq_of_eq ?_)
    funext i; fin_cases i <;> rfl
  right_inv _ := rfl

open Classical in
/-- **The carrier equivalence with Mathlib's `Digraph V`** (`Prop ≃ Bool` classically), a
plain type equivalence — the topology / measurable structure lives on the relational
structure, not on `Digraph V`. A digraph is exactly an arbitrary `Bool` assignment to ordered
vertex pairs. -/
noncomputable def digraphStructureEquiv (V : Type*) :
    RelStructure digraphSig (fun _ => V) ≃ Digraph V where
  toFun G := ⟨fun a b => G (digraphCoord a b) = true⟩
  invFun D := fun c => decide (D.Adj (c.2 0) (c.2 1))
  left_inv G := by
    funext c
    obtain ⟨_, w⟩ := c
    have hw : (![w 0, w 1] : Fin 2 → V) = w := by funext i; fin_cases i <;> rfl
    simp [digraphCoord, hw]
  right_inv D := by
    ext a b
    simp

@[simp] theorem digraphStructureEquiv_adj {V : Type*}
    (G : RelStructure digraphSig (fun _ => V)) (a b : V) :
    (digraphStructureEquiv V G).Adj a b ↔ G (digraphCoord a b) = true := Iff.rfl

/-! ### The infinite and finite digraph carriers -/

/-- **The infinite digraph space**: the relational structure over `digraphSig` with vertex
set `ℕ`. Inherits the entire R1 topological / measurable structure. -/
abbrev InfiniteDigraph : Type := RelStructure digraphSig (Vinfinite digraphSig)

/-- **The finite digraph space** on `Fin n`. -/
abbrev FiniteDigraph (n : ℕ) : Type := RelStructure digraphSig (Vfinite fun _ => n)

-- The R1b instances are inherited with no new proofs.
example : CompactSpace InfiniteDigraph := inferInstance
example : StandardBorelSpace InfiniteDigraph := inferInstance

/-- The infinite carrier equivalence with Mathlib's `Digraph ℕ`. -/
noncomputable def digraphEquiv : InfiniteDigraph ≃ Digraph ℕ := digraphStructureEquiv ℕ

/-- The finite carrier equivalence with Mathlib's `Digraph (Fin n)` — the bridge D2 uses. -/
noncomputable def finiteDigraphEquiv (n : ℕ) : FiniteDigraph n ≃ Digraph (Fin n) :=
  digraphStructureEquiv (Fin n)

namespace InfiniteDigraph

/-- **Boolean adjacency**: whether the ordered pair `(a, b)` stands in the relation. -/
def adjBit (G : InfiniteDigraph) (a b : ℕ) : Bool := G (digraphCoord a b)

/-- **Adjacency** (Prop-valued, matching Mathlib's graph APIs). -/
def Adj (G : InfiniteDigraph) (a b : ℕ) : Prop := G.adjBit a b

@[simp] theorem adj_iff_adjBit (G : InfiniteDigraph) (a b : ℕ) :
    G.Adj a b ↔ G.adjBit a b = true := Iff.rfl

@[simp] theorem digraphEquiv_adj (G : InfiniteDigraph) (a b : ℕ) :
    (digraphEquiv G).Adj a b ↔ G.Adj a b := Iff.rfl

/-! ### Inherited finite restriction and measure extensionality -/

/-- Finite restriction of an infinite digraph to the first `n` vertices (the R1b
`restrictFin`, specialized). -/
abbrev restrictFin (n : ℕ) : InfiniteDigraph → FiniteDigraph n :=
  RelStructure.restrictFin (S := digraphSig) fun _ => n

theorem measurable_restrictFin (n : ℕ) : Measurable (restrictFin n) :=
  RelSignature.measurable_restrictFin (S := digraphSig) _

/-- **Finite-restriction measure extensionality for infinite digraphs** (R1b, specialized):
two finite measures agree once their finite-restriction pushforwards agree, quantified over
`n : ℕ` (the uniform size vector). -/
theorem ext_of_map_restrictFin {μ ν : Measure InfiniteDigraph} [IsFiniteMeasure μ]
    (h : ∀ n : ℕ, μ.map (restrictFin n) = ν.map (restrictFin n)) : μ = ν := by
  refine RelStructure.ext_of_map_restrictFin (fun m => ?_)
  have hm : m = fun _ => m () := funext fun u => by cases u; rfl
  rw [hm]; exact h (m ())

end InfiniteDigraph
