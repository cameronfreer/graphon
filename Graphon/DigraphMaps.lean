/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Combinatorics.Digraph.Basic

/-!
# Comap of a directed graph

The minimal pullback API for Mathlib's `Digraph`, mirroring `SimpleGraph.comap`. A candidate
for upstreaming to Mathlib (tracked on issue #24). Only `comap` is provided — `map` is
unnecessary for restriction consistency and has less canonical behaviour, so it is omitted.
-/

variable {U V W : Type*}

/-- **The comap** of a digraph along a function: `x` and `y` are adjacent in `G.comap f` iff
`f x` and `f y` are adjacent in `G`. -/
protected def Digraph.comap (f : V → W) (G : Digraph W) : Digraph V :=
  ⟨fun x y => G.Adj (f x) (f y)⟩

@[simp] theorem Digraph.comap_adj (f : V → W) (G : Digraph W) (x y : V) :
    (G.comap f).Adj x y ↔ G.Adj (f x) (f y) := Iff.rfl

@[simp] theorem Digraph.comap_id (G : Digraph V) : G.comap id = G := rfl

theorem Digraph.comap_comp (f : U → V) (g : V → W) (G : Digraph W) :
    G.comap (g ∘ f) = (G.comap g).comap f := rfl

instance Digraph.decidableRelComap (f : V → W) (G : Digraph W) [DecidableRel G.Adj] :
    DecidableRel (G.comap f).Adj :=
  fun x y => decidable_of_iff _ (Digraph.comap_adj f G x y).symm
