/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.InfiniteDigraph
import Graphon.RelEqualityPattern

/-!
# Support geometry of digraph coordinates (shared regression infrastructure)

The support of a digraph coordinate, in its own module so that the foundational relational/directed
carrier `Graphon.InfiniteDigraph` (D1) does not depend on the equality-pattern layer
`Graphon.RelEqualityPattern`, where `RelCoord.support` is defined. Every D1 consumer would
otherwise inherit that dependency for the sake of two lemmas neither it nor they use — the same
reason `Graphon.SimpleGraphDigraphBridge` keeps `SimpleGraph` out of D1.

Both regressions for the R4 successor contract (#196) were proving this geometry independently;
it is stated here once, over an arbitrary vertex type.

The pair is stated with `[DecidableEq V]` and proved by **membership** rather than by unfolding an
image. That is not a stylistic choice: `RelCoord.support` is built with the classical instance, and
over a concrete carrier the natural `DecidableEq` is not definitionally equal to it, so an
image-shaped statement would be unusable at exactly the sites that need it.
-/

open RelSignature

open scoped Classical in
/-- **The support of a digraph coordinate** is the pair of its endpoints. Proved by membership, so
that the `DecidableEq` instance forming the pair is the caller's rather than the classical one used
to build `RelCoord.support`. -/
theorem support_digraphCoord {V : Type*} [DecidableEq V] (a b : V) :
    (digraphCoord a b : RelCoord digraphSig (fun _ => V)).support =
      {(⟨(), a⟩ : Σ _ : Unit, V), ⟨(), b⟩} := by
  refine Finset.ext fun w => ?_
  rw [RelCoord.mem_support_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- **An off-diagonal digraph coordinate has a two-point support.** -/
theorem card_support_digraphCoord {V : Type*} [DecidableEq V] {a b : V} (hab : a ≠ b) :
    (digraphCoord a b : RelCoord digraphSig (fun _ => V)).support.card = 2 := by
  rw [support_digraphCoord]
  exact Finset.card_pair fun h => hab (congrArg Sigma.snd h)
