/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.SubgraphDensities
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Bridge from finite graph densities to Mathlib's copy count

The finite-density development originally counted injective homomorphisms directly as filtered
vertex maps.  Mathlib's public numerator is `SimpleGraph.labelledCopyCount`, the cardinality of
the bundled `SimpleGraph.Copy` type.  This file proves the two counts identical and records
Mathlib's host-first argument order.
-/

open scoped Classical

namespace SimpleGraph

variable {V W : Type*} [Fintype V] [Fintype W]

/-- Mathlib's labeled-copy count is the filtered count of injective vertex maps that preserve
adjacency.  The theorem is generic so that no concrete type's decidability instance competes
with the classical instance hidden inside `labelledCopyCount`. -/
theorem card_filter_injective_le_comap_eq_labelledCopyCount
    (F : SimpleGraph W) (H : SimpleGraph V) :
    (Finset.univ.filter fun f : W → V => Function.Injective f ∧ F ≤ H.comap f).card =
      H.labelledCopyCount F := by
  classical
  rw [← Fintype.card_subtype, labelledCopyCount]
  exact Fintype.card_congr
    { toFun := fun f => ⟨⟨f.1, fun h => f.2.2 h⟩, f.2.1⟩
      invFun := fun f => ⟨f, f.injective, f.toHom.le_comap⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => SimpleGraph.Copy.ext fun _ => rfl }

variable {k n : ℕ}

/-- The project's injective-homomorphism numerator is Mathlib's labeled-copy count, with
Mathlib's host-first argument order. -/
theorem injHomCount_eq_labelledCopyCount (F : SimpleGraph (Fin k)) (H : SimpleGraph (Fin n)) :
    injHomCount F H = H.labelledCopyCount F := by
  unfold injHomCount
  convert card_filter_injective_le_comap_eq_labelledCopyCount F H using 1
  apply Finset.card_bij (fun f _ => f)
  · intro f hf
    simpa using hf
  · intro f₁ _ f₂ _ h
    exact h
  · intro f hf
    exact ⟨f, by simpa using hf, rfl⟩

end SimpleGraph
