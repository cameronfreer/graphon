/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.RestrictionIndependence
import Graphon.HomDensityAlgebra
import Mathlib.Probability.Independence.Basic

/-!
# Dissociation implies restriction independence (Diaconis–Janson Theorem 5.5, issue #91)

The reverse arc completing the five-way extremality theorem: a dissociated law is
restriction independent. The finite content is a two-block factorization obtained from
the upper-mass dissociation criterion by a two-variable Möbius inversion; it is then
lifted from finite tail windows to the whole tail σ-algebra.
-/

open MeasureTheory Set

open scoped Classical

namespace Graphon

/-- The two-variable upper transform. -/
noncomputable def upperSum₂ {k m : ℕ}
    (p : SimpleGraph (Fin k) → SimpleGraph (Fin m) → ℝ)
    (F : SimpleGraph (Fin k)) (H : SimpleGraph (Fin m)) : ℝ :=
  upperSum (fun F' => upperSum (fun H' => p F' H') H) F

/-- The two-variable upper transform is injective. -/
theorem upperSum₂_injective {k m : ℕ}
    {p q : SimpleGraph (Fin k) → SimpleGraph (Fin m) → ℝ}
    (h : ∀ F H, upperSum₂ p F H = upperSum₂ q F H) : p = q := by
  have h1 : ∀ H F', upperSum (fun H' => p F' H') H = upperSum (fun H' => q F' H') H := by
    intro H
    have hF : (fun F' => upperSum (fun H' => p F' H') H)
        = (fun F' => upperSum (fun H' => q F' H') H) :=
      upperSum_injective (fun F => h F H)
    exact congrFun hF
  funext F'
  exact upperSum_injective (fun H => h1 H F')

end Graphon

namespace InfiniteGraph

/-- The initial-block embedding `Fin k ↪ Fin (k+m)` (the first `k` vertices), matching
`finSumFinEquiv` on `Sum.inl`. -/
def blockInit (k m : ℕ) : Fin k ↪ Fin (k + m) :=
  Function.Embedding.trans Function.Embedding.inl finSumFinEquiv.toEmbedding

/-- The tail-block embedding `Fin m ↪ Fin (k+m)` (the vertices `k, …, k+m-1`), matching
`finSumFinEquiv` on `Sum.inr`. -/
def blockTail (k m : ℕ) : Fin m ↪ Fin (k + m) :=
  Function.Embedding.trans Function.Embedding.inr finSumFinEquiv.toEmbedding

@[simp] theorem blockInit_apply (k m : ℕ) (a : Fin k) :
    (blockInit k m a : ℕ) = a := by
  rw [blockInit, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  show (finSumFinEquiv (Sum.inl a) : Fin (k + m)).val = a.val
  rw [finSumFinEquiv_apply_left, Fin.val_castAdd]

@[simp] theorem blockTail_apply (k m : ℕ) (b : Fin m) :
    (blockTail k m b : ℕ) = k + b := by
  rw [blockTail, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  show (finSumFinEquiv (Sum.inr b) : Fin (k + m)).val = k + b.val
  rw [finSumFinEquiv_apply_right, Fin.val_natAdd]

/-- The initial restriction is the initial-block comap of the `(k+m)`-restriction. -/
theorem restrictFin_eq_comap_blockInit (k m : ℕ) (G : InfiniteGraph) :
    restrictFin k G = (restrictFin (k + m) G).comap (blockInit k m) := by
  ext a b
  simp only [restrictFin, SimpleGraph.comap_adj]
  rw [blockInit_apply, blockInit_apply]

/-- The tail-window restriction is the tail-block comap of the `(k+m)`-restriction. -/
theorem restrictFin_drop_eq_comap_blockTail (k m : ℕ) (G : InfiniteGraph) :
    restrictFin m (drop k G) = (restrictFin (k + m) G).comap (blockTail k m) := by
  ext a b
  simp only [restrictFin, SimpleGraph.comap_adj, drop_adj]
  rw [blockTail_apply, blockTail_apply]
  constructor
  · intro h; rwa [Nat.add_comm k _, Nat.add_comm k _]
  · intro h; rwa [Nat.add_comm _ k, Nat.add_comm _ k]

/-- **The disjoint-union order characterization**: a graph on `Fin (k+m)` contains the
mapped disjoint union `(F ⊕g H).map finSumFinEquiv` iff its initial block contains `F`
and its tail block contains `H` (cross-block edges unrestricted). -/
theorem sum_map_le_iff {k m : ℕ} (F : SimpleGraph (Fin k)) (H : SimpleGraph (Fin m))
    (K : SimpleGraph (Fin (k + m))) :
    (F ⊕g H).map finSumFinEquiv.toEmbedding ≤ K ↔
      F ≤ K.comap (blockInit k m) ∧ H ≤ K.comap (blockTail k m) := by
  rw [SimpleGraph.map_le_iff_le_comap]
  constructor
  · intro h
    refine ⟨fun {a b} hab => ?_, fun {a b} hab => ?_⟩
    · have h2 := h ((SimpleGraph.sum_adj_inl).mpr hab)
      rw [SimpleGraph.comap_adj] at h2 ⊢
      exact h2
    · have h2 := h ((SimpleGraph.sum_adj_inr).mpr hab)
      rw [SimpleGraph.comap_adj] at h2 ⊢
      exact h2
  · rintro ⟨hF, hH⟩ u v huv
    obtain (a | a) := u <;> obtain (b | b) := v
    · have := hF ((SimpleGraph.sum_adj_inl).mp huv)
      rw [SimpleGraph.comap_adj] at this ⊢
      exact this
    · exact absurd huv (by simp [SimpleGraph.sum])
    · exact absurd huv (by simp [SimpleGraph.sum])
    · have := hH ((SimpleGraph.sum_adj_inr).mp huv)
      rw [SimpleGraph.comap_adj] at this ⊢
      exact this

end InfiniteGraph
