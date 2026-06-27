/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.CycleKrylov
import Graphon.CaiGovorov

/-!
# Cai–Govorov simple test graphs and their closed forms (#70)

The Cai–Govorov orbit-separation route for `#70` uses two families of simple test
graphs whose `simpleEvalAt` values are explicit weighted moment sums. This file
defines them and proves the closed forms, as inputs to the Vandermonde argument
(`Graphon.CaiGovorov`).

* `starTestGraph S` (Gχ): one unlabeled vertex joined to the labels in `S ⊆ Fin K`.
  `simpleEvalAt B W (starTestGraph S) ξ = ∑ₜ W t · ∏_{i∈S} B (ξ i) t`.

(Staging file: imports `CycleKrylov` for `out_pair_eq'`/`simpleEvalAt`; the proofs
will be relocated upstream into `Lovasz` when wiring the `tupleEquivSimple_implies_orbit`
wrapper, since that theorem and its consumers precede `CycleKrylov`.)
-/

open Finset

namespace Graphon.Lovasz

variable {K : ℕ}

/-- Embed label `i : Fin K` as the vertex of value `i` in `Fin (1 + K)`. -/
def labVertex (i : Fin K) : Fin (1 + K) := ⟨(i : ℕ), by have := i.isLt; omega⟩

/-- The single unlabeled vertex (value `K`) in `Fin (1 + K)`. -/
def unlVertex : Fin (1 + K) := ⟨K, by omega⟩

/-- **Cai–Govorov test graph Gχ**: the unlabeled vertex is joined to exactly the
labels in `S ⊆ Fin K`. -/
def starTestGraph (S : Finset (Fin K)) : SimpleGraph (Fin (1 + K)) :=
  SimpleGraph.fromEdgeSet
    ((S.image (fun i => s(labVertex i, unlVertex))) : Set (Sym2 (Fin (1 + K))))

noncomputable instance (S : Finset (Fin K)) : DecidableRel (starTestGraph S).Adj :=
  Classical.decRel _

theorem labVertex_ne_unlVertex (i : Fin K) : labVertex i ≠ unlVertex := by
  intro h
  have := congrArg Fin.val h
  simp only [labVertex, unlVertex] at this
  have := i.isLt; omega

theorem starTestGraph_edge_injOn (S : Finset (Fin K)) :
    ∀ i ∈ S, ∀ i' ∈ S, s(labVertex i, unlVertex) = s(labVertex i', unlVertex) → i = i' := by
  intro i _ i' _ heq
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
  · apply Fin.ext
    have := congrArg Fin.val h1
    simpa [labVertex] using this
  · exact absurd h1 (labVertex_ne_unlVertex i)

theorem starTestGraph_edgeFinset (S : Finset (Fin K)) :
    (starTestGraph S).edgeFinset = S.image (fun i => s(labVertex i, unlVertex)) := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, starTestGraph, SimpleGraph.edgeSet_fromEdgeSet,
    Set.mem_sdiff, Finset.coe_image, Set.mem_image, Finset.mem_coe, Sym2.mem_diagSet,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, _⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨⟨i, hi, rfl⟩, ?_⟩
    rw [Sym2.mk_isDiag_iff]
    exact labVertex_ne_unlVertex i

/-- The `simpleEvalAt` label map sends `labVertex i` to `ξ i` (stated in the
beta-reduced `dite` form produced by `out_pair_eq'`). -/
theorem tau_apply_labVertex {T : ℕ} (ξ : Fin K → Fin T) (σ : Fin 1 → Fin T) (i : Fin K) :
    (if h : ((labVertex i : Fin (1 + K)) : ℕ) < K then ξ ⟨↑(labVertex i), h⟩
        else σ ⟨↑(labVertex i) - K, by have := (labVertex i).isLt; omega⟩) = ξ i := by
  rw [dif_pos (show ((labVertex i : Fin (1 + K)) : ℕ) < K from i.isLt)]
  congr 1

/-- The `simpleEvalAt` label map sends `unlVertex` to `σ 0` (beta-reduced `dite` form). -/
theorem tau_apply_unlVertex {T : ℕ} (ξ : Fin K → Fin T) (σ : Fin 1 → Fin T) :
    (if h : ((unlVertex : Fin (1 + K)) : ℕ) < K then ξ ⟨↑(unlVertex : Fin (1 + K)), h⟩
        else σ ⟨↑(unlVertex : Fin (1 + K)) - K, by have := (unlVertex : Fin (1 + K)).isLt; omega⟩)
        = σ 0 := by
  rw [dif_neg (show ¬ ((unlVertex : Fin (1 + K)) : ℕ) < K from by simp [unlVertex])]
  congr 1
  apply Fin.ext
  simp [unlVertex]

/-- **Closed form for Gχ**: `simpleEvalAt B W (starTestGraph S) ξ = ∑ₜ W t · ∏_{i∈S} B (ξ i) t`. -/
theorem simpleEvalAt_starTestGraph {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (S : Finset (Fin K)) (ξ : Fin K → Fin T) :
    simpleEvalAt B W (starTestGraph S) ξ = ∑ t, W t * ∏ i ∈ S, B (ξ i) t := by
  rw [show (∑ t, W t * ∏ i ∈ S, B (ξ i) t)
      = ∑ σ : Fin 1 → Fin T, W (σ 0) * ∏ i ∈ S, B (ξ i) (σ 0) from
    (Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin T))
      (fun t => W t * ∏ i ∈ S, B (ξ i) t)).symm]
  unfold simpleEvalAt
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [starTestGraph_edgeFinset]
  show (∏ v : Fin 1, W (σ v)) *
      ∏ e ∈ S.image (fun i => s(labVertex i, unlVertex)),
        B ((fun v : Fin (1 + K) => if h : (v : ℕ) < K then ξ ⟨v, h⟩
              else σ ⟨v - K, by have := v.isLt; omega⟩) (Quot.out e).1)
          ((fun v : Fin (1 + K) => if h : (v : ℕ) < K then ξ ⟨v, h⟩
              else σ ⟨v - K, by have := v.isLt; omega⟩) (Quot.out e).2)
      = W (σ 0) * ∏ i ∈ S, B (ξ i) (σ 0)
  rw [Fin.prod_univ_one, Finset.prod_image (starTestGraph_edge_injOn S)]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [out_pair_eq' B hB (fun v : Fin (1 + K) => if h : (v : ℕ) < K then ξ ⟨v, h⟩
        else σ ⟨v - K, by have := v.isLt; omega⟩) (labVertex i) unlVertex,
    tau_apply_labVertex ξ σ i, tau_apply_unlVertex ξ σ]

end Graphon.Lovasz
