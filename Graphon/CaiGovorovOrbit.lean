/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.CycleKrylov
import Graphon.CaiGovorov
import Mathlib.Combinatorics.Pigeonhole

/-!
# Cai–Govorov simple test graphs and their closed forms (#70)

The Cai–Govorov orbit-separation route for `#70` uses two families of simple test
graphs whose `simpleEvalAt` values are explicit weighted moment sums. This file
defines them and proves the closed forms, as inputs to the Vandermonde argument
(`Graphon.CaiGovorov`).

* `starTestGraph S` (Gχ): one unlabeled vertex joined to the labels in `S ⊆ Fin K`.
  `simpleEvalAt B W (starTestGraph S) ξ = ∑ₜ W t · ∏_{i∈S} B (ξ i) t`.
* `edgeTestGraph Sₗ Sτ` (Gλτ): two adjacent unlabeled vertices, the first joined to
  the labels in `Sₗ`, the second to `Sτ`.
  `simpleEvalAt B W (edgeTestGraph Sₗ Sτ) ξ =`
  `∑ₜ ∑ₜ' W t · W t' · B t t' · (∏_{i∈Sₗ} B (ξ i) t) · (∏_{i∈Sτ} B (ξ i) t')`.

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

/-! ## Cai–Govorov edge-test graph Gλτ (two unlabeled vertices) -/

/-- Embed label `i : Fin K` as the vertex of value `i` in `Fin (2 + K)`. -/
def labVertex2 (i : Fin K) : Fin (2 + K) := ⟨(i : ℕ), by have := i.isLt; omega⟩

/-- The first unlabeled vertex (value `K`, mapped to `σ 0`) in `Fin (2 + K)`. -/
def unlVertex0 : Fin (2 + K) := ⟨K, by omega⟩

/-- The second unlabeled vertex (value `K + 1`, mapped to `σ 1`) in `Fin (2 + K)`. -/
def unlVertex1 : Fin (2 + K) := ⟨K + 1, by omega⟩

/-- **Cai–Govorov edge-test graph Gλτ**: the two unlabeled vertices are joined to each
other, vertex `0` is joined to the labels in `Sₗ`, and vertex `1` to the labels in `Sτ`. -/
def edgeTestGraph (Sₗ Sτ : Finset (Fin K)) : SimpleGraph (Fin (2 + K)) :=
  SimpleGraph.fromEdgeSet
    ((insert s(unlVertex0, unlVertex1)
      (Sₗ.image (fun i => s(labVertex2 i, unlVertex0)) ∪
       Sτ.image (fun i => s(labVertex2 i, unlVertex1)))) : Set (Sym2 (Fin (2 + K))))

noncomputable instance (Sₗ Sτ : Finset (Fin K)) :
    DecidableRel (edgeTestGraph Sₗ Sτ).Adj := Classical.decRel _

theorem labVertex2_ne_unlVertex0 (i : Fin K) : labVertex2 i ≠ unlVertex0 := by
  intro h
  have := congrArg Fin.val h
  simp only [labVertex2, unlVertex0] at this
  have := i.isLt; omega

theorem labVertex2_ne_unlVertex1 (i : Fin K) : labVertex2 i ≠ unlVertex1 := by
  intro h
  have := congrArg Fin.val h
  simp only [labVertex2, unlVertex1] at this
  have := i.isLt; omega

theorem unlVertex0_ne_unlVertex1 : (unlVertex0 : Fin (2 + K)) ≠ unlVertex1 := by
  intro h
  have := congrArg Fin.val h
  simp only [unlVertex0, unlVertex1] at this
  omega

theorem edgeTestGraph_edge_injOn_Sₗ (Sₗ : Finset (Fin K)) :
    ∀ i ∈ Sₗ, ∀ i' ∈ Sₗ,
      s(labVertex2 i, unlVertex0) = s(labVertex2 i', unlVertex0) → i = i' := by
  intro i _ i' _ heq
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
  · apply Fin.ext
    have := congrArg Fin.val h1
    simpa [labVertex2] using this
  · exact absurd h1 (labVertex2_ne_unlVertex0 i)

theorem edgeTestGraph_edge_injOn_Sτ (Sτ : Finset (Fin K)) :
    ∀ i ∈ Sτ, ∀ i' ∈ Sτ,
      s(labVertex2 i, unlVertex1) = s(labVertex2 i', unlVertex1) → i = i' := by
  intro i _ i' _ heq
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
  · apply Fin.ext
    have := congrArg Fin.val h1
    simpa [labVertex2] using this
  · exact absurd h1 (labVertex2_ne_unlVertex1 i)

theorem edgeTestGraph_edgeFinset (Sₗ Sτ : Finset (Fin K)) :
    (edgeTestGraph Sₗ Sτ).edgeFinset =
      insert s(unlVertex0, unlVertex1)
        (Sₗ.image (fun i => s(labVertex2 i, unlVertex0)) ∪
         Sτ.image (fun i => s(labVertex2 i, unlVertex1))) := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, edgeTestGraph, SimpleGraph.edgeSet_fromEdgeSet,
    Set.mem_sdiff, Set.mem_insert_iff, Set.mem_union, Finset.coe_image, Set.mem_image,
    Finset.mem_coe, Sym2.mem_diagSet, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨h, -⟩; exact h
  · intro h
    refine ⟨h, ?_⟩
    rcases h with heq | ⟨i, _, heq⟩ | ⟨i, _, heq⟩
    · rw [heq, Sym2.mk_isDiag_iff]; exact unlVertex0_ne_unlVertex1
    · rw [← heq, Sym2.mk_isDiag_iff]; exact labVertex2_ne_unlVertex0 i
    · rw [← heq, Sym2.mk_isDiag_iff]; exact labVertex2_ne_unlVertex1 i

/-- `simpleEvalAt` label map: `labVertex2 i ↦ ξ i` (beta-reduced `dite` form). -/
theorem tau2_apply_labVertex2 {T : ℕ} (ξ : Fin K → Fin T) (σ : Fin 2 → Fin T) (i : Fin K) :
    (if h : ((labVertex2 i : Fin (2 + K)) : ℕ) < K then ξ ⟨↑(labVertex2 i), h⟩
        else σ ⟨↑(labVertex2 i) - K, by have := (labVertex2 i).isLt; omega⟩) = ξ i := by
  rw [dif_pos (show ((labVertex2 i : Fin (2 + K)) : ℕ) < K from i.isLt)]
  congr 1

/-- `simpleEvalAt` label map: `unlVertex0 ↦ σ 0` (beta-reduced `dite` form). -/
theorem tau2_apply_unlVertex0 {T : ℕ} (ξ : Fin K → Fin T) (σ : Fin 2 → Fin T) :
    (if h : ((unlVertex0 : Fin (2 + K)) : ℕ) < K then ξ ⟨↑(unlVertex0 : Fin (2 + K)), h⟩
        else σ ⟨↑(unlVertex0 : Fin (2 + K)) - K,
          by have := (unlVertex0 : Fin (2 + K)).isLt; omega⟩) = σ 0 := by
  rw [dif_neg (show ¬ ((unlVertex0 : Fin (2 + K)) : ℕ) < K from by simp [unlVertex0])]
  congr 1
  apply Fin.ext
  simp [unlVertex0]

/-- `simpleEvalAt` label map: `unlVertex1 ↦ σ 1` (beta-reduced `dite` form). -/
theorem tau2_apply_unlVertex1 {T : ℕ} (ξ : Fin K → Fin T) (σ : Fin 2 → Fin T) :
    (if h : ((unlVertex1 : Fin (2 + K)) : ℕ) < K then ξ ⟨↑(unlVertex1 : Fin (2 + K)), h⟩
        else σ ⟨↑(unlVertex1 : Fin (2 + K)) - K,
          by have := (unlVertex1 : Fin (2 + K)).isLt; omega⟩) = σ 1 := by
  rw [dif_neg (show ¬ ((unlVertex1 : Fin (2 + K)) : ℕ) < K from by simp [unlVertex1])]
  congr 1
  apply Fin.ext
  simp [unlVertex1]

/-- **Closed form for Gλτ**:
`simpleEvalAt B W (edgeTestGraph Sₗ Sτ) ξ
  = ∑ₜ ∑ₜ' W t · W t' · B t t' · ∏_{i∈Sₗ} B (ξ i) t · ∏_{i∈Sτ} B (ξ i) t'`. -/
theorem simpleEvalAt_edgeTestGraph {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (Sₗ Sτ : Finset (Fin K)) (ξ : Fin K → Fin T) :
    simpleEvalAt B W (edgeTestGraph Sₗ Sτ) ξ
      = ∑ t, ∑ t', W t * W t' * B t t'
          * (∏ i ∈ Sₗ, B (ξ i) t) * (∏ i ∈ Sτ, B (ξ i) t') := by
  have h_notin : s(unlVertex0, unlVertex1) ∉
      (Sₗ.image (fun i => s(labVertex2 i, unlVertex0)) ∪
       Sτ.image (fun i => s(labVertex2 i, unlVertex1))) := by
    simp only [Finset.mem_union, Finset.mem_image, not_or]
    refine ⟨?_, ?_⟩
    · rintro ⟨i, _, heq⟩
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact labVertex2_ne_unlVertex0 i h1
      · exact labVertex2_ne_unlVertex1 i h1
    · rintro ⟨i, _, heq⟩
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact labVertex2_ne_unlVertex0 i h1
      · exact labVertex2_ne_unlVertex1 i h1
  have h_disj : Disjoint (Sₗ.image (fun i => s(labVertex2 i, unlVertex0)))
      (Sτ.image (fun i => s(labVertex2 i, unlVertex1))) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [Finset.mem_image] at he1 he2
    obtain ⟨i, _, rfl⟩ := he1
    obtain ⟨j, _, heq⟩ := he2
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact unlVertex0_ne_unlVertex1 h2.symm
    · exact labVertex2_ne_unlVertex0 j h1
  have hsum : (∑ t, ∑ t', W t * W t' * B t t'
        * (∏ i ∈ Sₗ, B (ξ i) t) * (∏ i ∈ Sτ, B (ξ i) t'))
      = ∑ σ : Fin 2 → Fin T, W (σ 0) * W (σ 1) * B (σ 0) (σ 1)
          * (∏ i ∈ Sₗ, B (ξ i) (σ 0)) * (∏ i ∈ Sτ, B (ξ i) (σ 1)) :=
    (Fintype.sum_prod_type (fun p : Fin T × Fin T => W p.1 * W p.2 * B p.1 p.2
        * (∏ i ∈ Sₗ, B (ξ i) p.1) * (∏ i ∈ Sτ, B (ξ i) p.2))).symm.trans
      (Equiv.sum_comp (piFinTwoEquiv (fun _ => Fin T))
        (fun p => W p.1 * W p.2 * B p.1 p.2
          * (∏ i ∈ Sₗ, B (ξ i) p.1) * (∏ i ∈ Sτ, B (ξ i) p.2))).symm
  rw [hsum]
  unfold simpleEvalAt
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [edgeTestGraph_edgeFinset]
  show (∏ v : Fin 2, W (σ v)) *
      ∏ e ∈ insert s(unlVertex0, unlVertex1)
          (Sₗ.image (fun i => s(labVertex2 i, unlVertex0)) ∪
           Sτ.image (fun i => s(labVertex2 i, unlVertex1))),
        B ((fun v : Fin (2 + K) => if h : (v : ℕ) < K then ξ ⟨v, h⟩
              else σ ⟨v - K, by have := v.isLt; omega⟩) (Quot.out e).1)
          ((fun v : Fin (2 + K) => if h : (v : ℕ) < K then ξ ⟨v, h⟩
              else σ ⟨v - K, by have := v.isLt; omega⟩) (Quot.out e).2)
      = W (σ 0) * W (σ 1) * B (σ 0) (σ 1)
          * (∏ i ∈ Sₗ, B (ξ i) (σ 0)) * (∏ i ∈ Sτ, B (ξ i) (σ 1))
  rw [Fin.prod_univ_two, Finset.prod_insert h_notin, Finset.prod_union h_disj,
    Finset.prod_image (edgeTestGraph_edge_injOn_Sₗ Sₗ),
    Finset.prod_image (edgeTestGraph_edge_injOn_Sτ Sτ),
    out_pair_eq' B hB (fun v : Fin (2 + K) => if h : (v : ℕ) < K then ξ ⟨v, h⟩
        else σ ⟨v - K, by have := v.isLt; omega⟩) unlVertex0 unlVertex1,
    tau2_apply_unlVertex0 ξ σ, tau2_apply_unlVertex1 ξ σ]
  rw [show (∏ i ∈ Sₗ, B ((fun v : Fin (2 + K) => if h : (v : ℕ) < K then ξ ⟨v, h⟩
          else σ ⟨v - K, by have := v.isLt; omega⟩) (Quot.out s(labVertex2 i, unlVertex0)).1)
        ((fun v : Fin (2 + K) => if h : (v : ℕ) < K then ξ ⟨v, h⟩
          else σ ⟨v - K, by have := v.isLt; omega⟩) (Quot.out s(labVertex2 i, unlVertex0)).2))
      = ∏ i ∈ Sₗ, B (ξ i) (σ 0) from
    Finset.prod_congr rfl fun i _ => by
      rw [out_pair_eq' B hB (fun v : Fin (2 + K) => if h : (v : ℕ) < K then ξ ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩) (labVertex2 i) unlVertex0,
        tau2_apply_labVertex2 ξ σ i, tau2_apply_unlVertex0 ξ σ]]
  rw [show (∏ i ∈ Sτ, B ((fun v : Fin (2 + K) => if h : (v : ℕ) < K then ξ ⟨v, h⟩
          else σ ⟨v - K, by have := v.isLt; omega⟩) (Quot.out s(labVertex2 i, unlVertex1)).1)
        ((fun v : Fin (2 + K) => if h : (v : ℕ) < K then ξ ⟨v, h⟩
          else σ ⟨v - K, by have := v.isLt; omega⟩) (Quot.out s(labVertex2 i, unlVertex1)).2))
      = ∏ i ∈ Sτ, B (ξ i) (σ 1) from
    Finset.prod_congr rfl fun i _ => by
      rw [out_pair_eq' B hB (fun v : Fin (2 + K) => if h : (v : ℕ) < K then ξ ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩) (labVertex2 i) unlVertex1,
        tau2_apply_labVertex2 ξ σ i, tau2_apply_unlVertex1 ξ σ]]
  ring

/-! ## Chunk 3A: super-surjective orbit separation (Cai–Govorov Lemma 5.1, base case) -/

/-- `ξ : Fin K → Fin T` is **super-surjective** when every host vertex `v` is the image of
at least `2·T²` labels. This Cai–Govorov hypothesis provides the room to realize every
bounded exponent vector in the Vandermonde argument (by pigeonhole it yields, inside each
`ξ`-fibre, a `ξ'`-constant subset of size `≥ 2T`, aligning the exponents on both sides). -/
def SuperSurjective {T : ℕ} (ξ : Fin K → Fin T) : Prop :=
  ∀ v : Fin T, 2 * T * T ≤ (univ.filter (fun i => ξ i = v)).card

/-- Regroup a product over labels into a product over host vertices weighted by multiplicity:
`∏_{i∈S} B (ξ i) t = ∏_v (B v t) ^ |{i∈S : ξ i = v}|`. -/
theorem prod_label_eq_prod_mult {T : ℕ} (B : Fin T → Fin T → ℝ) (ξ : Fin K → Fin T)
    (S : Finset (Fin K)) (t : Fin T) :
    ∏ i ∈ S, B (ξ i) t = ∏ v, (B v t) ^ (S.filter (fun i => ξ i = v)).card := by
  rw [Finset.prod_comp (fun v => B v t) ξ]
  refine Finset.prod_subset (Finset.subset_univ _) ?_
  intro v _ hv
  rw [Finset.mem_image] at hv
  have hempty : S.filter (fun i => ξ i = v) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    exact fun i hi heq => hv ⟨i, hi, heq⟩
  rw [hempty, Finset.card_empty, pow_zero]

/-- **Multiplicity form of the Gχ equation.** Simple-equivalence makes the two
host-multiplicity-weighted moment sums agree, for every label subset `S`. This is the
bridge from `tupleEquivSimple` + the `starTestGraph` closed form to the Vandermonde input. -/
theorem tupleEquivSimple_starTestGraph_mult {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) {ξ ξ' : Fin K → Fin T}
    (h : tupleEquivSimple B W ξ ξ') (S : Finset (Fin K)) :
    ∑ t, W t * ∏ v, (B v t) ^ (S.filter (fun i => ξ i = v)).card
      = ∑ t, W t * ∏ v, (B v t) ^ (S.filter (fun i => ξ' i = v)).card := by
  have heq : simpleEvalAt B W (starTestGraph S) ξ = simpleEvalAt B W (starTestGraph S) ξ' :=
    h 1 (starTestGraph S)
  rw [simpleEvalAt_starTestGraph B hB W S ξ, simpleEvalAt_starTestGraph B hB W S ξ'] at heq
  simp only [prod_label_eq_prod_mult] at heq
  exact heq

/-- **Test-graph evaluation equality** — the moment-level interface to the chunk-3A engine.
Records exactly the two families of simple-graph equalities the super-surjective argument
consumes: the star tests `Gχ` and the edge tests `Gλτ`. Weaker than `tupleEquivSimple`
(which quantifies over ALL simple graphs); the descent step (chunk 4F) produces instances
of this interface from eq. (10) moment matching, where full `tupleEquivSimple` is not
available. -/
structure TestEvalEq {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (ξ ξ' : Fin K → Fin T) : Prop where
  star : ∀ S : Finset (Fin K),
    simpleEvalAt B W (starTestGraph S) ξ = simpleEvalAt B W (starTestGraph S) ξ'
  edge : ∀ Sₗ Sτ : Finset (Fin K),
    simpleEvalAt B W (edgeTestGraph Sₗ Sτ) ξ = simpleEvalAt B W (edgeTestGraph Sₗ Sτ) ξ'

/-- Full simple-equivalence yields the test-graph interface. -/
theorem TestEvalEq.of_tupleEquivSimple {T : ℕ} {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    {ξ ξ' : Fin K → Fin T} (h : tupleEquivSimple B W ξ ξ') : TestEvalEq B W ξ ξ' :=
  ⟨fun S => h 1 (starTestGraph S), fun Sₗ Sτ => h 2 (edgeTestGraph Sₗ Sτ)⟩

/-- **Aligned-Vandermonde extraction** (graph-free core of chunk 3A). If the moment sums of
two profile families `x`, `y` (weighted by `a`, `b`) agree for every exponent vector bounded
by `2·T`, then the `a`-mass and `b`-mass over each profile level set agree. The combined index
`Fin T ⊕ Fin T` turns the equality into a single multivariate Vandermonde cancellation
(`Graphon.CaiGovorov.multivariate_vandermonde_class_sums_zero`).

NB the exponent bound is `2·T`, not `T+1`: the combined index has `2T` points, and with only
`T+1` moments the statement is already false at `T = 2` (3 equations cannot pin a signed measure
on 4 points). This matches Cai–Govorov's range `0 ≤ k_j < 2m`. -/
theorem aligned_moments_class_balance {T : ℕ}
    (x y : Fin T → (Fin T → ℝ)) (a b : Fin T → ℝ)
    (hmom : ∀ k : Fin T → ℕ, (∀ j, k j < 2 * T) →
        ∑ t, a t * ∏ j, (x t j) ^ k j = ∑ t, b t * ∏ j, (y t j) ^ k j)
    (z : Fin T → ℝ) :
    ∑ t ∈ univ.filter (fun t => x t = z), a t
      = ∑ t ∈ univ.filter (fun t => y t = z), b t := by
  classical
  set bb : (Fin T ⊕ Fin T) → Fin T → ℝ := Sum.elim x y with hbb
  set aa : (Fin T ⊕ Fin T) → ℝ := Sum.elim a (fun t => - b t) with haa
  have hcard : Fintype.card (Fin T ⊕ Fin T) = 2 * T := by
    rw [Fintype.card_sum, Fintype.card_fin, two_mul]
  have hmoments : ∀ ℓ : Fin T → ℕ, (∀ j, ℓ j < Fintype.card (Fin T ⊕ Fin T)) →
      ∑ i, aa i * ∏ j, bb i j ^ ℓ j = 0 := by
    intro ℓ hℓ
    have hb : ∀ j, ℓ j < 2 * T := fun j => hcard ▸ hℓ j
    rw [Fintype.sum_sum_type]
    simp only [hbb, haa, Sum.elim_inl, Sum.elim_inr]
    rw [hmom ℓ hb, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun t _ => by ring
  have key := CaiGovorov.multivariate_vandermonde_class_sums_zero bb aa hmoments z
  rw [Finset.sum_filter, Fintype.sum_sum_type] at key
  simp only [hbb, haa, Sum.elim_inl, Sum.elim_inr, ← Finset.sum_filter] at key
  have hneg : ∑ t ∈ univ.filter (fun t => y t = z), -b t
      = -∑ t ∈ univ.filter (fun t => y t = z), b t := Finset.sum_neg_distrib b
  rw [hneg] at key
  linarith

/-- **Bounded-exponent aligned-Vandermonde extraction.** The bounded analogue of
`aligned_moments_class_balance`: an explicit per-coordinate distinct-value bound `N` replaces the
implicit cardinality `|ι|`, and the cancellation runs through the bounded multivariate Vandermonde
(`Graphon.CaiGovorov.multivariate_vandermonde_class_sums_zero_of_bound`). The combined index has at
most `2·N` distinct values per coordinate, matching the exponent range `0 ≤ k_c < 2·N`. -/
theorem aligned_moments_class_balance_of_bound {ι : Type*} [Fintype ι] {s : ℕ}
    (x y : ι → (Fin s → ℝ)) (a b : ι → ℝ) (N : ℕ)
    (hNx : ∀ c, (univ.image (fun i => x i c)).card ≤ N)
    (hNy : ∀ c, (univ.image (fun i => y i c)).card ≤ N)
    (hmom : ∀ k : Fin s → ℕ, (∀ c, k c < 2 * N) →
        ∑ i, a i * ∏ c, (x i c) ^ k c = ∑ i, b i * ∏ c, (y i c) ^ k c)
    (z : Fin s → ℝ) :
    ∑ i ∈ univ.filter (fun i => x i = z), a i
      = ∑ i ∈ univ.filter (fun i => y i = z), b i := by
  classical
  set bb : (ι ⊕ ι) → Fin s → ℝ := Sum.elim x y with hbb
  set aa : (ι ⊕ ι) → ℝ := Sum.elim a (fun i => - b i) with haa
  have hbound : ∀ c, (univ.image (fun p => bb p c)).card ≤ 2 * N := by
    intro c
    have hsub : univ.image (fun p => bb p c)
        ⊆ (univ.image (fun i => x i c)) ∪ (univ.image (fun i => y i c)) := by
      rw [Finset.image_subset_iff]
      rintro (i | i) _
      · simp only [hbb, Sum.elim_inl]
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (mem_univ i))
      · simp only [hbb, Sum.elim_inr]
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (mem_univ i))
    calc (univ.image (fun p => bb p c)).card
        ≤ ((univ.image (fun i => x i c)) ∪ (univ.image (fun i => y i c))).card :=
          Finset.card_le_card hsub
      _ ≤ (univ.image (fun i => x i c)).card + (univ.image (fun i => y i c)).card :=
          Finset.card_union_le _ _
      _ ≤ N + N := Nat.add_le_add (hNx c) (hNy c)
      _ = 2 * N := (two_mul N).symm
  have hmoments : ∀ ℓ : Fin s → ℕ, (∀ c, ℓ c < 2 * N) →
      ∑ p, aa p * ∏ c, bb p c ^ ℓ c = 0 := by
    intro ℓ hb
    rw [Fintype.sum_sum_type]
    simp only [hbb, haa, Sum.elim_inl, Sum.elim_inr]
    rw [hmom ℓ hb, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring
  have key := CaiGovorov.multivariate_vandermonde_class_sums_zero_of_bound bb aa (2 * N)
    hbound hmoments z
  rw [Finset.sum_filter, Fintype.sum_sum_type] at key
  simp only [hbb, haa, Sum.elim_inl, Sum.elim_inr, ← Finset.sum_filter] at key
  have hneg : ∑ i ∈ univ.filter (fun i => y i = z), -b i
      = -∑ i ∈ univ.filter (fun i => y i = z), b i := Finset.sum_neg_distrib b
  rw [hneg] at key
  linarith

/-- Profile-balance specialization: with `x t = B · t` (the profile/column of `t`),
`y t = B (s ·) t`, and weights `a = b = W`, the aligned moments force the `W`-mass over each
profile level set to match. -/
theorem aligned_star_moments_profile_balance {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (s : Fin T → Fin T)
    (haligned : ∀ k : Fin T → ℕ, (∀ j, k j < 2 * T) →
        ∑ t, W t * ∏ j, (B j t) ^ k j = ∑ t, W t * ∏ j, (B (s j) t) ^ k j)
    (z : Fin T → ℝ) :
    ∑ t ∈ univ.filter (fun t => (fun j => B j t) = z), W t
      = ∑ t ∈ univ.filter (fun t => (fun j => B (s j) t) = z), W t :=
  aligned_moments_class_balance (fun t j => B j t) (fun t j => B (s j) t) W W haligned z

/-- **Weight balance.** Twin-freeness collapses the left profile level set of `t` to the
singleton `{t}`, so the aligned Vandermonde output is exactly `W t = ∑_{u : B·t = B(s·)u} W u`. -/
theorem aligned_star_moments_weight_balance {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (s : Fin T → Fin T)
    (haligned : ∀ k : Fin T → ℕ, (∀ j, k j < 2 * T) →
        ∑ t, W t * ∏ j, (B j t) ^ k j = ∑ t, W t * ∏ j, (B (s j) t) ^ k j)
    (t : Fin T) :
    W t = ∑ u ∈ univ.filter (fun u => ∀ j, B j t = B (s j) u), W u := by
  have hbal := aligned_star_moments_profile_balance B W s haligned (fun j => B j t)
  have hsingle : (univ.filter (fun t' => (fun j => B j t') = fun j => B j t)) = {t} := by
    ext t'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hprof
      by_contra hne
      refine htwin t' t hne ?_
      funext j
      rw [hB t' j, hB t j]
      exact congrFun hprof j
    · rintro rfl; rfl
  rw [hsingle, Finset.sum_singleton] at hbal
  rw [hbal]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro u _
  constructor
  · intro h j; exact (congrFun h j).symm
  · intro h; funext j; exact (h j).symm

/-- **Support.** From weight balance and positivity, every host vertex `t` is matched: there is a
`u` with `B j t = B (s j) u` for all `j`. (The Vandermonde engine builds the matching.) -/
theorem aligned_star_moments_support {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (hW : ∀ v, 0 < W v)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j) (s : Fin T → Fin T)
    (haligned : ∀ k : Fin T → ℕ, (∀ j, k j < 2 * T) →
        ∑ t, W t * ∏ j, (B j t) ^ k j = ∑ t, W t * ∏ j, (B (s j) t) ^ k j)
    (t : Fin T) :
    ∃ u, ∀ j, B j t = B (s j) u := by
  have hbal := aligned_star_moments_weight_balance B hB W htwin s haligned t
  have hne : (univ.filter (fun u => ∀ j, B j t = B (s j) u)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.sum_empty] at hbal
    exact (hW t).ne' hbal
  obtain ⟨u, hu⟩ := hne
  rw [Finset.mem_filter] at hu
  exact ⟨u, hu.2⟩

/-! ### Chunk 3A.2: pigeonhole and the preliminary map `s` -/

/-- **Pigeonhole.** Super-surjectivity gives, inside each `ξ`-fibre over `j`, a subset `J` of
size `≥ 2T` on which `ξ'` is constant (value `s_j`). (`ξ'` takes ≤ T values on the fibre of
size `≥ 2T²`, so some value is hit `≥ 2T` times.) -/
theorem exists_large_const_image_subset {T : ℕ} (ξ ξ' : Fin K → Fin T)
    (hξ : SuperSurjective ξ) (j : Fin T) :
    ∃ (s_j : Fin T) (J : Finset (Fin K)),
      J ⊆ univ.filter (fun i => ξ i = j) ∧ 2 * T ≤ J.card ∧ (∀ i ∈ J, ξ' i = s_j) := by
  classical
  have hmaps : ∀ i ∈ univ.filter (fun i => ξ i = j), ξ' i ∈ (univ : Finset (Fin T)) :=
    fun i _ => mem_univ _
  have hcard : (univ : Finset (Fin T)).card * (2 * T)
      ≤ (univ.filter (fun i => ξ i = j)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    calc T * (2 * T) = 2 * T * T := by ring
      _ ≤ (univ.filter (fun i => ξ i = j)).card := hξ j
  obtain ⟨s_j, _, hsj⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hmaps ⟨j, mem_univ j⟩ hcard
  exact ⟨s_j, (univ.filter (fun i => ξ i = j)).filter (fun i => ξ' i = s_j),
    Finset.filter_subset _ _, hsj, fun i hi => (Finset.mem_filter.mp hi).2⟩

/-- The preliminary Cai–Govorov map `s : Fin T → Fin T`: the constant `ξ'`-value on a large
subset of each `ξ`-fibre. -/
noncomputable def superMap {T : ℕ} (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ) (j : Fin T) :
    Fin T :=
  (exists_large_const_image_subset ξ ξ' hξ j).choose

/-- The chosen large `ξ'`-constant subset of the `ξ`-fibre over `j`. -/
noncomputable def superFiberSubset {T : ℕ} (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ)
    (j : Fin T) : Finset (Fin K) :=
  (exists_large_const_image_subset ξ ξ' hξ j).choose_spec.choose

theorem superFiberSubset_subset {T : ℕ} (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ)
    (j : Fin T) : superFiberSubset ξ ξ' hξ j ⊆ univ.filter (fun i => ξ i = j) :=
  (exists_large_const_image_subset ξ ξ' hξ j).choose_spec.choose_spec.1

theorem superFiberSubset_card {T : ℕ} (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ)
    (j : Fin T) : 2 * T ≤ (superFiberSubset ξ ξ' hξ j).card :=
  (exists_large_const_image_subset ξ ξ' hξ j).choose_spec.choose_spec.2.1

theorem superFiberSubset_mem_left {T : ℕ} (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ)
    (j : Fin T) {i : Fin K} (hi : i ∈ superFiberSubset ξ ξ' hξ j) : ξ i = j := by
  have := superFiberSubset_subset ξ ξ' hξ j hi
  rw [Finset.mem_filter] at this
  exact this.2

theorem superFiberSubset_image_const {T : ℕ} (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ)
    (j : Fin T) : ∀ i ∈ superFiberSubset ξ ξ' hξ j, ξ' i = superMap ξ ξ' hξ j :=
  (exists_large_const_image_subset ξ ξ' hξ j).choose_spec.choose_spec.2.2

/-- Distinct fibres give disjoint chosen subsets (each lies in a distinct `ξ`-fibre). -/
theorem superFiberSubset_disjoint {T : ℕ} (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ)
    {j j' : Fin T} (hjj : j ≠ j') :
    Disjoint (superFiberSubset ξ ξ' hξ j) (superFiberSubset ξ ξ' hξ j') := by
  apply Finset.disjoint_left.mpr
  intro i hi hi'
  exact hjj ((superFiberSubset_mem_left ξ ξ' hξ j hi).symm.trans
    (superFiberSubset_mem_left ξ ξ' hξ j' hi'))

/-! ### Chunk 3A.3: aligned moments from selected labels -/

/-- For any bounded exponent vector `k`, select inside each `ξ`-fibre's distinguished subset a
sub-subset of size exactly `k j`. -/
theorem exists_exponent_label_set {T : ℕ} (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ)
    (k : Fin T → ℕ) (hk : ∀ j, k j < 2 * T) :
    ∃ Kf : Fin T → Finset (Fin K),
      (∀ j, Kf j ⊆ superFiberSubset ξ ξ' hξ j) ∧ (∀ j, (Kf j).card = k j) := by
  choose Kf hsub hcard using fun j =>
    Finset.exists_subset_card_eq (s := superFiberSubset ξ ξ' hξ j) (n := k j)
      (lt_of_lt_of_le (hk j) (superFiberSubset_card ξ ξ' hξ j)).le
  exact ⟨Kf, hsub, hcard⟩

/-- **Aligned-moment bridge.** From the star-test equalities (`TestEvalEq.star`) and
super-surjectivity, the aligned moment identity holds for every bounded exponent vector, with the
right-hand side reindexed by `superMap`.
This consumes the `starTestGraph` closed form: the label set `S = ⋃ⱼ Kⱼ` has `ξ ≡ j` on `Kⱼ` (giving
`(B j t)^{k j}` on the left) and `ξ' ≡ superMap j` on `Kⱼ` (giving `(B (superMap j) t)^{k j}` on the
right) — no injectivity of `superMap` is needed. -/
theorem aligned_moments_of_testEvalEq_super {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (ξ ξ' : Fin K → Fin T)
    (hξ : SuperSurjective ξ) (h : TestEvalEq B W ξ ξ') :
    ∀ k : Fin T → ℕ, (∀ j, k j < 2 * T) →
      ∑ t, W t * ∏ j, (B j t) ^ k j
        = ∑ t, W t * ∏ j, (B (superMap ξ ξ' hξ j) t) ^ k j := by
  intro k hk
  classical
  obtain ⟨Kf, hKf_sub, hKf_card⟩ := exists_exponent_label_set ξ ξ' hξ k hk
  set S := univ.biUnion Kf with hS
  have hdisj : Set.PairwiseDisjoint (↑(univ : Finset (Fin T))) Kf :=
    fun j _ j' _ hjj => Finset.disjoint_of_subset_left (hKf_sub j)
      (Finset.disjoint_of_subset_right (hKf_sub j') (superFiberSubset_disjoint ξ ξ' hξ hjj))
  have hLHS : ∀ t, ∏ i ∈ S, B (ξ i) t = ∏ j, (B j t) ^ k j := by
    intro t
    rw [hS, Finset.prod_biUnion hdisj]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hconst : ∏ i ∈ Kf j, B (ξ i) t = ∏ i ∈ Kf j, B j t :=
      Finset.prod_congr rfl fun i hi => by
        rw [superFiberSubset_mem_left ξ ξ' hξ j (hKf_sub j hi)]
    rw [hconst, Finset.prod_const, hKf_card j]
  have hRHS : ∀ t, ∏ i ∈ S, B (ξ' i) t = ∏ j, (B (superMap ξ ξ' hξ j) t) ^ k j := by
    intro t
    rw [hS, Finset.prod_biUnion hdisj]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hconst : ∏ i ∈ Kf j, B (ξ' i) t = ∏ i ∈ Kf j, B (superMap ξ ξ' hξ j) t :=
      Finset.prod_congr rfl fun i hi => by
        rw [superFiberSubset_image_const ξ ξ' hξ j i (hKf_sub j hi)]
    rw [hconst, Finset.prod_const, hKf_card j]
  have heq : simpleEvalAt B W (starTestGraph S) ξ = simpleEvalAt B W (starTestGraph S) ξ' :=
    h.star S
  rw [simpleEvalAt_starTestGraph B hB W S ξ, simpleEvalAt_starTestGraph B hB W S ξ'] at heq
  calc ∑ t, W t * ∏ j, (B j t) ^ k j
      = ∑ t, W t * ∏ i ∈ S, B (ξ i) t := by
        refine Finset.sum_congr rfl fun t _ => ?_; rw [hLHS t]
    _ = ∑ t, W t * ∏ i ∈ S, B (ξ' i) t := heq
    _ = ∑ t, W t * ∏ j, (B (superMap ξ ξ' hξ j) t) ^ k j := by
        refine Finset.sum_congr rfl fun t _ => ?_; rw [hRHS t]

/-- **`superMap` support** (the user's straightforward corollary): every host vertex `t` is matched
by the preliminary map — there is a `u` with `B j t = B (superMap … j) u` for all `j`. Combines the
aligned-moment bridge with the proved aligned-Vandermonde support lemma. -/
theorem superMap_support {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ v, 0 < W v) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ) (h : TestEvalEq B W ξ ξ') (t : Fin T) :
    ∃ u, ∀ j, B j t = B (superMap ξ ξ' hξ j) u :=
  aligned_star_moments_support B hB W hW htwin (superMap ξ ξ' hξ)
    (aligned_moments_of_testEvalEq_super B hB W ξ ξ' hξ h) t

/-! ### Chunk 3A.4: `superMap` is bijective -/

/-- **`superMap` is injective.** If `superMap a = superMap b`, then for every `t` the support
witness `u` gives `B a t = B (superMap a) u = B (superMap b) u = B b t`, so the rows `B a`, `B b`
agree; twin-freeness forces `a = b`. (No edge tests needed.) -/
theorem superMap_injective {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ v, 0 < W v) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ) (h : TestEvalEq B W ξ ξ') :
    Function.Injective (superMap ξ ξ' hξ) := by
  intro a b hab
  by_contra hne
  refine htwin a b hne ?_
  funext t
  obtain ⟨u, hu⟩ := superMap_support B hB W hW htwin ξ ξ' hξ h t
  rw [hu a, hu b, hab]

/-- **`superMap` is bijective** (injective endomap of a finite type). -/
theorem superMap_bijective {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ v, 0 < W v) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ) (h : TestEvalEq B W ξ ξ') :
    Function.Bijective (superMap ξ ξ' hξ) :=
  Finite.injective_iff_bijective.mp (superMap_injective B hB W hW htwin ξ ξ' hξ h)

/-- The preliminary map as a permutation of `Fin T`. The orbit-defining automorphism `σ` will be
exactly this permutation (since `ξ' i = superMap (ξ i)` on the selected labels, `σ = superMap`,
not its inverse); edge/weight preservation are established next (3A.5) via `edgeTestGraph`. -/
noncomputable def superPerm {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ v, 0 < W v) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ) (h : TestEvalEq B W ξ ξ') :
    Equiv.Perm (Fin T) :=
  Equiv.ofBijective (superMap ξ ξ' hξ) (superMap_bijective B hB W hW htwin ξ ξ' hξ h)

@[simp] theorem superPerm_apply {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ v, 0 < W v) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ) (h : TestEvalEq B W ξ ξ') (j : Fin T) :
    superPerm B hB W hW htwin ξ ξ' hξ h j = superMap ξ ξ' hξ j := rfl

/-! ### Chunk 3A.5: aligned edge moments (`edgeTestGraph`) -/

/-- Regroup a product over a pairwise-disjoint union `⋃ⱼ Kf j` of a function that is constant
(`= c j`) on each block `Kf j` into `∏ⱼ (c j) ^ (k j)`, where `(Kf j).card = k j`. -/
private theorem prod_biUnion_const {T : ℕ} {Kf : Fin T → Finset (Fin K)}
    (hdisj : Set.PairwiseDisjoint (↑(univ : Finset (Fin T))) Kf)
    {f : Fin K → ℝ} {c : Fin T → ℝ} (hc : ∀ j, ∀ i ∈ Kf j, f i = c j)
    {k : Fin T → ℕ} (hcard : ∀ j, (Kf j).card = k j) :
    ∏ i ∈ univ.biUnion Kf, f i = ∏ j, (c j) ^ k j := by
  rw [Finset.prod_biUnion hdisj]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hconst : ∏ i ∈ Kf j, f i = ∏ i ∈ Kf j, c j :=
    Finset.prod_congr rfl fun i hi => hc j i hi
  rw [hconst, Finset.prod_const, hcard j]

/-- **Aligned edge-moment bridge** (pair analogue of `aligned_moments_of_testEvalEq_super`).
From the edge-test equalities (`TestEvalEq.edge`) and super-surjectivity, the aligned
*edge*-moment identity holds for every pair of bounded exponent vectors `k`, `l`, with the
right-hand side reindexed by `superMap`. This
consumes the `edgeTestGraph` closed form: with `Sₗ = ⋃ⱼ Klⱼ`, `Sτ = ⋃ⱼ Ktⱼ` one has `ξ ≡ j` on
each block (giving `(B j ·)^{k j}`/`(B j ·)^{l j}`) and `ξ' ≡ superMap j` (giving the reindexed
right-hand side) — no injectivity of `superMap` is needed. -/
theorem aligned_edge_moments_of_testEvalEq_super {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (ξ ξ' : Fin K → Fin T)
    (hξ : SuperSurjective ξ) (h : TestEvalEq B W ξ ξ') :
    ∀ k l : Fin T → ℕ, (∀ j, k j < 2 * T) → (∀ j, l j < 2 * T) →
      ∑ x, ∑ y, W x * W y * B x y * (∏ j, (B j x) ^ k j) * (∏ j, (B j y) ^ l j)
        = ∑ x, ∑ y, W x * W y * B x y
            * (∏ j, (B (superMap ξ ξ' hξ j) x) ^ k j) * (∏ j, (B (superMap ξ ξ' hξ j) y) ^ l j) := by
  intro k l hk hl
  classical
  obtain ⟨Kl, hKl_sub, hKl_card⟩ := exists_exponent_label_set ξ ξ' hξ k hk
  obtain ⟨Kt, hKt_sub, hKt_card⟩ := exists_exponent_label_set ξ ξ' hξ l hl
  have hdisj_l : Set.PairwiseDisjoint (↑(univ : Finset (Fin T))) Kl :=
    fun j _ j' _ hjj => Finset.disjoint_of_subset_left (hKl_sub j)
      (Finset.disjoint_of_subset_right (hKl_sub j') (superFiberSubset_disjoint ξ ξ' hξ hjj))
  have hdisj_t : Set.PairwiseDisjoint (↑(univ : Finset (Fin T))) Kt :=
    fun j _ j' _ hjj => Finset.disjoint_of_subset_left (hKt_sub j)
      (Finset.disjoint_of_subset_right (hKt_sub j') (superFiberSubset_disjoint ξ ξ' hξ hjj))
  have hLl : ∀ x, ∏ i ∈ univ.biUnion Kl, B (ξ i) x = ∏ j, (B j x) ^ k j := fun x =>
    prod_biUnion_const hdisj_l
      (fun j i hi => by rw [superFiberSubset_mem_left ξ ξ' hξ j (hKl_sub j hi)]) hKl_card
  have hLl' : ∀ x, ∏ i ∈ univ.biUnion Kl, B (ξ' i) x
      = ∏ j, (B (superMap ξ ξ' hξ j) x) ^ k j := fun x =>
    prod_biUnion_const hdisj_l
      (fun j i hi => by rw [superFiberSubset_image_const ξ ξ' hξ j i (hKl_sub j hi)]) hKl_card
  have hTt : ∀ y, ∏ i ∈ univ.biUnion Kt, B (ξ i) y = ∏ j, (B j y) ^ l j := fun y =>
    prod_biUnion_const hdisj_t
      (fun j i hi => by rw [superFiberSubset_mem_left ξ ξ' hξ j (hKt_sub j hi)]) hKt_card
  have hTt' : ∀ y, ∏ i ∈ univ.biUnion Kt, B (ξ' i) y
      = ∏ j, (B (superMap ξ ξ' hξ j) y) ^ l j := fun y =>
    prod_biUnion_const hdisj_t
      (fun j i hi => by rw [superFiberSubset_image_const ξ ξ' hξ j i (hKt_sub j hi)]) hKt_card
  have heq : simpleEvalAt B W (edgeTestGraph (univ.biUnion Kl) (univ.biUnion Kt)) ξ
      = simpleEvalAt B W (edgeTestGraph (univ.biUnion Kl) (univ.biUnion Kt)) ξ' :=
    h.edge (univ.biUnion Kl) (univ.biUnion Kt)
  rw [simpleEvalAt_edgeTestGraph B hB W _ _ ξ,
    simpleEvalAt_edgeTestGraph B hB W _ _ ξ'] at heq
  calc ∑ x, ∑ y, W x * W y * B x y * (∏ j, (B j x) ^ k j) * (∏ j, (B j y) ^ l j)
      = ∑ x, ∑ y, W x * W y * B x y
          * (∏ i ∈ univ.biUnion Kl, B (ξ i) x) * (∏ i ∈ univ.biUnion Kt, B (ξ i) y) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [hLl x, hTt y]
    _ = ∑ x, ∑ y, W x * W y * B x y
          * (∏ i ∈ univ.biUnion Kl, B (ξ' i) x) * (∏ i ∈ univ.biUnion Kt, B (ξ' i) y) := heq
    _ = ∑ x, ∑ y, W x * W y * B x y
          * (∏ j, (B (superMap ξ ξ' hξ j) x) ^ k j)
          * (∏ j, (B (superMap ξ ξ' hξ j) y) ^ l j) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [hLl' x, hTt' y]

/-- **Aligned edge-moment pair balance.** Specializing the bounded extraction engine
`aligned_moments_class_balance_of_bound` at `ι = Fin T × Fin T` and coordinate dimension `T + T`
(gluing the two `B`-columns of a pair via `Fin.append`), the aligned edge moments force the
`W·W·B`-mass over each pair of column profiles `(z₁, z₂)` to match between the original labelling and
the `superMap`-reindexed one. -/
theorem aligned_edge_moments_pair_balance {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (ξ ξ' : Fin K → Fin T)
    (hξ : SuperSurjective ξ) (h : TestEvalEq B W ξ ξ') (z₁ z₂ : Fin T → ℝ) :
    ∑ p : Fin T × Fin T,
        (if (fun j => B j p.1) = z₁ ∧ (fun j => B j p.2) = z₂
         then W p.1 * W p.2 * B p.1 p.2 else 0)
      = ∑ p : Fin T × Fin T,
          (if (fun j => B (superMap ξ ξ' hξ j) p.1) = z₁ ∧
              (fun j => B (superMap ξ ξ' hξ j) p.2) = z₂
           then W p.1 * W p.2 * B p.1 p.2 else 0) := by
  set x : Fin T × Fin T → (Fin (T + T) → ℝ) :=
    fun p => Fin.append (fun j => B j p.1) (fun j => B j p.2) with hx
  set y : Fin T × Fin T → (Fin (T + T) → ℝ) :=
    fun p => Fin.append (fun j => B (superMap ξ ξ' hξ j) p.1)
      (fun j => B (superMap ξ ξ' hξ j) p.2) with hy
  set a : Fin T × Fin T → ℝ := fun p => W p.1 * W p.2 * B p.1 p.2 with ha
  -- Per-coordinate distinct-value bound (≤ T) for the left profiles.
  have hNx : ∀ c, (univ.image (fun p => x p c)).card ≤ T := by
    intro c
    refine Fin.addCases (fun j => ?_) (fun j => ?_) c
    · have hsub : univ.image (fun p : Fin T × Fin T => x p (Fin.castAdd T j))
          ⊆ univ.image (fun u : Fin T => B j u) := by
        intro val hval
        rw [mem_image] at hval ⊢
        obtain ⟨p, -, hp⟩ := hval
        refine ⟨p.1, mem_univ _, ?_⟩
        rw [← hp]; simp only [hx, Fin.append_left]
      calc (univ.image (fun p : Fin T × Fin T => x p (Fin.castAdd T j))).card
          ≤ (univ.image (fun u : Fin T => B j u)).card := Finset.card_le_card hsub
        _ ≤ (univ : Finset (Fin T)).card := Finset.card_image_le
        _ = T := by rw [Finset.card_univ, Fintype.card_fin]
    · have hsub : univ.image (fun p : Fin T × Fin T => x p (Fin.natAdd T j))
          ⊆ univ.image (fun u : Fin T => B j u) := by
        intro val hval
        rw [mem_image] at hval ⊢
        obtain ⟨p, -, hp⟩ := hval
        refine ⟨p.2, mem_univ _, ?_⟩
        rw [← hp]; simp only [hx, Fin.append_right]
      calc (univ.image (fun p : Fin T × Fin T => x p (Fin.natAdd T j))).card
          ≤ (univ.image (fun u : Fin T => B j u)).card := Finset.card_le_card hsub
        _ ≤ (univ : Finset (Fin T)).card := Finset.card_image_le
        _ = T := by rw [Finset.card_univ, Fintype.card_fin]
  have hNy : ∀ c, (univ.image (fun p => y p c)).card ≤ T := by
    intro c
    refine Fin.addCases (fun j => ?_) (fun j => ?_) c
    · have hsub : univ.image (fun p : Fin T × Fin T => y p (Fin.castAdd T j))
          ⊆ univ.image (fun u : Fin T => B (superMap ξ ξ' hξ j) u) := by
        intro val hval
        rw [mem_image] at hval ⊢
        obtain ⟨p, -, hp⟩ := hval
        refine ⟨p.1, mem_univ _, ?_⟩
        rw [← hp]; simp only [hy, Fin.append_left]
      calc (univ.image (fun p : Fin T × Fin T => y p (Fin.castAdd T j))).card
          ≤ (univ.image (fun u : Fin T => B (superMap ξ ξ' hξ j) u)).card :=
            Finset.card_le_card hsub
        _ ≤ (univ : Finset (Fin T)).card := Finset.card_image_le
        _ = T := by rw [Finset.card_univ, Fintype.card_fin]
    · have hsub : univ.image (fun p : Fin T × Fin T => y p (Fin.natAdd T j))
          ⊆ univ.image (fun u : Fin T => B (superMap ξ ξ' hξ j) u) := by
        intro val hval
        rw [mem_image] at hval ⊢
        obtain ⟨p, -, hp⟩ := hval
        refine ⟨p.2, mem_univ _, ?_⟩
        rw [← hp]; simp only [hy, Fin.append_right]
      calc (univ.image (fun p : Fin T × Fin T => y p (Fin.natAdd T j))).card
          ≤ (univ.image (fun u : Fin T => B (superMap ξ ξ' hξ j) u)).card :=
            Finset.card_le_card hsub
        _ ≤ (univ : Finset (Fin T)).card := Finset.card_image_le
        _ = T := by rw [Finset.card_univ, Fintype.card_fin]
  -- The bounded moment identity, fed by the edge-moment bridge.
  have hmom : ∀ k : Fin (T + T) → ℕ, (∀ c, k c < 2 * T) →
      ∑ p, a p * ∏ c, (x p c) ^ k c = ∑ p, a p * ∏ c, (y p c) ^ k c := by
    intro k hk
    have hbridge := aligned_edge_moments_of_testEvalEq_super B hB W ξ ξ' hξ h
      (fun j => k (Fin.castAdd T j)) (fun j => k (Fin.natAdd T j))
      (fun j => hk (Fin.castAdd T j)) (fun j => hk (Fin.natAdd T j))
    have hxprod : ∀ p : Fin T × Fin T, ∏ c, (x p c) ^ k c
        = (∏ j, (B j p.1) ^ k (Fin.castAdd T j)) * (∏ j, (B j p.2) ^ k (Fin.natAdd T j)) := by
      intro p
      rw [Fin.prod_univ_add]
      congr 1
      · refine Finset.prod_congr rfl (fun i _ => ?_); simp only [hx, Fin.append_left]
      · refine Finset.prod_congr rfl (fun i _ => ?_); simp only [hx, Fin.append_right]
    have hyprod : ∀ p : Fin T × Fin T, ∏ c, (y p c) ^ k c
        = (∏ j, (B (superMap ξ ξ' hξ j) p.1) ^ k (Fin.castAdd T j))
          * (∏ j, (B (superMap ξ ξ' hξ j) p.2) ^ k (Fin.natAdd T j)) := by
      intro p
      rw [Fin.prod_univ_add]
      congr 1
      · refine Finset.prod_congr rfl (fun i _ => ?_); simp only [hy, Fin.append_left]
      · refine Finset.prod_congr rfl (fun i _ => ?_); simp only [hy, Fin.append_right]
    calc ∑ p, a p * ∏ c, (x p c) ^ k c
        = ∑ p : Fin T × Fin T, W p.1 * W p.2 * B p.1 p.2
            * (∏ j, (B j p.1) ^ k (Fin.castAdd T j))
            * (∏ j, (B j p.2) ^ k (Fin.natAdd T j)) := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [hxprod p]; simp only [ha]; ring
      _ = ∑ p : Fin T × Fin T, W p.1 * W p.2 * B p.1 p.2
            * (∏ j, (B (superMap ξ ξ' hξ j) p.1) ^ k (Fin.castAdd T j))
            * (∏ j, (B (superMap ξ ξ' hξ j) p.2) ^ k (Fin.natAdd T j)) := by
          rw [Fintype.sum_prod_type, Fintype.sum_prod_type]; exact hbridge
      _ = ∑ p, a p * ∏ c, (y p c) ^ k c := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [hyprod p]; simp only [ha]; ring
  -- Apply the bounded extraction engine at `z = Fin.append z₁ z₂`.
  have key := aligned_moments_class_balance_of_bound x y a a T hNx hNy hmom (Fin.append z₁ z₂)
  -- `Fin.append`-injectivity: a glued profile equals `append z₁ z₂` iff its halves are `z₁`, `z₂`.
  have happend : ∀ f g : Fin T → ℝ,
      (Fin.append f g = Fin.append z₁ z₂) ↔ (f = z₁ ∧ g = z₂) := by
    intro f g
    constructor
    · intro happ
      refine ⟨?_, ?_⟩
      · funext j
        have hj := congrFun happ (Fin.castAdd T j)
        rwa [Fin.append_left, Fin.append_left] at hj
      · funext j
        have hj := congrFun happ (Fin.natAdd T j)
        rwa [Fin.append_right, Fin.append_right] at hj
    · rintro ⟨rfl, rfl⟩; rfl
  have hfiltL : univ.filter (fun p : Fin T × Fin T =>
        (fun j => B j p.1) = z₁ ∧ (fun j => B j p.2) = z₂)
      = univ.filter (fun p => x p = Fin.append z₁ z₂) := by
    refine Finset.filter_congr (fun p _ => ?_)
    exact (happend (fun j => B j p.1) (fun j => B j p.2)).symm
  have hfiltR : univ.filter (fun p : Fin T × Fin T =>
        (fun j => B (superMap ξ ξ' hξ j) p.1) = z₁ ∧
          (fun j => B (superMap ξ ξ' hξ j) p.2) = z₂)
      = univ.filter (fun p => y p = Fin.append z₁ z₂) := by
    refine Finset.filter_congr (fun p _ => ?_)
    exact (happend (fun j => B (superMap ξ ξ' hξ j) p.1)
      (fun j => B (superMap ξ ξ' hξ j) p.2)).symm
  rw [← Finset.sum_filter, ← Finset.sum_filter, hfiltL, hfiltR]
  exact key

/-! ### Chunk 3A.5 steps 2–7: the support-witness map and the weighted automorphism -/

/-- The support-witness map `r = superInv`: `r t` is the unique `u` with
`∀ j, B j t = B (superMap j) u`. It turns out to be the orbit automorphism (`= superMap`). -/
noncomputable def superInv {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ v, 0 < W v) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ) (h : TestEvalEq B W ξ ξ') (t : Fin T) :
    Fin T :=
  (superMap_support B hB W hW htwin ξ ξ' hξ h t).choose

theorem superInv_spec {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ v, 0 < W v) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ) (h : TestEvalEq B W ξ ξ') (t : Fin T) :
    ∀ j, B j t = B (superMap ξ ξ' hξ j) (superInv B hB W hW htwin ξ ξ' hξ h t) :=
  (superMap_support B hB W hW htwin ξ ξ' hξ h t).choose_spec

theorem superInv_unique {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ v, 0 < W v) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ) (h : TestEvalEq B W ξ ξ') {t u : Fin T}
    (hu : ∀ j, B j t = B (superMap ξ ξ' hξ j) u) :
    u = superInv B hB W hW htwin ξ ξ' hξ h t := by
  by_contra hne
  refine htwin u (superInv B hB W hW htwin ξ ξ' hξ h t) hne ?_
  funext w
  obtain ⟨j, hj⟩ := (superMap_bijective B hB W hW htwin ξ ξ' hξ h).surjective w
  rw [← hj, hB u (superMap ξ ξ' hξ j),
    hB (superInv B hB W hW htwin ξ ξ' hξ h t) (superMap ξ ξ' hξ j),
    ← hu j, superInv_spec B hB W hW htwin ξ ξ' hξ h t j]

theorem superInv_injective {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ v, 0 < W v) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ) (h : TestEvalEq B W ξ ξ') :
    Function.Injective (superInv B hB W hW htwin ξ ξ' hξ h) := by
  intro a b hab
  by_contra hne
  refine htwin a b hne ?_
  funext j
  rw [hB a j, superInv_spec B hB W hW htwin ξ ξ' hξ h a j, hab,
    ← superInv_spec B hB W hW htwin ξ ξ' hξ h b j, ← hB b j]

theorem superInv_bijective {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ v, 0 < W v) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ) (h : TestEvalEq B W ξ ξ') :
    Function.Bijective (superInv B hB W hW htwin ξ ξ' hξ h) :=
  Finite.injective_iff_bijective.mp (superInv_injective B hB W hW htwin ξ ξ' hξ h)

/-- **Weight preservation for `superInv`.** The support fibre of `t` is the singleton
`{superInv t}`, so weight balance gives `W (superInv t) = W t`. -/
theorem superInv_preserves_W {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ v, 0 < W v) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ) (h : TestEvalEq B W ξ ξ') (t : Fin T) :
    W (superInv B hB W hW htwin ξ ξ' hξ h t) = W t := by
  have hbal := aligned_star_moments_weight_balance B hB W htwin (superMap ξ ξ' hξ)
    (aligned_moments_of_testEvalEq_super B hB W ξ ξ' hξ h) t
  have hfib : (univ.filter (fun u => ∀ j, B j t = B (superMap ξ ξ' hξ j) u))
      = {superInv B hB W hW htwin ξ ξ' hξ h t} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hu => superInv_unique B hB W hW htwin ξ ξ' hξ h hu,
      fun hu => hu ▸ superInv_spec B hB W hW htwin ξ ξ' hξ h t⟩
  rw [hfib, Finset.sum_singleton] at hbal
  exact hbal.symm

/-- **Edge preservation for `superInv`.** Plugging the pair balance at `z₁ = B·a`, `z₂ = B·b`:
the left fibre is `{(a,b)}` (twin-free) and the right fibre is `{(superInv a, superInv b)}`
(`superInv_unique`); positivity cancels the weights. So `superInv` preserves `B`. -/
theorem superInv_preserves_B {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ v, 0 < W v) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ) (h : TestEvalEq B W ξ ξ') (a b : Fin T) :
    B (superInv B hB W hW htwin ξ ξ' hξ h a) (superInv B hB W hW htwin ξ ξ' hξ h b) = B a b := by
  classical
  have hcol : ∀ u v : Fin T, (fun j => B j u) = (fun j => B j v) → u = v := by
    intro u v huv
    by_contra hne
    refine htwin u v hne ?_
    funext j
    have hj := congrFun huv j
    rw [hB u j, hB v j]; exact hj
  have hLHS : (∑ p : Fin T × Fin T,
      if (fun j => B j p.1) = (fun j => B j a) ∧ (fun j => B j p.2) = (fun j => B j b)
      then W p.1 * W p.2 * B p.1 p.2 else 0) = W a * W b * B a b := by
    rw [Finset.sum_eq_single (a, b)]
    · simp
    · intro p _ hp
      have hfalse : ¬ ((fun j => B j p.1) = (fun j => B j a) ∧
          (fun j => B j p.2) = (fun j => B j b)) := by
        rintro ⟨hp1, hp2⟩
        exact hp (Prod.ext (hcol p.1 a hp1) (hcol p.2 b hp2))
      rw [if_neg hfalse]
    · intro hc; exact absurd (Finset.mem_univ _) hc
  have hRHS : (∑ p : Fin T × Fin T,
      if (fun j => B (superMap ξ ξ' hξ j) p.1) = (fun j => B j a) ∧
         (fun j => B (superMap ξ ξ' hξ j) p.2) = (fun j => B j b)
      then W p.1 * W p.2 * B p.1 p.2 else 0)
      = W (superInv B hB W hW htwin ξ ξ' hξ h a) * W (superInv B hB W hW htwin ξ ξ' hξ h b)
        * B (superInv B hB W hW htwin ξ ξ' hξ h a) (superInv B hB W hW htwin ξ ξ' hξ h b) := by
    rw [Finset.sum_eq_single (superInv B hB W hW htwin ξ ξ' hξ h a,
        superInv B hB W hW htwin ξ ξ' hξ h b)]
    · rw [if_pos]
      exact ⟨funext fun j => (superInv_spec B hB W hW htwin ξ ξ' hξ h a j).symm,
        funext fun j => (superInv_spec B hB W hW htwin ξ ξ' hξ h b j).symm⟩
    · intro p _ hp
      have hfalse : ¬ ((fun j => B (superMap ξ ξ' hξ j) p.1) = (fun j => B j a) ∧
          (fun j => B (superMap ξ ξ' hξ j) p.2) = (fun j => B j b)) := by
        rintro ⟨hp1, hp2⟩
        exact hp (Prod.ext
          (superInv_unique B hB W hW htwin ξ ξ' hξ h (fun j => (congrFun hp1 j).symm))
          (superInv_unique B hB W hW htwin ξ ξ' hξ h (fun j => (congrFun hp2 j).symm)))
      rw [if_neg hfalse]
    · intro hc; exact absurd (Finset.mem_univ _) hc
  have hpb := aligned_edge_moments_pair_balance B hB W ξ ξ' hξ h (fun j => B j a) (fun j => B j b)
  rw [hLHS, hRHS, superInv_preserves_W B hB W hW htwin ξ ξ' hξ h a,
    superInv_preserves_W B hB W hW htwin ξ ξ' hξ h b] at hpb
  have hpos : W a * W b ≠ 0 := ne_of_gt (mul_pos (hW a) (hW b))
  exact (mul_left_cancel₀ hpos hpb).symm

/-- **`superInv = superMap`.** Support gives `B a b = B (superMap a) (superInv b)`, and edge
preservation gives `B a b = B (superInv a) (superInv b)`; comparing over all columns
(`superInv` surjective) and applying twin-freeness identifies the two maps. -/
theorem superInv_eq_superMap {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ v, 0 < W v) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ) (h : TestEvalEq B W ξ ξ') :
    superInv B hB W hW htwin ξ ξ' hξ h = superMap ξ ξ' hξ := by
  funext a
  have hrow : B (superMap ξ ξ' hξ a) = B (superInv B hB W hW htwin ξ ξ' hξ h a) := by
    funext w
    obtain ⟨b, hb⟩ := (superInv_bijective B hB W hW htwin ξ ξ' hξ h).surjective w
    rw [← hb, ← superInv_spec B hB W hW htwin ξ ξ' hξ h b a]
    exact (superInv_preserves_B B hB W hW htwin ξ ξ' hξ h a b).symm
  by_contra hne
  exact (htwin (superMap ξ ξ' hξ a) (superInv B hB W hW htwin ξ ξ' hξ h a)
    (fun heq => hne heq.symm)) hrow

/-! ### Chunk 3A.5 exports: superMap is a weighted automorphism -/

theorem superMap_preserves_B {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ v, 0 < W v) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ) (h : TestEvalEq B W ξ ξ') (a b : Fin T) :
    B (superMap ξ ξ' hξ a) (superMap ξ ξ' hξ b) = B a b := by
  rw [← superInv_eq_superMap B hB W hW htwin ξ ξ' hξ h]
  exact superInv_preserves_B B hB W hW htwin ξ ξ' hξ h a b

theorem superMap_preserves_W {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ v, 0 < W v) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ) (h : TestEvalEq B W ξ ξ') (a : Fin T) :
    W (superMap ξ ξ' hξ a) = W a := by
  rw [← superInv_eq_superMap B hB W hW htwin ξ ξ' hξ h]
  exact superInv_preserves_W B hB W hW htwin ξ ξ' hξ h a

/-- **The super-surjective orbit automorphism.** `superPerm` is a weighted automorphism of
`(B, W)` — the certified output of chunk 3A.5. -/
theorem superMap_isWeightedAutomorphism {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ v, 0 < W v) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ) (h : TestEvalEq B W ξ ξ') :
    IsWeightedAutomorphism B W (superPerm B hB W hW htwin ξ ξ' hξ h) := by
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · rw [superPerm_apply]; exact superMap_preserves_W B hB W hW htwin ξ ξ' hξ h i
  · rw [superPerm_apply, superPerm_apply]; exact superMap_preserves_B B hB W hW htwin ξ ξ' hξ h i j

/-- **One-extra-label raw moment identity.** Attaching a single distinguished label `i₀` to a
star-test graph and selecting disjoint exponent blocks inside the (large) super-fibres minus
`{i₀}`, the `tupleEquivSimple` equality on the star graph yields the raw moment identity with one
extra `B (ξ i₀) t` / `B (ξ' i₀) t` factor. Reindexing the right-hand side by the orbit permutation
`superMap` (which preserves `W` and `B`) turns `B (ξ' i₀) t` into `B (ξ' i₀) (superMap t)` while
restoring the aligned exponent product `∏ⱼ (B j t) ^ k j`. -/
theorem one_extra_label_moment {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ v, 0 < W v) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ) (h : TestEvalEq B W ξ ξ') (i₀ : Fin K)
    (k : Fin T → ℕ) (hk : ∀ j, k j < T) :
    ∑ t, W t * B (ξ i₀) t * ∏ j, (B j t) ^ k j
      = ∑ t, W t * B (ξ' i₀) (superMap ξ ξ' hξ t) * ∏ j, (B j t) ^ k j := by
  classical
  -- Each super-fibre minus `{i₀}` is still large enough to hold `k j` labels.
  have hbound : ∀ j, k j ≤ (superFiberSubset ξ ξ' hξ j \ {i₀}).card := by
    intro j
    have h1 := superFiberSubset_card ξ ξ' hξ j
    have h2 : (superFiberSubset ξ ξ' hξ j).card
        ≤ (superFiberSubset ξ ξ' hξ j \ {i₀}).card + ({i₀} : Finset (Fin K)).card :=
      Finset.card_le_card_sdiff_add_card
    have h3 : ({i₀} : Finset (Fin K)).card = 1 := Finset.card_singleton i₀
    have h4 := hk j
    omega
  choose Kf hKf_sub hKf_card using fun j =>
    Finset.exists_subset_card_eq (s := superFiberSubset ξ ξ' hξ j \ {i₀}) (n := k j) (hbound j)
  have hKf_sub' : ∀ j, Kf j ⊆ superFiberSubset ξ ξ' hξ j :=
    fun j => (hKf_sub j).trans Finset.sdiff_subset
  have hi₀ : i₀ ∉ univ.biUnion Kf := by
    intro hmem
    rw [Finset.mem_biUnion] at hmem
    obtain ⟨j, -, hj⟩ := hmem
    have hj' := hKf_sub j hj
    rw [Finset.mem_sdiff] at hj'
    exact hj'.2 (Finset.mem_singleton_self i₀)
  have hdisj : Set.PairwiseDisjoint (↑(univ : Finset (Fin T))) Kf :=
    fun j _ j' _ hjj => Finset.disjoint_of_subset_left (hKf_sub' j)
      (Finset.disjoint_of_subset_right (hKf_sub' j') (superFiberSubset_disjoint ξ ξ' hξ hjj))
  have hLHS : ∀ t, ∏ i ∈ univ.biUnion Kf, B (ξ i) t = ∏ j, (B j t) ^ k j := fun t =>
    prod_biUnion_const hdisj
      (fun j i hi => by rw [superFiberSubset_mem_left ξ ξ' hξ j (hKf_sub' j hi)]) hKf_card
  have hRHS : ∀ t, ∏ i ∈ univ.biUnion Kf, B (ξ' i) t
      = ∏ j, (B (superMap ξ ξ' hξ j) t) ^ k j := fun t =>
    prod_biUnion_const hdisj
      (fun j i hi => by rw [superFiberSubset_image_const ξ ξ' hξ j i (hKf_sub' j hi)]) hKf_card
  -- The star-test equality on `S = insert i₀ (⋃ⱼ Kf j)`.
  have heq : simpleEvalAt B W (starTestGraph (insert i₀ (univ.biUnion Kf))) ξ
      = simpleEvalAt B W (starTestGraph (insert i₀ (univ.biUnion Kf))) ξ' :=
    h.star (insert i₀ (univ.biUnion Kf))
  rw [simpleEvalAt_starTestGraph B hB W _ ξ, simpleEvalAt_starTestGraph B hB W _ ξ'] at heq
  -- Phase A: raw moment identity with one extra `i₀` factor.
  have phaseA : ∑ t, W t * B (ξ i₀) t * ∏ j, (B j t) ^ k j
      = ∑ t, W t * B (ξ' i₀) t * ∏ j, (B (superMap ξ ξ' hξ j) t) ^ k j := by
    calc ∑ t, W t * B (ξ i₀) t * ∏ j, (B j t) ^ k j
        = ∑ t, W t * ∏ i ∈ insert i₀ (univ.biUnion Kf), B (ξ i) t := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.prod_insert hi₀, hLHS t]; ring
      _ = ∑ t, W t * ∏ i ∈ insert i₀ (univ.biUnion Kf), B (ξ' i) t := heq
      _ = ∑ t, W t * B (ξ' i₀) t * ∏ j, (B (superMap ξ ξ' hξ j) t) ^ k j := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.prod_insert hi₀, hRHS t]; ring
  -- Phase B: reindex the right-hand side by the orbit permutation `superMap`.
  have phaseB : ∑ t, W t * B (ξ' i₀) t * ∏ j, (B (superMap ξ ξ' hξ j) t) ^ k j
      = ∑ t, W t * B (ξ' i₀) (superMap ξ ξ' hξ t) * ∏ j, (B j t) ^ k j := by
    rw [← Equiv.sum_comp (superPerm B hB W hW htwin ξ ξ' hξ h)
      (fun t => W t * B (ξ' i₀) t * ∏ j, (B (superMap ξ ξ' hξ j) t) ^ k j)]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [superPerm_apply]
    rw [superMap_preserves_W B hB W hW htwin ξ ξ' hξ h u]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [superMap_preserves_B B hB W hW htwin ξ ξ' hξ h j u]
  exact phaseA.trans phaseB

/-- **Full-fibre reconciliation (3A.6).** Every label `i` maps under `ξ'` to `superMap (ξ i)` —
not only the labels in the selected subsets. The one-extra-label moment identity feeds the
(graph-free) Vandermonde class-sum over `Fin T`: twin-freeness makes each profile fibre a
singleton, positivity gives `B (ξ i₀) t = B (ξ' i₀) (superMap t)` for all `t`, and applying the
automorphism property identifies `ξ' i₀ = superMap (ξ i₀)`. -/
theorem superMap_agrees_on_all_labels {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ v, 0 < W v) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ) (h : TestEvalEq B W ξ ξ') :
    ∀ i : Fin K, ξ' i = superMap ξ ξ' hξ (ξ i) := by
  intro i₀
  have hmom : ∀ k : Fin T → ℕ, (∀ j, k j < T) →
      ∑ t, (W t * (B (ξ i₀) t - B (ξ' i₀) (superMap ξ ξ' hξ t))) * ∏ j, (B j t) ^ k j = 0 := by
    intro k hk
    have heq := one_extra_label_moment B hB W hW htwin ξ ξ' hξ h i₀ k hk
    have hsplit : ∑ t, (W t * (B (ξ i₀) t - B (ξ' i₀) (superMap ξ ξ' hξ t))) * ∏ j, (B j t) ^ k j
        = (∑ t, W t * B (ξ i₀) t * ∏ j, (B j t) ^ k j)
          - (∑ t, W t * B (ξ' i₀) (superMap ξ ξ' hξ t) * ∏ j, (B j t) ^ k j) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun t _ => ?_); ring
    rw [hsplit, heq, sub_self]
  have hstar : ∀ t, B (ξ i₀) t = B (ξ' i₀) (superMap ξ ξ' hξ t) := by
    intro t₀
    have hclass := CaiGovorov.multivariate_vandermonde_class_sums_zero
      (fun t => fun j => B j t)
      (fun t => W t * (B (ξ i₀) t - B (ξ' i₀) (superMap ξ ξ' hξ t)))
      (fun ℓ hℓ => hmom ℓ (fun j => Fintype.card_fin T ▸ hℓ j)) (fun j => B j t₀)
    have hfilt : (univ.filter (fun t => (fun j => B j t) = (fun j => B j t₀))) = {t₀} := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hcol
        by_contra hne
        refine htwin t t₀ hne ?_
        funext j; have hj := congrFun hcol j; rw [hB t j, hB t₀ j]; exact hj
      · rintro rfl; rfl
    rw [hfilt, Finset.sum_singleton] at hclass
    rcases mul_eq_zero.mp hclass with h0 | h0
    · exact absurd h0 (ne_of_gt (hW t₀))
    · exact sub_eq_zero.mp h0
  by_contra hne
  refine htwin (superMap ξ ξ' hξ (ξ i₀)) (ξ' i₀) (fun heq => hne heq.symm) ?_
  funext u
  obtain ⟨t, ht⟩ := (superMap_bijective B hB W hW htwin ξ ξ' hξ h).surjective u
  rw [← ht, superMap_preserves_B B hB W hW htwin ξ ξ' hξ h (ξ i₀) t]
  exact hstar t

/-- **Chunk 3A core — the super-surjective Cai–Govorov orbit separation, moment form.** If `ξ`
is super-surjective and the star/edge test evaluations agree (`TestEvalEq`), then `ξ'` is in the
weighted-automorphism orbit of `ξ`. Combines `superMap_isWeightedAutomorphism` with the
full-fibre reconciliation. The `TestEvalEq` interface (rather than full `tupleEquivSimple`) is
what the eq. (10) descent step can supply for matched extensions. -/
theorem testEvalEq_implies_orbit_super {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (hW : ∀ v, 0 < W v)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j) (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ)
    (h : TestEvalEq B W ξ ξ') :
    tupleOrbitRel B W ξ ξ' :=
  ⟨superPerm B hB W hW htwin ξ ξ' hξ h,
   superMap_isWeightedAutomorphism B hB W hW htwin ξ ξ' hξ h,
   fun i => by rw [superPerm_apply]; exact superMap_agrees_on_all_labels B hB W hW htwin ξ ξ' hξ h i⟩

/-- **Chunk 3A — the super-surjective Cai–Govorov orbit separation.** If `ξ` is super-surjective
and `ξ ≈ ξ'` (equal simple-graph evaluations), then `ξ'` is in the weighted-automorphism orbit of
`ξ`. Wrapper around the moment-form core `testEvalEq_implies_orbit_super`. -/
theorem tupleEquivSimple_implies_orbit_super {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (hW : ∀ v, 0 < W v)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j) (ξ ξ' : Fin K → Fin T) (hξ : SuperSurjective ξ)
    (h : tupleEquivSimple B W ξ ξ') :
    tupleOrbitRel B W ξ ξ' :=
  testEvalEq_implies_orbit_super B hB W hW htwin ξ ξ' hξ (.of_tupleEquivSimple h)

/-! ## Chunk 3B.1b: iterating the trace over the extra labels

The trace operator `MultiLabeledGraph.trace` folds the *last* label into a new unlabeled
vertex. Iterating it `m` times folds the last `m` labels of a `(K+m)`-labeled multigraph,
yielding a `K`-labeled multigraph on `n + m` unlabeled vertices. The closure identity
`multiLabeledEvalK_sum_last_label` then accumulates into a `W`-weighted sum over the `m`
folded label values (`ρ : Fin m → Fin T`). -/

/-- **Unlabeled re-cast of a multigraph.** Reindex the vertex space `Fin (b + K)` of a target
multigraph onto `Fin (a + K)` through the val-preserving `Fin.cast`, when `a = b`. Used to
reconcile `(n + 1) + m` with `n + (m + 1)` in `traceIterExtraLabels`. -/
def MultiLabeledGraph.castUnlabeled {K a b : ℕ} (hab : a = b) (M : MultiLabeledGraph K a) :
    MultiLabeledGraph K b where
  mult e := M.mult (Sym2.map (Fin.cast (by rw [hab])) e)
  multNoLoop x := by rw [Sym2.map_mk]; exact M.multNoLoop _

/-- The multigraph evaluation is invariant under the val-preserving unlabeled re-cast. -/
theorem multiLabeledEvalK_castUnlabeled {T K a b : ℕ} (hab : a = b)
    (M : MultiLabeledGraph K a) (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (φ : Fin K → Fin T) :
    multiLabeledEvalK K b (M.castUnlabeled hab) B W φ = multiLabeledEvalK K a M B W φ := by
  subst hab
  have hmult : ∀ e : Sym2 (Fin (a + K)), (M.castUnlabeled (rfl : a = a)).mult e = M.mult e := by
    intro e
    refine congrArg M.mult ?_
    refine Sym2.ind (fun x y => ?_) e
    rw [Sym2.map_mk, Fin.cast_eq_self, Fin.cast_eq_self]
  simp only [multiLabeledEvalK]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [hmult e]

/-- **Iterated trace** over the last `m` labels. Folds the last `m` labels of a `(K+m)`-labeled
multigraph into `m` new unlabeled vertices, yielding a `K`-labeled multigraph on `n + m`
unlabeled vertices. Recurses on `m`, threading `MultiLabeledGraph.trace` and reconciling the
`(n+1)+m = n+(m+1)` vertex-count mismatch with `castUnlabeled`. -/
def traceIterExtraLabels {K : ℕ} : ∀ {n : ℕ} (m : ℕ),
    MultiLabeledGraph (K + m) n → MultiLabeledGraph K (n + m)
  | _, 0, M => M
  | n, m + 1, M =>
      (traceIterExtraLabels m M.trace).castUnlabeled (by omega : (n + 1) + m = n + (m + 1))

/-- **Eq. (10) core** (3B.1 pillar). Unpinning the last `m` labels: summing the `(K+m)`-labeled
evaluation over the extra label values `ρ`, weighted by `∏ⱼ W(ρ j)`, equals the `K`-labeled
evaluation of the `m`-fold trace `traceIterExtraLabels m M`. Induction on `m`, peeling the last
label each step via `multiLabeledEvalK_sum_last_label`. Purely multigraph-side; bridged to simple
graphs by `traceIterExtraLabels_ofSimple_eq` and fed into `extension_sum_identity`. -/
theorem multiLabeledEvalK_sum_extra_labels {K m n T : ℕ}
    (M : MultiLabeledGraph (K + m) n) (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (φ : Fin K → Fin T) :
    ∑ ρ : Fin m → Fin T,
        (∏ j : Fin m, W (ρ j)) * multiLabeledEvalK (K + m) n M B W (Fin.append φ ρ)
      = multiLabeledEvalK K (n + m) (traceIterExtraLabels m M) B W φ := by
  induction m generalizing n with
  | zero =>
    rw [Fintype.sum_unique, Fin.prod_univ_zero, one_mul]
    have happ : Fin.append φ (default : Fin 0 → Fin T) = φ := by
      rw [Fin.append_right_nil φ _ rfl]
      funext v
      exact congrArg φ (Fin.ext rfl)
    rw [happ]
    rfl
  | succ m ih =>
    have hcast : multiLabeledEvalK K (n + (m + 1)) (traceIterExtraLabels (m + 1) M) B W φ
        = multiLabeledEvalK K ((n + 1) + m) (traceIterExtraLabels m M.trace) B W φ := by
      rw [show traceIterExtraLabels (m + 1) M
            = (traceIterExtraLabels m M.trace).castUnlabeled
                (by omega : (n + 1) + m = n + (m + 1)) from rfl]
      rw [multiLabeledEvalK_castUnlabeled]
    rw [hcast, ← ih M.trace]
    -- Normalize the label count `K + (m+1)` to `K + m + 1` to align with `sum_last_label`.
    show ∑ ρ : Fin (m + 1) → Fin T,
        (∏ j : Fin (m + 1), W (ρ j)) *
          multiLabeledEvalK (K + m + 1) n M B W (@Fin.append K (m + 1) (Fin T) φ ρ)
      = ∑ ρ : Fin m → Fin T,
        (∏ j : Fin m, W (ρ j)) *
          multiLabeledEvalK (K + m) (n + 1) M.trace B W (Fin.append φ ρ)
    -- Split the last folded label `x` off `ρ = Fin.snoc ρ₀ x`.
    have hsnocEq : ∀ p : Fin T × (Fin m → Fin T),
        (Fin.snocEquiv (fun _ : Fin (m + 1) => Fin T)) p = Fin.snoc p.2 p.1 :=
      fun p => funext fun x => Fin.snocEquiv_apply (fun _ : Fin (m + 1) => Fin T) p x
    rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (m + 1) => Fin T)),
        Fintype.sum_prod_type]
    simp only [hsnocEq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ρ₀ _ => ?_
    simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fin.append_snoc]
    have hlast : ∑ x : Fin T,
        W x * multiLabeledEvalK (K + m + 1) n M B W (Fin.snoc (Fin.append φ ρ₀) x)
      = multiLabeledEvalK (K + m) (n + 1) M.trace B W (Fin.append φ ρ₀) :=
      multiLabeledEvalK_sum_last_label M B hB W (Fin.append φ ρ₀)
    rw [← hlast, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring

/-! ## Chunk 3B.1c step 2: the trace-to-simple eval bridge -/

/-- Local (public) connector: `simpleEvalAt` is `multiLabeledEvalK` on `ofSimple`
(the file-local analog of the private `simpleEvalAt_eq_multi` in `Lovasz`). -/
theorem simpleEvalAt_eq_multi' {T K n : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (F : SimpleGraph (Fin (n + K))) [DecidableRel F.Adj] (ξ : Fin K → Fin T) :
    simpleEvalAt B W F ξ = multiLabeledEvalK K n (MultiLabeledGraph.ofSimple F) B W ξ := by
  rw [multiLabeledEvalK_ofSimple]; rfl

/-- **Unlabel-extras simple graph.** Comap of `G` along the val-preserving cast
`Fin ((n + m) + K) → Fin (n + (K + m))`, moving the last `m` labels back into unlabeled
position. The trace bridge (`traceIterExtraLabels_ofSimple_eq`) identifies
`traceIterExtraLabels m (ofSimple G)` with `ofSimple (unlabelExtras G)`. -/
def unlabelExtras {K m n : ℕ} (G : SimpleGraph (Fin (n + (K + m)))) :
    SimpleGraph (Fin ((n + m) + K)) :=
  SimpleGraph.comap (Fin.cast (by omega : (n + m) + K = n + (K + m))) G

noncomputable instance {K m n} (G : SimpleGraph (Fin (n + (K + m)))) [DecidableRel G.Adj] :
    DecidableRel (unlabelExtras G).Adj := Classical.decRel _

/-- **Net-cast lemma** (the crux). The iterated `trace`/`castUnlabeled` reindexing collapses to
a single val-preserving `Fin.cast`: reading a multiplicity of `traceIterExtraLabels m M` at `e`
equals reading `M`'s multiplicity at the cast of `e`. -/
theorem traceIterExtraLabels_mult {K : ℕ} : ∀ {n : ℕ} (m : ℕ) (M : MultiLabeledGraph (K + m) n)
    (e : Sym2 (Fin ((n + m) + K))),
    (traceIterExtraLabels m M).mult e
      = M.mult (Sym2.map (Fin.cast (by omega : (n + m) + K = n + (K + m))) e) := by
  intro n m
  induction m generalizing n with
  | zero =>
    intro M e
    refine e.ind fun x y => ?_
    show M.mult s(x, y) = M.mult (Sym2.map (Fin.cast _) s(x, y))
    rw [Sym2.map_mk]
    congr 1
  | succ m ih =>
    intro M e
    rw [show traceIterExtraLabels (m + 1) M
          = (traceIterExtraLabels m M.trace).castUnlabeled
              (by omega : (n + 1) + m = n + (m + 1)) from rfl]
    refine e.ind fun x y => ?_
    show (traceIterExtraLabels m M.trace).mult (Sym2.map (Fin.cast _) s(x, y))
        = M.mult (Sym2.map (Fin.cast _) s(x, y))
    rw [ih M.trace]
    show M.mult (Sym2.map (Fin.cast _) (Sym2.map (Fin.cast _) (Sym2.map (Fin.cast _) s(x, y))))
        = M.mult (Sym2.map (Fin.cast _) s(x, y))
    rw [Sym2.map_mk, Sym2.map_mk, Sym2.map_mk, Sym2.map_mk]
    congr 1

/-- **Graph bridge.** Iterating the trace over the extra labels of an `ofSimple` multigraph
yields the `ofSimple` multigraph of the unlabel-extras simple graph. -/
theorem traceIterExtraLabels_ofSimple_eq {K m n : ℕ} (G : SimpleGraph (Fin (n + (K + m))))
    [DecidableRel G.Adj] :
    traceIterExtraLabels m (MultiLabeledGraph.ofSimple G)
      = MultiLabeledGraph.ofSimple (unlabelExtras G) := by
  have hiff : ∀ e : Sym2 (Fin ((n + m) + K)),
      (Sym2.map (Fin.cast (by omega : (n + m) + K = n + (K + m))) e) ∈ G.edgeFinset
        ↔ e ∈ (unlabelExtras G).edgeFinset := by
    refine fun e => e.ind fun u v => ?_
    rw [Sym2.map_mk]
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, unlabelExtras,
      SimpleGraph.comap_adj]
  have hmult : ∀ e, (traceIterExtraLabels m (MultiLabeledGraph.ofSimple G)).mult e
      = (MultiLabeledGraph.ofSimple (unlabelExtras G)).mult e := by
    intro e
    rw [traceIterExtraLabels_mult]
    show (if (Sym2.map (Fin.cast _) e) ∈ G.edgeFinset then (1 : ℕ) else 0)
        = (if e ∈ (unlabelExtras G).edgeFinset then (1 : ℕ) else 0)
    rw [if_congr (hiff e) rfl rfl]
  rcases hG : MultiLabeledGraph.ofSimple (unlabelExtras G) with ⟨mu, mnu⟩
  rcases hT : traceIterExtraLabels m (MultiLabeledGraph.ofSimple G) with ⟨mt, mnt⟩
  show MultiLabeledGraph.mk _ _ = MultiLabeledGraph.mk _ _
  congr 1
  funext e
  have := hmult e
  rw [hG, hT] at this
  exact this

/-- **Eval bridge** (the step-2 target). Evaluating the traced `ofSimple G` multigraph equals the
simple-graph evaluation of the unlabel-extras graph. -/
theorem traceIterExtraLabels_ofSimple_eval {T K m n : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (G : SimpleGraph (Fin (n + (K + m)))) [DecidableRel G.Adj] (ξ : Fin K → Fin T) :
    multiLabeledEvalK K (n + m) (traceIterExtraLabels m (MultiLabeledGraph.ofSimple G)) B W ξ
      = simpleEvalAt B W (unlabelExtras G) ξ := by
  rw [traceIterExtraLabels_ofSimple_eq, ← simpleEvalAt_eq_multi']

/-! ### Chunk 3B.1c steps 3–5: extension family (extras-last) and equation (10) -/

/-- `μ : Fin (K + m) → Fin T` extends `ξ` if it agrees with `ξ` on the first `K` labels.
(`abbrev` so the subtype `{μ // ExtendsFin ξ μ}` gets `DecidablePred`/`Fintype` automatically.) -/
abbrev ExtendsFin {T m : ℕ} (ξ : Fin K → Fin T) (μ : Fin (K + m) → Fin T) : Prop :=
  ∀ i : Fin K, μ (Fin.castAdd m i) = ξ i

/-- The `W`-product over the `m` extra label values of `μ`. -/
noncomputable def extensionWeightFin {T m : ℕ} (W : Fin T → ℝ) (μ : Fin (K + m) → Fin T) : ℝ :=
  ∏ j : Fin m, W (μ (Fin.natAdd K j))

/-- Extensions of `ξ` are exactly `Fin.append ξ ρ` for the free extra-value tuple `ρ`. -/
def appendExtensionEquiv {T m : ℕ} (ξ : Fin K → Fin T) :
    (Fin m → Fin T) ≃ {μ : Fin (K + m) → Fin T // ExtendsFin ξ μ} where
  toFun ρ := ⟨Fin.append ξ ρ, by intro i; rw [Fin.append_left]⟩
  invFun μ := fun j => μ.1 (Fin.natAdd K j)
  left_inv ρ := by
    funext j
    show Fin.append ξ ρ (Fin.natAdd K j) = ρ j
    rw [Fin.append_right]
  right_inv μ := by
    apply Subtype.ext
    funext k
    show Fin.append ξ (fun j => μ.1 (Fin.natAdd K j)) k = μ.1 k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [Fin.append_left]; exact (μ.2 i).symm
    · rw [Fin.append_right]

theorem sum_extensions_eq_sum_rho {T m n : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (G : SimpleGraph (Fin (n + (K + m)))) [DecidableRel G.Adj] (ξ : Fin K → Fin T) :
    ∑ μ : {μ : Fin (K + m) → Fin T // ExtendsFin ξ μ},
        extensionWeightFin W μ.1 * simpleEvalAt B W G μ.1
      = ∑ ρ : Fin m → Fin T, (∏ j, W (ρ j)) * simpleEvalAt B W G (Fin.append ξ ρ) := by
  rw [← Equiv.sum_comp (appendExtensionEquiv ξ)
    (fun μ => extensionWeightFin W μ.1 * simpleEvalAt B W G μ.1)]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  show extensionWeightFin W (Fin.append ξ ρ) * simpleEvalAt B W G (Fin.append ξ ρ)
    = (∏ j, W (ρ j)) * simpleEvalAt B W G (Fin.append ξ ρ)
  congr 1
  unfold extensionWeightFin
  exact Finset.prod_congr rfl (fun j _ => by rw [Fin.append_right])

/-- **Equation (10)** (Cai–Govorov, the extension-family sum identity). Simple-equivalence at
level `K` lifts to an equality of extension-family sums at level `K + m`: unpinning the extra
labels (trace-to-simple bridge) reduces both sides to `simpleEvalAt` of `unlabelExtras G`, where
`h` applies. -/
theorem extension_sum_identity {T m n : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) {ξ ξ' : Fin K → Fin T} (h : tupleEquivSimple B W ξ ξ')
    (G : SimpleGraph (Fin (n + (K + m)))) [DecidableRel G.Adj] :
    ∑ μ : {μ : Fin (K + m) → Fin T // ExtendsFin ξ μ},
        extensionWeightFin W μ.1 * simpleEvalAt B W G μ.1
      = ∑ ν : {ν : Fin (K + m) → Fin T // ExtendsFin ξ' ν},
          extensionWeightFin W ν.1 * simpleEvalAt B W G ν.1 := by
  have hbridge : ∀ ζ : Fin K → Fin T,
      ∑ μ : {μ : Fin (K + m) → Fin T // ExtendsFin ζ μ},
          extensionWeightFin W μ.1 * simpleEvalAt B W G μ.1
        = simpleEvalAt B W (unlabelExtras G) ζ := by
    intro ζ
    rw [sum_extensions_eq_sum_rho B W G ζ,
      show (∑ ρ : Fin m → Fin T, (∏ j, W (ρ j)) * simpleEvalAt B W G (Fin.append ζ ρ))
          = ∑ ρ : Fin m → Fin T, (∏ j, W (ρ j)) *
              multiLabeledEvalK (K + m) n (MultiLabeledGraph.ofSimple G) B W (Fin.append ζ ρ) from
        Finset.sum_congr rfl (fun ρ _ => by rw [simpleEvalAt_eq_multi']),
      multiLabeledEvalK_sum_extra_labels (MultiLabeledGraph.ofSimple G) B hB W ζ,
      traceIterExtraLabels_ofSimple_eval B W G ζ]
  rw [hbridge ξ, hbridge ξ']
  exact h (n + m) (unlabelExtras G)

/-! ### Chunk 3B.2a: the concrete super-surjective extension of `ξ` (extras-last) -/

/-- The extra-value tuple that maps `2*T²` labels to each host vertex. Uses the product equiv
`Fin T × Fin (2*T²) ≃ Fin (T * (2*T²))`: label `j` maps to the vertex component of `j`. -/
noncomputable def coverExtra (T : ℕ) : Fin (T * (2 * T ^ 2)) → Fin T :=
  fun j => (finProdFinEquiv.symm j).1

/-- The canonical super-surjective extension of `ξ`: keep `ξ` on the first `K` labels, then add
`T * (2*T²)` extra labels covering every host vertex `2*T²` times. -/
noncomputable def superExt {T : ℕ} (ξ : Fin K → Fin T) :
    Fin (K + T * (2 * T ^ 2)) → Fin T :=
  Fin.append ξ (coverExtra T)

theorem superExt_extends {T : ℕ} (ξ : Fin K → Fin T) :
    ExtendsFin ξ (superExt ξ) := by
  intro i; rw [superExt, Fin.append_left]

theorem coverExtra_fiber_card {T : ℕ} (v : Fin T) :
    (univ.filter (fun j => coverExtra T j = v)).card = 2 * T ^ 2 := by
  classical
  have hg_inj : Function.Injective
      (fun c : Fin (2 * T ^ 2) => finProdFinEquiv (v, c)) := by
    intro c₁ c₂ h
    exact congrArg Prod.snd (finProdFinEquiv.injective h)
  have hset : univ.filter (fun j => coverExtra T j = v)
      = univ.image (fun c : Fin (2 * T ^ 2) => finProdFinEquiv (v, c)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hj
      simp only [coverExtra] at hj
      refine ⟨(finProdFinEquiv.symm j).2, ?_⟩
      rw [← hj]
      exact finProdFinEquiv.apply_symm_apply j
    · rintro ⟨c, rfl⟩
      simp only [coverExtra, Equiv.symm_apply_apply]
  rw [hset, Finset.card_image_of_injective _ hg_inj, Finset.card_univ, Fintype.card_fin]

theorem superExt_superSurjective {T : ℕ} (ξ : Fin K → Fin T) :
    SuperSurjective (superExt ξ) := by
  intro v
  classical
  have hsub : (univ.filter (fun j => coverExtra T j = v)).image (Fin.natAdd K)
      ⊆ univ.filter (fun i => superExt ξ i = v) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    show superExt ξ (Fin.natAdd K j) = v
    rw [superExt, Fin.append_right]
    exact hj.2
  have hcard : ((univ.filter (fun j => coverExtra T j = v)).image (Fin.natAdd K)).card
      = 2 * T ^ 2 := by
    rw [Finset.card_image_of_injective _ (Fin.natAdd_injective (T * (2 * T ^ 2)) K),
      coverExtra_fiber_card]
  have hle : 2 * T ^ 2 ≤ (univ.filter (fun i => superExt ξ i = v)).card := by
    have hcle := Finset.card_le_card hsub
    rwa [hcard] at hcle
  calc 2 * T * T = 2 * T ^ 2 := by ring
    _ ≤ _ := hle

/-! ### Chunk 3B.2b: separation (contrapositive of the super-surjective case) -/

/-- **Separation (Cai–Govorov Lemma 10).** Since `superExt ξ` is super-surjective, any extension
`μ` not in its weighted-automorphism orbit is *not* simple-equivalent to it — i.e. some simple
graph separates them. This is the contrapositive of `tupleEquivSimple_implies_orbit_super` applied
to the reference extension `η = superExt ξ`, and it is the oracle that builds the finite separating
family in the counting/Vandermonde step. -/
theorem not_tupleEquivSimple_of_not_orbit {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (hW : ∀ v, 0 < W v)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j) (ξ : Fin K → Fin T)
    (μ : Fin (K + T * (2 * T ^ 2)) → Fin T)
    (hnotorbit : ¬ tupleOrbitRel B W (superExt ξ) μ) :
    ¬ tupleEquivSimple B W (superExt ξ) μ :=
  fun heq => hnotorbit (tupleEquivSimple_implies_orbit_super B hB W hW htwin (superExt ξ) μ
    (superExt_superSurjective ξ) heq)

end Graphon.Lovasz
