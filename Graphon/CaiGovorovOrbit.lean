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

end Graphon.Lovasz
