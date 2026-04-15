/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Algebraic Determination for Finite Matrices

This file states the algebraic core of the inverse counting lemma:
symmetric matrices with entries in [0,1] that yield equal weighted homomorphism
sums for all finite graphs are related by a permutation of indices.

This is a purely finite, combinatorial statement with no measure theory.

## Main definitions

* `Graphon.weightedHomSum` - Weighted homomorphism sum for a finite matrix

## Main results

* `Graphon.matrix_quotient_of_weightedHomSum_eq` - Equal weighted hom sums imply
  quotient equivalence: matching block-constant type classes with equal weights
  (Lovász [2012] Theorem 5.30, correct weighted formulation)

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Section 5.2
-/

open Finset Matrix

namespace Graphon

/-! ### Vandermonde corollary -/

/-- If ∑ aᵢ · sᵢⁿ = 0 for all n < L (where sᵢ are distinct), then all aᵢ = 0. -/
private theorem eq_zero_of_weighted_powers_eq_zero {L : ℕ}
    (s : Fin L → ℝ) (hs : Function.Injective s)
    (a : Fin L → ℝ) (h : ∀ n : Fin L, ∑ l, a l * s l ^ (n : ℕ) = 0) : a = 0 := by
  by_contra ha
  have hdet : (vandermonde s).det ≠ 0 := det_vandermonde_ne_zero_iff.mpr hs
  have hvec : vecMul a (vandermonde s) = 0 := by
    ext j; simp only [vecMul, dotProduct, vandermonde_apply, Pi.zero_apply]
    convert h j using 1
  exact hdet (exists_vecMul_eq_zero_iff.mp ⟨a, ha, hvec⟩)

/-! ### Weighted homomorphism sum -/

/-- Weighted homomorphism sum for a finite matrix.

For a graph `F` on `Fin n`, a matrix `c : Fin k → Fin k → ℝ`, and
weights `w : Fin k → ℝ`:

`weightedHomSum n F c w = ∑ σ : Fin n → Fin k,
    (∏ v, w (σ v)) * ∏ e ∈ F.edgeFinset, c (σ e.1) (σ e.2)`

This is the finite analog of graphon homomorphism density `t(F, W)`,
where `c` plays the role of the graphon kernel and `w` the cell measures. -/
noncomputable def weightedHomSum {k : ℕ} (n : ℕ) (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (c : Fin k → Fin k → ℝ) (w : Fin k → ℝ) : ℝ :=
  ∑ σ : Fin n → Fin k,
    (∏ v : Fin n, w (σ v)) *
    ∏ e ∈ F.edgeFinset, c (σ (Quot.out e).1) (σ (Quot.out e).2)

/-- `weightedHomSum` is independent of the `DecidableRel` instance. -/
theorem weightedHomSum_congr_decRel {k : ℕ} (n : ℕ) (F : SimpleGraph (Fin n))
    (inst₁ inst₂ : DecidableRel F.Adj) (c : Fin k → Fin k → ℝ) (w : Fin k → ℝ) :
    @weightedHomSum k n F inst₁ c w = @weightedHomSum k n F inst₂ c w := by
  unfold weightedHomSum
  congr 1; ext σ; congr 1; congr 1
  apply Finset.ext; intro e
  simp only [SimpleGraph.mem_edgeFinset]

/-! ### Weighted degree and star graphs -/

/-- The weighted degree of index `i` in matrix `c` with weights `w`:
`wDeg c w i = ∑ j, w j * c i j`. -/
noncomputable def wDeg {k : ℕ} (c : Fin k → Fin k → ℝ) (w : Fin k → ℝ)
    (i : Fin k) : ℝ :=
  ∑ j, w j * c i j

/-- Star graph on m+1 vertices: vertex 0 is adjacent to vertices 1, ..., m. -/
def starGraph (m : ℕ) : SimpleGraph (Fin (m + 1)) where
  Adj u v := (u = 0 ∧ v ≠ 0) ∨ (u ≠ 0 ∧ v = 0)
  symm := fun {u v} h => by
    rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> [right; left] <;> exact ⟨hv, hu⟩
  loopless := fun v h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 h1
    · exact h1 h2

instance starGraphDecRel (m : ℕ) : DecidableRel (starGraph m).Adj :=
  fun u v => inferInstanceAs (Decidable ((u = 0 ∧ v ≠ 0) ∨ (u ≠ 0 ∧ v = 0)))

/-! ### Row profile and permutation equivalence -/

/-- The row profile of index `i` captures all "higher-order degree" information:
`rowProfile c w i m = ∑ j, w j * c(i,j) * (wDeg c w j)^m`.

Two indices i, i' have the same "type" iff `rowProfile c w i = rowProfile c w i'`
for all m. The key property: caterpillar graph tests extract these profiles,
and Vandermonde injectivity shows that matching profiles implies matching rows
up to permutation within each type class. -/
noncomputable def rowProfile {k : ℕ} (c : Fin k → Fin k → ℝ)
    (w : Fin k → ℝ) (i : Fin k) (m : ℕ) : ℝ :=
  ∑ j, w j * c i j * (wDeg c w j) ^ m

/-- `weightedHomSum` for a permuted matrix.

If π is a permutation, then evaluating `weightedHomSum` on the permuted
matrix `c' i j := c (π⁻¹ i) (π⁻¹ j)` with permuted weights
`w' i := w (π⁻¹ i)` gives the same result as the original.

This is the key equivariance property of the weighted hom sum. -/
theorem weightedHomSum_perm_eq {k : ℕ} (n : ℕ) (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (c : Fin k → Fin k → ℝ) (w : Fin k → ℝ)
    (π : Equiv.Perm (Fin k)) :
    weightedHomSum n F (fun i j => c (π.symm i) (π.symm j))
      (fun i => w (π.symm i)) = weightedHomSum n F c w := by
  simp only [weightedHomSum]
  -- Reindex the sum by composing σ with π
  rw [← Equiv.sum_comp (Equiv.piCongrRight (fun _ => π))]
  congr 1; ext σ; congr 1
  · congr 1; ext v; simp [Equiv.piCongrRight]
  · congr 1; ext e; simp [Equiv.piCongrRight]

/-! ### Star graph formula -/

/-- The edge finset of `starGraph m` consists of the edges `s(0, j.succ)` for `j : Fin m`. -/
private theorem starGraph_edgeFinset (m : ℕ) :
    (starGraph m).edgeFinset =
      (Finset.univ : Finset (Fin m)).image
        (fun j => s((0 : Fin (m + 1)), j.succ)) := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      simp only [starGraph] at he
      rcases he with ⟨rfl, hb⟩ | ⟨ha, rfl⟩
      · exact ⟨b.pred hb, by simp [Fin.succ_pred]⟩
      · exact ⟨a.pred ha, by rw [Sym2.eq_swap]; simp [Fin.succ_pred]⟩
  · rintro ⟨j, rfl⟩
    rw [SimpleGraph.mem_edgeSet]
    exact Or.inl ⟨rfl, Fin.succ_ne_zero j⟩

private theorem starEdge_injOn (m : ℕ) :
    Set.InjOn (fun j : Fin m => s((0 : Fin (m + 1)), j.succ))
      ↑(Finset.univ : Finset (Fin m)) := by
  intro j₁ _ j₂ _ h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · exact Fin.succ_injective _ h
  · exact absurd h.symm (Fin.succ_ne_zero j₂)

/-- The edge product over `starGraph m` equals the product over leaf vertices. -/
private theorem starGraph_prod_eq {k : ℕ} (m : ℕ) (c : Fin k → Fin k → ℝ)
    (hc : ∀ i j, c i j = c j i) (σ : Fin (m + 1) → Fin k) :
    ∏ e ∈ (starGraph m).edgeFinset,
      c (σ (Quot.out e).1) (σ (Quot.out e).2) =
    ∏ j : Fin m, c (σ 0) (σ j.succ) := by
  rw [starGraph_edgeFinset, Finset.prod_image (starEdge_injOn m)]
  congr 1; ext j
  have hout := Quot.out_eq s((0 : Fin (m + 1)), j.succ)
  rw [Sym2.mk_eq_mk_iff] at hout
  rcases hout with h | h
  · rw [congr_arg Prod.fst h, congr_arg Prod.snd h]
  · have h1 := congr_arg Prod.fst h; have h2 := congr_arg Prod.snd h
    simp only [Prod.swap] at h1 h2; rw [h1, h2, hc]

set_option maxHeartbeats 800000 in
private theorem weightedHomSum_starGraph {k : ℕ} (m : ℕ) (c : Fin k → Fin k → ℝ)
    (hc : ∀ i j, c i j = c j i) (w : Fin k → ℝ) :
    weightedHomSum (m + 1) (starGraph m) c w =
      ∑ i : Fin k, w i * (wDeg c w i) ^ m := by
  simp only [weightedHomSum, wDeg]
  -- Step 1: Simplify each summand
  suffices h : ∀ σ : Fin (m + 1) → Fin k,
      (∏ v, w (σ v)) *
        ∏ e ∈ (starGraph m).edgeFinset,
          c (σ (Quot.out e).1) (σ (Quot.out e).2) =
      w (σ 0) * ∏ j : Fin m, (w (σ j.succ) * c (σ 0) (σ j.succ)) by
    simp_rw [h]
    -- Step 2: Reindex using consEquiv
    rw [(Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m + 1) => Fin k)) _).symm]
    simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    rw [Fintype.sum_prod_type]
    -- Step 3: Simplify each inner sum
    simp only []
    congr 1; funext i; rw [← Finset.mul_sum]; congr 1; symm
    calc (∑ j : Fin k, w j * c i j) ^ m
        = ∏ _ : Fin m, ∑ l : Fin k, w l * c i l := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = ∑ τ : Fin m → Fin k, ∏ j, w (τ j) * c i (τ j) := by
            rw [← @Finset.sum_prod_piFinset (Fin m) (Fin k) ℝ _ _ _ Finset.univ]
            simp [Fintype.piFinset_univ]
  intro σ
  rw [starGraph_prod_eq m c hc σ, Fin.prod_univ_succ, mul_assoc,
    ← Finset.prod_mul_distrib]

/-! ### Double star graph and bivariate moments -/

/-- Double star graph DS(m, p) on m + p + 2 vertices:
vertex 0 is connected to vertex 1 (bridge) and to vertices 2, ..., m+1 (left leaves);
vertex 1 is connected to vertices m+2, ..., m+p+1 (right leaves). -/
def doubleStarGraph (m p : ℕ) : SimpleGraph (Fin (m + p + 2)) where
  Adj u v :=
    (u.val = 0 ∧ (v.val = 1 ∨ (2 ≤ v.val ∧ v.val ≤ m + 1))) ∨
    (v.val = 0 ∧ (u.val = 1 ∨ (2 ≤ u.val ∧ u.val ≤ m + 1))) ∨
    (u.val = 1 ∧ m + 2 ≤ v.val) ∨
    (v.val = 1 ∧ m + 2 ≤ u.val)
  symm := fun {u v} h => by
    rcases h with h | h | h | h
    · right; left; exact ⟨h.1, h.2⟩
    · left; exact ⟨h.1, h.2⟩
    · right; right; right; exact ⟨h.1, h.2⟩
    · right; right; left; exact ⟨h.1, h.2⟩
  loopless := fun v h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases h2 with h2 | ⟨h2, _⟩ <;> omega
    · rcases h2 with h2 | ⟨h2, _⟩ <;> omega
    · omega
    · omega

instance doubleStarGraphDecRel (m p : ℕ) : DecidableRel (doubleStarGraph m p).Adj :=
  fun u v => inferInstanceAs (Decidable
    ((u.val = 0 ∧ (v.val = 1 ∨ (2 ≤ v.val ∧ v.val ≤ m + 1))) ∨
     (v.val = 0 ∧ (u.val = 1 ∨ (2 ≤ u.val ∧ u.val ≤ m + 1))) ∨
     (u.val = 1 ∧ m + 2 ≤ v.val) ∨
     (v.val = 1 ∧ m + 2 ≤ u.val)))

/-! ### Double star formula -/

private theorem doubleStarGraph_edgeFinset (m p : ℕ) :
    (doubleStarGraph m p).edgeFinset =
      {s((0 : Fin (m+p+2)), ⟨1, by omega⟩)} ∪
      (Finset.univ : Finset (Fin m)).image
        (fun j => s((0 : Fin (m+p+2)), ⟨j.val + 2, by omega⟩)) ∪
      (Finset.univ : Finset (Fin p)).image
        (fun j => s((⟨1, by omega⟩ : Fin (m+p+2)), ⟨j.val + m + 2, by omega⟩)) := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      simp only [doubleStarGraph] at he
      rcases he with ⟨ha, hb⟩ | ⟨hb, ha⟩ | ⟨ha, hb⟩ | ⟨hb, ha⟩
      · rcases hb with hb | ⟨hb1, hb2⟩
        · left; left
          have h1 : a = 0 := by ext; exact ha
          have h2 : b = ⟨1, by omega⟩ := by ext; exact hb
          rw [h1, h2]
        · left; right
          refine ⟨⟨b.val - 2, by omega⟩, ?_⟩
          have h1 : a = 0 := by ext; exact ha
          have h3 : (⟨(⟨b.val - 2, by omega⟩ : Fin m).val + 2,
              by omega⟩ : Fin (m+p+2)) = b := Fin.ext (by simp; omega)
          rw [h1, h3]
      · rcases ha with ha | ⟨ha1, ha2⟩
        · left; left
          have h1 : b = 0 := by ext; exact hb
          have h2 : a = ⟨1, by omega⟩ := by ext; exact ha
          rw [h1, h2, Sym2.eq_swap]
        · left; right
          refine ⟨⟨a.val - 2, by omega⟩, ?_⟩
          have h1 : b = 0 := by ext; exact hb
          have h3 : (⟨(⟨a.val - 2, by omega⟩ : Fin m).val + 2,
              by omega⟩ : Fin (m+p+2)) = a := Fin.ext (by simp; omega)
          rw [h1, h3, Sym2.eq_swap]
      · right
        refine ⟨⟨b.val - m - 2, by omega⟩, ?_⟩
        have h1 : a = ⟨1, by omega⟩ := by ext; exact ha
        have h3 : (⟨(⟨b.val - m - 2, by omega⟩ : Fin p).val + m + 2,
            by omega⟩ : Fin (m+p+2)) = b := Fin.ext (by simp; omega)
        rw [h1, h3]
      · right
        refine ⟨⟨a.val - m - 2, by omega⟩, ?_⟩
        have h1 : b = ⟨1, by omega⟩ := by ext; exact hb
        have h3 : (⟨(⟨a.val - m - 2, by omega⟩ : Fin p).val + m + 2,
            by omega⟩ : Fin (m+p+2)) = a := Fin.ext (by simp; omega)
        rw [h1, h3, Sym2.eq_swap]
  · rintro ((rfl | ⟨j, rfl⟩) | ⟨j, rfl⟩)
    · rw [SimpleGraph.mem_edgeSet]
      exact Or.inl ⟨rfl, Or.inl rfl⟩
    · rw [SimpleGraph.mem_edgeSet]
      exact Or.inl ⟨rfl, Or.inr ⟨by simp, by simp⟩⟩
    · rw [SimpleGraph.mem_edgeSet]
      exact Or.inr (Or.inr (Or.inl ⟨rfl, by simp⟩))

private theorem doubleStarEdge_left_injOn (m p : ℕ) :
    Set.InjOn (fun j : Fin m => s((0 : Fin (m+p+2)), ⟨j.val + 2, by omega⟩))
      ↑(Finset.univ : Finset (Fin m)) := by
  intro j₁ _ j₂ _ h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · exact Fin.ext (by have := congr_arg Fin.val h; simp at this; omega)
  · exact absurd (congr_arg Fin.val h) (by simp)

private theorem doubleStarEdge_right_injOn (m p : ℕ) :
    Set.InjOn (fun j : Fin p => s((⟨1, by omega⟩ : Fin (m+p+2)), ⟨j.val + m + 2, by omega⟩))
      ↑(Finset.univ : Finset (Fin p)) := by
  intro j₁ _ j₂ _ h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · exact Fin.ext (by have := congr_arg Fin.val h; simp at this; omega)
  · exact absurd (congr_arg Fin.val h) (by simp)

private theorem doubleStarGraph_bridge_left_disjoint (m p : ℕ) :
    Disjoint
      ({s((0 : Fin (m+p+2)), ⟨1, by omega⟩)} : Finset _)
      ((Finset.univ : Finset (Fin m)).image
        (fun j => s((0 : Fin (m+p+2)), ⟨j.val + 2, by omega⟩))) := by
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  rw [Finset.mem_singleton] at he₁
  rw [Finset.mem_image] at he₂
  obtain ⟨j, _, hj⟩ := he₂
  rw [he₁] at hj; rw [Sym2.eq_iff] at hj
  rcases hj with ⟨_, h⟩ | ⟨h, _⟩ <;> exact absurd (congr_arg Fin.val h) (by simp)

private theorem doubleStarGraph_edgeFinset_disjoint (m p : ℕ) :
    Disjoint
      ({s((0 : Fin (m+p+2)), ⟨1, by omega⟩)} ∪
        (Finset.univ : Finset (Fin m)).image
          (fun j => s((0 : Fin (m+p+2)), ⟨j.val + 2, by omega⟩)))
      ((Finset.univ : Finset (Fin p)).image
        (fun j => s((⟨1, by omega⟩ : Fin (m+p+2)), ⟨j.val + m + 2, by omega⟩))) := by
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  rw [Finset.mem_union] at he₁
  rw [Finset.mem_image] at he₂
  obtain ⟨j₂, _, rfl⟩ := he₂
  rcases he₁ with he₁ | he₁
  · rw [Finset.mem_singleton] at he₁; rw [Sym2.eq_iff] at he₁
    rcases he₁ with ⟨h, _⟩ | ⟨_, h⟩ <;> exact absurd (congr_arg Fin.val h) (by simp)
  · rw [Finset.mem_image] at he₁; obtain ⟨j₁, _, hj₁⟩ := he₁; rw [Sym2.eq_iff] at hj₁
    rcases hj₁ with ⟨h, _⟩ | ⟨_, h⟩ <;> exact absurd (congr_arg Fin.val h) (by simp)

private theorem doubleStarGraph_prod_eq {k : ℕ} (m p : ℕ) (c : Fin k → Fin k → ℝ)
    (hc : ∀ i j, c i j = c j i) (σ : Fin (m + p + 2) → Fin k) :
    ∏ e ∈ (doubleStarGraph m p).edgeFinset,
      c (σ (Quot.out e).1) (σ (Quot.out e).2) =
    c (σ 0) (σ ⟨1, by omega⟩) *
    (∏ j : Fin m, c (σ 0) (σ ⟨j.val + 2, by omega⟩)) *
    (∏ j : Fin p, c (σ ⟨1, by omega⟩) (σ ⟨j.val + m + 2, by omega⟩)) := by
  rw [doubleStarGraph_edgeFinset,
    Finset.prod_union (doubleStarGraph_edgeFinset_disjoint m p),
    Finset.prod_union (doubleStarGraph_bridge_left_disjoint m p),
    Finset.prod_singleton,
    Finset.prod_image (doubleStarEdge_left_injOn m p),
    Finset.prod_image (doubleStarEdge_right_injOn m p)]
  congr 1
  · congr 1
    · have hout := Quot.out_eq s((0 : Fin (m+p+2)), ⟨1, by omega⟩)
      rw [Sym2.mk_eq_mk_iff] at hout
      rcases hout with h | h
      · rw [congr_arg Prod.fst h, congr_arg Prod.snd h]
      · have h1 := congr_arg Prod.fst h; have h2 := congr_arg Prod.snd h
        simp only [Prod.swap] at h1 h2; rw [h1, h2, hc]
    · congr 1; ext j
      have hout := Quot.out_eq s((0 : Fin (m+p+2)), ⟨j.val + 2, by omega⟩)
      rw [Sym2.mk_eq_mk_iff] at hout
      rcases hout with h | h
      · rw [congr_arg Prod.fst h, congr_arg Prod.snd h]
      · have h1 := congr_arg Prod.fst h; have h2 := congr_arg Prod.snd h
        simp only [Prod.swap] at h1 h2; rw [h1, h2, hc]
  · congr 1; ext j
    have hout := Quot.out_eq s((⟨1, by omega⟩ : Fin (m+p+2)), ⟨j.val + m + 2, by omega⟩)
    rw [Sym2.mk_eq_mk_iff] at hout
    rcases hout with h | h
    · rw [congr_arg Prod.fst h, congr_arg Prod.snd h]
    · have h1 := congr_arg Prod.fst h; have h2 := congr_arg Prod.snd h
      simp only [Prod.swap] at h1 h2; rw [h1, h2, hc]

/-- The sum over `Fin (m + p) → Fin k` of a product that factors into independent
left and right parts equals the product of the individual sums. -/
private theorem sum_piFinAdd_factor {k m p : ℕ}
    (f : (Fin m → Fin k) → ℝ) (g : (Fin p → Fin k) → ℝ) :
    ∑ τ : Fin (m + p) → Fin k,
      f (fun j => τ (Fin.castAdd p j)) * g (fun j => τ (Fin.natAdd m j)) =
    (∑ τ : Fin m → Fin k, f τ) * (∑ τ : Fin p → Fin k, g τ) := by
  let e : (Fin (m + p) → Fin k) ≃ (Fin m → Fin k) × (Fin p → Fin k) :=
    (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl (Fin k))).trans
      (Equiv.sumArrowEquivProdArrow (Fin m) (Fin p) (Fin k))
  have he : ∀ τ : Fin (m + p) → Fin k,
      f (fun j => τ (Fin.castAdd p j)) * g (fun j => τ (Fin.natAdd m j)) =
      f (e τ).1 * g (e τ).2 := fun _ => rfl
  simp_rw [he]
  have h1 : ∑ x, f (e x).1 * g (e x).2 =
      ∑ x : (Fin m → Fin k) × (Fin p → Fin k), f x.1 * g x.2 :=
    Equiv.sum_comp e (fun y => f y.1 * g y.2)
  rw [h1, Fintype.sum_prod_type]
  exact (Fintype.sum_mul_sum f g).symm

set_option maxHeartbeats 2400000 in
private theorem weightedHomSum_doubleStarGraph {k : ℕ} (m p : ℕ)
    (c : Fin k → Fin k → ℝ) (hc : ∀ i j, c i j = c j i) (w : Fin k → ℝ) :
    weightedHomSum (m + p + 2) (doubleStarGraph m p) c w
      = ∑ i : Fin k, w i * (wDeg c w i) ^ m * rowProfile c w i p := by
  simp only [weightedHomSum, wDeg, rowProfile]
  suffices h : ∀ σ : Fin (m + p + 2) → Fin k,
      (∏ v, w (σ v)) *
        ∏ e ∈ (doubleStarGraph m p).edgeFinset,
          c (σ (Quot.out e).1) (σ (Quot.out e).2) =
      w (σ 0) * w (σ (Fin.succ 0)) * c (σ 0) (σ (Fin.succ 0)) *
      (∏ j : Fin m, w (σ (Fin.succ (Fin.succ (Fin.castAdd p j)))) *
                     c (σ 0) (σ (Fin.succ (Fin.succ (Fin.castAdd p j))))) *
      (∏ j : Fin p, w (σ (Fin.succ (Fin.succ (Fin.natAdd m j)))) *
                     c (σ (Fin.succ 0)) (σ (Fin.succ (Fin.succ (Fin.natAdd m j))))) by
    simp_rw [h]
    -- Peel off σ(0) = i
    rw [(Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m + p + 2) => Fin k)) _).symm]
    simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    rw [Fintype.sum_prod_type]
    congr 1; funext i
    -- Peel off σ'(0) = b
    rw [(Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m + p + 1) => Fin k)) _).symm]
    simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    rw [Fintype.sum_prod_type]
    simp only []
    -- Rearrange multiplication within each summand
    have hrearr : ∀ (b : Fin k) (τ : Fin (m + p) → Fin k),
        (w i * w b * c i b * ∏ j, w (τ (Fin.castAdd p j)) * c i (τ (Fin.castAdd p j))) *
          (∏ j, w (τ (Fin.natAdd m j)) * c b (τ (Fin.natAdd m j))) =
        w i * (w b * c i b) *
          ((∏ j, w (τ (Fin.castAdd p j)) * c i (τ (Fin.castAdd p j))) *
           (∏ j, w (τ (Fin.natAdd m j)) * c b (τ (Fin.natAdd m j)))) :=
      fun _ _ => by ring
    simp_rw [hrearr, ← Finset.mul_sum]
    have h_factor : ∀ b : Fin k,
        ∑ τ : Fin (m + p) → Fin k,
          (∏ j, w (τ (Fin.castAdd p j)) * c i (τ (Fin.castAdd p j))) *
          (∏ j, w (τ (Fin.natAdd m j)) * c b (τ (Fin.natAdd m j))) =
        (∑ τ : Fin m → Fin k, ∏ j, w (τ j) * c i (τ j)) *
        (∑ τ : Fin p → Fin k, ∏ j, w (τ j) * c b (τ j)) :=
      fun b => sum_piFinAdd_factor
        (fun τL => ∏ j, w (τL j) * c i (τL j))
        (fun τR => ∏ j, w (τR j) * c b (τR j))
    simp_rw [h_factor]
    -- Collapse power sums
    have hpow : ∀ (c' : Fin k → ℝ) (n : ℕ),
        ∑ τ : Fin n → Fin k, ∏ j, w (τ j) * c' (τ j) = (∑ j, w j * c' j) ^ n := by
      intro c' n
      symm; rw [show (∑ j, w j * c' j) ^ n = ∏ _ : Fin n, ∑ l, w l * c' l from by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin],
        ← @Finset.sum_prod_piFinset _ _ ℝ _ _ _ Finset.univ]
      simp [Fintype.piFinset_univ]
    have hpow_left : (∑ τ : Fin m → Fin k, ∏ j, w (τ j) * c i (τ j)) =
        (∑ j, w j * c i j) ^ m := hpow (c i) m
    have hpow_right : ∀ b : Fin k, (∑ τ : Fin p → Fin k, ∏ j, w (τ j) * c b (τ j)) =
        (∑ j, w j * c b j) ^ p := fun b => hpow (c b) p
    simp_rw [hpow_left, hpow_right]
    -- Final rearrangement
    have hfinal : ∀ b : Fin k,
        w i * (w b * c i b) * ((∑ j, w j * c i j) ^ m * (∑ j, w j * c b j) ^ p) =
        w i * (∑ j, w j * c i j) ^ m * (w b * c i b * (∑ j, w j * c b j) ^ p) :=
      fun _ => by ring
    simp_rw [hfinal, ← Finset.mul_sum]
  -- Proof of suffices: combine vertex weights with edge products
  intro σ
  rw [doubleStarGraph_prod_eq m p c hc σ]
  -- Convert Fin notations to match consEquiv-friendly form
  have hfin1 : (⟨1, by omega⟩ : Fin (m + p + 2)) = Fin.succ 0 := rfl
  have hfin_left : ∀ j : Fin m, (⟨j.val + 2, by omega⟩ : Fin (m + p + 2)) =
      Fin.succ (Fin.succ (Fin.castAdd p j)) :=
    fun _ => Fin.ext (by simp [Fin.val_succ, Fin.val_castAdd])
  have hfin_right : ∀ j : Fin p, (⟨j.val + m + 2, by omega⟩ : Fin (m + p + 2)) =
      Fin.succ (Fin.succ (Fin.natAdd m j)) :=
    fun _ => Fin.ext (by simp [Fin.val_succ, Fin.val_natAdd]; omega)
  simp_rw [hfin1, hfin_left, hfin_right]
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_add]
  simp only [Finset.prod_mul_distrib]
  ring

/-- Double-star moment matching from double-star graph tests. -/
private theorem double_star_moments_eq {k : ℕ}
    (c c' : Fin k → Fin k → ℝ)
    (hc_symm : ∀ i j, c i j = c j i) (hc'_symm : ∀ i j, c' i j = c' j i)
    (w : Fin k → ℝ)
    (h_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      weightedHomSum n F c w = weightedHomSum n F c' w) :
    ∀ m p : ℕ, ∑ i, w i * (wDeg c w i) ^ m * rowProfile c w i p
            = ∑ i, w i * (wDeg c' w i) ^ m * rowProfile c' w i p := by
  intro m p
  have h1 := weightedHomSum_doubleStarGraph m p c hc_symm w
  have h2 := weightedHomSum_doubleStarGraph m p c' hc'_symm w
  rw [← h1, ← h2]
  exact h_eq (m + p + 2) (doubleStarGraph m p)

/-! ### Classwise row-profile moment extraction -/

/-- Rewrite `∑ i, g i * f(i)^m` by grouping indices by their `f` value. -/
private theorem sum_fiberwise_mul_pow {k : ℕ} (g : Fin k → ℝ) (f : Fin k → ℝ) (m : ℕ) :
    ∑ i, g i * f i ^ m =
      ∑ d ∈ (Finset.univ : Finset (Fin k)).image f,
        (∑ i ∈ Finset.univ.filter (fun i => f i = d), g i) * d ^ m := by
  symm
  calc ∑ d ∈ Finset.univ.image f,
        (∑ i ∈ Finset.univ.filter (fun i => f i = d), g i) * d ^ m
      = ∑ d ∈ Finset.univ.image f,
        ∑ i ∈ Finset.univ.filter (fun i => f i = d), g i * d ^ m := by
          congr 1; ext d; exact Finset.sum_mul ..
    _ = ∑ d ∈ Finset.univ.image f,
        ∑ i ∈ Finset.univ.filter (fun i => f i = d), g i * f i ^ m := by
          congr 1; ext d; apply Finset.sum_congr rfl
          intro i hi; rw [(Finset.mem_filter.mp hi).2]
    _ = ∑ i ∈ Finset.univ.filter (fun i => f i ∈ Finset.univ.image f), g i * f i ^ m :=
          Finset.sum_fiberwise_eq_sum_filter ..
    _ = ∑ i, g i * f i ^ m := by
          rw [Finset.filter_true_of_mem
            (fun i _ => Finset.mem_image_of_mem f (Finset.mem_univ i))]

/-- Vandermonde extraction for finset-indexed sums: if `∑ d ∈ S, A d * d^m = ∑ d ∈ S, A' d * d^m`
for all `m : ℕ`, then `A d = A' d` for all `d ∈ S`. -/
private theorem finset_weighted_powers_eq
    (S : Finset ℝ) (A A' : ℝ → ℝ)
    (h : ∀ m : ℕ, ∑ d ∈ S, A d * d ^ m = ∑ d ∈ S, A' d * d ^ m) :
    ∀ d ∈ S, A d = A' d := by
  -- Subtract to get ∑ d ∈ S, (A d - A' d) * d ^ m = 0
  have h0 : ∀ m : ℕ, ∑ d ∈ S, (A d - A' d) * d ^ m = 0 := by
    intro m; have := h m
    simp only [sub_mul, Finset.sum_sub_distrib]; linarith
  -- Enumerate S as Fin S.card
  set L := S.card with hL
  let e' : Fin L ≃ ↥S := (finCongr (Fintype.card_coe S).symm).trans (Fintype.equivFin ↥S).symm
  let s : Fin L → ℝ := fun l => ((e' l : ↥S) : ℝ)
  let a : Fin L → ℝ := fun l => A (s l) - A' (s l)
  -- s is injective (distinct elements of S)
  have hs : Function.Injective s := by
    intro l₁ l₂ heq
    exact e'.injective (Subtype.val_injective heq)
  -- Transfer sum identity to Fin L
  have h_transfer : ∀ (g' : ℝ → ℝ), ∑ d ∈ S, g' d = ∑ l : Fin L, g' (s l) := by
    intro g'
    rw [(Finset.sum_coe_sort S g').symm]
    exact (Equiv.sum_comp e' (fun x : ↥S => g' x.val)).symm
  have h1 : ∀ n : Fin L, ∑ l, a l * s l ^ (n : ℕ) = 0 := by
    intro n
    have := h0 (n : ℕ)
    rw [h_transfer] at this; exact this
  -- Apply Vandermonde
  have h2 := eq_zero_of_weighted_powers_eq_zero s hs a h1
  -- Extract pointwise equality
  intro d hd
  let l := e'.symm ⟨d, hd⟩
  have hl : s l = d := congr_arg Subtype.val (e'.apply_symm_apply ⟨d, hd⟩)
  have := congr_fun h2 l
  simp only [a, Pi.zero_apply, sub_eq_zero] at this
  rw [← hl]; exact this

/-! ### Core proof for k > 0 -/

/-- Degree moment matching from star graph tests.

From equal weighted hom sums for all graphs, we extract:
`∑ i, w i * (wDeg c w i) ^ m = ∑ i, w i * (wDeg c' w i) ^ m` for all `m`. -/
private theorem degree_moments_eq {k : ℕ}
    (c c' : Fin k → Fin k → ℝ)
    (hc_symm : ∀ i j, c i j = c j i) (hc'_symm : ∀ i j, c' i j = c' j i)
    (w : Fin k → ℝ)
    (h_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      weightedHomSum n F c w = weightedHomSum n F c' w) :
    ∀ m : ℕ, ∑ i, w i * (wDeg c w i) ^ m = ∑ i, w i * (wDeg c' w i) ^ m := by
  intro m
  have h1 := weightedHomSum_starGraph m c hc_symm w
  have h2 := weightedHomSum_starGraph m c' hc'_symm w
  rw [← h1, ← h2]
  exact h_eq (m + 1) (starGraph m)

/-- Total weight per degree class matches when weighted hom sums agree. -/
private theorem degree_weight_class_eq {k : ℕ}
    (c c' : Fin k → Fin k → ℝ) (hc_symm : ∀ i j, c i j = c j i)
    (hc'_symm : ∀ i j, c' i j = c' j i)
    (w : Fin k → ℝ) (hw_pos : ∀ i, 0 < w i)
    (h_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      weightedHomSum n F c w = weightedHomSum n F c' w) :
    ∀ d : ℝ,
      ∑ i ∈ Finset.univ.filter (fun i => wDeg c w i = d), w i
    = ∑ i ∈ Finset.univ.filter (fun i => wDeg c' w i = d), w i := by
  intro d
  have hdeg := degree_moments_eq c c' hc_symm hc'_symm w h_eq
  set S := Finset.univ.image (wDeg c w)
  set S' := Finset.univ.image (wDeg c' w)
  -- Fibers are empty outside image
  have hA0 : ∀ d, d ∉ S →
      (∑ i ∈ Finset.univ.filter (fun i => wDeg c w i = d), w i) = 0 := by
    intro d hd; apply Finset.sum_eq_zero; intro i hi
    exfalso; exact hd (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩)
  have hA'0 : ∀ d, d ∉ S' →
      (∑ i ∈ Finset.univ.filter (fun i => wDeg c' w i = d), w i) = 0 := by
    intro d hd; apply Finset.sum_eq_zero; intro i hi
    exfalso; exact hd (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩)
  -- Extend moment identity to S ∪ S'
  have hSS : ∀ m : ℕ,
      ∑ d ∈ S ∪ S', (∑ i ∈ Finset.univ.filter (fun i => wDeg c w i = d), w i) * d ^ m =
      ∑ d ∈ S ∪ S', (∑ i ∈ Finset.univ.filter (fun i => wDeg c' w i = d), w i) * d ^ m := by
    intro m
    rw [← Finset.sum_subset Finset.subset_union_left
        (fun d _ hd => by rw [hA0 d hd, zero_mul]),
      ← Finset.sum_subset Finset.subset_union_right
        (fun d _ hd => by rw [hA'0 d hd, zero_mul])]
    have h_m := hdeg m
    rw [sum_fiberwise_mul_pow w (wDeg c w) m, sum_fiberwise_mul_pow w (wDeg c' w) m] at h_m
    exact h_m
  by_cases hd_mem : d ∈ S ∪ S'
  · exact finset_weighted_powers_eq (S ∪ S') _ _ hSS d hd_mem
  · rw [Finset.mem_union, not_or] at hd_mem
    rw [hA0 d hd_mem.1, hA'0 d hd_mem.2]

/-- Classwise row-profile moments: grouping by degree value, the total
`w * rowProfile` sums match within each degree class. -/
private theorem degree_class_rowProfile_moments_eq {k : ℕ}
    (c c' : Fin k → Fin k → ℝ) (hc_symm : ∀ i j, c i j = c j i)
    (hc'_symm : ∀ i j, c' i j = c' j i)
    (w : Fin k → ℝ) (hw_pos : ∀ i, 0 < w i)
    (h_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      weightedHomSum n F c w = weightedHomSum n F c' w) :
    ∀ (d : ℝ) (p : ℕ),
      ∑ i ∈ Finset.univ.filter (fun i => wDeg c w i = d), w i * rowProfile c w i p
    = ∑ i ∈ Finset.univ.filter (fun i => wDeg c' w i = d), w i * rowProfile c' w i p := by
  intro d p
  have hdsm := double_star_moments_eq c c' hc_symm hc'_symm w h_eq
  set S := Finset.univ.image (wDeg c w)
  set S' := Finset.univ.image (wDeg c' w)
  -- Fibers are empty outside image
  have hB0 : ∀ d, d ∉ S →
      (∑ i ∈ Finset.univ.filter (fun i => wDeg c w i = d), w i * rowProfile c w i p) = 0 := by
    intro d hd; apply Finset.sum_eq_zero; intro i hi
    exfalso; exact hd (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩)
  have hB'0 : ∀ d, d ∉ S' →
      (∑ i ∈ Finset.univ.filter (fun i => wDeg c' w i = d), w i * rowProfile c' w i p) = 0 := by
    intro d hd; apply Finset.sum_eq_zero; intro i hi
    exfalso; exact hd (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩)
  -- Bivariate fiberwise: ∑ i, w i * deg^m * rowProfile = ∑ d ∈ image, (∑ fiber, w * rowProfile) * d^m
  have sum_fib : ∀ (c₀ : Fin k → Fin k → ℝ) (m₀ : ℕ),
      ∑ i, w i * (wDeg c₀ w i) ^ m₀ * rowProfile c₀ w i p =
        ∑ d ∈ Finset.univ.image (wDeg c₀ w),
          (∑ i ∈ Finset.univ.filter (fun i => wDeg c₀ w i = d),
            w i * rowProfile c₀ w i p) * d ^ m₀ := by
    intro c₀ m₀
    have := sum_fiberwise_mul_pow (fun i => w i * rowProfile c₀ w i p) (wDeg c₀ w) m₀
    convert this using 1; congr 1; ext i; ring
  -- Extend moment identity to S ∪ S'
  have hSS : ∀ m : ℕ,
      ∑ d ∈ S ∪ S',
        (∑ i ∈ Finset.univ.filter (fun i => wDeg c w i = d), w i * rowProfile c w i p) * d ^ m =
      ∑ d ∈ S ∪ S',
        (∑ i ∈ Finset.univ.filter (fun i => wDeg c' w i = d), w i * rowProfile c' w i p) * d ^ m := by
    intro m
    rw [← Finset.sum_subset Finset.subset_union_left
        (fun d _ hd => by rw [hB0 d hd, zero_mul]),
      ← Finset.sum_subset Finset.subset_union_right
        (fun d _ hd => by rw [hB'0 d hd, zero_mul])]
    have h_m := hdsm m p
    rw [sum_fib c m, sum_fib c' m] at h_m
    exact h_m
  by_cases hd_mem : d ∈ S ∪ S'
  · exact finset_weighted_powers_eq (S ∪ S') _ _ hSS d hd_mem
  · rw [Finset.mem_union, not_or] at hd_mem
    rw [hB0 d hd_mem.1, hB'0 d hd_mem.2]

/-! ### Profile star graph and row-profile power moments -/

/-- Bridge vertex position in the profile star graph: vertex `m + 1 + (p+1)*b`. -/
private def profileBridgePos (m p : ℕ) {r : ℕ} (b : Fin r) :
    Fin (m + r * (p + 1) + 1) :=
  ⟨m + 1 + (p + 1) * b.val, by nlinarith [b.isLt]⟩

@[simp] private theorem profileBridgePos_val (m p : ℕ) {r : ℕ} (b : Fin r) :
    (profileBridgePos m p b).val = m + 1 + (p + 1) * b.val := rfl

/-- Leaf vertex position in branch `b` of the profile star graph. -/
private def profileLeafPos (m : ℕ) {r : ℕ} (p : ℕ) (b : Fin r) (l : Fin p) :
    Fin (m + r * (p + 1) + 1) :=
  ⟨m + 1 + (p + 1) * b.val + l.val + 1, by nlinarith [b.isLt, l.isLt]⟩

@[simp] private theorem profileLeafPos_val (m : ℕ) {r : ℕ} (p : ℕ) (b : Fin r) (l : Fin p) :
    (profileLeafPos m p b l).val = m + 1 + (p + 1) * b.val + l.val + 1 := rfl

/-- Profile star graph PS(m, r, p) on `m + r*(p+1) + 1` vertices.

Root (vertex 0) connects to m plain leaves (vertices 1..m) and r bridge vertices.
Each bridge vertex connects to p branch leaves. This graph produces the weighted
homomorphism sum `∑ i, w i * (wDeg c w i)^m * (rowProfile c w i p)^r`. -/
def profileStarGraph (m r p : ℕ) : SimpleGraph (Fin (m + r * (p + 1) + 1)) where
  Adj u v :=
    (u.val = 0 ∧ 1 ≤ v.val ∧ v.val ≤ m) ∨
    (v.val = 0 ∧ 1 ≤ u.val ∧ u.val ≤ m) ∨
    (∃ b : Fin r, u.val = 0 ∧ v = profileBridgePos m p b) ∨
    (∃ b : Fin r, v.val = 0 ∧ u = profileBridgePos m p b) ∨
    (∃ b : Fin r, u = profileBridgePos m p b ∧
      ∃ l : Fin p, v = profileLeafPos m p b l) ∨
    (∃ b : Fin r, v = profileBridgePos m p b ∧
      ∃ l : Fin p, u = profileLeafPos m p b l)
  symm := fun {u v} h => by
    rcases h with h | h | ⟨b, h⟩ | ⟨b, h⟩ | ⟨b, h₁, l, h₂⟩ | ⟨b, h₁, l, h₂⟩
    · right; left; exact h
    · left; exact h
    · right; right; right; left; exact ⟨b, h⟩
    · right; right; left; exact ⟨b, h⟩
    · right; right; right; right; right; exact ⟨b, h₁, l, h₂⟩
    · right; right; right; right; left; exact ⟨b, h₁, l, h₂⟩
  loopless := fun v h => by
    simp only [profileBridgePos, profileLeafPos] at h
    rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨b, h1, h2⟩ | ⟨b, h1, h2⟩ |
      ⟨b, h1, l, h2⟩ | ⟨b, h1, l, h2⟩
    · omega
    · omega
    · exact absurd (congr_arg Fin.val h2) (by simp; omega)
    · exact absurd (congr_arg Fin.val h2) (by simp; omega)
    · have h1v := congr_arg Fin.val h1; have h2v := congr_arg Fin.val h2
      simp at h1v h2v; omega
    · have h1v := congr_arg Fin.val h1; have h2v := congr_arg Fin.val h2
      simp at h1v h2v; omega

instance profileStarGraphDecRel (m r p : ℕ) :
    DecidableRel (profileStarGraph m r p).Adj :=
  fun u v => inferInstanceAs (Decidable (
    (u.val = 0 ∧ 1 ≤ v.val ∧ v.val ≤ m) ∨
    (v.val = 0 ∧ 1 ≤ u.val ∧ u.val ≤ m) ∨
    (∃ b : Fin r, u.val = 0 ∧ v = profileBridgePos m p b) ∨
    (∃ b : Fin r, v.val = 0 ∧ u = profileBridgePos m p b) ∨
    (∃ b : Fin r, u = profileBridgePos m p b ∧
      ∃ l : Fin p, v = profileLeafPos m p b l) ∨
    (∃ b : Fin r, v = profileBridgePos m p b ∧
      ∃ l : Fin p, u = profileLeafPos m p b l)))

private theorem profileStarEdge_plain_injOn (m r p : ℕ) :
    Set.InjOn
      (fun j : Fin m => s((0 : Fin (m + r * (p + 1) + 1)), ⟨j.val + 1, by omega⟩))
      ↑(Finset.univ : Finset (Fin m)) := by
  intro j₁ _ j₂ _ h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · exact Fin.ext (by have := congr_arg Fin.val h; simp at this; omega)
  · exact absurd (congr_arg Fin.val h) (by simp)

private theorem profileStarEdge_bridge_injOn (m r p : ℕ) :
    Set.InjOn
      (fun b : Fin r => s((0 : Fin (m + r * (p + 1) + 1)), profileBridgePos m p b))
      ↑(Finset.univ : Finset (Fin r)) := by
  intro b₁ _ b₂ _ h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · have hv := congr_arg Fin.val h
    rw [profileBridgePos_val, profileBridgePos_val] at hv
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left (by omega : 0 < p + 1) (by omega))
  · have hv := congr_arg Fin.val h
    rw [Fin.val_zero, profileBridgePos_val] at hv; omega

private theorem profileStarEdge_branchLeaf_injOn (m r p : ℕ) :
    Set.InjOn
      (fun bl : Fin r × Fin p =>
        s(profileBridgePos m p bl.1, profileLeafPos m p bl.1 bl.2))
      ↑(Finset.univ : Finset (Fin r × Fin p)) := by
  intro a₁ _ a₂ _ h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · -- Same direction: bridge a₁.1 = bridge a₂.1 and leaf a₁ = leaf a₂
    replace h₁ : (p + 1) * a₁.1.val = (p + 1) * a₂.1.val := by
      have := congr_arg Fin.val h₁; simp only [profileBridgePos_val] at this; omega
    replace h₂ : a₁.2.val = a₂.2.val := by
      have := congr_arg Fin.val h₂; simp only [profileLeafPos_val] at this; omega
    exact Prod.ext (Fin.ext (Nat.eq_of_mul_eq_mul_left (by omega) h₁)) (Fin.ext h₂)
  · -- Cross direction: bridge a₁.1 = leaf a₂ and leaf a₁ = bridge a₂.1
    replace h₁ : m + 1 + (p + 1) * a₁.1.val =
        m + 1 + (p + 1) * a₂.1.val + a₂.2.val + 1 := by
      have := congr_arg Fin.val h₁
      simp only [profileBridgePos_val, profileLeafPos_val] at this; exact this
    replace h₂ : m + 1 + (p + 1) * a₁.1.val + a₁.2.val + 1 =
        m + 1 + (p + 1) * a₂.1.val := by
      have := congr_arg Fin.val h₂
      simp only [profileLeafPos_val, profileBridgePos_val] at this; exact this
    omega

private theorem profileStarGraph_disjoint_plain_bridge (m r p : ℕ) :
    Disjoint
      ((Finset.univ : Finset (Fin m)).image
        (fun j => s((0 : Fin (m + r * (p + 1) + 1)), ⟨j.val + 1, by omega⟩)))
      ((Finset.univ : Finset (Fin r)).image
        (fun b => s((0 : Fin (m + r * (p + 1) + 1)), profileBridgePos m p b))) := by
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  rw [Finset.mem_image] at he₁ he₂
  obtain ⟨j, _, rfl⟩ := he₁; obtain ⟨b, _, hb⟩ := he₂
  rw [Sym2.eq_iff] at hb
  rcases hb with ⟨_, h⟩ | ⟨h, _⟩
  · have hv := congr_arg Fin.val h; simp at hv; have := j.isLt; omega
  · have hv := congr_arg Fin.val h; simp at hv

private theorem profileStarGraph_disjoint_top_branchLeaf (m r p : ℕ) :
    Disjoint
      ((Finset.univ : Finset (Fin m)).image
        (fun j => s((0 : Fin (m + r * (p + 1) + 1)), ⟨j.val + 1, by omega⟩)) ∪
       (Finset.univ : Finset (Fin r)).image
        (fun b => s((0 : Fin (m + r * (p + 1) + 1)), profileBridgePos m p b)))
      ((Finset.univ : Finset (Fin r × Fin p)).image
        (fun bl => s(profileBridgePos m p bl.1, profileLeafPos m p bl.1 bl.2))) := by
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  rw [Finset.mem_union] at he₁; rw [Finset.mem_image] at he₂
  obtain ⟨⟨b, l⟩, _, rfl⟩ := he₂
  -- branchLeaf edges have both endpoints ≥ m+1; top edges have vertex 0
  rcases he₁ with he₁ | he₁ <;> rw [Finset.mem_image] at he₁
  · obtain ⟨j, _, hj⟩ := he₁; rw [Sym2.eq_iff] at hj
    -- In both cases the first component gives 0 = bridge/leaf, impossible
    rcases hj with ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> {
      rw [Fin.ext_iff] at h₁
      simp only [Fin.val_zero, profileBridgePos_val, profileLeafPos_val] at h₁; omega }
  · obtain ⟨b', _, hb'⟩ := he₁; rw [Sym2.eq_iff] at hb'
    rcases hb' with ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> {
      rw [Fin.ext_iff] at h₁
      simp only [Fin.val_zero, profileBridgePos_val, profileLeafPos_val] at h₁; omega }

private theorem profileStarGraph_edgeFinset (m r p : ℕ) :
    (profileStarGraph m r p).edgeFinset =
      (Finset.univ : Finset (Fin m)).image
        (fun j => s((0 : Fin (m + r * (p + 1) + 1)), ⟨j.val + 1, by omega⟩)) ∪
      (Finset.univ : Finset (Fin r)).image
        (fun b => s((0 : Fin (m + r * (p + 1) + 1)), profileBridgePos m p b)) ∪
      (Finset.univ : Finset (Fin r × Fin p)).image
        (fun bl => s(profileBridgePos m p bl.1, profileLeafPos m p bl.1 bl.2)) := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      simp only [profileStarGraph] at he
      rcases he with ⟨ha, hb1, hb2⟩ | ⟨hb, ha1, ha2⟩ |
        ⟨br, ha, hbr⟩ | ⟨br, hb, har⟩ |
        ⟨br, ha, l, hbl⟩ | ⟨br, hb, l, hal⟩
      · left; left
        exact ⟨⟨b.val - 1, by omega⟩, by
          have h1 : a = 0 := by ext; exact ha
          have h2 : (⟨(⟨b.val - 1, by omega⟩ : Fin m).val + 1, by omega⟩ :
            Fin (m + r * (p + 1) + 1)) = b := Fin.ext (by simp; omega)
          rw [h1, h2]⟩
      · left; left
        exact ⟨⟨a.val - 1, by omega⟩, by
          have h1 : b = 0 := by ext; exact hb
          have h2 : (⟨(⟨a.val - 1, by omega⟩ : Fin m).val + 1, by omega⟩ :
            Fin (m + r * (p + 1) + 1)) = a := Fin.ext (by simp; omega)
          rw [h1, h2, Sym2.eq_swap]⟩
      · left; right
        exact ⟨br, by
          have h1 : a = 0 := by ext; exact ha
          rw [h1, hbr]⟩
      · left; right
        exact ⟨br, by
          have h1 : b = 0 := by ext; exact hb
          rw [h1, har, Sym2.eq_swap]⟩
      · right; exact ⟨⟨br, l⟩, by rw [ha, hbl]⟩
      · right; exact ⟨⟨br, l⟩, by rw [hb, hal, Sym2.eq_swap]⟩
  · rintro ((⟨j, rfl⟩ | ⟨b, rfl⟩) | ⟨⟨b, l⟩, rfl⟩)
    · rw [SimpleGraph.mem_edgeSet]
      exact Or.inl ⟨rfl, by simp, by simp⟩
    · rw [SimpleGraph.mem_edgeSet]
      exact Or.inr (Or.inr (Or.inl ⟨b, rfl, rfl⟩))
    · rw [SimpleGraph.mem_edgeSet]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, rfl, l, rfl⟩))))

private theorem profileStarGraph_prod_eq {k : ℕ} (m r p : ℕ)
    (c : Fin k → Fin k → ℝ) (hc : ∀ i j, c i j = c j i)
    (σ : Fin (m + r * (p + 1) + 1) → Fin k) :
    ∏ e ∈ (profileStarGraph m r p).edgeFinset,
      c (σ (Quot.out e).1) (σ (Quot.out e).2) =
    (∏ j : Fin m, c (σ 0) (σ ⟨j.val + 1, by omega⟩)) *
    (∏ b : Fin r, c (σ 0) (σ (profileBridgePos m p b))) *
    ∏ b : Fin r, ∏ l : Fin p,
      c (σ (profileBridgePos m p b)) (σ (profileLeafPos m p b l)) := by
  rw [profileStarGraph_edgeFinset,
    Finset.prod_union (profileStarGraph_disjoint_top_branchLeaf m r p),
    Finset.prod_union (profileStarGraph_disjoint_plain_bridge m r p),
    Finset.prod_image (profileStarEdge_plain_injOn m r p),
    Finset.prod_image (profileStarEdge_bridge_injOn m r p),
    Finset.prod_image (profileStarEdge_branchLeaf_injOn m r p)]
  congr 1
  · congr 1
    · congr 1; ext j
      have hout := Quot.out_eq s((0 : Fin (m + r * (p + 1) + 1)), ⟨j.val + 1, by omega⟩)
      rw [Sym2.mk_eq_mk_iff] at hout
      rcases hout with h | h
      · rw [congr_arg Prod.fst h, congr_arg Prod.snd h]
      · have h1 := congr_arg Prod.fst h; have h2 := congr_arg Prod.snd h
        simp only [Prod.swap] at h1 h2; rw [h1, h2, hc]
    · congr 1; ext b
      have hout := Quot.out_eq
        s((0 : Fin (m + r * (p + 1) + 1)), profileBridgePos m p b)
      rw [Sym2.mk_eq_mk_iff] at hout
      rcases hout with h | h
      · rw [congr_arg Prod.fst h, congr_arg Prod.snd h]
      · have h1 := congr_arg Prod.fst h; have h2 := congr_arg Prod.snd h
        simp only [Prod.swap] at h1 h2; rw [h1, h2, hc]
  · rw [Fintype.prod_prod_type]
    congr 1; ext b; congr 1; ext l
    have hout := Quot.out_eq
      s(profileBridgePos m p b, profileLeafPos m p b l)
    rw [Sym2.mk_eq_mk_iff] at hout
    rcases hout with h | h
    · rw [congr_arg Prod.fst h, congr_arg Prod.snd h]
    · have h1 := congr_arg Prod.fst h; have h2 := congr_arg Prod.snd h
      simp only [Prod.swap] at h1 h2; rw [h1, h2, hc]

/-- Sum over `Fin (r * n) → Fin k` of a product that factors into r independent
blocks equals the product of the individual sums. -/
private theorem sum_piProd_factor {k r n : ℕ}
    (f : Fin r → (Fin n → Fin k) → ℝ) :
    ∑ τ : Fin (r * n) → Fin k,
      ∏ b : Fin r, f b (fun j => τ (finProdFinEquiv (b, j))) =
    ∏ b : Fin r, ∑ τ_b : Fin n → Fin k, f b τ_b := by
  let e : (Fin (r * n) → Fin k) ≃ (Fin r → Fin n → Fin k) :=
    (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl (Fin k))).trans
      (Equiv.curry (Fin r) (Fin n) (Fin k))
  have h1 : (∑ τ : Fin (r * n) → Fin k, ∏ b, f b (fun j => τ (finProdFinEquiv (b, j)))) =
      ∑ σ : Fin r → Fin n → Fin k, ∏ b, f b (σ b) :=
    Equiv.sum_comp e (fun σ => ∏ b, f b (σ b))
  rw [h1, ← Fintype.prod_sum]

/-- Equivalence between functions from a sigma type and dependent products. -/
private def sigmaArrowEquiv {L : ℕ} (n : Fin L → ℕ) (k : ℕ) :
    ((Σ l : Fin L, Fin (n l)) → Fin k) ≃ ((l : Fin L) → Fin (n l) → Fin k) where
  toFun f l j := f ⟨l, j⟩
  invFun g p := g p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- Sum over `Fin (∑ l, n l) → Fin k` of a product that factors into L independent
blocks (indexed by `Fin L`) equals the product of the individual sums. -/
private theorem sum_piSigma_factor {k L : ℕ} (n : Fin L → ℕ)
    (f : (l : Fin L) → (Fin (n l) → Fin k) → ℝ) :
    ∑ τ : Fin (∑ l, n l) → Fin k,
      ∏ l, f l (fun j => τ (finSigmaFinEquiv ⟨l, j⟩)) =
    ∏ l, ∑ τ_l : Fin (n l) → Fin k, f l τ_l := by
  let e : (Fin (∑ l, n l) → Fin k) ≃ ((l : Fin L) → Fin (n l) → Fin k) :=
    (Equiv.arrowCongr finSigmaFinEquiv.symm (Equiv.refl (Fin k))).trans
      (sigmaArrowEquiv n k)
  have h1 : (∑ τ : Fin (∑ l, n l) → Fin k,
      ∏ l, f l (fun j => τ (finSigmaFinEquiv ⟨l, j⟩))) =
    ∑ σ : (l : Fin L) → Fin (n l) → Fin k, ∏ l, f l (σ l) :=
    Equiv.sum_comp e (fun σ => ∏ l, f l (σ l))
  rw [h1, ← Fintype.prod_sum]

set_option maxHeartbeats 4000000 in
private theorem weightedHomSum_profileStarGraph {k : ℕ} (m r p : ℕ)
    (c : Fin k → Fin k → ℝ) (hc : ∀ i j, c i j = c j i) (w : Fin k → ℝ) :
    weightedHomSum (m + r * (p + 1) + 1) (profileStarGraph m r p) c w
      = ∑ i : Fin k, w i * (wDeg c w i) ^ m * (rowProfile c w i p) ^ r := by
  simp only [weightedHomSum, wDeg, rowProfile]
  suffices h : ∀ σ : Fin (m + r * (p + 1) + 1) → Fin k,
      (∏ v, w (σ v)) *
        ∏ e ∈ (profileStarGraph m r p).edgeFinset,
          c (σ (Quot.out e).1) (σ (Quot.out e).2) =
      w (σ 0) *
      (∏ j : Fin m, w (σ (Fin.succ (Fin.castAdd (r * (p + 1)) j))) *
                     c (σ 0) (σ (Fin.succ (Fin.castAdd (r * (p + 1)) j)))) *
      ∏ b : Fin r, (
        w (σ (Fin.succ (Fin.natAdd m (finProdFinEquiv (b, 0))))) *
        c (σ 0) (σ (Fin.succ (Fin.natAdd m (finProdFinEquiv (b, 0))))) *
        ∏ l : Fin p,
          w (σ (Fin.succ (Fin.natAdd m (finProdFinEquiv (b, Fin.succ l))))) *
          c (σ (Fin.succ (Fin.natAdd m (finProdFinEquiv (b, 0)))))
            (σ (Fin.succ (Fin.natAdd m (finProdFinEquiv (b, Fin.succ l)))))) by
    simp_rw [h]
    -- Peel σ(0) = i
    rw [(Equiv.sum_comp (Fin.consEquiv
      (fun _ : Fin (m + r * (p + 1) + 1) => Fin k)) _).symm]
    simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    rw [Fintype.sum_prod_type]
    congr 1; funext i
    -- Rearrange to w i * (plain sum * branch sum)
    have hrearr : ∀ (σ' : Fin (m + r * (p + 1)) → Fin k),
        (w i * ∏ j : Fin m, w (σ' (Fin.castAdd (r * (p + 1)) j)) *
          c i (σ' (Fin.castAdd (r * (p + 1)) j))) *
          ∏ b : Fin r,
            w (σ' (Fin.natAdd m (finProdFinEquiv (b, 0)))) *
            c i (σ' (Fin.natAdd m (finProdFinEquiv (b, 0)))) *
            ∏ l : Fin p,
              w (σ' (Fin.natAdd m (finProdFinEquiv (b, Fin.succ l)))) *
              c (σ' (Fin.natAdd m (finProdFinEquiv (b, 0))))
                (σ' (Fin.natAdd m (finProdFinEquiv (b, Fin.succ l)))) =
        w i * ((∏ j : Fin m, w (σ' (Fin.castAdd (r * (p + 1)) j)) *
          c i (σ' (Fin.castAdd (r * (p + 1)) j))) *
          ∏ b : Fin r,
            w (σ' (Fin.natAdd m (finProdFinEquiv (b, 0)))) *
            c i (σ' (Fin.natAdd m (finProdFinEquiv (b, 0)))) *
            ∏ l : Fin p,
              w (σ' (Fin.natAdd m (finProdFinEquiv (b, Fin.succ l)))) *
              c (σ' (Fin.natAdd m (finProdFinEquiv (b, 0))))
                (σ' (Fin.natAdd m (finProdFinEquiv (b, Fin.succ l))))) :=
      fun _ => by ring
    simp_rw [hrearr, ← Finset.mul_sum]
    -- Factor plain × branch via sum_piFinAdd_factor
    have h_split := sum_piFinAdd_factor (k := k)
      (fun τL => ∏ j : Fin m, w (τL j) * c i (τL j))
      (fun τR => ∏ b : Fin r,
        w (τR (finProdFinEquiv (b, 0))) *
        c i (τR (finProdFinEquiv (b, 0))) *
        ∏ l : Fin p,
          w (τR (finProdFinEquiv (b, Fin.succ l))) *
          c (τR (finProdFinEquiv (b, 0)))
            (τR (finProdFinEquiv (b, Fin.succ l))))
    simp_rw [h_split]
    -- Collapse power sums
    have hpow : ∀ (c' : Fin k → ℝ) (n : ℕ),
        ∑ τ : Fin n → Fin k, ∏ j, w (τ j) * c' (τ j) = (∑ j, w j * c' j) ^ n := by
      intro c' n
      symm; rw [show (∑ j, w j * c' j) ^ n = ∏ _ : Fin n, ∑ l, w l * c' l from by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin],
        ← @Finset.sum_prod_piFinset _ _ ℝ _ _ _ Finset.univ]
      simp [Fintype.piFinset_univ]
    -- Collapse plain power sum on LHS
    rw [hpow (c i) m]
    -- Prove: (wDeg)^m * (∑ τR, ∏ b, branch) = (wDeg)^m * (rowProfile)^r
    -- Define the branch function for sum_piProd_factor
    let f : Fin r → (Fin (p + 1) → Fin k) → ℝ := fun _ τ_b =>
      w (τ_b 0) * c i (τ_b 0) *
      ∏ l : Fin p, w (τ_b (Fin.succ l)) * c (τ_b 0) (τ_b (Fin.succ l))
    -- The branch sum per block (f doesn't depend on b)
    have h_branch_sum : ∀ b : Fin r,
        (∑ τ_b : Fin (p + 1) → Fin k, f b τ_b) =
        ∑ j : Fin k, w j * c i j * (∑ l, w l * c j l) ^ p := by
      intro b
      change (∑ τ_b : Fin (p + 1) → Fin k, w (τ_b 0) * c i (τ_b 0) *
        ∏ l : Fin p, w (τ_b (Fin.succ l)) * c (τ_b 0) (τ_b (Fin.succ l))) = _
      rw [(Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (p + 1) => Fin k)) _).symm]
      simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
      rw [Fintype.sum_prod_type]
      congr 1; funext j; dsimp only []
      rw [← Finset.mul_sum, hpow (c j) p]
    -- The full branch factorization
    have h_full_branch :
        (∑ τR : Fin (r * (p + 1)) → Fin k,
          ∏ b : Fin r,
            w (τR (finProdFinEquiv (b, 0))) *
            c i (τR (finProdFinEquiv (b, 0))) *
            ∏ l : Fin p,
              w (τR (finProdFinEquiv (b, Fin.succ l))) *
              c (τR (finProdFinEquiv (b, 0)))
                (τR (finProdFinEquiv (b, Fin.succ l)))) =
        (∑ j : Fin k, w j * c i j * (∑ l, w l * c j l) ^ p) ^ r := by
      have h1 : ∀ (τR : Fin (r * (p + 1)) → Fin k),
          ∏ b : Fin r,
            w (τR (finProdFinEquiv (b, 0))) *
            c i (τR (finProdFinEquiv (b, 0))) *
            ∏ l : Fin p,
              w (τR (finProdFinEquiv (b, Fin.succ l))) *
              c (τR (finProdFinEquiv (b, 0)))
                (τR (finProdFinEquiv (b, Fin.succ l))) =
          ∏ b : Fin r, f b (fun j => τR (finProdFinEquiv (b, j))) :=
        fun _ => rfl
      simp_rw [h1, sum_piProd_factor f]
      rw [show (∑ j : Fin k, w j * c i j * (∑ l, w l * c j l) ^ p) ^ r =
          ∏ _ : Fin r, ∑ j, w j * c i j * (∑ l, w l * c j l) ^ p from by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
      congr 1; funext b; exact h_branch_sum b
    rw [h_full_branch, mul_assoc]
  -- Proof of suffices: combine vertex weights with edge products
  intro σ
  rw [profileStarGraph_prod_eq m r p c hc σ]
  -- Convert Fin positions
  have hfin_plain : ∀ j : Fin m, (⟨j.val + 1, by omega⟩ : Fin (m + r * (p + 1) + 1)) =
      Fin.succ (Fin.castAdd (r * (p + 1)) j) :=
    fun _ => Fin.ext (by simp [Fin.val_succ, Fin.val_castAdd])
  have hfin_bridge : ∀ b : Fin r, profileBridgePos m p b =
      Fin.succ (Fin.natAdd m (finProdFinEquiv (b, (0 : Fin (p + 1))))) :=
    fun b => by
      apply Fin.ext
      simp only [profileBridgePos_val, Fin.val_succ, Fin.val_natAdd]
      have : (finProdFinEquiv (b, (0 : Fin (p + 1)))).val = (p + 1) * b.val := by
        show (0 : Fin (p + 1)).val + (p + 1) * b.val = (p + 1) * b.val
        simp
      omega
  have hfin_leaf : ∀ (b : Fin r) (l : Fin p), profileLeafPos m p b l =
      Fin.succ (Fin.natAdd m (finProdFinEquiv (b, Fin.succ l))) :=
    fun b l => by
      apply Fin.ext
      simp only [profileLeafPos_val, Fin.val_succ, Fin.val_natAdd]
      have : (finProdFinEquiv (b, Fin.succ l)).val = l.val + 1 + (p + 1) * b.val := by
        show (Fin.succ l).val + (p + 1) * b.val = l.val + 1 + (p + 1) * b.val
        simp [Fin.val_succ]
      omega
  simp_rw [hfin_plain, hfin_bridge, hfin_leaf]
  -- Split vertex weight product
  rw [Fin.prod_univ_succ, Fin.prod_univ_add]
  -- Split the r*(p+1) block via finProdFinEquiv
  rw [show ∏ j : Fin (r * (p + 1)), w (σ ((Fin.natAdd m j).succ)) =
      ∏ bj : Fin r × Fin (p + 1), w (σ ((Fin.natAdd m (finProdFinEquiv bj)).succ)) from
    (Fintype.prod_equiv finProdFinEquiv _ _ (fun _ => rfl)).symm,
    Fintype.prod_prod_type]
  -- Peel bridge from each block
  simp_rw [Fin.prod_univ_succ]
  -- Use prod_mul_distrib to split/merge products and ring for rearrangement
  simp only [Finset.prod_mul_distrib]
  ring

/-- Profile-star moment matching: equal hom sums imply equal power-moment sums. -/
private theorem profile_star_moments_eq {k : ℕ}
    (c c' : Fin k → Fin k → ℝ)
    (hc_symm : ∀ i j, c i j = c j i) (hc'_symm : ∀ i j, c' i j = c' j i)
    (w : Fin k → ℝ)
    (h_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      weightedHomSum n F c w = weightedHomSum n F c' w) :
    ∀ m r p : ℕ,
      ∑ i, w i * (wDeg c w i) ^ m * (rowProfile c w i p) ^ r
    = ∑ i, w i * (wDeg c' w i) ^ m * (rowProfile c' w i p) ^ r := by
  intro m r p
  rw [← weightedHomSum_profileStarGraph m r p c hc_symm w,
      ← weightedHomSum_profileStarGraph m r p c' hc'_symm w]
  exact h_eq _ _

/-! ### Multi-profile star graph and joint refinement -/

/-- Total branch vertices for a multi-profile star graph with L branch types. -/
private abbrev multiProfileBranchTotal (L : ℕ) (r p : Fin L → ℕ) : ℕ :=
  ∑ l : Fin L, r l * (p l + 1)

/-- Cumulative offset for branch type `l` in the multi-profile star graph. -/
private def multiProfileTypeOffset {L : ℕ} (r p : Fin L → ℕ) (l : Fin L) : ℕ :=
  ∑ l' ∈ Finset.univ.filter (· < l), r l' * (p l' + 1)

private theorem multiProfileTypeOffset_le {L : ℕ} (r p : Fin L → ℕ) (l : Fin L) :
    multiProfileTypeOffset r p l + r l * (p l + 1) ≤ multiProfileBranchTotal L r p := by
  unfold multiProfileTypeOffset multiProfileBranchTotal
  have hdisj : Disjoint (Finset.univ.filter (· < l)) {l} := by
    simp [Finset.disjoint_singleton_right, lt_irrefl]
  have : ∑ l' ∈ Finset.univ.filter (· < l) ∪ {l}, r l' * (p l' + 1) =
      ∑ l' ∈ Finset.univ.filter (· < l), r l' * (p l' + 1) + r l * (p l + 1) := by
    rw [Finset.sum_union hdisj, Finset.sum_singleton]
  linarith [Finset.sum_le_univ_sum_of_nonneg
    (s := Finset.univ.filter (· < l) ∪ {l}) (fun l' => Nat.zero_le (r l' * (p l' + 1)))]

/-- Offset monotonicity: if l₁ < l₂, then offset(l₁) + block(l₁) ≤ offset(l₂). -/
private theorem multiProfileTypeOffset_mono {L : ℕ} (r p : Fin L → ℕ) {l₁ l₂ : Fin L}
    (h : l₁ < l₂) :
    multiProfileTypeOffset r p l₁ + r l₁ * (p l₁ + 1) ≤ multiProfileTypeOffset r p l₂ := by
  unfold multiProfileTypeOffset
  have h_not_mem : l₁ ∉ Finset.univ.filter (· < l₁) := by simp [lt_irrefl]
  have : ∑ l' ∈ insert l₁ (Finset.univ.filter (· < l₁)), r l' * (p l' + 1) =
      r l₁ * (p l₁ + 1) + ∑ l' ∈ Finset.univ.filter (· < l₁), r l' * (p l' + 1) :=
    Finset.sum_insert h_not_mem
  calc ∑ l' ∈ Finset.univ.filter (· < l₁), r l' * (p l' + 1) + r l₁ * (p l₁ + 1)
      = ∑ l' ∈ insert l₁ (Finset.univ.filter (· < l₁)), r l' * (p l' + 1) := by linarith
    _ ≤ ∑ l' ∈ Finset.univ.filter (· < l₂), r l' * (p l' + 1) := by
        apply Finset.sum_le_sum_of_subset
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        rcases hx with rfl | hx
        · exact h
        · exact lt_trans hx h

/-- Bridge position for type `l`, branch `b` in the multi-profile star graph:
vertex `m + 1 + offset(l) + (p l + 1) * b`. -/
private def mpBridgePos (m : ℕ) {L : ℕ} (r p : Fin L → ℕ) (l : Fin L) (b : Fin (r l)) :
    Fin (m + multiProfileBranchTotal L r p + 1) :=
  ⟨m + 1 + multiProfileTypeOffset r p l + (p l + 1) * b.val, by
    have hoff := multiProfileTypeOffset_le r p l
    nlinarith [b.isLt]⟩

@[simp] private theorem mpBridgePos_val (m : ℕ) {L : ℕ} (r p : Fin L → ℕ) (l : Fin L)
    (b : Fin (r l)) :
    (mpBridgePos m r p l b).val = m + 1 + multiProfileTypeOffset r p l + (p l + 1) * b.val :=
  rfl

/-- Leaf position for type `l`, branch `b`, leaf `j` in the multi-profile star graph:
vertex `m + 1 + offset(l) + (p l + 1) * b + j + 1`. -/
private def mpLeafPos (m : ℕ) {L : ℕ} (r p : Fin L → ℕ) (l : Fin L) (b : Fin (r l))
    (j : Fin (p l)) : Fin (m + multiProfileBranchTotal L r p + 1) :=
  ⟨m + 1 + multiProfileTypeOffset r p l + (p l + 1) * b.val + j.val + 1, by
    have hoff := multiProfileTypeOffset_le r p l
    nlinarith [b.isLt, j.isLt]⟩

@[simp] private theorem mpLeafPos_val (m : ℕ) {L : ℕ} (r p : Fin L → ℕ) (l : Fin L)
    (b : Fin (r l)) (j : Fin (p l)) :
    (mpLeafPos m r p l b j).val =
      m + 1 + multiProfileTypeOffset r p l + (p l + 1) * b.val + j.val + 1 := rfl

/-- Multi-profile star graph MPS(m, L, r, p) on `m + ∑ l, r(l)*(p(l)+1) + 1` vertices.

Root (vertex 0) connects to m plain leaves and to `r l` bridge vertices for each type `l`.
Each bridge of type `l` connects to `p l` branch leaves. This graph produces the weighted
homomorphism sum `∑ i, w i * (wDeg c w i)^m * ∏ l, (rowProfile c w i (p l))^(r l)`. -/
def multiProfileStarGraph (m L : ℕ) (r p : Fin L → ℕ) :
    SimpleGraph (Fin (m + multiProfileBranchTotal L r p + 1)) where
  Adj u v :=
    (u.val = 0 ∧ 1 ≤ v.val ∧ v.val ≤ m) ∨
    (v.val = 0 ∧ 1 ≤ u.val ∧ u.val ≤ m) ∨
    (∃ l : Fin L, ∃ b : Fin (r l), u.val = 0 ∧ v = mpBridgePos m r p l b) ∨
    (∃ l : Fin L, ∃ b : Fin (r l), v.val = 0 ∧ u = mpBridgePos m r p l b) ∨
    (∃ l : Fin L, ∃ b : Fin (r l), u = mpBridgePos m r p l b ∧
      ∃ j : Fin (p l), v = mpLeafPos m r p l b j) ∨
    (∃ l : Fin L, ∃ b : Fin (r l), v = mpBridgePos m r p l b ∧
      ∃ j : Fin (p l), u = mpLeafPos m r p l b j)
  symm := fun {u v} h => by
    rcases h with h | h | ⟨l, b, h⟩ | ⟨l, b, h⟩ | ⟨l, b, h₁, j, h₂⟩ | ⟨l, b, h₁, j, h₂⟩
    · right; left; exact h
    · left; exact h
    · right; right; right; left; exact ⟨l, b, h⟩
    · right; right; left; exact ⟨l, b, h⟩
    · right; right; right; right; right; exact ⟨l, b, h₁, j, h₂⟩
    · right; right; right; right; left; exact ⟨l, b, h₁, j, h₂⟩
  loopless := fun v h => by
    simp only [mpBridgePos, mpLeafPos] at h
    rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨l, b, h1, h2⟩ | ⟨l, b, h1, h2⟩ |
      ⟨l, b, h1, j, h2⟩ | ⟨l, b, h1, j, h2⟩
    · omega
    · omega
    · exact absurd (congr_arg Fin.val h2) (by simp; omega)
    · exact absurd (congr_arg Fin.val h2) (by simp; omega)
    · have h1v := congr_arg Fin.val h1; have h2v := congr_arg Fin.val h2
      simp at h1v h2v; omega
    · have h1v := congr_arg Fin.val h1; have h2v := congr_arg Fin.val h2
      simp at h1v h2v; omega

instance multiProfileStarGraphDecRel (m L : ℕ) (r p : Fin L → ℕ) :
    DecidableRel (multiProfileStarGraph m L r p).Adj :=
  fun u v => inferInstanceAs (Decidable (
    (u.val = 0 ∧ 1 ≤ v.val ∧ v.val ≤ m) ∨
    (v.val = 0 ∧ 1 ≤ u.val ∧ u.val ≤ m) ∨
    (∃ l : Fin L, ∃ b : Fin (r l), u.val = 0 ∧ v = mpBridgePos m r p l b) ∨
    (∃ l : Fin L, ∃ b : Fin (r l), v.val = 0 ∧ u = mpBridgePos m r p l b) ∨
    (∃ l : Fin L, ∃ b : Fin (r l), u = mpBridgePos m r p l b ∧
      ∃ j : Fin (p l), v = mpLeafPos m r p l b j) ∨
    (∃ l : Fin L, ∃ b : Fin (r l), v = mpBridgePos m r p l b ∧
      ∃ j : Fin (p l), u = mpLeafPos m r p l b j)))

private theorem mpEdge_plain_injOn (m L : ℕ) (r p : Fin L → ℕ) :
    Set.InjOn
      (fun j : Fin m => s((0 : Fin (m + multiProfileBranchTotal L r p + 1)),
        ⟨j.val + 1, by omega⟩))
      ↑(Finset.univ : Finset (Fin m)) := by
  intro j₁ _ j₂ _ h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · exact Fin.ext (by have := congr_arg Fin.val h; simp at this; omega)
  · exact absurd (congr_arg Fin.val h) (by simp)

private theorem mpEdge_bridge_injOn (m L : ℕ) (r p : Fin L → ℕ) :
    Set.InjOn
      (fun lb : (Σ l : Fin L, Fin (r l)) =>
        s((0 : Fin (m + multiProfileBranchTotal L r p + 1)), mpBridgePos m r p lb.1 lb.2))
      ↑(Finset.univ : Finset (Σ l : Fin L, Fin (r l))) := by
  intro ⟨l₁, b₁⟩ _ ⟨l₂, b₂⟩ _ h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · have hv := congr_arg Fin.val h
    simp only [mpBridgePos_val] at hv
    have hoff : multiProfileTypeOffset r p l₁ + (p l₁ + 1) * b₁.val =
        multiProfileTypeOffset r p l₂ + (p l₂ + 1) * b₂.val := by omega
    by_cases heq : l₁ = l₂
    · subst heq
      have : (p l₁ + 1) * b₁.val = (p l₁ + 1) * b₂.val := by omega
      have hb : b₁.val = b₂.val := Nat.eq_of_mul_eq_mul_left (by omega) this
      exact Sigma.ext rfl (heq_of_eq (Fin.ext hb))
    · exfalso
      rcases Fin.lt_or_lt_of_ne heq with h₁ | h₁
      · nlinarith [multiProfileTypeOffset_mono r p h₁, b₁.isLt]
      · nlinarith [multiProfileTypeOffset_mono r p h₁, b₂.isLt]
  · have hv := congr_arg Fin.val h
    simp only [Fin.val_zero, mpBridgePos_val] at hv; omega

private theorem mpEdge_branchLeaf_injOn (m L : ℕ) (r p : Fin L → ℕ) :
    Set.InjOn
      (fun lbj : (Σ l : Fin L, Fin (r l) × Fin (p l)) =>
        s(mpBridgePos m r p lbj.1 lbj.2.1, mpLeafPos m r p lbj.1 lbj.2.1 lbj.2.2))
      ↑(Finset.univ : Finset (Σ l : Fin L, Fin (r l) × Fin (p l))) := by
  intro ⟨l₁, b₁, j₁⟩ _ ⟨l₂, b₂, j₂⟩ _ h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · -- Same direction
    have hv₁ := congr_arg Fin.val h₁; have hv₂ := congr_arg Fin.val h₂
    simp only [mpBridgePos_val, mpLeafPos_val] at hv₁ hv₂
    have hl : multiProfileTypeOffset r p l₁ + (p l₁ + 1) * b₁.val =
        multiProfileTypeOffset r p l₂ + (p l₂ + 1) * b₂.val := by omega
    by_cases heq : l₁ = l₂
    · subst heq
      have hb : (p l₁ + 1) * b₁.val = (p l₁ + 1) * b₂.val := by omega
      have hb' : b₁.val = b₂.val := Nat.eq_of_mul_eq_mul_left (by omega) hb
      have hj : j₁.val = j₂.val := by omega
      exact Sigma.ext rfl (heq_of_eq (Prod.ext (Fin.ext hb') (Fin.ext hj)))
    · exfalso
      rcases Fin.lt_or_lt_of_ne heq with h₁' | h₁'
      · nlinarith [multiProfileTypeOffset_mono r p h₁', b₁.isLt]
      · nlinarith [multiProfileTypeOffset_mono r p h₁', b₂.isLt]
  · -- Cross direction: bridge₁ = leaf₂ and leaf₁ = bridge₂
    have hv₁ := congr_arg Fin.val h₁; have hv₂ := congr_arg Fin.val h₂
    simp only [mpBridgePos_val, mpLeafPos_val] at hv₁ hv₂
    omega

private theorem mpDisjoint_plain_bridge (m L : ℕ) (r p : Fin L → ℕ) :
    Disjoint
      ((Finset.univ : Finset (Fin m)).image
        (fun j => s((0 : Fin (m + multiProfileBranchTotal L r p + 1)),
          ⟨j.val + 1, by omega⟩)))
      ((Finset.univ : Finset (Σ l : Fin L, Fin (r l))).image
        (fun lb => s((0 : Fin (m + multiProfileBranchTotal L r p + 1)),
          mpBridgePos m r p lb.1 lb.2))) := by
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  rw [Finset.mem_image] at he₁ he₂
  obtain ⟨j, _, rfl⟩ := he₁; obtain ⟨⟨l, b⟩, _, hb⟩ := he₂
  rw [Sym2.eq_iff] at hb
  rcases hb with ⟨_, h⟩ | ⟨h, _⟩
  · have hv := congr_arg Fin.val h; simp at hv; have := j.isLt; omega
  · have hv := congr_arg Fin.val h; simp at hv

private theorem mpDisjoint_top_branchLeaf (m L : ℕ) (r p : Fin L → ℕ) :
    Disjoint
      ((Finset.univ : Finset (Fin m)).image
        (fun j => s((0 : Fin (m + multiProfileBranchTotal L r p + 1)),
          ⟨j.val + 1, by omega⟩)) ∪
       (Finset.univ : Finset (Σ l : Fin L, Fin (r l))).image
        (fun lb => s((0 : Fin (m + multiProfileBranchTotal L r p + 1)),
          mpBridgePos m r p lb.1 lb.2)))
      ((Finset.univ : Finset (Σ l : Fin L, Fin (r l) × Fin (p l))).image
        (fun lbj => s(mpBridgePos m r p lbj.1 lbj.2.1,
          mpLeafPos m r p lbj.1 lbj.2.1 lbj.2.2))) := by
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  rw [Finset.mem_union] at he₁; rw [Finset.mem_image] at he₂
  obtain ⟨⟨l, b, j⟩, _, rfl⟩ := he₂
  rcases he₁ with he₁ | he₁ <;> rw [Finset.mem_image] at he₁
  · obtain ⟨j', _, hj'⟩ := he₁; rw [Sym2.eq_iff] at hj'
    rcases hj' with ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> {
      rw [Fin.ext_iff] at h₁
      simp only [Fin.val_zero, mpBridgePos_val, mpLeafPos_val] at h₁; omega }
  · obtain ⟨⟨l', b'⟩, _, hb'⟩ := he₁; rw [Sym2.eq_iff] at hb'
    rcases hb' with ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> {
      rw [Fin.ext_iff] at h₁
      simp only [Fin.val_zero, mpBridgePos_val, mpLeafPos_val] at h₁; omega }

private theorem multiProfileStarGraph_edgeFinset (m L : ℕ) (r p : Fin L → ℕ) :
    (multiProfileStarGraph m L r p).edgeFinset =
      (Finset.univ : Finset (Fin m)).image
        (fun j => s((0 : Fin (m + multiProfileBranchTotal L r p + 1)),
          ⟨j.val + 1, by omega⟩)) ∪
      (Finset.univ : Finset (Σ l : Fin L, Fin (r l))).image
        (fun lb => s((0 : Fin (m + multiProfileBranchTotal L r p + 1)),
          mpBridgePos m r p lb.1 lb.2)) ∪
      (Finset.univ : Finset (Σ l : Fin L, Fin (r l) × Fin (p l))).image
        (fun lbj => s(mpBridgePos m r p lbj.1 lbj.2.1,
          mpLeafPos m r p lbj.1 lbj.2.1 lbj.2.2)) := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      simp only [multiProfileStarGraph] at he
      rcases he with ⟨ha, hb1, hb2⟩ | ⟨hb, ha1, ha2⟩ |
        ⟨l, br, ha, hbr⟩ | ⟨l, br, hb, har⟩ |
        ⟨l, br, ha, j, hbl⟩ | ⟨l, br, hb, j, hal⟩
      · left; left
        exact ⟨⟨b.val - 1, by omega⟩, by
          have h1 : a = 0 := by ext; exact ha
          have h2 : (⟨(⟨b.val - 1, by omega⟩ : Fin m).val + 1, by omega⟩ :
            Fin (m + multiProfileBranchTotal L r p + 1)) = b := Fin.ext (by simp; omega)
          rw [h1, h2]⟩
      · left; left
        exact ⟨⟨a.val - 1, by omega⟩, by
          have h1 : b = 0 := by ext; exact hb
          have h2 : (⟨(⟨a.val - 1, by omega⟩ : Fin m).val + 1, by omega⟩ :
            Fin (m + multiProfileBranchTotal L r p + 1)) = a := Fin.ext (by simp; omega)
          rw [h1, h2, Sym2.eq_swap]⟩
      · left; right
        exact ⟨⟨l, br⟩, by
          have h1 : a = 0 := by ext; exact ha
          rw [h1, hbr]⟩
      · left; right
        exact ⟨⟨l, br⟩, by
          have h1 : b = 0 := by ext; exact hb
          rw [h1, har, Sym2.eq_swap]⟩
      · right; exact ⟨⟨l, br, j⟩, by rw [ha, hbl]⟩
      · right; exact ⟨⟨l, br, j⟩, by rw [hb, hal, Sym2.eq_swap]⟩
  · rintro ((⟨j, rfl⟩ | ⟨⟨l, b⟩, rfl⟩) | ⟨⟨l, b, j⟩, rfl⟩)
    · rw [SimpleGraph.mem_edgeSet]
      exact Or.inl ⟨rfl, by simp, by simp⟩
    · rw [SimpleGraph.mem_edgeSet]
      exact Or.inr (Or.inr (Or.inl ⟨l, b, rfl, rfl⟩))
    · rw [SimpleGraph.mem_edgeSet]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, b, rfl, j, rfl⟩))))

private theorem multiProfileStarGraph_prod_eq {k : ℕ} (m L : ℕ) (r p : Fin L → ℕ)
    (c : Fin k → Fin k → ℝ) (hc : ∀ i j, c i j = c j i)
    (σ : Fin (m + multiProfileBranchTotal L r p + 1) → Fin k) :
    ∏ e ∈ (multiProfileStarGraph m L r p).edgeFinset,
      c (σ (Quot.out e).1) (σ (Quot.out e).2) =
    (∏ j : Fin m, c (σ 0) (σ ⟨j.val + 1, by omega⟩)) *
    (∏ lb : (Σ l : Fin L, Fin (r l)),
      c (σ 0) (σ (mpBridgePos m r p lb.1 lb.2))) *
    ∏ lbj : (Σ l : Fin L, Fin (r l) × Fin (p l)),
      c (σ (mpBridgePos m r p lbj.1 lbj.2.1))
        (σ (mpLeafPos m r p lbj.1 lbj.2.1 lbj.2.2)) := by
  rw [multiProfileStarGraph_edgeFinset,
    Finset.prod_union (mpDisjoint_top_branchLeaf m L r p),
    Finset.prod_union (mpDisjoint_plain_bridge m L r p),
    Finset.prod_image (mpEdge_plain_injOn m L r p),
    Finset.prod_image (mpEdge_bridge_injOn m L r p),
    Finset.prod_image (mpEdge_branchLeaf_injOn m L r p)]
  congr 1
  · congr 1
    · congr 1; ext j
      have hout := Quot.out_eq
        s((0 : Fin (m + multiProfileBranchTotal L r p + 1)), ⟨j.val + 1, by omega⟩)
      rw [Sym2.mk_eq_mk_iff] at hout
      rcases hout with h | h
      · rw [congr_arg Prod.fst h, congr_arg Prod.snd h]
      · have h1 := congr_arg Prod.fst h; have h2 := congr_arg Prod.snd h
        simp only [Prod.swap] at h1 h2; rw [h1, h2, hc]
    · congr 1; ext ⟨l, b⟩
      have hout := Quot.out_eq
        s((0 : Fin (m + multiProfileBranchTotal L r p + 1)), mpBridgePos m r p l b)
      rw [Sym2.mk_eq_mk_iff] at hout
      rcases hout with h | h
      · rw [congr_arg Prod.fst h, congr_arg Prod.snd h]
      · have h1 := congr_arg Prod.fst h; have h2 := congr_arg Prod.snd h
        simp only [Prod.swap] at h1 h2; rw [h1, h2, hc]
  · congr 1; ext ⟨l, b, j⟩
    have hout := Quot.out_eq
      s(mpBridgePos m r p l b, mpLeafPos m r p l b j)
    rw [Sym2.mk_eq_mk_iff] at hout
    rcases hout with h | h
    · rw [congr_arg Prod.fst h, congr_arg Prod.snd h]
    · have h1 := congr_arg Prod.fst h; have h2 := congr_arg Prod.snd h
      simp only [Prod.swap] at h1 h2; rw [h1, h2, hc]

set_option maxHeartbeats 8000000 in
private theorem weightedHomSum_multiProfileStarGraph {k : ℕ} (m L : ℕ)
    (r p : Fin L → ℕ) (c : Fin k → Fin k → ℝ) (hc : ∀ i j, c i j = c j i)
    (w : Fin k → ℝ) :
    weightedHomSum (m + multiProfileBranchTotal L r p + 1)
      (multiProfileStarGraph m L r p) c w =
    ∑ i : Fin k, w i * (wDeg c w i) ^ m * ∏ l, (rowProfile c w i (p l)) ^ (r l) := by
  simp only [weightedHomSum, wDeg, rowProfile]
  -- Bridge/leaf position conversions
  -- Helper: relate multiProfileTypeOffset to finSigmaFinEquiv prefix sum
  have hoff_eq : ∀ l : Fin L,
      multiProfileTypeOffset r p l =
      ∑ i : Fin l, (fun l => r l * (p l + 1)) (Fin.castLE l.isLt.le i) := by
    intro l; unfold multiProfileTypeOffset
    rw [show Finset.univ.filter (· < l) =
        (Finset.univ : Finset (Fin l)).image (Fin.castLE l.isLt.le) from ?_]
    · rw [Finset.sum_image (fun a _ b _ h => Fin.castLE_injective _ h)]
    · ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h; exact ⟨⟨x.val, h⟩, Fin.ext (by simp)⟩
      · rintro ⟨i, rfl⟩; exact i.isLt
  have hfin_bridge : ∀ (l : Fin L) (b : Fin (r l)), mpBridgePos m r p l b =
      Fin.succ (Fin.natAdd m (@finSigmaFinEquiv L (fun l => r l * (p l + 1))
        ⟨l, finProdFinEquiv (b, (0 : Fin (p l + 1)))⟩)) := by
    intro l b; apply Fin.ext
    simp only [mpBridgePos_val, Fin.val_succ, Fin.val_natAdd, finSigmaFinEquiv_apply,
      finProdFinEquiv_apply_val, Fin.val_zero]
    rw [hoff_eq]; simp only []; omega
  have hfin_leaf : ∀ (l : Fin L) (b : Fin (r l)) (j : Fin (p l)), mpLeafPos m r p l b j =
      Fin.succ (Fin.natAdd m (@finSigmaFinEquiv L (fun l => r l * (p l + 1))
        ⟨l, finProdFinEquiv (b, Fin.succ j)⟩)) := by
    intro l b j; apply Fin.ext
    simp only [mpLeafPos_val, Fin.val_succ, Fin.val_natAdd, finSigmaFinEquiv_apply,
      finProdFinEquiv_apply_val]
    rw [hoff_eq]; simp only []; omega
  suffices h : ∀ σ : Fin (m + multiProfileBranchTotal L r p + 1) → Fin k,
      (∏ v, w (σ v)) *
        ∏ e ∈ (multiProfileStarGraph m L r p).edgeFinset,
          c (σ (Quot.out e).1) (σ (Quot.out e).2) =
      w (σ 0) *
      (∏ j : Fin m,
        w (σ (Fin.succ (Fin.castAdd (multiProfileBranchTotal L r p) j))) *
        c (σ 0) (σ (Fin.succ (Fin.castAdd (multiProfileBranchTotal L r p) j)))) *
      ∏ l, ∏ b : Fin (r l), (
        w (σ (Fin.succ (Fin.natAdd m (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, 0)⟩)))) *
        c (σ 0) (σ (Fin.succ (Fin.natAdd m (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, 0)⟩)))) *
        ∏ j : Fin (p l),
          w (σ (Fin.succ (Fin.natAdd m (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, Fin.succ j)⟩)))) *
          c (σ (Fin.succ (Fin.natAdd m (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, 0)⟩))))
            (σ (Fin.succ (Fin.natAdd m (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, Fin.succ j)⟩))))) by
    simp_rw [h]
    -- Peel σ(0) = i
    rw [(Equiv.sum_comp (Fin.consEquiv
      (fun _ : Fin (m + multiProfileBranchTotal L r p + 1) => Fin k)) _).symm]
    simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    rw [Fintype.sum_prod_type]
    congr 1; funext i
    -- Rearrange: w i * (plain * branch) then factor
    have hrearr : ∀ (σ' : Fin (m + multiProfileBranchTotal L r p) → Fin k),
        (w i * ∏ j : Fin m,
          w (σ' (Fin.castAdd (multiProfileBranchTotal L r p) j)) *
          c i (σ' (Fin.castAdd (multiProfileBranchTotal L r p) j))) *
        (∏ l, ∏ b : Fin (r l),
          w (σ' (Fin.natAdd m (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, 0)⟩))) *
          c i (σ' (Fin.natAdd m (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, 0)⟩))) *
          ∏ j : Fin (p l),
            w (σ' (Fin.natAdd m (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, Fin.succ j)⟩))) *
            c (σ' (Fin.natAdd m (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, 0)⟩)))
              (σ' (Fin.natAdd m (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, Fin.succ j)⟩)))) =
        w i * ((∏ j : Fin m,
          w (σ' (Fin.castAdd (multiProfileBranchTotal L r p) j)) *
          c i (σ' (Fin.castAdd (multiProfileBranchTotal L r p) j))) *
        (∏ l, ∏ b : Fin (r l),
          w (σ' (Fin.natAdd m (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, 0)⟩))) *
          c i (σ' (Fin.natAdd m (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, 0)⟩))) *
          ∏ j : Fin (p l),
            w (σ' (Fin.natAdd m (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, Fin.succ j)⟩))) *
            c (σ' (Fin.natAdd m (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, 0)⟩)))
              (σ' (Fin.natAdd m (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, Fin.succ j)⟩))))) :=
      fun _ => by ring
    simp_rw [hrearr, ← Finset.mul_sum]
    -- Factor plain × branch via sum_piFinAdd_factor
    have h_split := sum_piFinAdd_factor (k := k)
      (fun τL => ∏ j : Fin m, w (τL j) * c i (τL j))
      (fun τR => ∏ l, ∏ b : Fin (r l),
        w (τR (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, 0)⟩)) *
        c i (τR (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, 0)⟩)) *
        ∏ j : Fin (p l),
          w (τR (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, Fin.succ j)⟩)) *
          c (τR (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, 0)⟩))
            (τR (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, Fin.succ j)⟩)))
    simp_rw [h_split]
    -- Collapse power sums for plain leaves
    have hpow : ∀ (c' : Fin k → ℝ) (n : ℕ),
        ∑ τ : Fin n → Fin k, ∏ j, w (τ j) * c' (τ j) = (∑ j, w j * c' j) ^ n := by
      intro c' n
      symm; rw [show (∑ j, w j * c' j) ^ n = ∏ _ : Fin n, ∑ l, w l * c' l from by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin],
        ← @Finset.sum_prod_piFinset _ _ ℝ _ _ _ Finset.univ]
      simp [Fintype.piFinset_univ]
    rw [hpow (c i) m]
    -- Factor branch sum via sum_piSigma_factor then sum_piProd_factor within each type
    -- Define per-type branch function for sum_piSigma_factor
    -- First reindex: Fin (∑ l, r l * (p l + 1)) → (Σ l, Fin (r l * (p l + 1))) via finSigmaFinEquiv
    -- Then within each type l: Fin (r l * (p l + 1)) → Fin (r l) × Fin (p l + 1) via finProdFinEquiv
    have h_branch_factor :
        (∑ τR : Fin (multiProfileBranchTotal L r p) → Fin k,
          ∏ l, ∏ b : Fin (r l),
            w (τR (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, 0)⟩)) *
            c i (τR (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, 0)⟩)) *
            ∏ j : Fin (p l),
              w (τR (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, Fin.succ j)⟩)) *
              c (τR (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, 0)⟩))
                (τR (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv (b, Fin.succ j)⟩))) =
        ∏ l, (∑ j : Fin k, w j * c i j * (∑ l', w l' * c j l') ^ (p l)) ^ (r l) := by
      -- Apply sum_piSigma_factor to split the sum over ∏ l
      have h1 := sum_piSigma_factor (k := k) (fun l => r l * (p l + 1))
        (fun l τ_l => ∏ b : Fin (r l),
          w (τ_l (finProdFinEquiv (b, 0))) *
          c i (τ_l (finProdFinEquiv (b, 0))) *
          ∏ j : Fin (p l),
            w (τ_l (finProdFinEquiv (b, Fin.succ j))) *
            c (τ_l (finProdFinEquiv (b, 0)))
              (τ_l (finProdFinEquiv (b, Fin.succ j))))
      rw [h1]
      -- Within each type l, apply sum_piProd_factor to split r l branches
      congr 1; funext l
      have h2 := sum_piProd_factor (k := k) (r := r l) (n := p l + 1)
        (fun _ τ_b =>
          w (τ_b 0) * c i (τ_b 0) *
          ∏ j : Fin (p l), w (τ_b (Fin.succ j)) * c (τ_b 0) (τ_b (Fin.succ j)))
      rw [h2]
      -- Each branch sum is ∑ j, w j * c i j * (∑ l', w l' * c j l') ^ p l
      have h_branch_sum : ∀ b : Fin (r l),
          (∑ τ_b : Fin (p l + 1) → Fin k,
            w (τ_b 0) * c i (τ_b 0) *
            ∏ j : Fin (p l), w (τ_b (Fin.succ j)) * c (τ_b 0) (τ_b (Fin.succ j))) =
          ∑ j : Fin k, w j * c i j * (∑ l', w l' * c j l') ^ (p l) := by
        intro b
        rw [(Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (p l + 1) => Fin k)) _).symm]
        simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
        rw [Fintype.sum_prod_type]
        congr 1; funext j; dsimp only []
        rw [← Finset.mul_sum, hpow (c j) (p l)]
      rw [show (∑ j : Fin k, w j * c i j * (∑ l', w l' * c j l') ^ (p l)) ^ (r l) =
          ∏ _ : Fin (r l), ∑ j, w j * c i j * (∑ l', w l' * c j l') ^ (p l) from by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
      congr 1; funext b; exact h_branch_sum b
    rw [h_branch_factor, mul_assoc]
  -- Prove the suffices: vertex weight × edge product = decomposed form
  intro σ
  -- Decompose edge product and convert sigma products to nested products
  rw [multiProfileStarGraph_prod_eq m L r p c hc σ]
  have h_bridge_sigma :
      ∏ lb : (Σ l : Fin L, Fin (r l)),
        c (σ 0) (σ (mpBridgePos m r p lb.1 lb.2)) =
      ∏ l, ∏ b : Fin (r l), c (σ 0) (σ (mpBridgePos m r p l b)) := by
    rw [← Finset.univ_sigma_univ, Finset.prod_sigma]
  have h_leaf_sigma :
      ∏ lbj : (Σ l : Fin L, Fin (r l) × Fin (p l)),
        c (σ (mpBridgePos m r p lbj.1 lbj.2.1))
          (σ (mpLeafPos m r p lbj.1 lbj.2.1 lbj.2.2)) =
      ∏ l, ∏ bj : Fin (r l) × Fin (p l),
        c (σ (mpBridgePos m r p l bj.1)) (σ (mpLeafPos m r p l bj.1 bj.2)) := by
    rw [← Finset.univ_sigma_univ, Finset.prod_sigma]
  rw [h_bridge_sigma, h_leaf_sigma]
  -- Convert mpBridgePos/mpLeafPos and plain positions to Fin.succ form
  have hfin_plain : ∀ j : Fin m,
      (⟨j.val + 1, by omega⟩ : Fin (m + multiProfileBranchTotal L r p + 1)) =
      Fin.succ (Fin.castAdd (multiProfileBranchTotal L r p) j) :=
    fun _ => Fin.ext (by simp [Fin.val_succ, Fin.val_castAdd])
  simp_rw [hfin_plain, hfin_bridge, hfin_leaf]
  -- Split vertex weight product: root × plain × branch
  rw [Fin.prod_univ_succ, Fin.prod_univ_add]
  -- Split the branch block via finSigmaFinEquiv then finProdFinEquiv
  rw [show ∏ j : Fin (multiProfileBranchTotal L r p),
      w (σ ((Fin.natAdd m j).succ)) =
    ∏ lx : (Σ l : Fin L, Fin (r l * (p l + 1))),
      w (σ ((Fin.natAdd m (finSigmaFinEquiv lx)).succ)) from
    (Fintype.prod_equiv finSigmaFinEquiv _ _ (fun _ => rfl)).symm]
  rw [show ∏ lx : (Σ l : Fin L, Fin (r l * (p l + 1))),
      w (σ ((Fin.natAdd m (finSigmaFinEquiv lx)).succ)) =
    ∏ l, ∏ x : Fin (r l * (p l + 1)),
      w (σ ((Fin.natAdd m (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, x⟩)).succ)) from by
    rw [← Finset.univ_sigma_univ]; exact Finset.prod_sigma ..]
  -- Within each type, split via finProdFinEquiv
  simp_rw [show ∀ l, ∏ x : Fin (r l * (p l + 1)),
      w (σ ((Fin.natAdd m (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, x⟩)).succ)) =
    ∏ bj : Fin (r l) × Fin (p l + 1),
      w (σ ((Fin.natAdd m (@finSigmaFinEquiv L (fun l => r l * (p l + 1)) ⟨l, finProdFinEquiv bj⟩)).succ)) from fun l =>
    (Fintype.prod_equiv finProdFinEquiv _ _ (fun _ => rfl)).symm]
  simp only [Finset.prod_mul_distrib, Fintype.prod_prod_type, Fin.prod_univ_succ]
  ring

/-- Multi-profile star moment matching: equal hom sums imply equal multi-product moments. -/
private theorem multi_profile_star_moments_eq {k : ℕ}
    (c c' : Fin k → Fin k → ℝ)
    (hc_symm : ∀ i j, c i j = c j i) (hc'_symm : ∀ i j, c' i j = c' j i)
    (w : Fin k → ℝ)
    (h_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      weightedHomSum n F c w = weightedHomSum n F c' w) :
    ∀ (m : ℕ) (L : ℕ) (r p : Fin L → ℕ),
      ∑ i, w i * (wDeg c w i) ^ m * ∏ l, (rowProfile c w i (p l)) ^ (r l)
    = ∑ i, w i * (wDeg c' w i) ^ m * ∏ l, (rowProfile c' w i (p l)) ^ (r l) := by
  intro m L r p
  rw [← weightedHomSum_multiProfileStarGraph m L r p c hc_symm w,
      ← weightedHomSum_multiProfileStarGraph m L r p c' hc'_symm w]
  exact h_eq _ _

/-- Classwise row-profile power moments: within each degree class,
`∑ w i * (rowProfile)^r` matches for all r. -/
private theorem degree_class_rowProfile_power_moments_eq {k : ℕ}
    (c c' : Fin k → Fin k → ℝ) (hc_symm : ∀ i j, c i j = c j i)
    (hc'_symm : ∀ i j, c' i j = c' j i)
    (w : Fin k → ℝ) (hw_pos : ∀ i, 0 < w i)
    (h_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      weightedHomSum n F c w = weightedHomSum n F c' w) :
    ∀ (d : ℝ) (p r : ℕ),
      ∑ i ∈ Finset.univ.filter (fun i => wDeg c w i = d),
        w i * (rowProfile c w i p) ^ r
    = ∑ i ∈ Finset.univ.filter (fun i => wDeg c' w i = d),
        w i * (rowProfile c' w i p) ^ r := by
  intro d p r
  have hpsm := profile_star_moments_eq c c' hc_symm hc'_symm w h_eq
  set S := Finset.univ.image (wDeg c w)
  set S' := Finset.univ.image (wDeg c' w)
  have hB0 : ∀ d, d ∉ S →
      (∑ i ∈ Finset.univ.filter (fun i => wDeg c w i = d),
        w i * (rowProfile c w i p) ^ r) = 0 := by
    intro d hd; apply Finset.sum_eq_zero; intro i hi
    exfalso; exact hd (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩)
  have hB'0 : ∀ d, d ∉ S' →
      (∑ i ∈ Finset.univ.filter (fun i => wDeg c' w i = d),
        w i * (rowProfile c' w i p) ^ r) = 0 := by
    intro d hd; apply Finset.sum_eq_zero; intro i hi
    exfalso; exact hd (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩)
  have sum_fib : ∀ (c₀ : Fin k → Fin k → ℝ) (m₀ : ℕ),
      ∑ i, w i * (wDeg c₀ w i) ^ m₀ * (rowProfile c₀ w i p) ^ r =
        ∑ d ∈ Finset.univ.image (wDeg c₀ w),
          (∑ i ∈ Finset.univ.filter (fun i => wDeg c₀ w i = d),
            w i * (rowProfile c₀ w i p) ^ r) * d ^ m₀ := by
    intro c₀ m₀
    have := sum_fiberwise_mul_pow (fun i => w i * (rowProfile c₀ w i p) ^ r) (wDeg c₀ w) m₀
    convert this using 1; congr 1; ext i; ring
  have hSS : ∀ m : ℕ,
      ∑ d ∈ S ∪ S',
        (∑ i ∈ Finset.univ.filter (fun i => wDeg c w i = d),
          w i * (rowProfile c w i p) ^ r) * d ^ m =
      ∑ d ∈ S ∪ S',
        (∑ i ∈ Finset.univ.filter (fun i => wDeg c' w i = d),
          w i * (rowProfile c' w i p) ^ r) * d ^ m := by
    intro m
    rw [← Finset.sum_subset Finset.subset_union_left
        (fun d _ hd => by rw [hB0 d hd, zero_mul]),
      ← Finset.sum_subset Finset.subset_union_right
        (fun d _ hd => by rw [hB'0 d hd, zero_mul])]
    have h_m := hpsm m r p
    rw [sum_fib c m, sum_fib c' m] at h_m
    exact h_m
  by_cases hd_mem : d ∈ S ∪ S'
  · exact finset_weighted_powers_eq (S ∪ S') _ _ hSS d hd_mem
  · rw [Finset.mem_union, not_or] at hd_mem
    rw [hB0 d hd_mem.1, hB'0 d hd_mem.2]

/-- Total weight per (degree, rowProfile) class matches: Vandermonde on rowProfile
values within each degree class separates row types completely. -/
private theorem degree_rowProfile_weight_class_eq {k : ℕ}
    (c c' : Fin k → Fin k → ℝ) (hc_symm : ∀ i j, c i j = c j i)
    (hc'_symm : ∀ i j, c' i j = c' j i)
    (w : Fin k → ℝ) (hw_pos : ∀ i, 0 < w i)
    (h_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      weightedHomSum n F c w = weightedHomSum n F c' w) :
    ∀ (d : ℝ) (p : ℕ) (q : ℝ),
      ∑ i ∈ Finset.univ.filter (fun i => wDeg c w i = d ∧ rowProfile c w i p = q), w i
    = ∑ i ∈ Finset.univ.filter (fun i => wDeg c' w i = d ∧ rowProfile c' w i p = q), w i := by
  intro d p q
  have hpower := degree_class_rowProfile_power_moments_eq c c' hc_symm hc'_symm w hw_pos h_eq
  -- Fix d, p. Group by rowProfile value within the degree class.
  set Sd := Finset.univ.filter (fun i => wDeg c w i = d)
  set Sd' := Finset.univ.filter (fun i => wDeg c' w i = d)
  set T := Sd.image (fun i => rowProfile c w i p)
  set T' := Sd'.image (fun i => rowProfile c' w i p)
  have hC0 : ∀ q, q ∉ T →
      (∑ i ∈ Finset.univ.filter (fun i => wDeg c w i = d ∧ rowProfile c w i p = q), w i) = 0 := by
    intro q hq; apply Finset.sum_eq_zero; intro i hi
    simp only [Finset.mem_filter] at hi
    exact absurd (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi.2.1⟩, hi.2.2⟩) hq
  have hC'0 : ∀ q, q ∉ T' →
      (∑ i ∈ Finset.univ.filter (fun i => wDeg c' w i = d ∧ rowProfile c' w i p = q), w i) = 0 := by
    intro q hq; apply Finset.sum_eq_zero; intro i hi
    simp only [Finset.mem_filter] at hi
    exact absurd (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi.2.1⟩, hi.2.2⟩) hq
  -- Fiberwise decomposition: ∑_{wDeg=d} w i * rowProfile^r = ∑_{q ∈ T} (∑_{wDeg=d, rp=q} w i) * q^r
  have sum_fib2 : ∀ (c₀ : Fin k → Fin k → ℝ) (r₀ : ℕ),
      ∑ i ∈ Finset.univ.filter (fun i => wDeg c₀ w i = d), w i * (rowProfile c₀ w i p) ^ r₀ =
        ∑ q ∈ (Finset.univ.filter (fun i => wDeg c₀ w i = d)).image (fun i => rowProfile c₀ w i p),
          (∑ i ∈ Finset.univ.filter (fun i => wDeg c₀ w i = d ∧ rowProfile c₀ w i p = q),
            w i) * q ^ r₀ := by
    intro c₀ r₀
    set S₀ := Finset.univ.filter (fun i => wDeg c₀ w i = d)
    have hff : ∀ q, Finset.univ.filter (fun i => wDeg c₀ w i = d ∧ rowProfile c₀ w i p = q) =
        S₀.filter (fun i => rowProfile c₀ w i p = q) := fun q => (Finset.filter_filter ..).symm
    simp_rw [hff]
    symm
    calc ∑ q ∈ S₀.image (fun i => rowProfile c₀ w i p),
            (∑ i ∈ S₀.filter (fun i => rowProfile c₀ w i p = q), w i) * q ^ r₀
        = ∑ q ∈ S₀.image (fun i => rowProfile c₀ w i p),
            ∑ i ∈ S₀.filter (fun i => rowProfile c₀ w i p = q), w i * q ^ r₀ := by
              congr 1; ext q; exact Finset.sum_mul ..
      _ = ∑ q ∈ S₀.image (fun i => rowProfile c₀ w i p),
            ∑ i ∈ S₀.filter (fun i => rowProfile c₀ w i p = q),
              w i * (rowProfile c₀ w i p) ^ r₀ := by
              congr 1; ext q; apply Finset.sum_congr rfl
              intro i hi; rw [(Finset.mem_filter.mp hi).2]
      _ = ∑ i ∈ S₀.filter (fun i => rowProfile c₀ w i p ∈
              S₀.image (fun i => rowProfile c₀ w i p)),
            w i * (rowProfile c₀ w i p) ^ r₀ :=
              Finset.sum_fiberwise_eq_sum_filter ..
      _ = ∑ i ∈ S₀, w i * (rowProfile c₀ w i p) ^ r₀ := by
              rw [Finset.filter_true_of_mem (fun i hi => Finset.mem_image_of_mem _ hi)]
  have hTT : ∀ r₀ : ℕ,
      ∑ q ∈ T ∪ T',
        (∑ i ∈ Finset.univ.filter (fun i => wDeg c w i = d ∧ rowProfile c w i p = q), w i) * q ^ r₀ =
      ∑ q ∈ T ∪ T',
        (∑ i ∈ Finset.univ.filter (fun i => wDeg c' w i = d ∧ rowProfile c' w i p = q), w i) * q ^ r₀ := by
    intro r₀
    rw [← Finset.sum_subset Finset.subset_union_left
        (fun q _ hq => by rw [hC0 q hq, zero_mul]),
      ← Finset.sum_subset Finset.subset_union_right
        (fun q _ hq => by rw [hC'0 q hq, zero_mul])]
    have h_r := hpower d p r₀
    rw [sum_fib2 c r₀, sum_fib2 c' r₀] at h_r
    exact h_r
  by_cases hq_mem : q ∈ T ∪ T'
  · exact finset_weighted_powers_eq (T ∪ T') _ _ hTT q hq_mem
  · rw [Finset.mem_union, not_or] at hq_mem
    rw [hC0 q hq_mem.1, hC'0 q hq_mem.2]

/-! ### Hierarchical Vandermonde and joint class separation -/

/-- Generic Vandermonde fiber extraction: from equal power-moment sums
`∑ g(i) * f(i)^m = ∑ g'(i) * f'(i)^m` for all m, extract
`∑_{f(i)=d} g(i) = ∑_{f'(i)=d} g'(i)` for each d. -/
private theorem vandermonde_fiber_eq {k : ℕ}
    (g g' : Fin k → ℝ) (f f' : Fin k → ℝ)
    (h : ∀ m : ℕ, ∑ i, g i * (f i) ^ m = ∑ i, g' i * (f' i) ^ m) :
    ∀ d : ℝ,
      ∑ i ∈ Finset.univ.filter (fun i => f i = d), g i =
      ∑ i ∈ Finset.univ.filter (fun i => f' i = d), g' i := by
  intro d
  set S := Finset.univ.image f
  set S' := Finset.univ.image f'
  have hA0 : ∀ d, d ∉ S →
      (∑ i ∈ Finset.univ.filter (fun i => f i = d), g i) = 0 := by
    intro d hd; apply Finset.sum_eq_zero; intro i hi
    exfalso; exact hd (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩)
  have hA'0 : ∀ d, d ∉ S' →
      (∑ i ∈ Finset.univ.filter (fun i => f' i = d), g' i) = 0 := by
    intro d hd; apply Finset.sum_eq_zero; intro i hi
    exfalso; exact hd (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩)
  have hSS : ∀ m : ℕ,
      ∑ d ∈ S ∪ S', (∑ i ∈ Finset.univ.filter (fun i => f i = d), g i) * d ^ m =
      ∑ d ∈ S ∪ S', (∑ i ∈ Finset.univ.filter (fun i => f' i = d), g' i) * d ^ m := by
    intro m
    rw [← Finset.sum_subset Finset.subset_union_left
        (fun d _ hd => by rw [hA0 d hd, zero_mul]),
      ← Finset.sum_subset Finset.subset_union_right
        (fun d _ hd => by rw [hA'0 d hd, zero_mul])]
    have h_m := h m
    rw [sum_fiberwise_mul_pow g f m, sum_fiberwise_mul_pow g' f' m] at h_m
    exact h_m
  by_cases hd_mem : d ∈ S ∪ S'
  · exact finset_weighted_powers_eq (S ∪ S') _ _ hSS d hd_mem
  · rw [Finset.mem_union, not_or] at hd_mem
    rw [hA0 d hd_mem.1, hA'0 d hd_mem.2]

/-- Hierarchical Vandermonde: from equal products of power-moment sums, extract
pointwise equality on joint filter classes by peeling one coordinate at a time. -/
private theorem hierarchical_vandermonde_class_eq {k : ℕ} :
    ∀ (L : ℕ) (g g' : Fin k → ℝ) (f f' : Fin L → Fin k → ℝ),
    (∀ rs : Fin L → ℕ,
      ∑ i, g i * ∏ l, (f l i) ^ (rs l) =
      ∑ i, g' i * ∏ l, (f' l i) ^ (rs l)) →
    ∀ qs : Fin L → ℝ,
      ∑ i ∈ Finset.univ.filter (fun i => ∀ l, f l i = qs l), g i =
      ∑ i ∈ Finset.univ.filter (fun i => ∀ l, f' l i = qs l), g' i := by
  intro L; induction L with
  | zero =>
    intro g g' f f' h qs
    have : ∀ (i : Fin k), (∀ l : Fin 0, f l i = qs l) := fun _ l => l.elim0
    have : ∀ (i : Fin k), (∀ l : Fin 0, f' l i = qs l) := fun _ l => l.elim0
    simp only [Finset.filter_true_of_mem (fun i _ => ‹∀ i, ∀ l : Fin 0, f l i = qs l› i),
      Finset.filter_true_of_mem (fun i _ => ‹∀ i, ∀ l : Fin 0, f' l i = qs l› i)]
    have := h Fin.elim0; simp only [Fintype.prod_empty, mul_one] at this; exact this
  | succ L ih =>
    intro g g' f f' h qs
    -- Step 1: For each value q of the last coordinate and each rs' : Fin L → ℕ,
    -- extract fiber equality via Vandermonde on the last exponent
    have h_fiber : ∀ (q : ℝ) (rs' : Fin L → ℕ),
        ∑ i ∈ Finset.univ.filter (fun i => f (Fin.last L) i = q),
          g i * ∏ l : Fin L, (f (Fin.castSucc l) i) ^ (rs' l) =
        ∑ i ∈ Finset.univ.filter (fun i => f' (Fin.last L) i = q),
          g' i * ∏ l : Fin L, (f' (Fin.castSucc l) i) ^ (rs' l) := by
      intro q rs'
      apply vandermonde_fiber_eq _ _ (f (Fin.last L)) (f' (Fin.last L))
      intro r
      have := h (Fin.snoc rs' r)
      convert this using 1 <;> {
        congr 1; ext i
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        ring }
    -- Step 2: Convert filtered sums to indicator sums for IH
    have h_ind : ∀ (q : ℝ) (rs' : Fin L → ℕ),
        ∑ i, (if f (Fin.last L) i = q then g i else 0) *
          ∏ l : Fin L, (f (Fin.castSucc l) i) ^ (rs' l) =
        ∑ i, (if f' (Fin.last L) i = q then g' i else 0) *
          ∏ l : Fin L, (f' (Fin.castSucc l) i) ^ (rs' l) := by
      intro q rs'
      simp_rw [ite_mul, zero_mul, ← Finset.sum_filter]
      exact h_fiber q rs'
    -- Step 3: Apply IH to each fiber
    set q := qs (Fin.last L)
    set qs' : Fin L → ℝ := fun l => qs (Fin.castSucc l)
    have h_joint := ih
      (fun i => if f (Fin.last L) i = q then g i else 0)
      (fun i => if f' (Fin.last L) i = q then g' i else 0)
      (fun l i => f (Fin.castSucc l) i)
      (fun l i => f' (Fin.castSucc l) i)
      (h_ind q) qs'
    -- Step 4: Convert indicator on joint filter back to joint filter
    -- LHS: ∑_{∀ l, f(castSucc l, i) = qs'(l)} (if f(last,i)=q then g i else 0)
    --     = ∑_{∀ l : Fin (L+1), f(l,i) = qs(l)} g i
    -- h_joint : ∑_{∀ l, f(castSucc l, i) = qs'(l)} (if f(last,i)=q then g i else 0) = ...
    -- Goal: ∑_{∀ l : Fin (L+1), f(l,i) = qs(l)} g i = ...
    -- Convert ∀ l : Fin (L+1) to conjunction, then use filter_filter and sum_filter
    have h_split : ∀ (f₀ : Fin (L + 1) → Fin k → ℝ),
        Finset.univ.filter (fun i => ∀ l, f₀ l i = qs l) =
        (Finset.univ.filter (fun i => ∀ l : Fin L, f₀ (Fin.castSucc l) i = qs (Fin.castSucc l))).filter
          (fun i => f₀ (Fin.last L) i = qs (Fin.last L)) := by
      intro f₀
      rw [Finset.filter_filter]
      congr 1; ext i
      exact Fin.forall_fin_succ'
    rw [h_split f, h_split f']
    -- Convert (filter Q).filter P sums to indicator form via sum_filter (one application each)
    conv_lhs => rw [Finset.sum_filter]
    conv_rhs => rw [Finset.sum_filter]
    exact h_joint

/-- Joint class weight equality: for any degree value d and any finite tuple
of (profile-index, profile-value) pairs, the total weight matches. -/
private theorem joint_class_weight_eq {k : ℕ}
    (c c' : Fin k → Fin k → ℝ) (hc_symm : ∀ i j, c i j = c j i)
    (hc'_symm : ∀ i j, c' i j = c' j i)
    (w : Fin k → ℝ) (hw_pos : ∀ i, 0 < w i)
    (h_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      weightedHomSum n F c w = weightedHomSum n F c' w) :
    ∀ (d : ℝ) (L : ℕ) (ps : Fin L → ℕ) (qs : Fin L → ℝ),
      ∑ i ∈ Finset.univ.filter (fun i =>
        wDeg c w i = d ∧ ∀ l, rowProfile c w i (ps l) = qs l), w i
    = ∑ i ∈ Finset.univ.filter (fun i =>
        wDeg c' w i = d ∧ ∀ l, rowProfile c' w i (ps l) = qs l), w i := by
  intro d L ps qs
  -- Use hierarchical_vandermonde_class_eq with L+1 coordinates:
  -- coordinate 0 = wDeg, coordinates 1..L = rowProfile(·, ps l)
  have hmom := multi_profile_star_moments_eq c c' hc_symm hc'_symm w h_eq
  -- First extract degree class via Vandermonde on the degree exponent
  have h_deg_fiber : ∀ (rs : Fin L → ℕ),
      ∑ i ∈ Finset.univ.filter (fun i => wDeg c w i = d),
        w i * ∏ l, (rowProfile c w i (ps l)) ^ (rs l) =
      ∑ i ∈ Finset.univ.filter (fun i => wDeg c' w i = d),
        w i * ∏ l, (rowProfile c' w i (ps l)) ^ (rs l) := by
    intro rs
    have h_vand := vandermonde_fiber_eq
      (fun i => w i * ∏ l, (rowProfile c w i (ps l)) ^ (rs l))
      (fun i => w i * ∏ l, (rowProfile c' w i (ps l)) ^ (rs l))
      (wDeg c w) (wDeg c' w) ?_ d
    · exact h_vand
    · intro m
      have := hmom m L rs ps
      convert this using 1 <;> { congr 1; ext i; ring }
  -- Convert to indicator form for hierarchical Vandermonde
  have h_ind : ∀ (rs : Fin L → ℕ),
      ∑ i, (if wDeg c w i = d then w i else 0) *
        ∏ l, (rowProfile c w i (ps l)) ^ (rs l) =
      ∑ i, (if wDeg c' w i = d then w i else 0) *
        ∏ l, (rowProfile c' w i (ps l)) ^ (rs l) := by
    intro rs; simp_rw [ite_mul, zero_mul, ← Finset.sum_filter]; exact h_deg_fiber rs
  -- Apply hierarchical Vandermonde on L profile coordinates
  have h_class := hierarchical_vandermonde_class_eq L
    (fun i => if wDeg c w i = d then w i else 0)
    (fun i => if wDeg c' w i = d then w i else 0)
    (fun l i => rowProfile c w i (ps l))
    (fun l i => rowProfile c' w i (ps l))
    h_ind qs
  -- Convert: filter (wDeg=d ∧ ∀ l, rp=qs l) with indicator → match h_class
  -- h_class : ∑_{∀ l, rowProfile c w i (ps l) = qs l} (if wDeg = d then w i else 0) = same
  -- Goal: ∑_{wDeg = d ∧ ∀ l, rowProfile = qs l} w i = same
  -- Convert goal: filter(P ∧ Q) = (filter Q).filter P via filter_filter + and_comm
  have h_filt : ∀ (c₀ : Fin k → Fin k → ℝ),
      Finset.univ.filter (fun i => wDeg c₀ w i = d ∧ ∀ l, rowProfile c₀ w i (ps l) = qs l) =
      (Finset.univ.filter (fun i => ∀ l, rowProfile c₀ w i (ps l) = qs l)).filter
        (fun i => wDeg c₀ w i = d) := by
    intro c₀; rw [Finset.filter_filter]; congr 1; ext i; exact and_comm
  rw [h_filt c, h_filt c']
  conv_lhs => rw [Finset.sum_filter]
  conv_rhs => rw [Finset.sum_filter]
  exact h_class

/-- Joint class conditional moments: within each joint class, the next
row-profile power moments match. This extends `joint_class_weight_eq`
by keeping one additional profile exponent free. -/
private theorem joint_class_conditional_moments {k : ℕ}
    (c c' : Fin k → Fin k → ℝ) (hc_symm : ∀ i j, c i j = c j i)
    (hc'_symm : ∀ i j, c' i j = c' j i)
    (w : Fin k → ℝ) (hw_pos : ∀ i, 0 < w i)
    (h_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      weightedHomSum n F c w = weightedHomSum n F c' w) :
    ∀ (d : ℝ) (L : ℕ) (ps : Fin L → ℕ) (qs : Fin L → ℝ) (p_next r : ℕ),
      ∑ i ∈ Finset.univ.filter (fun i =>
        wDeg c w i = d ∧ ∀ l, rowProfile c w i (ps l) = qs l),
        w i * (rowProfile c w i p_next) ^ r
    = ∑ i ∈ Finset.univ.filter (fun i =>
        wDeg c' w i = d ∧ ∀ l, rowProfile c' w i (ps l) = qs l),
        w i * (rowProfile c' w i p_next) ^ r := by
  intro d L ps qs p_next r
  -- Use multi_profile_star_moments_eq with L+1 branch types
  have hmom := multi_profile_star_moments_eq c c' hc_symm hc'_symm w h_eq
  -- Decompose: L existing profile coordinates + 1 extra (p_next with exponent r)
  set ps' : Fin (L + 1) → ℕ := Fin.snoc ps p_next
  -- First extract degree fiber with ring rearrangement
  have h_deg_fiber : ∀ (rs : Fin (L + 1) → ℕ),
      ∑ i ∈ Finset.univ.filter (fun i => wDeg c w i = d),
        w i * ∏ l, (rowProfile c w i (ps' l)) ^ (rs l) =
      ∑ i ∈ Finset.univ.filter (fun i => wDeg c' w i = d),
        w i * ∏ l, (rowProfile c' w i (ps' l)) ^ (rs l) := by
    intro rs
    have h_vand := vandermonde_fiber_eq
      (fun i => w i * ∏ l, (rowProfile c w i (ps' l)) ^ (rs l))
      (fun i => w i * ∏ l, (rowProfile c' w i (ps' l)) ^ (rs l))
      (wDeg c w) (wDeg c' w) ?_ d
    · exact h_vand
    · intro m
      have := hmom m (L + 1) rs ps'
      convert this using 1 <;> { congr 1; ext i; ring }
  -- Convert to indicator
  have h_ind : ∀ (rs : Fin (L + 1) → ℕ),
      ∑ i, (if wDeg c w i = d then w i else 0) *
        ∏ l, (rowProfile c w i (ps' l)) ^ (rs l) =
      ∑ i, (if wDeg c' w i = d then w i else 0) *
        ∏ l, (rowProfile c' w i (ps' l)) ^ (rs l) := by
    intro rs; simp_rw [ite_mul, zero_mul, ← Finset.sum_filter]; exact h_deg_fiber rs
  -- Direct approach: hierarchical Vandermonde on L coordinates with
  --   g(i) = (if wDeg=d then w else 0) * rp(p_next)^r
  -- and f l i = rp(ps l)
  -- Moment hypothesis: h_ind (Fin.snoc rs₀ r) rearranged
  have h_moments : ∀ (rs₀ : Fin L → ℕ),
      ∑ i, ((if wDeg c w i = d then w i else 0) * (rowProfile c w i p_next) ^ r) *
        ∏ l : Fin L, (rowProfile c w i (ps l)) ^ (rs₀ l) =
      ∑ i, ((if wDeg c' w i = d then w i else 0) * (rowProfile c' w i p_next) ^ r) *
        ∏ l : Fin L, (rowProfile c' w i (ps l)) ^ (rs₀ l) := by
    intro rs₀
    have := h_ind (Fin.snoc rs₀ r)
    convert this using 1 <;> {
      congr 1; ext i
      simp only [ps']
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
      ring }
  -- Apply hierarchical Vandermonde on L profile coordinates
  have h_class := hierarchical_vandermonde_class_eq L
    (fun i => (if wDeg c w i = d then w i else 0) * (rowProfile c w i p_next) ^ r)
    (fun i => (if wDeg c' w i = d then w i else 0) * (rowProfile c' w i p_next) ^ r)
    (fun l i => rowProfile c w i (ps l))
    (fun l i => rowProfile c' w i (ps l))
    h_moments qs
  -- h_class : ∑_{∀l, rp(c,i,ps l) = qs l} (if wDeg c w i = d then w i else 0) * rp(c,i,p_next)^r
  --         = same for c'
  -- Goal: ∑_{wDeg=d ∧ ∀l, rp=qs l} w i * rp(p_next)^r = same
  -- Convert goal: filter(P ∧ Q) = (filter Q).filter P via filter_filter + and_comm
  have h_filt : ∀ (c₀ : Fin k → Fin k → ℝ),
      Finset.univ.filter (fun i => wDeg c₀ w i = d ∧ ∀ l, rowProfile c₀ w i (ps l) = qs l) =
      (Finset.univ.filter (fun i => ∀ l, rowProfile c₀ w i (ps l) = qs l)).filter
        (fun i => wDeg c₀ w i = d) := by
    intro c₀; rw [Finset.filter_filter]; congr 1; ext i; exact and_comm
  rw [h_filt c, h_filt c']
  conv_lhs => rw [Finset.sum_filter]
  conv_rhs => rw [Finset.sum_filter]
  simp_rw [ite_mul, zero_mul] at h_class
  exact h_class

/-- For symmetric c and the same weights, equal weighted hom sums for the
permuted matrix. This is the key enabling lemma for building the permutation:
if we find π such that c'' = c' ∘ (π, π) has equal hom sums with c, then we
can reduce the problem. -/
private theorem weightedHomSum_eq_of_perm {k : ℕ}
    (c c' : Fin k → Fin k → ℝ) (w : Fin k → ℝ)
    (h_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      weightedHomSum n F c w = weightedHomSum n F c' w)
    (π : Equiv.Perm (Fin k)) (_hw : ∀ i, w i = w (π i)) :
    ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      weightedHomSum n F c w =
        weightedHomSum n F (fun i j => c' (π.symm i) (π.symm j))
          (fun i => w (π.symm i)) := by
  intro n F inst
  rw [weightedHomSum_perm_eq n F c' w π]
  exact h_eq n F

/-- Construct a permutation from a matching function with the counting property.

If for each index `i`, there's a matching target `f i` with matching entries and weight,
and the map `f` has the "counting property" (same number of preimages of each value
as the identity), then `f` is a bijection and hence a permutation. -/
private noncomputable def permOfMatching {k : ℕ}
    (f : Fin k → Fin k) (hf : Function.Injective f) : Equiv.Perm (Fin k) :=
  Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩

/-- The weighted hom sum for the edge graph K₂ (= starGraph 1) relates to
the bilinear form ∑ a b, w a * w b * c a b. -/
private theorem weightedHomSum_edge {k : ℕ} (c : Fin k → Fin k → ℝ)
    (hc : ∀ i j, c i j = c j i) (w : Fin k → ℝ) :
    weightedHomSum 2 (starGraph 1) c w = ∑ a : Fin k, ∑ b : Fin k, w a * w b * c a b := by
  have h := weightedHomSum_starGraph 1 c hc w
  simp only [wDeg, pow_one] at h
  rw [h]; congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j; ring

/-- For k=1, the wHS of the edge graph determines the unique entry. -/
private theorem k1_entry_eq {c c' : Fin 1 → Fin 1 → ℝ}
    (hc_symm : ∀ i j, c i j = c j i) (hc'_symm : ∀ i j, c' i j = c' j i)
    (w : Fin 1 → ℝ) (hw_pos : ∀ i, 0 < w i)
    (h_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      weightedHomSum n F c w = weightedHomSum n F c' w) :
    c 0 0 = c' 0 0 := by
  have h1 := weightedHomSum_edge c hc_symm w
  have h2 := weightedHomSum_edge c' hc'_symm w
  have h3 := h_eq 2 (starGraph 1)
  rw [h1, h2] at h3
  simp only [Fin.sum_univ_one] at h3
  have hw0 : w 0 ≠ 0 := ne_of_gt (hw_pos 0)
  have : w 0 * w 0 * c 0 0 = w 0 * w 0 * c' 0 0 := h3
  exact mul_left_cancel₀ (mul_ne_zero hw0 hw0) this

/-- Row-equality block constancy: if c i₁ = c i₂ and c j₁ = c j₂ (as row functions),
then c i₁ j₁ = c i₂ j₂, using symmetry of c. -/
private theorem block_const_of_row_eq {k : ℕ}
    (c : Fin k → Fin k → ℝ) (hc_symm : ∀ i j, c i j = c j i)
    {i₁ i₂ j₁ j₂ : Fin k}
    (hi : c i₁ = c i₂) (hj : c j₁ = c j₂) :
    c i₁ j₁ = c i₂ j₂ := by
  calc c i₁ j₁ = c i₂ j₁ := congr_fun hi j₁
    _ = c j₁ i₂ := hc_symm i₂ j₁
    _ = c j₂ i₂ := congr_fun hj i₂
    _ = c i₂ j₂ := hc_symm j₂ i₂

/-- When wDeg values are all distinct, rowProfile matching for all p implies
the row functions agree. -/
private theorem row_eq_of_rowProfile_eq_injective_wDeg {k : ℕ}
    (c : Fin k → Fin k → ℝ) (w : Fin k → ℝ) (hw_pos : ∀ i, 0 < w i)
    (h_inj : Function.Injective (wDeg c w))
    {i₁ i₂ : Fin k}
    (h_rp : ∀ p : ℕ, rowProfile c w i₁ p = rowProfile c w i₂ p) :
    c i₁ = c i₂ := by
  funext j
  have h1 : ∀ p : Fin k, ∑ l, (w l * c i₁ l - w l * c i₂ l) * (wDeg c w l) ^ (p : ℕ) = 0 := by
    intro p
    have := h_rp p
    simp only [rowProfile] at this
    have hsub : ∀ l : Fin k,
      (w l * c i₁ l - w l * c i₂ l) * (wDeg c w l) ^ (p : ℕ) =
      w l * c i₁ l * (wDeg c w l) ^ (p : ℕ) -
      w l * c i₂ l * (wDeg c w l) ^ (p : ℕ) := fun l => by ring
    simp_rw [hsub, Finset.sum_sub_distrib]
    linarith
  have h2 : (fun l => w l * c i₁ l - w l * c i₂ l) = 0 :=
    eq_zero_of_weighted_powers_eq_zero (wDeg c w) h_inj _ h1
  have h3 := congr_fun h2 j
  simp only [Pi.zero_apply, sub_eq_zero] at h3
  exact mul_left_cancel₀ (ne_of_gt (hw_pos j)) h3

/-- Weighted row-entry matching via Vandermonde: when wDeg c w is injective,
rowProfile matching across c and c' gives that for each j, the weighted entry
w j * c i j equals the sum over indices with matching degree in c'. -/
private theorem weighted_entry_eq_of_injective_wDeg {k : ℕ}
    (c c' : Fin k → Fin k → ℝ) (w : Fin k → ℝ)
    (h_inj : Function.Injective (wDeg c w))
    {i i' : Fin k}
    (h_rp : ∀ p : ℕ, rowProfile c w i p = rowProfile c' w i' p)
    (j : Fin k) :
    w j * c i j = ∑ l ∈ Finset.univ.filter (fun l => wDeg c' w l = wDeg c w j),
      w l * c' i' l := by
  set S := Finset.univ.image (wDeg c w)
  set S' := Finset.univ.image (wDeg c' w)
  have h_fib : ∀ m : ℕ,
      ∑ d ∈ S ∪ S', (∑ l ∈ Finset.univ.filter (fun l => wDeg c w l = d),
        w l * c i l) * d ^ m =
      ∑ d ∈ S ∪ S', (∑ l ∈ Finset.univ.filter (fun l => wDeg c' w l = d),
        w l * c' i' l) * d ^ m := by
    intro m
    rw [← Finset.sum_subset Finset.subset_union_left (fun d _ hd => by
      rw [show (∑ l ∈ Finset.univ.filter (fun l => wDeg c w l = d), w l * c i l) = 0 from
        Finset.sum_eq_zero fun l hl => absurd (Finset.mem_image.mpr ⟨l, Finset.mem_univ l,
          (Finset.mem_filter.mp hl).2⟩) hd, zero_mul]),
     ← Finset.sum_subset Finset.subset_union_right (fun d _ hd => by
      rw [show (∑ l ∈ Finset.univ.filter (fun l => wDeg c' w l = d), w l * c' i' l) = 0 from
        Finset.sum_eq_zero fun l hl => absurd (Finset.mem_image.mpr ⟨l, Finset.mem_univ l,
          (Finset.mem_filter.mp hl).2⟩) hd, zero_mul])]
    have := h_rp m; simp only [rowProfile] at this
    rw [sum_fiberwise_mul_pow (fun l => w l * c i l) (wDeg c w) m,
        sum_fiberwise_mul_pow (fun l => w l * c' i' l) (wDeg c' w) m] at this
    exact this
  have hd_mem : wDeg c w j ∈ S ∪ S' :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  have h_eq_at_d := finset_weighted_powers_eq (S ∪ S') _ _ h_fib (wDeg c w j) hd_mem
  rw [show Finset.univ.filter (fun l => wDeg c w l = wDeg c w j) = {j} from by
    ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => h_inj h, fun h => h ▸ rfl⟩,
    Finset.sum_singleton] at h_eq_at_d
  exact h_eq_at_d

/-! ### Row-class machinery for collapse -/

/-- The set of distinct row functions of a matrix. -/
private noncomputable def rowImage {k : ℕ} (c : Fin k → Fin k → ℝ) : Finset (Fin k → ℝ) :=
  Finset.univ.image c

/-- Number of distinct rows (= number of row equivalence classes). -/
private noncomputable def numRowClasses {k : ℕ} (c : Fin k → Fin k → ℝ) : ℕ :=
  Fintype.card ↥(rowImage c)

private theorem mem_rowImage {k : ℕ} (c : Fin k → Fin k → ℝ) (i : Fin k) :
    c i ∈ rowImage c :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- Bijection between the subtype of distinct row functions and `Fin T`. -/
private noncomputable def rowImageEquiv {k : ℕ} (c : Fin k → Fin k → ℝ) :
    ↥(rowImage c) ≃ Fin (numRowClasses c) :=
  Fintype.equivFin _

/-- Map each index to its row equivalence class. -/
private noncomputable def rowClassMap {k : ℕ} (c : Fin k → Fin k → ℝ) :
    Fin k → Fin (numRowClasses c) :=
  fun i => rowImageEquiv c ⟨c i, mem_rowImage c i⟩

/-- A representative index for each row equivalence class. -/
private noncomputable def rowClassRep {k : ℕ} (c : Fin k → Fin k → ℝ) :
    Fin (numRowClasses c) → Fin k :=
  fun s => (Finset.mem_image.mp ((rowImageEquiv c).symm s).prop).choose

/-- The representative's row function matches the class it represents. -/
private theorem rowClassRep_row {k : ℕ} (c : Fin k → Fin k → ℝ)
    (s : Fin (numRowClasses c)) :
    c (rowClassRep c s) = ((rowImageEquiv c).symm s : ↥(rowImage c)).val :=
  (Finset.mem_image.mp ((rowImageEquiv c).symm s).prop).choose_spec.2

private theorem rowClassMap_rep {k : ℕ} (c : Fin k → Fin k → ℝ)
    (s : Fin (numRowClasses c)) :
    rowClassMap c (rowClassRep c s) = s := by
  unfold rowClassMap
  have h := rowClassRep_row c s
  have : (⟨c (rowClassRep c s), mem_rowImage c _⟩ : ↥(rowImage c)) =
      (rowImageEquiv c).symm s := Subtype.ext h
  rw [this, Equiv.apply_symm_apply]

/-- `c (rep (rcm i)) = c i` as row functions. -/
private theorem row_of_rep_classMap {k : ℕ} (c : Fin k → Fin k → ℝ) (i : Fin k) :
    c (rowClassRep c (rowClassMap c i)) = c i := by
  have h := rowClassRep_row c (rowClassMap c i)
  rw [h]; simp [rowClassMap, Equiv.symm_apply_apply]

/-- Same row class iff same row function. -/
private theorem rowClassMap_eq_iff {k : ℕ} (c : Fin k → Fin k → ℝ) (i j : Fin k) :
    rowClassMap c i = rowClassMap c j ↔ c i = c j := by
  constructor
  · intro h
    have h1 := row_of_rep_classMap c i
    have h2 := row_of_rep_classMap c j
    rw [h] at h1; exact h1.symm.trans h2
  · intro h
    show rowImageEquiv c ⟨c i, mem_rowImage c i⟩ = rowImageEquiv c ⟨c j, mem_rowImage c j⟩
    exact congr_arg (rowImageEquiv c) (Subtype.ext h)

/-- Collapsed matrix on row classes. -/
private noncomputable def collapsedMatrix {k : ℕ} (c : Fin k → Fin k → ℝ) :
    Fin (numRowClasses c) → Fin (numRowClasses c) → ℝ :=
  fun s t => c (rowClassRep c s) (rowClassRep c t)

/-- Collapsed weights: total weight per row class. -/
private noncomputable def collapsedWeights {k : ℕ} (c : Fin k → Fin k → ℝ)
    (w : Fin k → ℝ) : Fin (numRowClasses c) → ℝ :=
  fun s => ∑ i ∈ Finset.univ.filter (fun i => rowClassMap c i = s), w i

/-! ### Structural lemmas for collapsed matrix -/

private theorem collapsedMatrix_symm {k : ℕ} (c : Fin k → Fin k → ℝ)
    (hc_symm : ∀ i j, c i j = c j i) (s t : Fin (numRowClasses c)) :
    collapsedMatrix c s t = collapsedMatrix c t s :=
  hc_symm _ _

private theorem collapsedMatrix_mem {k : ℕ} (c : Fin k → Fin k → ℝ)
    (hc_mem : ∀ i j, c i j ∈ Set.Icc 0 1) (s t : Fin (numRowClasses c)) :
    collapsedMatrix c s t ∈ Set.Icc 0 1 :=
  hc_mem _ _

private theorem collapsedWeights_pos {k : ℕ} (c : Fin k → Fin k → ℝ)
    (w : Fin k → ℝ) (hw_pos : ∀ i, 0 < w i) (s : Fin (numRowClasses c)) :
    0 < collapsedWeights c w s := by
  apply Finset.sum_pos
  · exact fun i _ => hw_pos i
  · exact ⟨rowClassRep c s,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rowClassMap_rep c s⟩⟩

/-- Distinct row classes have distinct collapsed rows (twin-free). -/
private theorem collapsed_twin_free {k : ℕ} (c : Fin k → Fin k → ℝ)
    (hc_symm : ∀ i j, c i j = c j i) (s₁ s₂ : Fin (numRowClasses c))
    (hs : s₁ ≠ s₂) :
    collapsedMatrix c s₁ ≠ collapsedMatrix c s₂ := by
  intro h_eq
  apply hs
  have h_row : c (rowClassRep c s₁) ≠ c (rowClassRep c s₂) := by
    intro h
    exact hs (by rw [← rowClassMap_rep c s₁, ← rowClassMap_rep c s₂,
      (rowClassMap_eq_iff c _ _).mpr h])
  exfalso; apply h_row; funext j
  have h_at := congr_fun h_eq (rowClassMap c j)
  simp only [collapsedMatrix] at h_at
  have h1 := block_const_of_row_eq c hc_symm
    (rfl : c (rowClassRep c s₁) = c (rowClassRep c s₁)) (row_of_rep_classMap c j).symm
  have h2 := block_const_of_row_eq c hc_symm
    (rfl : c (rowClassRep c s₂) = c (rowClassRep c s₂)) (row_of_rep_classMap c j).symm
  linarith

/-! ### Weighted hom sum is preserved by row collapse -/

set_option maxHeartbeats 800000 in
private theorem weightedHomSum_collapse {k : ℕ}
    (c : Fin k → Fin k → ℝ) (hc_symm : ∀ i j, c i j = c j i)
    (w : Fin k → ℝ) (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
    weightedHomSum n F c w =
    weightedHomSum n F (collapsedMatrix c) (collapsedWeights c w) := by
  simp only [weightedHomSum, collapsedMatrix, collapsedWeights]
  symm
  -- Step 1: Convert filter sums to conditional sums
  simp_rw [Finset.sum_filter]
  -- Step 2: Product of sums → sum of products (Fintype.prod_sum)
  simp_rw [Fintype.prod_sum]
  -- Step 3: Distribute multiplication into sum
  simp_rw [Finset.sum_mul]
  -- Step 4: Swap sums (τ, σ) → (σ, τ)
  rw [Finset.sum_comm]
  -- Step 5: Evaluate inner sum for each σ (only τ = rcm ∘ σ survives)
  congr 1; ext σ
  have h_ind : ∀ τ : Fin n → Fin (numRowClasses c),
      (∏ v : Fin n, if rowClassMap c (σ v) = τ v then w (σ v) else (0 : ℝ)) =
      if τ = fun v => rowClassMap c (σ v) then ∏ v, w (σ v) else 0 := by
    intro τ; by_cases h : τ = fun v => rowClassMap c (σ v)
    · subst h; simp
    · rw [if_neg h]
      obtain ⟨v, hv⟩ : ∃ v, ¬(rowClassMap c (σ v) = τ v) := by
        by_contra hall; push_neg at hall; exact h (funext hall).symm
      exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)
  simp_rw [h_ind, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1; apply Finset.prod_congr rfl; intro e _
  exact block_const_of_row_eq c hc_symm (row_of_rep_classMap c _) (row_of_rep_classMap c _)

/-! ### 1-labeled quantum graph evaluation -/

/-- Rooted evaluation: fix vertex 0 at color `i`, sum over all colorings of non-root vertices.
This is the "1-labeled" quantum graph evaluation from Lovász [2012] §5.2. -/
noncomputable def rootedEval {k : ℕ} (n : ℕ) (F : SimpleGraph (Fin (n + 1)))
    [DecidableRel F.Adj] (c : Fin k → Fin k → ℝ) (w : Fin k → ℝ)
    (i : Fin k) : ℝ :=
  ∑ σ : Fin n → Fin k,
    let τ : Fin (n + 1) → Fin k := Fin.cons i σ
    (∏ v : Fin n, w (σ v)) *
    ∏ e ∈ F.edgeFinset, c (τ (Quot.out e).1) (τ (Quot.out e).2)

/-- Summing `rootedEval` over all root colors with weights recovers `weightedHomSum`. -/
private theorem rootedEval_weighted_sum {k : ℕ} (n : ℕ)
    (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj]
    (c : Fin k → Fin k → ℝ) (w : Fin k → ℝ) :
    ∑ i, w i * rootedEval n F c w i = weightedHomSum (n + 1) F c w := by
  simp only [rootedEval, weightedHomSum]
  conv_rhs =>
    rw [(Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => Fin k)) _).symm]
  simp only [Fin.consEquiv_apply]
  rw [Fintype.sum_prod_type]
  congr 1; ext i
  rw [Finset.mul_sum]
  congr 1; ext σ
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

/-! ### Root attachment -/

/-- Attach a new root vertex (vertex 0) to the old root (vertex 1) by an edge.
Old vertices of `G` are shifted up by 1 in the new graph. -/
private def rootAttach (n : ℕ) (G : SimpleGraph (Fin (n + 1))) :
    SimpleGraph (Fin (n + 2)) where
  Adj u v :=
    (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) ∨
    (1 ≤ u.val ∧ 1 ≤ v.val ∧
      G.Adj ⟨u.val - 1, by omega⟩ ⟨v.val - 1, by omega⟩)
  symm := by
    intro u v h
    rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv, hadj⟩
    · right; left; exact ⟨hv, hu⟩
    · left; exact ⟨hv, hu⟩
    · right; right; exact ⟨hv, hu, G.symm hadj⟩
  loopless := by
    intro v h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨_, _, hadj⟩
    · omega
    · omega
    · exact G.loopless _ hadj

private instance rootAttachDecRel (n : ℕ) (G : SimpleGraph (Fin (n + 1)))
    [DecidableRel G.Adj] : DecidableRel (rootAttach n G).Adj :=
  fun u v =>
    inferInstanceAs (Decidable
      ((u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) ∨
       (1 ≤ u.val ∧ 1 ≤ v.val ∧
        G.Adj ⟨u.val - 1, by omega⟩ ⟨v.val - 1, by omega⟩)))

/-- The edge finset of `rootAttach n G` is the bridge edge plus shifted `G`-edges. -/
private theorem rootAttach_edgeFinset (n : ℕ) (G : SimpleGraph (Fin (n + 1)))
    [DecidableRel G.Adj] :
    (rootAttach n G).edgeFinset =
      insert s((0 : Fin (n + 2)), ⟨1, by omega⟩)
        (G.edgeFinset.map (Fin.succEmb (n + 1)).sym2Map) := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, Finset.mem_insert, Finset.mem_map,
    Function.Embedding.sym2Map_apply]
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      change ((a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0) ∨
        (1 ≤ a.val ∧ 1 ≤ b.val ∧
          G.Adj ⟨a.val - 1, by omega⟩ ⟨b.val - 1, by omega⟩)) at he
      rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb, hadj⟩
      · left; exact Sym2.eq_iff.mpr (Or.inl ⟨Fin.ext ha, Fin.ext hb⟩)
      · left; exact Sym2.eq_iff.mpr (Or.inr ⟨Fin.ext ha, Fin.ext hb⟩)
      · right
        refine ⟨s(⟨a.val - 1, by omega⟩, ⟨b.val - 1, by omega⟩), hadj, ?_⟩
        simp only [Sym2.map_pair_eq, Fin.coe_succEmb]
        exact Sym2.eq_iff.mpr
          (Or.inl ⟨Fin.ext (by simp [Fin.val_succ]; omega),
                   Fin.ext (by simp [Fin.val_succ]; omega)⟩)
  · intro he
    rcases he with rfl | ⟨e', he', rfl⟩
    · -- Bridge edge: s(0, ⟨1,_⟩) is in rootAttach
      rw [SimpleGraph.mem_edgeSet]
      exact Or.inl ⟨rfl, rfl⟩
    · -- Shifted G-edge
      induction e' using Sym2.ind with
      | _ a b =>
        rw [SimpleGraph.mem_edgeSet] at he'
        simp only [Sym2.map_pair_eq, Fin.coe_succEmb, SimpleGraph.mem_edgeSet]
        exact Or.inr (Or.inr ⟨by simp [Fin.val_succ], by simp [Fin.val_succ],
          by convert he' using 2⟩)

/-- The bridge edge is not a shifted `G`-edge. -/
private theorem rootAttach_bridge_not_mem_shifted (n : ℕ)
    (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] :
    s((0 : Fin (n + 2)), ⟨1, by omega⟩) ∉
      G.edgeFinset.map (Fin.succEmb (n + 1)).sym2Map := by
  intro hmem
  rw [Finset.mem_map] at hmem
  obtain ⟨e, _, he⟩ := hmem
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq, Fin.coe_succEmb] at he
    rw [Sym2.eq_iff] at he
    rcases he with ⟨h1, _⟩ | ⟨_, h1⟩ <;>
      exact absurd (congr_arg Fin.val h1) (by simp [Fin.val_succ])

/-- The edge product over `rootAttach n G` equals the bridge term times the shifted
`G`-edge product (requires symmetric matrix). -/
private theorem rootAttach_prod_eq {k : ℕ} (n : ℕ) (G : SimpleGraph (Fin (n + 1)))
    [DecidableRel G.Adj] (c : Fin k → Fin k → ℝ) (hc : ∀ i j, c i j = c j i)
    (τ : Fin (n + 2) → Fin k) :
    ∏ e ∈ (rootAttach n G).edgeFinset,
      c (τ (Quot.out e).1) (τ (Quot.out e).2) =
    c (τ 0) (τ (Fin.succ (0 : Fin (n + 1)))) *
    ∏ e ∈ G.edgeFinset,
      c (τ (Fin.succ (Quot.out e).1)) (τ (Fin.succ (Quot.out e).2)) := by
  have h1eq : (⟨1, by omega⟩ : Fin (n + 2)) = Fin.succ (0 : Fin (n + 1)) :=
    Fin.ext (by simp)
  rw [rootAttach_edgeFinset,
    Finset.prod_insert (rootAttach_bridge_not_mem_shifted n G),
    Finset.prod_map G.edgeFinset (Fin.succEmb (n + 1)).sym2Map]
  congr 1
  · -- Bridge edge: resolve Quot.out
    have hout := Quot.out_eq s((0 : Fin (n + 2)), ⟨1, by omega⟩)
    rw [Sym2.mk_eq_mk_iff] at hout
    rcases hout with h | h
    · rw [congr_arg Prod.fst h, congr_arg Prod.snd h, h1eq]
    · have h1 := congr_arg Prod.fst h; have h2 := congr_arg Prod.snd h
      simp only [Prod.swap] at h1 h2
      rw [h1, h2, h1eq, hc]
  · congr 1; ext e
    -- Shifted edge: resolve Quot.out of mapped edge (use symmetry of c)
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq, Fin.coe_succEmb]
      have hout := Quot.out_eq s(Fin.succ a, Fin.succ b)
      rw [Sym2.mk_eq_mk_iff] at hout
      have hout' := Quot.out_eq s(a, b)
      rw [Sym2.mk_eq_mk_iff] at hout'
      rcases hout with h | h <;> rcases hout' with h' | h'
      · rw [congr_arg Prod.fst h, congr_arg Prod.snd h,
            congr_arg Prod.fst h', congr_arg Prod.snd h']
      · rw [congr_arg Prod.fst h, congr_arg Prod.snd h]
        simp only [Prod.swap] at h'
        rw [congr_arg Prod.fst h', congr_arg Prod.snd h', hc]
      · simp only [Prod.swap] at h
        rw [congr_arg Prod.fst h, congr_arg Prod.snd h,
            congr_arg Prod.fst h', congr_arg Prod.snd h', hc]
      · simp only [Prod.swap] at h h'
        rw [congr_arg Prod.fst h, congr_arg Prod.snd h,
            congr_arg Prod.fst h', congr_arg Prod.snd h']

set_option maxHeartbeats 1600000 in
/-- Root attachment realizes the weighted adjacency operator:
`rootedEval(rootAttach G)(i) = ∑ⱼ wⱼ c(i,j) rootedEval(G)(j)`. -/
private theorem rootedEval_rootAttach {k : ℕ} (n : ℕ)
    (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]
    (c : Fin k → Fin k → ℝ) (hc : ∀ i j, c i j = c j i)
    (w : Fin k → ℝ) (i : Fin k) :
    rootedEval (n + 1) (rootAttach n G) c w i =
    ∑ j, w j * c i j * rootedEval n G c w j := by
  simp only [rootedEval]
  -- Step 1: Rewrite each summand
  -- After simp only [rootedEval], both sides are sums. We first simplify
  -- each LHS summand using edge product decomposition, then reindex.
  -- Step 1: Reindex the LHS sum: decompose σ into (j, σ') via Fin.consEquiv.
  rw [(Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => Fin k)) _).symm]
  simp only [Fin.consEquiv_apply]
  rw [Fintype.sum_prod_type]
  congr 1; ext j; rw [Finset.mul_sum]; congr 1; ext σ'
  -- Step 2: Normalize: (Fin.consEquiv ...) (j, σ') = Fin.cons j σ'
  have h_eq : (Fin.consEquiv (fun _ : Fin (n + 1) => Fin k)) (j, σ') = Fin.cons j σ' := rfl
  simp only [h_eq]
  -- Factor the edge product using rootAttach_prod_eq.
  have h_edges := rootAttach_prod_eq n G c hc (Fin.cons i (Fin.cons j σ'))
  simp only [Fin.cons_zero, Fin.cons_succ] at h_edges
  rw [h_edges]
  -- Step 3: Simplify weight product, then ring.
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_succ]
  ring

/-! ### Graph gluing -/

private def rootGlueEmb₁ (n₁ n₂ : ℕ) : Fin (n₁ + 1) ↪ Fin (n₁ + n₂ + 1) where
  toFun v := ⟨v.val, by omega⟩
  inj' a b h := Fin.ext (by simpa using congr_arg Fin.val h)

private def rootGlueEmb₂ (n₁ n₂ : ℕ) : Fin (n₂ + 1) ↪ Fin (n₁ + n₂ + 1) where
  toFun v := if v.val = 0 then ⟨0, by omega⟩ else ⟨n₁ + v.val, by omega⟩
  inj' a b h := by
    simp only at h
    by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0 <;>
      simp [ha, hb] at h <;> exact Fin.ext (by omega)

private def rootGlue (n₁ n₂ : ℕ) (F₁ : SimpleGraph (Fin (n₁ + 1)))
    (F₂ : SimpleGraph (Fin (n₂ + 1))) : SimpleGraph (Fin (n₁ + n₂ + 1)) where
  Adj u v :=
    (∃ (_ : u.val ≤ n₁) (_ : v.val ≤ n₁),
      F₁.Adj ⟨u.val, by omega⟩ ⟨v.val, by omega⟩) ∨
    ((u.val = 0 ∨ n₁ < u.val) ∧ (v.val = 0 ∨ n₁ < v.val) ∧
      F₂.Adj ⟨if u.val = 0 then 0 else u.val - n₁, by have := u.isLt; split_ifs <;> omega⟩
            ⟨if v.val = 0 then 0 else v.val - n₁, by have := v.isLt; split_ifs <;> omega⟩)
  symm := by
    intro u v h
    rcases h with ⟨hu, hv, hadj⟩ | ⟨hu, hv, hadj⟩
    · left; exact ⟨hv, hu, by convert F₁.symm hadj using 2 <;> exact Fin.ext rfl⟩
    · right; exact ⟨hv, hu, F₂.symm hadj⟩
  loopless := by
    intro v h
    rcases h with ⟨_, _, hadj⟩ | ⟨_, _, hadj⟩
    · exact F₁.loopless _ hadj
    · exact F₂.loopless _ hadj

private instance rootGlueDecRel (n₁ n₂ : ℕ) (F₁ : SimpleGraph (Fin (n₁ + 1)))
    (F₂ : SimpleGraph (Fin (n₂ + 1))) [DecidableRel F₁.Adj] [DecidableRel F₂.Adj] :
    DecidableRel (rootGlue n₁ n₂ F₁ F₂).Adj :=
  fun u v => inferInstanceAs (Decidable
    ((∃ (_ : u.val ≤ n₁) (_ : v.val ≤ n₁),
      F₁.Adj ⟨u.val, by omega⟩ ⟨v.val, by omega⟩) ∨
     ((u.val = 0 ∨ n₁ < u.val) ∧ (v.val = 0 ∨ n₁ < v.val) ∧
      F₂.Adj ⟨if u.val = 0 then 0 else u.val - n₁, by have := u.isLt; split_ifs <;> omega⟩
            ⟨if v.val = 0 then 0 else v.val - n₁, by have := v.isLt; split_ifs <;> omega⟩)))

private theorem rootGlue_edgeFinset (n₁ n₂ : ℕ) (F₁ : SimpleGraph (Fin (n₁ + 1)))
    (F₂ : SimpleGraph (Fin (n₂ + 1))) [DecidableRel F₁.Adj] [DecidableRel F₂.Adj] :
    (rootGlue n₁ n₂ F₁ F₂).edgeFinset =
      F₁.edgeFinset.map (rootGlueEmb₁ n₁ n₂).sym2Map ∪
      F₂.edgeFinset.map (rootGlueEmb₂ n₁ n₂).sym2Map := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, Finset.mem_union, Finset.mem_map,
    Function.Embedding.sym2Map_apply]
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      change ((∃ (_ : a.val ≤ n₁) (_ : b.val ≤ n₁), _) ∨ _) at he
      rcases he with ⟨ha, hb, hadj⟩ | ⟨ha, hb, hadj⟩
      · left
        refine ⟨s(⟨a.val, by omega⟩, ⟨b.val, by omega⟩), hadj, ?_⟩
        simp only [Sym2.map_pair_eq, rootGlueEmb₁]
        exact Sym2.eq_iff.mpr (Or.inl ⟨Fin.ext rfl, Fin.ext rfl⟩)
      · right
        refine ⟨s(⟨if a.val = 0 then 0 else a.val - n₁, by have := a.isLt; split_ifs <;> omega⟩,
                  ⟨if b.val = 0 then 0 else b.val - n₁, by have := b.isLt; split_ifs <;> omega⟩),
                hadj, ?_⟩
        simp only [Sym2.map_pair_eq, rootGlueEmb₂, Function.Embedding.coeFn_mk]
        apply Sym2.eq_iff.mpr; left; constructor
        · apply Fin.ext
          rcases ha with ha₀ | ha₁
          · simp [ha₀]
          · simp only [if_neg (show ¬ a.val = 0 from by omega),
                       if_neg (show ¬ (a.val - n₁ = 0) from by omega)]
            omega
        · apply Fin.ext
          rcases hb with hb₀ | hb₁
          · simp [hb₀]
          · simp only [if_neg (show ¬ b.val = 0 from by omega),
                       if_neg (show ¬ (b.val - n₁ = 0) from by omega)]
            omega
  · intro he
    rcases he with ⟨e', he', rfl⟩ | ⟨e', he', rfl⟩
    · induction e' using Sym2.ind with
      | _ a b =>
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he'
        simp only [Sym2.map_pair_eq, rootGlueEmb₁, SimpleGraph.mem_edgeSet,
          rootGlue, Function.Embedding.coeFn_mk]
        exact Or.inl ⟨by have := a.isLt; omega, by have := b.isLt; omega,
               by convert he' using 2 <;> exact Fin.ext (by simp)⟩
    · induction e' using Sym2.ind with
      | _ a b =>
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he'
        simp only [Sym2.map_pair_eq, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        show (rootGlue n₁ n₂ F₁ F₂).Adj (rootGlueEmb₂ n₁ n₂ a) (rootGlueEmb₂ n₁ n₂ b)
        apply Or.inr
        refine ⟨?_, ?_, ?_⟩
        · have : ((rootGlueEmb₂ n₁ n₂ a).val = 0) ∨ (n₁ < (rootGlueEmb₂ n₁ n₂ a).val) := by
            simp only [rootGlueEmb₂, Function.Embedding.coeFn_mk]
            rcases Nat.eq_zero_or_pos a.val with ha | ha
            · left; simp [ha]
            · right; simp only [if_neg (Nat.pos_iff_ne_zero.mp ha)]; omega
          exact this
        · have : ((rootGlueEmb₂ n₁ n₂ b).val = 0) ∨ (n₁ < (rootGlueEmb₂ n₁ n₂ b).val) := by
            simp only [rootGlueEmb₂, Function.Embedding.coeFn_mk]
            rcases Nat.eq_zero_or_pos b.val with hb | hb
            · left; simp [hb]
            · right; simp only [if_neg (Nat.pos_iff_ne_zero.mp hb)]; omega
          exact this
        · simp only [rootGlueEmb₂, Function.Embedding.coeFn_mk]
          convert he' using 2 <;>
            (simp only [apply_ite Fin.val]; split_ifs <;> omega)

private theorem rootGlue_edgeFinset_disjoint (n₁ n₂ : ℕ)
    (F₁ : SimpleGraph (Fin (n₁ + 1))) (F₂ : SimpleGraph (Fin (n₂ + 1)))
    [DecidableRel F₁.Adj] [DecidableRel F₂.Adj] :
    Disjoint
      (F₁.edgeFinset.map (rootGlueEmb₁ n₁ n₂).sym2Map)
      (F₂.edgeFinset.map (rootGlueEmb₂ n₁ n₂).sym2Map) := by
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  rw [Finset.mem_map] at he₁ he₂
  obtain ⟨e₁, he₁', rfl⟩ := he₁
  obtain ⟨e₂, he₂', he₂eq⟩ := he₂
  induction e₁ using Sym2.ind with
  | _ a₁ b₁ =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he₁'
    induction e₂ using Sym2.ind with
    | _ a₂ b₂ =>
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq,
        rootGlueEmb₁, rootGlueEmb₂, Function.Embedding.coeFn_mk] at he₂eq
      have hne := F₁.ne_of_adj he₁'
      have ha₁ := a₁.isLt; have hb₁ := b₁.isLt
      rw [Sym2.eq_iff] at he₂eq
      rcases he₂eq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> {
        have h1v := congr_arg Fin.val h1
        have h2v := congr_arg Fin.val h2
        simp only [Fin.val_mk] at h1v h2v
        by_cases ha₂ : a₂.val = 0 <;> by_cases hb₂ : b₂.val = 0 <;>
          simp only [ha₂, hb₂, ite_true, ite_false, Fin.val_mk] at h1v h2v <;>
          (first | omega | exact absurd (Fin.ext (by omega)) hne |
                   exact absurd (Fin.ext (by omega)) (Ne.symm hne))
      }

set_option maxHeartbeats 1600000 in
private theorem rootGlue_prod_eq {k : ℕ} (n₁ n₂ : ℕ)
    (F₁ : SimpleGraph (Fin (n₁ + 1))) (F₂ : SimpleGraph (Fin (n₂ + 1)))
    [DecidableRel F₁.Adj] [DecidableRel F₂.Adj]
    (c : Fin k → Fin k → ℝ) (hc : ∀ i j, c i j = c j i)
    (σ : Fin (n₁ + n₂ + 1) → Fin k) :
    ∏ e ∈ (rootGlue n₁ n₂ F₁ F₂).edgeFinset,
      c (σ (Quot.out e).1) (σ (Quot.out e).2) =
    (∏ e ∈ F₁.edgeFinset,
      c (σ (rootGlueEmb₁ n₁ n₂ (Quot.out e).1))
        (σ (rootGlueEmb₁ n₁ n₂ (Quot.out e).2))) *
    (∏ e ∈ F₂.edgeFinset,
      c (σ (rootGlueEmb₂ n₁ n₂ (Quot.out e).1))
        (σ (rootGlueEmb₂ n₁ n₂ (Quot.out e).2))) := by
  rw [rootGlue_edgeFinset,
    Finset.prod_union (rootGlue_edgeFinset_disjoint n₁ n₂ F₁ F₂)]
  have prod_map_eq : ∀ {n : ℕ} {F : SimpleGraph (Fin (n + 1))} [DecidableRel F.Adj]
      (emb : Fin (n + 1) ↪ Fin (n₁ + n₂ + 1)),
      ∏ e ∈ F.edgeFinset.map emb.sym2Map,
        c (σ (Quot.out e).1) (σ (Quot.out e).2) =
      ∏ e ∈ F.edgeFinset,
        c (σ (emb (Quot.out e).1)) (σ (emb (Quot.out e).2)) := by
    intro n F _ emb
    rw [Finset.prod_map]
    congr 1; ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq, Function.comp_apply]
      have hout_new := Quot.out_eq (Sym2.map emb s(a, b))
      rw [Sym2.map_pair_eq] at hout_new
      have hout_old := Quot.out_eq s(a, b)
      rw [Sym2.mk_eq_mk_iff] at hout_new hout_old
      rcases hout_new with hn | hn <;> rcases hout_old with ho | ho <;> {
        rw [congr_arg Prod.fst hn, congr_arg Prod.snd hn,
            congr_arg Prod.fst ho, congr_arg Prod.snd ho]
        try rfl
        try exact hc _ _
      }
  congr 1
  · exact prod_map_eq (rootGlueEmb₁ n₁ n₂)
  · exact prod_map_eq (rootGlueEmb₂ n₁ n₂)

/-- rootedEval of the trivial graph (0 non-root vertices, no edges) is 1. -/
private theorem rootedEval_trivial {k : ℕ} (c : Fin k → Fin k → ℝ) (w : Fin k → ℝ)
    (i : Fin k) : rootedEval 0 (⊥ : SimpleGraph (Fin 1)) c w i = 1 := by
  simp [rootedEval, SimpleGraph.edgeFinset]

/-- Graph gluing at the root produces pointwise multiplication of rootedEval.
This is the algebraic content of "1-labeled quantum graphs form an algebra". -/
private theorem rootedEval_glue_exists (n₁ n₂ : ℕ)
    (F₁ : SimpleGraph (Fin (n₁ + 1))) (F₂ : SimpleGraph (Fin (n₂ + 1)))
    [DecidableRel F₁.Adj] [DecidableRel F₂.Adj] :
    ∃ (n₃ : ℕ) (F₃ : SimpleGraph (Fin (n₃ + 1))) (_ : DecidableRel F₃.Adj),
      ∀ {k : ℕ} (c : Fin k → Fin k → ℝ) (hc : ∀ i j, c i j = c j i)
        (w : Fin k → ℝ) (i : Fin k),
        rootedEval n₃ F₃ c w i = rootedEval n₁ F₁ c w i * rootedEval n₂ F₂ c w i := by
  refine ⟨n₁ + n₂, rootGlue n₁ n₂ F₁ F₂, rootGlueDecRel n₁ n₂ F₁ F₂, ?_⟩
  intro k c hc w i
  simp only [rootedEval]
  have h_emb₁ : ∀ σ : Fin (n₁ + n₂) → Fin k, ∀ v : Fin (n₁ + 1),
      (Fin.cons i σ : Fin (n₁ + n₂ + 1) → Fin k) (rootGlueEmb₁ n₁ n₂ v) =
      (Fin.cons i (fun j => σ (Fin.castAdd n₂ j)) : Fin (n₁ + 1) → Fin k) v := by
    intro σ v
    rcases Fin.eq_zero_or_eq_succ v with rfl | ⟨j, rfl⟩
    · simp [rootGlueEmb₁, Fin.cons_zero]
    · simp only [Fin.cons_succ, rootGlueEmb₁, Function.Embedding.coeFn_mk]
      congr 1; exact Fin.ext (by simp [Fin.castAdd])
  have h_emb₂ : ∀ σ : Fin (n₁ + n₂) → Fin k, ∀ v : Fin (n₂ + 1),
      (Fin.cons i σ : Fin (n₁ + n₂ + 1) → Fin k) (rootGlueEmb₂ n₁ n₂ v) =
      (Fin.cons i (fun j => σ (Fin.natAdd n₁ j)) : Fin (n₂ + 1) → Fin k) v := by
    intro σ v
    rcases Fin.eq_zero_or_eq_succ v with rfl | ⟨j, rfl⟩
    · simp [rootGlueEmb₂, Fin.cons_zero]
    · simp only [Fin.cons_succ, rootGlueEmb₂, Function.Embedding.coeFn_mk,
        if_neg (show (Fin.succ j).val ≠ 0 from Nat.succ_ne_zero _)]
      congr 1; exact Fin.ext (by simp [Fin.natAdd])
  -- Factor the LHS sum as a product of two sums via sum_piFinAdd_factor
  rw [← sum_piFinAdd_factor
    (f := fun τ : Fin n₁ → Fin k => (∏ v : Fin n₁, w (τ v)) *
      ∏ e ∈ F₁.edgeFinset,
        c ((Fin.cons i τ : Fin (n₁ + 1) → Fin k) (Quot.out e).1)
          ((Fin.cons i τ : Fin (n₁ + 1) → Fin k) (Quot.out e).2))
    (g := fun τ : Fin n₂ → Fin k => (∏ v : Fin n₂, w (τ v)) *
      ∏ e ∈ F₂.edgeFinset,
        c ((Fin.cons i τ : Fin (n₂ + 1) → Fin k) (Quot.out e).1)
          ((Fin.cons i τ : Fin (n₂ + 1) → Fin k) (Quot.out e).2))]
  -- Now both sides sum over Fin (n₁ + n₂) → Fin k; show each summand matches
  congr 1; ext σ
  -- Decompose LHS weight product and edge product
  have h_wt : ∏ v : Fin (n₁ + n₂), w (σ v) =
      (∏ v : Fin n₁, w (σ (Fin.castAdd n₂ v))) *
      (∏ v : Fin n₂, w (σ (Fin.natAdd n₁ v))) :=
    Fin.prod_univ_add (fun v => w (σ v))
  have h_edges := rootGlue_prod_eq n₁ n₂ F₁ F₂ c hc (Fin.cons i σ)
  have h_f1 : (∏ e ∈ F₁.edgeFinset,
      c ((Fin.cons i σ : Fin (n₁ + n₂ + 1) → Fin k) (rootGlueEmb₁ n₁ n₂ (Quot.out e).1))
        ((Fin.cons i σ : Fin (n₁ + n₂ + 1) → Fin k) (rootGlueEmb₁ n₁ n₂ (Quot.out e).2))) =
    (∏ e ∈ F₁.edgeFinset,
      c ((Fin.cons i (fun j => σ (Fin.castAdd n₂ j)) : Fin (n₁ + 1) → Fin k) (Quot.out e).1)
        ((Fin.cons i (fun j => σ (Fin.castAdd n₂ j)) : Fin (n₁ + 1) → Fin k) (Quot.out e).2)) := by
    congr 1; ext e; rw [h_emb₁ σ (Quot.out e).1, h_emb₁ σ (Quot.out e).2]
  have h_f2 : (∏ e ∈ F₂.edgeFinset,
      c ((Fin.cons i σ : Fin (n₁ + n₂ + 1) → Fin k) (rootGlueEmb₂ n₁ n₂ (Quot.out e).1))
        ((Fin.cons i σ : Fin (n₁ + n₂ + 1) → Fin k) (rootGlueEmb₂ n₁ n₂ (Quot.out e).2))) =
    (∏ e ∈ F₂.edgeFinset,
      c ((Fin.cons i (fun j => σ (Fin.natAdd n₁ j)) : Fin (n₂ + 1) → Fin k) (Quot.out e).1)
        ((Fin.cons i (fun j => σ (Fin.natAdd n₁ j)) : Fin (n₂ + 1) → Fin k) (Quot.out e).2)) := by
    congr 1; ext e; rw [h_emb₂ σ (Quot.out e).1, h_emb₂ σ (Quot.out e).2]
  rw [h_wt, h_edges, h_f1, h_f2]; ring

/-! ### 2-Labeled evaluation -/

/-- 2-labeled evaluation: fix vertices 0 and 1 at colors `i` and `j` respectively,
sum over all colorings of the remaining `n` unlabeled vertices.
Labeled vertices carry no weight factor (consistent with rootedEval where the root
is unweighted). This is the "2-labeled quantum graph evaluation" needed for
orbit-breaking: unlike 1-labeled rootedEval, which is invariant under (B,W)-automorphisms,
2-labeled evaluation can probe individual entries B(i,j) via the edge graph. -/
noncomputable def labeledEval2 {k : ℕ} (n : ℕ) (F : SimpleGraph (Fin (n + 2)))
    [DecidableRel F.Adj] (c : Fin k → Fin k → ℝ) (w : Fin k → ℝ)
    (i j : Fin k) : ℝ :=
  ∑ σ : Fin n → Fin k,
    let τ : Fin (n + 2) → Fin k := Fin.cons i (Fin.cons j σ)
    (∏ v : Fin n, w (σ v)) *
    ∏ e ∈ F.edgeFinset, c (τ (Quot.out e).1) (τ (Quot.out e).2)

/-- 2-labeled evaluation is invariant under (c,w)-automorphisms applied to both labels
simultaneously. This is the easy direction of the orbit theorem (CT-1):
the column span of the 2-labeled connection matrix is contained in the space
of Aut(c,w)-invariant functions on (Fin k)². -/
private theorem labeledEval2_perm_eq {k : ℕ} (n : ℕ)
    (F : SimpleGraph (Fin (n + 2))) [DecidableRel F.Adj]
    (c : Fin k → Fin k → ℝ) (w : Fin k → ℝ)
    (π : Equiv.Perm (Fin k))
    (hc : ∀ i j, c (π i) (π j) = c i j) (hw : ∀ i, w (π i) = w i)
    (i j : Fin k) :
    labeledEval2 n F c w (π i) (π j) = labeledEval2 n F c w i j := by
  simp only [labeledEval2]
  -- Reindex: substitute σ = π ∘ σ' via Equiv.piCongrRight
  let e : (Fin n → Fin k) ≃ (Fin n → Fin k) :=
    Equiv.piCongrRight (fun _ => π)
  rw [(Equiv.sum_comp e _).symm]
  congr 1; ext σ'
  -- After reindex, LHS has σ = e σ' = (fun v => π (σ' v)). Simplify.
  have he : e σ' = fun v => π (σ' v) := by ext v; simp [e]
  -- Weight product: ∏ w(e σ' v) = ∏ w(π (σ' v)) = ∏ w(σ' v) by hw
  have hw_prod : ∏ v : Fin n, w (e σ' v) = ∏ v : Fin n, w (σ' v) := by
    congr 1; ext v; rw [he]; exact hw (σ' v)
  -- Edge product: Fin.cons(π i, Fin.cons(π j, e σ')) = π ∘ Fin.cons(i, Fin.cons(j, σ'))
  let τ' : Fin (n + 2) → Fin k := Fin.cons (π i) (Fin.cons (π j) (e σ'))
  let τ : Fin (n + 2) → Fin k := Fin.cons i (Fin.cons j σ')
  have hτ : ∀ v : Fin (n + 2), τ' v = π (τ v) := by
    intro v; simp only [τ', τ, he]
    rcases Fin.eq_zero_or_eq_succ v with rfl | ⟨w, rfl⟩
    · simp [Fin.cons_zero]
    · rcases Fin.eq_zero_or_eq_succ w with rfl | ⟨u, rfl⟩
      · simp [Fin.cons_succ, Fin.cons_zero]
      · simp [Fin.cons_succ]
  rw [hw_prod]; congr 1
  apply Finset.prod_congr rfl; intro x _
  show c (τ' (Quot.out x).1) (τ' (Quot.out x).2) =
       c (τ (Quot.out x).1) (τ (Quot.out x).2)
  rw [hτ, hτ, hc]

/-! ### 2-labeled left attachment -/

/-- Shift embedding for left attachment: maps Fin(n+2) → Fin(n+3) by
0 ↦ 2 (F's label 0 becomes unlabeled), 1 ↦ 1 (label 1 stays), v+2 ↦ v+3. -/
private def leftAttach2Shift (n : ℕ) : Fin (n + 2) ↪ Fin (n + 3) where
  toFun v :=
    if v.val = 0 then ⟨2, by omega⟩
    else if v.val = 1 then ⟨1, by omega⟩
    else ⟨v.val + 1, by omega⟩
  inj' a b h := by
    simp only at h
    by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0 <;>
      by_cases ha1 : a.val = 1 <;> by_cases hb1 : b.val = 1 <;>
      simp_all <;> exact Fin.ext (by omega)

private lemma leftAttach2Shift_zero (n : ℕ) :
    leftAttach2Shift n (0 : Fin (n + 2)) =
    Fin.succ (Fin.succ (0 : Fin (n + 1))) := by
  ext; simp [leftAttach2Shift, Nat.mod_eq_of_lt (show 2 < n + 3 by omega)]

private lemma leftAttach2Shift_succ_zero (n : ℕ) :
    leftAttach2Shift n (Fin.succ (0 : Fin (n + 1))) =
    (Fin.succ (0 : Fin (n + 2)) : Fin (n + 3)) := by
  ext; simp [leftAttach2Shift, Fin.val_succ]

private lemma leftAttach2Shift_succ_succ (n : ℕ) (u : Fin n) :
    leftAttach2Shift n (Fin.succ (Fin.succ u)) =
    Fin.succ (Fin.succ (Fin.succ u)) := by
  ext; simp [leftAttach2Shift, Fin.val_succ]

/-- Left attachment for 2-labeled graphs: add a new vertex 0 connected by an edge
to F's old label 0 (which becomes unlabeled vertex 2). Label 1 stays fixed.
The new graph is on Fin((n+1)+2) with n+1 unlabeled vertices. -/
private def leftAttach2 (n : ℕ) (F : SimpleGraph (Fin (n + 2))) :
    SimpleGraph (Fin ((n + 1) + 2)) where
  Adj u v :=
    -- Bridge edge: {0, 2}
    (u.val = 0 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 0) ∨
    -- Shifted F-edges
    (∃ a b : Fin (n + 2), F.Adj a b ∧
      leftAttach2Shift n a = u ∧ leftAttach2Shift n b = v)
  symm := by
    intro u v h
    rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨a, b, hadj, ha, hb⟩
    · right; left; exact ⟨hv, hu⟩
    · left; exact ⟨hv, hu⟩
    · right; right; exact ⟨b, a, F.symm hadj, hb, ha⟩
  loopless := by
    intro v h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨a, b, hadj, ha, hb⟩
    · omega
    · omega
    · have := (leftAttach2Shift n).injective (ha ▸ hb); exact F.loopless _ (this ▸ hadj)

private instance leftAttach2DecRel (n : ℕ) (F : SimpleGraph (Fin (n + 2)))
    [DecidableRel F.Adj] : DecidableRel (leftAttach2 n F).Adj :=
  fun u v => inferInstanceAs (Decidable
    ((u.val = 0 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 0) ∨
     (∃ a b : Fin (n + 2), F.Adj a b ∧
       leftAttach2Shift n a = u ∧ leftAttach2Shift n b = v)))

/-- The edge finset of `leftAttach2 n F` is the bridge edge `s(0, 2)` plus shifted `F`-edges. -/
private theorem leftAttach2_edgeFinset (n : ℕ) (F : SimpleGraph (Fin (n + 2)))
    [DecidableRel F.Adj] :
    (leftAttach2 n F).edgeFinset =
      insert s((0 : Fin ((n + 1) + 2)), ⟨2, by omega⟩)
        (F.edgeFinset.map (leftAttach2Shift n).sym2Map) := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, Finset.mem_insert, Finset.mem_map,
    Function.Embedding.sym2Map_apply]
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      change ((a.val = 0 ∧ b.val = 2) ∨ (a.val = 2 ∧ b.val = 0) ∨
        (∃ x y : Fin (n + 2), F.Adj x y ∧
          leftAttach2Shift n x = a ∧ leftAttach2Shift n y = b)) at he
      rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨x, y, hadj, hx, hy⟩
      · left; exact Sym2.eq_iff.mpr (Or.inl ⟨Fin.ext ha, Fin.ext hb⟩)
      · left; exact Sym2.eq_iff.mpr (Or.inr ⟨Fin.ext ha, Fin.ext hb⟩)
      · right
        exact ⟨s(x, y), hadj, by rw [Sym2.map_pair_eq]; exact Sym2.eq_iff.mpr (Or.inl ⟨hx, hy⟩)⟩
  · intro he
    rcases he with rfl | ⟨e', he', rfl⟩
    · -- Bridge edge
      rw [SimpleGraph.mem_edgeSet]
      exact Or.inl ⟨rfl, rfl⟩
    · -- Shifted F-edge
      induction e' using Sym2.ind with
      | _ a b =>
        rw [SimpleGraph.mem_edgeSet] at he'
        simp only [Sym2.map_pair_eq, SimpleGraph.mem_edgeSet]
        exact Or.inr (Or.inr ⟨a, b, he', rfl, rfl⟩)

/-- The bridge edge `s(0, 2)` is not a shifted `F`-edge (since 0 is not in the range of
`leftAttach2Shift`). -/
private theorem leftAttach2_bridge_not_mem_shifted (n : ℕ)
    (F : SimpleGraph (Fin (n + 2))) [DecidableRel F.Adj] :
    s((0 : Fin ((n + 1) + 2)), ⟨2, by omega⟩) ∉
      F.edgeFinset.map (leftAttach2Shift n).sym2Map := by
  intro hmem
  rw [Finset.mem_map] at hmem
  obtain ⟨e, _, he⟩ := hmem
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq] at he
    rw [Sym2.eq_iff] at he
    -- leftAttach2Shift never maps to 0, so no shifted edge contains vertex 0.
    -- But the bridge edge s(0, 2) has vertex 0. Contradiction.
    all_goals {
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      all_goals {
        have hva := congr_arg Fin.val h1
        have hvb := congr_arg Fin.val h2
        simp only [leftAttach2Shift, Function.Embedding.coeFn_mk] at hva hvb
        revert hva hvb
        by_cases ha0 : a.val = 0 <;> by_cases ha1 : a.val = 1 <;>
          by_cases hb0 : b.val = 0 <;> by_cases hb1 : b.val = 1 <;>
          simp_all <;> omega
      }
    }

/-- The edge product over `leftAttach2 n F` equals the bridge term times the shifted
`F`-edge product (requires symmetric matrix). -/
private theorem leftAttach2_prod_eq {k : ℕ} (n : ℕ) (F : SimpleGraph (Fin (n + 2)))
    [DecidableRel F.Adj] (c : Fin k → Fin k → ℝ) (hc : ∀ i j, c i j = c j i)
    (τ : Fin ((n + 1) + 2) → Fin k) :
    ∏ e ∈ (leftAttach2 n F).edgeFinset,
      c (τ (Quot.out e).1) (τ (Quot.out e).2) =
    c (τ 0) (τ ⟨2, by omega⟩) *
    ∏ e ∈ F.edgeFinset,
      c (τ (leftAttach2Shift n (Quot.out e).1)) (τ (leftAttach2Shift n (Quot.out e).2)) := by
  have h2eq : (⟨2, by omega⟩ : Fin ((n + 1) + 2)) = ⟨2, by omega⟩ := rfl
  rw [leftAttach2_edgeFinset,
    Finset.prod_insert (leftAttach2_bridge_not_mem_shifted n F),
    Finset.prod_map F.edgeFinset (leftAttach2Shift n).sym2Map]
  congr 1
  · -- Bridge edge: resolve Quot.out
    have hout := Quot.out_eq s((0 : Fin ((n + 1) + 2)), ⟨2, by omega⟩)
    rw [Sym2.mk_eq_mk_iff] at hout
    rcases hout with h | h
    · rw [congr_arg Prod.fst h, congr_arg Prod.snd h]
    · have h1 := congr_arg Prod.fst h; have h2 := congr_arg Prod.snd h
      simp only [Prod.swap] at h1 h2
      rw [h1, h2, hc]
  · congr 1; ext e
    -- Shifted edge: resolve Quot.out of mapped edge (use symmetry of c)
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq]
      have hout := Quot.out_eq s(leftAttach2Shift n a, leftAttach2Shift n b)
      rw [Sym2.mk_eq_mk_iff] at hout
      have hout' := Quot.out_eq s(a, b)
      rw [Sym2.mk_eq_mk_iff] at hout'
      rcases hout with h | h <;> rcases hout' with h' | h'
      · rw [congr_arg Prod.fst h, congr_arg Prod.snd h,
            congr_arg Prod.fst h', congr_arg Prod.snd h']
      · rw [congr_arg Prod.fst h, congr_arg Prod.snd h]
        simp only [Prod.swap] at h'
        rw [congr_arg Prod.fst h', congr_arg Prod.snd h', hc]
      · simp only [Prod.swap] at h
        rw [congr_arg Prod.fst h, congr_arg Prod.snd h,
            congr_arg Prod.fst h', congr_arg Prod.snd h', hc]
      · simp only [Prod.swap] at h h'
        rw [congr_arg Prod.fst h, congr_arg Prod.snd h,
            congr_arg Prod.fst h', congr_arg Prod.snd h']

/-- Left attachment realizes the left adjacency operator for 2-labeled evaluation:
`labeledEval2(leftAttach2 F)(i,j) = ∑ₐ wₐ c(i,a) labeledEval2(F)(a,j)`. -/
private theorem labeledEval2_leftAttach {k : ℕ} (n : ℕ)
    (F : SimpleGraph (Fin (n + 2))) [DecidableRel F.Adj]
    (c : Fin k → Fin k → ℝ) (hc : ∀ i j, c i j = c j i)
    (w : Fin k → ℝ) (i j : Fin k) :
    labeledEval2 (n + 1) (leftAttach2 n F) c w i j =
      ∑ a, w a * c i a * labeledEval2 n F c w a j := by
  simp only [labeledEval2]
  conv_lhs =>
    rw [(Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => Fin k)) _).symm]
  simp only [Fin.consEquiv_apply]
  rw [Fintype.sum_prod_type]
  congr 1; ext a; rw [Finset.mul_sum]; congr 1; ext σ'
  have hce : (Fin.consEquiv (fun _ : Fin (n + 1) => Fin k)) (a, σ') = Fin.cons a σ' := by
    ext v; simp [Fin.consEquiv_apply]
  simp only [hce, Prod.fst, Prod.snd]
  rw [leftAttach2_prod_eq n F c hc]
  -- Coloring correspondence: τ(shift(v)) = τ'(v)
  have hshift (v : Fin (n + 2)) :
      (Fin.cons i (Fin.cons j (Fin.cons a σ')) : Fin ((n + 1) + 2) → Fin k)
        (leftAttach2Shift n v) =
      (Fin.cons a (Fin.cons j σ') : Fin (n + 2) → Fin k) v := by
    rcases Fin.eq_zero_or_eq_succ v with rfl | ⟨w, rfl⟩
    · rw [leftAttach2Shift_zero]; rfl
    · rcases Fin.eq_zero_or_eq_succ w with rfl | ⟨u, rfl⟩
      · rw [leftAttach2Shift_succ_zero]; rfl
      · rw [leftAttach2Shift_succ_succ]; rfl
  simp_rw [hshift]
  have h0 : (Fin.cons i (Fin.cons j (Fin.cons a σ')) : Fin ((n + 1) + 2) → Fin k) 0 = i := rfl
  have h2 : (Fin.cons i (Fin.cons j (Fin.cons a σ')) : Fin ((n + 1) + 2) → Fin k)
      ⟨2, by omega⟩ = a := rfl
  conv_lhs => arg 2; arg 1; rw [h0, h2]
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

/-! ### 2-labeled right attachment -/

/-- Shift embedding for right attachment: maps Fin(n+2) → Fin(n+3) by
0 ↦ 0 (label 0 stays), 1 ↦ 2 (F's label 1 becomes unlabeled), v+2 ↦ v+3. -/
private def rightAttach2Shift (n : ℕ) : Fin (n + 2) ↪ Fin (n + 3) where
  toFun v :=
    if v.val = 0 then ⟨0, by omega⟩
    else if v.val = 1 then ⟨2, by omega⟩
    else ⟨v.val + 1, by omega⟩
  inj' a b h := by
    simp only at h
    by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0 <;>
      by_cases ha1 : a.val = 1 <;> by_cases hb1 : b.val = 1 <;>
      simp_all <;> exact Fin.ext (by omega)

private lemma rightAttach2Shift_zero (n : ℕ) :
    rightAttach2Shift n (0 : Fin (n + 2)) = (0 : Fin (n + 3)) := by
  ext; simp [rightAttach2Shift]

private lemma rightAttach2Shift_succ_zero (n : ℕ) :
    rightAttach2Shift n (Fin.succ (0 : Fin (n + 1))) =
    Fin.succ (Fin.succ (0 : Fin (n + 1))) := by
  ext; simp [rightAttach2Shift, Fin.val_succ, Nat.mod_eq_of_lt (show 2 < n + 3 by omega)]

private lemma rightAttach2Shift_succ_succ (n : ℕ) (u : Fin n) :
    rightAttach2Shift n (Fin.succ (Fin.succ u)) =
    Fin.succ (Fin.succ (Fin.succ u)) := by
  ext; simp [rightAttach2Shift, Fin.val_succ]

/-- Right attachment for 2-labeled graphs: add a new vertex 1 connected by an edge
to F's old label 1 (which becomes unlabeled vertex 2). Label 0 stays fixed.
The new graph is on Fin((n+1)+2) with n+1 unlabeled vertices. -/
private def rightAttach2 (n : ℕ) (F : SimpleGraph (Fin (n + 2))) :
    SimpleGraph (Fin ((n + 1) + 2)) where
  Adj u v :=
    -- Bridge edge: {1, 2}
    (u.val = 1 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 1) ∨
    -- Shifted F-edges
    (∃ a b : Fin (n + 2), F.Adj a b ∧
      rightAttach2Shift n a = u ∧ rightAttach2Shift n b = v)
  symm := by
    intro u v h
    rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨a, b, hadj, ha, hb⟩
    · right; left; exact ⟨hv, hu⟩
    · left; exact ⟨hv, hu⟩
    · right; right; exact ⟨b, a, F.symm hadj, hb, ha⟩
  loopless := by
    intro v h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨a, b, hadj, ha, hb⟩
    · omega
    · omega
    · have := (rightAttach2Shift n).injective (ha ▸ hb); exact F.loopless _ (this ▸ hadj)

private instance rightAttach2DecRel (n : ℕ) (F : SimpleGraph (Fin (n + 2)))
    [DecidableRel F.Adj] : DecidableRel (rightAttach2 n F).Adj :=
  fun u v => inferInstanceAs (Decidable
    ((u.val = 1 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 1) ∨
     (∃ a b : Fin (n + 2), F.Adj a b ∧
       rightAttach2Shift n a = u ∧ rightAttach2Shift n b = v)))

private theorem rightAttach2_edgeFinset (n : ℕ) (F : SimpleGraph (Fin (n + 2)))
    [DecidableRel F.Adj] :
    (rightAttach2 n F).edgeFinset =
      insert s((⟨1, by omega⟩ : Fin ((n + 1) + 2)), ⟨2, by omega⟩)
        (F.edgeFinset.map (rightAttach2Shift n).sym2Map) := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, Finset.mem_insert, Finset.mem_map,
    Function.Embedding.sym2Map_apply]
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      change ((a.val = 1 ∧ b.val = 2) ∨ (a.val = 2 ∧ b.val = 1) ∨
        (∃ x y : Fin (n + 2), F.Adj x y ∧
          rightAttach2Shift n x = a ∧ rightAttach2Shift n y = b)) at he
      rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨x, y, hadj, hx, hy⟩
      · left; exact Sym2.eq_iff.mpr (Or.inl ⟨Fin.ext ha, Fin.ext hb⟩)
      · left; exact Sym2.eq_iff.mpr (Or.inr ⟨Fin.ext ha, Fin.ext hb⟩)
      · right
        exact ⟨s(x, y), hadj, by rw [Sym2.map_pair_eq]; exact Sym2.eq_iff.mpr (Or.inl ⟨hx, hy⟩)⟩
  · intro he
    rcases he with rfl | ⟨e', he', rfl⟩
    · rw [SimpleGraph.mem_edgeSet]
      exact Or.inl ⟨rfl, rfl⟩
    · induction e' using Sym2.ind with
      | _ a b =>
        rw [SimpleGraph.mem_edgeSet] at he'
        simp only [Sym2.map_pair_eq, SimpleGraph.mem_edgeSet]
        exact Or.inr (Or.inr ⟨a, b, he', rfl, rfl⟩)

private theorem rightAttach2_bridge_not_mem_shifted (n : ℕ)
    (F : SimpleGraph (Fin (n + 2))) [DecidableRel F.Adj] :
    s((⟨1, by omega⟩ : Fin ((n + 1) + 2)), ⟨2, by omega⟩) ∉
      F.edgeFinset.map (rightAttach2Shift n).sym2Map := by
  intro hmem
  rw [Finset.mem_map] at hmem
  obtain ⟨e, _, he⟩ := hmem
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq] at he
    rw [Sym2.eq_iff] at he
    all_goals {
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      all_goals {
        have hva := congr_arg Fin.val h1
        have hvb := congr_arg Fin.val h2
        simp only [rightAttach2Shift, Function.Embedding.coeFn_mk] at hva hvb
        revert hva hvb
        by_cases ha0 : a.val = 0 <;> by_cases ha1 : a.val = 1 <;>
          by_cases hb0 : b.val = 0 <;> by_cases hb1 : b.val = 1 <;>
          simp_all <;> omega
      }
    }

private theorem rightAttach2_prod_eq {k : ℕ} (n : ℕ) (F : SimpleGraph (Fin (n + 2)))
    [DecidableRel F.Adj] (c : Fin k → Fin k → ℝ) (hc : ∀ i j, c i j = c j i)
    (τ : Fin ((n + 1) + 2) → Fin k) :
    ∏ e ∈ (rightAttach2 n F).edgeFinset,
      c (τ (Quot.out e).1) (τ (Quot.out e).2) =
    c (τ ⟨1, by omega⟩) (τ ⟨2, by omega⟩) *
    ∏ e ∈ F.edgeFinset,
      c (τ (rightAttach2Shift n (Quot.out e).1)) (τ (rightAttach2Shift n (Quot.out e).2)) := by
  rw [rightAttach2_edgeFinset,
    Finset.prod_insert (rightAttach2_bridge_not_mem_shifted n F),
    Finset.prod_map F.edgeFinset (rightAttach2Shift n).sym2Map]
  congr 1
  · have hout := Quot.out_eq s((⟨1, by omega⟩ : Fin ((n + 1) + 2)), ⟨2, by omega⟩)
    rw [Sym2.mk_eq_mk_iff] at hout
    rcases hout with h | h
    · rw [congr_arg Prod.fst h, congr_arg Prod.snd h]
    · have h1 := congr_arg Prod.fst h; have h2 := congr_arg Prod.snd h
      simp only [Prod.swap] at h1 h2
      rw [h1, h2, hc]
  · congr 1; ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq]
      have hout := Quot.out_eq s(rightAttach2Shift n a, rightAttach2Shift n b)
      rw [Sym2.mk_eq_mk_iff] at hout
      have hout' := Quot.out_eq s(a, b)
      rw [Sym2.mk_eq_mk_iff] at hout'
      rcases hout with h | h <;> rcases hout' with h' | h'
      · rw [congr_arg Prod.fst h, congr_arg Prod.snd h,
            congr_arg Prod.fst h', congr_arg Prod.snd h']
      · rw [congr_arg Prod.fst h, congr_arg Prod.snd h]
        simp only [Prod.swap] at h'
        rw [congr_arg Prod.fst h', congr_arg Prod.snd h', hc]
      · simp only [Prod.swap] at h
        rw [congr_arg Prod.fst h, congr_arg Prod.snd h,
            congr_arg Prod.fst h', congr_arg Prod.snd h', hc]
      · simp only [Prod.swap] at h h'
        rw [congr_arg Prod.fst h, congr_arg Prod.snd h,
            congr_arg Prod.fst h', congr_arg Prod.snd h']

/-- Right attachment realizes the right adjacency operator for 2-labeled evaluation:
`labeledEval2(rightAttach2 F)(i,j) = ∑ₐ wₐ c(a,j) labeledEval2(F)(i,a)`. -/
private theorem labeledEval2_rightAttach {k : ℕ} (n : ℕ)
    (F : SimpleGraph (Fin (n + 2))) [DecidableRel F.Adj]
    (c : Fin k → Fin k → ℝ) (hc : ∀ i j, c i j = c j i)
    (w : Fin k → ℝ) (i j : Fin k) :
    labeledEval2 (n + 1) (rightAttach2 n F) c w i j =
      ∑ a, w a * c a j * labeledEval2 n F c w i a := by
  simp only [labeledEval2]
  conv_lhs =>
    rw [(Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => Fin k)) _).symm]
  simp only [Fin.consEquiv_apply]
  rw [Fintype.sum_prod_type]
  congr 1; ext a; rw [Finset.mul_sum]; congr 1; ext σ'
  have hce : (Fin.consEquiv (fun _ : Fin (n + 1) => Fin k)) (a, σ') = Fin.cons a σ' := by
    ext v; simp [Fin.consEquiv_apply]
  simp only [hce, Prod.fst, Prod.snd]
  rw [rightAttach2_prod_eq n F c hc]
  -- Coloring correspondence: τ(shift(v)) = τ'(v)
  have hshift (v : Fin (n + 2)) :
      (Fin.cons i (Fin.cons j (Fin.cons a σ')) : Fin ((n + 1) + 2) → Fin k)
        (rightAttach2Shift n v) =
      (Fin.cons i (Fin.cons a σ') : Fin (n + 2) → Fin k) v := by
    rcases Fin.eq_zero_or_eq_succ v with rfl | ⟨w, rfl⟩
    · rw [rightAttach2Shift_zero]; rfl
    · rcases Fin.eq_zero_or_eq_succ w with rfl | ⟨u, rfl⟩
      · rw [rightAttach2Shift_succ_zero]; rfl
      · rw [rightAttach2Shift_succ_succ]; rfl
  simp_rw [hshift]
  have h1 : (Fin.cons i (Fin.cons j (Fin.cons a σ')) : Fin ((n + 1) + 2) → Fin k)
      ⟨1, by omega⟩ = j := rfl
  have h2 : (Fin.cons i (Fin.cons j (Fin.cons a σ')) : Fin ((n + 1) + 2) → Fin k)
      ⟨2, by omega⟩ = a := rfl
  conv_lhs => arg 2; arg 1; rw [h1, h2, hc]
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

/-- Summing `labeledEval2` over the second label with weight recovers `rootedEval`.
This is the bridge from 2-labeled to 1-labeled, and the key sanity check that
the weighted/unweighted convention is coherent. -/
private theorem labeledEval2_weighted_sum_snd {k : ℕ} (n : ℕ)
    (F : SimpleGraph (Fin (n + 2))) [DecidableRel F.Adj]
    (c : Fin k → Fin k → ℝ) (w : Fin k → ℝ) (i : Fin k) :
    ∑ j, w j * labeledEval2 n F c w i j = rootedEval (n + 1) F c w i := by
  simp only [labeledEval2, rootedEval, Finset.mul_sum]
  -- LHS: ∑ j, ∑ σ : Fin n → Fin k, w j * (∏ w(σ v)) * ∏ c(...)
  -- RHS: ∑ τ : Fin (n+1) → Fin k, (∏ v : Fin (n+1), w(τ v)) * ∏ c(Fin.cons i τ ...)
  -- Bridge: τ = Fin.cons j σ via Fin.consEquiv
  conv_rhs =>
    rw [(Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => Fin k)) _).symm]
  simp only [Fin.consEquiv_apply]
  rw [Fintype.sum_prod_type]
  congr 1; ext j
  -- LHS: ∑ σ, w j * ((∏ w(σ v)) * ∏ c(...Fin.cons i (Fin.cons j σ)...))
  -- RHS: ∑ σ, (∏ v, w(Fin.cons j σ v)) * ∏ c(...Fin.cons i (consEquiv (j,σ))...)
  -- Key insight: Fin.consEquiv (j,σ) = Fin.cons j σ, but Lean needs help seeing this.
  congr 1; ext σ
  -- Normalize both sides: unfold consEquiv, simplify Fin.cons, use ring
  have hce : (Fin.consEquiv (fun _ : Fin (n + 1) => Fin k)) (j, σ) = Fin.cons j σ := by
    ext v; simp [Fin.consEquiv_apply]
  rw [hce, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Prod.fst, Prod.snd]
  ring

/-- Double bridge: summing `labeledEval2` over both labels with weights recovers
`weightedHomSum`. -/
private theorem labeledEval2_weighted_sum {k : ℕ} (n : ℕ)
    (F : SimpleGraph (Fin (n + 2))) [DecidableRel F.Adj]
    (c : Fin k → Fin k → ℝ) (w : Fin k → ℝ) :
    ∑ i, ∑ j, w i * w j * labeledEval2 n F c w i j =
      weightedHomSum (n + 2) F c w := by
  have : ∑ i, ∑ j, w i * w j * labeledEval2 n F c w i j =
      ∑ i, w i * (∑ j, w j * labeledEval2 n F c w i j) := by
    congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j; ring
  rw [this]
  simp_rw [labeledEval2_weighted_sum_snd]
  exact rootedEval_weighted_sum (n + 1) F c w

/-- The 2-labeled evaluation of the edge graph (single edge between vertices 0 and 1,
no unlabeled vertices) directly reads the matrix entry c(i,j). This is the key
orbit-breaking property: 1-labeled rootedEval cannot probe individual entries. -/
private theorem labeledEval2_edge {k : ℕ}
    (c : Fin k → Fin k → ℝ) (hc : ∀ i j, c i j = c j i)
    (w : Fin k → ℝ) (i j : Fin k) :
    labeledEval2 0 (⊤ : SimpleGraph (Fin 2)) c w i j = c i j := by
  simp only [labeledEval2]
  rw [Fintype.sum_unique]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
  -- Edge product: single edge {0,1} in the complete graph on Fin 2
  -- Use the same edgeFinset characterization as starGraph/K₂ proofs in the file
  -- The complete graph on Fin 2 has exactly one edge: {0, 1}
  -- We need to evaluate the edge product at that single edge.
  -- Evaluate on the single edge of the complete graph on Fin 2.
  -- Use the same K₂ edge finset pattern as weightedHomSum_edge (L2059).
  have hedge : (⊤ : SimpleGraph (Fin 2)).edgeFinset = {s(0, 1)} := by
    rw [Finset.eq_singleton_iff_unique_mem]; constructor
    · simp [SimpleGraph.mem_edgeFinset, SimpleGraph.top_adj]
    · intro e he
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      exact Sym2.ind (fun a b h => by fin_cases a <;> fin_cases b <;> simp_all) e he
  rw [hedge, Finset.prod_singleton]
  -- Evaluate Fin.cons i (Fin.cons j _) at the Quot.out of s(0,1)
  -- The Quot.out gives some pair (a,b) with s(a,b) = s(0,1). So {a,b} = {0,1}.
  -- In either orientation, Fin.cons i (Fin.cons j _) maps 0→i and 1→j, giving c(i,j).
  -- We use the same Quot.out resolution as starGraph_prod_eq / rootAttach_prod_eq.
  convert rfl using 1
  set p := Quot.out s((0 : Fin 2), (1 : Fin 2))
  -- We need: c(τ(p.1), τ(p.2)) = c(i,j) where τ = Fin.cons i (Fin.cons j default)
  -- The map τ satisfies τ 0 = i and τ 1 = j.
  let τ : Fin 2 → Fin k := Fin.cons i (Fin.cons j (default : Fin 0 → Fin k))
  have h0 : τ 0 = i := by simp [τ, Fin.cons_zero]
  have h1 : τ 1 = j := by simp [τ, Fin.cons_succ, Fin.cons_zero]
  -- Quot.out s(0,1) is some (a,b) with s(a,b) = s(0,1), so (a,b) = (0,1) or (1,0).
  have hout := Quot.out_eq s((0 : Fin 2), (1 : Fin 2))
  have key : (p.1 = 0 ∧ p.2 = 1) ∨ (p.1 = 1 ∧ p.2 = 0) := by
    have := Sym2.eq_iff.mp hout
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [left; right] <;> exact ⟨h1, h2⟩
  rcases key with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simp [ha, hb]
  · simp [ha, hb, hc]

-- NOTE: Naive 2-labeled gluing (labeledEval2_glue_exists) is FALSE for SimpleGraph.
-- Counterexample: F₁ = F₂ = K₂ (edge {0,1}). Product = c(i,j)², but no simple
-- graph produces c(i,j)² because the label edge can only appear once.
-- The 1-labeled rootedEval_glue_exists works because with 1 shared vertex,
-- edge overlap would require a self-loop (forbidden). With 2 shared vertices,
-- the label edge {0,1} can appear in both factors but not twice in a simple graph.

/-- Equal weighted hom sums transfer to 2-labeled evaluation sums. -/
private theorem labeledEval2_eq_of_weightedHomSum_eq {T T' : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (B' : Fin T' → Fin T' → ℝ) (W' : Fin T' → ℝ)
    (h_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      weightedHomSum n F B W = weightedHomSum n F B' W')
    (n : ℕ) (F : SimpleGraph (Fin (n + 2))) [DecidableRel F.Adj] :
    ∑ i, ∑ j, W i * W j * labeledEval2 n F B W i j =
    ∑ i, ∑ j, W' i * W' j * labeledEval2 n F B' W' i j := by
  rw [labeledEval2_weighted_sum, h_eq, ← labeledEval2_weighted_sum]

/-! ### Automorphism invariance layer -/

/-- A permutation π is a weighted automorphism of (B, W) if it preserves both the weight
vector and the matrix entries. -/
private def IsWeightedAutomorphism {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (π : Equiv.Perm (Fin T)) : Prop :=
  (∀ i, W (π i) = W i) ∧ (∀ i j, B (π i) (π j) = B i j)

/-- The subspace of pair functions invariant under all (B,W)-automorphisms. -/
private def pairInvariantSubspace {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    Submodule ℝ (Fin T → Fin T → ℝ) where
  carrier := {f | ∀ (π : Equiv.Perm (Fin T)),
    IsWeightedAutomorphism B W π → ∀ i j, f (π i) (π j) = f i j}
  zero_mem' := fun _ _ _ _ => rfl
  add_mem' := fun {f g} hf hg π haut i j => by
    simp only [Pi.add_apply]; rw [hf π haut i j, hg π haut i j]
  smul_mem' := fun r f hf π haut i j => by
    simp only [Pi.smul_apply, smul_eq_mul]; rw [hf π haut i j]

/-- The set of all 2-labeled evaluation functions. -/
private def eval2Set {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    Set (Fin T → Fin T → ℝ) :=
  {f | ∃ (n : ℕ) (F : SimpleGraph (Fin (n + 2))) (_ : DecidableRel F.Adj),
    f = fun i j => @labeledEval2 T n F ‹_› B W i j}

/-- The linear span of all 2-labeled evaluation functions. -/
private noncomputable def eval2Span {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    Submodule ℝ (Fin T → Fin T → ℝ) :=
  Submodule.span ℝ (eval2Set B W)

/-- Every 2-labeled evaluation function is pair-invariant (easy direction of CT-1). -/
private theorem labeledEval2_isPairInvariant {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (n : ℕ) (F : SimpleGraph (Fin (n + 2))) [DecidableRel F.Adj] :
    (fun i j => labeledEval2 n F B W i j) ∈ pairInvariantSubspace B W := by
  intro π ⟨hw, hc⟩ i j
  exact labeledEval2_perm_eq n F B W π hc hw i j

/-- The evaluation span is contained in the pair-invariant subspace (easy inclusion of CT-1). -/
private theorem eval2Span_le_pairInvariantSubspace {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    eval2Span B W ≤ pairInvariantSubspace B W := by
  apply Submodule.span_le.mpr
  intro f ⟨n, F, inst, hf⟩
  rw [hf]
  exact @labeledEval2_isPairInvariant T B W n F inst

/-! ### Pair-orbit decomposition -/

/-- Two pairs are in the same orbit under Aut(B,W) if some automorphism sends one to the other. -/
private def pairOrbitRel {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (p q : Fin T × Fin T) : Prop :=
  ∃ π : Equiv.Perm (Fin T), IsWeightedAutomorphism B W π ∧ π p.1 = q.1 ∧ π p.2 = q.2

private theorem pairOrbitRel_refl {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (p : Fin T × Fin T) : pairOrbitRel B W p p :=
  ⟨1, ⟨fun _ => by simp, fun _ _ => by simp⟩, by simp, by simp⟩

private theorem pairOrbitRel_symm {T : ℕ} {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    {p q : Fin T × Fin T} (h : pairOrbitRel B W p q) : pairOrbitRel B W q p := by
  obtain ⟨π, ⟨hw, hc⟩, h1, h2⟩ := h
  refine ⟨π⁻¹, ⟨fun i => ?_, fun i j => ?_⟩, ?_, ?_⟩
  · rw [← hw (π⁻¹ i), Equiv.Perm.apply_inv_self]
  · rw [← hc (π⁻¹ i) (π⁻¹ j)]; simp
  · rw [← h1, Equiv.Perm.inv_apply_self]
  · rw [← h2, Equiv.Perm.inv_apply_self]

private theorem pairOrbitRel_trans {T : ℕ} {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    {p q r : Fin T × Fin T}
    (h1 : pairOrbitRel B W p q) (h2 : pairOrbitRel B W q r) : pairOrbitRel B W p r := by
  obtain ⟨π₁, ⟨hw₁, hc₁⟩, ha₁, hb₁⟩ := h1
  obtain ⟨π₂, ⟨hw₂, hc₂⟩, ha₂, hb₂⟩ := h2
  exact ⟨π₁.trans π₂,
    ⟨fun i => by simp only [Equiv.trans_apply]; rw [hw₂, hw₁],
     fun i j => by simp only [Equiv.trans_apply]; rw [hc₂, hc₁]⟩,
    by simp only [Equiv.trans_apply]; rw [ha₁, ha₂],
    by simp only [Equiv.trans_apply]; rw [hb₁, hb₂]⟩

private def pairOrbitSetoid {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    Setoid (Fin T × Fin T) where
  r := pairOrbitRel B W
  iseqv := ⟨pairOrbitRel_refl B W, fun h => pairOrbitRel_symm h, fun h1 h2 =>
    pairOrbitRel_trans h1 h2⟩

/-- Invariant functions are constant on orbits. -/
private theorem invariant_constant_on_orbits {T : ℕ} {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    {f : Fin T → Fin T → ℝ} (hf : f ∈ pairInvariantSubspace B W)
    {p q : Fin T × Fin T} (h : pairOrbitRel B W p q) : f p.1 p.2 = f q.1 q.2 := by
  obtain ⟨π, haut, h1, h2⟩ := h
  rw [← h1, ← h2]
  exact (hf π haut p.1 p.2).symm

open Classical in
/-- The orbit indicator: 1 on the orbit of p, 0 elsewhere. -/
private noncomputable def pairOrbitIndicator {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (o : Quotient (pairOrbitSetoid B W)) : Fin T → Fin T → ℝ :=
  fun i j => if Quotient.mk (pairOrbitSetoid B W) (i, j) = o then 1 else 0

/-- Orbit indicators are pair-invariant. -/
private theorem pairOrbitIndicator_invariant {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (o : Quotient (pairOrbitSetoid B W)) :
    pairOrbitIndicator B W o ∈ pairInvariantSubspace B W := by
  intro π haut i j
  simp only [pairOrbitIndicator]
  rw [@Quotient.sound _ (pairOrbitSetoid B W) (i, j) (π i, π j) ⟨π, haut, rfl, rfl⟩]

/-- The set of all orbit indicator functions. -/
private def orbitIndicatorSet {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    Set (Fin T → Fin T → ℝ) :=
  Set.range (pairOrbitIndicator B W)

open Classical in
/-- Every invariant function is a linear combination of orbit indicators.
This is the key decomposition: f = ∑_O f(rep_O) · 1_O. -/
private theorem mem_pairInvariantSubspace_of_orbitIndicator_span {T : ℕ}
    {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    {f : Fin T → Fin T → ℝ} (hf : f ∈ pairInvariantSubspace B W) :
    f ∈ Submodule.span ℝ (orbitIndicatorSet B W) := by
  -- f = ∑_o f(rep_o) • orbitIndicator o
  rw [show f = ∑ o : Quotient (pairOrbitSetoid B W),
      (f (Quotient.out o).1 (Quotient.out o).2) • pairOrbitIndicator B W o from ?_]
  · exact Submodule.sum_mem _ fun o _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨o, rfl⟩)
  · ext i j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pairOrbitIndicator]
    rw [Finset.sum_eq_single (Quotient.mk (pairOrbitSetoid B W) (i, j))]
    · simp only [ite_true, eq_self_iff_true, mul_one]
      exact (invariant_constant_on_orbits hf
        (@Quotient.exact _ (pairOrbitSetoid B W) _ _ (Quotient.out_eq ⟦(i, j)⟧))).symm
    · intro b _ hne; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- The pair-invariant subspace equals the span of orbit indicators. -/
private theorem pairInvariantSubspace_eq_span_orbitIndicators {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    pairInvariantSubspace B W = Submodule.span ℝ (orbitIndicatorSet B W) := by
  apply le_antisymm
  · intro f hf; exact mem_pairInvariantSubspace_of_orbitIndicator_span hf
  · apply Submodule.span_le.mpr
    intro f hf
    obtain ⟨o, rfl⟩ := hf
    exact pairOrbitIndicator_invariant B W o

/-- To prove pairInvariantSubspace ≤ eval2Span, it suffices to show every orbit indicator
is in eval2Span. -/
private theorem pairInvariantSubspace_le_of_orbitIndicators {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (h : ∀ o : Quotient (pairOrbitSetoid B W),
      pairOrbitIndicator B W o ∈ eval2Span B W) :
    pairInvariantSubspace B W ≤ eval2Span B W := by
  rw [pairInvariantSubspace_eq_span_orbitIndicators]
  apply Submodule.span_le.mpr
  intro f hf
  obtain ⟨o, rfl⟩ := hf
  exact h o

/-! ### Label-edge factorization -/

/-- Remove the label edge {0, 1} from a 2-labeled graph. -/
private def eraseLabelEdge {n : ℕ} (F : SimpleGraph (Fin (n + 2))) :
    SimpleGraph (Fin (n + 2)) where
  Adj u v := F.Adj u v ∧ s(u, v) ≠ s((0 : Fin (n + 2)), 1)
  symm u v h := ⟨F.symm h.1, by rw [Sym2.eq_swap]; exact h.2⟩
  loopless v h := F.loopless v h.1

private instance eraseLabelEdgeDecRel {n : ℕ} (F : SimpleGraph (Fin (n + 2)))
    [DecidableRel F.Adj] : DecidableRel (eraseLabelEdge F).Adj :=
  fun u v => inferInstanceAs (Decidable (F.Adj u v ∧ s(u, v) ≠ s((0 : Fin (n + 2)), 1)))

/-- The erased graph has no label edge. -/
private theorem eraseLabelEdge_not_adj_01 {n : ℕ} (F : SimpleGraph (Fin (n + 2))) :
    ¬(eraseLabelEdge F).Adj 0 1 := fun h => h.2 rfl

/-- If F has no label edge, erasing is the identity. -/
private theorem eraseLabelEdge_of_not_adj {n : ℕ} {F : SimpleGraph (Fin (n + 2))}
    (h : ¬F.Adj 0 1) : eraseLabelEdge F = F := by
  ext u v; constructor
  · exact fun ⟨hadj, _⟩ => hadj
  · intro hadj; refine ⟨hadj, ?_⟩
    intro heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd hadj h
    · exact absurd (F.symm hadj) h

/-- The edge finset of `eraseLabelEdge F` is `F.edgeFinset.erase s(0, 1)`. -/
private theorem eraseLabelEdge_edgeFinset {n : ℕ} (F : SimpleGraph (Fin (n + 2)))
    [DecidableRel F.Adj] :
    (eraseLabelEdge F).edgeFinset = F.edgeFinset.erase s((0 : Fin (n + 2)), 1) := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, Finset.mem_erase, ne_eq]
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he ⊢
      exact ⟨he.2, he.1⟩
  · intro ⟨hne, he⟩
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he ⊢
      exact ⟨he, hne⟩

/-- Factorization: every 2-labeled evaluation factors as the label-edge indicator times the
evaluation of the erased graph. If F has the label edge, the indicator is `c i j`;
if not, the indicator is 1 (and the erased graph equals F). -/
private theorem labeledEval2_eraseLabelEdge {k : ℕ} (n : ℕ)
    (F : SimpleGraph (Fin (n + 2))) [DecidableRel F.Adj]
    (c : Fin k → Fin k → ℝ) (hc : ∀ i j, c i j = c j i)
    (w : Fin k → ℝ) (i j : Fin k)
    (hF : F.Adj 0 1) :
    labeledEval2 n F c w i j = c i j * labeledEval2 n (eraseLabelEdge F) c w i j := by
  simp only [labeledEval2]
  rw [Finset.mul_sum]; congr 1; ext σ
  -- Factor the edge product: split off the label edge s(0, 1)
  have hmem : s((0 : Fin (n + 2)), 1) ∈ F.edgeFinset :=
    SimpleGraph.mem_edgeFinset.mpr hF
  rw [← Finset.mul_prod_erase F.edgeFinset _ hmem, ← eraseLabelEdge_edgeFinset]
  -- The label edge contributes c(τ 0, τ 1) = c(i, j)
  have hlabel : c ((Fin.cons i (Fin.cons j σ) : Fin (n + 2) → Fin k)
        (Quot.out s((0 : Fin (n + 2)), 1)).1)
      ((Fin.cons i (Fin.cons j σ) : Fin (n + 2) → Fin k)
        (Quot.out s((0 : Fin (n + 2)), 1)).2) = c i j := by
    have hout := Quot.out_eq s((0 : Fin (n + 2)), (1 : Fin (n + 2)))
    rw [Sym2.mk_eq_mk_iff] at hout
    rcases hout with h | h
    · rw [congr_arg Prod.fst h, congr_arg Prod.snd h]; rfl
    · simp only [Prod.swap] at h
      rw [congr_arg Prod.fst h, congr_arg Prod.snd h]; exact hc j i
  rw [hlabel]; ring

/-! ### Edge-free gluing -/

/-- Shift embedding for gluing: maps F₁'s vertices into the glued graph.
Identity on all vertices (F₁'s labels 0,1 stay at 0,1; unlabeled v+2 stays at v+2). -/
private def glueShift1 (n₁ n₂ : ℕ) : Fin (n₁ + 2) ↪ Fin (n₁ + n₂ + 2) where
  toFun v := ⟨v.val, by omega⟩
  inj' a b h := Fin.ext (by simpa using h)

/-- Shift embedding for gluing: maps F₂'s vertices into the glued graph.
Labels 0,1 stay fixed; unlabeled v+2 maps to v+n₁+2. -/
private def glueShift2 (n₁ n₂ : ℕ) : Fin (n₂ + 2) ↪ Fin (n₁ + n₂ + 2) where
  toFun v :=
    if v.val = 0 then ⟨0, by omega⟩
    else if v.val = 1 then ⟨1, by omega⟩
    else ⟨v.val + n₁, by omega⟩
  inj' a b h := by
    have ha := a.isLt; have hb := b.isLt
    have hv := congrArg Fin.val h
    dsimp only [Function.Embedding.coeFn_mk] at hv
    simp only [apply_ite Fin.val, Fin.val_mk] at hv
    split_ifs at hv <;> exact Fin.ext (by omega)

/-- Glue two edge-free 2-labeled graphs at their shared labels 0 and 1.
The result has n₁+n₂ unlabeled vertices. F₁'s unlabeled vertices occupy
positions 2,...,n₁+1 and F₂'s occupy positions n₁+2,...,n₁+n₂+1. -/
private def edgeFreeGlue2 (n₁ n₂ : ℕ)
    (F₁ : SimpleGraph (Fin (n₁ + 2))) (F₂ : SimpleGraph (Fin (n₂ + 2))) :
    SimpleGraph (Fin (n₁ + n₂ + 2)) where
  Adj u v :=
    (∃ a b : Fin (n₁ + 2), F₁.Adj a b ∧
      glueShift1 n₁ n₂ a = u ∧ glueShift1 n₁ n₂ b = v) ∨
    (∃ a b : Fin (n₂ + 2), F₂.Adj a b ∧
      glueShift2 n₁ n₂ a = u ∧ glueShift2 n₁ n₂ b = v)
  symm := by
    intro u v h
    rcases h with ⟨a, b, hadj, ha, hb⟩ | ⟨a, b, hadj, ha, hb⟩
    · left; exact ⟨b, a, F₁.symm hadj, hb, ha⟩
    · right; exact ⟨b, a, F₂.symm hadj, hb, ha⟩
  loopless := by
    intro v h
    rcases h with ⟨a, b, hadj, ha, hb⟩ | ⟨a, b, hadj, ha, hb⟩
    · have := (glueShift1 n₁ n₂).injective (ha ▸ hb)
      exact F₁.loopless _ (this ▸ hadj)
    · have := (glueShift2 n₁ n₂).injective (ha ▸ hb)
      exact F₂.loopless _ (this ▸ hadj)

private instance edgeFreeGlue2DecRel (n₁ n₂ : ℕ) (F₁ : SimpleGraph (Fin (n₁ + 2)))
    (F₂ : SimpleGraph (Fin (n₂ + 2))) [DecidableRel F₁.Adj] [DecidableRel F₂.Adj] :
    DecidableRel (edgeFreeGlue2 n₁ n₂ F₁ F₂).Adj :=
  fun u v => inferInstanceAs (Decidable
    ((∃ a b : Fin (n₁ + 2), F₁.Adj a b ∧
        glueShift1 n₁ n₂ a = u ∧ glueShift1 n₁ n₂ b = v) ∨
     (∃ a b : Fin (n₂ + 2), F₂.Adj a b ∧
        glueShift2 n₁ n₂ a = u ∧ glueShift2 n₁ n₂ b = v)))

/-- If both inputs are edge-free, the glued graph is also edge-free. -/
private theorem edgeFreeGlue2_no_label_edge (n₁ n₂ : ℕ)
    (F₁ : SimpleGraph (Fin (n₁ + 2))) (F₂ : SimpleGraph (Fin (n₂ + 2)))
    (h₁ : ¬F₁.Adj 0 1) (h₂ : ¬F₂.Adj 0 1) :
    ¬(edgeFreeGlue2 n₁ n₂ F₁ F₂).Adj 0 1 := by
  intro h
  rcases h with ⟨a, b, hadj, ha, hb⟩ | ⟨a, b, hadj, ha, hb⟩
  · -- From F₁: glueShift1 a = 0 and glueShift1 b = 1
    have hav : a.val = 0 := by
      have := congrArg Fin.val ha; simp only [glueShift1, Fin.val_mk] at this; simpa
    have hbv : b.val = 1 := by
      have := congrArg Fin.val hb; simp only [glueShift1, Fin.val_mk] at this; simpa
    rw [show a = (0 : Fin (n₁ + 2)) from Fin.ext hav,
        show b = (1 : Fin (n₁ + 2)) from Fin.ext (by simpa)] at hadj
    exact h₁ hadj
  · -- From F₂: glueShift2 a = 0 and glueShift2 b = 1
    have ha0 : a = 0 := by
      have hh : glueShift2 n₁ n₂ a = 0 := ha
      simp only [glueShift2, Function.Embedding.coeFn_mk] at hh
      split_ifs at hh with h0 h1
      · exact Fin.ext h0
      · have := congrArg Fin.val hh; simp only [Fin.val_mk, Fin.val_zero] at this; omega
      · have := congrArg Fin.val hh; simp only [Fin.val_mk, Fin.val_zero] at this; omega
    have hb1 : b = 1 := by
      have hh : glueShift2 n₁ n₂ b = 1 := hb
      simp only [glueShift2, Function.Embedding.coeFn_mk] at hh
      split_ifs at hh with h0 h1
      · have := congrArg Fin.val hh; simp only [Fin.val_mk, Fin.val_zero, Fin.val_one] at this; omega
      · exact Fin.ext h1
      · have := congrArg Fin.val hh; simp only [Fin.val_mk, Fin.val_one] at this; omega
    rw [ha0, hb1] at hadj; exact h₂ hadj

/-- The edge finset of `edgeFreeGlue2` is the union of the shifted edge finsets. -/
private theorem edgeFreeGlue2_edgeFinset (n₁ n₂ : ℕ)
    (F₁ : SimpleGraph (Fin (n₁ + 2))) (F₂ : SimpleGraph (Fin (n₂ + 2)))
    [DecidableRel F₁.Adj] [DecidableRel F₂.Adj] :
    (edgeFreeGlue2 n₁ n₂ F₁ F₂).edgeFinset =
      F₁.edgeFinset.map (glueShift1 n₁ n₂).sym2Map ∪
      F₂.edgeFinset.map (glueShift2 n₁ n₂).sym2Map := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, Finset.mem_union, Finset.mem_map,
    Function.Embedding.sym2Map_apply]
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      change ((∃ x y : Fin (n₁ + 2), F₁.Adj x y ∧
          glueShift1 n₁ n₂ x = a ∧ glueShift1 n₁ n₂ y = b) ∨
        (∃ x y : Fin (n₂ + 2), F₂.Adj x y ∧
          glueShift2 n₁ n₂ x = a ∧ glueShift2 n₁ n₂ y = b)) at he
      rcases he with ⟨x, y, hadj, hx, hy⟩ | ⟨x, y, hadj, hx, hy⟩
      · left; exact ⟨s(x, y), hadj,
          by simp only [Sym2.map_pair_eq]; exact Sym2.eq_iff.mpr (Or.inl ⟨hx, hy⟩)⟩
      · right; exact ⟨s(x, y), hadj,
          by simp only [Sym2.map_pair_eq]; exact Sym2.eq_iff.mpr (Or.inl ⟨hx, hy⟩)⟩
  · intro he
    rcases he with ⟨e', he', rfl⟩ | ⟨e', he', rfl⟩
    · induction e' using Sym2.ind with
      | _ a b =>
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he'
        simp only [Sym2.map_pair_eq, SimpleGraph.mem_edgeSet]
        exact Or.inl ⟨a, b, he', rfl, rfl⟩
    · induction e' using Sym2.ind with
      | _ a b =>
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he'
        simp only [Sym2.map_pair_eq, SimpleGraph.mem_edgeSet]
        exact Or.inr ⟨a, b, he', rfl, rfl⟩

/-- The two shifted edge finsets in `edgeFreeGlue2` are disjoint (using h₁, h₂). -/
private theorem edgeFreeGlue2_edgeFinset_disjoint (n₁ n₂ : ℕ)
    (F₁ : SimpleGraph (Fin (n₁ + 2))) (F₂ : SimpleGraph (Fin (n₂ + 2)))
    [DecidableRel F₁.Adj] [DecidableRel F₂.Adj]
    (h₁ : ¬F₁.Adj 0 1) (h₂ : ¬F₂.Adj 0 1) :
    Disjoint
      (F₁.edgeFinset.map (glueShift1 n₁ n₂).sym2Map)
      (F₂.edgeFinset.map (glueShift2 n₁ n₂).sym2Map) := by
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  rw [Finset.mem_map] at he₁ he₂
  obtain ⟨e₁, he₁', rfl⟩ := he₁
  obtain ⟨e₂, he₂', he₂eq⟩ := he₂
  induction e₁ using Sym2.ind with
  | _ a₁ b₁ =>
    rw [SimpleGraph.mem_edgeFinset] at he₁'
    induction e₂ using Sym2.ind with
    | _ a₂ b₂ =>
      rw [SimpleGraph.mem_edgeFinset] at he₂'
      have ha₁ := a₁.isLt; have hb₁ := b₁.isLt
      have ha₂ := a₂.isLt; have hb₂ := b₂.isLt
      -- Unfold both shifts and work at val level
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq,
        glueShift1, glueShift2, Function.Embedding.coeFn_mk] at he₂eq
      -- Extract the Fin equalities from the Sym2 equality
      -- Helper: ⟨x.val,_⟩ equals glueShift2 image implies x.val ∈ {0,1}
      have small_of_fin_eq : ∀ (x : Fin (n₁ + 2)) (y : Fin (n₂ + 2)),
          (⟨x.val, by omega⟩ : Fin (n₁ + n₂ + 2)) =
            (if y.val = 0 then ⟨0, by omega⟩
             else if y.val = 1 then ⟨1, by omega⟩
             else ⟨y.val + n₁, by omega⟩ : Fin (n₁ + n₂ + 2)) →
          x.val = 0 ∨ x.val = 1 := fun x y heq => by
        have hx := x.isLt; have hy := y.isLt
        rw [Fin.ext_iff] at heq
        simp only [apply_ite Fin.val] at heq
        split_ifs at heq <;> omega
      -- In case 1: glueShift2(a₂)=glueShift1(a₁) and glueShift2(b₂)=glueShift1(b₁)
      -- In case 2: glueShift2(a₂)=glueShift1(b₁) and glueShift2(b₂)=glueShift1(a₁)
      have finish : ∀ (ha : a₁.val = 0 ∨ a₁.val = 1) (hb : b₁.val = 0 ∨ b₁.val = 1),
          False := fun ha hb => by
        rcases ha with ha₁0 | ha₁1 <;> rcases hb with hb₁0 | hb₁1
        · have heq : a₁ = b₁ := Fin.ext (by omega)
          exact absurd (heq ▸ he₁') (F₁.loopless a₁)
        · rw [show a₁ = (0 : Fin (n₁ + 2)) from Fin.ext ha₁0,
              show b₁ = (1 : Fin (n₁ + 2)) from Fin.ext hb₁1] at he₁'
          exact h₁ he₁'
        · rw [show a₁ = (1 : Fin (n₁ + 2)) from Fin.ext ha₁1,
              show b₁ = (0 : Fin (n₁ + 2)) from Fin.ext hb₁0] at he₁'
          exact h₁ (F₁.symm he₁')
        · have heq : a₁ = b₁ := Fin.ext (by omega)
          exact absurd (heq ▸ he₁') (F₁.loopless a₁)
      rcases Sym2.eq_iff.mp he₂eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · -- h1 : glueShift2(a₂) = glueShift1(a₁), h2 : glueShift2(b₂) = glueShift1(b₁)
        exact finish (small_of_fin_eq a₁ _ h1.symm) (small_of_fin_eq b₁ _ h2.symm)
      · -- h1 : glueShift2(a₂) = glueShift1(b₁), h2 : glueShift2(b₂) = glueShift1(a₁)
        exact finish (small_of_fin_eq a₁ _ h2.symm) (small_of_fin_eq b₁ _ h1.symm)

/-- The edge product over `edgeFreeGlue2` factors into the product from F₁ times F₂. -/
private theorem edgeFreeGlue2_prod_eq {k : ℕ} (n₁ n₂ : ℕ)
    (F₁ : SimpleGraph (Fin (n₁ + 2))) (F₂ : SimpleGraph (Fin (n₂ + 2)))
    [DecidableRel F₁.Adj] [DecidableRel F₂.Adj]
    (c : Fin k → Fin k → ℝ) (hc : ∀ i j, c i j = c j i)
    (h₁ : ¬F₁.Adj 0 1) (h₂ : ¬F₂.Adj 0 1)
    (σ : Fin (n₁ + n₂ + 2) → Fin k) :
    ∏ e ∈ (edgeFreeGlue2 n₁ n₂ F₁ F₂).edgeFinset,
      c (σ (Quot.out e).1) (σ (Quot.out e).2) =
    (∏ e ∈ F₁.edgeFinset,
      c (σ (glueShift1 n₁ n₂ (Quot.out e).1))
        (σ (glueShift1 n₁ n₂ (Quot.out e).2))) *
    (∏ e ∈ F₂.edgeFinset,
      c (σ (glueShift2 n₁ n₂ (Quot.out e).1))
        (σ (glueShift2 n₁ n₂ (Quot.out e).2))) := by
  rw [edgeFreeGlue2_edgeFinset,
    Finset.prod_union (edgeFreeGlue2_edgeFinset_disjoint n₁ n₂ F₁ F₂ h₁ h₂)]
  have prod_map_eq : ∀ {n : ℕ} {F : SimpleGraph (Fin (n + 2))} [DecidableRel F.Adj]
      (emb : Fin (n + 2) ↪ Fin (n₁ + n₂ + 2)),
      ∏ e ∈ F.edgeFinset.map emb.sym2Map,
        c (σ (Quot.out e).1) (σ (Quot.out e).2) =
      ∏ e ∈ F.edgeFinset,
        c (σ (emb (Quot.out e).1)) (σ (emb (Quot.out e).2)) := by
    intro n F _ emb
    rw [Finset.prod_map]
    congr 1; ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq, Function.comp_apply]
      have hout_new := Quot.out_eq (Sym2.map emb s(a, b))
      rw [Sym2.map_pair_eq] at hout_new
      have hout_old := Quot.out_eq s(a, b)
      rw [Sym2.mk_eq_mk_iff] at hout_new hout_old
      rcases hout_new with hn | hn <;> rcases hout_old with ho | ho <;> {
        rw [congr_arg Prod.fst hn, congr_arg Prod.snd hn,
            congr_arg Prod.fst ho, congr_arg Prod.snd ho]
        try rfl
        try exact hc _ _
      }
  congr 1
  · exact prod_map_eq (glueShift1 n₁ n₂)
  · exact prod_map_eq (glueShift2 n₁ n₂)

/-- Edge-free gluing realizes pointwise multiplication of 2-labeled evaluations:
`labeledEval2(glue F₁ F₂)(i,j) = labeledEval2(F₁)(i,j) * labeledEval2(F₂)(i,j)`.

This is the correct replacement for the false full-gluing theorem: it works because
both F₁ and F₂ are edge-free, so the glued graph has no duplicate edges.
This is the key multiplicative closure for the evaluation span. -/
private theorem labeledEval2_edgeFreeGlue2 {k : ℕ} (n₁ n₂ : ℕ)
    (F₁ : SimpleGraph (Fin (n₁ + 2))) (F₂ : SimpleGraph (Fin (n₂ + 2)))
    [DecidableRel F₁.Adj] [DecidableRel F₂.Adj]
    (c : Fin k → Fin k → ℝ) (hc : ∀ i j, c i j = c j i)
    (w : Fin k → ℝ) (i j : Fin k)
    (h₁ : ¬F₁.Adj 0 1) (h₂ : ¬F₂.Adj 0 1) :
    labeledEval2 (n₁ + n₂) (edgeFreeGlue2 n₁ n₂ F₁ F₂) c w i j =
      labeledEval2 n₁ F₁ c w i j * labeledEval2 n₂ F₂ c w i j := by
  simp only [labeledEval2]
  -- Coloring correspondence for glueShift1:
  -- τ (glueShift1 n₁ n₂ v) = τ₁ v where τ₁ = Fin.cons i (Fin.cons j σ₁), σ₁ = castAdd
  have h_emb₁ : ∀ σ : Fin (n₁ + n₂) → Fin k, ∀ v : Fin (n₁ + 2),
      (Fin.cons i (Fin.cons j σ) : Fin (n₁ + n₂ + 2) → Fin k) (glueShift1 n₁ n₂ v) =
      (Fin.cons i (Fin.cons j (fun r => σ (Fin.castAdd n₂ r))) : Fin (n₁ + 2) → Fin k) v := by
    intro σ v
    rcases Fin.eq_zero_or_eq_succ v with rfl | ⟨v', rfl⟩
    · simp [glueShift1, Fin.cons_zero]
    · rcases Fin.eq_zero_or_eq_succ v' with rfl | ⟨u, rfl⟩
      · simp [glueShift1, Fin.cons_zero]
      · -- glueShift1 (Fin.succ (Fin.succ u)) = Fin.succ (Fin.succ (castAdd n₂ u))
        have hshift : glueShift1 n₁ n₂ (Fin.succ (Fin.succ u)) =
            Fin.succ (Fin.succ (Fin.castAdd n₂ u)) := by
          ext; simp [glueShift1, Fin.val_succ, Fin.castAdd]
        rw [hshift, Fin.cons_succ, Fin.cons_succ, Fin.cons_succ, Fin.cons_succ]
  -- Coloring correspondence for glueShift2:
  -- τ (glueShift2 n₁ n₂ v) = τ₂ v where τ₂ = Fin.cons i (Fin.cons j σ₂), σ₂ = natAdd
  have h_emb₂ : ∀ σ : Fin (n₁ + n₂) → Fin k, ∀ v : Fin (n₂ + 2),
      (Fin.cons i (Fin.cons j σ) : Fin (n₁ + n₂ + 2) → Fin k) (glueShift2 n₁ n₂ v) =
      (Fin.cons i (Fin.cons j (fun r => σ (Fin.natAdd n₁ r))) : Fin (n₂ + 2) → Fin k) v := by
    intro σ v
    rcases Fin.eq_zero_or_eq_succ v with rfl | ⟨v', rfl⟩
    · simp [glueShift2, Fin.cons_zero]
    · rcases Fin.eq_zero_or_eq_succ v' with rfl | ⟨u, rfl⟩
      · simp [glueShift2, Fin.cons_zero]
      · -- glueShift2 (Fin.succ (Fin.succ u)) = Fin.succ (Fin.succ (natAdd n₁ u))
        have hshift : glueShift2 n₁ n₂ (Fin.succ (Fin.succ u)) =
            Fin.succ (Fin.succ (Fin.natAdd n₁ u)) := by
          ext; simp [glueShift2, Fin.val_succ, Fin.natAdd]; omega
        rw [hshift, Fin.cons_succ, Fin.cons_succ, Fin.cons_succ, Fin.cons_succ]
  -- Factor the LHS sum as product of two sums via sum_piFinAdd_factor
  rw [← sum_piFinAdd_factor
    (f := fun τ₁ : Fin n₁ → Fin k => (∏ v : Fin n₁, w (τ₁ v)) *
      ∏ e ∈ F₁.edgeFinset,
        c ((Fin.cons i (Fin.cons j τ₁) : Fin (n₁ + 2) → Fin k) (Quot.out e).1)
          ((Fin.cons i (Fin.cons j τ₁) : Fin (n₁ + 2) → Fin k) (Quot.out e).2))
    (g := fun τ₂ : Fin n₂ → Fin k => (∏ v : Fin n₂, w (τ₂ v)) *
      ∏ e ∈ F₂.edgeFinset,
        c ((Fin.cons i (Fin.cons j τ₂) : Fin (n₂ + 2) → Fin k) (Quot.out e).1)
          ((Fin.cons i (Fin.cons j τ₂) : Fin (n₂ + 2) → Fin k) (Quot.out e).2))]
  -- Show each summand matches
  congr 1; ext σ
  -- Decompose the weight product
  have h_wt : ∏ v : Fin (n₁ + n₂), w (σ v) =
      (∏ v : Fin n₁, w (σ (Fin.castAdd n₂ v))) *
      (∏ v : Fin n₂, w (σ (Fin.natAdd n₁ v))) :=
    Fin.prod_univ_add (fun v => w (σ v))
  -- Decompose the edge product
  have h_edges := edgeFreeGlue2_prod_eq n₁ n₂ F₁ F₂ c hc h₁ h₂
    (Fin.cons i (Fin.cons j σ))
  have h_f1 : (∏ e ∈ F₁.edgeFinset,
      c ((Fin.cons i (Fin.cons j σ) : Fin (n₁ + n₂ + 2) → Fin k)
          (glueShift1 n₁ n₂ (Quot.out e).1))
        ((Fin.cons i (Fin.cons j σ) : Fin (n₁ + n₂ + 2) → Fin k)
          (glueShift1 n₁ n₂ (Quot.out e).2))) =
    (∏ e ∈ F₁.edgeFinset,
      c ((Fin.cons i (Fin.cons j (fun r => σ (Fin.castAdd n₂ r))) : Fin (n₁ + 2) → Fin k)
          (Quot.out e).1)
        ((Fin.cons i (Fin.cons j (fun r => σ (Fin.castAdd n₂ r))) : Fin (n₁ + 2) → Fin k)
          (Quot.out e).2)) := by
    congr 1; ext e; rw [h_emb₁ σ (Quot.out e).1, h_emb₁ σ (Quot.out e).2]
  have h_f2 : (∏ e ∈ F₂.edgeFinset,
      c ((Fin.cons i (Fin.cons j σ) : Fin (n₁ + n₂ + 2) → Fin k)
          (glueShift2 n₁ n₂ (Quot.out e).1))
        ((Fin.cons i (Fin.cons j σ) : Fin (n₁ + n₂ + 2) → Fin k)
          (glueShift2 n₁ n₂ (Quot.out e).2))) =
    (∏ e ∈ F₂.edgeFinset,
      c ((Fin.cons i (Fin.cons j (fun r => σ (Fin.natAdd n₁ r))) : Fin (n₂ + 2) → Fin k)
          (Quot.out e).1)
        ((Fin.cons i (Fin.cons j (fun r => σ (Fin.natAdd n₁ r))) : Fin (n₂ + 2) → Fin k)
          (Quot.out e).2)) := by
    congr 1; ext e; rw [h_emb₂ σ (Quot.out e).1, h_emb₂ σ (Quot.out e).2]
  rw [h_wt, h_edges, h_f1, h_f2]; ring

/-! ### Edge-free evaluation algebra -/

/-- The set of 2-labeled evaluation functions coming from edge-free graphs
(those with `¬F.Adj 0 1`). -/
private def edgeFreeEvalSet {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    Set (Fin T → Fin T → ℝ) :=
  {f | ∃ (n : ℕ) (F : SimpleGraph (Fin (n + 2))) (_ : DecidableRel F.Adj) (_ : ¬F.Adj 0 1),
    f = fun i j => @labeledEval2 T n F ‹_› B W i j}

/-- The linear span of all edge-free 2-labeled evaluation functions. -/
private noncomputable def edgeFreeEvalSpan {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    Submodule ℝ (Fin T → Fin T → ℝ) :=
  Submodule.span ℝ (edgeFreeEvalSet B W)

/-- Adds the label edge {0, 1} to a 2-labeled graph. -/
private def addLabelEdge {n : ℕ} (F : SimpleGraph (Fin (n + 2))) :
    SimpleGraph (Fin (n + 2)) where
  Adj u v := F.Adj u v ∨ s(u, v) = s((0 : Fin (n + 2)), 1)
  symm u v h := by
    rcases h with h | h
    · exact Or.inl (F.symm h)
    · exact Or.inr (by rwa [Sym2.eq_swap])
  loopless v h := by
    rcases h with h | h
    · exact F.loopless v h
    · have := Sym2.eq_iff.mp h
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all

private instance addLabelEdgeDecRel {n : ℕ} (F : SimpleGraph (Fin (n + 2)))
    [DecidableRel F.Adj] : DecidableRel (addLabelEdge F).Adj :=
  fun u v => inferInstanceAs (Decidable (F.Adj u v ∨ s(u, v) = s((0 : Fin (n + 2)), 1)))

/-- `leftAttach2` preserves edge-freeness: if F has no label edge, neither does
`leftAttach2 n F`. -/
private theorem leftAttach2_edgeFree {n : ℕ} (F : SimpleGraph (Fin (n + 2)))
    (h : ¬F.Adj 0 1) : ¬(leftAttach2 n F).Adj 0 1 := by
  intro hadj
  -- Unfold: leftAttach2.Adj 0 1 is bridge∨bridge∨shifted
  change ((0 : Fin ((n + 1) + 2)).val = 0 ∧ (1 : Fin ((n + 1) + 2)).val = 2) ∨
    ((0 : Fin ((n + 1) + 2)).val = 2 ∧ (1 : Fin ((n + 1) + 2)).val = 0) ∨
    (∃ a b : Fin (n + 2), F.Adj a b ∧
      leftAttach2Shift n a = 0 ∧ leftAttach2Shift n b = 1) at hadj
  rcases hadj with ⟨_, hv⟩ | ⟨hu, _⟩ | ⟨a, b, hadj_ab, ha, hb⟩
  · -- 0.val = 0 ∧ 1.val = 2: contradicts 1.val = 1 ≠ 2
    simp at hv
  · -- 0.val = 2: contradicts 0.val = 0
    simp at hu
  · -- shifted case: leftAttach2Shift outputs ≥ 1 (specifically: 2, 1, or ≥3); never 0
    -- ha : leftAttach2Shift n a = (0 : Fin ((n+1)+2)), so its val = 0
    have ha_val : (leftAttach2Shift n a).val = 0 := by
      have := congrArg Fin.val ha; simpa using this
    simp only [leftAttach2Shift, Function.Embedding.coeFn_mk] at ha_val
    -- After split_ifs: val = 2, 1, or a.val+1 — none equals 0
    split_ifs at ha_val <;> simp_all

/-- `rightAttach2` preserves edge-freeness: if F has no label edge, neither does
`rightAttach2 n F`. -/
private theorem rightAttach2_edgeFree {n : ℕ} (F : SimpleGraph (Fin (n + 2)))
    (h : ¬F.Adj 0 1) : ¬(rightAttach2 n F).Adj 0 1 := by
  intro hadj
  change ((0 : Fin ((n + 1) + 2)).val = 1 ∧ (1 : Fin ((n + 1) + 2)).val = 2) ∨
    ((0 : Fin ((n + 1) + 2)).val = 2 ∧ (1 : Fin ((n + 1) + 2)).val = 1) ∨
    (∃ a b : Fin (n + 2), F.Adj a b ∧
      rightAttach2Shift n a = 0 ∧ rightAttach2Shift n b = 1) at hadj
  rcases hadj with ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨a, b, hadj_ab, ha, hb⟩
  · -- 0.val = 1: contradiction
    simp at hu
  · -- 0.val = 2: contradiction
    simp at hu
  · -- shifted case: rightAttach2Shift maps 0↦0, 1↦2, v+2↦v+3; never outputs 1
    -- hb : rightAttach2Shift n b = (1 : Fin ((n+1)+2)), so its val = 1
    have hb_val : (rightAttach2Shift n b).val = 1 := by
      have := congrArg Fin.val hb; simpa using this
    simp only [rightAttach2Shift, Function.Embedding.coeFn_mk] at hb_val
    -- After split_ifs: val = 0, 2, or b.val+1 — none equals 1 when b.val ≠ 0,1
    split_ifs at hb_val <;> simp_all

/-- `addLabelEdge F` has the label edge `0 -- 1`. -/
private theorem addLabelEdge_adj_01 {n : ℕ} (F : SimpleGraph (Fin (n + 2))) :
    (addLabelEdge F).Adj 0 1 :=
  Or.inr rfl

/-- Erasing the label edge from `addLabelEdge F` recovers F, provided F was edge-free. -/
private theorem eraseLabelEdge_addLabelEdge {n : ℕ} (F : SimpleGraph (Fin (n + 2)))
    (h : ¬F.Adj 0 1) : eraseLabelEdge (addLabelEdge F) = F := by
  ext u v
  simp only [eraseLabelEdge, addLabelEdge]
  constructor
  · rintro ⟨hadj | heq, hne⟩
    · exact hadj
    · -- heq : s(u,v) = s(0,1), hne : s(u,v) ≠ s(0,1) — contradiction
      exact absurd heq hne
  · intro hadj
    refine ⟨Or.inl hadj, ?_⟩
    intro heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd hadj h
    · exact absurd (F.symm hadj) h

/-- For an edge-free graph F, `labeledEval2 (addLabelEdge F) = B i j * labeledEval2 F`. -/
private theorem labeledEval2_addLabelEdge {k : ℕ} (n : ℕ)
    (F : SimpleGraph (Fin (n + 2))) [DecidableRel F.Adj]
    (B : Fin k → Fin k → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin k → ℝ) (i j : Fin k)
    (h : ¬F.Adj 0 1) :
    @labeledEval2 k n (addLabelEdge F) (addLabelEdgeDecRel F) B W i j =
      B i j * labeledEval2 n F B W i j := by
  rw [labeledEval2_eraseLabelEdge n (addLabelEdge F) B hB W i j (addLabelEdge_adj_01 F)]
  -- Now goal: B i j * labeledEval2 n (eraseLabelEdge (addLabelEdge F)) B W i j =
  --           B i j * labeledEval2 n F B W i j
  congr 1
  -- eraseLabelEdge (addLabelEdge F) = F, so their evals agree
  have heq : eraseLabelEdge (addLabelEdge F) = F := eraseLabelEdge_addLabelEdge F h
  simp only [labeledEval2]
  -- Use heq to rewrite the edgeFinset in the product
  have hedge : (eraseLabelEdge (addLabelEdge F)).edgeFinset = F.edgeFinset :=
    SimpleGraph.edgeFinset_inj.mpr heq
  congr 1; ext σ; congr 1
  apply Finset.prod_congr hedge
  intros; rfl

/-- The constant function `1` is in `edgeFreeEvalSpan`: it arises as the evaluation
of the empty graph `⊥ : SimpleGraph (Fin 2)`. -/
private theorem one_mem_edgeFreeEvalSpan {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    (fun _ _ => (1 : ℝ)) ∈ edgeFreeEvalSpan B W := by
  apply Submodule.subset_span
  refine ⟨0, ⊥, inferInstance, by simp [SimpleGraph.bot_adj], ?_⟩
  ext i j
  simp only [labeledEval2]
  simp only [Fintype.sum_unique, Fintype.prod_empty, one_mul]
  -- goal: 1 = ∏ e ∈ (⊥ : SimpleGraph (Fin 2)).edgeFinset, B (...) (...)
  -- The bot graph has no edges, so the product is 1
  symm
  apply Finset.prod_eq_one
  intro e he
  exact absurd he (by simp [SimpleGraph.mem_edgeFinset, SimpleGraph.bot_adj])

/-- The edge-free evaluation span is contained in the full evaluation span. -/
private theorem edgeFreeEvalSpan_le_eval2Span {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    edgeFreeEvalSpan B W ≤ eval2Span B W := by
  apply Submodule.span_le.mpr
  intro f ⟨n, F, inst, _, hf⟩
  apply Submodule.subset_span
  exact ⟨n, F, inst, hf⟩

/-! ### Evaluation algebra closure operators -/

/-- Left adjacency as a linear map: `(L f)(i,j) = ∑ a, W a * B i a * f a j` -/
private noncomputable def leftAdjLM {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    (Fin T → Fin T → ℝ) →ₗ[ℝ] (Fin T → Fin T → ℝ) where
  toFun f i j := ∑ a, W a * B i a * f a j
  map_add' f g := by ext i j; simp [Finset.sum_add_distrib, mul_add]
  map_smul' r f := by
    funext i j
    simp only [smul_eq_mul, Pi.smul_apply, RingHom.id_apply]
    rw [Finset.mul_sum]; congr 1; ext a; ring

/-- Right adjacency as a linear map: `(R f)(i,j) = ∑ a, W a * f i a * B a j` -/
private noncomputable def rightAdjLM {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    (Fin T → Fin T → ℝ) →ₗ[ℝ] (Fin T → Fin T → ℝ) where
  toFun f i j := ∑ a, W a * f i a * B a j
  map_add' f g := by ext i j; simp [Finset.sum_add_distrib, mul_add, add_mul]
  map_smul' r f := by
    funext i j
    simp only [smul_eq_mul, Pi.smul_apply, RingHom.id_apply]
    rw [Finset.mul_sum]; congr 1; ext a; ring

/-- Multiplication by edge observable as a linear map: `(E · f)(i,j) = B i j * f i j` -/
private noncomputable def mulByEdgeLM {T : ℕ} (B : Fin T → Fin T → ℝ) :
    (Fin T → Fin T → ℝ) →ₗ[ℝ] (Fin T → Fin T → ℝ) where
  toFun f i j := B i j * f i j
  map_add' f g := by ext i j; simp [mul_add]
  map_smul' r f := by ext i j; simp [mul_comm r, mul_assoc]

/-- Applying `leftAdjLM` to an edge-free generator yields another element of
`edgeFreeEvalSpan`: it corresponds to `leftAttach2 n F`. -/
private theorem leftAdj_generator_mem {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i)
    {n : ℕ} {F : SimpleGraph (Fin (n + 2))} [inst : DecidableRel F.Adj] (hF : ¬F.Adj 0 1) :
    leftAdjLM B W (fun a b => @labeledEval2 T n F inst B W a b) ∈ edgeFreeEvalSpan B W := by
  have h : ∀ i j, leftAdjLM B W (fun a b => @labeledEval2 T n F inst B W a b) i j =
      @labeledEval2 T (n + 1) (leftAttach2 n F) inferInstance B W i j := by
    intro i j
    simp only [leftAdjLM, LinearMap.coe_mk, AddHom.coe_mk]
    exact (labeledEval2_leftAttach n F B hB W i j).symm
  rw [show leftAdjLM B W (fun a b => @labeledEval2 T n F inst B W a b) =
      fun i j => @labeledEval2 T (n + 1) (leftAttach2 n F) inferInstance B W i j from
    funext fun i => funext fun j => h i j]
  exact Submodule.subset_span ⟨n + 1, leftAttach2 n F, inferInstance, leftAttach2_edgeFree F hF, rfl⟩

/-- Applying `rightAdjLM` to an edge-free generator yields another element of
`edgeFreeEvalSpan`: it corresponds to `rightAttach2 n F`. -/
private theorem rightAdj_generator_mem {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i)
    {n : ℕ} {F : SimpleGraph (Fin (n + 2))} [inst : DecidableRel F.Adj] (hF : ¬F.Adj 0 1) :
    rightAdjLM B W (fun a b => @labeledEval2 T n F inst B W a b) ∈ edgeFreeEvalSpan B W := by
  have h : ∀ i j, rightAdjLM B W (fun a b => @labeledEval2 T n F inst B W a b) i j =
      @labeledEval2 T (n + 1) (rightAttach2 n F) inferInstance B W i j := by
    intro i j
    simp only [rightAdjLM, LinearMap.coe_mk, AddHom.coe_mk]
    have heq : ∑ a : Fin T, W a * @labeledEval2 T n F inst B W i a * B a j =
        ∑ a : Fin T, W a * B a j * @labeledEval2 T n F inst B W i a := by
      congr 1; ext a; ring
    rw [heq, ← labeledEval2_rightAttach n F B hB W i j]
  rw [show rightAdjLM B W (fun a b => @labeledEval2 T n F inst B W a b) =
      fun i j => @labeledEval2 T (n + 1) (rightAttach2 n F) inferInstance B W i j from
    funext fun i => funext fun j => h i j]
  exact Submodule.subset_span
    ⟨n + 1, rightAttach2 n F, inferInstance, rightAttach2_edgeFree F hF, rfl⟩

/-- Pointwise product of two edge-free generators is in `edgeFreeEvalSpan`. -/
private theorem mul_generators_mem {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i)
    {n₁ n₂ : ℕ} {F₁ : SimpleGraph (Fin (n₁ + 2))} {F₂ : SimpleGraph (Fin (n₂ + 2))}
    [inst₁ : DecidableRel F₁.Adj] [inst₂ : DecidableRel F₂.Adj]
    (hF₁ : ¬F₁.Adj 0 1) (hF₂ : ¬F₂.Adj 0 1) :
    (fun i j => @labeledEval2 T n₁ F₁ inst₁ B W i j * @labeledEval2 T n₂ F₂ inst₂ B W i j) ∈
      edgeFreeEvalSpan B W := by
  have h : ∀ i j,
      @labeledEval2 T n₁ F₁ inst₁ B W i j * @labeledEval2 T n₂ F₂ inst₂ B W i j =
      @labeledEval2 T (n₁ + n₂) (edgeFreeGlue2 n₁ n₂ F₁ F₂) inferInstance B W i j := by
    intro i j
    exact (labeledEval2_edgeFreeGlue2 n₁ n₂ F₁ F₂ B hB W i j hF₁ hF₂).symm
  rw [show (fun i j =>
        @labeledEval2 T n₁ F₁ inst₁ B W i j * @labeledEval2 T n₂ F₂ inst₂ B W i j) =
      fun i j => @labeledEval2 T (n₁ + n₂) (edgeFreeGlue2 n₁ n₂ F₁ F₂) inferInstance B W i j from
    funext fun i => funext fun j => h i j]
  exact Submodule.subset_span
    ⟨n₁ + n₂, edgeFreeGlue2 n₁ n₂ F₁ F₂, inferInstance,
     edgeFreeGlue2_no_label_edge n₁ n₂ F₁ F₂ hF₁ hF₂, rfl⟩

/-- Applying `mulByEdgeLM B` to an edge-free generator yields an element of `eval2Span`:
it corresponds to `addLabelEdge F`. -/
private theorem mulByEdge_generator_mem {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i)
    {n : ℕ} {F : SimpleGraph (Fin (n + 2))} [inst : DecidableRel F.Adj] (hF : ¬F.Adj 0 1) :
    mulByEdgeLM B (fun a b => @labeledEval2 T n F inst B W a b) ∈ eval2Span B W := by
  have h : ∀ i j, mulByEdgeLM B (fun a b => @labeledEval2 T n F inst B W a b) i j =
      @labeledEval2 T n (addLabelEdge F) (addLabelEdgeDecRel F) B W i j := by
    intro i j
    simp only [mulByEdgeLM, LinearMap.coe_mk, AddHom.coe_mk]
    exact (labeledEval2_addLabelEdge n F B hB W i j hF).symm
  rw [show mulByEdgeLM B (fun a b => @labeledEval2 T n F inst B W a b) =
      fun i j => @labeledEval2 T n (addLabelEdge F) (addLabelEdgeDecRel F) B W i j from
    funext fun i => funext fun j => h i j]
  exact Submodule.subset_span ⟨n, addLabelEdge F, addLabelEdgeDecRel F, rfl⟩

/-- The image of `edgeFreeEvalSpan` under `leftAdjLM` is contained in `edgeFreeEvalSpan`. -/
private theorem leftAdj_mem_edgeFreeEvalSpan {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) :
    Submodule.map (leftAdjLM B W) (edgeFreeEvalSpan B W) ≤ edgeFreeEvalSpan B W := by
  rw [edgeFreeEvalSpan, Submodule.map_span_le]
  rintro g ⟨n, F, inst, hF, hg⟩
  rw [hg]; exact leftAdj_generator_mem B W hB hF

/-- The image of `edgeFreeEvalSpan` under `rightAdjLM` is contained in `edgeFreeEvalSpan`. -/
private theorem rightAdj_mem_edgeFreeEvalSpan {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) :
    Submodule.map (rightAdjLM B W) (edgeFreeEvalSpan B W) ≤ edgeFreeEvalSpan B W := by
  rw [edgeFreeEvalSpan, Submodule.map_span_le]
  rintro g ⟨n, F, inst, hF, hg⟩
  rw [hg]; exact rightAdj_generator_mem B W hB hF

/-- `edgeFreeEvalSpan` is closed under pointwise multiplication. -/
private theorem mul_mem_edgeFreeEvalSpan {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i)
    {f g : Fin T → Fin T → ℝ}
    (hf : f ∈ edgeFreeEvalSpan B W) (hg : g ∈ edgeFreeEvalSpan B W) :
    (fun i j => f i j * g i j) ∈ edgeFreeEvalSpan B W := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · rintro f₀ ⟨n₁, F₁, inst₁, hF₁, hf₀⟩
    rw [hf₀]
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
    · rintro g₀ ⟨n₂, F₂, inst₂, hF₂, hg₀⟩
      rw [hg₀]; exact mul_generators_mem B W hB hF₁ hF₂
    · show (fun i j => @labeledEval2 T n₁ F₁ inst₁ B W i j * (0 : Fin T → Fin T → ℝ) i j) ∈ _
      simp only [Pi.zero_apply, mul_zero]; exact Submodule.zero_mem _
    · intro g₁ g₂ _ _ hg₁ hg₂
      have : (fun i j => @labeledEval2 T n₁ F₁ inst₁ B W i j * (g₁ + g₂) i j) =
          (fun i j => @labeledEval2 T n₁ F₁ inst₁ B W i j * g₁ i j) +
          (fun i j => @labeledEval2 T n₁ F₁ inst₁ B W i j * g₂ i j) := by
        ext i j; simp [Pi.add_apply, mul_add]
      rw [this]; exact Submodule.add_mem _ hg₁ hg₂
    · intro r g₁ _ hg₁
      have : (fun i j => @labeledEval2 T n₁ F₁ inst₁ B W i j * (r • g₁) i j) =
          r • (fun i j => @labeledEval2 T n₁ F₁ inst₁ B W i j * g₁ i j) := by
        ext i j; simp [Pi.smul_apply, smul_eq_mul, mul_comm, mul_assoc, mul_left_comm]
      rw [this]; exact Submodule.smul_mem _ r hg₁
  · show (fun i j => (0 : Fin T → Fin T → ℝ) i j * g i j) ∈ _
    simp only [Pi.zero_apply, zero_mul]; exact Submodule.zero_mem _
  · intro f₁ f₂ _ _ hf₁ hf₂
    have : (fun i j => (f₁ + f₂) i j * g i j) =
        (fun i j => f₁ i j * g i j) + (fun i j => f₂ i j * g i j) := by
      ext i j; simp [Pi.add_apply, add_mul]
    rw [this]; exact Submodule.add_mem _ hf₁ hf₂
  · intro r f₁ _ hf₁
    have : (fun i j => (r • f₁) i j * g i j) = r • (fun i j => f₁ i j * g i j) := by
      ext i j; simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [this]; exact Submodule.smul_mem _ r hf₁

/-- The image of `edgeFreeEvalSpan` under `mulByEdgeLM B` is contained in `eval2Span`. -/
private theorem mulByEdge_edgeFreeEvalSpan_le_eval2Span {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) :
    Submodule.map (mulByEdgeLM B) (edgeFreeEvalSpan B W) ≤ eval2Span B W := by
  rw [edgeFreeEvalSpan, Submodule.map_span_le]
  rintro g ⟨n, F, inst, hF, hg⟩
  rw [hg]; exact mulByEdge_generator_mem B W hB hF

/-- Every generator of `eval2Span` is in
`edgeFreeEvalSpan ⊔ map (mulByEdgeLM B) edgeFreeEvalSpan`. -/
private theorem eval2Span_le_edgeFree_sup_mulByEdge {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) :
    eval2Span B W ≤
      edgeFreeEvalSpan B W ⊔ Submodule.map (mulByEdgeLM B) (edgeFreeEvalSpan B W) := by
  apply Submodule.span_le.mpr
  rintro f ⟨n, F, inst, hf⟩
  rw [hf]
  rcases Classical.em (F.Adj 0 1) with h01 | h01
  · -- F has the label edge; factor as B(i,j) * eval(eraseLabelEdge F)
    rw [SetLike.mem_coe, Submodule.mem_sup]
    refine ⟨0, Submodule.zero_mem _, _, ?_, zero_add _⟩
    apply Submodule.mem_map.mpr
    refine ⟨fun a b => @labeledEval2 T n (eraseLabelEdge F) (eraseLabelEdgeDecRel F) B W a b,
      Submodule.subset_span ⟨n, eraseLabelEdge F, eraseLabelEdgeDecRel F,
        eraseLabelEdge_not_adj_01 F, rfl⟩, ?_⟩
    ext i j
    simp only [mulByEdgeLM, LinearMap.coe_mk, AddHom.coe_mk]
    exact (@labeledEval2_eraseLabelEdge T n F inst B hB W i j h01).symm
  · -- F is edge-free; directly in edgeFreeEvalSpan
    rw [SetLike.mem_coe, Submodule.mem_sup]
    exact ⟨_, Submodule.subset_span ⟨n, F, inst, h01, rfl⟩, 0, Submodule.zero_mem _, add_zero _⟩

/-- Decomposition: `eval2Span = edgeFreeEvalSpan ⊔ map (mulByEdgeLM B) edgeFreeEvalSpan`. -/
private theorem eval2Span_eq_edgeFree_sup_mulByEdge {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) :
    eval2Span B W =
      edgeFreeEvalSpan B W ⊔ Submodule.map (mulByEdgeLM B) (edgeFreeEvalSpan B W) := by
  apply le_antisymm
  · exact eval2Span_le_edgeFree_sup_mulByEdge B W hB
  · exact sup_le (edgeFreeEvalSpan_le_eval2Span B W)
      (mulByEdge_edgeFreeEvalSpan_le_eval2Span B W hB)

/-! ### CT-1 bridge: indistinguishability relations -/

/-- Two pairs are edge-free indistinguishable if every edge-free 2-labeled evaluation
agrees on them. -/
private def edgeFreeIndist {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (p q : Fin T × Fin T) : Prop :=
  ∀ f ∈ edgeFreeEvalSet B W, f p.1 p.2 = f q.1 q.2

/-- Two pairs are fully indistinguishable if they are edge-free indistinguishable
and have the same direct edge value B(i,j). -/
private def fullIndist {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (p q : Fin T × Fin T) : Prop :=
  edgeFreeIndist B W p q ∧ B p.1 p.2 = B q.1 q.2

private theorem edgeFreeIndist_refl {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (p : Fin T × Fin T) : edgeFreeIndist B W p p :=
  fun _ _ => rfl

private theorem edgeFreeIndist_symm {T : ℕ} {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    {p q : Fin T × Fin T} (h : edgeFreeIndist B W p q) : edgeFreeIndist B W q p :=
  fun f hf => (h f hf).symm

private theorem fullIndist_refl {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (p : Fin T × Fin T) : fullIndist B W p p :=
  ⟨edgeFreeIndist_refl B W p, rfl⟩

/-- Functions in edgeFreeEvalSpan are constant on edgeFreeIndist-classes. -/
private theorem edgeFreeEvalSpan_constant_on_edgeFreeIndist {T : ℕ}
    {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    {f : Fin T → Fin T → ℝ} (hf : f ∈ edgeFreeEvalSpan B W)
    {p q : Fin T × Fin T} (hpq : edgeFreeIndist B W p q) :
    f p.1 p.2 = f q.1 q.2 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · intro g hg; exact hpq g hg
  · rfl
  · intro g₁ g₂ _ _ h₁ h₂; simp only [Pi.add_apply]; rw [h₁, h₂]
  · intro r g _ hg; simp only [Pi.smul_apply, smul_eq_mul]; rw [hg]

/-- Functions in eval2Span are constant on fullIndist-classes. -/
private theorem eval2Span_constant_on_fullIndist {T : ℕ}
    {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    (hB : ∀ i j, B i j = B j i)
    {f : Fin T → Fin T → ℝ} (hf : f ∈ eval2Span B W)
    {p q : Fin T × Fin T} (hpq : fullIndist B W p q) :
    f p.1 p.2 = f q.1 q.2 := by
  rw [eval2Span_eq_edgeFree_sup_mulByEdge B W hB] at hf
  obtain ⟨g, hg, h, hh, rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨h₀, hh₀, rfl⟩ := Submodule.mem_map.mp hh
  simp only [Pi.add_apply, mulByEdgeLM, LinearMap.coe_mk, AddHom.coe_mk]
  rw [edgeFreeEvalSpan_constant_on_edgeFreeIndist hg hpq.1,
      edgeFreeEvalSpan_constant_on_edgeFreeIndist hh₀ hpq.1, hpq.2]

/-- Orbit-related pairs are fully indistinguishable (easy direction of CT-1). -/
private theorem pairOrbitRel_implies_fullIndist {T : ℕ}
    {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    (hB : ∀ i j, B i j = B j i)
    {p q : Fin T × Fin T} (h : pairOrbitRel B W p q) :
    fullIndist B W p q := by
  obtain ⟨π, ⟨hw, hc⟩, h1, h2⟩ := h
  constructor
  · -- Edge-free indist: each edge-free evaluation is Aut-invariant
    intro f ⟨n, F, inst, hF, hf⟩
    rw [hf, ← h1, ← h2]
    exact (labeledEval2_perm_eq n F B W π hc hw p.1 p.2).symm
  · -- Edge value preserved by automorphism
    rw [← h1, ← h2]; exact (hc p.1 p.2).symm

/-! ### Lovász TR-2004-82 k-labeled infrastructure

The 5-motif route below (starting at the "Explicit separating motifs" header)
was refuted by the `C₅ ⊔ C₆` counterexample (`scripts/counterexample_C5_C6.py`).
This section installs the **honest book path** from Lovász's
*The rank of connection matrices and the dimension of graph algebras*
(Microsoft Research Technical Report TR-2004-82, August 2004;
<https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2004-82.pdf>;
book form: *Large Networks and Graph Limits*, AMS Colloquium Publications 60).

This is **Session A** of the pivot: k-labeled evaluation, equivalence, orbit
relation, cheap consistency/invariance lemmas, and Claim 4.1 (restriction).
Claim 4.2 (trace-extension) is installed as the new honest frontier sorry.
The existing CT-1 chain (line 5200) and downstream theorems still route
through the known-false motif subclaims for now; rewiring is deferred to a
later session after Lemma 2.4 itself has landed.
-/

/-- **Lovász TR-2004-82 eq. (1)**, p. 4. Normalized k-labeled hom count.

For a k-labeled graph `F` on `Fin (n + k)` with the first `k` vertices labeled
by `φ : Fin k → Fin T`, and `n` unlabeled vertices summed over via
`σ : Fin n → Fin T`. The combined coloring `τ : Fin (n + k) → Fin T` puts
labels at indices `0..k-1` and unlabeled at indices `k..n+k-1`.

This generalizes `rootedEval` (k=1, line 2311) and `labeledEval2` (k=2,
line 2756). -/
private noncomputable def labeledEvalK {T : ℕ} (k n : ℕ)
    (F : SimpleGraph (Fin (n + k))) [DecidableRel F.Adj]
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (φ : Fin k → Fin T) : ℝ :=
  ∑ σ : Fin n → Fin T,
    let τ : Fin (n + k) → Fin T := fun v =>
      if h : (v : ℕ) < k then φ ⟨v, h⟩
      else σ ⟨v - k, by have := v.isLt; omega⟩
    (∏ v : Fin n, W (σ v)) *
    ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2)

/-- **Lovász TR-2004-82 §2**, p. 6. Two label maps `φ, ψ : Fin k → Fin T` are
*equivalent* iff every k-labeled graph evaluates equally on them. -/
private def tupleEquiv {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) {k : ℕ}
    (φ ψ : Fin k → Fin T) : Prop :=
  ∀ (n : ℕ) (F : SimpleGraph (Fin (n + k))) [DecidableRel F.Adj],
    labeledEvalK k n F B W φ = labeledEvalK k n F B W ψ

/-- **Lovász TR-2004-82 §2**, p. 5 (orbit relation on k-tuples).
Two tuples are orbit-related iff some `(B, W)`-automorphism conjugates one
into the other. Composition order matches `pairOrbitRel` at line 3352:
`ψ i = σ (φ i)`. -/
private def tupleOrbitRel {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    {k : ℕ} (φ ψ : Fin k → Fin T) : Prop :=
  ∃ σ : Equiv.Perm (Fin T),
    IsWeightedAutomorphism B W σ ∧ ∀ i, ψ i = σ (φ i)

/-- Restriction of a `(k+1)`-tuple to its first `k` coordinates via
`Fin.castSucc`. Lovász's `φ'` notation. -/
private def restrictTuple {T k : ℕ} (φ : Fin (k + 1) → Fin T) : Fin k → Fin T :=
  fun i => φ i.castSucc

/-- **k=1 compatibility**: `labeledEvalK` at k=1 agrees with `rootedEval`. -/
private theorem labeledEvalK_one_eq_rootedEval {T : ℕ} (n : ℕ)
    (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj]
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (i : Fin T) :
    labeledEvalK 1 n F B W (fun _ => i) = rootedEval n F B W i := by
  -- Helper: pointwise equality of the two τ functions. Use explicit
  -- non-dependent ascription to avoid the motive issue on Fin.cons.
  have htau : ∀ (σ : Fin n → Fin T) (v : Fin (n + 1)),
      (if h : (v : ℕ) < 1 then (fun _ : Fin 1 => i) ⟨v, h⟩
       else σ ⟨v - 1, by have := v.isLt; omega⟩) =
      (Fin.cons (α := fun _ => Fin T) i σ) v := by
    intro σ v
    by_cases hv : (v : ℕ) < 1
    · rw [dif_pos hv]
      have h0 : v = (0 : Fin (n + 1)) := by
        apply Fin.ext; show v.val = 0; omega
      subst h0
      rfl
    · rw [dif_neg hv]
      set m : Fin n := ⟨v.val - 1, by have := v.isLt; omega⟩ with hm_def
      have hrw : v = (m.succ : Fin (n + 1)) := by
        apply Fin.ext
        show v.val = (m.succ : Fin (n + 1)).val
        simp [hm_def, Fin.val_succ]
        omega
      rw [hrw]
      rfl
  simp only [labeledEvalK, rootedEval]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun e _ => ?_
  congr 1 <;> exact htau σ _

/-- **k=2 compatibility**: `labeledEvalK` at k=2 agrees with `labeledEval2`. -/
private theorem labeledEvalK_two_eq_labeledEval2 {T : ℕ} (n : ℕ)
    (F : SimpleGraph (Fin (n + 2))) [DecidableRel F.Adj]
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (i j : Fin T) :
    labeledEvalK 2 n F B W ![i, j] = labeledEval2 n F B W i j := by
  -- Helper: pointwise equality of the two τ functions.
  have htau : ∀ (σ : Fin n → Fin T) (v : Fin (n + 2)),
      (if h : (v : ℕ) < 2 then (![i, j] : Fin 2 → Fin T) ⟨v, h⟩
       else σ ⟨v - 2, by have := v.isLt; omega⟩) =
      (Fin.cons (α := fun _ => Fin T) i
        (Fin.cons (α := fun _ => Fin T) j σ)) v := by
    intro σ v
    by_cases hv0 : v.val = 0
    · have h : (v : ℕ) < 2 := by omega
      rw [dif_pos h]
      have heq : v = (0 : Fin (n + 2)) := by
        apply Fin.ext; show v.val = 0; exact hv0
      subst heq
      rfl
    by_cases hv1 : v.val = 1
    · have h : (v : ℕ) < 2 := by omega
      rw [dif_pos h]
      have heq : v = ((0 : Fin (n + 1)).succ : Fin (n + 2)) := by
        apply Fin.ext
        show v.val = ((0 : Fin (n + 1)).succ : Fin (n + 2)).val
        simp [Fin.val_succ]
        exact hv1
      subst heq
      rfl
    -- v.val ≥ 2
    have hv : ¬ (v : ℕ) < 2 := by omega
    rw [dif_neg hv]
    set m : Fin n := ⟨v.val - 2, by have := v.isLt; omega⟩ with hm_def
    have hrw : v = ((m.succ : Fin (n + 1)).succ : Fin (n + 2)) := by
      apply Fin.ext
      show v.val = ((m.succ : Fin (n + 1)).succ : Fin (n + 2)).val
      simp [hm_def, Fin.val_succ]
      omega
    rw [hrw]
    rfl
  simp only [labeledEvalK, labeledEval2]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun e _ => ?_
  congr 1 <;> exact htau σ _

/-- **Automorphism invariance of `labeledEvalK`**. Generalizes
`labeledEval2_perm_eq` (line 2768) to arbitrary k. Proof structure matches
k=2 exactly: reindex `σ = π ∘ σ'` via `Equiv.piCongrRight`, then observe
that `τ` commutes with `π` on both label and unlabeled positions. -/
private theorem labeledEvalK_perm_eq {T k : ℕ} (n : ℕ)
    (F : SimpleGraph (Fin (n + k))) [DecidableRel F.Adj]
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (π : Equiv.Perm (Fin T))
    (hc : ∀ i j, B (π i) (π j) = B i j) (hw : ∀ i, W (π i) = W i)
    (φ : Fin k → Fin T) :
    labeledEvalK k n F B W (π ∘ φ) = labeledEvalK k n F B W φ := by
  simp only [labeledEvalK]
  -- Reindex σ = π ∘ σ'
  let e : (Fin n → Fin T) ≃ (Fin n → Fin T) :=
    Equiv.piCongrRight (fun _ => π)
  rw [(Equiv.sum_comp e _).symm]
  congr 1; ext σ'
  have he : ∀ v, e σ' v = π (σ' v) := fun v => by simp [e]
  -- Weight product: ∏ W(e σ' v) = ∏ W(π (σ' v)) = ∏ W(σ' v) by hw
  have hw_prod : ∏ v : Fin n, W (e σ' v) = ∏ v : Fin n, W (σ' v) := by
    congr 1; ext v; rw [he]; exact hw (σ' v)
  rw [hw_prod]; congr 1
  apply Finset.prod_congr rfl; intro x _
  -- Need: B(τ' (out x).1) (τ' (out x).2) = B(τ (out x).1) (τ (out x).2)
  -- where τ' uses (π ∘ φ, e σ') and τ uses (φ, σ').
  -- By pointwise reasoning on τ, we show τ' v = π (τ v) for all v.
  have hτ : ∀ v : Fin (n + k),
      (if h : (v : ℕ) < k then (π ∘ φ) ⟨v, h⟩
       else e σ' ⟨v - k, by have := v.isLt; omega⟩) =
      π (if h : (v : ℕ) < k then φ ⟨v, h⟩
         else σ' ⟨v - k, by have := v.isLt; omega⟩) := by
    intro v
    by_cases hv : (v : ℕ) < k
    · simp only [dif_pos hv]; rfl
    · simp only [dif_neg hv]; exact he _
  rw [hτ, hτ, hc]

/-- **Easy direction**: `tupleOrbitRel` implies `tupleEquiv`. The reverse
direction is the hard Lovász Lemma 2.4. -/
private theorem tupleEquiv_of_tupleOrbitRel {T k : ℕ}
    {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    {φ ψ : Fin k → Fin T} (h : tupleOrbitRel B W φ ψ) :
    tupleEquiv B W φ ψ := by
  obtain ⟨π, ⟨hw, hc⟩, hψ⟩ := h
  intro n F _
  -- ψ = π ∘ φ by `hψ`
  have hψ_eq : ψ = π ∘ φ := funext hψ
  rw [hψ_eq, labeledEvalK_perm_eq n F B W π hc hw φ]

/-! ### Lovász TR-2004-82 Claim 4.1 and frontier statement (Claim 4.2) -/

/-- **Lovász TR-2004-82, Claim 4.1**, §4.3, p. 9.
Restriction preserves tuple equivalence.

**Proof idea** (Lovász, p. 9): contrapositive. If the restrictions are
distinguished by some k-labeled `F`, then `F ⊗ E_1` (disjoint union of `F`
with a single isolated vertex labeled `k+1`) is a `(k+1)`-labeled graph
that distinguishes the original tuples. The lift uses `Fin.succAbove` to
insert the new label at position `k`, shifting unlabeled vertices by 1.

The symmetry hypothesis `hB` is needed because `labeledEvalK` reads edges
via `Quot.out` (a classical choice), and only `B`-symmetry makes the
edge-product well-defined up to representative swap — see `h_edge` below. -/
private theorem tupleEquiv_restrict {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) {k : ℕ}
    {φ ψ : Fin (k + 1) → Fin T}
    (h : tupleEquiv B W φ ψ) :
    tupleEquiv B W (restrictTuple φ) (restrictTuple ψ) := by
  intro n F' hdec
  -- Helper: edge-product term is independent of the Sym2 representative,
  -- thanks to `hB`. Stated for `Fin (n + (k + 1))` (the F-side target) to
  -- avoid universe-polymorphism at the `private theorem` level.
  have h_edge : ∀ (ν : Fin (n + (k + 1)) → Fin T) (a b : Fin (n + (k + 1))),
      B (ν (Quot.out (s(a, b) : Sym2 (Fin (n + (k + 1))))).1)
        (ν (Quot.out (s(a, b) : Sym2 (Fin (n + (k + 1))))).2) = B (ν a) (ν b) := by
    intro ν a b
    have h_out_eq : Sym2.mk (Quot.out (s(a, b) : Sym2 (Fin (n + (k + 1))))) =
        s(a, b) := Quot.out_eq _
    rcases Sym2.mk_eq_mk_iff.mp h_out_eq with heq | heq
    · rw [heq]
    · rw [heq]; exact hB _ _
  have h_edge' : ∀ (ν : Fin (n + k) → Fin T) (a b : Fin (n + k)),
      B (ν (Quot.out (s(a, b) : Sym2 (Fin (n + k)))).1)
        (ν (Quot.out (s(a, b) : Sym2 (Fin (n + k)))).2) = B (ν a) (ν b) := by
    intro ν a b
    have h_out_eq : Sym2.mk (Quot.out (s(a, b) : Sym2 (Fin (n + k)))) = s(a, b) :=
      Quot.out_eq _
    rcases Sym2.mk_eq_mk_iff.mp h_out_eq with heq | heq
    · rw [heq]
    · rw [heq]; exact hB _ _
  -- Pivot: position k in Fin (n + (k + 1)).
  have hk : k < n + (k + 1) := by omega
  let p : Fin (n + (k + 1)) := ⟨k, hk⟩
  let shift : Fin (n + k) ↪ Fin (n + (k + 1)) := Fin.succAboveEmb p
  let F : SimpleGraph (Fin (n + (k + 1))) := SimpleGraph.map shift F'
  haveI hF_dec : DecidableRel F.Adj := Classical.decRel _
  -- The core translation lemma.
  suffices trans : ∀ (θ : Fin (k + 1) → Fin T),
      labeledEvalK (k + 1) n F B W θ = labeledEvalK k n F' B W (restrictTuple θ) by
    rw [← trans φ, ← trans ψ]
    exact h n F
  intro θ
  simp only [labeledEvalK]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  -- The edge product. Use `Finset.prod_bij` with `shift.sym2Map` as the
  -- bijection between F'.edgeFinset and F.edgeFinset.
  symm
  refine Finset.prod_bij (fun e _ => shift.sym2Map e) ?_ ?_ ?_ ?_
  · -- 1. Map lands in F.edgeFinset.
    intro e he
    change shift.sym2Map e ∈ (SimpleGraph.map shift F').edgeFinset
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    -- e ∈ F'.edgeSet means F'.Adj on the underlying pair; after shift it lands
    -- in (SimpleGraph.map shift F').edgeSet.
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq] at *
      rw [SimpleGraph.mem_edgeSet] at he ⊢
      exact ⟨a, b, he, rfl, rfl⟩
  · -- 2. Injective on edgeFinset.
    intro e1 _ e2 _ hij
    exact shift.sym2Map.injective hij
  · -- 3. Surjective onto F.edgeFinset.
    intro e he
    change e ∈ (SimpleGraph.map shift F').edgeFinset at he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ x y =>
      rw [SimpleGraph.mem_edgeSet] at he
      -- he : (SimpleGraph.map shift F').Adj x y
      obtain ⟨a, b, hab, hax, hby⟩ := he
      refine ⟨s(a, b), ?_, ?_⟩
      · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact hab
      · simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq]
        rw [hax, hby]
  · -- 4. Term-by-term equality.
    intro e _
    -- Abstract the τ functions to make h_edge / h_edge' applicable.
    set ν' : Fin (n + k) → Fin T := fun v =>
      if h : (v : ℕ) < k then (restrictTuple θ) ⟨v, h⟩
      else σ ⟨(v : Fin (n + k)).val - k, by have := v.isLt; omega⟩ with hν'_def
    set ν : Fin (n + (k + 1)) → Fin T := fun v =>
      if h : (v : ℕ) < k + 1 then θ ⟨v, h⟩
      else σ ⟨(v : Fin (n + (k + 1))).val - (k + 1),
              by have := v.isLt; omega⟩ with hν_def
    -- Induct on e : Sym2 (Fin (n+k)).
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq]
      -- Goal: B (ν' (out s(a,b)).1) (ν' (out s(a,b)).2) =
      --       B (ν (out s(shift a, shift b)).1) (ν (out s(shift a, shift b)).2).
      change B (ν' (Quot.out s(a, b)).1) (ν' (Quot.out s(a, b)).2) =
        B (ν (Quot.out s(shift a, shift b)).1) (ν (Quot.out s(shift a, shift b)).2)
      rw [h_edge' ν' a b, h_edge ν (shift a) (shift b)]
      -- Goal: B (ν' a) (ν' b) = B (ν (shift a)) (ν (shift b)).
      -- Reduces to pointwise equality ν ∘ shift = ν'.
      have hτ : ∀ v : Fin (n + k), ν (shift v) = ν' v := by
        intro v
        -- First compute (shift v).val in terms of v.val, case by case.
        by_cases hv : (v : ℕ) < k
        · -- Below the pivot: shift v = v.castSucc, (shift v).val = v.val.
          have h_shift_val : (shift v : Fin (n + (k + 1))).val = v.val := by
            show (p.succAboveEmb v : Fin (n + (k + 1))).val = v.val
            simp only [Fin.coe_succAboveEmb]
            rw [Fin.succAbove_of_castSucc_lt]
            · rfl
            · show v.castSucc < p
              simp only [Fin.lt_iff_val_lt_val, Fin.coe_castSucc]
              exact hv
          have h_lt : ((shift v : Fin (n + (k + 1))) : ℕ) < k + 1 := by
            rw [h_shift_val]; omega
          simp only [hν_def, hν'_def, dif_pos h_lt, dif_pos hv, restrictTuple]
          congr 1
          apply Fin.ext
          simp only [Fin.coe_castSucc]
          exact h_shift_val
        · -- Above the pivot: shift v = v.succ, (shift v).val = v.val + 1.
          have h_shift_val : (shift v : Fin (n + (k + 1))).val = v.val + 1 := by
            show (p.succAboveEmb v : Fin (n + (k + 1))).val = v.val + 1
            simp only [Fin.coe_succAboveEmb]
            rw [Fin.succAbove_of_le_castSucc]
            · rfl
            · show p ≤ v.castSucc
              simp only [Fin.le_iff_val_le_val, Fin.coe_castSucc]
              show k ≤ v.val
              omega
          have h_not_lt : ¬ ((shift v : Fin (n + (k + 1))) : ℕ) < k + 1 := by
            rw [h_shift_val]; omega
          simp only [hν_def, hν'_def, dif_neg h_not_lt, dif_neg hv]
          congr 1
          apply Fin.ext
          show (shift v : Fin (n + (k + 1))).val - (k + 1) = v.val - k
          rw [h_shift_val]; omega
      rw [hτ, hτ]

/-- **Domain-permutation invariance of `tupleEquiv`**. Permuting the label
positions (right-composing both sides with `π : Equiv.Perm (Fin k)`)
preserves equivalence. Mirrors the `tupleEquiv_restrict` proof pattern
(`SimpleGraph.map` + `Finset.prod_bij`) but permutes label positions
instead of dropping the last one.

Unlike `labeledEvalK_perm_eq` (codomain permutation, requires `π` to be a
`(B, W)`-automorphism), here `π` acts on the domain indices — no
automorphism hypothesis is needed. -/
private theorem tupleEquiv_dom_perm {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) {k : ℕ}
    {φ ψ : Fin k → Fin T} (π : Equiv.Perm (Fin k))
    (h : tupleEquiv B W φ ψ) :
    tupleEquiv B W (φ ∘ π) (ψ ∘ π) := by
  intro n F' hdec
  -- Build σ_perm : Equiv.Perm (Fin (n + k)) permuting label positions (val < k)
  -- via π, fixing unlabeled positions (val ≥ k).
  let spFun : Fin (n + k) → Fin (n + k) := fun v =>
    if h : (v : ℕ) < k then
      ⟨(π ⟨v.val, h⟩).val, by have := (π ⟨v.val, h⟩).isLt; omega⟩
    else v
  let spInv : Fin (n + k) → Fin (n + k) := fun v =>
    if h : (v : ℕ) < k then
      ⟨(π.symm ⟨v.val, h⟩).val, by have := (π.symm ⟨v.val, h⟩).isLt; omega⟩
    else v
  have hsp_lr : Function.LeftInverse spInv spFun := by
    intro v
    by_cases hv : (v : ℕ) < k
    · have hv' : ((⟨(π ⟨v.val, hv⟩).val,
          by have := (π ⟨v.val, hv⟩).isLt; omega⟩ : Fin (n + k))).val < k :=
        (π ⟨v.val, hv⟩).isLt
      show (if h : _ then _ else _) = v
      rw [show spFun v = ⟨(π ⟨v.val, hv⟩).val,
          by have := (π ⟨v.val, hv⟩).isLt; omega⟩ from dif_pos hv]
      rw [dif_pos hv']
      apply Fin.ext
      show (π.symm ⟨(π ⟨v.val, hv⟩).val, hv'⟩).val = v.val
      have hrec : (⟨(π ⟨v.val, hv⟩).val, hv'⟩ : Fin k) = π ⟨v.val, hv⟩ := Fin.ext rfl
      rw [hrec, π.symm_apply_apply]
    · show (if h : _ then _ else _) = v
      rw [show spFun v = v from dif_neg hv]
      rw [dif_neg hv]
  have hsp_rl : Function.RightInverse spInv spFun := by
    intro v
    by_cases hv : (v : ℕ) < k
    · have hv' : ((⟨(π.symm ⟨v.val, hv⟩).val,
          by have := (π.symm ⟨v.val, hv⟩).isLt; omega⟩ : Fin (n + k))).val < k :=
        (π.symm ⟨v.val, hv⟩).isLt
      show (if h : _ then _ else _) = v
      rw [show spInv v = ⟨(π.symm ⟨v.val, hv⟩).val,
          by have := (π.symm ⟨v.val, hv⟩).isLt; omega⟩ from dif_pos hv]
      rw [dif_pos hv']
      apply Fin.ext
      show (π ⟨(π.symm ⟨v.val, hv⟩).val, hv'⟩).val = v.val
      have hrec : (⟨(π.symm ⟨v.val, hv⟩).val, hv'⟩ : Fin k) = π.symm ⟨v.val, hv⟩ :=
        Fin.ext rfl
      rw [hrec, π.apply_symm_apply]
    · show (if h : _ then _ else _) = v
      rw [show spInv v = v from dif_neg hv]
      rw [dif_neg hv]
  let σ_perm : Equiv.Perm (Fin (n + k)) :=
    ⟨spFun, spInv, hsp_lr, hsp_rl⟩
  -- Edge-product is independent of Sym2 representative (B-symmetry).
  have h_edge : ∀ (ν : Fin (n + k) → Fin T) (a b : Fin (n + k)),
      B (ν (Quot.out (s(a, b) : Sym2 (Fin (n + k)))).1)
        (ν (Quot.out (s(a, b) : Sym2 (Fin (n + k)))).2) = B (ν a) (ν b) := by
    intro ν a b
    have h_out_eq : Sym2.mk (Quot.out (s(a, b) : Sym2 (Fin (n + k)))) = s(a, b) :=
      Quot.out_eq _
    rcases Sym2.mk_eq_mk_iff.mp h_out_eq with heq | heq
    · rw [heq]
    · rw [heq]; exact hB _ _
  -- The key graph: F = SimpleGraph.map σ_perm.toEmbedding F'.
  let F : SimpleGraph (Fin (n + k)) := SimpleGraph.map σ_perm.toEmbedding F'
  haveI hF_dec : DecidableRel F.Adj := Classical.decRel _
  -- Main reduction: labeledEvalK at (θ ∘ π, F') equals labeledEvalK at (θ, F).
  suffices trans : ∀ (θ : Fin k → Fin T),
      labeledEvalK k n F' B W (θ ∘ π) = labeledEvalK k n F B W θ by
    rw [trans φ, trans ψ]
    exact h n F
  intro θ
  simp only [labeledEvalK]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine Finset.prod_bij (fun e _ => σ_perm.toEmbedding.sym2Map e) ?_ ?_ ?_ ?_
  · intro e he
    change σ_perm.toEmbedding.sym2Map e ∈ (SimpleGraph.map σ_perm.toEmbedding F').edgeFinset
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq] at *
      rw [SimpleGraph.mem_edgeSet] at he ⊢
      exact ⟨a, b, he, rfl, rfl⟩
  · intro e1 _ e2 _ hij
    exact σ_perm.toEmbedding.sym2Map.injective hij
  · intro e he
    change e ∈ (SimpleGraph.map σ_perm.toEmbedding F').edgeFinset at he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ x y =>
      rw [SimpleGraph.mem_edgeSet] at he
      obtain ⟨a, b, hab, hax, hby⟩ := he
      refine ⟨s(a, b), ?_, ?_⟩
      · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact hab
      · simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq]
        rw [hax, hby]
  · intro e _
    set ν' : Fin (n + k) → Fin T := fun v =>
      if h : (v : ℕ) < k then (θ ∘ π) ⟨v, h⟩
      else σ ⟨(v : Fin (n + k)).val - k, by have := v.isLt; omega⟩ with hν'_def
    set ν : Fin (n + k) → Fin T := fun v =>
      if h : (v : ℕ) < k then θ ⟨v, h⟩
      else σ ⟨(v : Fin (n + k)).val - k, by have := v.isLt; omega⟩ with hν_def
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq]
      change B (ν' (Quot.out s(a, b)).1) (ν' (Quot.out s(a, b)).2) =
        B (ν (Quot.out s(σ_perm a, σ_perm b)).1) (ν (Quot.out s(σ_perm a, σ_perm b)).2)
      rw [h_edge ν' a b, h_edge ν (σ_perm a) (σ_perm b)]
      -- Pointwise: ν (σ_perm v) = ν' v.
      have hτ : ∀ v : Fin (n + k), ν (σ_perm v) = ν' v := by
        intro v
        by_cases hv : (v : ℕ) < k
        · have h_spm_eq : σ_perm v = ⟨(π ⟨v.val, hv⟩).val,
              by have := (π ⟨v.val, hv⟩).isLt; omega⟩ := by
            show spFun v = _
            exact dif_pos hv
          have h_lt : ((σ_perm v : Fin (n + k)) : ℕ) < k := by
            rw [h_spm_eq]; exact (π ⟨v.val, hv⟩).isLt
          simp only [hν_def, hν'_def, dif_pos h_lt, dif_pos hv]
          congr 1
          apply Fin.ext
          show (σ_perm v).val = (π ⟨v.val, hv⟩).val
          rw [h_spm_eq]
        · have h_spm_eq : σ_perm v = v := by
            show spFun v = _
            exact dif_neg hv
          rw [h_spm_eq]
          simp only [hν_def, hν'_def, dif_neg hv]
      rw [hτ, hτ]

/-- **Restriction along an arbitrary label-index injection**. For any
injection `r : Fin T' ↪ Fin k`, restricting tuple equivalence along `r`
on the label positions preserves equivalence. Generalizes both
`tupleEquiv_restrict` (drop the last coordinate: r = Fin.castSuccEmb) and
`tupleEquiv_dom_perm` (permute label positions: r = π.toEmbedding, T' = k).

Used in the proof of Claim 4.4 (`tupleEquiv_surjective_case_both`) to
restrict from `Fin k` down to `Fin T` along a section `r : Fin T ↪ Fin k`
of `φ`. -/
private theorem tupleEquiv_restrict_along {T k T' : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i)
    {φ ψ : Fin k → Fin T} (r : Fin T' ↪ Fin k)
    (h : tupleEquiv B W φ ψ) :
    tupleEquiv B W (φ ∘ r) (ψ ∘ r) := by
  intro n H hdec
  -- Build shift : Fin (n + T') → Fin (n + k): label positions via r,
  -- unlabeled positions shifted by (k - T').
  let shiftFun : Fin (n + T') → Fin (n + k) := fun v =>
    if hv : v.val < T' then
      ⟨(r ⟨v.val, hv⟩).val, by have := (r ⟨v.val, hv⟩).isLt; omega⟩
    else ⟨(v.val - T') + k, by have := v.isLt; omega⟩
  have shiftFun_pos : ∀ (v : Fin (n + T')) (hv : v.val < T'),
      shiftFun v = (⟨(r ⟨v.val, hv⟩).val,
        by have := (r ⟨v.val, hv⟩).isLt; omega⟩ : Fin (n + k)) := fun _ hv => dif_pos hv
  have shiftFun_neg : ∀ (v : Fin (n + T')) (hv : ¬ v.val < T'),
      shiftFun v = (⟨(v.val - T') + k, by have := v.isLt; omega⟩ : Fin (n + k)) :=
    fun _ hv => dif_neg hv
  have hshift_inj : Function.Injective shiftFun := by
    intro a b hab
    apply Fin.ext
    by_cases ha : a.val < T'
    · have ha' : (shiftFun a).val = (r ⟨a.val, ha⟩).val := by
        rw [shiftFun_pos a ha]
      by_cases hb : b.val < T'
      · have hb' : (shiftFun b).val = (r ⟨b.val, hb⟩).val := by
          rw [shiftFun_pos b hb]
        have hval : (r ⟨a.val, ha⟩).val = (r ⟨b.val, hb⟩).val := by
          rw [← ha', ← hb', hab]
        have heq : (⟨a.val, ha⟩ : Fin T') = ⟨b.val, hb⟩ :=
          r.injective (Fin.ext hval)
        simpa using heq
      · -- a labeled, b unlabeled: val mismatch on k-boundary.
        exfalso
        have hb' : (shiftFun b).val = (b.val - T') + k := by
          rw [shiftFun_neg b hb]
        have h1 : (shiftFun a).val < k := by rw [ha']; exact (r _).isLt
        have h2 : (shiftFun b).val ≥ k := by rw [hb']; omega
        have : (shiftFun a).val = (shiftFun b).val := by rw [hab]
        omega
    · have ha' : (shiftFun a).val = (a.val - T') + k := by
        rw [shiftFun_neg a ha]
      by_cases hb : b.val < T'
      · exfalso
        have hb' : (shiftFun b).val = (r ⟨b.val, hb⟩).val := by
          rw [shiftFun_pos b hb]
        have h1 : (shiftFun b).val < k := by rw [hb']; exact (r _).isLt
        have h2 : (shiftFun a).val ≥ k := by rw [ha']; omega
        have : (shiftFun a).val = (shiftFun b).val := by rw [hab]
        omega
      · have hb' : (shiftFun b).val = (b.val - T') + k := by
          rw [shiftFun_neg b hb]
        have heq : (shiftFun a).val = (shiftFun b).val := by rw [hab]
        rw [ha', hb'] at heq
        omega
  let shift : Fin (n + T') ↪ Fin (n + k) := ⟨shiftFun, hshift_inj⟩
  -- Edge-product helpers (B-symmetry absorbs Quot.out orientation).
  have h_edge : ∀ (ν : Fin (n + k) → Fin T) (a b : Fin (n + k)),
      B (ν (Quot.out (s(a, b) : Sym2 (Fin (n + k)))).1)
        (ν (Quot.out (s(a, b) : Sym2 (Fin (n + k)))).2) = B (ν a) (ν b) := by
    intro ν a b
    have h_out_eq : Sym2.mk (Quot.out (s(a, b) : Sym2 (Fin (n + k)))) = s(a, b) :=
      Quot.out_eq _
    rcases Sym2.mk_eq_mk_iff.mp h_out_eq with heq | heq
    · rw [heq]
    · rw [heq]; exact hB _ _
  have h_edge' : ∀ (ν : Fin (n + T') → Fin T) (a b : Fin (n + T')),
      B (ν (Quot.out (s(a, b) : Sym2 (Fin (n + T')))).1)
        (ν (Quot.out (s(a, b) : Sym2 (Fin (n + T')))).2) = B (ν a) (ν b) := by
    intro ν a b
    have h_out_eq : Sym2.mk (Quot.out (s(a, b) : Sym2 (Fin (n + T')))) = s(a, b) :=
      Quot.out_eq _
    rcases Sym2.mk_eq_mk_iff.mp h_out_eq with heq | heq
    · rw [heq]
    · rw [heq]; exact hB _ _
  let G : SimpleGraph (Fin (n + k)) := SimpleGraph.map shift H
  haveI hG_dec : DecidableRel G.Adj := Classical.decRel _
  suffices trans : ∀ (θ : Fin k → Fin T),
      labeledEvalK T' n H B W (θ ∘ r) = labeledEvalK k n G B W θ by
    rw [trans φ, trans ψ]
    exact h n G
  intro θ
  simp only [labeledEvalK]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine Finset.prod_bij (fun e _ => shift.sym2Map e) ?_ ?_ ?_ ?_
  · intro e he
    change shift.sym2Map e ∈ (SimpleGraph.map shift H).edgeFinset
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq] at *
      rw [SimpleGraph.mem_edgeSet] at he ⊢
      exact ⟨a, b, he, rfl, rfl⟩
  · intro e1 _ e2 _ hij
    exact shift.sym2Map.injective hij
  · intro e he
    change e ∈ (SimpleGraph.map shift H).edgeFinset at he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ x y =>
      rw [SimpleGraph.mem_edgeSet] at he
      obtain ⟨a, b, hab, hax, hby⟩ := he
      refine ⟨s(a, b), ?_, ?_⟩
      · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact hab
      · simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq]
        rw [hax, hby]
  · intro e _
    set ν' : Fin (n + T') → Fin T := fun v =>
      if h : (v : ℕ) < T' then (θ ∘ r) ⟨v, h⟩
      else σ ⟨(v : Fin (n + T')).val - T', by have := v.isLt; omega⟩ with hν'_def
    set ν : Fin (n + k) → Fin T := fun v =>
      if h : (v : ℕ) < k then θ ⟨v, h⟩
      else σ ⟨(v : Fin (n + k)).val - k, by have := v.isLt; omega⟩ with hν_def
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq]
      change B (ν' (Quot.out s(a, b)).1) (ν' (Quot.out s(a, b)).2) =
        B (ν (Quot.out s(shift a, shift b)).1) (ν (Quot.out s(shift a, shift b)).2)
      rw [h_edge' ν' a b, h_edge ν (shift a) (shift b)]
      -- Pointwise: ν (shift v) = ν' v.
      have hτ : ∀ v : Fin (n + T'), ν (shift v) = ν' v := by
        intro v
        by_cases hv : (v : ℕ) < T'
        · have h_sh_eq : (shift v).val = (r ⟨v.val, hv⟩).val := by
            show (shiftFun v).val = _
            rw [shiftFun_pos v hv]
          have h_lt : ((shift v : Fin (n + k)) : ℕ) < k := by
            rw [h_sh_eq]; exact (r _).isLt
          simp only [hν_def, hν'_def, dif_pos h_lt, dif_pos hv]
          congr 1
          apply Fin.ext
          show (shift v).val = (r ⟨v.val, hv⟩).val
          exact h_sh_eq
        · have h_sh_eq : (shift v).val = (v.val - T') + k := by
            show (shiftFun v).val = _
            rw [shiftFun_neg v hv]
          have h_ge : ¬ ((shift v : Fin (n + k)) : ℕ) < k := by
            rw [h_sh_eq]; omega
          simp only [hν_def, hν'_def, dif_neg h_ge, dif_neg hv]
          congr 1
          apply Fin.ext
          show (shift v).val - k = v.val - T'
          rw [h_sh_eq]; omega
      rw [hτ, hτ]

/-! ### Graph-level trace lemma (combinatorial form of Lovász eq. (6)) -/

/-- **Graph-level trace**: summing `labeledEvalK (k+1) n F B W` over the
last label `t` of a `(k+1)`-tuple `Fin.snoc φ t`, weighted by `W(t)`,
gives a sum with `k` labels from `φ` and `n+1` unlabeled positions.

This is the combinatorial heart of Lovász's trace operator
`tr : A_{k+1} → A_k` (TR-2004-82 §3, eq. (6), p. 7), without the
algebraic wrapping. Generalizes `rootedEval_weighted_sum` (line 2320,
k=0 → k=1) and `labeledEval2_weighted_sum_snd` (line 3203, k=1 → k=2).

The RHS is literally `labeledEvalK k (n+1) F B W φ` except stated
with explicit sums to avoid the `Fin (n + (k+1))` vs `Fin ((n+1) + k)`
type-cast. -/
private theorem labeledEvalK_sum_last_label {T : ℕ} (k n : ℕ)
    (F : SimpleGraph (Fin (n + (k + 1)))) [DecidableRel F.Adj]
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (φ : Fin k → Fin T) :
    ∑ t : Fin T, W t * labeledEvalK (k + 1) n F B W (Fin.snoc φ t) =
    ∑ σ' : Fin (n + 1) → Fin T,
      let τ : Fin (n + (k + 1)) → Fin T := fun v =>
        if h : (v : ℕ) < k then φ ⟨v, h⟩
        else σ' ⟨v.val - k, by have := v.isLt; omega⟩
      (∏ v : Fin (n + 1), W (σ' v)) *
      ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2) := by
  -- Unfold labeledEvalK on the LHS.
  simp only [labeledEvalK]
  -- LHS: ∑ t, W t * ∑ σ, (∏ W(σ v)) * ∏ B(τ_{k+1} ...)
  -- where τ_{k+1} uses (Fin.snoc φ t) on 0..k and σ on k+1..n+k.
  -- RHS: ∑ σ', (∏ W(σ' v)) * ∏ B(τ_k ...)
  -- where τ_k uses φ on 0..k-1 and σ' on k..n+k.
  -- Bijection: σ' = Fin.cons t σ (t at position 0 of σ').
  -- Reindex RHS via Fin.consEquiv to get ∑ (t, σ), then match.
  conv_rhs =>
    rw [(Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => Fin T)) _).symm]
  simp only [Fin.consEquiv_apply]
  rw [Fintype.sum_prod_type]
  -- Now RHS = ∑ t, ∑ σ, (∏ W(Fin.cons t σ v)) * ∏ B(τ_k(Fin.cons t σ) ...)
  -- LHS = ∑ t, ∑ σ, W(t) * (∏ W(σ v)) * ∏ B(τ_{k+1}(t, σ) ...)
  -- Push W(t) inside on LHS.
  congr 1; ext t
  rw [Finset.mul_sum]
  -- Both sides: ∑ σ, something(t, σ). Match summands.
  refine Finset.sum_congr rfl fun σ _ => ?_
  -- Weight product: W(t) * ∏ W(σ v) = ∏ W(Fin.cons t σ v)
  -- because ∏ W(Fin.cons t σ v) = W(t) * ∏ W(σ v) by Fin.prod_univ_succ.
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring_nf
  -- After ring_nf, both sides should have the same weight factor.
  -- Need to match edge products.
  congr 1
  refine Finset.prod_congr rfl fun e _ => ?_
  -- Pointwise τ equality: for all v : Fin (n + (k+1)),
  -- τ_{k+1}(Fin.snoc φ t, σ)(v) = τ_k(φ, Fin.cons t σ)(v).
  -- Pointwise τ equality: τ_{k+1}(Fin.snoc φ t, σ) = τ_k(φ, Fin.cons t σ).
  have hτ : ∀ v : Fin (n + (k + 1)),
      (if h : (v : ℕ) < k + 1 then (Fin.snoc (α := fun _ => Fin T) φ t) ⟨v, h⟩
       else σ ⟨v.val - (k + 1), by have := v.isLt; omega⟩) =
      (if h : (v : ℕ) < k then φ ⟨v, h⟩
       else (Fin.cons (α := fun _ => Fin T) t σ)
            ⟨v.val - k, by have := v.isLt; omega⟩) := by
    intro v
    by_cases hv : (v : ℕ) < k
    · -- v.val < k: both sides give φ(v).
      rw [dif_pos (show (v : ℕ) < k + 1 by omega), dif_pos hv]
      -- (Fin.snoc φ t) ⟨v, _⟩ = φ ⟨v, hv⟩
      have : (⟨v, (show (v : ℕ) < k + 1 by omega)⟩ : Fin (k + 1)) =
             (⟨v, hv⟩ : Fin k).castSucc := Fin.ext rfl
      rw [this, Fin.snoc_castSucc]
    by_cases hv_eq : (v : ℕ) = k
    · -- v.val = k: LHS gives t (Fin.snoc at last), RHS gives t (Fin.cons at 0).
      rw [dif_pos (show (v : ℕ) < k + 1 by omega), dif_neg hv]
      -- LHS: Fin.snoc φ t at position k = t (via Fin.snoc_last).
      have hlast : (⟨v.val, (show v.val < k + 1 by omega)⟩ : Fin (k + 1)) =
                   Fin.last k := by apply Fin.ext; show v.val = k; omega
      rw [hlast, Fin.snoc_last]
      -- RHS: Fin.cons t σ at position 0 = t (via Fin.cons_zero).
      have hzero : (⟨v.val - k, (by have := v.isLt; omega)⟩ : Fin (n + 1)) =
                   (0 : Fin (n + 1)) := by apply Fin.ext; show v.val - k = 0; omega
      rw [hzero]; rfl
    · -- v.val > k: LHS gives σ(v - (k+1)), RHS gives σ(v - k - 1) via Fin.cons_succ.
      rw [dif_neg (show ¬ (v : ℕ) < k + 1 by omega), dif_neg hv]
      -- (Fin.cons t σ) ⟨v.val - k, _⟩ = σ ⟨v.val - k - 1, _⟩
      have hsucc : (⟨v.val - k, (by have := v.isLt; omega)⟩ : Fin (n + 1)) =
                   (⟨v.val - k - 1, (by have := v.isLt; omega)⟩ : Fin n).succ :=
        Fin.ext (by simp [Fin.val_succ]; omega)
      rw [hsucc, Fin.cons_succ]
      congr 1
  -- Lean normalizes `k + 1` to `1 + k` after simp; reconcile.
  simp only [show (1 : ℕ) + k = k + 1 from by omega] at *
  congr 1 <;> exact hτ _

/-- The empty graph (0 unlabeled vertices) evaluates to 1. -/
private theorem labeledEvalK_empty {T : ℕ} (k : ℕ)
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (φ : Fin k → Fin T) :
    labeledEvalK k 0 (⊥ : SimpleGraph (Fin (0 + k))) B W φ = 1 := by
  simp only [labeledEvalK, Fintype.sum_unique, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
  apply Finset.prod_eq_one; intro e he; exfalso
  simp only [SimpleGraph.edgeFinset, Set.mem_toFinset, SimpleGraph.mem_edgeSet] at he
  exact Sym2.ind (fun a b h => (SimpleGraph.bot_adj a b).mp h) e he

/-- **Separation implies functional spanning on a finite type.**
Given a finite type `Q`, a function `d : Q → ℝ`, and a family of functions
`f : I → (Q → ℝ)` that:
(a) contains the constant 1 (∃ i₀, f i₀ = 1),
(b) is closed under pointwise multiplication (∀ i j, ∃ k, f k = f i * f j),
(c) separates points (q₁ ≠ q₂ → ∃ i, f i q₁ ≠ f i q₂),
(d) satisfies ∑_q d(q) * f(i)(q) = 0 for all i,
then d = 0.

Proof by strong induction on |Finset.filter (d · ≠ 0) Finset.univ|. -/
private theorem functional_span_zero {Q : Type*} [Fintype Q] [DecidableEq Q]
    {I : Type*} (f : I → Q → ℝ) (d : Q → ℝ)
    (hconst : ∃ i₀ : I, ∀ q, f i₀ q = 1)
    (hmul : ∀ i j : I, ∃ k : I, ∀ q, f k q = f i q * f j q)
    (hsep : ∀ q₁ q₂ : Q, q₁ ≠ q₂ → ∃ i : I, f i q₁ ≠ f i q₂)
    (hortho : ∀ i : I, ∑ q, d q * f i q = 0) :
    ∀ q, d q = 0 := by
  -- Induction on |{q | d q ≠ 0}|.
  -- We prove: for any d satisfying the hypotheses, |support(d)| = 0 → d = 0.
  -- By strong induction: if the result holds for all d' with smaller support,
  -- then it holds for d.
  suffices key : ∀ (m : ℕ) (d : Q → ℝ),
      (Finset.univ.filter (fun q => d q ≠ 0)).card ≤ m →
      (∀ i : I, ∑ q, d q * f i q = 0) →
      ∀ q, d q = 0 by
    exact key (Finset.univ.filter (fun q => d q ≠ 0)).card d le_rfl hortho
  intro m
  induction m with
  | zero =>
    intro d hm _
    intro q
    by_contra hq
    have : q ∈ Finset.univ.filter (fun q => d q ≠ 0) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
    have := Finset.card_pos.mpr ⟨q, this⟩
    omega
  | succ m IH =>
    intro d hm hd_ortho
    -- If d = 0, done.
    by_cases h_all_zero : ∀ q, d q = 0
    · exact h_all_zero
    push_neg at h_all_zero
    obtain ⟨q₀, hq₀⟩ := h_all_zero
    -- If q₀ is the only nonzero, use hconst to derive contradiction.
    by_cases h_unique : ∀ q, q ≠ q₀ → d q = 0
    · obtain ⟨i₀, hi₀⟩ := hconst
      have := hd_ortho i₀
      simp only [hi₀, mul_one] at this
      rw [show ∑ q, d q = d q₀ + ∑ q ∈ Finset.univ.erase q₀, d q from by
        rw [Finset.add_sum_erase _ _ (Finset.mem_univ _)]] at this
      have hzero : ∑ q ∈ Finset.univ.erase q₀, d q = 0 :=
        Finset.sum_eq_zero fun q hq => h_unique q (Finset.ne_of_mem_erase hq)
      rw [hzero, add_zero] at this
      exact absurd this hq₀
    · -- ∃ q₁ ≠ q₀ with d(q₁) ≠ 0.
      push_neg at h_unique
      obtain ⟨q₁, hq₁_ne, hq₁⟩ := h_unique
      -- Find f_i separating q₀ and q₁.
      obtain ⟨i_sep, hi_sep⟩ := hsep q₀ q₁ hq₁_ne.symm
      -- Define d'(q) = d(q) * (f i_sep q - f i_sep q₀).
      let d' : Q → ℝ := fun q => d q * (f i_sep q - f i_sep q₀)
      -- d' satisfies orthogonality.
      have hd'_ortho : ∀ j : I, ∑ q, d' q * f j q = 0 := by
        intro j
        obtain ⟨k, hk⟩ := hmul i_sep j
        show ∑ q, d q * (f i_sep q - f i_sep q₀) * f j q = 0
        have h1 : ∑ q, d q * (f i_sep q - f i_sep q₀) * f j q =
            ∑ q, d q * f i_sep q * f j q - ∑ q, d q * (f i_sep q₀ * f j q) := by
          simp only [Finset.sum_sub_distrib (f := fun q => d q * f i_sep q * f j q)
            (g := fun q => d q * (f i_sep q₀ * f j q)) |>.symm]
          congr 1; ext q; ring
        rw [h1]
        rw [show ∑ q, d q * f i_sep q * f j q = ∑ q, d q * f k q by
          congr 1; ext q; rw [hk]; ring]
        rw [hd_ortho k]
        rw [show ∑ q, d q * (f i_sep q₀ * f j q) =
          f i_sep q₀ * ∑ q, d q * f j q by
          rw [Finset.mul_sum]; congr 1; ext q; ring]
        rw [hd_ortho j, mul_zero, sub_self]
      -- d'(q₀) = 0.
      have hd'q₀ : d' q₀ = 0 := by
        show d q₀ * (f i_sep q₀ - f i_sep q₀) = 0; simp
      -- support(d') ⊆ support(d) \ {q₀}, so |support(d')| ≤ m.
      have hd'_card : (Finset.univ.filter (fun q => d' q ≠ 0)).card ≤ m := by
        have hsub : Finset.univ.filter (fun q => d' q ≠ 0) ⊆
            (Finset.univ.filter (fun q => d q ≠ 0)).erase q₀ := by
          intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
          rw [Finset.mem_erase]
          refine ⟨fun heq => ?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun habs => ?_⟩⟩
          · subst heq; exact hq hd'q₀
          · exact hq (show d' q = 0 by show d q * (f i_sep q - f i_sep q₀) = 0; rw [habs, zero_mul])
        calc (Finset.univ.filter (fun q => d' q ≠ 0)).card
            ≤ ((Finset.univ.filter (fun q => d q ≠ 0)).erase q₀).card :=
              Finset.card_le_card hsub
          _ ≤ (Finset.univ.filter (fun q => d q ≠ 0)).card - 1 :=
              Nat.le_sub_one_of_lt (Finset.card_erase_lt_of_mem
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq₀⟩))
          _ ≤ m := by omega
      -- Apply IH to d'.
      have := IH d' hd'_card hd'_ortho q₁
      -- d'(q₁) = d(q₁) * (f i_sep q₁ - f i_sep q₀) = 0
      change d q₁ * (f i_sep q₁ - f i_sep q₀) = 0 at this
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hq₁
      · exact absurd (sub_eq_zero.mp h) hi_sep.symm

/-- **IH-parameterized form of Lovász Claim 4.2** (extension of equivalent tuples).

Given the inductive hypothesis that Lemma 2.4 holds at level `k` (i.e.,
k-equivalence implies k-orbit), Claim 4.2 at level `k + 1` is an immediate
consequence: apply the orbit automorphism `σ` from `IH` to `μ`, and
`σ ∘ μ` extends `ψ` and is equivalent to `μ` by the easy direction
(`tupleEquiv_of_tupleOrbitRel`).

This lemma anchors the induction structure for Session D's proof of
Lemma 2.4 (the full theorem). -/
private theorem tupleEquiv_extend_of_ih {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    {k : ℕ} {φ ψ : Fin k → Fin T}
    (IH : tupleEquiv B W φ ψ → tupleOrbitRel B W φ ψ)
    (h : tupleEquiv B W φ ψ)
    (μ : Fin (k + 1) → Fin T) (hμ : restrictTuple μ = φ) :
    ∃ ν : Fin (k + 1) → Fin T, restrictTuple ν = ψ ∧ tupleEquiv B W μ ν := by
  obtain ⟨σ, hσ_aut, hσ_conj⟩ := IH h
  -- ν := σ ∘ μ extends ψ and is orbit-related to μ.
  refine ⟨σ ∘ μ, ?_, ?_⟩
  · -- restrictTuple (σ ∘ μ) = ψ
    funext i
    show σ (μ i.castSucc) = ψ i
    rw [show μ i.castSucc = φ i from congr_fun hμ i, ← hσ_conj i]
  · -- tupleEquiv B W μ (σ ∘ μ)
    exact tupleEquiv_of_tupleOrbitRel ⟨σ, hσ_aut, fun _ => rfl⟩

/-! ### Claim 4.2 via equivalence-class coefficient argument -/

/-- The restriction-weighted coefficient: for fixed `μ : Fin (k+1) → Fin T`,
the W-weighted count of extensions of `ξ : Fin k → Fin T` in the equivalence
class `Ψ_μ = {η : η ≡ μ}`.

`coeffRestrict μ ξ = ∑_{η ≡ μ, restrictTuple η = ξ} W(η (Fin.last k))`

This is the Lovász trace coefficient: the trace of the indicator `1_{Ψ_μ}`
evaluated at `ξ`. -/
private noncomputable def coeffRestrict {T : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) {k : ℕ} (μ : Fin (k + 1) → Fin T) (ξ : Fin k → Fin T) : ℝ :=
  ∑ t : Fin T,
    @ite ℝ (tupleEquiv B W μ (Fin.snoc ξ t)) (Classical.dec _) (W t) 0

/-- The coefficient at `φ = restrictTuple μ` is positive: μ itself witnesses. -/
private theorem coeffRestrict_pos_at_restrict {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (hW : ∀ i, 0 < W i) {k : ℕ}
    (μ : Fin (k + 1) → Fin T) :
    0 < coeffRestrict B W μ (restrictTuple μ) := by
  classical
  unfold coeffRestrict
  -- The term at t = μ (Fin.last k) contributes W(μ last) > 0.
  apply Finset.sum_pos'
  · intro i _; split_ifs with h
    · exact le_of_lt (hW i)
    · exact le_refl 0
  · refine ⟨μ (Fin.last k), Finset.mem_univ _, ?_⟩
    rw [if_pos]
    · exact hW _
    -- Need: Fin.snoc (restrictTuple μ) (μ (Fin.last k)) ≡ μ
    have hrecon : Fin.snoc (α := fun _ => Fin T)
        (restrictTuple μ) (μ (Fin.last k)) = μ := by
      ext i
      by_cases hi : (i : ℕ) < k
      · rw [show i = (⟨i, hi⟩ : Fin k).castSucc from Fin.ext rfl,
             Fin.snoc_castSucc]
        rfl
      · have : i = Fin.last k := by
          apply Fin.ext; show i.val = k; omega
        rw [this, Fin.snoc_last]
    rw [hrecon]; intro n F _; rfl

/-- If `coeffRestrict μ ξ > 0`, then there exists an extension `ν` of `ξ`
equivalent to `μ`. -/
private theorem exists_extension_of_coeffRestrict_pos {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (hW : ∀ i, 0 < W i) {k : ℕ}
    (μ : Fin (k + 1) → Fin T) (ξ : Fin k → Fin T)
    (hpos : 0 < coeffRestrict B W μ ξ) :
    ∃ ν : Fin (k + 1) → Fin T, restrictTuple ν = ξ ∧ tupleEquiv B W μ ν := by
  classical
  -- Some term in the sum is positive, so ∃ t with the if-condition true.
  unfold coeffRestrict at hpos
  rw [Finset.sum_pos_iff_of_nonneg (fun x _ => by split_ifs <;> [exact le_of_lt (hW x); rfl])]
    at hpos
  obtain ⟨t, _, ht⟩ := hpos
  split_ifs at ht with heq
  · refine ⟨Fin.snoc ξ t, funext fun i => Fin.snoc_castSucc .., heq⟩
  · linarith

set_option maxHeartbeats 4000000 in
/-- **Trace invariance of `coeffRestrict`**: the coefficient is constant on
k-equivalence classes. This is the single remaining gap for Claim 4.2.

**Proof sketch** (not yet formalized):

Step 1 (trace lemma): By `labeledEvalK_sum_last_label` + `ξ ≡ ξ'`,
for every (k+1)-labeled graph G on `Fin (n + (k+1))`:
`∑_t W(t) * h_G(Fin.snoc ξ t) = ∑_t W(t) * h_G(Fin.snoc ξ' t)`.

Step 2 (group by class): Since h_G is constant on (k+1)-equivalence
classes, both sides are `∑_{[ρ]} c_ξ([ρ]) * h_G([ρ])` where
`c_ξ([ρ]) = ∑_{t : (ξ,t) ∈ [ρ]} W(t)`. Hence
`∑_{[ρ]} (c_ξ([ρ]) - c_{ξ'}([ρ])) * h_G([ρ]) = 0` for all G.

Step 3 (linear independence of class evaluations): The vectors
`{v_{[ρ]} := (h_G([ρ]))_{all G} : [ρ] class}` are linearly independent
in `ℝ^{graphs}`. This follows from the algebra structure: `labeledEvalK`
evaluations are closed under multiplication (via graph disjoint union
with shared labels: `h_{G₁⊗G₂}(η) = h_{G₁}(η) * h_{G₂}(η)`), and
separation (by definition of `tupleEquiv`) plus multiplicative closure
gives spanning via the finite Stone-Weierstrass / Lagrange interpolation
argument: pick G₀ separating all classes pairwise (exists by combining
pairwise separators with a linear combination over ℝ), form the
Vandermonde matrix (h_{G₀^n}([ρ_i]))_{n,i}, and use its non-singularity.

Step 4: By Step 3, `∑_{[ρ]} d([ρ]) * h_G([ρ]) = 0` for all G forces
`d = 0`, i.e., `c_ξ = c_{ξ'}`. In particular `coeffRestrict B W μ ξ =
c_ξ([μ]) = c_{ξ'}([μ]) = coeffRestrict B W μ ξ'`.

**Remaining gap**: Step 3 requires formalizing the graph disjoint-union
product (`h_{G₁⊗G₂} = h_{G₁} · h_{G₂}`), constructing a single graph
G₀ that pairwise separates all classes, and the Vandermonde determinant
lemma. This is ~200-400 lines of new Lean. -/
private theorem coeffRestrict_equiv {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (hB : ∀ i j, B i j = B j i) {k : ℕ}
    (IH_orbit : ∀ {φ ψ : Fin k → Fin T}, tupleEquiv B W φ ψ → tupleOrbitRel B W φ ψ)
    (μ : Fin (k + 1) → Fin T) {ξ ξ' : Fin k → Fin T}
    (h : tupleEquiv B W ξ ξ') :
    coeffRestrict B W μ ξ = coeffRestrict B W μ ξ' := by
  classical
  -- **Step 1**: The trace identity. For every (k+1)-labeled graph, the
  -- W-weighted sum over the last label is a k-level evaluation, hence
  -- equal for ξ and ξ' by `h`.
  have trace_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin (n + (k + 1)))) [DecidableRel F.Adj],
      ∑ t : Fin T, W t * labeledEvalK (k + 1) n F B W (Fin.snoc ξ t) =
      ∑ t : Fin T, W t * labeledEvalK (k + 1) n F B W (Fin.snoc ξ' t) := by
    intro n F _
    -- By the trace lemma, each side equals a k-level evaluation.
    -- n + (k + 1) = (n + 1) + k, so F is also on Fin ((n+1) + k).
    -- Apply the trace lemma. The trace lemma gives each side as a
    -- k-level evaluation, which equals for ξ and ξ' by tupleEquiv.
    -- The Fin arithmetic n+(k+1) vs (n+1)+k is handled by
    -- converting the graph via Fin.castOrderIso.
    -- The trace lemma converts each side to a sum over Fin(n+1)→Fin T
    -- with edges from F. We need to relate this to labeledEvalK k (n+1)
    -- on a graph of type Fin((n+1)+k). Construct G inline.
    let G : SimpleGraph (Fin ((n + 1) + k)) :=
      { Adj := fun u v => F.Adj ⟨u.val, by have := u.isLt; omega⟩
                              ⟨v.val, by have := v.isLt; omega⟩
        symm := fun _ _ h => F.symm h
        loopless := fun _ h => F.loopless _ h }
    haveI : DecidableRel G.Adj := fun u v => inferInstanceAs
      (Decidable (F.Adj ⟨u.val, _⟩ ⟨v.val, _⟩))
    -- Bridge: the trace lemma RHS equals labeledEvalK k (n+1) G B W φ.
    have bridge : ∀ φ : Fin k → Fin T,
        ∑ t : Fin T, W t * labeledEvalK (k + 1) n F B W (Fin.snoc φ t) =
        labeledEvalK k (n + 1) G B W φ := by
      intro φ; rw [labeledEvalK_sum_last_label]; simp only [labeledEvalK]
      refine Finset.sum_congr rfl fun σ' _ => ?_; congr 1
      -- F.edgeFinset (Fin(n+(k+1))) ↔ G.edgeFinset via val-preserving bijection.
      -- Since n+(k+1) = (n+1)+k propositionally, use finCongr to transport edges.
      let e := finCongr (show n + (k + 1) = n + 1 + k by omega)
      -- Use Finset.prod_nbij' with Sym2.map e as the bijection.
      apply Finset.prod_nbij' (Sym2.map e) (Sym2.map e.symm)
      -- hi: F-edges map to G-edges
      · intro a ha
        refine Sym2.ind (fun u v h => ?_) a ha
        rw [SimpleGraph.mem_edgeFinset, Sym2.map_pair_eq, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at h; exact h
      -- hj: G-edges map to F-edges
      · intro a ha
        refine Sym2.ind (fun u v h => ?_) a ha
        rw [SimpleGraph.mem_edgeFinset, Sym2.map_pair_eq, SimpleGraph.mem_edgeSet]
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, G] at h; exact h
      -- left_inv: Sym2.map e.symm ∘ Sym2.map e = id
      · intro a _
        simp only [Sym2.map_map, Equiv.symm_comp_self]; exact congr_fun Sym2.map_id a
      -- right_inv: Sym2.map e ∘ Sym2.map e.symm = id
      · intro a _
        simp only [Sym2.map_map, Equiv.self_comp_symm]; exact congr_fun Sym2.map_id a
      -- hfg: the B-product values match for corresponding edges.
      -- Both sides evaluate B on the same .val, but Quot.out may pick different
      -- orderings. Use B-symmetry (hB) to handle both cases.
      · intro a ha
        refine Sym2.ind (fun u v _ => ?_) a ha
        simp only [Sym2.map_pair_eq]
        -- Need: B(τ_F(Quot.out s(u,v)).1)(τ_F(Quot.out s(u,v)).2) =
        --       B(τ_G(Quot.out s(eu,ev)).1)(τ_G(Quot.out s(eu,ev)).2)
        -- where τ_F, τ_G evaluate the same function on .val.
        -- Strategy: both sides = B(g(u.val))(g(v.val)) via Quot.out case analysis + hB.
        have hout_F := Sym2.rel_iff'.mp (Sym2.eq.mp (Quot.out_eq (s(u, v))))
        have hout_G := Sym2.rel_iff'.mp
          (Sym2.eq.mp (Quot.out_eq (s(e u, e v))))
        -- Both sides evaluate B on endpoints of the same unordered pair, but
        -- Quot.out may choose different orderings. Use B-symmetry.
        -- Helper: for any (a,b) related to (u,v) in Sym2.Rel, the τ-value
        -- is either B(τu)(τv) or B(τv)(τu) = B(τu)(τv) by hB.
        suffices key : ∀ {m : ℕ} (a b : Fin m) (p : Fin m × Fin m),
            p = (a, b) ∨ p = (b, a) →
            ∀ (f : Fin m → Fin T),
            B (f p.1) (f p.2) = B (f a) (f b) by
          -- Define τ_F and τ_G as Fin → Fin T.
          let τ_F : Fin (n + (k + 1)) → Fin T := fun x =>
            if h : (x : ℕ) < k then φ ⟨x, h⟩ else σ' ⟨x.val - k, by have := x.isLt; omega⟩
          let τ_G : Fin (n + 1 + k) → Fin T := fun x =>
            if h : (x : ℕ) < k then φ ⟨x, h⟩ else σ' ⟨x.val - k, by have := x.isLt; omega⟩
          rw [key u v _ hout_F τ_F, key (e u) (e v) _ hout_G τ_G]
          -- Now: B(τ_F u)(τ_F v) = B(τ_G (e u))(τ_G (e v)).
          -- Since e preserves .val, τ_F u = τ_G (e u).
          congr 1 <;> { simp only [τ_F, τ_G, e, finCongr_apply, Fin.val_cast]
                        split_ifs <;> congr 1 <;> exact Fin.ext rfl }
        intro m a b p hp f
        rcases hp with rfl | rfl
        · rfl
        · exact hB _ _
    rw [bridge ξ, bridge ξ']; exact h (n + 1) G
  -- **Step 2**: Define the difference function d.
  -- For each (k+1)-tuple η, assign it to its tupleEquiv class.
  -- Then coeffRestrict is a class-weighted sum.
  -- The trace identity says ∑ d(class) * h_F(class) = 0 for all F.
  --
  -- **Step 3**: Algebraic spanning / linear independence.
  -- The (k+1)-labeled evaluations (extended to multigraph evaluations
  -- via label B-power factors) form a unital point-separating subalgebra
  -- of functions on the finite set of equivalence classes. By the finite
  -- Stone-Weierstrass theorem (or strong induction on support size with
  -- graph products), the evaluations span all class functions.
  -- Therefore d = 0, giving coeffRestrict_equiv.
  --
  -- The full algebraic argument requires a multigraph evaluation framework
  -- (label-edge B-powers ∏ B(η(i),η(j))^{m(i,j)} times simple-graph
  -- evaluations with no label-label edges) and its multiplicative closure.
  -- This is the content of Lovász TR-2004-82 §3-4 (the algebra A_k and
  -- its trace operator). See the docstring above for the full proof sketch.
  --
  -- Core claim: for d : Q → ℝ with ∑_q d(q) * h_F(q) = 0 for all F,
  -- we have d = 0. Proof by strong induction on |support(d)| using:
  -- (a) multigraph evaluations separate classes (from tupleEquiv definition),
  -- (b) they are multiplicatively closed (graph product + multiplicity sum),
  -- (c) they contain constants (empty graph),
  -- (d) ∑ d * mg = 0 for all multigraph evals (trace identity extended
  --     via B(ξ(i),ξ(j)) = B(ξ'(i),ξ'(j)) from single-edge evaluations).
  unfold coeffRestrict
  -- We need: ∑ t, ite (μ ≡ snoc ξ t) (W t) 0 = ∑ t, ite (μ ≡ snoc ξ' t) (W t) 0
  -- Strategy: show any function constant on (k+1)-equivalence classes gives equal
  -- weighted sums over ξ-extensions and ξ'-extensions.
  --
  -- From trace_eq: ∑_t W(t) * f(snoc ξ t) = ∑_t W(t) * f(snoc ξ' t) for all evaluations f.
  -- The indicator 1_{[μ]} is in the closure of evaluations (by functional_span_zero
  -- applied to the quotient by (k+1)-equivalence). Hence the weighted sums match.
  --
  -- The full formalization passes through the quotient by tupleEquiv at level k+1,
  -- applies functional_span_zero with:
  -- - Q = quotient classes (Fintype via Quotient of Fintype)
  -- - f indexed by labeled graphs
  -- - hconst from labeledEvalK_empty
  -- - hmul from labeledEvalK_glue
  -- - hsep from tupleEquiv definition
  -- to conclude that the class-level weight difference is zero.
  --
  -- The key infrastructure gap is labeledEvalK_glue (graph product multiplicativity),
  -- which is a substantial but straightforward combinatorial argument.
  -- With it, the proof assembles cleanly from functional_span_zero.
  -- Define the class-level weight difference and show it vanishes.
  suffices class_eq : ∀ (g : (Fin (k + 1) → Fin T) → ℝ),
      (∀ η η', tupleEquiv B W η η' → g η = g η') →
      ∑ t, W t * g (Fin.snoc ξ t) = ∑ t, W t * g (Fin.snoc ξ' t) by
    -- Apply class_eq with g = indicator of [μ].
    have := class_eq (fun η => @ite ℝ (tupleEquiv B W μ η) (Classical.dec _) 1 0)
      (fun η η' heq => by
        simp only
        congr 1
        exact propext ⟨fun h n F => (h n F).trans (heq n F),
                        fun h n F => (h n F).trans (heq n F).symm⟩)
    simp only [mul_ite, mul_one, mul_zero] at this
    exact this
  -- Prove class_eq via the automorphism from `IH_orbit`.
  -- By IH_orbit, ∃ σ automorphism with ξ' = σ ∘ ξ. Then σ applied to
  -- Fin.snoc ξ t gives Fin.snoc ξ' (σ t), so g(snoc ξ t) = g(snoc ξ' (σ t))
  -- (g is class-constant, orbit-related tuples are in the same class).
  -- Reindexing by σ and using W(σ⁻¹ t) = W(t) gives the result.
  intro g hg_class
  obtain ⟨σ, hσ_aut, hσ_conj⟩ := IH_orbit h
  -- Key: σ ∘ (snoc ξ t) = snoc ξ' (σ t), so they're orbit-related.
  have hsnoc_orbit : ∀ t : Fin T,
      tupleOrbitRel B W (Fin.snoc ξ t) (Fin.snoc ξ' (σ t)) :=
    fun t => ⟨σ, hσ_aut, fun i => by
      by_cases hi : (i : ℕ) < k
      · rw [show i = (⟨i, hi⟩ : Fin k).castSucc from Fin.ext rfl,
             Fin.snoc_castSucc, Fin.snoc_castSucc, ← hσ_conj]
      · have : i = Fin.last k := by apply Fin.ext; show i.val = k; omega
        rw [this, Fin.snoc_last, Fin.snoc_last]⟩
  have hg_snoc : ∀ t, g (Fin.snoc ξ t) = g (Fin.snoc ξ' (σ t)) :=
    fun t => hg_class _ _ (tupleEquiv_of_tupleOrbitRel (hsnoc_orbit t))
  -- Reindex: ∑_t W(t) g(snoc ξ t) = ∑_t W(t) g(snoc ξ' (σ t))
  --        = ∑_s W(σ⁻¹ s) g(snoc ξ' s)  [substituting s = σ t]
  --        = ∑_s W(s) g(snoc ξ' s)        [σ preserves W]
  conv_lhs => arg 2; ext t; rw [hg_snoc t]
  -- Now LHS = ∑ t, W t * g (snoc ξ' (σ t)).
  -- Reindex via σ: ∑ t, f(σ t) = ∑ t, f(t) by Equiv.sum_comp.
  rw [show (∑ t, W t * g (Fin.snoc ξ' (σ t))) =
      ∑ t, W (σ.symm t) * g (Fin.snoc ξ' (σ (σ.symm t))) from
    (Equiv.sum_comp σ.symm _).symm]
  congr 1; ext t
  rw [show σ (σ.symm t) = t from σ.apply_symm_apply t]
  congr 1
  -- W(σ⁻¹ t) = W(t): from IsWeightedAutomorphism, W(σ x) = W(x) for all x.
  -- So W(σ⁻¹ t) = W(σ (σ⁻¹ t)) [by hσ_aut.1 applied to σ⁻¹ t ... reversed]
  have : W (σ (σ.symm t)) = W (σ.symm t) := hσ_aut.1 (σ.symm t)
  simp only [Equiv.apply_symm_apply] at this
  exact this.symm

/-- **Lovász TR-2004-82, Claim 4.2**, §4.3, p. 9 (trace-based extension).
Given equivalent k-tuples `φ, ψ` and any extension `μ` of `φ` to `k+1`,
there is an equivalent extension `ν` of `ψ`.

Assembled from `coeffRestrict_pos_at_restrict`, `coeffRestrict_equiv`,
and `exists_extension_of_coeffRestrict_pos`. Requires `IH_orbit`
(Lemma 2.4 at level k) for `coeffRestrict_equiv`. -/
private theorem tupleEquiv_extend {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (hB : ∀ i j, B i j = B j i)
    {k : ℕ}
    (IH_orbit : ∀ {φ ψ : Fin k → Fin T}, tupleEquiv B W φ ψ → tupleOrbitRel B W φ ψ)
    {φ ψ : Fin k → Fin T} (h : tupleEquiv B W φ ψ)
    (μ : Fin (k + 1) → Fin T) (hμ : restrictTuple μ = φ) :
    ∃ ν : Fin (k + 1) → Fin T, restrictTuple ν = ψ ∧ tupleEquiv B W μ ν := by
  -- The coefficient at restrictTuple μ is positive.
  have hpos : 0 < coeffRestrict B W μ (restrictTuple μ) :=
    coeffRestrict_pos_at_restrict B W hW μ
  -- By trace invariance (ξ = restrictTuple μ ≡ ψ via hμ ▸ h), coefficient at ψ is positive.
  have hpos_ψ : 0 < coeffRestrict B W μ ψ := by
    rwa [coeffRestrict_equiv B W hW hB IH_orbit μ (hμ ▸ h)] at hpos
  -- Extract a witness.
  exact exists_extension_of_coeffRestrict_pos B W hW μ ψ hpos_ψ

/-- Evaluation of a k-labeled graph with a single edge `{a, b}` and no unlabeled
vertices directly reads the matrix entry `B(φ a)(φ b)`. Generalizes `labeledEval2_edge`
to arbitrary k. The graph lives on `Fin (0 + k)` to match `labeledEvalK`'s signature. -/
private theorem labeledEvalK_singleEdge {T k : ℕ}
    (F : SimpleGraph (Fin (0 + k))) [DecidableRel F.Adj]
    {a b : Fin (0 + k)} (hab : a ≠ b)
    (hedge : F.edgeFinset = {s(a, b)})
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (φ : Fin k → Fin T) :
    labeledEvalK k 0 F B W φ =
      B (φ ⟨a.val, by omega⟩) (φ ⟨b.val, by omega⟩) := by
  simp only [labeledEvalK, Fintype.sum_unique, Finset.univ_eq_empty, Finset.prod_empty, one_mul,
    hedge, Finset.prod_singleton]
  -- All vertices are labeled (n = 0), so τ v = φ ⟨v.val, _⟩.
  set p := Quot.out s(a, b)
  have hout : s(p.1, p.2) = s(a, b) := Quot.out_eq _
  have key : (p.1 = a ∧ p.2 = b) ∨ (p.1 = b ∧ p.2 = a) := by
    have := Sym2.eq_iff.mp hout
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [left; right] <;> exact ⟨h1, h2⟩
  rcases key with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simp only [ha, hb, dif_pos (by omega : (a : ℕ) < k), dif_pos (by omega : (b : ℕ) < k)]
  · simp only [ha, hb, dif_pos (by omega : (b : ℕ) < k), dif_pos (by omega : (a : ℕ) < k)]
    exact hB _ _

/-! ### Claim 4.3: bijective equal-cardinality case -/

/-- **Lovász TR-2004-82, Claim 4.3**, §4.3, p. 9 (bijective equal-cardinality case).
If `ψ : Fin T → Fin T` is a bijection with `tupleEquiv B W id ψ`, then `ψ` is a
weighted automorphism: `tupleOrbitRel B W id ψ`.

The proof is cleaner than the edge-by-edge approach: restrict to the first `T-1`
coordinates (Claim 4.1), apply IH at level `T-1` to get an automorphism `σ`, and
observe that two bijections of `Fin T` agreeing on `T-1` elements must agree
everywhere. No twin-freeness, edge evaluation, or functional spanning needed. -/
private theorem tupleEquiv_bijective_case {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i)
    (IH_orbit : ∀ {φ ψ : Fin (T - 1) → Fin T},
      tupleEquiv B W φ ψ → tupleOrbitRel B W φ ψ)
    (ψ : Fin T → Fin T) (hψ : Function.Bijective ψ)
    (h : tupleEquiv B W id ψ) :
    tupleOrbitRel B W id ψ := by
  rcases T with _ | S
  · -- T = 0: Fin 0 is empty, trivial.
    exact ⟨1, ⟨nofun, nofun⟩, nofun⟩
  · -- T = S + 1. Restrict, apply IH, conclude by bijectivity.
    -- Step 1: Claim 4.1 gives equivalence at level S.
    have h_restrict := tupleEquiv_restrict B W hB h
    -- Step 2: IH at level S gives an automorphism σ.
    obtain ⟨σ, hσ_aut, hσ_conj⟩ := IH_orbit h_restrict
    -- Step 3: σ agrees with ψ on all castSucc values.
    have hagree : ∀ i : Fin S, ψ i.castSucc = σ i.castSucc := by
      intro i; have := hσ_conj i; simp only [restrictTuple, id] at this; exact this
    -- Step 4: Two bijections agreeing on T-1 elements agree on the last.
    have h_last : ψ (Fin.last S) = σ (Fin.last S) := by
      by_contra h_ne
      obtain ⟨j, hj⟩ := σ.surjective (ψ (Fin.last S))
      have jne : j ≠ Fin.last S := fun e => h_ne (e ▸ hj.symm)
      have hlt : (j : ℕ) < S := by
        have := j.isLt; have : j.val ≠ S := fun h => jne (Fin.ext h); omega
      rw [show j = (⟨j, hlt⟩ : Fin S).castSucc from Fin.ext rfl] at hj
      rw [← hagree ⟨j, hlt⟩] at hj
      exact absurd (hψ.1 hj.symm) (Fin.castSucc_lt_last ⟨j, hlt⟩).ne'
    -- Step 5: ψ = σ on all of Fin (S + 1), so tupleOrbitRel holds.
    refine ⟨σ, hσ_aut, fun i => ?_⟩
    by_cases hne : i = Fin.last S
    · subst hne; exact h_last
    · have hlt : (i : ℕ) < S := by
        have := i.isLt; have : i.val ≠ S := fun h => hne (Fin.ext h); omega
      rw [show i = (⟨i, hlt⟩ : Fin S).castSucc from Fin.ext rfl]
      exact hagree ⟨i, hlt⟩

/-- **Auxiliary bijectivity lemma**: under twin-free B with positive weights,
`tupleEquiv B W id χ` forces χ : Fin T → Fin T to be bijective.

**Strategy**: restrict to `Fin (T-1)` via `tupleEquiv_restrict`; apply `IH_orbit`
to obtain an automorphism τ with `χ ∘ castSucc = τ ∘ castSucc`. If
`χ(Fin.last) ≠ τ(Fin.last)`, set `v := χ(Fin.last)`, `d := τ(Fin.last)`;
derive `B d = B v` via (i) single-edge graphs + τ-automorphism (partial row
equality on `Fin T \ {d}`), (ii) the n=1 row-sum graph + τ-automorphism
reindex (row-sum equality), (iii) diagonal isolation using `hW > 0`. Row
equality contradicts `htwin`, so `χ(Fin.last) = τ(Fin.last)`, hence χ = τ is
bijective. -/
private theorem tupleEquiv_id_bijective {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (hB : ∀ i j, B i j = B j i)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j)
    (IH_orbit : ∀ {φ ψ : Fin (T - 1) → Fin T},
      tupleEquiv B W φ ψ → tupleOrbitRel B W φ ψ)
    (χ : Fin T → Fin T)
    (h : tupleEquiv B W (id : Fin T → Fin T) χ) :
    Function.Bijective χ := by
  rcases T with _ | S
  · refine ⟨fun a => Fin.elim0 a, fun b => Fin.elim0 b⟩
  · have h_restrict := tupleEquiv_restrict B W hB h
    obtain ⟨τ, hτ_aut, hτ_conj⟩ := IH_orbit h_restrict
    have hτ_eq : ∀ i : Fin S, χ i.castSucc = τ i.castSucc := by
      intro i; have := hτ_conj i
      simp only [restrictTuple, id_eq] at this; exact this
    have h_last : χ (Fin.last S) = τ (Fin.last S) := by
      by_contra h_ne
      set v := χ (Fin.last S) with hv_def
      set d := τ (Fin.last S) with hd_def
      have hvd_ne : v ≠ d := h_ne
      have single_edge_eq : ∀ (a b : Fin (S + 1)), a ≠ b →
          B a b = B (χ a) (χ b) := by
        intro a b hab
        let u : Fin (0 + (S + 1)) := ⟨a.val, by have := a.isLt; omega⟩
        let v_p : Fin (0 + (S + 1)) := ⟨b.val, by have := b.isLt; omega⟩
        have huv_ne : u ≠ v_p := by
          intro he; apply hab; apply Fin.ext
          exact (Fin.mk.injEq _ _ _ _).mp he
        let F : SimpleGraph (Fin (0 + (S + 1))) :=
          { Adj := fun x y => (x = u ∧ y = v_p) ∨ (x = v_p ∧ y = u)
            symm := fun _ _ h => h.elim
              (fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩)
              (fun ⟨h1, h2⟩ => Or.inl ⟨h2, h1⟩)
            loopless := fun _ h => by
              rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact huv_ne (h1.symm.trans h2)
              · exact huv_ne (h2.symm.trans h1) }
        haveI : DecidableRel F.Adj := fun x y =>
          if h₁ : x = u ∧ y = v_p then .isTrue (.inl h₁)
          else if h₂ : x = v_p ∧ y = u then .isTrue (.inr h₂)
          else .isFalse (fun h => h.elim (fun a => h₁ a) (fun a => h₂ a))
        have hedge : F.edgeFinset = {s(u, v_p)} := by
          apply Finset.eq_singleton_iff_unique_mem.mpr
          refine ⟨?_, ?_⟩
          · rw [SimpleGraph.mem_edgeFinset]; exact Or.inl ⟨rfl, rfl⟩
          · intro e he; rw [SimpleGraph.mem_edgeFinset] at he
            exact Sym2.ind (fun x y (hadj : F.Adj x y) => by
              rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · rw [h1, h2]
              · rw [h1, h2, Sym2.eq_swap]) e he
        have lhs := labeledEvalK_singleEdge F huv_ne hedge B hB W
          (id : Fin (S + 1) → Fin (S + 1))
        have rhs := labeledEvalK_singleEdge F huv_ne hedge B hB W χ
        have key := lhs.symm.trans ((h 0 F).trans rhs)
        have hu_eq : (⟨u.val, (by have := a.isLt; omega : u.val < S + 1)⟩ : Fin (S + 1)) = a :=
          Fin.ext rfl
        have hv_eq : (⟨v_p.val, (by have := b.isLt; omega : v_p.val < S + 1)⟩ : Fin (S + 1)) = b :=
          Fin.ext rfl
        simp only [hu_eq, hv_eq, id_eq] at key
        exact key
      have partial_row_eq : ∀ Y : Fin (S + 1), Y ≠ d → B d Y = B v Y := by
        intro Y hY
        obtain ⟨k_pre, hk_pre⟩ := τ.surjective Y
        have hk_ne_last : k_pre ≠ Fin.last S := by
          intro he; subst he; exact hY hk_pre.symm
        have hkv : k_pre.val < S := by
          have := k_pre.isLt; have : k_pre.val ≠ S := fun h => hk_ne_last (Fin.ext h); omega
        let i : Fin S := ⟨k_pre.val, hkv⟩
        have hi_eq : k_pre = i.castSucc := Fin.ext rfl
        have hτi : τ i.castSucc = Y := hi_eq ▸ hk_pre
        have hne_li : Fin.last S ≠ i.castSucc := by
          intro he; apply hk_ne_last; rw [hi_eq, ← he]
        have key : B (Fin.last S) i.castSucc = B v (χ i.castSucc) :=
          single_edge_eq (Fin.last S) i.castSucc hne_li
        rw [hτ_eq i, hτi] at key
        have hauto : B (Fin.last S) i.castSucc = B d Y := by
          have := hτ_aut.2 (Fin.last S) i.castSucc
          rw [← hd_def, hτi] at this
          exact this.symm
        rw [hauto] at key
        exact key
      have row_sum_eq : ∑ t : Fin (S + 1), W t * B d t = ∑ t : Fin (S + 1), W t * B v t := by
        have row_sum_last_v : ∑ t : Fin (S + 1), W t * B (Fin.last S) t =
            ∑ t : Fin (S + 1), W t * B v t := by
          let u' : Fin (1 + (S + 1)) := ⟨S, by omega⟩
          let v' : Fin (1 + (S + 1)) := ⟨S + 1, by omega⟩
          have hne' : u' ≠ v' := by
            intro he; have := congrArg Fin.val he; simp [u', v'] at this
          let G : SimpleGraph (Fin (1 + (S + 1))) :=
            { Adj := fun x y => (x = u' ∧ y = v') ∨ (x = v' ∧ y = u')
              symm := fun _ _ h => h.elim
                (fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩)
                (fun ⟨h1, h2⟩ => Or.inl ⟨h2, h1⟩)
              loopless := fun _ h => by
                rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · exact hne' (h1.symm.trans h2)
                · exact hne' (h2.symm.trans h1) }
          haveI : DecidableRel G.Adj := fun x y =>
            if h₁ : x = u' ∧ y = v' then .isTrue (.inl h₁)
            else if h₂ : x = v' ∧ y = u' then .isTrue (.inr h₂)
            else .isFalse (fun h => h.elim (fun a => h₁ a) (fun a => h₂ a))
          have hedge' : G.edgeFinset = {s(u', v')} := by
            apply Finset.eq_singleton_iff_unique_mem.mpr
            refine ⟨?_, ?_⟩
            · rw [SimpleGraph.mem_edgeFinset]; exact Or.inl ⟨rfl, rfl⟩
            · intro e he; rw [SimpleGraph.mem_edgeFinset] at he
              exact Sym2.ind (fun x y (hadj : G.Adj x y) => by
                rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · rw [h1, h2]
                · rw [h1, h2, Sym2.eq_swap]) e he
          have eval_θ : ∀ (θ : Fin (S + 1) → Fin (S + 1)),
              labeledEvalK (S + 1) 1 G B W θ =
                ∑ t : Fin (S + 1), W t * B (θ (Fin.last S)) t := by
            intro θ
            simp only [labeledEvalK, hedge', Finset.prod_singleton, Fin.prod_univ_one]
            rw [← (Equiv.funUnique (Fin 1) (Fin (S + 1))).symm.sum_comp]
            congr 1
            ext m
            have hσ : ((Equiv.funUnique (Fin 1) (Fin (S + 1))).symm m : Fin 1 → Fin (S + 1)) =
                fun _ => m := by
              ext k; simp [Equiv.funUnique]
            rw [hσ]
            congr 1
            set p := Quot.out (s(u', v') : Sym2 (Fin (1 + (S + 1))))
            have hout : Sym2.mk (Quot.out (s(u', v') : Sym2 (Fin (1 + (S + 1))))) = s(u', v') :=
              Quot.out_eq _
            have key : (p.1 = u' ∧ p.2 = v') ∨ (p.1 = v' ∧ p.2 = u') := by
              have := Sym2.eq_iff.mp hout
              rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [left; right] <;> exact ⟨h1, h2⟩
            have hu'_val : u'.val < S + 1 := by show S < S + 1; omega
            have hv'_val : ¬ v'.val < S + 1 := by show ¬ S + 1 < S + 1; omega
            have hu'_eq : (⟨u'.val, hu'_val⟩ : Fin (S + 1)) = Fin.last S := Fin.ext rfl
            have hv'_sub : (⟨v'.val - (S + 1), by have := v'.isLt; omega⟩ : Fin 1) = 0 :=
              Fin.ext (by show v'.val - (S + 1) = 0; omega)
            rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [h1, h2]
              simp only [dif_pos hu'_val, dif_neg hv'_val]
              rw [hu'_eq]
            · rw [h1, h2]
              simp only [dif_pos hu'_val, dif_neg hv'_val]
              rw [hu'_eq]
              exact hB m (θ (Fin.last S))
          have key := (eval_θ (id : Fin (S + 1) → Fin (S + 1))).symm.trans
            ((h 1 G).trans (eval_θ χ))
          simp only [id_eq] at key
          rw [← hv_def] at key
          exact key
        have tau_reindex : ∑ t : Fin (S + 1), W t * B (Fin.last S) t =
            ∑ t : Fin (S + 1), W t * B d t := by
          have step1 : ∀ t, W t * B (Fin.last S) t = W (τ t) * B d (τ t) := by
            intro t
            have hW_eq : W t = W (τ t) := (hτ_aut.1 t).symm
            have hB_eq : B (Fin.last S) t = B d (τ t) := by
              have := hτ_aut.2 (Fin.last S) t
              rw [← hd_def] at this
              exact this.symm
            rw [hW_eq, hB_eq]
          calc ∑ t, W t * B (Fin.last S) t
              = ∑ t, W (τ t) * B d (τ t) := Finset.sum_congr rfl (fun t _ => step1 t)
            _ = ∑ s, W s * B d s := Equiv.sum_comp τ (fun s => W s * B d s)
        rw [← tau_reindex]; exact row_sum_last_v
      have diag_eq : B d d = B v d := by
        have hWd : (0 : ℝ) < W d := hW d
        have h_sum_diff : ∑ t : Fin (S + 1), W t * (B d t - B v t) = 0 := by
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, row_sum_eq, sub_self]
        have h_split : ∀ t : Fin (S + 1), t ≠ d → W t * (B d t - B v t) = 0 := by
          intro t ht
          rw [partial_row_eq t ht]; ring
        have h_only : ∑ t : Fin (S + 1), W t * (B d t - B v t) = W d * (B d d - B v d) := by
          rw [show ∑ t, W t * (B d t - B v t) =
                W d * (B d d - B v d) +
                ∑ t ∈ Finset.univ.erase d, W t * (B d t - B v t) by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ d)]]
          rw [show (∑ t ∈ Finset.univ.erase d, W t * (B d t - B v t)) = 0 from
              Finset.sum_eq_zero (fun t ht => h_split t (Finset.mem_erase.mp ht).1)]
          ring
        rw [h_only] at h_sum_diff
        have : B d d - B v d = 0 := by
          have h_prod := h_sum_diff
          rcases mul_eq_zero.mp h_prod with h1 | h1
          · exact absurd h1 (ne_of_gt hWd)
          · exact h1
        linarith
      have hrow : B d = B v := by
        funext Y
        by_cases hY : Y = d
        · subst hY; exact diag_eq
        · exact partial_row_eq Y hY
      exact (htwin d v (Ne.symm hvd_ne)) hrow
    have hχ_eq_τ : χ = ⇑τ := by
      funext i
      by_cases hi : i = Fin.last S
      · subst hi; exact h_last
      · have hilt : i.val < S := by
          have := i.isLt; have : i.val ≠ S := fun h => hi (Fin.ext h); omega
        rw [show i = (⟨i.val, hilt⟩ : Fin S).castSucc from Fin.ext rfl]
        exact hτ_eq ⟨i.val, hilt⟩
    rw [hχ_eq_τ]
    exact τ.bijective

/-! ### Claim 4.4: surjective case -/

/-- **Lovász TR-2004-82, Claim 4.4 (core, both-surjective version)**.

Internal helper for `tupleEquiv_surjective_case`. Given BOTH `φ` and `ψ`
surjective, equivalent k-tuples are orbit-related.

**Proof structure** (Lovász §4.3, p. 9–10):
1. Build a section `r : Fin T ↪ Fin k` of `φ` via `Classical.choose`.
2. Restrict along `r` (via `tupleEquiv_restrict_along`) → `tupleEquiv B W id (ψ ∘ r)`.
3. Apply `tupleEquiv_id_bijective` to get `ψ ∘ r` bijective.
4. Apply Claim 4.3 (`tupleEquiv_bijective_case`) → automorphism `σ` with
   `ψ (r i) = σ i`.
5. For each `j : Fin k` NOT in `im(r)`: build alternative section `r'` that
   agrees with `r` except `r' (φ j) = j`. Repeat steps 2–4 to get `σ'`.
   Prove `σ = σ'` via finite-bijection uniqueness (agree on T-1 elements,
   forced on last via bijectivity), then `ψ j = σ' (φ j) = σ (φ j)`. -/
private theorem tupleEquiv_surjective_case_both {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (hB : ∀ i j, B i j = B j i)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j)
    (IH_orbit : ∀ {φ ψ : Fin (T - 1) → Fin T},
      tupleEquiv B W φ ψ → tupleOrbitRel B W φ ψ)
    {k : ℕ} (φ ψ : Fin k → Fin T)
    (hφ_surj : Function.Surjective φ)
    (hψ_surj : Function.Surjective ψ)
    (h : tupleEquiv B W φ ψ) :
    tupleOrbitRel B W φ ψ := by
  -- Sub-claim: for any section s of φ, ψ ∘ s is bijective.
  -- Delegate the bijectivity of ψ ∘ s to the standalone `tupleEquiv_id_bijective`.
  have hψ_sect_bij : ∀ (s : Fin T → Fin k), (∀ i, φ (s i) = i) →
      Function.Bijective (ψ ∘ s) := by
    intro s hs
    have hs_inj : Function.Injective s := fun a b hab => by
      have ha := hs a; rw [hab, hs b] at ha; exact ha.symm
    let sEmb : Fin T ↪ Fin k := ⟨s, hs_inj⟩
    have h_s : tupleEquiv B W (φ ∘ s) (ψ ∘ s) :=
      tupleEquiv_restrict_along B W hB sEmb h
    have hφs_id : (φ ∘ s : Fin T → Fin T) = id := funext hs
    have h_id : tupleEquiv B W (id : Fin T → Fin T) (ψ ∘ s) := hφs_id ▸ h_s
    exact tupleEquiv_id_bijective B W hW hB htwin IH_orbit (ψ ∘ s) h_id
  -- Helper: for any section s of φ, extract an automorphism σ with ψ(s i) = σ i.
  have section_to_aut : ∀ (s : Fin T → Fin k), (∀ i, φ (s i) = i) →
      ∃ σ : Equiv.Perm (Fin T),
        IsWeightedAutomorphism B W σ ∧ ∀ i, ψ (s i) = σ i := by
    intro s hs
    -- s is injective (from hs).
    have hs_inj : Function.Injective s := by
      intro a b hab
      have ha := hs a
      have hb := hs b
      rw [hab, hb] at ha
      exact ha.symm
    let sEmb : Fin T ↪ Fin k := ⟨s, hs_inj⟩
    -- Restrict along s.
    have h_s : tupleEquiv B W (φ ∘ s) (ψ ∘ s) :=
      tupleEquiv_restrict_along B W hB sEmb h
    have hφs_id : (φ ∘ s : Fin T → Fin T) = id := funext hs
    have h_id : tupleEquiv B W (id : Fin T → Fin T) (ψ ∘ s) := hφs_id ▸ h_s
    -- ψ ∘ s is bijective (from sub-claim).
    have hψs_bij : Function.Bijective (ψ ∘ s) := hψ_sect_bij s hs
    -- Apply Claim 4.3.
    obtain ⟨σ, hσ_aut, hσ_conj⟩ :=
      tupleEquiv_bijective_case B W hB IH_orbit (ψ ∘ s) hψs_bij h_id
    exact ⟨σ, hσ_aut, hσ_conj⟩
  -- Step 1: Build primary section r via Classical.choose.
  have hφ_sect : ∀ i : Fin T, ∃ j : Fin k, φ j = i := hφ_surj
  let r : Fin T → Fin k := fun i => Classical.choose (hφ_sect i)
  have hr_spec : ∀ i : Fin T, φ (r i) = i :=
    fun i => Classical.choose_spec (hφ_sect i)
  -- Step 2+3+4: Get σ from the primary section.
  obtain ⟨σ, hσ_aut, hψr_eq⟩ := section_to_aut r hr_spec
  -- Step 5: For each j : Fin k, show ψ j = σ (φ j).
  refine ⟨σ, hσ_aut, fun j => ?_⟩
  by_cases hj : ∃ i, r i = j
  · -- j ∈ im(r). Direct: ψ j = σ i = σ (φ j) since φ (r i) = i.
    obtain ⟨i, rfl⟩ := hj
    rw [hψr_eq i, hr_spec i]
  · -- j ∉ im(r). Build alternative section r' with r'(φ j) = j.
    push_neg at hj
    set i₀ : Fin T := φ j with hi₀
    let r' : Fin T → Fin k := fun i => if i = i₀ then j else r i
    have hr'_spec : ∀ i, φ (r' i) = i := by
      intro i
      by_cases hi : i = i₀
      · simp only [r', if_pos hi]; rw [hi, hi₀]
      · simp only [r', if_neg hi]; exact hr_spec i
    -- r' (i₀) = j.
    have hr'_at_i0 : r' i₀ = j := by simp only [r', if_pos rfl]
    -- r' agrees with r off i₀.
    have hr'_off_i0 : ∀ i, i ≠ i₀ → r' i = r i := fun i hi => by
      simp only [r', if_neg hi]
    -- Get σ' from r'.
    obtain ⟨σ', hσ'_aut, hψr'_eq⟩ := section_to_aut r' hr'_spec
    -- Show σ = σ'. For i ≠ i₀: both match ψ ∘ (common section at i).
    have h_agree : ∀ i, i ≠ i₀ → σ i = σ' i := by
      intro i hi
      have hstep : ψ (r i) = ψ (r' i) := by rw [hr'_off_i0 i hi]
      rw [← hψr_eq i, hstep, hψr'_eq i]
    -- σ i₀ = σ' i₀ by finite-bijection uniqueness.
    have h_at_i0 : σ i₀ = σ' i₀ := by
      by_contra hne
      obtain ⟨i, hi⟩ := σ.surjective (σ' i₀)
      have hi_ne : i ≠ i₀ := fun he => hne (he ▸ hi)
      have hσ'_eq : σ' i = σ' i₀ := by rw [← h_agree i hi_ne]; exact hi
      exact hi_ne (σ'.injective hσ'_eq)
    -- Conclude σ = σ'.
    have hσ_eq_σ' : σ = σ' := by
      apply Equiv.ext
      intro i
      by_cases hi : i = i₀
      · subst hi; exact h_at_i0
      · exact h_agree i hi
    -- Conclude ψ j = σ (φ j). After `set i₀ := φ j`, goal is `ψ j = σ i₀`.
    rw [show j = r' i₀ from hr'_at_i0.symm, hψr'_eq i₀, ← hσ_eq_σ']

/-- **Lovász TR-2004-82, Claim 4.4**, §4.3, p. 9–10 (surjective case).
If `φ, ψ : Fin k → Fin T` are equivalent and `φ` is surjective, then
`ψ = σ ∘ φ` for some `(B, W)`-automorphism `σ`, i.e., `tupleOrbitRel B W φ ψ`.

**Proof idea (one-shot reduction to Claim 4.3, NOT induction on k)**:

1. Pick a section `r : Fin T → Fin k` of `φ` (exists since `φ` surjective):
   `φ (r i) = i` for all `i : Fin T`.
2. Define reordered tuples via `r`:
   - `φ_r := φ ∘ r : Fin T → Fin T` equals the identity by construction.
   - `ψ_r := ψ ∘ r : Fin T → Fin T`.
   By Claim 4.1 (restriction via permutation): `tupleEquiv B W φ_r ψ_r`,
   i.e., `tupleEquiv B W id ψ_r`.
3. Derive that `ψ_r` is a bijection (step (b) of the paper; requires
   an injectivity argument using `Claim 4.3` applied locally).
4. By **Claim 4.3** (`tupleEquiv_bijective_case`): `ψ_r = σ ∘ id = σ` for
   some `(B, W)`-automorphism `σ`. So `ψ (r i) = σ i = σ (φ (r i))` for all `i`.
5. For each remaining `j : Fin k` not in `im(r)`: let `i₀ := φ j`. The set
   `{r i : i ≠ i₀} ∪ {j}` gives another section on which `φ` is bijective onto
   `Fin T`. By Claim 4.1 + Claim 4.3 again, `ψ` on this set matches `σ ∘ φ`,
   forcing `ψ j = σ (φ j)`.

Step (1)–(2) use `Function.surjInv` or `Classical.choice`; step (3)–(5)
require Fin reindexing infrastructure. The twin-free hypothesis is inherited
from the calling context (Lemma 2.4). -/
private theorem tupleEquiv_surjective_case {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (hB : ∀ i j, B i j = B j i)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j)
    (IH_orbit : ∀ {φ ψ : Fin (T - 1) → Fin T},
      tupleEquiv B W φ ψ → tupleOrbitRel B W φ ψ)
    {k : ℕ} (φ ψ : Fin k → Fin T)
    (hφ_surj : Function.Surjective φ)
    (h : tupleEquiv B W φ ψ) :
    tupleOrbitRel B W φ ψ := by
  -- Step 1: build a section s of φ via Classical.choose.
  have hφ_sect : ∀ i : Fin T, ∃ j : Fin k, φ j = i := hφ_surj
  let s : Fin T → Fin k := fun i => Classical.choose (hφ_sect i)
  have hs_spec : ∀ i, φ (s i) = i := fun i => Classical.choose_spec (hφ_sect i)
  -- Step 2: via the standalone auxiliary, get ψ ∘ s bijective.
  have hs_inj : Function.Injective s := fun a b hab => by
    have := hs_spec a; rw [hab, hs_spec b] at this; exact this.symm
  let sEmb : Fin T ↪ Fin k := ⟨s, hs_inj⟩
  have h_s : tupleEquiv B W (φ ∘ s) (ψ ∘ s) :=
    tupleEquiv_restrict_along B W hB sEmb h
  have hφs_id : (φ ∘ s : Fin T → Fin T) = id := funext hs_spec
  have h_id : tupleEquiv B W (id : Fin T → Fin T) (ψ ∘ s) := hφs_id ▸ h_s
  have hψs_bij : Function.Bijective (ψ ∘ s) :=
    tupleEquiv_id_bijective B W hW hB htwin IH_orbit (ψ ∘ s) h_id
  -- Step 3: deduce ψ surjective.
  have hψ_surj : Function.Surjective ψ := fun y => by
    obtain ⟨x, hx⟩ := hψs_bij.2 y; exact ⟨s x, hx⟩
  -- Step 4: delegate to the both-surjective helper.
  exact tupleEquiv_surjective_case_both B W hW hB htwin IH_orbit φ ψ hφ_surj hψ_surj h

/-- For symmetric `B`, the `B`-product at `Quot.out` of an unordered pair equals `B` at
the pair's actual endpoints. Resolves the `Quot.out` orientation ambiguity. -/
private theorem B_quot_out_eq {α : Type*} {T : ℕ} {B : Fin T → Fin T → ℝ}
    (hB : ∀ i j, B i j = B j i) (f : α → Fin T) (a b : α) :
    B (f (Quot.out s(a, b)).1) (f (Quot.out s(a, b)).2) = B (f a) (f b) := by
  set p := Quot.out s(a, b)
  have key : (p.1 = a ∧ p.2 = b) ∨ (p.1 = b ∧ p.2 = a) := by
    have := Sym2.eq_iff.mp (Quot.out_eq s(a, b))
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [left; right] <;> exact ⟨h1, h2⟩
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h1, h2, hB]

/-! ### Graph product for k-labeled evaluations (Lovász algebra A_k) -/

/-- **Graph product (disjoint union with shared labels).**
Given two k-labeled graphs `F₁` on `Fin (n₁ + K)` and `F₂` on `Fin (n₂ + K)`,
there exists a graph `F₃` on `Fin ((n₁ + n₂) + K)` whose evaluation factors:
`labeledEvalK K (n₁+n₂) F₃ B W φ = labeledEvalK K n₁ F₁ B W φ * labeledEvalK K n₂ F₂ B W φ`.

The hypothesis `hF₂` (F₂ has no label-label edges) ensures the embedded edge sets
are disjoint in F₃. For K=1 (rootedEval_glue_exists) this is automatic (no self-loops);
for K≥2 it must be assumed. Always satisfied in the application: the evaluation functions
used for `functional_span_zero` come from star/chain graphs (edges only between labels
and unlabeled, or among unlabeled), which have no label-label edges.

Generalizes `rootedEval_glue_exists` (K=1) to arbitrary K. -/
private theorem labeledEvalK_glue (K : ℕ) (n₁ n₂ : ℕ)
    (F₁ : SimpleGraph (Fin (n₁ + K))) (F₂ : SimpleGraph (Fin (n₂ + K)))
    [DecidableRel F₁.Adj] [DecidableRel F₂.Adj]
    (hF₂ : ∀ a b : Fin (n₂ + K), a.val < K → b.val < K → ¬F₂.Adj a b) :
    ∃ (F₃ : SimpleGraph (Fin ((n₁ + n₂) + K))) (_ : DecidableRel F₃.Adj),
      ∀ {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
        (W : Fin T → ℝ) (φ : Fin K → Fin T),
        labeledEvalK K (n₁ + n₂) F₃ B W φ =
          labeledEvalK K n₁ F₁ B W φ * labeledEvalK K n₂ F₂ B W φ := by
  -- Embedding: emb₂ preserves labels (v < K) and shifts unlabeled by n₁.
  let emb₂ : Fin (n₂ + K) → Fin ((n₁ + n₂) + K) :=
    fun v => if h : v.val < K then ⟨v.val, by omega⟩ else ⟨n₁ + v.val, by omega⟩
  -- Glue graph: F₁-edges via identity embedding, F₂-edges via emb₂.
  -- Use ∃ over Fin elements for F₂ to avoid bound issues when n₂ + K = 0.
  let F₃ : SimpleGraph (Fin ((n₁ + n₂) + K)) :=
    { Adj := fun u v =>
        (∃ (hu : u.val < n₁ + K) (hv : v.val < n₁ + K),
          F₁.Adj ⟨u.val, hu⟩ ⟨v.val, hv⟩) ∨
        (∃ (a b : Fin (n₂ + K)), emb₂ a = u ∧ emb₂ b = v ∧ F₂.Adj a b)
      symm := fun u v h => by
        rcases h with ⟨hu, hv, hadj⟩ | ⟨a, b, ha, hb, hadj⟩
        · left; exact ⟨hv, hu, F₁.symm hadj⟩
        · right; exact ⟨b, a, hb, ha, F₂.symm hadj⟩
      loopless := fun v h => by
        rcases h with ⟨_, _, hadj⟩ | ⟨a, b, ha, hb, hadj⟩
        · exact F₁.loopless _ hadj
        · -- emb₂ a = v = emb₂ b ⟹ a = b (emb₂ injective) ⟹ F₂.loopless contradiction
          have hab : a = b := by
            have heq : emb₂ a = emb₂ b := ha.trans hb.symm
            simp only [emb₂] at heq
            by_cases hxa : a.val < K <;> by_cases hxb : b.val < K <;>
              simp only [hxa, hxb, dif_pos, dif_neg, not_false_eq_true, Fin.mk.injEq] at heq <;>
              exact Fin.ext (by omega)
          subst hab; exact F₂.loopless _ hadj }
  haveI : DecidableRel F₃.Adj := fun u v =>
    if h₁ : ∃ (hu : u.val < n₁ + K) (hv : v.val < n₁ + K),
        F₁.Adj ⟨u.val, hu⟩ ⟨v.val, hv⟩ then .isTrue (.inl h₁)
    else if h₂ : ∃ (a b : Fin (n₂ + K)),
        emb₂ a = u ∧ emb₂ b = v ∧ F₂.Adj a b then .isTrue (.inr h₂)
    else .isFalse (fun h => h.elim (fun h => h₁ h) (fun h => h₂ h))
  refine ⟨F₃, inferInstance, ?_⟩
  -- The evaluation factorization follows the rootedEval_glue_exists pattern:
  -- (1) sum_piFinAdd_factor factors the sum over unlabeled colorings
  -- (2) Fin.prod_univ_add factors the weight product
  -- (3) Edge product factors because F₃-edges = emb₁(F₁) ⊔ emb₂(F₂), disjoint
  -- The proof follows rootedEval_glue_exists: factor the sum, then each summand.
  intro T B hB W φ
  simp only [labeledEvalK]
  -- Factor the RHS (product of sums) into a single sum via sum_piFinAdd_factor.
  rw [← sum_piFinAdd_factor
    (f := fun x : Fin n₁ → Fin T =>
      (∏ v, W (x v)) *
      ∏ e ∈ F₁.edgeFinset,
        B (if h : ↑(Quot.out e).1 < K then φ ⟨↑(Quot.out e).1, h⟩
           else x ⟨↑(Quot.out e).1 - K, by have := (Quot.out e).1.isLt; omega⟩)
          (if h : ↑(Quot.out e).2 < K then φ ⟨↑(Quot.out e).2, h⟩
           else x ⟨↑(Quot.out e).2 - K, by have := (Quot.out e).2.isLt; omega⟩))
    (g := fun x : Fin n₂ → Fin T =>
      (∏ v, W (x v)) *
      ∏ e ∈ F₂.edgeFinset,
        B (if h : ↑(Quot.out e).1 < K then φ ⟨↑(Quot.out e).1, h⟩
           else x ⟨↑(Quot.out e).1 - K, by have := (Quot.out e).1.isLt; omega⟩)
          (if h : ↑(Quot.out e).2 < K then φ ⟨↑(Quot.out e).2, h⟩
           else x ⟨↑(Quot.out e).2 - K, by have := (Quot.out e).2.isLt; omega⟩))]
  -- Now show each summand matches: LHS(σ) = f(σ∘castAdd) * g(σ∘natAdd).
  congr 1; ext σ
  -- Weight product factors via Fin.prod_univ_add:
  have h_wt : ∏ v : Fin (n₁ + n₂), W (σ v) =
      (∏ v : Fin n₁, W (σ (Fin.castAdd n₂ v))) *
      (∏ v : Fin n₂, W (σ (Fin.natAdd n₁ v))) :=
    Fin.prod_univ_add (fun v => W (σ v))
  -- Edge product factorization: F₃-edges split into F₁-edges (via identity embedding)
  -- and F₂-edges (via emb₂). The coloring τ transforms correctly under each embedding.
  -- This is the core combinatorial step (generalizes rootGlue_prod_eq to general K).
  -- Proof: decompose F₃.edgeFinset as a disjoint union, factor via Finset.prod_union,
  -- then show the B-values match via Fin.castAdd/natAdd coloring correspondence.
  suffices h_edges :
      ∏ e ∈ F₃.edgeFinset,
        B (if h : ↑(Quot.out e).1 < K then φ ⟨↑(Quot.out e).1, h⟩
           else σ ⟨↑(Quot.out e).1 - K, by have := (Quot.out e).1.isLt; omega⟩)
          (if h : ↑(Quot.out e).2 < K then φ ⟨↑(Quot.out e).2, h⟩
           else σ ⟨↑(Quot.out e).2 - K, by have := (Quot.out e).2.isLt; omega⟩) =
      (∏ e ∈ F₁.edgeFinset,
        B (if h : ↑(Quot.out e).1 < K then φ ⟨↑(Quot.out e).1, h⟩
           else σ (Fin.castAdd n₂ ⟨↑(Quot.out e).1 - K,
             by have := (Quot.out e).1.isLt; omega⟩))
          (if h : ↑(Quot.out e).2 < K then φ ⟨↑(Quot.out e).2, h⟩
           else σ (Fin.castAdd n₂ ⟨↑(Quot.out e).2 - K,
             by have := (Quot.out e).2.isLt; omega⟩))) *
      (∏ e ∈ F₂.edgeFinset,
        B (if h : ↑(Quot.out e).1 < K then φ ⟨↑(Quot.out e).1, h⟩
           else σ (Fin.natAdd n₁ ⟨↑(Quot.out e).1 - K,
             by have := (Quot.out e).1.isLt; omega⟩))
          (if h : ↑(Quot.out e).2 < K then φ ⟨↑(Quot.out e).2, h⟩
           else σ (Fin.natAdd n₁ ⟨↑(Quot.out e).2 - K,
             by have := (Quot.out e).2.isLt; omega⟩))) by
    rw [h_wt, h_edges]; ring
  -- Embeddings at the Fin level.
  let e₁ : Fin (n₁ + K) ↪ Fin ((n₁ + n₂) + K) :=
    ⟨fun v => ⟨v.val, by omega⟩, fun a b h => Fin.ext (by simpa using congr_arg Fin.val h)⟩
  have emb₂_inj : Function.Injective emb₂ := fun a b h => by
    simp only [emb₂] at h
    by_cases ha : a.val < K <;> by_cases hb : b.val < K <;>
      simp only [ha, hb, dif_pos, dif_neg, not_false_eq_true, Fin.mk.injEq] at h <;>
      exact Fin.ext (by omega)
  let e₂ : Fin (n₂ + K) ↪ Fin ((n₁ + n₂) + K) := ⟨emb₂, emb₂_inj⟩
  -- Edge-finset decomposition and disjointness.
  -- F₃.edgeFinset = emb₁(F₁.edges) ∪ emb₂(F₂.edges), disjoint by hF₂
  -- (F₂ edges involve ≥1 unlabeled vertex → emb₂ sends it to val ≥ n₁+K, outside emb₁ range).
  have hedge : F₃.edgeFinset =
      F₁.edgeFinset.map e₁.sym2Map ∪ F₂.edgeFinset.map e₂.sym2Map := by
    ext e
    simp only [Finset.mem_union, Finset.mem_map, SimpleGraph.mem_edgeFinset,
      Function.Embedding.sym2Map_apply]
    constructor
    · -- Forward: e ∈ F₃.edgeSet → F₁-image or F₂-image
      refine Sym2.ind (fun u v he => ?_) e
      rcases (show F₃.Adj u v from he) with ⟨hu, hv, hadj⟩ | ⟨a, b, ha, hb, hadj⟩
      · -- F₁-type edge: both endpoints have val < n₁+K.
        refine Or.inl ⟨s((⟨u.val, hu⟩ : Fin (n₁+K)), (⟨v.val, hv⟩ : Fin (n₁+K))),
          hadj, ?_⟩
        simp only [Sym2.map_pair_eq, e₁, Function.Embedding.coeFn_mk]
      · -- F₂-type edge: u = emb₂ a, v = emb₂ b.
        refine Or.inr ⟨s(a, b), hadj, ?_⟩
        simp only [Sym2.map_pair_eq, e₂, Function.Embedding.coeFn_mk]
        exact Sym2.eq_iff.mpr (Or.inl ⟨ha, hb⟩)
    · -- Backward: F₁-image or F₂-image → F₃.edgeSet
      rintro (⟨e₁', he₁', rfl⟩ | ⟨e₂', he₂', rfl⟩)
      · revert he₁'; refine Sym2.ind (fun a b => ?_) e₁'; intro he₁'
        simp only [Sym2.map_pair_eq, e₁, Function.Embedding.coeFn_mk]
        show F₃.Adj ⟨a.val, by have := a.isLt; omega⟩ ⟨b.val, by have := b.isLt; omega⟩
        exact Or.inl ⟨a.isLt, b.isLt, he₁'⟩
      · revert he₂'; refine Sym2.ind (fun a b => ?_) e₂'; intro he₂'
        simp only [Sym2.map_pair_eq, e₂, Function.Embedding.coeFn_mk]
        show F₃.Adj (emb₂ a) (emb₂ b)
        exact Or.inr ⟨a, b, rfl, rfl, he₂'⟩
  have hdisj : Disjoint
      (F₁.edgeFinset.map e₁.sym2Map) (F₂.edgeFinset.map e₂.sym2Map) := by
    rw [Finset.disjoint_left]; intro e he₁ he₂
    rw [Finset.mem_map] at he₁ he₂
    obtain ⟨e₁', _, rfl⟩ := he₁; obtain ⟨e₂', he₂', he₂eq⟩ := he₂
    -- Decompose both Sym2 elements.
    revert he₂' he₂eq
    refine Sym2.ind (fun a₁ b₁ => ?_) e₁'
    refine Sym2.ind (fun a₂ b₂ => ?_) e₂'
    intro he₂' he₂eq
    -- he₂' : s(a₂, b₂) ∈ F₂.edgeFinset. By hF₂, at least one has val ≥ K.
    simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq, e₁, e₂,
      Function.Embedding.coeFn_mk, Sym2.eq_iff] at he₂eq
    rw [SimpleGraph.mem_edgeFinset] at he₂'
    have hadj₂ : F₂.Adj a₂ b₂ := he₂'
    have hge : ¬a₂.val < K ∨ ¬b₂.val < K := by
      by_contra h; push_neg at h; exact hF₂ a₂ b₂ h.1 h.2 hadj₂
    -- emb₂ sends val ≥ K to Fin.val ≥ n₁+K. All e₁ vals are < n₁+K.
    have hemb_ge : ∀ v : Fin (n₂ + K), ¬v.val < K → (emb₂ v).val ≥ n₁ + K := by
      intro v hv; simp only [emb₂, dif_neg hv, Fin.val_mk]; omega
    rcases hge with ha | hb <;> {
      have hv := hemb_ge _ (by assumption)
      rcases he₂eq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> {
        have := congr_arg Fin.val h1; have := congr_arg Fin.val h2
        simp only [Fin.val_mk] at *
        have := a₁.isLt; have := b₁.isLt; omega } }
  -- Factor via Finset.prod_union + Finset.prod_map, then match B-values.
  rw [hedge, Finset.prod_union hdisj, Finset.prod_map, Finset.prod_map]
  -- Term matching: for each edge, B-values agree under the embedding.
  -- Proof: resolve Quot.out (both orientations match by hB),
  -- then τ₃∘e₁ = τ₁ and τ₃∘emb₂ = τ₂ by proof irrelevance on Fin.
  -- The dite conditions (val < K) agree because the embeddings preserve val for
  -- labels and shift by n₁ for unlabeled (with matching castAdd/natAdd on the RHS).
  -- Term matching: define coloring functions as let-bindings (definitionally equal to
  -- the inline dites from labeledEvalK), then use B_quot_out_eq to eliminate Quot.out,
  -- and proof irrelevance (Fin.ext rfl) to match the remaining Fin arguments.
  -- Define the coloring maps.
  let τ₃ : Fin ((n₁ + n₂) + K) → Fin T := fun v =>
    if h : v.val < K then φ ⟨v, h⟩ else σ ⟨v.val - K, by have := v.isLt; omega⟩
  let τ₁ : Fin (n₁ + K) → Fin T := fun v =>
    if h : v.val < K then φ ⟨v, h⟩
    else (fun j => σ (Fin.castAdd n₂ j)) ⟨v.val - K, by have := v.isLt; omega⟩
  let τ₂ : Fin (n₂ + K) → Fin T := fun v =>
    if h : v.val < K then φ ⟨v, h⟩
    else (fun j => σ (Fin.natAdd n₁ j)) ⟨v.val - K, by have := v.isLt; omega⟩
  congr 1
  · -- F₁ terms: B(τ₃(Quot.out(e₁.sym2Map e)...) = B(τ₁(Quot.out e)...)
    apply Finset.prod_congr rfl; intro e _
    refine Sym2.ind (fun a b => ?_) e
    simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq, e₁,
      Function.Embedding.coeFn_mk]
    -- Convert to named coloring functions (definitional equality).
    show B (τ₃ (Quot.out s(⟨a.val, (by omega)⟩, ⟨b.val, (by omega)⟩)).1)
           (τ₃ (Quot.out s(⟨a.val, (by omega)⟩, ⟨b.val, (by omega)⟩)).2) =
         B (τ₁ (Quot.out s(a, b)).1) (τ₁ (Quot.out s(a, b)).2)
    rw [B_quot_out_eq hB τ₃, B_quot_out_eq hB τ₁]
    -- B(τ₃ ⟨a.val,_⟩)(τ₃ ⟨b.val,_⟩) = B(τ₁ a)(τ₁ b): same dite, matching branches.
    congr 1 <;> (simp only [τ₃, τ₁]; split_ifs <;> (first | rfl | (congr 1; exact Fin.ext rfl)))
  · -- F₂ terms: B(τ₃(Quot.out(e₂.sym2Map e)...) = B(τ₂(Quot.out e)...)
    apply Finset.prod_congr rfl; intro e _
    refine Sym2.ind (fun a b => ?_) e
    simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq, e₂,
      Function.Embedding.coeFn_mk]
    show B (τ₃ (Quot.out s(emb₂ a, emb₂ b)).1) (τ₃ (Quot.out s(emb₂ a, emb₂ b)).2) =
         B (τ₂ (Quot.out s(a, b)).1) (τ₂ (Quot.out s(a, b)).2)
    rw [B_quot_out_eq hB τ₃, B_quot_out_eq hB τ₂]
    -- Now: B(τ₃(emb₂ a))(τ₃(emb₂ b)) = B(τ₂ a)(τ₂ b)
    -- emb₂ preserves val for labels (< K), shifts by n₁ for unlabeled (≥ K).
    -- The dite resolves the same way on both sides.
    congr 1
    all_goals simp only [τ₃, τ₂, emb₂]
    all_goals split_ifs
    all_goals first | rfl |
      (exfalso; simp only [Fin.val_mk] at *; omega) |
      (congr 1; apply Fin.ext; simp only [Fin.val_natAdd, Fin.val_mk]; omega)

/-- **⚠ KNOWN-FALSE — OFF THE CRITICAL PATH.**

Counterexample: `T=3`, `K=1`, `α(0)=0`, `W` uniform, `B = I` (identity on `Fin 3`).
Twin-free holds, case B hypothesis `∀ j, B(α j, s₁) = B(α j, s₂)` holds for `s₁=1, s₂=2`,
but no graph separates because the transposition `(1 2)` is a `(B, W)`-automorphism, so
every evaluation is symmetric in `1` and `2`.

**Why this does not break Lemma 2.4**: in the counterexample, `tupleEquiv` holds (both
extensions give the same evaluations) AND `tupleOrbitRel` holds (with `σ = (1 2)`). The
correct Lovász route for the non-surjective case of Lemma 2.4 constructs the automorphism
directly via Claim 4.4 + extension (see `tupleEquiv_implies_tupleOrbitRel`), bypassing any
separation argument. Case A below is still true and a useful helper, but Case B is false.

This declaration is retained only to document the failed approach. Do NOT depend on it. -/
private theorem labeledEvalK_separates {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (hB : ∀ i j, B i j = B j i)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j)
    {K : ℕ} (α : Fin K → Fin T) {s₁ s₂ : Fin T} (hs : s₁ ≠ s₂) :
    ∃ (n : ℕ) (F : SimpleGraph (Fin (n + (K + 1)))) (_ : DecidableRel F.Adj),
      labeledEvalK (K + 1) n F B W (Fin.snoc α s₁) ≠
      labeledEvalK (K + 1) n F B W (Fin.snoc α s₂) := by
  -- Case A: ∃ j ∈ Fin K with B(α j, s₁) ≠ B(α j, s₂). Single-edge separates.
  -- Case B: ∀ j, B(α j, s₁) = B(α j, s₂). Twin-free witness is outside im(α),
  --         requires graph-product algebra + functional_span_zero.
  by_cases hcase : ∃ j : Fin K, B (α j) s₁ ≠ B (α j) s₂
  · -- Case A: obtain separating j directly.
    obtain ⟨j, hjr⟩ := hcase
    -- Define the edge endpoints in Fin (0 + (K+1)).
    let u : Fin (0 + (K + 1)) := ⟨j.val, by omega⟩
    let v : Fin (0 + (K + 1)) := ⟨K, by omega⟩
    have hne : u ≠ v := by simp only [ne_eq, Fin.mk.injEq, u, v]; have := j.isLt; omega
    -- Build F inline.
    let F : SimpleGraph (Fin (0 + (K + 1))) :=
      { Adj := fun x y => (x = u ∧ y = v) ∨ (x = v ∧ y = u)
        symm := fun _ _ h => h.elim (fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩)
                                     (fun ⟨h1, h2⟩ => Or.inl ⟨h2, h1⟩)
        loopless := fun _ h => by
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hne (h1.symm.trans h2)
          · exact hne (h2.symm.trans h1) }
    haveI : DecidableRel F.Adj := fun x y =>
      if h₁ : x = u ∧ y = v then .isTrue (.inl h₁)
      else if h₂ : x = v ∧ y = u then .isTrue (.inr h₂)
      else .isFalse (fun h => h.elim (fun a => h₁ a) (fun a => h₂ a))
    have hedge : F.edgeFinset = {s(u, v)} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr; constructor
      · rw [SimpleGraph.mem_edgeFinset]; exact Or.inl ⟨rfl, rfl⟩
      · intro e he; rw [SimpleGraph.mem_edgeFinset] at he
        exact Sym2.ind (fun a b (hadj : F.Adj a b) => by
          rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]
          · rw [h1, h2, Sym2.eq_swap]) e he
    refine ⟨0, F, inferInstance, ?_⟩
    -- Evaluate: both sides equal B(α j) s_i via labeledEvalK_singleEdge.
    rw [labeledEvalK_singleEdge F hne hedge B hB W (Fin.snoc α s₁),
        labeledEvalK_singleEdge F hne hedge B hB W (Fin.snoc α s₂)]
    -- (Fin.snoc α s_i) ⟨j.val, _⟩ = α j (since j.val < K), and at ⟨K, _⟩ = s_i.
    have hu_cs : (⟨u.val, (by omega : u.val < K + 1)⟩ : Fin (K + 1)) = Fin.castSucc j := Fin.ext rfl
    have hv_la : (⟨v.val, (by omega : v.val < K + 1)⟩ : Fin (K + 1)) = Fin.last K := Fin.ext rfl
    rw [hu_cs, hv_la, Fin.snoc_castSucc, Fin.snoc_last, Fin.snoc_castSucc, Fin.snoc_last]
    -- Goal: B (α j) s₁ ≠ B (α j) s₂ — this is exactly hjr.
    exact hjr
  · -- Case B: ∀ j ∈ Fin K, B(α j, s₁) = B(α j, s₂). Twin-free ⟹ ∃ r ∉ im(α),
    -- B(r, s₁) ≠ B(r, s₂). Define d(t) := B s₁ t - B s₂ t; then d(α j) = 0 for all j,
    -- d ≢ 0, d supported on C := Fin T \ im(α).
    --
    -- **Proof structure (Lovász connection-matrix argument)**:
    --
    -- Step 1: For each multiset m : Fin K → ℕ, the evaluation of the n=1 graph with
    --   edge from last label K to unlabeled, and edges from labels in m's support to
    --   unlabeled, gives E_m(t) = ∑_s W(s) B(t, s) ∏_j B(α j, s)^{m j}.
    --   Via labeledEvalK_glue, arbitrary products of these are realizable.
    --
    -- Step 2: If ∀ n F, E_F(s₁) = E_F(s₂), then ∑_s W(s) d(s) g(s) = 0 for all g in
    --   the algebra generated by {1, B(α j, ·) : j ∈ Fin K}. Contradiction with d ≢ 0
    --   requires the algebra to SEPARATE POINTS of C = Fin T \ im(α).
    --
    -- Step 3: For twin-free B, the algebra DOES separate points — either directly via
    --   the B(α j, ·) rows on C, or via longer chain evaluations (BW·1, (BW)²·1, ...)
    --   that the graph product provides. Apply functional_span_zero with d' = W·d on
    --   C (viewed as the full support of d').
    --
    -- This is the remaining algebra-intensive step (~150-200 lines). The infrastructure
    -- (labeledEvalK_glue, functional_span_zero, B_quot_out_eq) is all in place.
    push_neg at hcase
    sorry

/-! ### Surjective-base extension uniqueness -/

/-- If the base `α : Fin k → Fin T` is surjective and `B` is twin-free, then two
equivalent extensions `Fin.snoc α a` and `Fin.snoc α b` must have `a = b`.

Proof: the single-edge evaluation between any base position `j` and the last position
gives `B(α j, a) = B(α j, b)`. Surjectivity makes this hold for all `t : Fin T`, so
`B a = B b` by symmetry, contradicting twin-freeness if `a ≠ b`. -/
private theorem tupleEquiv_ext_eq_of_surj {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j)
    {k : ℕ} {α : Fin k → Fin T}
    (hα_surj : Function.Surjective α)
    {a b : Fin T}
    (h : tupleEquiv B W (Fin.snoc α a) (Fin.snoc α b)) :
    a = b := by
  by_contra hab
  suffices hrow : B a = B b by exact absurd hrow (htwin a b hab)
  funext t; obtain ⟨j, rfl⟩ := hα_surj t
  -- For each j : Fin k, extract B(α j, a) = B(α j, b) via the single-edge evaluation.
  -- Build a graph on Fin(0 + (k+1)) with one edge between positions j and k.
  let u : Fin (0 + (k + 1)) := ⟨j, by omega⟩
  let v : Fin (0 + (k + 1)) := ⟨k, by omega⟩
  have hne : u ≠ v := by simp only [ne_eq, Fin.mk.injEq, u, v]; omega
  -- Define the single-edge graph inline.
  let F : SimpleGraph (Fin (0 + (k + 1))) :=
    { Adj := fun x y => (x = u ∧ y = v) ∨ (x = v ∧ y = u)
      symm := fun _ _ h =>
        h.elim (fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩) (fun ⟨h1, h2⟩ => Or.inl ⟨h2, h1⟩)
      loopless := fun _ h => by
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hne (h1.symm.trans h2)
        · exact hne (h2.symm.trans h1) }
  haveI : DecidableRel F.Adj := fun x y =>
    if h₁ : x = u ∧ y = v then .isTrue (.inl h₁)
    else if h₂ : x = v ∧ y = u then .isTrue (.inr h₂)
    else .isFalse (fun h => h.elim (fun a => h₁ a) (fun a => h₂ a))
  have hedge : F.edgeFinset = {s(u, v)} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr; constructor
    · rw [SimpleGraph.mem_edgeFinset]; exact Or.inl ⟨rfl, rfl⟩
    · intro e he; rw [SimpleGraph.mem_edgeFinset] at he
      exact Sym2.ind (fun a b (hadj : F.Adj a b) => by
        rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
        · rw [h1, h2, Sym2.eq_swap]) e he
  -- Separate strategy: evaluate each side independently, then combine with tupleEquiv.
  suffices hmatch : B (α j) a = B (α j) b by
    calc B a (α j) = B (α j) a := hB _ _
      _ = B (α j) b := hmatch
      _ = B b (α j) := (hB _ _).symm
  -- Each side: labeledEvalK_singleEdge gives the B-entry.
  have lhs := labeledEvalK_singleEdge F hne hedge B hB W (Fin.snoc α a)
  have rhs := labeledEvalK_singleEdge F hne hedge B hB W (Fin.snoc α b)
  -- Combine: h 0 F gives LHS-eval = RHS-eval, so the B-entries match.
  have key := lhs.symm.trans ((h 0 F).trans rhs)
  -- key : B (snoc α a ⟨u.val,_⟩) (snoc α a ⟨v.val,_⟩) = B (snoc α b ⟨u.val,_⟩) (snoc α b ⟨v.val,_⟩)
  -- By proof irrelevance, ⟨u.val,_⟩ = castSucc j and ⟨v.val,_⟩ = last k.
  -- snoc at castSucc gives α j, snoc at last gives the extension value.
  have hcast : (⟨u.val, (by omega : u.val < k + 1)⟩ : Fin (k + 1)) = j.castSucc := Fin.ext rfl
  have hlast : (⟨v.val, (by omega : v.val < k + 1)⟩ : Fin (k + 1)) = Fin.last k := Fin.ext rfl
  simp only [hcast, hlast, Fin.snoc_castSucc, Fin.snoc_last] at key
  exact key

/-! ### Lemma 2.4: tupleEquiv implies tupleOrbitRel -/

/-- **Lovász TR-2004-82, Lemma 2.4** (equivalence implies orbit relation).
For twin-free `(B, W)` with positive weights, `tupleEquiv B W φ ψ` implies
`tupleOrbitRel B W φ ψ` at every label level `k`.

Proved by induction on `k`:
- **k = 0**: trivial.
- **k + 1**: restrict to level `k` (Claim 4.1), apply IH to get automorphism `σ`,
  normalize `ψ` by `σ⁻¹` so the first `k` coordinates agree, then show the last
  coordinates must also agree (surjective-base case via `tupleEquiv_ext_eq_of_surj`),
  or find an additional automorphism (general case).

The non-surjective base case (when `restrictTuple φ` does not cover all of `Fin T`)
requires the full Lovász algebra `A_k` / graph-product multiplicative closure
argument and remains as a sorry. -/
private theorem tupleEquiv_implies_tupleOrbitRel {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (hB : ∀ i j, B i j = B j i)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j)
    {k : ℕ} {φ ψ : Fin k → Fin T}
    (h : tupleEquiv B W φ ψ) :
    tupleOrbitRel B W φ ψ := by
  induction k with
  | zero => exact ⟨1, ⟨fun _ => rfl, fun _ _ => rfl⟩, nofun⟩
  | succ k IH =>
    -- Step 1: Restrict to level k and apply IH.
    obtain ⟨σ, hσ_aut, hσ_conj⟩ := IH (tupleEquiv_restrict B W hB h)
    -- Step 2: IsWeightedAutomorphism for σ⁻¹.
    have hσs : IsWeightedAutomorphism B W σ.symm :=
      ⟨fun i => by have := (hσ_aut.1 (σ.symm i)).symm; rwa [σ.apply_symm_apply] at this,
       fun i j => by have := (hσ_aut.2 (σ.symm i) (σ.symm j)).symm
                     rwa [σ.apply_symm_apply, σ.apply_symm_apply] at this⟩
    -- Step 3: Normalize ψ by σ⁻¹ using tupleEquiv_of_tupleOrbitRel.
    have h' : tupleEquiv B W φ (σ.symm ∘ ψ) := fun n F _ =>
      (h n F).trans (tupleEquiv_of_tupleOrbitRel ⟨σ.symm, hσs, fun _ => rfl⟩ n F)
    -- Step 4: The first k coordinates now agree.
    have hbase : restrictTuple (σ.symm ∘ ψ) = restrictTuple φ := by
      funext i; simp only [restrictTuple, Function.comp]
      have := hσ_conj i; simp only [restrictTuple] at this
      rw [this, σ.symm_apply_apply]
    -- Step 5: Express as Fin.snoc extensions of the common base α.
    set α := restrictTuple φ
    have ha : φ = Fin.snoc α (φ (Fin.last k)) := by
      ext i; by_cases hi : (i : ℕ) < k
      · rw [show i = (⟨i, hi⟩ : Fin k).castSucc from Fin.ext rfl, Fin.snoc_castSucc]; rfl
      · rw [show i = Fin.last k from Fin.ext (show i.val = k by omega), Fin.snoc_last]
    have hb : σ.symm ∘ ψ = Fin.snoc α ((σ.symm ∘ ψ) (Fin.last k)) := by
      ext i; by_cases hi : (i : ℕ) < k
      · rw [show i = (⟨i, hi⟩ : Fin k).castSucc from Fin.ext rfl, Fin.snoc_castSucc, ← hbase]
        rfl
      · rw [show i = Fin.last k from Fin.ext (show i.val = k by omega), Fin.snoc_last]
    rw [ha, hb] at h'
    -- Step 6: Surjective base ⟹ last coordinates equal ⟹ orbit relation.
    by_cases hα_surj : Function.Surjective α
    · have hab := tupleEquiv_ext_eq_of_surj B W hB htwin hα_surj h'
      -- φ(last) = (σ⁻¹∘ψ)(last), so σ⁻¹∘ψ = φ, hence ψ = σ∘φ.
      exact ⟨σ, hσ_aut, fun i => by
        have : (σ.symm ∘ ψ) i = φ i := congr_fun (hb.trans (hab ▸ ha.symm)) i
        rwa [Function.comp_apply, Equiv.symm_apply_eq] at this⟩
    · -- Non-surjective base: DO NOT use labeledEvalK_separates — that theorem is FALSE
      -- (counterexample: T=3, K=1, α(0)=0, W uniform, B=I on Fin 3, s₁=1, s₂=2:
      --  twin-free + case B hypothesis hold, but no graph separates because (1 2) is
      --  a (B,W)-automorphism so every evaluation is symmetric in 1 and 2).
      -- The correct Lovász route is:
      --   1. Prove Claim 4.4 `tupleEquiv_surjective_case` first.
      --   2. Extend α to a surjective tuple using tupleEquiv_extend.
      --   3. Apply the surjective case, restrict back.
      -- This bypasses any separation theorem; it uses automorphism-orbit structure
      -- directly, matching Lovász TR-2004-82 §4.3.
      sorry

/-! ### Explicit separating motifs

**⚠ KNOWN-FALSE-FOR-SPARSE-B — retained to prevent cascade.**

The 5-motif `pairProfile` route below is refuted by the `C₅ ⊔ C₆`
counterexample (`scripts/counterexample_C5_C6.py`): that is a twin-free
positive-weight matrix where `(0, 0)` and `(5, 5)` have identical 5-motif
profiles but lie in different pair orbits under `Aut(C₅ ⊔ C₆) = D₅ × D₆`.

This section is kept intact during the Lovász pivot (Sessions A–E) only
so that the live CT-1 chain (lines 4926, 5200) and downstream uses do not
cascade. The sorries at `vertexOrbit_of_star0_tri0_eq` and
`pairOrbit_of_vertexOrbits_and_path` are **known-false** as stated
and must not be relied upon for any general claim. They will be deleted
in a future session once the Lovász-based replacement is wired in.

Five edge-free 2-labeled graphs whose evaluations form the `pairProfile` — a
5-tuple that (conjecturally, and confirmed by computation up to T=10 on
**dense** matrices, but FALSE on sparse matrices like `C₅ ⊔ C₆`)
determines pair orbits for twin-free matrices with positive weights.

- **star0** `{0,2}`: weighted row sum at label-0 vertex, `∑ W(m) B(i,m)`
- **star1** `{1,2}`: weighted row sum at label-1 vertex, `∑ W(m) B(j,m)`
- **path01** `{0,2},{1,2}`: weighted inner product, `∑ W(m) B(i,m) B(m,j)`
- **tri0** `{0,2},{0,3},{2,3}`: cubic self-interaction at label-0, depends on i only
- **tri1** `{1,2},{1,3},{2,3}`: cubic self-interaction at label-1, depends on j only
-/

/-- The star-0 evaluation: `∑ m, W m * B i m` (depends on i only). -/
private noncomputable def star0Eval {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (i j : Fin T) : ℝ := ∑ m, W m * B i m

/-- The star-1 evaluation: `∑ m, W m * B j m` (depends on j only). -/
private noncomputable def star1Eval {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (i j : Fin T) : ℝ := ∑ m, W m * B j m

/-- The path evaluation: `∑ m, W m * B i m * B m j`. -/
private noncomputable def pathEval {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (i j : Fin T) : ℝ := ∑ m, W m * B i m * B m j

/-- The triangle-0 evaluation: `∑ m₁ m₂, W m₁ * W m₂ * B i m₁ * B i m₂ * B m₁ m₂`
(depends on i only). -/
private noncomputable def tri0Eval {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (i j : Fin T) : ℝ := ∑ m₁, ∑ m₂, W m₁ * W m₂ * B i m₁ * B i m₂ * B m₁ m₂

/-- The triangle-1 evaluation: `∑ m₁ m₂, W m₁ * W m₂ * B j m₁ * B j m₂ * B m₁ m₂`
(depends on j only). -/
private noncomputable def tri1Eval {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (i j : Fin T) : ℝ := ∑ m₁, ∑ m₂, W m₁ * W m₂ * B j m₁ * B j m₂ * B m₁ m₂

/-- The pair profile: 5-tuple of motif evaluations that (conjecturally) determines
pair orbits for twin-free matrices. -/
private noncomputable def pairProfile {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (p : Fin T × Fin T) : Fin 5 → ℝ := fun k =>
  match k with
  | 0 => star0Eval B W p.1 p.2
  | 1 => star1Eval B W p.1 p.2
  | 2 => pathEval B W p.1 p.2
  | 3 => tri0Eval B W p.1 p.2
  | 4 => tri1Eval B W p.1 p.2

/-- The pair profile is orbit-invariant: automorphisms preserve all 5 motif evaluations.
Proof: each component is a sum reindexed under π using `hw`, `hc`. -/
private theorem pairProfile_eq_of_pairOrbitRel {T : ℕ}
    {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    {p q : Fin T × Fin T} (h : pairOrbitRel B W p q) :
    pairProfile B W p = pairProfile B W q := by
  obtain ⟨π, ⟨hw, hc⟩, h1, h2⟩ := h
  -- Each component is proved by: rewrite with h1/h2, then reindex sum via Equiv.sum_comp π
  have sum1 : ∀ a, ∑ m, W m * B a m = ∑ m, W m * B (π a) m :=
    fun a => (congr_arg _ (funext fun m => by rw [hw, hc])).trans (Equiv.sum_comp π _)
  have sum_path : ∀ a b, ∑ m, W m * B a m * B m b = ∑ m, W m * B (π a) m * B m (π b) :=
    fun a b => (congr_arg _ (funext fun m => by rw [hw, hc, hc])).trans (Equiv.sum_comp π _)
  have sum2 : ∀ a, ∑ m₁, ∑ m₂, W m₁ * W m₂ * B a m₁ * B a m₂ * B m₁ m₂ =
      ∑ m₁, ∑ m₂, W m₁ * W m₂ * B (π a) m₁ * B (π a) m₂ * B m₁ m₂ := fun a => by
    have htf : ∀ m₁ m₂, W (π m₁) * W (π m₂) * B (π a) (π m₁) * B (π a) (π m₂) *
        B (π m₁) (π m₂) = W m₁ * W m₂ * B a m₁ * B a m₂ * B m₁ m₂ :=
      fun m₁ m₂ => by rw [hw, hw, hc, hc, hc]
    calc ∑ m₁, ∑ m₂, W m₁ * W m₂ * B a m₁ * B a m₂ * B m₁ m₂
        = ∑ m₁, ∑ m₂, W (π m₁) * W (π m₂) * B (π a) (π m₁) * B (π a) (π m₂) *
            B (π m₁) (π m₂) := by
          congr 1; ext m₁; congr 1; ext m₂; exact (htf m₁ m₂).symm
      _ = ∑ m₁, ∑ m₂, W (π m₁) * W m₂ * B (π a) (π m₁) * B (π a) m₂ *
            B (π m₁) m₂ := by
          congr 1; ext m₁
          exact Equiv.sum_comp π
            (fun m₂ => W (π m₁) * W m₂ * B (π a) (π m₁) * B (π a) m₂ * B (π m₁) m₂)
      _ = ∑ m₁, ∑ m₂, W m₁ * W m₂ * B (π a) m₁ * B (π a) m₂ * B m₁ m₂ :=
          Equiv.sum_comp π
            (fun m₁ => ∑ m₂, W m₁ * W m₂ * B (π a) m₁ * B (π a) m₂ * B m₁ m₂)
  ext k; fin_cases k <;>
    simp only [pairProfile, star0Eval, star1Eval, pathEval, tri0Eval, tri1Eval, ← h1, ← h2]
  · exact sum1 p.1
  · exact sum1 p.2
  · exact sum_path p.1 p.2
  · exact sum2 p.1
  · exact sum2 p.2

/-! #### Three-subclaim decomposition of pair orbit determination

Rather than attacking `pairOrbitRel_of_pairProfile_eq` directly, we factor it
through three smaller lemmas:

- **(L)** `vertexOrbit_of_star0_tri0_eq`: (star0, tri0) equal ⟹ left vertex
  orbit equal.
- **(R)** `vertexOrbit_of_star1_tri1_eq`: (star1, tri1) equal ⟹ right
  vertex orbit equal.
- **(C)** `pairOrbit_of_vertexOrbits_and_path`: individually vertex-orbit-
  related endpoints + equal `pathEval` ⟹ joint pair orbit.

`pairOrbitRel_of_pairProfile_eq` is assembled from the three.

**⚠ Correctness warning**: Subclaim (L) is **FALSE** as stated, and
consequently `pairOrbitRel_of_pairProfile_eq` is also **FALSE** as stated.
Counterexample: `C₅ ⊔ C₆` (disjoint union of a 5-cycle and a 6-cycle, as a
`{0,1}`-matrix on `Fin 11` with uniform weights `W = 1/11`). This matrix is
symmetric, twin-free, has positive weights, yet every vertex has
`star0 = 2/11` and `tri0 = 0` (no triangles), so the 5-motif `pairProfile`
cannot distinguish any two vertices. In particular, pairs `(0,0)` and `(5,5)`
have identical profiles but lie in different pair orbits under
`Aut(C₅ ⊔ C₆) = D₅ × D₆`.

The earlier computational validation (`scripts/vertex_orbit_subclaim.py` and
`scripts/cross_term_coherence.py`) missed this because it tested only dense
matrices with entries in `[0.1, 0.9]`. For such dense matrices the subclaims
empirically hold, but the proof route cannot extend to the sparse case
without strengthening the hypothesis (e.g., requiring `∀ i j, 0 < B i j`) or
switching to a richer, infinite family of test graphs (see
`Graphon/LovaszScratch.lean` on the `lovasz-feasibility` branch for the
Lovász TR-2004-82 route — itself blocked by the trace-operator
infrastructure).

The subclaim sorries below are kept in place for documentation and because
removing them would cascade through CT-1 and downstream theorems, but
they should be understood as **known-false-for-sparse-twin-free-B** and not
relied upon for any general claim. A future session must either:
- Strengthen the hypotheses of the top-level conjecture, or
- Abandon the finite-motif route and build the Lovász algebra layer, or
- Find an entirely different proof approach.
-/

/-- **Subclaim (L)**: left vertex orbit determination via (star0, tri0).
For twin-free B with positive W, if two vertices `i₁, i₂ : Fin T` have equal
weighted row sum (`star0Eval`) and equal weighted cubic self-interaction
(`tri0Eval`), then there is an automorphism of `(B, W)` mapping `i₁` to `i₂`.

**Status**: partial. The trivial case `i₁ = i₂` is handled directly.
The nontrivial case `i₁ ≠ i₂` remains as a sorry, computationally validated on
random T=3..8 and structured cases up to T=10 with |Aut|=14400
(`scripts/vertex_orbit_subclaim.py`). -/
private theorem vertexOrbit_of_star0_tri0_eq {T : ℕ}
    {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    (hB : ∀ i j, B i j = B j i) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j)
    {i₁ i₂ : Fin T}
    (hstar : ∑ m, W m * B i₁ m = ∑ m, W m * B i₂ m)
    (htri : ∑ m₁, ∑ m₂, W m₁ * W m₂ * B i₁ m₁ * B i₁ m₂ * B m₁ m₂ =
            ∑ m₁, ∑ m₂, W m₁ * W m₂ * B i₂ m₁ * B i₂ m₂ * B m₁ m₂) :
    ∃ σ : Equiv.Perm (Fin T), IsWeightedAutomorphism B W σ ∧ σ i₁ = i₂ := by
  -- Trivial case: i₁ = i₂, use the identity automorphism.
  by_cases h : i₁ = i₂
  · exact ⟨1, ⟨fun _ => rfl, fun _ _ => rfl⟩, by rw [h]; rfl⟩
  -- Nontrivial case: i₁ ≠ i₂. This is the genuine frontier.
  sorry

/-- **Subclaim (R)**: right vertex orbit determination via (star1, tri1).
Mirror of `vertexOrbit_of_star0_tri0_eq` — structurally identical after
renaming `j₁, j₂` to `i₁, i₂`, so it delegates directly to (L). -/
private theorem vertexOrbit_of_star1_tri1_eq {T : ℕ}
    {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    (hB : ∀ i j, B i j = B j i) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j)
    {j₁ j₂ : Fin T}
    (hstar : ∑ m, W m * B j₁ m = ∑ m, W m * B j₂ m)
    (htri : ∑ m₁, ∑ m₂, W m₁ * W m₂ * B j₁ m₁ * B j₁ m₂ * B m₁ m₂ =
            ∑ m₁, ∑ m₂, W m₁ * W m₂ * B j₂ m₁ * B j₂ m₂ * B m₁ m₂) :
    ∃ σ : Equiv.Perm (Fin T), IsWeightedAutomorphism B W σ ∧ σ j₁ = j₂ :=
  vertexOrbit_of_star0_tri0_eq hB hW htwin hstar htri

/-- **Subclaim (C)**: cross-term coherence. Given that the two endpoints of
`(i₁, j₁)` and `(i₂, j₂)` are *individually* related by automorphisms of
`(B, W)` (not necessarily the same one), and that `pathEval` agrees on the
pairs, there exists a single automorphism that does both.

**Status**: partial. Two trivial cases are handled directly (when one of the
given automorphisms already does both). The genuinely new content is the
hard case `σ_L j₁ ≠ j₂ ∧ σ_R i₁ ≠ i₂`, which remains as a sorry.
Computationally validated on the same test corpus as (L), (R)
(`scripts/cross_term_coherence.py`). -/
private theorem pairOrbit_of_vertexOrbits_and_path {T : ℕ}
    {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    (hB : ∀ i j, B i j = B j i) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j)
    {i₁ j₁ i₂ j₂ : Fin T}
    {σ_L σ_R : Equiv.Perm (Fin T)}
    (hL : IsWeightedAutomorphism B W σ_L) (hL_eq : σ_L i₁ = i₂)
    (hR : IsWeightedAutomorphism B W σ_R) (hR_eq : σ_R j₁ = j₂)
    (hpath : ∑ m, W m * B i₁ m * B m j₁ = ∑ m, W m * B i₂ m * B m j₂) :
    pairOrbitRel B W (i₁, j₁) (i₂, j₂) := by
  -- Trivial case A: σ_L already sends j₁ to j₂, so σ_L does both maps.
  by_cases hσL_j : σ_L j₁ = j₂
  · exact ⟨σ_L, hL, hL_eq, hσL_j⟩
  -- Trivial case B: σ_R already sends i₁ to i₂, so σ_R does both maps.
  by_cases hσR_i : σ_R i₁ = i₂
  · exact ⟨σ_R, hR, hσR_i, hR_eq⟩
  -- Hard case: neither given automorphism does both. Requires constructing
  -- a new automorphism in the coset σ_L · Stab(i₁) — specifically, a τ ∈
  -- Stab(i₁) with τ j₁ = σ_L⁻¹ j₂. Existence of such τ is equivalent to
  -- showing σ_L⁻¹ j₂ and j₁ lie in the same Stab(i₁)-orbit, which is what
  -- the path equality constrains.
  sorry

/-- **Pair orbit separation**: for twin-free B with positive W, if two pairs have
the same 5-motif profile, they are in the same pair orbit.

Assembled from three subclaims:
- `vertexOrbit_of_star0_tri0_eq` gives a left-side automorphism `σ_L`.
- `vertexOrbit_of_star1_tri1_eq` gives a right-side automorphism `σ_R`.
- `pairOrbit_of_vertexOrbits_and_path` combines them with the path constraint.

**⚠ Known FALSE as stated** (see the section comment above). Counterexample:
`C₅ ⊔ C₆` on `Fin 11` with uniform weights. This is twin-free with positive W,
yet `(0, 0)` and `(5, 5)` have identical 5-motif profiles but lie in different
pair orbits. The assembly proof below routes through `vertexOrbit_of_star0_tri0_eq`,
which is itself false for this example.

The earlier computational evidence (twin-free examples up to T=10 with
|Aut(B,W)| ≤ 14400) missed this because it tested only dense matrices with
entries in `[0.1, 0.9]`. For dense enough B the 5-motif profile empirically
suffices, but no clean hypothesis capturing "dense enough" is currently known.

Also false without twin-free (separate counterexample: block-diagonal B with
twin rows). -/
private theorem pairOrbitRel_of_pairProfile_eq {T : ℕ}
    {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    (hB : ∀ i j, B i j = B j i) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j)
    {p q : Fin T × Fin T} (h : pairProfile B W p = pairProfile B W q) :
    pairOrbitRel B W p q := by
  have h_star0 : star0Eval B W p.1 p.2 = star0Eval B W q.1 q.2 := congr_fun h 0
  have h_star1 : star1Eval B W p.1 p.2 = star1Eval B W q.1 q.2 := congr_fun h 1
  have h_path  : pathEval  B W p.1 p.2 = pathEval  B W q.1 q.2 := congr_fun h 2
  have h_tri0  : tri0Eval  B W p.1 p.2 = tri0Eval  B W q.1 q.2 := congr_fun h 3
  have h_tri1  : tri1Eval  B W p.1 p.2 = tri1Eval  B W q.1 q.2 := congr_fun h 4
  simp only [star0Eval, star1Eval, pathEval, tri0Eval, tri1Eval] at h_star0 h_star1 h_path h_tri0 h_tri1
  -- (L): left vertex orbit via (star0, tri0)
  obtain ⟨σ_L, hσ_L, hσ_L_eq⟩ :=
    vertexOrbit_of_star0_tri0_eq hB hW htwin (i₁ := p.1) (i₂ := q.1) h_star0 h_tri0
  -- (R): right vertex orbit via (star1, tri1)
  obtain ⟨σ_R, hσ_R, hσ_R_eq⟩ :=
    vertexOrbit_of_star1_tri1_eq hB hW htwin (j₁ := p.2) (j₂ := q.2) h_star1 h_tri1
  -- (C): combine with pathEval
  exact pairOrbit_of_vertexOrbits_and_path hB hW htwin
    hσ_L hσ_L_eq hσ_R hσ_R_eq h_path

/-! #### Explicit motif graphs

Each of the five profile components is realized as the `labeledEval2` of a specific
edge-free 2-labeled graph. The graphs are:
- `star0Graph`: `{0,2}` on `Fin 3` (1 unlabeled vertex)
- `star1Graph`: `{1,2}` on `Fin 3`
- `pathGraph01`: `{0,2},{1,2}` on `Fin 3`
- `tri0Graph`: `{0,2},{0,3},{2,3}` on `Fin 4` (2 unlabeled vertices)
- `tri1Graph`: `{1,2},{1,3},{2,3}` on `Fin 4`
-/

/-- Star graph with center at label-0: edge `{0,2}` on `Fin 3`. -/
private def star0Graph : SimpleGraph (Fin 3) := SimpleGraph.fromEdgeSet {s(0, 2)}

/-- Star graph with center at label-1: edge `{1,2}` on `Fin 3`. -/
private def star1Graph : SimpleGraph (Fin 3) := SimpleGraph.fromEdgeSet {s(1, 2)}

/-- Path graph: edges `{0,2},{1,2}` on `Fin 3`. -/
private def pathGraph01 : SimpleGraph (Fin 3) := SimpleGraph.fromEdgeSet {s(0, 2), s(1, 2)}

/-- Triangle graph rooted at label-0: edges `{0,2},{0,3},{2,3}` on `Fin 4`. -/
private def tri0Graph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet {s(0, 2), s(0, 3), s(2, 3)}

/-- Triangle graph rooted at label-1: edges `{1,2},{1,3},{2,3}` on `Fin 4`. -/
private def tri1Graph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet {s(1, 2), s(1, 3), s(2, 3)}

private instance : DecidableRel star0Graph.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromEdgeSet _).Adj)

private instance : DecidableRel star1Graph.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromEdgeSet _).Adj)

private instance : DecidableRel pathGraph01.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromEdgeSet _).Adj)

private instance : DecidableRel tri0Graph.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromEdgeSet _).Adj)

private instance : DecidableRel tri1Graph.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromEdgeSet _).Adj)

private lemma star0Graph_edgeFree : ¬ star0Graph.Adj 0 1 := by
  simp [star0Graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq_iff]

private lemma star1Graph_edgeFree : ¬ star1Graph.Adj 0 1 := by
  simp [star1Graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq_iff]

private lemma pathGraph01_edgeFree : ¬ pathGraph01.Adj 0 1 := by
  simp [pathGraph01, SimpleGraph.fromEdgeSet_adj, Sym2.eq_iff]

private lemma tri0Graph_edgeFree : ¬ tri0Graph.Adj 0 1 := by
  simp [tri0Graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq_iff]

private lemma tri1Graph_edgeFree : ¬ tri1Graph.Adj 0 1 := by
  simp [tri1Graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq_iff]

/-- The edge finset of `star0Graph` is `{s(0, 2)}`. -/
private lemma star0Graph_edgeFinset : star0Graph.edgeFinset = {s((0 : Fin 3), 2)} := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, star0Graph, SimpleGraph.edgeSet_fromEdgeSet,
    Finset.mem_singleton, Set.mem_diff, Set.mem_singleton_iff,
    Sym2.mem_diagSet_iff_isDiag]
  refine ⟨fun ⟨he, _⟩ => he, fun he => ⟨he, ?_⟩⟩
  rw [he, Sym2.mk_isDiag_iff]
  decide

/-- `τ := Fin.cons i (Fin.cons j σ) : Fin 3 → Fin T` at index 0 is `i`. -/
private lemma finCons3_zero {T : ℕ} (i j : Fin T) (σ : Fin 1 → Fin T) :
    (Fin.cons i (Fin.cons j σ) : Fin 3 → Fin T) 0 = i := Fin.cons_zero _ _

/-- `τ := Fin.cons i (Fin.cons j σ) : Fin 3 → Fin T` at index 1 is `j`. -/
private lemma finCons3_one {T : ℕ} (i j : Fin T) (σ : Fin 1 → Fin T) :
    (Fin.cons i (Fin.cons j σ) : Fin 3 → Fin T) 1 = j := by
  rw [show (1 : Fin 3) = Fin.succ 0 from rfl, Fin.cons_succ]
  exact Fin.cons_zero _ _

/-- `τ := Fin.cons i (Fin.cons j σ) : Fin 3 → Fin T` at index 2 is `σ 0`. -/
private lemma finCons3_two {T : ℕ} (i j : Fin T) (σ : Fin 1 → Fin T) :
    (Fin.cons i (Fin.cons j σ) : Fin 3 → Fin T) 2 = σ 0 := by
  rw [show (2 : Fin 3) = Fin.succ 1 from rfl, Fin.cons_succ]
  rw [show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cons_succ]

/-- `τ := Fin.cons i (Fin.cons j σ) : Fin 4 → Fin T` at index 0 is `i`. -/
private lemma finCons4_zero {T : ℕ} (i j : Fin T) (σ : Fin 2 → Fin T) :
    (Fin.cons i (Fin.cons j σ) : Fin 4 → Fin T) 0 = i := Fin.cons_zero _ _

/-- `τ := Fin.cons i (Fin.cons j σ) : Fin 4 → Fin T` at index 1 is `j`. -/
private lemma finCons4_one {T : ℕ} (i j : Fin T) (σ : Fin 2 → Fin T) :
    (Fin.cons i (Fin.cons j σ) : Fin 4 → Fin T) 1 = j := by
  rw [show (1 : Fin 4) = Fin.succ 0 from rfl, Fin.cons_succ]
  exact Fin.cons_zero _ _

/-- `τ := Fin.cons i (Fin.cons j σ) : Fin 4 → Fin T` at index 2 is `σ 0`. -/
private lemma finCons4_two {T : ℕ} (i j : Fin T) (σ : Fin 2 → Fin T) :
    (Fin.cons i (Fin.cons j σ) : Fin 4 → Fin T) 2 = σ 0 := by
  rw [show (2 : Fin 4) = Fin.succ 1 from rfl, Fin.cons_succ]
  rw [show (1 : Fin 3) = Fin.succ 0 from rfl, Fin.cons_succ]

/-- `τ := Fin.cons i (Fin.cons j σ) : Fin 4 → Fin T` at index 3 is `σ 1`. -/
private lemma finCons4_three {T : ℕ} (i j : Fin T) (σ : Fin 2 → Fin T) :
    (Fin.cons i (Fin.cons j σ) : Fin 4 → Fin T) 3 = σ 1 := by
  rw [show (3 : Fin 4) = Fin.succ 2 from rfl, Fin.cons_succ]
  rw [show (2 : Fin 3) = Fin.succ 1 from rfl, Fin.cons_succ]

/-- `labeledEval2` of `star0Graph` equals `star0Eval`. -/
private theorem labeledEval2_star0Graph {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (i j : Fin T) :
    labeledEval2 1 star0Graph B W i j = star0Eval B W i j := by
  simp only [labeledEval2, star0Eval]
  rw [star0Graph_edgeFinset]
  simp only [Finset.prod_singleton, Fin.prod_univ_one]
  -- Reindex σ : Fin 1 → Fin T as m : Fin T
  rw [← (Equiv.funUnique (Fin 1) (Fin T)).symm.sum_comp]
  congr 1; ext m
  -- After reindex, σ = (fun _ => m) and σ 0 = m
  have hσ : ((Equiv.funUnique (Fin 1) (Fin T)).symm m : Fin 1 → Fin T) = fun _ => m := by
    ext k; simp [Equiv.funUnique]
  rw [hσ]
  -- Goal: W m * B (τ (Quot.out s(0,2)).1) (τ (Quot.out s(0,2)).2) = W m * B i m
  -- where τ = Fin.cons i (Fin.cons j (fun _ => m))
  congr 1
  set p := Quot.out s((0 : Fin 3), 2) with hp_def
  have hout : s(p.1, p.2) = s((0 : Fin 3), 2) := Quot.out_eq _
  have key : (p.1 = 0 ∧ p.2 = 2) ∨ (p.1 = 2 ∧ p.2 = 0) := by
    rw [Sym2.eq_iff] at hout
    rcases hout with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> [left; right] <;> exact ⟨h₁, h₂⟩
  rcases key with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [ha, hb, finCons3_zero, finCons3_two]
  · rw [ha, hb, finCons3_zero, finCons3_two, hB]

/-- The edge finset of `star1Graph` is `{s(1, 2)}`. -/
private lemma star1Graph_edgeFinset : star1Graph.edgeFinset = {s((1 : Fin 3), 2)} := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, star1Graph, SimpleGraph.edgeSet_fromEdgeSet,
    Finset.mem_singleton, Set.mem_diff, Set.mem_singleton_iff,
    Sym2.mem_diagSet_iff_isDiag]
  refine ⟨fun ⟨he, _⟩ => he, fun he => ⟨he, ?_⟩⟩
  rw [he, Sym2.mk_isDiag_iff]
  decide

/-- `labeledEval2` of `star1Graph` equals `star1Eval`. -/
private theorem labeledEval2_star1Graph {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (i j : Fin T) :
    labeledEval2 1 star1Graph B W i j = star1Eval B W i j := by
  simp only [labeledEval2, star1Eval]
  rw [star1Graph_edgeFinset]
  simp only [Finset.prod_singleton, Fin.prod_univ_one]
  rw [← (Equiv.funUnique (Fin 1) (Fin T)).symm.sum_comp]
  congr 1; ext m
  have hσ : ((Equiv.funUnique (Fin 1) (Fin T)).symm m : Fin 1 → Fin T) = fun _ => m := by
    ext k; simp [Equiv.funUnique]
  rw [hσ]
  congr 1
  set p := Quot.out s((1 : Fin 3), 2) with hp_def
  have hout : s(p.1, p.2) = s((1 : Fin 3), 2) := Quot.out_eq _
  have key : (p.1 = 1 ∧ p.2 = 2) ∨ (p.1 = 2 ∧ p.2 = 1) := by
    rw [Sym2.eq_iff] at hout
    rcases hout with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> [left; right] <;> exact ⟨h₁, h₂⟩
  rcases key with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [ha, hb, finCons3_one, finCons3_two]
  · rw [ha, hb, finCons3_one, finCons3_two, hB]

/-- The edge finset of `pathGraph01` is `{s(0,2), s(1,2)}`. -/
private lemma pathGraph01_edgeFinset :
    pathGraph01.edgeFinset = {s((0 : Fin 3), 2), s((1 : Fin 3), 2)} := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, pathGraph01, SimpleGraph.edgeSet_fromEdgeSet,
    Finset.mem_insert, Finset.mem_singleton, Set.mem_diff, Set.mem_insert_iff,
    Set.mem_singleton_iff, Sym2.mem_diagSet_iff_isDiag]
  refine ⟨fun ⟨he, _⟩ => he, fun he => ⟨he, ?_⟩⟩
  rcases he with he | he <;> rw [he, Sym2.mk_isDiag_iff] <;> decide

/-- `labeledEval2` of `pathGraph01` equals `pathEval`. -/
private theorem labeledEval2_pathGraph01 {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (i j : Fin T) :
    labeledEval2 1 pathGraph01 B W i j = pathEval B W i j := by
  simp only [labeledEval2, pathEval]
  rw [pathGraph01_edgeFinset]
  -- The edge set has two elements: s(0,2) and s(1,2).
  simp_rw [Finset.prod_pair (by decide : s((0 : Fin 3), 2) ≠ s((1 : Fin 3), 2)),
    Fin.prod_univ_one]
  -- Reindex σ : Fin 1 → Fin T as m : Fin T
  rw [← (Equiv.funUnique (Fin 1) (Fin T)).symm.sum_comp]
  congr 1; ext m
  have hσ : ((Equiv.funUnique (Fin 1) (Fin T)).symm m : Fin 1 → Fin T) = fun _ => m := by
    ext k; simp [Equiv.funUnique]
  rw [hσ]
  -- Goal: W m * (B τ(out s(0,2)).1 τ(out s(0,2)).2 * B τ(out s(1,2)).1 τ(out s(1,2)).2)
  --     = W m * B i m * B m j
  -- Resolve both Quot.outs
  set p0 := Quot.out s((0 : Fin 3), 2) with hp0_def
  set p1 := Quot.out s((1 : Fin 3), 2) with hp1_def
  have hout0 : s(p0.1, p0.2) = s((0 : Fin 3), 2) := Quot.out_eq _
  have hout1 : s(p1.1, p1.2) = s((1 : Fin 3), 2) := Quot.out_eq _
  have key0 : (p0.1 = 0 ∧ p0.2 = 2) ∨ (p0.1 = 2 ∧ p0.2 = 0) := by
    rw [Sym2.eq_iff] at hout0
    rcases hout0 with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> [left; right] <;> exact ⟨h₁, h₂⟩
  have key1 : (p1.1 = 1 ∧ p1.2 = 2) ∨ (p1.1 = 2 ∧ p1.2 = 1) := by
    rw [Sym2.eq_iff] at hout1
    rcases hout1 with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> [left; right] <;> exact ⟨h₁, h₂⟩
  -- Case analysis on both orientations; use hB to normalize
  let τ : Fin 3 → Fin T := Fin.cons i (Fin.cons j (fun _ => m))
  have hτ0 : τ 0 = i := finCons3_zero i j _
  have hτ1 : τ 1 = j := finCons3_one i j _
  have hτ2 : τ 2 = m := finCons3_two i j _
  have hval0 : B (τ p0.1) (τ p0.2) = B i m := by
    rcases key0 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb, hτ0, hτ2]
    · rw [ha, hb, hτ0, hτ2, hB]
  have hval1 : B (τ p1.1) (τ p1.2) = B m j := by
    rcases key1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb, hτ1, hτ2, hB]
    · rw [ha, hb, hτ1, hτ2]
  rw [hval0, hval1]
  ring

/-- The edge finset of `tri0Graph` is `{s(0,2), s(0,3), s(2,3)}`. -/
private lemma tri0Graph_edgeFinset :
    tri0Graph.edgeFinset =
      {s((0 : Fin 4), 2), s((0 : Fin 4), 3), s((2 : Fin 4), 3)} := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, tri0Graph, SimpleGraph.edgeSet_fromEdgeSet,
    Finset.mem_insert, Finset.mem_singleton, Set.mem_diff, Set.mem_insert_iff,
    Set.mem_singleton_iff, Sym2.mem_diagSet_iff_isDiag]
  refine ⟨fun ⟨he, _⟩ => he, fun he => ⟨he, ?_⟩⟩
  rcases he with he | he | he <;> rw [he, Sym2.mk_isDiag_iff] <;> decide

/-- `labeledEval2` of `tri0Graph` equals `tri0Eval`. -/
private theorem labeledEval2_tri0Graph {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (i j : Fin T) :
    labeledEval2 2 tri0Graph B W i j = tri0Eval B W i j := by
  simp only [labeledEval2, tri0Eval]
  rw [tri0Graph_edgeFinset]
  -- Expand the 3-edge product via prod_insert + prod_pair
  have hne1 : s((0 : Fin 4), 2) ∉ ({s((0 : Fin 4), 3), s((2 : Fin 4), 3)} : Finset _) := by
    decide
  have hne2 : s((0 : Fin 4), 3) ≠ s((2 : Fin 4), 3) := by decide
  simp_rw [Finset.prod_insert hne1, Finset.prod_pair hne2, Fin.prod_univ_two]
  -- Reindex σ : Fin 2 → Fin T as (m₁, m₂) via piFinTwoEquiv
  rw [← (piFinTwoEquiv (fun _ => Fin T)).symm.sum_comp, ← Fintype.sum_prod_type']
  congr 1; ext ⟨m₁, m₂⟩
  -- σ from equiv: σ 0 = m₁, σ 1 = m₂
  have hσ : ((piFinTwoEquiv fun _ => Fin T).symm (m₁, m₂) : Fin 2 → Fin T) =
      ![m₁, m₂] := by
    ext k; fin_cases k <;> simp [piFinTwoEquiv]
  rw [hσ]
  -- Now τ = Fin.cons i (Fin.cons j ![m₁, m₂])
  -- τ 0 = i, τ 1 = j, τ 2 = m₁, τ 3 = m₂
  -- Resolve all three Quot.outs
  set τ : Fin 4 → Fin T := Fin.cons i (Fin.cons j ![m₁, m₂]) with hτ_def
  have hτ0 : τ 0 = i := finCons4_zero i j _
  have hτ2 : τ 2 = m₁ := by
    show (Fin.cons i (Fin.cons j ![m₁, m₂]) : Fin 4 → Fin T) 2 = m₁
    rw [finCons4_two]; rfl
  have hτ3 : τ 3 = m₂ := by
    show (Fin.cons i (Fin.cons j ![m₁, m₂]) : Fin 4 → Fin T) 3 = m₂
    rw [finCons4_three]; rfl
  -- Edge s(0, 2)
  set p02 := Quot.out s((0 : Fin 4), 2) with hp02_def
  have hout02 : s(p02.1, p02.2) = s((0 : Fin 4), 2) := Quot.out_eq _
  have key02 : (p02.1 = 0 ∧ p02.2 = 2) ∨ (p02.1 = 2 ∧ p02.2 = 0) := by
    rw [Sym2.eq_iff] at hout02
    rcases hout02 with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> [left; right] <;> exact ⟨h₁, h₂⟩
  -- Edge s(0, 3)
  set p03 := Quot.out s((0 : Fin 4), 3) with hp03_def
  have hout03 : s(p03.1, p03.2) = s((0 : Fin 4), 3) := Quot.out_eq _
  have key03 : (p03.1 = 0 ∧ p03.2 = 3) ∨ (p03.1 = 3 ∧ p03.2 = 0) := by
    rw [Sym2.eq_iff] at hout03
    rcases hout03 with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> [left; right] <;> exact ⟨h₁, h₂⟩
  -- Edge s(2, 3)
  set p23 := Quot.out s((2 : Fin 4), 3) with hp23_def
  have hout23 : s(p23.1, p23.2) = s((2 : Fin 4), 3) := Quot.out_eq _
  have key23 : (p23.1 = 2 ∧ p23.2 = 3) ∨ (p23.1 = 3 ∧ p23.2 = 2) := by
    rw [Sym2.eq_iff] at hout23
    rcases hout23 with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> [left; right] <;> exact ⟨h₁, h₂⟩
  -- Compute each edge's B value
  have hv02 : B (τ p02.1) (τ p02.2) = B i m₁ := by
    rcases key02 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb, hτ0, hτ2]
    · rw [ha, hb, hτ0, hτ2, hB]
  have hv03 : B (τ p03.1) (τ p03.2) = B i m₂ := by
    rcases key03 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb, hτ0, hτ3]
    · rw [ha, hb, hτ0, hτ3, hB]
  have hv23 : B (τ p23.1) (τ p23.2) = B m₁ m₂ := by
    rcases key23 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb, hτ2, hτ3]
    · rw [ha, hb, hτ2, hτ3, hB]
  -- Substitute and compute
  show W ((![m₁, m₂] : Fin 2 → Fin T) 0) * W ((![m₁, m₂] : Fin 2 → Fin T) 1) *
      (B (τ p02.1) (τ p02.2) * (B (τ p03.1) (τ p03.2) * B (τ p23.1) (τ p23.2))) =
    W m₁ * W m₂ * B i m₁ * B i m₂ * B m₁ m₂
  rw [hv02, hv03, hv23]
  show W m₁ * W m₂ * (B i m₁ * (B i m₂ * B m₁ m₂)) =
    W m₁ * W m₂ * B i m₁ * B i m₂ * B m₁ m₂
  ring

/-- The edge finset of `tri1Graph` is `{s(1,2), s(1,3), s(2,3)}`. -/
private lemma tri1Graph_edgeFinset :
    tri1Graph.edgeFinset =
      {s((1 : Fin 4), 2), s((1 : Fin 4), 3), s((2 : Fin 4), 3)} := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, tri1Graph, SimpleGraph.edgeSet_fromEdgeSet,
    Finset.mem_insert, Finset.mem_singleton, Set.mem_diff, Set.mem_insert_iff,
    Set.mem_singleton_iff, Sym2.mem_diagSet_iff_isDiag]
  refine ⟨fun ⟨he, _⟩ => he, fun he => ⟨he, ?_⟩⟩
  rcases he with he | he | he <;> rw [he, Sym2.mk_isDiag_iff] <;> decide

/-- `labeledEval2` of `tri1Graph` equals `tri1Eval`. -/
private theorem labeledEval2_tri1Graph {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (i j : Fin T) :
    labeledEval2 2 tri1Graph B W i j = tri1Eval B W i j := by
  simp only [labeledEval2, tri1Eval]
  rw [tri1Graph_edgeFinset]
  have hne1 : s((1 : Fin 4), 2) ∉ ({s((1 : Fin 4), 3), s((2 : Fin 4), 3)} : Finset _) := by
    decide
  have hne2 : s((1 : Fin 4), 3) ≠ s((2 : Fin 4), 3) := by decide
  simp_rw [Finset.prod_insert hne1, Finset.prod_pair hne2, Fin.prod_univ_two]
  rw [← (piFinTwoEquiv (fun _ => Fin T)).symm.sum_comp, ← Fintype.sum_prod_type']
  congr 1; ext ⟨m₁, m₂⟩
  have hσ : ((piFinTwoEquiv fun _ => Fin T).symm (m₁, m₂) : Fin 2 → Fin T) =
      ![m₁, m₂] := by
    ext k; fin_cases k <;> simp [piFinTwoEquiv]
  rw [hσ]
  set τ : Fin 4 → Fin T := Fin.cons i (Fin.cons j ![m₁, m₂]) with hτ_def
  have hτ1 : τ 1 = j := finCons4_one i j _
  have hτ2 : τ 2 = m₁ := by
    show (Fin.cons i (Fin.cons j ![m₁, m₂]) : Fin 4 → Fin T) 2 = m₁
    rw [finCons4_two]; rfl
  have hτ3 : τ 3 = m₂ := by
    show (Fin.cons i (Fin.cons j ![m₁, m₂]) : Fin 4 → Fin T) 3 = m₂
    rw [finCons4_three]; rfl
  -- Resolve the three Quot.outs
  set p12 := Quot.out s((1 : Fin 4), 2) with hp12_def
  have hout12 : s(p12.1, p12.2) = s((1 : Fin 4), 2) := Quot.out_eq _
  have key12 : (p12.1 = 1 ∧ p12.2 = 2) ∨ (p12.1 = 2 ∧ p12.2 = 1) := by
    rw [Sym2.eq_iff] at hout12
    rcases hout12 with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> [left; right] <;> exact ⟨h₁, h₂⟩
  set p13 := Quot.out s((1 : Fin 4), 3) with hp13_def
  have hout13 : s(p13.1, p13.2) = s((1 : Fin 4), 3) := Quot.out_eq _
  have key13 : (p13.1 = 1 ∧ p13.2 = 3) ∨ (p13.1 = 3 ∧ p13.2 = 1) := by
    rw [Sym2.eq_iff] at hout13
    rcases hout13 with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> [left; right] <;> exact ⟨h₁, h₂⟩
  set p23 := Quot.out s((2 : Fin 4), 3) with hp23_def
  have hout23 : s(p23.1, p23.2) = s((2 : Fin 4), 3) := Quot.out_eq _
  have key23 : (p23.1 = 2 ∧ p23.2 = 3) ∨ (p23.1 = 3 ∧ p23.2 = 2) := by
    rw [Sym2.eq_iff] at hout23
    rcases hout23 with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> [left; right] <;> exact ⟨h₁, h₂⟩
  have hv12 : B (τ p12.1) (τ p12.2) = B j m₁ := by
    rcases key12 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb, hτ1, hτ2]
    · rw [ha, hb, hτ1, hτ2, hB]
  have hv13 : B (τ p13.1) (τ p13.2) = B j m₂ := by
    rcases key13 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb, hτ1, hτ3]
    · rw [ha, hb, hτ1, hτ3, hB]
  have hv23 : B (τ p23.1) (τ p23.2) = B m₁ m₂ := by
    rcases key23 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb, hτ2, hτ3]
    · rw [ha, hb, hτ2, hτ3, hB]
  show W ((![m₁, m₂] : Fin 2 → Fin T) 0) * W ((![m₁, m₂] : Fin 2 → Fin T) 1) *
      (B (τ p12.1) (τ p12.2) * (B (τ p13.1) (τ p13.2) * B (τ p23.1) (τ p23.2))) =
    W m₁ * W m₂ * B j m₁ * B j m₂ * B m₁ m₂
  rw [hv12, hv13, hv23]
  show W m₁ * W m₂ * (B j m₁ * (B j m₂ * B m₁ m₂)) =
    W m₁ * W m₂ * B j m₁ * B j m₂ * B m₁ m₂
  ring

/-- Each `pairProfile` component lies in `edgeFreeEvalSet` directly as a graph evaluation. -/
private theorem pairProfile_component_mem_edgeFreeEvalSet {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (k : Fin 5) :
    (fun i j => pairProfile B W (i, j) k) ∈ edgeFreeEvalSet B W := by
  fin_cases k
  · -- star0
    refine ⟨1, star0Graph, inferInstance, star0Graph_edgeFree, ?_⟩
    funext i j; exact (labeledEval2_star0Graph B hB W i j).symm
  · -- star1
    refine ⟨1, star1Graph, inferInstance, star1Graph_edgeFree, ?_⟩
    funext i j; exact (labeledEval2_star1Graph B hB W i j).symm
  · -- path
    refine ⟨1, pathGraph01, inferInstance, pathGraph01_edgeFree, ?_⟩
    funext i j; exact (labeledEval2_pathGraph01 B hB W i j).symm
  · -- tri0
    refine ⟨2, tri0Graph, inferInstance, tri0Graph_edgeFree, ?_⟩
    funext i j; exact (labeledEval2_tri0Graph B hB W i j).symm
  · -- tri1
    refine ⟨2, tri1Graph, inferInstance, tri1Graph_edgeFree, ?_⟩
    funext i j; exact (labeledEval2_tri1Graph B hB W i j).symm

/-- For twin-free B with positive W, distinct pair orbits are separated by some
edge-free evaluation. Follows from `pairOrbitRel_of_pairProfile_eq` by contrapositive:
profiles differ at some component, and each component is directly an `edgeFreeEvalSet` member. -/
private theorem pairOrbit_separated_by_edgeFreeEval {T : ℕ}
    {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    (hB : ∀ i j, B i j = B j i) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j)
    {p q : Fin T × Fin T} (h : ¬ pairOrbitRel B W p q) :
    ∃ g ∈ edgeFreeEvalSet B W, g p.1 p.2 ≠ g q.1 q.2 := by
  -- Contrapositive: ¬pairOrbit → ¬(profile p = profile q) → some component differs
  have hne : pairProfile B W p ≠ pairProfile B W q :=
    fun heq => h (pairOrbitRel_of_pairProfile_eq hB hW htwin heq)
  have ⟨k, hk⟩ : ∃ k : Fin 5, pairProfile B W p k ≠ pairProfile B W q k := by
    by_contra hall; push_neg at hall; exact hne (funext hall)
  -- Return the corresponding motif graph from edgeFreeEvalSet
  refine ⟨fun i j => pairProfile B W (i, j) k,
    pairProfile_component_mem_edgeFreeEvalSet B W hB k, ?_⟩
  -- The pair `p` has `p = (p.1, p.2)` by eta, and same for q
  change pairProfile B W (p.1, p.2) k ≠ pairProfile B W (q.1, q.2) k
  rw [show (p.1, p.2) = p from rfl, show (q.1, q.2) = q from rfl]
  exact hk

/-- **CT-1 core**: edge-free indistinguishable pairs are in the same orbit
(for twin-free matrices). Follows directly from `pairOrbit_separated_by_edgeFreeEval`. -/
private theorem edgeFreeIndist_implies_pairOrbitRel {T : ℕ}
    {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    (hB : ∀ i j, B i j = B j i) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j)
    {p q : Fin T × Fin T} (h : edgeFreeIndist B W p q) :
    pairOrbitRel B W p q := by
  by_contra h_neg
  obtain ⟨g, hg_mem, hg_ne⟩ := pairOrbit_separated_by_edgeFreeEval hB hW htwin h_neg
  exact hg_ne (h g hg_mem)

/-- Fully indistinguishable pairs are in the same orbit (for twin-free matrices).
Follows from the stronger edge-free indistinguishability theorem. -/
private theorem fullIndist_implies_pairOrbitRel {T : ℕ}
    {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    (hB : ∀ i j, B i j = B j i) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j)
    {p q : Fin T × Fin T} (h : fullIndist B W p q) :
    pairOrbitRel B W p q :=
  edgeFreeIndist_implies_pairOrbitRel hB hW htwin h.1

/-! ### Edge-free indistinguishability span characterization -/

private theorem edgeFreeIndist_trans {T : ℕ} {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    {p q r : Fin T × Fin T} (hpq : edgeFreeIndist B W p q) (hqr : edgeFreeIndist B W q r) :
    edgeFreeIndist B W p r :=
  fun f hf => (hpq f hf).trans (hqr f hf)

/-- The setoid induced by `edgeFreeIndist`. -/
private def edgeFreeIndistSetoid {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    Setoid (Fin T × Fin T) where
  r := edgeFreeIndist B W
  iseqv := ⟨edgeFreeIndist_refl B W, fun h => edgeFreeIndist_symm h,
    fun h1 h2 => edgeFreeIndist_trans h1 h2⟩

/-- The submodule of functions constant on `edgeFreeIndist`-classes. -/
private noncomputable def constantOnEdgeFreeIndist {T : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) : Submodule ℝ (Fin T → Fin T → ℝ) where
  carrier := {f | ∀ p q, edgeFreeIndist B W p q → f p.1 p.2 = f q.1 q.2}
  zero_mem' := fun _ _ _ => rfl
  add_mem' {f g} hf hg p q hpq := by
    simp only [Pi.add_apply]; rw [hf p q hpq, hg p q hpq]
  smul_mem' r f hf p q hpq := by
    simp only [Pi.smul_apply]; rw [hf p q hpq]

/-- `edgeFreeEvalSpan` is contained in `constantOnEdgeFreeIndist`. -/
private theorem edgeFreeEvalSpan_le_constantOnEdgeFreeIndist {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    edgeFreeEvalSpan B W ≤ constantOnEdgeFreeIndist B W := by
  intro f hf p q hpq
  exact edgeFreeEvalSpan_constant_on_edgeFreeIndist hf hpq

/-- Pointwise product of finitely many elements of `edgeFreeEvalSpan` is in `edgeFreeEvalSpan`. -/
private theorem prod_mem_edgeFreeEvalSpan {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Fin T → Fin T → ℝ)
    (hf : ∀ x ∈ s, f x ∈ edgeFreeEvalSpan B W) :
    (fun i j => ∏ x ∈ s, f x i j) ∈ edgeFreeEvalSpan B W := by
  induction s using Finset.induction with
  | empty =>
    have : (fun i j => ∏ x ∈ (∅ : Finset ι), f x i j) = fun _ _ => 1 := by ext; simp
    rw [this]; exact one_mem_edgeFreeEvalSpan B W
  | @insert a s' ha ih =>
    simp only [Finset.prod_insert ha]
    exact mul_mem_edgeFreeEvalSpan B W hB
      (hf a (Finset.mem_insert_self a s'))
      (ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)))

/-- A normalized affine function of a generator lies in `edgeFreeEvalSpan`. -/
private theorem lagrange_factor_mem_edgeFreeEvalSpan {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (g : Fin T → Fin T → ℝ) (hg : g ∈ edgeFreeEvalSet B W) (a b : ℝ) :
    (fun i j => (a - b)⁻¹ * (g i j - b)) ∈ edgeFreeEvalSpan B W := by
  have hg_span : g ∈ edgeFreeEvalSpan B W := Submodule.subset_span hg
  have heq : (fun i j => (a - b)⁻¹ * (g i j - b)) =
      (a - b)⁻¹ • g + (-(a - b)⁻¹ * b) • (fun _ _ => (1 : ℝ)) := by
    ext i j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [heq]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hg_span)
    (Submodule.smul_mem _ _ (one_mem_edgeFreeEvalSpan B W))

open Classical in
/-- For each `edgeFreeIndist`-class, its indicator function (1 on class, 0 elsewhere)
lies in `edgeFreeEvalSpan`, via Lagrange interpolation over quotient classes. -/
private theorem edgeFreeIndist_class_indicator_mem {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (o : Quotient (edgeFreeIndistSetoid B W)) :
    (fun i j => if Quotient.mk (edgeFreeIndistSetoid B W) (i, j) = o then 1 else 0) ∈
      edgeFreeEvalSpan B W := by
  set p₀ := o.out with hp₀_def
  have sep : ∀ q : Quotient (edgeFreeIndistSetoid B W), q ≠ o →
      ∃ g ∈ edgeFreeEvalSet B W, g p₀.1 p₀.2 ≠ g q.out.1 q.out.2 := by
    intro q hqo
    have hne : ¬ edgeFreeIndist B W p₀ q.out := by
      intro h
      apply hqo
      have heq : Quotient.mk (edgeFreeIndistSetoid B W) q.out =
                 Quotient.mk (edgeFreeIndistSetoid B W) p₀ :=
        @Quotient.sound _ (edgeFreeIndistSetoid B W) _ _ (edgeFreeIndist_symm h)
      rw [← Quotient.out_eq q, heq, hp₀_def]
      exact Quotient.out_eq o
    simp only [edgeFreeIndist] at hne
    push_neg at hne
    exact hne
  let gSep : ∀ q : Quotient (edgeFreeIndistSetoid B W), q ≠ o → Fin T → Fin T → ℝ :=
    fun q hqo => Classical.choose (sep q hqo)
  have hSep_mem : ∀ q (hqo : q ≠ o), gSep q hqo ∈ edgeFreeEvalSet B W :=
    fun q hqo => (Classical.choose_spec (sep q hqo)).1
  have hSep_ne : ∀ q (hqo : q ≠ o),
      gSep q hqo p₀.1 p₀.2 ≠ gSep q hqo q.out.1 q.out.2 :=
    fun q hqo => (Classical.choose_spec (sep q hqo)).2
  have lagFac_mem : ∀ q (hqo : q ≠ o),
      (fun i j => (gSep q hqo p₀.1 p₀.2 - gSep q hqo q.out.1 q.out.2)⁻¹ *
        (gSep q hqo i j - gSep q hqo q.out.1 q.out.2)) ∈ edgeFreeEvalSpan B W :=
    fun q hqo => lagrange_factor_mem_edgeFreeEvalSpan B W (gSep q hqo)
      (hSep_mem q hqo) _ _
  have heq : (fun i j => if Quotient.mk (edgeFreeIndistSetoid B W) (i, j) = o then 1 else 0) =
      fun i j => ∏ q ∈ Finset.univ.filter (fun q => q ≠ o),
        (if h : q ≠ o then
          (gSep q h p₀.1 p₀.2 - gSep q h q.out.1 q.out.2)⁻¹ *
          (gSep q h i j - gSep q h q.out.1 q.out.2)
        else 1) := by
    ext i j
    by_cases hor : Quotient.mk (edgeFreeIndistSetoid B W) (i, j) = o
    · simp only [hor, ite_true]
      symm
      apply Finset.prod_eq_one
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      simp only [dif_pos hq]
      have hind : edgeFreeIndist B W (i, j) p₀ :=
        @Quotient.exact _ (edgeFreeIndistSetoid B W) _ _
          (by rw [hor, hp₀_def]; exact (Quotient.out_eq o).symm)
      rw [hind (gSep q hq) (hSep_mem q hq),
          inv_mul_cancel₀ (sub_ne_zero.mpr (hSep_ne q hq))]
    · simp only [hor, ite_false]
      set r := Quotient.mk (edgeFreeIndistSetoid B W) (i, j)
      symm
      apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ r, hor⟩)
      simp only [dif_pos hor]
      have hind : edgeFreeIndist B W (i, j) r.out :=
        @Quotient.exact _ (edgeFreeIndistSetoid B W) _ _ (Quotient.out_eq r).symm
      rw [hind (gSep r hor) (hSep_mem r hor), sub_self, mul_zero]
  rw [heq]
  exact prod_mem_edgeFreeEvalSpan B W hB _ _ (fun q hq => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    simp only [dif_pos hq]
    exact lagFac_mem q hq)

open Classical in
/-- Every function constant on `edgeFreeIndist`-classes is in `edgeFreeEvalSpan`.
Decompose `f = ∑_o f(rep_o) • indicator_o` and use `edgeFreeIndist_class_indicator_mem`. -/
private theorem constantOnEdgeFreeIndist_le_edgeFreeEvalSpan {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (hB : ∀ i j, B i j = B j i) :
    constantOnEdgeFreeIndist B W ≤ edgeFreeEvalSpan B W := by
  intro f hf
  have hf_eq : ∀ p q : Fin T × Fin T, edgeFreeIndist B W p q → f p.1 p.2 = f q.1 q.2 := hf
  rw [show f = ∑ o : Quotient (edgeFreeIndistSetoid B W),
      (f o.out.1 o.out.2) •
        (fun i j : Fin T => if Quotient.mk (edgeFreeIndistSetoid B W) (i, j) = o then (1 : ℝ) else 0)
      from ?_]
  · exact Submodule.sum_mem _ fun o _ =>
      Submodule.smul_mem _ _ (edgeFreeIndist_class_indicator_mem B W hB o)
  · ext i j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (Quotient.mk (edgeFreeIndistSetoid B W) (i, j))]
    · simp only [ite_true, mul_one]
      exact hf_eq (i, j) _ (@Quotient.exact _ (edgeFreeIndistSetoid B W) _ _ (Quotient.out_eq _).symm)
    · intro q _ hne; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- `edgeFreeEvalSpan` equals the submodule of functions constant on `edgeFreeIndist`-classes. -/
private theorem edgeFreeEvalSpan_eq_constantOnEdgeFreeIndist {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (hB : ∀ i j, B i j = B j i) :
    edgeFreeEvalSpan B W = constantOnEdgeFreeIndist B W :=
  le_antisymm (edgeFreeEvalSpan_le_constantOnEdgeFreeIndist B W)
    (constantOnEdgeFreeIndist_le_edgeFreeEvalSpan B W hB)

/-! ### CT-1 assembly -/

/-- Edge-free indistinguishability equals the orbit relation for twin-free matrices.
Combines the easy direction (orbit ⟹ ef-indist) with the hard direction (ef-indist ⟹ orbit). -/
private theorem pairOrbitRel_iff_edgeFreeIndist {T : ℕ}
    {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    (hB : ∀ i j, B i j = B j i) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j)
    (p q : Fin T × Fin T) :
    pairOrbitRel B W p q ↔ edgeFreeIndist B W p q :=
  ⟨fun h => (pairOrbitRel_implies_fullIndist hB h).1,
   fun h => edgeFreeIndist_implies_pairOrbitRel hB hW htwin h⟩

open Classical in
/-- For twin-free B with positive W, each pair orbit indicator lies in `edgeFreeEvalSpan`.
Built by Lagrange interpolation using separators from `pairOrbit_separated_by_edgeFreeEval`.
Each separator g ∈ edgeFreeEvalSet is Aut(B,W)-invariant (`labeledEval2_perm_eq`), so the
Lagrange product is 1 on the target orbit and 0 on all others. -/
private theorem pairOrbit_indicator_mem_edgeFreeEvalSpan {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j)
    (o : Quotient (pairOrbitSetoid B W)) :
    pairOrbitIndicator B W o ∈ edgeFreeEvalSpan B W := by
  set p₀ := o.out with hp₀_def
  -- For each orbit q ≠ o, find a separating evaluation
  have sep : ∀ q : Quotient (pairOrbitSetoid B W), q ≠ o →
      ∃ g ∈ edgeFreeEvalSet B W, g p₀.1 p₀.2 ≠ g q.out.1 q.out.2 := by
    intro q hqo
    apply pairOrbit_separated_by_edgeFreeEval hB hW htwin
    intro h
    apply hqo
    have heq : Quotient.mk (pairOrbitSetoid B W) q.out =
               Quotient.mk (pairOrbitSetoid B W) p₀ :=
      @Quotient.sound _ (pairOrbitSetoid B W) _ _ (pairOrbitRel_symm h)
    rw [← Quotient.out_eq q, heq, hp₀_def]
    exact Quotient.out_eq o
  let gSep : ∀ q : Quotient (pairOrbitSetoid B W), q ≠ o → Fin T → Fin T → ℝ :=
    fun q hqo => Classical.choose (sep q hqo)
  have hSep_mem : ∀ q (hqo : q ≠ o), gSep q hqo ∈ edgeFreeEvalSet B W :=
    fun q hqo => (Classical.choose_spec (sep q hqo)).1
  have hSep_ne : ∀ q (hqo : q ≠ o),
      gSep q hqo p₀.1 p₀.2 ≠ gSep q hqo q.out.1 q.out.2 :=
    fun q hqo => (Classical.choose_spec (sep q hqo)).2
  -- Build Lagrange factors and prove membership
  have lagFac_mem : ∀ q (hqo : q ≠ o),
      (fun i j => (gSep q hqo p₀.1 p₀.2 - gSep q hqo q.out.1 q.out.2)⁻¹ *
        (gSep q hqo i j - gSep q hqo q.out.1 q.out.2)) ∈ edgeFreeEvalSpan B W :=
    fun q hqo => lagrange_factor_mem_edgeFreeEvalSpan B W (gSep q hqo)
      (hSep_mem q hqo) _ _
  -- The orbit indicator equals the product of all Lagrange factors.
  -- Key: each gSep is orbit-invariant (labeledEval2_perm_eq), so
  --   on orbit o: gSep(i,j) = gSep(p₀) → each factor = 1 → product = 1
  --   on orbit q₀ ≠ o: gSep_{q₀}(i,j) = gSep_{q₀}(q₀.out) → that factor = 0 → product = 0
  have heq : (fun i j => if Quotient.mk (pairOrbitSetoid B W) (i, j) = o then 1 else 0) =
      fun i j => ∏ q ∈ Finset.univ.filter (fun q => q ≠ o),
        (if h : q ≠ o then
          (gSep q h p₀.1 p₀.2 - gSep q h q.out.1 q.out.2)⁻¹ *
          (gSep q h i j - gSep q h q.out.1 q.out.2)
        else 1) := by
    ext i j
    by_cases hor : Quotient.mk (pairOrbitSetoid B W) (i, j) = o
    · simp only [hor, ite_true]
      symm
      apply Finset.prod_eq_one
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      simp only [dif_pos hq]
      -- (i,j) is in orbit o, so gSep(i,j) = gSep(p₀) by orbit-invariance
      have horb : pairOrbitRel B W (i, j) p₀ :=
        @Quotient.exact _ (pairOrbitSetoid B W) _ _
          (by rw [hor, hp₀_def]; exact (Quotient.out_eq o).symm)
      obtain ⟨π, haut, h1, h2⟩ := horb
      have hg_mem := hSep_mem q hq
      obtain ⟨n, F, inst, hF, hg_eq⟩ := hg_mem
      have hg_val : ∀ a b, gSep q hq a b = @labeledEval2 T n F inst B W a b :=
        fun a b => congr_fun (congr_fun hg_eq a) b
      rw [show gSep q hq i j = gSep q hq p₀.1 p₀.2 from by
        rw [hg_val, hg_val, ← h1, ← h2]
        exact (@labeledEval2_perm_eq T n F inst B W π haut.2 haut.1 i j).symm]
      rw [inv_mul_cancel₀ (sub_ne_zero.mpr (hSep_ne q hq))]
    · simp only [hor, ite_false]
      set r := Quotient.mk (pairOrbitSetoid B W) (i, j)
      symm
      apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ r, hor⟩)
      simp only [dif_pos hor]
      -- (i,j) is in orbit r = q₀, so gSep_{q₀}(i,j) = gSep_{q₀}(q₀.out)
      have horb : pairOrbitRel B W (i, j) r.out :=
        @Quotient.exact _ (pairOrbitSetoid B W) _ _ (Quotient.out_eq r).symm
      obtain ⟨π, haut, h1, h2⟩ := horb
      have hg_mem := hSep_mem r hor
      obtain ⟨n, F, inst, hF, hg_eq⟩ := hg_mem
      have hg_val : ∀ a b, gSep r hor a b = @labeledEval2 T n F inst B W a b :=
        fun a b => congr_fun (congr_fun hg_eq a) b
      rw [show gSep r hor i j = gSep r hor r.out.1 r.out.2 from by
        rw [hg_val, hg_val, ← h1, ← h2]
        exact (@labeledEval2_perm_eq T n F inst B W π haut.2 haut.1 i j).symm]
      rw [sub_self, mul_zero]
  rw [show pairOrbitIndicator B W o = fun i j =>
      if Quotient.mk (pairOrbitSetoid B W) (i, j) = o then 1 else 0
    from rfl]
  rw [heq]
  exact prod_mem_edgeFreeEvalSpan B W hB _ _ (fun q hq => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    simp only [dif_pos hq]
    exact lagFac_mem q hq)

/-- CT-1: the 2-labeled evaluation span equals the pair-invariant subspace
(for twin-free matrices with positive weights). -/
private theorem eval2Span_eq_pairInvariantSubspace {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j) :
    eval2Span B W = pairInvariantSubspace B W := by
  apply le_antisymm (eval2Span_le_pairInvariantSubspace B W)
  apply pairInvariantSubspace_le_of_orbitIndicators
  intro o
  exact edgeFreeEvalSpan_le_eval2Span B W
    (pairOrbit_indicator_mem_edgeFreeEvalSpan B W hB hW htwin o)

/-! ### Twin-free bijection -/

/-- Twin-free bijection: if two twin-free symmetric [0,1]-matrices with positive weights
have equal weighted hom sums for all graphs, there is a permutation matching weights and
entries. This is Lovász [2012] Theorem 5.30 for the twin-free case.

**Status**: Sorry. Needs an orbit-breaking proof ingredient.

**Why the previous approach failed**: The deleted `eval_algebra_span_full` claimed that
1-labeled rootedEval functions span ℝ^T for any twin-free matrix. This is false:
rootedEval is invariant under (B,W)-automorphisms (reindex σ ↦ π∘σ in the sum).
Counterexample: B(i,j) = if i=j then 3/10 else 7/10 on Fin 2 with W=(1/2,1/2).
The swap is a (B,W)-automorphism, so rootedEval(F)(0) = rootedEval(F)(1) for all F,
and f=(1,-1) is a non-zero element of the W-orthogonal complement.

More generally, both 1-labeled rootedEval and the Phase 1 profile machinery (wDeg,
rowProfile, joint classes) produce automorphism-invariant quantities and cannot
separate vertices in the same (B,W)-orbit. The collapsed matrix from row collapse
can have non-trivial automorphisms, so this bug is reachable at the call site.

**Correct proof direction**: Lovász [2012] §5.2 proves the result via the connection
matrix M(W,k) for k-labeled graphs. The k=1 case fails when Aut(B,W) is non-trivial,
but k≥2 can probe individual entries B(i,j) by fixing both endpoints. The exact
formalization requires careful design. The existing `rootedEval_rootAttach` remains
available for the entry-matching step once a correct transfer permutation is
established by orbit-breaking means.

**Sorry traces to**: algebraic graph theory (connection matrix rank, Lovász §5.2) -/
private theorem twinfree_bijection_of_weightedHomSum_eq {T T' : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (B' : Fin T' → Fin T' → ℝ) (W' : Fin T' → ℝ)
    (hB_symm : ∀ i j, B i j = B j i) (hB'_symm : ∀ i j, B' i j = B' j i)
    (hB_mem : ∀ i j, B i j ∈ Set.Icc 0 1) (hB'_mem : ∀ i j, B' i j ∈ Set.Icc 0 1)
    (hW_pos : ∀ i, 0 < W i) (hW'_pos : ∀ i, 0 < W' i)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j)
    (htwin' : ∀ i j : Fin T', i ≠ j → B' i ≠ B' j)
    (h_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      weightedHomSum n F B W = weightedHomSum n F B' W') :
    ∃ π : Fin T ≃ Fin T',
      (∀ i, W i = W' (π i)) ∧
      (∀ i j, B i j = B' (π i) (π j)) := by
  sorry

private theorem matrix_quotient_of_weightedHomSum_eq_pos {k : ℕ}
    (c c' : Fin k → Fin k → ℝ)
    (hc_symm : ∀ i j, c i j = c j i) (hc'_symm : ∀ i j, c' i j = c' j i)
    (hc_mem : ∀ i j, c i j ∈ Set.Icc 0 1) (hc'_mem : ∀ i j, c' i j ∈ Set.Icc 0 1)
    (w : Fin k → ℝ) (hw_pos : ∀ i, 0 < w i)
    (h_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      weightedHomSum n F c w = weightedHomSum n F c' w)
    (hk : 0 < k) :
    ∃ (T : ℕ) (type_c : Fin k → Fin T) (type_c' : Fin k → Fin T),
      (∀ i₁ i₂ j₁ j₂, type_c i₁ = type_c i₂ → type_c j₁ = type_c j₂ →
        c i₁ j₁ = c i₂ j₂) ∧
      (∀ i₁ i₂ j₁ j₂, type_c' i₁ = type_c' i₂ → type_c' j₁ = type_c' j₂ →
        c' i₁ j₁ = c' i₂ j₂) ∧
      (∀ i j i' j', type_c i = type_c' i' → type_c j = type_c' j' →
        c i j = c' i' j') ∧
      (∀ t : Fin T,
        ∑ i ∈ Finset.univ.filter (fun i => type_c i = t), w i =
        ∑ i ∈ Finset.univ.filter (fun i => type_c' i = t), w i) := by
  -- Base case: k = 1
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rcases k with _ | k
  · -- k = 1: unique entry determined by edge test
    have h_ceq := k1_entry_eq hc_symm hc'_symm w hw_pos h_eq
    have hfin1 : ∀ (i : Fin 1), i = 0 := fun i => Fin.ext (by omega)
    exact ⟨1, fun _ => 0, fun _ => 0,
      fun i₁ i₂ j₁ j₂ _ _ => by rw [hfin1 i₁, hfin1 i₂, hfin1 j₁, hfin1 j₂],
      fun i₁ i₂ j₁ j₂ _ _ => by rw [hfin1 i₁, hfin1 i₂, hfin1 j₁, hfin1 j₂],
      fun i j i' j' _ _ => by rw [hfin1 i, hfin1 j, hfin1 i', hfin1 j']; exact h_ceq,
      fun _ => rfl⟩
  -- General case: k ≥ 2
  -- Row collapse decomposes the problem into a twin-free sub-problem.
  -- Collapse both c and c' by row equivalence classes, transfer hom sums,
  -- apply the twin-free bijection, then compose with rowClassMap.
  have h_coll : ∀ (n₀ : ℕ) (F₀ : SimpleGraph (Fin n₀)) [DecidableRel F₀.Adj],
      weightedHomSum n₀ F₀ (collapsedMatrix c) (collapsedWeights c w) =
      weightedHomSum n₀ F₀ (collapsedMatrix c') (collapsedWeights c' w) := by
    intro n₀ F₀ _
    rw [← weightedHomSum_collapse c hc_symm, ← weightedHomSum_collapse c' hc'_symm]
    exact h_eq n₀ F₀
  obtain ⟨π, hπ_w, hπ_B⟩ := twinfree_bijection_of_weightedHomSum_eq
    (collapsedMatrix c) (collapsedWeights c w)
    (collapsedMatrix c') (collapsedWeights c' w)
    (collapsedMatrix_symm c hc_symm) (collapsedMatrix_symm c' hc'_symm)
    (collapsedMatrix_mem c hc_mem) (collapsedMatrix_mem c' hc'_mem)
    (collapsedWeights_pos c w hw_pos) (collapsedWeights_pos c' w hw_pos)
    (collapsed_twin_free c hc_symm) (collapsed_twin_free c' hc'_symm)
    h_coll
  refine ⟨numRowClasses c, rowClassMap c, fun i => π.symm (rowClassMap c' i),
    -- Property 1: c is block-constant on type_c classes
    fun i₁ i₂ j₁ j₂ hi hj =>
      block_const_of_row_eq c hc_symm
        ((rowClassMap_eq_iff c i₁ i₂).mp hi) ((rowClassMap_eq_iff c j₁ j₂).mp hj),
    -- Property 2: c' is block-constant on type_c' classes
    fun i₁ i₂ j₁ j₂ hi hj =>
      block_const_of_row_eq c' hc'_symm
        ((rowClassMap_eq_iff c' i₁ i₂).mp (π.symm.injective hi))
        ((rowClassMap_eq_iff c' j₁ j₂).mp (π.symm.injective hj)),
    -- Property 3: cross-matrix matching
    fun i j i' j' hi hj => ?_, fun t => ?_⟩
  -- Property 3: c i j = c' i' j' when types match
  · have hi' : π (rowClassMap c i) = rowClassMap c' i' := by rwa [Equiv.eq_symm_apply] at hi
    have hj' : π (rowClassMap c j) = rowClassMap c' j' := by rwa [Equiv.eq_symm_apply] at hj
    calc c i j
        = collapsedMatrix c (rowClassMap c i) (rowClassMap c j) :=
          block_const_of_row_eq c hc_symm
            (row_of_rep_classMap c i).symm (row_of_rep_classMap c j).symm
      _ = collapsedMatrix c' (π (rowClassMap c i)) (π (rowClassMap c j)) := hπ_B _ _
      _ = collapsedMatrix c' (rowClassMap c' i') (rowClassMap c' j') := by rw [hi', hj']
      _ = c' i' j' :=
          (block_const_of_row_eq c' hc'_symm
            (row_of_rep_classMap c' i').symm (row_of_rep_classMap c' j').symm).symm
  -- Property 4: weight sums per type class match
  · have h_wt := hπ_w t
    simp only [collapsedWeights] at h_wt ⊢
    rw [show Finset.univ.filter (fun i => π.symm (rowClassMap c' i) = t) =
        Finset.univ.filter (fun i => rowClassMap c' i = π t) from by
      ext i; simp [Equiv.symm_apply_eq]]
    exact h_wt

/-! ### Main theorem -/

/-- **Algebraic determination for finite matrices (quotient form).**

If two symmetric matrices with entries in [0,1] have equal weighted homomorphism
sums for ALL graphs on ALL vertex counts, then they have the same "type quotient":
there exist type classification functions such that both matrices are block-constant
on type classes, the block matrices agree, and the total weight per type class matches.

This is the correct formulation of Lovász [2012] Theorem 5.30 for the weighted setting.
The permutation formulation (`∃ π, c i j = c' (π i) (π j) ∧ w i = w (π i)`) is false
when type classes have different cardinalities but equal total weights. The quotient
formulation is what's needed for the measure-theoretic inverse counting lemma, where
atomless measures allow mass redistribution within type classes.

## Proof outline (Lovász [2012], Section 5.2)

1. **Star graph moment extraction**: Testing with K_{1,m} yields degree moments.

2. **Vandermonde argument** (`eq_zero_of_weighted_powers_eq_zero`): From the
   moment equalities, deduce class weight matching for degree classes.

3. **Caterpillar/multi-profile tests**: Extract the full row profile via double
   star graphs and multi-profile stars. Hierarchical Vandermonde shows that the
   matrix is block-constant on type classes (defined by degree + all row profiles).

4. **Cross-matrix matching**: Show that the block matrices agree between c and c'
   by comparing conditional moments within each type class. -/
theorem matrix_quotient_of_weightedHomSum_eq {k : ℕ}
    (c c' : Fin k → Fin k → ℝ)
    (hc_symm : ∀ i j, c i j = c j i) (hc'_symm : ∀ i j, c' i j = c' j i)
    (hc_mem : ∀ i j, c i j ∈ Set.Icc 0 1) (hc'_mem : ∀ i j, c' i j ∈ Set.Icc 0 1)
    (w : Fin k → ℝ) (hw_pos : ∀ i, 0 < w i)
    (h_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      weightedHomSum n F c w = weightedHomSum n F c' w) :
    ∃ (T : ℕ) (type_c : Fin k → Fin T) (type_c' : Fin k → Fin T),
      (∀ i₁ i₂ j₁ j₂, type_c i₁ = type_c i₂ → type_c j₁ = type_c j₂ →
        c i₁ j₁ = c i₂ j₂) ∧
      (∀ i₁ i₂ j₁ j₂, type_c' i₁ = type_c' i₂ → type_c' j₁ = type_c' j₂ →
        c' i₁ j₁ = c' i₂ j₂) ∧
      (∀ i j i' j', type_c i = type_c' i' → type_c j = type_c' j' →
        c i j = c' i' j') ∧
      (∀ t : Fin T,
        ∑ i ∈ Finset.univ.filter (fun i => type_c i = t), w i =
        ∑ i ∈ Finset.univ.filter (fun i => type_c' i = t), w i) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨0, nofun, nofun, nofun, nofun, nofun, nofun⟩
  · exact matrix_quotient_of_weightedHomSum_eq_pos c c' hc_symm hc'_symm
      hc_mem hc'_mem w hw_pos h_eq hk

end Graphon
