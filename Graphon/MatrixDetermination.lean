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
