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

* `Graphon.matrix_perm_of_weightedHomSum_eq` - Equal weighted hom sums imply
  permutation equivalence (Lovász [2012] Theorem 5.30)

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

private theorem matrix_perm_of_weightedHomSum_eq_pos {k : ℕ}
    (c c' : Fin k → Fin k → ℝ)
    (hc_symm : ∀ i j, c i j = c j i) (hc'_symm : ∀ i j, c' i j = c' j i)
    (hc_mem : ∀ i j, c i j ∈ Set.Icc 0 1) (hc'_mem : ∀ i j, c' i j ∈ Set.Icc 0 1)
    (w : Fin k → ℝ) (hw_pos : ∀ i, 0 < w i)
    (h_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      weightedHomSum n F c w = weightedHomSum n F c' w)
    (hk : 0 < k) :
    ∃ π : Equiv.Perm (Fin k),
      (∀ i j, c i j = c' (π i) (π j)) ∧ (∀ i, w i = w (π i)) := by
  sorry

/-! ### Main theorem -/

/-- **Algebraic determination for finite matrices.**

If two symmetric matrices with entries in [0,1] have equal weighted homomorphism
sums for ALL graphs on ALL vertex counts, then they are related by a permutation
of indices (that also preserves weights).

This is Lovász [2012] Theorem 5.30 restricted to the weighted setting.

## Proof outline (Lovász [2012], Section 5.2)

The proof proceeds by building a permutation that simultaneously matches
matrix entries and weights, using an induction on the structure of the
"row profile" of the matrix.

1. **Star graph moment extraction**: Testing with K_{1,m} yields the moment
   identity `∑ᵢ wᵢ · dᵢᵐ = ∑ᵢ wᵢ · d'ᵢᵐ` where dᵢ = ∑ⱼ wⱼ c(i,j).

2. **Vandermonde argument** (`eq_zero_of_weighted_powers_eq_zero`): From the
   moment equalities, deduce that for each degree value v, the total weight
   of indices with that degree is the same for c and c'.

3. **Caterpillar graph tests**: Testing with caterpillar graphs (paths with
   pendant edges) extracts the row profiles `rowProfile c w i m`. Vandermonde
   applied to these shows that the multiset of (weight, row-type) pairs is
   the same for c and c'.

4. **Inductive row matching**: Build π by matching rows within each type
   class. For rows of the same type, the entries toward other type classes
   are identical, so matching reduces to a smaller instance of the same
   problem. Terminate by `eq_zero_of_weighted_powers_eq_zero` at the base. -/
theorem matrix_perm_of_weightedHomSum_eq {k : ℕ}
    (c c' : Fin k → Fin k → ℝ)
    (hc_symm : ∀ i j, c i j = c j i) (hc'_symm : ∀ i j, c' i j = c' j i)
    (hc_mem : ∀ i j, c i j ∈ Set.Icc 0 1) (hc'_mem : ∀ i j, c' i j ∈ Set.Icc 0 1)
    (w : Fin k → ℝ) (hw_pos : ∀ i, 0 < w i)
    (h_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      weightedHomSum n F c w = weightedHomSum n F c' w) :
    ∃ π : Equiv.Perm (Fin k),
      (∀ i j, c i j = c' (π i) (π j)) ∧ (∀ i, w i = w (π i)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨Equiv.refl _, nofun, nofun⟩
  · -- k > 0: Lovász [2012] Theorem 5.30
    -- The full proof uses ALL graph homomorphism tests to build a
    -- permutation π simultaneously matching entries and weights.
    -- Steps: star graph moments → Vandermonde → degree class matching →
    -- caterpillar tests → row profile matching → inductive assembly.
    exact matrix_perm_of_weightedHomSum_eq_pos c c' hc_symm hc'_symm hc_mem hc'_mem w hw_pos h_eq hk

end Graphon
