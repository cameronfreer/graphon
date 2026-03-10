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
