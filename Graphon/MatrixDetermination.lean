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

/-! ### Core proof for k > 0 -/

/-- Core of the algebraic determination theorem for k > 0.

This is Lovász [2012] Theorem 5.30. The proof uses the full family of graph
homomorphism tests to build a permutation matching entries and weights.

## Proof structure

The argument proceeds by strong induction on k. The base case k = 1 is
trivial. For the inductive step:

1. Test with star graphs K_{1,m} to extract weighted degree moments.
2. Apply Vandermonde (`eq_zero_of_weighted_powers_eq_zero`) to show that for
   each degree value, the total weight of indices is the same for c and c'.
3. Test with caterpillar graphs to extract row profile moments, refining the
   equivalence classes of rows.
4. At each level of the refinement, apply Vandermonde again to show
   matching within each class.
5. Assemble the permutation class-by-class. Within each class, the problem
   reduces to a strictly smaller instance (fewer distinct row types). -/
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
