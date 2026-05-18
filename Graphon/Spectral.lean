/-
Spectral closing of #77 (`vertex_orbit_of_closed_walks_eq`).

Per 2026-05-18 design plan: provide a finite-dimensional spectral
section for the weighted adjacency operator, isolated from
`Graphon/Lovasz.lean` so that `Real.sqrt` and spectral simp lemmas
don't pollute the rest of the codebase.

**Scope**:
- Define the symmetric operator `S := D^{1/2} B D^{1/2}`.
- Prove symmetry.
- (Later) bridge `closedWalkProfile` to diagonal of `S^m`.
- (Later) finite spectral decomposition + orbit upgrade under twin-free.

This file's PUBLIC API target is one named theorem:
`vertex_orbit_of_closed_walks_eq` (Lovász §3 K=1 spectral closing).
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Graphon.Lovasz

namespace Graphon.Spectral

open Graphon.Lovasz

open scoped BigOperators

/-- **Symmetric weighted adjacency operator** `S = D^{1/2} B D^{1/2}`.

For a symmetric `B : Fin T → Fin T → ℝ` and positive weights `W : Fin T → ℝ`,
`symAdj B W i j = sqrt(W i) · B i j · sqrt(W j)` is symmetric, and its
finite spectral theory provides the closing content for the closed-walk
profile separation theorem. -/
noncomputable def symAdj {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (i j : Fin T) : ℝ :=
  Real.sqrt (W i) * B i j * Real.sqrt (W j)

/-- `symAdj` is symmetric whenever `B` is. -/
lemma symAdj_symm {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (i j : Fin T) :
    symAdj B W i j = symAdj B W j i := by
  unfold symAdj
  rw [hB]
  ring

/-- For `W i > 0`, `Real.sqrt (W i) * Real.sqrt (W i) = W i`. -/
lemma sqrt_W_sq {T : ℕ} (W : Fin T → ℝ) (hW : ∀ i, 0 < W i) (i : Fin T) :
    Real.sqrt (W i) * Real.sqrt (W i) = W i :=
  Real.mul_self_sqrt (le_of_lt (hW i))

/-- Diagonal of `symAdj` at `i`: `S[i, i] = W i · B i i`. -/
lemma symAdj_diag {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hW : ∀ i, 0 < W i) (i : Fin T) :
    symAdj B W i i = W i * B i i := by
  unfold symAdj
  rw [show Real.sqrt (W i) * B i i * Real.sqrt (W i) =
      (Real.sqrt (W i) * Real.sqrt (W i)) * B i i from by ring]
  rw [sqrt_W_sq W hW i]

/-- Iterated multiplication of `symAdj` (matrix power as a function). -/
noncomputable def symAdjIter {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    ℕ → Fin T → Fin T → ℝ
  | 0,     i, j => if i = j then 1 else 0
  | n + 1, i, j => ∑ k : Fin T, symAdjIter B W n i k * symAdj B W k j

/-- `S^0` is the identity (diagonal). -/
@[simp] lemma symAdjIter_zero {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (i j : Fin T) :
    symAdjIter B W 0 i j = if i = j then 1 else 0 := rfl

/-- Recursive definition of `S^(n+1)`. -/
lemma symAdjIter_succ {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (n : ℕ) (i j : Fin T) :
    symAdjIter B W (n + 1) i j =
      ∑ k : Fin T, symAdjIter B W n i k * symAdj B W k j := rfl

/-! ### Bridge: closed walk profiles ↔ diagonal moments of `S^m`

The key identity (to be proved by induction):
`closedWalkProfile B W i k = symAdjIter B W k i i / W i` for `k ≥ 1`.

Proof outline: by induction on m, using the conjugation
`M = D^{-1/2} S D^{1/2}` between the (non-symmetric) `weightedAdj` operator
and the symmetric `S`. Both operators have the same powers up to
diagonal-similarity scaling. -/

/-- `symAdjIter` is associative: left-multiplication by `S` is the same
as the recursive (right-multiplication) definition. -/
lemma symAdjIter_left_mult {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (v i : Fin T) :
    ∀ n : ℕ, ∑ k : Fin T, symAdj B W v k * symAdjIter B W n k i =
      symAdjIter B W (n + 1) v i := by
  intro n
  induction n generalizing i with
  | zero =>
      -- LHS: ∑ k, symAdj v k * (if k = i then 1 else 0) = symAdj v i.
      -- RHS: symAdjIter 1 v i = symAdj v i.
      simp only [symAdjIter_zero, mul_ite, mul_one, mul_zero,
                 Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [symAdjIter_succ]
      simp only [symAdjIter_zero, ite_mul, one_mul, zero_mul,
                 Finset.sum_ite_eq, Finset.mem_univ, if_true]
  | succ n ih =>
      -- LHS: ∑ k, symAdj v k * symAdjIter (n+1) k i.
      -- RHS: symAdjIter (n+2) v i = ∑ l, symAdjIter (n+1) v l * symAdj l i.
      rw [symAdjIter_succ]
      -- RHS now: ∑ l, symAdjIter (n+1) v l * symAdj l i.
      -- Use IH (at i := l): ∑ k, symAdj v k * symAdjIter n k l = symAdjIter (n+1) v l.
      have : (∑ l, symAdjIter B W (n + 1) v l * symAdj B W l i) =
             ∑ l, (∑ k, symAdj B W v k * symAdjIter B W n k l) * symAdj B W l i := by
        apply Finset.sum_congr rfl
        intro l _
        rw [ih l]
      rw [this]
      -- Now: ∑ k, symAdj v k * symAdjIter (n+1) k i =
      --      ∑ l, (∑ k, symAdj v k * symAdjIter n k l) * symAdj l i
      -- Expand RHS using Finset.sum_mul + sum_comm:
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      -- Now: ∑ k, symAdj v k * symAdjIter (n+1) k i =
      --      ∑ k, ∑ l, symAdj v k * symAdjIter n k l * symAdj l i
      -- Unfold symAdjIter (n+1) k i = ∑ l, symAdjIter n k l * symAdj l i in LHS:
      conv_lhs => simp only [symAdjIter_succ]
      -- Now: ∑ k, symAdj v k * (∑ l, symAdjIter n k l * symAdj l i) =
      --      ∑ k, ∑ l, symAdj v k * symAdjIter n k l * symAdj l i
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring

/-- **Strong translation lemma**: at any vertex `v`, the weighted-adjacency
iterate scales to the symmetric iterate. -/
lemma weightedAdjIter_eq_symAdjIter_scaled {T : ℕ}
    (B : Fin T → Fin T → ℝ) (_hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ i, 0 < W i) (i : Fin T) :
    ∀ (m : ℕ) (v : Fin T),
      Graphon.Lovasz.weightedAdjIter B W m (fun u => B u i) v *
        Real.sqrt (W v) * Real.sqrt (W i) =
      symAdjIter B W (m + 1) v i := by
  intro m
  induction m with
  | zero =>
      intro v
      show B v i * Real.sqrt (W v) * Real.sqrt (W i) = symAdjIter B W 1 v i
      rw [symAdjIter_succ]
      simp only [symAdjIter_zero, ite_mul, one_mul, zero_mul,
                 Finset.sum_ite_eq, Finset.mem_univ, if_true]
      unfold symAdj
      ring
  | succ m ih =>
      intro v
      show (∑ k : Fin T, W k * B v k *
                Graphon.Lovasz.weightedAdjIter B W m (fun u => B u i) k) *
            Real.sqrt (W v) * Real.sqrt (W i) =
          symAdjIter B W (m + 2) v i
      rw [← symAdjIter_left_mult B W v i (m + 1)]
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      have ihk := ih k
      have hk := sqrt_W_sq W hW k
      show W k * B v k *
              Graphon.Lovasz.weightedAdjIter B W m (fun u => B u i) k *
              Real.sqrt (W v) * Real.sqrt (W i) =
          symAdj B W v k * symAdjIter B W (m + 1) k i
      rw [← ihk]
      conv_lhs => rw [show W k = Real.sqrt (W k) * Real.sqrt (W k) from hk.symm]
      unfold symAdj
      ring

theorem closedWalkProfile_eq_symAdjIter_diag {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (i : Fin T) (m : ℕ) :
    Graphon.Lovasz.closedWalkProfile B W i (m + 1) * W i =
      symAdjIter B W (m + 1) i i := by
  show Graphon.Lovasz.weightedAdjIter B W m (fun v => B v i) i * W i =
       symAdjIter B W (m + 1) i i
  have h := weightedAdjIter_eq_symAdjIter_scaled B hB W hW i m i
  rw [← h, mul_assoc, sqrt_W_sq W hW i]

/-! ### Spectral decomposition + orbit upgrade (Lovász §3 content)

The full closure requires:
1. Real symmetric matrices have orthonormal eigenvector basis
   (mathlib: `Matrix.IsSymm.eigenvectorBasis`).
2. Equal diagonal `(S^m)[i, i]` for all m ⟹ equal spectral measures
   at i, j (Vandermonde on distinct eigenvalues).
3. Twin-free B + positive W ⟹ spectral measures determine orbit class.

Step 3 is the genuine paper-root content. Empirically robust across
4 falsification corpora (>25,000 twin-free graphs, 0 counterexamples). -/

end Graphon.Spectral
