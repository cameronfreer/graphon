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

/-- **Translation lemma** (#77 stepping stone, partial scaffold).

The closed-walk profile of length `m + 1` at vertex `i` equals the
diagonal of `S^(m+1)` divided by `W i`. Equivalently:

`closedWalkProfile B W i (m + 1) * W i = symAdjIter B W (m + 1) i i`

**Status**: stated. Proof by induction on m using the conjugation
`M = D^{-1/2} S D^{1/2}` between `weightedAdj` and `symAdj`. -/
theorem closedWalkProfile_eq_symAdjIter_diag {T : ℕ}
    (_B : Fin T → Fin T → ℝ) (_hB : ∀ i j, _B i j = _B j i)
    (_W : Fin T → ℝ) (_hW : ∀ i, 0 < _W i)
    (i : Fin T) (m : ℕ) :
    Graphon.Lovasz.closedWalkProfile _B _W i (m + 1) * _W i =
      symAdjIter _B _W (m + 1) i i := by
  sorry

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
