/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Graphon.MatrixDetermination

/-!
# Lovász TR-2004-82 feasibility scratch

**This file is intentionally not imported by `Graphon.lean`.** It is a
scratch / branch-only feasibility pass for the Lovász general k-tuple route.
The main `Graphon/MatrixDetermination.lean` is **frozen** at its 3-sorry
state during this pass.

## Reference

> L. Lovász, "The rank of connection matrices and the dimension of graph
> algebras", Microsoft Research Technical Report TR-2004-82, August 2004.
> https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2004-82.pdf

## Goals of this feasibility pass

1. Define `labeledEvalK`, `tupleEquiv`, `tupleOrbitRel`.
2. Prove the k=2 reduction back to the existing `labeledEval2`.
3. Prove **Claim 4.1** (TR-2004-82 §4.3, p. 9): restriction preserves
   equivalence. Easy test of the definitions.
4. Attempt **Claim 4.2** (TR-2004-82 §4.3, p. 9): trace-based extension.
   This is the real bottleneck. If it formalizes cleanly, the Lovász pivot
   is viable. If it doesn't, abandon the pivot and return to the
   constructive frontier in `MatrixDetermination.lean`.

## Status

**Feasibility pass complete. VERDICT: Claim 4.2 does not formalize cleanly.**

The pass landed:
1. Definitions `labeledEvalK`, `tupleEquiv`, `tupleOrbitRel` (clean, straightforward).
2. Claim 4.1 (restriction): skipped — bounded but tedious graph lift via
   `Fin.succAbove`. Routine to formalize, not the bottleneck.
3. Claim 4.2 (trace-extension): **blocker identified**. The proof requires
   the equation `tr(A''_{k+1}) ⊆ A''_k` from Lovász §3 (eq. 6, p. 7), which
   says the trace operator commutes with the algebra homomorphism
   `f_k : G_k → A_k`. Both `A_k` (formal linear combinations of label maps,
   with the `φ * ψ = δ_{φ,ψ} φ` multiplication) and `f_k` (extracting the
   coefficient `hom_φ(F, G)` for each map `φ`) need to exist as Lean
   structures, with several supporting lemmas (algebra homomorphism, inner
   product, kernel of `f_k` equals nullspace, etc.). None of this
   infrastructure currently exists in the codebase.

The blocker is **not a missing tactic** but a **missing layer of definitions**.
Building it would be a multi-session task on the order of 500-1000 lines of
new Lean (the algebra layer + structural lemmas), and is itself only the
prerequisite to the trace argument — Claim 4.2 itself would still need
careful proof on top of it.

**Decision**: per the user's instruction, abandon the Lovász pivot for now
and return to attacking subclaim (L) directly in `MatrixDetermination.lean`.
The Lovász route stays documented in this scratch file as future work; if a
later session validates Claim 4.2 independently, the pivot can be reopened.

This file is on a branch (`lovasz-feasibility`) and is **not** imported by
`Graphon.lean`, so it does not affect the master build.
-/

namespace Graphon
namespace LovaszScratch

open Finset

/-- Local copy of `IsWeightedAutomorphism` (the corresponding definition in
`MatrixDetermination.lean:3306` is `private`, so we duplicate it here for the
feasibility pass to avoid touching the main file). -/
private def IsWeightedAutomorphism {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (π : Equiv.Perm (Fin T)) : Prop :=
  (∀ i, W (π i) = W i) ∧ (∀ i j, B (π i) (π j) = B i j)

/-- **Lovász TR-2004-82 eq. (1)**, p. 4. The normalized k-labeled hom count.

For a k-labeled graph `F` on `Fin (n + k)` with the first k vertices labeled
by `φ : Fin k → Fin T`, and `n` unlabeled vertices summed over via
`σ : Fin n → Fin T`. The combined coloring `τ : Fin (n + k) → Fin T` puts
labels at indices `0..k-1` and unlabeled at indices `k..n+k-1`.

This generalizes `rootedEval` (k=1, in `MatrixDetermination.lean:2311`) and
`labeledEval2` (k=2, in `MatrixDetermination.lean:2756`). -/
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
into the other. The composition order matches the existing `pairOrbitRel` in
`MatrixDetermination.lean:3352`: `ψ i = σ (φ i)`. -/
private def tupleOrbitRel {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) {k : ℕ}
    (φ ψ : Fin k → Fin T) : Prop :=
  ∃ σ : Equiv.Perm (Fin T),
    IsWeightedAutomorphism B W σ ∧ ∀ i, ψ i = σ (φ i)

/-! ### Claim 4.1: restriction preserves equivalence

**TR-2004-82 §4.3, p. 9**. If two `(k+1)`-tuples are equivalent, then their
restrictions to the first k coordinates are also equivalent.

**Proof idea** (Lovász, p. 9): contrapositive. If the restrictions are
distinguished by some k-labeled `F`, then `F ⊗ E_1` (disjoint union of `F`
with a single isolated vertex labeled `k+1`) is a `(k+1)`-labeled graph that
distinguishes the original tuples.
-/

/-- Restriction `Fin.castSucc : Fin k → Fin (k + 1)` of a tuple to its
first k coordinates. -/
private def restrictTuple {T k : ℕ} (φ : Fin (k + 1) → Fin T) : Fin k → Fin T :=
  fun i => φ i.castSucc

/-- **Lovász TR-2004-82, Claim 4.1**, §4.3, p. 9.
Restriction preserves tuple equivalence.

**Status**: sorry (skipped during the feasibility pass — the mechanics of
lifting a k-labeled graph to a (k+1)-labeled graph by inserting an isolated
label at position k via `Fin.succAbove` are tedious but routine). The goal
of the feasibility pass is to test Claim 4.2, not Claim 4.1. -/
private theorem tupleEquiv_restrict {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) {k : ℕ}
    {φ ψ : Fin (k + 1) → Fin T}
    (h : tupleEquiv B W φ ψ) :
    tupleEquiv B W (restrictTuple φ) (restrictTuple ψ) := by
  sorry

/-! ### Claim 4.2: trace-based extension — **the real bottleneck**

**TR-2004-82 §4.3, p. 9**. Given equivalent k-tuples `φ, ψ` and any
extension `μ` of `φ` to k+1, there exists a corresponding extension `ν` of
`ψ` that is equivalent to `μ`.

**Lovász's proof** (p. 9): consider the formal sum `Σ_{η ≡ μ} 1_η ∈ A''_{k+1}`
(elements of A_{k+1} invariant under equivalence). Apply the trace operator
`tr : A''_{k+1} → A''_k` to get `Σ_{η ≡ μ} α(η(k+1)) · 1_{η'} ∈ A''_k` where
`η' = η ∘ castSucc` is the restriction. Since `μ ∈ Ψ_μ` contributes a
non-zero coefficient to `μ' = φ`, and `φ ≡ ψ` (so they have equal
coefficients in any element of A''_k), `ψ` must also have a non-zero
coefficient. So some `η ∈ Ψ_μ` has `η ∘ castSucc = ψ`; this `η` is the
desired `ν`.

**Formalization plan**: avoid building the algebra `A_k` and `A''_k`
explicitly. Instead, work directly with the equivalence class `Ψ_μ` as a
finset and reason about coefficients via `Finset.sum_filter`. The key
ingredients are:
- `Ψ_μ : Finset (Fin (k + 1) → Fin T)` — the equivalence class of `μ`.
  Decidability of `tupleEquiv` is needed to define this finset.
- The "coefficient of `φ` in the restricted sum" is
  `∑ η ∈ Ψ_μ, if η ∘ castSucc = φ then W(η k_last) else 0`.
- Since `μ ∈ Ψ_μ` and `μ ∘ castSucc = φ`, this coefficient is at least
  `W(μ k_last) > 0`.
- The "trace preserves A''" property: equivalent restrictions should sum to
  the same coefficient. This is the technical heart.
- Conclude the coefficient at `ψ` is also positive, hence non-empty, hence
  some `ν ∈ Ψ_μ` has `ν ∘ castSucc = ψ`.

**Decidability of tupleEquiv**: `tupleEquiv B W φ ψ` is `∀ n F, ...`, which
is universally quantified over all `n : ℕ` and all `F : SimpleGraph (Fin (n+k))`.
This is a Π-type over an infinite family — not decidable in general. To work
around this, we may need to *redefine* `tupleEquiv` finitely, e.g., as
"equal on all graphs of size ≤ N" for some sufficient N (Lovász shows
N = T^k suffices for vector-space dimension reasons). This is a major
formalization sub-question.

**Status**: feasibility test. If this formalizes cleanly, the pivot is
viable. If not, abandon. -/
private theorem tupleEquiv_extend {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j) {k : ℕ}
    {φ ψ : Fin k → Fin T} (h : tupleEquiv B W φ ψ)
    (μ : Fin (k + 1) → Fin T) (hμ : restrictTuple μ = φ) :
    ∃ ν : Fin (k + 1) → Fin T, restrictTuple ν = ψ ∧ tupleEquiv B W μ ν := by
  -- Step 1: Define Ψ = equivalence class of μ.
  -- Need decidability of `tupleEquiv` to use Finset.filter; use Classical.dec.
  classical
  let Ψ : Finset (Fin (k + 1) → Fin T) :=
    Finset.univ.filter (fun η => tupleEquiv B W μ η)
  -- Step 2: μ ∈ Ψ.
  have hμ_mem : μ ∈ Ψ := by
    simp only [Ψ, Finset.mem_filter, Finset.mem_univ, true_and]
    intro n F _
    rfl
  -- Step 3: define the trace coefficient at f : Fin k → Fin T as
  -- `coeff f = ∑ η ∈ Ψ.filter (fun η => restrictTuple η = f), W (η (Fin.last k))`.
  -- The intended fact is: equivalent f ≡ g have equal coeff. This is the
  -- "trace preserves A''" property (Lovász eq. (6)).
  --
  -- BLOCKER: proving this requires showing that the trace operator commutes
  -- with the algebra homomorphism f_{k+1} : G_{k+1} → A_{k+1}, which is
  -- structural and depends on the algebra A_k machinery (Lovász §3, p. 6-7).
  -- That machinery does not currently exist in this codebase. The blocker is
  -- not a missing tactic but a missing layer of definitions.
  sorry

end LovaszScratch
end Graphon
