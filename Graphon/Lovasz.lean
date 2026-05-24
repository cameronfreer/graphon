/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lovász §3 — Connection-matrix algebra and the multigraph bridge

This module is **forward-looking infrastructure** for closing the
canonical algebraic root in `Graphon/MatrixDetermination.lean`:

```
private theorem multiLabeledEvalK_tupleEquiv_invariant
```

at `MatrixDetermination.lean:7150`. That sorry is the precise Lovász
TR-2004-82 §3 content: simple-graph `tupleEquiv` ⟹ all multigraph
evaluations agree.

## Module status

**Scaffolding stage**: this module mirrors the multigraph carrier
(`MultiLabeledGraph`, `multiLabeledEvalK`, `MultiLabeledGraph.ofSimple`)
from `MatrixDetermination.lean` and states the bridge theorem here as
the canonical sorry. Other infrastructure stubs (algebra, trace
operator, quotient) are listed but not yet declared.

**Self-contained**: imports only Mathlib basics, no `Graphon.*`
dependencies. Can be developed independently.

**Adapter pattern**: when the bridge proof lands here, the
`MatrixDetermination.lean` consumer call sites get updated to invoke
`Graphon.Lovasz.multiLabeledEvalK_tupleEquiv_invariant` (after wiring
through a small `MultiLabeledGraph` ↔ `Graphon.Lovasz.MultiLabeledGraph`
adapter, since the types live in different namespaces).

## Module structure (planned)

### §1 — Multigraph carrier (DECLARED below)

* `MultiLabeledGraph K n` — structure with `mult : Sym2 (Fin (n + K)) → ℕ`
  and `multNoLoop`.
* `multiLabeledEvalK` — sum-over-σ of W-product times B-power-product.
* `MultiLabeledGraph.ofSimple` — embed a simple graph as a 0/1
  multiplicity multigraph.
* `multiLabeledEvalK_ofSimple` — embedding preserves evaluation.

### §2 — Algebra of multigraphs (Lovász's `𝒢_k`) — STUBS

* `MultiLabeledGraph.empty` — empty multigraph (mult ≡ 0).
* `MultiLabeledGraph.add` — same-vertex pointwise addition.
* `MultiLabeledGraph.glue` — disjoint glue (Lovász's F₁F₂ product);
  analog of `labeledEvalK_glue` (~250 lines future work).
* `multiLabeledEvalK_empty` — empty evaluation = 1 (n = 0) or
  appropriate W-sum-product (n ≥ 1).
* `multiLabeledEvalK_glue` — glue evaluation factors as product.

### §3 — Trace operator and quotient — STUBS

* `multiLabeledEvalK.trace` — fold last label into a new unlabeled.
* `tupleEquivMulti` — multigraph version of `tupleEquiv`.
* `multiLabeledEvalK_trace_closure` — Lovász eq. 6, page 7.

### §4 — The bridge theorem (DECLARED, sorry'd)

* `multiLabeledEvalK_tupleEquiv_invariant` — bridge.

## References

* Lovász, "The rank of connection matrices and the dimension of graph
  algebras", arXiv:math/0408232, Microsoft Research TR-2004-82, 2004.

-/

namespace Graphon.Lovasz

open scoped BigOperators

/-! ### §1 — Multigraph carrier

**Design note (2026-05-17)**: the current `MultiLabeledGraph` carrier
forbids self-loops via `multNoLoop`. This is a restriction relative to
Lovász's full framework (TR-2004-82 §2, p. 3) where self-loops are
allowed via edge-multiset semantics.

**Why this matters for closing #62 and downstream**:
- The IH-free versions of Claims 4.3/4.4 (needed for #70) require
  extracting `B(ψ i, ψ i) = B(i, i)` (diagonal preservation). With
  `multNoLoop`, this is NOT extractable even via multigraph
  evaluations. A self-loop at label-position i with multiplicity 1
  evaluates to `B(ξ i, ξ i)` directly.
- Pointwise W-preservation `W(ψ i) = W(i)` requires either:
  (a) a W-factor at label vertices (our current eval only includes W
      at unlabeled), OR
  (b) a "vertex weight" multigraph operator analogous to self-loops.

**Recommended next-session design** (separate-carrier approach):
1. Add `MultiLabeledGraphLoop K n` carrier WITHOUT `multNoLoop`.
2. Define `multiLabeledEvalKLoop` mirror including `B(τx, τx)^M.mult s(x,x)`.
3. Lift current `MultiLabeledGraph` content via injection
   `MultiLabeledGraph → MultiLabeledGraphLoop`. Existing #62 results
   transfer to no-loop multigraphs trivially.
4. State the full Lovász Theorem 2.2 over `MultiLabeledGraphLoop`:
   simple-graph `h_simple` ⟹ multi-loop evaluation equivalence.
5. Use specific self-loop multigraphs to extract `B(ψ i, ψ i) = B(i, i)`
   and derive IH-free Claims 4.3/4.4.

**W-pointwise (W(ψ i) = W(i)) is a separate open design question**:
- Current eval `multiLabeledEvalK` only includes W at UNLABELED vertices.
- Lovász's framework allows vertex weights `α(v)` at all vertices
  (with `α(label) = 1` by convention in homomorphism counts).
- Extracting `W(ψ i)` for label i requires a different evaluator (e.g.,
  with vertex weight at labels) or going through aut-from-orbit.
- Likely resolution: aut-from-orbit route — once we have orbit
  equivalence (via #70 closure with self-loops), aut preservation of W
  follows from `IsWeightedAutomorphism.W_preserves`. So W-pointwise is
  a CONSEQUENCE, not a primitive, of orbit equivalence.

**Conclusion**: extend with self-loop carrier first (Path A), defer
W-pointwise as a downstream derivation. -/
structure MultiLabeledGraph (K n : ℕ) where
  mult : Sym2 (Fin (n + K)) → ℕ
  multNoLoop : ∀ x : Fin (n + K), mult s(x, x) = 0

/-- **Lovász k-labeled multigraph with self-loops** on `Fin (n + K)`.

Same as `MultiLabeledGraph` but WITHOUT the `multNoLoop` constraint.
Allows self-loops `s(x, x)` to carry positive multiplicity, matching
Lovász TR-2004-82 §2 (p. 3) "graphs" with edge-multiset semantics.

Used as the target carrier for the full rank theorem (closing #62's
mult-≥-2 sub-case and unlocking IH-free Claims 4.3/4.4). See §1
design note above. -/
structure MultiLabeledGraphLoop (K n : ℕ) where
  mult : Sym2 (Fin (n + K)) → ℕ

/-- Inject `MultiLabeledGraph` into `MultiLabeledGraphLoop` (forget
the `multNoLoop` constraint). -/
def MultiLabeledGraph.toLoop {K n : ℕ} (M : MultiLabeledGraph K n) :
    MultiLabeledGraphLoop K n where
  mult := M.mult

/-- **Multigraph evaluation** at a labeled tuple `φ : Fin K → Fin T`.

Sum over unlabeled assignments `σ : Fin n → Fin T` of W-product times
B-power-product (per Sym2-pair, raised to its multiplicity). Reduces
to a simple-graph `labeledEvalK` when all multiplicities are 0 or 1
(see `multiLabeledEvalK_ofSimple`). -/
noncomputable def multiLabeledEvalK {T : ℕ} (K n : ℕ)
    (M : MultiLabeledGraph K n) (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (φ : Fin K → Fin T) : ℝ :=
  ∑ σ : Fin n → Fin T,
    let τ : Fin (n + K) → Fin T := fun v =>
      if h : (v : ℕ) < K then φ ⟨v, h⟩
      else σ ⟨v - K, by have := v.isLt; omega⟩
    (∏ v : Fin n, W (σ v)) *
    ∏ e : Sym2 (Fin (n + K)),
      B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ M.mult e

/-- **Multigraph evaluation with self-loops**.

Mirror of `multiLabeledEvalK` for `MultiLabeledGraphLoop`. The
`B^mult` product runs over the FULL `Sym2 (Fin (n + K))`, including
diagonal pairs `s(x, x)` which contribute `B(τ x, τ x)^M.mult s(x, x)`.

When `M.mult s(x, x) = 0` for all x (i.e., `M = M_noLoop.toLoop` for
some `M_noLoop : MultiLabeledGraph`), this reduces to `multiLabeledEvalK`
(see `multiLabeledEvalKLoop_of_toLoop`). -/
noncomputable def multiLabeledEvalKLoop {T : ℕ} (K n : ℕ)
    (M : MultiLabeledGraphLoop K n) (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (φ : Fin K → Fin T) : ℝ :=
  ∑ σ : Fin n → Fin T,
    let τ : Fin (n + K) → Fin T := fun v =>
      if h : (v : ℕ) < K then φ ⟨v, h⟩
      else σ ⟨v - K, by have := v.isLt; omega⟩
    (∏ v : Fin n, W (σ v)) *
    ∏ e : Sym2 (Fin (n + K)),
      B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ M.mult e

/-- **No-loop reduction**: when injected from `MultiLabeledGraph`, the
loop-aware evaluator agrees with `multiLabeledEvalK` (diagonal terms
contribute `B^0 = 1`). -/
theorem multiLabeledEvalKLoop_of_toLoop {T K n : ℕ}
    (M : MultiLabeledGraph K n) (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (φ : Fin K → Fin T) :
    multiLabeledEvalKLoop K n M.toLoop B W φ =
      multiLabeledEvalK K n M B W φ := rfl

/-- **Automorphism invariance of `multiLabeledEvalKLoop`**.

Mirrors `multiLabeledEvalK_aut_invariant`. The proof transfers directly
because the only difference is the domain of the Sym2 product (with vs
without diagonals), and `hσ_B` applies uniformly to diagonal pairs too. -/
theorem multiLabeledEvalKLoop_aut_invariant {T K n : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (M : MultiLabeledGraphLoop K n)
    (σ : Equiv.Perm (Fin T))
    (hσ_W : ∀ i, W (σ i) = W i)
    (hσ_B : ∀ i j, B (σ i) (σ j) = B i j)
    (φ : Fin K → Fin T) :
    multiLabeledEvalKLoop K n M B W (σ ∘ φ) =
    multiLabeledEvalKLoop K n M B W φ := by
  unfold multiLabeledEvalKLoop
  rw [← Equiv.sum_comp (Equiv.arrowCongr (Equiv.refl (Fin n)) σ)]
  refine Finset.sum_congr rfl fun σ_inner _ => ?_
  have hW_eq : ∀ v : Fin n,
      W (((Equiv.arrowCongr (Equiv.refl (Fin n)) σ) σ_inner) v) = W (σ_inner v) := by
    intro v; show W (σ (σ_inner v)) = W (σ_inner v); exact hσ_W _
  have hB_eq : ∀ τ_L τ_R : Fin (n + K) → Fin T,
      (∀ v, τ_L v = σ (τ_R v)) →
      (∏ e : Sym2 (Fin (n + K)),
        B (τ_L (Quot.out e).1) (τ_L (Quot.out e).2) ^ M.mult e) =
      (∏ e : Sym2 (Fin (n + K)),
        B (τ_R (Quot.out e).1) (τ_R (Quot.out e).2) ^ M.mult e) := by
    intro τ_L τ_R hτ
    refine Finset.prod_congr rfl fun e _ => ?_
    congr 1
    rw [hτ, hτ]; exact hσ_B _ _
  let τ_R : Fin (n + K) → Fin T := fun v =>
    if h : (v : ℕ) < K then φ ⟨v, h⟩
    else σ_inner ⟨v - K, by have := v.isLt; omega⟩
  let τ_L : Fin (n + K) → Fin T := fun v =>
    if h : (v : ℕ) < K then (σ ∘ φ) ⟨v, h⟩
    else ((Equiv.arrowCongr (Equiv.refl (Fin n)) σ) σ_inner)
            ⟨v - K, by have := v.isLt; omega⟩
  have hτ_pt : ∀ v : Fin (n + K), τ_L v = σ (τ_R v) := by
    intro v
    by_cases hv : (v : ℕ) < K
    · show (if h : (v : ℕ) < K then (σ ∘ φ) ⟨v, h⟩ else _) =
            σ (if h : (v : ℕ) < K then φ ⟨v, h⟩ else _)
      rw [dif_pos hv, dif_pos hv]
      rfl
    · show (if h : (v : ℕ) < K then _ else
              ((Equiv.arrowCongr (Equiv.refl (Fin n)) σ) σ_inner)
                ⟨v - K, by have := v.isLt; omega⟩) =
            σ (if h : (v : ℕ) < K then _ else
                σ_inner ⟨v - K, by have := v.isLt; omega⟩)
      rw [dif_neg hv, dif_neg hv]
      rfl
  change (∏ v : Fin n, W (((Equiv.arrowCongr (Equiv.refl (Fin n)) σ) σ_inner) v)) *
       (∏ e : Sym2 (Fin (n + K)),
         B (τ_L (Quot.out e).1) (τ_L (Quot.out e).2) ^ M.mult e) =
       (∏ v : Fin n, W (σ_inner v)) *
       (∏ e : Sym2 (Fin (n + K)),
         B (τ_R (Quot.out e).1) (τ_R (Quot.out e).2) ^ M.mult e)
  rw [Finset.prod_congr rfl (fun v _ => hW_eq v), hB_eq τ_L τ_R hτ_pt]

/-- **Orbit invariance of `multiLabeledEvalKLoop`** (corollary). -/
theorem multiLabeledEvalKLoop_orbit_invariant {T K n : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (M : MultiLabeledGraphLoop K n)
    {ξ ξ' : Fin K → Fin T}
    (h : ∃ σ : Equiv.Perm (Fin T),
      (∀ i, W (σ i) = W i) ∧ (∀ i j, B (σ i) (σ j) = B i j) ∧
      (∀ i, ξ' i = σ (ξ i))) :
    multiLabeledEvalKLoop K n M B W ξ = multiLabeledEvalKLoop K n M B W ξ' := by
  obtain ⟨σ, hσ_W, hσ_B, hξ'⟩ := h
  have : ξ' = σ ∘ ξ := funext hξ'
  rw [this]
  exact (multiLabeledEvalKLoop_aut_invariant B W M σ hσ_W hσ_B ξ).symm

/-- **Loop n=0 bridge** (step 4 of #79). At `n = 0`, the loop multigraph
evaluation is a product of B-power factors over `Sym2 (Fin K)`,
including diagonal pairs `s(a, a)` weighted by their multiplicity.
Equality between `ξ` and `ξ'` holds given:
- per-pair B-equality at non-diagonal label positions (`h_offdiag`,
  derivable from `tupleEquivSimple`), and
- per-vertex diagonal observable (`h_diag`, the data needed beyond
  simple-graph equivalence — supplied by the rank theorem).

This isolates the diagonal observable as the SOLE additional input
needed for the n=0 loop case. -/
theorem multiLabeledEvalKLoop_n_zero_of_diag {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (M : MultiLabeledGraphLoop K 0)
    {ξ ξ' : Fin K → Fin T}
    (h_offdiag : ∀ a b : Fin K, a ≠ b → B (ξ a) (ξ b) = B (ξ' a) (ξ' b))
    (h_diag : ∀ a : Fin K, B (ξ a) (ξ a) = B (ξ' a) (ξ' a)) :
    multiLabeledEvalKLoop K 0 M B W ξ = multiLabeledEvalKLoop K 0 M B W ξ' := by
  classical
  unfold multiLabeledEvalKLoop
  rw [Fintype.sum_unique, Fintype.sum_unique]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
  -- ∏ e : Sym2 (Fin (0+K)), B (τξ ·) ^ M.mult e = same with τξ'
  apply Finset.prod_congr rfl
  intro e _
  congr 1
  -- Goal: B (τξ (Quot.out e).1) (τξ (Quot.out e).2) =
  --       B (τξ' (Quot.out e).1) (τξ' (Quot.out e).2)
  -- where τξ x = ξ ⟨x.val, _⟩, since v.val < K for all v : Fin (0+K).
  set p := Quot.out (e : Sym2 (Fin (0 + K)))
  -- Compute τ at p.1, p.2 (both have val < K).
  have hp1 : (p.1 : ℕ) < K := by have := p.1.isLt; omega
  have hp2 : (p.2 : ℕ) < K := by have := p.2.isLt; omega
  rw [dif_pos hp1, dif_pos hp2, dif_pos hp1, dif_pos hp2]
  -- Goal: B (ξ ⟨p.1, _⟩) (ξ ⟨p.2, _⟩) = B (ξ' ⟨p.1, _⟩) (ξ' ⟨p.2, _⟩).
  by_cases hp_eq : (⟨p.1.val, hp1⟩ : Fin K) = ⟨p.2.val, hp2⟩
  · rw [hp_eq]; exact h_diag _
  · exact h_offdiag _ _ hp_eq

/-- **Simple-graph embedding** into the multigraph carrier.

For any `F : SimpleGraph (Fin (n + K))` with decidable adjacency, the
0/1-multiplicity multigraph has `mult e = if e ∈ F.edgeFinset then 1
else 0`. `multNoLoop` follows from `SimpleGraph.loopless`. -/
noncomputable def MultiLabeledGraph.ofSimple {K n : ℕ}
    (F : SimpleGraph (Fin (n + K))) [DecidableRel F.Adj] :
    MultiLabeledGraph K n where
  mult e := if e ∈ F.edgeFinset then 1 else 0
  multNoLoop x := by
    rw [if_neg]
    intro h
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at h
    exact F.loopless _ h

/-- **`multiLabeledEvalK` of `ofSimple F` matches the simple-graph
σ-sum body** (the analog of `MatrixDetermination.lean:7156`).

The 0/1-multigraph evaluation reduces to the simple-graph form:
- For `e ∈ F.edgeFinset`: `B^1 = B` (factor present).
- For `e ∉ F.edgeFinset`: `B^0 = 1` (no contribution).

The RHS is the simple-graph evaluation pattern (analog of
`labeledEvalK F`); its product is over `F.edgeFinset` rather than
all of `Sym2`. -/
theorem multiLabeledEvalK_ofSimple {T K n : ℕ}
    (F : SimpleGraph (Fin (n + K))) [DecidableRel F.Adj]
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (φ : Fin K → Fin T) :
    multiLabeledEvalK K n (MultiLabeledGraph.ofSimple F) B W φ =
    ∑ σ : Fin n → Fin T,
      (let τ : Fin (n + K) → Fin T := fun v =>
        if h : (v : ℕ) < K then φ ⟨v, h⟩
        else σ ⟨v - K, by have := v.isLt; omega⟩
      (∏ v : Fin n, W (σ v)) *
      ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2)) := by
  classical
  -- Helper: τ-parametric Sym2 product reduces to F.edgeFinset product.
  have hprod : ∀ τ : Fin (n + K) → Fin T,
      (∏ e : Sym2 (Fin (n + K)),
        B (τ (Quot.out e).1) (τ (Quot.out e).2) ^
          (MultiLabeledGraph.ofSimple F).mult e) =
      ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2) := by
    intro τ
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Sym2 (Fin (n + K))))
          (· ∈ F.edgeFinset)]
    have hnot : (∏ x ∈ (Finset.univ : Finset (Sym2 (Fin (n + K)))).filter
            (fun e => ¬ e ∈ F.edgeFinset),
          B (τ (Quot.out x).1) (τ (Quot.out x).2) ^
            (MultiLabeledGraph.ofSimple F).mult x) = 1 :=
      Finset.prod_eq_one fun e he => by
        rw [Finset.mem_filter] at he
        show B _ _ ^ (if _ then 1 else 0 : ℕ) = 1
        rw [if_neg he.2]; exact pow_zero _
    rw [hnot, mul_one]
    rw [show ((Finset.univ : Finset (Sym2 (Fin (n + K)))).filter (· ∈ F.edgeFinset)) =
          F.edgeFinset from by ext e; simp]
    refine Finset.prod_congr rfl fun e he => ?_
    show B _ _ ^ (if _ then 1 else 0 : ℕ) = _
    rw [if_pos he]; exact pow_one _
  unfold multiLabeledEvalK
  refine Finset.sum_congr rfl fun σ _ => ?_
  set τ : Fin (n + K) → Fin T := fun v =>
    if h : (v : ℕ) < K then φ ⟨v, h⟩
    else σ ⟨v - K, by have := v.isLt; omega⟩
  show (∏ v : Fin n, W (σ v)) *
       (∏ e : Sym2 (Fin (n + K)),
         B (τ (Quot.out e).1) (τ (Quot.out e).2) ^
           (MultiLabeledGraph.ofSimple F).mult e) =
       (∏ v : Fin n, W (σ v)) *
       (∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2))
  rw [hprod τ]

/-! ### §2 — Algebra of multigraphs (Lovász's `𝒢_k`)

Bounded building blocks: `empty`, `add` (same-vertex pointwise
addition), and the basic `multiLabeledEvalK_empty` reduction. The
heavyweight `glue` (Lovász's F₁F₂ product, disjoint union of unlabeled
vertices) is deferred to a future session — it requires a multigraph
analog of `labeledEvalK_glue` (~250 lines).

The corresponding evaluation factorization for `add` is non-trivial
even at the same vertex set (W-product gets squared), so it's treated
as a separate algebra step coupled with the disjoint-glue construction
in Lovász's framework. Stub theorems are listed in module docstring
above. -/

/-- The **empty multigraph**: zero multiplicity on every Sym2-pair. -/
def MultiLabeledGraph.empty (K n : ℕ) : MultiLabeledGraph K n where
  mult _ := 0
  multNoLoop _ := rfl

/-- **Pointwise addition** of multiplicities (same vertex set). The
addition operation in the quantum-graph algebra `𝒢_k` at fixed
unlabeled-vertex count. -/
def MultiLabeledGraph.add {K n : ℕ}
    (M₁ M₂ : MultiLabeledGraph K n) : MultiLabeledGraph K n where
  mult e := M₁.mult e + M₂.mult e
  multNoLoop x := by simp [M₁.multNoLoop x, M₂.multNoLoop x]

/-- **Per-Sym2 add factorization**: for ANY function τ, the
product over Sym2 of `B(τ ·)(τ ·) ^ (M₁.mult + M₂.mult)` factors as
the product of `B^M₁.mult` and `B^M₂.mult`. -/
theorem multiLabeledEvalK_perSym2_add {T K n : ℕ}
    (B : Fin T → Fin T → ℝ) (M₁ M₂ : MultiLabeledGraph K n)
    (τ : Fin (n + K) → Fin T) :
    (∏ e : Sym2 (Fin (n + K)),
      B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ (M₁.add M₂).mult e) =
    (∏ e : Sym2 (Fin (n + K)),
      B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ M₁.mult e) *
    (∏ e : Sym2 (Fin (n + K)),
      B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ M₂.mult e) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ => ?_
  show _ ^ (M₁.mult e + M₂.mult e) = _
  exact pow_add _ _ _

/-- Empty multigraph evaluation: every B-power factor is `B^0 = 1`,
so the σ-sum body collapses to the W-product. -/
theorem multiLabeledEvalK_empty {T K n : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (φ : Fin K → Fin T) :
    multiLabeledEvalK K n (MultiLabeledGraph.empty K n) B W φ =
    ∑ σ : Fin n → Fin T, ∏ v : Fin n, W (σ v) := by
  unfold multiLabeledEvalK
  refine Finset.sum_congr rfl fun σ _ => ?_
  -- Helper: each B-power factor with exponent 0 is 1, so the Sym2
  -- product collapses to 1. Apply via a τ-parametric helper to avoid
  -- the let-binding unification issue.
  have hone : ∀ τ : Fin (n + K) → Fin T,
      (∏ e : Sym2 (Fin (n + K)),
        B (τ (Quot.out e).1) (τ (Quot.out e).2) ^
          (MultiLabeledGraph.empty K n).mult e) = 1 :=
    fun τ => Finset.prod_eq_one fun e _ => by
      show B _ _ ^ (0 : ℕ) = 1
      exact pow_zero _
  -- Bind τ as a name and apply hone.
  set τ : Fin (n + K) → Fin T := fun v =>
    if h : (v : ℕ) < K then φ ⟨v, h⟩
    else σ ⟨v - K, by have := v.isLt; omega⟩
  show (∏ v : Fin n, W (σ v)) *
       (∏ e : Sym2 (Fin (n + K)),
         B (τ (Quot.out e).1) (τ (Quot.out e).2) ^
           (MultiLabeledGraph.empty K n).mult e) =
       ∏ v : Fin n, W (σ v)
  rw [hone τ, mul_one]

/-- **Same-vertex add factorization** (general n).

For any pair `M₁ M₂ : MultiLabeledGraph K n`, the multigraph
evaluation of `M₁.add M₂` does NOT factor as the product of
evaluations in general: the `W`-product gets shared once but the
B-product factors via `pow_add`. Compare with Lovász's F₁F₂ product
(disjoint glue), which DOES factor cleanly.

Result: per-σ factorization holds, but the σ-sum doesn't distribute. -/
theorem multiLabeledEvalK_add_perσ {T K n : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (M₁ M₂ : MultiLabeledGraph K n) (φ : Fin K → Fin T) :
    multiLabeledEvalK K n (M₁.add M₂) B W φ =
    ∑ σ : Fin n → Fin T,
      let τ : Fin (n + K) → Fin T := fun v =>
        if h : (v : ℕ) < K then φ ⟨v, h⟩
        else σ ⟨v - K, by have := v.isLt; omega⟩
      (∏ v : Fin n, W (σ v)) *
      ((∏ e : Sym2 (Fin (n + K)),
          B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ M₁.mult e) *
       (∏ e : Sym2 (Fin (n + K)),
          B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ M₂.mult e)) := by
  unfold multiLabeledEvalK
  refine Finset.sum_congr rfl fun σ _ => ?_
  set τ : Fin (n + K) → Fin T := fun v =>
    if h : (v : ℕ) < K then φ ⟨v, h⟩
    else σ ⟨v - K, by have := v.isLt; omega⟩
  show (∏ v : Fin n, W (σ v)) *
       (∏ e : Sym2 (Fin (n + K)),
         B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ (M₁.add M₂).mult e) =
       (∏ v : Fin n, W (σ v)) * _
  rw [multiLabeledEvalK_perSym2_add B M₁ M₂ τ]

/-! ### §3 — Disjoint-glue product (Lovász's F₁F₂)

The disjoint-glue product is the multiplication operation in the
quantum-graph algebra `𝒢_k`. Vertex space: `Fin ((n₁ + n₂) + K)`.
Labels (val < K) are shared. M₁'s unlabeled occupy positions
`K..K+n₁-1`; M₂'s unlabeled occupy positions `K+n₁..K+n₁+n₂-1`.

Multiplicity at e ∈ Sym2(Fin ((n₁+n₂)+K)):
  - **Label-label** (both endpoints val < K): `M₁.mult e + M₂.mult e`
    (using Sym2.map identity-on-labels embeddings).
  - **M₁-only** (both endpoints val < K + n₁, not both labels):
    `M₁.mult` of the lift via emb₁.
  - **M₂-only** (both endpoints val < K or val ≥ K + n₁):
    `M₂.mult` of the lift via emb₂.
  - **Cross** (one M₁-unlabeled, one M₂-unlabeled): 0. -/

/-- **M₁-side cast**: project a vertex `v : Fin ((n₁+n₂)+K)` into `Fin (n₁+K)`
when its `val` lies in M₁'s scope (i.e. `val < n₁+K`). Returns `none` for
M₂-unlabeled vertices (`val ≥ n₁+K`). -/
def glueCast₁ (K n₁ n₂ : ℕ) (v : Fin ((n₁ + n₂) + K)) : Option (Fin (n₁ + K)) :=
  if h : v.val < n₁ + K then some ⟨v.val, h⟩ else none

/-- **M₂-side cast**: project a vertex `v : Fin ((n₁+n₂)+K)` into `Fin (n₂+K)`
when its `val` is either a label (`val < K`, mapped to itself) or M₂-unlabeled
(`val ≥ n₁+K`, shifted back by `n₁`). Returns `none` for M₁-unlabeled vertices. -/
def glueCast₂ (K n₁ n₂ : ℕ) (v : Fin ((n₁ + n₂) + K)) : Option (Fin (n₂ + K)) :=
  if h : v.val < K then some ⟨v.val, by omega⟩
  else if h2 : v.val ≥ n₁ + K then some ⟨v.val - n₁, by have := v.isLt; omega⟩
  else none

/-- **Disjoint glue** of two k-labeled multigraphs (Lovász's F₁F₂ product).

Vertex space `Fin ((n₁+n₂)+K)`: labels at positions `0..K-1` (shared);
M₁'s unlabeled at `K..K+n₁-1`; M₂'s unlabeled at `K+n₁..K+n₁+n₂-1`.
Multiplicity at `e` adds the M₁-contribution (when both endpoints are in
M₁'s scope) and the M₂-contribution (when both endpoints are labels or in
M₂'s shifted unlabeled range). Cross-type pairs (one M₁-unlabeled, one
M₂-unlabeled) contribute 0. -/
def MultiLabeledGraph.glue {K n₁ n₂ : ℕ}
    (M₁ : MultiLabeledGraph K n₁) (M₂ : MultiLabeledGraph K n₂) :
    MultiLabeledGraph K (n₁ + n₂) where
  mult := Sym2.lift ⟨fun u v =>
    (match glueCast₁ K n₁ n₂ u, glueCast₁ K n₁ n₂ v with
     | some u', some v' => M₁.mult s(u', v')
     | _, _ => 0) +
    (match glueCast₂ K n₁ n₂ u, glueCast₂ K n₁ n₂ v with
     | some u', some v' => M₂.mult s(u', v')
     | _, _ => 0),
   by
     intro a b
     rcases hc1a : glueCast₁ K n₁ n₂ a with _ | u₁a <;>
       rcases hc1b : glueCast₁ K n₁ n₂ b with _ | u₁b <;>
       rcases hc2a : glueCast₂ K n₁ n₂ a with _ | u₂a <;>
       rcases hc2b : glueCast₂ K n₁ n₂ b with _ | u₂b <;>
       simp only [hc1a, hc1b, hc2a, hc2b] <;>
       (try rw [show s(u₁a, u₁b) = s(u₁b, u₁a) from Sym2.eq_swap]) <;>
       (try rw [show s(u₂a, u₂b) = s(u₂b, u₂a) from Sym2.eq_swap])⟩
  multNoLoop x := by
    show (match glueCast₁ K n₁ n₂ x, glueCast₁ K n₁ n₂ x with
          | some u', some v' => M₁.mult s(u', v')
          | _, _ => 0) +
         (match glueCast₂ K n₁ n₂ x, glueCast₂ K n₁ n₂ x with
          | some u', some v' => M₂.mult s(u', v')
          | _, _ => 0) = 0
    rcases hc1 : glueCast₁ K n₁ n₂ x with _ | u₁ <;>
      rcases hc2 : glueCast₂ K n₁ n₂ x with _ | u₂ <;>
      simp [M₁.multNoLoop, M₂.multNoLoop]

/-- Unfold lemma for `MultiLabeledGraph.glue.mult` at an unordered pair `s(a, b)`. -/
theorem MultiLabeledGraph.glue_mult_pair {K n₁ n₂ : ℕ}
    (M₁ : MultiLabeledGraph K n₁) (M₂ : MultiLabeledGraph K n₂)
    (a b : Fin ((n₁ + n₂) + K)) :
    (M₁.glue M₂).mult s(a, b) =
    (match glueCast₁ K n₁ n₂ a, glueCast₁ K n₁ n₂ b with
     | some u', some v' => M₁.mult s(u', v')
     | _, _ => 0) +
    (match glueCast₂ K n₁ n₂ a, glueCast₂ K n₁ n₂ b with
     | some u', some v' => M₂.mult s(u', v')
     | _, _ => 0) := rfl

/-- **Sum factorization over `Fin (m + p)` colorings.** A function on
`Fin (m+p) → Fin k` colorings restricted via `Fin.castAdd`/`Fin.natAdd`
factors the sum into a product of independent sums. Mirrors
`MatrixDetermination.lean`'s `sum_piFinAdd_factor`. -/
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
      f (e τ).1 * g (e τ).2 := fun _ => by rfl
  simp_rw [he]
  have h1 : ∑ x, f (e x).1 * g (e x).2 =
      ∑ x : (Fin m → Fin k) × (Fin p → Fin k), f x.1 * g x.2 :=
    Equiv.sum_comp e (fun y => f y.1 * g y.2)
  rw [h1, Fintype.sum_prod_type]
  exact (Fintype.sum_mul_sum f g).symm

/-- For symmetric `B`, the `B`-product at `Quot.out` of an unordered pair equals
`B` at the pair's actual endpoints. Resolves the `Quot.out` orientation. -/
private theorem B_quot_out_eq {α : Type*} {T : ℕ} {B : Fin T → Fin T → ℝ}
    (hB : ∀ i j, B i j = B j i) (f : α → Fin T) (a b : α) :
    B (f (Quot.out s(a, b)).1) (f (Quot.out s(a, b)).2) = B (f a) (f b) := by
  set p := Quot.out s(a, b)
  have key : (p.1 = a ∧ p.2 = b) ∨ (p.1 = b ∧ p.2 = a) := by
    have := Sym2.eq_iff.mp (Quot.out_eq s(a, b))
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [left; right] <;> exact ⟨h1, h2⟩
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h1, h2, hB]

/-- Same as `B_quot_out_eq` but with mult exponentiation. -/
private theorem B_pow_quot_out_eq {α : Type*} {T : ℕ} {B : Fin T → Fin T → ℝ}
    (hB : ∀ i j, B i j = B j i) (f : α → Fin T) (a b : α) (m : ℕ) :
    B (f (Quot.out s(a, b)).1) (f (Quot.out s(a, b)).2) ^ m = B (f a) (f b) ^ m := by
  rw [B_quot_out_eq hB]

/-- Identity-on-labels embedding `Fin (n₁ + K) ↪ Fin ((n₁ + n₂) + K)`. -/
def glueEmb₁ (K n₁ n₂ : ℕ) : Fin (n₁ + K) ↪ Fin ((n₁ + n₂) + K) :=
  ⟨fun v => ⟨v.val, by have := v.isLt; omega⟩,
   fun a b h => Fin.ext (by simpa using congr_arg Fin.val h)⟩

/-- Embedding `Fin (n₂ + K) ↪ Fin ((n₁ + n₂) + K)`: labels (val < K) are
preserved; M₂'s unlabeled vertices (val ≥ K) are shifted by n₁. -/
def glueEmb₂ (K n₁ n₂ : ℕ) : Fin (n₂ + K) ↪ Fin ((n₁ + n₂) + K) where
  toFun v := if h : v.val < K then ⟨v.val, by omega⟩
             else ⟨n₁ + v.val, by have := v.isLt; omega⟩
  inj' a b h := by
    by_cases ha : a.val < K <;> by_cases hb : b.val < K <;>
      simp only [ha, hb, dif_pos, dif_neg, not_false_eq_true, Fin.mk.injEq] at h <;>
      exact Fin.ext (by omega)

/-- `glueCast₁ K n₁ n₂ (glueEmb₁ K n₁ n₂ v) = some v`. -/
@[simp] theorem glueCast₁_glueEmb₁ (K n₁ n₂ : ℕ) (v : Fin (n₁ + K)) :
    glueCast₁ K n₁ n₂ (glueEmb₁ K n₁ n₂ v) = some v := by
  simp only [glueCast₁, glueEmb₁, Function.Embedding.coeFn_mk]
  have : v.val < n₁ + K := v.isLt
  rw [dif_pos this]

/-- `glueCast₂ K n₁ n₂ (glueEmb₂ K n₁ n₂ v) = some v`. -/
@[simp] theorem glueCast₂_glueEmb₂ (K n₁ n₂ : ℕ) (v : Fin (n₂ + K)) :
    glueCast₂ K n₁ n₂ (glueEmb₂ K n₁ n₂ v) = some v := by
  by_cases h : v.val < K
  · have hemb : (glueEmb₂ K n₁ n₂ v) = ⟨v.val, by omega⟩ := by
      show (if h' : v.val < K then (⟨v.val, by omega⟩ : Fin _)
            else ⟨n₁ + v.val, by have := v.isLt; omega⟩) = _
      rw [dif_pos h]
    rw [hemb]
    show (if h' : (⟨v.val, _⟩ : Fin ((n₁ + n₂) + K)).val < K
          then some ⟨(⟨v.val, _⟩ : Fin ((n₁ + n₂) + K)).val, by omega⟩
          else _) = some v
    rw [dif_pos h]
  · have hemb : (glueEmb₂ K n₁ n₂ v) =
        ⟨n₁ + v.val, by have := v.isLt; omega⟩ := by
      show (if h' : v.val < K then (⟨v.val, by omega⟩ : Fin _)
            else ⟨n₁ + v.val, by have := v.isLt; omega⟩) = _
      rw [dif_neg h]
    rw [hemb]
    show glueCast₂ K n₁ n₂ ⟨n₁ + v.val, _⟩ = some v
    have hnK : ¬ (n₁ + v.val < K) := by omega
    have hge : n₁ + v.val ≥ n₁ + K := by omega
    simp only [glueCast₂, hnK, hge, ↓reduceDIte]
    congr 1
    apply Fin.ext
    show n₁ + v.val - n₁ = v.val
    omega

/-- For an M₁-side vertex (val < n₁ + K), `glueCast₁` evaluated at it is
`some` of its restriction. Allows treating M₁-only positions explicitly. -/
theorem glueCast₁_of_val_lt (K n₁ n₂ : ℕ) (v : Fin ((n₁ + n₂) + K))
    (h : v.val < n₁ + K) : glueCast₁ K n₁ n₂ v = some ⟨v.val, h⟩ := by
  simp [glueCast₁, h]

/-- For an M₂-unlabeled vertex (val ≥ n₁ + K), `glueCast₂` returns
`some ⟨v.val - n₁, _⟩`. -/
theorem glueCast₂_of_val_ge (K n₁ n₂ : ℕ) (v : Fin ((n₁ + n₂) + K))
    (h : v.val ≥ n₁ + K) :
    glueCast₂ K n₁ n₂ v = some ⟨v.val - n₁, by have := v.isLt; omega⟩ := by
  have hnK : ¬ v.val < K := by omega
  simp [glueCast₂, hnK, h]

/-- For a label vertex (val < K), `glueCast₂` returns `some ⟨v.val, _⟩`. -/
theorem glueCast₂_of_label (K n₁ n₂ : ℕ) (v : Fin ((n₁ + n₂) + K))
    (h : v.val < K) : glueCast₂ K n₁ n₂ v = some ⟨v.val, by omega⟩ := by
  simp [glueCast₂, h]

/-- For an M₁-unlabeled vertex (K ≤ val < n₁ + K), `glueCast₂` returns `none`. -/
theorem glueCast₂_of_M1_unlabeled (K n₁ n₂ : ℕ) (v : Fin ((n₁ + n₂) + K))
    (hge : v.val ≥ K) (hlt : v.val < n₁ + K) :
    glueCast₂ K n₁ n₂ v = none := by
  have h1 : ¬ v.val < K := by omega
  have h2 : ¬ v.val ≥ n₁ + K := by omega
  simp [glueCast₂, h1, h2]

/-- For an M₂-unlabeled vertex (val ≥ n₁ + K), `glueCast₁` returns `none`. -/
theorem glueCast₁_of_M2_unlabeled (K n₁ n₂ : ℕ) (v : Fin ((n₁ + n₂) + K))
    (h : v.val ≥ n₁ + K) : glueCast₁ K n₁ n₂ v = none := by
  have h1 : ¬ v.val < n₁ + K := by omega
  simp [glueCast₁, h1]

/-- The first additive part of `(M₁.glue M₂).mult`: contribution from M₁
(zero outside M₁'s scope, computed via `glueCast₁`). -/
def gluePart₁ {K n₁ n₂ : ℕ}
    (M₁ : MultiLabeledGraph K n₁) (_M₂ : MultiLabeledGraph K n₂)
    (e : Sym2 (Fin ((n₁ + n₂) + K))) : ℕ :=
  Sym2.lift ⟨fun u v =>
    match glueCast₁ K n₁ n₂ u, glueCast₁ K n₁ n₂ v with
    | some u', some v' => M₁.mult s(u', v')
    | _, _ => 0,
   by
     intro a b
     rcases hc1a : glueCast₁ K n₁ n₂ a with _ | u₁a <;>
       rcases hc1b : glueCast₁ K n₁ n₂ b with _ | u₁b <;>
       (simp only [hc1a, hc1b];
        try rw [show s(u₁a, u₁b) = s(u₁b, u₁a) from Sym2.eq_swap])⟩ e

/-- The second additive part of `(M₁.glue M₂).mult`: contribution from M₂
(zero outside M₂'s scope, computed via `glueCast₂`). -/
def gluePart₂ {K n₁ n₂ : ℕ}
    (_M₁ : MultiLabeledGraph K n₁) (M₂ : MultiLabeledGraph K n₂)
    (e : Sym2 (Fin ((n₁ + n₂) + K))) : ℕ :=
  Sym2.lift ⟨fun u v =>
    match glueCast₂ K n₁ n₂ u, glueCast₂ K n₁ n₂ v with
    | some u', some v' => M₂.mult s(u', v')
    | _, _ => 0,
   by
     intro a b
     rcases hc2a : glueCast₂ K n₁ n₂ a with _ | u₂a <;>
       rcases hc2b : glueCast₂ K n₁ n₂ b with _ | u₂b <;>
       (simp only [hc2a, hc2b];
        try rw [show s(u₂a, u₂b) = s(u₂b, u₂a) from Sym2.eq_swap])⟩ e

/-- `(M₁.glue M₂).mult = gluePart₁ + gluePart₂`. -/
theorem MultiLabeledGraph.glue_mult_eq_add {K n₁ n₂ : ℕ}
    (M₁ : MultiLabeledGraph K n₁) (M₂ : MultiLabeledGraph K n₂)
    (e : Sym2 (Fin ((n₁ + n₂) + K))) :
    (M₁.glue M₂).mult e = gluePart₁ M₁ M₂ e + gluePart₂ M₁ M₂ e := by
  refine Sym2.ind (fun a b => ?_) e
  rfl

/-- `gluePart₁` evaluated at `(glueEmb₁ a, glueEmb₁ b)` returns `M₁.mult s(a, b)`. -/
theorem gluePart₁_emb₁ {K n₁ n₂ : ℕ}
    (M₁ : MultiLabeledGraph K n₁) (M₂ : MultiLabeledGraph K n₂)
    (a b : Fin (n₁ + K)) :
    gluePart₁ M₁ M₂ s(glueEmb₁ K n₁ n₂ a, glueEmb₁ K n₁ n₂ b) = M₁.mult s(a, b) := by
  show (match glueCast₁ K n₁ n₂ (glueEmb₁ K n₁ n₂ a), glueCast₁ K n₁ n₂ (glueEmb₁ K n₁ n₂ b) with
        | some u', some v' => M₁.mult s(u', v')
        | _, _ => 0) = M₁.mult s(a, b)
  rw [glueCast₁_glueEmb₁, glueCast₁_glueEmb₁]

/-- `gluePart₂` evaluated at `(glueEmb₂ a, glueEmb₂ b)` returns `M₂.mult s(a, b)`. -/
theorem gluePart₂_emb₂ {K n₁ n₂ : ℕ}
    (M₁ : MultiLabeledGraph K n₁) (M₂ : MultiLabeledGraph K n₂)
    (a b : Fin (n₂ + K)) :
    gluePart₂ M₁ M₂ s(glueEmb₂ K n₁ n₂ a, glueEmb₂ K n₁ n₂ b) = M₂.mult s(a, b) := by
  show (match glueCast₂ K n₁ n₂ (glueEmb₂ K n₁ n₂ a), glueCast₂ K n₁ n₂ (glueEmb₂ K n₁ n₂ b) with
        | some u', some v' => M₂.mult s(u', v')
        | _, _ => 0) = M₂.mult s(a, b)
  rw [glueCast₂_glueEmb₂, glueCast₂_glueEmb₂]

/-- `gluePart₁` is zero outside the image of `glueEmb₁.sym2Map`. -/
theorem gluePart₁_eq_zero_of_not_mem_image {K n₁ n₂ : ℕ}
    (M₁ : MultiLabeledGraph K n₁) (M₂ : MultiLabeledGraph K n₂)
    (e : Sym2 (Fin ((n₁ + n₂) + K)))
    (h : ¬ ∃ e' : Sym2 (Fin (n₁ + K)), Sym2.map (glueEmb₁ K n₁ n₂) e' = e) :
    gluePart₁ M₁ M₂ e = 0 := by
  refine Sym2.ind (fun a b he => ?_) e h
  show (match glueCast₁ K n₁ n₂ a, glueCast₁ K n₁ n₂ b with
        | some u', some v' => M₁.mult s(u', v')
        | _, _ => 0) = 0
  rcases hca : glueCast₁ K n₁ n₂ a with _ | u_a <;>
    rcases hcb : glueCast₁ K n₁ n₂ b with _ | u_b
  any_goals rfl
  -- Only some/some case remains: derive contradiction from `he`
  exfalso
  apply he
  have ha_eq : (glueEmb₁ K n₁ n₂ u_a) = a := by
    apply Fin.ext
    have hac : a.val < n₁ + K := by
      simp only [glueCast₁] at hca; split_ifs at hca with h_; · exact h_
    have huval : u_a.val = a.val := by
      simp only [glueCast₁, dif_pos hac] at hca
      injection hca with hu
      exact (congr_arg Fin.val hu).symm
    show u_a.val = a.val
    exact huval
  have hb_eq : (glueEmb₁ K n₁ n₂ u_b) = b := by
    apply Fin.ext
    have hbc : b.val < n₁ + K := by
      simp only [glueCast₁] at hcb; split_ifs at hcb with h_; · exact h_
    have huval : u_b.val = b.val := by
      simp only [glueCast₁, dif_pos hbc] at hcb
      injection hcb with hu
      exact (congr_arg Fin.val hu).symm
    show u_b.val = b.val
    exact huval
  exact ⟨s(u_a, u_b), by rw [Sym2.map_pair_eq, ha_eq, hb_eq]⟩

/-- `gluePart₂` is zero outside the image of `glueEmb₂.sym2Map`. -/
theorem gluePart₂_eq_zero_of_not_mem_image {K n₁ n₂ : ℕ}
    (M₁ : MultiLabeledGraph K n₁) (M₂ : MultiLabeledGraph K n₂)
    (e : Sym2 (Fin ((n₁ + n₂) + K)))
    (h : ¬ ∃ e' : Sym2 (Fin (n₂ + K)), Sym2.map (glueEmb₂ K n₁ n₂) e' = e) :
    gluePart₂ M₁ M₂ e = 0 := by
  refine Sym2.ind (fun a b he => ?_) e h
  show (match glueCast₂ K n₁ n₂ a, glueCast₂ K n₁ n₂ b with
        | some u', some v' => M₂.mult s(u', v')
        | _, _ => 0) = 0
  rcases hca : glueCast₂ K n₁ n₂ a with _ | u_a <;>
    rcases hcb : glueCast₂ K n₁ n₂ b with _ | u_b
  any_goals rfl
  exfalso
  apply he
  -- For each non-none case in hca: either a.val < K and u_a.val = a.val,
  -- or a.val ≥ n₁ + K and u_a.val = a.val - n₁.
  have ha_eq : (glueEmb₂ K n₁ n₂ u_a) = a := by
    apply Fin.ext
    by_cases hak : a.val < K
    · -- u_a.val = a.val
      have huv : u_a.val = a.val := by
        simp only [glueCast₂, dif_pos hak] at hca
        injection hca with hu; exact (congr_arg Fin.val hu).symm
      have hua : u_a.val < K := by omega
      show (glueEmb₂ K n₁ n₂ u_a).val = a.val
      simp only [glueEmb₂, Function.Embedding.coeFn_mk, dif_pos hua]
      omega
    · -- a.val ≥ K, then we must have a.val ≥ n₁ + K (else cast₂ = none).
      have hageK : ¬ a.val < K := hak
      simp only [glueCast₂, dif_neg hageK] at hca
      split_ifs at hca with hak2
      · injection hca with hu
        -- u_a.val = a.val - n₁
        have huv : u_a.val = a.val - n₁ := (congr_arg Fin.val hu).symm
        -- a.val ≥ n₁ + K so a.val - n₁ ≥ K, hence u_a.val ≥ K
        have hua : ¬ u_a.val < K := by omega
        show (glueEmb₂ K n₁ n₂ u_a).val = a.val
        simp only [glueEmb₂, Function.Embedding.coeFn_mk, dif_neg hua]
        omega
  have hb_eq : (glueEmb₂ K n₁ n₂ u_b) = b := by
    apply Fin.ext
    by_cases hbk : b.val < K
    · have huv : u_b.val = b.val := by
        simp only [glueCast₂, dif_pos hbk] at hcb
        injection hcb with hu; exact (congr_arg Fin.val hu).symm
      have hub : u_b.val < K := by omega
      show (glueEmb₂ K n₁ n₂ u_b).val = b.val
      simp only [glueEmb₂, Function.Embedding.coeFn_mk, dif_pos hub]
      omega
    · have hbgeK : ¬ b.val < K := hbk
      simp only [glueCast₂, dif_neg hbgeK] at hcb
      split_ifs at hcb with hbk2
      · injection hcb with hu
        have huv : u_b.val = b.val - n₁ := (congr_arg Fin.val hu).symm
        have hub : ¬ u_b.val < K := by omega
        show (glueEmb₂ K n₁ n₂ u_b).val = b.val
        simp only [glueEmb₂, Function.Embedding.coeFn_mk, dif_neg hub]
        omega
  exact ⟨s(u_a, u_b), by rw [Sym2.map_pair_eq, ha_eq, hb_eq]⟩

/-- **Sym2 product over `glueEmb₁` factors via prod over `Sym2 (Fin (n₁ + K))`.**
For any function `g : Sym2 (Fin ((n₁+n₂)+K)) → ℝ` that equals `1` outside the
image of `Sym2.map (glueEmb₁ ...)`, the product over `Sym2 (Fin ((n₁+n₂)+K))`
equals the product over `Sym2 (Fin (n₁ + K))` after pulling back through
`glueEmb₁.sym2Map`. -/
private theorem prod_Sym2_emb₁_factor {K n₁ n₂ : ℕ} (g : Sym2 (Fin ((n₁ + n₂) + K)) → ℝ)
    (h_one : ∀ e : Sym2 (Fin ((n₁ + n₂) + K)),
      e ∉ Finset.map (glueEmb₁ K n₁ n₂).sym2Map (Finset.univ : Finset (Sym2 (Fin (n₁ + K)))) →
      g e = 1) :
    ∏ e : Sym2 (Fin ((n₁ + n₂) + K)), g e =
    ∏ e' : Sym2 (Fin (n₁ + K)), g (Sym2.map (glueEmb₁ K n₁ n₂) e') := by
  have h1 := Finset.prod_map (Finset.univ : Finset (Sym2 (Fin (n₁ + K))))
              (glueEmb₁ K n₁ n₂).sym2Map g
  simp only [Function.Embedding.sym2Map_apply] at h1
  rw [← h1]
  exact (Finset.prod_subset (Finset.subset_univ _) (fun e _ he => h_one e he)).symm

private theorem prod_Sym2_emb₂_factor {K n₁ n₂ : ℕ} (g : Sym2 (Fin ((n₁ + n₂) + K)) → ℝ)
    (h_one : ∀ e : Sym2 (Fin ((n₁ + n₂) + K)),
      e ∉ Finset.map (glueEmb₂ K n₁ n₂).sym2Map (Finset.univ : Finset (Sym2 (Fin (n₂ + K)))) →
      g e = 1) :
    ∏ e : Sym2 (Fin ((n₁ + n₂) + K)), g e =
    ∏ e' : Sym2 (Fin (n₂ + K)), g (Sym2.map (glueEmb₂ K n₁ n₂) e') := by
  have h1 := Finset.prod_map (Finset.univ : Finset (Sym2 (Fin (n₂ + K))))
              (glueEmb₂ K n₁ n₂).sym2Map g
  simp only [Function.Embedding.sym2Map_apply] at h1
  rw [← h1]
  exact (Finset.prod_subset (Finset.subset_univ _) (fun e _ he => h_one e he)).symm

/-- **Disjoint glue factorization** of multigraph evaluations.

Lovász's F₁F₂ product (multigraph version): the evaluation of a glued multigraph
factors as the product of evaluations. Generalizes `labeledEvalK_glue` from
SimpleGraph to MultiLabeledGraph (with multiplicities). The proof factors over
σ-sums via `sum_piFinAdd_factor`, the W-products via `Fin.prod_univ_add`, and
the Sym2 B-products via `pow_add` + `prod_Sym2_embᵢ_factor`. -/
theorem multiLabeledEvalK_glue {T K n₁ n₂ : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (M₁ : MultiLabeledGraph K n₁) (M₂ : MultiLabeledGraph K n₂)
    (φ : Fin K → Fin T) :
    multiLabeledEvalK K (n₁ + n₂) (M₁.glue M₂) B W φ =
      multiLabeledEvalK K n₁ M₁ B W φ * multiLabeledEvalK K n₂ M₂ B W φ := by
  unfold multiLabeledEvalK
  -- Factor RHS into a single sum via sum_piFinAdd_factor
  rw [← sum_piFinAdd_factor
    (f := fun x : Fin n₁ → Fin T =>
      let τ : Fin (n₁ + K) → Fin T := fun v =>
        if h : (v : ℕ) < K then φ ⟨v, h⟩ else x ⟨v - K, by have := v.isLt; omega⟩
      (∏ v : Fin n₁, W (x v)) *
      ∏ e : Sym2 (Fin (n₁ + K)),
        B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ M₁.mult e)
    (g := fun x : Fin n₂ → Fin T =>
      let τ : Fin (n₂ + K) → Fin T := fun v =>
        if h : (v : ℕ) < K then φ ⟨v, h⟩ else x ⟨v - K, by have := v.isLt; omega⟩
      (∏ v : Fin n₂, W (x v)) *
      ∏ e : Sym2 (Fin (n₂ + K)),
        B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ M₂.mult e)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  -- σ : Fin (n₁ + n₂) → Fin T. Define τ_glue, τ₁, τ₂ as the colorings.
  set σ₁ : Fin n₁ → Fin T := fun j => σ (Fin.castAdd n₂ j) with hσ₁
  set σ₂ : Fin n₂ → Fin T := fun j => σ (Fin.natAdd n₁ j) with hσ₂
  -- W-product factorization
  have h_wt : ∏ v : Fin (n₁ + n₂), W (σ v) =
      (∏ v : Fin n₁, W (σ₁ v)) * (∏ v : Fin n₂, W (σ₂ v)) := by
    rw [hσ₁, hσ₂]
    exact Fin.prod_univ_add (fun v => W (σ v))
  -- Define the colorings as let-bindings
  set τ_glue : Fin ((n₁ + n₂) + K) → Fin T := fun v =>
    if h : (v : ℕ) < K then φ ⟨v, h⟩ else σ ⟨v - K, by have := v.isLt; omega⟩
    with hτ_glue
  set τ₁ : Fin (n₁ + K) → Fin T := fun v =>
    if h : (v : ℕ) < K then φ ⟨v, h⟩ else σ₁ ⟨v - K, by have := v.isLt; omega⟩
    with hτ₁
  set τ₂ : Fin (n₂ + K) → Fin T := fun v =>
    if h : (v : ℕ) < K then φ ⟨v, h⟩ else σ₂ ⟨v - K, by have := v.isLt; omega⟩
    with hτ₂
  -- Coloring relation: τ_glue ∘ glueEmb₁ = τ₁ and τ_glue ∘ glueEmb₂ = τ₂
  have h_τ₁ : ∀ v : Fin (n₁ + K), τ_glue (glueEmb₁ K n₁ n₂ v) = τ₁ v := by
    intro v
    have hvlt : v.val < n₁ + n₂ + K := by have := v.isLt; omega
    simp only [τ_glue, τ₁, glueEmb₁, Function.Embedding.coeFn_mk]
    by_cases hv : v.val < K
    · -- label: both branches yield φ ⟨v, hv⟩
      have hv' : ((⟨v.val, hvlt⟩ : Fin ((n₁ + n₂) + K)) : ℕ) < K := hv
      rw [dif_pos hv', dif_pos hv]
    · have hv' : ¬ ((⟨v.val, hvlt⟩ : Fin ((n₁ + n₂) + K)) : ℕ) < K := hv
      rw [dif_neg hv', dif_neg hv]
      simp only [σ₁]
      apply congr_arg σ
      apply Fin.ext
      simp
  have h_τ₂ : ∀ v : Fin (n₂ + K), τ_glue (glueEmb₂ K n₁ n₂ v) = τ₂ v := by
    intro v
    have hvlt₁ : v.val < n₁ + n₂ + K := by have := v.isLt; omega
    have hvlt₂ : n₁ + v.val < n₁ + n₂ + K := by have := v.isLt; omega
    by_cases hv : v.val < K
    · -- v is a label
      have hemb : glueEmb₂ K n₁ n₂ v = ⟨v.val, hvlt₁⟩ := by
        show (if h : v.val < K then (⟨v.val, by omega⟩ : Fin _)
              else ⟨n₁ + v.val, by have := v.isLt; omega⟩) = _
        rw [dif_pos hv]
      rw [hemb]
      show τ_glue ⟨v.val, hvlt₁⟩ = τ₂ v
      rw [hτ_glue, hτ₂]
      simp only [dif_pos (show ((⟨v.val, hvlt₁⟩ : Fin ((n₁+n₂)+K)) : ℕ) < K from hv)]
    · -- v is M₂-unlabeled
      have hemb : glueEmb₂ K n₁ n₂ v = ⟨n₁ + v.val, hvlt₂⟩ := by
        show (if h : v.val < K then (⟨v.val, by omega⟩ : Fin _)
              else ⟨n₁ + v.val, by have := v.isLt; omega⟩) = _
        rw [dif_neg hv]
      rw [hemb]
      show τ_glue ⟨n₁ + v.val, hvlt₂⟩ = τ₂ v
      rw [hτ_glue, hτ₂]
      have hv1 : ¬ ((⟨n₁ + v.val, hvlt₂⟩ : Fin ((n₁ + n₂) + K)) : ℕ) < K := by
        show ¬ n₁ + v.val < K; omega
      simp only [dif_neg hv1, dif_neg hv]
      simp only [σ₂]
      apply congr_arg σ
      apply Fin.ext
      simp
      omega
  -- Sym2 product factorization via additivity of glue.mult
  have h_sym2 : (∏ e : Sym2 (Fin ((n₁ + n₂) + K)),
      B (τ_glue (Quot.out e).1) (τ_glue (Quot.out e).2) ^ (M₁.glue M₂).mult e) =
      (∏ e : Sym2 (Fin (n₁ + K)),
        B (τ₁ (Quot.out e).1) (τ₁ (Quot.out e).2) ^ M₁.mult e) *
      (∏ e : Sym2 (Fin (n₂ + K)),
        B (τ₂ (Quot.out e).1) (τ₂ (Quot.out e).2) ^ M₂.mult e) := by
    -- Use the additive split: (M₁.glue M₂).mult = gluePart₁ + gluePart₂
    have h_add : ∀ e, (M₁.glue M₂).mult e = gluePart₁ M₁ M₂ e + gluePart₂ M₁ M₂ e :=
      M₁.glue_mult_eq_add M₂
    -- Factor product via pow_add
    have h_split : (∏ e : Sym2 (Fin ((n₁ + n₂) + K)),
        B (τ_glue (Quot.out e).1) (τ_glue (Quot.out e).2) ^ (M₁.glue M₂).mult e) =
        (∏ e : Sym2 (Fin ((n₁ + n₂) + K)),
          B (τ_glue (Quot.out e).1) (τ_glue (Quot.out e).2) ^ gluePart₁ M₁ M₂ e) *
        (∏ e : Sym2 (Fin ((n₁ + n₂) + K)),
          B (τ_glue (Quot.out e).1) (τ_glue (Quot.out e).2) ^ gluePart₂ M₁ M₂ e) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun e _ => ?_
      rw [h_add e, pow_add]
    rw [h_split]
    -- Match each side with prod_Sym2_embᵢ_factor
    congr 1
    · -- M₁ side
      rw [prod_Sym2_emb₁_factor (g := fun e =>
          B (τ_glue (Quot.out e).1) (τ_glue (Quot.out e).2) ^ gluePart₁ M₁ M₂ e)]
      · -- The pulled-back form equals the M₁ Sym2 product
        refine Finset.prod_congr rfl fun e _ => ?_
        refine Sym2.ind (fun a b => ?_) e
        rw [Sym2.map_pair_eq, gluePart₁_emb₁]
        -- Need: B^M₁.mult s(a,b) at τ_glue ∘ emb₁ pair equals at τ₁ pair
        rw [B_pow_quot_out_eq hB τ_glue (glueEmb₁ K n₁ n₂ a) (glueEmb₁ K n₁ n₂ b)]
        rw [B_pow_quot_out_eq hB τ₁ a b]
        rw [h_τ₁, h_τ₁]
      · -- Outside the image, gluePart₁ = 0, so B^0 = 1
        intro e he
        have h0 : gluePart₁ M₁ M₂ e = 0 := by
          apply gluePart₁_eq_zero_of_not_mem_image
          intro ⟨e', hmap⟩
          apply he
          rw [Finset.mem_map]
          refine ⟨e', Finset.mem_univ _, ?_⟩
          rw [Function.Embedding.sym2Map_apply, hmap]
        rw [h0]; exact pow_zero _
    · -- M₂ side (analogous)
      rw [prod_Sym2_emb₂_factor (g := fun e =>
          B (τ_glue (Quot.out e).1) (τ_glue (Quot.out e).2) ^ gluePart₂ M₁ M₂ e)]
      · refine Finset.prod_congr rfl fun e _ => ?_
        refine Sym2.ind (fun a b => ?_) e
        rw [Sym2.map_pair_eq, gluePart₂_emb₂]
        rw [B_pow_quot_out_eq hB τ_glue (glueEmb₂ K n₁ n₂ a) (glueEmb₂ K n₁ n₂ b)]
        rw [B_pow_quot_out_eq hB τ₂ a b]
        rw [h_τ₂, h_τ₂]
      · intro e he
        have h0 : gluePart₂ M₁ M₂ e = 0 := by
          apply gluePart₂_eq_zero_of_not_mem_image
          intro ⟨e', hmap⟩
          apply he
          rw [Finset.mem_map]
          refine ⟨e', Finset.mem_univ _, ?_⟩
          rw [Function.Embedding.sym2Map_apply, hmap]
        rw [h0]; exact pow_zero _
  -- Combine W-product factorization and Sym2 product factorization
  show (∏ v : Fin (n₁ + n₂), W (σ v)) *
       (∏ e : Sym2 (Fin ((n₁ + n₂) + K)),
         B (τ_glue (Quot.out e).1) (τ_glue (Quot.out e).2) ^ (M₁.glue M₂).mult e) =
       _ * _
  rw [h_wt, h_sym2]
  ring

/-! ### §3.5 — Trace operator (Lovász eq. 6) -/

/-- **Trace operator on multigraphs.** Folds the last label of a `(K+1)`-labeled
multigraph into a new unlabeled vertex, yielding a `K`-labeled multigraph with
`n + 1` unlabeled vertices.

Vertex spaces `Fin (n + (K + 1))` and `Fin ((n + 1) + K)` have the same
cardinality; the multiplicity is pulled back via the val-preserving
`Fin.cast`. -/
def MultiLabeledGraph.trace {K n : ℕ}
    (M : MultiLabeledGraph (K + 1) n) : MultiLabeledGraph K (n + 1) where
  mult e := M.mult (Sym2.map (Fin.cast (show (n + 1) + K = n + (K + 1) by omega)) e)
  multNoLoop x := by
    rw [Sym2.map_pair_eq]
    exact M.multNoLoop _

/-- **Promotion** (section of `trace`): from `MultiLabeledGraph K (n+1)` build
`MultiLabeledGraph (K+1) n` by reindexing the val-equal vertex space via the
inverse cast. Round-trip property: `M.promote.trace = M` (definitionally up
to `Sym2.map_id`). -/
def MultiLabeledGraph.promote {K n : ℕ}
    (M : MultiLabeledGraph K (n + 1)) : MultiLabeledGraph (K + 1) n where
  mult e := M.mult (Sym2.map (Fin.cast (show n + (K + 1) = (n + 1) + K by omega)) e)
  multNoLoop x := by
    rw [Sym2.map_pair_eq]
    exact M.multNoLoop _

/-- **Trace-promote round-trip**: closing the last label of a promoted
multigraph recovers the original. Both sides have val-equal vertex spaces
`Fin ((n+1)+K)`; multiplicities agree pointwise via the cast composition
identity. -/
theorem MultiLabeledGraph.trace_promote {K n : ℕ}
    (M : MultiLabeledGraph K (n + 1)) : M.promote.trace = M := by
  have hmult : ∀ e, M.promote.trace.mult e = M.mult e := by
    intro e
    show M.mult (Sym2.map (Fin.cast _) (Sym2.map (Fin.cast _) e)) = M.mult e
    rw [Sym2.map_map]
    have h_id : (Fin.cast (show n + (K + 1) = (n + 1) + K by omega)) ∘
                (Fin.cast (show (n + 1) + K = n + (K + 1) by omega)) = id := by
      funext x
      apply Fin.ext
      rfl
    rw [h_id, Sym2.map_id, id_eq]
  rcases h : M with ⟨m, mn⟩
  show MultiLabeledGraph.mk _ _ = MultiLabeledGraph.mk _ _
  congr 1
  funext e
  have := hmult e
  rw [h] at this
  exact this

/-- **Trace-closure identity** (Lovász eq. 6, p. 7).

Summing `multiLabeledEvalK (K+1) n M B W` over the last label `t` of a
`(K+1)`-tuple `Fin.snoc φ t`, weighted by `W(t)`, equals
`multiLabeledEvalK K (n+1) M.trace B W φ` — i.e., closing the last label
into a new unlabeled vertex.

Multigraph analog of `labeledEvalK_sum_last_label`
(`MatrixDetermination.lean:4906`). Requires `B` symmetric since the
vertex-space cast `Fin ((n+1)+K) ↔ Fin (n+(K+1))` reindexes Sym2 pairs
through `Sym2.map (Fin.cast _)` and `Quot.out` may pick swapped
orientations. -/
theorem multiLabeledEvalK_sum_last_label {T K n : ℕ}
    (M : MultiLabeledGraph (K + 1) n) (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (φ : Fin K → Fin T) :
    ∑ t : Fin T, W t * multiLabeledEvalK (K + 1) n M B W (Fin.snoc φ t) =
    multiLabeledEvalK K (n + 1) M.trace B W φ := by
  -- Unfold both sides.
  simp only [multiLabeledEvalK]
  -- LHS: ∑ t, W t * ∑ σ, (∏ W(σ v)) * ∏ B(τ_{K+1} ...) ^ M.mult e
  -- RHS: ∑ σ', (∏ W(σ' v)) * ∏ B(τ_K ...) ^ M.trace.mult e
  -- (RHS Sym2 product is over Fin ((n+1)+K), via M.trace.)
  -- Bijection: σ' = Fin.cons t σ.
  conv_rhs =>
    rw [(Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => Fin T)) _).symm]
  simp only [Fin.consEquiv_apply]
  rw [Fintype.sum_prod_type]
  congr 1; ext t
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  -- Weight product on RHS: ∏ W((Fin.cons t σ) v) = W(t) * ∏ W(σ v)
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [show W t * ((∏ v : Fin n, W (σ v)) *
        ∏ e : Sym2 (Fin (n + (K + 1))),
          B _ _ ^ M.mult e) =
      (W t * ∏ v : Fin n, W (σ v)) *
        ∏ e : Sym2 (Fin (n + (K + 1))),
          B _ _ ^ M.mult e from by ring]
  congr 1
  -- Sym2 product equality. The LHS is over Sym2 (Fin (n + (K+1))) with M.mult e;
  -- the RHS is over Sym2 (Fin ((n+1) + K)) with M.trace.mult e' = M.mult (Sym2.map cast e').
  -- Reindex LHS via the bijection e' ↦ Sym2.map (Fin.cast h_eq) e'.
  set h_eq : (n + 1) + K = n + (K + 1) := by omega
  -- The Sym2 cast as an Equiv.
  let e_fin : Fin ((n + 1) + K) ≃ Fin (n + (K + 1)) :=
    (Fin.castOrderIso h_eq).toEquiv
  let e_sym2 : Sym2 (Fin ((n + 1) + K)) ≃ Sym2 (Fin (n + (K + 1))) :=
    { toFun := Sym2.map e_fin
      invFun := Sym2.map e_fin.symm
      left_inv := fun x => by
        rw [Sym2.map_map]
        have h_id : e_fin.symm ∘ e_fin = id := by ext; simp
        rw [h_id, Sym2.map_id, id_eq]
      right_inv := fun x => by
        rw [Sym2.map_map]
        have h_id : e_fin ∘ e_fin.symm = id := by ext; simp
        rw [h_id, Sym2.map_id, id_eq] }
  -- Reindex LHS via e_sym2: apply Equiv.prod_comp.
  rw [show
      (∏ e : Sym2 (Fin (n + (K + 1))),
        B ((fun v : Fin (n + (K + 1)) =>
            if h : (v : ℕ) < K + 1 then (Fin.snoc (α := fun _ => Fin T) φ t) ⟨v, h⟩
            else σ ⟨v.val - (K + 1), by have := v.isLt; omega⟩)
            (Quot.out e).1)
          ((fun v : Fin (n + (K + 1)) =>
            if h : (v : ℕ) < K + 1 then (Fin.snoc (α := fun _ => Fin T) φ t) ⟨v, h⟩
            else σ ⟨v.val - (K + 1), by have := v.isLt; omega⟩)
            (Quot.out e).2) ^ M.mult e) =
      ∏ e' : Sym2 (Fin ((n + 1) + K)),
        B ((fun v : Fin (n + (K + 1)) =>
            if h : (v : ℕ) < K + 1 then (Fin.snoc (α := fun _ => Fin T) φ t) ⟨v, h⟩
            else σ ⟨v.val - (K + 1), by have := v.isLt; omega⟩)
            (Quot.out (e_sym2 e')).1)
          ((fun v : Fin (n + (K + 1)) =>
            if h : (v : ℕ) < K + 1 then (Fin.snoc (α := fun _ => Fin T) φ t) ⟨v, h⟩
            else σ ⟨v.val - (K + 1), by have := v.isLt; omega⟩)
            (Quot.out (e_sym2 e')).2) ^ M.mult (e_sym2 e') from
    (Equiv.prod_comp e_sym2 _).symm]
  -- Now both sides are products over Sym2 (Fin ((n+1) + K)).
  refine Finset.prod_congr rfl fun e _ => ?_
  -- M.trace.mult e = M.mult (e_sym2 e) by definition.
  have hmult : M.trace.mult e = M.mult (e_sym2 e) := by
    show M.mult (Sym2.map (Fin.cast h_eq) e) = M.mult (Sym2.map e_fin e)
    rfl
  rw [hmult]
  congr 1
  -- B-arg equality up to symmetry: case-split on Quot.out orientations.
  refine Sym2.ind (fun a b => ?_) e
  -- e_sym2 s(a, b) = s(Fin.cast h_eq a, Fin.cast h_eq b).
  have h_es : e_sym2 s(a, b) = s(Fin.cast h_eq a, Fin.cast h_eq b) := by
    show Sym2.map e_fin s(a, b) = _
    rw [Sym2.map_pair_eq]
    rfl
  rw [h_es]
  -- Quot.out orientations on both sides.
  set p_lhs := Quot.out s(Fin.cast h_eq a, Fin.cast h_eq b)
  set p_rhs := Quot.out s(a, b)
  have h_lhs : (p_lhs.1 = Fin.cast h_eq a ∧ p_lhs.2 = Fin.cast h_eq b) ∨
               (p_lhs.1 = Fin.cast h_eq b ∧ p_lhs.2 = Fin.cast h_eq a) := by
    have := Sym2.eq_iff.mp (Quot.out_eq s(Fin.cast h_eq a, Fin.cast h_eq b))
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨h1, h2⟩
    · right; exact ⟨h1, h2⟩
  have h_rhs : (p_rhs.1 = a ∧ p_rhs.2 = b) ∨ (p_rhs.1 = b ∧ p_rhs.2 = a) := by
    have := Sym2.eq_iff.mp (Quot.out_eq s(a, b))
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨h1, h2⟩
    · right; exact ⟨h1, h2⟩
  -- Pointwise τ equality on cast vertices.
  have hτ : ∀ v : Fin ((n + 1) + K),
      (if h : ((Fin.cast h_eq v) : ℕ) < K + 1
        then (Fin.snoc (α := fun _ => Fin T) φ t) ⟨(Fin.cast h_eq v), h⟩
        else σ ⟨(Fin.cast h_eq v).val - (K + 1),
                by have := (Fin.cast h_eq v).isLt; omega⟩) =
      (if h : ((v : Fin ((n + 1) + K)) : ℕ) < K
        then φ ⟨v, h⟩
        else (Fin.cons (α := fun _ => Fin T) t σ)
              ⟨v.val - K, by have := v.isLt; omega⟩) := by
    intro v
    have hv_eq : ((Fin.cast h_eq v) : ℕ) = v.val := Fin.val_cast _ _
    by_cases hvK : v.val < K
    · have hvK1 : v.val < K + 1 := by omega
      have h1 : ((Fin.cast h_eq v) : ℕ) < K + 1 := by rw [hv_eq]; exact hvK1
      rw [dif_pos h1, dif_pos hvK]
      have hrec : (⟨((Fin.cast h_eq v) : ℕ), h1⟩ : Fin (K + 1)) =
                  (⟨v.val, hvK⟩ : Fin K).castSucc := by
        apply Fin.ext
        show ((Fin.cast h_eq v) : ℕ) = v.val
        exact hv_eq
      rw [hrec, Fin.snoc_castSucc]
    by_cases hvK1 : v.val = K
    · have h1 : ((Fin.cast h_eq v) : ℕ) < K + 1 := by rw [hv_eq]; omega
      rw [dif_pos h1, dif_neg hvK]
      have hlast : (⟨((Fin.cast h_eq v) : ℕ), h1⟩ : Fin (K + 1)) =
                   Fin.last K := by
        apply Fin.ext; show ((Fin.cast h_eq v) : ℕ) = K
        rw [hv_eq]; exact hvK1
      rw [hlast, Fin.snoc_last]
      have hzero : (⟨v.val - K, by have := v.isLt; omega⟩ : Fin (n + 1)) =
                   (0 : Fin (n + 1)) := by
        apply Fin.ext; show v.val - K = 0; omega
      rw [hzero]; rfl
    · have h1 : ¬ ((Fin.cast h_eq v) : ℕ) < K + 1 := by
        rw [hv_eq]; omega
      rw [dif_neg h1, dif_neg hvK]
      have hsucc : (⟨v.val - K, by have := v.isLt; omega⟩ : Fin (n + 1)) =
                   (⟨v.val - K - 1, by have := v.isLt; omega⟩ : Fin n).succ := by
        apply Fin.ext; simp; omega
      rw [hsucc, Fin.cons_succ]
      apply congr_arg σ
      apply Fin.ext
      show ((Fin.cast h_eq v) : ℕ) - (K + 1) = v.val - K - 1
      rw [hv_eq]; omega
  -- Apply hτ at the Quot.out endpoints; use B symmetry to handle swapped orientations.
  -- Beta-reduce the lambda first.
  beta_reduce
  rcases h_lhs with ⟨hL1, hL2⟩ | ⟨hL1, hL2⟩ <;>
    rcases h_rhs with ⟨hR1, hR2⟩ | ⟨hR1, hR2⟩ <;>
    rw [hL1, hL2, hR1, hR2, hτ a, hτ b] <;>
    first
    | rfl
    | exact hB _ _

/-- **Promote-unfolding identity**: a multigraph evaluation at level `(K, n+1)`
unfolds into a `W`-weighted sum (over the value `t` of the new label) of the
promoted multigraph at level `(K+1, n)`. Direct corollary of
`multiLabeledEvalK_sum_last_label` and `MultiLabeledGraph.trace_promote`. -/
theorem multiLabeledEvalK_promote_unfold {T K n : ℕ}
    (M : MultiLabeledGraph K (n + 1)) (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (ξ : Fin K → Fin T) :
    multiLabeledEvalK K (n + 1) M B W ξ =
    ∑ t : Fin T, W t * multiLabeledEvalK (K + 1) n M.promote B W (Fin.snoc ξ t) := by
  rw [multiLabeledEvalK_sum_last_label M.promote B hB W ξ]
  rw [MultiLabeledGraph.trace_promote]

/-! ### §3.5 — Automorphism-invariance of multigraph evaluation

A bounded preliminary: any `(B, W)`-automorphism `σ : Fin T ≃ Fin T`
acts trivially on multigraph evaluations (substitute `τ ∘ σ` in the
σ-sum). This is the standard symmetry observation, NOT the bridge
content (which would say simple-graph `tupleEquiv` implies multi
evaluations agree).

The orbit-based corollary: if `ξ' = σ ∘ ξ` for some aut σ, then
`multiEval M ξ = multiEval M ξ'`. This is bounded (~30 lines) and
serves as a stepping-stone for the full bridge. -/

/-- **Automorphism invariance of `multiLabeledEvalK`**.

If `σ : Fin T ≃ Fin T` is a `(B, W)`-automorphism (preserves W and B),
then for any multigraph `M` and any labeled tuple `φ`,
`multiLabeledEvalK M (σ ∘ φ) = multiLabeledEvalK M φ`. -/
theorem multiLabeledEvalK_aut_invariant {T K n : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (M : MultiLabeledGraph K n)
    (σ : Equiv.Perm (Fin T))
    (hσ_W : ∀ i, W (σ i) = W i)
    (hσ_B : ∀ i j, B (σ i) (σ j) = B i j)
    (φ : Fin K → Fin T) :
    multiLabeledEvalK K n M B W (σ ∘ φ) =
    multiLabeledEvalK K n M B W φ := by
  unfold multiLabeledEvalK
  rw [← Equiv.sum_comp (Equiv.arrowCongr (Equiv.refl (Fin n)) σ)]
  refine Finset.sum_congr rfl fun σ_inner _ => ?_
  -- Per-σ-inner integrand factor equality. Use τ-parametric helpers
  -- to avoid the let-binding unification issue.
  have hW_eq : ∀ v : Fin n,
      W (((Equiv.arrowCongr (Equiv.refl (Fin n)) σ) σ_inner) v) = W (σ_inner v) := by
    intro v; show W (σ (σ_inner v)) = W (σ_inner v); exact hσ_W _
  have hB_eq : ∀ τ_L τ_R : Fin (n + K) → Fin T,
      (∀ v, τ_L v = σ (τ_R v)) →
      (∏ e : Sym2 (Fin (n + K)),
        B (τ_L (Quot.out e).1) (τ_L (Quot.out e).2) ^ M.mult e) =
      (∏ e : Sym2 (Fin (n + K)),
        B (τ_R (Quot.out e).1) (τ_R (Quot.out e).2) ^ M.mult e) := by
    intro τ_L τ_R hτ
    refine Finset.prod_congr rfl fun e _ => ?_
    congr 1
    rw [hτ, hτ]; exact hσ_B _ _
  -- Bind τ_L and τ_R via `let` so they unfold via `show` for `rfl` checks.
  let τ_R : Fin (n + K) → Fin T := fun v =>
    if h : (v : ℕ) < K then φ ⟨v, h⟩
    else σ_inner ⟨v - K, by have := v.isLt; omega⟩
  let τ_L : Fin (n + K) → Fin T := fun v =>
    if h : (v : ℕ) < K then (σ ∘ φ) ⟨v, h⟩
    else ((Equiv.arrowCongr (Equiv.refl (Fin n)) σ) σ_inner)
            ⟨v - K, by have := v.isLt; omega⟩
  have hτ_pt : ∀ v : Fin (n + K), τ_L v = σ (τ_R v) := by
    intro v
    by_cases hv : (v : ℕ) < K
    · show (if h : (v : ℕ) < K then (σ ∘ φ) ⟨v, h⟩ else _) =
            σ (if h : (v : ℕ) < K then φ ⟨v, h⟩ else _)
      rw [dif_pos hv, dif_pos hv]
      rfl
    · show (if h : (v : ℕ) < K then _ else
              ((Equiv.arrowCongr (Equiv.refl (Fin n)) σ) σ_inner)
                ⟨v - K, by have := v.isLt; omega⟩) =
            σ (if h : (v : ℕ) < K then _ else
                σ_inner ⟨v - K, by have := v.isLt; omega⟩)
      rw [dif_neg hv, dif_neg hv]
      rfl
  -- Goal: (∏ W (σ∘σ_inner)) * (∏ B^M.mult on τ_L) = (∏ W σ_inner) * (∏ B^M.mult on τ_R)
  change (∏ v : Fin n, W (((Equiv.arrowCongr (Equiv.refl (Fin n)) σ) σ_inner) v)) *
       (∏ e : Sym2 (Fin (n + K)),
         B (τ_L (Quot.out e).1) (τ_L (Quot.out e).2) ^ M.mult e) =
       (∏ v : Fin n, W (σ_inner v)) *
       (∏ e : Sym2 (Fin (n + K)),
         B (τ_R (Quot.out e).1) (τ_R (Quot.out e).2) ^ M.mult e)
  rw [Finset.prod_congr rfl (fun v _ => hW_eq v), hB_eq τ_L τ_R hτ_pt]

/-- **Orbit-based invariance**: corollary of `multiLabeledEvalK_aut_invariant`.
If `ξ' = σ ∘ ξ` for some `(B, W)`-automorphism `σ`, multigraph
evaluations agree. -/
theorem multiLabeledEvalK_orbit_invariant {T K n : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (M : MultiLabeledGraph K n)
    {ξ ξ' : Fin K → Fin T}
    (h : ∃ σ : Equiv.Perm (Fin T),
      (∀ i, W (σ i) = W i) ∧ (∀ i j, B (σ i) (σ j) = B i j) ∧
      (∀ i, ξ' i = σ (ξ i))) :
    multiLabeledEvalK K n M B W ξ = multiLabeledEvalK K n M B W ξ' := by
  obtain ⟨σ, hσ_W, hσ_B, hξ'⟩ := h
  have : ξ' = σ ∘ ξ := funext hξ'
  rw [this]
  exact (multiLabeledEvalK_aut_invariant B W M σ hσ_W hσ_B ξ).symm

/-- **Bridge for n = 0** (label-only multigraphs). The simplest non-trivial
case: when M has no unlabeled vertices, `multiLabeledEvalK` reduces to
a product of B-power factors over `Sym2 (Fin K)`. The simple-graph
`tupleEquiv` hypothesis (h_simple) applied to single-edge graphs gives
B-equality at each non-loop pair, and `multNoLoop` handles the diagonal. -/
theorem multiLabeledEvalK_tupleEquiv_invariant_n_zero {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (M : MultiLabeledGraph K 0)
    {ξ ξ' : Fin K → Fin T}
    (h_simple : ∀ (n' : ℕ) (F : SimpleGraph (Fin (n' + K)))
        [DecidableRel F.Adj],
      ∑ σ : Fin n' → Fin T,
        (let τ : Fin (n' + K) → Fin T := fun v =>
          if h : (v : ℕ) < K then ξ ⟨v, h⟩
          else σ ⟨v - K, by have := v.isLt; omega⟩
        (∏ v : Fin n', W (σ v)) *
        ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2)) =
      ∑ σ : Fin n' → Fin T,
        (let τ : Fin (n' + K) → Fin T := fun v =>
          if h : (v : ℕ) < K then ξ' ⟨v, h⟩
          else σ ⟨v - K, by have := v.isLt; omega⟩
        (∏ v : Fin n', W (σ v)) *
        ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2))) :
    multiLabeledEvalK K 0 M B W ξ = multiLabeledEvalK K 0 M B W ξ' := by
  classical
  -- ── Step 1: per-pair B-equality on labels via single-edge graphs ──
  have h_pair : ∀ a b : Fin K, a ≠ b → B (ξ a) (ξ b) = B (ξ' a) (ξ' b) := by
    intro a b hab
    let u : Fin (0 + K) := ⟨a.val, by have := a.isLt; omega⟩
    let v : Fin (0 + K) := ⟨b.val, by have := b.isLt; omega⟩
    have hne : u ≠ v := by
      simp only [ne_eq, Fin.mk.injEq, u, v]; intro h; apply hab; exact Fin.ext h
    let F : SimpleGraph (Fin (0 + K)) :=
      { Adj := fun a b => (a = u ∧ b = v) ∨ (a = v ∧ b = u)
        symm := fun _ _ h => h.elim (fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩)
                                     (fun ⟨h1, h2⟩ => Or.inl ⟨h2, h1⟩)
        loopless := fun _ h => by
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hne (h1.symm.trans h2)
          · exact hne (h2.symm.trans h1) }
    haveI : DecidableRel F.Adj := Classical.decRel _
    have hedgeFin : F.edgeFinset = {s(u, v)} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr; constructor
      · rw [SimpleGraph.mem_edgeFinset]; exact Or.inl ⟨rfl, rfl⟩
      · intro e he
        rw [SimpleGraph.mem_edgeFinset] at he
        exact Sym2.ind (fun a b (hadj : F.Adj a b) => by
          rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]
          · rw [h1, h2, Sym2.eq_swap]) e he
    have hkey := h_simple 0 F
    rw [hedgeFin, Fintype.sum_unique, Fintype.sum_unique] at hkey
    simp only [Finset.prod_singleton, Finset.univ_eq_empty,
               Finset.prod_empty, one_mul] at hkey
    let τξ : Fin (0 + K) → Fin T := fun x => ξ ⟨x.val, by have := x.isLt; omega⟩
    let τξ' : Fin (0 + K) → Fin T := fun x => ξ' ⟨x.val, by have := x.isLt; omega⟩
    have h_eq_τξ : ∀ x : Fin (0 + K),
        (if h : (x : ℕ) < K then ξ ⟨x.val, h⟩
         else (default : Fin 0 → Fin T) ⟨x - K, by have := x.isLt; omega⟩) = τξ x := by
      intro x; have hx : x.val < K := by have := x.isLt; omega
      simp [hx, τξ]
    have h_eq_τξ' : ∀ x : Fin (0 + K),
        (if h : (x : ℕ) < K then ξ' ⟨x.val, h⟩
         else (default : Fin 0 → Fin T) ⟨x - K, by have := x.isLt; omega⟩) = τξ' x := by
      intro x; have hx : x.val < K := by have := x.isLt; omega
      simp [hx, τξ']
    rw [h_eq_τξ, h_eq_τξ, h_eq_τξ', h_eq_τξ'] at hkey
    rw [B_quot_out_eq hB τξ u v, B_quot_out_eq hB τξ' u v] at hkey
    have hτξ_u : τξ u = ξ a := by show ξ ⟨u.val, _⟩ = ξ a; congr
    have hτξ_v : τξ v = ξ b := by show ξ ⟨v.val, _⟩ = ξ b; congr
    have hτξ'_u : τξ' u = ξ' a := by show ξ' ⟨u.val, _⟩ = ξ' a; congr
    have hτξ'_v : τξ' v = ξ' b := by show ξ' ⟨v.val, _⟩ = ξ' b; congr
    rw [hτξ_u, hτξ_v, hτξ'_u, hτξ'_v] at hkey
    exact hkey
  -- ── Step 2: reduce both sides of the goal via Fintype.sum_unique ──
  have hreduce : ∀ (η : Fin K → Fin T),
      multiLabeledEvalK K 0 M B W η =
      ∏ e : Sym2 (Fin (0 + K)),
        B (η ⟨((Quot.out e).1 : ℕ), by have := (Quot.out e).1.isLt; omega⟩)
          (η ⟨((Quot.out e).2 : ℕ), by have := (Quot.out e).2.isLt; omega⟩) ^ M.mult e := by
    intro η
    unfold multiLabeledEvalK
    rw [Fintype.sum_unique]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    refine Finset.prod_congr rfl fun e _ => ?_
    congr 2
    · show (if h : (((Quot.out e).1 : ℕ)) < K then η ⟨_, h⟩ else _) = _
      have h1_lt : ((Quot.out e).1 : ℕ) < K := by have := (Quot.out e).1.isLt; omega
      rw [dif_pos h1_lt]
    · show (if h : (((Quot.out e).2 : ℕ)) < K then η ⟨_, h⟩ else _) = _
      have h2_lt : ((Quot.out e).2 : ℕ) < K := by have := (Quot.out e).2.isLt; omega
      rw [dif_pos h2_lt]
  rw [hreduce ξ, hreduce ξ']
  -- ── Step 3: per-Sym2-pair argument ──
  refine Finset.prod_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | h x y =>
    by_cases hxy : x = y
    · subst hxy
      -- multNoLoop ⟹ M.mult s(x,x) = 0 ⟹ B^0 = 1 on both sides.
      rw [M.multNoLoop x, pow_zero, pow_zero]
    · -- x ≠ y: route through h_pair on the corresponding Fin K elements.
      let fξ : Fin (0 + K) → Fin T := fun z => ξ ⟨z.val, by have := z.isLt; omega⟩
      let fξ' : Fin (0 + K) → Fin T := fun z => ξ' ⟨z.val, by have := z.isLt; omega⟩
      have h1 : B (ξ ⟨((Quot.out s(x, y)).1 : ℕ),
                    by have := (Quot.out s(x, y)).1.isLt; omega⟩)
                  (ξ ⟨((Quot.out s(x, y)).2 : ℕ),
                    by have := (Quot.out s(x, y)).2.isLt; omega⟩)
              = B (fξ x) (fξ y) := by
        change B (fξ (Quot.out s(x, y)).1) (fξ (Quot.out s(x, y)).2) = B (fξ x) (fξ y)
        exact B_quot_out_eq hB fξ x y
      have h2 : B (ξ' ⟨((Quot.out s(x, y)).1 : ℕ),
                    by have := (Quot.out s(x, y)).1.isLt; omega⟩)
                  (ξ' ⟨((Quot.out s(x, y)).2 : ℕ),
                    by have := (Quot.out s(x, y)).2.isLt; omega⟩)
              = B (fξ' x) (fξ' y) := by
        change B (fξ' (Quot.out s(x, y)).1) (fξ' (Quot.out s(x, y)).2) = B (fξ' x) (fξ' y)
        exact B_quot_out_eq hB fξ' x y
      rw [h1, h2]
      let xK : Fin K := ⟨x.val, by have := x.isLt; omega⟩
      let yK : Fin K := ⟨y.val, by have := y.isLt; omega⟩
      have hxKyK : xK ≠ yK := by
        intro heq; apply hxy
        exact Fin.ext (by simpa [xK, yK, Fin.ext_iff] using heq)
      have hfξx : fξ x = ξ xK := by show ξ _ = ξ xK; rfl
      have hfξy : fξ y = ξ yK := by show ξ _ = ξ yK; rfl
      have hfξ'x : fξ' x = ξ' xK := by show ξ' _ = ξ' xK; rfl
      have hfξ'y : fξ' y = ξ' yK := by show ξ' _ = ξ' yK; rfl
      rw [hfξx, hfξy, hfξ'x, hfξ'y, h_pair xK yK hxKyK]

/-! ### §3.7 — Rank algebra (closure-of-simple-evals)

Canonical algebraic framework for the multigraph bridge (#62). Per
Lovász TR-2004-82 §3: define the closure of simple-graph evaluations
under `+, *, smul, const`, prove the closure descends to
`tupleEquivSimple`-classes (trivial induction), and state the canonical
paper-root: every multigraph evaluation lies in the closure.

The closure uses the **inlined** simple-graph evaluation form (matching
the `h_simple` hypothesis of `multiLabeledEvalK_tupleEquiv_invariant`),
avoiding a forward dependency on `simpleEvalAt` (defined at L2381). -/

/-- **Closure of simple-graph evaluations** (inlined form, before
`simpleEvalAt` is in scope). A function `f : (Fin K → Fin T) → ℝ` is in
the closure iff it can be built from simple-graph evaluations using ring
operations. The base case `of_simple` uses the explicit `∑ σ ... * ∏ B`
expansion, matching the `h_simple` hypothesis of #62. -/
inductive InSimpleProfileClosure {T : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (K : ℕ) : ((Fin K → Fin T) → ℝ) → Prop
  | of_simple (n : ℕ) (F : SimpleGraph (Fin (n + K))) [DecidableRel F.Adj] :
      InSimpleProfileClosure B W K (fun ξ =>
        ∑ σ : Fin n → Fin T,
          (let τ : Fin (n + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then ξ ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩
          (∏ v : Fin n, W (σ v)) *
          ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2)))
  | const (c : ℝ) : InSimpleProfileClosure B W K (fun _ => c)
  | add {f g} : InSimpleProfileClosure B W K f →
      InSimpleProfileClosure B W K g →
      InSimpleProfileClosure B W K (fun ξ => f ξ + g ξ)
  | smul (c : ℝ) {f} : InSimpleProfileClosure B W K f →
      InSimpleProfileClosure B W K (fun ξ => c * f ξ)
  | mul {f g} : InSimpleProfileClosure B W K f →
      InSimpleProfileClosure B W K g →
      InSimpleProfileClosure B W K (fun ξ => f ξ * g ξ)

/-- **Closure functions descend to `h_simple`-equivalent tuples**. Takes
the inlined `tupleEquivSimple`-form hypothesis (matching #62's
`h_simple`). -/
theorem InSimpleProfileClosure.descends {T K : ℕ}
    {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    {f : (Fin K → Fin T) → ℝ} (hf : InSimpleProfileClosure B W K f)
    {ξ ξ' : Fin K → Fin T}
    (h : ∀ (n' : ℕ) (F : SimpleGraph (Fin (n' + K))) [DecidableRel F.Adj],
      ∑ σ : Fin n' → Fin T,
        (let τ : Fin (n' + K) → Fin T := fun v =>
          if h : (v : ℕ) < K then ξ ⟨v, h⟩
          else σ ⟨v - K, by have := v.isLt; omega⟩
        (∏ v : Fin n', W (σ v)) *
        ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2)) =
      ∑ σ : Fin n' → Fin T,
        (let τ : Fin (n' + K) → Fin T := fun v =>
          if h : (v : ℕ) < K then ξ' ⟨v, h⟩
          else σ ⟨v - K, by have := v.isLt; omega⟩
        (∏ v : Fin n', W (σ v)) *
        ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2))) :
    f ξ = f ξ' := by
  induction hf with
  | of_simple n F => exact h n F
  | const c => rfl
  | add _ _ ih_f ih_g => simp only; rw [ih_f, ih_g]
  | smul c _ ih_f => simp only; rw [ih_f]
  | mul _ _ ih_f ih_g => simp only; rw [ih_f, ih_g]

/-- **Zero is in the closure** (empty Finset.sum gives 0; or `smul 0` any
member). -/
theorem InSimpleProfileClosure.zero {T : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (K : ℕ) :
    InSimpleProfileClosure B W K (fun _ => (0 : ℝ)) := by
  have h := (InSimpleProfileClosure.const (B := B) (W := W) (K := K) 0).smul 0
  convert h using 1
  funext _; ring

/-- **Closure under subtraction**: `f - g ∈ closure` if both are. -/
theorem InSimpleProfileClosure.sub {T K : ℕ} {B : Fin T → Fin T → ℝ}
    {W : Fin T → ℝ} {f g : (Fin K → Fin T) → ℝ}
    (hf : InSimpleProfileClosure B W K f) (hg : InSimpleProfileClosure B W K g) :
    InSimpleProfileClosure B W K (fun ξ => f ξ - g ξ) := by
  have h := hf.add (hg.smul (-1))
  convert h using 1
  funext ξ; ring

/-- **Closure under `Finset.sum`** over an index set. -/
theorem InSimpleProfileClosure.finset_sum {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    {α : Type*} (S : Finset α) (g : α → (Fin K → Fin T) → ℝ)
    (hg : ∀ a ∈ S, InSimpleProfileClosure B W K (g a)) :
    InSimpleProfileClosure B W K (fun ξ => ∑ a ∈ S, g a ξ) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact InSimpleProfileClosure.zero B W K
  | insert a S ha_notin ih =>
    have h_a : InSimpleProfileClosure B W K (g a) := hg a (Finset.mem_insert_self a S)
    have h_S := ih (fun b hb => hg b (Finset.mem_insert_of_mem hb))
    have h_add := h_a.add h_S
    convert h_add using 1
    funext ξ
    rw [Finset.sum_insert ha_notin]

/-- **Closure under `Finset.prod`** over an index set. -/
theorem InSimpleProfileClosure.finset_prod {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    {α : Type*} (S : Finset α) (g : α → (Fin K → Fin T) → ℝ)
    (hg : ∀ a ∈ S, InSimpleProfileClosure B W K (g a)) :
    InSimpleProfileClosure B W K (fun ξ => ∏ a ∈ S, g a ξ) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    have := InSimpleProfileClosure.const (B := B) (W := W) (K := K) 1
    exact this
  | insert a S ha_notin ih =>
    have h_a : InSimpleProfileClosure B W K (g a) := hg a (Finset.mem_insert_self a S)
    have h_S := ih (fun b hb => hg b (Finset.mem_insert_of_mem hb))
    have h_mul := h_a.mul h_S
    convert h_mul using 1
    funext ξ
    rw [Finset.prod_insert ha_notin]

/-! ### §3.8 — Architecture for closing #86

The closure infrastructure above (`InSimpleProfileClosure` with `descends`,
algebra closures, `zero`/`add`/`sub`/`smul`/`mul`/`finset_sum`/`finset_prod`)
provides the building blocks. The path to #86:

1. **Lagrange fullness**: prove `of_const_on_tupleEquivSimple` — every
   `tupleEquivSimple`-invariant function is in the closure. Pure Lagrange
   interpolation, ~200 LOC. Mirrors K=1 `of_const_on_orbit`.

2. **Multigraph descent**: prove multigraph evaluations are
   `tupleEquivSimple`-invariant. THIS IS THE SUBSTANTIVE LOVÁSZ §3
   CONTENT (cannot be assumed; must be proved by the connection-matrix
   idempotent decomposition or polynomial-decomposition argument).

3. Combine: #86 follows from steps 1 + 2.

Both steps are non-trivial. Step 1 is finite algebra/Lagrange (doable
with the K=1 chain pattern). Step 2 is the remaining real Lovász §3
content. Splitting them clarifies what's needed but does not reduce the
algebraic burden.

For now, #86 remains the canonical paper-root. Stating step 1
separately would just add a sorry without progress — defer to a focused
Lagrange session where the proof can actually close. -/

/-! ### §3.9 — Lagrange fullness (Step 1 toward #86) -/

/-- Abbreviation for the inlined simple-graph evaluation at `ξ`, for a
specific `(n, F, [DecidableRel F.Adj])` triple. Matches the body of
`InSimpleProfileClosure.of_simple` and `tupleEquivSimple`. -/
private noncomputable def inlineSimpleEval {T K n : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (F : SimpleGraph (Fin (n + K))) [DecidableRel F.Adj]
    (ξ : Fin K → Fin T) : ℝ :=
  ∑ σ : Fin n → Fin T,
    (let τ : Fin (n + K) → Fin T := fun v =>
      if h : (v : ℕ) < K then ξ ⟨v, h⟩
      else σ ⟨v - K, by have := v.isLt; omega⟩
    (∏ v : Fin n, W (σ v)) *
    ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2))

/-- `inlineSimpleEval` for fixed `F` is in `InSimpleProfileClosure` (basic
`of_simple` witness, viewed as a function of `ξ`). -/
private theorem inlineSimpleEval_mem {T K n : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (F : SimpleGraph (Fin (n + K))) [hF : DecidableRel F.Adj] :
    InSimpleProfileClosure B W K (fun ξ => inlineSimpleEval B W F ξ) :=
  InSimpleProfileClosure.of_simple n F

/-- **Tuple simple-graph separator**: packages the witness for two
non-equivalent tuples — the `(n, F, [dec], sep_proof)` quadruple.
Analog of `RootedSeparator` from the K=1 chain. -/
private structure TupleSimpleSeparator {T K : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (ξ ξ' : Fin K → Fin T) where
  n : ℕ
  F : SimpleGraph (Fin (n + K))
  inst : DecidableRel F.Adj
  sep : @inlineSimpleEval T K n B W F inst ξ ≠ @inlineSimpleEval T K n B W F inst ξ'

/-- Constructor from negation of (inlined) `tupleEquivSimple`, via
`Classical.choose` (since `TupleSimpleSeparator` is `Type`-valued). -/
private noncomputable def mkTupleSimpleSeparator {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    {ξ ξ' : Fin K → Fin T}
    (h : ¬ ∀ (n' : ℕ) (F : SimpleGraph (Fin (n' + K))) [DecidableRel F.Adj],
      @inlineSimpleEval T K n' B W F _ ξ = @inlineSimpleEval T K n' B W F _ ξ') :
    TupleSimpleSeparator B W ξ ξ' :=
  let h' : ∃ (n : ℕ) (F : SimpleGraph (Fin (n + K))) (_ : DecidableRel F.Adj),
      @inlineSimpleEval T K n B W F _ ξ ≠ @inlineSimpleEval T K n B W F _ ξ' := by
    push_neg at h; exact h
  { n := h'.choose
    F := h'.choose_spec.choose
    inst := h'.choose_spec.choose_spec.choose
    sep := h'.choose_spec.choose_spec.choose_spec }

/-- Difference of `inlineSimpleEval` from a constant is in the closure. -/
private theorem InSimpleProfileClosure.inlineSimpleEval_sub_const {T K n : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (F : SimpleGraph (Fin (n + K))) [DecidableRel F.Adj] (c : ℝ) :
    InSimpleProfileClosure B W K (fun ξ => inlineSimpleEval B W F ξ - c) := by
  have h₁ := inlineSimpleEval_mem B W F
  have h₂ : InSimpleProfileClosure B W K (fun _ => c) :=
    InSimpleProfileClosure.const c
  exact h₁.sub h₂

/-- Lagrange factor for `inlineSimpleEval`: scaled difference. -/
private theorem InSimpleProfileClosure.inlineSimpleEval_lagrange_factor
    {T K n : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (F : SimpleGraph (Fin (n + K))) [DecidableRel F.Adj]
    (cξ cξ' : ℝ) :
    InSimpleProfileClosure B W K
      (fun ζ => (inlineSimpleEval B W F ζ - cξ') / (cξ - cξ')) := by
  have h := (InSimpleProfileClosure.inlineSimpleEval_sub_const B W F cξ').smul
    (1 / (cξ - cξ'))
  convert h using 1
  funext ζ
  rw [mul_comm, mul_one_div]

/-- **Step 1 of #86**: every function constant on (inlined) `tupleEquivSimple`-
classes is in `InSimpleProfileClosure`.

**Proof**: Lagrange interpolation. For each pair (ξ, ξ') with distinct
simple-graph profiles, fix a separating graph (via `mkTupleSimpleSeparator`).
Build per-tuple Lagrange indicators via products of `inlineSimpleEval_lagrange_factor`s.
Express any `tupleEquivSimple`-invariant function as a linear combination of
indicators using `finset_sum` and `smul`.

**Status**: ~200 LOC of Lagrange port from the K=1 `of_const_on_orbit`
proof. Currently sorry'd as Step 1 target. Closing this collapses #86's
remaining content to "multigraph evaluations are tupleEquivSimple-
invariant" (Step 2, the substantive Lovász §3 descent). -/
theorem InSimpleProfileClosure.of_const_on_tupleEquivSimple {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (f : (Fin K → Fin T) → ℝ)
    (hf : ∀ ξ ξ' : Fin K → Fin T,
      (∀ (n' : ℕ) (F : SimpleGraph (Fin (n' + K))) [DecidableRel F.Adj],
        @inlineSimpleEval T K n' B W F _ ξ =
        @inlineSimpleEval T K n' B W F _ ξ') →
      f ξ = f ξ') :
    InSimpleProfileClosure B W K f := by
  classical
  -- Define the inlined-equivalence relation locally.
  let Equiv : (Fin K → Fin T) → (Fin K → Fin T) → Prop := fun ξ ξ' =>
    ∀ (n' : ℕ) (F : SimpleGraph (Fin (n' + K))) [DecidableRel F.Adj],
      @inlineSimpleEval T K n' B W F _ ξ = @inlineSimpleEval T K n' B W F _ ξ'
  -- Step 1: each class indicator is in closure via Lagrange.
  have ind_closure : ∀ ξ : Fin K → Fin T,
      InSimpleProfileClosure B W K (fun ζ => if Equiv ξ ζ then (1 : ℝ) else 0) := by
    intro ξ
    -- Factor function: uses TupleSimpleSeparator for explicit instance.
    let factor : (Fin K → Fin T) → (Fin K → Fin T) → ℝ := fun η ζ =>
      if h : ¬ Equiv η ξ then
        let s := mkTupleSimpleSeparator B W (h := h)
        letI : DecidableRel s.F.Adj := s.inst
        (@inlineSimpleEval T K s.n B W s.F _ ζ - @inlineSimpleEval T K s.n B W s.F _ η) /
        (@inlineSimpleEval T K s.n B W s.F _ ξ - @inlineSimpleEval T K s.n B W s.F _ η)
      else 1
    let nonClass : Finset (Fin K → Fin T) :=
      Finset.univ.filter (fun η => ¬ Equiv η ξ)
    let lagInd : (Fin K → Fin T) → ℝ := fun ζ => ∏ η ∈ nonClass, factor η ζ
    have lagInd_mem : InSimpleProfileClosure B W K lagInd := by
      apply InSimpleProfileClosure.finset_prod B W nonClass factor
      intro η hη
      have hη_no : ¬ Equiv η ξ := by
        simp only [nonClass, Finset.mem_filter, Finset.mem_univ, true_and] at hη
        exact hη
      show InSimpleProfileClosure B W K (factor η)
      simp only [factor, dif_pos hη_no]
      let s := mkTupleSimpleSeparator B W (h := hη_no)
      letI : DecidableRel s.F.Adj := s.inst
      exact InSimpleProfileClosure.inlineSimpleEval_lagrange_factor B W s.F
        (@inlineSimpleEval T K s.n B W s.F _ ξ)
        (@inlineSimpleEval T K s.n B W s.F _ η)
    -- Show lagInd = (if Equiv ξ ζ then 1 else 0).
    have lagInd_eq : lagInd = fun ζ => if Equiv ξ ζ then (1 : ℝ) else 0 := by
      funext ζ
      by_cases hζ : Equiv ξ ζ
      · rw [if_pos hζ]
        show ∏ η ∈ nonClass, factor η ζ = (1 : ℝ)
        apply Finset.prod_eq_one
        intro η hη
        have hη_no : ¬ Equiv η ξ := by
          simp only [nonClass, Finset.mem_filter, Finset.mem_univ, true_and] at hη
          exact hη
        simp only [factor, dif_pos hη_no]
        let s := mkTupleSimpleSeparator B W (h := hη_no)
        letI : DecidableRel s.F.Adj := s.inst
        -- Numerator: eval at ζ = eval at ξ (since Equiv ξ ζ).
        have h_eq : @inlineSimpleEval T K s.n B W s.F _ ζ =
            @inlineSimpleEval T K s.n B W s.F _ ξ := (@hζ s.n s.F s.inst).symm
        have h_denom_ne :
            @inlineSimpleEval T K s.n B W s.F _ ξ -
            @inlineSimpleEval T K s.n B W s.F _ η ≠ 0 :=
          sub_ne_zero.mpr (fun he => s.sep he.symm)
        rw [h_eq]
        exact div_self h_denom_ne
      · rw [if_neg hζ]
        show ∏ η ∈ nonClass, factor η ζ = (0 : ℝ)
        -- ζ itself is in nonClass; the ζ-factor is 0.
        have h_ζ_no : ¬ Equiv ζ ξ := fun h_eq_ζ_ξ => by
          apply hζ
          intro n F hF
          exact (@h_eq_ζ_ξ n F hF).symm
        have h_ζ_mem : ζ ∈ nonClass := by
          simp only [nonClass, Finset.mem_filter, Finset.mem_univ, true_and]
          exact h_ζ_no
        refine Finset.prod_eq_zero h_ζ_mem ?_
        simp only [factor, dif_pos h_ζ_no]
        let s := mkTupleSimpleSeparator B W (h := h_ζ_no)
        letI : DecidableRel s.F.Adj := s.inst
        show (@inlineSimpleEval T K s.n B W s.F _ ζ -
              @inlineSimpleEval T K s.n B W s.F _ ζ) /
             (@inlineSimpleEval T K s.n B W s.F _ ξ -
              @inlineSimpleEval T K s.n B W s.F _ ζ) = 0
        rw [sub_self, zero_div]
    rw [← lagInd_eq]
    exact lagInd_mem
  -- Step 2: express f as a linear combination of class indicators.
  set classSize : (Fin K → Fin T) → ℕ := fun ξ =>
    (Finset.univ.filter (fun ζ => Equiv ξ ζ)).card with hclassSize_def
  have heq : f = fun ζ => ∑ ξ : Fin K → Fin T,
      (f ξ / (classSize ξ : ℝ)) * (if Equiv ξ ζ then 1 else 0) := by
    funext ζ
    -- Reduce sum to ξ such that Equiv ξ ζ (i.e., ξ in class of ζ).
    have h_sum_filter :
        (∑ ξ : Fin K → Fin T,
            (f ξ / (classSize ξ : ℝ)) * (if Equiv ξ ζ then (1:ℝ) else 0)) =
        ∑ ξ ∈ Finset.univ.filter (fun ξ => Equiv ξ ζ),
            f ξ / (classSize ξ : ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ξ _
      split_ifs with h <;> simp
    rw [h_sum_filter]
    -- For ξ with Equiv ξ ζ: f ξ = f ζ and classSize ξ = classSize ζ.
    have hEquiv_symm : ∀ {a b : Fin K → Fin T}, Equiv a b → Equiv b a :=
      fun {a b} h n F _ => (h n F).symm
    have hEquiv_trans : ∀ {a b c : Fin K → Fin T},
        Equiv a b → Equiv b c → Equiv a c :=
      fun {a b c} h₁ h₂ n F _ => (h₁ n F).trans (h₂ n F)
    have h_summands : ∀ ξ ∈ Finset.univ.filter (fun ξ => Equiv ξ ζ),
        f ξ / (classSize ξ : ℝ) = f ζ / (classSize ζ : ℝ) := by
      intro ξ hξ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hξ
      have hfξ : f ξ = f ζ := hf ξ ζ hξ
      have h_size : classSize ξ = classSize ζ := by
        have h_set_eq :
            (Finset.univ.filter (fun η => Equiv ξ η)) =
            (Finset.univ.filter (fun η => Equiv ζ η)) := by
          ext η
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h_ξη => hEquiv_trans (hEquiv_symm hξ) h_ξη,
                 fun h_ζη => hEquiv_trans hξ h_ζη⟩
        rw [hclassSize_def]
        exact congrArg Finset.card h_set_eq
      rw [hfξ, h_size]
    rw [Finset.sum_congr rfl h_summands]
    rw [Finset.sum_const, nsmul_eq_mul]
    -- card of filter = classSize ζ.
    have hcard : (Finset.univ.filter (fun ξ => Equiv ξ ζ)).card = classSize ζ := by
      rw [hclassSize_def]
      congr 1
      ext ξ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => hEquiv_symm h, fun h => hEquiv_symm h⟩
    rw [hcard]
    -- (classSize ζ : ℝ) > 0 since ζ ∈ class(ζ) (Equiv ζ ζ).
    have h_pos : (0 : ℝ) < (classSize ζ : ℝ) := by
      have h_pos_nat : 0 < classSize ζ := by
        rw [hclassSize_def]
        apply Finset.card_pos.mpr
        refine ⟨ζ, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro n F _; rfl
      exact_mod_cast h_pos_nat
    rw [mul_div_assoc']
    rw [mul_comm (classSize ζ : ℝ) (f ζ), mul_div_assoc, div_self (ne_of_gt h_pos), mul_one]
  rw [heq]
  exact InSimpleProfileClosure.finset_sum B W Finset.univ
    (fun ξ ζ => (f ξ / (classSize ξ : ℝ)) * (if Equiv ξ ζ then 1 else 0))
    (fun ξ _ => (ind_closure ξ).smul (f ξ / (classSize ξ : ℝ)))

/-! ### §3.9.5 — Multiplicity peel infrastructure (for LL-excess sub-case)

Helpers for closing the **LL-excess sub-case** of #86 via polynomial
decomposition. The key identity is the "single label-label peel":

  multiLabeledEvalK M B W ξ =
    B(ξ_a, ξ_b) * multiLabeledEvalK (M.decAt s(a, b)) B W ξ

valid for any label-label edge `(a, b)` (both `a.val, b.val < K`) with
`M.mult s(a, b) ≥ 1`. Iterating across LL edges reduces M to its
LL-kernel (LL multiplicities all zero), which is a simple graph when
all non-LL multiplicities are ≤ 1. -/

/-- **Decrement multiplicity at one edge.** A focused multigraph operation:
zero-saturated subtraction at `e₀`, identity elsewhere. -/
private def MultiLabeledGraph.decAt {K n : ℕ} (M : MultiLabeledGraph K n)
    (e₀ : Sym2 (Fin (n + K))) : MultiLabeledGraph K n where
  mult e := if e = e₀ then M.mult e - 1 else M.mult e
  multNoLoop x := by
    show (if s(x, x) = e₀ then M.mult s(x, x) - 1 else M.mult s(x, x)) = 0
    rw [M.multNoLoop x]
    split <;> rfl

/-- **Single LL-edge peel identity.** For a label-label edge `(a, b)` with
`a.val, b.val < K` and `M.mult s(a, b) ≥ 1`, the multigraph evaluation
factors as `B(ξ_a, ξ_b)` times the evaluation of `M.decAt s(a, b)`. -/
private lemma multiLabeledEvalK_decAt_LL_peel {T K n : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (M : MultiLabeledGraph K n)
    (a b : Fin (n + K)) (ha : a.val < K) (hb : b.val < K)
    (hm : 1 ≤ M.mult s(a, b))
    (ξ : Fin K → Fin T) :
    multiLabeledEvalK K n M B W ξ =
      B (ξ ⟨a.val, ha⟩) (ξ ⟨b.val, hb⟩) *
      multiLabeledEvalK K n (M.decAt s(a, b)) B W ξ := by
  classical
  unfold multiLabeledEvalK
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  let τ : Fin (n + K) → Fin T := fun v =>
    if h : (v : ℕ) < K then ξ ⟨v, h⟩
    else σ ⟨v - K, by have := v.isLt; omega⟩
  -- Reshape the goal to use the named τ.
  change (∏ v : Fin n, W (σ v)) *
         (∏ e : Sym2 (Fin (n + K)),
           B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ M.mult e) =
         B (ξ ⟨a.val, ha⟩) (ξ ⟨b.val, hb⟩) *
         ((∏ v : Fin n, W (σ v)) *
          (∏ e : Sym2 (Fin (n + K)),
            B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ (M.decAt s(a, b)).mult e))
  -- Compute τ at a, b (both labels).
  have hτa : τ a = ξ ⟨a.val, ha⟩ := by
    show (if h : (a : ℕ) < K then ξ ⟨a.val, h⟩ else _) = _
    rw [dif_pos ha]
  have hτb : τ b = ξ ⟨b.val, hb⟩ := by
    show (if h : (b : ℕ) < K then ξ ⟨b.val, h⟩ else _) = _
    rw [dif_pos hb]
  set e₀ : Sym2 (Fin (n + K)) := s(a, b) with he₀
  -- Apply Finset.mul_prod_erase at e₀ on both sides of the equation.
  have hLHS_split : (∏ e : Sym2 (Fin (n + K)),
        B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ M.mult e) =
      (B (τ (Quot.out e₀).1) (τ (Quot.out e₀).2) ^ M.mult e₀) *
      (∏ e ∈ (Finset.univ.erase e₀ : Finset (Sym2 (Fin (n + K)))),
        B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ M.mult e) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm
  have hRHS_split : (∏ e : Sym2 (Fin (n + K)),
        B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ (M.decAt s(a, b)).mult e) =
      (B (τ (Quot.out e₀).1) (τ (Quot.out e₀).2) ^ (M.decAt s(a, b)).mult e₀) *
      (∏ e ∈ (Finset.univ.erase e₀ : Finset (Sym2 (Fin (n + K)))),
        B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ (M.decAt s(a, b)).mult e) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm
  -- decAt's mult at e₀ is M.mult e₀ - 1.
  have hM'_e₀ : (M.decAt s(a, b)).mult e₀ = M.mult e₀ - 1 := by
    show (if e₀ = e₀ then M.mult e₀ - 1 else _) = _
    rw [if_pos rfl]
  -- decAt's mult agrees with M off e₀.
  have hM'_ne : ∀ e ∈ (Finset.univ.erase e₀ : Finset (Sym2 (Fin (n + K)))),
      (M.decAt s(a, b)).mult e = M.mult e := by
    intro e he
    rw [Finset.mem_erase] at he
    show (if e = e₀ then _ else _) = _
    rw [if_neg he.1]
  -- B at Quot.out e₀ via symmetry.
  have hquot : B (τ (Quot.out e₀).1) (τ (Quot.out e₀).2) =
               B (ξ ⟨a.val, ha⟩) (ξ ⟨b.val, hb⟩) := by
    rw [B_quot_out_eq hB τ a b, hτa, hτb]
  -- Equate the erase products (over Sym2, NOT Fin n).
  have h_erase_eq : (∏ e ∈ (Finset.univ.erase e₀ : Finset (Sym2 (Fin (n + K)))),
                     B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ (M.decAt s(a, b)).mult e) =
                    (∏ e ∈ (Finset.univ.erase e₀ : Finset (Sym2 (Fin (n + K)))),
                     B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ M.mult e) := by
    refine Finset.prod_congr rfl fun e he => ?_
    rw [hM'_ne e he]
  rw [hLHS_split, hRHS_split, hM'_e₀, h_erase_eq, hquot]
  -- Goal: W_prod * (B^M.mult e₀ * ∏_erase B^M.mult) =
  --       B * (W_prod * (B^(M.mult e₀ - 1) * ∏_erase B^M.mult))
  -- Use M.mult e₀ = (M.mult e₀ - 1) + 1 and pow_succ.
  have hmsucc : M.mult e₀ = (M.mult e₀ - 1) + 1 := by omega
  rw [show (B (ξ ⟨a.val, ha⟩) (ξ ⟨b.val, hb⟩)) ^ M.mult e₀ =
       (B (ξ ⟨a.val, ha⟩) (ξ ⟨b.val, hb⟩)) ^ (M.mult e₀ - 1) *
       B (ξ ⟨a.val, ha⟩) (ξ ⟨b.val, hb⟩) from by
    conv_lhs => rw [hmsucc]
    rw [pow_succ]]
  ring

/-- **LL predicate** on Sym2 pairs: both endpoints have val < K (are labels). -/
private def isLLEdge {K n : ℕ} : Sym2 (Fin (n + K)) → Prop := fun e =>
  Sym2.lift ⟨fun a b => (a.val < K ∧ b.val < K),
    fun a b => propext ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩⟩ e

private instance {K n : ℕ} : DecidablePred (@isLLEdge K n) := fun e =>
  Quot.recOnSubsingleton (motive := fun e => Decidable (isLLEdge e)) e
    (fun p => (inferInstance : Decidable (p.1.val < K ∧ p.2.val < K)))

@[simp] private lemma isLLEdge_mk {K n : ℕ} (a b : Fin (n + K)) :
    isLLEdge s(a, b) ↔ a.val < K ∧ b.val < K := Iff.rfl

/-- **Restriction embedding helper**: given an injection `g : Fin m → Fin n`
on unlabeled positions, build a map `Fin (m + K) → Fin (n + K)` that:
- Sends labels (val < K) identity-preserving.
- Sends rest-positions (val ≥ K) through `g`, shifted by K.
Used in the UU isolated subcase (Step 7) to embed F_rest's vertex space
into M's. Lifted to top-level to avoid deep `⟨_, by ...⟩` nesting. -/
private def restEmbedAux {n K m : ℕ} (g : Fin m → Fin n) :
    Fin (m + K) → Fin (n + K) := fun v =>
  if h : v.val < K then ⟨v.val, by omega⟩
  else
    let v_K : Fin m := ⟨v.val - K, by have := v.isLt; omega⟩
    ⟨(g v_K).val + K, by have := (g v_K).isLt; omega⟩

private lemma restEmbedAux_val_lab {n K m : ℕ} (g : Fin m → Fin n)
    (v : Fin (m + K)) (h : v.val < K) :
    (restEmbedAux g v).val = v.val := by
  unfold restEmbedAux
  rw [dif_pos h]

private lemma restEmbedAux_val_rest {n K m : ℕ} (g : Fin m → Fin n)
    (v : Fin (m + K)) (h : ¬ v.val < K) :
    (restEmbedAux g v).val =
    (g ⟨v.val - K, by have := v.isLt; omega⟩).val + K := by
  unfold restEmbedAux
  rw [dif_neg h]

private theorem restEmbedAux_injective {n K m : ℕ} {g : Fin m → Fin n}
    (hg : Function.Injective g) :
    Function.Injective (@restEmbedAux n K m g) := by
  intro x y h_eq
  apply Fin.ext
  have h_val : (restEmbedAux g x).val = (restEmbedAux g y).val := congr_arg Fin.val h_eq
  by_cases hx : x.val < K
  · by_cases hy : y.val < K
    · rw [restEmbedAux_val_lab g x hx, restEmbedAux_val_lab g y hy] at h_val
      exact h_val
    · push_neg at hy
      rw [restEmbedAux_val_lab g x hx,
          restEmbedAux_val_rest g y (not_lt.mpr hy)] at h_val
      omega
  · push_neg at hx
    by_cases hy : y.val < K
    · rw [restEmbedAux_val_rest g x (not_lt.mpr hx),
          restEmbedAux_val_lab g y hy] at h_val
      omega
    · push_neg at hy
      rw [restEmbedAux_val_rest g x (not_lt.mpr hx),
          restEmbedAux_val_rest g y (not_lt.mpr hy)] at h_val
      have h_inner : (g ⟨x.val - K, by have := x.isLt; omega⟩ : Fin n).val =
                     (g ⟨y.val - K, by have := y.isLt; omega⟩ : Fin n).val := by omega
      have h_g_eq : g ⟨x.val - K, by have := x.isLt; omega⟩ =
                    g ⟨y.val - K, by have := y.isLt; omega⟩ := Fin.ext h_inner
      have h_arg_eq : (⟨x.val - K, by have := x.isLt; omega⟩ : Fin m) =
                      (⟨y.val - K, by have := y.isLt; omega⟩ : Fin m) := hg h_g_eq
      have h_val_eq : x.val - K = y.val - K := by
        have := congr_arg Fin.val h_arg_eq
        simpa using this
      show x.val = y.val
      omega

/-- **LL multiplicity sum**: total multiplicity over LL edges. Used as the
strong-induction measure for closing the LL-excess sub-case of #86. -/
private def MultiLabeledGraph.LLSum {K n : ℕ} (M : MultiLabeledGraph K n) : ℕ :=
  ∑ e ∈ (Finset.univ.filter isLLEdge : Finset (Sym2 (Fin (n + K)))), M.mult e

/-- **LL-excess invariance** (auxiliary for #86's LL-excess sub-case). Strong
induction on `M.LLSum` reduces to the all-mults-≤-1 simple-graph case via
iterated peeling. Each peel: applies `multiLabeledEvalK_decAt_LL_peel` at
a chosen LL edge; the `B(ξ_a, ξ_b)` factor matches at ξ vs ξ' via h_simple
on the single-edge LL graph. -/
private lemma multigraphEval_LL_excess_descends_aux {T K n : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    {ξ ξ' : Fin K → Fin T}
    (h_simple : ∀ (n' : ℕ) (F : SimpleGraph (Fin (n' + K))) [DecidableRel F.Adj],
        ∑ σ : Fin n' → Fin T,
          (let τ : Fin (n' + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then ξ ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩
          (∏ v : Fin n', W (σ v)) *
          ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2)) =
        ∑ σ : Fin n' → Fin T,
          (let τ : Fin (n' + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then ξ' ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩
          (∏ v : Fin n', W (σ v)) *
          ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2)))
    (N : ℕ) :
    ∀ M : MultiLabeledGraph K n,
      (∀ e, ¬ isLLEdge e → M.mult e ≤ 1) →
      M.LLSum = N →
      multiLabeledEvalK K n M B W ξ = multiLabeledEvalK K n M B W ξ' := by
  classical
  induction N with
  | zero =>
    intro M h_nonLL_le_one hN
    -- M.LLSum = 0 ⟹ all LL mults are 0 ⟹ all mults ≤ 1 ⟹ simple-graph case.
    have h_LL_zero : ∀ e, isLLEdge e → M.mult e = 0 := by
      intro e he
      have hmem : e ∈ (Finset.univ.filter isLLEdge : Finset (Sym2 (Fin (n + K)))) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
      have hsum : (∑ e' ∈ (Finset.univ.filter isLLEdge : Finset (Sym2 (Fin (n + K)))),
                    M.mult e') = 0 := hN
      exact Nat.eq_zero_of_le_zero
        (hsum ▸ Finset.single_le_sum (f := fun e' => M.mult e')
          (fun _ _ => Nat.zero_le _) hmem)
    have h_all_le_one : ∀ e, M.mult e ≤ 1 := by
      intro e
      by_cases he : isLLEdge e
      · rw [h_LL_zero e he]; omega
      · exact h_nonLL_le_one e he
    -- Build the corresponding simple graph and apply h_simple.
    let F : SimpleGraph (Fin (n + K)) :=
      { Adj := fun a b => a ≠ b ∧ M.mult s(a, b) = 1
        symm := fun a b ⟨hne, hmult⟩ =>
          ⟨hne.symm, by rwa [Sym2.eq_swap]⟩
        loopless := fun a ⟨hne, _⟩ => hne rfl }
    haveI : DecidableRel F.Adj := Classical.decRel _
    have hmult_eq : ∀ e, M.mult e = (MultiLabeledGraph.ofSimple F).mult e := by
      intro e
      induction e with
      | h a b =>
        show M.mult s(a, b) = if s(a, b) ∈ F.edgeFinset then 1 else 0
        by_cases hM : M.mult s(a, b) = 0
        · rw [hM]
          have : ¬ s(a, b) ∈ F.edgeFinset := by
            rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
            intro ⟨_, hmult⟩
            rw [hM] at hmult; exact absurd hmult (by omega)
          rw [if_neg this]
        · have hM_one : M.mult s(a, b) = 1 := by
            have := h_all_le_one s(a, b); omega
          rw [hM_one]
          have : s(a, b) ∈ F.edgeFinset := by
            rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
            refine ⟨?_, hM_one⟩
            intro hab; rw [hab] at hM_one
            have := M.multNoLoop b; omega
          rw [if_pos this]
    have hev : ∀ ζ : Fin K → Fin T,
        multiLabeledEvalK K n M B W ζ =
        multiLabeledEvalK K n (MultiLabeledGraph.ofSimple F) B W ζ := by
      intro ζ
      unfold multiLabeledEvalK
      refine Finset.sum_congr rfl fun σ _ => ?_
      simp_rw [hmult_eq]
    rw [hev ξ, hev ξ', multiLabeledEvalK_ofSimple, multiLabeledEvalK_ofSimple]
    exact h_simple n F
  | succ k IH =>
    intro M h_nonLL_le_one hN
    -- LLSum = k + 1 ⟹ ∃ LL edge with mult ≥ 1.
    have h_sum_pos : 0 < M.LLSum := by rw [hN]; omega
    have h_exists : ∃ e ∈ (Finset.univ.filter isLLEdge :
        Finset (Sym2 (Fin (n + K)))), 1 ≤ M.mult e := by
      by_contra h
      push_neg at h
      have : M.LLSum = 0 := by
        unfold MultiLabeledGraph.LLSum
        exact Finset.sum_eq_zero fun e he => by have := h e he; omega
      omega
    obtain ⟨e₀, he₀_mem, he₀_mult⟩ := h_exists
    rw [Finset.mem_filter] at he₀_mem
    have he₀_LL := he₀_mem.2
    -- Extract a, b from e₀ via Sym2 induction.
    induction e₀ using Sym2.ind with
    | h a b =>
      rw [isLLEdge_mk] at he₀_LL
      obtain ⟨ha, hb⟩ := he₀_LL
      -- Peel at s(a, b).
      have hM_decAt_LLSum : (M.decAt s(a, b)).LLSum = k := by
        unfold MultiLabeledGraph.LLSum
        have h_decAt_mem :
            s(a, b) ∈ (Finset.univ.filter isLLEdge : Finset (Sym2 (Fin (n + K)))) := by
          rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rw [isLLEdge_mk]; exact ⟨ha, hb⟩⟩
        have h_sum_split : (∑ e ∈ (Finset.univ.filter isLLEdge :
              Finset (Sym2 (Fin (n + K)))), (M.decAt s(a, b)).mult e) =
            (∑ e ∈ (Finset.univ.filter isLLEdge).erase s(a, b),
              (M.decAt s(a, b)).mult e) + (M.decAt s(a, b)).mult s(a, b) :=
          (Finset.sum_erase_add _ _ h_decAt_mem).symm
        rw [h_sum_split]
        have h_decAt_e₀ : (M.decAt s(a, b)).mult s(a, b) = M.mult s(a, b) - 1 := by
          show (if s(a, b) = s(a, b) then M.mult s(a, b) - 1 else _) = _
          rw [if_pos rfl]
        have h_decAt_ne : ∀ e ∈ ((Finset.univ.filter isLLEdge).erase s(a, b) :
            Finset (Sym2 (Fin (n + K)))),
            (M.decAt s(a, b)).mult e = M.mult e := by
          intro e he
          rw [Finset.mem_erase] at he
          show (if e = s(a, b) then _ else _) = _
          rw [if_neg he.1]
        have h_erase_sum : (∑ e ∈ (Finset.univ.filter isLLEdge).erase s(a, b),
              (M.decAt s(a, b)).mult e) =
            (∑ e ∈ (Finset.univ.filter isLLEdge).erase s(a, b), M.mult e) :=
          Finset.sum_congr rfl h_decAt_ne
        rw [h_erase_sum, h_decAt_e₀]
        have hM_LLSum_split : M.LLSum =
            (∑ e ∈ (Finset.univ.filter isLLEdge).erase s(a, b), M.mult e) +
            M.mult s(a, b) :=
          (Finset.sum_erase_add _ _ h_decAt_mem).symm
        have h_mult_pos : 1 ≤ M.mult s(a, b) := he₀_mult
        rw [hM_LLSum_split] at hN
        omega
      have h_decAt_nonLL : ∀ e, ¬ isLLEdge e → (M.decAt s(a, b)).mult e ≤ 1 := by
        intro e he
        show (if e = s(a, b) then M.mult e - 1 else M.mult e) ≤ 1
        have h_e_ne : e ≠ s(a, b) := by
          intro h_eq
          apply he
          rw [h_eq, isLLEdge_mk]
          exact ⟨ha, hb⟩
        rw [if_neg h_e_ne]
        exact h_nonLL_le_one e he
      have h_IH := IH (M.decAt s(a, b)) h_decAt_nonLL hM_decAt_LLSum
      -- Apply peel to express both sides via decAt.
      rw [multiLabeledEvalK_decAt_LL_peel B hB W M a b ha hb he₀_mult ξ,
          multiLabeledEvalK_decAt_LL_peel B hB W M a b ha hb he₀_mult ξ']
      -- Single-edge LL h_simple: B(ξ_⟨a⟩)(ξ_⟨b⟩) = B(ξ'_⟨a⟩)(ξ'_⟨b⟩).
      have h_single_edge : B (ξ ⟨a.val, ha⟩) (ξ ⟨b.val, hb⟩) =
                          B (ξ' ⟨a.val, ha⟩) (ξ' ⟨b.val, hb⟩) := by
        -- Use h_simple at n' = 0 with a single-edge graph between labels ⟨a.val, ha⟩, ⟨b.val, hb⟩.
        let aK : Fin K := ⟨a.val, ha⟩
        let bK : Fin K := ⟨b.val, hb⟩
        have h_aK_ne_bK : aK ≠ bK := by
          intro h_eq
          have : a.val = b.val := by
            have := congr_arg Fin.val h_eq
            simpa [aK, bK] using this
          -- a ≠ b in Fin (n + K). isLL says a.val < K, b.val < K. M.multNoLoop says s(a,a) = 0.
          -- But we have he₀_mult : 1 ≤ M.mult s(a, b). If a = b, M.mult s(a, a) = 0. Contradiction.
          have hab : a = b := Fin.ext this
          rw [hab] at he₀_mult
          have := M.multNoLoop b
          omega
        -- Build the single-edge simple graph on Fin (0 + K).
        let aF : Fin (0 + K) := ⟨aK.val, by have := aK.isLt; omega⟩
        let bF : Fin (0 + K) := ⟨bK.val, by have := bK.isLt; omega⟩
        have h_aF_ne_bF : aF ≠ bF := by
          intro h_eq
          apply h_aK_ne_bK
          exact Fin.ext (by have := congr_arg Fin.val h_eq; simpa [aF, bF] using this)
        let G : SimpleGraph (Fin (0 + K)) :=
          { Adj := fun u v => (u = aF ∧ v = bF) ∨ (u = bF ∧ v = aF)
            symm := fun u v => by rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> [right; left] <;> exact ⟨h2, h1⟩
            loopless := fun u h => by
              rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact h_aF_ne_bF (h1.symm.trans h2)
              · exact h_aF_ne_bF (h2.symm.trans h1) }
        haveI : DecidableRel G.Adj := Classical.decRel _
        have hG_edge : G.edgeFinset = {s(aF, bF)} := by
          ext e
          induction e with
          | h u v =>
            rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_singleton]
            show ((u = aF ∧ v = bF) ∨ (u = bF ∧ v = aF)) ↔ s(u, v) = s(aF, bF)
            rw [Sym2.eq_iff]
        have heq := h_simple 0 G
        -- General reduction for single-edge n=0 eval (works for any η).
        have hreduce : ∀ (η : Fin K → Fin T),
            (∑ σ : Fin 0 → Fin T,
              (let τ : Fin (0 + K) → Fin T := fun v =>
                if h : (v : ℕ) < K then η ⟨v, h⟩
                else σ ⟨v - K, by have := v.isLt; omega⟩
              (∏ v : Fin 0, W (σ v)) *
              ∏ e ∈ G.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2))) =
            B (η aK) (η bK) := by
          intro η
          rw [Fintype.sum_unique]
          let τ : Fin (0 + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then η ⟨v, h⟩
            else (default : Fin 0 → Fin T) ⟨v - K, by have := v.isLt; omega⟩
          change (∏ v : Fin 0, W ((default : Fin 0 → Fin T) v)) *
                 (∏ e ∈ G.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2)) =
                 B (η aK) (η bK)
          rw [hG_edge]
          simp only [Finset.prod_singleton]
          rw [Fin.prod_univ_zero, one_mul]
          rw [B_quot_out_eq hB τ aF bF]
          have hτaF : τ aF = η aK := by
            show (if h : (aF : ℕ) < K then η ⟨aF.val, h⟩ else _) = _
            have h_lt : (aF : ℕ) < K := aK.isLt
            rw [dif_pos h_lt]
          have hτbF : τ bF = η bK := by
            show (if h : (bF : ℕ) < K then η ⟨bF.val, h⟩ else _) = _
            have h_lt : (bF : ℕ) < K := bK.isLt
            rw [dif_pos h_lt]
          rw [hτaF, hτbF]
        rw [hreduce ξ, hreduce ξ'] at heq
        show B (ξ ⟨a.val, ha⟩) (ξ ⟨b.val, hb⟩) = B (ξ' ⟨a.val, ha⟩) (ξ' ⟨b.val, hb⟩)
        exact heq
      rw [h_single_edge, h_IH]

/-- **CANONICAL PAPER-ROOT** — unlabeled-excess descent (the final Lovász §3
core). After polynomial decomposition handles all label-label multiplicities
(via `multigraphEval_LL_excess_descends_aux`), the remaining residue is
the case where some mult≥2 edge touches at least one unlabeled vertex.
Polynomial decomposition does NOT apply directly: the B-factor at such
an edge depends on σ (the unlabeled coloring), so it cannot be pulled
out of the σ-sum.

**Hypotheses**:
  - `B` symmetric.
  - `h_simple`: the inlined `tupleEquivSimple` hypothesis at level K.
  - `h_unlabeled_excess`: there exists an edge with multiplicity ≥ 2
    that touches at least one unlabeled vertex (val ≥ K).

**Conclusion**: `multiLabeledEvalK K n M B W ξ = multiLabeledEvalK K n M B W ξ'`.

**Status** (2026-05-19): this is the residual Lovász §3 content of #86,
the canonical paper-root for #62. Closing requires the connection-matrix
/ idempotent decomposition of the multigraph algebra `𝒜_K` (~300-500 LOC
of new spectral/rank infrastructure).

**Smallest non-trivial subcase** (next target): "one doubled edge involving
an unlabeled vertex" — even that requires the substantive Lovász §3
algebra. If that subcase reduces, general multiplicities follow by
products (per Lovász §3.3).

**Architecture note**: this is the general unlabeled-excess case. The
**final paper-root** is the smaller doubled-edge subcase
`multigraphEval_one_doubled_unlabeled_edge_descends` (see below), which
isolates the K=1 square moment as the genuine Lovász §3 residue. -/
private theorem multigraphEval_unlabeled_excess_descends {T K n : ℕ}
    (B : Fin T → Fin T → ℝ) (_hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (M : MultiLabeledGraph K n)
    (_h_unlabeled_excess :
      ∃ e : Sym2 (Fin (n + K)), ¬ isLLEdge e ∧ 2 ≤ M.mult e)
    {ξ ξ' : Fin K → Fin T}
    (_h_simple : ∀ (n' : ℕ) (F : SimpleGraph (Fin (n' + K))) [DecidableRel F.Adj],
        ∑ σ : Fin n' → Fin T,
          (let τ : Fin (n' + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then ξ ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩
          (∏ v : Fin n', W (σ v)) *
          ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2)) =
        ∑ σ : Fin n' → Fin T,
          (let τ : Fin (n' + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then ξ' ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩
          (∏ v : Fin n', W (σ v)) *
          ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2))) :
    multiLabeledEvalK K n M B W ξ = multiLabeledEvalK K n M B W ξ' := by
  sorry

/-- **FINAL PAPER-ROOT (minimal hard residue)** — K=1 square moment
identity. Under `tupleEquivSimple ξ ξ'`,
  `∑_t W(t) · B(ξ_a, t)² = ∑_t W(t) · B(ξ'_a, t)²`
for any label coordinate `a : Fin K`.

This is the genuine Lovász §3 bottleneck. The square moment is
auto-invariant (Aut(B, W) permutes `t` while preserving W and B²) but
is **NOT** a polynomial in single-edge simple-graph evaluations:
no simple graph evaluates to `B(ξ_a, t)²`, and the polynomial closure
of single-edge evals contains only products like `B(x, t) · B(y, t)`
(which differ from `B(x, t)²` unless `x = y`).

Lovász Lemma 2.5 says every auto-invariant function lies in the
multigraph eval span, but reducing this to simple-graph evals requires
the connection-matrix / idempotent decomposition (Lovász §3 proper).
~300-500 LOC of new spectral/rank infrastructure.

**Status**: NAMED FINAL PAPER-ROOT (2026-05-19). Sorry'd. -/
private theorem label_unlabeled_square_moment_descends {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    {ξ ξ' : Fin K → Fin T}
    (_h_simple : ∀ (n' : ℕ) (F : SimpleGraph (Fin (n' + K))) [DecidableRel F.Adj],
        ∑ σ : Fin n' → Fin T,
          (let τ : Fin (n' + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then ξ ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩
          (∏ v : Fin n', W (σ v)) *
          ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2)) =
        ∑ σ : Fin n' → Fin T,
          (let τ : Fin (n' + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then ξ' ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩
          (∏ v : Fin n', W (σ v)) *
          ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2)))
    (a : Fin K) :
    ∑ t : Fin T, W t * B (ξ a) t ^ 2 = ∑ t : Fin T, W t * B (ξ' a) t ^ 2 := by
  sorry

/-- **Isolated unlabeled-unlabeled doubled-edge subcase**. M has one
doubled edge `(i, j)` with both `i, j` unlabeled (val ≥ K), and no
other edges touch `i` or `j`. All other multiplicities ≤ 1.

**Status**: algebraically closable (ξ-independent scalar prefactor
`∑_{s,t} W(s)W(t) B(s,t)²` times a simple-graph evaluation on the
remaining vertices). Sorry'd pending the σ-sum factorization
infrastructure (~200 LOC of Equiv-based Fin reindexing). -/
private theorem multigraphEval_isolated_unlabeled_unlabeled_doubled_edge_descends
    {T K n : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (M : MultiLabeledGraph K n)
    (i j : Fin (n + K))
    (hi : K ≤ i.val) (hj : K ≤ j.val) (hij : i ≠ j)
    (h_doubled : M.mult s(i, j) = 2)
    (h_others_le_one : ∀ e, e ≠ s(i, j) → M.mult e ≤ 1)
    (h_isolated : ∀ e, e ≠ s(i, j) → (i ∈ e ∨ j ∈ e) → M.mult e = 0)
    {ξ ξ' : Fin K → Fin T}
    (h_simple : ∀ (n' : ℕ) (F : SimpleGraph (Fin (n' + K))) [DecidableRel F.Adj],
        ∑ σ : Fin n' → Fin T,
          (let τ : Fin (n' + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then ξ ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩
          (∏ v : Fin n', W (σ v)) *
          ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2)) =
        ∑ σ : Fin n' → Fin T,
          (let τ : Fin (n' + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then ξ' ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩
          (∏ v : Fin n', W (σ v)) *
          ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2))) :
    multiLabeledEvalK K n M B W ξ = multiLabeledEvalK K n M B W ξ' := by
  classical
  -- Step 1: u_p ≠ v_p (the unlabeled positions of i, j in Fin n).
  let u_p : Fin n := ⟨i.val - K, by have := i.isLt; omega⟩
  let v_p : Fin n := ⟨j.val - K, by have := j.isLt; omega⟩
  have hu_p_ne_v_p : u_p ≠ v_p := by
    intro h_eq
    apply hij
    apply Fin.ext
    have hval : u_p.val = v_p.val := by rw [h_eq]
    show i.val = j.val
    have : i.val - K = j.val - K := hval
    omega
  -- The doubled edge `s(i, j)` is not a self-loop (multNoLoop + mult = 2 > 0).
  have hi_lift : i = ⟨u_p.val + K, by have := i.isLt; omega⟩ := by
    apply Fin.ext; show i.val = (i.val - K) + K; omega
  have hj_lift : j = ⟨v_p.val + K, by have := j.isLt; omega⟩ := by
    apply Fin.ext; show j.val = (j.val - K) + K; omega
  -- Step 2: LL/non-LL predicate on Fin n positions.
  let p : Fin n → Prop := fun k => k = u_p ∨ k = v_p
  haveI hpdec : DecidablePred p := fun k =>
    (inferInstance : Decidable (k = u_p ∨ k = v_p))
  -- Step 3: Subtype p ≃ Fin 2, with u_p ↦ 0, v_p ↦ 1.
  let mkU : Subtype p := ⟨u_p, Or.inl rfl⟩
  let mkV : Subtype p := ⟨v_p, Or.inr rfl⟩
  have hmkU_val : (mkU : Subtype p).val = u_p := rfl
  have hmkV_val : (mkV : Subtype p).val = v_p := rfl
  have hvu_ne : v_p ≠ u_p := fun h => hu_p_ne_v_p h.symm
  let subtypeEquiv : Subtype p ≃ Fin 2 :=
    { toFun := fun x => if x.val = u_p then (0 : Fin 2) else 1
      invFun := fun i => if i = (0 : Fin 2) then mkU else mkV
      left_inv := fun x => by
        rcases x.property with h_u | h_v
        · have hx : x = mkU := Subtype.ext h_u
          subst hx
          dsimp only
          rw [if_pos hmkU_val, if_pos rfl]
        · have hx : x = mkV := Subtype.ext h_v
          subst hx
          dsimp only
          rw [if_neg (show ¬ ((mkV : Subtype p).val = u_p) from hvu_ne)]
          rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]
      right_inv := fun i => by
        by_cases hi0 : i = (0 : Fin 2)
        · subst hi0
          dsimp only
          rw [if_pos rfl, if_pos hmkU_val]
        · have hi1 : i = 1 := by
            apply Fin.ext
            have h_lt : i.val < 2 := i.isLt
            have h_ne : i.val ≠ 0 := fun heq => hi0 (Fin.ext heq)
            show i.val = 1; omega
          subst hi1
          dsimp only
          rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]
          rw [if_neg (show ¬ ((mkV : Subtype p).val = u_p) from hvu_ne)] }
  -- Step 4: combined σ-sum split equiv.
  let splitSigma : (Fin n → Fin T) ≃ ((Fin 2 → Fin T) × ({k : Fin n // ¬ p k} → Fin T)) :=
    (Equiv.piEquivPiSubtypeProd p (fun _ => Fin T)).trans
      (Equiv.prodCongr (Equiv.arrowCongr subtypeEquiv (Equiv.refl (Fin T))) (Equiv.refl _))
  -- Local lemma: at u_p, splitSigma.symm reads off α 0; at v_p, reads off α 1.
  have h_at_u : ∀ (α : Fin 2 → Fin T) (ρ : {k // ¬ p k} → Fin T),
      (splitSigma.symm (α, ρ)) u_p = α 0 := by
    intro α ρ
    show (Equiv.piEquivPiSubtypeProd p (fun _ => Fin T)).symm
         (((Equiv.arrowCongr subtypeEquiv (Equiv.refl (Fin T))).symm α), ρ) u_p = α 0
    rw [Equiv.piEquivPiSubtypeProd_symm_apply]
    rw [dif_pos (Or.inl rfl : p u_p)]
    show (Equiv.arrowCongr subtypeEquiv (Equiv.refl (Fin T))).symm α
         ⟨u_p, Or.inl rfl⟩ = α 0
    show α (subtypeEquiv ⟨u_p, Or.inl rfl⟩) = α 0
    congr 1
    show (if (⟨u_p, Or.inl rfl⟩ : Subtype p).val = u_p then (0 : Fin 2) else 1) = 0
    rw [if_pos rfl]
  have h_at_v : ∀ (α : Fin 2 → Fin T) (ρ : {k // ¬ p k} → Fin T),
      (splitSigma.symm (α, ρ)) v_p = α 1 := by
    intro α ρ
    show (Equiv.piEquivPiSubtypeProd p (fun _ => Fin T)).symm
         (((Equiv.arrowCongr subtypeEquiv (Equiv.refl (Fin T))).symm α), ρ) v_p = α 1
    rw [Equiv.piEquivPiSubtypeProd_symm_apply]
    rw [dif_pos (Or.inr rfl : p v_p)]
    show (Equiv.arrowCongr subtypeEquiv (Equiv.refl (Fin T))).symm α
         ⟨v_p, Or.inr rfl⟩ = α 1
    show α (subtypeEquiv ⟨v_p, Or.inr rfl⟩) = α 1
    congr 1
    show (if (⟨v_p, Or.inr rfl⟩ : Subtype p).val = u_p then (0 : Fin 2) else 1) = 1
    rw [if_neg hvu_ne]
  have h_at_rest : ∀ (α : Fin 2 → Fin T) (ρ : {k // ¬ p k} → Fin T)
      (k : Fin n) (hk : ¬ p k),
      (splitSigma.symm (α, ρ)) k = ρ ⟨k, hk⟩ := by
    intro α ρ k hk
    show (Equiv.piEquivPiSubtypeProd p (fun _ => Fin T)).symm
         (((Equiv.arrowCongr subtypeEquiv (Equiv.refl (Fin T))).symm α), ρ) k = ρ ⟨k, hk⟩
    rw [Equiv.piEquivPiSubtypeProd_symm_apply]
    rw [dif_neg hk]
  -- Step 5: W-product factorization.
  have hW_factor : ∀ (α : Fin 2 → Fin T) (ρ : {k // ¬ p k} → Fin T),
      (∏ k : Fin n, W ((splitSigma.symm (α, ρ)) k)) =
      W (α 0) * W (α 1) * ∏ k : {k // ¬ p k}, W (ρ k) := by
    intro α ρ
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ p
        (fun k => W ((splitSigma.symm (α, ρ)) k))]
    have h_filter_p_eq : (Finset.univ.filter p : Finset (Fin n)) = {u_p, v_p} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                 Finset.mem_singleton]
      rfl
    rw [h_filter_p_eq, Finset.prod_pair hu_p_ne_v_p, h_at_u α ρ, h_at_v α ρ]
    congr 1
    -- Remaining: filter (¬p) product = ∏ k : Subtype (¬p), W (ρ k).
    rw [Finset.prod_subtype (Finset.univ.filter (¬ p ·)) (p := (¬ p ·))
        (fun k => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
        (fun k => W ((splitSigma.symm (α, ρ)) k))]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [h_at_rest α ρ k.val k.property]
  -- Step 6: B-product factorization.
  -- For σ = splitSigma.symm (α, ρ) and τ extending it with ξ at labels,
  -- the Sym2 product factors as B(α 0, α 1)^2 times the product over edges
  -- not touching i or j.
  have hB_factor : ∀ (α : Fin 2 → Fin T) (ρ : {k // ¬ p k} → Fin T)
      (η : Fin K → Fin T),
      (∏ e : Sym2 (Fin (n + K)),
        B ((fun v : Fin (n + K) =>
              if h : (v : ℕ) < K then η ⟨v, h⟩
              else (splitSigma.symm (α, ρ)) ⟨v - K, by have := v.isLt; omega⟩)
            (Quot.out e).1)
          ((fun v : Fin (n + K) =>
              if h : (v : ℕ) < K then η ⟨v, h⟩
              else (splitSigma.symm (α, ρ)) ⟨v - K, by have := v.isLt; omega⟩)
            (Quot.out e).2) ^ M.mult e) =
      B (α 0) (α 1) ^ 2 *
      (∏ e ∈ (Finset.univ.filter (fun e : Sym2 (Fin (n + K)) => i ∉ e ∧ j ∉ e) :
              Finset (Sym2 (Fin (n + K)))),
        B ((fun v : Fin (n + K) =>
              if h : (v : ℕ) < K then η ⟨v, h⟩
              else (splitSigma.symm (α, ρ)) ⟨v - K, by have := v.isLt; omega⟩)
            (Quot.out e).1)
          ((fun v : Fin (n + K) =>
              if h : (v : ℕ) < K then η ⟨v, h⟩
              else (splitSigma.symm (α, ρ)) ⟨v - K, by have := v.isLt; omega⟩)
            (Quot.out e).2) ^ M.mult e) := by
    intro α ρ η
    set τ : Fin (n + K) → Fin T := fun v =>
      if h : (v : ℕ) < K then η ⟨v, h⟩
      else (splitSigma.symm (α, ρ)) ⟨v - K, by have := v.isLt; omega⟩
    -- τ at i = α 0, τ at j = α 1.
    have hτi : τ i = α 0 := by
      show (if h : (i : ℕ) < K then η ⟨i.val, h⟩ else _) = α 0
      rw [dif_neg (by omega : ¬ ((i : ℕ) < K))]
      show (splitSigma.symm (α, ρ)) ⟨i.val - K, _⟩ = α 0
      have h_eq : (⟨i.val - K, by have := i.isLt; omega⟩ : Fin n) = u_p := rfl
      rw [h_eq]
      exact h_at_u α ρ
    have hτj : τ j = α 1 := by
      show (if h : (j : ℕ) < K then η ⟨j.val, h⟩ else _) = α 1
      rw [dif_neg (by omega : ¬ ((j : ℕ) < K))]
      show (splitSigma.symm (α, ρ)) ⟨j.val - K, _⟩ = α 1
      have h_eq : (⟨j.val - K, by have := j.isLt; omega⟩ : Fin n) = v_p := rfl
      rw [h_eq]
      exact h_at_v α ρ
    -- Apply Finset.mul_prod_erase at s(i, j).
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ s(i, j))]
    rw [h_doubled, B_quot_out_eq hB τ i j, hτi, hτj]
    congr 1
    -- Goal: ∏ e ∈ erase, B(τ_e)^M.mult e = ∏ e ∈ filter (i ∉ e ∧ j ∉ e), B(τ_e)^M.mult e.
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ.erase s(i, j))
          (fun e => i ∈ e ∨ j ∈ e)
          (fun e => B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ M.mult e)]
    have h_touching : (∏ e ∈ (Finset.univ.erase s(i, j) :
          Finset (Sym2 (Fin (n + K)))).filter (fun e => i ∈ e ∨ j ∈ e),
          B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ M.mult e) = 1 := by
      apply Finset.prod_eq_one
      intro e he
      rw [Finset.mem_filter, Finset.mem_erase] at he
      obtain ⟨⟨he_ne, _⟩, h_touches⟩ := he
      rw [h_isolated e he_ne h_touches, pow_zero]
    rw [h_touching, one_mul]
    -- Convert erase ∩ ¬touching = filter (i ∉ e ∧ j ∉ e).
    refine Finset.prod_congr (Finset.ext fun e => ?_) (fun _ _ => rfl)
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true,
               not_or]
    refine ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun h_eq => ?_, h⟩⟩
    rw [h_eq] at h
    exact h.1 (Sym2.mem_mk_left i j)
  -- Step 7 foundations: cardinality of complement subtype, n ≥ 2.
  have hn_ge_2 : 2 ≤ n := by
    by_contra h
    push_neg at h
    -- h : n < 2. Since u_p : Fin n, n ≥ 1. So n = 1. Then Fin 1 is subsingleton.
    have h_ge_1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun heq => by
      rw [heq] at u_p
      exact u_p.elim0)
    have hn1 : n = 1 := by omega
    subst hn1
    exact hu_p_ne_v_p (Subsingleton.elim u_p v_p)
  -- Subtype p = {u_p, v_p} has exactly 2 elements (using subtypeEquiv).
  have h_card_p : Fintype.card (Subtype p) = 2 := by
    rw [Fintype.card_of_bijective subtypeEquiv.bijective]
    simp
  -- The complement has cardinality n - 2.
  have h_card_compl : Fintype.card {k // ¬ p k} = n - 2 := by
    have h_total : Fintype.card (Subtype p) + Fintype.card {k // ¬ p k} =
                   Fintype.card (Fin n) := by
      rw [← Fintype.card_sum]
      exact Fintype.card_congr (Equiv.sumCompl p)
    rw [Fintype.card_fin] at h_total
    omega
  -- Step 7 continued: build the complement Equiv {k // ¬ p k} ≃ Fin (n - 2).
  let complEquiv : {k // ¬ p k} ≃ Fin (n - 2) :=
    Fintype.equivFinOfCardEq h_card_compl
  -- The restEmbed: instantiate top-level restEmbedAux with the injection
  -- from Fin (n-2) into Fin n via complEquiv.symm.
  let g_rest : Fin (n - 2) → Fin n := fun r => (complEquiv.symm r).val
  have g_rest_injective : Function.Injective g_rest := by
    intro r₁ r₂ h_eq
    have : (complEquiv.symm r₁ : {k // ¬ p k}) = complEquiv.symm r₂ :=
      Subtype.ext h_eq
    exact complEquiv.symm.injective this
  let restEmbed : Fin (n - 2 + K) → Fin (n + K) := @restEmbedAux n K (n - 2) g_rest
  -- F_rest: simple graph on Fin (n - 2 + K) with edges from mult-1 edges of M.
  let F_rest : SimpleGraph (Fin (n - 2 + K)) :=
    { Adj := fun a b => a ≠ b ∧ M.mult s(restEmbed a, restEmbed b) = 1
      symm := fun a b ⟨hne, hmult⟩ =>
        ⟨hne.symm, by rwa [Sym2.eq_swap]⟩
      loopless := fun a ⟨hne, _⟩ => hne rfl }
  haveI : DecidableRel F_rest.Adj := Classical.decRel _
  -- Step 7 application: instantiate h_simple at F_rest. This gives the
  -- equality of F_rest's evaluation at ξ vs ξ' for free.
  have h_simple_F_rest := h_simple (n - 2) F_rest
  -- Step 7 named local lemma h_rest_eval (statement only; body sorry'd).
  -- Parameterized by α : Fin 2 → Fin T so τ is fully defined via
  -- σ = splitSigma.symm (α, ρ); no `default : Fin T` needed (Path 2).
  have h_rest_eval : ∀ (α : Fin 2 → Fin T) (η : Fin K → Fin T),
      (∑ σ_rest : Fin (n - 2) → Fin T,
        (let τ_rest : Fin (n - 2 + K) → Fin T := fun v =>
          if h : (v : ℕ) < K then η ⟨v, h⟩
          else σ_rest ⟨v - K, by have := v.isLt; omega⟩
        (∏ v : Fin (n - 2), W (σ_rest v)) *
        ∏ e ∈ F_rest.edgeFinset,
          B (τ_rest (Quot.out e).1) (τ_rest (Quot.out e).2))) =
      (∑ ρ : {k : Fin n // ¬ p k} → Fin T,
        (let σ : Fin n → Fin T := splitSigma.symm (α, ρ)
         let τ : Fin (n + K) → Fin T := fun v =>
          if h : (v : ℕ) < K then η ⟨v, h⟩
          else σ ⟨v - K, by have := v.isLt; omega⟩
        (∏ k : {k : Fin n // ¬ p k}, W (ρ k)) *
        ∏ e ∈ (Finset.univ.filter (fun e : Sym2 (Fin (n + K)) => i ∉ e ∧ j ∉ e) :
                Finset (Sym2 (Fin (n + K)))),
          B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ M.mult e)) := by
    intro α η
    -- Step 7a: reindex the σ_rest-sum to a ρ-sum via Equiv.arrowCongr complEquiv.
    let arrowE : ({k : Fin n // ¬ p k} → Fin T) ≃ (Fin (n - 2) → Fin T) :=
      Equiv.arrowCongr complEquiv (Equiv.refl (Fin T))
    rw [← arrowE.sum_comp]
    -- Now: ∑ ρ, F_rest_body (arrowE ρ) = ∑ ρ, [W-prod * complement-B-prod].
    -- Step 7b (per-ρ): show F_rest_body (arrowE ρ) = W-prod * complement-B-prod.
    refine Finset.sum_congr rfl fun ρ _ => ?_
    -- Step 7b₁ (hW_rest): W-product match via Equiv.prod_comp complEquiv.symm.
    have hW_rest : (∏ r : Fin (n - 2), W ((arrowE ρ) r)) =
                   ∏ k : {k : Fin n // ¬ p k}, W (ρ k) :=
      complEquiv.symm.prod_comp (fun k => W (ρ k))
    -- Step 7b₂ (hE_rest): edge-product match via Sym2.map restEmbed.
    -- First: membership equivalence for F_rest.edgeFinset.
    have hmem : ∀ e : Sym2 (Fin (n - 2 + K)),
        e ∈ F_rest.edgeFinset ↔
        (Sym2.lift ⟨fun a b : Fin (n - 2 + K) => a ≠ b, fun _ _ => propext ne_comm⟩ e ∧
         M.mult (Sym2.map restEmbed e) = 1) := by
      intro e
      induction e with
      | h a b =>
        show s(a, b) ∈ F_rest.edgeFinset ↔ (a ≠ b ∧ M.mult (Sym2.map restEmbed s(a, b)) = 1)
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        show (a ≠ b ∧ M.mult s(restEmbed a, restEmbed b) = 1) ↔
             (a ≠ b ∧ M.mult (Sym2.map restEmbed s(a, b)) = 1)
        rw [Sym2.map_pair_eq]
    -- Step 7b₂ continued: restEmbed injectivity via the top-level lemma.
    have restEmbed_injective : Function.Injective restEmbed :=
      restEmbedAux_injective g_rest_injective
    -- Sym2 injectivity (lift restEmbed_injective to Sym2.map).
    have hSym2inj : Function.Injective (fun e : Sym2 (Fin (n - 2 + K)) =>
        Sym2.map restEmbed e) := Sym2.map.injective restEmbed_injective
    -- Surjectivity onto mult-1 complement edges. For each edge e in the
    -- complement filter with M.mult e = 1, build a preimage in F_rest.edgeFinset
    -- via complEquiv on unlabeled endpoints and label-identity on label endpoints.
    -- Uses the isolation hypothesis to ensure non-(u_p, v_p) unlabeled endpoints
    -- have ¬ p, hence are in the complEquiv domain.
    have h_surj : ∀ e : Sym2 (Fin (n + K)),
        e ∈ (Finset.univ.filter (fun e => i ∉ e ∧ j ∉ e) :
              Finset (Sym2 (Fin (n + K)))) →
        M.mult e = 1 →
        ∃ e' : Sym2 (Fin (n - 2 + K)),
          e' ∈ F_rest.edgeFinset ∧ Sym2.map restEmbed e' = e := by
      intro e he hmult
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      induction e with
      | h a b =>
        obtain ⟨hi_notin, hj_notin⟩ := he
        rw [Sym2.mem_iff, not_or] at hi_notin hj_notin
        -- hi_notin : i ≠ a ∧ i ≠ b; hj_notin : j ≠ a ∧ j ≠ b.
        have ha_ne_i : a ≠ i := fun h => hi_notin.1 h.symm
        have hb_ne_i : b ≠ i := fun h => hi_notin.2 h.symm
        have ha_ne_j : a ≠ j := fun h => hj_notin.1 h.symm
        have hb_ne_j : b ≠ j := fun h => hj_notin.2 h.symm
        -- a ≠ b from M.mult = 1 + multNoLoop.
        have hab_ne : a ≠ b := by
          intro h_eq
          rw [h_eq] at hmult
          have := M.multNoLoop b
          omega
        -- Endpoint preimage helper.
        have endpoint_preimage : ∀ x : Fin (n + K), x ≠ i → x ≠ j →
            ∃ y : Fin (n - 2 + K), restEmbed y = x := by
          intro x hxi hxj
          by_cases hx_lab : x.val < K
          · -- Label case.
            refine ⟨⟨x.val, by have := hn_ge_2; omega⟩, ?_⟩
            apply Fin.ext
            exact restEmbedAux_val_lab g_rest ⟨x.val, by have := hn_ge_2; omega⟩ hx_lab
          · -- Unlabeled case.
            push_neg at hx_lab
            let x_un : Fin n := ⟨x.val - K, by have := x.isLt; omega⟩
            have hx_un_ne_u_p : x_un ≠ u_p := by
              intro h_eq
              apply hxi
              apply Fin.ext
              have hval : x_un.val = u_p.val := by rw [h_eq]
              have h_x_K : x_un.val = x.val - K := rfl
              have h_u_eq : u_p.val = i.val - K := rfl
              show x.val = i.val
              omega
            have hx_un_ne_v_p : x_un ≠ v_p := by
              intro h_eq
              apply hxj
              apply Fin.ext
              have hval : x_un.val = v_p.val := by rw [h_eq]
              have h_x_K : x_un.val = x.val - K := rfl
              have h_v_eq : v_p.val = j.val - K := rfl
              show x.val = j.val
              omega
            have hx_un_not_p : ¬ p x_un := by
              intro h
              rcases h with h_u | h_v
              · exact hx_un_ne_u_p h_u
              · exact hx_un_ne_v_p h_v
            let x_subt : {k : Fin n // ¬ p k} := ⟨x_un, hx_un_not_p⟩
            let x_fin : Fin (n - 2) := complEquiv x_subt
            refine ⟨⟨x_fin.val + K, by have := x_fin.isLt; omega⟩, ?_⟩
            apply Fin.ext
            -- restEmbed y = x.
            have hy_not_lab : ¬ (x_fin.val + K < K) := by omega
            rw [restEmbedAux_val_rest g_rest _ hy_not_lab]
            -- (g_rest ⟨(x_fin.val + K) - K, _⟩).val + K = x.val.
            -- Simplify: (x_fin.val + K) - K = x_fin.val.
            have h_arg_simp : (⟨x_fin.val + K - K,
                by have := x_fin.isLt; omega⟩ : Fin (n - 2)) = x_fin := by
              apply Fin.ext; show x_fin.val + K - K = x_fin.val; omega
            rw [h_arg_simp]
            show (complEquiv.symm x_fin).val.val + K = x.val
            -- complEquiv.symm x_fin = complEquiv.symm (complEquiv x_subt) = x_subt.
            rw [show x_fin = complEquiv x_subt from rfl, Equiv.symm_apply_apply]
            show x_un.val + K = x.val
            have : x_un.val = x.val - K := rfl
            omega
        -- Apply to a and b.
        obtain ⟨a', ha'⟩ := endpoint_preimage a ha_ne_i ha_ne_j
        obtain ⟨b', hb'⟩ := endpoint_preimage b hb_ne_i hb_ne_j
        refine ⟨s(a', b'), ?_, ?_⟩
        · -- s(a', b') ∈ F_rest.edgeFinset via hmem.
          rw [hmem]
          refine ⟨?_, ?_⟩
          · -- a' ≠ b': restEmbed a' = a ≠ b = restEmbed b'.
            show a' ≠ b'
            intro h_eq
            exact hab_ne (ha'.symm.trans ((congrArg restEmbed h_eq).trans hb'))
          · -- M.mult (Sym2.map restEmbed s(a', b')) = 1.
            rw [Sym2.map_pair_eq, ha', hb']
            exact hmult
        · -- Sym2.map restEmbed s(a', b') = s(a, b).
          rw [Sym2.map_pair_eq, ha', hb']
    -- Step 7b₂ remainder: assemble the per-ρ body equality.
    -- Both sides are W-product * B-product. Split via congr 1.
    dsimp only
    rw [hW_rest]
    congr 1
    -- Now goal is: ∏ e ∈ F_rest.edgeFinset, B(τ_rest_e) =
    --              ∏ e ∈ complement_filter, B(τ_e)^M.mult e.
    -- Introduce named τ's to make h_value, h_rhs_filter, h_lhs_reindex tractable.
    set τ_rest : Fin (n - 2 + K) → Fin T := fun v =>
      if h : (v : ℕ) < K then η ⟨v, h⟩
      else (arrowE ρ) ⟨v - K, by have := v.isLt; omega⟩ with hτ_rest_def
    set τ_orig : Fin (n + K) → Fin T := fun v =>
      if h : (v : ℕ) < K then η ⟨v, h⟩
      else (splitSigma.symm (α, ρ)) ⟨v - K, by have := v.isLt; omega⟩ with hτ_orig_def
    -- Step 0: hτ_compat — τ_orig (restEmbed v) = τ_rest v.
    have hτ_compat : ∀ v : Fin (n - 2 + K), τ_orig (restEmbed v) = τ_rest v := by
      intro v
      by_cases h_lab : v.val < K
      · -- Label case.
        have h_re_val : (restEmbed v).val = v.val := restEmbedAux_val_lab g_rest v h_lab
        have h_re_lab : (restEmbed v).val < K := by rw [h_re_val]; exact h_lab
        show (if h : (restEmbed v).val < K then η ⟨(restEmbed v).val, h⟩
              else (splitSigma.symm (α, ρ))
                ⟨(restEmbed v).val - K, by have := (restEmbed v).isLt; omega⟩) =
             (if h : v.val < K then η ⟨v.val, h⟩
              else (arrowE ρ) ⟨v.val - K, by have := v.isLt; omega⟩)
        rw [dif_pos h_re_lab, dif_pos h_lab]
        congr 1
        exact Fin.ext h_re_val
      · -- Rest case.
        push_neg at h_lab
        have h_v_not_lab : ¬ v.val < K := not_lt.mpr h_lab
        let r : Fin (n - 2) := ⟨v.val - K, by have := v.isLt; omega⟩
        let k : {x : Fin n // ¬ p x} := complEquiv.symm r
        have h_re_val : (restEmbed v).val = k.val.val + K :=
          restEmbedAux_val_rest g_rest v h_v_not_lab
        have h_re_not_lab : ¬ (restEmbed v).val < K := by
          intro h_lt; have := h_re_val; omega
        show (if h : (restEmbed v).val < K then η ⟨(restEmbed v).val, h⟩
              else (splitSigma.symm (α, ρ))
                ⟨(restEmbed v).val - K, by have := (restEmbed v).isLt; omega⟩) =
             (if h : v.val < K then η ⟨v.val, h⟩
              else (arrowE ρ) ⟨v.val - K, by have := v.isLt; omega⟩)
        rw [dif_neg h_re_not_lab, dif_neg h_v_not_lab]
        have hk_fin :
            (⟨(restEmbed v).val - K, by have := (restEmbed v).isLt; omega⟩ : Fin n) = k.val := by
          apply Fin.ext
          have : (restEmbed v).val - K = k.val.val := by have := h_re_val; omega
          exact this
        have h_step :
            (splitSigma.symm (α, ρ))
              ⟨(restEmbed v).val - K, by have := (restEmbed v).isLt; omega⟩ =
            (splitSigma.symm (α, ρ)) k.val := by rw [hk_fin]
        rw [h_step, h_at_rest α ρ k.val k.property]
        -- Goal: ρ ⟨k.val, k.property⟩ = arrowE ρ r.
        show ρ ⟨k.val, k.property⟩ = (arrowE ρ) r
        have hk_subt : (⟨k.val, k.property⟩ : {x : Fin n // ¬ p x}) = k := Subtype.ext rfl
        rw [hk_subt]
        rfl
    -- Step 1: h_value — per-edge B value preservation under Sym2.map restEmbed.
    have h_value : ∀ e ∈ F_rest.edgeFinset,
        B (τ_rest (Quot.out e).1) (τ_rest (Quot.out e).2) =
        B (τ_orig (Quot.out (Sym2.map restEmbed e)).1)
          (τ_orig (Quot.out (Sym2.map restEmbed e)).2) := by
      intro e _
      induction e with
      | h a b =>
        rw [B_quot_out_eq hB τ_rest a b]
        rw [Sym2.map_pair_eq]
        rw [B_quot_out_eq hB τ_orig (restEmbed a) (restEmbed b)]
        rw [hτ_compat a, hτ_compat b]
    -- Step 2: h_rhs_filter — split complement product by M.mult = 1.
    have h_rhs_filter :
        (∏ e ∈ (Finset.univ.filter (fun e : Sym2 (Fin (n + K)) =>
                i ∉ e ∧ j ∉ e) : Finset (Sym2 (Fin (n + K)))),
          B (τ_orig (Quot.out e).1) (τ_orig (Quot.out e).2) ^ M.mult e) =
        (∏ e ∈ ((Finset.univ.filter (fun e : Sym2 (Fin (n + K)) =>
                  i ∉ e ∧ j ∉ e)).filter (fun e => M.mult e = 1) :
                Finset (Sym2 (Fin (n + K)))),
          B (τ_orig (Quot.out e).1) (τ_orig (Quot.out e).2)) := by
      rw [← Finset.prod_filter_mul_prod_filter_not
            (Finset.univ.filter (fun e : Sym2 (Fin (n + K)) => i ∉ e ∧ j ∉ e))
            (fun e => M.mult e = 1)
            (fun e => B (τ_orig (Quot.out e).1) (τ_orig (Quot.out e).2) ^ M.mult e)]
      have h_zero_part :
          (∏ e ∈ (Finset.univ.filter (fun e : Sym2 (Fin (n + K)) =>
                  i ∉ e ∧ j ∉ e)).filter (fun e => ¬ M.mult e = 1),
            B (τ_orig (Quot.out e).1) (τ_orig (Quot.out e).2) ^ M.mult e) = 1 := by
        apply Finset.prod_eq_one
        intro e he
        rw [Finset.mem_filter, Finset.mem_filter] at he
        obtain ⟨⟨_, h_compl⟩, h_ne_1⟩ := he
        have h_ne_doubled : e ≠ s(i, j) := by
          intro heq
          rw [heq] at h_compl
          exact h_compl.1 (Sym2.mem_mk_left i j)
        have h_le_1 : M.mult e ≤ 1 := h_others_le_one e h_ne_doubled
        have h_zero : M.mult e = 0 := by omega
        rw [h_zero, pow_zero]
      rw [h_zero_part, mul_one]
      refine Finset.prod_congr rfl fun e he => ?_
      rw [Finset.mem_filter] at he
      rw [he.2, pow_one]
    -- Helpers: restEmbed never hits i or j (image avoids u_p, v_p positions).
    have h_restEmbed_ne_i : ∀ v : Fin (n - 2 + K), restEmbed v ≠ i := by
      intro v h_eq
      by_cases h_lab : v.val < K
      · have hv : (restEmbed v).val = v.val := restEmbedAux_val_lab g_rest v h_lab
        have : v.val = i.val := by rw [← hv, h_eq]
        omega
      · push_neg at h_lab
        have hv : (restEmbed v).val =
            (g_rest ⟨v.val - K, by have := v.isLt; omega⟩).val + K :=
          restEmbedAux_val_rest g_rest v (not_lt.mpr h_lab)
        have h_eq_val : (restEmbed v).val = i.val := by rw [h_eq]
        have h_i_lift_val : i.val = u_p.val + K := by
          have := congr_arg Fin.val hi_lift; simpa using this
        have h_g_val : (g_rest ⟨v.val - K, by have := v.isLt; omega⟩).val = u_p.val := by omega
        have h_complEquiv_prop := (complEquiv.symm
            (⟨v.val - K, by have := v.isLt; omega⟩ : Fin (n - 2))).property
        apply h_complEquiv_prop
        left
        apply Fin.ext
        exact h_g_val
    have h_restEmbed_ne_j : ∀ v : Fin (n - 2 + K), restEmbed v ≠ j := by
      intro v h_eq
      by_cases h_lab : v.val < K
      · have hv : (restEmbed v).val = v.val := restEmbedAux_val_lab g_rest v h_lab
        have : v.val = j.val := by rw [← hv, h_eq]
        omega
      · push_neg at h_lab
        have hv : (restEmbed v).val =
            (g_rest ⟨v.val - K, by have := v.isLt; omega⟩).val + K :=
          restEmbedAux_val_rest g_rest v (not_lt.mpr h_lab)
        have h_eq_val : (restEmbed v).val = j.val := by rw [h_eq]
        have h_j_lift_val : j.val = v_p.val + K := by
          have := congr_arg Fin.val hj_lift; simpa using this
        have h_g_val : (g_rest ⟨v.val - K, by have := v.isLt; omega⟩).val = v_p.val := by omega
        have h_complEquiv_prop := (complEquiv.symm
            (⟨v.val - K, by have := v.isLt; omega⟩ : Fin (n - 2))).property
        apply h_complEquiv_prop
        right
        apply Fin.ext
        exact h_g_val
    -- Step 3: h_lhs_reindex via Finset.prod_nbij.
    have h_lhs_reindex :
        (∏ e ∈ F_rest.edgeFinset,
          B (τ_rest (Quot.out e).1) (τ_rest (Quot.out e).2)) =
        (∏ e ∈ ((Finset.univ.filter (fun e : Sym2 (Fin (n + K)) =>
                  i ∉ e ∧ j ∉ e)).filter (fun e => M.mult e = 1) :
                Finset (Sym2 (Fin (n + K)))),
          B (τ_orig (Quot.out e).1) (τ_orig (Quot.out e).2)) := by
      refine Finset.prod_nbij (fun e => Sym2.map restEmbed e) ?mem ?inj ?surj ?value
      case mem =>
        intro e he
        rw [Finset.mem_filter, Finset.mem_filter]
        refine ⟨⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · show i ∉ Sym2.map restEmbed e ∧ j ∉ Sym2.map restEmbed e
          induction e with
          | h a b =>
            rw [Sym2.map_pair_eq]
            refine ⟨?_, ?_⟩
            · rw [Sym2.mem_iff]
              rintro (heq | heq)
              · exact h_restEmbed_ne_i a heq.symm
              · exact h_restEmbed_ne_i b heq.symm
            · rw [Sym2.mem_iff]
              rintro (heq | heq)
              · exact h_restEmbed_ne_j a heq.symm
              · exact h_restEmbed_ne_j b heq.symm
        · show M.mult (Sym2.map restEmbed e) = 1
          exact ((hmem e).mp he).2
      case inj => exact fun _ _ _ _ h_eq => hSym2inj h_eq
      case surj =>
        intro e he
        simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter,
                   Finset.mem_univ, true_and, Set.mem_setOf_eq] at he
        obtain ⟨he_compl, he_mult⟩ := he
        obtain ⟨e', he'_mem, he'_eq⟩ := h_surj e
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he_compl⟩) he_mult
        exact ⟨e', he'_mem, he'_eq⟩
      case value => exact h_value
    -- Step 4: close via rewrites.
    rw [h_lhs_reindex, h_rhs_filter]
  -- Step 8: scalar congruence via normal-form lemma h_norm.
  -- Local scalar (α-only factor, ξ-independent).
  let scalar : ℝ := ∑ α : Fin 2 → Fin T, W (α 0) * W (α 1) * B (α 0) (α 1) ^ 2
  -- F_rest_eval η is the F_rest σ_rest-sum (inlined form, same as in h_rest_eval LHS).
  let F_rest_eval : (Fin K → Fin T) → ℝ := fun η =>
    ∑ σ_rest : Fin (n - 2) → Fin T,
      (let τ_rest : Fin (n - 2 + K) → Fin T := fun v =>
        if h : (v : ℕ) < K then η ⟨v, h⟩
        else σ_rest ⟨v - K, by have := v.isLt; omega⟩
      (∏ v : Fin (n - 2), W (σ_rest v)) *
      ∏ e ∈ F_rest.edgeFinset,
        B (τ_rest (Quot.out e).1) (τ_rest (Quot.out e).2))
  -- h_norm: multiLabeledEvalK M η = scalar * F_rest_eval η.
  have h_norm : ∀ η : Fin K → Fin T,
      multiLabeledEvalK K n M B W η = scalar * F_rest_eval η := by
    intro η
    unfold multiLabeledEvalK
    rw [← splitSigma.symm.sum_comp]
    rw [Fintype.sum_prod_type]
    -- Per-(α, ρ) body factor via hW_factor + hB_factor.
    rw [show (∑ α : Fin 2 → Fin T, ∑ ρ : {k : Fin n // ¬ p k} → Fin T,
              (let τ : Fin (n + K) → Fin T := fun v =>
                if h : (v : ℕ) < K then η ⟨v, h⟩
                else (splitSigma.symm (α, ρ)) ⟨v - K, by have := v.isLt; omega⟩
              (∏ v : Fin n, W ((splitSigma.symm (α, ρ)) v)) *
              ∏ e : Sym2 (Fin (n + K)),
                B (τ (Quot.out e).1) (τ (Quot.out e).2) ^ M.mult e)) =
            ∑ α : Fin 2 → Fin T, ∑ ρ : {k : Fin n // ¬ p k} → Fin T,
              (W (α 0) * W (α 1) * B (α 0) (α 1) ^ 2) *
              ((∏ k : {k : Fin n // ¬ p k}, W (ρ k)) *
               (∏ e ∈ (Finset.univ.filter
                  (fun e : Sym2 (Fin (n + K)) => i ∉ e ∧ j ∉ e) :
                  Finset (Sym2 (Fin (n + K)))),
                 B ((fun v : Fin (n + K) =>
                      if h : (v : ℕ) < K then η ⟨v, h⟩
                      else (splitSigma.symm (α, ρ))
                        ⟨v - K, by have := v.isLt; omega⟩)
                    (Quot.out e).1)
                   ((fun v : Fin (n + K) =>
                      if h : (v : ℕ) < K then η ⟨v, h⟩
                      else (splitSigma.symm (α, ρ))
                        ⟨v - K, by have := v.isLt; omega⟩)
                    (Quot.out e).2) ^ M.mult e)) from by
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun ρ _ => ?_
      dsimp only
      rw [hW_factor α ρ, hB_factor α ρ η]
      ring]
    -- Pull α-scalar out of inner ρ-sum (Finset.mul_sum direction).
    simp_rw [← Finset.mul_sum]
    -- Apply h_rest_eval in reverse to identify inner ρ-sum with F_rest_eval η.
    simp_rw [← h_rest_eval _ η]
    -- Pull F_rest_eval η out of α-sum (closes goal definitionally).
    rw [← Finset.sum_mul]
  -- Conclude via h_norm + h_simple_F_rest.
  have h_compat : F_rest_eval ξ = F_rest_eval ξ' := h_simple_F_rest
  rw [h_norm ξ, h_norm ξ', h_compat]

/-- **Label-unlabeled isolated reduction**: doubled edge with one label endpoint
`a` and one unlabeled endpoint `b`, where no other edges touch `b`. Reduces to
the K=1 square moment via splitSigma at `b` (parallel to UU isolated proof):
the σ_b-sum factors as `(∑_t W(t) · B(ξ_a, t)²) · F_rest_eval ξ`, where the
scalar factor IS the K=1 square moment. Dependency: the FINAL paper-root
`label_unlabeled_square_moment_descends`. ~600 LOC parallel to UU isolated. -/
private theorem multigraphEval_label_unlabeled_isolated_descends
    {T K n : ℕ} (B : Fin T → Fin T → ℝ) (_hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (M : MultiLabeledGraph K n)
    (a b : Fin (n + K))
    (_ha : a.val < K) (_hb : K ≤ b.val) (_hab : a ≠ b)
    (_h_doubled : M.mult s(a, b) = 2)
    (_h_others_le_one : ∀ e, e ≠ s(a, b) → M.mult e ≤ 1)
    (_h_b_iso : ∀ e, e ≠ s(a, b) → b ∈ e → M.mult e = 0)
    {ξ ξ' : Fin K → Fin T}
    (_h_simple : ∀ (n' : ℕ) (F : SimpleGraph (Fin (n' + K))) [DecidableRel F.Adj],
        ∑ σ : Fin n' → Fin T,
          (let τ : Fin (n' + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then ξ ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩
          (∏ v : Fin n', W (σ v)) *
          ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2)) =
        ∑ σ : Fin n' → Fin T,
          (let τ : Fin (n' + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then ξ' ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩
          (∏ v : Fin n', W (σ v)) *
          ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2))) :
    multiLabeledEvalK K n M B W ξ = multiLabeledEvalK K n M B W ξ' := by
  -- BLOCKED BY: label_unlabeled_square_moment_descends (FINAL paper-root).
  -- Proof pattern: parallel to UU isolated. splitSigma at b → factor σ-sum
  -- into scalar(ξ) · F_rest_eval ξ where scalar(ξ) = ∑_t W(t) · B(ξ_⟨a.val⟩, t)².
  -- Apply label_unlabeled_square_moment_descends to match scalar at ξ vs ξ'.
  -- F_rest_eval matches via h_simple on the simple graph from M's mult-1 edges.
  sorry

/-- **Label-unlabeled non-isolated reduction**: same orientation as above
but with other edges touching `b`. Reduces to the isolated case via peeling
those other edges. BLOCKED BY: label_unlabeled_square_moment_descends +
non-LL peel infrastructure. -/
private theorem multigraphEval_label_unlabeled_nonisolated_descends
    {T K n : ℕ} (B : Fin T → Fin T → ℝ) (_hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (M : MultiLabeledGraph K n)
    (a b : Fin (n + K))
    (_ha : a.val < K) (_hb : K ≤ b.val) (_hab : a ≠ b)
    (_h_doubled : M.mult s(a, b) = 2)
    (_h_others_le_one : ∀ e, e ≠ s(a, b) → M.mult e ≤ 1)
    (_h_b_not_iso : ¬ ∀ e, e ≠ s(a, b) → b ∈ e → M.mult e = 0)
    {ξ ξ' : Fin K → Fin T}
    (_h_simple : ∀ (n' : ℕ) (F : SimpleGraph (Fin (n' + K))) [DecidableRel F.Adj],
        ∑ σ : Fin n' → Fin T,
          (let τ : Fin (n' + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then ξ ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩
          (∏ v : Fin n', W (σ v)) *
          ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2)) =
        ∑ σ : Fin n' → Fin T,
          (let τ : Fin (n' + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then ξ' ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩
          (∏ v : Fin n', W (σ v)) *
          ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2))) :
    multiLabeledEvalK K n M B W ξ = multiLabeledEvalK K n M B W ξ' := by
  sorry

/-- **Unlabeled-label isolated reduction**: symmetric to label-unlabeled
isolated via Sym2.eq_swap. Same dependency: `label_unlabeled_square_moment_descends`. -/
private theorem multigraphEval_unlabeled_label_isolated_descends
    {T K n : ℕ} (B : Fin T → Fin T → ℝ) (_hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (M : MultiLabeledGraph K n)
    (a b : Fin (n + K))
    (_ha : K ≤ a.val) (_hb : b.val < K) (_hab : a ≠ b)
    (_h_doubled : M.mult s(a, b) = 2)
    (_h_others_le_one : ∀ e, e ≠ s(a, b) → M.mult e ≤ 1)
    (_h_a_iso : ∀ e, e ≠ s(a, b) → a ∈ e → M.mult e = 0)
    {ξ ξ' : Fin K → Fin T}
    (_h_simple : ∀ (n' : ℕ) (F : SimpleGraph (Fin (n' + K))) [DecidableRel F.Adj],
        ∑ σ : Fin n' → Fin T,
          (let τ : Fin (n' + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then ξ ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩
          (∏ v : Fin n', W (σ v)) *
          ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2)) =
        ∑ σ : Fin n' → Fin T,
          (let τ : Fin (n' + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then ξ' ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩
          (∏ v : Fin n', W (σ v)) *
          ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2))) :
    multiLabeledEvalK K n M B W ξ = multiLabeledEvalK K n M B W ξ' := by
  sorry

/-- **Unlabeled-label non-isolated reduction**: symmetric to
label-unlabeled non-isolated. -/
private theorem multigraphEval_unlabeled_label_nonisolated_descends
    {T K n : ℕ} (B : Fin T → Fin T → ℝ) (_hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (M : MultiLabeledGraph K n)
    (a b : Fin (n + K))
    (_ha : K ≤ a.val) (_hb : b.val < K) (_hab : a ≠ b)
    (_h_doubled : M.mult s(a, b) = 2)
    (_h_others_le_one : ∀ e, e ≠ s(a, b) → M.mult e ≤ 1)
    (_h_a_not_iso : ¬ ∀ e, e ≠ s(a, b) → a ∈ e → M.mult e = 0)
    {ξ ξ' : Fin K → Fin T}
    (_h_simple : ∀ (n' : ℕ) (F : SimpleGraph (Fin (n' + K))) [DecidableRel F.Adj],
        ∑ σ : Fin n' → Fin T,
          (let τ : Fin (n' + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then ξ ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩
          (∏ v : Fin n', W (σ v)) *
          ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2)) =
        ∑ σ : Fin n' → Fin T,
          (let τ : Fin (n' + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then ξ' ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩
          (∏ v : Fin n', W (σ v)) *
          ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2))) :
    multiLabeledEvalK K n M B W ξ = multiLabeledEvalK K n M B W ξ' := by
  sorry

/-- **UU non-isolated reduction**: doubled edge between two unlabeled vertices
with at least one OTHER edge touching `a` or `b`. Reduces to the proved
isolated UU theorem via peeling the offending edges. Dependency: the proved
`multigraphEval_isolated_unlabeled_unlabeled_doubled_edge_descends`. -/
private theorem multigraphEval_unlabeled_unlabeled_nonisolated_descends
    {T K n : ℕ} (B : Fin T → Fin T → ℝ) (_hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (M : MultiLabeledGraph K n)
    (a b : Fin (n + K))
    (_ha : K ≤ a.val) (_hb : K ≤ b.val) (_hab : a ≠ b)
    (_h_doubled : M.mult s(a, b) = 2)
    (_h_others_le_one : ∀ e, e ≠ s(a, b) → M.mult e ≤ 1)
    (_h_not_iso : ¬ ∀ e, e ≠ s(a, b) → (a ∈ e ∨ b ∈ e) → M.mult e = 0)
    {ξ ξ' : Fin K → Fin T}
    (_h_simple : ∀ (n' : ℕ) (F : SimpleGraph (Fin (n' + K))) [DecidableRel F.Adj],
        ∑ σ : Fin n' → Fin T,
          (let τ : Fin (n' + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then ξ ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩
          (∏ v : Fin n', W (σ v)) *
          ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2)) =
        ∑ σ : Fin n' → Fin T,
          (let τ : Fin (n' + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then ξ' ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩
          (∏ v : Fin n', W (σ v)) *
          ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2))) :
    multiLabeledEvalK K n M B W ξ = multiLabeledEvalK K n M B W ξ' := by
  -- BLOCKED BY: peel reduction to isolated UU case
  -- (`multigraphEval_isolated_unlabeled_unlabeled_doubled_edge_descends` is proved).
  -- Each peel removes one other edge touching `a` or `b`. Peel must handle
  -- non-LL edges (since other edges have at least one unlabeled endpoint —
  -- specifically `a` or `b`). Requires new non-LL peel infrastructure.
  sorry

/-- **FINAL PAPER-ROOT** — smallest unlabeled-excess subcase: one doubled
edge involving an unlabeled vertex, all other multiplicities ≤ 1.

**Algebraic analysis** (2026-05-19): given the above hypotheses, with
`e₀ = s(a, b)` the unique mult-2 edge having at least one endpoint
with `val ≥ K`, the σ-sum body of `multiLabeledEvalK M ξ` carries the
factor `B(τ_a, τ_b)²`. Three sub-sub-cases:

1. **Unlabeled-unlabeled, isolated endpoints** (no other edges touch
   `a` or `b`):
   `multiLabeledEvalK M ξ = (∑_{s,t} W(s)W(t) B(s,t)²) · labeledEvalK F' ξ`
   where the prefactor is **ξ-INDEPENDENT** and `F'` is the simple graph
   on the remaining vertices. Both factors match at ξ vs ξ' (the
   prefactor trivially, F' via `h_simple`). **Closable** via direct
   σ-sum factorization.

2. **Label-unlabeled, isolated unlabeled endpoint** (no other edges
   touch the unlabeled vertex `j`): the σ_j-sum reduces to the K=1
   square moment `∑_t W(t) · B(ξ_a, t)²`. This is **NOT** a polynomial
   in single-edge simple-graph evaluations (no simple graph evaluates
   to `B(ξ_a, t)²`). Its ξ-invariance under `tupleEquivSimple` is
   exactly the substantive Lovász §3 content (Lemma 2.5: every
   auto-invariant function is in the simple-graph eval span; the
   square moment is auto-invariant).

3. **General doubled edge with other edges touching the endpoint(s)**:
   the σ-sum involves mixed moments combining `B(?,t)²` with other
   `B(t, ?)¹` factors. Strictly harder than case 2; reducible to
   case 2 after handling the label-touching contributions, but the
   reduction is itself non-trivial.

**Conclusion**: the **smallest genuine paper-root** is the K=1 square
moment identity (case 2 — the simplest case requiring genuine Lovász §3
content). Closing it requires the connection-matrix / idempotent
decomposition of the multigraph algebra `𝒜_K`. ~300-500 LOC of new
spectral/rank infrastructure.

**Status** (2026-05-19): PROMOTED as the final paper-root per directive.
The unlabeled-unlabeled isolated case (1) is algebraically closable but
is not the bottleneck. The label-unlabeled isolated case (2) — the K=1
square moment — IS the bottleneck. -/
private theorem multigraphEval_one_doubled_unlabeled_edge_descends {T K n : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (M : MultiLabeledGraph K n)
    (e₀ : Sym2 (Fin (n + K)))
    (he₀_unlabeled : ¬ isLLEdge e₀)
    (he₀_doubled : M.mult e₀ = 2)
    (h_others_le_one : ∀ e, e ≠ e₀ → M.mult e ≤ 1)
    {ξ ξ' : Fin K → Fin T}
    (h_simple : ∀ (n' : ℕ) (F : SimpleGraph (Fin (n' + K))) [DecidableRel F.Adj],
        ∑ σ : Fin n' → Fin T,
          (let τ : Fin (n' + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then ξ ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩
          (∏ v : Fin n', W (σ v)) *
          ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2)) =
        ∑ σ : Fin n' → Fin T,
          (let τ : Fin (n' + K) → Fin T := fun v =>
            if h : (v : ℕ) < K then ξ' ⟨v, h⟩
            else σ ⟨v - K, by have := v.isLt; omega⟩
          (∏ v : Fin n', W (σ v)) *
          ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2))) :
    multiLabeledEvalK K n M B W ξ = multiLabeledEvalK K n M B W ξ' := by
  classical
  -- Case analysis on the orientation of `e₀`.
  induction e₀ using Sym2.ind with
  | h a b =>
    -- `M.mult e₀ = 2` ⟹ `a ≠ b` (no self-loop).
    have hab_ne : a ≠ b := by
      intro h_eq
      have h_loop : M.mult s(a, b) = 0 := by rw [h_eq]; exact M.multNoLoop b
      rw [he₀_doubled] at h_loop; omega
    by_cases ha_lab : a.val < K
    · by_cases hb_lab : b.val < K
      · -- Both labels: contradicts `he₀_unlabeled`.
        exact absurd (show a.val < K ∧ b.val < K from ⟨ha_lab, hb_lab⟩) he₀_unlabeled
      · -- `a` label, `b` unlabeled. Label-unlabeled case.
        push_neg at hb_lab
        by_cases h_b_iso : ∀ e, e ≠ s(a, b) → b ∈ e → M.mult e = 0
        · exact multigraphEval_label_unlabeled_isolated_descends
            B hB W M a b ha_lab hb_lab hab_ne he₀_doubled h_others_le_one h_b_iso h_simple
        · exact multigraphEval_label_unlabeled_nonisolated_descends
            B hB W M a b ha_lab hb_lab hab_ne he₀_doubled h_others_le_one h_b_iso h_simple
    · push_neg at ha_lab
      by_cases hb_lab : b.val < K
      · -- `a` unlabeled, `b` label.
        by_cases h_a_iso : ∀ e, e ≠ s(a, b) → a ∈ e → M.mult e = 0
        · exact multigraphEval_unlabeled_label_isolated_descends
            B hB W M a b ha_lab hb_lab hab_ne he₀_doubled h_others_le_one h_a_iso h_simple
        · exact multigraphEval_unlabeled_label_nonisolated_descends
            B hB W M a b ha_lab hb_lab hab_ne he₀_doubled h_others_le_one h_a_iso h_simple
      · -- Both unlabeled.
        push_neg at hb_lab
        by_cases h_iso : ∀ e, e ≠ s(a, b) → (a ∈ e ∨ b ∈ e) → M.mult e = 0
        · -- **Isolated unlabeled-unlabeled doubled edge** — CLOSED via
          -- `multigraphEval_isolated_unlabeled_unlabeled_doubled_edge_descends` (proved).
          exact multigraphEval_isolated_unlabeled_unlabeled_doubled_edge_descends
            B hB W M a b ha_lab hb_lab hab_ne he₀_doubled h_others_le_one h_iso h_simple
        · -- **Non-isolated unlabeled-unlabeled** — dispatch to named reduction.
          exact multigraphEval_unlabeled_unlabeled_nonisolated_descends
            B hB W M a b ha_lab hb_lab hab_ne he₀_doubled h_others_le_one h_iso h_simple

/-- **Canonical paper-root for #62**: every multigraph evaluation is in
the simple-profile closure.

**Proof outline** (Lovász §3 substantive content, ~300-500 LOC):
The space of functions on `tupleEquivSimple`-classes forms a finite-
dimensional ℝ-algebra. Simple-graph evaluations span this algebra (by
the rank theorem). Multigraph evaluations factor through this algebra
via the connection-matrix idempotent decomposition. The "subgraph
counts" of all multigraphs are polynomial combinations of subgraph
counts of simple graphs.

**Status** (2026-05-19): #86 is now a clean wrapper over three cases:

  1. **n = 0 / mults ≤ 1**: dispatched in-line via existing infrastructure
     (`multiLabeledEvalK_tupleEquiv_invariant_n_zero` / simple-graph
     correspondence + `h_equiv`).

  2. **LL-excess sub-case** (every mult≥2 edge is label-label):
     **CLOSED** via `multigraphEval_LL_excess_descends_aux` (strong
     induction on `M.LLSum`; iterated single-edge peel; base case
     reduces to a simple graph). Polynomial decomposition à la
     Lovász §3.2 (F₁F₂-product).

  3. **Unlabeled-excess sub-case** (some mult≥2 edge touches an
     unlabeled vertex): **DISPATCHED** to the named paper-root
     `multigraphEval_unlabeled_excess_descends` (the final residual
     Lovász §3 content; ~300-500 LOC of new spectral/rank
     infrastructure for the multigraph algebra `𝒜_K`).

Step 1 (`of_const_on_tupleEquivSimple`, Lagrange fullness) is PROVED.
The only remaining sorry is inside `multigraphEval_unlabeled_excess_descends`. -/
theorem multigraphEval_in_simpleProfileClosure {T K n : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (M : MultiLabeledGraph K n) :
    InSimpleProfileClosure B W K (fun ξ => multiLabeledEvalK K n M B W ξ) := by
  apply InSimpleProfileClosure.of_const_on_tupleEquivSimple
  intro ξ ξ' h_equiv
  -- Descent: multiLabeledEvalK is constant on inlined-tupleEquivSimple classes.
  -- Case split on n and multiplicities, matching the existing
  -- `multiLabeledEvalK_tupleEquiv_invariant` (#62) wrapper structure.
  -- The mult ≥ 2 case is the substantive Lovász §3 content (sorry'd here).
  match n, M with
  | 0, M => exact multiLabeledEvalK_tupleEquiv_invariant_n_zero B hB W M
              (fun n' F hF => h_equiv n' F)
  | n + 1, M =>
    by_cases h_mult_le_one : ∀ e, M.mult e ≤ 1
    · classical
      let F : SimpleGraph (Fin ((n + 1) + K)) :=
        { Adj := fun a b => a ≠ b ∧ M.mult s(a, b) = 1
          symm := fun a b ⟨hne, hmult⟩ =>
            ⟨hne.symm, by rwa [Sym2.eq_swap]⟩
          loopless := fun a ⟨hne, _⟩ => hne rfl }
      haveI : DecidableRel F.Adj := Classical.decRel _
      have hmult_eq : ∀ e, M.mult e = (MultiLabeledGraph.ofSimple F).mult e := by
        intro e
        induction e with
        | h a b =>
          show M.mult s(a, b) = if s(a, b) ∈ F.edgeFinset then 1 else 0
          by_cases hM : M.mult s(a, b) = 0
          · rw [hM]
            have : ¬ s(a, b) ∈ F.edgeFinset := by
              rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
              intro ⟨_, hmult⟩
              rw [hM] at hmult; exact absurd hmult (by omega)
            rw [if_neg this]
          · have hM_one : M.mult s(a, b) = 1 := by
              have := h_mult_le_one s(a, b); omega
            rw [hM_one]
            have : s(a, b) ∈ F.edgeFinset := by
              rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
              refine ⟨?_, hM_one⟩
              intro hab; rw [hab] at hM_one
              have := M.multNoLoop b; omega
            rw [if_pos this]
      have hev : ∀ ζ : Fin K → Fin T,
          multiLabeledEvalK K (n + 1) M B W ζ =
          multiLabeledEvalK K (n + 1) (MultiLabeledGraph.ofSimple F) B W ζ := by
        intro ζ
        unfold multiLabeledEvalK
        refine Finset.sum_congr rfl fun σ _ => ?_
        simp_rw [hmult_eq]
      rw [hev ξ, hev ξ', multiLabeledEvalK_ofSimple, multiLabeledEvalK_ofSimple]
      exact h_equiv (n + 1) F
    · -- Multiplicity ≥ 2 sub-case. Architectural refinement: split on
      -- whether the excess multiplicity sits at label-label edges (LL,
      -- handled by polynomial decomposition) or at edges touching some
      -- unlabeled vertex (the genuinely hard Lovász §3 content).
      classical
      -- LL predicate on Sym2 pairs of vertices in `Fin ((n+1)+K)`:
      -- both endpoints have val < K (i.e., are labels).
      let isLL : Sym2 (Fin ((n + 1) + K)) → Prop := fun e =>
        Sym2.lift ⟨fun a b => (a.val < K ∧ b.val < K),
          fun a b => propext ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩⟩ e
      haveI : DecidablePred isLL := fun e =>
        Quot.recOnSubsingleton (motive := fun e => Decidable (isLL e)) e
          (fun p => (inferInstance : Decidable (p.1.val < K ∧ p.2.val < K)))
      by_cases h_LL_excess : ∀ e, M.mult e ≥ 2 → isLL e
      · -- **LL-excess sub-case** — CLOSED via `multigraphEval_LL_excess_descends_aux`.
        -- Strong induction on M.LLSum: each iteration peels a single LL edge
        -- via `multiLabeledEvalK_decAt_LL_peel`, applying h_equiv on the
        -- single-edge LL graph to match B(ξ_a, ξ_b) at ξ vs ξ'. Base case:
        -- all LL mults zero → M has all mults ≤ 1 → simple graph case.
        have h_nonLL_le_one : ∀ e, ¬ isLLEdge e → M.mult e ≤ 1 := by
          intro e he
          by_contra h_ge
          push_neg at h_ge
          have hLL := h_LL_excess e (by omega)
          exact he hLL
        exact multigraphEval_LL_excess_descends_aux B hB W
          (fun n' F _ => h_equiv n' F) M.LLSum M h_nonLL_le_one rfl
      · -- **Unlabeled-excess sub-case** — dispatched to the canonical
        -- paper-root `multigraphEval_unlabeled_excess_descends`. The
        -- hypothesis `h_LL_excess` is false here, so some mult≥2 edge
        -- is non-LL (touches an unlabeled vertex).
        have h_unlabeled_excess :
            ∃ e : Sym2 (Fin ((n + 1) + K)), ¬ isLLEdge e ∧ 2 ≤ M.mult e := by
          push_neg at h_LL_excess
          obtain ⟨e, he_mult, he_notLL⟩ := h_LL_excess
          refine ⟨e, ?_, he_mult⟩
          -- The local `isLL` and the global `isLLEdge` are definitionally equal.
          intro h_isLL
          exact he_notLL h_isLL
        exact multigraphEval_unlabeled_excess_descends B hB W M h_unlabeled_excess
          (fun n' F _ => h_equiv n' F)

/-- **The multigraph bridge — SECONDARY paper root** (general,
non-twin-free version).

**Dependency hierarchy** (post-2026-05-12 architectural decision):
  - **PRIMARY ROOT**: `connection_matrix_rank_theorem` at L3018
    (Lovász §3 Theorem 2.2, simple-graph form, requires twin-free).
  - **SECONDARY**: this bridge (no twin-free hypothesis; strictly
    stronger statement).

For the twin-free version that downstream consumers actually need,
use `multiLabeledEvalK_tupleEquiv_invariant_twinFree` (already proved
modulo `connection_matrix_rank_theorem`). This general bridge can be
treated as off-axis if all consumers can use the twin-free variant.

Every multigraph evaluation descends through the simple-graph version
of `tupleEquiv`. This is the Lovász §3 content (Theorem 2.2 / Lemma 2.5)
translated to our framework: simple-graph `tupleEquiv` ⟹ all
multigraph evaluations agree.

**Hypothesis form** (`h_simple`): for every level-K simple graph
`F : SimpleGraph (Fin (n' + K))` (with any `n'` unlabeled vertices),
the simple-graph evaluations at `ξ` and `ξ'` agree. This is the
inlined definition of `tupleEquiv B W ξ ξ'`.

**Status** (2026-05-17): designated PRIMARY PAPER-ROOT theorem
(Lovász TR-2004-82 Theorem 2.2 / Lemma 2.5 content). The n = 0 case
is dispatched via `multiLabeledEvalK_tupleEquiv_invariant_n_zero`.
The general n case requires the connection-matrix / idempotent-
decomposition argument from Lovász §3 — substantial spectral/rank
infrastructure (~300-500 LOC) beyond a quick closure. Natural
induction on n via `promote_unfold` needs a "lifted simple-equivalence"
hypothesis at level K + 1, which does NOT follow from the level-K
`h_simple` alone.

**Downstream impact** (closes #62 ⟹ unlocks):
- IH-free Claims 4.3/4.4 (via multigraph evaluations giving
  B-diagonal + W-pointwise data, currently unavailable in
  simple-graph framework alone).
- Task #70 (`orbit_separation_by_simple_graph`).
- Remaining MatrixDetermination chain.

Treat as foundational citation for downstream consumers until a
dedicated paper-root formalization project is undertaken. -/
theorem multiLabeledEvalK_tupleEquiv_invariant {T K n : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (M : MultiLabeledGraph K n)
    {ξ ξ' : Fin K → Fin T}
    (h_simple : ∀ (n' : ℕ) (F : SimpleGraph (Fin (n' + K)))
        [DecidableRel F.Adj],
      ∑ σ : Fin n' → Fin T,
        (let τ : Fin (n' + K) → Fin T := fun v =>
          if h : (v : ℕ) < K then ξ ⟨v, h⟩
          else σ ⟨v - K, by have := v.isLt; omega⟩
        (∏ v : Fin n', W (σ v)) *
        ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2)) =
      ∑ σ : Fin n' → Fin T,
        (let τ : Fin (n' + K) → Fin T := fun v =>
          if h : (v : ℕ) < K then ξ' ⟨v, h⟩
          else σ ⟨v - K, by have := v.isLt; omega⟩
        (∏ v : Fin n', W (σ v)) *
        ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2))) :
    multiLabeledEvalK K n M B W ξ = multiLabeledEvalK K n M B W ξ' := by
  -- Dispatch the n=0 case via the dedicated lemma.
  match n, M with
  | 0, M => exact multiLabeledEvalK_tupleEquiv_invariant_n_zero B hB W M h_simple
  | n + 1, M =>
    -- Sub-case: if all multiplicities are ≤ 1, M corresponds to a simple
    -- graph and the invariance follows directly from h_simple via
    -- multiLabeledEvalK_ofSimple. Otherwise the standard approach
    -- (Lovász §3 rank theorem / connection-matrix idempotent
    -- decomposition) is required.
    by_cases h_mult_le_one : ∀ e, M.mult e ≤ 1
    · -- Build the corresponding simple graph and reduce.
      classical
      let F : SimpleGraph (Fin ((n + 1) + K)) :=
        { Adj := fun a b => a ≠ b ∧ M.mult s(a, b) = 1
          symm := fun a b ⟨hne, hmult⟩ =>
            ⟨hne.symm, by rwa [Sym2.eq_swap]⟩
          loopless := fun a ⟨hne, _⟩ => hne rfl }
      haveI : DecidableRel F.Adj := Classical.decRel _
      -- Show M.mult = (MultiLabeledGraph.ofSimple F).mult pointwise.
      have hmult_eq : ∀ e, M.mult e = (MultiLabeledGraph.ofSimple F).mult e := by
        intro e
        induction e with
        | h a b =>
          show M.mult s(a, b) = if s(a, b) ∈ F.edgeFinset then 1 else 0
          by_cases hM : M.mult s(a, b) = 0
          · rw [hM]
            have : ¬ s(a, b) ∈ F.edgeFinset := by
              rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
              show ¬ F.Adj a b
              intro ⟨_, hmult⟩
              rw [hM] at hmult
              exact absurd hmult (by omega)
            rw [if_neg this]
          · have hM_one : M.mult s(a, b) = 1 := by
              have := h_mult_le_one s(a, b); omega
            rw [hM_one]
            have : s(a, b) ∈ F.edgeFinset := by
              rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
              show F.Adj a b
              refine ⟨?_, hM_one⟩
              intro hab
              rw [hab] at hM_one
              have := M.multNoLoop b
              omega
            rw [if_pos this]
      -- Rewrite multiLabeledEvalK using pointwise equality of mult.
      have hev : ∀ ζ : Fin K → Fin T,
          multiLabeledEvalK K (n + 1) M B W ζ =
          multiLabeledEvalK K (n + 1) (MultiLabeledGraph.ofSimple F) B W ζ := by
        intro ζ
        unfold multiLabeledEvalK
        refine Finset.sum_congr rfl fun σ _ => ?_
        simp_rw [hmult_eq]
      rw [hev ξ, hev ξ', multiLabeledEvalK_ofSimple, multiLabeledEvalK_ofSimple]
      exact h_simple (n + 1) F
    · -- Multiplicity ≥ 2 sub-case: routes through the canonical paper-root
      -- `multigraphEval_in_simpleProfileClosure` (#86, declared above in §3.7).
      -- The closure inductive's `descends` reduces this to the `h_simple`
      -- hypothesis directly.
      exact (multigraphEval_in_simpleProfileClosure B hB W M).descends h_simple

/-! ### §3.8 — Equivalence predicates and Lovász Lemma 2.5

This section introduces the two equivalence relations on label-tuples
that bracket the bridge theorem:

* `tupleEquivSimple` — agreement of all **simple-graph** evaluations
  (Lovász TR-2004-82 §2, p. 6). This is the simple-graph `tupleEquiv`
  inlined here so this module needs no dependency on
  `Graphon/MatrixDetermination.lean`.
* `tupleEquivMulti` — agreement of all **multigraph** evaluations
  (the natural multigraph generalization).

The bridge theorem (§4 below) is exactly `tupleEquivSimple → tupleEquivMulti`.
The reverse direction `tupleEquivMulti → tupleEquivSimple` is trivial
because `multiLabeledEvalK` of `MultiLabeledGraph.ofSimple F` recovers
the simple-graph evaluation (`multiLabeledEvalK_ofSimple`).

**Lovász Lemma 2.5** (informal): if `B` is twin-free, then
`tupleEquivMulti ξ ξ'` if and only if `ξ` and `ξ'` lie in the same
`(B, W)`-automorphism orbit.

* The **forward direction** (orbit ⟹ multi-equivalence) is the
  trivial corollary `multiLabeledEvalK_orbit_invariant` (already proved
  above): aut-invariance of multigraph evaluation gives equality on every
  multigraph automatically.
* The **reverse direction** (multi-equivalence ⟹ orbit) is the deep paper
  content. Lovász's proof goes through the connection-matrix rank /
  idempotent decomposition argument (TR-2004-82 §3): the connection
  matrix `M(B, W) ∈ ℝ^{T^k × T^k}` factors through twin-free quotients,
  and equal multi-eval rows are exactly orbit equivalences. -/

/-- **Simple-graph tuple equivalence** (Lovász §2, p. 6).

Two label maps `ξ, ξ' : Fin K → Fin T` are simple-equivalent iff every
level-`K` **simple** graph (with any number `n'` of unlabeled vertices)
evaluates equally on them. This is the simple-graph `tupleEquiv`
inlined to avoid a `MatrixDetermination` dependency. -/
def tupleEquivSimple {T K : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (ξ ξ' : Fin K → Fin T) : Prop :=
  ∀ (n' : ℕ) (F : SimpleGraph (Fin (n' + K))) [DecidableRel F.Adj],
    ∑ σ : Fin n' → Fin T,
      (let τ : Fin (n' + K) → Fin T := fun v =>
        if h : (v : ℕ) < K then ξ ⟨v, h⟩
        else σ ⟨v - K, by have := v.isLt; omega⟩
      (∏ v : Fin n', W (σ v)) *
      ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2)) =
    ∑ σ : Fin n' → Fin T,
      (let τ : Fin (n' + K) → Fin T := fun v =>
        if h : (v : ℕ) < K then ξ' ⟨v, h⟩
        else σ ⟨v - K, by have := v.isLt; omega⟩
      (∏ v : Fin n', W (σ v)) *
      ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2))

/-- **Multigraph tuple equivalence**.

Two label maps `ξ, ξ' : Fin K → Fin T` are multi-equivalent iff every
level-`K` **multigraph** (with any number `n` of unlabeled vertices)
evaluates equally on them. This is the natural multigraph generalization
of `tupleEquivSimple`. -/
def tupleEquivMulti {T K : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (ξ ξ' : Fin K → Fin T) : Prop :=
  ∀ (n : ℕ) (M : MultiLabeledGraph K n),
    multiLabeledEvalK K n M B W ξ = multiLabeledEvalK K n M B W ξ'

/-- **Loop-multigraph tuple equivalence**.

Two label maps `ξ, ξ' : Fin K → Fin T` are loop-multi-equivalent iff
every level-`K` **multigraph with self-loops** evaluates equally on
them. Strictly stronger than `tupleEquivMulti` (loop case includes
diagonal contributions). The target of task #79: prove
`tupleEquivSimple → tupleEquivLoop` via the Lovász §3 rank theorem. -/
def tupleEquivLoop {T K : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (ξ ξ' : Fin K → Fin T) : Prop :=
  ∀ (n : ℕ) (M : MultiLabeledGraphLoop K n),
    multiLabeledEvalKLoop K n M B W ξ = multiLabeledEvalKLoop K n M B W ξ'

/-- **Loop ⟹ multi** (trivial direction via the `toLoop` injection). -/
theorem tupleEquivMulti_of_tupleEquivLoop {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) {ξ ξ' : Fin K → Fin T}
    (h : tupleEquivLoop B W ξ ξ') :
    tupleEquivMulti B W ξ ξ' := by
  intro n M
  have hL := h n M.toLoop
  rw [multiLabeledEvalKLoop_of_toLoop, multiLabeledEvalKLoop_of_toLoop] at hL
  exact hL

/-- **Lovász Lemma 2.5 (loop), forward direction** (orbit ⟹ loop equiv). -/
theorem tupleEquivLoop_of_orbit {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) {ξ ξ' : Fin K → Fin T}
    (h : ∃ σ : Equiv.Perm (Fin T),
      (∀ i, W (σ i) = W i) ∧ (∀ i j, B (σ i) (σ j) = B i j) ∧
      (∀ i, ξ' i = σ (ξ i))) :
    tupleEquivLoop B W ξ ξ' := by
  intro n M
  exact multiLabeledEvalKLoop_orbit_invariant B W M h

/-! **Diagonal observable** (#79, 2026-05-17 / 2026-05-18).

The theorem `diagonal_observable_of_tupleEquivSimple` is defined LATER
in this file (after `diagonal_observable_K1`), at the position where
all required dependencies (`tupleEquivSimple_restrict_along`,
`rooted_profiles_separate_vertex_orbits`) are in scope.

**Mathematical content**: `η ↦ B(η a, η a)` is orbit-invariant. The
proof reduces to the K=1 case (via `tupleEquivSimple_restrict_along`)
which routes through `rooted_profiles_separate_vertex_orbits` (#77
paper-root). This collapses #79's diagonal observable into the #77
spectral chain, more direct than the rank-theorem route. -/

-- The n=0 loop bridge from `tupleEquivSimple` follows by combining:
--   1. existing `multiLabeledEvalK_tupleEquiv_invariant_n_zero` (off-diagonal),
--   2. `diagonal_observable_of_tupleEquivSimple` (closed modulo #77),
--   3. `multiLabeledEvalKLoop_n_zero_of_diag` (assembly).
-- Wiring deferred (avoids motive-not-type-correct issues with naive rw
-- on Fin.mk constructions during off-diagonal extraction).

/-- **Multi ⟹ simple** (trivial direction).

If `ξ ξ'` agree on every multigraph evaluation, they agree on every
simple-graph evaluation, since `MultiLabeledGraph.ofSimple F` reduces
to the simple-graph form (`multiLabeledEvalK_ofSimple`). -/
theorem tupleEquivSimple_of_tupleEquivMulti {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) {ξ ξ' : Fin K → Fin T}
    (h : tupleEquivMulti B W ξ ξ') :
    tupleEquivSimple B W ξ ξ' := by
  intro n' F _
  have hM := h n' (MultiLabeledGraph.ofSimple F)
  rw [multiLabeledEvalK_ofSimple, multiLabeledEvalK_ofSimple] at hM
  exact hM

/-- **Lovász Lemma 2.5, forward direction** (orbit ⟹ multi-equivalence).

If `ξ` and `ξ'` lie in the same `(B, W)`-automorphism orbit
(`ξ' i = σ (ξ i)` for some weighted automorphism `σ`), then they agree
on every multigraph evaluation. Immediate corollary of
`multiLabeledEvalK_orbit_invariant`. -/
theorem tupleEquivMulti_of_orbit {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) {ξ ξ' : Fin K → Fin T}
    (h : ∃ σ : Equiv.Perm (Fin T),
      (∀ i, W (σ i) = W i) ∧ (∀ i j, B (σ i) (σ j) = B i j) ∧
      (∀ i, ξ' i = σ (ξ i))) :
    tupleEquivMulti B W ξ ξ' := by
  intro n M
  exact multiLabeledEvalK_orbit_invariant B W M h

/-! ### §3.9 — Lovász Lemma 2.4 scaffolding (Claims 4.1–4.4)

This subsection introduces the named helpers and Claims used in Lovász
TR-2004-82's proof of Lemma 2.4. The chain mirrors the (private) chain
already proved in `Graphon/MatrixDetermination.lean` as
`tupleEquiv_restrict` / `tupleEquiv_extend` / `tupleEquiv_bijective_case`
/ `tupleEquiv_surjective_case` / `tupleEquiv_implies_tupleOrbitRel`, but
adapted to the inline `tupleEquivSimple` predicate to avoid the import
cycle with `MatrixDetermination`. The current status:

* **Claim 4.1** (`tupleEquivSimple_restrict`) — proved.
* **Claim 4.2** (`tupleEquivSimple_extend`) — proved MODULO the named
  sub-sorry `product_trace_identity_simple` (the LIST-product trace
  identity; the Lovász §3 deep content). The class-constancy step
  `coeffRestrictSimple_equiv` is now proved as a wrapper around
  `functional_span_zero` + `product_trace_identity_simple`. The
  single-graph trace identity case is fully proved here.
* **Claim 4.3** (`tupleEquivSimple_bijective_case`) — proved (restriction +
  IH at `T-1` + bijection-uniqueness).
* **Claim 4.4** (`tupleEquivSimple_surjective_case`) — proved via the
  helpers `tupleEquivSimple_restrict_along` (restriction along an arbitrary
  label-index injection) and `tupleEquivSimple_id_bijective` (twin-free + W>0
  forces `tupleEquivSimple B W id χ` to make `χ` bijective).

The main theorem `tupleEquivSimple_implies_orbit` is wired below via
strong induction on `K`, with the architectural sorry localized to the
non-surjective branch (mirroring `tupleEquiv_implies_tupleOrbitRel`). -/

/-- **Weighted automorphism predicate**.

A permutation `σ : Equiv.Perm (Fin T)` is a `(B, W)`-automorphism iff it
preserves both the weight vector `W` and the matrix `B` entrywise. -/
def IsWeightedAutomorphism {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (σ : Equiv.Perm (Fin T)) : Prop :=
  (∀ i, W (σ i) = W i) ∧ (∀ i j, B (σ i) (σ j) = B i j)

/-- **Tuple-orbit relation** (Lovász TR-2004-82 §2, p. 5).

Two tuples `ξ ξ' : Fin K → Fin T` are orbit-related iff some
`(B, W)`-automorphism `σ` conjugates one to the other: `ξ' i = σ (ξ i)`.
This is the explicit-σ form of the existential conclusion of
`tupleEquivSimple_implies_orbit`. -/
def tupleOrbitRel {T K : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (ξ ξ' : Fin K → Fin T) : Prop :=
  ∃ σ : Equiv.Perm (Fin T),
    IsWeightedAutomorphism B W σ ∧ ∀ i, ξ' i = σ (ξ i)

/-- Restriction of a `(k+1)`-tuple to its first `k` coordinates via
`Fin.castSucc`. Lovász's `φ'` notation (TR-2004-82 §4). -/
def restrictTuple {T k : ℕ} (ξ : Fin (k + 1) → Fin T) : Fin k → Fin T :=
  fun i => ξ i.castSucc

/-- Range of a tuple `φ : Fin k → Fin T` as a `Finset (Fin T)`.

Used as the well-founded measure in the deficit-induction proof of
`tupleEquivSimple_implies_orbit`'s non-surjective branch. -/
noncomputable def rangeFinset {T k : ℕ} (φ : Fin k → Fin T) : Finset (Fin T) :=
  Finset.image φ Finset.univ

/-- Deficit of `φ : Fin k → Fin T`: `T - |range φ|`. Zero iff `φ` is
surjective. The deficit strictly decreases when extending by a fresh
element (see `deficit_lt_of_not_mem`), giving the well-founded measure
used in Lovász's "extend-and-recurse" plan for Lemma 2.4's
non-surjective branch. -/
noncomputable def deficit {T k : ℕ} (φ : Fin k → Fin T) : ℕ :=
  T - (rangeFinset φ).card

lemma rangeFinset_card_le {T k : ℕ} (φ : Fin k → Fin T) :
    (rangeFinset φ).card ≤ T := by
  classical
  have := Finset.card_le_univ (rangeFinset φ)
  simpa [Fintype.card_fin] using this

lemma rangeFinset_snoc {T k : ℕ} (φ : Fin k → Fin T) (a : Fin T) :
    rangeFinset (Fin.snoc φ a : Fin (k + 1) → Fin T) =
      insert a (rangeFinset φ) := by
  classical
  ext x
  simp only [rangeFinset, Finset.mem_image, Finset.mem_univ, true_and,
             Finset.mem_insert]
  constructor
  · rintro ⟨i, hi⟩
    by_cases h : (i : ℕ) < k
    · refine Or.inr ⟨⟨i, h⟩, ?_⟩
      rw [show i = (⟨i, h⟩ : Fin k).castSucc from Fin.ext rfl,
          Fin.snoc_castSucc] at hi
      exact hi
    · have hi_last : i = Fin.last k := by
        apply Fin.ext
        have := i.isLt
        simp [Fin.val_last]
        omega
      subst hi_last
      rw [Fin.snoc_last] at hi
      exact Or.inl hi.symm
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨Fin.last k, Fin.snoc_last (α := fun _ => Fin T) _ _⟩
    · refine ⟨i.castSucc, ?_⟩
      exact Fin.snoc_castSucc (α := fun _ => Fin T) a φ i

/-- **Deficit strictly decreases on snoc with a fresh element.**

If `a ∉ range φ`, then `deficit (Fin.snoc φ a) < deficit φ`. This is the
key well-founded measure decrease that drives Lovász's
"extend-and-recurse" argument in `tupleEquivSimple_implies_orbit`. -/
lemma deficit_lt_of_not_mem {T k : ℕ} (φ : Fin k → Fin T) (a : Fin T)
    (ha : a ∉ rangeFinset φ) :
    deficit (Fin.snoc φ a : Fin (k + 1) → Fin T) < deficit φ := by
  classical
  simp only [deficit, rangeFinset_snoc]
  rw [Finset.card_insert_of_notMem ha]
  -- a ∉ range and a ∈ univ ⟹ range.card < |univ| = T.
  have hstrict : (rangeFinset φ).card < T := by
    have hsub : rangeFinset φ ⊂ Finset.univ := by
      refine ⟨Finset.subset_univ _, ?_⟩
      intro hsuper
      exact ha (hsuper (Finset.mem_univ a))
    have := Finset.card_lt_card hsub
    simpa [Fintype.card_fin] using this
  omega

/-- Surjectivity reads off `rangeFinset = univ`. -/
lemma surjective_iff_rangeFinset_eq_univ {T k : ℕ} (φ : Fin k → Fin T) :
    Function.Surjective φ ↔ rangeFinset φ = Finset.univ := by
  classical
  refine ⟨fun hsurj => ?_, fun heq y => ?_⟩
  · apply Finset.eq_univ_iff_forall.mpr
    intro y
    obtain ⟨i, hi⟩ := hsurj y
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  · have : y ∈ rangeFinset φ := heq ▸ Finset.mem_univ y
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp this
    exact ⟨i, hi⟩

/-- Surjectivity iff deficit = 0. -/
lemma deficit_eq_zero_iff_surjective {T k : ℕ} (φ : Fin k → Fin T) :
    deficit φ = 0 ↔ Function.Surjective φ := by
  classical
  rw [surjective_iff_rangeFinset_eq_univ, deficit]
  have hle : (rangeFinset φ).card ≤ T := rangeFinset_card_le φ
  constructor
  · intro h
    have hcard : (rangeFinset φ).card = T := by omega
    apply Finset.eq_univ_of_card
    rw [Fintype.card_fin]
    exact hcard
  · intro h
    have : (rangeFinset φ).card = T := by
      rw [h, Finset.card_univ, Fintype.card_fin]
    omega

/-- If `φ` is not surjective, some `a : Fin T` is missing from the
range. -/
lemma exists_not_mem_rangeFinset {T k : ℕ} (φ : Fin k → Fin T)
    (h : ¬ Function.Surjective φ) :
    ∃ a, a ∉ rangeFinset φ := by
  classical
  rw [surjective_iff_rangeFinset_eq_univ] at h
  by_contra hcontra
  push_neg at hcontra
  apply h
  exact Finset.eq_univ_iff_forall.mpr hcontra

/-- **Orbit ⟹ simple-equivalence** (forward direction of Lemma 2.5,
specialized to simple graphs). If `ξ ξ'` are `(B, W)`-orbit related,
they agree on every simple-graph evaluation. Used inside the strong
induction to normalize `ψ` by `σ⁻¹` before extending the base.

This is the simple-graph specialization of `tupleEquivMulti_of_orbit`
(via `tupleEquivSimple_of_tupleEquivMulti`). Direct proof here avoids
the multigraph detour. -/
theorem tupleEquivSimple_of_tupleOrbitRel {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) {ξ ξ' : Fin K → Fin T}
    (h : tupleOrbitRel B W ξ ξ') :
    tupleEquivSimple B W ξ ξ' := by
  -- Pass through tupleEquivMulti, then descend to simple via the
  -- trivial direction.
  obtain ⟨σ, ⟨hW, hB⟩, hconj⟩ := h
  refine tupleEquivSimple_of_tupleEquivMulti B W ?_
  intro n M
  exact multiLabeledEvalK_orbit_invariant B W M ⟨σ, hW, hB, hconj⟩

/-- **Claim 4.1 — Restriction preserves `tupleEquivSimple`**
(Lovász TR-2004-82 §4, p. 6, "first paragraph").

If `ξ ξ' : Fin (k+1) → Fin T` are simple-equivalent, then their
restrictions to the first `k` coordinates (via `Fin.castSucc`) are
also simple-equivalent.

**Proof**: any simple graph `F'` on `Fin (n + k)` lifts to a simple
graph `F` on `Fin (n + (k + 1))` via the embedding `Fin.succAboveEmb p`
with `p = ⟨k, _⟩` (skip the pivot position `k`). The level-`(k+1)`
evaluation of `F` at `ξ` equals the level-`k` evaluation of `F'` at
`restrictTuple ξ`, because the embedding leaves the unlabeled vertices
untouched while reindexing the label slot. The hypothesis applied at
`F` then transfers to `F'`.

This is the simple-graph analog of `tupleEquiv_restrict` (line 4461 of
`MatrixDetermination.lean`). -/
theorem tupleEquivSimple_restrict {T k : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i)
    {ξ ξ' : Fin (k + 1) → Fin T}
    (h : tupleEquivSimple B W ξ ξ') :
    tupleEquivSimple B W (restrictTuple ξ) (restrictTuple ξ') := by
  classical
  intro n F' hdec
  -- Helper: edge-product term is independent of the Sym2 representative
  -- thanks to `hB`. Stated for both target sizes.
  have h_edge_rep : ∀ {m : ℕ} (ν : Fin m → Fin T) (a b : Fin m),
      B (ν (Quot.out (s(a, b) : Sym2 (Fin m))).1)
        (ν (Quot.out (s(a, b) : Sym2 (Fin m))).2) = B (ν a) (ν b) := by
    intro m ν a b
    have h_out_eq : Sym2.mk (Quot.out (s(a, b) : Sym2 (Fin m))) = s(a, b) :=
      Quot.out_eq _
    rcases Sym2.mk_eq_mk_iff.mp h_out_eq with heq | heq
    · rw [heq]
    · rw [heq]; exact hB _ _
  -- Pivot at position k; shift = succAboveEmb p maps Fin (n+k) → Fin (n+(k+1)).
  have hk : k < n + (k + 1) := by omega
  let p : Fin (n + (k + 1)) := ⟨k, hk⟩
  let shift : Fin (n + k) ↪ Fin (n + (k + 1)) := Fin.succAboveEmb p
  let F : SimpleGraph (Fin (n + (k + 1))) := SimpleGraph.map shift F'
  haveI hF_dec : DecidableRel F.Adj := Classical.decRel _
  -- Core translation. The sum on the LHS of `tupleEquivSimple` at
  -- `(restrictTuple ξ, F')` equals the sum on the LHS at `(ξ, F)`.
  suffices trans : ∀ (θ : Fin (k + 1) → Fin T),
      (∑ σ : Fin n → Fin T,
        (let τ : Fin (n + (k + 1)) → Fin T := fun v =>
          if h : (v : ℕ) < k + 1 then θ ⟨v, h⟩
          else σ ⟨v - (k + 1), by have := v.isLt; omega⟩
        (∏ v : Fin n, W (σ v)) *
        ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2))) =
      (∑ σ : Fin n → Fin T,
        (let τ : Fin (n + k) → Fin T := fun v =>
          if h : (v : ℕ) < k then (restrictTuple θ) ⟨v, h⟩
          else σ ⟨v - k, by have := v.isLt; omega⟩
        (∏ v : Fin n, W (σ v)) *
        ∏ e ∈ F'.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2))) by
    -- Apply trans on both sides, then h at F.
    rw [← trans ξ, ← trans ξ']
    exact h n F
  intro θ
  refine Finset.sum_congr rfl fun σ _ => ?_
  -- Both sides have the form (∏ W σ) * (edge prod). The W-prods agree
  -- definitionally; reduce to edge-product equality.
  simp only
  refine congrArg (fun x => (∏ v : Fin n, W (σ v)) * x) ?_
  -- Edge product: Finset.prod_bij with shift.sym2Map.
  symm
  refine Finset.prod_bij (fun e _ => shift.sym2Map e) ?_ ?_ ?_ ?_
  · -- 1. Map lands in F.edgeFinset.
    intro e he
    change shift.sym2Map e ∈ (SimpleGraph.map shift F').edgeFinset
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq] at *
      rw [SimpleGraph.mem_edgeSet] at he ⊢
      exact ⟨a, b, he, rfl, rfl⟩
  · -- 2. Injective.
    intro e1 _ e2 _ hij
    exact shift.sym2Map.injective hij
  · -- 3. Surjective.
    intro e he
    change e ∈ (SimpleGraph.map shift F').edgeFinset at he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ x y =>
      rw [SimpleGraph.mem_edgeSet] at he
      obtain ⟨a, b, hab, hax, hby⟩ := he
      refine ⟨s(a, b), ?_, ?_⟩
      · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact hab
      · simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq]
        rw [hax, hby]
  · -- 4. Term-by-term equality.
    intro e _
    set ν' : Fin (n + k) → Fin T := fun v =>
      if h : (v : ℕ) < k then (restrictTuple θ) ⟨v, h⟩
      else σ ⟨(v : Fin (n + k)).val - k, by have := v.isLt; omega⟩ with hν'_def
    set ν : Fin (n + (k + 1)) → Fin T := fun v =>
      if h : (v : ℕ) < k + 1 then θ ⟨v, h⟩
      else σ ⟨(v : Fin (n + (k + 1))).val - (k + 1),
              by have := v.isLt; omega⟩ with hν_def
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq]
      change B (ν' (Quot.out s(a, b)).1) (ν' (Quot.out s(a, b)).2) =
        B (ν (Quot.out s(shift a, shift b)).1)
          (ν (Quot.out s(shift a, shift b)).2)
      rw [h_edge_rep ν' a b, h_edge_rep ν (shift a) (shift b)]
      -- Reduces to ν ∘ shift = ν' pointwise.
      have hτ : ∀ v : Fin (n + k), ν (shift v) = ν' v := by
        intro v
        by_cases hv : (v : ℕ) < k
        · -- Below the pivot: shift v = v.castSucc, .val preserved.
          have h_shift_val : (shift v : Fin (n + (k + 1))).val = v.val := by
            show (p.succAboveEmb v : Fin (n + (k + 1))).val = v.val
            simp only [Fin.coe_succAboveEmb]
            rw [Fin.succAbove_of_castSucc_lt]
            · rfl
            · show v.castSucc < p
              simp only [Fin.lt_def, Fin.val_castSucc]
              exact hv
          have h_lt : ((shift v : Fin (n + (k + 1))) : ℕ) < k + 1 := by
            rw [h_shift_val]; omega
          simp only [hν_def, hν'_def, dif_pos h_lt, dif_pos hv, restrictTuple]
          congr 1
          apply Fin.ext
          simp only [Fin.val_castSucc]
          exact h_shift_val
        · -- Above the pivot: shift v = v.succ, .val = v.val + 1.
          have h_shift_val : (shift v : Fin (n + (k + 1))).val = v.val + 1 := by
            show (p.succAboveEmb v : Fin (n + (k + 1))).val = v.val + 1
            simp only [Fin.coe_succAboveEmb]
            rw [Fin.succAbove_of_le_castSucc]
            · rfl
            · show p ≤ v.castSucc
              simp only [Fin.le_def, Fin.val_castSucc]
              show k ≤ v.val
              omega
          have h_nlt : ¬ ((shift v : Fin (n + (k + 1))) : ℕ) < k + 1 := by
            rw [h_shift_val]; omega
          have h_nlt' : ¬ (v : ℕ) < k := hv
          simp only [hν_def, hν'_def, dif_neg h_nlt, dif_neg h_nlt']
          congr 1
          apply Fin.ext
          show (shift v : Fin (n + (k + 1))).val - (k + 1) = v.val - k
          rw [h_shift_val]; omega
      rw [hτ a, hτ b]

/-! ### §3.9.1 — Restriction-weight coefficient (Claim 4.2 architecture)

The proof of Claim 4.2 (`tupleEquivSimple_extend`) below routes through
a `coeffRestrictSimple` "restriction weight" coefficient:

  `coeffRestrictSimple B W μ ξ := ∑ t : Fin T, [tupleEquivSimple B W μ (snoc ξ t)] · W t`

i.e., the total `W`-mass of extensions `t` of `ξ` that are
simple-equivalent (at level `k + 1`) to the given `(k + 1)`-tuple `μ`.

Three lemmas drive the assembly:

* `coeffRestrictSimple_pos_at_restrict` — the coefficient is positive
  at `ξ = restrictTuple μ` (witnessed by `t = μ (Fin.last k)`, which
  makes the indicator `tupleEquivSimple μ μ` true by reflexivity).
* `coeffRestrictSimple_equiv` — class constancy: simple-equivalence
  of `ξ` and `ξ'` transfers `coeffRestrictSimple B W μ ξ =
  coeffRestrictSimple B W μ ξ'`. PROVED via `functional_span_zero`
  + `product_trace_identity_simple` (the latter is a focused
  sub-sorry capturing the Lovász §3 deep content).
* `exists_extension_of_coeffRestrictSimple_pos` — from positivity, some
  `t` makes the indicator true, yielding the extension.

The class-constancy step is now proved structurally. The single
remaining architectural hurdle is the LIST-product trace identity
`product_trace_identity_simple` (Lovász §3 / DecLabeledGraph). -/

/-- **Restriction-weight coefficient** for a `(k+1)`-tuple `μ`
at a level-`k` base `ξ`. Sums `W t` over `t : Fin T` such that the
extended tuple `Fin.snoc ξ t` is simple-equivalent to `μ`. -/
noncomputable def coeffRestrictSimple {T k : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (μ : Fin (k + 1) → Fin T) (ξ : Fin k → Fin T) : ℝ :=
  ∑ t : Fin T,
    haveI : Decidable (tupleEquivSimple B W μ (Fin.snoc ξ t)) := Classical.dec _
    if tupleEquivSimple B W μ (Fin.snoc ξ t) then W t else 0

/-- `μ` is `Fin.snoc`-canonical at its own restriction: any tuple
equals `Fin.snoc` of its restriction with its last coordinate. -/
private theorem snoc_restrict_eq {T k : ℕ} (μ : Fin (k + 1) → Fin T) :
    Fin.snoc (restrictTuple μ) (μ (Fin.last k)) = μ := by
  funext i
  by_cases hi : (i : ℕ) < k
  · rw [show i = (⟨i, hi⟩ : Fin k).castSucc from Fin.ext rfl,
        Fin.snoc_castSucc]
    rfl
  · rw [show i = Fin.last k from Fin.ext (show i.val = k by omega),
        Fin.snoc_last]

/-- Reflexivity of `tupleEquivSimple`. -/
private theorem tupleEquivSimple_refl {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (ξ : Fin K → Fin T) :
    tupleEquivSimple B W ξ ξ :=
  fun _ _ _ => rfl

/-- **Positivity of `coeffRestrictSimple` at its own restriction**.

Under `0 < W`, the coefficient `coeffRestrictSimple B W μ
(restrictTuple μ)` is strictly positive: the term `t = μ (Fin.last k)`
contributes `W t > 0` (the indicator `tupleEquivSimple μ μ` holds by
reflexivity), and all other terms are nonneg. -/
theorem coeffRestrictSimple_pos_at_restrict {T k : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (μ : Fin (k + 1) → Fin T) :
    0 < coeffRestrictSimple B W μ (restrictTuple μ) := by
  classical
  unfold coeffRestrictSimple
  -- Witness term: t = μ (Fin.last k).
  set t₀ : Fin T := μ (Fin.last k) with ht₀
  -- Indicator at t₀ is true: snoc (restrictTuple μ) t₀ = μ, then refl.
  have h_snoc_eq : Fin.snoc (restrictTuple μ) t₀ = μ := snoc_restrict_eq μ
  have h_indicator : tupleEquivSimple B W μ (Fin.snoc (restrictTuple μ) t₀) := by
    rw [h_snoc_eq]; exact tupleEquivSimple_refl B W μ
  -- Apply Finset.sum_pos' (nonneg + exists-positive).
  refine Finset.sum_pos' ?_ ⟨t₀, Finset.mem_univ _, ?_⟩
  · intro i _
    by_cases hi : tupleEquivSimple B W μ (Fin.snoc (restrictTuple μ) i)
    · rw [if_pos hi]; exact (hW i).le
    · rw [if_neg hi]
  · rw [if_pos h_indicator]; exact hW t₀

/-- **Existence of an extension witness from positive coefficient**.

If the restriction-weight coefficient `coeffRestrictSimple B W μ ψ` is
strictly positive (under `0 ≤ W`), then there is some `a : Fin T` such
that `Fin.snoc ψ a` is simple-equivalent to `μ` at level `k + 1`. -/
theorem exists_extension_of_coeffRestrictSimple_pos {T k : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (μ : Fin (k + 1) → Fin T) (ψ : Fin k → Fin T)
    (hpos : 0 < coeffRestrictSimple B W μ ψ) :
    ∃ a : Fin T, tupleEquivSimple B W μ (Fin.snoc ψ a) := by
  classical
  by_contra h_no
  push_neg at h_no
  -- Every term vanishes, so the sum is 0, contradicting positivity.
  have h_all_zero : ∀ t : Fin T,
      (if tupleEquivSimple B W μ (Fin.snoc ψ t) then W t else 0) = 0 := by
    intro t
    rw [if_neg (h_no t)]
  have h_sum_zero : coeffRestrictSimple B W μ ψ = 0 := by
    unfold coeffRestrictSimple
    exact Finset.sum_eq_zero (fun t _ => h_all_zero t)
  rw [h_sum_zero] at hpos
  exact lt_irrefl 0 hpos

/-! ### §3.9.2 — Functional-span machinery (port of MD `functional_span_zero`)

To prove `coeffRestrictSimple_equiv` we use the standard finite
Stone-Weierstrass-style lemma: given a separating, unital,
multiplicatively closed family `f : I → Q → ℝ` and a `d : Q → ℝ` that
is orthogonal to every `f i` (under the counting measure), `d = 0`.

This is a verbatim port of `MatrixDetermination.functional_span_zero`
(L5004) — self-contained, ~100 lines of finite induction on the support
of `d`. Used below to conclude that the class-weight difference between
`ξ` and `ξ'` over the level-`(k+1)` `tupleEquivSimple`-quotient
vanishes, given orthogonality from a product trace identity. -/

/-- **Functional span zero**: if a function `d : Q → ℝ` on a finite
type is orthogonal (w.r.t. counting measure) to every member of a
separating, unital, multiplicatively closed family `f : I → Q → ℝ`,
then `d` vanishes pointwise.

Port of `MatrixDetermination.functional_span_zero`. -/
private theorem functional_span_zero {Q : Type*} [Fintype Q] [DecidableEq Q]
    {I : Type*} (f : I → Q → ℝ) (d : Q → ℝ)
    (hconst : ∃ i₀ : I, ∀ q, f i₀ q = 1)
    (hmul : ∀ i j : I, ∃ k : I, ∀ q, f k q = f i q * f j q)
    (hsep : ∀ q₁ q₂ : Q, q₁ ≠ q₂ → ∃ i : I, f i q₁ ≠ f i q₂)
    (hortho : ∀ i : I, ∑ q, d q * f i q = 0) :
    ∀ q, d q = 0 := by
  -- Strong induction on |support(d)|.
  suffices key : ∀ (m : ℕ) (d : Q → ℝ),
      (Finset.univ.filter (fun q => d q ≠ 0)).card ≤ m →
      (∀ i : I, ∑ q, d q * f i q = 0) →
      ∀ q, d q = 0 by
    exact key (Finset.univ.filter (fun q => d q ≠ 0)).card d le_rfl hortho
  intro m
  induction m with
  | zero =>
    intro d hm _ q
    by_contra hq
    have hmem : q ∈ Finset.univ.filter (fun q => d q ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
    have := Finset.card_pos.mpr ⟨q, hmem⟩
    omega
  | succ m IH =>
    intro d hm hd_ortho
    by_cases h_all_zero : ∀ q, d q = 0
    · exact h_all_zero
    push_neg at h_all_zero
    obtain ⟨q₀, hq₀⟩ := h_all_zero
    by_cases h_unique : ∀ q, q ≠ q₀ → d q = 0
    · obtain ⟨i₀, hi₀⟩ := hconst
      have h := hd_ortho i₀
      simp only [hi₀, mul_one] at h
      rw [show ∑ q, d q = d q₀ + ∑ q ∈ Finset.univ.erase q₀, d q from by
        rw [Finset.add_sum_erase _ _ (Finset.mem_univ _)]] at h
      have hzero : ∑ q ∈ Finset.univ.erase q₀, d q = 0 :=
        Finset.sum_eq_zero fun q hq => h_unique q (Finset.ne_of_mem_erase hq)
      rw [hzero, add_zero] at h
      exact absurd h hq₀
    · push_neg at h_unique
      obtain ⟨q₁, hq₁_ne, hq₁⟩ := h_unique
      obtain ⟨i_sep, hi_sep⟩ := hsep q₀ q₁ hq₁_ne.symm
      let d' : Q → ℝ := fun q => d q * (f i_sep q - f i_sep q₀)
      have hd'_ortho : ∀ j : I, ∑ q, d' q * f j q = 0 := by
        intro j
        obtain ⟨k, hk⟩ := hmul i_sep j
        show ∑ q, d q * (f i_sep q - f i_sep q₀) * f j q = 0
        have h1 : ∑ q, d q * (f i_sep q - f i_sep q₀) * f j q =
            ∑ q, d q * f i_sep q * f j q -
              ∑ q, d q * (f i_sep q₀ * f j q) := by
          rw [(Finset.sum_sub_distrib
                (f := fun q => d q * f i_sep q * f j q)
                (g := fun q => d q * (f i_sep q₀ * f j q))).symm]
          congr 1; ext q; ring
        rw [h1]
        rw [show ∑ q, d q * f i_sep q * f j q = ∑ q, d q * f k q by
          congr 1; ext q; rw [hk]; ring]
        rw [hd_ortho k]
        rw [show ∑ q, d q * (f i_sep q₀ * f j q) =
          f i_sep q₀ * ∑ q, d q * f j q by
          rw [Finset.mul_sum]; congr 1; ext q; ring]
        rw [hd_ortho j, mul_zero, sub_self]
      have hd'q₀ : d' q₀ = 0 := by
        show d q₀ * (f i_sep q₀ - f i_sep q₀) = 0; simp
      have hd'_card : (Finset.univ.filter (fun q => d' q ≠ 0)).card ≤ m := by
        have hsub : Finset.univ.filter (fun q => d' q ≠ 0) ⊆
            (Finset.univ.filter (fun q => d q ≠ 0)).erase q₀ := by
          intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
          rw [Finset.mem_erase]
          refine ⟨fun heq => ?_, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, fun habs => ?_⟩⟩
          · subst heq; exact hq hd'q₀
          · exact hq (show d' q = 0 by
              show d q * (f i_sep q - f i_sep q₀) = 0
              rw [habs, zero_mul])
        calc (Finset.univ.filter (fun q => d' q ≠ 0)).card
            ≤ ((Finset.univ.filter (fun q => d q ≠ 0)).erase q₀).card :=
              Finset.card_le_card hsub
          _ ≤ (Finset.univ.filter (fun q => d q ≠ 0)).card - 1 :=
              Nat.le_sub_one_of_lt (Finset.card_erase_lt_of_mem
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq₀⟩))
          _ ≤ m := by omega
      have hkey := IH d' hd'_card hd'_ortho q₁
      change d q₁ * (f i_sep q₁ - f i_sep q₀) = 0 at hkey
      rcases mul_eq_zero.mp hkey with hcase | hcase
      · exact absurd hcase hq₁
      · exact absurd (sub_eq_zero.mp hcase) hi_sep.symm

/-! ### §3.9.3 — Simple-graph evaluation, single-graph trace identity, and
    the product trace identity (named focused sorry).

We package the simple-graph evaluation body that appears inside
`tupleEquivSimple` as a noncomputable definition `simpleEvalAt`, prove
the single-graph trace identity directly from
`multiLabeledEvalK_sum_last_label`, and state the LIST-product trace
identity as a focused sorry. The product identity is the genuine
Lovász §3 content (it requires the connection-matrix / DecLabeledGraph
machinery in `MatrixDetermination.lean`, ~3000 lines), and is the SOLE
remaining gap for `coeffRestrictSimple_equiv` below. -/

/-- Simple-graph evaluation extracted as a named definition (matching the
body of `tupleEquivSimple` and the RHS of `multiLabeledEvalK_ofSimple`). -/
noncomputable def simpleEvalAt {T K n : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (F : SimpleGraph (Fin (n + K))) [DecidableRel F.Adj]
    (ξ : Fin K → Fin T) : ℝ :=
  ∑ σ : Fin n → Fin T,
    (let τ : Fin (n + K) → Fin T := fun v =>
      if h : (v : ℕ) < K then ξ ⟨v, h⟩
      else σ ⟨v - K, by have := v.isLt; omega⟩
    (∏ v : Fin n, W (σ v)) *
    ∏ e ∈ F.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2))

/-- `simpleEvalAt` is `multiLabeledEvalK` on `MultiLabeledGraph.ofSimple`. -/
private theorem simpleEvalAt_eq_multi {T K n : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (F : SimpleGraph (Fin (n + K))) [DecidableRel F.Adj]
    (ξ : Fin K → Fin T) :
    simpleEvalAt B W F ξ =
      multiLabeledEvalK K n (MultiLabeledGraph.ofSimple F) B W ξ := by
  rw [multiLabeledEvalK_ofSimple]; rfl

/-- **Product trace identity (named focused sorry)** —
the LIST-product analog of `simpleEvalAt_trace_eq` below.

For any list `L` of `(k+1)`-labeled simple graphs and any tuples `ξ ξ'`
simple-equivalent at level `k`, the W-weighted last-label sum of the
product `∏ simpleEvalAt F_i (snoc ξ t)` is equal for `ξ` and `ξ'`.

**This is the Lovász §3 deep content.** In
`MatrixDetermination.lean` it is `product_trace_identity` (L10390),
proved via a long chain ending in
`DecLabeledGraph.trace_eval_tupleEquiv_invariant` (~3000 lines of
decorated-labeled-graph machinery). Porting that here is out of
scope; we name this as a focused architectural sorry, which is the
SOLE missing piece for `coeffRestrictSimple_equiv`.

Note: the single-graph case (`L = [⟨n, F⟩]`) is provable directly via
`multiLabeledEvalK_sum_last_label` (see `simpleEvalAt_trace_eq` below).
The empty list `L = []` is trivial. The non-trivial content is the
binary case (`L = L₁ ++ L₂`), which is genuinely a multigraph trace
statement that does not reduce to `tupleEquivSimple` at level `k`
alone — it needs either the bridge theorem (currently sorry in
`multiLabeledEvalK_tupleEquiv_invariant`) or the DecLabeledGraph
machinery. -/
private theorem product_trace_identity_simple {T k : ℕ}
    (_B : Fin T → Fin T → ℝ) (_hB : ∀ i j, _B i j = _B j i) (_W : Fin T → ℝ)
    {ξ ξ' : Fin k → Fin T} (_h : tupleEquivSimple _B _W ξ ξ')
    (L : List (Σ (n : ℕ), SimpleGraph (Fin (n + (k + 1))))) :
    ∑ t : Fin T, _W t *
      (L.map (fun p => @simpleEvalAt T (k + 1) p.1 _B _W p.2
        (Classical.decRel _) (Fin.snoc ξ t))).prod =
    ∑ t : Fin T, _W t *
      (L.map (fun p => @simpleEvalAt T (k + 1) p.1 _B _W p.2
        (Classical.decRel _) (Fin.snoc ξ' t))).prod := by
  classical
  -- **Step 1**: Build a combined multigraph `M_L : MultiLabeledGraph (k+1) N_L`
  -- whose evaluation matches the product of `simpleEvalAt`s over the list.
  -- We construct it by recursion on `L`: empty list ↦ empty (n = 0), cons ↦
  -- glue head's `ofSimple` with tail's combined multigraph.
  suffices hcombined : ∃ (N : ℕ) (M : MultiLabeledGraph (k + 1) N),
      ∀ φ : Fin (k + 1) → Fin T,
        (L.map (fun p => @simpleEvalAt T (k + 1) p.1 _B _W p.2
          (Classical.decRel _) φ)).prod = multiLabeledEvalK (k + 1) N M _B _W φ by
    obtain ⟨N, M, hM⟩ := hcombined
    -- Rewrite both sides using hM at φ = Fin.snoc ξ t (resp. Fin.snoc ξ' t).
    have hLHS : ∀ t : Fin T,
        _W t * (L.map (fun p => @simpleEvalAt T (k + 1) p.1 _B _W p.2
            (Classical.decRel _) (Fin.snoc ξ t))).prod =
        _W t * multiLabeledEvalK (k + 1) N M _B _W (Fin.snoc ξ t) :=
      fun t => by rw [hM (Fin.snoc ξ t)]
    have hRHS : ∀ t : Fin T,
        _W t * (L.map (fun p => @simpleEvalAt T (k + 1) p.1 _B _W p.2
            (Classical.decRel _) (Fin.snoc ξ' t))).prod =
        _W t * multiLabeledEvalK (k + 1) N M _B _W (Fin.snoc ξ' t) :=
      fun t => by rw [hM (Fin.snoc ξ' t)]
    rw [Finset.sum_congr rfl (fun t _ => hLHS t),
        Finset.sum_congr rfl (fun t _ => hRHS t)]
    -- Apply `multiLabeledEvalK_sum_last_label` to fold the t-sum into a trace.
    rw [multiLabeledEvalK_sum_last_label M _B _hB _W ξ,
        multiLabeledEvalK_sum_last_label M _B _hB _W ξ']
    -- Now apply the bridge `multiLabeledEvalK_tupleEquiv_invariant` to `M.trace`.
    exact multiLabeledEvalK_tupleEquiv_invariant _B _hB _W M.trace _h
  -- **Step 2**: Construct the combined multigraph by induction on `L`.
  clear _h
  induction L with
  | nil =>
    refine ⟨0, MultiLabeledGraph.empty (k + 1) 0, fun φ => ?_⟩
    -- LHS: empty list product = 1; RHS: empty multigraph evaluation = 1.
    simp only [List.map_nil, List.prod_nil]
    rw [multiLabeledEvalK_empty]
    simp
  | cons head tail ih =>
    obtain ⟨N_tail, M_tail, h_tail⟩ := ih
    -- Glue head's `ofSimple` with tail's combined multigraph.
    refine ⟨head.1 + N_tail,
      (MultiLabeledGraph.ofSimple head.2).glue M_tail, fun φ => ?_⟩
    -- LHS: head's simpleEvalAt times tail's product.
    -- RHS: glue eval = head's multi eval times tail's multi eval.
    simp only [List.map_cons, List.prod_cons]
    rw [h_tail φ]
    rw [multiLabeledEvalK_glue _B _hB _W (MultiLabeledGraph.ofSimple head.2) M_tail φ]
    -- Convert head's simpleEvalAt to multi eval via `simpleEvalAt_eq_multi`.
    rw [simpleEvalAt_eq_multi]

/-- **Class-constancy of the restriction-weight coefficient**
(Lovász TR-2004-82 §4 core; the IH-free heart of Claim 4.2).

If `ξ` and `ξ'` are simple-equivalent at level `k`, the restriction
weight `coeffRestrictSimple B W μ ξ` is invariant under replacing `ξ`
by `ξ'`.

**Proof outline** (mirrors `MatrixDetermination.coeffRestrict_equiv`):

1. **Reduction to class-constant `g`**: it suffices to prove
   `∑_t W(t) g (snoc ξ t) = ∑_t W(t) g (snoc ξ' t)` for every
   class-constant `g : (Fin (k+1) → Fin T) → ℝ`. Take `g` to be the
   indicator of `[μ]`; this recovers `coeffRestrictSimple_equiv`.
2. **Apply `functional_span_zero`**: on the level-`(k+1)` quotient by
   `tupleEquivSimple`, use the class-weight difference as `d` and lists
   of `simpleEvalAt` evaluations as the test family. Constants come
   from the empty list; multiplicative closure from list concatenation;
   separation from the definition of `tupleEquivSimple`; orthogonality
   from `product_trace_identity_simple`.

**Modulo**: the named architectural sorry `product_trace_identity_simple`
(the genuine Lovász §3 content; ~3000 lines via DecLabeledGraph in
`MatrixDetermination.lean`). Everything else is closed. -/
theorem coeffRestrictSimple_equiv {T k : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i)
    (μ : Fin (k + 1) → Fin T) {ξ ξ' : Fin k → Fin T}
    (h : tupleEquivSimple B W ξ ξ') :
    coeffRestrictSimple B W μ ξ = coeffRestrictSimple B W μ ξ' := by
  classical
  -- **Reduction**: it suffices to show class-constant `g` give equal
  -- `W`-weighted last-label sums over `ξ` and `ξ'` extensions.
  suffices class_eq : ∀ (g : (Fin (k + 1) → Fin T) → ℝ),
      (∀ η η', tupleEquivSimple B W η η' → g η = g η') →
      ∑ t, W t * g (Fin.snoc ξ t) = ∑ t, W t * g (Fin.snoc ξ' t) by
    -- Apply `class_eq` with `g` = indicator of the `tupleEquivSimple`-class of `μ`.
    have hind := class_eq
      (fun η => @ite ℝ (tupleEquivSimple B W μ η) (Classical.dec _) 1 0)
      (fun η η' heq => by
        simp only
        congr 1
        refine propext ⟨fun hh => ?_, fun hh => ?_⟩
        · intro n F _
          exact (hh n F).trans (heq n F)
        · intro n F _
          exact (hh n F).trans (heq n F).symm)
    simp only [mul_ite, mul_one, mul_zero] at hind
    -- LHS and RHS of `hind` are exactly `coeffRestrictSimple B W μ ξ` and `ξ'`.
    unfold coeffRestrictSimple
    convert hind using 2
  -- **Step 2: prove `class_eq` via `functional_span_zero`.**
  intro g hg_class
  -- Setoid on level-`(k+1)` tuples via `tupleEquivSimple`.
  let S : Setoid (Fin (k + 1) → Fin T) :=
    ⟨tupleEquivSimple B W,
      tupleEquivSimple_refl B W,
      fun hh n F _ => (hh n F).symm,
      fun h₁ h₂ n F _ => (h₁ n F).trans (h₂ n F)⟩
  haveI : Fintype (Quotient S) := Quotient.fintype S
  -- Lift `g` to the quotient.
  let g_lift : Quotient S → ℝ := Quotient.lift g hg_class
  -- Each `(n, F)` descends to `Quotient S → ℝ` by definition.
  let eval_lift : (Σ (n : ℕ), SimpleGraph (Fin (n + (k + 1)))) → Quotient S → ℝ :=
    fun p => Quotient.lift
      (fun η => @simpleEvalAt T (k + 1) p.1 B W p.2 (Classical.decRel _) η)
      (fun _ _ hab => hab _ _)
  -- `f_fun L q` = product of evaluations on the class `q` indexed by `L`.
  let f_fun : List (Σ (n : ℕ), SimpleGraph (Fin (n + (k + 1)))) →
      Quotient S → ℝ :=
    fun L q => (L.map (fun p => eval_lift p q)).prod
  -- Class-weighted distributions of `snoc ξ ·` and `snoc ξ' ·`.
  let α_w : Quotient S → ℝ := fun q =>
    ∑ t : Fin T, if Quotient.mk S (Fin.snoc ξ t) = q then W t else 0
  let β_w : Quotient S → ℝ := fun q =>
    ∑ t : Fin T, if Quotient.mk S (Fin.snoc ξ' t) = q then W t else 0
  let d_fun : Quotient S → ℝ := fun q => α_w q - β_w q
  -- Helper: weighted sum over `t` of `φ ⟦η t⟧` equals class-sum via partition.
  have class_decomp : ∀ (η : Fin T → (Fin (k + 1) → Fin T)) (φ : Quotient S → ℝ),
      ∑ q, (∑ t, if Quotient.mk S (η t) = q then W t else 0) * φ q =
      ∑ t, W t * φ (Quotient.mk S (η t)) := by
    intro η φ
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ (Quotient.mk S (η t)) (fun q => W t * φ q)]
    simp
  -- Apply `functional_span_zero` to conclude `d_fun = 0`.
  have hd_zero : ∀ q, d_fun q = 0 := by
    apply functional_span_zero f_fun d_fun
    · -- hconst: empty list gives constant 1.
      exact ⟨[], fun _ => by simp only [f_fun, List.map_nil, List.prod_nil]⟩
    · -- hmul: list concatenation gives pointwise product.
      intro L₁ L₂
      refine ⟨L₁ ++ L₂, fun q => ?_⟩
      simp only [f_fun, List.map_append, List.prod_append]
    · -- hsep: distinct classes distinguished by some `(n, F)`.
      intro q₁ q₂ hne
      obtain ⟨η₁, rfl⟩ := Quotient.exists_rep q₁
      obtain ⟨η₂, rfl⟩ := Quotient.exists_rep q₂
      have hne' : ¬ tupleEquivSimple B W η₁ η₂ := fun hh => hne (Quotient.sound hh)
      simp only [tupleEquivSimple, not_forall] at hne'
      obtain ⟨n, F, _, hne_F⟩ := hne'
      refine ⟨[⟨n, F⟩], ?_⟩
      simp only [f_fun, eval_lift, List.map_cons, List.map_nil, List.prod_cons,
                 List.prod_nil, mul_one, Quotient.lift_mk]
      intro heq
      apply hne_F
      -- `heq` is `simpleEvalAt B W F η₁ = simpleEvalAt B W F η₂`,
      -- which by `simpleEvalAt` definition is exactly the body of
      -- `tupleEquivSimple` at this `(n, F)`.
      unfold simpleEvalAt at heq
      convert heq
    · -- hortho: via the product trace identity.
      intro L
      show ∑ q, (α_w q - β_w q) * f_fun L q = 0
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, class_decomp _ (f_fun L),
          class_decomp _ (f_fun L)]
      have hbridge : ∀ (ξ'' : Fin k → Fin T) (t : Fin T),
          f_fun L (Quotient.mk S (Fin.snoc ξ'' t)) =
          (L.map (fun p => @simpleEvalAt T (k + 1) p.1 B W p.2
            (Classical.decRel _) (Fin.snoc ξ'' t))).prod := by
        intros; simp only [f_fun, eval_lift, Quotient.lift_mk]
      simp_rw [hbridge ξ, hbridge ξ']
      linarith [product_trace_identity_simple B hB W h L]
  -- Conclude `∑ t, W t * g (snoc ξ t) = ∑ t, W t * g (snoc ξ' t)`.
  have hsum_zero : ∑ q, d_fun q * g_lift q = 0 :=
    Finset.sum_eq_zero fun q _ => by rw [hd_zero q, zero_mul]
  have hgoal_decomp :
      ∑ t, W t * g (Fin.snoc ξ t) - ∑ t, W t * g (Fin.snoc ξ' t) =
      ∑ q, d_fun q * g_lift q := by
    show _ = ∑ q, (α_w q - β_w q) * g_lift q
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, class_decomp _ g_lift, class_decomp _ g_lift]
    simp only [g_lift, Quotient.lift_mk]
  linarith

/-- **Claim 4.2 — Extension lemma**
(Lovász TR-2004-82 §4, p. 6, "second paragraph").

If `ξ ξ' : Fin k → Fin T` are simple-equivalent at level `k`, then for
every level-`(k+1)` extension `μ` of `ξ` (`restrictTuple μ = ξ`) there
exists a level-`(k+1)` extension `ν` of `ξ'` (`restrictTuple ν = ξ'`)
such that `μ` and `ν` are simple-equivalent at level `k+1`.

**Proof** (this file): build the restriction-weight coefficient
`coeffRestrictSimple B W μ` (sum of `W t` over `t` with
`tupleEquivSimple μ (snoc ξ t)`).

* At `ξ = restrictTuple μ` the coefficient is positive
  (`coeffRestrictSimple_pos_at_restrict`, witnessed by
  `t = μ (Fin.last k)`).
* Class constancy (`coeffRestrictSimple_equiv`) transfers positivity
  from `restrictTuple μ` (= `ξ`) to `ξ'`.
* Positivity yields some `a` with `tupleEquivSimple μ (snoc ξ' a)`
  (`exists_extension_of_coeffRestrictSimple_pos`); take `ν = snoc ξ' a`.

**Modulo**: the named sorry `coeffRestrictSimple_equiv` (the class
constancy step — the IH-free Lovász §4 core). -/
theorem tupleEquivSimple_extend {T k : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (hB : ∀ i j, B i j = B j i)
    {ξ ξ' : Fin k → Fin T}
    (h : tupleEquivSimple B W ξ ξ')
    (μ : Fin (k + 1) → Fin T) (hμ : restrictTuple μ = ξ) :
    ∃ ν : Fin (k + 1) → Fin T,
      restrictTuple ν = ξ' ∧ tupleEquivSimple B W μ ν := by
  classical
  -- Step 1: positivity at restrictTuple μ.
  have h_pos_restrict : 0 < coeffRestrictSimple B W μ (restrictTuple μ) :=
    coeffRestrictSimple_pos_at_restrict B W hW μ
  -- Step 2: rewrite restrictTuple μ as ξ.
  rw [hμ] at h_pos_restrict
  -- Step 3: class constancy transfers positivity ξ → ξ'.
  have h_eq := coeffRestrictSimple_equiv B W hB μ h
  have h_pos_ξ' : 0 < coeffRestrictSimple B W μ ξ' := h_eq ▸ h_pos_restrict
  -- Step 4: extract an extension witness a.
  obtain ⟨a, ha⟩ := exists_extension_of_coeffRestrictSimple_pos B W μ ξ' h_pos_ξ'
  -- Step 5: ν = Fin.snoc ξ' a satisfies both conjuncts.
  refine ⟨Fin.snoc ξ' a, ?_, ha⟩
  -- restrictTuple (Fin.snoc ξ' a) = ξ' by Fin.snoc_castSucc.
  funext i
  show (Fin.snoc ξ' a : Fin (k + 1) → Fin T) i.castSucc = ξ' i
  exact Fin.snoc_castSucc (α := fun _ => Fin T) a ξ' i

/-- **Claim 4.3 — Bijective base case**
(Lovász TR-2004-82 §4, p. 6, "third paragraph").

If `ψ : Fin T → Fin T` is bijective and `tupleEquivSimple B W id ψ`
holds, then `ψ` IS a `(B, W)`-automorphism (orbit relation holds with
σ = ψ).

**Proof strategy**: build single-edge simple graphs `F_{i,j}` (the
graph on `Fin T` with a single edge `{i, j}`); their level-`T`
evaluations at `id` and `ψ` extract `B i j = B (ψ i) (ψ j)`, giving
the B-preservation half. Single-vertex graphs (no edges) similarly
extract `W` preservation via the `∏ W(σ_inner)` factor. The pair is
exactly `IsWeightedAutomorphism B W ψ`. (`Equiv.ofBijective` is used
to convert the function-level bijection to `Equiv.Perm`.)

**Status**: proved via IH-at-`T-1` route (matches `tupleEquiv_bijective_case`
in `MatrixDetermination.lean:5339`). The proof restricts to the first
`T-1` coordinates (Claim 4.1), applies IH to extract an automorphism `σ`
agreeing with `ψ` on those coordinates, then uses bijectivity to force
agreement at the last coordinate. -/
theorem tupleEquivSimple_bijective_case {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i)
    (IH_orbit : ∀ {ξ' ψ' : Fin (T - 1) → Fin T},
      tupleEquivSimple B W ξ' ψ' → tupleOrbitRel B W ξ' ψ')
    (ψ : Fin T → Fin T) (hψ_bij : Function.Bijective ψ)
    (h : tupleEquivSimple B W (id : Fin T → Fin T) ψ) :
    tupleOrbitRel B W (id : Fin T → Fin T) ψ := by
  rcases T with _ | S
  · -- T = 0: Fin 0 is empty, trivial. σ = identity works.
    exact ⟨Equiv.refl _, ⟨nofun, nofun⟩, nofun⟩
  · -- T = S + 1. Restrict, apply IH, conclude by bijectivity.
    -- Step 1: Claim 4.1 (`tupleEquivSimple_restrict`) gives equivalence at level S.
    have h_restrict := tupleEquivSimple_restrict B W hB h
    -- Step 2: IH at level S = T - 1 gives an automorphism σ.
    obtain ⟨σ, hσ_aut, hσ_conj⟩ := IH_orbit h_restrict
    -- Step 3: σ agrees with ψ on all castSucc values (the first S coords).
    have hagree : ∀ i : Fin S, ψ i.castSucc = σ i.castSucc := by
      intro i
      have := hσ_conj i
      simp only [restrictTuple, id] at this
      exact this
    -- Step 4: Two bijections agreeing on T-1 elements agree on the last.
    have h_last : ψ (Fin.last S) = σ (Fin.last S) := by
      by_contra h_ne
      -- Use σ.surjective to find some j with σ j = ψ (Fin.last S).
      obtain ⟨j, hj⟩ := σ.surjective (ψ (Fin.last S))
      have jne : j ≠ Fin.last S := fun e => h_ne (e ▸ hj.symm)
      have hlt : (j : ℕ) < S := by
        have := j.isLt
        have hval : j.val ≠ S := fun h => jne (Fin.ext h)
        omega
      -- j = ⟨j.val, hlt⟩.castSucc.
      rw [show j = (⟨j.val, hlt⟩ : Fin S).castSucc from Fin.ext rfl] at hj
      rw [← hagree ⟨j.val, hlt⟩] at hj
      -- hj : ψ ⟨j.val, hlt⟩.castSucc = ψ (Fin.last S)
      -- by ψ injectivity: castSucc = last, impossible.
      exact absurd (hψ_bij.1 hj.symm) (Fin.castSucc_lt_last ⟨j.val, hlt⟩).ne'
    -- Step 5: ψ = σ everywhere on Fin (S + 1), so tupleOrbitRel holds.
    refine ⟨σ, hσ_aut, fun i => ?_⟩
    by_cases hne : i = Fin.last S
    · subst hne; exact h_last
    · have hlt : (i : ℕ) < S := by
        have := i.isLt
        have hval : i.val ≠ S := fun h => hne (Fin.ext h)
        omega
      rw [show i = (⟨i.val, hlt⟩ : Fin S).castSucc from Fin.ext rfl]
      -- Conclusion form: `ψ i = σ (id i)`. With id, becomes ψ i = σ i.
      simp only [id]
      exact hagree ⟨i.val, hlt⟩

/-- **Restriction along an arbitrary label-index injection** (Lovasz inline
analog of `MatrixDetermination.tupleEquiv_restrict_along`).

For any injection `r : Fin T' ↪ Fin k`, restricting tuple equivalence along
`r` on the label positions preserves equivalence. Generalizes
`tupleEquivSimple_restrict` (which uses the case `r = Fin.castSuccEmb`).

Used inside `tupleEquivSimple_surjective_case` to restrict from `Fin k` down
to `Fin T` along a section `r : Fin T ↪ Fin k` of `φ`. -/
theorem tupleEquivSimple_restrict_along {T k T' : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i)
    {φ ψ : Fin k → Fin T} (r : Fin T' ↪ Fin k)
    (h : tupleEquivSimple B W φ ψ) :
    tupleEquivSimple B W (φ ∘ r) (ψ ∘ r) := by
  classical
  intro n H hdec
  -- Edge-product helper for any size.
  have h_edge_rep : ∀ {m : ℕ} (ν : Fin m → Fin T) (a b : Fin m),
      B (ν (Quot.out (s(a, b) : Sym2 (Fin m))).1)
        (ν (Quot.out (s(a, b) : Sym2 (Fin m))).2) = B (ν a) (ν b) := by
    intro m ν a b
    have h_out_eq : Sym2.mk (Quot.out (s(a, b) : Sym2 (Fin m))) = s(a, b) :=
      Quot.out_eq _
    rcases Sym2.mk_eq_mk_iff.mp h_out_eq with heq | heq
    · rw [heq]
    · rw [heq]; exact hB _ _
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
      · exfalso
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
  let G : SimpleGraph (Fin (n + k)) := SimpleGraph.map shift H
  haveI hG_dec : DecidableRel G.Adj := Classical.decRel _
  -- Core translation. The sum on the LHS of `tupleEquivSimple` at
  -- `(φ ∘ r, H)` equals the sum at `(φ, G)`.
  suffices trans : ∀ (θ : Fin k → Fin T),
      (∑ σ : Fin n → Fin T,
        (let τ : Fin (n + T') → Fin T := fun v =>
          if h : (v : ℕ) < T' then (θ ∘ r) ⟨v, h⟩
          else σ ⟨v - T', by have := v.isLt; omega⟩
        (∏ v : Fin n, W (σ v)) *
        ∏ e ∈ H.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2))) =
      (∑ σ : Fin n → Fin T,
        (let τ : Fin (n + k) → Fin T := fun v =>
          if h : (v : ℕ) < k then θ ⟨v, h⟩
          else σ ⟨v - k, by have := v.isLt; omega⟩
        (∏ v : Fin n, W (σ v)) *
        ∏ e ∈ G.edgeFinset, B (τ (Quot.out e).1) (τ (Quot.out e).2))) by
    rw [trans φ, trans ψ]
    exact h n G
  intro θ
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only
  refine congrArg (fun x => (∏ v : Fin n, W (σ v)) * x) ?_
  -- Edge product: Finset.prod_bij with shift.sym2Map.
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
      rw [h_edge_rep ν' a b, h_edge_rep ν (shift a) (shift b)]
      have hτ : ∀ v : Fin (n + T'), ν (shift v) = ν' v := by
        intro v
        by_cases hv : (v : ℕ) < T'
        · have h_sh_eq : (shift v).val = (r ⟨v.val, hv⟩).val := by
            show (shiftFun v).val = _
            rw [shiftFun_pos v hv]
          have h_lt : ((shift v : Fin (n + k)) : ℕ) < k := by
            rw [h_sh_eq]; exact (r _).isLt
          simp only [hν_def, hν'_def, dif_pos h_lt, dif_pos hv, Function.comp_apply]
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

/-- **Auxiliary bijectivity lemma** (analog of `tupleEquiv_id_bijective` from
`MatrixDetermination.lean:5388`).

Under twin-free `B` with positive weights `W`, `tupleEquivSimple B W id χ`
forces `χ : Fin T → Fin T` to be bijective.

**Strategy**: restrict to `Fin (T - 1)` via `tupleEquivSimple_restrict`; apply
`IH_orbit` to obtain an automorphism τ with `χ ∘ castSucc = τ ∘ castSucc`. If
`χ(Fin.last) ≠ τ(Fin.last)`, set `v := χ(Fin.last)`, `d := τ(Fin.last)`; derive
`B d = B v` via (i) single-edge graphs + τ-automorphism (partial row equality
on `Fin T \ {d}`), (ii) an `n' = 1` row-sum graph + τ-automorphism reindex (row
sum equality), (iii) diagonal isolation using `hW > 0`. Row equality
contradicts `htwin`, so `χ(Fin.last) = τ(Fin.last)`, hence `χ = τ` is bijective. -/
theorem tupleEquivSimple_id_bijective {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (hB : ∀ i j, B i j = B j i)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j)
    (IH_orbit : ∀ {ξ' ψ' : Fin (T - 1) → Fin T},
      tupleEquivSimple B W ξ' ψ' → tupleOrbitRel B W ξ' ψ')
    (χ : Fin T → Fin T)
    (h : tupleEquivSimple B W (id : Fin T → Fin T) χ) :
    Function.Bijective χ := by
  classical
  rcases T with _ | S
  · refine ⟨fun a => Fin.elim0 a, fun b => Fin.elim0 b⟩
  · have h_restrict := tupleEquivSimple_restrict B W hB h
    obtain ⟨τ, hτ_aut, hτ_conj⟩ := IH_orbit h_restrict
    have hτ_eq : ∀ i : Fin S, χ i.castSucc = τ i.castSucc := by
      intro i; have := hτ_conj i
      simp only [restrictTuple, id_eq] at this; exact this
    have h_last : χ (Fin.last S) = τ (Fin.last S) := by
      by_contra h_ne
      set v := χ (Fin.last S) with hv_def
      set d := τ (Fin.last S) with hd_def
      have hvd_ne : v ≠ d := h_ne
      -- Single-edge graph (n' = 0): for a ≠ b, B a b = B (χ a) (χ b).
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
            symm := fun _ _ h =>
              h.elim (fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩)
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
        have key := h 0 F
        simp only [Fintype.sum_unique, Finset.univ_eq_empty, Finset.prod_empty,
          one_mul, hedge, Finset.prod_singleton] at key
        -- Unfold τ at u and v_p: u.val = a.val < S+1, v_p.val = b.val < S+1.
        set p := Quot.out (s(u, v_p) : Sym2 (Fin (0 + (S + 1))))
        have hout : (Sym2.mk p : Sym2 (Fin (0 + (S + 1)))) = s(u, v_p) :=
          Quot.out_eq _
        have key' : (p.1 = u ∧ p.2 = v_p) ∨ (p.1 = v_p ∧ p.2 = u) := by
          have := Sym2.eq_iff.mp hout
          rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h1, h2⟩
        have hu_eq : (⟨u.val, (by have := a.isLt; omega : u.val < S + 1)⟩ :
            Fin (S + 1)) = a := Fin.ext rfl
        have hv_eq : (⟨v_p.val, (by have := b.isLt; omega : v_p.val < S + 1)⟩ :
            Fin (S + 1)) = b := Fin.ext rfl
        have hu_lt : (u : Fin (0 + (S + 1))).val < S + 1 := by
          have := a.isLt; simp [u]
        have hv_lt : (v_p : Fin (0 + (S + 1))).val < S + 1 := by
          have := b.isLt; simp [v_p]
        rcases key' with ⟨hpu, hpv⟩ | ⟨hpu, hpv⟩
        · simp only [hpu, hpv, dif_pos hu_lt, dif_pos hv_lt, hu_eq, hv_eq, id_eq] at key
          exact key
        · simp only [hpu, hpv, dif_pos hv_lt, dif_pos hu_lt, hu_eq, hv_eq, id_eq] at key
          -- key : B b a = B (χ b) (χ a); want B a b = B (χ a) (χ b).
          calc B a b = B b a := hB _ _
            _ = B (χ b) (χ a) := key
            _ = B (χ a) (χ b) := hB _ _
      have partial_row_eq : ∀ Y : Fin (S + 1), Y ≠ d → B d Y = B v Y := by
        intro Y hY
        obtain ⟨k_pre, hk_pre⟩ := τ.surjective Y
        have hk_ne_last : k_pre ≠ Fin.last S := by
          intro he; subst he; exact hY hk_pre.symm
        have hkv : k_pre.val < S := by
          have := k_pre.isLt
          have : k_pre.val ≠ S := fun h => hk_ne_last (Fin.ext h)
          omega
        let i : Fin S := ⟨k_pre.val, hkv⟩
        have hi_eq : k_pre = i.castSucc := Fin.ext rfl
        have hτi : τ i.castSucc = Y := hi_eq ▸ hk_pre
        have hne_li : Fin.last S ≠ i.castSucc := by
          intro he; apply hk_ne_last; rw [hi_eq, ← he]
        have key : B (Fin.last S) i.castSucc = B (χ (Fin.last S)) (χ i.castSucc) :=
          single_edge_eq (Fin.last S) i.castSucc hne_li
        rw [hτ_eq i, hτi, ← hv_def] at key
        have hauto : B (Fin.last S) i.castSucc = B d Y := by
          have := hτ_aut.2 (Fin.last S) i.castSucc
          rw [← hd_def, hτi] at this
          exact this.symm
        rw [hauto] at key
        exact key
      -- Row-sum graph (n' = 1): edge between labeled-last and the single
      -- unlabeled vertex. Endpoints in Fin (1 + (S+1)).
      have row_sum_eq : ∑ t : Fin (S + 1), W t * B d t = ∑ t : Fin (S + 1), W t * B v t := by
        have row_sum_last_v : ∑ t : Fin (S + 1), W t * B (Fin.last S) t =
            ∑ t : Fin (S + 1), W t * B v t := by
          -- u' is labeled position `last` (val = S < S+1).
          -- v' is the unique unlabeled position (val = S+1 = (S+1)+0).
          let u' : Fin (1 + (S + 1)) := ⟨S, by omega⟩
          let v' : Fin (1 + (S + 1)) := ⟨S + 1, by omega⟩
          have hne' : u' ≠ v' := by
            intro he; have := congrArg Fin.val he; simp [u', v'] at this
          let G : SimpleGraph (Fin (1 + (S + 1))) :=
            { Adj := fun x y => (x = u' ∧ y = v') ∨ (x = v' ∧ y = u')
              symm := fun _ _ h =>
                h.elim (fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩)
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
          -- The simple-eval form for a generic θ : Fin (S+1) → Fin (S+1).
          have eval_θ : ∀ (θ : Fin (S + 1) → Fin (S + 1)),
              (∑ σ : Fin 1 → Fin (S + 1),
                (let τ' : Fin (1 + (S + 1)) → Fin (S + 1) := fun w =>
                  if hw : (w : ℕ) < S + 1 then θ ⟨w, hw⟩
                  else σ ⟨w - (S + 1), by have := w.isLt; omega⟩
                (∏ q : Fin 1, W (σ q)) *
                ∏ e ∈ G.edgeFinset, B (τ' (Quot.out e).1) (τ' (Quot.out e).2))) =
                ∑ t : Fin (S + 1), W t * B (θ (Fin.last S)) t := by
            intro θ
            rw [← (Equiv.funUnique (Fin 1) (Fin (S + 1))).symm.sum_comp]
            simp only [Equiv.funUnique_symm_apply]
            refine Finset.sum_congr rfl ?_
            intro m _
            simp only [hedge', Finset.prod_singleton, Fin.prod_univ_one]
            -- The W-prod is `W m`; the B-edge term equals `B (θ last) m`.
            congr 1
            -- Use Quot.out + Sym2 case-split.
            set p := Quot.out (s(u', v') : Sym2 (Fin (1 + (S + 1))))
            have hout : Sym2.mk p = s(u', v') := Quot.out_eq _
            have key : (p.1 = u' ∧ p.2 = v') ∨ (p.1 = v' ∧ p.2 = u') := by
              have := Sym2.eq_iff.mp hout
              rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [left; right] <;>
                exact ⟨h1, h2⟩
            have hu'_val : u'.val < S + 1 := by show S < S + 1; omega
            have hv'_val : ¬ v'.val < S + 1 := by show ¬ S + 1 < S + 1; omega
            have hu'_eq : (⟨u'.val, hu'_val⟩ : Fin (S + 1)) = Fin.last S := Fin.ext rfl
            have hv'_sub : (⟨v'.val - (S + 1), by have := v'.isLt; omega⟩ : Fin 1) = 0 :=
              Fin.ext (by show v'.val - (S + 1) = 0; omega)
            rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [h1, h2]
              simp only [dif_pos hu'_val, dif_neg hv'_val,
                hu'_eq, hv'_sub, uniqueElim_const]
            · rw [h1, h2]
              simp only [dif_pos hu'_val, dif_neg hv'_val,
                hu'_eq, hv'_sub, uniqueElim_const]
              exact hB _ _
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
          rcases mul_eq_zero.mp h_sum_diff with h1 | h1
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
          have := i.isLt
          have : i.val ≠ S := fun h => hi (Fin.ext h)
          omega
        rw [show i = (⟨i.val, hilt⟩ : Fin S).castSucc from Fin.ext rfl]
        exact hτ_eq ⟨i.val, hilt⟩
    rw [hχ_eq_τ]
    exact τ.bijective

/-- **Claim 4.4 — Surjective base case** (analog of
`MatrixDetermination.tupleEquiv_surjective_case_both` followed by
`tupleEquiv_surjective_case`).

If `φ : Fin k → Fin T` is surjective and `tupleEquivSimple B W φ ψ`,
then `tupleOrbitRel B W φ ψ`.

**Proof strategy**: pick a section `s : Fin T → Fin k` with `φ ∘ s = id`.
Restrict the equivalence along `s` (via `tupleEquivSimple_restrict_along`)
to obtain `tupleEquivSimple B W id (ψ ∘ s)`. Apply `tupleEquivSimple_id_bijective`
(uses `hW > 0`) to deduce `ψ ∘ s` is bijective, hence `ψ` is surjective.
Apply Claim 4.3 (`tupleEquivSimple_bijective_case`) to get an automorphism `σ`
with `ψ (s i) = σ i`. To extend to all of `Fin k`: for each `j` not in `im(s)`,
build a variant section `s'` agreeing with `s` off `φ j` but with `s' (φ j) = j`,
extract `σ'`, prove `σ = σ'` via the standard bijection-uniqueness argument. -/
theorem tupleEquivSimple_surjective_case {T k : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hW : ∀ i, 0 < W i)
    (hB : ∀ i j, B i j = B j i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (IH_orbit : ∀ {ξ' ψ' : Fin (T - 1) → Fin T},
      tupleEquivSimple B W ξ' ψ' → tupleOrbitRel B W ξ' ψ')
    (φ ψ : Fin k → Fin T) (hφ_surj : Function.Surjective φ)
    (h : tupleEquivSimple B W φ ψ) :
    tupleOrbitRel B W φ ψ := by
  classical
  -- Sub-claim: for any section s of φ, ψ ∘ s is bijective.
  have hψ_sect_bij : ∀ (s : Fin T → Fin k), (∀ i, φ (s i) = i) →
      Function.Bijective (ψ ∘ s) := by
    intro s hs
    have hs_inj : Function.Injective s := fun a b hab => by
      have ha := hs a; rw [hab, hs b] at ha; exact ha.symm
    let sEmb : Fin T ↪ Fin k := ⟨s, hs_inj⟩
    have h_s : tupleEquivSimple B W (φ ∘ s) (ψ ∘ s) :=
      tupleEquivSimple_restrict_along B W hB sEmb h
    have hφs_id : (φ ∘ s : Fin T → Fin T) = id := funext hs
    have h_id : tupleEquivSimple B W (id : Fin T → Fin T) (ψ ∘ s) := hφs_id ▸ h_s
    exact tupleEquivSimple_id_bijective B W hW hB htwin IH_orbit (ψ ∘ s) h_id
  -- Helper: for any section s of φ, extract σ with ψ ∘ s = σ.
  have section_to_aut : ∀ (s : Fin T → Fin k), (∀ i, φ (s i) = i) →
      ∃ σ : Equiv.Perm (Fin T),
        IsWeightedAutomorphism B W σ ∧ ∀ i, ψ (s i) = σ i := by
    intro s hs
    have hs_inj : Function.Injective s := fun a b hab => by
      have ha := hs a; rw [hab, hs b] at ha; exact ha.symm
    let sEmb : Fin T ↪ Fin k := ⟨s, hs_inj⟩
    have h_s : tupleEquivSimple B W (φ ∘ s) (ψ ∘ s) :=
      tupleEquivSimple_restrict_along B W hB sEmb h
    have hφs_id : (φ ∘ s : Fin T → Fin T) = id := funext hs
    have h_id : tupleEquivSimple B W (id : Fin T → Fin T) (ψ ∘ s) := hφs_id ▸ h_s
    have hψs_bij : Function.Bijective (ψ ∘ s) := hψ_sect_bij s hs
    obtain ⟨σ, hσ_aut, hσ_conj⟩ :=
      tupleEquivSimple_bijective_case B W hB IH_orbit (ψ ∘ s) hψs_bij h_id
    exact ⟨σ, hσ_aut, hσ_conj⟩
  -- Step 1: build primary section r via Classical.choose.
  have hφ_sect : ∀ i : Fin T, ∃ j : Fin k, φ j = i := hφ_surj
  let r : Fin T → Fin k := fun i => Classical.choose (hφ_sect i)
  have hr_spec : ∀ i : Fin T, φ (r i) = i :=
    fun i => Classical.choose_spec (hφ_sect i)
  obtain ⟨σ, hσ_aut, hψr_eq⟩ := section_to_aut r hr_spec
  -- Step 2: show ψ j = σ (φ j) for every j : Fin k.
  refine ⟨σ, hσ_aut, fun j => ?_⟩
  by_cases hj : ∃ i, r i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [hψr_eq i, hr_spec i]
  · push_neg at hj
    set i₀ : Fin T := φ j with hi₀
    let r' : Fin T → Fin k := fun i => if i = i₀ then j else r i
    have hr'_spec : ∀ i, φ (r' i) = i := by
      intro i
      by_cases hi : i = i₀
      · simp only [r', if_pos hi]; rw [hi, hi₀]
      · simp only [r', if_neg hi]; exact hr_spec i
    have hr'_at_i0 : r' i₀ = j := by simp only [r', if_pos rfl]
    have hr'_off_i0 : ∀ i, i ≠ i₀ → r' i = r i := fun i hi => by
      simp only [r', if_neg hi]
    obtain ⟨σ', hσ'_aut, hψr'_eq⟩ := section_to_aut r' hr'_spec
    have h_agree : ∀ i, i ≠ i₀ → σ i = σ' i := by
      intro i hi
      have hstep : ψ (r i) = ψ (r' i) := by rw [hr'_off_i0 i hi]
      rw [← hψr_eq i, hstep, hψr'_eq i]
    have h_at_i0 : σ i₀ = σ' i₀ := by
      by_contra hne
      obtain ⟨i, hi⟩ := σ.surjective (σ' i₀)
      have hi_ne : i ≠ i₀ := fun he => hne (he ▸ hi)
      have hσ'_eq : σ' i = σ' i₀ := by rw [← h_agree i hi_ne]; exact hi
      exact hi_ne (σ'.injective hσ'_eq)
    have hσ_eq_σ' : σ = σ' := by
      apply Equiv.ext
      intro i
      by_cases hi : i = i₀
      · subst hi; exact h_at_i0
      · exact h_agree i hi
    rw [show j = r' i₀ from hr'_at_i0.symm, hψr'_eq i₀, ← hσ_eq_σ']

/-- **Surjective-extension uniqueness** (`tupleEquiv_ext_eq_of_surj`
analog, `MatrixDetermination.lean:10801`).

If `α : Fin k → Fin T` is surjective and `B` is twin-free, then two
simple-equivalent extensions `Fin.snoc α a` and `Fin.snoc α b` must
have `a = b`.

**Proof strategy**: build single-edge simple graphs `F_{j, k}` on
`Fin (0 + (k + 1))` for each `j : Fin k`; the level-`(k+1)`
evaluation gives `B (α j) a = B (α j) b`. Surjectivity transfers
this to `∀ t, B t a = B t b`, hence `B a = B b` by symmetry,
contradicting twin-freeness unless `a = b`.

**Status**: proved by inlining the single-edge `labeledEvalK_singleEdge`
form directly into the `tupleEquivSimple` unfolding (`n' = 0`,
`Fintype.sum_unique` collapses the σ-sum). -/
theorem tupleEquivSimple_ext_eq_of_surj {T k : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j)
    {α : Fin k → Fin T}
    (hα_surj : Function.Surjective α)
    {a b : Fin T}
    (h : tupleEquivSimple B W (Fin.snoc α a) (Fin.snoc α b)) :
    a = b := by
  classical
  by_contra hab
  -- Reduce to row equality B a = B b, then contradict twin-freeness.
  suffices hrow : B a = B b by exact absurd hrow (htwin a b hab)
  funext t
  obtain ⟨j, rfl⟩ := hα_surj t
  -- For each j : Fin k, build the single-edge graph on Fin (0 + (k+1))
  -- with edge between positions j (= castSucc j as label) and k (= last
  -- as label). Apply `h` at this graph to extract `B (α j) a = B (α j) b`.
  suffices hmatch : B (α j) a = B (α j) b by
    calc B a (α j) = B (α j) a := hB _ _
      _ = B (α j) b := hmatch
      _ = B b (α j) := (hB _ _).symm
  -- Build the edge endpoints in Fin (0 + (k+1)).
  let u : Fin (0 + (k + 1)) := ⟨j.val, by have := j.isLt; omega⟩
  let v : Fin (0 + (k + 1)) := ⟨k, by omega⟩
  have hne : u ≠ v := by
    simp only [ne_eq, Fin.mk.injEq, u, v]
    have := j.isLt; omega
  -- Define the single-edge graph inline.
  let F : SimpleGraph (Fin (0 + (k + 1))) :=
    { Adj := fun x y => (x = u ∧ y = v) ∨ (x = v ∧ y = u)
      symm := fun _ _ h =>
        h.elim (fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩) (fun ⟨h1, h2⟩ => Or.inl ⟨h2, h1⟩)
      loopless := fun _ h => by
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hne (h1.symm.trans h2)
        · exact hne (h2.symm.trans h1) }
  haveI hF_dec : DecidableRel F.Adj := fun x y =>
    if h₁ : x = u ∧ y = v then .isTrue (.inl h₁)
    else if h₂ : x = v ∧ y = u then .isTrue (.inr h₂)
    else .isFalse (fun h => h.elim (fun a => h₁ a) (fun a => h₂ a))
  have hedge : F.edgeFinset = {s(u, v)} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset]; exact Or.inl ⟨rfl, rfl⟩
    · intro e he; rw [SimpleGraph.mem_edgeFinset] at he
      exact Sym2.ind (fun x y (hadj : F.Adj x y) => by
        rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
        · rw [h1, h2, Sym2.eq_swap]) e he
  -- Apply h at this graph. The `n' = 0` case collapses the σ sum to a
  -- single term (the empty function), and the W-product is empty.
  have key := h 0 F
  -- Unfold both sides via Fintype.sum_unique and the single-edge form.
  -- The Sym2 representative of s(u, v) might be either (u, v) or (v, u);
  -- handle both via Quot.out_eq + hB symmetry.
  simp only [Fintype.sum_unique, Finset.univ_eq_empty, Finset.prod_empty,
    one_mul, hedge, Finset.prod_singleton] at key
  -- Now τ for both sides: positions < k+1 read the label map (snoc α _),
  -- and there are no positions ≥ k+1 since n' = 0.
  set p := Quot.out (s(u, v) : Sym2 (Fin (0 + (k + 1))))
  have hout : (Sym2.mk p : Sym2 (Fin (0 + (k + 1)))) = s(u, v) := Quot.out_eq _
  -- Case split on which order p represents.
  have key' : (p.1 = u ∧ p.2 = v) ∨ (p.1 = v ∧ p.2 = u) := by
    have := Sym2.eq_iff.mp hout
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  -- Simplify (Fin.snoc α x) at castSucc j and at last k to α j and x.
  have hu_cs : (⟨u.val, (by have := j.isLt; omega : u.val < k + 1)⟩ :
      Fin (k + 1)) = j.castSucc := Fin.ext rfl
  have hv_la : (⟨v.val, (by omega : v.val < k + 1)⟩ :
      Fin (k + 1)) = Fin.last k := Fin.ext rfl
  rcases key' with ⟨hpu, hpv⟩ | ⟨hpu, hpv⟩
  · -- p = (u, v): direct read.
    simp only [hpu, hpv, dif_pos (show (u : Fin (0 + (k + 1))).val < k + 1
      by have := j.isLt; simp [u]; omega),
      dif_pos (show (v : Fin (0 + (k + 1))).val < k + 1 by simp [v]),
      hu_cs, hv_la, Fin.snoc_castSucc, Fin.snoc_last] at key
    exact key
  · -- p = (v, u): swap via symmetry.
    simp only [hpu, hpv, dif_pos (show (v : Fin (0 + (k + 1))).val < k + 1
      by simp [v]),
      dif_pos (show (u : Fin (0 + (k + 1))).val < k + 1
      by have := j.isLt; simp [u]; omega),
      hu_cs, hv_la, Fin.snoc_castSucc, Fin.snoc_last] at key
    -- key : B a (α j) = B b (α j); want B (α j) a = B (α j) b.
    calc B (α j) a = B a (α j) := hB _ _
      _ = B b (α j) := key
      _ = B (α j) b := hB _ _

/-! ### §3.95 — Connection-matrix rank theorem (canonical architectural sorry)

This subsection introduces the **connection matrix** `N(K, B, W)` over
k-labeled (multi-)graphs and states the **rank theorem** (Lovász
TR-2004-82 §3, Theorem 2.2). The rank theorem is the deep Lovász §3
content underlying Lemma 2.4 / Lemma 2.5 in our framework.

**Connection matrix** `N(K, B, W)` (Lovász §2, p. 4): rows indexed by
label maps `ξ : Fin K → Fin T`, columns indexed by k-labeled (simple)
graphs `F`. Entry `N(K, B, W)[ξ, F] := simpleEvalK F B W ξ`. Two rows
`ξ, ξ'` are equal iff `tupleEquivSimple B W ξ ξ'` holds.

In our framework we do not materialize the matrix explicitly; we
instead **encode "row equality" as `tupleEquivSimple`** directly. By
the definition of `tupleEquivSimple` (∀ n F, `simpleEvalAt` ξ =
`simpleEvalAt` ξ'), this is precisely row-extensional equality —
the row of `ξ` in `N(K, B, W)` IS the function
`(n, F) ↦ simpleEvalAt B W F ξ`.

The forward direction (orbit ⟹ row equality) is proved as
`tupleEquivSimple_of_tupleOrbitRel` (L1619, FULLY PROVED): if two
tuples are in the same orbit, their rows agree.

The reverse direction (row equality ⟹ orbit, under twin-free + W > 0)
is the rank theorem itself, stated as the proposition

```
tupleEquivSimple B W ξ ξ' → tupleOrbitRel B W ξ ξ'
```

under twin-free `B` and strictly positive `W`. This is exactly Lovász's
Theorem 2.2 ("rk N(K, B, W) = orb_K(B, W)") in the equivalence-class
form: distinct rank = distinct orbit, so row equality forces orbit
equality.

**Status**: SORRY'd at the rank theorem. All downstream content
(`tupleEquivSimple_implies_orbit`, `tupleEquivMulti_implies_orbit`, the
twin-free multigraph bridge corollary) routes through this single named
sorry. The remaining sorry (general non-twin-free `n+1` multigraph
bridge, `multiLabeledEvalK_tupleEquiv_invariant`) is independent.

**Reduction to the deep paper content**: the proof structure mirrors the
strong induction + deficit-induction in
`tupleEquiv_implies_tupleOrbitRel` (`MatrixDetermination.lean:10873`),
with the architectural sorry at the inner-base `T - 1 ≥ k + 1` case of
the deficit-induction. Closing this requires either a multigraph-
evaluation route (diagonal / self-loop extraction) or a direct fiber
construction in `tupleEquivSimple_surjective_case` /
`tupleEquivSimple_id_bijective` that avoids the deficit-1 IH (see
`MatrixDetermination.lean:11002-11007`). -/

/-! **Connection-matrix rank theorem** (Lovász TR-2004-82 §3,
Theorem 2.2; equivalence-class form) — **PRIMARY paper root**.

**Dependency hierarchy** (post-2026-05-12 architectural decision):
  - **PRIMARY ROOT**: the rank theorem (Lovász §3 Theorem 2.2,
    simple-graph form, twin-free).
  - **SECONDARY**: `multiLabeledEvalK_tupleEquiv_invariant` at L1315
    (general, non-twin-free multigraph form).

Closing the rank theorem discharges everything the downstream
matrix-determination chain needs (which all has twin-free hypothesis):
`tupleEquivSimple_implies_orbit`, `tupleEquivMulti_implies_orbit`,
`multiLabeledEvalK_tupleEquiv_invariant_twinFree`. The secondary
multigraph bridge is a strictly stronger non-twin-free statement
that may be left as an off-axis generalization.

Under twin-free `B` and strictly positive `W`, the rank theorem
states `tupleEquivSimple ⟹ tupleOrbitRel`. The **separation**
contrapositive (`orbit_separation_by_simple_graph` below) is the
canonical primary sorry; the rank theorem is a short contradiction
proof from it. -/

/-! ### Lovász §3 — Idempotent decomposition: orbit indicators

This section introduces the **orbit indicator** for `(B, W)`-automorphism
orbits of `Fin K → Fin T`, plus the named architectural lemma asserting
that orbit indicators lie in the ℝ-span of simple-graph evaluations
(Lovász §3 multigraph-algebra fullness, restricted to simple graphs
under twin-free `B`).

The canonical primary sorry of the Lovász chain is *migrated* from
`orbit_separation_by_simple_graph` to `orbitIndicator_mem_simpleGraphSpan`
— a cleaner ℝ-linear-algebra statement that captures the same content. -/

/-- **`tupleOrbitRel` is reflexive.**

Witnessed by the identity automorphism. -/
theorem tupleOrbitRel_refl {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (ξ : Fin K → Fin T) :
    tupleOrbitRel B W ξ ξ :=
  ⟨Equiv.refl _, ⟨fun _ => rfl, fun _ _ => rfl⟩, fun _ => rfl⟩

/-- **`tupleOrbitRel` is symmetric.**

If `σ` realizes `ξ' = σ ∘ ξ`, then `σ.symm` realizes `ξ = σ.symm ∘ ξ'`. -/
theorem tupleOrbitRel_symm {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    {ξ ξ' : Fin K → Fin T} (h : tupleOrbitRel B W ξ ξ') :
    tupleOrbitRel B W ξ' ξ := by
  obtain ⟨σ, ⟨hW_aut, hB_aut⟩, hσ⟩ := h
  refine ⟨σ.symm, ⟨?_, ?_⟩, ?_⟩
  · -- W (σ.symm i) = W i
    intro i
    have := hW_aut (σ.symm i)
    -- W (σ (σ.symm i)) = W (σ.symm i), and σ (σ.symm i) = i
    rw [σ.apply_symm_apply] at this
    exact this.symm
  · -- B (σ.symm i) (σ.symm j) = B i j
    intro i j
    have := hB_aut (σ.symm i) (σ.symm j)
    rw [σ.apply_symm_apply, σ.apply_symm_apply] at this
    exact this.symm
  · -- ξ i = σ.symm (ξ' i)
    intro i
    have := hσ i
    rw [this, σ.symm_apply_apply]

/-- **`tupleOrbitRel` is transitive.**

If `σ₁` realizes `ξ' = σ₁ ∘ ξ` and `σ₂` realizes `ξ'' = σ₂ ∘ ξ'`, then
`σ₂ * σ₁` realizes `ξ'' = (σ₂ * σ₁) ∘ ξ`. -/
theorem tupleOrbitRel_trans {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    {ξ ξ' ξ'' : Fin K → Fin T}
    (h₁ : tupleOrbitRel B W ξ ξ') (h₂ : tupleOrbitRel B W ξ' ξ'') :
    tupleOrbitRel B W ξ ξ'' := by
  obtain ⟨σ₁, ⟨hW₁, hB₁⟩, hσ₁⟩ := h₁
  obtain ⟨σ₂, ⟨hW₂, hB₂⟩, hσ₂⟩ := h₂
  refine ⟨σ₁.trans σ₂, ⟨?_, ?_⟩, ?_⟩
  · intro i
    show W (σ₂ (σ₁ i)) = W i
    rw [hW₂ (σ₁ i), hW₁ i]
  · intro i j
    show B (σ₂ (σ₁ i)) (σ₂ (σ₁ j)) = B i j
    rw [hB₂ (σ₁ i) (σ₁ j), hB₁ i j]
  · intro i
    show ξ'' i = σ₂ (σ₁ (ξ i))
    rw [hσ₂ i, hσ₁ i]

/-- **`tupleOrbitRel` is an equivalence relation.** -/
theorem tupleOrbitRel_equivalence {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    Equivalence (tupleOrbitRel B W (K := K)) :=
  { refl := tupleOrbitRel_refl B W
    symm := tupleOrbitRel_symm B W
    trans := tupleOrbitRel_trans B W }

/-- **Setoid on tuples** induced by `tupleOrbitRel`. -/
def tupleOrbitSetoid {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (K : ℕ) : Setoid (Fin K → Fin T) :=
  ⟨tupleOrbitRel B W, tupleOrbitRel_equivalence B W⟩

/-- **Quotient of `Fin K → Fin T` by the `(B, W)`-orbit relation.**

`OrbitClass T K B W` parametrizes `(B, W)`-automorphism orbits of
`K`-tuples. Used as the index set for the idempotent decomposition in
Lovász §3. -/
def OrbitClass (T K : ℕ) (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :=
  Quotient (tupleOrbitSetoid B W K)

/-- **Orbit indicator** of a `K`-tuple `ξ`.

`orbitIndicator B W ξ ξ' = 1` if `ξ` and `ξ'` are orbit-related and
`0` otherwise. Equivalently, the {0,1}-indicator of the orbit-class
of `ξ` (a representative-dependent name for a representative-invariant
function — invariance is `orbitIndicator_orbit_invariant`). -/
noncomputable def orbitIndicator {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (ξ : Fin K → Fin T) : (Fin K → Fin T) → ℝ :=
  fun ξ' =>
    haveI : Decidable (tupleOrbitRel B W ξ ξ') := Classical.dec _
    if tupleOrbitRel B W ξ ξ' then 1 else 0

/-- **Orbit-invariance of `orbitIndicator`** (as a function of the source).

Replacing the source representative `ξ` by an orbit-related `ξ_alt`
gives the same indicator function. -/
theorem orbitIndicator_orbit_invariant {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    {ξ ξ_alt : Fin K → Fin T} (h : tupleOrbitRel B W ξ ξ_alt) :
    orbitIndicator B W ξ = orbitIndicator B W ξ_alt := by
  funext η
  unfold orbitIndicator
  by_cases hξη : tupleOrbitRel B W ξ η
  · -- ξ ~ η. Need ξ_alt ~ η. From ξ ~ ξ_alt (h), get ξ_alt ~ ξ, then trans.
    have h_alt : tupleOrbitRel B W ξ_alt η :=
      tupleOrbitRel_trans B W (tupleOrbitRel_symm B W h) hξη
    simp [hξη, h_alt]
  · -- ¬ ξ ~ η. Need ¬ ξ_alt ~ η. Otherwise ξ ~ ξ_alt ~ η.
    have h_alt : ¬ tupleOrbitRel B W ξ_alt η := by
      intro h_alt_pos
      exact hξη (tupleOrbitRel_trans B W h h_alt_pos)
    simp [hξη, h_alt]

/-- **`orbitIndicator ξ ξ = 1`** (reflexivity). -/
theorem orbitIndicator_self {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (ξ : Fin K → Fin T) :
    orbitIndicator B W ξ ξ = 1 := by
  unfold orbitIndicator
  simp [tupleOrbitRel_refl B W ξ]

/-- **`orbitIndicator ξ ξ' = 0` when not orbit-related.** -/
theorem orbitIndicator_of_not_orbit {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    {ξ ξ' : Fin K → Fin T} (h : ¬ tupleOrbitRel B W ξ ξ') :
    orbitIndicator B W ξ ξ' = 0 := by
  unfold orbitIndicator
  simp [h]

/-- **Orbit indicators lie in the ℝ-span of simple-graph evaluations**
(Lovász §3 — fullness of the simple-graph evaluation algebra under
twin-free `B`) — **SECONDARY / OFF-AXIS** (post-2026-05-13 reanalysis).

For any source tuple `ξ : Fin K → Fin T`, the orbit indicator
`orbitIndicator B W ξ` can be written as an ℝ-linear combination of
simple-graph evaluations `simpleEvalAt B W F : (Fin K → Fin T) → ℝ`
(ranging over simple graphs `F` on `Fin (n + K)` for various `n`).

**Status reverted to OFF-AXIS**: the natural Lagrange-interpolation
route produces PRODUCTS of `simpleEvalAt` (= multigraph evals via
glue), not linear combinations. Converting back to a linear
combination of simple-graph evals would itself need Lemma 2.5
content — circular.

The PRIMARY ROOT is now `orbit_separation_by_simple_graph` (the
contrapositive form, which doesn't require product expansion). This
span theorem is a stronger CONSEQUENCE that may follow from
separation + the multigraph bridge.

The representation uses pairs `(c, ⟨n, ⟨F, dec⟩⟩)` where
`c : ℝ` is a coefficient, `n : ℕ` is an unlabeled-vertex count,
`F : SimpleGraph (Fin (n + K))` is a simple labeled graph, and
`dec : DecidableRel F.Adj` is the required decidability witness.

**Status**: canonical primary sorry (migrated from
`orbit_separation_by_simple_graph`).

**Proof approach** (Lovász §3): the simple-graph evaluation algebra
under twin-free `B` is **dense** in the space of orbit-invariant
functions; the orbit indicators form a basis of this latter space;
hence each indicator is a finite ℝ-linear combination. This is the
multigraph-algebra fullness theorem of Lovász §3, restricted to
simple graphs under the twin-free hypothesis.

**Natural Lagrange-interpolation route** (per post-2026-05-13 user
analysis): for each orbit class O' ≠ orbit(ξ), pick a separating
simple graph F_{O'} (its existence is `orbit_separation_by_simple_graph`,
PROVED from this theorem — a circular dependency). The indicator is
the product `∏_{O' ≠ orbit(ξ)} (simpleEvalAt F_{O'} - w_{O'}) /
(v_{O'} - w_{O'})` over orbit classes.

**Obstacle** (multigraph-vs-simple-graph product): expanding the
product yields PRODUCTS of `simpleEvalAt`s, which via the
glue-multigraph identity are MULTIGRAPH evaluations (since disjoint
unions of simple graphs at shared labels can produce label-label
multi-edges). Converting these multigraph evals back to simple-graph
linear combinations is itself the Lemma 2.5 content. The
contrapositive `orbit_separation_by_simple_graph` does NOT have this
issue (it just exhibits a single separating graph) — so the
"separation" form may be the actually attackable formulation, with
the span form derived from it via a careful product-expansion route. -/
theorem orbitIndicator_mem_simpleGraphSpan {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (_hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (_hW : ∀ i, 0 < W i)
    (_htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (ξ : Fin K → Fin T) :
    ∃ (cs : List (ℝ × Σ (n : ℕ) (F : SimpleGraph (Fin (n + K))),
        DecidableRel F.Adj)),
      orbitIndicator B W ξ = fun η =>
        (cs.map (fun p =>
          p.1 * @simpleEvalAt T K p.2.1 B W p.2.2.1 p.2.2.2 η)).sum := by
  sorry

/-! ### Orbit separation: edge-or-degree → simple-graph form

Post-2026-05-13 separator_search empirical analysis: across 21K non-
orbit pairs at small (T, K), 100% are separated by a SINGLE edge —
either label-label or label-to-unlabeled. This motivates an
intermediate theorem `orbit_separation_by_edge_or_degree` giving an
explicit edge OR degree-profile witness, from which the simple graph
is a single-edge graph (n=0) or a single-edge "rooted star" (n=1).

Falsification: see `scripts/falsify_edge_degree_conjecture.py`. 64K
pairs tested, zero counterexamples. -/

/-! **Orbit separation by edge or degree** — **KNOWN-FALSE / OFF-AXIS**
(refuted 2026-05-14 by C₅ ⊔ C₆ counterexample at K=1).

**Counterexample**: B = adjacency of C₅ ⊔ C₆, W = uniform 1.
- ξ = (0,) (vertex in C₅), ξ' = (5,) (vertex in C₆).
- K = 1: edge profile vacuous (no a ≠ b).
- Weighted degrees agree: both = 2 (regular graphs).
- But no aut σ ∈ Aut(C₅ ⊔ C₆) = D₅ × D₆ sends C₅-vertex to C₆-vertex
  (component preservation).

Falsification: `scripts/falsify_edge_degree_conjecture.py` updated
with C₅ ⊔ C₆ test; 60 counterexamples found in this single family.

The minimal separating simple graph for this pair is a **5-cycle
rooted at the label** (n_unlabeled = 4, 5 edges): the label vertex
participates in 2 distinct 5-cycles in C₅ but 0 in C₆. Found by
`scripts/separator_search.py cycles`.

**Implication**: edge + degree profiles are insufficient. The
canonical primary sorry must reflect this — restore
`orbit_separation_by_simple_graph` as the abstract primary, with
explicit acknowledgment that the separator family includes rooted
cycles / paths / trees of unbounded size. -/

/-- **Weighted degree** of vertex `i` in `(B, W)`. -/
noncomputable def weightedDegree {T : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (i : Fin T) : ℝ :=
  ∑ t : Fin T, W t * B i t

/-- **Same tuple edge profile**: ξ and ξ' agree on all label-label
B-entries at distinct labels. -/
def sameTupleEdgeProfile {T K : ℕ} (B : Fin T → Fin T → ℝ)
    (ξ ξ' : Fin K → Fin T) : Prop :=
  ∀ a b : Fin K, a ≠ b → B (ξ a) (ξ b) = B (ξ' a) (ξ' b)

/-- **Same tuple degree profile**: ξ and ξ' have equal weighted
degrees at every label position. -/
def sameTupleDegreeProfile {T K : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (ξ ξ' : Fin K → Fin T) : Prop :=
  ∀ a : Fin K, weightedDegree B W (ξ a) = weightedDegree B W (ξ' a)

-- NOTE: previously-stated `orbit_separation_by_edge_or_degree` and
-- `same_edge_and_degree_profile_implies_orbit` are KNOWN-FALSE per
-- 2026-05-14 C₅ ⊔ C₆ analysis (60 counterexamples in this single
-- family). Removed entirely (rather than sorry'd) to prevent
-- transitive use of a false theorem. See docstring above and
-- `scripts/falsify_edge_degree_conjecture.py` + `separator_search.py`.
--
-- The minimal separator for the C₅ vs C₆ K=1 pair is a 5-cycle
-- rooted at the label (n_unlabeled = 4, 5 edges). The genuine
-- Lovász §3 content requires UNBOUNDED rooted simple-graph
-- separator families.

/-! ### §3.95.5 — K=1 rooted profile target

Per 2026-05-14 user directive: introduce a K=1 rooted-profile
specialization of the separation theorem. This is the simplest
non-trivial Lovász separation form: under twin-free B + W > 0,
distinct vertex orbits are separated by some rooted simple graph
evaluation.

This statement is empirically valid (C₅ vs C₆ separator is a
5-cycle rooted at the label). Unlike the false edge-or-degree
conjecture, the rooted-profile family is unbounded — but the
separation IS by a SINGLE simple graph, not a polynomial in
multiple. -/

/-- **Vertex orbit relation** — K=1 specialization of `tupleOrbitRel`.
Two vertices are orbit-related iff some `(B, W)`-automorphism maps
one to the other. -/
def vertexOrbitRel {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (i j : Fin T) : Prop :=
  ∃ σ : Equiv.Perm (Fin T), IsWeightedAutomorphism B W σ ∧ σ i = j

/-- **Rooted simple-graph profile** at vertex `i`: the simple-graph
evaluation with the single label position fixed to `i`. -/
noncomputable def rootedProfile {T n : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (i : Fin T) (F : SimpleGraph (Fin (n + 1)))
    [DecidableRel F.Adj] : ℝ :=
  simpleEvalAt B W F (fun _ : Fin 1 => i)

/-- **Rooted-profile equivalence**: two vertices `i, j` agree on every
rooted simple-graph evaluation.

This is the K=1 specialization of `tupleEquivSimple`. By Lovász Lemma 2.4
K=1, under twin-free B + W > 0, this equivalence corresponds exactly to
the vertex orbit relation. -/
def rootedProfileEquiv {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (i j : Fin T) : Prop :=
  ∀ (n : ℕ) (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj],
    rootedProfile B W i F = rootedProfile B W j F

/-- **Forward direction (trivial)**: vertex orbit ⟹ rooted-profile equivalence.
Follows from automorphism invariance of `simpleEvalAt`. -/
theorem rootedProfileEquiv_of_vertexOrbitRel {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) {i j : Fin T}
    (h : vertexOrbitRel B W i j) :
    rootedProfileEquiv B W i j := by
  obtain ⟨σ, hσ_aut, hσ_eq⟩ := h
  intro n F _
  unfold rootedProfile simpleEvalAt
  -- Use the K=1 specialization of orbit-invariance.
  have h_orbit : tupleOrbitRel B W (fun _ : Fin 1 => i) (fun _ : Fin 1 => j) := by
    refine ⟨σ, hσ_aut, ?_⟩
    intro k
    have : k = (0 : Fin 1) := Subsingleton.elim _ _
    rw [this]; exact hσ_eq.symm
  exact tupleEquivSimple_of_tupleOrbitRel B W h_orbit n F

/-- **Rooted orbit indicator** of vertex `i`: the function `Fin T → ℝ`
mapping each vertex `v` to `1` if `v` lies in the `(B, W)`-orbit of `i`,
and `0` otherwise.

This is the canonical "test function" for the Lovász §3 K=1 rank theorem:
the orbit indicators span the space of `(B, W)`-automorphism-invariant
functions on `Fin T`. The K=1 rank theorem asserts that the rooted-profile
functions span this same space, so each orbit indicator lies in the
rooted-profile ℝ-span. -/
noncomputable def rootedOrbitIndicator {T : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (i : Fin T) : Fin T → ℝ :=
  fun v => open Classical in if vertexOrbitRel B W i v then (1 : ℝ) else 0

/-- **Rooted-profile function** as a function `Fin T → ℝ`. For a fixed
simple graph `F` with one labeled position, `rootedProfileFun B W F v`
is the rooted simple-graph evaluation with the label fixed to `v`. -/
noncomputable def rootedProfileFun {T n : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj] :
    Fin T → ℝ :=
  fun v => rootedProfile B W v F

/-! ### Algebra of rooted simple-graph profiles (K=1 rank theorem) -/

/-- **Membership predicate** for the rooted-profile ℝ-span: `f : Fin T → ℝ`
is in the ℝ-span iff it equals a finite linear combination of
rooted-profile functions `rootedProfileFun B W F` over simple graphs `F`. -/
def InRootedProfileSpan {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (f : Fin T → ℝ) : Prop :=
  ∃ (N : ℕ) (g : Fin N → Σ (n : ℕ) (F : SimpleGraph (Fin (n + 1))), DecidableRel F.Adj)
    (c : Fin N → ℝ),
    f = fun v => ∑ k : Fin N, c k * @rootedProfileFun T (g k).1 B W (g k).2.1 (g k).2.2 v

/-- The rooted profile of a single graph is in the span (singleton sum). -/
theorem InRootedProfileSpan.of_profile {T n : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (F : SimpleGraph (Fin (n + 1))) [hF : DecidableRel F.Adj] :
    InRootedProfileSpan B W (rootedProfileFun B W F) := by
  refine ⟨1, fun _ => ⟨n, F, hF⟩, fun _ => 1, ?_⟩
  funext v
  simp

/-- Zero function is in the span (empty sum). -/
theorem InRootedProfileSpan.zero {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    InRootedProfileSpan B W (fun _ => (0 : ℝ)) := by
  refine ⟨0, Fin.elim0, Fin.elim0, ?_⟩
  funext v
  simp

/-- Closure under addition. -/
theorem InRootedProfileSpan.add {T : ℕ} {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    {f₁ f₂ : Fin T → ℝ}
    (h₁ : InRootedProfileSpan B W f₁) (h₂ : InRootedProfileSpan B W f₂) :
    InRootedProfileSpan B W (f₁ + f₂) := by
  obtain ⟨N₁, g₁, c₁, hf₁⟩ := h₁
  obtain ⟨N₂, g₂, c₂, hf₂⟩ := h₂
  -- Re-index via Sum to sidestep Fin.addCases motive issues.
  let g : Fin N₁ ⊕ Fin N₂ → Σ (n : ℕ) (F : SimpleGraph (Fin (n + 1))), DecidableRel F.Adj :=
    Sum.elim g₁ g₂
  let c : Fin N₁ ⊕ Fin N₂ → ℝ := Sum.elim c₁ c₂
  refine ⟨N₁ + N₂,
    fun k => g (finSumFinEquiv.symm k),
    fun k => c (finSumFinEquiv.symm k), ?_⟩
  funext v
  have e₁ := congr_fun hf₁ v
  have e₂ := congr_fun hf₂ v
  simp only [Pi.add_apply, e₁, e₂]
  rw [show (∑ k : Fin (N₁ + N₂), c (finSumFinEquiv.symm k) *
        @rootedProfileFun T (g (finSumFinEquiv.symm k)).1 B W
          (g (finSumFinEquiv.symm k)).2.1 (g (finSumFinEquiv.symm k)).2.2 v)
      = ∑ s : Fin N₁ ⊕ Fin N₂, c s *
          @rootedProfileFun T (g s).1 B W (g s).2.1 (g s).2.2 v from ?_]
  · rw [Fintype.sum_sum_type]
    rfl
  · exact Equiv.sum_comp finSumFinEquiv.symm
      (fun s => c s * @rootedProfileFun T (g s).1 B W (g s).2.1 (g s).2.2 v)

/-- Closure under scalar multiplication. -/
theorem InRootedProfileSpan.smul {T : ℕ} {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    (c : ℝ) {f : Fin T → ℝ} (h : InRootedProfileSpan B W f) :
    InRootedProfileSpan B W (fun v => c * f v) := by
  obtain ⟨N, g, c', hf⟩ := h
  refine ⟨N, g, fun k => c * c' k, ?_⟩
  funext v
  have e := congr_fun hf v
  rw [e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The empty graph on `Fin 1` has rooted profile equal to `1` at every vertex. -/
theorem rootedProfileFun_bot {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    rootedProfileFun B W (⊥ : SimpleGraph (Fin (0 + 1))) = fun _ => 1 := by
  funext v
  unfold rootedProfileFun rootedProfile simpleEvalAt
  simp
  convert (pow_zero (B v v)).symm using 1

/-- Constant function `1` is in the rooted-profile span (via the empty graph). -/
theorem InRootedProfileSpan.one {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    InRootedProfileSpan B W (fun _ => (1 : ℝ)) := by
  have h := InRootedProfileSpan.of_profile B W (⊥ : SimpleGraph (Fin (0 + 1)))
  rw [rootedProfileFun_bot] at h
  exact h

/-- Constant function `c` is in the rooted-profile span. -/
theorem InRootedProfileSpan.const {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (c : ℝ) : InRootedProfileSpan B W (fun _ => c) := by
  have h := (InRootedProfileSpan.one B W).smul c
  simpa using h

/-- Embedding of `F₁`'s vertices into the rooted-product graph: identity
on values (so position 0 → root, positions 1..n₁ → F₁'s unlabeled). -/
def rootedProductEmb₁ (n₁ n₂ : ℕ) : Fin (n₁ + 1) ↪ Fin ((n₁ + n₂) + 1) where
  toFun v := ⟨v.val, by have := v.isLt; omega⟩
  inj' a b h := by
    have : a.val = b.val := by exact_mod_cast Fin.mk.inj h
    exact Fin.ext this

/-- Embedding of `F₂`'s vertices into the rooted-product graph: position 0
maps to the root (shared with `F₁`'s root); positions 1..n₂ map to
positions `n₁ + 1..n₁ + n₂` (F₂'s unlabeled, disjoint from F₁'s). -/
def rootedProductEmb₂ (n₁ n₂ : ℕ) : Fin (n₂ + 1) ↪ Fin ((n₁ + n₂) + 1) where
  toFun v := if v.val = 0 then ⟨0, by omega⟩
             else ⟨v.val + n₁, by have := v.isLt; omega⟩
  inj' a b h := by
    ext
    by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0
    · omega
    · simp only [ha, hb, ↓reduceIte] at h
      have : (0 : ℕ) = b.val + n₁ := by exact_mod_cast Fin.mk.inj h
      omega
    · simp only [ha, hb, ↓reduceIte] at h
      have : a.val + n₁ = 0 := by exact_mod_cast Fin.mk.inj h
      omega
    · simp only [ha, hb, ↓reduceIte] at h
      have : a.val + n₁ = b.val + n₁ := by exact_mod_cast Fin.mk.inj h
      omega

noncomputable def rootedProduct {n₁ n₂ : ℕ}
    (F₁ : SimpleGraph (Fin (n₁ + 1)))
    (F₂ : SimpleGraph (Fin (n₂ + 1))) :
    SimpleGraph (Fin ((n₁ + n₂) + 1)) :=
  SimpleGraph.map (rootedProductEmb₁ n₁ n₂) F₁ ⊔
    SimpleGraph.map (rootedProductEmb₂ n₁ n₂) F₂

/-! Exact-shape application lemmas for the rooted-product embeddings.
These unfold the `where`-defined `toFun` directly, so `rfl` works. -/

@[simp] theorem rootedProductEmb₁_val {n₁ n₂ : ℕ} (v : Fin (n₁ + 1)) :
    (rootedProductEmb₁ n₁ n₂ v).val = v.val := rfl

@[simp] theorem rootedProductEmb₂_val_zero {n₁ n₂ : ℕ} (v : Fin (n₂ + 1))
    (h : v.val = 0) : (rootedProductEmb₂ n₁ n₂ v).val = 0 := by
  show (if v.val = 0 then (⟨0, by omega⟩ : Fin _)
        else ⟨v.val + n₁, by have := v.isLt; omega⟩).val = 0
  rw [if_pos h]

@[simp] theorem rootedProductEmb₂_val_pos {n₁ n₂ : ℕ} (v : Fin (n₂ + 1))
    (h : v.val ≠ 0) : (rootedProductEmb₂ n₁ n₂ v).val = v.val + n₁ := by
  show (if v.val = 0 then (⟨0, by omega⟩ : Fin _)
        else ⟨v.val + n₁, by have := v.isLt; omega⟩).val = v.val + n₁
  rw [if_neg h]

/-! Disjointness helpers between the two embedding images. -/

/-- `rootedProductEmb₁` image vertices have val ≤ n₁. -/
theorem rootedProductEmb₁_val_le {n₁ n₂ : ℕ} (v : Fin (n₁ + 1)) :
    (rootedProductEmb₁ n₁ n₂ v).val ≤ n₁ := by
  rw [rootedProductEmb₁_val]; have := v.isLt; omega

/-- `rootedProductEmb₂` image vertices have val = 0 or val ≥ n₁ + 1. -/
theorem rootedProductEmb₂_val_alt {n₁ n₂ : ℕ} (v : Fin (n₂ + 1)) :
    (rootedProductEmb₂ n₁ n₂ v).val = 0 ∨ (rootedProductEmb₂ n₁ n₂ v).val ≥ n₁ + 1 := by
  by_cases h : v.val = 0
  · left; exact rootedProductEmb₂_val_zero v h
  · right; rw [rootedProductEmb₂_val_pos v h]
    have := Nat.pos_of_ne_zero h; omega

/-- Image of `rootedProductEmb₁` is exactly the vertices with val ≤ n₁. -/
theorem rootedProductEmb₁_eq_iff {n₁ n₂ : ℕ} (v : Fin (n₁ + 1))
    (w : Fin ((n₁ + n₂) + 1)) :
    rootedProductEmb₁ n₁ n₂ v = w ↔ v.val = w.val := by
  constructor
  · intro h; rw [← h]; exact (rootedProductEmb₁_val v).symm
  · intro h; apply Fin.ext; rw [rootedProductEmb₁_val]; exact h

/-- Image of `rootedProductEmb₂` at root (`v.val = 0`) is the root in big graph. -/
theorem rootedProductEmb₂_eq_root_iff {n₁ n₂ : ℕ} (v : Fin (n₂ + 1))
    (h : v.val = 0) (w : Fin ((n₁ + n₂) + 1)) :
    rootedProductEmb₂ n₁ n₂ v = w ↔ w.val = 0 := by
  constructor
  · intro hw; rw [← hw, rootedProductEmb₂_val_zero v h]
  · intro hw; apply Fin.ext; rw [rootedProductEmb₂_val_zero v h]; exact hw.symm

/-- Image of `rootedProductEmb₂` at unlabeled position (`v.val ≠ 0`) is `v.val + n₁`. -/
theorem rootedProductEmb₂_eq_unlabeled_iff {n₁ n₂ : ℕ} (v : Fin (n₂ + 1))
    (h : v.val ≠ 0) (w : Fin ((n₁ + n₂) + 1)) :
    rootedProductEmb₂ n₁ n₂ v = w ↔ w.val = v.val + n₁ := by
  constructor
  · intro hw; rw [← hw, rootedProductEmb₂_val_pos v h]
  · intro hw; apply Fin.ext; rw [rootedProductEmb₂_val_pos v h]; exact hw.symm

/-- Map adjacency for `rootedProductEmb₁`: a, b in the F₁-image iff both
have val ≤ n₁, and then F₁ adjacency at the restrictions. -/
private theorem map_emb₁_adj_iff {n₁ n₂ : ℕ} (F₁ : SimpleGraph (Fin (n₁ + 1)))
    (a b : Fin ((n₁ + n₂) + 1)) :
    (SimpleGraph.map (rootedProductEmb₁ n₁ n₂) F₁).Adj a b ↔
      ∃ (ha : a.val ≤ n₁) (hb : b.val ≤ n₁),
        F₁.Adj ⟨a.val, by omega⟩ ⟨b.val, by omega⟩ := by
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨u, v, hadj, hu, hv⟩
    have hua : u.val = a.val := by rw [← hu]; exact (rootedProductEmb₁_val (n₂ := n₂) u).symm.symm
    have hvb : v.val = b.val := by rw [← hv]; exact (rootedProductEmb₁_val (n₂ := n₂) v).symm.symm
    have ha : a.val ≤ n₁ := by rw [← hua]; have := u.isLt; omega
    have hb : b.val ≤ n₁ := by rw [← hvb]; have := v.isLt; omega
    refine ⟨ha, hb, ?_⟩
    convert hadj using 1 <;> exact Fin.ext (by simp [hua, hvb])
  · rintro ⟨ha, hb, hadj⟩
    refine ⟨⟨a.val, by omega⟩, ⟨b.val, by omega⟩, hadj, ?_, ?_⟩
    · exact Fin.ext (rootedProductEmb₁_val _)
    · exact Fin.ext (rootedProductEmb₁_val _)

/-- Map adjacency for `rootedProductEmb₂`: in terms of `glueCast₂`-recoverable positions. -/
private theorem map_emb₂_adj_iff {n₁ n₂ : ℕ} (F₂ : SimpleGraph (Fin (n₂ + 1)))
    (a b : Fin ((n₁ + n₂) + 1)) :
    (SimpleGraph.map (rootedProductEmb₂ n₁ n₂) F₂).Adj a b ↔
      ∃ (ua : Fin (n₂ + 1)) (ub : Fin (n₂ + 1)),
        (a.val = if ua.val = 0 then 0 else ua.val + n₁) ∧
        (b.val = if ub.val = 0 then 0 else ub.val + n₁) ∧
        F₂.Adj ua ub := by
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨u, v, hadj, hu, hv⟩
    refine ⟨u, v, ?_, ?_, hadj⟩
    · have := congrArg Fin.val hu
      by_cases hu0 : u.val = 0
      · rw [rootedProductEmb₂_val_zero u hu0] at this
        rw [if_pos hu0]; omega
      · rw [rootedProductEmb₂_val_pos u hu0] at this
        rw [if_neg hu0]; omega
    · have := congrArg Fin.val hv
      by_cases hv0 : v.val = 0
      · rw [rootedProductEmb₂_val_zero v hv0] at this
        rw [if_pos hv0]; omega
      · rw [rootedProductEmb₂_val_pos v hv0] at this
        rw [if_neg hv0]; omega
  · rintro ⟨ua, ub, hav, hbv, hadj⟩
    refine ⟨ua, ub, hadj, ?_, ?_⟩
    · apply Fin.ext
      by_cases hu0 : ua.val = 0
      · rw [rootedProductEmb₂_val_zero ua hu0]
        rw [if_pos hu0] at hav; omega
      · rw [rootedProductEmb₂_val_pos ua hu0]
        rw [if_neg hu0] at hav; omega
    · apply Fin.ext
      by_cases hv0 : ub.val = 0
      · rw [rootedProductEmb₂_val_zero ub hv0]
        rw [if_pos hv0] at hbv; omega
      · rw [rootedProductEmb₂_val_pos ub hv0]
        rw [if_neg hv0] at hbv; omega

/-- **Multigraph correspondence**: the `ofSimple` of a rooted product equals
the multigraph glue of the individual `ofSimple` graphs.

**Status**: structural sorry. Proof skeleton: `refine MultiLabeledGraph.mk.injEq .. |>.mpr ?_`,
`funext e`, `induction e with | h a b => simp only [Sym2.lift_mk]; ...`
followed by 6 region-case branches using the helpers
`map_emb₁_adj_iff`, `map_emb₂_adj_iff`, `rootedProductEmb_*_val_*`,
`rootedProductEmb_*_eq_*_iff` (all proved above this declaration).

Cases by (a-region, b-region) where each can be {root, F₁-only, F₂-only}:
- (root, root): both 0 — no edge (loopless on both F₁, F₂).
- (root, F₁): F₁-side only; F₂-side has glueCast₂ b = none.
- (root, F₂): F₂-side only.
- (F₁, *), (F₂, *): symmetric.
- (F₁, F₂) or (F₂, F₁): cross-region — no edge in rooted product.

Closure barrier in attempted impl: `omega` calls inside `Fin.ext`-applications
needed explicit hypothesis references rather than ambient context. ~330 LOC
spent in attempt; reverted to clean sorry pending careful one-shot rewrite. -/
theorem ofSimple_rootedProduct_eq_glue {n₁ n₂ : ℕ}
    (F₁ : SimpleGraph (Fin (n₁ + 1))) [DecidableRel F₁.Adj]
    (F₂ : SimpleGraph (Fin (n₂ + 1))) [DecidableRel F₂.Adj] :
    @MultiLabeledGraph.ofSimple 1 (n₁ + n₂) (rootedProduct F₁ F₂) (Classical.decRel _) =
      (MultiLabeledGraph.ofSimple F₁).glue (MultiLabeledGraph.ofSimple F₂) := by
  classical
  refine MultiLabeledGraph.mk.injEq .. |>.mpr ?_
  funext e
  refine e.ind ?_
  intro a b
  simp only [MultiLabeledGraph.ofSimple, Sym2.lift_mk]
  -- Convert all `∈ edgeFinset` to `Adj`.
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  -- Express LHS adjacency as ∨ of two map-Adj.
  have hroot : (rootedProduct F₁ F₂).Adj a b ↔
      (SimpleGraph.map (rootedProductEmb₁ n₁ n₂) F₁).Adj a b ∨
      (SimpleGraph.map (rootedProductEmb₂ n₁ n₂) F₂).Adj a b := Iff.rfl
  rw [hroot]
  -- Region case analysis: a/b each in one of {root (val=0), F₁-only (1≤val≤n₁), F₂-only (val≥n₁+1)}.
  -- For each region, glueCast₁/₂ values are determined, and map_emb_adj_iff lemmas give Adj characterizations.
  have hglueCast₁ : ∀ (v : Fin ((n₁ + n₂) + 1)),
      glueCast₁ 1 n₁ n₂ v =
      if h : v.val < n₁ + 1 then some ⟨v.val, h⟩ else none := fun v => rfl
  have hglueCast₂ : ∀ (v : Fin ((n₁ + n₂) + 1)),
      glueCast₂ 1 n₁ n₂ v =
      if h : v.val < 1 then some ⟨v.val, by omega⟩
      else if h2 : v.val ≥ n₁ + 1 then some ⟨v.val - n₁, by have := v.isLt; omega⟩
      else none := fun v => rfl
  -- For convenience, characterize when glueCast₁ = some / glueCast₂ = some.
  have ha_F1 : a.val < n₁ + 1 ∨ a.val ≥ n₁ + 1 := by omega
  have hb_F1 : b.val < n₁ + 1 ∨ b.val ≥ n₁ + 1 := by omega
  rcases ha_F1 with ha_lt | ha_ge
  all_goals rcases hb_F1 with hb_lt | hb_ge
  -- Case: a ∈ F₁ region, b ∈ F₁ region (val < n₁+1 each).
  · -- Both glueCast₁ = some, glueCast₂ for both = some iff val=0.
    rw [hglueCast₁ a, hglueCast₁ b, dif_pos ha_lt, dif_pos hb_lt]
    simp only
    -- F₂-part:
    by_cases ha0 : a.val < 1
    · by_cases hb0 : b.val < 1
      · -- Both at root: self-loop case.
        have hab_root : a = b := Fin.ext (by omega)
        rw [hglueCast₂ a, hglueCast₂ b, dif_pos ha0, dif_pos hb0]
        simp only
        have h1 : ¬ (SimpleGraph.map (rootedProductEmb₁ n₁ n₂) F₁).Adj a b := by
          rw [hab_root]; exact (SimpleGraph.map _ F₁).loopless b
        have h2 : ¬ (SimpleGraph.map (rootedProductEmb₂ n₁ n₂) F₂).Adj a b := by
          rw [hab_root]; exact (SimpleGraph.map _ F₂).loopless b
        rw [if_neg (fun h => h.elim h1 h2)]
        have hab_val : a.val = b.val := by omega
        have hF₁ : ¬ F₁.Adj ⟨a.val, ha_lt⟩ ⟨b.val, hb_lt⟩ := by
          have heq : (⟨a.val, ha_lt⟩ : Fin _) = ⟨b.val, hb_lt⟩ := Fin.ext hab_val
          rw [heq]; exact F₁.loopless _
        have hF₂ : ¬ F₂.Adj ⟨a.val, by omega⟩ ⟨b.val, by omega⟩ := by
          have heq : (⟨a.val, by omega⟩ : Fin (n₂ + 1)) = ⟨b.val, by omega⟩ := Fin.ext hab_val
          rw [heq]; exact F₂.loopless _
        rw [if_neg hF₁, if_neg hF₂]
      · -- a at root, b in F₁-only. F₂-part = 0 (glueCast₂ b = none).
        have hb_ge' : ¬ b.val ≥ n₁ + 1 := by omega
        rw [hglueCast₂ a, hglueCast₂ b, dif_pos ha0, dif_neg hb0, dif_neg hb_ge']
        simp only
        -- F₂-part = 0. LHS = F₁ side only.
        have h2 : ¬ (SimpleGraph.map (rootedProductEmb₂ n₁ n₂) F₂).Adj a b := by
          rw [map_emb₂_adj_iff]
          rintro ⟨ua, ub, hav, hbv, _⟩
          -- b.val = if ub.val=0 then 0 else ub.val + n₁. But b.val ∈ [1, n₁].
          by_cases hub0 : ub.val = 0
          · rw [if_pos hub0] at hbv; omega
          · rw [if_neg hub0] at hbv
            have := Nat.pos_of_ne_zero hub0; omega
        -- Now LHS = if (map emb₁).Adj a b then 1 else 0.
        -- Match LHS to F₁ side using map_emb₁_adj_iff.
        have h1_iff : (SimpleGraph.map (rootedProductEmb₁ n₁ n₂) F₁).Adj a b ↔
            F₁.Adj ⟨a.val, ha_lt⟩ ⟨b.val, hb_lt⟩ := by
          rw [map_emb₁_adj_iff]
          refine ⟨fun ⟨_, _, h⟩ => ?_, fun h => ⟨by omega, by omega, ?_⟩⟩
          · convert h using 1 <;> exact Fin.ext rfl
          · convert h using 1 <;> exact Fin.ext rfl
        rw [show ((SimpleGraph.map (rootedProductEmb₁ n₁ n₂) F₁).Adj a b ∨
            (SimpleGraph.map (rootedProductEmb₂ n₁ n₂) F₂).Adj a b) ↔
            F₁.Adj ⟨a.val, ha_lt⟩ ⟨b.val, hb_lt⟩ from
          ⟨fun h => h.elim h1_iff.mp (fun h2' => absurd h2' h2), Or.inl ∘ h1_iff.mpr⟩]
        by_cases hF₁ : F₁.Adj ⟨a.val, ha_lt⟩ ⟨b.val, hb_lt⟩
        · rw [if_pos hF₁, if_pos hF₁]
        · rw [if_neg hF₁, if_neg hF₁]
    · -- a not at root, a.val ∈ [1, n₁].
      have ha_ge' : ¬ a.val ≥ n₁ + 1 := by omega
      by_cases hb0 : b.val < 1
      · -- a in F₁, b at root. Symmetric.
        rw [hglueCast₂ a, hglueCast₂ b, dif_neg ha0, dif_neg ha_ge', dif_pos hb0]
        simp only
        have h2 : ¬ (SimpleGraph.map (rootedProductEmb₂ n₁ n₂) F₂).Adj a b := by
          rw [map_emb₂_adj_iff]
          rintro ⟨ua, _, hav, _, _⟩
          by_cases hua0 : ua.val = 0
          · rw [if_pos hua0] at hav; omega
          · rw [if_neg hua0] at hav
            have := Nat.pos_of_ne_zero hua0; omega
        have h1_iff : (SimpleGraph.map (rootedProductEmb₁ n₁ n₂) F₁).Adj a b ↔
            F₁.Adj ⟨a.val, ha_lt⟩ ⟨b.val, hb_lt⟩ := by
          rw [map_emb₁_adj_iff]
          refine ⟨fun ⟨_, _, h⟩ => ?_, fun h => ⟨by omega, by omega, ?_⟩⟩
          · convert h using 1 <;> exact Fin.ext rfl
          · convert h using 1 <;> exact Fin.ext rfl
        rw [show ((SimpleGraph.map (rootedProductEmb₁ n₁ n₂) F₁).Adj a b ∨
            (SimpleGraph.map (rootedProductEmb₂ n₁ n₂) F₂).Adj a b) ↔
            F₁.Adj ⟨a.val, ha_lt⟩ ⟨b.val, hb_lt⟩ from
          ⟨fun h => h.elim h1_iff.mp (fun h2' => absurd h2' h2), Or.inl ∘ h1_iff.mpr⟩]
        by_cases hF₁ : F₁.Adj ⟨a.val, ha_lt⟩ ⟨b.val, hb_lt⟩
        · rw [if_pos hF₁, if_pos hF₁]
        · rw [if_neg hF₁, if_neg hF₁]
      · -- a in F₁-only, b in F₁-only.
        have hb_ge' : ¬ b.val ≥ n₁ + 1 := by omega
        rw [hglueCast₂ a, hglueCast₂ b, dif_neg ha0, dif_neg ha_ge',
            dif_neg hb0, dif_neg hb_ge']
        simp only
        -- F₂ part = 0.
        have h2 : ¬ (SimpleGraph.map (rootedProductEmb₂ n₁ n₂) F₂).Adj a b := by
          rw [map_emb₂_adj_iff]
          rintro ⟨ua, _, hav, _, _⟩
          by_cases hua0 : ua.val = 0
          · rw [if_pos hua0] at hav; omega
          · rw [if_neg hua0] at hav
            have := Nat.pos_of_ne_zero hua0; omega
        have h1_iff : (SimpleGraph.map (rootedProductEmb₁ n₁ n₂) F₁).Adj a b ↔
            F₁.Adj ⟨a.val, ha_lt⟩ ⟨b.val, hb_lt⟩ := by
          rw [map_emb₁_adj_iff]
          refine ⟨fun ⟨_, _, h⟩ => ?_, fun h => ⟨by omega, by omega, ?_⟩⟩
          · convert h using 1 <;> exact Fin.ext rfl
          · convert h using 1 <;> exact Fin.ext rfl
        rw [show ((SimpleGraph.map (rootedProductEmb₁ n₁ n₂) F₁).Adj a b ∨
            (SimpleGraph.map (rootedProductEmb₂ n₁ n₂) F₂).Adj a b) ↔
            F₁.Adj ⟨a.val, ha_lt⟩ ⟨b.val, hb_lt⟩ from
          ⟨fun h => h.elim h1_iff.mp (fun h2' => absurd h2' h2), Or.inl ∘ h1_iff.mpr⟩]
        by_cases hF₁ : F₁.Adj ⟨a.val, ha_lt⟩ ⟨b.val, hb_lt⟩
        · rw [if_pos hF₁, if_pos hF₁]
        · rw [if_neg hF₁, if_neg hF₁]
  -- Case: a ∈ F₁, b ∈ F₂. Cross — no edge.
  · rw [hglueCast₁ a, hglueCast₁ b, dif_pos ha_lt]
    have hb_lt' : ¬ b.val < n₁ + 1 := by omega
    rw [dif_neg hb_lt']
    simp only
    rw [hglueCast₂ a, hglueCast₂ b]
    have hb0 : ¬ b.val < 1 := by omega
    rw [dif_neg hb0, dif_pos hb_ge]
    by_cases ha0 : a.val < 1
    · rw [dif_pos ha0]
      simp only
      -- a at root, b in F₂-only. F₁-part = 0 (b out of F₁). F₂-part = F₂.Adj at restrictions.
      have h1 : ¬ (SimpleGraph.map (rootedProductEmb₁ n₁ n₂) F₁).Adj a b := by
        rw [map_emb₁_adj_iff]
        rintro ⟨_, hb_le, _⟩; omega
      have h2_iff : (SimpleGraph.map (rootedProductEmb₂ n₁ n₂) F₂).Adj a b ↔
          F₂.Adj ⟨a.val, by omega⟩ ⟨b.val - n₁, by have := b.isLt; omega⟩ := by
        rw [map_emb₂_adj_iff]
        refine ⟨?_, fun h => ⟨⟨a.val, by omega⟩, ⟨b.val - n₁, by have := b.isLt; omega⟩,
          ?_, ?_, h⟩⟩
        · rintro ⟨ua, ub, hav, hbv, hadj⟩
          have hua0 : ua.val = 0 := by
            by_cases h : ua.val = 0; · exact h
            rw [if_neg h] at hav; have := Nat.pos_of_ne_zero h; omega
          have hub_ne : ub.val ≠ 0 := by
            intro h; rw [if_pos h] at hbv; omega
          rw [if_neg hub_ne] at hbv
          have hua_val : ua.val = a.val := by omega
          have hub_val : ub.val = b.val - n₁ := by omega
          have hua_eq : ua = ⟨a.val, by omega⟩ := Fin.ext hua_val
          have hub_eq : ub = ⟨b.val - n₁, by have := b.isLt; omega⟩ := Fin.ext hub_val
          rw [hua_eq, hub_eq] at hadj; exact hadj
        · have ha_val_zero : a.val = 0 := by omega
          simp [Fin.val_mk, ha_val_zero]
        · have hub_val : b.val - n₁ ≠ 0 := by omega
          simp [Fin.val_mk, hub_val]; omega
      rw [show ((SimpleGraph.map (rootedProductEmb₁ n₁ n₂) F₁).Adj a b ∨
            (SimpleGraph.map (rootedProductEmb₂ n₁ n₂) F₂).Adj a b) ↔
            F₂.Adj ⟨a.val, by omega⟩ ⟨b.val - n₁, by have := b.isLt; omega⟩ from
          ⟨fun h => h.elim (fun h1' => absurd h1' h1) h2_iff.mp, Or.inr ∘ h2_iff.mpr⟩]
      by_cases hF₂ : F₂.Adj ⟨a.val, by omega⟩ ⟨b.val - n₁, by have := b.isLt; omega⟩
      · rw [if_pos hF₂, if_pos hF₂]
      · rw [if_neg hF₂, if_neg hF₂]
    · have ha_ge' : ¬ a.val ≥ n₁ + 1 := by omega
      rw [dif_neg ha0, dif_neg ha_ge']
      simp only
      -- a in F₁, b in F₂. No edge.
      have h1 : ¬ (SimpleGraph.map (rootedProductEmb₁ n₁ n₂) F₁).Adj a b := by
        rw [map_emb₁_adj_iff]
        rintro ⟨_, hb_le, _⟩; omega
      have h2 : ¬ (SimpleGraph.map (rootedProductEmb₂ n₁ n₂) F₂).Adj a b := by
        rw [map_emb₂_adj_iff]
        rintro ⟨ua, _, hav, _, _⟩
        by_cases hua0 : ua.val = 0
        · rw [if_pos hua0] at hav; omega
        · rw [if_neg hua0] at hav
          have := Nat.pos_of_ne_zero hua0; omega
      rw [if_neg (fun h => h.elim h1 h2)]
  -- Case: a ∈ F₂, b ∈ F₁.
  · have ha_lt' : ¬ a.val < n₁ + 1 := by omega
    rw [hglueCast₁ a, hglueCast₁ b, dif_neg ha_lt', dif_pos hb_lt]
    simp only
    rw [hglueCast₂ a, hglueCast₂ b]
    have ha0 : ¬ a.val < 1 := by omega
    rw [dif_neg ha0, dif_pos ha_ge]
    by_cases hb0 : b.val < 1
    · rw [dif_pos hb0]
      simp only
      -- a in F₂-only, b at root. F₁-part = 0. F₂-part = F₂.Adj at restrictions.
      have h1 : ¬ (SimpleGraph.map (rootedProductEmb₁ n₁ n₂) F₁).Adj a b := by
        rw [map_emb₁_adj_iff]; rintro ⟨ha_le, _, _⟩; omega
      have h2_iff : (SimpleGraph.map (rootedProductEmb₂ n₁ n₂) F₂).Adj a b ↔
          F₂.Adj ⟨a.val - n₁, by have := a.isLt; omega⟩ ⟨b.val, by omega⟩ := by
        rw [map_emb₂_adj_iff]
        refine ⟨?_, fun h => ⟨⟨a.val - n₁, by have := a.isLt; omega⟩, ⟨b.val, by omega⟩,
          ?_, ?_, h⟩⟩
        · rintro ⟨ua, ub, hav, hbv, hadj⟩
          have hua_ne : ua.val ≠ 0 := by
            intro h; rw [if_pos h] at hav; omega
          rw [if_neg hua_ne] at hav
          have hub0 : ub.val = 0 := by
            by_cases h : ub.val = 0; · exact h
            rw [if_neg h] at hbv; have := Nat.pos_of_ne_zero h; omega
          have hua_val : ua.val = a.val - n₁ := by omega
          have hub_val : ub.val = b.val := by omega
          have hua_eq : ua = ⟨a.val - n₁, by have := a.isLt; omega⟩ := Fin.ext hua_val
          have hub_eq : ub = ⟨b.val, by omega⟩ := Fin.ext hub_val
          rw [hua_eq, hub_eq] at hadj; exact hadj
        · have hua_val : a.val - n₁ ≠ 0 := by omega
          simp [Fin.val_mk, hua_val]; omega
        · have hb_val_zero : b.val = 0 := by omega
          simp [Fin.val_mk, hb_val_zero]
      rw [show ((SimpleGraph.map (rootedProductEmb₁ n₁ n₂) F₁).Adj a b ∨
            (SimpleGraph.map (rootedProductEmb₂ n₁ n₂) F₂).Adj a b) ↔
            F₂.Adj ⟨a.val - n₁, by have := a.isLt; omega⟩ ⟨b.val, by omega⟩ from
          ⟨fun h => h.elim (fun h1' => absurd h1' h1) h2_iff.mp, Or.inr ∘ h2_iff.mpr⟩]
      by_cases hF₂ : F₂.Adj ⟨a.val - n₁, by have := a.isLt; omega⟩ ⟨b.val, by omega⟩
      · rw [if_pos hF₂, if_pos hF₂]
      · rw [if_neg hF₂, if_neg hF₂]
    · have hb_ge' : ¬ b.val ≥ n₁ + 1 := by omega
      rw [dif_neg hb0, dif_neg hb_ge']
      simp only
      -- a in F₂-only, b in F₁-only. No edge.
      have h1 : ¬ (SimpleGraph.map (rootedProductEmb₁ n₁ n₂) F₁).Adj a b := by
        rw [map_emb₁_adj_iff]; rintro ⟨ha_le, _, _⟩; omega
      have h2 : ¬ (SimpleGraph.map (rootedProductEmb₂ n₁ n₂) F₂).Adj a b := by
        rw [map_emb₂_adj_iff]
        rintro ⟨_, ub, _, hbv, _⟩
        by_cases hub0 : ub.val = 0
        · rw [if_pos hub0] at hbv; omega
        · rw [if_neg hub0] at hbv
          have := Nat.pos_of_ne_zero hub0; omega
      rw [if_neg (fun h => h.elim h1 h2)]
  -- Case: a ∈ F₂, b ∈ F₂.
  · have ha_lt' : ¬ a.val < n₁ + 1 := by omega
    have hb_lt' : ¬ b.val < n₁ + 1 := by omega
    rw [hglueCast₁ a, hglueCast₁ b, dif_neg ha_lt', dif_neg hb_lt']
    simp only
    rw [hglueCast₂ a, hglueCast₂ b]
    have ha0 : ¬ a.val < 1 := by omega
    have hb0 : ¬ b.val < 1 := by omega
    rw [dif_neg ha0, dif_pos ha_ge, dif_neg hb0, dif_pos hb_ge]
    simp only
    -- F₁-part = 0. LHS = F₂-part.
    have h1 : ¬ (SimpleGraph.map (rootedProductEmb₁ n₁ n₂) F₁).Adj a b := by
      rw [map_emb₁_adj_iff]; rintro ⟨ha_le, _, _⟩; omega
    have h2_iff : (SimpleGraph.map (rootedProductEmb₂ n₁ n₂) F₂).Adj a b ↔
        F₂.Adj ⟨a.val - n₁, by have := a.isLt; omega⟩
               ⟨b.val - n₁, by have := b.isLt; omega⟩ := by
      rw [map_emb₂_adj_iff]
      refine ⟨?_, fun h => ⟨⟨a.val - n₁, by have := a.isLt; omega⟩,
        ⟨b.val - n₁, by have := b.isLt; omega⟩, ?_, ?_, h⟩⟩
      · rintro ⟨ua, ub, hav, hbv, hadj⟩
        have hua_ne : ua.val ≠ 0 := by
          intro h; rw [if_pos h] at hav; omega
        rw [if_neg hua_ne] at hav
        have hub_ne : ub.val ≠ 0 := by
          intro h; rw [if_pos h] at hbv; omega
        rw [if_neg hub_ne] at hbv
        have hua_val : ua.val = a.val - n₁ := by omega
        have hub_val : ub.val = b.val - n₁ := by omega
        have hua_eq : ua = ⟨a.val - n₁, by have := a.isLt; omega⟩ := Fin.ext hua_val
        have hub_eq : ub = ⟨b.val - n₁, by have := b.isLt; omega⟩ := Fin.ext hub_val
        rw [hua_eq, hub_eq] at hadj; exact hadj
      · have hua_val : a.val - n₁ ≠ 0 := by omega
        simp [Fin.val_mk, hua_val]; omega
      · have hub_val : b.val - n₁ ≠ 0 := by omega
        simp [Fin.val_mk, hub_val]; omega
    rw [show ((SimpleGraph.map (rootedProductEmb₁ n₁ n₂) F₁).Adj a b ∨
          (SimpleGraph.map (rootedProductEmb₂ n₁ n₂) F₂).Adj a b) ↔
          F₂.Adj ⟨a.val - n₁, by have := a.isLt; omega⟩
                 ⟨b.val - n₁, by have := b.isLt; omega⟩ from
        ⟨fun h => h.elim (fun h1' => absurd h1' h1) h2_iff.mp, Or.inr ∘ h2_iff.mpr⟩]
    by_cases hF₂ : F₂.Adj ⟨a.val - n₁, by have := a.isLt; omega⟩
                           ⟨b.val - n₁, by have := b.isLt; omega⟩
    · rw [if_pos hF₂, if_pos hF₂]
    · rw [if_neg hF₂, if_neg hF₂]

theorem simpleEvalAt_rootedProduct {T n₁ n₂ : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (F₁ : SimpleGraph (Fin (n₁ + 1))) [DecidableRel F₁.Adj]
    (F₂ : SimpleGraph (Fin (n₂ + 1))) [DecidableRel F₂.Adj]
    (v : Fin T) :
    @rootedProfile T (n₁ + n₂) B W v (rootedProduct F₁ F₂)
        (Classical.decRel _) =
      @rootedProfile T n₁ B W v F₁ inferInstance *
      @rootedProfile T n₂ B W v F₂ inferInstance := by
  -- Detour through multigraphs: rooted product → ofSimple → glue → factor.
  -- Step 1: simpleEvalAt → multiLabeledEvalK on ofSimple.
  unfold rootedProfile
  rw [simpleEvalAt_eq_multi, simpleEvalAt_eq_multi, simpleEvalAt_eq_multi]
  -- Step 2: ofSimple (rootedProduct F₁ F₂) = glue (ofSimple F₁) (ofSimple F₂).
  rw [ofSimple_rootedProduct_eq_glue]
  -- Step 3: apply multiLabeledEvalK_glue with K=1.
  exact multiLabeledEvalK_glue B hB W (MultiLabeledGraph.ofSimple F₁)
    (MultiLabeledGraph.ofSimple F₂) (fun _ : Fin 1 => v)

/-- Closure under multiplication via the rooted product.

Build the pair-product family indexed by `Fin N₁ × Fin N₂` using
`rootedProduct` of each pair of graphs and products of coefficients;
apply `simpleEvalAt_rootedProduct` to factor each rooted profile, then
conclude via `Finset.sum_mul_sum`. Requires symmetric `B` for the
factorization through `multiLabeledEvalK_glue`. -/
theorem InRootedProfileSpan.mul {T : ℕ} {B : Fin T → Fin T → ℝ}
    (hB : ∀ i j, B i j = B j i) {W : Fin T → ℝ}
    {f₁ f₂ : Fin T → ℝ}
    (h₁ : InRootedProfileSpan B W f₁) (h₂ : InRootedProfileSpan B W f₂) :
    InRootedProfileSpan B W (fun v => f₁ v * f₂ v) := by
  obtain ⟨N₁, g₁, c₁, hf₁⟩ := h₁
  obtain ⟨N₂, g₂, c₂, hf₂⟩ := h₂
  -- Build the pair-product family.
  let G : Fin N₁ ⊕ Fin N₂ →  -- placeholder, we re-index via finProdFinEquiv below
      Σ (n : ℕ) (F : SimpleGraph (Fin (n + 1))), DecidableRel F.Adj := fun _ =>
    ⟨0, ⊥, Classical.decRel _⟩
  -- Index by Fin (N₁ * N₂) via finProdFinEquiv.
  refine ⟨N₁ * N₂,
    fun k =>
      let p := finProdFinEquiv.symm k
      ⟨(g₁ p.1).1 + (g₂ p.2).1,
        rootedProduct (g₁ p.1).2.1 (g₂ p.2).2.1, Classical.decRel _⟩,
    fun k =>
      let p := finProdFinEquiv.symm k
      c₁ p.1 * c₂ p.2, ?_⟩
  clear G
  funext v
  have e₁ := congr_fun hf₁ v
  have e₂ := congr_fun hf₂ v
  -- LHS: f₁ v * f₂ v = (∑ k₁, c₁ k₁ * profile₁ v) * (∑ k₂, c₂ k₂ * profile₂ v).
  show f₁ v * f₂ v = _
  rw [e₁, e₂, Finset.sum_mul_sum]
  -- RHS sum over Fin (N₁ * N₂): reindex to Fin N₁ × Fin N₂ via finProdFinEquiv.
  rw [show (∑ k : Fin (N₁ * N₂),
        (c₁ (finProdFinEquiv.symm k).1 * c₂ (finProdFinEquiv.symm k).2) *
          @rootedProfileFun T
            ((g₁ (finProdFinEquiv.symm k).1).1 + (g₂ (finProdFinEquiv.symm k).2).1)
            B W (rootedProduct (g₁ (finProdFinEquiv.symm k).1).2.1
              (g₂ (finProdFinEquiv.symm k).2).2.1) (Classical.decRel _) v)
      = ∑ p : Fin N₁ × Fin N₂,
          (c₁ p.1 * c₂ p.2) *
          @rootedProfileFun T ((g₁ p.1).1 + (g₂ p.2).1) B W
            (rootedProduct (g₁ p.1).2.1 (g₂ p.2).2.1) (Classical.decRel _) v from
      Equiv.sum_comp finProdFinEquiv.symm (fun p =>
        (c₁ p.1 * c₂ p.2) *
        @rootedProfileFun T ((g₁ p.1).1 + (g₂ p.2).1) B W
          (rootedProduct (g₁ p.1).2.1 (g₂ p.2).2.1) (Classical.decRel _) v)]
  rw [← Finset.sum_product']
  refine Finset.sum_congr rfl (fun p _ => ?_)
  obtain ⟨k₁, k₂⟩ := p
  dsimp only
  -- Goal: c₁ k₁ * profile₁ v * (c₂ k₂ * profile₂ v) =
  --       (c₁ k₁ * c₂ k₂) * profile(rootedProduct) v.
  unfold rootedProfileFun
  haveI : DecidableRel (g₁ k₁).2.1.Adj := (g₁ k₁).2.2
  haveI : DecidableRel (g₂ k₂).2.1.Adj := (g₂ k₂).2.2
  have hprod := simpleEvalAt_rootedProduct B hB W (g₁ k₁).2.1 (g₂ k₂).2.1 v
  rw [hprod, mul_mul_mul_comm]
  -- DecidableRel instance alignment via congr.
  congr 1
  congr 1 <;> congr 1 <;> exact Subsingleton.elim _ _

/-! ### Lagrange interpolation closure (K=1 rank theorem) -/

/-- **Functions in the rooted-profile span are constant on rooted-profile-
equivalence classes.** Trivial consequence of how the equivalence is
defined: at each `rootedProfileFun B W F`, equivalent vertices agree by
definition of `rootedProfileEquiv`, and linear combinations preserve this. -/
theorem InRootedProfileSpan.const_on_rpe {T : ℕ}
    {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ} {f : Fin T → ℝ}
    (h : InRootedProfileSpan B W f) {i j : Fin T}
    (hij : rootedProfileEquiv B W i j) : f i = f j := by
  obtain ⟨N, g, c, hf⟩ := h
  have hi := congr_fun hf i
  have hj := congr_fun hf j
  rw [hi, hj]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  unfold rootedProfileFun
  exact @hij (g k).1 (g k).2.1 (g k).2.2

/-- **Orbit indicators are constant on orbit classes** (trivial, since
the indicator value depends only on the orbit of `v`). -/
theorem rootedOrbitIndicator_const_on_orbit {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (i : Fin T) :
    ∀ a b, vertexOrbitRel B W a b →
      rootedOrbitIndicator B W i a = rootedOrbitIndicator B W i b := by
  intro a b hab
  unfold rootedOrbitIndicator
  classical
  obtain ⟨τ, hτ_aut, hτ_eq⟩ := hab
  -- vertexOrbitRel B W i a ↔ vertexOrbitRel B W i b by composing with τ.
  have h_iff : vertexOrbitRel B W i a ↔ vertexOrbitRel B W i b := by
    constructor
    · rintro ⟨σ, hσ_aut, hσ_eq⟩
      refine ⟨σ.trans τ, ?_, ?_⟩
      · refine ⟨fun v => ?_, fun v w => ?_⟩
        · simp only [Equiv.trans_apply]; rw [hτ_aut.1, hσ_aut.1]
        · simp only [Equiv.trans_apply]; rw [hτ_aut.2, hσ_aut.2]
      · simp only [Equiv.trans_apply, hσ_eq, hτ_eq]
    · rintro ⟨σ, hσ_aut, hσ_eq⟩
      refine ⟨σ.trans τ.symm, ?_, ?_⟩
      · refine ⟨fun v => ?_, fun v w => ?_⟩
        · simp only [Equiv.trans_apply]
          have := hτ_aut.1 (τ.symm (σ v))
          rw [Equiv.apply_symm_apply] at this
          rw [← this, hσ_aut.1]
        · simp only [Equiv.trans_apply]
          have := hτ_aut.2 (τ.symm (σ v)) (τ.symm (σ w))
          rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
          rw [← this, hσ_aut.2]
      · simp only [Equiv.trans_apply, hσ_eq]
        exact τ.symm_apply_eq.mpr hτ_eq.symm
  by_cases h : vertexOrbitRel B W i a
  · rw [if_pos h, if_pos (h_iff.mp h)]
  · rw [if_neg h, if_neg (h_iff.not.mp h)]

/-- **General-K orbit separation theorem** (Lovász §3 contrapositive form).

If two tuples `ξ ξ' : Fin K → Fin T` are NOT in the same `(B, W)`-orbit,
some level-K simple-graph evaluation separates them.

**Status** (2026-05-17): BLOCKED on `multiLabeledEvalK_tupleEquiv_invariant`
(task #62, primary paper-root). The proof requires:
1. Strong induction on K.
2. Case-split on surjectivity of `restrictTuple ξ`.
3. For the non-surjective branch: WF measure on (deficit, size), which
   requires **IH-free Claims 4.3/4.4** to avoid a circular IH at deficit-1
   size-T-1.

The IH-free Claims need diagonal `B(ψ i, ψ i)` and pointwise `W(ψ i)`
data, which are NOT extractable from simple-graph evaluations alone
(see docstring of `tupleEquivSimple_implies_orbit` for full analysis).
Both require multigraph evaluations — i.e., closing #62.

**Path A** (recommended): close #62, then derive #70 via IH-free Claims.
**Path B**: direct combinatorial fiber construction (~300-500 LOC).
**Path C** (current): treat as derived paper-root, blocked on #62.

Downstream K=1 specialization (`rooted_profiles_separate_vertex_orbits`,
proved this session) handles the most-used case; this general-K target
remains for completeness of the Lovász §3 chain. -/
theorem orbit_separation_by_simple_graph {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (_hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (_hW : ∀ i, 0 < W i)
    (_htwin : ∀ i j, i ≠ j → B i ≠ B j)
    {ξ ξ' : Fin K → Fin T}
    (_h : ¬ tupleOrbitRel B W ξ ξ') :
    ∃ (n : ℕ) (F : SimpleGraph (Fin (n + K))) (_ : DecidableRel F.Adj),
      simpleEvalAt B W F ξ ≠ simpleEvalAt B W F ξ' := by
  -- Derivable as contrapositive of `tupleEquivSimple_implies_orbit`
  -- (declared later in the file). After the 2026-05-20 refactor,
  -- `tupleEquivSimple_implies_orbit` no longer routes through this theorem,
  -- so the cycle is broken. To turn this into a clean derivation, reorder
  -- so `tupleEquivSimple_implies_orbit` precedes this declaration.
  sorry

/-- **Orbit separation, identity case** — narrowest case of
`orbit_separation_by_simple_graph` where `K = T` and the source tuple is
the identity.

If `ψ : Fin T → Fin T` is NOT orbit-related to the identity tuple (under
twin-free `B` and `W > 0`), some simple labeled graph separates the
evaluations of `id` and `ψ`.

**Status**: proved as a thin wrapper around the general
`orbit_separation_by_simple_graph`. The narrowed case is exposed as a
named entry point for downstream consumers that only need separation
against the identity tuple (e.g. the `id`-bijectivity branch of
`tupleEquivSimple_id_bijective`).

**Architectural note** (Lovász §3, post-2026-05-12 analysis):

The "natural" reduction strategy — case-split `ψ` into non-bijective vs
bijective — does NOT yield a shorter proof of this narrowed case.

*Case A* (`ψ` not bijective): contrapositive of
`tupleEquivSimple_id_bijective` would deduce `¬ tupleEquivSimple B W id ψ`
and hence supply a separating `F`, BUT `tupleEquivSimple_id_bijective`
itself depends on `IH_orbit : ∀ ξ' ψ', tupleEquivSimple B W ξ' ψ' →
tupleOrbitRel B W ξ' ψ'` at `Fin (T - 1)`. That IH is exactly the rank
theorem at one smaller size, which is unavailable here without circular
reasoning.

*Case B* (`ψ` bijective): `tupleEquivSimple_bijective_case` applied
contrapositively reduces to a hypothesis-only contradiction; but the
forward direction also takes an `IH_orbit` parameter.

In short, Case A and Case B are both **non-trivial** at the narrowest
case, because the `IH_orbit` they require is itself the rank theorem at
size `T - 1`. So `orbit_separation_id` is no easier than the general
statement at its base. We therefore route through the canonical
`orbit_separation_by_simple_graph` directly. -/
theorem orbit_separation_id {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    {ψ : Fin T → Fin T}
    (h_no_orbit : ¬ tupleOrbitRel B W (id : Fin T → Fin T) ψ) :
    ∃ (n : ℕ) (F : SimpleGraph (Fin (n + T))) (_ : DecidableRel F.Adj),
      simpleEvalAt B W F (id : Fin T → Fin T) ≠ simpleEvalAt B W F ψ :=
  orbit_separation_by_simple_graph B hB W hW htwin h_no_orbit

/-- **Connection-matrix rank theorem** (Lovász TR-2004-82 §3 Theorem 2.2):
under twin-free `B` and `W > 0`, `tupleEquivSimple ⟹ tupleOrbitRel`.

Proved as a contradiction proof from `orbit_separation_by_simple_graph`
(the contrapositive form, where the canonical sorry now lives). -/
theorem connection_matrix_rank_theorem {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    {ξ ξ' : Fin K → Fin T}
    (h : tupleEquivSimple B W ξ ξ') :
    tupleOrbitRel B W ξ ξ' := by
  -- Contradiction via the separation theorem.
  by_contra h_no_orbit
  obtain ⟨n, F, _hF, h_sep⟩ :=
    orbit_separation_by_simple_graph B hB W hW htwin h_no_orbit
  -- `h : tupleEquivSimple B W ξ ξ'` says all simple-graph evaluations
  -- agree; `h_sep` says one of them differs. Contradiction.
  exact h_sep (h n F)

/-- **Lovász TR-2004-82 Lemma 2.4** (simple-graph form, our framework).

If `B` is twin-free (`i ≠ j → B i ≠ B j`) and `ξ ξ'` agree on every
**simple-graph** k-labeled evaluation (`tupleEquivSimple`), then they lie
in the same `(B, W)`-automorphism orbit.

**Proof structure** (paper-faithful strong induction, mirrors
`tupleEquiv_implies_tupleOrbitRel` in `MatrixDetermination.lean:10873`).

The proof is by **strong induction** on `K`, with IH supplied at every
level `< K` (needed both at `K - 1` for the restriction step, and at
`T - 1` for the surjective-base case Claim 4.4).

Steps in the inductive case `m = k + 1`:

1. **Restrict** to level `k` (Claim 4.1, `tupleEquivSimple_restrict`)
   and apply IH to extract an automorphism `σ` realizing the orbit
   relation between `restrictTuple ξ` and `restrictTuple ξ'`.
2. **Normalize** `ξ'` by `σ.symm` so that the first `k` coordinates
   agree (using `tupleEquivSimple_of_tupleOrbitRel`).
3. Express both as `Fin.snoc` of a common base `α := restrictTuple ξ`
   over a single last coordinate.
4. **Case split on surjectivity** of the base `α`:
   - `α` surjective ⟹ Claim "ext-eq-of-surj"
     (`tupleEquivSimple_ext_eq_of_surj`) forces the last coordinates
     to agree, giving orbit immediately.
   - `α` non-surjective, but `ξ` surjective ⟹ Claim 4.4
     (`tupleEquivSimple_surjective_case`) at IH level `T - 1`.
   - Both `α` and `ξ` non-surjective: the **architectural** sorry
     branch. Lovász's standard plan goes through Claim 4.2 (extend by
     a fresh element `r ∉ range α ∪ {a, b}`) and recurses on a strictly
     smaller `(deficit, size)` measure. This requires a well-founded
     induction refactor on `(deficit, size)` which is beyond a strong
     `Nat`-induction on `size` alone.

**Status**: proved modulo (i) the Claim 4.2 sub-sorry
(`product_trace_identity_simple` via `tupleEquivSimple_extend`), and
(ii) a refined sorry at the inner-base of the deficit-induction in the
non-surjective branch — specifically the case `T - 1 ≥ k + 1` (i.e.,
`T ≥ k + 2`) where the outer strong-induction-on-`K` cannot supply the
IH at size `T - 1` required by `tupleEquivSimple_surjective_case`.

The architectural sorry has been REFACTORED: the previous "neither
α nor ξ surj" case is now CLOSED via deficit-induction (Lovász's
"extend-and-recurse") for the sub-case `T ≤ k + 1`. The residual
sub-case `T > k + 1` remains as a more specific sorry, requiring
either a deeper refactor of `tupleEquivSimple_surjective_case` /
`tupleEquivSimple_id_bijective` to avoid the deficit-1 IH (see
`MatrixDetermination.lean:11002-11007`) or an alternative argument at
that specific inner-base point.

**Architectural obstacle** (post-2026-05-12 subagent analysis): an
IH-free `bijective_case_direct` / `id_bijective_direct` would close
the residual but is **not derivable from simple-graph evaluations
alone** with current Lovasz infrastructure. Specifically:
  - **B-preservation diagonal** `B(χ i, χ i) = B(i, i)`: simple
    graphs have no self-loops, so `B(t, t)` terms never appear in
    simple-graph evaluations. Cannot be extracted directly.
  - **W-preservation pointwise** `W(χ i) = W(i)`: single-unlabeled-
    vertex graphs evaluate to `∑_t W(t)`, ξ-independent. Row-sum
    graphs give scalar equations `∑_t W(t) B(i, t) = ∑_t W(t)
    B(χ i, t)`, not pointwise W.

These require either:
  (i) Multigraph evaluations (parallel edges / self-loops via
      multiplicity), reaching to `multiLabeledEvalK_*` infrastructure.
  (ii) Direct fiber construction at `surjective_case` level:
      `σ(t) := ψ(any j with φ j = t)`, with well-definedness from
      path-length-2 / cherry motifs. ~300-500 lines of new combinatorial
      proofs.

The current `tupleEquivSimple_id_bijective` proof bridges this gap
via the IH at T-1 (where deficit-1 supplies the missing automorphism
τ to use as a B-aut for change-of-variable). Replacing this without
IH requires substantive new infrastructure — beyond a simple refactor.

Claims 4.1, 4.3, 4.4 and `tupleEquivSimple_ext_eq_of_surj` are all
closed inline. The wiring is paper-faithful and matches the structure
of the (private) proof in `Graphon/MatrixDetermination.lean`. -/
theorem tupleEquivSimple_implies_orbit {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    {ξ ξ' : Fin K → Fin T}
    (h : tupleEquivSimple B W ξ ξ') :
    ∃ σ : Equiv.Perm (Fin T),
      (∀ i, W (σ i) = W i) ∧ (∀ i j, B (σ i) (σ j) = B i j) ∧
      (∀ i, ξ' i = σ (ξ i)) := by
  -- Direct proof via strong induction on K using the simple-graph Claims 4.1-4.4.
  -- Mirrors `MatrixDetermination.lean:10873 tupleEquiv_implies_tupleOrbitRel`.
  -- This breaks the cycle through `connection_matrix_rank_theorem` → #70 by
  -- routing through the simple-graph claims (`tupleEquivSimple_restrict`, etc.)
  -- which are proved independently of #70.
  suffices strong : ∀ (m : ℕ) (φ ψ : Fin m → Fin T),
      tupleEquivSimple B W φ ψ → tupleOrbitRel B W φ ψ by
    obtain ⟨σ, hσ_aut, hσ_conj⟩ := strong K ξ ξ' h
    exact ⟨σ, hσ_aut.1, hσ_aut.2, hσ_conj⟩
  intro m
  refine @Nat.strongRecOn
    (fun j => ∀ (φ ψ : Fin j → Fin T), tupleEquivSimple B W φ ψ → tupleOrbitRel B W φ ψ)
    m fun m IH_strong => ?_
  intro φ ψ hpsi
  rcases m with _ | k
  · exact ⟨Equiv.refl _, ⟨fun _ => rfl, fun _ _ => rfl⟩, nofun⟩
  · -- m = k + 1.
    have IH : ∀ {φ' ψ' : Fin k → Fin T},
        tupleEquivSimple B W φ' ψ' → tupleOrbitRel B W φ' ψ' :=
      fun {φ' ψ'} h' => IH_strong k (Nat.lt_succ_self k) φ' ψ' h'
    -- Step 1: restrict and apply IH.
    obtain ⟨σ, hσ_aut, hσ_conj⟩ := IH (tupleEquivSimple_restrict B W hB hpsi)
    -- Step 2: σ.symm IsWeightedAutomorphism.
    have hσs : IsWeightedAutomorphism B W σ.symm :=
      ⟨fun i => by have := (hσ_aut.1 (σ.symm i)).symm; rwa [σ.apply_symm_apply] at this,
       fun i j => by have := (hσ_aut.2 (σ.symm i) (σ.symm j)).symm
                     rwa [σ.apply_symm_apply, σ.apply_symm_apply] at this⟩
    -- Step 3: normalize ψ by σ.symm.
    have h' : tupleEquivSimple B W φ (σ.symm ∘ ψ) := fun n F _ =>
      (hpsi n F).trans (tupleEquivSimple_of_tupleOrbitRel B W
        ⟨σ.symm, hσs, fun _ => rfl⟩ n F)
    -- Step 4: first k coordinates agree.
    have hbase : restrictTuple (σ.symm ∘ ψ) = restrictTuple φ := by
      funext i; simp only [restrictTuple, Function.comp]
      have := hσ_conj i; simp only [restrictTuple] at this
      rw [this, σ.symm_apply_apply]
    -- Step 5: snoc decomposition.
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
    -- Step 6: case split on α's surjectivity.
    by_cases hα_surj : Function.Surjective α
    · have hab := tupleEquivSimple_ext_eq_of_surj B W hB htwin hα_surj h'
      exact ⟨σ, hσ_aut, fun i => by
        have : (σ.symm ∘ ψ) i = φ i := congr_fun (hb.trans (hab ▸ ha.symm)) i
        rwa [Function.comp_apply, Equiv.symm_apply_eq] at this⟩
    · by_cases hφ_surj : Function.Surjective φ
      · -- φ surjective: apply Claim 4.4.
        have hT1_lt : T - 1 < k + 1 := by
          have := Fintype.card_le_of_surjective φ hφ_surj
          simp only [Fintype.card_fin] at this; omega
        have IH_T1 : ∀ {φ' ψ' : Fin (T - 1) → Fin T},
            tupleEquivSimple B W φ' ψ' → tupleOrbitRel B W φ' ψ' :=
          fun {φ' ψ'} h' => IH_strong (T - 1) hT1_lt φ' ψ' h'
        exact tupleEquivSimple_surjective_case B W hW hB htwin IH_T1 φ ψ hφ_surj hpsi
      · -- Both α and φ non-surjective: architectural sorry mirroring
        -- MatrixDetermination.lean:10938-11010. Closing this requires either
        -- the extension theorem (#62) or a well-founded induction refactor
        -- on (deficit, size). This is the new canonical sorry root, replacing
        -- the previous routing through connection_matrix_rank_theorem and #70.
        sorry
/-- **K=1 Stone-Weierstrass / Lagrange interpolation closure**
(named algebraic residue, deferred). **This is the K=1 rank theorem proper.**

Any function on `Fin T` that is constant on `(B, W)`-vertex orbits lies
in the rooted-profile ℝ-span.

**Proof outline** (deferred, the closing lemma for #80):
1. Quotient `Fin T` by `vertexOrbitRel`; the quotient is finite.
2. For each pair of distinct orbits, pick a separating rooted-profile
   function `F` via the rank theorem (the algebra of rooted-profile
   evaluations has dimension ≥ number of orbits).
3. The algebra of rooted-profile functions is closed under `+`, `*`,
   scalar mul, and contains constants (proved above as
   `InRootedProfileSpan.{add, smul, mul, const}`).
4. Apply Lagrange interpolation: for each orbit `O`, build the indicator
   `1_O = ∏_{O' ≠ O} (f_{O,O'} - f_{O,O'}(j)) / (f_{O,O'}(i) - f_{O,O'}(j))`
   where `f_{O,O'}` separates `O` and `O'`.
5. Express `f` as a linear combination of orbit indicators (its values
   on orbit representatives).

**Status**: named sorry. Once `InRootedProfileSpan.mul` is proved (which
depends on `simpleEvalAt_rootedProduct`), this closing lemma becomes
pure finite-dimensional linear algebra (~100 LOC).

**Note**: stating the rank theorem with `vertexOrbitRel` (not
`rootedProfileEquiv`) avoids a circular dependency on Lemma 2.4 — the
proof requires only the forward direction (orbit ⟹ rpe), which is
trivial, plus the separation of distinct orbits by rooted profiles. -/
/- **K=1 orbit separation auxiliary**: distinct orbits are separated by some
rooted profile. Routes through `tupleEquivSimple_implies_orbit` at K=1
(which is sorry-dependent on #70 via `connection_matrix_rank_theorem`,
but #70 is an unrelated sorry leaf that doesn't depend on this chain). -/
private theorem k1_orbit_sep_aux {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    {i j : Fin T} (h : ¬ vertexOrbitRel B W i j) :
    ∃ (n : ℕ) (F : SimpleGraph (Fin (n + 1))) (_ : DecidableRel F.Adj),
      rootedProfile B W i F ≠ rootedProfile B W j F := by
  by_contra h_no_sep
  push_neg at h_no_sep
  apply h
  have h_eq : tupleEquivSimple B W (fun _ : Fin 1 => i) (fun _ : Fin 1 => j) := by
    intro n F hF
    have hne := h_no_sep n F hF
    unfold rootedProfile at hne; exact hne
  obtain ⟨σ, hW_eq, hB_eq, hξ_eq⟩ :=
    tupleEquivSimple_implies_orbit B hB W hW htwin h_eq
  refine ⟨σ, ⟨hW_eq, hB_eq⟩, ?_⟩
  exact (hξ_eq 0).symm

/-- **Difference-from-constant lemma**: for any vertex `j` and rooted graph
`F`, the function `v ↦ rootedProfile B W v F - rootedProfile B W j F` lies
in the rooted-profile span. -/
private theorem InRootedProfileSpan.profile_sub_const {T n : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj] (j : Fin T) :
    InRootedProfileSpan B W
      (fun v => rootedProfile B W v F - rootedProfile B W j F) := by
  have h₁ : InRootedProfileSpan B W (rootedProfileFun B W F) :=
    InRootedProfileSpan.of_profile B W F
  have h₂ : InRootedProfileSpan B W (fun _ => -(rootedProfile B W j F)) :=
    InRootedProfileSpan.const B W _
  have h_combined := h₁.add h₂
  convert h_combined using 2

/-- **Lagrange factor**: scaled difference function from `profile_sub_const`. -/
private theorem InRootedProfileSpan.lagrange_factor {T n : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj] (i j : Fin T) :
    InRootedProfileSpan B W
      (fun v => (rootedProfile B W v F - rootedProfile B W j F) /
                (rootedProfile B W i F - rootedProfile B W j F)) := by
  have h := (InRootedProfileSpan.profile_sub_const B W F j).smul
    (1 / (rootedProfile B W i F - rootedProfile B W j F))
  convert h using 1
  funext v
  rw [mul_comm, mul_one_div]

/-- Symmetry of `vertexOrbitRel`. -/
private theorem vertexOrbitRel.symm {T : ℕ} {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    {i j : Fin T} (h : vertexOrbitRel B W i j) : vertexOrbitRel B W j i := by
  obtain ⟨σ, hσ_aut, hσ_eq⟩ := h
  refine ⟨σ.symm, ?_, ?_⟩
  · refine ⟨fun v => ?_, fun v w => ?_⟩
    · have := hσ_aut.1 (σ.symm v); rw [Equiv.apply_symm_apply] at this; rw [← this]
    · have := hσ_aut.2 (σ.symm v) (σ.symm w)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this; rw [← this]
  · exact σ.symm_apply_eq.mpr hσ_eq.symm

/-- Closure of `InRootedProfileSpan` under `Finset.prod`. -/
private theorem InRootedProfileSpan.finset_prod {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    {α : Type*} (S : Finset α) (g : α → Fin T → ℝ)
    (hg : ∀ a ∈ S, InRootedProfileSpan B W (g a)) :
    InRootedProfileSpan B W (fun v => ∏ a ∈ S, g a v) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact InRootedProfileSpan.one B W
  | insert a S ha_notin ih =>
    have h_a : InRootedProfileSpan B W (g a) := hg a (Finset.mem_insert_self a S)
    have h_S : InRootedProfileSpan B W (fun v => ∏ a ∈ S, g a v) := ih (fun b hb =>
      hg b (Finset.mem_insert_of_mem hb))
    have h_mul := InRootedProfileSpan.mul hB h_a h_S
    convert h_mul using 1
    funext v
    rw [Finset.prod_insert ha_notin]

/-- Closure of `InRootedProfileSpan` under `Finset.sum`. -/
private theorem InRootedProfileSpan.finset_sum {T : ℕ}
    {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    {α : Type*} (S : Finset α) (g : α → Fin T → ℝ)
    (hg : ∀ a ∈ S, InRootedProfileSpan B W (g a)) :
    InRootedProfileSpan B W (fun v => ∑ a ∈ S, g a v) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact InRootedProfileSpan.zero B W
  | insert a S ha_notin ih =>
    have h_a : InRootedProfileSpan B W (g a) := hg a (Finset.mem_insert_self a S)
    have h_S : InRootedProfileSpan B W (fun v => ∑ a ∈ S, g a v) := ih (fun b hb =>
      hg b (Finset.mem_insert_of_mem hb))
    have h_add := h_a.add h_S
    convert h_add using 1
    funext v
    rw [Finset.sum_insert ha_notin]
    rfl

/-- **Rooted separator** packaging: explicit structure for the witness of
non-orbit separation. Carries the graph, its `DecidableRel` instance, and
the separation proof in a single record — avoids instance mismatch issues
that arise when chaining `Classical.choose` on the nested existential. -/
private structure RootedSeparator {T : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (i j : Fin T) where
  n : ℕ
  F : SimpleGraph (Fin (n + 1))
  inst : DecidableRel F.Adj
  sep : @rootedProfile T n B W i F inst ≠ @rootedProfile T n B W j F inst

/-- Build a `RootedSeparator` from `k1_orbit_sep_aux` for distinct orbits. -/
private noncomputable def mkRootedSeparator {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (hW : ∀ i, 0 < W i) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    {i j : Fin T} (h : ¬ vertexOrbitRel B W i j) :
    RootedSeparator B W i j :=
  let sep := k1_orbit_sep_aux B hB W hW htwin h
  { n := sep.choose
    F := sep.choose_spec.choose
    inst := sep.choose_spec.choose_spec.choose
    sep := sep.choose_spec.choose_spec.choose_spec }

set_option maxHeartbeats 800000 in
theorem InRootedProfileSpan.of_const_on_orbit {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (f : Fin T → ℝ)
    (hf : ∀ i j, vertexOrbitRel B W i j → f i = f j) :
    InRootedProfileSpan B W f := by
  classical
  -- Step 1: each orbit indicator is in span via Lagrange.
  have ind_span : ∀ i : Fin T,
      InRootedProfileSpan B W (rootedOrbitIndicator B W i) := by
    intro i
    -- Factor function: uses RootedSeparator for explicit instance.
    let factor : Fin T → Fin T → ℝ := fun j v =>
      if h : ¬ vertexOrbitRel B W j i then
        let s := mkRootedSeparator B hB W hW htwin h
        letI : DecidableRel s.F.Adj := s.inst
        (rootedProfile B W v s.F - rootedProfile B W j s.F) /
        (rootedProfile B W i s.F - rootedProfile B W j s.F)
      else 1
    let nonOrb : Finset (Fin T) := Finset.univ.filter (fun j => ¬ vertexOrbitRel B W j i)
    let lagInd : Fin T → ℝ := fun v => ∏ j ∈ nonOrb, factor j v
    have lagInd_span : InRootedProfileSpan B W lagInd := by
      apply InRootedProfileSpan.finset_prod B hB W nonOrb factor
      intro j hj
      have hj_orb : ¬ vertexOrbitRel B W j i := by
        simp only [nonOrb, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact hj
      show InRootedProfileSpan B W (factor j)
      simp only [factor, dif_pos hj_orb]
      let s := mkRootedSeparator B hB W hW htwin hj_orb
      letI : DecidableRel s.F.Adj := s.inst
      exact InRootedProfileSpan.lagrange_factor B W s.F i j
    -- Show lagInd = rootedOrbitIndicator B W i.
    have lagInd_eq : lagInd = rootedOrbitIndicator B W i := by
      funext v
      unfold rootedOrbitIndicator
      by_cases hv : vertexOrbitRel B W i v
      · rw [if_pos hv]
        show ∏ j ∈ nonOrb, factor j v = (1 : ℝ)
        apply Finset.prod_eq_one
        intro j hj
        have hj_orb : ¬ vertexOrbitRel B W j i := by
          simp only [nonOrb, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          exact hj
        simp only [factor, dif_pos hj_orb]
        let s := mkRootedSeparator B hB W hW htwin hj_orb
        letI : DecidableRel s.F.Adj := s.inst
        have h_denom_ne : rootedProfile B W i s.F - rootedProfile B W j s.F ≠ 0 :=
          sub_ne_zero.mpr s.sep.symm
        have h_equiv : rootedProfileEquiv B W i v :=
          rootedProfileEquiv_of_vertexOrbitRel B W hv
        have h_eq : rootedProfile B W v s.F = rootedProfile B W i s.F :=
          (@h_equiv s.n s.F s.inst).symm
        rw [h_eq]
        exact div_self h_denom_ne
      · rw [if_neg hv]
        show ∏ j ∈ nonOrb, factor j v = (0 : ℝ)
        have h_v_no : ¬ vertexOrbitRel B W v i := fun h => hv (vertexOrbitRel.symm h)
        have h_v_mem : v ∈ nonOrb := by
          simp only [nonOrb, Finset.mem_filter, Finset.mem_univ, true_and]
          exact h_v_no
        refine Finset.prod_eq_zero h_v_mem ?_
        simp only [factor, dif_pos h_v_no]
        let s := mkRootedSeparator B hB W hW htwin h_v_no
        letI : DecidableRel s.F.Adj := s.inst
        show (rootedProfile B W v s.F - rootedProfile B W v s.F) /
             (rootedProfile B W i s.F - rootedProfile B W v s.F) = 0
        rw [sub_self, zero_div]
    rw [← lagInd_eq]
    exact lagInd_span
  -- Step 2: express f as a linear combination of orbit indicators.
  -- orbitSize i := card of orbit(i). Always ≥ 1.
  set orbitSize : Fin T → ℕ := fun i =>
    (Finset.univ.filter (fun j => vertexOrbitRel B W i j)).card with horbitSize_def
  have heq : f = fun v => ∑ i : Fin T,
      (f i / (orbitSize i : ℝ)) * rootedOrbitIndicator B W i v := by
    funext v
    -- Sum picks out i with v ∈ orbit(i), i.e., i ∈ orbit(v).
    have h_sum_filter :
        (∑ i : Fin T, (f i / (orbitSize i : ℝ)) * rootedOrbitIndicator B W i v) =
        ∑ i ∈ Finset.univ.filter (fun i => vertexOrbitRel B W i v),
            f i / (orbitSize i : ℝ) := by
      unfold rootedOrbitIndicator
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with h <;> simp
    rw [h_sum_filter]
    -- For i ∈ orbit(v), f i = f v and orbitSize i = orbitSize v.
    have h_summands : ∀ i ∈ Finset.univ.filter (fun i => vertexOrbitRel B W i v),
        f i / (orbitSize i : ℝ) = f v / (orbitSize v : ℝ) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hfi : f i = f v := hf i v hi
      -- orbit(i) = orbit(v) as Finsets (by transitivity).
      -- Helper: transitivity of vertexOrbitRel.
      have hOrbTrans : ∀ {a b c : Fin T}, vertexOrbitRel B W a b →
          vertexOrbitRel B W b c → vertexOrbitRel B W a c := by
        rintro a b c ⟨σ, ha₁, he₁⟩ ⟨τ, ha₂, he₂⟩
        refine ⟨σ.trans τ, ?_, ?_⟩
        · refine ⟨fun w => ?_, fun w x => ?_⟩
          · simp only [Equiv.trans_apply]; rw [ha₂.1, ha₁.1]
          · simp only [Equiv.trans_apply]; rw [ha₂.2, ha₁.2]
        · simp only [Equiv.trans_apply, he₁, he₂]
      have h_size : orbitSize i = orbitSize v := by
        have h_set_eq :
            (Finset.univ.filter (fun j => vertexOrbitRel B W i j)) =
            (Finset.univ.filter (fun j => vertexOrbitRel B W v j)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h_ij => hOrbTrans (vertexOrbitRel.symm hi) h_ij,
                 fun h_vj => hOrbTrans hi h_vj⟩
        rw [horbitSize_def]
        exact congrArg Finset.card h_set_eq
      rw [hfi, h_size]
    rw [Finset.sum_congr rfl h_summands]
    rw [Finset.sum_const, nsmul_eq_mul]
    -- card of filter = orbitSize v.
    have hcard : (Finset.univ.filter (fun i => vertexOrbitRel B W i v)).card = orbitSize v := by
      rw [horbitSize_def]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => vertexOrbitRel.symm h, fun h => vertexOrbitRel.symm h⟩
    rw [hcard]
    -- (orbitSize v : ℝ) > 0 since v ∈ orbit(v).
    have h_pos : (0 : ℝ) < (orbitSize v : ℝ) := by
      have h_pos_nat : 0 < orbitSize v := by
        rw [horbitSize_def]
        apply Finset.card_pos.mpr
        refine ⟨v, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨Equiv.refl _, ⟨fun _ => rfl, fun _ _ => rfl⟩, rfl⟩
      exact_mod_cast h_pos_nat
    rw [mul_div_assoc']
    rw [mul_comm (orbitSize v : ℝ) (f v), mul_div_assoc, div_self (ne_of_gt h_pos), mul_one]
  rw [heq]
  exact InRootedProfileSpan.finset_sum Finset.univ
    (fun i v => (f i / (orbitSize i : ℝ)) * rootedOrbitIndicator B W i v)
    (fun i _ => (ind_span i).smul (f i / (orbitSize i : ℝ)))

/-! ### K=1 rank theorem consequences (orbit indicators, Lemma 2.4) -/

/-- **Rank-theorem target** (K=1, span form), now DERIVED from
`InRootedProfileSpan.of_const_on_orbit`.

The orbit indicator of any vertex lies in the ℝ-span of rooted
simple-graph profile functions. Proved by combining:
- `rootedOrbitIndicator_const_on_orbit`: the indicator is orbit-invariant.
- `InRootedProfileSpan.of_const_on_orbit`: orbit-invariant functions are
  in the span (the K=1 rank-theorem paper-root). -/
theorem rootedOrbitIndicator_mem_rootedProfileSpan {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j) (i : Fin T) :
    ∃ (N : ℕ) (g : Fin N → Σ (n : ℕ) (F : SimpleGraph (Fin (n + 1))), DecidableRel F.Adj)
      (c : Fin N → ℝ),
      rootedOrbitIndicator B W i = fun v =>
        ∑ k : Fin N, c k * @rootedProfileFun T (g k).1 B W (g k).2.1 (g k).2.2 v :=
  InRootedProfileSpan.of_const_on_orbit B hB W hW htwin
    (rootedOrbitIndicator B W i)
    (rootedOrbitIndicator_const_on_orbit B W i)

/-- **Backward direction (Lovász §3 K=1 rank theorem)**: rooted-profile
equivalence ⟹ vertex orbit, under twin-free `B` + `W > 0`.

**Proof**: derived from `rootedOrbitIndicator_mem_rootedProfileSpan` by
evaluating the indicator at both `i` and `j`. Rooted-profile equivalence
forces the linear combination to agree at both, and reflexivity gives
`indicator_i(i) = 1`, hence `indicator_i(j) = 1`, hence vertex orbit. -/
theorem rootedProfileEquiv_imp_vertexOrbitRel {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    {i j : Fin T} (h : rootedProfileEquiv B W i j) :
    vertexOrbitRel B W i j := by
  obtain ⟨N, g, c, hspan⟩ :=
    rootedOrbitIndicator_mem_rootedProfileSpan B hB W hW htwin i
  have h_eq_at_j : rootedOrbitIndicator B W i j = rootedOrbitIndicator B W i i := by
    have := congr_fun hspan j
    have h' := congr_fun hspan i
    rw [this, h']
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    unfold rootedProfileFun
    exact (@h (g k).1 (g k).2.1 (g k).2.2).symm
  have h_refl : vertexOrbitRel B W i i :=
    ⟨Equiv.refl _, ⟨fun _ => rfl, fun _ _ => rfl⟩, rfl⟩
  have h_i_self : rootedOrbitIndicator B W i i = 1 := by
    unfold rootedOrbitIndicator
    classical
    exact if_pos h_refl
  have h_j_val : rootedOrbitIndicator B W i j = 1 := h_eq_at_j.trans h_i_self
  by_contra h_no
  unfold rootedOrbitIndicator at h_j_val
  classical
  rw [if_neg h_no] at h_j_val
  exact zero_ne_one h_j_val

/-- **K=1 Lovász Lemma 2.4** (iff form). Combines the forward direction
(orbit ⟹ equiv, free) with the backward direction (equiv ⟹ orbit, the
rank-theorem paper-root). -/
theorem rootedProfileEquiv_iff_vertexOrbitRel {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j) (i j : Fin T) :
    rootedProfileEquiv B W i j ↔ vertexOrbitRel B W i j :=
  ⟨rootedProfileEquiv_imp_vertexOrbitRel B hB W hW htwin,
   rootedProfileEquiv_of_vertexOrbitRel B W⟩

/-- **Weighted adjacency operator** `A f i := ∑ j, W j · B i j · f j`.
The key linear operator for the Krylov/path-profile route to
separation in the K=1 case. -/
noncomputable def weightedAdj {T : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (f : Fin T → ℝ) (i : Fin T) : ℝ :=
  ∑ j : Fin T, W j * B i j * f j

/-- **Iterated weighted adjacency**: `A^m` as a function. -/
noncomputable def weightedAdjIter {T : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) : ℕ → (Fin T → ℝ) → Fin T → ℝ
  | 0, f => f
  | m + 1, f => weightedAdj B W (weightedAdjIter B W m f)

/-- **Closed-walk profile** at vertex `i` of length `m`.

`CW_m(i) := ∑_{v_1,...,v_{m-1}} W(v_1)...W(v_{m-1}) ·
            B(i, v_1) · B(v_1, v_2) · ... · B(v_{m-1}, i)`

Compositional form: let `g_i(v) := B(v, i)`. Then for `m ≥ 1`,
`CW_m(i) = (A^{m-1} g_i)(i)` where `A` is `weightedAdj`. Encoded
recursively via `weightedAdjIter`.

For `m = 0`: trivially `1` (empty product).
For `m = 1`: `B(i, i) = 0` for simple graphs without self-loops.
For `m ≥ 2`: well-defined closed walk sum. -/
noncomputable def closedWalkProfile {T : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (i : Fin T) : ℕ → ℝ
  | 0     => 1
  | m + 1 => weightedAdjIter B W m (fun v => B v i) i

/-! ### §4 — Spectral scaffolding for #77 (deferred)

Per 2026-05-18 design plan, the K=1 spectral closing lemma
`vertex_orbit_of_closed_walks_eq` factors through finite-dimensional
spectral theory on the symmetric operator `S := D^{1/2} B D^{1/2}`
where `D = diag(W)`.

**Key identity** (to be proved as a stepping stone):
`closedWalkProfile B W i (m + 1) = (S^m)[i, i] / W i` for `m ≥ 1`.

Closure path:
1. Bridge: closed walks ↔ diagonal moments of S^m.
2. Cayley-Hamilton: equality at m = 0..T-1 suffices.
3. Spectral decomposition: S = ∑ λ_k u_k u_k^T (mathlib's
   `Matrix.IsSymm.eigenvectorBasis`).
4. Equal spectral diagonals + twin-free → orbit upgrade.

**Scaffolding deferred**: importing `Real.sqrt` machinery
(`Analysis.SpecialFunctions.Pow.*`) introduces simp lemmas that
conflict with earlier proofs in this file. The spectral work
should be done in a SEPARATE FILE `Graphon/Spectral.lean` that
imports the necessary analysis modules without polluting Lovasz.lean.
That refactor is the natural next-session task. -/

/-! **K=1 spectral closing chain** (former #77 docstring, 2026-05-18).

Empirical evidence (cumulative across 4 falsification scripts):
- 291/291 random + cycle-disjoint-union pairs separated at length ≥ 3.
- 22,096 twin-free simple graphs (T ≤ 6 full enum): 0 counterexamples.
- 7 adversarial known cospectral structures: 0 counterexamples.
- 78 weighted twin-free cases: 0 counterexamples.

The `m + 3` offset (length ≥ 3) is required because length-2 closed
walks `∑_v W(v) B(i,v)²` are inherently multigraph evaluations (edge
multiplicity 2) and cannot be realized by simple graphs. -/

/-- **K=1 spectral closing lemma** (named paper-root for #77).

If two vertices have matching closed-walk profiles at all lengths
≥ 3, then they lie in the same `(B, W)`-vertex orbit (under twin-free
B + W > 0).

This is the positive (contrapositive) form of #77. Stating it
explicitly localizes the spectral content of Lovász §3 K=1 to a
single named theorem.

**Mathematical content**: closed walk profiles `CW_m(i) = (S^m)[i,i]/W[i]`
(where `S = D^{1/2} B D^{1/2}`) determine the spectral diagonal data
at i. The conjecture was that Cayley-Hamilton + spectral theory +
twin-free could force orbit relation.

**STATUS (2026-05-18): REFUTED**.

Counterexample: vertices 1 and 5 in the 9-vertex "double-pin tree"
have identical (S^m)[i, i] for all m but lie in different orbits
(|Aut| = 1). The graph is twin-free. See
`scripts/spectral_orbit_validation.py`.

**Implications**:
- This theorem is FALSE as stated. The sorry'd statement is retained
  for architectural documentation; it should NOT be assumed downstream.
- `closed_walk_profiles_separate_vertex_orbits` (proved below via
  contrapositive of this) inherits the issue; its statement is also
  false in this form.
- `rooted_profiles_separate_vertex_orbits` (the K=1 specialization
  of Lovász Lemma 2.4) is TRUE but our current proof route via the
  closed-walk bridge is INVALID. Needs to be re-proved through the
  full rooted simple-graph family (paths, trees, asymmetric shapes),
  not just rooted cycles.

**Earlier empirical evidence** turned out to be incomplete:
- The cospectral_vertex_search.py corpus stopped at T = 6.
- The double-pin counterexample is on T = 9 — outside the prior
  exhaustive enum range.
- Random/adversarial scripts didn't include this specific
  graph structure.

**Salvaged content**: the bridge theorems `rootedProfile_rootedCycleGraph_eq_closedWalkProfile`
and `closedWalkProfile_eq_symAdjIter_diag` (in Spectral.lean) are
still valuable. They translate between representations; what's wrong
is the orbit-upgrade INFERENCE from closed walks alone. -/
theorem vertex_orbit_of_closed_walks_eq {T : ℕ}
    (_B : Fin T → Fin T → ℝ) (_hB : ∀ i j, _B i j = _B j i)
    (_W : Fin T → ℝ) (_hW : ∀ i, 0 < _W i)
    (_htwin : ∀ i j, i ≠ j → _B i ≠ _B j)
    {i j : Fin T}
    (_h : ∀ m : ℕ, closedWalkProfile _B _W i (m + 3) =
                   closedWalkProfile _B _W j (m + 3)) :
    vertexOrbitRel _B _W i j := by
  sorry

/-- **#77** — REFUTED 2026-05-18.

Statement is FALSE: the double-pin tree (T=9) has twin-free B + W = 1
with two non-orbit vertices (1, 5) whose closed-walk profiles agree
for all m. Retained as a sorry'd statement to document the
counterexample and prevent accidental downstream use.

The proof previously routed through `vertex_orbit_of_closed_walks_eq`
(also REFUTED). Do not assume this theorem in downstream work.

Counterexample: edges (0,1)(1,2)(2,3)(3,7)(0,4)(4,5)(5,6)(4,8); vertices
1 and 5 are spectrally equivalent (closed walks match for all m) but
|Aut| = 1, so they are in different orbits. -/
theorem closed_walk_profiles_separate_vertex_orbits {T : ℕ}
    (_B : Fin T → Fin T → ℝ) (_hB : ∀ i j, _B i j = _B j i) (_W : Fin T → ℝ)
    (_hW : ∀ i, 0 < _W i)
    (_htwin : ∀ i j, i ≠ j → _B i ≠ _B j)
    {i j : Fin T} (_h : ¬ vertexOrbitRel _B _W i j) :
    ∃ m : ℕ, closedWalkProfile _B _W i (m + 3) ≠ closedWalkProfile _B _W j (m + 3) := by
  sorry

/-- **Rooted cycle graph** at length `m + 2`. Edges are consecutive
pairs `(j, j+1)` plus the wrap edge `(0, m+1)`. The K=1 label placement
makes vertex 0 the "root" of the rooted cycle. The `m + 2` offset
ensures `m + 2 ≥ 2`, so the graph has at least one edge. -/
def rootedCycleGraph (m : ℕ) : SimpleGraph (Fin (m + 2)) where
  Adj a b := (a.val + 1 = b.val) ∨ (b.val + 1 = a.val) ∨
             (a.val = 0 ∧ b.val = m + 1) ∨ (a.val = m + 1 ∧ b.val = 0)
  symm := fun a b h => by
    rcases h with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr ⟨h2, h1⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))
  loopless := fun a h => by
    rcases h with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · omega
    · omega
    · have := a.isLt; omega
    · have := a.isLt; omega

instance (m : ℕ) : DecidableRel (rootedCycleGraph m).Adj := by
  intro a b
  unfold rootedCycleGraph
  exact inferInstance

/-- Adjacency unfolding lemma for `rootedCycleGraph`. -/
@[simp] lemma rootedCycleGraph_adj_iff {m : ℕ} (a b : Fin (m + 2)) :
    (rootedCycleGraph m).Adj a b ↔
      (a.val + 1 = b.val) ∨ (b.val + 1 = a.val) ∨
      (a.val = 0 ∧ b.val = m + 1) ∨ (a.val = m + 1 ∧ b.val = 0) :=
  Iff.rfl

/-- Loopless property unfolding. -/
lemma rootedCycleGraph_not_adj_self {m : ℕ} (a : Fin (m + 2)) :
    ¬ (rootedCycleGraph m).Adj a a :=
  (rootedCycleGraph m).loopless a

/-- Sum decomposition: a sum over `Fin (k+1) → α` decomposes as a double sum
over the head (element of `α`) and the tail (`Fin k → α`). Re-indexing via
`Fin.consEquiv`. Used to express the recursive structure of `weightedAdjIter`
as a single sum over walk-coordinate functions. -/
lemma sum_fin_succ_eq_sum_cons {T n : ℕ} [AddCommMonoid β]
    (f : (Fin (n + 1) → Fin T) → β) :
    ∑ σ : Fin (n + 1) → Fin T, f σ
      = ∑ x : Fin T, ∑ σ' : Fin n → Fin T, f (Fin.cons x σ') := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin T)).sum_comp]
  rw [← Finset.sum_product']
  rfl

/-- Cyclic successor on `Fin (m + 2)`: maps `j` to `j + 1` modulo `m + 2`. -/
def cycleSucc {m : ℕ} (j : Fin (m + 2)) : Fin (m + 2) :=
  if h : j.val + 1 < m + 2 then ⟨j.val + 1, h⟩ else ⟨0, by omega⟩

@[simp] lemma cycleSucc_val_of_lt {m : ℕ} (j : Fin (m + 2)) (hj : j.val + 1 < m + 2) :
    (cycleSucc j).val = j.val + 1 := by
  unfold cycleSucc; rw [dif_pos hj]

@[simp] lemma cycleSucc_val_of_eq {m : ℕ} (j : Fin (m + 2)) (hj : j.val = m + 1) :
    (cycleSucc j).val = 0 := by
  unfold cycleSucc
  have : ¬ (j.val + 1 < m + 2) := by omega
  rw [dif_neg this]

lemma cycleSucc_adj {m : ℕ} (j : Fin (m + 2)) :
    (rootedCycleGraph m).Adj j (cycleSucc j) := by
  rcases lt_or_ge (j.val + 1) (m + 2) with h | h
  · -- consecutive case
    left
    exact (cycleSucc_val_of_lt j h).symm
  · -- wrap case: j.val = m + 1; cycleSucc j has val = 0.
    have hj_eq : j.val = m + 1 := by have := j.isLt; omega
    right; right; right
    refine ⟨hj_eq, ?_⟩
    exact cycleSucc_val_of_eq j hj_eq

/-- Every edge of `rootedCycleGraph (m+1)` (for `m+3 ≥ 3` vertices) is of
the form `s(j, cycleSucc j)` for some `j : Fin (m+3)`. The `m+1` offset
ensures the cycle has at least 3 vertices, so the edge map is injective
(distinct `j` give distinct unordered pairs, since a 2-cycle would
require `m+2 = 2`). -/
lemma rootedCycleGraph_adj_iff_succ {m : ℕ} (a b : Fin (m + 3)) :
    (rootedCycleGraph (m + 1)).Adj a b ↔
      cycleSucc a = b ∨ cycleSucc b = a := by
  constructor
  · intro h
    rw [rootedCycleGraph_adj_iff] at h
    rcases h with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- a.val + 1 = b.val: cycleSucc a = b (in the within-range branch)
      left
      apply Fin.ext
      rw [cycleSucc_val_of_lt a (by have := b.isLt; omega)]
      exact h
    · -- b.val + 1 = a.val: cycleSucc b = a
      right
      apply Fin.ext
      rw [cycleSucc_val_of_lt b (by have := a.isLt; omega)]
      exact h
    · -- a.val = 0 ∧ b.val = m + 2: cycleSucc b = a (b wraps to 0 = a)
      right
      apply Fin.ext
      rw [cycleSucc_val_of_eq b h2]
      exact h1.symm
    · -- a.val = m + 2 ∧ b.val = 0: cycleSucc a = b (a wraps to 0 = b)
      left
      apply Fin.ext
      rw [cycleSucc_val_of_eq a h1]
      exact h2.symm
  · intro h
    rcases h with h | h
    · rw [← h]; exact cycleSucc_adj a
    · rw [← h]; exact (rootedCycleGraph (m + 1)).symm (cycleSucc_adj b)

/-- `cycleSucc` is not its own inverse: `cycleSucc (cycleSucc j) ≠ j` on
`Fin (m + 3)` (which has at least 3 elements, so no 2-cycles exist). -/
lemma cycleSucc_cycleSucc_ne {m : ℕ} (k : Fin (m + 3)) :
    cycleSucc (cycleSucc k) ≠ k := by
  intro h
  have hval : (cycleSucc (cycleSucc k)).val = k.val := congrArg Fin.val h
  have hk := k.isLt
  by_cases h1 : k.val + 1 < m + 3
  · have hsk : (cycleSucc k).val = k.val + 1 := cycleSucc_val_of_lt _ h1
    by_cases h2 : (cycleSucc k).val + 1 < m + 3
    · have : (cycleSucc (cycleSucc k)).val = k.val + 2 := by
        rw [cycleSucc_val_of_lt _ h2, hsk]
      omega
    · have hsk_eq : (cycleSucc k).val = m + 2 := by
        have := (cycleSucc k).isLt; omega
      have : (cycleSucc (cycleSucc k)).val = 0 :=
        cycleSucc_val_of_eq _ hsk_eq
      omega
  · have hk_eq : k.val = m + 2 := by omega
    have hsk : (cycleSucc k).val = 0 := cycleSucc_val_of_eq _ hk_eq
    have hsk_lt : (cycleSucc k).val + 1 < m + 3 := by rw [hsk]; omega
    have : (cycleSucc (cycleSucc k)).val = 1 := by
      rw [cycleSucc_val_of_lt _ hsk_lt, hsk]
    omega

/-- The map `j ↦ s(j, cycleSucc j)` is injective on `Fin (m + 3)`. -/
lemma cycleSucc_pair_injective {m : ℕ} :
    Function.Injective
      (fun j : Fin (m + 3) => (s(j, cycleSucc j) : Sym2 (Fin (m + 3)))) := by
  intro j k hjk
  rw [Sym2.eq_iff] at hjk
  rcases hjk with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact h1
  · exfalso
    apply cycleSucc_cycleSucc_ne k
    rw [← h1]; exact h2

/-- The edge finset of `rootedCycleGraph (m+1)` is exactly the image of
the map `j ↦ s(j, cycleSucc j)` over `Fin (m + 3)`. -/
lemma rootedCycleGraph_edgeFinset_eq {m : ℕ} :
    (rootedCycleGraph (m + 1)).edgeFinset =
      Finset.univ.image (fun j : Fin (m + 3) => s(j, cycleSucc j)) := by
  classical
  ext e
  refine e.ind ?_
  intro a b
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, rootedCycleGraph_adj_iff_succ]
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (h | h)
    · exact ⟨a, by rw [h]⟩
    · refine ⟨b, ?_⟩
      rw [h]; exact Sym2.eq_swap
  · rintro ⟨j, hj⟩
    rw [Sym2.eq_iff] at hj
    rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [← h1, ← h2]
    · right; rw [← h1, ← h2]

/-- For a symmetric `B`, the τ-parametric edge product over the cycle
factors via `cycleSucc`: each edge `s(j, cycleSucc j)` contributes
`B (τ j) (τ (cycleSucc j))`, regardless of `Quot.out` orientation. -/
lemma rootedCycleGraph_edgeProduct_eq {T m : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (τ : Fin (m + 3) → Fin T) :
    (∏ e ∈ (rootedCycleGraph (m + 1)).edgeFinset,
        B (τ (Quot.out e).1) (τ (Quot.out e).2))
    = ∏ j : Fin (m + 3), B (τ j) (τ (cycleSucc j)) := by
  classical
  rw [rootedCycleGraph_edgeFinset_eq]
  rw [Finset.prod_image (fun _ _ _ _ h => cycleSucc_pair_injective h)]
  apply Finset.prod_congr rfl
  intro j _
  -- For each j: Quot.out of s(j, cycleSucc j) gives some (a, b) with
  -- Sym2.mk (a, b) = s(j, cycleSucc j); use Sym2.eq_iff + hB symmetry.
  have hp : (Sym2.mk (Quot.out (s(j, cycleSucc j) : Sym2 _)))
            = (s(j, cycleSucc j) : Sym2 _) := Quot.out_eq _
  rw [Sym2.eq_iff] at hp
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]; exact hB _ _

/-- One-step unfold of `weightedAdjIter`: `M^{k+1} g v = ∑ u, W u · B v u · M^k g u`. -/
private lemma weightedAdjIter_succ {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (k : ℕ) (g : Fin T → ℝ) (v : Fin T) :
    weightedAdjIter B W (k + 1) g v
      = ∑ u : Fin T, W u * B v u * weightedAdjIter B W k g u := by
  rfl

/-- `cycleSucc 0 = ⟨1, _⟩` in `Fin (m + 3)`. -/
private lemma cycleSucc_zero {m : ℕ} :
    cycleSucc (⟨0, by omega⟩ : Fin (m + 3)) = ⟨1, by omega⟩ := by
  apply Fin.ext
  rw [cycleSucc_val_of_lt _ (by show 0 + 1 < m + 3; omega)]

/-- OfNat-shape `cycleSucc 0 = 1` for products generated by
`Fin.prod_univ_succ`. -/
private lemma cycleSucc_ofNat_zero {m : ℕ} :
    cycleSucc (0 : Fin (m + 3)) = (1 : Fin (m + 3)) := by
  apply Fin.ext
  show (cycleSucc (0 : Fin (m + 3))).val = (1 : Fin (m + 3)).val
  rw [cycleSucc_val_of_lt _ (by show 0 + 1 < m + 3; omega)]
  rfl

/-- `cycleSucc` of `⟨m+2, _⟩` wraps to `⟨0, _⟩`. -/
private lemma cycleSucc_last_eq {m : ℕ} :
    cycleSucc (⟨m + 2, by omega⟩ : Fin (m + 3)) = ⟨0, by omega⟩ := by
  apply Fin.ext
  rw [cycleSucc_val_of_eq _ (by show (m + 2 : ℕ) = m + 1 + 1; omega)]

/-- `cycleSucc` at index `k + 1` is `k + 2` (when `k + 1 < m + 2`). -/
private lemma cycleSucc_mid {m : ℕ} (k : Fin (m + 1)) :
    cycleSucc (⟨k.val + 1, by have := k.isLt; omega⟩ : Fin (m + 3))
      = ⟨k.val + 2, by have := k.isLt; omega⟩ := by
  apply Fin.ext
  rw [cycleSucc_val_of_lt _ (by have := k.isLt; show k.val + 1 + 1 < m + 3; omega)]

/-- Term-by-term expansion of `weightedAdjIter`: a coordinate assignment
`σ : Fin n → Fin T` contributes the W-product and the directed path product
from the current vertex through `σ`. -/
private noncomputable def weightedAdjIterTerm {T : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) : (n : ℕ) → (Fin T → ℝ) → Fin T → (Fin n → Fin T) → ℝ
  | 0, g, v, _ => g v
  | n + 1, g, v, σ =>
      W (σ 0) * B v (σ 0) *
        weightedAdjIterTerm B W n g (σ 0) (fun k => σ k.succ)

/-- `weightedAdjIter` is the sum of its coordinate-wise path terms. -/
private lemma weightedAdjIter_eq_sum_term {T : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (n : ℕ) (g : Fin T → ℝ) (v : Fin T) :
    weightedAdjIter B W n g v =
      ∑ σ : Fin n → Fin T, weightedAdjIterTerm B W n g v σ := by
  induction n generalizing v with
  | zero =>
      simp [weightedAdjIter, weightedAdjIterTerm]
  | succ n ih =>
      rw [weightedAdjIter_succ]
      simp_rw [ih]
      rw [sum_fin_succ_eq_sum_cons]
      simp [weightedAdjIterTerm, Finset.mul_sum]

/-- Explicit closed form for `weightedAdjIterTerm` of level `n + 1`:
weight product × root-edge × interior chain × terminal `g`. -/
private lemma weightedAdjIterTerm_succ_form {T : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (g : Fin T → ℝ) :
    ∀ (n : ℕ) (v : Fin T) (σ : Fin (n + 1) → Fin T),
      weightedAdjIterTerm B W (n + 1) g v σ =
        (∏ k : Fin (n + 1), W (σ k)) *
        B v (σ 0) *
        (∏ k : Fin n, B (σ k.castSucc) (σ k.succ)) *
        g (σ (Fin.last n)) := by
  intro n
  induction n with
  | zero =>
      intro v σ
      simp [weightedAdjIterTerm, Fin.prod_univ_succ, Fin.prod_univ_zero]
  | succ n ih =>
      intro v σ
      show W (σ 0) * B v (σ 0) *
           weightedAdjIterTerm B W (n + 1) g (σ 0) (fun k => σ k.succ) = _
      rw [ih (σ 0) (fun k => σ k.succ)]
      simp only [Fin.prod_univ_succ, Fin.succ_castSucc, Fin.castSucc_zero,
                 Fin.succ_last]
      ring

/-- The cycle B-product on `rootedCycleGraph (m+1)` factors as
root edge × interior chain × closing edge. Pure combinatorial identity
via `Fin.prod_univ_succ` + `Fin.prod_univ_castSucc`. -/
private lemma cycle_prod_factored {T m : ℕ} (B : Fin T → Fin T → ℝ) (i : Fin T)
    (σ : Fin (m + 2) → Fin T) :
    (∏ j : Fin (m + 3), B
      (if h : (j : ℕ) < 1 then i else σ ⟨j.val - 1, by have := j.isLt; omega⟩)
      (if h : ((cycleSucc j) : ℕ) < 1 then i
       else σ ⟨(cycleSucc j).val - 1, by have := (cycleSucc j).isLt; omega⟩))
    = B i (σ 0) * (∏ k : Fin (m + 1), B (σ k.castSucc) (σ k.succ)) *
      B (σ (Fin.last (m + 1))) i := by
  -- Step 1: cycleSucc values at the three positions we care about.
  have h0_val : ((0 : Fin (m + 3)) : ℕ) = 0 := rfl
  have hcs_zero : (cycleSucc (0 : Fin (m + 3))).val = 1 := by
    have := cycleSucc_val_of_lt (0 : Fin (m + 3)) (by rw [h0_val]; omega)
    rw [this, h0_val]
  have h_last_succ_val : (((Fin.last (m + 1)).succ : Fin (m + 3)) : ℕ) = m + 2 := by
    simp [Fin.val_succ, Fin.val_last]
  have hcs_last : (cycleSucc ((Fin.last (m + 1)).succ : Fin (m + 3))).val = 0 := by
    apply cycleSucc_val_of_eq
    rw [h_last_succ_val]
  have h_mid_succ_val : ∀ k : Fin (m + 1),
      ((k.castSucc.succ : Fin (m + 3)) : ℕ) = k.val + 1 := by
    intro k
    simp [Fin.val_succ, Fin.val_castSucc]
  have hcs_mid : ∀ k : Fin (m + 1),
      (cycleSucc (k.castSucc.succ : Fin (m + 3))).val = k.val + 2 := by
    intro k
    have := cycleSucc_val_of_lt (k.castSucc.succ : Fin (m + 3))
      (by rw [h_mid_succ_val]; have := k.isLt; omega)
    rw [this, h_mid_succ_val]
  -- Step 2: split product.
  rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc]
  -- Step 3: reduce each factor using cycleSucc values + Fin.val computations.
  -- Root factor: B (τ 0) (τ (cycleSucc 0)) = B i (σ 0).
  have h_root : B
        (if h : ((0 : Fin (m + 3)) : ℕ) < 1 then i
         else σ ⟨((0 : Fin (m + 3)) : ℕ) - 1, by
           have := (0 : Fin (m + 3)).isLt; omega⟩)
        (if h : ((cycleSucc (0 : Fin (m + 3))) : ℕ) < 1 then i
         else σ ⟨((cycleSucc (0 : Fin (m + 3))) : ℕ) - 1, by
           have := (cycleSucc (0 : Fin (m + 3))).isLt; omega⟩)
      = B i (σ 0) := by
    rw [dif_pos (show ((0 : Fin (m + 3)) : ℕ) < 1 by show 0 < 1; omega)]
    rw [dif_neg (by rw [hcs_zero]; omega)]
    congr 2
  -- Closing factor: B (τ last.succ) (τ (cycleSucc last.succ)) = B (σ last) i.
  have h_close : B
        (if h : (((Fin.last (m + 1)).succ : Fin (m + 3)) : ℕ) < 1 then i
         else σ ⟨(((Fin.last (m + 1)).succ : Fin (m + 3)) : ℕ) - 1, by
           have := ((Fin.last (m + 1)).succ : Fin (m + 3)).isLt; omega⟩)
        (if h : ((cycleSucc ((Fin.last (m + 1)).succ : Fin (m + 3))) : ℕ) < 1 then i
         else σ ⟨((cycleSucc ((Fin.last (m + 1)).succ : Fin (m + 3))) : ℕ) - 1, by
           have := (cycleSucc ((Fin.last (m + 1)).succ : Fin (m + 3))).isLt; omega⟩)
      = B (σ (Fin.last (m + 1))) i := by
    rw [dif_neg (by rw [h_last_succ_val]; omega)]
    rw [dif_pos (by rw [hcs_last]; omega)]
    congr 2
  -- Middle factor: ∀ k, B (τ k.castSucc.succ) (τ (cycleSucc k.castSucc.succ)) = B (σ k.castSucc) (σ k.succ).
  have h_middle : ∀ k : Fin (m + 1),
      B (if h : ((k.castSucc.succ : Fin (m + 3)) : ℕ) < 1 then i
         else σ ⟨((k.castSucc.succ : Fin (m + 3)) : ℕ) - 1, by
           have := (k.castSucc.succ : Fin (m + 3)).isLt; omega⟩)
        (if h : ((cycleSucc (k.castSucc.succ : Fin (m + 3))) : ℕ) < 1 then i
         else σ ⟨((cycleSucc (k.castSucc.succ : Fin (m + 3))) : ℕ) - 1, by
           have := (cycleSucc (k.castSucc.succ : Fin (m + 3))).isLt; omega⟩)
      = B (σ k.castSucc) (σ k.succ) := by
    intro k
    rw [dif_neg (by rw [h_mid_succ_val]; omega)]
    rw [dif_neg (by rw [hcs_mid k]; omega)]
    congr 1
    apply congrArg σ; apply Fin.ext
    show ((cycleSucc (k.castSucc.succ : Fin (m + 3))).val - 1 : ℕ) = (k.succ : Fin (m + 2)).val
    rw [hcs_mid k]; simp [Fin.val_succ]
  -- Assemble.
  rw [h_root, h_close]
  rw [show (∏ i_1 : Fin (m + 1), B
        (if h : ((i_1.castSucc.succ : Fin (m + 3)) : ℕ) < 1 then i
         else σ ⟨((i_1.castSucc.succ : Fin (m + 3)) : ℕ) - 1, by
           have := (i_1.castSucc.succ : Fin (m + 3)).isLt; omega⟩)
        (if h : ((cycleSucc (i_1.castSucc.succ : Fin (m + 3))) : ℕ) < 1 then i
         else σ ⟨((cycleSucc (i_1.castSucc.succ : Fin (m + 3))) : ℕ) - 1, by
           have := (cycleSucc (i_1.castSucc.succ : Fin (m + 3))).isLt; omega⟩))
      = ∏ k : Fin (m + 1), B (σ k.castSucc) (σ k.succ) from
    Finset.prod_congr rfl (fun k _ => h_middle k)]
  ring

/-- The cycle product in the rooted cycle evaluation is exactly the
coordinate-wise term in the closed-walk expansion. -/
private lemma cycleEvalTerm_eq_weightedAdjIterTerm {T m : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (i : Fin T)
    (σ : Fin (m + 2) → Fin T) :
    (let τ : Fin (m + 3) → Fin T := fun v =>
      if h : (v : ℕ) < 1 then i else σ ⟨v - 1, by have := v.isLt; omega⟩
    (∏ v : Fin (m + 2), W (σ v)) *
      ∏ j : Fin (m + 3), B (τ j) (τ (cycleSucc j))) =
    weightedAdjIterTerm B W (m + 2) (fun v => B v i) i σ := by
  rw [weightedAdjIterTerm_succ_form]
  -- LHS has `let τ := ...`; eliminate via show to expose the if-then-else.
  show (∏ v : Fin (m + 2), W (σ v)) *
       (∏ j : Fin (m + 3), B
         (if h : (j : ℕ) < 1 then i else σ ⟨j.val - 1, by have := j.isLt; omega⟩)
         (if h : ((cycleSucc j) : ℕ) < 1 then i
          else σ ⟨(cycleSucc j).val - 1, by have := (cycleSucc j).isLt; omega⟩))
       = _
  rw [cycle_prod_factored]
  ring

/-- **Bridge lemma**: `rootedProfile` of `rootedCycleGraph (m+1)` at
vertex `i` equals the closed-walk profile `closedWalkProfile B W i (m+3)`.

Pure combinatorics: the edges of the cycle on `Fin (m+3)` are exactly
`{j, j+1}` for `j : Fin (m+3)` plus the wrap `{0, m+2}`, so the edge
product in `simpleEvalAt` factors as the closed-walk product
`B(i, σ 0) · B(σ 0, σ 1) · ... · B(σ (m+1), i)`, matching
`(weightedAdjIter B W (m+2) g_i)(i)` where `g_i(v) := B(v, i)`.

The `m + 1` offset on `rootedCycleGraph` (giving cycle length ≥ 3) is
necessary because `rootedCycleGraph 0` is a single edge (1 edge),
which evaluates to ∑ W(v) B(i,v) (weighted degree), not the
closed-walk-of-length-2 profile ∑ W(v) B(i,v)² (which is inherently
a multigraph evaluation, requiring edge multiplicity 2).

**Status**: focused infrastructure sorry. Needed to wire
`closed_walk_profiles_separate_vertex_orbits` into
`rooted_profiles_separate_vertex_orbits`. ~30-80 lines of Fin
arithmetic + `Quot.out` reasoning (down from 100-200 thanks to
the cycleSucc helper set). -/
theorem rootedProfile_rootedCycleGraph_eq_closedWalkProfile {T m : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (i : Fin T) :
    rootedProfile B W i (rootedCycleGraph (m + 1)) =
      closedWalkProfile B W i (m + 3) := by
  classical
  show rootedProfile B W i (rootedCycleGraph (m + 1)) =
       weightedAdjIter B W (m + 2) (fun v => B v i) i
  unfold rootedProfile simpleEvalAt
  rw [weightedAdjIter_eq_sum_term]
  apply Finset.sum_congr rfl
  intro σ _
  let τ : Fin (m + 3) → Fin T := fun v =>
    if h : (v : ℕ) < 1 then i else σ ⟨v - 1, by have := v.isLt; omega⟩
  change (∏ v : Fin (m + 2), W (σ v)) *
         (∏ e ∈ (rootedCycleGraph (m + 1)).edgeFinset,
           B (τ (Quot.out e).1) (τ (Quot.out e).2)) = _
  rw [rootedCycleGraph_edgeProduct_eq B hB τ]
  exact cycleEvalTerm_eq_weightedAdjIterTerm B W i σ

/-- **Rooted profiles separate vertex orbits** (Lovász §3 K=1 case).
If two vertices are NOT in the same `(B, W)`-orbit (under twin-free
B + W > 0), some rooted simple graph evaluation separates them.

This is the K=1 case of `orbit_separation_by_simple_graph`,
specialized to vertex (single-label) tuples.

**Empirical evidence stack** (post-2026-05-14 falsification passes):
- Path profiles ALONE: FAIL on cycle-disjoint-union families
  (`scripts/path_profile_search.py`). Regular graphs have identical
  path profiles at every vertex.
- Closed-walk / rooted-cycle profiles: PASS broadly (291/291 pairs
  on the test corpus, `scripts/closed_walk_search.py`); zero
  cospectral-vertex counterexamples on full enumeration of all
  twin-free simple graphs through T ≤ 6.
- The full rooted simple-graph family (paths + cycles + trees +
  arbitrary connected) suffices in all tested cases.

**STATUS (2026-05-18)**: PAPER-ROOT (was: proved via closed walks,
REFUTED).

Previous proof routed through `closed_walk_profiles_separate_vertex_orbits`
+ the `rootedCycleGraph` bridge. That route is INVALID — the
double-pin tree counterexample (2026-05-18) shows closed walks alone
are insufficient even under twin-free + W > 0.

The THEOREM itself is TRUE (Lovász Lemma 2.4 K=1 specialization), but
proving it requires the FULL rooted simple-graph family (paths, trees,
asymmetric shapes), which is the Lovász §3 rank theorem content. -/
theorem rooted_profiles_separate_vertex_orbits {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    {i j : Fin T} (h : ¬ vertexOrbitRel B W i j) :
    ∃ (n : ℕ) (F : SimpleGraph (Fin (n + 1))) (_ : DecidableRel F.Adj),
      rootedProfile B W i F ≠ rootedProfile B W j F := by
  -- Contrapositive of rootedProfileEquiv_imp_vertexOrbitRel.
  by_contra h_no_sep
  push_neg at h_no_sep
  apply h
  apply rootedProfileEquiv_imp_vertexOrbitRel B hB W hW htwin
  intro n F hF_dec
  exact h_no_sep n F hF_dec

/-- **Bridge from K=1 rooted profile to general orbit separation**.
At K = 1, `orbit_separation_by_simple_graph` follows from
`rooted_profiles_separate_vertex_orbits` by reducing the tuple
relation to vertex relation. -/
theorem orbit_separation_by_simple_graph_K1 {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    {ξ ξ' : Fin 1 → Fin T}
    (h : ¬ tupleOrbitRel B W ξ ξ') :
    ∃ (n : ℕ) (F : SimpleGraph (Fin (n + 1))) (_ : DecidableRel F.Adj),
      simpleEvalAt B W F ξ ≠ simpleEvalAt B W F ξ' := by
  -- ξ = fun _ => ξ 0; ξ' = fun _ => ξ' 0; tupleOrbitRel ↔ vertexOrbitRel.
  have hvert : ¬ vertexOrbitRel B W (ξ 0) (ξ' 0) := by
    intro ⟨σ, hσ_aut, hσ_eq⟩
    apply h
    refine ⟨σ, hσ_aut, ?_⟩
    intro i
    have : i = (0 : Fin 1) := Subsingleton.elim _ _
    rw [this]
    exact hσ_eq.symm
  obtain ⟨n, F, _hF_dec, hne⟩ :=
    rooted_profiles_separate_vertex_orbits B hB W hW htwin hvert
  refine ⟨n, F, inferInstance, ?_⟩
  -- simpleEvalAt B W F ξ = rootedProfile B W (ξ 0) F = same with ξ' 0.
  have h_unfold : ∀ ζ : Fin 1 → Fin T,
      simpleEvalAt B W F ζ = rootedProfile B W (ζ 0) F := by
    intro ζ
    unfold rootedProfile
    congr 1
    funext k
    have : k = (0 : Fin 1) := Subsingleton.elim _ _
    rw [this]
  rw [h_unfold ξ, h_unfold ξ']
  exact hne

/-- **Diagonal observable at K=1** — derived from rooted-profile separation.

For K=1, the diagonal observable `B(ξ 0, ξ 0) = B(ξ' 0, ξ' 0)` follows
from `tupleEquivSimple B W ξ ξ'` via:
1. `tupleEquivSimple` at K=1 ⟹ all rooted profiles agree at (ξ 0, ξ' 0).
2. Contrapositive of `rooted_profiles_separate_vertex_orbits` (proved
   modulo #77) ⟹ `vertexOrbitRel B W (ξ 0) (ξ' 0)`.
3. Vertex orbit relation gives `σ` automorphism with `σ (ξ 0) = ξ' 0`.
4. `B(ξ 0, ξ 0) = B(σ (ξ 0), σ (ξ 0)) = B(ξ' 0, ξ' 0)` by aut B-preservation.

**Status**: proved modulo #77 (closed_walk_profiles_separate, K=1 spectral
paper-root). Note this reduces `diagonal_observable_of_tupleEquivSimple`
at K=1 to a paper-root we already have (#77) rather than to the rank
theorem. -/
theorem diagonal_observable_K1 {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    {ξ ξ' : Fin 1 → Fin T}
    (h : tupleEquivSimple B W ξ ξ') :
    B (ξ 0) (ξ 0) = B (ξ' 0) (ξ' 0) := by
  -- Step 1: tupleEquivSimple → vertexOrbitRel via contrapositive of rooted_profiles_separate.
  by_contra h_ne
  -- Suppose B(ξ 0, ξ 0) ≠ B(ξ' 0, ξ' 0). Show this contradicts h.
  -- First derive vertexOrbitRel from h (negation of separation).
  have h_vert : vertexOrbitRel B W (ξ 0) (ξ' 0) := by
    by_contra h_no_vert
    obtain ⟨n, F, _hF_dec, hne⟩ :=
      rooted_profiles_separate_vertex_orbits B hB W hW htwin h_no_vert
    -- hne : rootedProfile B W (ξ 0) F ≠ rootedProfile B W (ξ' 0) F.
    -- But h says simpleEvalAt F ξ = simpleEvalAt F ξ' = rootedProfile.
    apply hne
    have h_unfold : ∀ ζ : Fin 1 → Fin T,
        simpleEvalAt B W F ζ = rootedProfile B W (ζ 0) F := by
      intro ζ
      unfold rootedProfile
      congr 1
      funext k
      have : k = (0 : Fin 1) := Subsingleton.elim _ _
      rw [this]
    rw [← h_unfold ξ, ← h_unfold ξ']
    exact h n F
  -- Step 2: derive B-equality from vertexOrbitRel.
  obtain ⟨σ, hσ_aut, hσ_eq⟩ := h_vert
  apply h_ne
  calc B (ξ 0) (ξ 0)
      = B (σ (ξ 0)) (σ (ξ 0)) := (hσ_aut.2 (ξ 0) (ξ 0)).symm
    _ = B (ξ' 0) (ξ' 0) := by rw [hσ_eq]

/-- **Diagonal observable** — general K version, derived from K=1 case
via `tupleEquivSimple_restrict_along`.

For each label position `a : Fin K`, fix the embedding `r : Fin 1 ↪ Fin K`
sending `0 ↦ a`. Restriction gives `tupleEquivSimple` at K=1 for the
single coordinate. Apply `diagonal_observable_K1` to conclude.

**Status**: proved modulo #77 (the K=1 spectral paper-root). This replaces
the earlier sorry-stub `diagonal_observable_of_tupleEquivSimple` that
was a placeholder pending the rank-theorem path. Routing through the
K=1 spectral chain (#77) is more direct than the rank theorem.

**Architectural consequence**: #79's diagonal observable now reduces
to #77 (K=1 spectral paper-root) rather than to a separate rank theorem.
This collapses two paper-roots into one.

**Downstream**: any consumer of `diagonal_observable_of_tupleEquivSimple`
(e.g., the n=0 loop bridge `multiLabeledEvalKLoop_n_zero_of_diag`)
inherits dependency on #77. -/
theorem diagonal_observable_of_tupleEquivSimple {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    {ξ ξ' : Fin K → Fin T}
    (h : tupleEquivSimple B W ξ ξ') :
    ∀ a : Fin K, B (ξ a) (ξ a) = B (ξ' a) (ξ' a) := by
  intro a
  -- Build embedding r : Fin 1 ↪ Fin K sending 0 ↦ a.
  let r : Fin 1 ↪ Fin K := ⟨fun _ => a, fun _ _ _ => Subsingleton.elim _ _⟩
  -- Restrict tupleEquivSimple along r.
  have h1 : tupleEquivSimple B W (ξ ∘ r) (ξ' ∘ r) :=
    tupleEquivSimple_restrict_along B W hB r h
  -- (ξ ∘ r) 0 = ξ a, (ξ' ∘ r) 0 = ξ' a.
  have h_K1 := diagonal_observable_K1 B hB W hW htwin h1
  -- h_K1 : B ((ξ ∘ r) 0) ((ξ ∘ r) 0) = B ((ξ' ∘ r) 0) ((ξ' ∘ r) 0)
  -- Simplify: (ξ ∘ r) 0 = ξ (r 0) = ξ a.
  show B (ξ a) (ξ a) = B (ξ' a) (ξ' a)
  exact h_K1


/-- **Lovász Lemma 2.5, reverse direction** (multi-equivalence ⟹ orbit),
*twin-free hypothesis*.

If `B` is twin-free (rows of `B` distinct: `i ≠ j → B i ≠ B j`) and
`ξ ξ'` agree on every multigraph evaluation, then they lie in the same
`(B, W)`-automorphism orbit.

**Proof strategy** (chain): multi-equivalence ⟹ simple-equivalence
(`tupleEquivSimple_of_tupleEquivMulti`, trivial direction) ⟹ orbit
(`tupleEquivSimple_implies_orbit`, the canonical sorry).

Closed modulo the canonical sorry on `tupleEquivSimple_implies_orbit`. -/
theorem tupleEquivMulti_implies_orbit {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    {ξ ξ' : Fin K → Fin T}
    (h : tupleEquivMulti B W ξ ξ') :
    ∃ σ : Equiv.Perm (Fin T),
      (∀ i, W (σ i) = W i) ∧ (∀ i j, B (σ i) (σ j) = B i j) ∧
      (∀ i, ξ' i = σ (ξ i)) :=
  tupleEquivSimple_implies_orbit B hB W hW htwin
    (tupleEquivSimple_of_tupleEquivMulti B W h)

/-! ### §4 — The bridge theorem (canonical sorry)

Stated abstractly: for any pair `ξ ξ'` such that ALL simple-graph
evaluations agree (the simple-graph `tupleEquiv` predicate), every
multigraph evaluation also agrees.

The hypothesis `h_simple` is the simple-graph version of `tupleEquiv`,
inlined here so this module needs no dependency on
`Graphon/MatrixDetermination.lean`. -/

/-- **Twin-free bridge** (corollary). Under twin-freeness, the bridge
follows by chaining through the orbit relation:

  `tupleEquivSimple` → orbit (via `tupleEquivSimple_implies_orbit`)
  → multi-eval-equality (via `multiLabeledEvalK_orbit_invariant`).

This avoids the `n+1` sorry of the general bridge. It does NOT
subsume `multiLabeledEvalK_tupleEquiv_invariant`: the latter must hold
for all `B` (including `B` with twins), while this version requires
twin-freeness.

**This is the RECOMMENDED reduction theorem** (per post-2026-05-12
architectural decision): downstream twin-free consumers should route
through THIS theorem (and hence the rank theorem) rather than the
general non-twin-free bridge at L1327.

**Dependency** (post-rank-theorem-refactor): this proof routes
through `tupleEquivSimple_implies_orbit`, which is now a thin wrapper
over `connection_matrix_rank_theorem` (the named canonical root).
Closing the rank theorem closes this reduction.

The earlier "self-cyclic" concern (about IH-free bijective case
needing multigraph diagonal extraction = the bridge) is moot now:
the rank theorem is the SINGLE primary root, and the bridge is
secondary / off-axis. -/
theorem multiLabeledEvalK_tupleEquiv_invariant_twinFree {T K n : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (M : MultiLabeledGraph K n)
    {ξ ξ' : Fin K → Fin T}
    (h : tupleEquivSimple B W ξ ξ') :
    multiLabeledEvalK K n M B W ξ = multiLabeledEvalK K n M B W ξ' := by
  -- Step 1: simple-equivalence ⟹ orbit (the canonical sorry).
  obtain ⟨σ, hW_eq, hB_eq, hξ_eq⟩ :=
    tupleEquivSimple_implies_orbit B hB W hW htwin h
  -- Step 2: orbit ⟹ multi-eval-equality (orbit-invariance, fully proved).
  exact multiLabeledEvalK_orbit_invariant B W M ⟨σ, hW_eq, hB_eq, hξ_eq⟩

end Graphon.Lovasz
