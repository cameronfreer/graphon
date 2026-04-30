/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Sym2
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

/-! ### §1 — Multigraph carrier -/

/-- **Lovász k-labeled multigraph** on `Fin (n + K)`. Edge multiplicity
function on `Sym2 (Fin (n + K))`. `multNoLoop` ensures no self-loops
(`mult s(x, x) = 0`), per Lovász §2 page 3. -/
structure MultiLabeledGraph (K n : ℕ) where
  mult : Sym2 (Fin (n + K)) → ℕ
  multNoLoop : ∀ x : Fin (n + K), mult s(x, x) = 0

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

/-! ### §3 — Disjoint-glue product (Lovász's F₁F₂) — STUB

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
  - **Cross** (one M₁-unlabeled, one M₂-unlabeled): 0.

Then `multiLabeledEvalK_glue`: evaluation of M₁.glue M₂ factors as
the product of evaluations.

**Stubbed below — implementation deferred** (~250 lines mirroring
`labeledEvalK_glue` at `MatrixDetermination.lean:5785`). -/

/-! ### §4 — The bridge theorem (canonical sorry)

Stated abstractly: for any pair `ξ ξ'` such that ALL simple-graph
evaluations agree (the simple-graph `tupleEquiv` predicate), every
multigraph evaluation also agrees.

The hypothesis `h_simple` is the simple-graph version of `tupleEquiv`,
inlined here so this module needs no dependency on
`Graphon/MatrixDetermination.lean`. -/

/-- **The multigraph bridge — canonical sorry.**

Every multigraph evaluation descends through the simple-graph version
of `tupleEquiv`. This is the Lovász §3 content (Theorem 2.2 / Lemma 2.5)
translated to our framework: simple-graph `tupleEquiv` ⟹ all
multigraph evaluations agree.

**Hypothesis form** (`h_simple`): for every level-K simple graph
`F : SimpleGraph (Fin (n' + K))` (with any `n'` unlabeled vertices),
the simple-graph evaluations at `ξ` and `ξ'` agree. This is the
inlined definition of `tupleEquiv B W ξ ξ'`.

**Status**: stub. Future proof requires the algebra-of-graphs
infrastructure (§2 + §3 above), totalling ~300-500 lines. Stage in
this module; do not pollute `MatrixDetermination.lean`. -/
theorem multiLabeledEvalK_tupleEquiv_invariant {T K n : ℕ}
    (B : Fin T → Fin T → ℝ) (_hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (M : MultiLabeledGraph K n)
    {ξ ξ' : Fin K → Fin T}
    (_h_simple : ∀ (n' : ℕ) (F : SimpleGraph (Fin (n' + K)))
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
  sorry

end Graphon.Lovasz
