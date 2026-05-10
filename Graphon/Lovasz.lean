/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
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
* **Claim 4.2** (`tupleEquivSimple_extend`) — stated, sorry'd
  (depends on the `coeffRestrict_equiv` / functional-span chain).
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

/-- **Claim 4.2 — Extension lemma**
(Lovász TR-2004-82 §4, p. 6, "second paragraph").

If `ξ ξ' : Fin k → Fin T` are simple-equivalent at level `k`, then for
every level-`(k+1)` extension `μ` of `ξ` (`restrictTuple μ = ξ`) there
exists a level-`(k+1)` extension `ν` of `ξ'` (`restrictTuple ν = ξ'`)
such that `μ` and `ν` are simple-equivalent at level `k+1`.

**Proof strategy** (Lovász): factor `coeffRestrict B W μ ξ` (the
`W`-weighted sum over `t : Fin T` extending `ξ` to a copy of `μ`'s
equivalence class at level `k+1`) as a class function, and argue
via `functional_span_zero` that the coefficient extends to `ξ'`. The
full chain is `tupleEquiv_extend` (`MatrixDetermination.lean:5110`)
which depends on `coeffRestrict_equiv` (the IH-free Claim-4.2 core).

**Status**: sorry. The full proof is ~1000 lines of paper-faithful
algebraic work that lives in `MatrixDetermination.lean`. Adapting it
here requires also porting `coeffRestrict_equiv`, `functional_span_zero`,
and the product-trace identity — out of scope for this scaffolding pass. -/
theorem tupleEquivSimple_extend {T k : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (_hB : ∀ i j, B i j = B j i)
    {ξ ξ' : Fin k → Fin T}
    (_h : tupleEquivSimple B W ξ ξ')
    (μ : Fin (k + 1) → Fin T) (_hμ : restrictTuple μ = ξ) :
    ∃ ν : Fin (k + 1) → Fin T,
      restrictTuple ν = ξ' ∧ tupleEquivSimple B W μ ν := by
  sorry

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

**Status**: proved modulo (i) the Claim 4.2 sorry
(`tupleEquivSimple_extend`), and (ii) the single architectural sorry in the
non-surjective branch of the strong induction (neither `α` nor `ξ`
surjective). Claims 4.1, 4.3, 4.4 and `tupleEquivSimple_ext_eq_of_surj` are
all closed inline. The wiring is paper-faithful and matches the structure
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
  -- Convert the existential conclusion to `tupleOrbitRel` form.
  suffices hOrbit : tupleOrbitRel B W ξ ξ' by
    obtain ⟨σ, ⟨hW_eq, hB_eq⟩, hξ_eq⟩ := hOrbit
    exact ⟨σ, hW_eq, hB_eq, hξ_eq⟩
  -- Strong induction on K.
  suffices strong : ∀ (m : ℕ) (ξ ξ' : Fin m → Fin T),
      tupleEquivSimple B W ξ ξ' → tupleOrbitRel B W ξ ξ' from strong K ξ ξ' h
  intro m
  refine @Nat.strongRecOn
    (fun j => ∀ (ξ ξ' : Fin j → Fin T),
      tupleEquivSimple B W ξ ξ' → tupleOrbitRel B W ξ ξ')
    m fun m IH_strong => ?_
  intro ξ ξ' h
  rcases m with _ | k
  · -- m = 0: trivially, σ = refl (identity) works.
    exact ⟨Equiv.refl _, ⟨fun _ => rfl, fun _ _ => rfl⟩, nofun⟩
  · -- m = k + 1. IH supplies orbit relation at every level < k + 1.
    have IH : ∀ {ξ' ψ' : Fin k → Fin T},
        tupleEquivSimple B W ξ' ψ' → tupleOrbitRel B W ξ' ψ' :=
      fun {ξ' ψ'} h' => IH_strong k (Nat.lt_succ_self k) ξ' ψ' h'
    -- **Step 1**: restrict to level k, apply IH.
    obtain ⟨σ, hσ_aut, hσ_conj⟩ :=
      IH (tupleEquivSimple_restrict B W hB h)
    -- **Step 2**: σ⁻¹ is also a weighted automorphism.
    have hσs : IsWeightedAutomorphism B W σ.symm := by
      refine ⟨fun i => ?_, fun i j => ?_⟩
      · have := (hσ_aut.1 (σ.symm i)).symm
        rwa [σ.apply_symm_apply] at this
      · have := (hσ_aut.2 (σ.symm i) (σ.symm j)).symm
        rwa [σ.apply_symm_apply, σ.apply_symm_apply] at this
    -- **Step 3**: normalize ξ' by σ⁻¹.
    have h' : tupleEquivSimple B W ξ (σ.symm ∘ ξ') := by
      -- ξ ≃ ξ' and ξ' = σ ∘ (σ⁻¹ ∘ ξ'), so ξ ≃ σ⁻¹ ∘ ξ' via orbit invariance.
      intro n F hdec
      rw [h n F]
      -- Now goal: simple-eval at ξ' = simple-eval at σ⁻¹ ∘ ξ'.
      -- σ⁻¹ ∘ ξ' and ξ' are orbit-related via σ (σ takes σ⁻¹ ∘ ξ' to ξ').
      have hrel : tupleOrbitRel B W (σ.symm ∘ ξ') ξ' :=
        ⟨σ, hσ_aut, fun i => by
          simp only [Function.comp_apply, σ.apply_symm_apply]⟩
      exact (tupleEquivSimple_of_tupleOrbitRel B W hrel n F).symm
    -- **Step 4**: the first k coordinates of ξ and σ⁻¹ ∘ ξ' now agree.
    have hbase : restrictTuple (σ.symm ∘ ξ') = restrictTuple ξ := by
      funext i
      simp only [restrictTuple, Function.comp]
      have hi := hσ_conj i
      simp only [restrictTuple] at hi
      rw [hi, σ.symm_apply_apply]
    -- **Step 5**: express both as Fin.snoc of α := restrictTuple ξ.
    set α := restrictTuple ξ with hα_def
    have ha : ξ = Fin.snoc α (ξ (Fin.last k)) := by
      ext i
      by_cases hi : (i : ℕ) < k
      · rw [show i = (⟨i, hi⟩ : Fin k).castSucc from Fin.ext rfl,
            Fin.snoc_castSucc]
        rfl
      · rw [show i = Fin.last k from Fin.ext (show i.val = k by omega),
            Fin.snoc_last]
    have hb : σ.symm ∘ ξ' = Fin.snoc α ((σ.symm ∘ ξ') (Fin.last k)) := by
      ext i
      by_cases hi : (i : ℕ) < k
      · rw [show i = (⟨i, hi⟩ : Fin k).castSucc from Fin.ext rfl,
            Fin.snoc_castSucc, ← hbase]
        rfl
      · rw [show i = Fin.last k from Fin.ext (show i.val = k by omega),
            Fin.snoc_last]
    rw [ha, hb] at h'
    -- **Step 6**: case split on surjectivity of α.
    by_cases hα_surj : Function.Surjective α
    · -- Surjective base: ext-eq-of-surj forces the last coordinates to match.
      have hab :=
        tupleEquivSimple_ext_eq_of_surj B W hB htwin hα_surj h'
      refine ⟨σ, hσ_aut, fun i => ?_⟩
      have : (σ.symm ∘ ξ') i = ξ i :=
        congr_fun (hb.trans (hab ▸ ha.symm)) i
      rwa [Function.comp_apply, Equiv.symm_apply_eq] at this
    · -- α non-surjective.
      by_cases hξ_surj : Function.Surjective ξ
      · -- ξ surjective: apply Claim 4.4 (T ≤ k+1, so T-1 < k+1).
        have hT1_lt : T - 1 < k + 1 := by
          have := Fintype.card_le_of_surjective ξ hξ_surj
          simp only [Fintype.card_fin] at this
          omega
        have IH_T1 : ∀ {ξ' ψ' : Fin (T - 1) → Fin T},
            tupleEquivSimple B W ξ' ψ' → tupleOrbitRel B W ξ' ψ' :=
          fun {ξ' ψ'} h' => IH_strong (T - 1) hT1_lt ξ' ψ' h'
        exact tupleEquivSimple_surjective_case B W hW hB htwin IH_T1 ξ ξ' hξ_surj h
      · -- **Architectural sorry**: neither α nor ξ surjective. Lovász's
        -- "extend-and-recurse" plan requires Claim 4.2 + a well-founded
        -- induction refactor on `(deficit, size)` — see the lengthy
        -- comment at `MatrixDetermination.lean:10938` for the full
        -- discussion of why strong induction on size alone cannot close
        -- this branch.
        sorry

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

/-- **The multigraph bridge — canonical sorry.**

Every multigraph evaluation descends through the simple-graph version
of `tupleEquiv`. This is the Lovász §3 content (Theorem 2.2 / Lemma 2.5)
translated to our framework: simple-graph `tupleEquiv` ⟹ all
multigraph evaluations agree.

**Hypothesis form** (`h_simple`): for every level-K simple graph
`F : SimpleGraph (Fin (n' + K))` (with any `n'` unlabeled vertices),
the simple-graph evaluations at `ξ` and `ξ'` agree. This is the
inlined definition of `tupleEquiv B W ξ ξ'`.

**Status**: partial — `n = 0` case dispatched via
`multiLabeledEvalK_tupleEquiv_invariant_n_zero`. The general `n` case
remains sorry'd. The natural induction on `n` via `promote_unfold`
needs a "lifted simple-equivalence" hypothesis at level `K + 1`, which
does NOT follow from the level-`K` `h_simple` alone (a level-(K+1)
graph constrained at the new label position does not factor through
a free σ-sum). The connection-matrix / idempotent-decomposition
argument from Lovász §3 is the standard way to close this. -/
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
  | n + 1, _M =>
    -- The n+1 case requires either (i) a level-(K+1) lift of `h_simple`,
    -- or (ii) the connection-matrix idempotent-decomposition argument
    -- from Lovász TR-2004-82 §3. Neither is in scope yet.
    sorry

/-- **Twin-free bridge** (corollary). Under twin-freeness, the bridge
follows by chaining through the orbit relation:

  `tupleEquivSimple` → orbit (via `tupleEquivSimple_implies_orbit`)
  → multi-eval-equality (via `multiLabeledEvalK_orbit_invariant`).

This avoids the `n+1` sorry of the general bridge. It does NOT
subsume `multiLabeledEvalK_tupleEquiv_invariant`: the latter must hold
for all `B` (including `B` with twins), while this version requires
twin-freeness.

Closed modulo the canonical `tupleEquivSimple_implies_orbit` sorry. -/
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
