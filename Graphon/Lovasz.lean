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
