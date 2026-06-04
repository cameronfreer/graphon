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
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Lagrange
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

/-- **Named spectral theorem for #77** (REFUTED 2026-05-18).

**REFUTATION**: vertices 1 and 5 in the 9-vertex "double-pin tree"
(scripts/spectral_orbit_validation.py) have identical diagonal
moments [1, 0, 2, 0, 6, 0, ...] but |Aut| = 1 (different orbits).
The graph IS twin-free. So this conjecture is FALSE.

The statement remains here as a sorry'd FALSE conjecture for
documentation purposes. It should NOT be assumed in downstream
proofs. The correct route to vertex_orbit_of_closed_walks_eq
(if that conjecture itself survives) requires the FULL rooted
simple-graph family (Lovász §3 rank theorem), NOT just closed
walks / diagonal moments.

**Original conjecture** (DISPROVEN):
If two vertices i, j have matching diagonal entries `(S^m)[i, i] = (S^m)[j, j]`
for all m, under twin-free B + W > 0, then there exists a (B, W)-aut σ
mapping i to j.

**Counterexample**: double-pin tree T = 9:
  edges: (0,1), (1,2), (2,3), (3,7) — arm 1
         (0,4), (4,5), (5,6), (4,8) — arm 2 (extra leaf at 4)
  Vertices 1, 5 are cospectral (equal moments) but not orbit-related.

**Architectural impact**: any downstream Lemma proved via this
sorry'd conjecture is on shaky ground. Specifically affected:
- closed_walk_profiles_separate_vertex_orbits (Lovasz.lean #77)
- rooted_profiles_separate_vertex_orbits (proved via the above)
- diagonal_observable_K1 + _of_tupleEquivSimple (proved via the above)

The "rooted_profiles_separate" THEOREM is still TRUE (Lovász Lemma 2.4
K=1) — just its proof route via closed walks is invalid. Need to
re-prove via the FULL rooted simple-graph family. -/
theorem same_diag_powers_imp_vertex_orbit {T : ℕ}
    (B : Fin T → Fin T → ℝ) (_hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (_hW : ∀ i, 0 < W i)
    (_htwin : ∀ i j, i ≠ j → B i ≠ B j)
    {i j : Fin T}
    (_h_diag : ∀ m : ℕ, symAdjIter B W m i i = symAdjIter B W m j j) :
    ∃ σ : Equiv.Perm (Fin T),
      (∀ k, W (σ k) = W k) ∧ (∀ k l, B (σ k) (σ l) = B k l) ∧ σ i = j := by
  sorry

/-! ### Rank-language form of the easy direction: `dim V ≤ #orbits`

Foothold for the global `multiEval_separates_orbits` theorem, kept here (not in
`Lovasz.lean`) so the linear-algebra imports do not pollute that file. The
multigraph-eval span, as a submodule of `(Fin K → Fin T) → ℝ`, has dimension at
most the number of `(B, W)`-orbits of `K`-tuples — because it sits inside the
aut-invariant subspace, which injects into functions on the orbit quotient. The
reverse `#orbits ≤ dim V` (separation) is the hard residue. -/

/-- The multigraph-eval span as a submodule of `(Fin K → Fin T) → ℝ`. -/
noncomputable def multiSpanSubmodule {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) : Submodule ℝ ((Fin K → Fin T) → ℝ) :=
  Submodule.span ℝ (Set.range (fun p : Σ n, MultiLabeledGraph K n =>
    (fun ξ => multiLabeledEvalK K p.1 p.2 B W ξ)))

/-- The aut-invariant functions, as a submodule. -/
def autInvariantSubmodule {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) : Submodule ℝ ((Fin K → Fin T) → ℝ) where
  carrier := {f | ∀ σ : Equiv.Perm (Fin T), IsWeightedAutomorphism B W σ →
    ∀ ξ, f (σ ∘ ξ) = f ξ}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := fun {a b} ha hb σ hσ ξ => by
    simp only [Pi.add_apply]; rw [ha σ hσ ξ, hb σ hσ ξ]
  smul_mem' := fun c a ha σ hσ ξ => by
    simp only [Pi.smul_apply, smul_eq_mul]; rw [ha σ hσ ξ]

/-- The span lies in the aut-invariant subspace (submodule form of
`InTupleMultiEvalSpan.aut_invariant`; proved from the generators directly). -/
theorem multiSpan_le_autInvariant {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) : multiSpanSubmodule K B W ≤ autInvariantSubmodule K B W := by
  unfold multiSpanSubmodule
  refine Submodule.span_le.2 ?_
  rintro f ⟨p, rfl⟩ σ hσ ξ
  exact multiLabeledEvalK_aut_invariant B W p.2 σ hσ.1 hσ.2 ξ

/-- **Easy rank inequality `dim V ≤ #orbits`** (foothold for the global theorem):
the multigraph-eval span has dimension at most the number of `(B, W)`-orbits of
`K`-tuples. -/
theorem finrank_multiSpan_le_card_orbitClass {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) :
    Module.finrank ℝ (multiSpanSubmodule K B W) ≤ Nat.card (OrbitClass T K B W) := by
  -- `Nat.card` in the statement needs no `Fintype` instance; supply one inside the proof.
  classical
  haveI : Fintype (OrbitClass T K B W) := Quotient.fintype (tupleOrbitSetoid B W K)
  -- Linear injection  V_multi ↪ (OrbitClass → ℝ),  f ↦ (q ↦ f (out q)).
  let L : multiSpanSubmodule K B W →ₗ[ℝ] (OrbitClass T K B W → ℝ) :=
    { toFun := fun f q => f.1 (Quotient.out q)
      map_add' := fun f g => rfl
      map_smul' := fun c f => rfl }
  have hLinj : Function.Injective L := by
    intro f g hfg
    apply Subtype.ext
    funext ξ
    have hconst : ∀ (p : (Fin K → Fin T) → ℝ), p ∈ autInvariantSubmodule K B W →
        p ξ = p (Quotient.out (Quotient.mk (tupleOrbitSetoid B W K) ξ)) := by
      intro p hp
      obtain ⟨σ, hσ_aut, hσ_eq⟩ := Quotient.mk_out (s := tupleOrbitSetoid B W K) ξ
      have hcomp : (σ ∘ Quotient.out (Quotient.mk (tupleOrbitSetoid B W K) ξ)) = ξ := by
        funext i; exact (hσ_eq i).symm
      calc p ξ
          = p (σ ∘ Quotient.out (Quotient.mk (tupleOrbitSetoid B W K) ξ)) := by rw [hcomp]
        _ = p (Quotient.out (Quotient.mk (tupleOrbitSetoid B W K) ξ)) := hp σ hσ_aut _
    have hf := hconst f.1 (multiSpan_le_autInvariant K B W f.2)
    have hg := hconst g.1 (multiSpan_le_autInvariant K B W g.2)
    rw [hf, hg]
    exact congr_fun hfg (Quotient.mk (tupleOrbitSetoid B W K) ξ)
  rw [Nat.card_eq_fintype_card, ← Module.finrank_pi (ι := OrbitClass T K B W) ℝ]
  exact LinearMap.finrank_le_finrank_of_injective hLinj

/-! ### Route A scaffolding: the reverse rank inequality `#orbits ≤ dim V`

The hard direction (separation), via the Lovász connection-matrix / Gram argument. We work on
the **orbit quotient** (`OrbitClass`), set up a positive-weighted inner product (`orbitInner`,
with per-class weight `orbitWeight` = the class total of tuple weights, hence strictly positive
under `W > 0`), and state the full-rank residue as the single paper-root, deriving the rank
equality. The genuine content — the orbit connection/Gram matrix is nonsingular — is
`card_orbitClass_le_finrank_multiSpan`. -/

/-- `DecidableEq` / `Fintype` for `OrbitClass`: the orbit relation involves real-number
equalities (noncomputable), so we supply these classically. Provided explicitly with the
`OrbitClass` head because auto-synthesis does not unfold the def. -/
noncomputable instance instDecidableEqOrbitQuot {T K : ℕ} {B : Fin T → Fin T → ℝ}
    {W : Fin T → ℝ} : DecidableEq (Quotient (tupleOrbitSetoid B W K)) := Classical.decEq _

noncomputable instance instDecidableEqOrbitClass {T K : ℕ} {B : Fin T → Fin T → ℝ}
    {W : Fin T → ℝ} : DecidableEq (OrbitClass T K B W) := Classical.decEq _

noncomputable instance instFintypeOrbitClass {T K : ℕ} {B : Fin T → Fin T → ℝ}
    {W : Fin T → ℝ} : Fintype (OrbitClass T K B W) :=
  letI : DecidableRel (tupleOrbitSetoid B W K).r := fun _ _ => Classical.propDecidable _
  Quotient.fintype (tupleOrbitSetoid B W K)

/-- **Per-orbit weight**: the total tuple weight of an orbit class,
`orbitWeight q = ∑_{ξ ∈ q} ∏_a W (ξ a)`. The class total (not a representative value) keeps
positivity transparent. -/
noncomputable def orbitWeight {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (q : OrbitClass T K B W) : ℝ :=
  ∑ ξ ∈ Finset.univ.filter (fun ξ : Fin K → Fin T =>
    Quotient.mk (tupleOrbitSetoid B W K) ξ = q), ∏ a, W (ξ a)

/-- **First formal target**: orbit weights are strictly positive (each fiber is nonempty —
contains `q.out` — and every tuple weight `∏ W` is positive). -/
lemma orbitWeight_pos {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ) {W : Fin T → ℝ}
    (hW : ∀ i, 0 < W i) (q : OrbitClass T K B W) : 0 < orbitWeight K B W q := by
  unfold orbitWeight
  refine Finset.sum_pos (fun ξ _ => Finset.prod_pos fun i _ => hW (ξ i)) ?_
  exact ⟨Quotient.out q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Quotient.out_eq q⟩⟩

/-- **Weighted inner product on orbit-class functions**:
`⟪f, g⟫ = ∑_q orbitWeight q · f q · g q`. Positive-definite since each `orbitWeight q > 0`. -/
noncomputable def orbitInner {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (f g : OrbitClass T K B W → ℝ) : ℝ :=
  ∑ q, orbitWeight K B W q * f q * g q

/-- `orbitInner` is symmetric. -/
lemma orbitInner_comm {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (f g : OrbitClass T K B W → ℝ) : orbitInner K B W f g = orbitInner K B W g f := by
  unfold orbitInner; refine Finset.sum_congr rfl fun q _ => ?_; ring

/-- `⟪f, f⟫ ≥ 0`. -/
lemma orbitInner_self_nonneg {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ) {W : Fin T → ℝ}
    (hW : ∀ i, 0 < W i) (f : OrbitClass T K B W → ℝ) : 0 ≤ orbitInner K B W f f := by
  unfold orbitInner
  refine Finset.sum_nonneg fun q _ => ?_
  rw [mul_assoc]
  exact mul_nonneg (orbitWeight_pos K B hW q).le (mul_self_nonneg _)

/-- **Positive-definiteness** of `orbitInner` (uses `orbitWeight_pos`). -/
lemma orbitInner_self_eq_zero_iff {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ) {W : Fin T → ℝ}
    (hW : ∀ i, 0 < W i) (f : OrbitClass T K B W → ℝ) :
    orbitInner K B W f f = 0 ↔ f = 0 := by
  constructor
  · intro h
    funext q
    have hterm : ∀ p ∈ (Finset.univ : Finset (OrbitClass T K B W)),
        0 ≤ orbitWeight K B W p * f p * f p := by
      intro p _
      rw [mul_assoc]; exact mul_nonneg (orbitWeight_pos K B hW p).le (mul_self_nonneg _)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 h q (Finset.mem_univ q)
    rw [mul_assoc] at hz
    rcases mul_eq_zero.1 hz with hp | hf
    · exact absurd hp (ne_of_gt (orbitWeight_pos K B hW q))
    · exact mul_self_eq_zero.1 hf
  · intro h; subst h; simp [orbitInner]

/-- `orbitInner` packaged as a bilinear form (for the dual/rank argument). -/
noncomputable def orbitInnerBil {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    (OrbitClass T K B W → ℝ) →ₗ[ℝ] (OrbitClass T K B W → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (orbitInner K B W)
    (fun h₁ h₂ g => by
      simp only [orbitInner, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_; simp only [Pi.add_apply]; ring)
    (fun c h g => by
      simp only [orbitInner, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_; simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun h g₁ g₂ => by
      simp only [orbitInner, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_; simp only [Pi.add_apply]; ring)
    (fun c h g => by
      simp only [orbitInner, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_; simp only [Pi.smul_apply, smul_eq_mul]; ring)

@[simp] lemma orbitInnerBil_apply {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (h g : OrbitClass T K B W → ℝ) : orbitInnerBil K B W h g = orbitInner K B W h g := rfl

/-! #### Descended-eval algebra on orbit classes (the explicit layer before full rank) -/

/-- **Descended multigraph evaluation** on orbit classes: `multiLabeledEvalK M` is
orbit-invariant (`multiLabeledEvalK_orbit_invariant`), so it factors through `OrbitClass`. -/
noncomputable def multiEvalOnOrbit {T : ℕ} (K n : ℕ) (M : MultiLabeledGraph K n)
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) : OrbitClass T K B W → ℝ :=
  Quotient.lift (s := tupleOrbitSetoid B W K) (fun ξ => multiLabeledEvalK K n M B W ξ)
    (fun ξ ξ' h => by
      obtain ⟨σ, ⟨hWσ, hBσ⟩, hξ⟩ := h
      exact multiLabeledEvalK_orbit_invariant B W M ⟨σ, hWσ, hBσ, hξ⟩)

@[simp] lemma multiEvalOnOrbit_mk {T : ℕ} (K n : ℕ) (M : MultiLabeledGraph K n)
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (ξ : Fin K → Fin T) :
    multiEvalOnOrbit K n M B W (Quotient.mk (tupleOrbitSetoid B W K) ξ) =
      multiLabeledEvalK K n M B W ξ := rfl

/-- **Glue ↦ product** for descended evals (via `multiLabeledEvalK_glue`): the descended
evals form a commutative algebra on `OrbitClass → ℝ`. -/
theorem multiEvalOnOrbit_glue {T K n₁ n₂ : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (M₁ : MultiLabeledGraph K n₁) (M₂ : MultiLabeledGraph K n₂) (q : OrbitClass T K B W) :
    multiEvalOnOrbit K (n₁ + n₂) (M₁.glue M₂) B W q =
      multiEvalOnOrbit K n₁ M₁ B W q * multiEvalOnOrbit K n₂ M₂ B W q := by
  induction q using Quotient.ind with
  | _ ξ => exact multiLabeledEvalK_glue B hB W M₁ M₂ ξ

/-- **Gram = glue** identity (FLS connection-matrix Gram entry). The orbit inner
product of two descended evals collapses to a *single* descended evaluation of the
glued multigraph against `1`:
`⟨ev M₁, ev M₂⟩ = ⟨1, ev (M₁.glue M₂)⟩`. Immediate from `multiEvalOnOrbit_glue`
(glue ↦ pointwise product) and the definition of `orbitInner`. This is the first
slice of the FLS PSD-rank proof of `connectionMatrix_full_rank`: it identifies the
Gram matrix of the eval vectors with the single-row data `q ↦ ⟨1, ev M q⟩`. -/
theorem orbitInner_eval_eval {T K n₁ n₂ : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (M₁ : MultiLabeledGraph K n₁) (M₂ : MultiLabeledGraph K n₂) :
    orbitInner K B W (multiEvalOnOrbit K n₁ M₁ B W) (multiEvalOnOrbit K n₂ M₂ B W)
      = orbitInner K B W 1 (multiEvalOnOrbit K (n₁ + n₂) (M₁.glue M₂) B W) := by
  unfold orbitInner
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [multiEvalOnOrbit_glue B hB W M₁ M₂ q]
  simp only [Pi.one_apply]
  ring

/-- The span of the descended evals inside `OrbitClass → ℝ`. -/
noncomputable def multiOrbitSpan {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) : Submodule ℝ (OrbitClass T K B W → ℝ) :=
  Submodule.span ℝ (Set.range (fun p : Σ n, MultiLabeledGraph K n =>
    multiEvalOnOrbit K p.1 p.2 B W))

/-- The empty graph descends to the constant function `1`. -/
lemma multiEvalOnOrbit_one {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    multiEvalOnOrbit K 0 (MultiLabeledGraph.empty K 0) B W = (1 : OrbitClass T K B W → ℝ) := by
  funext q
  induction q using Quotient.ind with
  | _ ξ =>
    show multiLabeledEvalK K 0 (MultiLabeledGraph.empty K 0) B W ξ = 1
    rw [multiLabeledEvalK_empty, Fintype.sum_unique, Fin.prod_univ_zero]

/-- `1 ∈ multiOrbitSpan`. -/
lemma one_mem_multiOrbitSpan {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    (1 : OrbitClass T K B W → ℝ) ∈ multiOrbitSpan K B W := by
  rw [← multiEvalOnOrbit_one K B W]
  exact Submodule.subset_span ⟨⟨0, MultiLabeledGraph.empty K 0⟩, rfl⟩

/-- **Product closure** of `multiOrbitSpan` (the descended `.mul`, via
`multiEvalOnOrbit_glue`): the descended evals form a unital subalgebra. -/
lemma multiOrbitSpan_mul_le {T K : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) :
    multiOrbitSpan K B W * multiOrbitSpan K B W ≤ multiOrbitSpan K B W := by
  rw [multiOrbitSpan, Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨p, rfl⟩, _, ⟨p', rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨⟨p.1 + p'.1, p.2.glue p'.2⟩, ?_⟩
  funext q
  exact multiEvalOnOrbit_glue B hB W p.2 p'.2 q

/-- **Signed-measure moment problem** — THE single internal paper-root, in the
cleanest finite form: a *nonzero* signed measure `μ` on the orbit classes has a
nonzero rooted-multigraph moment `∑_q μ q · multiEvalOnOrbit M q` for some `M`.

Equivalent to `fls_orthogonal_zero` (orthogonality) via the positive reweighting
`μ q = orbitWeight q · h q` (`orbitWeight > 0`), hence to `connectionMatrix_full_rank`.
This is the genuine FLS PSD-rank target: nondegeneracy of the multigraph-moment map
on signed orbit-class measures, under symmetric `B`, positive `W`, twin-free `B`.

Falsified non-routes (do not attempt): simple-graph separation (downstream/cyclic)
and the 1-WL `refineRel`/`stableSetoid` tower (1-WL ⊊ orbits; Frucht; fractional
automorphisms ≠ automorphisms). To be proved via the full rooted-multigraph
hierarchy. SORRY (paper-root). -/
theorem signed_orbit_measure_has_nonzero_moment {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j) (μ : OrbitClass T K B W → ℝ) (hμ : μ ≠ 0) :
    ∃ (n : ℕ) (M : MultiLabeledGraph K n),
      (∑ q, μ q * multiEvalOnOrbit K n M B W q) ≠ 0 := by
  sorry

/-- **FLS orthogonality vanishing** — now a wrapper over the moment-problem root
`signed_orbit_measure_has_nonzero_moment` via the positive reweighting
`μ q = orbitWeight q · h q`. A function orthogonal to every descended eval is `0`. -/
theorem fls_orthogonal_zero {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (hW : ∀ i, 0 < W i) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (h : OrbitClass T K B W → ℝ)
    (horth : ∀ (n : ℕ) (M : MultiLabeledGraph K n),
      orbitInner K B W h (multiEvalOnOrbit K n M B W) = 0) : h = 0 := by
  by_contra hne
  have hμ : (fun q => orbitWeight K B W q * h q) ≠ 0 := by
    intro hμ0
    refine hne (funext fun q => ?_)
    have hq : orbitWeight K B W q * h q = 0 := congrFun hμ0 q
    exact (mul_eq_zero.mp hq).resolve_left (orbitWeight_pos K B hW q).ne'
  obtain ⟨n, M, hM⟩ := signed_orbit_measure_has_nonzero_moment K B W hB hW htwin _ hμ
  apply hM
  show orbitInner K B W h (multiEvalOnOrbit K n M B W) = 0
  exact horth n M

/-- **Positive Gram self-test** (contrapositive of `fls_orthogonal_zero`, the
construction target): a nonzero orbit-class function has a nonzero `orbitInner`
against some descended multigraph evaluation. -/
theorem exists_positive_gram_test {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (hW : ∀ i, 0 < W i) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (h : OrbitClass T K B W → ℝ) (hne : h ≠ 0) :
    ∃ (n : ℕ) (M : MultiLabeledGraph K n),
      orbitInner K B W h (multiEvalOnOrbit K n M B W) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  exact hne (fls_orthogonal_zero K B W hB hW htwin h hcon)

/-- **Orthogonality ⟹ full rank** (the bounded wrapper, PROVED). If no nonzero
orbit-class function is orthogonal to all descended evals, the evals span
everything. Via the dual-pairing map `Ψ : h ↦ ⟨h, ·⟩|_{multiOrbitSpan}`: its kernel
is the orthogonal complement (`= 0` by hypothesis), so `Ψ` is injective, giving
`#orbits = finrank (OrbitClass → ℝ) ≤ finrank (Dual multiOrbitSpan) = finrank
multiOrbitSpan`; with the easy reverse `≤` this forces `multiOrbitSpan = ⊤`. -/
theorem connectionMatrix_full_rank_of_orthogonal {T K : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ)
    (horth0 : ∀ h : OrbitClass T K B W → ℝ,
      (∀ (n : ℕ) (M : MultiLabeledGraph K n),
        orbitInner K B W h (multiEvalOnOrbit K n M B W) = 0) → h = 0) :
    multiOrbitSpan K B W = ⊤ := by
  classical
  set Ψ : (OrbitClass T K B W → ℝ) →ₗ[ℝ] Module.Dual ℝ (multiOrbitSpan K B W) :=
    (multiOrbitSpan K B W).subtype.dualMap ∘ₗ orbitInnerBil K B W with hΨ
  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro h hh
    refine horth0 h fun n M => ?_
    have hc := LinearMap.congr_fun hh
      (⟨multiEvalOnOrbit K n M B W, Submodule.subset_span ⟨⟨n, M⟩, rfl⟩⟩ :
        multiOrbitSpan K B W)
    simpa only [hΨ, LinearMap.comp_apply, LinearMap.dualMap_apply, Submodule.subtype_apply,
      orbitInnerBil_apply, LinearMap.zero_apply] using hc
  have hle1 : Nat.card (OrbitClass T K B W) ≤ Module.finrank ℝ (multiOrbitSpan K B W) := by
    have h1 : Module.finrank ℝ (OrbitClass T K B W → ℝ)
        ≤ Module.finrank ℝ (Module.Dual ℝ (multiOrbitSpan K B W)) :=
      LinearMap.finrank_le_finrank_of_injective hΨinj
    rw [Subspace.dual_finrank_eq] at h1
    rw [Nat.card_eq_fintype_card, ← Module.finrank_pi (ι := OrbitClass T K B W) ℝ]
    exact h1
  have hle2 : Module.finrank ℝ (multiOrbitSpan K B W) ≤ Nat.card (OrbitClass T K B W) := by
    rw [Nat.card_eq_fintype_card, ← Module.finrank_pi (ι := OrbitClass T K B W) ℝ]
    exact Submodule.finrank_le _
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [Module.finrank_pi (ι := OrbitClass T K B W) ℝ, ← Nat.card_eq_fintype_card]
  exact le_antisymm hle2 hle1

/-- **Connection-matrix full rank** — `multiOrbitSpan K B W = ⊤`, in Lovász/FLS
rank language; now a corollary of the single internal paper-root
`fls_orthogonal_zero` via `connectionMatrix_full_rank_of_orthogonal`. Equivalent
(via `multiOrbitSpan_eq_top_iff_separates`) to `multiEvalOnOrbit_separates`. -/
theorem connectionMatrix_full_rank {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (hW : ∀ i, 0 < W i) (htwin : ∀ i j, i ≠ j → B i ≠ B j) :
    multiOrbitSpan K B W = ⊤ :=
  connectionMatrix_full_rank_of_orthogonal B W
    (fun h horth => fls_orthogonal_zero K B W hB hW htwin h horth)

/-- The signed measure `μ` on orbit classes has all rooted-multigraph moments zero. -/
def allMomentsZero {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (μ : OrbitClass T K B W → ℝ) : Prop :=
  ∀ (n : ℕ) (M : MultiLabeledGraph K n), (∑ q, μ q * multiEvalOnOrbit K n M B W q) = 0

/-- **All moments vanish ⟺ `μ` is (plain-pairing) orthogonal to `multiOrbitSpan`.**
Equates the moment condition with orthogonality to the descended-eval span (the
generators are the evals; closed under the span operations). -/
theorem allMomentsZero_iff_orthogonal {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (μ : OrbitClass T K B W → ℝ) :
    allMomentsZero K B W μ ↔ ∀ s ∈ multiOrbitSpan K B W, (∑ q, μ q * s q) = 0 := by
  constructor
  · intro hall s hs
    induction hs using Submodule.span_induction with
    | mem x hx => obtain ⟨⟨n, M⟩, rfl⟩ := hx; exact hall n M
    | zero => simp
    | add x y _ _ ihx ihy =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ihx, ihy, add_zero]
    | smul a x _ ih =>
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [show (∑ q, μ q * (a * x q)) = a * ∑ q, μ q * x q from by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring, ih, mul_zero]
  · intro horth n M
    exact horth _ (Submodule.subset_span ⟨⟨n, M⟩, rfl⟩)

/-- **The moment problem ⟺ full rank** — pins `signed_orbit_measure_has_nonzero_moment`
to the already-built span formalism: the multigraph-moment map on signed orbit-class
measures is nondegenerate iff the descended evals span everything
(`multiOrbitSpan = ⊤`). Forward via `connectionMatrix_full_rank_of_orthogonal`
(reweighting `μ = orbitWeight · h`); backward via the indicator `δ_{q₀} ∈ ⊤`. So the
moment-problem root, full rank, and point separation are all interchangeable. -/
theorem moment_nondegenerate_iff_multiOrbitSpan_eq_top {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (hW : ∀ i, 0 < W i) :
    (∀ μ : OrbitClass T K B W → ℝ, μ ≠ 0 →
      ∃ (n : ℕ) (M : MultiLabeledGraph K n), (∑ q, μ q * multiEvalOnOrbit K n M B W q) ≠ 0)
    ↔ multiOrbitSpan K B W = ⊤ := by
  constructor
  · intro hnd
    apply connectionMatrix_full_rank_of_orthogonal B W
    intro h horth
    by_contra hh
    have hμ : (fun q => orbitWeight K B W q * h q) ≠ 0 := by
      intro hμ0
      apply hh
      funext q
      exact (mul_eq_zero.mp (congrFun hμ0 q)).resolve_left (orbitWeight_pos K B hW q).ne'
    obtain ⟨n, M, hM⟩ := hnd _ hμ
    apply hM
    show orbitInner K B W h (multiEvalOnOrbit K n M B W) = 0
    exact horth n M
  · intro htop μ hμ
    by_contra hcon
    push_neg at hcon
    apply hμ
    have horth := (allMomentsZero_iff_orthogonal K B W μ).mp hcon
    funext q₀
    have hval := horth (fun q => if q = q₀ then (1 : ℝ) else 0)
      (by rw [htop]; exact Submodule.mem_top)
    simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Pi.zero_apply] using hval

/-- **Full span ⟹ point separation** (easy direction): if the descended evals span
every orbit-class function (`multiOrbitSpan = ⊤`) then they separate orbit classes.
If all evals agreed at `q₁ ≠ q₂`, the whole span — including the `q₁`-indicator —
would too, but the indicator separates them. -/
theorem sep_of_multiOrbitSpan_eq_top {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (htop : multiOrbitSpan K B W = ⊤) {q₁ q₂ : OrbitClass T K B W} (hne : q₁ ≠ q₂) :
    ∃ (n : ℕ) (M : MultiLabeledGraph K n),
      multiEvalOnOrbit K n M B W q₁ ≠ multiEvalOnOrbit K n M B W q₂ := by
  classical
  by_contra hcon
  push_neg at hcon
  have hle : multiOrbitSpan K B W ≤
      LinearMap.ker ((LinearMap.proj q₁ : (OrbitClass T K B W → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj q₂) := by
    rw [multiOrbitSpan, Submodule.span_le]
    rintro _ ⟨⟨n, M⟩, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.proj_apply,
      LinearMap.proj_apply, sub_eq_zero]
    exact hcon n M
  have hδ : (fun q' => if q' = q₁ then (1 : ℝ) else 0)
      ∈ LinearMap.ker ((LinearMap.proj q₁ : (OrbitClass T K B W → ℝ) →ₗ[ℝ] ℝ)
        - LinearMap.proj q₂) := by
    apply hle; rw [htop]; exact Submodule.mem_top
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.proj_apply,
    if_pos rfl, if_neg (Ne.symm hne), sub_zero] at hδ
  exact one_ne_zero hδ

/-- **Rooted weighted-multigraph hom-counts separate orbit classes** (Lovász §3
detector theorem) — now a one-line corollary of the paper-root
`connectionMatrix_full_rank` via the easy direction. Distinct `Aut(B,W)`-orbit
classes are distinguished by some rooted multigraph evaluation. -/
theorem multiEvalOnOrbit_separates {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (hW : ∀ i, 0 < W i) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    {q₁ q₂ : OrbitClass T K B W} (hne : q₁ ≠ q₂) :
    ∃ (n : ℕ) (M : MultiLabeledGraph K n),
      multiEvalOnOrbit K n M B W q₁ ≠ multiEvalOnOrbit K n M B W q₂ := by
  -- Honest proof via the (now-proved) tuple-level Lovász separator `multiEval_separates_orbits`,
  -- independent of the `signed_orbit_measure_has_nonzero_moment` root.
  obtain ⟨ξ₁, hξ₁⟩ := Quotient.exists_rep q₁
  obtain ⟨ξ₂, hξ₂⟩ := Quotient.exists_rep q₂
  have hnr : ¬ tupleOrbitRel B W ξ₁ ξ₂ := fun hr => hne (by rw [← hξ₁, ← hξ₂]; exact Quotient.sound hr)
  obtain ⟨n, M, hM⟩ := multiEval_separates_orbits B hB W hW htwin hnr
  exact ⟨n, M, by rw [← hξ₁, ← hξ₂]; simpa using hM⟩

/-- **Finset product closure** of `multiOrbitSpan` (via `mul` + `1`). -/
lemma multiOrbitSpan_prod_mem {T K : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) {ι : Type*} (s : Finset ι) (f : ι → (OrbitClass T K B W → ℝ))
    (hf : ∀ i ∈ s, f i ∈ multiOrbitSpan K B W) :
    (∏ i ∈ s, f i) ∈ multiOrbitSpan K B W := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_multiOrbitSpan K B W
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact multiOrbitSpan_mul_le B hB W (Submodule.mul_mem_mul
      (hf a (Finset.mem_insert_self a s)) (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))))

/-- **Orbit-class indicators lie in `multiOrbitSpan`, hypothesis form** — Lagrange
interpolation over orbit classes from a *separation hypothesis* `hsep` (rather than
the `multiEvalOnOrbit_separates` paper-root), using the descended `.mul`/`1`. This is
the hard direction of `multiOrbitSpan_eq_top_iff_separates`. -/
lemma orbitClassIndicator_mem_of_sep {T K : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (hsep : ∀ (q₁ q₂ : OrbitClass T K B W), q₁ ≠ q₂ →
      ∃ (n : ℕ) (M : MultiLabeledGraph K n),
        multiEvalOnOrbit K n M B W q₁ ≠ multiEvalOnOrbit K n M B W q₂)
    (q : OrbitClass T K B W) :
    (fun q' : OrbitClass T K B W => if q' = q then (1 : ℝ) else 0) ∈ multiOrbitSpan K B W := by
  classical
  let ev : OrbitClass T K B W → (OrbitClass T K B W → ℝ) := fun η =>
    if h : q ≠ η then
      multiEvalOnOrbit K (hsep q η h).choose (hsep q η h).choose_spec.choose B W
    else 0
  let factor : OrbitClass T K B W → (OrbitClass T K B W → ℝ) := fun η ζ =>
    (ev η ζ - ev η η) / (ev η q - ev η η)
  let nonEq : Finset (OrbitClass T K B W) := Finset.univ.filter (fun η => η ≠ q)
  have hdenom : ∀ η ∈ nonEq, ev η q - ev η η ≠ 0 := by
    intro η hη
    have hqη : q ≠ η := by
      simp only [nonEq, Finset.mem_filter, Finset.mem_univ, true_and] at hη; exact Ne.symm hη
    have hsepprop := (hsep q η hqη).choose_spec.choose_spec
    simp only [ev, dif_pos hqη]
    exact sub_ne_zero.mpr hsepprop
  have hfac : ∀ η ∈ nonEq, factor η ∈ multiOrbitSpan K B W := by
    intro η hη
    have hqη : q ≠ η := by
      simp only [nonEq, Finset.mem_filter, Finset.mem_univ, true_and] at hη; exact Ne.symm hη
    have hev_mem : ev η ∈ multiOrbitSpan K B W := by
      simp only [ev, dif_pos hqη]
      exact Submodule.subset_span ⟨⟨_, _⟩, rfl⟩
    have hrw : factor η =
        (1 / (ev η q - ev η η)) • (ev η - (ev η η) • (1 : OrbitClass T K B W → ℝ)) := by
      funext ζ
      simp only [factor, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul]
      ring
    rw [hrw]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hev_mem
      (Submodule.smul_mem _ _ (one_mem_multiOrbitSpan K B W)))
  have hprod := multiOrbitSpan_prod_mem B hB W nonEq factor hfac
  have heq : (∏ η ∈ nonEq, factor η) = (fun q' => if q' = q then (1 : ℝ) else 0) := by
    funext ζ
    rw [Finset.prod_apply]
    by_cases hζ : ζ = q
    · subst hζ
      rw [if_pos rfl]
      refine Finset.prod_eq_one (fun η hη => ?_)
      simp only [factor]; exact div_self (hdenom η hη)
    · rw [if_neg hζ]
      have hζmem : ζ ∈ nonEq := by
        simp only [nonEq, Finset.mem_filter, Finset.mem_univ, true_and]; exact hζ
      refine Finset.prod_eq_zero hζmem ?_
      simp only [factor, sub_self, zero_div]
  rw [heq] at hprod; exact hprod

/-- **Orbit-class indicators lie in `multiOrbitSpan`** — Lagrange interpolation over orbit
classes, using `multiEvalOnOrbit_separates` for the separators and the descended `.mul`/`1`. -/
lemma orbitClassIndicator_mem {T K : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ i, 0 < W i) (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (q : OrbitClass T K B W) :
    (fun q' : OrbitClass T K B W => if q' = q then (1 : ℝ) else 0) ∈ multiOrbitSpan K B W := by
  classical
  let ev : OrbitClass T K B W → (OrbitClass T K B W → ℝ) := fun η =>
    if h : q ≠ η then
      multiEvalOnOrbit K (multiEvalOnOrbit_separates K B W hB hW htwin h).choose
        (multiEvalOnOrbit_separates K B W hB hW htwin h).choose_spec.choose B W
    else 0
  let factor : OrbitClass T K B W → (OrbitClass T K B W → ℝ) := fun η ζ =>
    (ev η ζ - ev η η) / (ev η q - ev η η)
  let nonEq : Finset (OrbitClass T K B W) := Finset.univ.filter (fun η => η ≠ q)
  have hdenom : ∀ η ∈ nonEq, ev η q - ev η η ≠ 0 := by
    intro η hη
    have hqη : q ≠ η := by
      simp only [nonEq, Finset.mem_filter, Finset.mem_univ, true_and] at hη; exact Ne.symm hη
    have hsep := (multiEvalOnOrbit_separates K B W hB hW htwin hqη).choose_spec.choose_spec
    simp only [ev, dif_pos hqη]
    exact sub_ne_zero.mpr hsep
  have hfac : ∀ η ∈ nonEq, factor η ∈ multiOrbitSpan K B W := by
    intro η hη
    have hqη : q ≠ η := by
      simp only [nonEq, Finset.mem_filter, Finset.mem_univ, true_and] at hη; exact Ne.symm hη
    have hev_mem : ev η ∈ multiOrbitSpan K B W := by
      simp only [ev, dif_pos hqη]
      exact Submodule.subset_span ⟨⟨_, _⟩, rfl⟩
    have hrw : factor η =
        (1 / (ev η q - ev η η)) • (ev η - (ev η η) • (1 : OrbitClass T K B W → ℝ)) := by
      funext ζ
      simp only [factor, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul]
      ring
    rw [hrw]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hev_mem
      (Submodule.smul_mem _ _ (one_mem_multiOrbitSpan K B W)))
  have hprod := multiOrbitSpan_prod_mem B hB W nonEq factor hfac
  have heq : (∏ η ∈ nonEq, factor η) = (fun q' => if q' = q then (1 : ℝ) else 0) := by
    funext ζ
    rw [Finset.prod_apply]
    by_cases hζ : ζ = q
    · subst hζ
      rw [if_pos rfl]
      refine Finset.prod_eq_one (fun η hη => ?_)
      simp only [factor]; exact div_self (hdenom η hη)
    · rw [if_neg hζ]
      have hζmem : ζ ∈ nonEq := by
        simp only [nonEq, Finset.mem_filter, Finset.mem_univ, true_and]; exact hζ
      refine Finset.prod_eq_zero hζmem ?_
      simp only [factor, sub_self, zero_div]
  rw [heq] at hprod; exact hprod

/-- **The descended evals span all orbit-class functions** (`multiOrbitSpan = ⊤`): every
orbit-class function is a finite linear combination of the orbit indicators, each in
`multiOrbitSpan` by Lagrange interpolation (`orbitClassIndicator_mem`). -/
theorem multiOrbitSpan_eq_top {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j) : multiOrbitSpan K B W = ⊤ := by
  classical
  rw [Submodule.eq_top_iff']
  intro g
  have hg : g = ∑ q : OrbitClass T K B W,
      g q • (fun q' => if q' = q then (1 : ℝ) else 0) := by
    funext q'
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ q' g]
    simp
  rw [hg]
  exact Submodule.sum_mem _ (fun q _ =>
    Submodule.smul_mem _ _ (orbitClassIndicator_mem B hB W hW htwin q))

/-- **Full span from a separation hypothesis** (hard direction of the equivalence):
if the descended evals separate orbit classes (`hsep`) then they span everything. -/
theorem multiOrbitSpan_eq_top_of_sep {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i)
    (hsep : ∀ (q₁ q₂ : OrbitClass T K B W), q₁ ≠ q₂ →
      ∃ (n : ℕ) (M : MultiLabeledGraph K n),
        multiEvalOnOrbit K n M B W q₁ ≠ multiEvalOnOrbit K n M B W q₂) :
    multiOrbitSpan K B W = ⊤ := by
  classical
  rw [Submodule.eq_top_iff']
  intro g
  have hg : g = ∑ q : OrbitClass T K B W,
      g q • (fun q' => if q' = q then (1 : ℝ) else 0) := by
    funext q'
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ q' g]
    simp
  rw [hg]
  exact Submodule.sum_mem _ (fun q _ =>
    Submodule.smul_mem _ _ (orbitClassIndicator_mem_of_sep B hB W hsep q))

/-- **Point separation ⟺ full span** — the `connectionMatrix_full_rank` reframing.
The Lovász §3 point-separation theorem (`multiEvalOnOrbit_separates`) is equivalent to
`multiOrbitSpan = ⊤` (the descended orbit-class evals are a spanning / full-rank
family). Hard direction `⟸`: Lagrange interpolation (`multiOrbitSpan_eq_top_of_sep`);
easy direction `⟹`: `sep_of_multiOrbitSpan_eq_top`. So the genuine paper-root may be
stated equivalently as the connection-matrix full-rank statement `multiOrbitSpan = ⊤`,
in Lovász/FLS language, rather than as separation. -/
theorem multiOrbitSpan_eq_top_iff_separates {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (hB : ∀ i j, B i j = B j i) :
    multiOrbitSpan K B W = ⊤ ↔
      ∀ (q₁ q₂ : OrbitClass T K B W), q₁ ≠ q₂ →
        ∃ (n : ℕ) (M : MultiLabeledGraph K n),
          multiEvalOnOrbit K n M B W q₁ ≠ multiEvalOnOrbit K n M B W q₂ :=
  ⟨fun htop _ _ hne => sep_of_multiOrbitSpan_eq_top K B W htop hne,
   fun hsep => multiOrbitSpan_eq_top_of_sep K B W hB hsep⟩

/-- **Orthogonality form** — now literally the paper-root `fls_orthogonal_zero`
(kept as a named alias for downstream callers); a function orthogonal to every
descended eval is `0`. -/
theorem multiOrbitSpan_orthogonal_eq_bot {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j) (h : OrbitClass T K B W → ℝ)
    (horth : ∀ (n : ℕ) (M : MultiLabeledGraph K n),
      orbitInner K B W h (multiEvalOnOrbit K n M B W) = 0) : h = 0 :=
  fls_orthogonal_zero K B W hB hW htwin h horth

/-- **Reverse rank inequality `#orbits ≤ dim V`**, derived from `multiOrbitSpan_eq_top`:
the pullback `Φ : (OrbitClass → ℝ) ↪ ((Fin K → Fin T) → ℝ)` along `⟦·⟧` is injective and (since
`multiOrbitSpan = ⊤`) lands inside `multiSpanSubmodule`, so `#orbits = finrank (OrbitClass → ℝ)
≤ finrank (multiSpanSubmodule)`. -/
theorem card_orbitClass_le_finrank_multiSpan {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j) :
    Nat.card (OrbitClass T K B W) ≤ Module.finrank ℝ (multiSpanSubmodule K B W) := by
  set Φ : (OrbitClass T K B W → ℝ) →ₗ[ℝ] ((Fin K → Fin T) → ℝ) :=
    LinearMap.funLeft ℝ ℝ (Quotient.mk (tupleOrbitSetoid B W K)) with hΦ
  have hmaple : Submodule.map Φ (multiOrbitSpan K B W) ≤ multiSpanSubmodule K B W := by
    rw [multiOrbitSpan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨p, ?_⟩
    funext ξ
    simp only [hΦ, LinearMap.funLeft_apply, multiEvalOnOrbit_mk]
  have hmaps : ∀ h : OrbitClass T K B W → ℝ, Φ h ∈ multiSpanSubmodule K B W := fun h =>
    hmaple ⟨h, by rw [multiOrbitSpan_eq_top K B W hB hW htwin]; exact Submodule.mem_top, rfl⟩
  let Ψ : (OrbitClass T K B W → ℝ) →ₗ[ℝ] multiSpanSubmodule K B W :=
    LinearMap.codRestrict (multiSpanSubmodule K B W) Φ hmaps
  have hΨinj : Function.Injective Ψ := fun h h' hee =>
    LinearMap.funLeft_injective_of_surjective ℝ ℝ _ Quotient.mk_surjective
      (congrArg Subtype.val hee)
  rw [Nat.card_eq_fintype_card, ← Module.finrank_pi (ι := OrbitClass T K B W) ℝ]
  exact LinearMap.finrank_le_finrank_of_injective hΨinj

/-- **Rank theorem `dim V = #orbits`** (modulo the full-rank residue): the multigraph-eval
span is exactly the orbit-invariant functions. -/
theorem finrank_multiSpan_eq_card_orbitClass {T : ℕ} (K : ℕ) (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j) :
    Module.finrank ℝ (multiSpanSubmodule K B W) = Nat.card (OrbitClass T K B W) :=
  le_antisymm (finrank_multiSpan_le_card_orbitClass K B W)
    (card_orbitClass_le_finrank_multiSpan K B W hB hW htwin)

/-! ### Level-1 foundation for the weighted-WL build

`weighted_powersum_determines_measure`: a finite signed measure on `ℝ` (here, `W`-weighted values
of a function on a finite index) is determined by its power-sum moments. This is the K=1 level-1
refinement step (the single-vertex multigraph moments read each vertex's weighted row measure), and
a reusable brick for the eventual `multiEvalOnOrbit_separates` (weighted Weisfeiler–Leman) proof. -/

/-- **Weighted power sums determine the weighted value measure.** If `∑_t W t · (x t)^k =
∑_t W t · (y t)^k` for all `k`, then for every value `a` the `W`-weighted preimage masses agree:
`∑_{t : x t = a} W t = ∑_{t : y t = a} W t`. (No positivity of `W` is needed for this form; the
proof is a Lagrange interpolation that turns moment equality into preimage-mass equality.) -/
theorem weighted_powersum_determines_measure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι → ℝ) (W : ι → ℝ)
    (hmom : ∀ k : ℕ, ∑ i, W i * x i ^ k = ∑ i, W i * y i ^ k) (a : ℝ) :
    (∑ i ∈ Finset.univ.filter (fun i => x i = a), W i) =
      ∑ i ∈ Finset.univ.filter (fun i => y i = a), W i := by
  classical
  -- Moment equality extends to `∑ W·Q(·)` for every polynomial `Q`.
  have hpoly : ∀ Q : Polynomial ℝ,
      (∑ i, W i * Q.eval (x i)) = ∑ i, W i * Q.eval (y i) := by
    intro Q
    have key : ∀ z : ι → ℝ, (∑ i, W i * Q.eval (z i)) =
        ∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * ∑ i, W i * z i ^ k := by
      intro z
      simp_rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [key x, key y]
    exact Finset.sum_congr rfl fun k _ => by rw [hmom k]
  -- The Lagrange indicator polynomial for value `a` over the set of occurring values.
  set S : Finset ℝ := Finset.univ.image x ∪ Finset.univ.image y with hSdef
  set Pa : Polynomial ℝ :=
    ∏ b ∈ S.erase a, Polynomial.C (a - b)⁻¹ * (Polynomial.X - Polynomial.C b) with hPaDef
  have hPa : ∀ c ∈ S, Pa.eval c = if c = a then 1 else 0 := by
    intro c hc
    by_cases hca : c = a
    · subst hca
      rw [if_pos rfl, hPaDef]
      simp only [Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_sub, Polynomial.eval_X]
      refine Finset.prod_eq_one fun b hb => ?_
      have hcb : c - b ≠ 0 := sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hb))
      exact inv_mul_cancel₀ hcb
    · rw [if_neg hca, hPaDef]
      have hce : c ∈ S.erase a := Finset.mem_erase.mpr ⟨hca, hc⟩
      simp only [Polynomial.eval_prod]
      refine Finset.prod_eq_zero hce ?_
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        sub_self, mul_zero]
  have hx : (∑ i, W i * Pa.eval (x i)) =
      ∑ i ∈ Finset.univ.filter (fun i => x i = a), W i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hxiS : x i ∈ S :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_image_of_mem x (Finset.mem_univ i)))
    rw [hPa (x i) hxiS]; split_ifs <;> simp
  have hy : (∑ i, W i * Pa.eval (y i)) =
      ∑ i ∈ Finset.univ.filter (fun i => y i = a), W i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hyiS : y i ∈ S :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_image_of_mem y (Finset.mem_univ i)))
    rw [hPa (y i) hyiS]; split_ifs <;> simp
  rw [← hx, ← hy]; exact hpoly Pa

/-- The **`W`-weighted neighbor moment** of a vertex `i` in a weighted graph
`(B, W)`: the `a`-th power-sum `∑ₜ W t · B i t ^ a` of its `B`-row under the
weight `W`. This is the level-1 weighted-WL observable; it is realized inside the
multigraph algebra by the *star probe* (a root joined to a single unlabeled leaf
by `a` parallel edges), whose `multiLabeledEvalK` at the singleton tuple `i ↦ i`
is exactly this sum. -/
noncomputable def neighborMoment {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (i : Fin T) (a : ℕ) : ℝ := ∑ t, W t * B i t ^ a

/-- The **`W`-weighted neighbor-profile measure** of a vertex `i`: for each value
`v : ℝ`, the total `W`-mass `∑_{t : B i t = v} W t` of neighbors `t` whose edge
weight to `i` equals `v`. This is the level-1 color in weighted color-refinement
(the `W`-weighted multiset `νᵢ := ∑ₜ W t · δ_{B i t}`, recorded as a function of
the value). -/
noncomputable def neighborProfileMeasure {T : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (i : Fin T) (v : ℝ) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t => B i t = v), W t

/-- **Refinement step 1: equal weighted neighbor moments ⟹ equal weighted
neighbor-profile measures.** If two vertices `i, j` of a weighted graph share
*all* their `W`-weighted neighbor moments, then their `W`-weighted
neighbor-profile measures agree value-by-value.

This is the first rung of the weighted Weisfeiler–Leman tower: the single-vertex
multigraph observables (`neighborMoment`, read off the star probes) determine
each vertex's level-1 color (`neighborProfileMeasure`). It is a direct
specialization of `weighted_powersum_determines_measure` to the rows `B i`,
`B j` as value functions — the Lagrange/Vandermonde brick lifted into the graph
setting. (Necessary but, alone, *not* sufficient for orbit separation: 1-WL is
strictly weaker than `multiEvalOnOrbit_separates`; higher rungs feed lower-level
colors back through the multigraph algebra.) -/
theorem neighborProfileMeasure_eq_of_neighborMoment_eq {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (i j : Fin T)
    (hmom : ∀ a : ℕ, neighborMoment B W i a = neighborMoment B W j a) (v : ℝ) :
    neighborProfileMeasure B W i v = neighborProfileMeasure B W j v :=
  weighted_powersum_determines_measure (B i) (B j) W hmom v

/-- **Observable grounding: `neighborMoment` IS a multigraph evaluation.** For
symmetric `B`, the `a`-th `W`-weighted neighbor moment of a vertex `i` equals the
`multiLabeledEvalK` of the multiplicity-`a` star probe (`starProbe`, from
`Graphon/Lovasz.lean`) at the singleton tuple `· ↦ i`.

This is the bridge that turns the level-1 WL refinement into a statement about
the actual orbit-separation algebra: whenever two vertices agree under
`multiLabeledEvalK` for *all* multigraphs — in particular all star probes — they
share every `neighborMoment`, hence (via
`neighborProfileMeasure_eq_of_neighborMoment_eq`) every level-1 color. So the
hypothesis of refinement step 1 is *supplied* by `multiEvalOnOrbit` agreement. -/
theorem multiLabeledEvalK_starProbe_eq_neighborMoment {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (i : Fin T) (a : ℕ) :
    multiLabeledEvalK 1 1 (starProbe a) B W (fun _ => i) = neighborMoment B W i a :=
  multiLabeledEvalK_starProbe B hB W i a

/-- The **refined neighbor moment** of a vertex `i` against a previously
constructed color/feature `χ : Fin T → ℝ`: the `a`-th `(W·χ)`-weighted power-sum
`∑ₜ W t · B i t ^ a · χ t` of its `B`-row. Generalizes `neighborMoment`
(`χ ≡ 1`); realized by a *decorated* star probe whose leaf is constrained by the
lower-level multigraph computing `χ` (the graph realization is a separate step). -/
noncomputable def refineMoment {T : ℕ} (B : Fin T → Fin T → ℝ) (W χ : Fin T → ℝ)
    (i : Fin T) (a : ℕ) : ℝ := ∑ t, W t * B i t ^ a * χ t

/-- The **refined neighbor-profile measure** of a vertex `i` against feature `χ`:
for each value `v`, the `(W·χ)`-mass `∑_{t : B i t = v} W t · χ t` of neighbors
with edge weight `v`. The level-`(k+1)` color in weighted color-refinement when
`χ` is a level-`k` color (or an indicator of a level-`k` color class).
Generalizes `neighborProfileMeasure` (`χ ≡ 1`). -/
noncomputable def refineMeasure {T : ℕ} (B : Fin T → Fin T → ℝ) (W χ : Fin T → ℝ)
    (i : Fin T) (v : ℝ) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t => B i t = v), W t * χ t

/-- **Refinement step (general): equal refined moments ⟹ equal refined profile
measures.** Against any fixed feature `χ`, if two vertices share all their
`(W·χ)`-weighted neighbor moments, then their `(W·χ)`-weighted neighbor-profile
measures agree value-by-value.

This is the inductive rung of the weighted Weisfeiler–Leman tower: feeding a
lower-level color `χ` back as a leaf weight is exactly *reweighting* the
Vandermonde/Lagrange brick from `W` to `W·χ`, so the proof is a direct
specialization of `weighted_powersum_determines_measure` (no new analysis). With
`χ ≡ 1` it recovers `neighborProfileMeasure_eq_of_neighborMoment_eq`; with `χ` an
indicator `t ↦ if color t = c then 1 else 0` it refines each color class `c`. The
moment hypothesis is *supplied* by multigraph-evaluation agreement once the
decorated star probe realizing `refineMoment` is built (separate graph step). -/
theorem refineMeasure_eq_of_refineMoment_eq {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W χ : Fin T → ℝ) (i j : Fin T)
    (hmom : ∀ a : ℕ, refineMoment B W χ i a = refineMoment B W χ j a) (v : ℝ) :
    refineMeasure B W χ i v = refineMeasure B W χ j v := by
  unfold refineMeasure
  refine weighted_powersum_determines_measure (B i) (B j) (fun t => W t * χ t) (fun a => ?_) v
  show (∑ t, W t * χ t * B i t ^ a) = ∑ t, W t * χ t * B j t ^ a
  rw [show (∑ t, W t * χ t * B i t ^ a) = ∑ t, W t * B i t ^ a * χ t from
        Finset.sum_congr rfl fun t _ => by ring,
      show (∑ t, W t * χ t * B j t ^ a) = ∑ t, W t * B j t ^ a * χ t from
        Finset.sum_congr rfl fun t _ => by ring]
  exact hmom a

/-- **Rung 2 graph realization: the refined moment is a multigraph evaluation.**
When the feature `χ` is itself a rooted multigraph evaluation
`χ t = multiLabeledEvalK 1 m Mχ B W (· ↦ t)`, the refined neighbor moment
`refineMoment B W χ i a` equals the `multiLabeledEvalK` of the *decorated star
probe* `decoratedProbe a Mχ` (from `Graphon/Lovasz.lean`) at `· ↦ i` — a star
probe with its single leaf pinned by `Mχ`.

This is the weighted-WL tower's **induction step**: if a level-`k` color lies in
the multigraph span, so does the level-`(k+1)` refined moment. Combined with
`refineMeasure_eq_of_refineMoment_eq`, multigraph-evaluation agreement on the
decorated probes forces agreement of the next-level colors. -/
theorem refineMoment_eq_decoratedProbe {T m : ℕ} (a : ℕ) (Mχ : MultiLabeledGraph 1 m)
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (i : Fin T) :
    refineMoment B W (fun t => multiLabeledEvalK 1 m Mχ B W (fun _ => t)) i a =
      multiLabeledEvalK 1 (m + 1) (decoratedProbe a Mχ) B W (fun _ => i) :=
  (multiLabeledEvalK_decoratedProbe a Mχ B hB W i).symm

/-! ### Weighted color refinement — definitions and monotonicity

The fixed-point side of the weighted-WL tower. A coloring of `Fin T` is modelled
as an equivalence relation `r` (same color ⇔ related). One refinement step
(`refineRel`) splits each class by the `(W·𝟙_class)`-weighted neighbor-profile
measure — exactly `refineMeasure` against class-indicator features. This section
establishes the operator and that it only *splits* classes (monotonicity) and
preserves the equivalence-relation structure. Termination and the
automorphism-orbit endpoint are deferred. -/

section Refinement

variable {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)

/-- The `ℝ`-valued feature indicator of the `r`-class of a vertex `k`
(`1` on the class, `0` off it). -/
def classIndicator (r : Fin T → Fin T → Prop) [DecidableRel r] (k : Fin T) : Fin T → ℝ :=
  fun t => if r k t then 1 else 0

/-- `refineMeasure` against a class indicator is the `W`-mass of the class's
vertices at edge-weight `v`: `∑_{t ∈ class k, B i t = v} W t`. Confirms the
refinement step below is the intended weighted color-refinement condition. -/
theorem refineMeasure_classIndicator (r : Fin T → Fin T → Prop) [DecidableRel r]
    (k i : Fin T) (v : ℝ) :
    refineMeasure B W (classIndicator r k) i v
      = ∑ t ∈ Finset.univ.filter (fun t => B i t = v ∧ r k t), W t := by
  simp only [refineMeasure, classIndicator, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, Finset.filter_filter]

/-- **One weighted-WL refinement step** on a coloring `r`. Two vertices get the
same next color iff they have the same current color (`r i j`) and, for every
current class (indexed by a representative `k`) and every edge-weight `v`, the
class's `W`-mass at weight `v` from `i` matches that from `j`. The class-wise
condition is exactly `refineMeasure` against the class indicator. -/
def refineRel (r : Fin T → Fin T → Prop) [DecidableRel r] (i j : Fin T) : Prop :=
  r i j ∧ ∀ (k : Fin T) (v : ℝ),
    refineMeasure B W (classIndicator r k) i v = refineMeasure B W (classIndicator r k) j v

/-- **Monotonicity / splitting**: one refinement step only splits classes — the
next coloring refines the current one (`refineRel ⊆ r`), never merging classes. -/
theorem refineRel_le (r : Fin T → Fin T → Prop) [DecidableRel r] {i j : Fin T}
    (h : refineRel B W r i j) : r i j := h.1

/-- The refined coloring is again an equivalence relation, so refinement can be
iterated. -/
theorem refineRel_equivalence (r : Fin T → Fin T → Prop) [DecidableRel r]
    (hr : Equivalence r) : Equivalence (refineRel B W r) where
  refl i := ⟨hr.refl i, fun _ _ => rfl⟩
  symm h := ⟨hr.symm h.1, fun k v => (h.2 k v).symm⟩
  trans h₁ h₂ := ⟨hr.trans h₁.1 h₂.1, fun k v => (h₁.2 k v).trans (h₂.2 k v)⟩

open scoped Classical

/-- Bundle one refinement step as a map on `Setoid`s (carrying the equivalence
proof, so the step can be iterated). -/
noncomputable def refineSetoid (s : Setoid (Fin T)) : Setoid (Fin T) :=
  ⟨refineRel B W s.r, refineRel_equivalence B W s.r s.iseqv⟩

/-- Iterating the refinement step `n` times from a starting coloring `s`. -/
noncomputable def refineSetoidIter (s : Setoid (Fin T)) : ℕ → Setoid (Fin T)
  | 0 => s
  | n + 1 => refineSetoid B W (refineSetoidIter s n)

/-- One refinement step only splits classes. -/
theorem refineSetoid_le (s : Setoid (Fin T)) {i j : Fin T}
    (h : (refineSetoid B W s).r i j) : s.r i j := refineRel_le B W s.r h

/-- **Monotone splitting** along the iteration: iterate `n+1` refines iterate `n`. -/
theorem refineSetoidIter_succ_le (s : Setoid (Fin T)) (n : ℕ) {i j : Fin T}
    (h : (refineSetoidIter B W s (n + 1)).r i j) : (refineSetoidIter B W s n).r i j :=
  refineSetoid_le B W (refineSetoidIter B W s n) h

/-- The number of color classes of a coloring. -/
noncomputable def classCount (s : Setoid (Fin T)) : ℕ := Nat.card (Quotient s)

/-- Coarsening map from the refined quotient to the original quotient (finer →
coarser); well-defined because refinement only splits. -/
noncomputable def coarsenMap (s : Setoid (Fin T)) :
    Quotient (refineSetoid B W s) → Quotient s :=
  Quotient.map' id (fun _ _ h => refineSetoid_le B W s h)

theorem coarsenMap_mk (s : Setoid (Fin T)) (a : Fin T) :
    coarsenMap B W s (Quotient.mk'' a) = Quotient.mk'' a :=
  Quotient.map'_mk'' _ _ a

theorem surjective_coarsenMap (s : Setoid (Fin T)) :
    Function.Surjective (coarsenMap B W s) :=
  fun q => Quotient.inductionOn q fun a => ⟨Quotient.mk'' a, coarsenMap_mk B W s a⟩

/-- **Class count is monotone nondecreasing** under one refinement step. -/
theorem classCount_le_refineSetoid (s : Setoid (Fin T)) :
    classCount s ≤ classCount (refineSetoid B W s) :=
  Nat.card_le_card_of_surjective _ (surjective_coarsenMap B W s)

/-- Class count is bounded by `T`. -/
theorem classCount_le_card (s : Setoid (Fin T)) : classCount s ≤ T := by
  have h : Nat.card (Quotient s) ≤ Nat.card (Fin T) :=
    Nat.card_le_card_of_surjective _ Quotient.mk''_surjective
  rwa [Nat.card_fin] at h

/-- If one refinement step does not increase the class count, the coloring is a
fixed point: equal counts together with only-splitting force equality. -/
theorem refineSetoid_eq_of_classCount_eq (s : Setoid (Fin T))
    (h : classCount (refineSetoid B W s) = classCount s) : refineSetoid B W s = s := by
  have hbij : Function.Bijective (coarsenMap B W s) :=
    (surjective_coarsenMap B W s).bijective_of_nat_card_le (le_of_eq h)
  refine Setoid.ext fun a b => ⟨fun hab => refineSetoid_le B W s hab, fun hab => ?_⟩
  have hq : coarsenMap B W s (Quotient.mk'' a) = coarsenMap B W s (Quotient.mk'' b) := by
    rw [coarsenMap_mk, coarsenMap_mk]; exact Quotient.sound' hab
  exact Quotient.exact' (hbij.injective hq)

/-- **Termination of weighted color refinement.** Along the iteration the class
count is monotone nondecreasing and bounded by `T`, so it stabilizes by step `T`;
at that step the coloring is a fixed point of refinement. -/
theorem exists_refineSetoidIter_fixed (s : Setoid (Fin T)) :
    ∃ n ≤ T, refineSetoidIter B W s (n + 1) = refineSetoidIter B W s n := by
  have hmono : ∀ n, classCount (refineSetoidIter B W s n)
      ≤ classCount (refineSetoidIter B W s (n + 1)) :=
    fun n => classCount_le_refineSetoid B W _
  have hbound : ∀ n, classCount (refineSetoidIter B W s n) ≤ T :=
    fun n => classCount_le_card _
  have hstab : ∃ n ≤ T,
      classCount (refineSetoidIter B W s (n + 1)) = classCount (refineSetoidIter B W s n) := by
    by_contra hc
    push_neg at hc
    have hstrict : ∀ n ≤ T,
        classCount (refineSetoidIter B W s n) < classCount (refineSetoidIter B W s (n + 1)) :=
      fun n hn => lt_of_le_of_ne (hmono n) fun he => hc n hn he.symm
    have hge : ∀ k, k ≤ T + 1 → k ≤ classCount (refineSetoidIter B W s k) := by
      intro k
      induction k with
      | zero => intro _; exact Nat.zero_le _
      | succ j ih =>
        intro hk
        have h1 := hstrict j (by omega)
        have h2 := ih (by omega)
        omega
    have h1 := hge (T + 1) (le_refl _)
    have h2 := hbound (T + 1)
    omega
  obtain ⟨n, hnT, hfn⟩ := hstab
  exact ⟨n, hnT, refineSetoid_eq_of_classCount_eq B W (refineSetoidIter B W s n) hfn⟩

/-! #### Automorphism invariance: orbits ⊆ refinement classes (easy direction)

A weighted automorphism `σ` preserves the refined measure of any class it
saturates (`∀ i, r i (σ i)`), because reindexing the defining sum by `σ` fixes
`B`, `W`, and the class indicator. Iterating from the trivial coloring `⊤` (which
every automorphism saturates), each refinement iterate stays σ-saturated, so the
orbit of `i` lies in every refinement class of `i`. -/

/-- **Refined measure is automorphism-invariant** on a σ-saturated coloring:
reindex the defining sum by `σ`, using `B`/`W`-invariance and that `σ s` shares
the `r`-class of `s`. -/
theorem refineMeasure_classIndicator_aut (r : Fin T → Fin T → Prop)
    (hr : Equivalence r) (σ : Equiv.Perm (Fin T))
    (hσW : ∀ i, W (σ i) = W i) (hσB : ∀ i j, B (σ i) (σ j) = B i j)
    (hsat : ∀ i, r i (σ i)) (k i : Fin T) (v : ℝ) :
    refineMeasure B W (classIndicator r k) (σ i) v
      = refineMeasure B W (classIndicator r k) i v := by
  unfold refineMeasure
  rw [Finset.sum_filter, Finset.sum_filter,
    ← Equiv.sum_comp σ (fun t => if B (σ i) t = v then W t * classIndicator r k t else 0)]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hci : classIndicator r k (σ s) = classIndicator r k s := by
    unfold classIndicator
    by_cases h : r k s
    · rw [if_pos h, if_pos (hr.trans h (hsat s))]
    · rw [if_neg h, if_neg fun hc => h (hr.trans hc (hr.symm (hsat s)))]
  rw [hσB i s, hσW s, hci]

/-- Every refinement iterate from the trivial coloring `⊤` is saturated by any
weighted automorphism: `i` and `σ i` always share a class. -/
theorem refineSetoidIter_top_saturated (σ : Equiv.Perm (Fin T))
    (hσW : ∀ i, W (σ i) = W i) (hσB : ∀ i j, B (σ i) (σ j) = B i j) :
    ∀ (n : ℕ) (i : Fin T), (refineSetoidIter B W ⊤ n).r i (σ i) := by
  intro n
  induction n with
  | zero => intro i; trivial
  | succ m ih =>
    intro i
    exact ⟨ih i, fun k v =>
      (refineMeasure_classIndicator_aut B W (refineSetoidIter B W ⊤ m).r
        (refineSetoidIter B W ⊤ m).iseqv σ hσW hσB ih k i v).symm⟩

/-- **Orbits ⊆ refinement classes** (easy containment): the weighted-automorphism
orbit of a vertex lies in every refinement class from the trivial coloring. -/
theorem vertexOrbitRel_imp_refineSetoidIter {i j : Fin T}
    (h : vertexOrbitRel B W i j) (n : ℕ) : (refineSetoidIter B W ⊤ n).r i j := by
  obtain ⟨σ, ⟨hσW, hσB⟩, hσij⟩ := h
  rw [← hσij]
  exact refineSetoidIter_top_saturated B W σ hσW hσB n i

/-- The stable coloring: refinement iterated to its fixed point (reached by `T`). -/
noncomputable def stableSetoid (s : Setoid (Fin T)) : Setoid (Fin T) :=
  refineSetoidIter B W s (exists_refineSetoidIter_fixed B W s).choose

/-- **Orbit ⟹ stable-class** (easy direction of `stable = orbit`): weighted
automorphism orbits are contained in the stable refinement classes. The reverse
inclusion (stable class ⟹ orbit) is the coherent-configuration theorem, deferred. -/
theorem vertexOrbitRel_imp_stable {i j : Fin T} (h : vertexOrbitRel B W i j) :
    (stableSetoid B W ⊤).r i j :=
  vertexOrbitRel_imp_refineSetoidIter B W h _

/-! #### Stable ⟹ equitable (first step of the hard direction)

At a refinement fixed point the defining condition of `refineRel` already holds
on each class, so same-class vertices share *all* their weighted
edge-distribution data. This is the equitable-partition / coherent-configuration
property — the algebraic input for the (deferred) reconstruction theorem. -/

/-- `stableSetoid B W s` is a fixed point of one refinement step (the iteration
stops increasing the class count by step `T`). -/
theorem stableSetoid_fixed (s : Setoid (Fin T)) :
    refineSetoid B W (stableSetoid B W s) = stableSetoid B W s :=
  (exists_refineSetoidIter_fixed B W s).choose_spec.2

/-- **Stable ⟹ equitable** (fixed-point form): at a refinement fixed point `s`,
two vertices in the same class have identical weighted edge-distributions to
every class — the edge-distribution data is class-independent. Immediate from
`refineRel` holding on the class at a fixed point. -/
theorem stable_imp_equitable (s : Setoid (Fin T)) (hfix : refineSetoid B W s = s)
    {i j : Fin T} (hij : s.r i j) (k : Fin T) (v : ℝ) :
    refineMeasure B W (classIndicator s.r k) i v
      = refineMeasure B W (classIndicator s.r k) j v := by
  have h : refineRel B W s.r i j := by
    have hh : (refineSetoid B W s).r i j := by rw [hfix]; exact hij
    exact hh
  exact h.2 k v

/-- **The stable coloring is equitable**: same-class vertices of `stableSetoid B W s`
share all their weighted edge-distribution data. -/
theorem stable_equitable (s : Setoid (Fin T)) {i j : Fin T}
    (hij : (stableSetoid B W s).r i j) (k : Fin T) (v : ℝ) :
    refineMeasure B W (classIndicator (stableSetoid B W s).r k) i v
      = refineMeasure B W (classIndicator (stableSetoid B W s).r k) j v :=
  stable_imp_equitable B W (stableSetoid B W s) (stableSetoid_fixed B W s) hij k v

/-- **Classwise measure equality** (step 1 of the reconstruction). For
stable-equivalent `i, j` and each stable class (represented by `k`), the
`W`-weighted value-measure of the `B`-row over that class agrees: for every value
`v`, the `W`-mass of class members `t` with `B i t = v` equals that with
`B j t = v`. Unfolds `stable_equitable` via `refineMeasure_classIndicator`; this
is the equal-value-multiset input for building a row-preserving bijection. -/
theorem stable_classMeasure_eq (s : Setoid (Fin T)) {i j : Fin T}
    (hij : (stableSetoid B W s).r i j) (k : Fin T) (v : ℝ) :
    (∑ t ∈ Finset.univ.filter (fun t => B i t = v ∧ (stableSetoid B W s).r k t), W t)
      = ∑ t ∈ Finset.univ.filter (fun t => B j t = v ∧ (stableSetoid B W s).r k t), W t := by
  rw [← refineMeasure_classIndicator, ← refineMeasure_classIndicator]
  exact stable_equitable B W s hij k v

/-- **Classwise moment / row equality.** The classwise measure equality lifts to
all power-sum moments of the `B`-row over a stable class: for stable-equivalent
`i, j`, every class `k`, and every `a`,
`∑_{t ∈ class k} W t · B i t ^ a = ∑_{t ∈ class k} W t · B j t ^ a`. The case
`a = 1` is the weighted row-sum to each class. Derived from `stable_classMeasure_eq`
by fiberwise decomposition over the (finite) set of occurring `B`-values. -/
theorem stable_classMoment_eq (s : Setoid (Fin T)) {i j : Fin T}
    (hij : (stableSetoid B W s).r i j) (k : Fin T) (a : ℕ) :
    (∑ t ∈ Finset.univ.filter (fun t => (stableSetoid B W s).r k t), W t * B i t ^ a)
      = ∑ t ∈ Finset.univ.filter (fun t => (stableSetoid B W s).r k t), W t * B j t ^ a := by
  set R := (stableSetoid B W s).r with hR
  set C : Finset (Fin T) := Finset.univ.filter (fun t => R k t) with hC
  set S : Finset ℝ := C.image (B i) ∪ C.image (B j) with hS
  have decomp : ∀ g : Fin T → ℝ, (∀ t ∈ C, g t ∈ S) →
      (∑ t ∈ C, W t * g t ^ a) = ∑ v ∈ S, v ^ a * ∑ t ∈ C.filter (fun t => g t = v), W t := by
    intro g hg
    rw [← Finset.sum_fiberwise_of_maps_to hg (fun t => W t * g t ^ a)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_filter] at ht
    rw [ht.2]; ring
  rw [decomp (B i) (fun t ht => Finset.mem_union.mpr (Or.inl (Finset.mem_image_of_mem _ ht))),
    decomp (B j) (fun t ht => Finset.mem_union.mpr (Or.inr (Finset.mem_image_of_mem _ ht)))]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  have hconv : ∀ w : Fin T → ℝ, C.filter (fun t => w t = v)
      = Finset.univ.filter (fun t => w t = v ∧ R k t) := by
    intro w
    ext t
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [hconv (B i), hconv (B j)]
  exact stable_classMeasure_eq B W s hij k v

/-- **Transportation lemma.** Two finite nonnegative weightings with equal total
weight admit a nonnegative coupling with the prescribed marginals — the *product
coupling* `c a b = wa a · wb b / Z`. (Equal totals give a fractional matching,
NOT a weight-preserving bijection: weights `{1,3}` and `{2,2}` both total `4` but
have no bijection. This is the right, weaker, assertion.) -/
theorem exists_coupling {α β : Type*} [Fintype α] [Fintype β]
    (wa : α → ℝ) (wb : β → ℝ) (hwa : ∀ a, 0 ≤ wa a) (hwb : ∀ b, 0 ≤ wb b)
    (htot : ∑ a, wa a = ∑ b, wb b) :
    ∃ c : α → β → ℝ, (∀ a b, 0 ≤ c a b) ∧
      (∀ a, ∑ b, c a b = wa a) ∧ (∀ b, ∑ a, c a b = wb b) := by
  by_cases hZ : ∑ a, wa a = 0
  · refine ⟨fun _ _ => 0, fun _ _ => le_refl 0, fun a => ?_, fun b => ?_⟩
    · rw [Finset.sum_const_zero]
      exact ((Finset.sum_eq_zero_iff_of_nonneg fun a _ => hwa a).mp hZ a (Finset.mem_univ a)).symm
    · rw [Finset.sum_const_zero]
      exact ((Finset.sum_eq_zero_iff_of_nonneg fun b _ => hwb b).mp (htot ▸ hZ) b
        (Finset.mem_univ b)).symm
  · have hZpos : 0 < ∑ a, wa a :=
      lt_of_le_of_ne (Finset.sum_nonneg fun a _ => hwa a) (Ne.symm hZ)
    refine ⟨fun a b => wa a * wb b / (∑ a', wa a'), fun a b => ?_, fun a => ?_, fun b => ?_⟩
    · exact div_nonneg (mul_nonneg (hwa a) (hwb b)) (le_of_lt hZpos)
    · rw [← Finset.sum_div, ← Finset.mul_sum, ← htot, mul_div_assoc, div_self hZpos.ne', mul_one]
    · rw [← Finset.sum_div, ← Finset.sum_mul, mul_div_right_comm, div_self hZpos.ne', one_mul]

/-- **Per-fiber coupling at a stable partition.** For stable-equivalent `i, j`,
every class `k`, and every value `v`, the two `(class, value)` fibers (members `t`
of class `k` with `B i t = v`, resp. `B j t = v`) have equal total `W`-weight
(`stable_classMeasure_eq`), hence a nonnegative coupling matching the `W`-weight
of `i`'s fiber against `j`'s. The local building block of a fractional
automorphism (which the deferred reconstruction assembles across all fibers). -/
theorem exists_fiber_coupling (s : Setoid (Fin T)) (hW : ∀ t, 0 ≤ W t) {i j : Fin T}
    (hij : (stableSetoid B W s).r i j) (k : Fin T) (v : ℝ) :
    ∃ c : Fin T → Fin T → ℝ, (∀ a b, 0 ≤ c a b) ∧
      (∀ a, ∑ b, c a b = if B i a = v ∧ (stableSetoid B W s).r k a then W a else 0) ∧
      (∀ b, ∑ a, c a b = if B j b = v ∧ (stableSetoid B W s).r k b then W b else 0) := by
  apply exists_coupling
  · intro a; split_ifs with h
    · exact hW a
    · exact le_refl 0
  · intro b; split_ifs with h
    · exact hW b
    · exact le_refl 0
  · rw [← Finset.sum_filter, ← Finset.sum_filter]
    exact stable_classMeasure_eq B W s hij k v

/-- Total `W`-weight of the `i`-fiber of `k`'s stable class at value `v`
(`∑_{t ∈ class k, B i t = v} W t`); the local normalizer of the assembled
coupling. -/
noncomputable def iFiberWeight (s : Setoid (Fin T)) (i k : Fin T) (v : ℝ) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t => B i t = v ∧ (stableSetoid B W s).r k t), W t

/-- **Assembled coupling matrix** for a stable-equivalent pair `(i, j)`: glue the
per-class/value product couplings into one matrix. `X a b` couples `a` (viewed via
the `i`-row) with `b` (viewed via the `j`-row) when they share a stable class and
`B i a = B j b`, with mass `W a · W b` normalized by `a`'s `i`-fiber weight. -/
noncomputable def couplingMatrix (s : Setoid (Fin T)) (i j a b : Fin T) : ℝ :=
  if B i a = B j b ∧ (stableSetoid B W s).r a b
  then W a * W b / iFiberWeight B W s i a (B i a) else 0

/-- A vertex lies in its own `i`-fiber, so that fiber has positive weight. -/
theorem iFiberWeight_self_pos (s : Setoid (Fin T)) (hW : ∀ t, 0 < W t) (i a : Fin T) :
    0 < iFiberWeight B W s i a (B i a) := by
  rw [iFiberWeight]
  refine lt_of_lt_of_le (hW a) (Finset.single_le_sum (fun t _ => (hW t).le) ?_)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, rfl, (stableSetoid B W s).iseqv.refl a⟩

/-- **(1) Nonnegativity** of the assembled coupling. -/
theorem couplingMatrix_nonneg (s : Setoid (Fin T)) (hW : ∀ t, 0 < W t) (i j a b : Fin T) :
    0 ≤ couplingMatrix B W s i j a b := by
  rw [couplingMatrix]
  split_ifs with hcond
  · exact div_nonneg (mul_nonneg (hW a).le (hW b).le)
      (by rw [iFiberWeight]; exact Finset.sum_nonneg fun t _ => (hW t).le)
  · exact le_refl 0

/-- **(4) Support**: a nonzero entry forces the two vertices into the same stable
class with equal relevant row-values. -/
theorem couplingMatrix_support (s : Setoid (Fin T)) (i j a b : Fin T)
    (h : couplingMatrix B W s i j a b ≠ 0) :
    (stableSetoid B W s).r a b ∧ B i a = B j b := by
  rw [couplingMatrix] at h
  by_cases hcond : B i a = B j b ∧ (stableSetoid B W s).r a b
  · exact ⟨hcond.2, hcond.1⟩
  · rw [if_neg hcond] at h; exact absurd rfl h

/-- **(2) Row marginals**: each row of the assembled coupling sums to `W a`. -/
theorem couplingMatrix_row (s : Setoid (Fin T)) (hW : ∀ t, 0 < W t) {i j : Fin T}
    (hij : (stableSetoid B W s).r i j) (a : Fin T) :
    ∑ b, couplingMatrix B W s i j a b = W a := by
  have hD : 0 < iFiberWeight B W s i a (B i a) := iFiberWeight_self_pos B W s hW i a
  simp only [couplingMatrix]
  rw [← Finset.sum_filter]
  have hsum : (∑ b ∈ Finset.univ.filter
        (fun b => B i a = B j b ∧ (stableSetoid B W s).r a b), W b)
      = iFiberWeight B W s i a (B i a) := by
    rw [iFiberWeight, stable_classMeasure_eq B W s hij a (B i a)]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2⟩
  rw [← Finset.sum_div, ← Finset.mul_sum, hsum, mul_div_assoc, div_self hD.ne', mul_one]

/-- **(3) Column marginals**: each column of the assembled coupling sums to `W b`. -/
theorem couplingMatrix_col (s : Setoid (Fin T)) (hW : ∀ t, 0 < W t) {i j : Fin T}
    (hij : (stableSetoid B W s).r i j) (b : Fin T) :
    ∑ a, couplingMatrix B W s i j a b = W b := by
  have hE : 0 < iFiberWeight B W s i b (B j b) := by
    rw [iFiberWeight, stable_classMeasure_eq B W s hij b (B j b)]
    refine lt_of_lt_of_le (hW b) (Finset.single_le_sum (fun t _ => (hW t).le) ?_)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ b, rfl, (stableSetoid B W s).iseqv.refl b⟩
  have hfib : ∀ a, B i a = B j b → (stableSetoid B W s).r a b →
      iFiberWeight B W s i a (B i a) = iFiberWeight B W s i b (B j b) := by
    intro a hab hRab
    rw [iFiberWeight, iFiberWeight]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hab ▸ h1, (stableSetoid B W s).iseqv.trans ((stableSetoid B W s).iseqv.symm hRab) h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1.trans hab.symm, (stableSetoid B W s).iseqv.trans hRab h2⟩
  simp only [couplingMatrix]
  rw [← Finset.sum_filter]
  have heq : ∀ a ∈ Finset.univ.filter
        (fun a => B i a = B j b ∧ (stableSetoid B W s).r a b),
      W a * W b / iFiberWeight B W s i a (B i a)
        = W a * W b / iFiberWeight B W s i b (B j b) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [hfib a ha.2.1 ha.2.2]
  rw [Finset.sum_congr rfl heq]
  have hsum_a : (∑ a ∈ Finset.univ.filter
        (fun a => B i a = B j b ∧ (stableSetoid B W s).r a b), W a)
      = iFiberWeight B W s i b (B j b) := by
    rw [iFiberWeight]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, (stableSetoid B W s).iseqv.symm h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (stableSetoid B W s).iseqv.symm h2⟩
  rw [← Finset.sum_div, ← Finset.sum_mul, hsum_a, mul_div_right_comm, div_self hE.ne', one_mul]

/-! #### Class-averaging fractional automorphism

The `couplingMatrix` above is tailored to the `i/j` rows and does not commute with
`B`. The *class-averaging* matrix `avgMatrix a b = [stable a b] · W b / classWeight a`
is the canonical `W`-weighted projection onto stable-class-constant functions; its
`B`-commutation follows from equitability (`stable_classMoment_eq`). Here we prove
its marginals/positivity; the commutation is the next step.

CAVEAT on the commutation form: for weighted graphs the *plain* matrix identity
`∑_c X a c · B c b = ∑_c B a c · X c b` is FALSE (it would force `W a = W b` across
classes). The identity that holds is the `W`-weighted one
`W b · ∑_c X a c · B c b = ∑_c W c · B a c · X c b`
(equivalently, `avgMatrix` commutes with the `W`-weighted operator `c ↦ B · c · W`),
which is what the reconstruction actually needs. -/

/-- Total `W`-weight of a vertex's stable class. -/
noncomputable def classWeight (s : Setoid (Fin T)) (a : Fin T) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t => (stableSetoid B W s).r a t), W t

theorem classWeight_pos (s : Setoid (Fin T)) (hW : ∀ t, 0 < W t) (a : Fin T) :
    0 < classWeight B W s a := by
  rw [classWeight]
  refine lt_of_lt_of_le (hW a) (Finset.single_le_sum (fun t _ => (hW t).le) ?_)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, (stableSetoid B W s).iseqv.refl a⟩

theorem classWeight_eq_of_rel (s : Setoid (Fin T)) {a b : Fin T}
    (h : (stableSetoid B W s).r a b) : classWeight B W s a = classWeight B W s b := by
  rw [classWeight, classWeight]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hat => (stableSetoid B W s).iseqv.trans ((stableSetoid B W s).iseqv.symm h) hat,
    fun hbt => (stableSetoid B W s).iseqv.trans h hbt⟩

/-- **Class-averaging fractional automorphism** for the stable partition: the
`W`-weighted average over stable classes. Row-stochastic, `W`-stationary, and
(in the `W`-weighted sense) `B`-commuting. -/
noncomputable def avgMatrix (s : Setoid (Fin T)) (a b : Fin T) : ℝ :=
  if (stableSetoid B W s).r a b then W b / classWeight B W s a else 0

/-- **(1) Nonnegativity.** -/
theorem avgMatrix_nonneg (s : Setoid (Fin T)) (hW : ∀ t, 0 < W t) (a b : Fin T) :
    0 ≤ avgMatrix B W s a b := by
  rw [avgMatrix]
  split_ifs with h
  · exact div_nonneg (hW b).le (classWeight_pos B W s hW a).le
  · exact le_refl 0

/-- **(2) Row-stochastic.** -/
theorem avgMatrix_row (s : Setoid (Fin T)) (hW : ∀ t, 0 < W t) (a : Fin T) :
    ∑ b, avgMatrix B W s a b = 1 := by
  simp only [avgMatrix]
  rw [← Finset.sum_filter, ← Finset.sum_div,
    show (∑ b ∈ Finset.univ.filter (fun b => (stableSetoid B W s).r a b), W b)
      = classWeight B W s a from rfl]
  exact div_self (classWeight_pos B W s hW a).ne'

/-- **(3) `W`-stationary / column balance**: `∑ₐ W a · X a b = W b`. -/
theorem avgMatrix_col_balance (s : Setoid (Fin T)) (hW : ∀ t, 0 < W t) (b : Fin T) :
    ∑ a, W a * avgMatrix B W s a b = W b := by
  have hcw := classWeight_pos B W s hW b
  have hsum : (∑ a ∈ Finset.univ.filter (fun a => (stableSetoid B W s).r a b), W a)
      = classWeight B W s b := by
    rw [classWeight]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => (stableSetoid B W s).iseqv.symm h, fun h => (stableSetoid B W s).iseqv.symm h⟩
  have heq : ∀ a ∈ Finset.univ.filter (fun a => (stableSetoid B W s).r a b),
      W a * (W b / classWeight B W s a) = W a * W b / classWeight B W s b := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [classWeight_eq_of_rel B W s ha.2, ← mul_div_assoc]
  simp only [avgMatrix, mul_ite, mul_zero]
  rw [← Finset.sum_filter, Finset.sum_congr rfl heq, ← Finset.sum_div, ← Finset.sum_mul, hsum,
    mul_div_right_comm, div_self hcw.ne', one_mul]

/-- **(5) Positivity on the diagonal block**: stable-equivalent vertices get
positive coupling. -/
theorem avgMatrix_pos (s : Setoid (Fin T)) (hW : ∀ t, 0 < W t) {i j : Fin T}
    (h : (stableSetoid B W s).r i j) : 0 < avgMatrix B W s i j := by
  rw [avgMatrix, if_pos h]
  exact div_pos (hW j) (classWeight_pos B W s hW i)

/-- **(4) `W`-weighted `B`-commutation** of the class-averaging fractional
automorphism: `avgMatrix` commutes with the `W`-weighted adjacency operator
(kernel `B a c · W c`),
`W b · ∑_c X a c · B c b = ∑_c W c · B a c · X c b`.
The key algebraic property; follows from equitability (`stable_classMoment_eq` at
moment `1`) and symmetry of `B`. (The *plain* matrix identity `XB = BX` is false
for unequal vertex weights — see the section caveat.) -/
theorem avgMatrix_commutes (s : Setoid (Fin T)) (hB : ∀ i j, B i j = B j i)
    (hW : ∀ t, 0 < W t) (a b : Fin T) :
    W b * ∑ c, avgMatrix B W s a c * B c b
      = ∑ c, W c * B a c * avgMatrix B W s c b := by
  have hcwa := classWeight_pos B W s hW a
  have hcwb := classWeight_pos B W s hW b
  have hfsymm : ∀ x : Fin T, Finset.univ.filter (fun c => (stableSetoid B W s).r c x)
      = Finset.univ.filter (fun c => (stableSetoid B W s).r x c) := by
    intro x; ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => (stableSetoid B W s).iseqv.symm h, fun h => (stableSetoid B W s).iseqv.symm h⟩
  -- LHS sum  =  X / classWeight a   (X = weighted B-sum from b into a's class)
  have hLeq : (∑ c, avgMatrix B W s a c * B c b)
      = (∑ c ∈ Finset.univ.filter (fun c => (stableSetoid B W s).r a c), W c * B c b)
          / classWeight B W s a := by
    simp only [avgMatrix, ite_mul, zero_mul]
    rw [← Finset.sum_filter, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _
    rw [div_mul_eq_mul_div]
  -- RHS sum  =  Y · W b / classWeight b   (Y = weighted B-sum from a into b's class)
  have hReq : (∑ c, W c * B a c * avgMatrix B W s c b)
      = (∑ c ∈ Finset.univ.filter (fun c => (stableSetoid B W s).r b c), W c * B a c)
          * W b / classWeight B W s b := by
    simp only [avgMatrix, mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    have hcwrepl : ∀ c ∈ Finset.univ.filter (fun c => (stableSetoid B W s).r c b),
        W c * B a c * (W b / classWeight B W s c)
          = W c * B a c * (W b / classWeight B W s b) := by
      intro c hc
      rw [Finset.mem_filter] at hc
      rw [classWeight_eq_of_rel B W s hc.2]
    rw [Finset.sum_congr rfl hcwrepl, hfsymm b, ← Finset.sum_mul, ← mul_div_assoc]
  -- Cross-multiplied equitable identity (the crux).
  have hstar : classWeight B W s b
        * (∑ c ∈ Finset.univ.filter (fun c => (stableSetoid B W s).r a c), W c * B c b)
      = classWeight B W s a
        * (∑ c ∈ Finset.univ.filter (fun c => (stableSetoid B W s).r b c), W c * B a c) := by
    have hLHS : classWeight B W s b
          * (∑ c ∈ Finset.univ.filter (fun c => (stableSetoid B W s).r a c), W c * B c b)
        = ∑ d ∈ Finset.univ.filter (fun d => (stableSetoid B W s).r b d),
            ∑ c ∈ Finset.univ.filter (fun c => (stableSetoid B W s).r a c), W d * W c * B d c := by
      rw [classWeight, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mem_filter] at hd
      have hX : (∑ c ∈ Finset.univ.filter (fun c => (stableSetoid B W s).r a c), W c * B c b)
          = ∑ c ∈ Finset.univ.filter (fun c => (stableSetoid B W s).r a c), W c * B d c := by
        rw [show (∑ c ∈ Finset.univ.filter (fun c => (stableSetoid B W s).r a c), W c * B c b)
            = ∑ c ∈ Finset.univ.filter (fun c => (stableSetoid B W s).r a c), W c * B b c from
            Finset.sum_congr rfl (fun c _ => by rw [hB c b])]
        have hm := stable_classMoment_eq B W s hd.2 a 1
        simp only [pow_one] at hm
        exact hm
      rw [hX, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    have hRHS : classWeight B W s a
          * (∑ c ∈ Finset.univ.filter (fun c => (stableSetoid B W s).r b c), W c * B a c)
        = ∑ d ∈ Finset.univ.filter (fun d => (stableSetoid B W s).r a d),
            ∑ c ∈ Finset.univ.filter (fun c => (stableSetoid B W s).r b c), W d * W c * B d c := by
      rw [classWeight, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mem_filter] at hd
      have hY : (∑ c ∈ Finset.univ.filter (fun c => (stableSetoid B W s).r b c), W c * B a c)
          = ∑ c ∈ Finset.univ.filter (fun c => (stableSetoid B W s).r b c), W c * B d c := by
        have hm := stable_classMoment_eq B W s hd.2 b 1
        simp only [pow_one] at hm
        exact hm
      rw [hY, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    rw [hLHS, hRHS, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun c _ => ?_))
    rw [mul_comm (W c) (W d), hB c d]
  rw [hLeq, hReq, ← mul_div_assoc, div_eq_div_iff hcwa.ne' hcwb.ne']
  linear_combination W b * hstar

/-- **Reverse inclusion: stable class ⟹ orbit.**

⚠️ **KNOWN FALSE as stated — DO NOT FILL THIS `sorry`** (filling it proves
`False`). `stableSetoid` is the fixed point of `refineRel`, which refines a vertex
by the multiset of `(neighbour class, edge value)` — i.e. it is exactly **1-WL /
color refinement**. The 1-WL partition is strictly *coarser* than the
automorphism-orbit partition in general, even with the hypotheses below:

* **Counterexample.** Any connected regular graph that is not vertex-transitive
  (e.g. the Frucht graph: 3-regular, twin-free, *asymmetric*). Color refinement
  on a regular graph stabilises at the single all-vertices class, so all vertices
  are `stableSetoid`-related; but the orbits are singletons. With `W ≡ 1` and
  `B` its `0/1` adjacency this satisfies symmetric + positive + twin-free, yet
  `stableSetoid`-related vertices are NOT orbit-related.

Equivalently: `avgMatrix` is a genuine *fractional* automorphism, and
**fractional-automorphism equivalence ≠ automorphism equivalence** (the Frucht
graph is fractionally vertex-transitive but not vertex-transitive). The proposed
"each supported permutation is an automorphism" (Birkhoff) step is precisely the
false `fractional-iso ⟹ iso` step.

What `stableSetoid` *does* certify is fractional-automorphism equivalence
(`vertexOrbitRel_imp_stable` is the true containment orbit ⊆ 1-WL class).

**To actually close `multiEvalOnOrbit_separates`** one needs refinement by the
*full rooted-multigraph evaluation hierarchy* (higher-order WL / the coherent
configuration generated by all `multiLabeledEvalK`), which is strictly stronger
than the 1-WL `refineRel`. This `sorry` is retained, frozen and clearly marked,
only to avoid disturbing the surrounding development. -/
theorem stable_imp_vertexOrbitRel (hB : ∀ i j, B i j = B j i) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j) {i j : Fin T}
    (h : (stableSetoid B W ⊤).r i j) : vertexOrbitRel B W i j := by
  sorry

end Refinement

end Graphon.Spectral
