/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Data.Real.Sqrt
import Graphon.SimpleRank

/-!
# Cycle–Krylov spectral slice (#70 square-moment descent)

The finite-dimensional linear algebra closing the cycle–Krylov–kernel proof of
square-moment descent (`docs/sqmoment-cycle-krylov.md`), kept in its own file
because it imports inner-product-space machinery that must not pollute
`Lovasz.lean` (known simp-conflict issue).

## Contents

* `inner_eq_zero_of_orthogonal_pos_powers` — the abstract lemma over a
  finite-dimensional real inner product space: if `A` is self-adjoint,
  `u ∈ range A`, and `e ⊥ A^q u` for all `q ≥ 1`, then `e ⊥ u`.
  Proof by orthogonal projection onto the positive-power Krylov span `K`:
  the residual `w = u - proj_K u` satisfies `A w = 0` (since `A² w ∈ K` and
  `‖A w‖² = ⟪w, A² w⟫ = 0`), hence `⟪w, u⟫ = ⟪w, A z⟫ = ⟪A w, z⟫ = 0`, hence
  `‖w‖² = 0`, so `u ∈ K` and `e ⊥ u`.
* `sqrtScale` / `conjAdj` — transport of the `W`-weighted inner product
  `wInner` to `EuclideanSpace ℝ (Fin T)` via `√W`-rescaling; `conjAdj` is the
  conjugated operator, i.e. the symmetric matrix
  `S(t,s) = √(W t) · B t s · √(W s)`.
* `wInner_eq_zero_of_iter_orthogonal` — the weighted instantiation in terms
  of `weightedAdj` / `weightedAdjIter`.
* `sqMoment_eq_of_closedWalkProfile_eq` — **the assembled spectral slice**:
  equal closed-walk profiles at all lengths ≥ 3 force equal square moments.
  After this, the remaining content of `sqMoment_descends_of_rootedProfileEquiv`
  is pure graph plumbing (rooted cycles realize `closedWalkProfile`, and rpe
  kills their differences).
-/

open scoped RealInnerProductSpace

namespace Graphon.Lovasz

/-! ### The abstract finite-dimensional lemma -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Krylov-kernel lemma**: in a finite-dimensional real inner product space,
if `A` is self-adjoint, `u` lies in the range of `A`, and `e` is orthogonal to
`A^q u` for every `q ≥ 1`, then `e` is orthogonal to `u` itself.

The "missing zeroth power" is recovered because `u ∈ range A` forces the
`ker A`-component of `u` to vanish. -/
theorem inner_eq_zero_of_orthogonal_pos_powers
    (A : E →ₗ[ℝ] E) (hA : ∀ x y : E, ⟪A x, y⟫ = ⟪x, A y⟫)
    {u : E} (hu : u ∈ LinearMap.range A)
    {e : E} (he : ∀ q : ℕ, ⟪e, (A ^ (q + 1)) u⟫ = 0) :
    ⟪e, u⟫ = 0 := by
  classical
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hu
  set K : Submodule ℝ E :=
    Submodule.span ℝ (Set.range fun q : ℕ => (A ^ (q + 1)) (A z)) with hKdef
  haveI : CompleteSpace K := FiniteDimensional.complete ℝ K
  -- A maps K into itself.
  have hinv : ∀ x ∈ K, A x ∈ K := by
    intro x hx
    rw [hKdef] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨q, rfl⟩ := hy
      refine Submodule.subset_span ⟨q + 1, ?_⟩
      show (A ^ (q + 1 + 1)) (A z) = A ((A ^ (q + 1)) (A z))
      rw [pow_succ' A (q + 1), Module.End.mul_apply]
    | zero => simp
    | add y y' _ _ hy hy' => rw [map_add]; exact Submodule.add_mem _ hy hy'
    | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy
  set p : E := K.starProjection (A z) with hpdef
  have hp_mem : p ∈ K := by
    rw [hpdef, Submodule.starProjection_apply]
    exact Submodule.coe_mem _
  set w : E := A z - p with hwdef
  have hw_orth : w ∈ Kᗮ := by
    rw [hwdef, hpdef]
    exact K.sub_starProjection_mem_orthogonal (A z)
  have hw_inner : ∀ v ∈ K, ⟪w, v⟫ = 0 := (K.mem_orthogonal' w).1 hw_orth
  -- A (A (A z)) is the q = 1 generator.
  have hAAu : A (A (A z)) ∈ K := by
    have hmem : (A ^ (1 + 1)) (A z) ∈ K := by
      rw [hKdef]
      exact Submodule.subset_span ⟨1, rfl⟩
    rwa [pow_succ', pow_one, Module.End.mul_apply] at hmem
  -- Hence A (A w) ∈ K, so A w = 0.
  have hAAw : A (A w) ∈ K := by
    have h2 : A (A p) ∈ K := hinv _ (hinv _ hp_mem)
    have hsub : A (A w) = A (A (A z)) - A (A p) := by rw [hwdef, map_sub, map_sub]
    rw [hsub]
    exact Submodule.sub_mem _ hAAu h2
  have hAw : A w = 0 := by
    have h0 : ⟪A w, A w⟫ = 0 := by
      rw [hA w (A w)]
      exact hw_inner _ hAAw
    exact inner_self_eq_zero.mp h0
  -- ⟪w, u⟫ = ⟪A w, z⟫ = 0, so ‖w‖² = 0 and u = p ∈ K.
  have hwu : ⟪w, A z⟫ = 0 := by
    rw [← hA w z, hAw, inner_zero_left]
  have hw0 : w = 0 := by
    have h0 : ⟪w, w⟫ = 0 := by
      calc ⟪w, w⟫ = ⟪w, A z - p⟫ := by rw [← hwdef]
        _ = ⟪w, A z⟫ - ⟪w, p⟫ := inner_sub_right _ _ _
        _ = 0 := by rw [hwu, hw_inner p hp_mem, sub_zero]
    exact inner_self_eq_zero.mp h0
  have hu_mem : A z ∈ K := by
    have hAzp : A z = p := by
      rw [hwdef] at hw0
      exact sub_eq_zero.mp hw0
    rw [hAzp]
    exact hp_mem
  -- e is orthogonal to every generator, hence to all of K, hence to u.
  have he_orth : ∀ v ∈ K, ⟪e, v⟫ = 0 := by
    intro v hv
    rw [hKdef] at hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨q, rfl⟩ := hy
      exact he q
    | zero => simp
    | add y y' _ _ hy hy' => rw [inner_add_right, hy, hy', add_zero]
    | smul c y _ hy => rw [inner_smul_right, hy, mul_zero]
  exact he_orth _ hu_mem

end Abstract

/-! ### Transport of the `W`-weighted form to Euclidean space -/

section Weighted

variable {T : ℕ}

/-- `√W`-rescaling into `EuclideanSpace ℝ (Fin T)`: an isometry from the
`wInner W` form to the standard inner product (for `W > 0`). -/
noncomputable def sqrtScale (W : Fin T → ℝ) (f : Fin T → ℝ) :
    EuclideanSpace ℝ (Fin T) :=
  WithLp.toLp 2 fun t => Real.sqrt (W t) * f t

/-- The conjugated weighted adjacency, as a plain function: the symmetric
matrix `S(t,s) = √(W t) · B t s · √(W s)` applied to `x`. -/
noncomputable def conjAdjFun (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (x : Fin T → ℝ) : Fin T → ℝ :=
  fun t => ∑ s : Fin T, Real.sqrt (W t) * B t s * Real.sqrt (W s) * x s

/-- The conjugated weighted adjacency as a linear endomorphism of
`EuclideanSpace ℝ (Fin T)`. -/
noncomputable def conjAdj (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    EuclideanSpace ℝ (Fin T) →ₗ[ℝ] EuclideanSpace ℝ (Fin T) where
  toFun x := WithLp.toLp 2 (conjAdjFun B W x.ofLp)
  map_add' x y := by
    have key : conjAdjFun B W (x.ofLp + y.ofLp) =
        conjAdjFun B W x.ofLp + conjAdjFun B W y.ofLp := by
      funext t
      show (∑ s : Fin T,
          Real.sqrt (W t) * B t s * Real.sqrt (W s) * (x.ofLp s + y.ofLp s)) =
        (∑ s : Fin T, Real.sqrt (W t) * B t s * Real.sqrt (W s) * x.ofLp s) +
        ∑ s : Fin T, Real.sqrt (W t) * B t s * Real.sqrt (W s) * y.ofLp s
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    show WithLp.toLp 2 (conjAdjFun B W (x + y).ofLp) = _
    rw [WithLp.ofLp_add, key, WithLp.toLp_add]
  map_smul' c x := by
    have key : conjAdjFun B W (c • x.ofLp) = c • conjAdjFun B W x.ofLp := by
      funext t
      show (∑ s : Fin T,
          Real.sqrt (W t) * B t s * Real.sqrt (W s) * (c * x.ofLp s)) =
        c * ∑ s : Fin T, Real.sqrt (W t) * B t s * Real.sqrt (W s) * x.ofLp s
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    show WithLp.toLp 2 (conjAdjFun B W (c • x).ofLp) = _
    rw [WithLp.ofLp_smul, key, WithLp.toLp_smul]
    rfl

@[simp] theorem conjAdj_apply (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (x : EuclideanSpace ℝ (Fin T)) :
    conjAdj B W x = WithLp.toLp 2 (conjAdjFun B W x.ofLp) := rfl

/-- The Euclidean inner product, concretely. -/
private theorem euc_inner_eq (x y : EuclideanSpace ℝ (Fin T)) :
    ⟪x, y⟫ = ∑ t : Fin T, x t * y t := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- `sqrtScale` carries `wInner W` to the Euclidean inner product. -/
theorem inner_sqrtScale (W : Fin T → ℝ) (hW : ∀ t, 0 < W t) (f g : Fin T → ℝ) :
    ⟪sqrtScale W f, sqrtScale W g⟫ = wInner W f g := by
  rw [euc_inner_eq]
  unfold wInner
  refine Finset.sum_congr rfl fun t _ => ?_
  show (Real.sqrt (W t) * f t) * (Real.sqrt (W t) * g t) = W t * f t * g t
  have h := Real.mul_self_sqrt (hW t).le
  linear_combination f t * g t * h

/-- `sqrtScale` intertwines `weightedAdj` and `conjAdj`. -/
theorem conjAdj_sqrtScale (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hW : ∀ t, 0 < W t) (f : Fin T → ℝ) :
    conjAdj B W (sqrtScale W f) = sqrtScale W (weightedAdj B W f) := by
  rw [conjAdj_apply]
  unfold sqrtScale
  congr 1
  funext t
  show (∑ s : Fin T,
      Real.sqrt (W t) * B t s * Real.sqrt (W s) * (Real.sqrt (W s) * f s)) =
    Real.sqrt (W t) * ∑ s : Fin T, W s * B t s * f s
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h := Real.mul_self_sqrt (hW s).le
  linear_combination Real.sqrt (W t) * B t s * f s * h

/-- `conjAdj` is self-adjoint for the Euclidean inner product (from `hB`). -/
theorem conjAdj_selfAdjoint (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (x y : EuclideanSpace ℝ (Fin T)) :
    ⟪conjAdj B W x, y⟫ = ⟪x, conjAdj B W y⟫ := by
  rw [euc_inner_eq, euc_inner_eq]
  show (∑ t : Fin T, conjAdjFun B W x.ofLp t * y t) =
    ∑ t : Fin T, x t * conjAdjFun B W y.ofLp t
  unfold conjAdjFun
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hB b a]
  ring

/-- `sqrtScale` intertwines iterates: `(conjAdj)^q ∘ sqrtScale = sqrtScale ∘ M^[q]`. -/
theorem conjAdj_pow_sqrtScale (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hW : ∀ t, 0 < W t) :
    ∀ (q : ℕ) (f : Fin T → ℝ),
      ((conjAdj B W) ^ q) (sqrtScale W f) = sqrtScale W (weightedAdjIter B W q f) := by
  intro q
  induction q with
  | zero =>
    intro f
    simp only [pow_zero, Module.End.one_apply]
    rfl
  | succ q ih =>
    intro f
    rw [pow_succ', Module.End.mul_apply, ih f, conjAdj_sqrtScale B W hW]
    rfl

/-- **The weighted Krylov-kernel lemma** (target shape of the spectral slice):
if `u` is in the range of `weightedAdj B W` and `eps` is `wInner`-orthogonal to
all positive `weightedAdjIter`-iterates of `u`, then `eps ⊥ u`. -/
theorem wInner_eq_zero_of_iter_orthogonal
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ t, 0 < W t)
    (eps u : Fin T → ℝ) (hu : ∃ z, weightedAdj B W z = u)
    (hortho : ∀ q : ℕ, wInner W eps (weightedAdjIter B W (q + 1) u) = 0) :
    wInner W eps u = 0 := by
  obtain ⟨z, hz⟩ := hu
  have hrange : sqrtScale W u ∈ LinearMap.range (conjAdj B W) := by
    refine LinearMap.mem_range.mpr ⟨sqrtScale W z, ?_⟩
    rw [conjAdj_sqrtScale B W hW, hz]
  have he : ∀ q : ℕ,
      ⟪sqrtScale W eps, ((conjAdj B W) ^ (q + 1)) (sqrtScale W u)⟫ = 0 := by
    intro q
    rw [conjAdj_pow_sqrtScale B W hW (q + 1) u, inner_sqrtScale W hW]
    exact hortho q
  have h := inner_eq_zero_of_orthogonal_pos_powers (conjAdj B W)
    (conjAdj_selfAdjoint B hB W) hrange he
  rwa [inner_sqrtScale W hW] at h

/-! ### The assembled spectral slice -/

/-- **Square moments from closed walks** — the spectral slice of the
cycle–Krylov proof, fully assembled: if two vertices have equal closed-walk
profiles at every length ≥ 3, their `W`-weighted square moments agree.

Combines (from `SimpleRank.lean`): `sqMoment_sub_eq_wInner` (gap = `⟪ε, u⟫_W`),
`rowSum_eq_weightedAdj` (`u ∈ Im M`), `closedWalkProfile_sub_eq_wInner`
(closed-walk diffs = `⟪ε, M^[q] u⟫_W`), and the weighted Krylov-kernel lemma
above. The remaining content of `sqMoment_descends_of_rootedProfileEquiv` is
graph plumbing: rooted cycles realize `closedWalkProfile` (the existing
focused sorry in `Lovasz.lean`), and rpe makes their profiles agree. -/
theorem sqMoment_eq_of_closedWalkProfile_eq
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ t, 0 < W t) (i j : Fin T)
    (hcw : ∀ m : ℕ, closedWalkProfile B W i (m + 3) = closedWalkProfile B W j (m + 3)) :
    sqMoment B W i = sqMoment B W j := by
  have hu : ∃ z, weightedAdj B W z = rowSum B i j :=
    ⟨_, (rowSum_eq_weightedAdj B hB W hW i j).symm⟩
  have hortho : ∀ q : ℕ,
      wInner W (rowDiff B i j) (weightedAdjIter B W (q + 1) (rowSum B i j)) = 0 := by
    intro q
    rw [← closedWalkProfile_sub_eq_wInner B hB W i j (q + 1)]
    show closedWalkProfile B W i (q + 3) - closedWalkProfile B W j (q + 3) = 0
    rw [hcw q, sub_self]
  have h0 := wInner_eq_zero_of_iter_orthogonal B hB W hW
    (rowDiff B i j) (rowSum B i j) hu hortho
  have hgap := sqMoment_sub_eq_wInner B W i j
  have hzero : sqMoment B W i - sqMoment B W j = 0 := hgap.trans h0
  linarith

/-! ### The assembled theorem: square-moment descent -/

/-- **Square-moment descent** (#70 minimal test case) — **PROVED**.

If `i` and `j` are rooted-profile equivalent (twin-freeness NOT needed), their
`W`-weighted square moments agree. This was the designated first obstruction
beyond the simple rooted algebra: `∑ t, W t * B i t ^ 2` is inherently a
multigraph observable (double edge `i–t`), yet rooted simple CYCLES pin it.

Assembly of the cycle–Krylov–kernel proof (`docs/sqmoment-cycle-krylov.md`):
rpe applied to `rootedCycleGraph (m+1)` + the bridge
`rootedProfile_rootedCycleGraph_eq_closedWalkProfile` (proved in `Lovasz.lean`;
its "focused sorry" docstring is STALE) give equal closed-walk profiles at all
lengths ≥ 3, and `sqMoment_eq_of_closedWalkProfile_eq` (the spectral slice)
concludes.

Supersedes the version formerly in `SimpleRank.lean` that was derived from the
(still open, strictly stronger) `classwise_sqMoment_descends`; this proof is
sorry-free and drops the `htwin` hypothesis. -/
theorem sqMoment_descends_of_rootedProfileEquiv {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    {i j : Fin T} (h : rootedProfileEquiv B W i j) :
    sqMoment B W i = sqMoment B W j := by
  refine sqMoment_eq_of_closedWalkProfile_eq B hB W hW i j fun m => ?_
  rw [← rootedProfile_rootedCycleGraph_eq_closedWalkProfile B hB W i,
    ← rootedProfile_rootedCycleGraph_eq_closedWalkProfile B hB W j]
  exact h (m + 2) (rootedCycleGraph (m + 1))

end Weighted

end Graphon.Lovasz
