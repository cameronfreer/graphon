/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
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

/-- **Krylov span membership for range elements** — the projection core of the
spectral slice, extracted as a standalone lemma: if `A` is self-adjoint and
`u ∈ range A`, then `u` lies in the span of its own positive `A`-powers.
(The "missing zeroth power" is recovered because `u ∈ range A` forces the
`ker A`-component of `u` to vanish.) -/
theorem mem_span_pos_powers_of_mem_range
    (A : E →ₗ[ℝ] E) (hA : ∀ x y : E, ⟪A x, y⟫ = ⟪x, A y⟫)
    {u : E} (hu : u ∈ LinearMap.range A) :
    u ∈ Submodule.span ℝ (Set.range fun q : ℕ => (A ^ (q + 1)) u) := by
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
  have hAzp : A z = p := by
    rw [hwdef] at hw0
    exact sub_eq_zero.mp hw0
  rw [hAzp]
  exact hp_mem

/-- **Krylov-kernel lemma**: in a finite-dimensional real inner product space,
if `A` is self-adjoint, `u` lies in the range of `A`, and `e` is orthogonal to
`A^q u` for every `q ≥ 1`, then `e` is orthogonal to `u` itself. -/
theorem inner_eq_zero_of_orthogonal_pos_powers
    (A : E →ₗ[ℝ] E) (hA : ∀ x y : E, ⟪A x, y⟫ = ⟪x, A y⟫)
    {u : E} (hu : u ∈ LinearMap.range A)
    {e : E} (he : ∀ q : ℕ, ⟪e, (A ^ (q + 1)) u⟫ = 0) :
    ⟪e, u⟫ = 0 := by
  have hu_mem := mem_span_pos_powers_of_mem_range A hA hu
  have he_orth : ∀ w ∈ Submodule.span ℝ (Set.range fun q : ℕ => (A ^ (q + 1)) u),
      ⟪e, w⟫ = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨q, rfl⟩ := hy
      exact he q
    | zero => simp
    | add y y' _ _ hy hy' => rw [inner_add_right, hy, hy', add_zero]
    | smul c y _ hy => rw [inner_smul_right, hy, mul_zero]
  exact he_orth _ hu_mem

/-! #### The direct-sum (common-coefficient) lemma -/

/-- The block-diagonal operator `A ⊕ A` on `WithLp 2 (E × E)`. -/
noncomputable def prodMapL2 (A : E →ₗ[ℝ] E) :
    WithLp 2 (E × E) →ₗ[ℝ] WithLp 2 (E × E) :=
  (WithLp.linearEquiv 2 ℝ (E × E)).symm.toLinearMap ∘ₗ
    (A.prodMap A) ∘ₗ (WithLp.linearEquiv 2 ℝ (E × E)).toLinearMap

omit [FiniteDimensional ℝ E] in
theorem prodMapL2_apply (A : E →ₗ[ℝ] E) (x : WithLp 2 (E × E)) :
    prodMapL2 A x =
      WithLp.toLp 2 (A (WithLp.ofLp x).1, A (WithLp.ofLp x).2) := rfl

omit [FiniteDimensional ℝ E] in
/-- `prodMapL2 A` inherits self-adjointness from `A` (for the `L²` product
inner product). -/
theorem prodMapL2_selfAdjoint (A : E →ₗ[ℝ] E)
    (hA : ∀ x y : E, ⟪A x, y⟫ = ⟪x, A y⟫) (x y : WithLp 2 (E × E)) :
    ⟪prodMapL2 A x, y⟫ = ⟪x, prodMapL2 A y⟫ := by
  simp only [prodMapL2_apply, WithLp.prod_inner_apply]
  rw [hA (WithLp.ofLp x).1 (WithLp.ofLp y).1, hA (WithLp.ofLp x).2 (WithLp.ofLp y).2]

omit [FiniteDimensional ℝ E] in
/-- Powers of `prodMapL2 A` act componentwise as powers of `A`. -/
theorem prodMapL2_pow_toLp (A : E →ₗ[ℝ] E) (q : ℕ) (a b : E) :
    ((prodMapL2 A) ^ q) (WithLp.toLp 2 (a, b)) =
      WithLp.toLp 2 ((A ^ q) a, (A ^ q) b) := by
  induction q with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ q ih =>
    rw [pow_succ' (prodMapL2 A) q, Module.End.mul_apply, ih, prodMapL2_apply]
    simp only [pow_succ' A q, Module.End.mul_apply]

/-- **Common Krylov coefficients for a pair** (the direct-sum trick): if `u`
and `v` both lie in the range of a self-adjoint `A`, then there are COMMON
coefficients expressing each of them as a combination of its own positive
`A`-powers. Obtained by applying `mem_span_pos_powers_of_mem_range` to the
block operator on `WithLp 2 (E × E)` and projecting the two coordinates.

Note a triple (or longer) version with REPEATED vectors needs nothing more:
the slots of a multilinear form repeat `u` or `v`, and this pair of common
expansions feeds every slot. -/
theorem pair_mem_common_pos_power_span
    (A : E →ₗ[ℝ] E) (hA : ∀ x y : E, ⟪A x, y⟫ = ⟪x, A y⟫)
    {u v : E} (hu : u ∈ LinearMap.range A) (hv : v ∈ LinearMap.range A) :
    ∃ (s : Finset ℕ) (c : ℕ → ℝ),
      (∑ q ∈ s, c q • (A ^ (q + 1)) u) = u ∧
      (∑ q ∈ s, c q • (A ^ (q + 1)) v) = v := by
  classical
  obtain ⟨zu, hzu⟩ := LinearMap.mem_range.mp hu
  obtain ⟨zv, hzv⟩ := LinearMap.mem_range.mp hv
  have hrange : WithLp.toLp 2 (u, v) ∈ LinearMap.range (prodMapL2 A) := by
    refine LinearMap.mem_range.mpr ⟨WithLp.toLp 2 (zu, zv), ?_⟩
    rw [prodMapL2_apply]
    show WithLp.toLp 2 (A zu, A zv) = _
    rw [hzu, hzv]
  have hmem := mem_span_pos_powers_of_mem_range (prodMapL2 A)
    (prodMapL2_selfAdjoint A hA) hrange
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hmem
  obtain ⟨c, hc⟩ := hmem
  rw [Finsupp.sum] at hc
  simp only [prodMapL2_pow_toLp] at hc
  have hc' : (∑ q ∈ c.support,
      ((c q • (A ^ (q + 1)) u, c q • (A ^ (q + 1)) v) : E × E)) = (u, v) := by
    have h := congrArg (WithLp.linearEquiv 2 ℝ (E × E)) hc
    rw [map_sum] at h
    simpa [WithLp.coe_linearEquiv, Prod.smul_mk] using h
  refine ⟨c.support, fun q => c q, ?_, ?_⟩
  · have := congrArg Prod.fst hc'
    simpa [Prod.fst_sum] using this
  · have := congrArg Prod.snd hc'
    simpa [Prod.snd_sum] using this

/-! #### The k-fold direct-sum (family common-coefficient) lemma -/

/-- The block-diagonal operator `⨁_{i : Fin m} A` on `PiLp 2 (fun _ : Fin m => E)`
(the `Fin m`-fold generalization of `prodMapL2`). -/
noncomputable def piMapL2 (m : ℕ) (A : E →ₗ[ℝ] E) :
    PiLp 2 (fun _ : Fin m => E) →ₗ[ℝ] PiLp 2 (fun _ : Fin m => E) :=
  (WithLp.linearEquiv 2 ℝ (∀ _ : Fin m, E)).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun i => A ∘ₗ LinearMap.proj i) ∘ₗ
    (WithLp.linearEquiv 2 ℝ (∀ _ : Fin m, E)).toLinearMap

omit [FiniteDimensional ℝ E] in
theorem piMapL2_apply (m : ℕ) (A : E →ₗ[ℝ] E) (x : PiLp 2 (fun _ : Fin m => E)) :
    piMapL2 m A x = WithLp.toLp 2 (fun i => A (WithLp.ofLp x i)) := rfl

omit [FiniteDimensional ℝ E] in
/-- `piMapL2 m A` inherits self-adjointness from `A`. -/
theorem piMapL2_selfAdjoint (m : ℕ) (A : E →ₗ[ℝ] E)
    (hA : ∀ x y : E, ⟪A x, y⟫ = ⟪x, A y⟫) (x y : PiLp 2 (fun _ : Fin m => E)) :
    ⟪piMapL2 m A x, y⟫ = ⟪x, piMapL2 m A y⟫ := by
  simp only [piMapL2_apply, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => hA _ _

omit [FiniteDimensional ℝ E] in
/-- Powers of `piMapL2 m A` act componentwise as powers of `A`. -/
theorem piMapL2_pow_toLp (m : ℕ) (A : E →ₗ[ℝ] E) (q : ℕ) (w : Fin m → E) :
    ((piMapL2 m A) ^ q) (WithLp.toLp 2 w) = WithLp.toLp 2 (fun i => (A ^ q) (w i)) := by
  induction q with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ q ih =>
    rw [pow_succ' (piMapL2 m A) q, Module.End.mul_apply, ih, piMapL2_apply]
    refine congrArg (WithLp.toLp 2) (funext fun i => ?_)
    show A ((A ^ q) (w i)) = (A ^ (q + 1)) (w i)
    rw [pow_succ' A q, Module.End.mul_apply]

/-- **Common Krylov coefficients for a finite family** (the k-fold direct-sum
trick): if every member of a family `w : Fin m → E` lies in the range of a
self-adjoint `A`, there are COMMON coefficients expressing each member as a
combination of its own positive `A`-powers. Generalizes
`pair_mem_common_pos_power_span`; obtained from the block operator on
`PiLp 2 (fun _ : Fin m => E)` by projecting each coordinate. -/
theorem common_krylov_coefficients_fin (m : ℕ)
    (A : E →ₗ[ℝ] E) (hA : ∀ x y : E, ⟪A x, y⟫ = ⟪x, A y⟫)
    {w : Fin m → E} (hw : ∀ i, w i ∈ LinearMap.range A) :
    ∃ (s : Finset ℕ) (c : ℕ → ℝ),
      ∀ i, (∑ q ∈ s, c q • (A ^ (q + 1)) (w i)) = w i := by
  classical
  choose z hz using fun i => LinearMap.mem_range.mp (hw i)
  have hrange : WithLp.toLp 2 w ∈ LinearMap.range (piMapL2 m A) := by
    refine LinearMap.mem_range.mpr ⟨WithLp.toLp 2 z, ?_⟩
    rw [piMapL2_apply]
    exact congrArg (WithLp.toLp 2) (funext hz)
  have hmem := mem_span_pos_powers_of_mem_range (piMapL2 m A)
    (piMapL2_selfAdjoint m A hA) hrange
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hmem
  obtain ⟨c, hc⟩ := hmem
  rw [Finsupp.sum] at hc
  simp only [piMapL2_pow_toLp] at hc
  have hc' : ∀ i, (∑ q ∈ c.support, c q • (A ^ (q + 1)) (w i)) = w i := by
    intro i
    have h := congrArg (WithLp.linearEquiv 2 ℝ (∀ _ : Fin m, E)) hc
    rw [map_sum] at h
    have h2 := congrArg (fun v : ∀ _ : Fin m, E => v i) h
    simpa [WithLp.coe_linearEquiv, Finset.sum_apply] using h2
  exact ⟨c.support, fun q => c q, hc'⟩

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

/-- `sqrtScale` is injective for positive weights. -/
theorem sqrtScale_injective (W : Fin T → ℝ) (hW : ∀ t, 0 < W t) :
    Function.Injective (sqrtScale W) := by
  intro f g hfg
  funext t
  have h : Real.sqrt (W t) * f t = Real.sqrt (W t) * g t :=
    congrArg (fun x : EuclideanSpace ℝ (Fin T) => WithLp.ofLp x t) hfg
  exact mul_left_cancel₀ (Real.sqrt_ne_zero'.mpr (hW t)) h

/-- `sqrtScale` commutes with scalar multiples. -/
theorem sqrtScale_smul (W : Fin T → ℝ) (c : ℝ) (f : Fin T → ℝ) :
    sqrtScale W (c • f) = c • sqrtScale W f := by
  unfold sqrtScale
  rw [← WithLp.toLp_smul]
  congr 1
  funext t
  show Real.sqrt (W t) * (c * f t) = c * (Real.sqrt (W t) * f t)
  ring

/-- `sqrtScale` commutes with finite sums. -/
theorem sqrtScale_sum (W : Fin T → ℝ) {ι : Type*} (s : Finset ι)
    (F : ι → Fin T → ℝ) :
    sqrtScale W (∑ q ∈ s, F q) = ∑ q ∈ s, sqrtScale W (F q) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold sqrtScale
    rw [show (fun t => Real.sqrt (W t) * (0 : Fin T → ℝ) t) = (0 : Fin T → ℝ) from
      funext fun t => by simp]
    rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    unfold sqrtScale
    rw [← WithLp.toLp_add]
    congr 1
    funext t
    show Real.sqrt (W t) * (F a t + (∑ q ∈ s, F q) t) = _
    have : (∑ q ∈ s, F q) t = ∑ q ∈ s, F q t := by
      rw [Finset.sum_apply]
    rw [this]
    show _ = Real.sqrt (W t) * F a t + Real.sqrt (W t) * (∑ q ∈ s, F q) t
    rw [this]
    ring

/-- **Common Krylov coefficients in the weighted setting**: if `f` and `g`
both lie in the range of `weightedAdj B W`, there are COMMON coefficients
expressing each as a combination of its own positive `weightedAdjIter`-powers.
This is the algebraic core of the K₂,₃-arms cube proof (and of the k ≥ 4
lift): every slot of the multilinear polarization can be expanded with the
SAME coefficient family. -/
theorem weightedAdj_pair_common_coeffs
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ t, 0 < W t)
    {f g : Fin T → ℝ}
    (hf : ∃ z, weightedAdj B W z = f) (hg : ∃ z, weightedAdj B W z = g) :
    ∃ (s : Finset ℕ) (c : ℕ → ℝ),
      (∑ q ∈ s, c q • weightedAdjIter B W (q + 1) f) = f ∧
      (∑ q ∈ s, c q • weightedAdjIter B W (q + 1) g) = g := by
  obtain ⟨zf, hzf⟩ := hf
  obtain ⟨zg, hzg⟩ := hg
  have hf' : sqrtScale W f ∈ LinearMap.range (conjAdj B W) :=
    LinearMap.mem_range.mpr ⟨sqrtScale W zf, by rw [conjAdj_sqrtScale B W hW, hzf]⟩
  have hg' : sqrtScale W g ∈ LinearMap.range (conjAdj B W) :=
    LinearMap.mem_range.mpr ⟨sqrtScale W zg, by rw [conjAdj_sqrtScale B W hW, hzg]⟩
  obtain ⟨s, c, h1, h2⟩ := pair_mem_common_pos_power_span (conjAdj B W)
    (conjAdj_selfAdjoint B hB W) hf' hg'
  have pull : ∀ h : Fin T → ℝ,
      (∑ q ∈ s, c q • ((conjAdj B W) ^ (q + 1)) (sqrtScale W h)) =
        sqrtScale W (∑ q ∈ s, c q • weightedAdjIter B W (q + 1) h) := by
    intro h
    rw [sqrtScale_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [conjAdj_pow_sqrtScale B W hW (q + 1) h, sqrtScale_smul]
  refine ⟨s, c, ?_, ?_⟩
  · exact sqrtScale_injective W hW (by rw [← pull f]; exact h1)
  · exact sqrtScale_injective W hW (by rw [← pull g]; exact h2)

/-! #### Trilinear polarization — the graph-free cube core -/

/-- The weighted trilinear form `T₃(f, g, h) = ∑ t, W t * f t * g t * h t`. -/
noncomputable def wTriple (W f g h : Fin T → ℝ) : ℝ :=
  ∑ t : Fin T, W t * f t * g t * h t

theorem wTriple_comm₁₂ (W f g h : Fin T → ℝ) :
    wTriple W f g h = wTriple W g f h :=
  Finset.sum_congr rfl fun _ _ => by ring

theorem wTriple_comm₁₃ (W f g h : Fin T → ℝ) :
    wTriple W f g h = wTriple W h g f :=
  Finset.sum_congr rfl fun _ _ => by ring

theorem wTriple_sum₁ {ι : Type*} (W : Fin T → ℝ) (s : Finset ι)
    (F : ι → Fin T → ℝ) (g h : Fin T → ℝ) :
    wTriple W (∑ a ∈ s, F a) g h = ∑ a ∈ s, wTriple W (F a) g h := by
  unfold wTriple
  have hpt : ∀ t, W t * (∑ a ∈ s, F a) t * g t * h t =
      ∑ a ∈ s, W t * F a t * g t * h t := by
    intro t
    rw [Finset.sum_apply, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  simp only [hpt]
  rw [Finset.sum_comm]

theorem wTriple_smul₁ (W : Fin T → ℝ) (r : ℝ) (f g h : Fin T → ℝ) :
    wTriple W (r • f) g h = r * wTriple W f g h := by
  unfold wTriple
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  show W t * (r * f t) * g t * h t = r * (W t * f t * g t * h t)
  ring

theorem wTriple_sum₂ {ι : Type*} (W : Fin T → ℝ) (s : Finset ι)
    (f : Fin T → ℝ) (G : ι → Fin T → ℝ) (h : Fin T → ℝ) :
    wTriple W f (∑ b ∈ s, G b) h = ∑ b ∈ s, wTriple W f (G b) h := by
  rw [wTriple_comm₁₂, wTriple_sum₁]
  exact Finset.sum_congr rfl fun b _ => wTriple_comm₁₂ W (G b) f h

theorem wTriple_smul₂ (W : Fin T → ℝ) (r : ℝ) (f g h : Fin T → ℝ) :
    wTriple W f (r • g) h = r * wTriple W f g h := by
  rw [wTriple_comm₁₂, wTriple_smul₁, wTriple_comm₁₂]

theorem wTriple_sum₃ {ι : Type*} (W : Fin T → ℝ) (s : Finset ι)
    (f g : Fin T → ℝ) (H : ι → Fin T → ℝ) :
    wTriple W f g (∑ d ∈ s, H d) = ∑ d ∈ s, wTriple W f g (H d) := by
  rw [wTriple_comm₁₃, wTriple_sum₁]
  exact Finset.sum_congr rfl fun d _ => wTriple_comm₁₃ W (H d) g f

theorem wTriple_smul₃ (W : Fin T → ℝ) (r : ℝ) (f g h : Fin T → ℝ) :
    wTriple W f g (r • h) = r * wTriple W f g h := by
  rw [wTriple_comm₁₃, wTriple_smul₁, wTriple_comm₁₃]

/-- **Pointwise cube factorization**:
`4·gap₃ = 3·T₃(ε, u, u) + T₃(ε, ε, ε)` (from
`4(x³ - y³) = 3(x-y)(x+y)² + (x-y)³`). -/
theorem cube_gap_polarization (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (i j : Fin T) :
    4 * ((∑ t : Fin T, W t * B i t ^ 3) - ∑ t : Fin T, W t * B j t ^ 3) =
      3 * wTriple W (rowDiff B i j) (rowSum B i j) (rowSum B i j) +
        wTriple W (rowDiff B i j) (rowDiff B i j) (rowDiff B i j) := by
  unfold wTriple rowDiff rowSum
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- `ε = rowDiff` is also in the range of `weightedAdj` (mirror of
`rowSum_eq_weightedAdj`). -/
theorem rowDiff_eq_weightedAdj (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (hW : ∀ t, 0 < W t)
    (i j : Fin T) :
    rowDiff B i j = weightedAdj B W
      (fun t => (if t = i then 1 else 0) / W t - (if t = j then 1 else 0) / W t) := by
  classical
  have key : ∀ a x : Fin T,
      (∑ t : Fin T, W t * B x t * ((if t = a then (1 : ℝ) else 0) / W t)) = B x a := by
    intro a x
    rw [Finset.sum_eq_single a]
    · rw [if_pos rfl, mul_one_div, mul_comm (W a) (B x a), mul_div_assoc,
        div_self (hW a).ne', mul_one]
    · intro t _ ht
      rw [if_neg ht, zero_div, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ a) h
  funext x
  unfold rowDiff weightedAdj
  rw [show (∑ t : Fin T, W t * B x t *
        ((if t = i then (1 : ℝ) else 0) / W t - (if t = j then 1 else 0) / W t)) =
      ∑ t : Fin T, (W t * B x t * ((if t = i then (1 : ℝ) else 0) / W t) -
        W t * B x t * ((if t = j then 1 else 0) / W t)) from
    Finset.sum_congr rfl fun t _ => by ring]
  rw [Finset.sum_sub_distrib, key i x, key j x, hB x i, hB x j]

/-- **The polarized cube observable** (algebraic form): the trilinear
polarization of the rooted K₂,₃-with-arms profile difference at arm lengths
`(a, b, c)` — one `ε`-placement per root edge, plus the all-`ε` term. The graph
slice will identify `4 ·` (the K₂,₃-arms profile difference) with this. -/
noncomputable def polarizedCubeObs (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (i j : Fin T) (a b c : ℕ) : ℝ :=
  wTriple W (weightedAdjIter B W a (rowDiff B i j))
      (weightedAdjIter B W b (rowSum B i j))
      (weightedAdjIter B W c (rowSum B i j)) +
    wTriple W (weightedAdjIter B W a (rowSum B i j))
      (weightedAdjIter B W b (rowDiff B i j))
      (weightedAdjIter B W c (rowSum B i j)) +
    wTriple W (weightedAdjIter B W a (rowSum B i j))
      (weightedAdjIter B W b (rowSum B i j))
      (weightedAdjIter B W c (rowDiff B i j)) +
    wTriple W (weightedAdjIter B W a (rowDiff B i j))
      (weightedAdjIter B W b (rowDiff B i j))
      (weightedAdjIter B W c (rowDiff B i j))

/-- **Triple expansion with common coefficients**: a trilinear form evaluated
at three vectors, each given by a (shared-coefficient) finite expansion,
equals the triple sum of coefficient-weighted evaluations. -/
private theorem wTriple_triple_expansion {ι : Type*} (W : Fin T → ℝ)
    (s : Finset ι) (c : ι → ℝ) (F G H : ι → Fin T → ℝ) (f g h : Fin T → ℝ)
    (hf : (∑ a ∈ s, c a • F a) = f) (hg : (∑ b ∈ s, c b • G b) = g)
    (hh : (∑ d ∈ s, c d • H d) = h) :
    wTriple W f g h = ∑ a ∈ s, ∑ b ∈ s, ∑ d ∈ s,
      c a * c b * c d * wTriple W (F a) (G b) (H d) := by
  rw [← hf, wTriple_sum₁]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [wTriple_smul₁, ← hg, wTriple_sum₂, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [wTriple_smul₂, ← hh, wTriple_sum₃, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [wTriple_smul₃]
  ring

/-- **The graph-free cube core**: if every polarized cube observable (at
positive arm lengths) vanishes, the cube gap is zero. With the (separate)
graph slice identifying `polarizedCubeObs` with `4 ·` the rooted K₂,₃-arms
profile difference, this reduces `cubeMoment_descends_of_rootedProfileEquiv`
to pure graph plumbing. -/
theorem cubeGap_eq_zero_of_polarized_obs (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (hW : ∀ t, 0 < W t)
    (i j : Fin T)
    (hobs : ∀ a b c : ℕ, polarizedCubeObs B W i j (a + 1) (b + 1) (c + 1) = 0) :
    ∑ t : Fin T, W t * B i t ^ 3 = ∑ t : Fin T, W t * B j t ^ 3 := by
  obtain ⟨s, c, hε, hu⟩ := weightedAdj_pair_common_coeffs B hB W hW
    ⟨_, (rowDiff_eq_weightedAdj B hB W hW i j).symm⟩
    ⟨_, (rowSum_eq_weightedAdj B hB W hW i j).symm⟩
  -- the four expansions of the trilinear pieces through the COMMON coefficients
  have e1 := wTriple_triple_expansion W s c _ _ _ _ _ _ hε hu hu
  have e2 := wTriple_triple_expansion W s c _ _ _ _ _ _ hu hε hu
  have e3 := wTriple_triple_expansion W s c _ _ _ _ _ _ hu hu hε
  have e4 := wTriple_triple_expansion W s c _ _ _ _ _ _ hε hε hε
  -- the total coefficient-weighted observable sum vanishes
  have htotal : (∑ a ∈ s, ∑ b ∈ s, ∑ d ∈ s,
      c a * c b * c d * polarizedCubeObs B W i j (a + 1) (b + 1) (d + 1)) = 0 :=
    Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun d _ => by rw [hobs a b d, mul_zero]
  -- split each observable into its four trilinear pieces and regroup
  have hsummand : ∀ a b d : ℕ,
      c a * c b * c d * polarizedCubeObs B W i j (a + 1) (b + 1) (d + 1) =
        c a * c b * c d * wTriple W (weightedAdjIter B W (a + 1) (rowDiff B i j))
          (weightedAdjIter B W (b + 1) (rowSum B i j))
          (weightedAdjIter B W (d + 1) (rowSum B i j)) +
        c a * c b * c d * wTriple W (weightedAdjIter B W (a + 1) (rowSum B i j))
          (weightedAdjIter B W (b + 1) (rowDiff B i j))
          (weightedAdjIter B W (d + 1) (rowSum B i j)) +
        c a * c b * c d * wTriple W (weightedAdjIter B W (a + 1) (rowSum B i j))
          (weightedAdjIter B W (b + 1) (rowSum B i j))
          (weightedAdjIter B W (d + 1) (rowDiff B i j)) +
        c a * c b * c d * wTriple W (weightedAdjIter B W (a + 1) (rowDiff B i j))
          (weightedAdjIter B W (b + 1) (rowDiff B i j))
          (weightedAdjIter B W (d + 1) (rowDiff B i j)) := by
    intro a b d
    unfold polarizedCubeObs
    ring
  have hsplit : (∑ a ∈ s, ∑ b ∈ s, ∑ d ∈ s,
      c a * c b * c d * polarizedCubeObs B W i j (a + 1) (b + 1) (d + 1)) =
      wTriple W (rowDiff B i j) (rowSum B i j) (rowSum B i j) +
      wTriple W (rowSum B i j) (rowDiff B i j) (rowSum B i j) +
      wTriple W (rowSum B i j) (rowSum B i j) (rowDiff B i j) +
      wTriple W (rowDiff B i j) (rowDiff B i j) (rowDiff B i j) := by
    simp only [hsummand, Finset.sum_add_distrib]
    rw [← e1, ← e2, ← e3, ← e4]
  rw [hsplit] at htotal
  -- conclude: 4·gap = 3 T(ε,u,u) + T(ε,ε,ε) = the vanishing total
  have hgap := cube_gap_polarization B W i j
  have hc₁₂ := wTriple_comm₁₂ W (rowDiff B i j) (rowSum B i j) (rowSum B i j)
  have hc₁₃ := wTriple_comm₁₃ W (rowDiff B i j) (rowSum B i j) (rowSum B i j)
  rw [← hc₁₂, ← hc₁₃] at htotal
  nlinarith [hgap, htotal]

/-! #### k-linear polarization — the graph-free power-moment core (k ≥ 4 lift) -/

/-- The weighted `k`-linear form `T_k(f) = ∑ t, W t * ∏ l, f l t`
(the `Fin k`-slot generalization of `wTriple`). -/
noncomputable def wMulti (k : ℕ) (W : Fin T → ℝ) (f : Fin k → Fin T → ℝ) : ℝ :=
  ∑ t : Fin T, W t * ∏ l : Fin k, f l t

/-- **Multilinear expansion with common coefficients** (k-ary analog of
`wTriple_triple_expansion`, in one shot via `Finset.prod_univ_sum`): a k-linear
form whose every slot has a shared-coefficient finite expansion equals the sum
over coefficient tuples of weighted evaluations. -/
theorem wMulti_expansion {ι : Type*} [DecidableEq ι] (k : ℕ) (W : Fin T → ℝ)
    (s : Finset ι) (c : ι → ℝ) (F : Fin k → ι → Fin T → ℝ)
    (f : Fin k → Fin T → ℝ) (hf : ∀ l, (∑ a ∈ s, c a • F l a) = f l) :
    wMulti k W f =
      ∑ φ ∈ Fintype.piFinset (fun _ : Fin k => s),
        (∏ l : Fin k, c (φ l)) * wMulti k W (fun l => F l (φ l)) := by
  unfold wMulti
  have hpt : ∀ t : Fin T, (∏ l : Fin k, f l t) =
      ∑ φ ∈ Fintype.piFinset (fun _ : Fin k => s),
        ∏ l : Fin k, c (φ l) * F l (φ l) t := by
    intro t
    have hslot : ∀ l : Fin k, f l t = ∑ a ∈ s, c a * F l a t := by
      intro l
      rw [← hf l, Finset.sum_apply]
      exact Finset.sum_congr rfl fun a _ => rfl
    calc (∏ l : Fin k, f l t) = ∏ l : Fin k, ∑ a ∈ s, c a * F l a t :=
          Finset.prod_congr rfl fun l _ => hslot l
      _ = _ := Finset.prod_univ_sum _ _
  simp only [hpt, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun φ _ => ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

/-- **Pointwise k-th power polarization**: `2^k (x^k − y^k)` is `2 ·` the sum
over ODD subsets `S ⊆ Fin k` of the slot products with `x − y` on `S` and
`x + y` off `S` (binomial expansion of `(u+ε)^k − (u−ε)^k`; even subsets
cancel, odd double). -/
private theorem pow_sub_pow_expand (k : ℕ) (x y : ℝ) :
    2 ^ k * (x ^ k - y ^ k) =
      2 * ∑ S ∈ Finset.univ.powerset.filter (fun S : Finset (Fin k) => Odd S.card),
        ∏ l : Fin k, (if l ∈ S then x - y else x + y) := by
  classical
  have h1 : (2 : ℝ) ^ k * x ^ k =
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        (∏ _l ∈ S, (x - y)) * ∏ _l ∈ Finset.univ \ S, (x + y) := by
    rw [← Finset.prod_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      show (x - y) + (x + y) = 2 * x by ring, mul_pow]
  have h2 : (2 : ℝ) ^ k * y ^ k =
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        (∏ _l ∈ S, -(x - y)) * ∏ _l ∈ Finset.univ \ S, (x + y) := by
    rw [← Finset.prod_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      show -(x - y) + (x + y) = 2 * y by ring, mul_pow]
  rw [mul_sub, h1, h2, ← Finset.sum_sub_distrib,
    ← Finset.sum_filter_add_sum_filter_not
      ((Finset.univ : Finset (Fin k)).powerset) (fun S => Odd S.card)]
  have heven : (∑ S ∈ ((Finset.univ : Finset (Fin k)).powerset).filter
      (fun S => ¬Odd S.card),
        ((∏ _l ∈ S, (x - y)) * (∏ _l ∈ Finset.univ \ S, (x + y)) -
          (∏ _l ∈ S, -(x - y)) * ∏ _l ∈ Finset.univ \ S, (x + y))) = 0 :=
    Finset.sum_eq_zero fun S hS => by
      have he : Even S.card :=
        Nat.not_odd_iff_even.mp (Finset.mem_filter.mp hS).2
      rw [Finset.prod_const, Finset.prod_const, Finset.prod_const, he.neg_pow,
        sub_self]
  rw [heven, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  have ho : Odd S.card := (Finset.mem_filter.mp hS).2
  have hsplit : (∏ l : Fin k, (if l ∈ S then x - y else x + y)) =
      (x - y) ^ S.card * (x + y) ^ (Finset.univ \ S).card := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const,
      Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sdiff_eq_filter]
  rw [hsplit, Finset.prod_const, Finset.prod_const, Finset.prod_const, ho.neg_pow]
  ring

/-- **k-th power-gap polarization** (sum form): the weighted power-moment gap
polarizes into the odd-subset `wMulti` evaluations of `(ε, u)`-slot
assignments. -/
theorem pow_gap_polarization (k : ℕ) (W : Fin T → ℝ) (f g : Fin T → ℝ) :
    2 ^ k * ((∑ t : Fin T, W t * f t ^ k) - ∑ t : Fin T, W t * g t ^ k) =
      2 * ∑ S ∈ Finset.univ.powerset.filter (fun S : Finset (Fin k) => Odd S.card),
        wMulti k W (fun l => if l ∈ S then (fun t => f t - g t)
          else fun t => f t + g t) := by
  classical
  unfold wMulti
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  have hswap : (2 : ℝ) * ∑ S ∈ Finset.univ.powerset.filter
        (fun S : Finset (Fin k) => Odd S.card),
      ∑ t : Fin T, W t * ∏ l : Fin k,
        (if l ∈ S then (fun t => f t - g t) else fun t => f t + g t) t =
      ∑ t : Fin T, ∑ S ∈ Finset.univ.powerset.filter
        (fun S : Finset (Fin k) => Odd S.card),
      2 * (W t * ∏ l : Fin k,
        (if l ∈ S then (fun t => f t - g t) else fun t => f t + g t) t) := by
    rw [Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.mul_sum]
  rw [hswap]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hpt := pow_sub_pow_expand k (f t) (g t)
  have hbridge : ∀ S : Finset (Fin k),
      (∏ l : Fin k, (if l ∈ S then (fun t => f t - g t) else fun t => f t + g t) t) =
        ∏ l : Fin k, (if l ∈ S then f t - g t else f t + g t) :=
    fun S => Finset.prod_congr rfl fun l _ =>
      apply_ite (fun h : Fin T → ℝ => h t) (l ∈ S) _ _
  simp only [hbridge]
  calc 2 ^ k * (W t * f t ^ k - W t * g t ^ k)
      = W t * (2 ^ k * (f t ^ k - g t ^ k)) := by ring
    _ = W t * (2 * ∑ S ∈ Finset.univ.powerset.filter
          (fun S : Finset (Fin k) => Odd S.card),
        ∏ l : Fin k, (if l ∈ S then f t - g t else f t + g t)) := by rw [hpt]
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun S _ => by ring

/-- **The polarized k-th power observable**: the odd-subset polarization of
the rooted K₂,ₖ-arms profile difference at arm-length vector `φ` (the k-ary
generalization of `polarizedCubeObs`; the graph slice will identify
`2^(k-1) ·` the K₂,ₖ-arms profile difference with this). -/
noncomputable def polarizedPowObs (k : ℕ) (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (i j : Fin T) (φ : Fin k → ℕ) : ℝ :=
  ∑ S ∈ Finset.univ.powerset.filter (fun S : Finset (Fin k) => Odd S.card),
    wMulti k W (fun l => weightedAdjIter B W (φ l)
      (if l ∈ S then rowDiff B i j else rowSum B i j))

/-- **The graph-free k-th power core**: if every polarized k-th power
observable at positive arm lengths vanishes, the k-th power-moment gap is
zero. With the (future) graph slice identifying `polarizedPowObs` with
`2^(k-1) ·` the rooted K₂,ₖ-arms profile difference, this reduces
`powerSum_descends_of_rootedProfileEquiv` (k ≥ 4) to pure graph plumbing. -/
theorem powGap_eq_zero_of_polarized_obs (k : ℕ) (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (hW : ∀ t, 0 < W t)
    (i j : Fin T)
    (hobs : ∀ φ : Fin k → ℕ,
      polarizedPowObs k B W i j (fun l => φ l + 1) = 0) :
    ∑ t : Fin T, W t * B i t ^ k = ∑ t : Fin T, W t * B j t ^ k := by
  classical
  obtain ⟨s, c, hε, hu⟩ := weightedAdj_pair_common_coeffs B hB W hW
    ⟨_, (rowDiff_eq_weightedAdj B hB W hW i j).symm⟩
    ⟨_, (rowSum_eq_weightedAdj B hB W hW i j).symm⟩
  -- each odd-subset wMulti expands through the COMMON coefficients
  have hexp : ∀ S : Finset (Fin k),
      wMulti k W (fun l => if l ∈ S then rowDiff B i j else rowSum B i j) =
        ∑ φ ∈ Fintype.piFinset (fun _ : Fin k => s),
          (∏ l : Fin k, c (φ l)) *
            wMulti k W (fun l => weightedAdjIter B W (φ l + 1)
              (if l ∈ S then rowDiff B i j else rowSum B i j)) := by
    intro S
    refine wMulti_expansion k W s c
      (fun l a => weightedAdjIter B W (a + 1)
        (if l ∈ S then rowDiff B i j else rowSum B i j)) _ fun l => ?_
    by_cases hl : l ∈ S
    · simp only [if_pos hl]; exact hε
    · simp only [if_neg hl]; exact hu
  -- the total polarization vanishes
  have htotal : (∑ S ∈ Finset.univ.powerset.filter
      (fun S : Finset (Fin k) => Odd S.card),
      wMulti k W (fun l => if l ∈ S then rowDiff B i j else rowSum B i j)) = 0 := by
    calc (∑ S ∈ Finset.univ.powerset.filter
        (fun S : Finset (Fin k) => Odd S.card),
        wMulti k W (fun l => if l ∈ S then rowDiff B i j else rowSum B i j))
        = ∑ S ∈ Finset.univ.powerset.filter
            (fun S : Finset (Fin k) => Odd S.card),
          ∑ φ ∈ Fintype.piFinset (fun _ : Fin k => s),
            (∏ l : Fin k, c (φ l)) *
              wMulti k W (fun l => weightedAdjIter B W (φ l + 1)
                (if l ∈ S then rowDiff B i j else rowSum B i j)) :=
          Finset.sum_congr rfl fun S _ => hexp S
      _ = ∑ φ ∈ Fintype.piFinset (fun _ : Fin k => s),
          (∏ l : Fin k, c (φ l)) *
            polarizedPowObs k B W i j (fun l => φ l + 1) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun φ _ => ?_
          unfold polarizedPowObs
          rw [Finset.mul_sum]
      _ = 0 := Finset.sum_eq_zero fun φ _ => by
          rw [hobs (fun l => φ l), mul_zero]
  -- conclude via the polarization identity
  have hgap := pow_gap_polarization k W (fun t => B i t) (fun t => B j t)
  have hd : (fun t => B i t - B j t) = rowDiff B i j := rfl
  have hs : (fun t => B i t + B j t) = rowSum B i j := rfl
  simp only [hd, hs] at hgap
  rw [htotal, mul_zero] at hgap
  have h2k : ((2 : ℝ) ^ k) ≠ 0 := pow_ne_zero k two_ne_zero
  have hzero := mul_eq_zero.mp hgap
  rcases hzero with h | h
  · exact absurd h h2k
  · linarith

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

/-! #### The K₂,₃-with-arms graph family (the cube's graph bridge)

Vertex layout on `Fin (4 + a + b + c + 1)`: `0` the root, `1, 2, 3` the
anchors (root-adjacent), `4` the hub, then three internal blocks of sizes
`a, b, c` (so the arm from anchor `l + 1` to the hub has length
`armLen + 1 ≥ 1` — positive arm lengths by construction, matching the
`(a+1, b+1, c+1)` indices of `polarizedCubeObs`). -/

/-- Internal count of arm `l ∈ {0,1,2}`. -/
def armLen (a b c l : ℕ) : ℕ :=
  if l = 0 then a else if l = 1 then b else c

/-- Start of the internal block of arm `l ∈ {0,1,2}` (as a raw value). -/
def armStart (a b l : ℕ) : ℕ :=
  if l = 0 then 5 else if l = 1 then 5 + a else 5 + a + b

/-- The `s`-th vertex value along arm `l`: `s = 0` is the anchor `l + 1`,
steps `1 .. armLen` are the internals, `s = armLen + 1` is the hub `4`. -/
def armSeq (a b c : ℕ) (l s : ℕ) : ℕ :=
  if s = 0 then l + 1
  else if s ≤ armLen a b c l then armStart a b l + s - 1
  else 4

/-- **The rooted K₂,₃-with-arms graph**: root `0` adjacent to anchors
`1, 2, 3`; arm `l` a path of length `armLen + 1` from anchor `l + 1` to the
hub `4`. -/
def k23Arms (a b c : ℕ) : SimpleGraph (Fin (4 + a + b + c + 1)) where
  Adj u v :=
    ((u : ℕ) = 0 ∧ ((v : ℕ) = 1 ∨ (v : ℕ) = 2 ∨ (v : ℕ) = 3)) ∨
    ((v : ℕ) = 0 ∧ ((u : ℕ) = 1 ∨ (u : ℕ) = 2 ∨ (u : ℕ) = 3)) ∨
    (∃ l < 3, ∃ s ≤ armLen a b c l,
      ((u : ℕ) = armSeq a b c l s ∧ (v : ℕ) = armSeq a b c l (s + 1)) ∨
      ((v : ℕ) = armSeq a b c l s ∧ (u : ℕ) = armSeq a b c l (s + 1)))
  symm := by
    intro u v h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨l, hl, s, hs, h⟩
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inr ⟨l, hl, s, hs, h.symm⟩)
  loopless := by
    intro u h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨l, hl, s, hs, h⟩
    · omega
    · omega
    · have hne : armSeq a b c l s ≠ armSeq a b c l (s + 1) := by
        simp only [armSeq, armLen, armStart] at hs ⊢
        split_ifs at hs ⊢ <;> first | contradiction | omega
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact hne (h1.symm.trans h2)

instance (a b c : ℕ) : DecidableRel (k23Arms a b c).Adj := fun u v => by
  unfold k23Arms
  exact inferInstance

/-- Arm vertices stay in range. -/
theorem armSeq_lt (a b c : ℕ) {l s : ℕ} (hl : l < 3)
    (hs : s ≤ armLen a b c l + 1) :
    armSeq a b c l s < 4 + a + b + c + 1 := by
  simp only [armSeq, armLen, armStart] at hs ⊢
  split_ifs at hs ⊢ <;> omega

/-- Arm vertices are never the root. -/
theorem armSeq_pos (a b c : ℕ) {l s : ℕ} (hl : l < 3) :
    0 < armSeq a b c l s := by
  simp only [armSeq, armLen, armStart]
  split_ifs <;> omega

/-- The edge index type of `k23Arms`: three root edges plus, per arm,
`armLen + 1` chain edges. -/
abbrev K23EdgeIdx (a b c : ℕ) : Type :=
  Fin 3 ⊕ ((l : Fin 3) × Fin (armLen a b c l + 1))

/-- The edge family of `k23Arms`, indexed by `K23EdgeIdx`. -/
def k23Edge (a b c : ℕ) : K23EdgeIdx a b c → Sym2 (Fin (4 + a + b + c + 1))
  | .inl l => s((0 : Fin (4 + a + b + c + 1)),
      ⟨(l : ℕ) + 1, by have := l.isLt; omega⟩)
  | .inr ⟨l, s⟩ =>
      s(⟨armSeq a b c l s,
          armSeq_lt a b c l.isLt (by have := s.isLt; omega)⟩,
        ⟨armSeq a b c l ((s : ℕ) + 1),
          armSeq_lt a b c l.isLt (by have := s.isLt; omega)⟩)

/-- Every indexed edge is an edge of `k23Arms`. -/
theorem k23Edge_mem (a b c : ℕ) (idx : K23EdgeIdx a b c) :
    k23Edge a b c idx ∈ (k23Arms a b c).edgeSet := by
  match idx with
  | .inl l =>
    simp only [k23Edge]
    rw [SimpleGraph.mem_edgeSet]
    refine Or.inl ⟨rfl, ?_⟩
    show (l : ℕ) + 1 = 1 ∨ (l : ℕ) + 1 = 2 ∨ (l : ℕ) + 1 = 3
    have := l.isLt
    omega
  | .inr ⟨l, s⟩ =>
    simp only [k23Edge]
    rw [SimpleGraph.mem_edgeSet]
    exact Or.inr (Or.inr ⟨(l : ℕ), l.isLt, (s : ℕ),
      (by have := s.isLt; omega), Or.inl ⟨rfl, rfl⟩⟩)

/-- **Edge classification** for `k23Arms` (reusable form): the edge finset is
the image of the indexed family — three root-anchor edges plus the three
anchor-to-hub arm chains, and nothing else. -/
theorem k23Arms_edgeFinset (a b c : ℕ) :
    (k23Arms a b c).edgeFinset =
      Finset.image (k23Edge a b c) Finset.univ := by
  classical
  ext e
  simp only [SimpleGraph.mem_edgeFinset, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ u w =>
      rw [SimpleGraph.mem_edgeSet] at he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨l, hl, s, hs, hcase⟩
      · refine ⟨.inl ⟨(w : ℕ) - 1, by omega⟩, ?_⟩
        simp only [k23Edge]
        rw [Sym2.eq_iff]
        exact Or.inl ⟨Fin.ext h1.symm, Fin.ext (by show (w : ℕ) - 1 + 1 = _; omega)⟩
      · refine ⟨.inl ⟨(u : ℕ) - 1, by omega⟩, ?_⟩
        simp only [k23Edge]
        rw [Sym2.eq_iff]
        exact Or.inr ⟨Fin.ext h1.symm, Fin.ext (by show (u : ℕ) - 1 + 1 = _; omega)⟩
      · refine ⟨.inr ⟨⟨l, hl⟩, ⟨s, by show s < armLen a b c l + 1; omega⟩⟩, ?_⟩
        simp only [k23Edge]
        rw [Sym2.eq_iff]
        rcases hcase with ⟨hu, hw⟩ | ⟨hw, hu⟩
        · exact Or.inl ⟨Fin.ext hu.symm, Fin.ext hw.symm⟩
        · exact Or.inr ⟨Fin.ext hw.symm, Fin.ext hu.symm⟩
  · rintro ⟨idx, rfl⟩
    exact k23Edge_mem a b c idx

set_option maxHeartbeats 1600000 in
/-- Two arm-chain edges with equal endpoint sets come from the same arm and
step (raw-`ℕ` arithmetic core of edge injectivity). -/
private theorem armSeq_pair_inj (a b c : ℕ) {l s l' s' : ℕ}
    (hl : l < 3) (hl' : l' < 3)
    (hs : s ≤ armLen a b c l) (hs' : s' ≤ armLen a b c l')
    (h : (armSeq a b c l s = armSeq a b c l' s' ∧
            armSeq a b c l (s + 1) = armSeq a b c l' (s' + 1)) ∨
         (armSeq a b c l s = armSeq a b c l' (s' + 1) ∧
            armSeq a b c l (s + 1) = armSeq a b c l' s')) :
    l = l' ∧ s = s' := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    (interval_cases l <;> interval_cases l' <;>
      (simp only [armSeq, armLen, armStart] at h1 h2 hs hs'
       split_ifs at h1 h2 hs hs' <;> first | contradiction | omega))

/-- The indexed edge family is injective (no duplicate edges). -/
theorem k23Edge_injective (a b c : ℕ) :
    Function.Injective (k23Edge a b c) := by
  intro x y hxy
  match x, y with
  | .inl l, .inl l' =>
    simp only [k23Edge] at hxy
    rw [Sym2.eq_iff] at hxy
    rcases hxy with ⟨-, h2⟩ | ⟨h1, -⟩
    · have hval : (l : ℕ) + 1 = (l' : ℕ) + 1 := congrArg Fin.val h2
      exact congrArg Sum.inl (Fin.ext (by omega))
    · have hval : (0 : ℕ) = (l' : ℕ) + 1 := congrArg Fin.val h1
      exact absurd hval (by omega)
  | .inl l, .inr ⟨l', s'⟩ =>
    exfalso
    simp only [k23Edge] at hxy
    rw [Sym2.eq_iff] at hxy
    have hp := armSeq_pos a b c (l := (l' : ℕ)) (s := (s' : ℕ)) l'.isLt
    have hp' := armSeq_pos a b c (l := (l' : ℕ)) (s := (s' : ℕ) + 1) l'.isLt
    rcases hxy with ⟨h1, -⟩ | ⟨h1, -⟩
    · have hval : (0 : ℕ) = armSeq a b c l' s' := congrArg Fin.val h1
      omega
    · have hval : (0 : ℕ) = armSeq a b c l' ((s' : ℕ) + 1) := congrArg Fin.val h1
      omega
  | .inr ⟨l', s'⟩, .inl l =>
    exfalso
    simp only [k23Edge] at hxy
    rw [Sym2.eq_iff] at hxy
    have hp := armSeq_pos a b c (l := (l' : ℕ)) (s := (s' : ℕ)) l'.isLt
    have hp' := armSeq_pos a b c (l := (l' : ℕ)) (s := (s' : ℕ) + 1) l'.isLt
    rcases hxy with ⟨h1, -⟩ | ⟨-, h2⟩
    · have hval : armSeq a b c l' s' = (0 : ℕ) := congrArg Fin.val h1
      omega
    · have hval : armSeq a b c l' ((s' : ℕ) + 1) = (0 : ℕ) := congrArg Fin.val h2
      omega
  | .inr ⟨l, s⟩, .inr ⟨l', s'⟩ =>
    simp only [k23Edge] at hxy
    rw [Sym2.eq_iff] at hxy
    have hls : (l : ℕ) = (l' : ℕ) ∧ (s : ℕ) = (s' : ℕ) := by
      refine armSeq_pair_inj a b c l.isLt l'.isLt
        (by have := s.isLt; omega) (by have := s'.isLt; omega) ?_
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨congrArg Fin.val h1, congrArg Fin.val h2⟩
      · exact Or.inr ⟨congrArg Fin.val h1, congrArg Fin.val h2⟩
    obtain ⟨hl, hs⟩ := hls
    have hl2 : l = l' := Fin.ext hl
    subst hl2
    have hs2 : s = s' := Fin.ext hs
    subst hs2
    rfl

/-- Resolve `Quot.out` on a literal `Sym2` pair under a symmetric matrix
(reusable helper for edge products). -/
private theorem out_pair_eq {T' n : ℕ} (Bm : Fin T' → Fin T' → ℝ)
    (hB : ∀ i j, Bm i j = Bm j i) (τ : Fin n → Fin T') (x y : Fin n) :
    Bm (τ (Quot.out s(x, y)).1) (τ (Quot.out s(x, y)).2) = Bm (τ x) (τ y) := by
  have hout := Quot.out_eq s(x, y)
  rw [Sym2.mk_eq_mk_iff] at hout
  rcases hout with h | h
  · rw [congrArg Prod.fst h, congrArg Prod.snd h]
  · simp only [Prod.swap] at h
    rw [congrArg Prod.fst h, congrArg Prod.snd h, hB]

/-- **Edge-product factorization** for `k23Arms`: the edge product splits into
the three root-edge factors times the three independent arm-chain products. -/
theorem k23Arms_prod_eq {T : ℕ} (a b c : ℕ) (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (τ : Fin (4 + a + b + c + 1) → Fin T) :
    (∏ e ∈ (k23Arms a b c).edgeFinset,
        B (τ (Quot.out e).1) (τ (Quot.out e).2)) =
      (∏ l : Fin 3, B (τ 0) (τ ⟨(l : ℕ) + 1, by have := l.isLt; omega⟩)) *
        ∏ l : Fin 3, ∏ s : Fin (armLen a b c l + 1),
          B (τ ⟨armSeq a b c l s,
              armSeq_lt a b c l.isLt (by have := s.isLt; omega)⟩)
            (τ ⟨armSeq a b c l ((s : ℕ) + 1),
              armSeq_lt a b c l.isLt (by have := s.isLt; omega)⟩) := by
  classical
  rw [k23Arms_edgeFinset,
    Finset.prod_image (fun x _ y _ h => k23Edge_injective a b c h),
    Fintype.prod_sum_type]
  congr 1
  · refine Finset.prod_congr rfl fun l _ => ?_
    simp only [k23Edge]
    exact out_pair_eq B hB τ _ _
  · rw [← Finset.univ_sigma_univ, Finset.prod_sigma]
    refine Finset.prod_congr rfl fun l _ => Finset.prod_congr rfl fun s _ => ?_
    simp only [k23Edge]
    exact out_pair_eq B hB τ _ _

/-! #### One-arm chain collapse -/

/-- The `(q+1)`-edge arm kernel from `x` to `y` (`q` internal vertices),
defined recursively — the normal form the internal sums collapse to. -/
noncomputable def armSum {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    ℕ → Fin T → Fin T → ℝ
  | 0, x, y => B x y
  | q + 1, x, y => ∑ t : Fin T, W t * B x t * armSum B W q t y

/-- Path-position function for a free-standing arm: `0 ↦ x`, `1..q ↦ σ`,
`q+1 ↦ y` (the `Fin T`-valued mirror of `armSeq`). -/
def chainPath {T : ℕ} (q : ℕ) (x y : Fin T) (σ : Fin q → Fin T) (s : ℕ) :
    Fin T :=
  if h0 : s = 0 then x
  else if h : s ≤ q then σ ⟨s - 1, by omega⟩ else y

/-- One step of `chainPath` reindexing: position `r + 1` of the
`(q+1)`-internal chain `x ⋯ y` with head `t` is position `r` of the
`q`-internal chain `t ⋯ y`. -/
private theorem chainPath_cons_succ {T : ℕ} (q : ℕ) (x y t : Fin T)
    (σ' : Fin q → Fin T) {r : ℕ} (hr : r ≤ q + 1) :
    chainPath (q + 1) x y (Fin.cons t σ') (r + 1) = chainPath q t y σ' r := by
  unfold chainPath
  rcases Nat.eq_zero_or_pos r with rfl | hpos
  · rw [dif_neg (by omega), dif_pos (by omega : 0 + 1 ≤ q + 1), dif_pos rfl]
    show Fin.cons (α := fun _ => Fin T) t σ' ⟨0 + 1 - 1, by omega⟩ = t
    rw [show (⟨0 + 1 - 1, by omega⟩ : Fin (q + 1)) = 0 from Fin.ext rfl,
      Fin.cons_zero]
  · by_cases hq : r ≤ q
    · rw [dif_neg (by omega), dif_pos (by omega : r + 1 ≤ q + 1),
        dif_neg (by omega), dif_pos hq]
      show Fin.cons (α := fun _ => Fin T) t σ' ⟨r + 1 - 1, by omega⟩ =
        σ' ⟨r - 1, by omega⟩
      rw [show (⟨r + 1 - 1, by omega⟩ : Fin (q + 1)) =
          Fin.succ ⟨r - 1, by omega⟩ from
        Fin.ext (by simp only [Fin.val_succ]; omega), Fin.cons_succ]
    · rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg hq]

/-- **One-arm collapse**: summing the internal vertices of an arm chain
gives the recursive kernel `armSum`. -/
theorem armChain_sum_eq_armSum {T : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) :
    ∀ (q : ℕ) (x y : Fin T),
      (∑ σ : Fin q → Fin T, (∏ k : Fin q, W (σ k)) *
        ∏ s : Fin (q + 1),
          B (chainPath q x y σ s) (chainPath q x y σ ((s : ℕ) + 1))) =
      armSum B W q x y := by
  intro q
  induction q with
  | zero =>
    intro x y
    rw [Fintype.sum_unique, Fin.prod_univ_zero, one_mul, Fin.prod_univ_one]
    show B (chainPath 0 x y default 0) (chainPath 0 x y default (0 + 1)) =
      armSum B W 0 x y
    unfold chainPath
    rw [dif_pos rfl, dif_neg (by omega : ¬(0 + 1 = 0)), dif_neg (by omega)]
    rfl
  | succ q ih =>
    intro x y
    rw [sum_fin_succ_eq_sum_cons]
    show _ = ∑ t : Fin T, W t * B x t * armSum B W q t y
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← ih t y, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ' _ => ?_
    -- weights: peel the head
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    -- chain: peel the first edge
    rw [Fin.prod_univ_succ]
    have h0 : chainPath (q + 1) x y (Fin.cons t σ') ((0 : Fin (q + 2)) : ℕ) = x := by
      show chainPath (q + 1) x y (Fin.cons t σ') 0 = x
      unfold chainPath
      rw [dif_pos rfl]
    have h1 : chainPath (q + 1) x y (Fin.cons t σ')
        (((0 : Fin (q + 2)) : ℕ) + 1) = t := by
      show chainPath (q + 1) x y (Fin.cons t σ') (0 + 1) = t
      rw [chainPath_cons_succ q x y t σ' (by omega)]
      unfold chainPath
      rw [dif_pos rfl]
    have hsucc : ∀ s : Fin (q + 1),
        B (chainPath (q + 1) x y (Fin.cons t σ') ((s.succ : Fin (q + 2)) : ℕ))
          (chainPath (q + 1) x y (Fin.cons t σ') (((s.succ : Fin (q + 2)) : ℕ) + 1)) =
        B (chainPath q t y σ' ((s : ℕ)))
          (chainPath q t y σ' ((s : ℕ) + 1)) := by
      intro s
      have hv : ((s.succ : Fin (q + 2)) : ℕ) = (s : ℕ) + 1 := rfl
      rw [hv, chainPath_cons_succ q x y t σ' (by have := s.isLt; omega),
        chainPath_cons_succ q x y t σ' (by have := s.isLt; omega)]
    rw [h0, h1]
    rw [Finset.prod_congr rfl fun s _ => hsucc s]
    ring

/-- **One-arm collapse, weighted form** (the consumer shape): summing the
anchor against the root edge and the arm kernel yields `weightedAdjIter`
at the hub. -/
theorem sum_weight_mul_armSum {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) :
    ∀ (q : ℕ) (f : Fin T → ℝ) (y : Fin T),
      (∑ x : Fin T, W x * f x * armSum B W q x y) =
        weightedAdjIter B W (q + 1) f y := by
  intro q
  induction q with
  | zero =>
    intro f y
    show (∑ x : Fin T, W x * f x * B x y) = weightedAdj B W f y
    unfold weightedAdj
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hB y x]
    ring
  | succ q ih =>
    intro f y
    show (∑ x : Fin T, W x * f x * ∑ t : Fin T, W t * B x t * armSum B W q t y) = _
    have key : ∀ t : Fin T,
        (∑ x : Fin T, W x * f x * (W t * B x t * armSum B W q t y)) =
          W t * weightedAdj B W f t * armSum B W q t y := by
      intro t
      unfold weightedAdj
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hB t x]
      ring
    have hswap : (∑ x : Fin T, W x * f x * ∑ t : Fin T, W t * B x t * armSum B W q t y) =
        ∑ t : Fin T, W t * weightedAdj B W f t * armSum B W q t y := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun t _ => key t
    rw [hswap, ih (weightedAdj B W f) y, weightedAdjIter_weightedAdj_comm]
    rfl

/-! #### Block-structured assignments (the global split) -/

/-- Concatenation of two assignment blocks (dif-based, so the value lemmas
are definitional — no `castAdd`/`natAdd` juggling downstream). -/
def appendFn {T m n : ℕ} (σ₁ : Fin m → Fin T) (σ₂ : Fin n → Fin T) :
    Fin (m + n) → Fin T :=
  fun i => if h : (i : ℕ) < m then σ₁ ⟨i, h⟩
    else σ₂ ⟨(i : ℕ) - m, by have := i.isLt; omega⟩

theorem appendFn_low {T m n : ℕ} (σ₁ : Fin m → Fin T) (σ₂ : Fin n → Fin T)
    {i : Fin (m + n)} (h : (i : ℕ) < m) :
    appendFn σ₁ σ₂ i = σ₁ ⟨i, h⟩ := dif_pos h

theorem appendFn_high {T m n : ℕ} (σ₁ : Fin m → Fin T) (σ₂ : Fin n → Fin T)
    {i : Fin (m + n)} (h : ¬(i : ℕ) < m) :
    appendFn σ₁ σ₂ i = σ₂ ⟨(i : ℕ) - m, by have := i.isLt; omega⟩ := dif_neg h

/-- The block-splitting equivalence for assignment spaces. -/
def appendEquiv (T m n : ℕ) :
    ((Fin m → Fin T) × (Fin n → Fin T)) ≃ (Fin (m + n) → Fin T) where
  toFun p := appendFn p.1 p.2
  invFun σ := (fun i => σ ⟨i, by have := i.isLt; omega⟩,
    fun j => σ ⟨m + (j : ℕ), by have := j.isLt; omega⟩)
  left_inv p := by
    obtain ⟨σ₁, σ₂⟩ := p
    rw [Prod.mk.injEq]
    refine ⟨funext fun i => ?_, funext fun j => ?_⟩ <;> dsimp only
    · rw [appendFn_low _ _ (show ((⟨(i : ℕ), _⟩ : Fin (m + n)) : ℕ) < m from i.isLt)]
    · rw [appendFn_high _ _ (show ¬((⟨m + (j : ℕ), _⟩ : Fin (m + n)) : ℕ) < m by
        show ¬m + (j : ℕ) < m; omega)]
      exact congrArg σ₂ (Fin.ext (show m + (j : ℕ) - m = (j : ℕ) by omega))
  right_inv σ := by
    funext i
    dsimp only
    by_cases h : (i : ℕ) < m
    · rw [appendFn_low _ _ h]
    · rw [appendFn_high _ _ h]
      exact congrArg σ (Fin.ext (show m + ((i : ℕ) - m) = (i : ℕ) by omega))

/-- **Sum splitting** along a block decomposition of the assignment space. -/
theorem sum_fin_split {T : ℕ} {β : Type*} [AddCommMonoid β] (m n : ℕ)
    (f : (Fin (m + n) → Fin T) → β) :
    (∑ σ : Fin (m + n) → Fin T, f σ) =
      ∑ σ₁ : Fin m → Fin T, ∑ σ₂ : Fin n → Fin T, f (appendFn σ₁ σ₂) := by
  rw [← Equiv.sum_comp (appendEquiv T m n) f, Fintype.sum_prod_type]
  rfl

/-- **Weight-product splitting** along a block decomposition. -/
theorem prod_appendFn {T m n : ℕ} (g : Fin T → ℝ)
    (σ₁ : Fin m → Fin T) (σ₂ : Fin n → Fin T) :
    (∏ u : Fin (m + n), g (appendFn σ₁ σ₂ u)) =
      (∏ u : Fin m, g (σ₁ u)) * ∏ u : Fin n, g (σ₂ u) := by
  rw [Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl fun u _ => ?_
    rw [appendFn_low _ _ (by rw [Fin.val_castAdd]; exact u.isLt)]
    exact congrArg g (congrArg σ₁ (Fin.ext (by rw [Fin.val_castAdd])))
  · refine Finset.prod_congr rfl fun u _ => ?_
    rw [appendFn_high _ _ (by rw [Fin.val_natAdd]; omega)]
    refine congrArg g (congrArg σ₂ (Fin.ext ?_))
    show ((Fin.natAdd m u : Fin (m + n)) : ℕ) - m = (u : ℕ)
    rw [Fin.val_natAdd]
    omega

/-- The structured K₂,₃-arms assignment: anchors, hub, and the three
internal arm blocks, assembled into a flat assignment. -/
def k23Assign {T : ℕ} (a b c : ℕ) (x : Fin 3 → Fin T) (h₁ : Fin 1 → Fin T)
    (σa : Fin a → Fin T) (σb : Fin b → Fin T) (σc : Fin c → Fin T) :
    Fin (4 + a + b + c) → Fin T :=
  appendFn (appendFn (appendFn (appendFn x h₁) σa) σb) σc

/-- Reconstruction: anchor values. -/
theorem k23Assign_anchor {T : ℕ} (a b c : ℕ) (x : Fin 3 → Fin T)
    (h₁ : Fin 1 → Fin T) (σa : Fin a → Fin T) (σb : Fin b → Fin T)
    (σc : Fin c → Fin T) {j : ℕ} (hj : j < 3) :
    k23Assign a b c x h₁ σa σb σc ⟨j, by omega⟩ = x ⟨j, hj⟩ := by
  unfold k23Assign
  rw [appendFn_low _ _ (show j < 4 + a + b by omega),
    appendFn_low _ _ (show j < 4 + a by omega),
    appendFn_low _ _ (show j < 4 by omega),
    appendFn_low _ _ (show j < 3 from hj)]

/-- Reconstruction: the hub value. -/
theorem k23Assign_hub {T : ℕ} (a b c : ℕ) (x : Fin 3 → Fin T)
    (h₁ : Fin 1 → Fin T) (σa : Fin a → Fin T) (σb : Fin b → Fin T)
    (σc : Fin c → Fin T) :
    k23Assign a b c x h₁ σa σb σc ⟨3, by omega⟩ = h₁ 0 := by
  unfold k23Assign
  rw [appendFn_low _ _ (show 3 < 4 + a + b by omega),
    appendFn_low _ _ (show 3 < 4 + a by omega),
    appendFn_low _ _ (show 3 < 4 by omega),
    appendFn_high _ _ (show ¬3 < 3 by omega)]
  exact congrArg h₁ (Fin.ext rfl)

/-- Reconstruction: arm-0 internal values. -/
theorem k23Assign_arm0 {T : ℕ} (a b c : ℕ) (x : Fin 3 → Fin T)
    (h₁ : Fin 1 → Fin T) (σa : Fin a → Fin T) (σb : Fin b → Fin T)
    (σc : Fin c → Fin T) {k : ℕ} (hk : k < a) :
    k23Assign a b c x h₁ σa σb σc ⟨4 + k, by omega⟩ = σa ⟨k, hk⟩ := by
  unfold k23Assign
  rw [appendFn_low _ _ (show 4 + k < 4 + a + b by omega),
    appendFn_low _ _ (show 4 + k < 4 + a by omega),
    appendFn_high _ _ (show ¬4 + k < 4 by omega)]
  exact congrArg σa (Fin.ext (show 4 + k - 4 = k by omega))

/-- Reconstruction: arm-1 internal values. -/
theorem k23Assign_arm1 {T : ℕ} (a b c : ℕ) (x : Fin 3 → Fin T)
    (h₁ : Fin 1 → Fin T) (σa : Fin a → Fin T) (σb : Fin b → Fin T)
    (σc : Fin c → Fin T) {k : ℕ} (hk : k < b) :
    k23Assign a b c x h₁ σa σb σc ⟨4 + a + k, by omega⟩ = σb ⟨k, hk⟩ := by
  unfold k23Assign
  rw [appendFn_low _ _ (show 4 + a + k < 4 + a + b by omega),
    appendFn_high _ _ (show ¬4 + a + k < 4 + a by omega)]
  exact congrArg σb (Fin.ext (show 4 + a + k - (4 + a) = k by omega))

/-- Reconstruction: arm-2 internal values. -/
theorem k23Assign_arm2 {T : ℕ} (a b c : ℕ) (x : Fin 3 → Fin T)
    (h₁ : Fin 1 → Fin T) (σa : Fin a → Fin T) (σb : Fin b → Fin T)
    (σc : Fin c → Fin T) {k : ℕ} (hk : k < c) :
    k23Assign a b c x h₁ σa σb σc ⟨4 + a + b + k, by omega⟩ = σc ⟨k, hk⟩ := by
  unfold k23Assign
  rw [appendFn_high _ _ (show ¬4 + a + b + k < 4 + a + b by omega)]
  exact congrArg σc (Fin.ext (show 4 + a + b + k - (4 + a + b) = k by omega))

/-- **Raw evaluation of the K₂,₃-arms profile** (SORRY — the brittle
`Fin`/edge-product slice, isolated here per plan): the rooted profile
factorizes through the hub as a `wTriple` of `weightedAdjIter`s of the
root's row. Mathematically: summing each arm's internals gives the walk
kernel `K_{armLen+1}(anchor, hub)`; summing each anchor against its root
edge gives `(M^{armLen+1} (B v ·))(hub)`; the hub sum is `wTriple`.
Machine-precision validated in `scripts/validate_cube_k23_arms.py`. -/
theorem k23Arms_eval {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (v : Fin T) (a b c : ℕ) :
    rootedProfile B W v (k23Arms a b c) =
      wTriple W (weightedAdjIter B W (a + 1) (fun t => B v t))
        (weightedAdjIter B W (b + 1) (fun t => B v t))
        (weightedAdjIter B W (c + 1) (fun t => B v t)) := by
  classical
  unfold rootedProfile simpleEvalAt
  rw [sum_fin_split (4 + a + b) c, sum_fin_split (4 + a) b, sum_fin_split 4 a,
    sum_fin_split 3 1]
  -- Step A: per-tuple body normalization (weights split, edges factored,
  -- values reconstructed into chainPath form).
  have hbody : ∀ (x : Fin 3 → Fin T) (h₁ : Fin 1 → Fin T) (σa : Fin a → Fin T)
      (σb : Fin b → Fin T) (σc : Fin c → Fin T),
      ((∏ u, W (appendFn (appendFn (appendFn (appendFn x h₁) σa) σb) σc u)) *
        ∏ e ∈ (k23Arms a b c).edgeFinset,
          B ((fun p : Fin (4 + a + b + c + 1) => if h : (p : ℕ) < 1 then v
              else appendFn (appendFn (appendFn (appendFn x h₁) σa) σb) σc
                ⟨(p : ℕ) - 1, by have := p.isLt; omega⟩) (Quot.out e).1)
            ((fun p : Fin (4 + a + b + c + 1) => if h : (p : ℕ) < 1 then v
              else appendFn (appendFn (appendFn (appendFn x h₁) σa) σb) σc
                ⟨(p : ℕ) - 1, by have := p.isLt; omega⟩) (Quot.out e).2)) =
      (W (x 0) * B v (x 0)) * ((W (x 1) * B v (x 1)) * ((W (x 2) * B v (x 2)) *
        (W (h₁ 0) *
          (((∏ u : Fin a, W (σa u)) * ∏ s : Fin (a + 1),
              B (chainPath a (x 0) (h₁ 0) σa s)
                (chainPath a (x 0) (h₁ 0) σa ((s : ℕ) + 1))) *
            (((∏ u : Fin b, W (σb u)) * ∏ s : Fin (b + 1),
              B (chainPath b (x 1) (h₁ 0) σb s)
                (chainPath b (x 1) (h₁ 0) σb ((s : ℕ) + 1))) *
              ((∏ u : Fin c, W (σc u)) * ∏ s : Fin (c + 1),
                B (chainPath c (x 2) (h₁ 0) σc s)
                  (chainPath c (x 2) (h₁ 0) σc ((s : ℕ) + 1)))))))) := by
    intro x h₁ σa σb σc
    rw [k23Arms_prod_eq a b c B hB
      (fun p : Fin (4 + a + b + c + 1) => if h : (p : ℕ) < 1 then v
        else appendFn (appendFn (appendFn (appendFn x h₁) σa) σb) σc
          ⟨(p : ℕ) - 1, by have := p.isLt; omega⟩)]
    rw [prod_appendFn, prod_appendFn, prod_appendFn, prod_appendFn,
      Fin.prod_univ_one]
    -- value lemmas: the root, the anchors, and the three arms
    have hrootv : (if h : ((0 : Fin (4 + a + b + c + 1)) : ℕ) < 1 then v
        else appendFn (appendFn (appendFn (appendFn x h₁) σa) σb) σc
          ⟨((0 : Fin (4 + a + b + c + 1)) : ℕ) - 1, by omega⟩) = v :=
      dif_pos Nat.zero_lt_one
    have hanchor : ∀ l : Fin 3, ∀ hlt : (l : ℕ) + 1 < 4 + a + b + c + 1,
        (if h : ((⟨(l : ℕ) + 1, hlt⟩ : Fin (4 + a + b + c + 1)) : ℕ) < 1 then v
          else appendFn (appendFn (appendFn (appendFn x h₁) σa) σb) σc
            ⟨((⟨(l : ℕ) + 1, hlt⟩ : Fin (4 + a + b + c + 1)) : ℕ) - 1, by omega⟩) =
        x l := by
      intro l hlt
      rw [dif_neg (show ¬(l : ℕ) + 1 < 1 by omega)]
      exact k23Assign_anchor a b c x h₁ σa σb σc l.isLt
    have harm0 : ∀ (r : ℕ) (hr : r ≤ a + 1)
        (hlt : armSeq a b c 0 r < 4 + a + b + c + 1),
        (if h : armSeq a b c 0 r < 1 then v
          else appendFn (appendFn (appendFn (appendFn x h₁) σa) σb) σc
            ⟨armSeq a b c 0 r - 1, by omega⟩) =
        chainPath a (x 0) (h₁ 0) σa r := by
      intro r hr hlt
      rw [dif_neg (show ¬armSeq a b c 0 r < 1 by
        have := armSeq_pos a b c (l := 0) (s := r) (by omega); omega)]
      by_cases h0 : r = 0
      · subst h0
        rw [show chainPath a (x 0) (h₁ 0) σa 0 = x 0 from dif_pos rfl]
        exact k23Assign_anchor a b c x h₁ σa σb σc (show (0 : ℕ) < 3 by omega)
      · by_cases hq : r ≤ a
        · have hv : armSeq a b c 0 r = 4 + r := by
            simp only [armSeq, armLen, armStart]
            split_ifs
            omega
          rw [show (⟨armSeq a b c 0 r - 1, by omega⟩ : Fin (4 + a + b + c)) =
              ⟨4 + (r - 1), by omega⟩ from
            Fin.ext (show armSeq a b c 0 r - 1 = 4 + (r - 1) by omega)]
          rw [show chainPath a (x 0) (h₁ 0) σa r = σa ⟨r - 1, by omega⟩ from by
            unfold chainPath; rw [dif_neg h0, dif_pos hq]]
          exact k23Assign_arm0 a b c x h₁ σa σb σc (show r - 1 < a by omega)
        · have hv : armSeq a b c 0 r = 4 := by
            simp only [armSeq, armLen, armStart]
            split_ifs
            omega
          rw [show (⟨armSeq a b c 0 r - 1, by omega⟩ : Fin (4 + a + b + c)) =
              ⟨3, by omega⟩ from
            Fin.ext (show armSeq a b c 0 r - 1 = 3 by omega)]
          rw [show chainPath a (x 0) (h₁ 0) σa r = h₁ 0 from by
            unfold chainPath; rw [dif_neg h0, dif_neg hq]]
          exact k23Assign_hub a b c x h₁ σa σb σc
    have harm1 : ∀ (r : ℕ) (hr : r ≤ b + 1)
        (hlt : armSeq a b c 1 r < 4 + a + b + c + 1),
        (if h : armSeq a b c 1 r < 1 then v
          else appendFn (appendFn (appendFn (appendFn x h₁) σa) σb) σc
            ⟨armSeq a b c 1 r - 1, by omega⟩) =
        chainPath b (x 1) (h₁ 0) σb r := by
      intro r hr hlt
      rw [dif_neg (show ¬armSeq a b c 1 r < 1 by
        have := armSeq_pos a b c (l := 1) (s := r) (by omega); omega)]
      by_cases h0 : r = 0
      · subst h0
        rw [show chainPath b (x 1) (h₁ 0) σb 0 = x 1 from dif_pos rfl]
        exact k23Assign_anchor a b c x h₁ σa σb σc (show (1 : ℕ) < 3 by omega)
      · by_cases hq : r ≤ b
        · have hv : armSeq a b c 1 r = 4 + a + r := by
            simp only [armSeq, armLen, armStart]
            split_ifs <;> first | contradiction | omega
          rw [show (⟨armSeq a b c 1 r - 1, by omega⟩ : Fin (4 + a + b + c)) =
              ⟨4 + a + (r - 1), by omega⟩ from
            Fin.ext (show armSeq a b c 1 r - 1 = 4 + a + (r - 1) by omega)]
          rw [show chainPath b (x 1) (h₁ 0) σb r = σb ⟨r - 1, by omega⟩ from by
            unfold chainPath; rw [dif_neg h0, dif_pos hq]]
          exact k23Assign_arm1 a b c x h₁ σa σb σc (show r - 1 < b by omega)
        · have hv : armSeq a b c 1 r = 4 := by
            simp only [armSeq, armLen, armStart]
            split_ifs <;> first | contradiction | omega
          rw [show (⟨armSeq a b c 1 r - 1, by omega⟩ : Fin (4 + a + b + c)) =
              ⟨3, by omega⟩ from
            Fin.ext (show armSeq a b c 1 r - 1 = 3 by omega)]
          rw [show chainPath b (x 1) (h₁ 0) σb r = h₁ 0 from by
            unfold chainPath; rw [dif_neg h0, dif_neg hq]]
          exact k23Assign_hub a b c x h₁ σa σb σc
    have harm2 : ∀ (r : ℕ) (hr : r ≤ c + 1)
        (hlt : armSeq a b c 2 r < 4 + a + b + c + 1),
        (if h : armSeq a b c 2 r < 1 then v
          else appendFn (appendFn (appendFn (appendFn x h₁) σa) σb) σc
            ⟨armSeq a b c 2 r - 1, by omega⟩) =
        chainPath c (x 2) (h₁ 0) σc r := by
      intro r hr hlt
      rw [dif_neg (show ¬armSeq a b c 2 r < 1 by
        have := armSeq_pos a b c (l := 2) (s := r) (by omega); omega)]
      by_cases h0 : r = 0
      · subst h0
        rw [show chainPath c (x 2) (h₁ 0) σc 0 = x 2 from dif_pos rfl]
        exact k23Assign_anchor a b c x h₁ σa σb σc (show (2 : ℕ) < 3 by omega)
      · by_cases hq : r ≤ c
        · have hv : armSeq a b c 2 r = 4 + a + b + r := by
            simp only [armSeq, armLen, armStart]
            split_ifs <;> first | contradiction | omega
          rw [show (⟨armSeq a b c 2 r - 1, by omega⟩ : Fin (4 + a + b + c)) =
              ⟨4 + a + b + (r - 1), by omega⟩ from
            Fin.ext (show armSeq a b c 2 r - 1 = 4 + a + b + (r - 1) by omega)]
          rw [show chainPath c (x 2) (h₁ 0) σc r = σc ⟨r - 1, by omega⟩ from by
            unfold chainPath; rw [dif_neg h0, dif_pos hq]]
          exact k23Assign_arm2 a b c x h₁ σa σb σc (show r - 1 < c by omega)
        · have hv : armSeq a b c 2 r = 4 := by
            simp only [armSeq, armLen, armStart]
            split_ifs <;> first | contradiction | omega
          rw [show (⟨armSeq a b c 2 r - 1, by omega⟩ : Fin (4 + a + b + c)) =
              ⟨3, by omega⟩ from
            Fin.ext (show armSeq a b c 2 r - 1 = 3 by omega)]
          rw [show chainPath c (x 2) (h₁ 0) σc r = h₁ 0 from by
            unfold chainPath; rw [dif_neg h0, dif_neg hq]]
          exact k23Assign_hub a b c x h₁ σa σb σc
    trans (((((∏ u : Fin 3, W (x u)) * W (h₁ 0) * ∏ u : Fin a, W (σa u)) *
        ∏ u : Fin b, W (σb u)) * ∏ u : Fin c, W (σc u)) *
      ((B v (x 0) * B v (x 1) * B v (x 2)) *
        ((∏ s : Fin (a + 1), B (chainPath a (x 0) (h₁ 0) σa s)
            (chainPath a (x 0) (h₁ 0) σa ((s : ℕ) + 1))) *
          (∏ s : Fin (b + 1), B (chainPath b (x 1) (h₁ 0) σb s)
            (chainPath b (x 1) (h₁ 0) σb ((s : ℕ) + 1))) *
          ∏ s : Fin (c + 1), B (chainPath c (x 2) (h₁ 0) σc s)
            (chainPath c (x 2) (h₁ 0) σc ((s : ℕ) + 1)))))
    · refine congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) ?_ ?_)
      · refine (Fin.prod_univ_three _).trans ?_
        exact congrArg₂ (· * ·) (congrArg₂ (· * ·)
          (congrArg₂ B hrootv (hanchor 0 (by omega)))
          (congrArg₂ B hrootv (hanchor 1 (by omega))))
          (congrArg₂ B hrootv (hanchor 2 (by omega)))
      · refine (Fin.prod_univ_three _).trans ?_
        refine congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) ?_
        · exact Finset.prod_congr rfl fun s _ => congrArg₂ B
            (harm0 ↑s (le_of_lt s.isLt)
              (armSeq_lt a b c (0 : Fin 3).isLt (le_of_lt s.isLt)))
            (harm0 ((s : ℕ) + 1) s.isLt (armSeq_lt a b c (0 : Fin 3).isLt s.isLt))
        · exact Finset.prod_congr rfl fun s _ => congrArg₂ B
            (harm1 ↑s (le_of_lt s.isLt)
              (armSeq_lt a b c (1 : Fin 3).isLt (le_of_lt s.isLt)))
            (harm1 ((s : ℕ) + 1) s.isLt (armSeq_lt a b c (1 : Fin 3).isLt s.isLt))
        · exact Finset.prod_congr rfl fun s _ => congrArg₂ B
            (harm2 ↑s (le_of_lt s.isLt)
              (armSeq_lt a b c (2 : Fin 3).isLt (le_of_lt s.isLt)))
            (harm2 ((s : ℕ) + 1) s.isLt (armSeq_lt a b c (2 : Fin 3).isLt s.isLt))
    · rw [Fin.prod_univ_three (fun u : Fin 3 => W (x u))]
      ring
  simp only [hbody]
  -- Step B: pull constants out of the inner sums and collapse each arm.
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  simp only [armChain_sum_eq_armSum]
  -- Step C: convert the hub block sum to a plain vertex sum.
  have hone : ∀ φ : (Fin 1 → Fin T) → ℝ,
      (∑ h₁ : Fin 1 → Fin T, φ h₁) = ∑ y : Fin T, φ (fun _ => y) :=
    fun φ => (Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin T)).symm φ).symm
  simp only [hone]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hx3 : ∀ G₁ G₂ G₃ : Fin T → ℝ,
      (∑ x : Fin 3 → Fin T, G₁ (x 0) * (G₂ (x 1) * G₃ (x 2))) =
        (∑ t : Fin T, G₁ t) * ((∑ t : Fin T, G₂ t) * ∑ t : Fin T, G₃ t) := by
    intro G₁ G₂ G₃
    rw [sum_fin_succ_eq_sum_cons]
    have hv0 : ∀ (t : Fin T) (x' : Fin 2 → Fin T),
        Fin.cons (α := fun _ => Fin T) t x' 0 = t :=
      fun t x' => by simp
    have hv1 : ∀ (t : Fin T) (x' : Fin 2 → Fin T),
        Fin.cons (α := fun _ => Fin T) t x' 1 = x' 0 :=
      fun t x' => rfl
    have hv2 : ∀ (t : Fin T) (x' : Fin 2 → Fin T),
        Fin.cons (α := fun _ => Fin T) t x' 2 = x' 1 :=
      fun t x' => rfl
    simp only [hv0, hv1, hv2]
    rw [← Finset.sum_mul_sum]
    congr 1
    rw [sum_fin_succ_eq_sum_cons]
    have hw0 : ∀ (t : Fin T) (x' : Fin 1 → Fin T),
        Fin.cons (α := fun _ => Fin T) t x' 0 = t :=
      fun t x' => by simp
    have hw1 : ∀ (t : Fin T) (x' : Fin 1 → Fin T),
        Fin.cons (α := fun _ => Fin T) t x' 1 = x' 0 :=
      fun t x' => rfl
    simp only [hw0, hw1]
    rw [← Finset.sum_mul_sum]
    congr 1
    exact (hone fun x' => G₃ (x' 0)).trans rfl
  unfold wTriple
  refine Finset.sum_congr rfl fun y _ => ?_
  have hper : ∀ x : Fin 3 → Fin T,
      W (x 0) * B v (x 0) * (W (x 1) * B v (x 1) * (W (x 2) * B v (x 2) *
        (W y * (armSum B W a (x 0) y *
          (armSum B W b (x 1) y * armSum B W c (x 2) y))))) =
      W y * ((W (x 0) * B v (x 0) * armSum B W a (x 0) y) *
        ((W (x 1) * B v (x 1) * armSum B W b (x 1) y) *
          (W (x 2) * B v (x 2) * armSum B W c (x 2) y))) := fun x => by ring
  rw [Finset.sum_congr rfl fun x _ => hper x, ← Finset.mul_sum,
    hx3 (fun t => W t * B v t * armSum B W a t y)
      (fun t => W t * B v t * armSum B W b t y)
      (fun t => W t * B v t * armSum B W c t y),
    sum_weight_mul_armSum B hB W a (fun t => B v t) y,
    sum_weight_mul_armSum B hB W b (fun t => B v t) y,
    sum_weight_mul_armSum B hB W c (fun t => B v t) y]
  ring

/-- `weightedAdj` is subtractive (mirror of `weightedAdj_add`). -/
theorem weightedAdj_sub {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (f g : Fin T → ℝ) :
    weightedAdj B W (fun t => f t - g t) =
      fun t => weightedAdj B W f t - weightedAdj B W g t := by
  funext x
  unfold weightedAdj
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- Iterates of `weightedAdj` are subtractive. -/
theorem weightedAdjIter_sub {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    ∀ (q : ℕ) (f g : Fin T → ℝ),
      weightedAdjIter B W q (fun t => f t - g t) =
        fun t => weightedAdjIter B W q f t - weightedAdjIter B W q g t := by
  intro q
  induction q with
  | zero => intro f g; rfl
  | succ q ih =>
    intro f g
    show weightedAdj B W (weightedAdjIter B W q (fun t => f t - g t)) = _
    rw [ih f g, weightedAdj_sub]
    rfl

/-- **The cube's graph bridge** (proved modulo `k23Arms_eval`):
`4 ·` the K₂,₃-arms profile difference is exactly the polarized cube
observable at arm lengths `(a+1, b+1, c+1)`. -/
theorem rootedProfile_k23Arms_sub_eq_polarizedCubeObs {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (i j : Fin T) (a b c : ℕ) :
    4 * (rootedProfile B W i (k23Arms a b c) -
        rootedProfile B W j (k23Arms a b c)) =
      polarizedCubeObs B W i j (a + 1) (b + 1) (c + 1) := by
  rw [k23Arms_eval B hB W i a b c, k23Arms_eval B hB W j a b c]
  have hd : ∀ q : ℕ, weightedAdjIter B W q (rowDiff B i j) =
      fun t => weightedAdjIter B W q (fun s => B i s) t -
        weightedAdjIter B W q (fun s => B j s) t :=
    fun q => weightedAdjIter_sub B W q (fun s => B i s) (fun s => B j s)
  have hs : ∀ q : ℕ, weightedAdjIter B W q (rowSum B i j) =
      fun t => weightedAdjIter B W q (fun s => B i s) t +
        weightedAdjIter B W q (fun s => B j s) t :=
    fun q => weightedAdjIter_add B W q (fun s => B i s) (fun s => B j s)
  unfold polarizedCubeObs wTriple
  simp only [hd, hs]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-! ### The Hadamard-power lift (next target)

With the square moment closed, the route to the full rank theorem
`vertexOrbitRel_of_rootedProfileEquiv` runs through ALL weighted power sums
of the rows: `powerSum_descends_of_rootedProfileEquiv` below (k ≥ 3 is the
open content), then `weighted_powersum_determines_measure` (proved, in
`Lovasz.lean`) recovers equality of the `W`-weighted row-value measures
(`rowValueMeasure_eq_of_rootedProfileEquiv`).

**Status of k ≥ 3** (the genuine open math): writing `ε = B i - B j`, the gap
is `⟨ε, ρᵢ^{∘(k-1)} + ρᵢ^{∘(k-2)}∘ρⱼ + ⋯ + ρⱼ^{∘(k-1)}⟩_W` (Hadamard powers
of the rows). The available rpe-killed observables with `d` root edges give
`d`-leg kernels from the Hadamard-ordinary closure of walk kernels (theta
graphs; at most ONE bare-`B` factor per Hadamard bundle — parallel edges are
multigraph). The k = 2 proof recovered the forbidden diagonal 2-tensor via
`u ∈ Im M`; k ≥ 3 needs the analogous recovery of the diagonal k-tensor, one
level up. Note `B^{∘(k-1)}` itself is NOT in the observable kernel algebra
(even off the root), so the lift is a genuine extension, not a substitution. -/

/-- **Cube-moment descent** — **MATHEMATICALLY RESOLVED (2026-06-10),
formalization pending** (SORRY until the K₂,₃-arms plumbing lands).

**The K₂,₃-ARMS proof** (machine-precision validated,
`scripts/validate_cube_k23_arms.py`; mechanism UNIFORM in k — at k = 2 the
K₂,₂-with-arms graph IS the rooted cycle, recovering the proved case):
1. **Arms identity**: for the rooted K₂,₃-with-arms graph (root adjacent to
   anchors `t₁,t₂,t₃`; internal hub `y`; arm `l` a path of length `a_l ≥ 1`
   from `t_l` to `y` — a SIMPLE graph), the profile difference is exactly
   `(1/4)·Σ_{|S| odd} T₃(M^{a_l}ε [l∈S], M^{a_l}u [l∉S])` where
   `T₃(f,g,h) = ∑ t, W t * f t * g t * h t` (trilinear polarization of the
   three root edges; arms act as `M`-powers). rpe kills these for all arms.
2. **Common expansion (direct-sum trick)**: `(ε, u) ∈ Im (M ⊕ M)`,
   self-adjoint, so the k = 2 projection lemma applied to `E ⊕ E` yields
   COMMON coefficients `c_q` with `ε = Σ_{q≥1} c_q M^q ε` AND
   `u = Σ_{q≥1} c_q M^q u` simultaneously.
3. **Reconstruction**: `gap₃ = (1/4)·Σ_{|S| odd} T₃(ε[S], u[S^c])
   = Σ_{a⃗≥1} c_{a₁}c_{a₂}c_{a₃} · ObsDiff(a⃗) = 0`. ∎
Only `hB`, `hW` needed.

**How it was found**: the LM falsification run (k=2 harness, cube gap pinned)
went infeasible at T=4 already at the base m≤3 family; at T=5 it was exactly
feasible at m≤3 and the top m=4 separators were the four rooted K₂,₃'s —
identifying the family, after which the identity is three lines.

**Superseded analysis** (kept as history; the earlier residual-branch frontier
is BYPASSED by the right family): in eigenbasis coordinates the theta/wedge/
triangle-wedge families force `F ≡ 0` generically but left open the branch
`G = 0 ∧ f_λf_μ = -g_λg_μ ≠ 0 ∧ F ≠ 0`; the K₂,₃-arms constraints close the
gap without case analysis.

**Formalization plan** (next session): trilinear polarization lemma
(generalizing `wInner_sub_iter_add`), the direct-sum common-coefficient lemma
(from `inner_eq_zero_of_orthogonal_pos_powers`'s projection core applied to
`E ⊕ E` — extract the span-membership statement), and the K₂,₃-arms graph
family + evaluation bridge (generalizing `rootedCycleGraph` +
`rootedProfile_rootedCycleGraph_eq_closedWalkProfile`). -/
theorem cubeMoment_descends_of_rootedProfileEquiv {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ t, 0 < W t)
    {i j : Fin T} (h : rootedProfileEquiv B W i j) :
    ∑ t : Fin T, W t * B i t ^ 3 = ∑ t : Fin T, W t * B j t ^ 3 := by
  refine cubeGap_eq_zero_of_polarized_obs B hB W hW i j fun a b c => ?_
  rw [← rootedProfile_k23Arms_sub_eq_polarizedCubeObs B hB W i j a b c,
    h (4 + a + b + c) (k23Arms a b c), sub_self, mul_zero]

/-! ### The `K₂,ₖ`-with-arms family (k ≥ 4 lift) — structured-vertex design

The cube case used `k23Arms`, a `SimpleGraph (Fin (4 + a + b + c + 1))` built
from explicit offset arithmetic (`armSeq`, `armStart`, nested `appendFn`). That
layout does not scale to an arbitrary number `k` of arms: the dependent block
offsets become unmanageable.

Instead we reason on a **structured** finite vertex type `K2kVertex k armLen`
and transport the graph to `Fin (n + 1)` only at the boundary forced by
`rootedProfile`, which is hardwired to `SimpleGraph (Fin (n + 1))` with the root
at position `0`. All human reasoning stays on the constructors; the `Fin`
version is a pure transport artifact (`SimpleGraph.comap` along an equivalence
that pins the root to `0`). -/

/-- **Structured vertex type** of the rooted `K₂,ₖ`-with-arms graph: a `root`,
one `anchor` per arm `l : Fin k`, a shared `hub`, and `armLen l` `internal`
vertices on arm `l`. Arm `l` is the path
`anchor l — internal l 0 — ⋯ — internal l (armLen l - 1) — hub`
(when `armLen l = 0` the arm degenerates to the single edge `anchor l — hub`). -/
inductive K2kVertex (k : ℕ) (armLen : Fin k → ℕ)
  | root
  | anchor (l : Fin k)
  | hub
  | internal (l : Fin k) (s : Fin (armLen l))
  deriving DecidableEq

/-- The NON-root vertices of `K2kVertex` as an explicit `Fintype`:
anchors `⊕` hub `⊕` internals. Carries the cardinality computation and lets us
pin the root to position `0` of the `Fin` transport. -/
abbrev K2kRest (k : ℕ) (armLen : Fin k → ℕ) : Type :=
  Fin k ⊕ Unit ⊕ (Σ l : Fin k, Fin (armLen l))

/-- `K2kVertex` is `root` adjoined to `K2kRest` (`root ↦ none`). This single
equivalence supplies the `Fintype` instance and pins the root for the `Fin`
transport. -/
def k2kVertexOptionEquiv (k : ℕ) (armLen : Fin k → ℕ) :
    K2kVertex k armLen ≃ Option (K2kRest k armLen) where
  toFun
    | .root => none
    | .anchor l => some (.inl l)
    | .hub => some (.inr (.inl ()))
    | .internal l s => some (.inr (.inr ⟨l, s⟩))
  invFun
    | none => .root
    | some (.inl l) => .anchor l
    | some (.inr (.inl ())) => .hub
    | some (.inr (.inr ⟨l, s⟩)) => .internal l s
  left_inv v := by cases v <;> rfl
  right_inv o := by rcases o with _ | l | u | ⟨l, s⟩ <;> rfl

instance (k : ℕ) (armLen : Fin k → ℕ) : Fintype (K2kVertex k armLen) :=
  Fintype.ofEquiv _ (k2kVertexOptionEquiv k armLen).symm

/-- Number of NON-root vertices: `k` anchors `+ 1` hub `+ ∑ armLen` internals. -/
def k2kRestCard (k : ℕ) (armLen : Fin k → ℕ) : ℕ := k + 1 + ∑ l : Fin k, armLen l

theorem k2kRest_card (k : ℕ) (armLen : Fin k → ℕ) :
    Fintype.card (K2kRest k armLen) = k2kRestCard k armLen := by
  simp only [K2kRest, k2kRestCard, Fintype.card_sum, Fintype.card_sigma,
    Fintype.card_fin, Fintype.card_unit]
  ring

/-- **Vertex equivalence to `Fin (n + 1)`** with the **root pinned to `0`** —
the position `simpleEvalAt`/`rootedProfile` fix to the labelled vertex.
Built as `K2kVertex ≃ Option (K2kRest) ≃ Option (Fin n) ≃ Fin (n + 1)`; the last
step `(finSuccEquiv n).symm` sends `none ↦ 0`, and the root is the unique
preimage of `none`. -/
noncomputable def K2kVertex_equivFin (k : ℕ) (armLen : Fin k → ℕ) :
    K2kVertex k armLen ≃ Fin (k2kRestCard k armLen + 1) :=
  (k2kVertexOptionEquiv k armLen).trans
    ((Equiv.optionCongr (Fintype.equivFinOfCardEq (k2kRest_card k armLen))).trans
      (finSuccEquiv (k2kRestCard k armLen)).symm)

@[simp] theorem K2kVertex_equivFin_root (k : ℕ) (armLen : Fin k → ℕ) :
    K2kVertex_equivFin k armLen .root = 0 := by
  have h : K2kVertex_equivFin k armLen .root
      = (finSuccEquiv (k2kRestCard k armLen)).symm none := rfl
  rw [h, Equiv.symm_apply_eq, finSuccEquiv_zero]

/-- The `s`-th vertex along arm `l`: `0 ↦ anchor`, `1 .. armLen ↦ internal`,
anything beyond `armLen ↦ hub`. The structured analogue of `armSeq`, valued in
the constructors (no `Fin`-offset arithmetic). When `armLen l = 0` the chain is
just `anchor l —(s=0)→ hub —(s=1)→ hub`, i.e. the single edge `anchor l — hub`. -/
def K2kVertex.armNode (k : ℕ) (armLen : Fin k → ℕ) (l : Fin k) (s : ℕ) :
    K2kVertex k armLen :=
  if hs0 : s = 0 then .anchor l
  else if hsa : s ≤ armLen l then .internal l ⟨s - 1, by omega⟩
  else .hub

/-- Consecutive arm vertices differ (needed for `loopless`). -/
theorem K2kVertex.armNode_succ_ne (k : ℕ) (armLen : Fin k → ℕ) (l : Fin k)
    {s : ℕ} (hs : s ≤ armLen l) :
    K2kVertex.armNode k armLen l s ≠ K2kVertex.armNode k armLen l (s + 1) := by
  unfold K2kVertex.armNode
  rcases Nat.eq_zero_or_pos s with hs0 | hspos
  · subst hs0
    rw [dif_pos (rfl : (0 : ℕ) = 0), dif_neg (by omega : ¬ (0 + 1 : ℕ) = 0)]
    split_ifs <;> simp
  · rw [dif_neg (by omega : ¬ s = 0), dif_pos hs, dif_neg (by omega : ¬ s + 1 = 0)]
    split_ifs with hsa
    · simp only [ne_eq, K2kVertex.internal.injEq, heq_eq_eq, Fin.mk.injEq, true_and]; omega
    · simp

/-- **The structured rooted `K₂,ₖ`-with-arms graph** on `K2kVertex k armLen`:
the `root` is adjacent to every `anchor l`; arm `l` is the path
`anchor l — internal l 0 — ⋯ — internal l (armLen l - 1) — hub` (the consecutive
pairs `armNode l s — armNode l (s+1)` for `s ≤ armLen l`). All reasoning about
the family happens here; the `Fin` version `k2kArms` is a transport of this. -/
def k2kArmsStructured (k : ℕ) (armLen : Fin k → ℕ) :
    SimpleGraph (K2kVertex k armLen) where
  Adj u v :=
    (∃ l : Fin k, (u = .root ∧ v = .anchor l) ∨ (v = .root ∧ u = .anchor l)) ∨
    (∃ l : Fin k, ∃ s ≤ armLen l,
      (u = K2kVertex.armNode k armLen l s ∧ v = K2kVertex.armNode k armLen l (s + 1)) ∨
      (v = K2kVertex.armNode k armLen l s ∧ u = K2kVertex.armNode k armLen l (s + 1)))
  symm := by
    intro u v h
    rcases h with ⟨l, h⟩ | ⟨l, s, hs, h⟩
    · exact Or.inl ⟨l, h.symm⟩
    · exact Or.inr ⟨l, s, hs, h.symm⟩
  loopless := by
    intro u h
    rcases h with ⟨l, h⟩ | ⟨l, s, hs, h⟩
    · obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := h <;> (rw [h1] at h2; simp at h2)
    · obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := h <;>
        exact K2kVertex.armNode_succ_ne k armLen l hs (h1.symm.trans h2)

instance (k : ℕ) (armLen : Fin k → ℕ) :
    DecidableRel (k2kArmsStructured k armLen).Adj :=
  fun _ _ => by unfold k2kArmsStructured; infer_instance

/-- **The `Fin`-indexed `K₂,ₖ`-with-arms graph** consumed by `rootedProfile`:
the structured graph pulled back along the root-pinned equivalence. Because
`K2kVertex_equivFin .root = 0`, position `0` of `Fin (n + 1)` is the root — the
position `simpleEvalAt`/`rootedProfile` fix to the labelled vertex. -/
noncomputable def k2kArms (k : ℕ) (armLen : Fin k → ℕ) :
    SimpleGraph (Fin (k2kRestCard k armLen + 1)) :=
  (k2kArmsStructured k armLen).comap (K2kVertex_equivFin k armLen).symm

noncomputable instance (k : ℕ) (armLen : Fin k → ℕ) :
    DecidableRel (k2kArms k armLen).Adj :=
  SimpleGraph.instDecidableComapAdj _ _

/-- The edge index type of `k2kArmsStructured`: `k` root-anchor edges plus, per
arm `l`, the `armLen l + 1` chain edges. -/
abbrev K2kEdgeIdx (k : ℕ) (armLen : Fin k → ℕ) : Type :=
  Fin k ⊕ (Σ l : Fin k, Fin (armLen l + 1))

/-- The edge family of `k2kArmsStructured`, indexed by `K2kEdgeIdx`. -/
def k2kEdge (k : ℕ) (armLen : Fin k → ℕ) :
    K2kEdgeIdx k armLen → Sym2 (K2kVertex k armLen)
  | .inl l => s(.root, .anchor l)
  | .inr ⟨l, s⟩ =>
      s(K2kVertex.armNode k armLen l s, K2kVertex.armNode k armLen l ((s : ℕ) + 1))

/-- Every indexed edge is an edge of `k2kArmsStructured`. -/
theorem k2kEdge_mem (k : ℕ) (armLen : Fin k → ℕ) (idx : K2kEdgeIdx k armLen) :
    k2kEdge k armLen idx ∈ (k2kArmsStructured k armLen).edgeSet := by
  match idx with
  | .inl l =>
    rw [k2kEdge, SimpleGraph.mem_edgeSet]
    exact Or.inl ⟨l, Or.inl ⟨rfl, rfl⟩⟩
  | .inr ⟨l, s⟩ =>
    rw [k2kEdge, SimpleGraph.mem_edgeSet]
    exact Or.inr ⟨l, (s : ℕ), by have := s.isLt; omega, Or.inl ⟨rfl, rfl⟩⟩

/-- **Edge classification** for the `K₂,ₖ`-with-arms family: the edge finset is
exactly the image of the indexed family `k2kEdge` — the `k` root-anchor edges
plus the `k` arm chains, and nothing else. This is the structured, reusable form
(the analogue of `k23Arms_edgeFinset`); the eventual `k2kArms_eval` will reindex
the edge product of the `Fin` graph through this. -/
theorem k2kArmsStructured_edgeFinset (k : ℕ) (armLen : Fin k → ℕ) :
    (k2kArmsStructured k armLen).edgeFinset =
      Finset.image (k2kEdge k armLen) Finset.univ := by
  classical
  ext e
  simp only [SimpleGraph.mem_edgeFinset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ u w =>
      rw [SimpleGraph.mem_edgeSet] at he
      rcases he with ⟨l, hroot⟩ | ⟨l, s, hs, harm⟩
      · refine ⟨.inl l, ?_⟩
        rw [k2kEdge, Sym2.eq_iff]
        tauto
      · refine ⟨.inr ⟨l, ⟨s, by omega⟩⟩, ?_⟩
        rw [k2kEdge, Sym2.eq_iff]
        tauto
  · rintro ⟨idx, rfl⟩
    exact k2kEdge_mem k armLen idx

/-! #### Commit 1 — Fin/structured edge transport + edge-product factorization -/

/-- `Quot.out` resolver on a literal `Sym2` pair over an ARBITRARY vertex type
(the `out_pair_eq` generalization needed for the structured graph). -/
theorem out_pair_eq' {T' : ℕ} {V : Type*} (Bm : Fin T' → Fin T' → ℝ)
    (hB : ∀ i j, Bm i j = Bm j i) (g : V → Fin T') (x y : V) :
    Bm (g (Quot.out s(x, y)).1) (g (Quot.out s(x, y)).2) = Bm (g x) (g y) := by
  have hout := Quot.out_eq s(x, y)
  rw [Sym2.mk_eq_mk_iff] at hout
  rcases hout with h | h
  · rw [congrArg Prod.fst h, congrArg Prod.snd h]
  · simp only [Prod.swap] at h
    rw [congrArg Prod.fst h, congrArg Prod.snd h, hB]

/-- Arm index of a vertex (anchors/internals carry their arm; root/hub `none`).
Used to recover `(l, s)` from a chain endpoint in `k2kEdge_injective`. -/
def K2kVertex.armOf {k : ℕ} {armLen : Fin k → ℕ} :
    K2kVertex k armLen → Option (Fin k)
  | .root => none
  | .anchor l => some l
  | .hub => none
  | .internal l _ => some l

/-- Step (depth) of a vertex along its arm (`0` for anchor, `s+1` for
internal `s`); `0` on root/hub (irrelevant there). -/
def K2kVertex.stepOf {k : ℕ} {armLen : Fin k → ℕ} : K2kVertex k armLen → ℕ
  | .root => 0
  | .anchor _ => 0
  | .hub => 0
  | .internal _ s => (s : ℕ) + 1

theorem K2kVertex.armOf_armNode {k : ℕ} {armLen : Fin k → ℕ} {l : Fin k} {s : ℕ}
    (hs : s ≤ armLen l) : (K2kVertex.armNode k armLen l s).armOf = some l := by
  unfold K2kVertex.armNode; split_ifs <;> rfl

theorem K2kVertex.stepOf_armNode {k : ℕ} {armLen : Fin k → ℕ} {l : Fin k} {s : ℕ}
    (hs : s ≤ armLen l) : (K2kVertex.armNode k armLen l s).stepOf = s := by
  unfold K2kVertex.armNode
  rcases Nat.eq_zero_or_pos s with rfl | hpos
  · rfl
  · rw [dif_neg (by omega : ¬ s = 0), dif_pos hs]
    simp only [K2kVertex.stepOf]; omega

theorem K2kVertex.armNode_ne_root {k : ℕ} {armLen : Fin k → ℕ} (l : Fin k) (s : ℕ) :
    K2kVertex.armNode k armLen l s ≠ .root := by
  unfold K2kVertex.armNode; split_ifs <;> simp

theorem K2kVertex.armNode_eq_hub_of_gt {k : ℕ} {armLen : Fin k → ℕ} {l : Fin k}
    {s : ℕ} (h : armLen l < s) : K2kVertex.armNode k armLen l s = .hub := by
  unfold K2kVertex.armNode
  rw [dif_neg (by omega : ¬ s = 0), dif_neg (by omega : ¬ s ≤ armLen l)]

/-- The indexed edge family is injective (each `(l, s)` recovered from the
non-hub chain endpoint via `armOf`/`stepOf`; the reversed orientation is killed
by `omega`). The structured analogue of `armSeq_pair_inj`. -/
theorem k2kEdge_injective (k : ℕ) (armLen : Fin k → ℕ) :
    Function.Injective (k2kEdge k armLen) := by
  intro x y hxy
  match x, y with
  | .inl l, .inl l' =>
      simp only [k2kEdge, Sym2.eq_iff] at hxy
      rcases hxy with ⟨-, h⟩ | ⟨h, -⟩
      · simp only [K2kVertex.anchor.injEq] at h; subst h; rfl
      · exact absurd h (by simp)
  | .inl l, .inr ⟨l', s'⟩ =>
      exfalso; simp only [k2kEdge, Sym2.eq_iff] at hxy
      rcases hxy with ⟨h, -⟩ | ⟨h, -⟩ <;> exact K2kVertex.armNode_ne_root _ _ h.symm
  | .inr ⟨l, s⟩, .inl l' =>
      exfalso; simp only [k2kEdge, Sym2.eq_iff] at hxy
      rcases hxy with ⟨h, -⟩ | ⟨-, h⟩ <;> exact K2kVertex.armNode_ne_root _ _ h
  | .inr ⟨l, s⟩, .inr ⟨l', s'⟩ =>
      have hsl : (s : ℕ) ≤ armLen l := by have := s.isLt; omega
      have hsl' : (s' : ℕ) ≤ armLen l' := by have := s'.isLt; omega
      simp only [k2kEdge, Sym2.eq_iff] at hxy
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hl : l = l' := by
          have ha := congrArg K2kVertex.armOf h1
          rw [K2kVertex.armOf_armNode hsl, K2kVertex.armOf_armNode hsl'] at ha
          exact Option.some.inj ha
        subst hl
        have hss : s = s' := by
          apply Fin.ext
          have hst := congrArg K2kVertex.stepOf h1
          rwa [K2kVertex.stepOf_armNode hsl, K2kVertex.stepOf_armNode hsl'] at hst
        subst hss; rfl
      · exfalso
        have hl : l = l' := by
          have ha := congrArg K2kVertex.armOf h1
          rw [K2kVertex.armOf_armNode hsl] at ha
          by_cases hc : armLen l' < (s' : ℕ) + 1
          · rw [K2kVertex.armNode_eq_hub_of_gt hc] at ha; simp [K2kVertex.armOf] at ha
          · rw [K2kVertex.armOf_armNode (by omega)] at ha; exact Option.some.inj ha
        subst hl
        have hub1 : (s' : ℕ) + 1 ≤ armLen l := by
          by_contra hc
          have ha := congrArg K2kVertex.armOf h1
          rw [K2kVertex.armOf_armNode hsl, K2kVertex.armNode_eq_hub_of_gt (by omega)] at ha
          simp [K2kVertex.armOf] at ha
        have hub2 : (s : ℕ) + 1 ≤ armLen l := by
          by_contra hc
          have ha := congrArg K2kVertex.armOf h2
          rw [K2kVertex.armNode_eq_hub_of_gt (by omega : armLen l < (s : ℕ) + 1),
              K2kVertex.armOf_armNode hsl'] at ha
          simp [K2kVertex.armOf] at ha
        have e1 := congrArg K2kVertex.stepOf h1
        rw [K2kVertex.stepOf_armNode hsl, K2kVertex.stepOf_armNode hub1] at e1
        have e2 := congrArg K2kVertex.stepOf h2
        rw [K2kVertex.stepOf_armNode hub2, K2kVertex.stepOf_armNode hsl'] at e2
        omega

/-- **Edge-product factorization on the structured graph** (the analogue of
`k23Arms_prod_eq`): the edge product splits into the `k` root-edge factors and
the `k` independent arm-chain products. -/
theorem k2kArmsStructured_prod_eq (k : ℕ) (armLen : Fin k → ℕ)
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (Φ : K2kVertex k armLen → Fin T) :
    (∏ E ∈ (k2kArmsStructured k armLen).edgeFinset,
        B (Φ (Quot.out E).1) (Φ (Quot.out E).2)) =
      (∏ l : Fin k, B (Φ .root) (Φ (.anchor l))) *
        ∏ l : Fin k, ∏ s : Fin (armLen l + 1),
          B (Φ (K2kVertex.armNode k armLen l s))
            (Φ (K2kVertex.armNode k armLen l ((s : ℕ) + 1))) := by
  classical
  rw [k2kArmsStructured_edgeFinset,
    Finset.prod_image (fun x _ y _ h => k2kEdge_injective k armLen h),
    Fintype.prod_sum_type]
  congr 1
  · exact Finset.prod_congr rfl fun l _ => by
      simp only [k2kEdge]; exact out_pair_eq' B hB Φ _ _
  · rw [← Finset.univ_sigma_univ, Finset.prod_sigma]
    exact Finset.prod_congr rfl fun l _ => Finset.prod_congr rfl fun s _ => by
      simp only [k2kEdge]; exact out_pair_eq' B hB Φ _ _

/-- Edge finset of a graph pulled back along an equivalence's inverse is the
`Sym2`-image of the source edge finset (generic transport lemma). -/
theorem comap_symm_edgeFinset {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (e : V ≃ W) (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    (SimpleGraph.comap e.symm G).edgeFinset =
      Finset.map e.toEmbedding.sym2Map G.edgeFinset := by
  have hG : SimpleGraph.comap (⇑e.symm) G = SimpleGraph.map e.toEmbedding G :=
    SimpleGraph.comap_symm G e
  rw [← SimpleGraph.edgeFinset_map e.toEmbedding G]
  apply Finset.coe_injective
  rw [SimpleGraph.coe_edgeFinset, SimpleGraph.coe_edgeFinset, hG]

/-- **Edge-finset transport** for the `Fin`-rooted graph: `k2kArms`' edges are
the `K2kVertex_equivFin`-images of the structured graph's edges. -/
theorem k2kArms_edgeFinset_transport (k : ℕ) (armLen : Fin k → ℕ) :
    (k2kArms k armLen).edgeFinset =
      Finset.map (K2kVertex_equivFin k armLen).toEmbedding.sym2Map
        (k2kArmsStructured k armLen).edgeFinset :=
  comap_symm_edgeFinset (K2kVertex_equivFin k armLen) (k2kArmsStructured k armLen)

/-- **Edge-product factorization on the `Fin` graph** (transport + structured
factorization combined): the `rootedProfile` edge product over `k2kArms`
factors, through `K2kVertex_equivFin`, into the `k` root-edge factors and the
`k` arm-chain products. This is the replacement for the brittle `k23Arms`
offset work; `k2kArms_eval` consumes it directly. -/
theorem k2kArms_prod_eq_structured (k : ℕ) (armLen : Fin k → ℕ)
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (τ : Fin (k2kRestCard k armLen + 1) → Fin T) :
    (∏ E ∈ (k2kArms k armLen).edgeFinset, B (τ (Quot.out E).1) (τ (Quot.out E).2)) =
      (∏ l : Fin k, B (τ (K2kVertex_equivFin k armLen .root))
          (τ (K2kVertex_equivFin k armLen (.anchor l)))) *
        ∏ l : Fin k, ∏ s : Fin (armLen l + 1),
          B (τ (K2kVertex_equivFin k armLen (K2kVertex.armNode k armLen l s)))
            (τ (K2kVertex_equivFin k armLen
              (K2kVertex.armNode k armLen l ((s : ℕ) + 1)))) := by
  classical
  rw [k2kArms_edgeFinset_transport, Finset.prod_map]
  have key : ∀ E' : Sym2 (K2kVertex k armLen),
      B (τ (Quot.out ((K2kVertex_equivFin k armLen).toEmbedding.sym2Map E')).1)
        (τ (Quot.out ((K2kVertex_equivFin k armLen).toEmbedding.sym2Map E')).2) =
      B ((fun x => τ (K2kVertex_equivFin k armLen x)) (Quot.out E').1)
        ((fun x => τ (K2kVertex_equivFin k armLen x)) (Quot.out E').2) := by
    intro E'
    induction E' using Sym2.ind with
    | _ a b =>
      rw [show (K2kVertex_equivFin k armLen).toEmbedding.sym2Map s(a, b)
          = s(K2kVertex_equivFin k armLen a, K2kVertex_equivFin k armLen b) from rfl,
        out_pair_eq' B hB τ _ _,
        out_pair_eq' B hB (fun x => τ (K2kVertex_equivFin k armLen x)) a b]
  rw [Finset.prod_congr rfl fun E' _ => key E']
  exact k2kArmsStructured_prod_eq k armLen B hB (fun x => τ (K2kVertex_equivFin k armLen x))

/-! #### Commit 2 — structured eval expansion (reindex + per-arm collapse) -/

/-- The non-root part of `K2kVertex_equivFin` as a standalone equivalence
`K2kRest ≃ Fin (k2kRestCard)` (definitionally the rest-equiv inside
`K2kVertex_equivFin`). -/
noncomputable def k2kRestEquivFin (k : ℕ) (armLen : Fin k → ℕ) :
    K2kRest k armLen ≃ Fin (k2kRestCard k armLen) :=
  Fintype.equivFinOfCardEq (k2kRest_card k armLen)

/-- **Vertex → Fin-position value lemma**: a non-root vertex `r` (as a `K2kRest`
element adjoined via `k2kVertexOptionEquiv.symm`) sits at position
`(k2kRestEquivFin r).succ` — i.e. one past the root (which is `0`). This is the
sole fact about the opaque rest-equiv the reindexing needs. -/
theorem K2kVertex_equivFin_some (k : ℕ) (armLen : Fin k → ℕ)
    (r : K2kRest k armLen) :
    K2kVertex_equivFin k armLen ((k2kVertexOptionEquiv k armLen).symm (some r))
      = (k2kRestEquivFin k armLen r).succ := by
  rw [K2kVertex_equivFin]
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.optionCongr_apply,
    Option.map_some, finSuccEquiv_symm_some]
  rfl

/-- The structured assignment `K2kVertex → Fin T` with `root ↦ v` and each
non-root vertex `r` taking the value `ρ r`. -/
def extendV {k : ℕ} {armLen : Fin k → ℕ} (v : Fin T)
    (ρ : K2kRest k armLen → Fin T) : K2kVertex k armLen → Fin T :=
  fun w => (k2kVertexOptionEquiv k armLen w).elim v ρ

@[simp] theorem extendV_root {k : ℕ} {armLen : Fin k → ℕ} (v : Fin T)
    (ρ : K2kRest k armLen → Fin T) : extendV v ρ (.root) = v := rfl

@[simp] theorem extendV_anchor {k : ℕ} {armLen : Fin k → ℕ} (v : Fin T)
    (ρ : K2kRest k armLen → Fin T) (l : Fin k) :
    extendV v ρ (.anchor l) = ρ (.inl l) := rfl

@[simp] theorem extendV_hub {k : ℕ} {armLen : Fin k → ℕ} (v : Fin T)
    (ρ : K2kRest k armLen → Fin T) : extendV v ρ (.hub) = ρ (.inr (.inl ())) := rfl

@[simp] theorem extendV_internal {k : ℕ} {armLen : Fin k → ℕ} (v : Fin T)
    (ρ : K2kRest k armLen → Fin T) (l : Fin k) (s : Fin (armLen l)) :
    extendV v ρ (.internal l s) = ρ (.inr (.inr ⟨l, s⟩)) := rfl

/-- On arm `l`, `extendV ∘ armNode` is exactly the free-standing `chainPath`
from the anchor value to the hub value over the arm's internal values. -/
theorem extendV_armNode {k : ℕ} {armLen : Fin k → ℕ} (v : Fin T)
    (ρ : K2kRest k armLen → Fin T) (l : Fin k) {s : ℕ} (hs : s ≤ armLen l + 1) :
    extendV v ρ (K2kVertex.armNode k armLen l s) =
      chainPath (armLen l) (ρ (.inl l)) (ρ (.inr (.inl ())))
        (fun j => ρ (.inr (.inr ⟨l, j⟩))) s := by
  unfold K2kVertex.armNode chainPath
  rcases Nat.eq_zero_or_pos s with rfl | hpos
  · simp
  · rw [dif_neg (by omega : ¬ s = 0), dif_neg (by omega : ¬ s = 0)]
    by_cases hsa : s ≤ armLen l
    · rw [dif_pos hsa, dif_pos hsa, extendV_internal]
    · rw [dif_neg hsa, dif_neg hsa, extendV_hub]

/-- **Edge-product transport** (product form): the `Fin`-graph edge product equals
the structured edge product with vertices read through `K2kVertex_equivFin`. -/
theorem k2kArms_edge_prod_transport (k : ℕ) (armLen : Fin k → ℕ)
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (τ : Fin (k2kRestCard k armLen + 1) → Fin T) :
    (∏ E ∈ (k2kArms k armLen).edgeFinset, B (τ (Quot.out E).1) (τ (Quot.out E).2)) =
      ∏ E ∈ (k2kArmsStructured k armLen).edgeFinset,
        B (τ (K2kVertex_equivFin k armLen (Quot.out E).1))
          (τ (K2kVertex_equivFin k armLen (Quot.out E).2)) := by
  rw [k2kArms_edgeFinset_transport, Finset.prod_map]
  refine Finset.prod_congr rfl fun E' _ => ?_
  induction E' using Sym2.ind with
  | _ a b =>
    rw [show (K2kVertex_equivFin k armLen).toEmbedding.sym2Map s(a, b)
        = s(K2kVertex_equivFin k armLen a, K2kVertex_equivFin k armLen b) from rfl,
      out_pair_eq' B hB τ _ _,
      out_pair_eq' B hB (fun x => τ (K2kVertex_equivFin k armLen x)) a b]

/-- **Reindexing the eval onto structured assignments**: the rooted profile of
`k2kArms` is the sum over structured non-root assignments `ρ : K2kRest → Fin T`
of the structured weight × edge product (root pinned to `v`). -/
theorem rootedProfile_k2kArms_eq_structSum (k : ℕ) (armLen : Fin k → ℕ)
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (v : Fin T) :
    rootedProfile B W v (k2kArms k armLen)
      = ∑ ρ : K2kRest k armLen → Fin T,
          (∏ r, W (ρ r)) *
          ∏ E ∈ (k2kArmsStructured k armLen).edgeFinset,
            B (extendV v ρ (Quot.out E).1) (extendV v ρ (Quot.out E).2) := by
  rw [rootedProfile, simpleEvalAt]
  refine Fintype.sum_equiv
    (Equiv.arrowCongr (k2kRestEquivFin k armLen).symm (Equiv.refl (Fin T)))
    _ _ (fun σ => ?_)
  have hτ : ∀ w : K2kVertex k armLen,
      (if h : (↑(K2kVertex_equivFin k armLen w) : ℕ) < 1 then v
        else σ ⟨↑(K2kVertex_equivFin k armLen w) - 1, by
          have := (K2kVertex_equivFin k armLen w).isLt
          have : 1 ≤ k2kRestCard k armLen := by unfold k2kRestCard; omega
          omega⟩)
      = extendV v (fun r => σ (k2kRestEquivFin k armLen r)) w := by
    intro w
    by_cases hw : w = K2kVertex.root
    · subst hw; simp [K2kVertex_equivFin_root]
    · obtain ⟨r, rfl⟩ : ∃ r, w = (k2kVertexOptionEquiv k armLen).symm (some r) := by
        rcases h : k2kVertexOptionEquiv k armLen w with _ | r
        · exact absurd ((k2kVertexOptionEquiv k armLen).injective h) hw
        · exact ⟨r, by rw [← (k2kVertexOptionEquiv k armLen).symm_apply_apply w, h]⟩
      simp only [K2kVertex_equivFin_some, extendV, Equiv.apply_symm_apply,
        Option.elim_some]
      rw [dif_neg (by simp [Fin.val_succ] :
        ¬ (↑(k2kRestEquivFin k armLen r).succ : ℕ) < 1)]
      exact congrArg σ (Fin.ext (by simp [Fin.val_succ]))
  have hρ' : (Equiv.arrowCongr (k2kRestEquivFin k armLen).symm (Equiv.refl (Fin T))) σ
      = fun r => σ (k2kRestEquivFin k armLen r) := by
    funext r; simp [Equiv.arrowCongr_apply]
  rw [hρ']
  dsimp only
  rw [k2kArms_edge_prod_transport k armLen B hB
        (fun v_ : Fin (k2kRestCard k armLen + 1) =>
          if h : (↑v_ : ℕ) < 1 then v else σ ⟨↑v_ - 1, by have := v_.isLt; omega⟩),
    ← Equiv.prod_comp (k2kRestEquivFin k armLen) (fun w => W (σ w))]
  refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun E _ => ?_)
  rw [hτ (Quot.out E).1, hτ (Quot.out E).2]

/-- **Assignment splitting equivalence**: a non-root structured assignment is
exactly a triple (anchor values, hub value, per-arm internal values). Built
directly so the component value lemmas are `rfl`. -/
def assignEquiv (k : ℕ) (armLen : Fin k → ℕ) :
    (K2kRest k armLen → Fin T) ≃
      (Fin k → Fin T) × Fin T × ((l : Fin k) → Fin (armLen l) → Fin T) where
  toFun ρ := (fun l => ρ (.inl l), ρ (.inr (.inl ())),
    fun l j => ρ (.inr (.inr ⟨l, j⟩)))
  invFun p := fun r => r.elim p.1
    (fun u => u.elim (fun _ => p.2.1) (fun s => p.2.2 s.1 s.2))
  left_inv ρ := by funext r; rcases r with l | u | ⟨l, j⟩ <;> rfl
  right_inv p := rfl

@[simp] theorem assignEquiv_symm_inl (k : ℕ) (armLen : Fin k → ℕ)
    (p : (Fin k → Fin T) × Fin T × ((l : Fin k) → Fin (armLen l) → Fin T))
    (l : Fin k) : (assignEquiv k armLen).symm p (.inl l) = p.1 l := rfl

@[simp] theorem assignEquiv_symm_hub (k : ℕ) (armLen : Fin k → ℕ)
    (p : (Fin k → Fin T) × Fin T × ((l : Fin k) → Fin (armLen l) → Fin T)) :
    (assignEquiv k armLen).symm p (.inr (.inl ())) = p.2.1 := rfl

@[simp] theorem assignEquiv_symm_inr (k : ℕ) (armLen : Fin k → ℕ)
    (p : (Fin k → Fin T) × Fin T × ((l : Fin k) → Fin (armLen l) → Fin T))
    (l : Fin k) (j : Fin (armLen l)) :
    (assignEquiv k armLen).symm p (.inr (.inr ⟨l, j⟩)) = p.2.2 l j := rfl

/-- Factorization of the structured vertex-weight product over the three
vertex blocks (anchors / hub / internals). -/
theorem k2kRest_weight_prod (k : ℕ) (armLen : Fin k → ℕ) (W : Fin T → ℝ)
    (ρ : K2kRest k armLen → Fin T) :
    (∏ r, W (ρ r)) =
      (∏ l : Fin k, W (ρ (.inl l))) *
        (W (ρ (.inr (.inl ()))) *
          ∏ l : Fin k, ∏ j : Fin (armLen l), W (ρ (.inr (.inr ⟨l, j⟩)))) := by
  classical
  rw [Fintype.prod_sum_type]
  congr 1
  rw [Fintype.prod_sum_type]
  congr 1
  · exact Fintype.prod_unique _
  · rw [← Finset.univ_sigma_univ, Finset.prod_sigma]

/-- **Structured eval expansion** (Commit 2b): the rooted profile of `k2kArms`
expands as a hub sum of an anchor sum of per-arm `armSum` kernels. -/
theorem k2kArms_eval_expanded (k : ℕ) (armLen : Fin k → ℕ)
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (v : Fin T) :
    rootedProfile B W v (k2kArms k armLen)
      = ∑ hub : Fin T, W hub *
          ∑ anchors : Fin k → Fin T,
            ∏ l : Fin k,
              W (anchors l) * B v (anchors l) * armSum B W (armLen l) (anchors l) hub := by
  classical
  rw [rootedProfile_k2kArms_eq_structSum k armLen B hB W v]
  -- Step 1: per-ρ summand → hub weight × per-arm (anchor weight·edge · internals·chain)
  have hsummand : ∀ ρ : K2kRest k armLen → Fin T,
      (∏ r, W (ρ r)) *
        ∏ E ∈ (k2kArmsStructured k armLen).edgeFinset,
          B (extendV v ρ (Quot.out E).1) (extendV v ρ (Quot.out E).2)
      = W (ρ (.inr (.inl ()))) *
          ∏ l : Fin k,
            W (ρ (.inl l)) * B v (ρ (.inl l)) *
              ((∏ j : Fin (armLen l), W (ρ (.inr (.inr ⟨l, j⟩)))) *
                ∏ s : Fin (armLen l + 1),
                  B (chainPath (armLen l) (ρ (.inl l)) (ρ (.inr (.inl ())))
                      (fun j => ρ (.inr (.inr ⟨l, j⟩))) s)
                    (chainPath (armLen l) (ρ (.inl l)) (ρ (.inr (.inl ())))
                      (fun j => ρ (.inr (.inr ⟨l, j⟩))) ((s : ℕ) + 1))) := by
    intro ρ
    have harm : ∀ (l : Fin k) (s : Fin (armLen l + 1)),
        B (extendV v ρ (K2kVertex.armNode k armLen l s))
          (extendV v ρ (K2kVertex.armNode k armLen l ((s : ℕ) + 1)))
        = B (chainPath (armLen l) (ρ (.inl l)) (ρ (.inr (.inl ())))
              (fun j => ρ (.inr (.inr ⟨l, j⟩))) s)
            (chainPath (armLen l) (ρ (.inl l)) (ρ (.inr (.inl ())))
              (fun j => ρ (.inr (.inr ⟨l, j⟩))) ((s : ℕ) + 1)) := fun l s => by
      rw [extendV_armNode v ρ l (by have := s.isLt; omega),
          extendV_armNode v ρ l (by have := s.isLt; omega)]
    rw [k2kArmsStructured_prod_eq k armLen B hB (extendV v ρ), k2kRest_weight_prod]
    simp only [extendV_root, extendV_anchor, harm, Finset.prod_mul_distrib]
    ring
  simp only [hsummand]
  -- Step 2: reindex ρ → (anchors, hub, internals)
  rw [← Equiv.sum_comp (assignEquiv k armLen).symm]
  simp only [assignEquiv_symm_inl, assignEquiv_symm_hub, assignEquiv_symm_inr,
    Fintype.sum_prod_type]
  -- Step 3: collapse the internal sum on each arm via armChain_sum_eq_armSum
  have hcollapse : ∀ (a : Fin k → Fin T) (h : Fin T),
      (∑ I : (l : Fin k) → Fin (armLen l) → Fin T,
        W h * ∏ l : Fin k, (W (a l) * B v (a l) *
          ((∏ j, W (I l j)) *
            ∏ s : Fin (armLen l + 1),
              B (chainPath (armLen l) (a l) h (fun j => I l j) ↑s)
                (chainPath (armLen l) (a l) h (fun j => I l j) ((s : ℕ) + 1)))))
      = W h * ∏ l : Fin k, (W (a l) * B v (a l) * armSum B W (armLen l) (a l) h) := by
    intro a h
    rw [← Finset.mul_sum]
    congr 1
    rw [show (∏ l : Fin k, (W (a l) * B v (a l) * armSum B W (armLen l) (a l) h))
          = ∏ l : Fin k, ∑ Il : Fin (armLen l) → Fin T,
              (W (a l) * B v (a l) *
                ((∏ j, W (Il j)) *
                  ∏ s : Fin (armLen l + 1),
                    B (chainPath (armLen l) (a l) h Il ↑s)
                      (chainPath (armLen l) (a l) h Il ((s : ℕ) + 1)))) from
        Finset.prod_congr rfl fun l _ => by
          rw [← armChain_sum_eq_armSum B W (armLen l) (a l) h, Finset.mul_sum]]
    rw [Finset.prod_univ_sum]
    exact Finset.sum_congr Fintype.piFinset_univ.symm fun I _ => rfl
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun h _ => hcollapse a h,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun hub _ => ?_
  rw [Finset.mul_sum]

/-! #### Commit 3 — wMulti collapse + polarization bridge -/

/-- **3.1 — `k2kArms` evaluation in `wMulti` form**: the rooted profile is the
weighted `k`-linear form of the root-row walk kernels `M^{armLen l + 1}(B v)`. -/
theorem k2kArms_eval (k : ℕ) (armLen : Fin k → ℕ) (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (v : Fin T) :
    rootedProfile B W v (k2kArms k armLen)
      = wMulti k W (fun l => weightedAdjIter B W (armLen l + 1) (fun t => B v t)) := by
  rw [k2kArms_eval_expanded k armLen B hB W v]
  unfold wMulti
  refine Finset.sum_congr rfl fun hub _ => ?_
  congr 1
  rw [Finset.prod_congr rfl (fun l (_ : l ∈ Finset.univ) =>
        (sum_weight_mul_armSum B hB W (armLen l) (fun t => B v t) hub).symm),
    Finset.prod_univ_sum]
  exact Finset.sum_congr Fintype.piFinset_univ.symm fun anchors _ => rfl

/-- **Multilinear product polarization** (per-slot generalization of
`pow_sub_pow_expand`): `2^k (∏ a − ∏ b)` is `2 ·` the odd-subset sum of the
slot products with `a−b` inside the subset and `a+b` outside. -/
theorem prod_sub_prod_polarization (k : ℕ) (a b : Fin k → ℝ) :
    2 ^ k * ((∏ l, a l) - ∏ l, b l) =
      2 * ∑ S ∈ Finset.univ.powerset.filter (fun S : Finset (Fin k) => Odd S.card),
        ∏ l : Fin k, (if l ∈ S then a l - b l else a l + b l) := by
  classical
  have hneg : ∀ S : Finset (Fin k),
      (∏ l ∈ S, -(a l - b l)) = (-1 : ℝ) ^ S.card * ∏ l ∈ S, (a l - b l) := by
    intro S
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun l _ => (neg_one_mul _).symm
  have h1 : (2 : ℝ) ^ k * ∏ l, a l =
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        (∏ l ∈ S, (a l - b l)) * ∏ l ∈ Finset.univ \ S, (a l + b l) := by
    rw [← Finset.prod_add,
      Finset.prod_congr rfl (fun l _ => show (a l - b l) + (a l + b l) = 2 * a l by ring),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h2 : (2 : ℝ) ^ k * ∏ l, b l =
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        (∏ l ∈ S, -(a l - b l)) * ∏ l ∈ Finset.univ \ S, (a l + b l) := by
    rw [← Finset.prod_add,
      Finset.prod_congr rfl (fun l _ => show -(a l - b l) + (a l + b l) = 2 * b l by ring),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [mul_sub, h1, h2, ← Finset.sum_sub_distrib,
    ← Finset.sum_filter_add_sum_filter_not
      ((Finset.univ : Finset (Fin k)).powerset) (fun S => Odd S.card)]
  have heven : (∑ S ∈ ((Finset.univ : Finset (Fin k)).powerset).filter
      (fun S => ¬Odd S.card),
        ((∏ l ∈ S, (a l - b l)) * (∏ l ∈ Finset.univ \ S, (a l + b l)) -
          (∏ l ∈ S, -(a l - b l)) * ∏ l ∈ Finset.univ \ S, (a l + b l))) = 0 :=
    Finset.sum_eq_zero fun S hS => by
      have he : Even S.card := Nat.not_odd_iff_even.mp (Finset.mem_filter.mp hS).2
      rw [hneg S, he.neg_one_pow, one_mul, sub_self]
  rw [heven, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  have ho : Odd S.card := (Finset.mem_filter.mp hS).2
  have hsplit : (∏ l : Fin k, (if l ∈ S then a l - b l else a l + b l)) =
      (∏ l ∈ S, (a l - b l)) * ∏ l ∈ Finset.univ \ S, (a l + b l) := by
    rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
      ← Finset.sdiff_eq_filter]
  rw [hsplit, hneg S, ho.neg_one_pow]
  ring

/-- **3.2 — the graph bridge**: `2 ·` the polarized `k`-th power observable at
arm lengths `armLen l + 1` equals `2^k ·` the rooted `K₂,ₖ`-arms profile
difference (the k-ary generalization of `rootedProfile_k23Arms_sub_eq_polarizedCubeObs`;
at `k = 3`, `2^3 = 8 = 2·4`). -/
theorem rootedProfile_k2kArms_sub_eq_polarizedPowObs (k : ℕ) (armLen : Fin k → ℕ)
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (i j : Fin T) :
    2 * polarizedPowObs k B W i j (fun l => armLen l + 1)
      = 2 ^ k * (rootedProfile B W i (k2kArms k armLen)
          - rootedProfile B W j (k2kArms k armLen)) := by
  classical
  rw [k2kArms_eval k armLen B hB W i, k2kArms_eval k armLen B hB W j]
  unfold polarizedPowObs wMulti
  have hpt : ∀ (S : Finset (Fin k)) (l : Fin k) (t : Fin T),
      weightedAdjIter B W (armLen l + 1)
          (if l ∈ S then rowDiff B i j else rowSum B i j) t
      = if l ∈ S
        then weightedAdjIter B W (armLen l + 1) (fun s => B i s) t
              - weightedAdjIter B W (armLen l + 1) (fun s => B j s) t
        else weightedAdjIter B W (armLen l + 1) (fun s => B i s) t
              + weightedAdjIter B W (armLen l + 1) (fun s => B j s) t := by
    intro S l t
    by_cases hl : l ∈ S
    · simp only [if_pos hl]
      rw [show rowDiff B i j = fun s => B i s - B j s from rfl,
        weightedAdjIter_sub B W (armLen l + 1) (fun s => B i s) (fun s => B j s)]
    · simp only [if_neg hl]
      rw [show rowSum B i j = fun s => B i s + B j s from rfl,
        weightedAdjIter_add B W (armLen l + 1) (fun s => B i s) (fun s => B j s)]
  simp only [hpt]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.mul_sum, mul_left_comm (2 : ℝ) (W t),
    ← prod_sub_prod_polarization k
      (fun l => weightedAdjIter B W (armLen l + 1) (fun s => B i s) t)
      (fun l => weightedAdjIter B W (armLen l + 1) (fun s => B j s) t)]
  ring

/-- **Weighted power sums descend** — now PROVED for ALL `k` (k ≤ 2 directly,
k = 3 via `cubeMoment_descends_of_rootedProfileEquiv`, k ≥ 4 via the
`K₂,ₖ`-arms bridge `rootedProfile_k2kArms_sub_eq_polarizedPowObs` feeding
`powGap_eq_zero_of_polarized_obs`).

`weighted_powersum_determines_measure` upgrades this to equality of the
`W`-weighted row-value measures, the key step toward the rank theorem
`vertexOrbitRel_of_rootedProfileEquiv`. -/
theorem powerSum_descends_of_rootedProfileEquiv {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ t, 0 < W t)
    {i j : Fin T} (h : rootedProfileEquiv B W i j) :
    ∀ k : ℕ, ∑ t : Fin T, W t * B i t ^ k = ∑ t : Fin T, W t * B j t ^ k := by
  intro k
  match k with
  | 0 => simp
  | 1 =>
    have h1 := first_moment_descends_of_rootedProfileEquiv B hB W h
      (g := fun _ => (1 : ℝ)) (fun _ _ _ => rfl)
    simpa using h1
  | 2 =>
    have h2 := sqMoment_descends_of_rootedProfileEquiv B hB W hW h
    simpa [sqMoment] using h2
  | 3 => exact cubeMoment_descends_of_rootedProfileEquiv B hB W hW h
  | (k + 4) =>
    refine powGap_eq_zero_of_polarized_obs (k + 4) B hB W hW i j fun φ => ?_
    have hbridge := rootedProfile_k2kArms_sub_eq_polarizedPowObs (k + 4) φ B hB W i j
    rw [h (k2kRestCard (k + 4) φ) (k2kArms (k + 4) φ), sub_self, mul_zero] at hbridge
    linarith [hbridge]

/-- **Row-value measures descend** (now unconditional): under rooted-profile
equivalence, the `W`-weighted preimage masses of the two rows agree at every
value — the rows are equal as weighted value measures. -/
theorem rowValueMeasure_eq_of_rootedProfileEquiv {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ t, 0 < W t)
    {i j : Fin T} (h : rootedProfileEquiv B W i j) (a : ℝ) :
    (∑ t ∈ Finset.univ.filter (fun t => B i t = a), W t) =
      ∑ t ∈ Finset.univ.filter (fun t => B j t = a), W t :=
  weighted_powersum_determines_measure (B i) (B j) W
    (powerSum_descends_of_rootedProfileEquiv B hB W hW h) a

/-! ### Single-vertex decoration — the gluing primitive for the weight-mod crux

`decorateAt F H u` glues `H` onto vertex `u` of `F` (identifying `H`'s root with
`u`). Its rooted profile factorizes: the `H`-block contributes
`rootedProfile B W (value at u) H` to each `F`-assignment. Decorating EVERY
unlabeled vertex by `H` then realizes the modified weight `W · (profile of H)`,
which is the engine of `rootedProfileEquiv_weightMod`. -/

/-- Embedding of `H`'s vertices into `Fin (n+1) ⊕ Fin m`: the root `0 ↦ inl u`
(identified with vertex `u` of `F`), and `Fin.succ k ↦ inr k`. -/
def hDecorEmb {n m : ℕ} (u : Fin (n + 1)) : Fin (m + 1) ↪ Fin (n + 1) ⊕ Fin m where
  toFun := Fin.cons (Sum.inl u) (fun k => Sum.inr k)
  inj' a b hab := by
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨k, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨l, rfl⟩ <;>
      simp_all [Fin.cons_zero, Fin.cons_succ]

/-- The structured single-vertex decoration on `Fin (n+1) ⊕ Fin m`: `F` on the
`inl` block, `⊔` `H` glued with its root at `u` (via `hDecorEmb`). -/
def decorateAtSum {n m : ℕ} (F : SimpleGraph (Fin (n + 1)))
    (H : SimpleGraph (Fin (m + 1))) (u : Fin (n + 1)) :
    SimpleGraph (Fin (n + 1) ⊕ Fin m) :=
  SimpleGraph.map Function.Embedding.inl F ⊔ SimpleGraph.map (hDecorEmb u) H

/-- `Fin (n+1) ⊕ Fin m ≃ Fin (n+m+1)` with the `F`-root `inl 0 ↦ 0` (so the
decorated graph's root is `F`'s root). -/
noncomputable def decorVertexEquiv (n m : ℕ) :
    (Fin (n + 1) ⊕ Fin m) ≃ Fin (n + m + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

@[simp] theorem decorVertexEquiv_inl_zero (n m : ℕ) :
    decorVertexEquiv n m (Sum.inl 0) = 0 :=
  Fin.ext (by simp [decorVertexEquiv, finSumFinEquiv])

/-- **Single-vertex decoration** as a `SimpleGraph (Fin (n+m+1))` (transported
from the structured form), consumable by `rootedProfile`. -/
noncomputable def decorateAt {n m : ℕ} (F : SimpleGraph (Fin (n + 1)))
    (H : SimpleGraph (Fin (m + 1))) (u : Fin (n + 1)) :
    SimpleGraph (Fin (n + m + 1)) :=
  (decorateAtSum F H u).comap (decorVertexEquiv n m).symm

instance {n m : ℕ} (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj]
    (H : SimpleGraph (Fin (m + 1))) [DecidableRel H.Adj] (u : Fin (n + 1)) :
    DecidableRel (decorateAtSum F H u).Adj := by unfold decorateAtSum; infer_instance

noncomputable instance {n m : ℕ} (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj]
    (H : SimpleGraph (Fin (m + 1))) [DecidableRel H.Adj] (u : Fin (n + 1)) :
    DecidableRel (decorateAt F H u).Adj :=
  SimpleGraph.instDecidableComapAdj _ _

/-- The `F`-block and `H`-block edge sets of `decorateAtSum` are disjoint: an
`H`-edge has at most one `Sum.inl` endpoint (only its root maps there), while an
`F`-edge has two — so a shared edge would force a self-loop in `H`. -/
theorem decorateAtSum_edge_disjoint {n m : ℕ} (F : SimpleGraph (Fin (n + 1)))
    [DecidableRel F.Adj] (H : SimpleGraph (Fin (m + 1))) [DecidableRel H.Adj]
    (u : Fin (n + 1)) :
    Disjoint (SimpleGraph.map Function.Embedding.inl F).edgeFinset
      (SimpleGraph.map (hDecorEmb u) H).edgeFinset := by
  rw [Finset.disjoint_left]
  intro E hF hH
  rw [SimpleGraph.mem_edgeFinset] at hF hH
  induction E using Sym2.ind with
  | _ x y =>
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.map_adj] at hF hH
    obtain ⟨a, b, _, ha, hb⟩ := hF
    obtain ⟨a', b', hadj', ha', hb'⟩ := hH
    have ha0 : a' = 0 := by
      rcases Fin.eq_zero_or_eq_succ a' with rfl | ⟨k, rfl⟩
      · rfl
      · exfalso
        have hk : (hDecorEmb u) (Fin.succ k) = Sum.inr k := by simp [hDecorEmb]
        rw [hk] at ha'; rw [← ha] at ha'; exact absurd ha' (by simp)
    have hb0 : b' = 0 := by
      rcases Fin.eq_zero_or_eq_succ b' with rfl | ⟨k, rfl⟩
      · rfl
      · exfalso
        have hk : (hDecorEmb u) (Fin.succ k) = Sum.inr k := by simp [hDecorEmb]
        rw [hk] at hb'; rw [← hb] at hb'; exact absurd hb' (by simp)
    subst ha0 hb0
    exact H.loopless 0 hadj'

/-- **Edge-product transport + split** (Commit 1 steps 1–2): the `rootedProfile`
edge product over `decorateAt F H u` factors, through `decorVertexEquiv`, into the
`F`-edge product and the `H`-edge product. -/
theorem decorateAt_prod_eq {T n m : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj]
    (H : SimpleGraph (Fin (m + 1))) [DecidableRel H.Adj] (u : Fin (n + 1))
    (τ : Fin (n + m + 1) → Fin T) :
    (∏ E ∈ (decorateAt F H u).edgeFinset, B (τ (Quot.out E).1) (τ (Quot.out E).2)) =
      (∏ e ∈ F.edgeFinset,
        B (τ (decorVertexEquiv n m (Sum.inl (Quot.out e).1)))
          (τ (decorVertexEquiv n m (Sum.inl (Quot.out e).2)))) *
      (∏ e ∈ H.edgeFinset,
        B (τ (decorVertexEquiv n m (hDecorEmb u (Quot.out e).1)))
          (τ (decorVertexEquiv n m (hDecorEmb u (Quot.out e).2)))) := by
  classical
  have step1 : (∏ E ∈ (decorateAt F H u).edgeFinset, B (τ (Quot.out E).1) (τ (Quot.out E).2)) =
      ∏ E ∈ (decorateAtSum F H u).edgeFinset,
        B (τ (decorVertexEquiv n m (Quot.out E).1))
          (τ (decorVertexEquiv n m (Quot.out E).2)) := by
    unfold decorateAt
    rw [comap_symm_edgeFinset, Finset.prod_map]
    refine Finset.prod_congr rfl fun E _ => ?_
    induction E using Sym2.ind with
    | _ a b =>
      rw [show (decorVertexEquiv n m).toEmbedding.sym2Map s(a, b)
          = s(decorVertexEquiv n m a, decorVertexEquiv n m b) from rfl,
        out_pair_eq' B hB τ _ _,
        out_pair_eq' B hB (fun s => τ (decorVertexEquiv n m s)) a b]
  rw [step1]
  have keySup : (decorateAtSum F H u).edgeFinset =
      (SimpleGraph.map Function.Embedding.inl F).edgeFinset ∪
        (SimpleGraph.map (hDecorEmb u) H).edgeFinset := by
    apply Finset.coe_injective
    rw [SimpleGraph.coe_edgeFinset, Finset.coe_union, SimpleGraph.coe_edgeFinset,
      SimpleGraph.coe_edgeFinset]
    show (decorateAtSum F H u).edgeSet = _
    unfold decorateAtSum
    rw [SimpleGraph.edgeSet_sup]
  rw [keySup, Finset.prod_union (decorateAtSum_edge_disjoint F H u)]
  congr 1
  · have key : (SimpleGraph.map Function.Embedding.inl F).edgeFinset
        = Finset.map (Function.Embedding.inl (β := Fin m)).sym2Map F.edgeFinset := by
      apply Finset.coe_injective
      rw [SimpleGraph.coe_edgeFinset, Finset.coe_map, SimpleGraph.coe_edgeFinset,
        SimpleGraph.edgeSet_map]
    rw [key, Finset.prod_map]
    refine Finset.prod_congr rfl fun e _ => ?_
    induction e using Sym2.ind with
    | _ a b =>
      rw [show (Function.Embedding.inl (β := Fin m)).sym2Map s(a, b)
          = s((Sum.inl a : Fin (n + 1) ⊕ Fin m), Sum.inl b) from rfl,
        out_pair_eq' B hB (fun s => τ (decorVertexEquiv n m s)) _ _,
        out_pair_eq' B hB (fun s => τ (decorVertexEquiv n m (Sum.inl s))) a b]
  · have key : (SimpleGraph.map (hDecorEmb u) H).edgeFinset
        = Finset.map (hDecorEmb u).sym2Map H.edgeFinset := by
      apply Finset.coe_injective
      rw [SimpleGraph.coe_edgeFinset, Finset.coe_map, SimpleGraph.coe_edgeFinset,
        SimpleGraph.edgeSet_map]
    rw [key, Finset.prod_map]
    refine Finset.prod_congr rfl fun e _ => ?_
    induction e using Sym2.ind with
    | _ a b =>
      rw [show (hDecorEmb u).sym2Map s(a, b) = s(hDecorEmb u a, hDecorEmb u b) from rfl,
        out_pair_eq' B hB (fun s => τ (decorVertexEquiv n m s)) _ _,
        out_pair_eq' B hB (fun s => τ (decorVertexEquiv n m (hDecorEmb u s))) a b]

/-- `rootedProfile` in `Fin.cons` form (re-derived here; the `SimpleRank` version
is private). -/
theorem rootedProfile_cons {T n : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (v : Fin T) (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj] :
    rootedProfile B W v F =
      ∑ σ : Fin n → Fin T, (∏ w : Fin n, W (σ w)) *
        ∏ e ∈ F.edgeFinset,
          B (Fin.cons (α := fun _ => Fin T) v σ (Quot.out e).1)
            (Fin.cons (α := fun _ => Fin T) v σ (Quot.out e).2) := by
  unfold rootedProfile simpleEvalAt
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hτ : ∀ w : Fin (n + 1),
      (if h : (w : ℕ) < 1 then (fun _ : Fin 1 => v) ⟨w.val, h⟩
       else σ ⟨w.val - 1, by have := w.isLt; omega⟩) =
        Fin.cons (α := fun _ => Fin T) v σ w := by
    intro w
    rcases Fin.eq_zero_or_eq_succ w with rfl | ⟨x, rfl⟩
    · rw [dif_pos (by norm_num)]; simp
    · rw [dif_neg (by simp), Fin.cons_succ]; congr 1
  simp only [hτ]

theorem decorVertexEquiv_inl_val (n m : ℕ) (x : Fin (n + 1)) :
    ((decorVertexEquiv n m (Sum.inl x)) : ℕ) = (x : ℕ) := by
  simp [decorVertexEquiv, finSumFinEquiv]

theorem decorVertexEquiv_inr_val (n m : ℕ) (z : Fin m) :
    ((decorVertexEquiv n m (Sum.inr z)) : ℕ) = n + 1 + (z : ℕ) := by
  simp [decorVertexEquiv, finSumFinEquiv]

/-- **F-side assignment value lemma**: under the block assignment `appendFn σF σH`,
the value at an `F`-vertex `inl x` is `Fin.cons v σF x`. -/
theorem consAppend_inl {T n m : ℕ} (v : Fin T) (σF : Fin n → Fin T) (σH : Fin m → Fin T)
    (x : Fin (n + 1)) :
    Fin.cons (α := fun _ => Fin T) v (appendFn σF σH) (decorVertexEquiv n m (Sum.inl x)) =
      Fin.cons (α := fun _ => Fin T) v σF x := by
  rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨w, rfl⟩
  · rw [show decorVertexEquiv n m (Sum.inl (0 : Fin (n + 1))) = 0 from
      Fin.ext (by rw [decorVertexEquiv_inl_val]; rfl)]; simp
  · rw [show decorVertexEquiv n m (Sum.inl (Fin.succ w)) = Fin.succ ⟨w, by omega⟩ from
      Fin.ext (by rw [decorVertexEquiv_inl_val]; rfl),
      Fin.cons_succ, Fin.cons_succ, appendFn_low σF σH (by simp)]

/-- **H-side assignment value lemma**: under `appendFn σF σH`, the value at an
`H`-vertex `hDecorEmb u a` is `Fin.cons (Fin.cons v σF u) σH a` — i.e. `H` rooted
at the value vertex `u` receives. -/
theorem consAppend_hDecorEmb {T n m : ℕ} (v : Fin T) (σF : Fin n → Fin T)
    (σH : Fin m → Fin T) (u : Fin (n + 1)) (a : Fin (m + 1)) :
    Fin.cons (α := fun _ => Fin T) v (appendFn σF σH)
        (decorVertexEquiv n m (hDecorEmb u a)) =
      Fin.cons (α := fun _ => Fin T) (Fin.cons (α := fun _ => Fin T) v σF u) σH a := by
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨z, rfl⟩
  · show Fin.cons (α := fun _ => Fin T) v (appendFn σF σH)
        (decorVertexEquiv n m (Sum.inl u)) = _
    rw [consAppend_inl]; simp
  · rw [show (hDecorEmb u) (Fin.succ z) = Sum.inr z from by simp [hDecorEmb],
      show decorVertexEquiv n m (Sum.inr z) = Fin.succ ⟨n + (z : ℕ), by omega⟩ from
        Fin.ext (by rw [decorVertexEquiv_inr_val]; simp; omega),
      Fin.cons_succ, Fin.cons_succ, appendFn_high σF σH (by simp)]
    exact congrArg σH (Fin.ext (by simp))

/-- **Single-vertex decoration factorization** (Commit 1 target — PROVED):
gluing `H` at vertex `u` multiplies each `F`-assignment's contribution by the
`H`-profile rooted at the value `u` receives. Analogue of `rootedProfile_rootAttach`,
but the attachment point is an arbitrary unlabeled vertex, not a fresh pendant root.

Proof plan: transport the edge product to `decorateAtSum` (`comap` along
`decorVertexEquiv`, as in `k2kArms_prod_eq_structured`); the structured edge set
is the disjoint union `(F.map inl).edgeFinset ∪ (H.map (hDecorEmb u)).edgeFinset`,
so the product splits into the `F`-edge product and the `H`-edge product; reindex
the assignment sum over `Fin (n+m) → Fin T` into `(Fin n → Fin T) × (Fin m → Fin T)`;
the `H`-factor, with its root pinned to the value at `u`, sums to
`rootedProfile B W (Fin.cons v σ u) H`. -/
theorem rootedProfile_decorate_vertex {T n m : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (v : Fin T)
    (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj]
    (H : SimpleGraph (Fin (m + 1))) [DecidableRel H.Adj] (u : Fin (n + 1)) :
    rootedProfile B W v (decorateAt F H u) =
      ∑ σ : Fin n → Fin T, (∏ w : Fin n, W (σ w)) *
        (∏ e ∈ F.edgeFinset,
          B (Fin.cons (α := fun _ => Fin T) v σ (Quot.out e).1)
            (Fin.cons (α := fun _ => Fin T) v σ (Quot.out e).2)) *
        rootedProfile B W (Fin.cons (α := fun _ => Fin T) v σ u) H := by
  classical
  rw [rootedProfile_cons]
  rw [Finset.sum_congr rfl fun σ (_ : σ ∈ Finset.univ) => by
    rw [decorateAt_prod_eq B hB F H u (Fin.cons (α := fun _ => Fin T) v σ)]]
  rw [sum_fin_split n m]
  refine Finset.sum_congr rfl fun σF _ => ?_
  rw [rootedProfile_cons, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σH _ => ?_
  rw [prod_appendFn W σF σH]
  simp only [consAppend_inl, consAppend_hDecorEmb]
  ring

/-! ### All-vertex decoration (Route B) — glue a copy of `H` at EVERY unlabeled
vertex of `F`. One fixed structured vertex type `Fin(n+1) ⊕ (Fin n × Fin m)`:
`inl 0` = `F`-root, `inl (succ w)` = unlabeled vertex `w`, `inr (w, z)` = the
`z`-th internal vertex of the `H`-copy glued at `w`. Decorating all vertices
realizes the modified weight `W · (profile of H)`, the engine of
`rootedProfileEquiv_weightMod`. -/

/-- Embedding of the `w`-th `H`-copy: root `0 ↦ inl (succ w)`, `succ z ↦ inr (w, z)`. -/
def embedHCopy {n m : ℕ} (w : Fin n) :
    Fin (m + 1) ↪ Fin (n + 1) ⊕ (Fin n × Fin m) where
  toFun := Fin.cons (Sum.inl w.succ) (fun z => Sum.inr (w, z))
  inj' a b hab := by
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨k, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨l, rfl⟩ <;>
      simp_all [Fin.cons_zero, Fin.cons_succ]

/-- The structured all-vertex decoration: `F` on the `inl` block, joined with one
`H`-copy per unlabeled vertex (via `Finset.sup`, not `iSup`, to keep decidability
and edge-finset instances controllable). -/
def decorateAllSum {n m : ℕ} (F : SimpleGraph (Fin (n + 1)))
    (H : SimpleGraph (Fin (m + 1))) : SimpleGraph (Fin (n + 1) ⊕ (Fin n × Fin m)) :=
  SimpleGraph.map Function.Embedding.inl F ⊔
    Finset.univ.sup (fun w : Fin n => SimpleGraph.map (embedHCopy w) H)

/-- `Fin (n+1) ⊕ (Fin n × Fin m) ≃ Fin (n + n*m + 1)` with `inl 0 ↦ 0`. -/
noncomputable def decorAllVertexEquiv (n m : ℕ) :
    (Fin (n + 1) ⊕ (Fin n × Fin m)) ≃ Fin (n + n * m + 1) :=
  (Equiv.sumCongr (Equiv.refl (Fin (n + 1))) finProdFinEquiv).trans
    (finSumFinEquiv.trans (finCongr (by omega)))

@[simp] theorem decorAllVertexEquiv_inl_zero (n m : ℕ) :
    decorAllVertexEquiv n m (Sum.inl 0) = 0 :=
  Fin.ext (by simp [decorAllVertexEquiv, finSumFinEquiv])

theorem decorAllVertexEquiv_inl_val (n m : ℕ) (x : Fin (n + 1)) :
    ((decorAllVertexEquiv n m (Sum.inl x)) : ℕ) = (x : ℕ) := by
  simp [decorAllVertexEquiv, finSumFinEquiv]

/-- **All-vertex decoration** as a `SimpleGraph (Fin (n+n*m+1))`. -/
noncomputable def decorateAll {n m : ℕ} (F : SimpleGraph (Fin (n + 1)))
    (H : SimpleGraph (Fin (m + 1))) : SimpleGraph (Fin (n + n * m + 1)) :=
  (decorateAllSum F H).comap (decorAllVertexEquiv n m).symm

/-- `Finset.sup`-adjacency over `Fin n` is the existential of the per-`w` adjacencies. -/
theorem decorateAllSum_sup_adj {n m : ℕ} (H : SimpleGraph (Fin (m + 1)))
    (x y : Fin (n + 1) ⊕ (Fin n × Fin m)) :
    (Finset.univ.sup (fun w : Fin n => SimpleGraph.map (embedHCopy w) H)).Adj x y ↔
      ∃ w : Fin n, (SimpleGraph.map (embedHCopy w) H).Adj x y := by
  simp [Finset.sup_eq_iSup, SimpleGraph.iSup_adj]

instance {n m : ℕ} (H : SimpleGraph (Fin (m + 1))) [DecidableRel H.Adj] :
    DecidableRel (Finset.univ.sup (fun w : Fin n => SimpleGraph.map (embedHCopy w) H)).Adj :=
  fun x y => decidable_of_iff _ (decorateAllSum_sup_adj H x y).symm

instance {n m : ℕ} (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj]
    (H : SimpleGraph (Fin (m + 1))) [DecidableRel H.Adj] :
    DecidableRel (decorateAllSum F H).Adj := by
  intro x y
  unfold decorateAllSum
  rw [SimpleGraph.sup_adj, decorateAllSum_sup_adj]
  infer_instance

noncomputable instance {n m : ℕ} (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj]
    (H : SimpleGraph (Fin (m + 1))) [DecidableRel H.Adj] :
    DecidableRel (decorateAll F H).Adj :=
  SimpleGraph.instDecidableComapAdj _ _

/-- The `w`-th and `w'`-th `H`-copies have disjoint vertex images for `w ≠ w'`. -/
theorem embedHCopy_apply_ne {n m : ℕ} {w w' : Fin n} (hww : w ≠ w')
    (a a' : Fin (m + 1)) : (embedHCopy w) a ≠ (embedHCopy w') a' := by
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨k, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ a' with rfl | ⟨l, rfl⟩
  · simp only [embedHCopy, Function.Embedding.coeFn_mk, Fin.cons_zero, ne_eq, Sum.inl.injEq]
    exact fun h => hww (Fin.succ_injective _ h)
  · simp [embedHCopy]
  · simp [embedHCopy]
  · simp only [embedHCopy, Function.Embedding.coeFn_mk, Fin.cons_succ, ne_eq, Sum.inr.injEq,
      Prod.mk.injEq]
    exact fun h => hww h.1

/-- Distinct `H`-copies have disjoint edge sets (disjoint vertex images). -/
theorem decorateAll_Hcopy_disjoint {n m : ℕ} (H : SimpleGraph (Fin (m + 1)))
    [DecidableRel H.Adj] {w w' : Fin n} (hww : w ≠ w') :
    Disjoint (SimpleGraph.map (embedHCopy w) H).edgeFinset
      (SimpleGraph.map (embedHCopy w') H).edgeFinset := by
  rw [Finset.disjoint_left]
  intro E hw hw'
  rw [SimpleGraph.mem_edgeFinset] at hw hw'
  induction E using Sym2.ind with
  | _ x y =>
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.map_adj] at hw hw'
    obtain ⟨a, b, _, ha, _⟩ := hw
    obtain ⟨a', b', _, ha', _⟩ := hw'
    exact embedHCopy_apply_ne hww a a' (ha.trans ha'.symm)

/-- The `F`-block is disjoint from every `H`-copy block: a sup-edge has at most
one `Sum.inl` endpoint, an `F`-edge has two. -/
theorem decorateAll_F_sup_disjoint {n m : ℕ} (F : SimpleGraph (Fin (n + 1)))
    [DecidableRel F.Adj] (H : SimpleGraph (Fin (m + 1))) [DecidableRel H.Adj] :
    Disjoint (SimpleGraph.map Function.Embedding.inl F).edgeFinset
      (Finset.univ.sup (fun w : Fin n => SimpleGraph.map (embedHCopy w) H)).edgeFinset := by
  rw [Finset.disjoint_left]
  intro E hF hS
  rw [SimpleGraph.mem_edgeFinset] at hF hS
  induction E using Sym2.ind with
  | _ x y =>
    rw [SimpleGraph.mem_edgeSet, decorateAllSum_sup_adj] at hS
    obtain ⟨w, hw⟩ := hS
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.map_adj] at hF
    rw [SimpleGraph.map_adj] at hw
    obtain ⟨a, b, _, ha, hb⟩ := hF
    obtain ⟨a', b', hadj', ha', hb'⟩ := hw
    have ha0 : a' = 0 := by
      rcases Fin.eq_zero_or_eq_succ a' with rfl | ⟨k, rfl⟩
      · rfl
      · exact absurd (ha'.trans ha.symm) (by simp [embedHCopy])
    have hb0 : b' = 0 := by
      rcases Fin.eq_zero_or_eq_succ b' with rfl | ⟨k, rfl⟩
      · rfl
      · exact absurd (hb'.trans hb.symm) (by simp [embedHCopy])
    subst ha0 hb0
    exact H.loopless 0 hadj'

/-- The `Finset.sup` of the `H`-copies has edge finset the disjoint union of the
per-copy edge finsets. -/
theorem decorateAllSum_sup_edgeFinset {n m : ℕ} (H : SimpleGraph (Fin (m + 1)))
    [DecidableRel H.Adj] :
    (Finset.univ.sup (fun w : Fin n => SimpleGraph.map (embedHCopy w) H)).edgeFinset =
      Finset.univ.biUnion (fun w => (SimpleGraph.map (embedHCopy w) H).edgeFinset) := by
  ext E
  induction E using Sym2.ind with
  | _ x y =>
    simp only [SimpleGraph.mem_edgeFinset, Finset.mem_biUnion, Finset.mem_univ, true_and,
      SimpleGraph.mem_edgeSet, decorateAllSum_sup_adj]

/-- **Edge-product transport + split** (B2): the `rootedProfile` edge product over
`decorateAll F H` factors, through `decorAllVertexEquiv`, into the `F`-edge product
times the product over the `n` `H`-copy edge products. -/
theorem decorateAll_prod_eq {T n m : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj]
    (H : SimpleGraph (Fin (m + 1))) [DecidableRel H.Adj]
    (τ : Fin (n + n * m + 1) → Fin T) :
    (∏ E ∈ (decorateAll F H).edgeFinset, B (τ (Quot.out E).1) (τ (Quot.out E).2)) =
      (∏ e ∈ F.edgeFinset,
        B (τ (decorAllVertexEquiv n m (Sum.inl (Quot.out e).1)))
          (τ (decorAllVertexEquiv n m (Sum.inl (Quot.out e).2)))) *
      ∏ w : Fin n, ∏ e ∈ H.edgeFinset,
        B (τ (decorAllVertexEquiv n m (embedHCopy w (Quot.out e).1)))
          (τ (decorAllVertexEquiv n m (embedHCopy w (Quot.out e).2))) := by
  classical
  have step1 : (∏ E ∈ (decorateAll F H).edgeFinset, B (τ (Quot.out E).1) (τ (Quot.out E).2)) =
      ∏ E ∈ (decorateAllSum F H).edgeFinset,
        B (τ (decorAllVertexEquiv n m (Quot.out E).1))
          (τ (decorAllVertexEquiv n m (Quot.out E).2)) := by
    unfold decorateAll
    rw [comap_symm_edgeFinset, Finset.prod_map]
    refine Finset.prod_congr rfl fun E _ => ?_
    induction E using Sym2.ind with
    | _ a b =>
      rw [show (decorAllVertexEquiv n m).toEmbedding.sym2Map s(a, b)
          = s(decorAllVertexEquiv n m a, decorAllVertexEquiv n m b) from rfl,
        out_pair_eq' B hB τ _ _,
        out_pair_eq' B hB (fun s => τ (decorAllVertexEquiv n m s)) a b]
  rw [step1]
  have keySup : (decorateAllSum F H).edgeFinset =
      (SimpleGraph.map Function.Embedding.inl F).edgeFinset ∪
        (Finset.univ.sup (fun w : Fin n => SimpleGraph.map (embedHCopy w) H)).edgeFinset := by
    apply Finset.coe_injective
    rw [SimpleGraph.coe_edgeFinset, Finset.coe_union, SimpleGraph.coe_edgeFinset,
      SimpleGraph.coe_edgeFinset]
    show (decorateAllSum F H).edgeSet = _
    unfold decorateAllSum
    rw [SimpleGraph.edgeSet_sup]
  rw [keySup, Finset.prod_union (decorateAll_F_sup_disjoint F H)]
  congr 1
  · have key : (SimpleGraph.map Function.Embedding.inl F).edgeFinset =
        Finset.map (Function.Embedding.inl (β := Fin n × Fin m)).sym2Map F.edgeFinset := by
      apply Finset.coe_injective
      rw [SimpleGraph.coe_edgeFinset, Finset.coe_map, SimpleGraph.coe_edgeFinset,
        SimpleGraph.edgeSet_map]
    rw [key, Finset.prod_map]
    refine Finset.prod_congr rfl fun e _ => ?_
    induction e using Sym2.ind with
    | _ a b =>
      rw [show (Function.Embedding.inl (β := Fin n × Fin m)).sym2Map s(a, b)
          = s((Sum.inl a : Fin (n + 1) ⊕ (Fin n × Fin m)), Sum.inl b) from rfl,
        out_pair_eq' B hB (fun s => τ (decorAllVertexEquiv n m s)) _ _,
        out_pair_eq' B hB (fun s => τ (decorAllVertexEquiv n m (Sum.inl s))) a b]
  · rw [decorateAllSum_sup_edgeFinset,
      Finset.prod_biUnion (fun w _ w' _ hww => decorateAll_Hcopy_disjoint H hww)]
    refine Finset.prod_congr rfl fun w _ => ?_
    have key : (SimpleGraph.map (embedHCopy w) H).edgeFinset =
        Finset.map (embedHCopy w).sym2Map H.edgeFinset := by
      apply Finset.coe_injective
      rw [SimpleGraph.coe_edgeFinset, Finset.coe_map, SimpleGraph.coe_edgeFinset,
        SimpleGraph.edgeSet_map]
    rw [key, Finset.prod_map]
    refine Finset.prod_congr rfl fun e _ => ?_
    induction e using Sym2.ind with
    | _ a b =>
      rw [show (embedHCopy w).sym2Map s(a, b) = s(embedHCopy w a, embedHCopy w b) from rfl,
        out_pair_eq' B hB (fun s => τ (decorAllVertexEquiv n m s)) _ _,
        out_pair_eq' B hB (fun s => τ (decorAllVertexEquiv n m (embedHCopy w s))) a b]

theorem decorAllVertexEquiv_inr_val (n m : ℕ) (w : Fin n) (z : Fin m) :
    ((decorAllVertexEquiv n m (Sum.inr (w, z))) : ℕ)
      = (n + 1) + (finProdFinEquiv (w, z) : ℕ) := by
  simp [decorAllVertexEquiv, finSumFinEquiv]

/-- **B3 F-side value lemma**: under `appendFn σF σHflat`, the value at an
`F`-vertex `inl x` is `Fin.cons v σF x`. -/
theorem consAppendAll_inl {T n m : ℕ} (v : Fin T) (σF : Fin n → Fin T)
    (σHflat : Fin (n * m) → Fin T) (x : Fin (n + 1)) :
    Fin.cons (α := fun _ => Fin T) v (appendFn σF σHflat)
        (decorAllVertexEquiv n m (Sum.inl x)) = Fin.cons (α := fun _ => Fin T) v σF x := by
  rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨w, rfl⟩
  · rw [show decorAllVertexEquiv n m (Sum.inl (0 : Fin (n + 1))) = 0 from
      Fin.ext (by rw [decorAllVertexEquiv_inl_val]; rfl)]; simp
  · rw [show decorAllVertexEquiv n m (Sum.inl (Fin.succ w)) = Fin.succ ⟨w, by omega⟩ from
      Fin.ext (by rw [decorAllVertexEquiv_inl_val]; rfl),
      Fin.cons_succ, Fin.cons_succ, appendFn_low σF σHflat (by simp)]

/-- **B3 H-side value lemma**: under `appendFn σF σHflat`, the `w`-th `H`-copy's
assignment is `Fin.cons (Fin.cons v σF w.succ) (fun z => σHflat (finProdFinEquiv (w,z)))`
— i.e. the `w`-th copy rooted at the value `F`-vertex `w` receives. -/
theorem consAppendAll_embedHCopy {T n m : ℕ} (v : Fin T) (σF : Fin n → Fin T)
    (σHflat : Fin (n * m) → Fin T) (w : Fin n) (a : Fin (m + 1)) :
    Fin.cons (α := fun _ => Fin T) v (appendFn σF σHflat)
        (decorAllVertexEquiv n m (embedHCopy w a)) =
      Fin.cons (α := fun _ => Fin T) (Fin.cons (α := fun _ => Fin T) v σF w.succ)
        (fun z => σHflat (finProdFinEquiv (w, z))) a := by
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨z, rfl⟩
  · show Fin.cons (α := fun _ => Fin T) v (appendFn σF σHflat)
        (decorAllVertexEquiv n m (Sum.inl w.succ)) = _
    rw [consAppendAll_inl]; simp
  · rw [show (embedHCopy w) (Fin.succ z) = Sum.inr (w, z) from by simp [embedHCopy],
      show decorAllVertexEquiv n m (Sum.inr (w, z))
          = Fin.succ ⟨n + (finProdFinEquiv (w, z) : ℕ), by
            have := (finProdFinEquiv (w, z)).isLt; omega⟩ from
        Fin.ext (by rw [decorAllVertexEquiv_inr_val]; simp; omega),
      Fin.cons_succ, Fin.cons_succ,
      appendFn_high σF σHflat (by simp)]
    exact congrArg σHflat (Fin.ext (by simp))

/-- **Flat ↔ curried assignment equivalence**: a flat assignment over the `n*m`
internal `H`-copy vertices is the same as `n` separate `H`-copy assignments,
matched via `finProdFinEquiv`. -/
noncomputable def flatAssignEquiv (T n m : ℕ) :
    (Fin n → Fin m → Fin T) ≃ (Fin (n * m) → Fin T) where
  toFun σH := fun k => σH (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  invFun σ := fun w z => σ (finProdFinEquiv (w, z))
  left_inv σH := by funext w z; simp
  right_inv σ := by
    funext k
    show σ (finProdFinEquiv (finProdFinEquiv.symm k)) = σ k
    rw [Equiv.apply_symm_apply]

theorem flatAssignEquiv_apply_fpfe {T n m : ℕ} (σH : Fin n → Fin m → Fin T)
    (w : Fin n) (z : Fin m) :
    (flatAssignEquiv T n m σH) (finProdFinEquiv (w, z)) = σH w z := by
  show σH (finProdFinEquiv.symm (finProdFinEquiv (w, z))).1
      (finProdFinEquiv.symm (finProdFinEquiv (w, z))).2 = σH w z
  rw [Equiv.symm_apply_apply]

theorem flatAssignEquiv_weight_prod {T n m : ℕ} (W : Fin T → ℝ)
    (σH : Fin n → Fin m → Fin T) :
    (∏ k : Fin (n * m), W ((flatAssignEquiv T n m σH) k)) =
      ∏ w : Fin n, ∏ z : Fin m, W (σH w z) := by
  rw [← Equiv.prod_comp finProdFinEquiv (fun k => W ((flatAssignEquiv T n m σH) k)),
    Fintype.prod_prod_type]
  exact Finset.prod_congr rfl fun w _ => Finset.prod_congr rfl fun z _ => by
    rw [flatAssignEquiv_apply_fpfe]

/-- **n-fold `H`-copy collapse** (B3 engine): summing the flat internal-vertex
assignment factors the contribution of the `n` glued `H`-copies into a product of
`n` rooted profiles, each rooted at the value `r w` its anchor vertex receives. -/
theorem decorateAll_Hflat_collapse {T n m : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (H : SimpleGraph (Fin (m + 1))) [DecidableRel H.Adj] (r : Fin n → Fin T) :
    (∑ σ : Fin (n * m) → Fin T, (∏ k : Fin (n * m), W (σ k)) *
        ∏ w : Fin n, ∏ e ∈ H.edgeFinset,
          B (Fin.cons (α := fun _ => Fin T) (r w)
                (fun z => σ (finProdFinEquiv (w, z))) (Quot.out e).1)
            (Fin.cons (α := fun _ => Fin T) (r w)
                (fun z => σ (finProdFinEquiv (w, z))) (Quot.out e).2))
      = ∏ w : Fin n, rootedProfile B W (r w) H := by
  classical
  have hrw : (∏ w : Fin n, rootedProfile B W (r w) H) =
      ∏ w : Fin n, ∑ τ : Fin m → Fin T, (∏ z : Fin m, W (τ z)) *
        ∏ e ∈ H.edgeFinset,
          B (Fin.cons (α := fun _ => Fin T) (r w) τ (Quot.out e).1)
            (Fin.cons (α := fun _ => Fin T) (r w) τ (Quot.out e).2) :=
    Finset.prod_congr rfl fun w _ => rootedProfile_cons B W (r w) H
  rw [hrw, Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin m → Fin T)))
      (fun w τ => (∏ z : Fin m, W (τ z)) *
        ∏ e ∈ H.edgeFinset,
          B (Fin.cons (α := fun _ => Fin T) (r w) τ (Quot.out e).1)
            (Fin.cons (α := fun _ => Fin T) (r w) τ (Quot.out e).2)),
    Fintype.piFinset_univ, ← Equiv.sum_comp (flatAssignEquiv T n m)]
  refine Finset.sum_congr rfl fun σH _ => ?_
  rw [flatAssignEquiv_weight_prod, Finset.prod_mul_distrib]
  refine congrArg (_ * ·) (Finset.prod_congr rfl fun w _ => ?_)
  rw [show (fun z => (flatAssignEquiv T n m σH) (finProdFinEquiv (w, z))) = σH w from
    funext fun z => flatAssignEquiv_apply_fpfe σH w z]

/-- **B3 — all-vertex decoration factorization** (the key theorem): decorating
every unlabeled vertex of `F` with a copy of `H` multiplies each `F`-assignment's
contribution by the product, over unlabeled vertices `w`, of the `H`-profile rooted
at the value `w` receives. The engine of `rootedProfileEquiv_weightMod`. -/
theorem rootedProfile_decorateAll {T n m : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (v : Fin T)
    (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj]
    (H : SimpleGraph (Fin (m + 1))) [DecidableRel H.Adj] :
    rootedProfile B W v (decorateAll F H) =
      ∑ σF : Fin n → Fin T,
        ((∏ w : Fin n, W (σF w)) *
          ∏ e ∈ F.edgeFinset,
            B (Fin.cons (α := fun _ => Fin T) v σF (Quot.out e).1)
              (Fin.cons (α := fun _ => Fin T) v σF (Quot.out e).2)) *
        ∏ w : Fin n, rootedProfile B W (σF w) H := by
  classical
  rw [rootedProfile_cons]
  rw [Finset.sum_congr rfl fun σ (_ : σ ∈ Finset.univ) => by
    rw [decorateAll_prod_eq B hB F H (Fin.cons (α := fun _ => Fin T) v σ)]]
  rw [sum_fin_split n (n * m)]
  refine Finset.sum_congr rfl fun σF _ => ?_
  simp only [prod_appendFn, consAppendAll_inl, consAppendAll_embedHCopy, Fin.cons_succ]
  rw [← decorateAll_Hflat_collapse B W H σF, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σHflat _ => by ring

/-- **B4 — single-profile weight modification stays in the span**: modifying the
weight `W` by the rooted profile of a single graph `H` turns the profile of `F`
into the profile of the all-vertex decoration `decorateAll F H`, which is a bare
profile and hence in `InRootedProfileSpan B W`. This is the single-`H` case of
`rootedProfileEquiv_weightMod`; the general `g ∈ span` case follows by linearity. -/
theorem rootedProfile_weightMul_of_profile_mem_span {T n m : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj]
    (H : SimpleGraph (Fin (m + 1))) [DecidableRel H.Adj] :
    InRootedProfileSpan B W
      (fun v => rootedProfile B (fun t => W t * rootedProfile B W t H) v F) := by
  have hfun : (fun v => rootedProfile B (fun t => W t * rootedProfile B W t H) v F)
      = rootedProfileFun B W (decorateAll F H) := by
    funext v
    show rootedProfile B (fun t => W t * rootedProfile B W t H) v F
        = rootedProfile B W v (decorateAll F H)
    rw [rootedProfile_decorateAll B hB W v F H,
      rootedProfile_cons B (fun t => W t * rootedProfile B W t H) v F]
    refine Finset.sum_congr rfl fun σF _ => ?_
    rw [Finset.prod_mul_distrib]
    ring
  rw [hfun]
  exact InRootedProfileSpan.of_profile B W (decorateAll F H)

/-! ### Per-vertex-family decoration (`decorateAllFam`) — the Σ-indexed generalization

`decorateAll` glues ONE graph `H` at every unlabeled vertex; for the general
`g = ∑_k c_k · rootedProfileFun B W H_k` we must glue a possibly DIFFERENT graph
`Hfam w` at each unlabeled vertex `w`. Sizes vary with `w`, so the internal vertices
form a Σ-type `(w : Fin n) × Fin (mfam w)` (flattened via `finSigmaFinEquiv`, never
common-size padding, which would scale the profile by `(∑ W)^extra` — zero for signed `W`). -/

/-- Embedding of the `w`-th `H`-copy (family version): `0 ↦ inl (succ w)`,
`succ z ↦ inr ⟨w, z⟩`. -/
def embedHCopyFam {n : ℕ} {mfam : Fin n → ℕ} (w : Fin n) :
    Fin (mfam w + 1) ↪ Fin (n + 1) ⊕ ((w' : Fin n) × Fin (mfam w')) where
  toFun := Fin.cons (Sum.inl w.succ) (fun z => Sum.inr ⟨w, z⟩)
  inj' a b hab := by
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨k, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨l, rfl⟩ <;>
      simp_all [Fin.cons_zero, Fin.cons_succ]

/-- The structured per-vertex-family decoration. -/
def decorateAllFamSum {n : ℕ} {mfam : Fin n → ℕ} (F : SimpleGraph (Fin (n + 1)))
    (Hfam : (w : Fin n) → SimpleGraph (Fin (mfam w + 1))) :
    SimpleGraph (Fin (n + 1) ⊕ ((w' : Fin n) × Fin (mfam w'))) :=
  SimpleGraph.map Function.Embedding.inl F ⊔
    Finset.univ.sup (fun w : Fin n => SimpleGraph.map (embedHCopyFam w) (Hfam w))

/-- `Fin (n+1) ⊕ ((w : Fin n) × Fin (mfam w)) ≃ Fin (n + (∑ w, mfam w) + 1)` with `inl 0 ↦ 0`. -/
noncomputable def decorAllFamVertexEquiv {n : ℕ} (mfam : Fin n → ℕ) :
    (Fin (n + 1) ⊕ ((w' : Fin n) × Fin (mfam w'))) ≃ Fin (n + (∑ w, mfam w) + 1) :=
  (Equiv.sumCongr (Equiv.refl (Fin (n + 1))) finSigmaFinEquiv).trans
    (finSumFinEquiv.trans (finCongr (by omega)))

@[simp] theorem decorAllFamVertexEquiv_inl_zero {n : ℕ} (mfam : Fin n → ℕ) :
    decorAllFamVertexEquiv mfam (Sum.inl 0) = 0 :=
  Fin.ext (by simp [decorAllFamVertexEquiv, finSumFinEquiv])

/-- **Per-vertex-family decoration** as a `SimpleGraph (Fin (n + (∑ mfam) + 1))`. -/
noncomputable def decorateAllFam {n : ℕ} {mfam : Fin n → ℕ} (F : SimpleGraph (Fin (n + 1)))
    (Hfam : (w : Fin n) → SimpleGraph (Fin (mfam w + 1))) :
    SimpleGraph (Fin (n + (∑ w, mfam w) + 1)) :=
  (decorateAllFamSum F Hfam).comap (decorAllFamVertexEquiv mfam).symm

theorem decorateAllFamSum_sup_adj {n : ℕ} {mfam : Fin n → ℕ}
    (Hfam : (w : Fin n) → SimpleGraph (Fin (mfam w + 1)))
    (x y : Fin (n + 1) ⊕ ((w' : Fin n) × Fin (mfam w'))) :
    (Finset.univ.sup (fun w : Fin n => SimpleGraph.map (embedHCopyFam w) (Hfam w))).Adj x y ↔
      ∃ w : Fin n, (SimpleGraph.map (embedHCopyFam w) (Hfam w)).Adj x y := by
  simp [Finset.sup_eq_iSup, SimpleGraph.iSup_adj]

instance {n : ℕ} {mfam : Fin n → ℕ} (Hfam : (w : Fin n) → SimpleGraph (Fin (mfam w + 1)))
    [∀ w, DecidableRel (Hfam w).Adj] :
    DecidableRel
      (Finset.univ.sup (fun w : Fin n => SimpleGraph.map (embedHCopyFam w) (Hfam w))).Adj :=
  fun x y => decidable_of_iff _ (decorateAllFamSum_sup_adj Hfam x y).symm

instance {n : ℕ} {mfam : Fin n → ℕ} (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj]
    (Hfam : (w : Fin n) → SimpleGraph (Fin (mfam w + 1))) [∀ w, DecidableRel (Hfam w).Adj] :
    DecidableRel (decorateAllFamSum F Hfam).Adj := by
  intro x y
  unfold decorateAllFamSum
  rw [SimpleGraph.sup_adj, decorateAllFamSum_sup_adj]
  infer_instance

noncomputable instance {n : ℕ} {mfam : Fin n → ℕ} (F : SimpleGraph (Fin (n + 1)))
    [DecidableRel F.Adj] (Hfam : (w : Fin n) → SimpleGraph (Fin (mfam w + 1)))
    [∀ w, DecidableRel (Hfam w).Adj] : DecidableRel (decorateAllFam F Hfam).Adj :=
  SimpleGraph.instDecidableComapAdj _ _

theorem embedHCopyFam_apply_ne {n : ℕ} {mfam : Fin n → ℕ} {w w' : Fin n} (hww : w ≠ w')
    (a : Fin (mfam w + 1)) (a' : Fin (mfam w' + 1)) :
    (embedHCopyFam w) a ≠ (embedHCopyFam w') a' := by
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨k, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ a' with rfl | ⟨l, rfl⟩
  · simp only [embedHCopyFam, Function.Embedding.coeFn_mk, Fin.cons_zero, ne_eq, Sum.inl.injEq]
    exact fun h => hww (Fin.succ_injective _ h)
  · simp [embedHCopyFam]
  · simp [embedHCopyFam]
  · simp only [embedHCopyFam, Function.Embedding.coeFn_mk, Fin.cons_succ, ne_eq, Sum.inr.injEq]
    exact fun h => hww (congrArg Sigma.fst h)

theorem decorateAllFam_Hcopy_disjoint {n : ℕ} {mfam : Fin n → ℕ}
    (Hfam : (w : Fin n) → SimpleGraph (Fin (mfam w + 1))) [∀ w, DecidableRel (Hfam w).Adj]
    {w w' : Fin n} (hww : w ≠ w') :
    Disjoint (SimpleGraph.map (embedHCopyFam w) (Hfam w)).edgeFinset
      (SimpleGraph.map (embedHCopyFam w') (Hfam w')).edgeFinset := by
  rw [Finset.disjoint_left]
  intro E hw hw'
  rw [SimpleGraph.mem_edgeFinset] at hw hw'
  induction E using Sym2.ind with
  | _ x y =>
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.map_adj] at hw hw'
    obtain ⟨a, b, _, ha, _⟩ := hw
    obtain ⟨a', b', _, ha', _⟩ := hw'
    exact embedHCopyFam_apply_ne hww a a' (ha.trans ha'.symm)

theorem decorateAllFam_F_sup_disjoint {n : ℕ} {mfam : Fin n → ℕ}
    (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj]
    (Hfam : (w : Fin n) → SimpleGraph (Fin (mfam w + 1))) [∀ w, DecidableRel (Hfam w).Adj] :
    Disjoint (SimpleGraph.map Function.Embedding.inl F).edgeFinset
      (Finset.univ.sup (fun w : Fin n =>
        SimpleGraph.map (embedHCopyFam w) (Hfam w))).edgeFinset := by
  rw [Finset.disjoint_left]
  intro E hF hS
  rw [SimpleGraph.mem_edgeFinset] at hF hS
  induction E using Sym2.ind with
  | _ x y =>
    rw [SimpleGraph.mem_edgeSet, decorateAllFamSum_sup_adj] at hS
    obtain ⟨w, hw⟩ := hS
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.map_adj] at hF
    rw [SimpleGraph.map_adj] at hw
    obtain ⟨a, b, _, ha, hb⟩ := hF
    obtain ⟨a', b', hadj', ha', hb'⟩ := hw
    have ha0 : a' = 0 := by
      rcases Fin.eq_zero_or_eq_succ a' with rfl | ⟨k, rfl⟩
      · rfl
      · exact absurd (ha'.trans ha.symm) (by simp [embedHCopyFam])
    have hb0 : b' = 0 := by
      rcases Fin.eq_zero_or_eq_succ b' with rfl | ⟨k, rfl⟩
      · rfl
      · exact absurd (hb'.trans hb.symm) (by simp [embedHCopyFam])
    subst ha0 hb0
    exact (Hfam w).loopless 0 hadj'

theorem decorateAllFamSum_sup_edgeFinset {n : ℕ} {mfam : Fin n → ℕ}
    (Hfam : (w : Fin n) → SimpleGraph (Fin (mfam w + 1))) [∀ w, DecidableRel (Hfam w).Adj] :
    (Finset.univ.sup (fun w : Fin n => SimpleGraph.map (embedHCopyFam w) (Hfam w))).edgeFinset =
      Finset.univ.biUnion (fun w => (SimpleGraph.map (embedHCopyFam w) (Hfam w)).edgeFinset) := by
  ext E
  induction E using Sym2.ind with
  | _ x y =>
    simp only [SimpleGraph.mem_edgeFinset, Finset.mem_biUnion, Finset.mem_univ, true_and,
      SimpleGraph.mem_edgeSet, decorateAllFamSum_sup_adj]

/-- **Edge-product transport + split** (C3 / B2-analog): the `rootedProfile` edge
product over `decorateAllFam F Hfam` factors into the `F`-edge product times the
product over the `n` per-vertex `H`-copy edge products. -/
theorem decorateAllFam_prod_eq {T n : ℕ} {mfam : Fin n → ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj]
    (Hfam : (w : Fin n) → SimpleGraph (Fin (mfam w + 1))) [∀ w, DecidableRel (Hfam w).Adj]
    (τ : Fin (n + (∑ w, mfam w) + 1) → Fin T) :
    (∏ E ∈ (decorateAllFam F Hfam).edgeFinset, B (τ (Quot.out E).1) (τ (Quot.out E).2)) =
      (∏ e ∈ F.edgeFinset,
        B (τ (decorAllFamVertexEquiv mfam (Sum.inl (Quot.out e).1)))
          (τ (decorAllFamVertexEquiv mfam (Sum.inl (Quot.out e).2)))) *
      ∏ w : Fin n, ∏ e ∈ (Hfam w).edgeFinset,
        B (τ (decorAllFamVertexEquiv mfam (embedHCopyFam w (Quot.out e).1)))
          (τ (decorAllFamVertexEquiv mfam (embedHCopyFam w (Quot.out e).2))) := by
  classical
  have step1 :
      (∏ E ∈ (decorateAllFam F Hfam).edgeFinset, B (τ (Quot.out E).1) (τ (Quot.out E).2)) =
      ∏ E ∈ (decorateAllFamSum F Hfam).edgeFinset,
        B (τ (decorAllFamVertexEquiv mfam (Quot.out E).1))
          (τ (decorAllFamVertexEquiv mfam (Quot.out E).2)) := by
    unfold decorateAllFam
    rw [comap_symm_edgeFinset, Finset.prod_map]
    refine Finset.prod_congr rfl fun E _ => ?_
    induction E using Sym2.ind with
    | _ a b =>
      rw [show (decorAllFamVertexEquiv mfam).toEmbedding.sym2Map s(a, b)
          = s(decorAllFamVertexEquiv mfam a, decorAllFamVertexEquiv mfam b) from rfl,
        out_pair_eq' B hB τ _ _,
        out_pair_eq' B hB (fun s => τ (decorAllFamVertexEquiv mfam s)) a b]
  rw [step1]
  have keySup : (decorateAllFamSum F Hfam).edgeFinset =
      (SimpleGraph.map Function.Embedding.inl F).edgeFinset ∪
        (Finset.univ.sup (fun w : Fin n =>
          SimpleGraph.map (embedHCopyFam w) (Hfam w))).edgeFinset := by
    apply Finset.coe_injective
    rw [SimpleGraph.coe_edgeFinset, Finset.coe_union, SimpleGraph.coe_edgeFinset,
      SimpleGraph.coe_edgeFinset]
    show (decorateAllFamSum F Hfam).edgeSet = _
    unfold decorateAllFamSum
    rw [SimpleGraph.edgeSet_sup]
  rw [keySup, Finset.prod_union (decorateAllFam_F_sup_disjoint F Hfam)]
  congr 1
  · have key : (SimpleGraph.map Function.Embedding.inl F).edgeFinset =
        Finset.map (Function.Embedding.inl (β := (w' : Fin n) × Fin (mfam w'))).sym2Map
          F.edgeFinset := by
      apply Finset.coe_injective
      rw [SimpleGraph.coe_edgeFinset, Finset.coe_map, SimpleGraph.coe_edgeFinset,
        SimpleGraph.edgeSet_map]
    rw [key, Finset.prod_map]
    refine Finset.prod_congr rfl fun e _ => ?_
    induction e using Sym2.ind with
    | _ a b =>
      rw [show (Function.Embedding.inl (β := (w' : Fin n) × Fin (mfam w'))).sym2Map s(a, b)
          = s((Sum.inl a : Fin (n + 1) ⊕ ((w' : Fin n) × Fin (mfam w'))), Sum.inl b) from rfl,
        out_pair_eq' B hB (fun s => τ (decorAllFamVertexEquiv mfam s)) _ _,
        out_pair_eq' B hB (fun s => τ (decorAllFamVertexEquiv mfam (Sum.inl s))) a b]
  · rw [decorateAllFamSum_sup_edgeFinset,
      Finset.prod_biUnion (fun w _ w' _ hww => decorateAllFam_Hcopy_disjoint Hfam hww)]
    refine Finset.prod_congr rfl fun w _ => ?_
    have key : (SimpleGraph.map (embedHCopyFam w) (Hfam w)).edgeFinset =
        Finset.map (embedHCopyFam w).sym2Map (Hfam w).edgeFinset := by
      apply Finset.coe_injective
      rw [SimpleGraph.coe_edgeFinset, Finset.coe_map, SimpleGraph.coe_edgeFinset,
        SimpleGraph.edgeSet_map]
    rw [key, Finset.prod_map]
    refine Finset.prod_congr rfl fun e _ => ?_
    induction e using Sym2.ind with
    | _ a b =>
      rw [show (embedHCopyFam w).sym2Map s(a, b)
          = s(embedHCopyFam w a, embedHCopyFam w b) from rfl,
        out_pair_eq' B hB (fun s => τ (decorAllFamVertexEquiv mfam s)) _ _,
        out_pair_eq' B hB (fun s => τ (decorAllFamVertexEquiv mfam (embedHCopyFam w s))) a b]

theorem decorAllFamVertexEquiv_inl_val {n : ℕ} (mfam : Fin n → ℕ) (x : Fin (n + 1)) :
    ((decorAllFamVertexEquiv mfam (Sum.inl x)) : ℕ) = (x : ℕ) := by
  simp [decorAllFamVertexEquiv, finSumFinEquiv]

theorem decorAllFamVertexEquiv_inr_val {n : ℕ} (mfam : Fin n → ℕ) (w : Fin n) (z : Fin (mfam w)) :
    ((decorAllFamVertexEquiv mfam (Sum.inr ⟨w, z⟩)) : ℕ)
      = (n + 1) + (finSigmaFinEquiv (⟨w, z⟩ : (w' : Fin n) × Fin (mfam w')) : ℕ) := by
  simp [decorAllFamVertexEquiv, finSumFinEquiv]

/-- **C3 F-side value lemma**: under `appendFn σF σHflat`, the value at an
`F`-vertex `inl x` is `Fin.cons v σF x`. -/
theorem consAppendAllFam_inl {T n : ℕ} {mfam : Fin n → ℕ} (v : Fin T) (σF : Fin n → Fin T)
    (σHflat : Fin (∑ w, mfam w) → Fin T) (x : Fin (n + 1)) :
    Fin.cons (α := fun _ => Fin T) v (appendFn σF σHflat)
        (decorAllFamVertexEquiv mfam (Sum.inl x)) = Fin.cons (α := fun _ => Fin T) v σF x := by
  rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨w, rfl⟩
  · rw [show decorAllFamVertexEquiv mfam (Sum.inl (0 : Fin (n + 1))) = 0 from
      Fin.ext (by rw [decorAllFamVertexEquiv_inl_val]; rfl)]; simp
  · rw [show decorAllFamVertexEquiv mfam (Sum.inl (Fin.succ w)) = Fin.succ ⟨w, by omega⟩ from
      Fin.ext (by rw [decorAllFamVertexEquiv_inl_val]; rfl),
      Fin.cons_succ, Fin.cons_succ, appendFn_low σF σHflat (by simp)]

/-- **C3 H-side value lemma**: under `appendFn σF σHflat`, the `w`-th `H`-copy's
assignment is `Fin.cons (Fin.cons v σF w.succ) (fun z => σHflat (finSigmaFinEquiv ⟨w, z⟩))`. -/
theorem consAppendAllFam_embedHCopyFam {T n : ℕ} {mfam : Fin n → ℕ} (v : Fin T) (σF : Fin n → Fin T)
    (σHflat : Fin (∑ w, mfam w) → Fin T) (w : Fin n) (a : Fin (mfam w + 1)) :
    Fin.cons (α := fun _ => Fin T) v (appendFn σF σHflat)
        (decorAllFamVertexEquiv mfam (embedHCopyFam w a)) =
      Fin.cons (α := fun _ => Fin T) (Fin.cons (α := fun _ => Fin T) v σF w.succ)
        (fun z => σHflat (finSigmaFinEquiv ⟨w, z⟩)) a := by
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨z, rfl⟩
  · show Fin.cons (α := fun _ => Fin T) v (appendFn σF σHflat)
        (decorAllFamVertexEquiv mfam (Sum.inl w.succ)) = _
    rw [consAppendAllFam_inl]; simp
  · rw [show (embedHCopyFam w) (Fin.succ z) = Sum.inr ⟨w, z⟩ from by simp [embedHCopyFam],
      show decorAllFamVertexEquiv mfam (Sum.inr ⟨w, z⟩)
          = Fin.succ ⟨n + (finSigmaFinEquiv (⟨w, z⟩ : (w' : Fin n) × Fin (mfam w')) : ℕ), by
            have := (finSigmaFinEquiv (⟨w, z⟩ : (w' : Fin n) × Fin (mfam w'))).isLt; omega⟩ from
        Fin.ext (by rw [decorAllFamVertexEquiv_inr_val]; simp; omega),
      Fin.cons_succ, Fin.cons_succ,
      appendFn_high σF σHflat (by simp)]
    exact congrArg σHflat (Fin.ext (by simp))

/-- **Family flat ↔ curried assignment equivalence**: a flat assignment over the
`∑ mfam` internal vertices is the same as `n` dependent per-copy assignments, matched
via `finSigmaFinEquiv`. -/
noncomputable def flatAssignEquivFam {n : ℕ} (mfam : Fin n → ℕ) (T : ℕ) :
    ((w : Fin n) → Fin (mfam w) → Fin T) ≃ (Fin (∑ w, mfam w) → Fin T) where
  toFun σH := fun k => σH (finSigmaFinEquiv.symm k).1 (finSigmaFinEquiv.symm k).2
  invFun σ := fun w z => σ (finSigmaFinEquiv ⟨w, z⟩)
  left_inv σH := by
    funext w z
    exact congrArg (fun p : (w' : Fin n) × Fin (mfam w') => σH p.1 p.2)
      (finSigmaFinEquiv.symm_apply_apply ⟨w, z⟩)
  right_inv σ := by
    funext k
    show σ (finSigmaFinEquiv (finSigmaFinEquiv.symm k)) = σ k
    rw [Equiv.apply_symm_apply]

theorem flatAssignEquivFam_apply_fse {T n : ℕ} {mfam : Fin n → ℕ}
    (σH : (w : Fin n) → Fin (mfam w) → Fin T) (w : Fin n) (z : Fin (mfam w)) :
    (flatAssignEquivFam mfam T σH) (finSigmaFinEquiv ⟨w, z⟩) = σH w z :=
  congr_fun (congr_fun ((flatAssignEquivFam mfam T).left_inv σH) w) z

theorem flatAssignEquivFam_weight_prod {T n : ℕ} {mfam : Fin n → ℕ} (W : Fin T → ℝ)
    (σH : (w : Fin n) → Fin (mfam w) → Fin T) :
    (∏ k : Fin (∑ w, mfam w), W ((flatAssignEquivFam mfam T σH) k)) =
      ∏ w : Fin n, ∏ z : Fin (mfam w), W (σH w z) := by
  rw [← Equiv.prod_comp finSigmaFinEquiv (fun k => W ((flatAssignEquivFam mfam T σH) k)),
    ← Finset.univ_sigma_univ, Finset.prod_sigma]
  exact Finset.prod_congr rfl fun w _ => Finset.prod_congr rfl fun z _ => by
    rw [flatAssignEquivFam_apply_fse]

/-- **n-fold family `H`-copy collapse** (C3 engine): summing the flat internal
assignment factors the `n` per-vertex glued copies into a product of the `n`
rooted profiles `rootedProfile B W (r w) (Hfam w)`. -/
theorem decorateAllFam_Hflat_collapse {T n : ℕ} {mfam : Fin n → ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (Hfam : (w : Fin n) → SimpleGraph (Fin (mfam w + 1)))
    [∀ w, DecidableRel (Hfam w).Adj] (r : Fin n → Fin T) :
    (∑ σ : Fin (∑ w, mfam w) → Fin T, (∏ k : Fin (∑ w, mfam w), W (σ k)) *
        ∏ w : Fin n, ∏ e ∈ (Hfam w).edgeFinset,
          B (Fin.cons (α := fun _ => Fin T) (r w)
                (fun z => σ (finSigmaFinEquiv ⟨w, z⟩)) (Quot.out e).1)
            (Fin.cons (α := fun _ => Fin T) (r w)
                (fun z => σ (finSigmaFinEquiv ⟨w, z⟩)) (Quot.out e).2))
      = ∏ w : Fin n, rootedProfile B W (r w) (Hfam w) := by
  classical
  have hrw : (∏ w : Fin n, rootedProfile B W (r w) (Hfam w)) =
      ∏ w : Fin n, ∑ τ : Fin (mfam w) → Fin T, (∏ z : Fin (mfam w), W (τ z)) *
        ∏ e ∈ (Hfam w).edgeFinset,
          B (Fin.cons (α := fun _ => Fin T) (r w) τ (Quot.out e).1)
            (Fin.cons (α := fun _ => Fin T) (r w) τ (Quot.out e).2) :=
    Finset.prod_congr rfl fun w _ => rootedProfile_cons B W (r w) (Hfam w)
  rw [hrw, Finset.prod_univ_sum (fun w : Fin n => (Finset.univ : Finset (Fin (mfam w) → Fin T)))
      (fun w τ => (∏ z : Fin (mfam w), W (τ z)) *
        ∏ e ∈ (Hfam w).edgeFinset,
          B (Fin.cons (α := fun _ => Fin T) (r w) τ (Quot.out e).1)
            (Fin.cons (α := fun _ => Fin T) (r w) τ (Quot.out e).2)),
    Fintype.piFinset_univ, ← Equiv.sum_comp (flatAssignEquivFam mfam T)]
  refine Finset.sum_congr rfl fun σH _ => ?_
  rw [flatAssignEquivFam_weight_prod, Finset.prod_mul_distrib]
  refine congrArg (_ * ·) (Finset.prod_congr rfl fun w _ => ?_)
  rw [show (fun z => (flatAssignEquivFam mfam T σH) (finSigmaFinEquiv ⟨w, z⟩)) = σH w from
    funext fun z => flatAssignEquivFam_apply_fse σH w z]

/-- **C3 — per-vertex-family decoration factorization**: decorating each unlabeled
vertex `w` of `F` with `Hfam w` multiplies each `F`-assignment's contribution by
`∏ w, rootedProfile B W (σF w) (Hfam w)`. The varying-graph generalization of
`rootedProfile_decorateAll`. -/
theorem rootedProfile_decorateAllFam {T n : ℕ} {mfam : Fin n → ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (v : Fin T)
    (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj]
    (Hfam : (w : Fin n) → SimpleGraph (Fin (mfam w + 1))) [∀ w, DecidableRel (Hfam w).Adj] :
    rootedProfile B W v (decorateAllFam F Hfam) =
      ∑ σF : Fin n → Fin T,
        ((∏ w : Fin n, W (σF w)) *
          ∏ e ∈ F.edgeFinset,
            B (Fin.cons (α := fun _ => Fin T) v σF (Quot.out e).1)
              (Fin.cons (α := fun _ => Fin T) v σF (Quot.out e).2)) *
        ∏ w : Fin n, rootedProfile B W (σF w) (Hfam w) := by
  classical
  rw [rootedProfile_cons]
  rw [Finset.sum_congr rfl fun σ (_ : σ ∈ Finset.univ) => by
    rw [decorateAllFam_prod_eq B hB F Hfam (Fin.cons (α := fun _ => Fin T) v σ)]]
  rw [sum_fin_split n (∑ w, mfam w)]
  refine Finset.sum_congr rfl fun σF _ => ?_
  simp only [prod_appendFn, consAppendAllFam_inl, consAppendAllFam_embedHCopyFam, Fin.cons_succ]
  rw [← decorateAllFam_Hflat_collapse B W Hfam σF, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σHflat _ => by ring

/-! ### Decorated power sums — the bridge to classwise row-value measures

`rowValueMeasure_eq_of_rootedProfileEquiv` gives equality of the GLOBAL
`W`-weighted row-value measures. The next step toward the rank theorem
`vertexOrbitRel_of_rootedProfileEquiv` is equality INSIDE each rooted-profile
atom class — obtained by decorating the power sums with atom indicators. -/

/-- Finite-sum closure of the rooted-profile span (CycleKrylov-local copy of the
private `Lovasz` helper, built from `.zero`/`.add`). -/
theorem InRootedProfileSpan.finset_sum' {T : ℕ} {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    {α : Type*} (S : Finset α) (g : α → Fin T → ℝ)
    (hg : ∀ a ∈ S, InRootedProfileSpan B W (g a)) :
    InRootedProfileSpan B W (fun v => ∑ a ∈ S, g a v) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using InRootedProfileSpan.zero B W
  | insert a S ha_notin ih =>
    have h_add := (hg a (Finset.mem_insert_self a S)).add
      (ih (fun b hb => hg b (Finset.mem_insert_of_mem hb)))
    convert h_add using 1
    funext v
    rw [Finset.sum_insert ha_notin]; rfl

/-- **C3 — modified-weight profile stays in the span** (PROVED). For any `g` in the
`(B, W)`-rooted-profile span and any graph `F`, the modified-weight profile
`v ↦ rootedProfile B (W·g) v F` lies in `InRootedProfileSpan B W`.

**Construction**: expanding `g = ∑_k c_k · rootedProfileFun B W H_k` from `hg`,
the per-vertex product `∏_w g(σ w) = ∑_φ ∏_w c_{φ w} · rootedProfile B W (σ w) H_{φ w}`
(`Finset.prod_univ_sum`); distributing turns `rootedProfile B (W·g) v F` into
`∑_φ (∏_w c_{φ w}) · rootedProfile B W v (decorateAllFam F (fun w => H_{φ w}))`,
a finite linear combination of bare profiles of per-vertex glued graphs — hence in
the span by `InRootedProfileSpan.{finset_sum, smul}`. The single-`H` case
(`decorateAllFam` constant) is `rootedProfile_weightMul_of_profile_mem_span` (B4).
The general case uses the per-vertex-family glue `decorateAllFam` (a Σ-indexed
generalization of `decorateAll`, sizes handled by `finSigmaFinEquiv`, not casts). -/
theorem weightMod_profile_mem_span {T n : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj]
    {g : Fin T → ℝ} (hg : InRootedProfileSpan B W g) :
    InRootedProfileSpan B W (fun v => rootedProfile B (fun t => W t * g t) v F) := by
  classical
  obtain ⟨N, gdata, c, hgeq⟩ := hg
  letI hInst : ∀ k : Fin N, DecidableRel ((gdata k).2.1).Adj := fun k => (gdata k).2.2
  have hfun : (fun v => rootedProfile B (fun t => W t * g t) v F)
      = fun v => ∑ φ : Fin n → Fin N, (∏ w : Fin n, c (φ w)) *
          rootedProfileFun B W (decorateAllFam F (fun w => (gdata (φ w)).2.1)) v := by
    funext v
    have hL : rootedProfile B (fun t => W t * g t) v F =
        ∑ σF : Fin n → Fin T, ((∏ w : Fin n, W (σF w)) *
          ∏ e ∈ F.edgeFinset, B (Fin.cons (α := fun _ => Fin T) v σF (Quot.out e).1)
            (Fin.cons (α := fun _ => Fin T) v σF (Quot.out e).2)) *
          ∏ w : Fin n, g (σF w) := by
      rw [rootedProfile_cons B (fun t => W t * g t) v F]
      exact Finset.sum_congr rfl fun σF _ => by rw [Finset.prod_mul_distrib]; ring
    have hR : (∑ φ : Fin n → Fin N, (∏ w : Fin n, c (φ w)) *
          rootedProfileFun B W (decorateAllFam F (fun w => (gdata (φ w)).2.1)) v)
        = ∑ σF : Fin n → Fin T, ((∏ w : Fin n, W (σF w)) *
            ∏ e ∈ F.edgeFinset, B (Fin.cons (α := fun _ => Fin T) v σF (Quot.out e).1)
              (Fin.cons (α := fun _ => Fin T) v σF (Quot.out e).2)) *
            ∏ w : Fin n, g (σF w) := by
      rw [Finset.sum_congr rfl fun φ (_ : φ ∈ Finset.univ) => by
        rw [show rootedProfileFun B W (decorateAllFam F (fun w => (gdata (φ w)).2.1)) v
              = rootedProfile B W v (decorateAllFam F (fun w => (gdata (φ w)).2.1)) from rfl,
          rootedProfile_decorateAllFam B hB W v F (fun w => (gdata (φ w)).2.1), Finset.mul_sum]]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun σF _ => ?_
      have hinner : (∏ w : Fin n, g (σF w))
          = ∑ φ : Fin n → Fin N, (∏ w : Fin n, c (φ w)) *
              ∏ w : Fin n, rootedProfile B W (σF w) (gdata (φ w)).2.1 := by
        have hpt : ∀ w : Fin n, g (σF w)
            = ∑ k : Fin N, c k * rootedProfile B W (σF w) (gdata k).2.1 :=
          fun w => congr_fun hgeq (σF w)
        rw [Finset.prod_congr rfl fun w (_ : w ∈ Finset.univ) => hpt w, Finset.prod_univ_sum,
          Fintype.piFinset_univ]
        exact Finset.sum_congr rfl fun φ _ => Finset.prod_mul_distrib
      rw [hinner, Finset.mul_sum]
      exact Finset.sum_congr rfl fun φ _ => by ring
    rw [hL]; exact hR.symm
  rw [hfun]
  exact InRootedProfileSpan.finset_sum' Finset.univ _ fun φ _ =>
    (InRootedProfileSpan.of_profile B W
      (decorateAllFam F (fun w => (gdata (φ w)).2.1))).smul (∏ w : Fin n, c (φ w))

/-- **Weight modification preserves rooted-profile equivalence** (C4 — PROVED
modulo the focused span-membership lemma `weightMod_profile_mem_span`). For any
`g` in the `(B, W)`-rooted-profile span, rooted-profile-equivalent vertices stay
equivalent under the modified weight `W · g`. The analytic content is discharged:
the modified-weight profile lies in the span (`weightMod_profile_mem_span`), and
span elements are constant on rpe-classes (`InRootedProfileSpan.const_on_rpe`). -/
theorem rootedProfileEquiv_weightMod {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) {i j : Fin T}
    (h : rootedProfileEquiv B W i j) {g : Fin T → ℝ}
    (hg : InRootedProfileSpan B W g) :
    rootedProfileEquiv B (fun t => W t * g t) i j := by
  intro n F _
  exact (weightMod_profile_mem_span B hB W F hg).const_on_rpe h

/-- **Decorated power sums descend** (PROVED modulo `rootedProfileEquiv_weightMod`).
For `g` in the rooted-profile span (e.g. an atom indicator `rpeIndicator C`),
the `g`-decorated power sums of rpe-equivalent rows agree at every degree `k`.
With `g = 1_C` and `k = 2` this is `classwise_sqMoment_descends`; in general it
gives equality of the row-value measures inside every atom class.

Proof: shift `g` by a positive constant `c` so `g + c > 0` and stays in the span,
apply `powerSum_descends_of_rootedProfileEquiv` at the positive weight
`W·(g + c)` (rpe-preserved by `rootedProfileEquiv_weightMod`) and at `W`, then
subtract (`∑ W·g·B^k = ∑ W·(g+c)·B^k − c·∑ W·B^k`). -/
theorem decoratedPowerSum_descends_of_rootedProfileEquiv {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (hW : ∀ t, 0 < W t) {i j : Fin T} (h : rootedProfileEquiv B W i j)
    {g : Fin T → ℝ} (hg : InRootedProfileSpan B W g) (k : ℕ) :
    ∑ t : Fin T, W t * g t * B i t ^ k = ∑ t : Fin T, W t * g t * B j t ^ k := by
  classical
  set c : ℝ := 1 + ∑ s, |g s| with hc
  have hcpos : ∀ t, 0 < g t + c := fun t => by
    have h1 : |g t| ≤ ∑ s, |g s| :=
      Finset.single_le_sum (f := fun s => |g s|) (fun s _ => abs_nonneg (g s))
        (Finset.mem_univ t)
    have h2 : -|g t| ≤ g t := neg_abs_le _
    rw [hc]; linarith
  have hgc : InRootedProfileSpan B W (fun t => g t + c) :=
    hg.add (InRootedProfileSpan.const B W c)
  have hgc_des := powerSum_descends_of_rootedProfileEquiv B hB
    (fun t => W t * (g t + c)) (fun t => mul_pos (hW t) (hcpos t))
    (rootedProfileEquiv_weightMod B hB W h hgc) k
  have hplain := powerSum_descends_of_rootedProfileEquiv B hB W hW h k
  have ei : ∀ j' : Fin T, ∑ t : Fin T, W t * g t * B j' t ^ k =
      (∑ t : Fin T, W t * (g t + c) * B j' t ^ k) - c * ∑ t : Fin T, W t * B j' t ^ k := by
    intro j'
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [ei i, ei j, hgc_des, hplain]

/-- **Classwise square-moment descent** (PROVED — no twin-free needed). For any
atom-invariant `g`, the `g`-decorated square moments of rpe-equivalent rows agree.
The `k = 2` specialization of `decoratedPowerSum_descends_of_rootedProfileEquiv`,
with span membership supplied by the K=1 fullness theorem
`InRootedProfileSpan.of_const_on_rpe` (atom-invariant ⟹ in the span). The `htwin`
hypothesis is retained for API compatibility but is unused — the weight-modification
route closes this WITHOUT twin-freeness, unlike the older singular-`M` stratum route. -/
theorem classwise_sqMoment_descends {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (_htwin : ∀ i j, i ≠ j → B i ≠ B j)
    {i j : Fin T} (h : rootedProfileEquiv B W i j)
    {g : Fin T → ℝ} (hg : ∀ a b, rootedProfileEquiv B W a b → g a = g b) :
    ∑ t : Fin T, W t * B i t ^ 2 * g t = ∑ t : Fin T, W t * B j t ^ 2 * g t := by
  have hspan : InRootedProfileSpan B W g := InRootedProfileSpan.of_const_on_rpe B hB W g hg
  have hpow := decoratedPowerSum_descends_of_rootedProfileEquiv B hB W hW h hspan 2
  calc ∑ t : Fin T, W t * B i t ^ 2 * g t
      = ∑ t : Fin T, W t * g t * B i t ^ 2 := Finset.sum_congr rfl fun t _ => by ring
    _ = ∑ t : Fin T, W t * g t * B j t ^ 2 := hpow
    _ = ∑ t : Fin T, W t * B j t ^ 2 * g t := Finset.sum_congr rfl fun t _ => by ring

/-- **Classwise row-value measures descend** (PROVED). Under rooted-profile
equivalence `i ~ j`, the two rows `B i` and `B j` have the SAME `W`-weighted
value distribution INSIDE every atom class `C = atom(r)` (the rpe-class of a
representative `r`). Phrased with the atom-restricting weight `W · rpeIndicator B W r`
(which is `W` on the class and `0` off it), so the indicator-weighted preimage mass
`∑_{t : B i t = a} W t · 1_{atom(r)}(t)` is exactly the `W`-mass of
`{t ∈ atom(r) : B i t = a}` — see `classwise_rowValueMeasure_eq_filter` for the
class-filtered restatement.

The classwise refinement of `rowValueMeasure_eq_of_rootedProfileEquiv`: apply
`weighted_powersum_determines_measure` with weight `W · rpeIndicator B W r`, whose
moments descend by `decoratedPowerSum_descends_of_rootedProfileEquiv` (span membership
from `rpeIndicator_mem_span`). The bridge to the orbit/rank theorem. -/
theorem classwise_rowValueMeasure_eq_of_rootedProfileEquiv {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ t, 0 < W t)
    {i j : Fin T} (h : rootedProfileEquiv B W i j) (r : Fin T) (a : ℝ) :
    (∑ t ∈ Finset.univ.filter (fun t => B i t = a), W t * rpeIndicator B W r t) =
      ∑ t ∈ Finset.univ.filter (fun t => B j t = a), W t * rpeIndicator B W r t :=
  weighted_powersum_determines_measure (B i) (B j) (fun t => W t * rpeIndicator B W r t)
    (fun k => decoratedPowerSum_descends_of_rootedProfileEquiv B hB W hW h
      (rpeIndicator_mem_span B hB W r) k) a

/-! ### Chunk A — the atom-class coherent structure

The invariants needed to build a weighted coherent configuration on the atom
partition of `rootedProfileEquiv`. `atomTransMeasure q i a` = the `W`-mass of the
value-`a` fibre of row `B i` restricted to atom class `atom(q)` — the "transition
measure" from the atom of `i` to the atom of `q`. The key fact
(`atomTransMeasure_eq_of_rpe`) is that it depends only on the atom of `i`, not the
representative — exactly the coherent-configuration coherence condition. This is
the constructive input for the orbit/rank theorem
`vertexOrbitRel_of_rootedProfileEquiv`; it does NOT yet build automorphisms (equal
`W`-masses give a coupling, not a bijection, with arbitrary positive real weights). -/

/-- **Indicator-`if` form of classwise row-value-measure equality** (wrapper around
`classwise_rowValueMeasure_eq_of_rootedProfileEquiv`): for rpe-equivalent `i, j` and
any atom representative `r` and value `a`, the atom-restricted value masses agree. -/
theorem atom_row_value_measure_eq {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ t, 0 < W t) {i j : Fin T} (h : rootedProfileEquiv B W i j)
    (r : Fin T) (a : ℝ) :
    (∑ t, W t * rpeIndicator B W r t * (if B i t = a then (1 : ℝ) else 0))
      = ∑ t, W t * rpeIndicator B W r t * (if B j t = a then (1 : ℝ) else 0) := by
  classical
  have cvt : ∀ b : Fin T,
      (∑ t, W t * rpeIndicator B W r t * (if B b t = a then (1 : ℝ) else 0))
        = ∑ t ∈ Finset.univ.filter (fun t => B b t = a), W t * rpeIndicator B W r t := by
    intro b
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun t _ => by rw [mul_ite, mul_one, mul_zero]
  rw [cvt i, cvt j]
  exact classwise_rowValueMeasure_eq_of_rootedProfileEquiv B hB W hW h r a

/-- The total `W`-mass of the atom class of `r` (`= ∑_{t ∈ atom(r)} W t`). -/
noncomputable def atomWeight {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (r : Fin T) : ℝ :=
  ∑ t, W t * rpeIndicator B W r t

/-- Every atom class has positive `W`-weight (it contains its representative `r`,
and `W r > 0`). -/
theorem atomWeight_pos {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (hW : ∀ t, 0 < W t)
    (r : Fin T) : 0 < atomWeight B W r := by
  classical
  unfold atomWeight
  refine Finset.sum_pos' (fun t _ => ?_) ⟨r, Finset.mem_univ r, ?_⟩
  · exact mul_nonneg (hW t).le (by unfold rpeIndicator; split_ifs <;> norm_num)
  · rw [show rpeIndicator B W r r = 1 from by
      unfold rpeIndicator; rw [if_pos (rootedProfileEquiv.refl B W r)]]
    simpa using hW r

/-- **Atom transition measure**: the `W`-mass of the value-`a` fibre of row `B i`
inside atom class `atom(q)`. (The source atom is the atom of `i`.) -/
noncomputable def atomTransMeasure {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (q i : Fin T) (a : ℝ) : ℝ :=
  ∑ t, W t * rpeIndicator B W q t * (if B i t = a then (1 : ℝ) else 0)

/-- **Coherence**: the atom transition measure depends only on the ATOM of `i`, not
the chosen representative — the coherent-configuration condition. -/
theorem atomTransMeasure_eq_of_rpe {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ t, 0 < W t) {i j : Fin T} (h : rootedProfileEquiv B W i j)
    (q : Fin T) (a : ℝ) :
    atomTransMeasure B W q i a = atomTransMeasure B W q j a :=
  atom_row_value_measure_eq B hB W hW h q a

/-- **Row signature equality inside atoms** (the coherent-configuration object):
rpe-equivalent rows `B i`, `B j` have the SAME atom-restricted value distribution
(`a ↦ atomTransMeasure q i a`) for every target atom `q`. -/
theorem atom_row_signature_eq {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ t, 0 < W t) {i j : Fin T} (h : rootedProfileEquiv B W i j) :
    ∀ q : Fin T, (fun a => atomTransMeasure B W q i a) = fun a => atomTransMeasure B W q j a :=
  fun q => funext fun a => atomTransMeasure_eq_of_rpe B hB W hW h q a

/-! ### §7 — atoms = orbits (#70 paper-root), via the DIRECT multigraph route

The #70 rank theorem `vertexOrbitRel_of_rootedProfileEquiv` factors through the
PROVED, axiom-clean multigraph Lemma 2.4 `tupleEquivMulti_implies_orbit`:

  `rootedProfileEquiv → tupleEquivMulti → vertexOrbitRel`.

The middle arrow is the ONLY remaining content — the focused bridge
`tupleEquivMulti_of_rootedProfileEquiv` (simple-rpe ⟹ multigraph tuple-equivalence
at K=1). No marker/augmentation is needed: `tupleEquivMulti` uses the SAME `(B,W)`,
with multigraphs as the PROBES. These declarations were relocated here from
`SimpleRank.lean` (they have no upstream consumers) because the bridge's eventual
proof uses the decorated/classwise power-sum machinery defined above. -/

/-- **Tree-fragment, base case**: the multiplicity-`a` star probe descends — its
evaluation is the `a`-th weighted power sum, which descends by `powerSum_descends`. -/
theorem starProbe_descends {T : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ t, 0 < W t) {i j : Fin T} (h : rootedProfileEquiv B W i j) (a : ℕ) :
    multiLabeledEvalK 1 1 (starProbe a) B W (fun _ => i)
      = multiLabeledEvalK 1 1 (starProbe a) B W (fun _ => j) := by
  rw [multiLabeledEvalK_starProbe B hB W i a, multiLabeledEvalK_starProbe B hB W j a]
  exact powerSum_descends_of_rootedProfileEquiv B hB W hW h a

/-- **Tree-fragment, inductive step**: if the sub-probe `Mχ` descends (its evaluation
is atom-invariant), then the decorated star probe `decoratedProbe a Mχ` descends. Its
evaluation `∑ₜ W t · B i t ^ a · χ(t)` is a decorated power sum with `χ` in the span
(`of_const_on_rpe`), so `decoratedPowerSum_descends` applies. Together with
`starProbe_descends` this gives, by induction on tree depth, that EVERY tree (= WL)
multigraph probe descends — the part of `tupleEquivMulti_of_rootedProfileEquiv` already
in reach. -/
theorem decoratedProbe_descends {T m : ℕ} (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ t, 0 < W t) (a : ℕ) (Mχ : MultiLabeledGraph 1 m)
    (hχ : ∀ p q : Fin T, rootedProfileEquiv B W p q →
      multiLabeledEvalK 1 m Mχ B W (fun _ => p) = multiLabeledEvalK 1 m Mχ B W (fun _ => q))
    {i j : Fin T} (h : rootedProfileEquiv B W i j) :
    multiLabeledEvalK 1 (m + 1) (decoratedProbe a Mχ) B W (fun _ => i)
      = multiLabeledEvalK 1 (m + 1) (decoratedProbe a Mχ) B W (fun _ => j) := by
  rw [multiLabeledEvalK_decoratedProbe a Mχ B hB W i,
      multiLabeledEvalK_decoratedProbe a Mχ B hB W j]
  have hspan : InRootedProfileSpan B W (fun t => multiLabeledEvalK 1 m Mχ B W (fun _ => t)) :=
    InRootedProfileSpan.of_const_on_rpe B hB W _ hχ
  have hdec := decoratedPowerSum_descends_of_rootedProfileEquiv B hB W hW h hspan a
  calc ∑ t, W t * B i t ^ a * multiLabeledEvalK 1 m Mχ B W (fun _ => t)
      = ∑ t, W t * multiLabeledEvalK 1 m Mχ B W (fun _ => t) * B i t ^ a :=
        Finset.sum_congr rfl fun t _ => by ring
    _ = ∑ t, W t * multiLabeledEvalK 1 m Mχ B W (fun _ => t) * B j t ^ a := hdec
    _ = ∑ t, W t * B j t ^ a * multiLabeledEvalK 1 m Mχ B W (fun _ => t) :=
        Finset.sum_congr rfl fun t _ => by ring

/-- **Base case (simple `M`)**: a 0/1-multigraph `ofSimple F` evaluates to the rooted
profile of `F`, so it lies in the span directly (`of_profile`). -/
theorem rootedMultiEval_ofSimple_mem {T n : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj] :
    InRootedProfileSpan B W
      (fun v => multiLabeledEvalK 1 n (MultiLabeledGraph.ofSimple F) B W (fun _ => v)) := by
  have heq : (fun v => multiLabeledEvalK 1 n (MultiLabeledGraph.ofSimple F) B W (fun _ => v))
      = rootedProfileFun B W F := by
    funext v; rw [multiLabeledEvalK_ofSimple]; rfl
  rw [heq]; exact InRootedProfileSpan.of_profile B W F

/-- **Base case (root-incident multi-edge / power sum)**: the multiplicity-`a` star
probe evaluates to `∑ₜ W t · B v t ^ a`, atom-invariant by `powerSum_descends`, hence
in the span by `of_const_on_rpe` (non-circular — the descent is independently proved). -/
theorem rootedMultiEval_starProbe_mem {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (hW : ∀ t, 0 < W t) (a : ℕ) :
    InRootedProfileSpan B W
      (fun v => multiLabeledEvalK 1 1 (starProbe a) B W (fun _ => v)) :=
  InRootedProfileSpan.of_const_on_rpe B hB W _
    (fun _ _ h => starProbe_descends B hB W hW h a)

/-- **Base case (tree / decorated probe)**: if the sub-probe `Mχ` lies in the span,
so does `decoratedProbe a Mχ` — atom-invariance via `decoratedProbe_descends`
(using `const_on_rpe` of the `Mχ`-membership), then `of_const_on_rpe`. -/
theorem rootedMultiEval_decoratedProbe_mem {T m : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (hW : ∀ t, 0 < W t) (a : ℕ)
    (Mχ : MultiLabeledGraph 1 m)
    (hMχ : InRootedProfileSpan B W (fun v => multiLabeledEvalK 1 m Mχ B W (fun _ => v))) :
    InRootedProfileSpan B W
      (fun v => multiLabeledEvalK 1 (m + 1) (decoratedProbe a Mχ) B W (fun _ => v)) :=
  InRootedProfileSpan.of_const_on_rpe B hB W _
    (fun _ _ h => decoratedProbe_descends B hB W hW a Mχ
      (fun _ _ hpq => hMχ.const_on_rpe hpq) h)

/-- **Warm-up diagonal primitive** (one neighbour, PROVED): for `g, h` in the span,
the "same-vertex" decorated first moment `v ↦ ∑ₛ W s · B v s · g s · h s` lies in the
span — via `InRootedProfileSpan.mul` then `.weightedAdj`. This extracts a coincidence
at ONE neighbour; the internal doubled edge needs the two-variable coincidence
detector (`tupleEquivSimple_preserves_diagonal`). -/
theorem rootedProfileSpan_pairDiagonal {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) {g h : Fin T → ℝ}
    (hg : InRootedProfileSpan B W g) (hh : InRootedProfileSpan B W h) :
    InRootedProfileSpan B W (fun v => ∑ s, W s * B v s * g s * h s) := by
  have heq : (fun v => ∑ s, W s * B v s * g s * h s)
      = weightedAdj B W (fun s => g s * h s) := by
    funext v
    simp only [Graphon.Lovasz.weightedAdj]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [heq]
  exact InRootedProfileSpan.weightedAdj hB (InRootedProfileSpan.mul hB hg hh)

/-- **Common-neighbour simple graph**: two labels `0, 1` both joined to the single
unlabeled vertex `2` (no `0–1` edge). Its rooted evaluation reads `⟨B(ξ 0), B(ξ 1)⟩_W`. -/
def commonNeighborGraph : SimpleGraph (Fin (1 + 2)) :=
  SimpleGraph.fromEdgeSet {s(0, 2), s(1, 2)}

noncomputable instance : DecidableRel commonNeighborGraph.Adj :=
  Classical.decRel _

theorem commonNeighborGraph_edgeFinset :
    commonNeighborGraph.edgeFinset = {s((0 : Fin (1 + 2)), 2), s((1 : Fin (1 + 2)), 2)} := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, commonNeighborGraph, SimpleGraph.edgeSet_fromEdgeSet,
    Finset.mem_insert, Finset.mem_singleton, Set.mem_diff, Set.mem_insert_iff,
    Set.mem_singleton_iff, Sym2.mem_diagSet_iff_isDiag]
  refine ⟨fun ⟨he, _⟩ => he, fun he => ⟨he, ?_⟩⟩
  rcases he with he | he <;> rw [he, Sym2.mk_isDiag_iff] <;> decide

/-- **Common-neighbour evaluation**: `simpleEvalAt commonNeighborGraph ξ = ∑ₜ W t · B (ξ 0) t · B (ξ 1) t`
`= ⟨B (ξ 0), B (ξ 1)⟩_W`. -/
theorem simpleEvalAt_commonNeighbor {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (ξ : Fin 2 → Fin T) :
    simpleEvalAt B W commonNeighborGraph ξ = ∑ t, W t * B (ξ 0) t * B (ξ 1) t := by
  rw [show (∑ t, W t * B (ξ 0) t * B (ξ 1) t)
      = ∑ σ : Fin 1 → Fin T, W (σ 0) * B (ξ 0) (σ 0) * B (ξ 1) (σ 0) from
    (Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin T))
      (fun t => W t * B (ξ 0) t * B (ξ 1) t)).symm]
  unfold simpleEvalAt
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [commonNeighborGraph_edgeFinset, Fin.prod_univ_one]
  show W (σ 0) *
      ∏ e ∈ ({s((0 : Fin (1 + 2)), 2), s((1 : Fin (1 + 2)), 2)} : Finset (Sym2 (Fin (1 + 2)))),
        B ((fun v : Fin (1 + 2) => if h : (v : ℕ) < 2 then ξ ⟨v, h⟩
              else σ ⟨v - 2, by have := v.isLt; omega⟩) (Quot.out e).1)
          ((fun v : Fin (1 + 2) => if h : (v : ℕ) < 2 then ξ ⟨v, h⟩
              else σ ⟨v - 2, by have := v.isLt; omega⟩) (Quot.out e).2)
      = W (σ 0) * B (ξ 0) (σ 0) * B (ξ 1) (σ 0)
  rw [Finset.prod_pair (show s((0 : Fin (1 + 2)), 2) ≠ s((1 : Fin (1 + 2)), 2) by decide),
    out_pair_eq' B hB (fun v : Fin (1 + 2) => if h : (v : ℕ) < 2 then ξ ⟨v, h⟩
        else σ ⟨v - 2, by have := v.isLt; omega⟩) 0 2,
    out_pair_eq' B hB (fun v : Fin (1 + 2) => if h : (v : ℕ) < 2 then ξ ⟨v, h⟩
        else σ ⟨v - 2, by have := v.isLt; omega⟩) 1 2]
  show W (σ 0) * (B (ξ 0) (σ 0) * B (ξ 1) (σ 0)) = W (σ 0) * B (ξ 0) (σ 0) * B (ξ 1) (σ 0)
  ring

/-- **Coincidence detector** (`tupleEquivSimple` preserves the diagonal) — the KEY
book step for internal multi-edge elimination (FOCUSED SORRY). If two `2`-tuples are
simple-equivalent and one is diagonal (`ξ 0 = ξ 1`), so is the other.

**Mechanism (non-circular, settled)**: instantiate `tupleEquivSimple` at the
common-neighbour simple graph (two labels both joined to one unlabeled vertex),
whose eval is `⟨B (ξ 0), B (ξ 1)⟩_W = ∑ᵤ W u · B (ξ 0) u · B (ξ 1) u`. For diagonal
`ξ` (so `ξ 0 = ξ 1 = s`) this and the single-label squares give
`⟨B (ξ' 0), B (ξ' 1)⟩_W = ‖B (ξ' 0)‖²_W = ‖B (ξ' 1)‖²_W = sqMoment s` (single-label
restriction + `sqMoment_descends`), whence `‖B (ξ' 0) − B (ξ' 1)‖²_W = s − 2s + s = 0`,
so `B (ξ' 0) = B (ξ' 1)` (positive `W`); **twin-free** then forces `ξ' 0 = ξ' 1`.
Uses only proved tools. Consequence: the diagonal indicator is constant on
`tupleEquivSimple`-classes ⟹ in the simple closure (`of_const_on_tupleEquivSimple`,
the Lagrange-over-values step), the primitive that extracts the internal `B s t²`. -/
theorem tupleEquivSimple_preserves_diagonal {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (hW : ∀ t, 0 < W t)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    {ξ ξ' : Fin 2 → Fin T} (h : tupleEquivSimple B W ξ ξ') :
    (ξ 0 = ξ 1) ↔ (ξ' 0 = ξ' 1) := by
  have fwd : ∀ (η η' : Fin 2 → Fin T), tupleEquivSimple B W η η' → η 0 = η 1 → η' 0 = η' 1 := by
    intro η η' hh hdiag
    -- common-neighbour eval agrees:  ⟨B(η0),B(η1)⟩_W = ⟨B(η'0),B(η'1)⟩_W
    have hcn : (∑ t, W t * B (η 0) t * B (η 1) t) = ∑ t, W t * B (η' 0) t * B (η' 1) t := by
      rw [← simpleEvalAt_commonNeighbor B hB W η, ← simpleEvalAt_commonNeighbor B hB W η']
      exact hh 1 commonNeighborGraph
    -- single-label restriction gives rpe, hence square-moment equality
    have rpeAt : ∀ a : Fin 2, rootedProfileEquiv B W (η a) (η' a) := by
      intro a n F _
      exact tupleEquivSimple_restrict_along B W hB
        (⟨fun _ : Fin 1 => a, fun x y _ => Subsingleton.elim x y⟩ : Fin 1 ↪ Fin 2) hh n F
    have hsq0 : (∑ t, W t * B (η' 0) t ^ 2) = ∑ t, W t * B (η 1) t ^ 2 := by
      have hd := sqMoment_descends_of_rootedProfileEquiv B hB W hW (rpeAt 0)
      unfold sqMoment at hd; rw [hdiag] at hd; exact hd.symm
    have hsq1 : (∑ t, W t * B (η' 1) t ^ 2) = ∑ t, W t * B (η 1) t ^ 2 := by
      have hd := sqMoment_descends_of_rootedProfileEquiv B hB W hW (rpeAt 1)
      unfold sqMoment at hd; exact hd.symm
    rw [hdiag] at hcn
    have hD : (∑ t, W t * B (η' 0) t * B (η' 1) t) = ∑ t, W t * B (η 1) t ^ 2 := by
      rw [← hcn]; exact Finset.sum_congr rfl fun t _ => by ring
    -- ‖B(η'0) − B(η'1)‖²_W = 0
    have hnorm : (∑ t, W t * (B (η' 0) t - B (η' 1) t) ^ 2) = 0 := by
      have e1 : (∑ t, W t * B (η' 0) t ^ 2) + (∑ t, W t * B (η' 1) t ^ 2)
          - 2 * (∑ t, W t * B (η' 0) t * B (η' 1) t)
          = ∑ t, W t * (B (η' 0) t - B (η' 1) t) ^ 2 := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun t _ => by ring
      rw [← e1, hsq0, hsq1, hD]; ring
    -- positive weights ⟹ rows equal
    have hrows : B (η' 0) = B (η' 1) := by
      funext t
      have hnn : ∀ s ∈ (Finset.univ : Finset (Fin T)),
          0 ≤ W s * (B (η' 0) s - B (η' 1) s) ^ 2 :=
        fun s _ => mul_nonneg (hW s).le (sq_nonneg _)
      have ht := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hnorm t (Finset.mem_univ t)
      have hsq : (B (η' 0) t - B (η' 1) t) ^ 2 = 0 := by
        rcases mul_eq_zero.mp ht with hw | hs
        · exact absurd hw (ne_of_gt (hW t))
        · exact hs
      have hz : B (η' 0) t - B (η' 1) t = 0 := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hsq
      linarith
    -- twin-free ⟹ the labels coincide
    by_contra hne
    exact htwin (η' 0) (η' 1) hne hrows
  have hsymm : tupleEquivSimple B W ξ' ξ := by intro n' F _inst; exact (h n' F).symm
  exact ⟨fwd ξ ξ' h, fwd ξ' ξ hsymm⟩

/-- **Rooted multigraph evaluations lie in the simple rooted-profile span**
(THE #70 paper-root, FOCUSED SORRY — the K=1 case of `InTupleMultiEvalSpan.toSimple`,
i.e. Lovász Lemma 2.5 specialized to a single root). For every rooted multigraph
probe `M`, the function `v ↦ multiLabeledEvalK 1 n M B W (·↦v)` lies in
`InRootedProfileSpan B W`. This is the clean algebraic form of the remaining #70
content: membership in the simple algebra, NOT obstruction-by-obstruction identities.

**Base cases already in reach** (membership is NON-circular for these, because their
descent is independently PROVED, so `of_const_on_rpe` applies):
- simple `M = ofSimple F`: the eval IS `rootedProfileFun B W F` ⟹ `of_profile`;
- tree/decorated `M` (`decoratedProbe`/`starProbe`/`glue`): `decoratedProbe_descends`
  + `starProbe_descends` give atom-invariance ⟹ `of_const_on_rpe`;
- root-incident multi-edge powers (`starProbe a`): `powerSum_descends` ⟹ `of_const_on_rpe`.

**Open core** (the genuine §3 residue = the Hadamard-square obstruction): an INTERNAL
multi-edge (multiplicity ≥2 between two UNLABELED vertices) — the simplest is the
multi-triangle `∑_{s,t} W s W t B(v,s) B(v,t) B(s,t)^c`. The paper-style induction must
eliminate one internal multiplicity at a time via finite-algebra closure, NOT
`of_const_on_rpe` (which would reduce membership back to the target — circular). The
numerical probe (`scripts/multitriangle_*.py`) confirms this descent IS forced at
finite depth (MU≥3), so the theorem is TRUE and finite; the missing book lemma is the
K=1 multi-edge-elimination step of Lemma 2.5. -/
theorem rootedMultiEval_mem_rootedProfileSpan {T n : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (hW : ∀ t, 0 < W t)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j) (M : MultiLabeledGraph 1 n) :
    InRootedProfileSpan B W (fun v => multiLabeledEvalK 1 n M B W (fun _ => v)) := by
  sorry

/-- **The simple → multigraph bridge at K=1** (PROVED modulo
`rootedMultiEval_mem_rootedProfileSpan`). Rooted simple-profile equivalence implies
MULTIGRAPH tuple-equivalence: every multigraph probe evaluates identically on
rpe-equivalent vertices. Immediate from membership of each rooted multigraph eval in
the simple span (`rootedMultiEval_mem_rootedProfileSpan`) and the fact that span
elements are constant on rpe-classes (`InRootedProfileSpan.const_on_rpe`). -/
theorem tupleEquivMulti_of_rootedProfileEquiv {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (hW : ∀ t, 0 < W t)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    {i j : Fin T} (h : rootedProfileEquiv B W i j) :
    tupleEquivMulti B W (fun _ : Fin 1 => i) (fun _ : Fin 1 => j) := by
  intro n M
  exact (rootedMultiEval_mem_rootedProfileSpan B hB W hW htwin M).const_on_rpe h

/-- **The K=1 simple-graph rank theorem** (#70): rooted-profile equivalence implies
vertex-orbit equivalence — the atoms of the rooted simple-profile algebra are exactly
the `(B, W)`-automorphism orbits. PROVED modulo the single focused bridge
`tupleEquivMulti_of_rootedProfileEquiv`, via the proved multigraph Lemma 2.4. -/
theorem vertexOrbitRel_of_rootedProfileEquiv {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    {i j : Fin T} (h : rootedProfileEquiv B W i j) :
    vertexOrbitRel B W i j := by
  obtain ⟨σ, haut, hσ⟩ := tupleEquivMulti_implies_orbit B hB W hW htwin
    (tupleEquivMulti_of_rootedProfileEquiv B hB W hW htwin h)
  exact ⟨σ, haut, (hσ 0).symm⟩

/-- **Atoms = orbits**, packaged form of the rank theorem. PROVED modulo
`tupleEquivMulti_of_rootedProfileEquiv` (via `vertexOrbitRel_of_rootedProfileEquiv`). -/
theorem algebraAtomRel_eq_vertexOrbitRel {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j) (i j : Fin T) :
    algebraAtomRel B W i j ↔ vertexOrbitRel B W i j := by
  rw [algebraAtomRel_iff_rootedProfileEquiv]
  exact ⟨vertexOrbitRel_of_rootedProfileEquiv B hB W hW htwin,
    rootedProfileEquiv_of_vertexOrbitRel B W⟩

/-- **Non-circular `of_const_on_orbit`** — an orbit-invariant function is
atom-invariant (atoms = orbits) hence in the span (`of_const_on_rpe`). Replaces the
cyclically-proved `InRootedProfileSpan.of_const_on_orbit` in `Lovasz.lean`. PROVED
modulo `tupleEquivMulti_of_rootedProfileEquiv`. -/
theorem InRootedProfileSpan.of_const_on_orbit_noncircular {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (f : Fin T → ℝ)
    (hf : ∀ i j, vertexOrbitRel B W i j → f i = f j) :
    InRootedProfileSpan B W f :=
  InRootedProfileSpan.of_const_on_rpe B hB W f (fun i j hij =>
    hf i j (vertexOrbitRel_of_rootedProfileEquiv B hB W hW htwin hij))

end Weighted

end Graphon.Lovasz
