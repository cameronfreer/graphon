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
  sorry

/-- **Weighted power sums descend** (k ≤ 3 reduced: k ≤ 2 PROVED, k = 3 via
`cubeMoment_descends_of_rootedProfileEquiv`; k ≥ 4 SORRY — the general
Hadamard-power lift, to be attacked after the cube validates the method).

Once proved for all `k`, `weighted_powersum_determines_measure` upgrades this
to equality of `W`-weighted row-value measures, the key step toward the rank
theorem `vertexOrbitRel_of_rootedProfileEquiv`. -/
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
    sorry

/-- **Row-value measures descend** (proved modulo the `k ≥ 3` power sums):
under rooted-profile equivalence, the `W`-weighted preimage masses of the two
rows agree at every value — the rows are equal as weighted value measures. -/
theorem rowValueMeasure_eq_of_rootedProfileEquiv {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ t, 0 < W t)
    {i j : Fin T} (h : rootedProfileEquiv B W i j) (a : ℝ) :
    (∑ t ∈ Finset.univ.filter (fun t => B i t = a), W t) =
      ∑ t ∈ Finset.univ.filter (fun t => B j t = a), W t :=
  weighted_powersum_determines_measure (B i) (B j) W
    (powerSum_descends_of_rootedProfileEquiv B hB W hW h) a

end Weighted

end Graphon.Lovasz
