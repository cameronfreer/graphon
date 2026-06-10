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
