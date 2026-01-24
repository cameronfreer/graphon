/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Tactic.Linarith

/-!
# Graphons

A graphon is a symmetric measurable function `W : [0,1]² → [0,1]` that represents
the limit of a convergent sequence of dense graphs.

This file introduces graphons parameterized by a probability space `(α, μ)`, using
`AEEqFun` (almost-everywhere equal functions) to handle the quotient by a.e. equality.

## Main definitions

* `SymmKernel` - A symmetric kernel: element of L⁰(α × α, ℝ) symmetric a.e.
  (general measure, used as base type)
* `Graphon` - A graphon over a probability space: symmetric kernel with values in [0,1] a.e.
* `SignedGraphon` - Signed graphon: |W| ≤ 1 a.e. For cut distance calculations.
* `GraphonI` - Canonical graphon type on the unit interval with Lebesgue measure

## Design notes

We parameterize `Graphon` and `SignedGraphon` by a probability space `(α, μ)` with
`[IsProbabilityMeasure μ]`, following Lovász's normalization convention. The canonical
type `GraphonI` uses the unit interval with Lebesgue measure. The base type `SymmKernel`
is defined for general measures to allow reuse in other contexts.

We use `AEEqFun` to represent kernels as elements of L⁰, which gives us automatic
quotienting by a.e. equality. We use `ℝ` as the codomain (rather than `Set.Icc 0 1`)
to enable subtraction for cut distance calculations.

The `IsProbabilityMeasure` assumption ensures:
- The product measure `μ.prod μ` is also a probability measure
- Swap is measure-preserving (`μ.prod μ` is symmetric)
- Integrals are normalized (important for homomorphism densities)

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012]
-/

open MeasureTheory Set Filter unitInterval

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ### Helper lemmas for product measure symmetry -/

/-- If a property holds a.e. for the product measure μ × μ, then it also holds
a.e. when composed with swap, since swap is measure-preserving. -/
lemma ae_prod_swap [SFinite μ] {P : α × α → Prop} (hP : ∀ᵐ p ∂(μ.prod μ), P p) :
    ∀ᵐ p ∂(μ.prod μ), P p.swap :=
  (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hP

/-- A symmetric kernel: an element of L⁰(α × α, ℝ) that is symmetric a.e.

This is the base type for both graphons (values in [0,1]) and signed kernels
(values in [-1,1]). The symmetry condition `W(x,y) = W(y,x)` holds almost
everywhere with respect to the product measure.

Note: This type is defined for general measures. For the swap-invariance of a.e.
properties to hold, the measure should be `SFinite`. The subtypes `Graphon` and
`SignedGraphon` are intended for use with probability measures. -/
structure SymmKernel (α : Type*) [MeasurableSpace α] (μ : Measure α) where
  /-- The underlying almost-everywhere equal function class -/
  toAEEqFun : (α × α) →ₘ[μ.prod μ] ℝ
  /-- The function is symmetric a.e.: W(x,y) = W(y,x) for a.e. (x,y) -/
  symm' : ∀ᵐ p ∂(μ.prod μ), toAEEqFun p.swap = toAEEqFun p

/-- A graphon: a symmetric kernel with values in [0,1] almost everywhere.

This represents the limit object for sequences of dense graphs. The domain is
a probability space `(α, μ)`. Operations on graphons require `[IsProbabilityMeasure μ]`
to ensure proper normalization and measure-theoretic properties.

The `IsProbabilityMeasure` constraint ensures:
- `μ.prod μ` is a probability measure on the product space
- Swap is measure-preserving (needed for symmetry properties)
- Integrals give meaningful densities -/
structure Graphon (α : Type*) [MeasurableSpace α] (μ : Measure α)
    extends SymmKernel α μ where
  /-- Values lie in [0,1] a.e. -/
  ae_mem_Icc : ∀ᵐ p ∂(μ.prod μ), toAEEqFun p ∈ Icc 0 1

/-- A signed graphon: a symmetric kernel with |W| ≤ 1 almost everywhere.

Used for cut distance calculations, where we need to consider differences of graphons.
The bound |W| ≤ 1 is preserved under taking differences of graphons.

Like `Graphon`, operations require `[IsProbabilityMeasure μ]`. -/
structure SignedGraphon (α : Type*) [MeasurableSpace α] (μ : Measure α)
    extends SymmKernel α μ where
  /-- Absolute value bounded by 1 a.e. -/
  ae_abs_le_one : ∀ᵐ p ∂(μ.prod μ), |toAEEqFun p| ≤ 1

/-! ### Canonical graphon type -/

/-- The canonical graphon type on the unit interval with Lebesgue measure.

This is the standard space for graphons in the literature. We use `I` (= `Set.Icc 0 1`)
as the underlying type, which carries the subtype measure from Lebesgue measure on ℝ. -/
abbrev GraphonI := Graphon I (volume : Measure I)

/-! ### Coercions and instances for SymmKernel -/

namespace SymmKernel

instance : CoeFun (SymmKernel α μ) (fun _ => (α × α) →ₘ[μ.prod μ] ℝ) :=
  ⟨toAEEqFun⟩

/-- Symmetric kernels are equal if their underlying AEEqFun are equal. -/
@[ext]
theorem ext {W₁ W₂ : SymmKernel α μ} (h : W₁.toAEEqFun = W₂.toAEEqFun) : W₁ = W₂ := by
  cases W₁; cases W₂; simp only [mk.injEq]; exact h

/-- The symmetry property: W(x,y) = W(y,x) a.e. -/
theorem symm_ae (W : SymmKernel α μ) : ∀ᵐ p ∂(μ.prod μ), W.toAEEqFun p.swap = W.toAEEqFun p :=
  W.symm'

end SymmKernel

/-! ### Coercions and instances for Graphon -/

namespace Graphon

instance : CoeFun (Graphon α μ) (fun _ => (α × α) →ₘ[μ.prod μ] ℝ) :=
  ⟨fun W => W.toSymmKernel.toAEEqFun⟩

/-- Coercion from Graphon to SymmKernel. -/
instance : Coe (Graphon α μ) (SymmKernel α μ) :=
  ⟨toSymmKernel⟩

/-- Graphons are equal if their underlying SymmKernels are equal. -/
@[ext]
theorem ext {W₁ W₂ : Graphon α μ} (h : W₁.toSymmKernel = W₂.toSymmKernel) : W₁ = W₂ := by
  cases W₁; cases W₂; simp only [mk.injEq]; exact h

/-- Values are non-negative a.e. -/
theorem ae_nonneg (W : Graphon α μ) : ∀ᵐ p ∂(μ.prod μ), 0 ≤ W.toAEEqFun p :=
  W.ae_mem_Icc.mono fun _ h => h.1

/-- Values are at most 1 a.e. -/
theorem ae_le_one (W : Graphon α μ) : ∀ᵐ p ∂(μ.prod μ), W.toAEEqFun p ≤ 1 :=
  W.ae_mem_Icc.mono fun _ h => h.2

/-- The symmetry property for graphons: W(x,y) = W(y,x) a.e. -/
theorem symm_ae (W : Graphon α μ) : ∀ᵐ p ∂(μ.prod μ), W.toAEEqFun p.swap = W.toAEEqFun p :=
  W.toSymmKernel.symm_ae

/-! ### Constant graphons -/

variable [IsProbabilityMeasure μ]

/-- The constant zero graphon. Represents the limit of empty graphs. -/
def zero : Graphon α μ where
  toAEEqFun := AEEqFun.const (α × α) 0
  symm' := by
    have h1 : ∀ᵐ p ∂(μ.prod μ), (AEEqFun.const (α × α) (0 : ℝ) : (α × α) →ₘ[μ.prod μ] ℝ) p = 0 :=
      (AEEqFun.coeFn_const (α × α) (0 : ℝ)).mono fun p hp => hp
    have h2 := ae_prod_swap h1
    filter_upwards [h1, h2] with p hp1 hp2
    rw [hp1, hp2]
  ae_mem_Icc := by
    filter_upwards [AEEqFun.coeFn_const (α × α) (0 : ℝ)] with p hp
    simp only [Function.const_apply, mem_Icc] at hp ⊢
    rw [hp]
    exact ⟨le_refl 0, zero_le_one⟩

/-- The constant one graphon. Represents the limit of complete graphs. -/
def one : Graphon α μ where
  toAEEqFun := AEEqFun.const (α × α) 1
  symm' := by
    have h1 : ∀ᵐ p ∂(μ.prod μ), (AEEqFun.const (α × α) (1 : ℝ) : (α × α) →ₘ[μ.prod μ] ℝ) p = 1 :=
      (AEEqFun.coeFn_const (α × α) (1 : ℝ)).mono fun p hp => hp
    have h2 := ae_prod_swap h1
    filter_upwards [h1, h2] with p hp1 hp2
    rw [hp1, hp2]
  ae_mem_Icc := by
    filter_upwards [AEEqFun.coeFn_const (α × α) (1 : ℝ)] with p hp
    simp only [Function.const_apply, mem_Icc] at hp ⊢
    rw [hp]
    exact ⟨zero_le_one, le_refl 1⟩

theorem zero_toAEEqFun : (zero : Graphon α μ).toAEEqFun = AEEqFun.const (α × α) 0 := rfl

theorem one_toAEEqFun : (one : Graphon α μ).toAEEqFun = AEEqFun.const (α × α) 1 := rfl

/-! ### Complement -/

/-- The complement of a graphon: (1 - W). If W represents graph G, then compl W
represents the complement graph Ḡ. -/
def compl (W : Graphon α μ) : Graphon α μ where
  toAEEqFun := AEEqFun.const (α × α) 1 - W.toAEEqFun
  symm' := by
    have hsub_ae : ∀ᵐ p ∂(μ.prod μ),
        (AEEqFun.const (α × α) 1 - W.toAEEqFun : (α × α) →ₘ[μ.prod μ] ℝ) p =
        (AEEqFun.const (α × α) (1 : ℝ) : (α × α) →ₘ[μ.prod μ] ℝ) p - W.toAEEqFun p :=
      AEEqFun.coeFn_sub (AEEqFun.const (α × α) 1) W.toAEEqFun
    have hsub_swap := ae_prod_swap hsub_ae
    have hconst_ae : ∀ᵐ p ∂(μ.prod μ),
        (AEEqFun.const (α × α) (1 : ℝ) : (α × α) →ₘ[μ.prod μ] ℝ) p = 1 :=
      (AEEqFun.coeFn_const (α × α) (1 : ℝ)).mono fun p hp => hp
    have hconst_swap := ae_prod_swap hconst_ae
    filter_upwards [W.symm_ae, hsub_ae, hsub_swap, hconst_ae, hconst_swap]
      with p hW hsub hsub_s hc hc_s
    rw [hsub_s, hsub, hc_s, hc, hW]
  ae_mem_Icc := by
    filter_upwards [W.ae_mem_Icc,
      AEEqFun.coeFn_sub (AEEqFun.const (α × α) 1) W.toAEEqFun,
      AEEqFun.coeFn_const (α × α) (1 : ℝ)] with p hp hsub hc
    simp only [Pi.sub_apply, Function.const_apply, mem_Icc] at hp hsub hc ⊢
    rw [hsub, hc]
    constructor
    · linarith [hp.2]
    · linarith [hp.1]

@[simp]
theorem compl_compl (W : Graphon α μ) : W.compl.compl = W := by
  ext
  simp only [compl]
  rw [sub_sub_cancel]

@[simp]
theorem compl_zero : (zero : Graphon α μ).compl = one := by
  ext
  simp only [compl, zero, one]
  filter_upwards [AEEqFun.coeFn_sub (AEEqFun.const (α × α) (1 : ℝ)) (AEEqFun.const (α × α) (0 : ℝ)),
    AEEqFun.coeFn_const (α × α) (1 : ℝ), AEEqFun.coeFn_const (α × α) (0 : ℝ)] with p hsub h1 h0
  simp only [Pi.sub_apply, Function.const_apply] at hsub h1 h0 ⊢
  rw [hsub, h1, h0, sub_zero]

@[simp]
theorem compl_one : (one : Graphon α μ).compl = zero := by
  ext
  simp only [compl, zero, one]
  filter_upwards [AEEqFun.coeFn_sub (AEEqFun.const (α × α) (1 : ℝ)) (AEEqFun.const (α × α) (1 : ℝ)),
    AEEqFun.coeFn_const (α × α) (1 : ℝ), AEEqFun.coeFn_const (α × α) (0 : ℝ)] with p hsub h1 h0
  simp only [Pi.sub_apply, Function.const_apply] at hsub h1 h0 ⊢
  rw [hsub, h1, sub_self, h0]

end Graphon

/-! ### Coercions and instances for SignedGraphon -/

namespace SignedGraphon

instance : CoeFun (SignedGraphon α μ) (fun _ => (α × α) →ₘ[μ.prod μ] ℝ) :=
  ⟨fun W => W.toSymmKernel.toAEEqFun⟩

/-- Coercion from SignedGraphon to SymmKernel. -/
instance : Coe (SignedGraphon α μ) (SymmKernel α μ) :=
  ⟨toSymmKernel⟩

/-- SignedGraphons are equal if their underlying SymmKernels are equal. -/
@[ext]
theorem ext {W₁ W₂ : SignedGraphon α μ} (h : W₁.toSymmKernel = W₂.toSymmKernel) : W₁ = W₂ := by
  cases W₁; cases W₂; simp only [mk.injEq]; exact h

variable [IsProbabilityMeasure μ]

/-- Create a signed graphon from a graphon. Since graphon values are in [0,1],
the absolute value is automatically bounded by 1. -/
def ofGraphon (W : Graphon α μ) : SignedGraphon α μ where
  toSymmKernel := W.toSymmKernel
  ae_abs_le_one := by
    filter_upwards [W.ae_mem_Icc] with p hp
    rw [abs_le]
    constructor
    · linarith [hp.1]
    · exact hp.2

/-- The difference of two graphons is a signed graphon. -/
def sub (W₁ W₂ : Graphon α μ) : SignedGraphon α μ where
  toAEEqFun := W₁.toAEEqFun - W₂.toAEEqFun
  symm' := by
    have hsub_ae := AEEqFun.coeFn_sub W₁.toAEEqFun W₂.toAEEqFun
    have hsub_swap := ae_prod_swap hsub_ae
    filter_upwards [W₁.symm_ae, W₂.symm_ae, hsub_ae, hsub_swap]
      with p h1 h2 hsub hsub_s
    simp only [Pi.sub_apply] at hsub hsub_s ⊢
    rw [hsub_s, hsub, h1, h2]
  ae_abs_le_one := by
    filter_upwards [W₁.ae_mem_Icc, W₂.ae_mem_Icc, AEEqFun.coeFn_sub W₁.toAEEqFun W₂.toAEEqFun]
      with p h1 h2 hsub
    simp only [Pi.sub_apply] at hsub ⊢
    rw [hsub, abs_le]
    constructor
    · linarith [h1.1, h2.2]
    · linarith [h1.2, h2.1]

end SignedGraphon
