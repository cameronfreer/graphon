/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Tactic.Linarith

/-!
# Graphons

A graphon is (informally) a symmetric measurable function `W : [0,1]² → [0,1]` that
represents the limit of a convergent sequence of dense graphs. More precisely,
graphons are equivalence classes of such functions under almost-everywhere equality.

This file introduces graphons parameterized by a probability space `(α, μ)`, using
`AEEqFun` (almost-everywhere equivalence classes of functions) to represent kernels.
Two kernels that agree almost everywhere are considered equal.

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

/-- If a property holds a.e. for the product measure `μ × μ`, then it also holds
a.e. when composed with swap.

This requires `[SFinite μ]` to ensure that swap is measure-preserving on the
product measure (i.e., `(μ.prod μ).map swap = μ.prod μ`). -/
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
@[blueprint "def:graphon"
  (title := /-- Graphon -/)]
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

/-! ### Coercions and instances for SymmKernel

We provide coercions so that a `SymmKernel` can be used directly as an `AEEqFun`.
The extensionality lemma shows that two symmetric kernels are equal iff their
underlying `AEEqFun` representatives are equal (which is itself equality up to
a.e. equivalence). -/

namespace SymmKernel

/-- A symmetric kernel can be used as its underlying `AEEqFun`. -/
instance : CoeFun (SymmKernel α μ) (fun _ => (α × α) →ₘ[μ.prod μ] ℝ) :=
  ⟨toAEEqFun⟩

/-- Symmetric kernels are equal iff their underlying `AEEqFun` are equal.

Since `AEEqFun` equality is defined as a.e. equality of representatives,
this means two symmetric kernels are equal iff they agree almost everywhere. -/
@[ext]
theorem ext {W₁ W₂ : SymmKernel α μ} (h : W₁.toAEEqFun = W₂.toAEEqFun) : W₁ = W₂ := by
  cases W₁; cases W₂; simp only [mk.injEq]; exact h

/-- The symmetry property: `W(x,y) = W(y,x)` for almost every `(x,y)`.

This is the defining property of symmetric kernels, ensuring the kernel
represents an undirected relationship. -/
theorem symm_ae (W : SymmKernel α μ) : ∀ᵐ p ∂(μ.prod μ), W.toAEEqFun p.swap = W.toAEEqFun p :=
  W.symm'

end SymmKernel

/-! ### Coercions and instances for Graphon

We provide coercions so that a `Graphon` can be used as a `SymmKernel` or `AEEqFun`.
The key properties are:
- `ae_nonneg`: values are non-negative a.e.
- `ae_le_one`: values are at most 1 a.e.
- `symm_ae`: the graphon is symmetric a.e.

Together these ensure the graphon represents a valid edge-weight function for
the limit of dense graphs. -/

namespace Graphon

/-- A graphon can be used as its underlying `AEEqFun`. -/
instance : CoeFun (Graphon α μ) (fun _ => (α × α) →ₘ[μ.prod μ] ℝ) :=
  ⟨fun W => W.toSymmKernel.toAEEqFun⟩

/-- A graphon can be viewed as its underlying symmetric kernel.

This forgets the `[0,1]` bound but retains the symmetry property. -/
instance : Coe (Graphon α μ) (SymmKernel α μ) :=
  ⟨toSymmKernel⟩

/-- Graphons are equal iff their underlying symmetric kernels are equal.

Since `SymmKernel` equality reduces to `AEEqFun` equality (a.e. equality),
two graphons are equal iff they agree almost everywhere. -/
@[ext]
theorem ext {W₁ W₂ : Graphon α μ} (h : W₁.toSymmKernel = W₂.toSymmKernel) : W₁ = W₂ := by
  cases W₁; cases W₂; simp only [mk.injEq]; exact h

/-- Graphon values are non-negative almost everywhere.

This is half of the `[0,1]` bound; combined with `ae_le_one`, it ensures
the graphon represents valid edge probabilities. -/
theorem ae_nonneg (W : Graphon α μ) : ∀ᵐ p ∂(μ.prod μ), 0 ≤ W.toAEEqFun p :=
  W.ae_mem_Icc.mono fun _ h => h.1

/-- Graphon values are at most 1 almost everywhere.

This is half of the `[0,1]` bound; combined with `ae_nonneg`, it ensures
the graphon represents valid edge probabilities. -/
theorem ae_le_one (W : Graphon α μ) : ∀ᵐ p ∂(μ.prod μ), W.toAEEqFun p ≤ 1 :=
  W.ae_mem_Icc.mono fun _ h => h.2

/-- The symmetry property for graphons: `W(x,y) = W(y,x)` for almost every `(x,y)`.

This ensures the graphon represents an undirected graph limit. -/
theorem symm_ae (W : Graphon α μ) : ∀ᵐ p ∂(μ.prod μ), W.toAEEqFun p.swap = W.toAEEqFun p :=
  W.toSymmKernel.symm_ae

/-! ### Constant graphons

The constant graphons `zero` and `one` represent the limits of sequences of
empty graphs and complete graphs, respectively. For a sequence of empty graphs
`Gₙ` on `n` vertices, the graphon limit is the constant function `W ≡ 0`.
Similarly, complete graphs converge to `W ≡ 1`.

These require `[IsProbabilityMeasure μ]` to ensure the product measure is
symmetric under swap. -/

variable [IsProbabilityMeasure μ]

/-- The constant zero graphon, representing the limit of empty graphs.

For a sequence of empty graphs `Gₙ` (graphs with no edges), the edge density
between any two sets converges to 0, giving the graphon `W(x,y) = 0` for all `x,y`. -/
noncomputable def zero : Graphon α μ where
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

/-- The constant one graphon, representing the limit of complete graphs.

For a sequence of complete graphs `Kₙ`, the edge density between any two sets
converges to 1, giving the graphon `W(x,y) = 1` for all `x,y`. -/
noncomputable def one : Graphon α μ where
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

/-- The constant graphon with value `p ∈ [0, 1]`, representing the limit of
Erdős–Rényi graphs `G(n, p)`. Specializes to `zero` and `one` at the endpoints. -/
noncomputable def constGraphon (p : Set.Icc (0 : ℝ) 1) : Graphon α μ where
  toAEEqFun := AEEqFun.const (α × α) (p : ℝ)
  symm' := by
    filter_upwards [AEEqFun.coeFn_const (α × α) (p : ℝ),
      ae_prod_swap (AEEqFun.coeFn_const (α × α) (p : ℝ))] with z hz hzswap
    rw [hz, hzswap]
    rfl
  ae_mem_Icc := by
    filter_upwards [AEEqFun.coeFn_const (α × α) (p : ℝ)] with z hz
    rw [hz]
    exact p.property

/-- The underlying `AEEqFun` of a constant graphon. -/
theorem constGraphon_toAEEqFun (p : Set.Icc (0 : ℝ) 1) :
    (constGraphon p : Graphon α μ).toAEEqFun = AEEqFun.const (α × α) (p : ℝ) := rfl

/-- Graphons exist on every probability space (e.g. the constant graphon `0`). -/
instance : Nonempty (Graphon α μ) := ⟨constGraphon 0⟩

/-- The underlying `AEEqFun` of the zero graphon is the constant 0 function. -/
theorem zero_toAEEqFun : (zero : Graphon α μ).toAEEqFun = AEEqFun.const (α × α) 0 := rfl

/-- The underlying `AEEqFun` of the one graphon is the constant 1 function. -/
theorem one_toAEEqFun : (one : Graphon α μ).toAEEqFun = AEEqFun.const (α × α) 1 := rfl

/-! ### Complement

The complement operation `compl W = 1 - W` corresponds to taking graph complements.
If `W` is the graphon limit of a sequence of graphs `Gₙ`, then `compl W` is the
graphon limit of the complement graphs `Ḡₙ`.

Key properties:
- `compl_compl`: complement is an involution
- `compl_zero`: the complement of the empty graph limit is the complete graph limit
- `compl_one`: the complement of the complete graph limit is the empty graph limit -/

/-- The complement of a graphon: `(1 - W)`.

If `W` is the graphon limit of graphs `Gₙ`, then `compl W` is the limit of the
complement graphs `Ḡₙ`. The edge probability `W(x,y)` becomes the non-edge
probability `1 - W(x,y)`. -/
noncomputable def compl (W : Graphon α μ) : Graphon α μ where
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

/-- Complement is an involution: `(1 - (1 - W)) = W`.

This reflects the graph-theoretic fact that the complement of the complement
of a graph is the original graph. -/
@[simp]
theorem compl_compl (W : Graphon α μ) : W.compl.compl = W := by
  ext
  simp only [compl]
  rw [sub_sub_cancel]

/-- The complement of the zero graphon is the one graphon: `1 - 0 = 1`.

Graph-theoretically: the complement of the empty graph is the complete graph. -/
@[simp]
theorem compl_zero : (zero : Graphon α μ).compl = one := by
  ext
  simp only [compl, zero, one]
  filter_upwards [AEEqFun.coeFn_sub (AEEqFun.const (α × α) (1 : ℝ)) (AEEqFun.const (α × α) (0 : ℝ)),
    AEEqFun.coeFn_const (α × α) (1 : ℝ), AEEqFun.coeFn_const (α × α) (0 : ℝ)] with p hsub h1 h0
  simp only [Pi.sub_apply, Function.const_apply] at hsub h1 h0 ⊢
  rw [hsub, h1, h0, sub_zero]

/-- The complement of the one graphon is the zero graphon: `1 - 1 = 0`.

Graph-theoretically: the complement of the complete graph is the empty graph. -/
@[simp]
theorem compl_one : (one : Graphon α μ).compl = zero := by
  ext
  simp only [compl, zero, one]
  filter_upwards [AEEqFun.coeFn_sub (AEEqFun.const (α × α) (1 : ℝ)) (AEEqFun.const (α × α) (1 : ℝ)),
    AEEqFun.coeFn_const (α × α) (1 : ℝ), AEEqFun.coeFn_const (α × α) (0 : ℝ)] with p hsub h1 h0
  simp only [Pi.sub_apply, Function.const_apply] at hsub h1 h0 ⊢
  rw [hsub, h1, sub_self, h0]

end Graphon

/-! ### Coercions and instances for SignedGraphon

Signed graphons arise naturally when computing cut distances, which involve
differences of graphons. The key property is that if `W₁, W₂ : Graphon α μ`
with values in `[0,1]`, then `W₁ - W₂` has values in `[-1,1]`, so
`|W₁ - W₂| ≤ 1` almost everywhere.

The `sub` operation constructs the difference of two graphons as a signed graphon,
which is essential for defining the cut norm and cut distance. -/

namespace SignedGraphon

/-- A signed graphon can be used as its underlying `AEEqFun`. -/
instance : CoeFun (SignedGraphon α μ) (fun _ => (α × α) →ₘ[μ.prod μ] ℝ) :=
  ⟨fun W => W.toSymmKernel.toAEEqFun⟩

/-- A signed graphon can be viewed as its underlying symmetric kernel.

This forgets the `|W| ≤ 1` bound but retains the symmetry property. -/
instance : Coe (SignedGraphon α μ) (SymmKernel α μ) :=
  ⟨toSymmKernel⟩

/-- Signed graphons are equal iff their underlying symmetric kernels are equal.

Since `SymmKernel` equality reduces to `AEEqFun` equality (a.e. equality),
two signed graphons are equal iff they agree almost everywhere. -/
@[ext]
theorem ext {W₁ W₂ : SignedGraphon α μ} (h : W₁.toSymmKernel = W₂.toSymmKernel) : W₁ = W₂ := by
  cases W₁; cases W₂; simp only [mk.injEq]; exact h

variable [IsProbabilityMeasure μ]

/-- Embed a graphon as a signed graphon.

Since graphon values lie in `[0,1]` a.e., we have `|W| ≤ 1` a.e., so every
graphon is trivially a signed graphon. This embedding is useful when we want
to use graphons in contexts that expect signed graphons (e.g., cut norm). -/
def ofGraphon (W : Graphon α μ) : SignedGraphon α μ where
  toSymmKernel := W.toSymmKernel
  ae_abs_le_one := by
    filter_upwards [W.ae_mem_Icc] with p hp
    rw [abs_le]
    constructor
    · linarith [hp.1]
    · exact hp.2

/-- The difference of two graphons as a signed graphon.

If `W₁(x,y) ∈ [0,1]` and `W₂(x,y) ∈ [0,1]` a.e., then
`(W₁ - W₂)(x,y) ∈ [-1,1]` a.e., so `|W₁ - W₂| ≤ 1`.

This operation is fundamental for defining the cut distance:
`δ□(U, W) = inf_φ ‖U - W^φ‖_□` where `W^φ` is a pullback of `W`. -/
noncomputable def sub (W₁ W₂ : Graphon α μ) : SignedGraphon α μ where
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
