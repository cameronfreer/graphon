/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Kernel Operators from Graphons

This file defines the integral operator associated with a graphon and proves
basic properties.

This module provides a pointwise kernel operator definition only; the full L²
operator API (continuous linear map, Hilbert-Schmidt, compactness) is not developed
here.

## Main definitions

* `Graphon.kernelOpFun` — Pointwise kernel operator `(T_W f)(x) = ∫ W(x,y) f(y) dμ(y)`

## Main results

* `Graphon.kernelOpFun_symmetric` — Symmetry of the bilinear form
* `Graphon.kernelOpFun_bound_ae` — Pointwise bound by ‖f‖₁

## Implementation notes

The kernel operator is central to spectral theory of graphons. Background facts
(not yet formalized here):
- `T_W` is a Hilbert-Schmidt operator (hence compact) when W ∈ L²
- `T_W` is self-adjoint since W is symmetric
- The eigenvalues of `T_W` are related to homomorphism densities

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Section 7.5
-/

open MeasureTheory Set Filter

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

/-! ### The kernel operator -/

section KernelOperator

variable [IsProbabilityMeasure μ]

/-- The kernel operator applied to a function.

Given a graphon `W : α × α → ℝ` and a function `f : α → ℝ`, the kernel operator
produces `(T_W f)(x) = ∫ W(x,y) f(y) dμ(y)`.

This is the basic building block for the L² operator.

**Note on well-definedness**: This definition evaluates `W.toAEEqFun (x, y)` pointwise.
Since `W` is only defined a.e., the section `W(x, ·)` may depend on the representative
for a null set of x values. A more robust definition would construct an L²-valued
operator directly. For graphons on standard probability spaces, this issue is
typically resolved by working with canonical representatives. -/
noncomputable def kernelOpFun (W : Graphon α μ) (f : α → ℝ) (x : α) : ℝ :=
  ∫ y, W.toAEEqFun (x, y) * f y ∂μ

/-- Graphon values are bounded by 1 in absolute value (a.e.). -/
theorem graphon_abs_le_one (W : Graphon α μ) :
    ∀ᵐ p ∂(μ.prod μ), |W.toAEEqFun p| ≤ 1 := by
  filter_upwards [W.ae_mem_Icc] with p hp
  rw [abs_le]
  exact ⟨by linarith [hp.1], hp.2⟩

/-- Section integrability: for a.e. x, the section y ↦ W(x,y) * f(y) is integrable.

This follows from Fubini's theorem applied to the integrable function W * (f ∘ snd). -/
theorem graphon_section_integrable_ae (W : Graphon α μ) (f : α → ℝ)
    (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => W.toAEEqFun (x, y) * f y) μ := by
  have hW_bound : ∀ᵐ p ∂(μ.prod μ), ‖W.toAEEqFun p‖ ≤ 1 := by
    filter_upwards [W.ae_mem_Icc] with p hp
    simp only [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hp.1], hp.2⟩
  have h_prod : Integrable (fun p : α × α => W.toAEEqFun p * f p.2) (μ.prod μ) := by
    have h_f : Integrable (fun p : α × α => f p.2) (μ.prod μ) := by
      haveI : IsFiniteMeasure μ := inferInstance
      exact hf.comp_snd μ
    exact Integrable.bdd_mul h_f W.toAEEqFun.aestronglyMeasurable hW_bound
  exact Integrable.prod_right_ae h_prod

/-- The kernel operator is linear in the function argument (a.e. version).

**Note**: The equality holds for a.e. x, since integrability of sections
`y ↦ W(x,y) * f(y)` only holds for a.e. x via Fubini. -/
theorem kernelOpFun_add_ae (W : Graphon α μ) (f g : α → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, kernelOpFun W (f + g) x = kernelOpFun W f x + kernelOpFun W g x := by
  -- Section measurability: for a.e. x, y ↦ W(x, y) is AEStronglyMeasurable
  have hW_meas : ∀ᵐ x ∂μ, AEStronglyMeasurable (fun y => W.toAEEqFun (x, y)) μ :=
    AEStronglyMeasurable.prodMk_left W.toAEEqFun.aestronglyMeasurable
  -- Section bounds: for a.e. x, |W(x,y)| ≤ 1 for a.e. y
  have hW_bound : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, |W.toAEEqFun (x, y)| ≤ 1 :=
    Measure.ae_ae_of_ae_prod (graphon_abs_le_one W)
  filter_upwards [hW_meas, hW_bound] with x hx_meas hx_bound
  simp only [kernelOpFun, Pi.add_apply]
  rw [← integral_add]
  · congr 1
    ext y
    ring
  · -- Integrability of W(x,·) * f(·)
    have hW_norm_bound : ∀ᵐ y ∂μ, ‖W.toAEEqFun (x, y)‖ ≤ 1 := by
      filter_upwards [hx_bound] with y hy
      simp only [Real.norm_eq_abs]
      exact hy
    exact Integrable.bdd_mul hf hx_meas hW_norm_bound
  · -- Integrability of W(x,·) * g(·)
    have hW_norm_bound : ∀ᵐ y ∂μ, ‖W.toAEEqFun (x, y)‖ ≤ 1 := by
      filter_upwards [hx_bound] with y hy
      simp only [Real.norm_eq_abs]
      exact hy
    exact Integrable.bdd_mul hg hx_meas hW_norm_bound

/-- The kernel operator respects scalar multiplication. -/
theorem kernelOpFun_smul (W : Graphon α μ) (c : ℝ) (f : α → ℝ) :
    kernelOpFun W (c • f) = c • kernelOpFun W f := by
  ext x
  simp only [kernelOpFun, Pi.smul_apply, smul_eq_mul]
  rw [← smul_eq_mul, ← integral_smul]
  congr 1
  ext y
  simp only [smul_eq_mul]
  ring

/-- The kernel operator is symmetric in the inner product sense.

For integrable f, g: `∫ (T_W f) * g = ∫ f * (T_W g)`.

This follows from the symmetry of W: W(x,y) = W(y,x) a.e.

**Proof outline**:
1. LHS = ∫ x, (∫ y, W(x,y) f(y)) g(x) dμ(x)
        = ∫∫ W(x,y) f(y) g(x) dμ(y) dμ(x) (Fubini)
2. RHS = ∫ x, f(x) (∫ y, W(x,y) g(y)) dμ(x)
        = ∫∫ W(x,y) f(x) g(y) dμ(y) dμ(x) (Fubini)
3. Swap (x,y) in RHS and use W(y,x) = W(x,y) a.e.

The proof requires `integral_integral` and `integral_prod_symm` from Mathlib.MeasureTheory.Integral.Prod. -/
theorem kernelOpFun_symmetric (W : Graphon α μ) (f g : α → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, kernelOpFun W f x * g x ∂μ = ∫ x, f x * kernelOpFun W g x ∂μ := by
  -- Define integrands for product space
  let F : α × α → ℝ := fun p => W.toAEEqFun p * f p.2 * g p.1
  let G : α × α → ℝ := fun p => W.toAEEqFun p * f p.1 * g p.2
  -- Integrability setup
  have hW_bound : ∀ᵐ p ∂(μ.prod μ), ‖W.toAEEqFun p‖ ≤ 1 := by
    filter_upwards [W.ae_mem_Icc] with p hp
    simp only [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hp.1], hp.2⟩
  have hF_int : Integrable F (μ.prod μ) := by
    have h_fg : Integrable (fun p : α × α => g p.1 * f p.2) (μ.prod μ) := Integrable.mul_prod hg hf
    have h_fg' : Integrable (fun p : α × α => f p.2 * g p.1) (μ.prod μ) := by
      convert h_fg using 1; ext p; ring
    have h := Integrable.bdd_mul h_fg' W.toAEEqFun.aestronglyMeasurable hW_bound
    convert h using 1; ext p; ring
  have hG_int : Integrable G (μ.prod μ) := by
    have h_fg : Integrable (fun p : α × α => f p.1 * g p.2) (μ.prod μ) := Integrable.mul_prod hf hg
    have h := Integrable.bdd_mul h_fg W.toAEEqFun.aestronglyMeasurable hW_bound
    convert h using 1; ext p; ring
  -- Key symmetry: ∫ F = ∫ G via integral_prod_swap and W(p.swap) = W(p)
  have hFG : ∫ p, F p ∂(μ.prod μ) = ∫ p, G p ∂(μ.prod μ) := by
    rw [← integral_prod_swap G]
    apply integral_congr_ae
    filter_upwards [W.symm'] with p hp
    simp only [G, F, Prod.fst_swap, Prod.snd_swap]
    rw [hp]
  -- Section integrability (a.e.)
  have h_sec_Wf : ∀ᵐ x ∂μ, Integrable (fun y => W.toAEEqFun (x, y) * f y) μ :=
    graphon_section_integrable_ae W f hf
  have h_sec_Wg : ∀ᵐ x ∂μ, Integrable (fun y => W.toAEEqFun (x, y) * g y) μ :=
    graphon_section_integrable_ae W g hg
  -- LHS = ∫ F
  have hLHS : ∫ x, kernelOpFun W f x * g x ∂μ = ∫ p, F p ∂(μ.prod μ) := by
    rw [integral_prod F hF_int]
    apply integral_congr_ae
    filter_upwards [h_sec_Wf] with x hx
    simp only [kernelOpFun, F]
    conv_lhs => rw [← integral_mul_const_of_integrable hx]
  -- RHS = ∫ G
  have hRHS : ∫ x, f x * kernelOpFun W g x ∂μ = ∫ p, G p ∂(μ.prod μ) := by
    rw [integral_prod G hG_int]
    apply integral_congr_ae
    filter_upwards [h_sec_Wg] with x hx
    simp only [kernelOpFun, G]
    conv_lhs => rw [← integral_const_mul_of_integrable hx]
    -- Goal: ∫ y, f(x) * (W(x,y) * g(y)) = ∫ y, W(x,y) * f(x) * g(y)
    apply integral_congr_ae
    filter_upwards with y
    ring
  rw [hLHS, hFG, ← hRHS]

/-- The kernel operator of the zero graphon is zero.

**Note**: This holds pointwise (not just a.e.) because `zero.toAEEqFun = AEEqFun.const 0`
evaluates to 0 everywhere when the measure is nonzero. -/
theorem kernelOpFun_zero (f : α → ℝ) : kernelOpFun (zero : Graphon α μ) f = 0 := by
  ext x
  simp only [kernelOpFun, zero, Pi.zero_apply]
  -- The zero graphon has W(x,y) = 0 for all (x,y) since it's a constant AEEqFun on a nonzero measure
  haveI : NeZero (μ.prod μ) := ⟨by simp [IsProbabilityMeasure.ne_zero]⟩
  simp only [AEEqFun.coeFn_const_eq (α × α) (0 : ℝ), zero_mul, integral_zero]

/-- The kernel operator of the one graphon equals the integral of f.

**Note**: This holds pointwise (not just a.e.) because `one.toAEEqFun = AEEqFun.const 1`
evaluates to 1 everywhere when the measure is nonzero. -/
theorem kernelOpFun_one (f : α → ℝ) : kernelOpFun (one : Graphon α μ) f = fun _ => ∫ y, f y ∂μ := by
  ext x
  simp only [kernelOpFun, one]
  -- The one graphon has W(x,y) = 1 for all (x,y)
  haveI : NeZero (μ.prod μ) := ⟨by simp [IsProbabilityMeasure.ne_zero]⟩
  simp only [AEEqFun.coeFn_const_eq (α × α) (1 : ℝ), one_mul]

/-- Bound on the kernel operator output (a.e. version).

For f ∈ L², for a.e. x, `|(T_W f)(x)| ≤ ‖f‖_L¹` since |W| ≤ 1 a.e.

**Note**: The bound holds for a.e. x (not all x), since graphon values are only
guaranteed to be in [0,1] a.e. on the product measure, and sections inherit
this property a.e. via Fubini. -/
theorem kernelOpFun_bound_ae (W : Graphon α μ) (f : α → ℝ) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, |kernelOpFun W f x| ≤ ∫ y, |f y| ∂μ := by
  -- From graphon bounds: |W(x,y)| ≤ 1 a.e. on product measure
  have hW_bound : ∀ᵐ p ∂(μ.prod μ), |W.toAEEqFun p| ≤ 1 := graphon_abs_le_one W
  -- Convert to: for a.e. x, |W(x,y)| ≤ 1 for a.e. y
  have hW_section : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, |W.toAEEqFun (x, y)| ≤ 1 :=
    Measure.ae_ae_of_ae_prod hW_bound
  -- Section measurability: for a.e. x, y ↦ W(x, y) is AEStronglyMeasurable
  have hW_meas : ∀ᵐ x ∂μ, AEStronglyMeasurable (fun y => W.toAEEqFun (x, y)) μ :=
    AEStronglyMeasurable.prodMk_left W.toAEEqFun.aestronglyMeasurable
  -- Combine the two a.e. properties
  filter_upwards [hW_section, hW_meas] with x hx hx_meas
  unfold kernelOpFun
  calc |∫ y, W.toAEEqFun (x, y) * f y ∂μ|
      ≤ ∫ y, |W.toAEEqFun (x, y) * f y| ∂μ := abs_integral_le_integral_abs
    _ = ∫ y, |W.toAEEqFun (x, y)| * |f y| ∂μ := by simp only [abs_mul]
    _ ≤ ∫ y, 1 * |f y| ∂μ := by
        apply integral_mono_ae
        · -- Integrability: |W(x,·)| * |f| is integrable since |W| ≤ 1 a.e. and f is integrable
          have hW_norm_bound : ∀ᵐ y ∂μ, ‖|W.toAEEqFun (x, y)|‖ ≤ 1 := by
            filter_upwards [hx] with y hy
            simp only [Real.norm_eq_abs, abs_abs]
            exact hy
          exact Integrable.bdd_mul hf.abs hx_meas.norm hW_norm_bound
        · simp only [one_mul]; exact hf.abs
        · filter_upwards [hx] with y hy
          exact mul_le_mul_of_nonneg_right hy (abs_nonneg _)
    _ = ∫ y, |f y| ∂μ := by simp only [one_mul]

end KernelOperator

/-! ### L² operator (not developed here)

The full development of the L² operator `T_W : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ` requires:
1. Showing kernelOpFun maps L² to L² (uses L² boundedness)
2. Constructing the ContinuousLinearMap
3. Proving self-adjointness in the inner product sense
4. Hilbert-Schmidt property and compactness

These are not yet implemented.
-/

end Graphon
