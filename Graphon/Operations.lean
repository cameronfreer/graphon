/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Pullback

/-!
# Operations on Graphons

**Experimental**: This module defines basic operations on graphons: pointwise
product and properties of the complement (already defined in Basic.lean).

## Main definitions

* `Graphon.pointwiseMul` - Pointwise product of two graphons

## Main results

* `Graphon.pointwiseMul_comm` - Pointwise product is commutative
* `Graphon.pointwiseMul_assoc` - Pointwise product is associative
* `Graphon.pointwiseMul_one` - Multiplying by the constant 1 graphon is identity
* `Graphon.pointwiseMul_zero` - Multiplying by the constant 0 graphon gives 0

## Implementation notes

The pointwise product `W₁ * W₂` represents the AND of independent edge events.
If `W₁` and `W₂` are graphon limits of graph sequences `G_n` and `H_n`, then
`W₁ * W₂` corresponds to the intersection `G_n ∩ H_n`.

The direct sum operation (combining two graphons on disjoint probability spaces)
and operator product (composition via integral operators) are more complex and
are not yet implemented.

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Section 7.4
-/

open MeasureTheory Set Filter Finset

open scoped unitInterval ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

/-! ### Pointwise multiplication -/

section PointwiseMul

variable [IsProbabilityMeasure μ]

/-- Pointwise multiplication of two graphons on the same probability space.

Given graphons `W₁, W₂ : α × α → [0,1]`, their pointwise product is
`(W₁ * W₂)(x, y) = W₁(x, y) * W₂(x, y)`.

This represents the AND of independent edge events: if `W₁` and `W₂` are
limits of graph sequences `G_n` and `H_n`, then `W₁ * W₂` corresponds to
the edge-intersection `G_n ∩ H_n`.

The product of values in [0,1] is again in [0,1], so pointwise multiplication
preserves the graphon property. -/
noncomputable def pointwiseMul (W₁ W₂ : Graphon α μ) : Graphon α μ where
  toAEEqFun := W₁.toAEEqFun * W₂.toAEEqFun
  symm' := by
    have h1 := W₁.symm_ae
    have h2 := W₂.symm_ae
    have hmul := AEEqFun.coeFn_mul W₁.toAEEqFun W₂.toAEEqFun
    have hmul_swap := ae_prod_swap hmul
    filter_upwards [h1, h2, hmul, hmul_swap] with p hp1 hp2 hm hm_swap
    simp only [Pi.mul_apply] at hm hm_swap ⊢
    rw [hm_swap, hm, hp1, hp2]
  ae_mem_Icc := by
    have h1 := W₁.ae_mem_Icc
    have h2 := W₂.ae_mem_Icc
    have hmul := AEEqFun.coeFn_mul W₁.toAEEqFun W₂.toAEEqFun
    filter_upwards [h1, h2, hmul] with p hp1 hp2 hm
    simp only [Pi.mul_apply, Set.mem_Icc] at hp1 hp2 hm ⊢
    rw [hm]
    constructor
    · exact mul_nonneg hp1.1 hp2.1
    · calc W₁.toAEEqFun p * W₂.toAEEqFun p
          ≤ 1 * W₂.toAEEqFun p := by apply mul_le_mul_of_nonneg_right hp1.2 hp2.1
        _ ≤ 1 * 1 := by apply mul_le_mul_of_nonneg_left hp2.2 zero_le_one
        _ = 1 := by ring

/-- The underlying AEEqFun of a pointwise product. -/
theorem pointwiseMul_toAEEqFun (W₁ W₂ : Graphon α μ) :
    (pointwiseMul W₁ W₂).toAEEqFun = W₁.toAEEqFun * W₂.toAEEqFun := rfl

/-- Pointwise multiplication is commutative. -/
theorem pointwiseMul_comm (W₁ W₂ : Graphon α μ) : pointwiseMul W₁ W₂ = pointwiseMul W₂ W₁ := by
  apply Graphon.ext
  apply SymmKernel.ext
  simp only [pointwiseMul_toAEEqFun, mul_comm]

/-- Pointwise multiplication is associative. -/
theorem pointwiseMul_assoc (W₁ W₂ W₃ : Graphon α μ) :
    pointwiseMul (pointwiseMul W₁ W₂) W₃ = pointwiseMul W₁ (pointwiseMul W₂ W₃) := by
  apply Graphon.ext
  apply SymmKernel.ext
  simp only [pointwiseMul_toAEEqFun, mul_assoc]

/-- Multiplying by the constant 1 graphon is the identity. -/
theorem pointwiseMul_one (W : Graphon α μ) : pointwiseMul W one = W := by
  apply Graphon.ext
  apply SymmKernel.ext
  have hmul := AEEqFun.coeFn_mul W.toAEEqFun (one : Graphon α μ).toAEEqFun
  have h1 := @AEEqFun.coeFn_const (α × α) ℝ _ (μ.prod μ) _ (1 : ℝ)
  apply AEEqFun.ext
  filter_upwards [hmul, h1] with p hp hp1
  simp only [Pi.mul_apply, pointwiseMul_toAEEqFun, one_toAEEqFun, Function.const] at hp hp1 ⊢
  rw [hp, hp1, mul_one]

/-- Multiplying by the constant 0 graphon gives 0. -/
theorem pointwiseMul_zero (W : Graphon α μ) : pointwiseMul W zero = zero := by
  apply Graphon.ext
  apply SymmKernel.ext
  have hmul := AEEqFun.coeFn_mul W.toAEEqFun (zero : Graphon α μ).toAEEqFun
  have h0 := @AEEqFun.coeFn_const (α × α) ℝ _ (μ.prod μ) _ (0 : ℝ)
  apply AEEqFun.ext
  filter_upwards [hmul, h0] with p hp hp0
  simp only [Pi.mul_apply, pointwiseMul_toAEEqFun, zero_toAEEqFun, Function.const] at hp hp0 ⊢
  rw [hp, hp0, mul_zero]

/-- The pointwise product takes values in [0,1] a.e. -/
theorem pointwiseMul_ae_mem_Icc (W₁ W₂ : Graphon α μ) :
    ∀ᵐ p ∂(μ.prod μ), (pointwiseMul W₁ W₂).toAEEqFun p ∈ Set.Icc 0 1 :=
  (pointwiseMul W₁ W₂).ae_mem_Icc

/-- Pointwise multiplication distributes over complement from the right:
    `(1 - W₁) * W₂ + W₁ * W₂ = W₂` (a.e.).

    This is the probabilistic identity: P(not A and B) + P(A and B) = P(B). -/
theorem compl_pointwiseMul_add (W₁ W₂ : Graphon α μ) :
    ∀ᵐ p ∂(μ.prod μ),
      (pointwiseMul W₁.compl W₂).toAEEqFun p + (pointwiseMul W₁ W₂).toAEEqFun p =
        W₂.toAEEqFun p := by
  have hcompl := AEEqFun.coeFn_sub (AEEqFun.const (α × α) 1) W₁.toAEEqFun
  have hmul1 := AEEqFun.coeFn_mul W₁.compl.toAEEqFun W₂.toAEEqFun
  have hmul2 := AEEqFun.coeFn_mul W₁.toAEEqFun W₂.toAEEqFun
  have hone := @AEEqFun.coeFn_const (α × α) ℝ _ (μ.prod μ) _ (1 : ℝ)
  filter_upwards [hcompl, hmul1, hmul2, hone] with p hc hm1 hm2 h1
  simp only [Pi.mul_apply, Pi.sub_apply, pointwiseMul_toAEEqFun, compl, Function.const] at hc hm1 hm2 h1 ⊢
  rw [hm1, hm2, hc, h1]
  ring

end PointwiseMul

/-! ### Interaction with homomorphism density -/

section HomDensity

variable [IsProbabilityMeasure μ]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The pointwise product evaluates to the product of evaluations, a.e. on the pi measure. -/
theorem pointwiseMul_eval_ae (W₁ W₂ : Graphon α μ) {v₁ v₂ : V} (hne : v₁ ≠ v₂) :
    ∀ᵐ x ∂Measure.pi (fun _ : V => μ),
      (pointwiseMul W₁ W₂).toAEEqFun (x v₁, x v₂) =
        W₁.toAEEqFun (x v₁, x v₂) * W₂.toAEEqFun (x v₁, x v₂) := by
  -- Lift AEEqFun.coeFn_mul through the coordinate projection
  have h_meas : Measurable (fun x : V → α => (x v₁, x v₂)) :=
    Measurable.prodMk (measurable_pi_apply _) (measurable_pi_apply _)
  have h_indep : ProbabilityTheory.iIndepFun (fun i (x : V → α) => x i)
      (Measure.pi (fun _ : V => μ)) := ProbabilityTheory.iIndepFun_pi (fun _ => aemeasurable_id)
  have h_indep_pair := h_indep.indepFun hne
  have h_map : Measure.map (fun x => (x v₁, x v₂)) (Measure.pi (fun _ : V => μ)) =
      (Measure.map (fun x => x v₁) (Measure.pi (fun _ : V => μ))).prod
      (Measure.map (fun x => x v₂) (Measure.pi (fun _ : V => μ))) := by
    rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      (measurable_pi_apply _).aemeasurable (measurable_pi_apply _).aemeasurable] at h_indep_pair
    exact h_indep_pair
  have h_marg₁ : Measure.map (fun x => x v₁) (Measure.pi (fun _ : V => μ)) = μ :=
    (MeasureTheory.measurePreserving_eval (fun _ : V => μ) v₁).map_eq
  have h_marg₂ : Measure.map (fun x => x v₂) (Measure.pi (fun _ : V => μ)) = μ :=
    (MeasureTheory.measurePreserving_eval (fun _ : V => μ) v₂).map_eq
  have h_map_eq : Measure.map (fun x => (x v₁, x v₂)) (Measure.pi (fun _ : V => μ)) =
      μ.prod μ := by rw [h_map, h_marg₁, h_marg₂]
  have h_qmp : Measure.QuasiMeasurePreserving (fun x : V → α => (x v₁, x v₂))
      (Measure.pi (fun _ : V => μ)) (μ.prod μ) := by
    constructor
    · exact h_meas
    · rw [h_map_eq]
  -- AEEqFun.coeFn_mul gives the a.e. equality on μ.prod μ
  have h_mul := AEEqFun.coeFn_mul W₁.toAEEqFun W₂.toAEEqFun
  -- Convert to the form we need: (pointwiseMul W₁ W₂).toAEEqFun p = W₁ p * W₂ p
  have h_ae : ∀ᵐ p ∂(μ.prod μ),
      (pointwiseMul W₁ W₂).toAEEqFun p = W₁.toAEEqFun p * W₂.toAEEqFun p := by
    filter_upwards [h_mul] with p hp
    simp only [Pi.mul_apply, pointwiseMul] at hp ⊢
    exact hp
  -- Lift to pi measure
  exact h_qmp.ae h_ae

/-- Homomorphism density of the pointwise product is bounded by the minimum of the
    individual densities.

    More precisely: `t(F, W₁ * W₂) ≤ min(t(F, W₁), t(F, W₂))` since each edge
    probability is the product, which is at most either factor. -/
theorem homDensity_pointwiseMul_le (F : SimpleGraph V) [DecidableRel F.Adj]
    (W₁ W₂ : Graphon α μ) :
    homDensity F (pointwiseMul W₁ W₂) ≤ min (homDensity F W₁) (homDensity F W₂) := by
  rw [le_min_iff]
  -- Get a.e. bounds for all edges
  have h_edges₁ : ∀ e ∈ F.edgeFinset,
      ∀ᵐ x ∂Measure.pi (fun _ : V => μ),
        W₁.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1 :=
    fun e he => graphonEval_mem_Icc_ae W₁ (edge_out_ne (SimpleGraph.mem_edgeFinset.mp he))
  have h_edges₂ : ∀ e ∈ F.edgeFinset,
      ∀ᵐ x ∂Measure.pi (fun _ : V => μ),
        W₂.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1 :=
    fun e he => graphonEval_mem_Icc_ae W₂ (edge_out_ne (SimpleGraph.mem_edgeFinset.mp he))
  -- Get a.e. equality for pointwiseMul evaluation
  have h_mul_edges : ∀ e ∈ F.edgeFinset,
      ∀ᵐ x ∂Measure.pi (fun _ : V => μ),
        (pointwiseMul W₁ W₂).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) =
          W₁.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) *
          W₂.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) :=
    fun e he => pointwiseMul_eval_ae W₁ W₂ (edge_out_ne (SimpleGraph.mem_edgeFinset.mp he))
  -- Combine all a.e. properties
  have h_all : ∀ᵐ x ∂Measure.pi (fun _ : V => μ),
      (∀ e ∈ F.edgeFinset, W₁.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1) ∧
      (∀ e ∈ F.edgeFinset, W₂.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1) ∧
      (∀ e ∈ F.edgeFinset, (pointwiseMul W₁ W₂).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) =
          W₁.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) *
          W₂.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) := by
    have aux : ∀ (s : Finset (Sym2 V)) (P : (V → α) → Sym2 V → Prop),
        (∀ e ∈ s, ∀ᵐ x ∂Measure.pi (fun _ : V => μ), P x e) →
        ∀ᵐ x ∂Measure.pi (fun _ : V => μ), ∀ e ∈ s, P x e := by
      intro s P
      refine Finset.induction_on s ?empty ?insert
      case empty => simp
      case insert =>
        intro a s' _ ih hs
        simp only [Finset.mem_insert, forall_eq_or_imp] at hs ⊢
        filter_upwards [hs.1, ih hs.2] with x hx1 hx2
        exact ⟨hx1, hx2⟩
    filter_upwards [aux F.edgeFinset _ h_edges₁, aux F.edgeFinset _ h_edges₂,
        aux F.edgeFinset _ h_mul_edges] with x hx₁ hx₂ hx_mul
    exact ⟨hx₁, hx₂, hx_mul⟩
  constructor
  · -- homDensity F (W₁ * W₂) ≤ homDensity F W₁
    rw [homDensity_eq_integral, homDensity_eq_integral]
    apply integral_mono_ae (homDensityIntegrand_integrable F (pointwiseMul W₁ W₂))
      (homDensityIntegrand_integrable F W₁)
    filter_upwards [h_all] with x ⟨hx₁, hx₂, hx_mul⟩
    simp only [homDensityIntegrand]
    -- Rewrite the pointwiseMul product using hx_mul
    have h_prod_eq : ∏ e ∈ F.edgeFinset,
        (pointwiseMul W₁ W₂).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) =
        ∏ e ∈ F.edgeFinset, W₁.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) *
          W₂.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) :=
      Finset.prod_congr rfl fun e he => hx_mul e he
    rw [h_prod_eq]
    apply Finset.prod_le_prod
    · intro e he
      exact mul_nonneg (hx₁ e he).1 (hx₂ e he).1
    · intro e he
      calc W₁.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) *
             W₂.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)
          ≤ W₁.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) * 1 := by
            apply mul_le_mul_of_nonneg_left (hx₂ e he).2 (hx₁ e he).1
        _ = W₁.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) := mul_one _
  · -- homDensity F (W₁ * W₂) ≤ homDensity F W₂
    rw [homDensity_eq_integral, homDensity_eq_integral]
    apply integral_mono_ae (homDensityIntegrand_integrable F (pointwiseMul W₁ W₂))
      (homDensityIntegrand_integrable F W₂)
    filter_upwards [h_all] with x ⟨hx₁, hx₂, hx_mul⟩
    simp only [homDensityIntegrand]
    have h_prod_eq : ∏ e ∈ F.edgeFinset,
        (pointwiseMul W₁ W₂).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) =
        ∏ e ∈ F.edgeFinset, W₁.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) *
          W₂.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) :=
      Finset.prod_congr rfl fun e he => hx_mul e he
    rw [h_prod_eq]
    apply Finset.prod_le_prod
    · intro e he
      exact mul_nonneg (hx₁ e he).1 (hx₂ e he).1
    · intro e he
      calc W₁.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) *
             W₂.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)
          ≤ 1 * W₂.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) := by
            apply mul_le_mul_of_nonneg_right (hx₁ e he).2 (hx₂ e he).1
        _ = W₂.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) := one_mul _

end HomDensity

end Graphon
