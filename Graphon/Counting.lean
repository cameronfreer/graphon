/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.HomDensity
import Graphon.CutDistance

/-!
# Counting Lemma for Graphons

This file proves the counting lemma, which relates the difference in homomorphism
densities to the cut norm of the difference between graphons.

## Main results

* `Graphon.homDensity_sub_le` - `|t(F, U) - t(F, W)| ≤ |E(F)| · ‖U - W‖_□`

## Implementation notes

The counting lemma is one of the central results in graphon theory. It says that
if two graphons are close in cut norm, then they have similar homomorphism densities
for any fixed graph F.

The constant `|E(F)|` (number of edges in F) is optimal in general.

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Chapter 10
-/

open MeasureTheory Set Filter Finset SimpleGraph

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Graphon

/-! ### Counting lemma -/

section Counting

variable [IsProbabilityMeasure μ]

/-! ### Helper lemmas for product bounds -/

/-- Bound on absolute difference of products by sum of differences.

For values in [0,1], the difference of products is bounded by the sum of
individual differences. This is used in the counting lemma proof. -/
theorem abs_prod_sub_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f g : ι → ℝ) (hf : ∀ i ∈ s, f i ∈ Set.Icc 0 1) (hg : ∀ i ∈ s, g i ∈ Set.Icc 0 1) :
    |s.prod f - s.prod g| ≤ s.sum (fun i => |f i - g i|) := by
  -- The proof uses the telescoping identity:
  -- ∏ f - ∏ g = Σⱼ (∏_{i<j} f i) · (f j - g j) · (∏_{i>j} g i)
  -- Each prefix product is in [0,1] and each suffix product is in [0,1],
  -- so the absolute value of each term is at most |f j - g j|.
  -- Summing over j gives the bound.
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    -- |f(a) * ∏ f - g(a) * ∏ g| = |f(a) * ∏ f - g(a) * ∏ f + g(a) * ∏ f - g(a) * ∏ g|
    --                          ≤ |f(a) - g(a)| * |∏ f| + |g(a)| * |∏ f - ∏ g|
    --                          ≤ |f(a) - g(a)| + |∏ f - ∏ g|  (since products in [0,1])
    have hfs : ∀ i ∈ s, f i ∈ Set.Icc 0 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgs : ∀ i ∈ s, g i ∈ Set.Icc 0 1 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hfa : f a ∈ Set.Icc 0 1 := hf a (Finset.mem_insert_self a s)
    have hga : g a ∈ Set.Icc 0 1 := hg a (Finset.mem_insert_self a s)
    have hpf : s.prod f ∈ Set.Icc 0 1 := by
      constructor
      · exact Finset.prod_nonneg (fun i hi => (hfs i hi).1)
      · exact Finset.prod_le_one (fun i hi => (hfs i hi).1) (fun i hi => (hfs i hi).2)
    have hpg : s.prod g ∈ Set.Icc 0 1 := by
      constructor
      · exact Finset.prod_nonneg (fun i hi => (hgs i hi).1)
      · exact Finset.prod_le_one (fun i hi => (hgs i hi).1) (fun i hi => (hgs i hi).2)
    calc |f a * s.prod f - g a * s.prod g|
        = |f a * s.prod f - g a * s.prod f + g a * s.prod f - g a * s.prod g| := by ring_nf
      _ = |(f a - g a) * s.prod f + g a * (s.prod f - s.prod g)| := by ring_nf
      _ ≤ |(f a - g a) * s.prod f| + |g a * (s.prod f - s.prod g)| := abs_add_le _ _
      _ = |f a - g a| * |s.prod f| + |g a| * |s.prod f - s.prod g| := by
          rw [abs_mul, abs_mul]
      _ ≤ |f a - g a| * 1 + 1 * |s.prod f - s.prod g| := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            rw [abs_of_nonneg hpf.1]; exact hpf.2
          · apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            rw [abs_of_nonneg hga.1]; exact hga.2
      _ = |f a - g a| + |s.prod f - s.prod g| := by ring
      _ ≤ |f a - g a| + s.sum (fun i => |f i - g i|) := add_le_add_right (ih hfs hgs) _

/-! ### Special case: Complete graph on 2 vertices (K₂)

The counting lemma for K₂ can be proven directly since homDensity K₂ W
equals the integral of W over μ.prod μ, which is rectIntegralDiff over univ × univ. -/

/-- Swap symmetry for Graphon integrals on Measure.pi (Fin 2 → α). -/
private lemma integral_swap_on_pi (W : Graphon α μ) :
    ∫ x : Fin 2 → α, W.toAEEqFun (x 1, x 0) ∂Measure.pi (fun _ => μ) =
    ∫ x : Fin 2 → α, W.toAEEqFun (x 0, x 1) ∂Measure.pi (fun _ => μ) := by
  have hmp := measurePreserving_finTwoArrow μ
  have hemb := MeasurableEquiv.measurableEmbedding (MeasurableEquiv.finTwoArrow (α := α))
  have h1 : ∫ x : Fin 2 → α, W.toAEEqFun (x 1, x 0) ∂Measure.pi (fun _ => μ) =
            ∫ p, W.toAEEqFun p.swap ∂(μ.prod μ) := by
    conv_lhs => arg 2; ext x
                rw [show (x 1, x 0) = (MeasurableEquiv.finTwoArrow x).swap by
                    simp [MeasurableEquiv.finTwoArrow_apply, Prod.swap]]
    exact hmp.integral_comp hemb (fun p => W.toAEEqFun p.swap)
  have h2 : ∫ x : Fin 2 → α, W.toAEEqFun (x 0, x 1) ∂Measure.pi (fun _ => μ) =
            ∫ p, W.toAEEqFun p ∂(μ.prod μ) := by
    conv_lhs => arg 2; ext x
                rw [show (x 0, x 1) = MeasurableEquiv.finTwoArrow x by
                    simp [MeasurableEquiv.finTwoArrow_apply]]
    exact hmp.integral_comp hemb (fun p => W.toAEEqFun p)
  rw [h1, h2]
  exact integral_congr_ae (by filter_upwards [W.symm'] with p hp; exact hp)

/-- The Quot.out of s(0,1) is either (0,1) or (1,0). -/
private lemma quot_out_01_cases :
    let p := Quot.out (s((0 : Fin 2), 1))
    (p.1 = 0 ∧ p.2 = 1) ∨ (p.1 = 1 ∧ p.2 = 0) := by
  set p := Quot.out (s((0 : Fin 2), 1)) with hp
  have h1 := Sym2.out_fst_mem (s((0 : Fin 2), 1))
  have h2 := Sym2.out_snd_mem (s((0 : Fin 2), 1))
  simp only [Sym2.mem_iff] at h1 h2
  have hQuot : s(p.1, p.2) = s((0 : Fin 2), 1) := Quot.out_eq _
  cases h1 with
  | inl h1_0 => cases h2 with
    | inl h2_0 => exfalso; rw [h1_0, h2_0] at hQuot; simp at hQuot
    | inr h2_1 => exact Or.inl ⟨h1_0, h2_1⟩
  | inr h1_1 => cases h2 with
    | inl h2_0 => exact Or.inr ⟨h1_1, h2_0⟩
    | inr h2_1 => exfalso; rw [h1_1, h2_1] at hQuot; simp at hQuot

/-- For the complete graph K₂, homDensity equals the integral over μ.prod μ.

This uses the equivalence between Measure.pi (Fin 2 → α) and μ.prod μ via
`measurePreserving_finTwoArrow`. -/
lemma homDensity_completeGraph_two (W : Graphon α μ) :
    homDensity (completeGraph (Fin 2)) W = ∫ p, W.toAEEqFun p ∂(μ.prod μ) := by
  unfold homDensity
  have hedge : (completeGraph (Fin 2)).edgeFinset = {s((0 : Fin 2), 1)} := by
    ext e; simp only [mem_edgeFinset, Finset.mem_singleton]
    constructor
    · intro h; induction e using Sym2.inductionOn with
      | _ v w => rw [completeGraph_eq_top] at h; simp only [mem_edgeSet, top_adj, ne_eq] at h
                 fin_cases v <;> fin_cases w <;> simp_all
    · intro h; rw [h, completeGraph_eq_top]; simp
  rw [hedge]; simp only [Finset.prod_singleton]
  have hmp := measurePreserving_finTwoArrow μ
  have hemb := MeasurableEquiv.measurableEmbedding (MeasurableEquiv.finTwoArrow (α := α))
  cases quot_out_01_cases with
  | inl h => simp only [h.1, h.2]
             conv_lhs => arg 2; ext x
                         rw [show (x 0, x 1) = MeasurableEquiv.finTwoArrow x by
                             simp [MeasurableEquiv.finTwoArrow_apply]]
             exact hmp.integral_comp hemb (fun p => W.toAEEqFun p)
  | inr h => simp only [h.1, h.2]; rw [integral_swap_on_pi W]
             conv_lhs => arg 2; ext x
                         rw [show (x 0, x 1) = MeasurableEquiv.finTwoArrow x by
                             simp [MeasurableEquiv.finTwoArrow_apply]]
             exact hmp.integral_comp hemb (fun p => W.toAEEqFun p)

/-- Convert integral to rectIntegralDiff over univ × univ. -/
private lemma integral_eq_rectIntegralDiff_univ (U W : Graphon α μ) :
    ∫ p, (U.toAEEqFun p - W.toAEEqFun p) ∂(μ.prod μ) = rectIntegralDiff U W univ univ := by
  unfold rectIntegralDiff
  rw [Set.univ_prod_univ]
  exact setIntegral_univ.symm

/-- Counting lemma for K₂: the complete graph on 2 vertices.

This is a base case that can be proven directly without the full layer cake machinery,
since K₂ has exactly one edge and the homDensity integral directly equals the
rectIntegralDiff over univ × univ. -/
theorem homDensity_sub_le_completeGraph_two (U W : Graphon α μ) :
    |homDensity (completeGraph (Fin 2)) U - homDensity (completeGraph (Fin 2)) W| ≤
      (completeGraph (Fin 2)).edgeFinset.card * cutNormDiff U W := by
  rw [homDensity_completeGraph_two U, homDensity_completeGraph_two W]
  rw [← integral_sub (SymmKernel.graphon_integrable U) (SymmKernel.graphon_integrable W)]
  rw [integral_eq_rectIntegralDiff_univ U W]
  have hle := abs_rectIntegralDiff_le U W MeasurableSet.univ MeasurableSet.univ
  have hcard : (completeGraph (Fin 2)).edgeFinset.card = 1 := by native_decide
  rw [hcard, Nat.cast_one, one_mul]
  exact hle

/-! ### General counting lemma -/

/-- For factored weights f(x_u)·g(x_v) with f,g ∈ [0,1] measurable, the weighted integral
of (U - W) over `Measure.pi` is bounded by `cutNormDiff U W`.

The key step is that the pair map `(x u, x v)` pushes forward `Measure.pi` to `μ.prod μ`
(by coordinate independence), so we can convert to the iterated integral form and apply
`abs_weighted_integral_diff_le`. -/
private lemma abs_weighted_pi_integral_diff_le (U W : Graphon α μ) (u v : V) (huv : u ≠ v)
    (f g : α → ℝ) (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_bound : ∀ x, f x ∈ Set.Icc 0 1) (hg_bound : ∀ x, g x ∈ Set.Icc 0 1) :
    |∫ x : V → α, f (x u) * g (x v) *
      (U.toAEEqFun (x u, x v) - W.toAEEqFun (x u, x v))
    ∂Measure.pi (fun _ => μ)| ≤ cutNormDiff U W := by
  set φ : (V → α) → α × α := fun x => (x u, x v)
  have hφ_meas : Measurable φ :=
    Measurable.prodMk (measurable_pi_apply _) (measurable_pi_apply _)
  have h_map_eq : Measure.map φ (Measure.pi (fun _ : V => μ)) = μ.prod μ := by
    have h_indep : ProbabilityTheory.IndepFun
        (fun x : V → α => x u) (fun x : V → α => x v) (Measure.pi (fun _ : V => μ)) := by
      have := (ProbabilityTheory.iIndepFun_pi (μ := fun _ : V => μ)
        (fun _ => aemeasurable_id)).indepFun huv
      simpa only [id] using this
    rw [show φ = fun x => ((fun x : V → α => x u) x, (fun x : V → α => x v) x) from rfl]
    rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      (measurable_pi_apply _).aemeasurable (measurable_pi_apply _).aemeasurable |>.mp h_indep,
      (measurePreserving_eval (fun _ : V => μ) u).map_eq,
      (measurePreserving_eval (fun _ : V => μ) v).map_eq]
  set h : α × α → ℝ := fun p => f p.1 * g p.2 * (U.toAEEqFun p - W.toAEEqFun p)
  have h_comp : ∀ x : V → α, f (x u) * g (x v) *
      (U.toAEEqFun (x u, x v) - W.toAEEqFun (x u, x v)) = h (φ x) := fun _ => rfl
  simp_rw [h_comp]
  have h_int : Integrable h (μ.prod μ) := by
    apply Integrable.bdd_mul
        ((SymmKernel.graphon_integrable U).sub (SymmKernel.graphon_integrable W))
    · exact ((hf_meas.comp measurable_fst).mul
        (hg_meas.comp measurable_snd)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf_bound p.1).1 (hg_bound p.2).1)]
        exact mul_le_one₀ (hf_bound p.1).2 (hg_bound p.2).1 (hg_bound p.2).2)
  have h_eq : ∫ x : V → α, h (φ x) ∂Measure.pi (fun _ => μ) =
      ∫ p, h p ∂(μ.prod μ) := by
    rw [← h_map_eq]
    exact (integral_map hφ_meas.aemeasurable
      (by rw [h_map_eq]; exact h_int.aestronglyMeasurable)).symm
  rw [h_eq, integral_prod _ h_int]
  exact abs_weighted_integral_diff_le U W f g hf_meas hg_meas hf_bound hg_bound

/-- Integrability of a product of [0,1]-valued graphon evaluations times a difference
of products. Both terms are bounded a.e., so the product is integrable on
a probability space. -/
private lemma counting_integrable_term (U W : Graphon α μ)
    (S R : Finset (Sym2 V)) (f : Sym2 V → Graphon α μ)
    (hS_edges : ∀ e ∈ S, (Quot.out e).1 ≠ (Quot.out e).2)
    (hR_edges : ∀ e ∈ R, (Quot.out e).1 ≠ (Quot.out e).2) :
    Integrable (fun x : V → α =>
      (∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
      (∏ e ∈ S, U.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
       ∏ e ∈ S, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)))
      (Measure.pi (fun _ => μ)) := by
  -- The integrand is a product of [0,1]-valued terms times a difference in [-1,1],
  -- hence bounded in [-1,1]. On a finite measure space, bounded a.e. functions are integrable.
  -- Helper: graphon eval at an edge is AEMeasurable w.r.t. Measure.pi
  have graphon_eval_aem : ∀ (G : Graphon α μ) (e : Sym2 V),
      (Quot.out e).1 ≠ (Quot.out e).2 →
      AEMeasurable (fun x : V → α => G.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
        (Measure.pi (fun _ => μ)) := by
    intro G e hne
    have h_pair : Measurable (fun x : V → α => (x (Quot.out e).1, x (Quot.out e).2)) :=
      Measurable.prodMk (measurable_pi_apply _) (measurable_pi_apply _)
    have h_indep : ProbabilityTheory.iIndepFun (fun i (x : V → α) => x i)
        (Measure.pi (fun _ : V => μ)) :=
      ProbabilityTheory.iIndepFun_pi (fun _ => aemeasurable_id)
    have h_indep_pair := h_indep.indepFun hne
    have h_map : Measure.map (fun x => (x (Quot.out e).1, x (Quot.out e).2))
        (Measure.pi (fun _ : V => μ)) =
        (Measure.map (fun x => x (Quot.out e).1) (Measure.pi (fun _ : V => μ))).prod
        (Measure.map (fun x => x (Quot.out e).2) (Measure.pi (fun _ : V => μ))) := by
      rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        (measurable_pi_apply _).aemeasurable (measurable_pi_apply _).aemeasurable] at h_indep_pair
      exact h_indep_pair
    have h_marg₁ : Measure.map (fun x => x (Quot.out e).1) (Measure.pi (fun _ : V => μ)) = μ :=
      (MeasureTheory.measurePreserving_eval (fun _ : V => μ) (Quot.out e).1).map_eq
    have h_marg₂ : Measure.map (fun x => x (Quot.out e).2) (Measure.pi (fun _ : V => μ)) = μ :=
      (MeasureTheory.measurePreserving_eval (fun _ : V => μ) (Quot.out e).2).map_eq
    have h_map_eq : Measure.map (fun x => (x (Quot.out e).1, x (Quot.out e).2))
        (Measure.pi (fun _ : V => μ)) = μ.prod μ := by
      rw [h_map, h_marg₁, h_marg₂]
    have h_aem_map : AEMeasurable G.toAEEqFun
        (Measure.map (fun x => (x (Quot.out e).1, x (Quot.out e).2))
          (Measure.pi (fun _ : V => μ))) := by
      rw [h_map_eq]; exact G.toAEEqFun.aemeasurable
    exact h_aem_map.comp_measurable h_pair
  -- AEMeasurability of product over R
  have hR_aem : AEMeasurable (fun x : V → α =>
      ∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
      (Measure.pi (fun _ => μ)) :=
    Finset.aemeasurable_fun_prod R (fun e he => graphon_eval_aem (f e) e (hR_edges e he))
  -- AEMeasurability of each product over S
  have hSU_aem : AEMeasurable (fun x : V → α =>
      ∏ e ∈ S, U.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
      (Measure.pi (fun _ => μ)) :=
    Finset.aemeasurable_fun_prod S (fun e he => graphon_eval_aem U e (hS_edges e he))
  have hSW_aem : AEMeasurable (fun x : V → α =>
      ∏ e ∈ S, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
      (Measure.pi (fun _ => μ)) :=
    Finset.aemeasurable_fun_prod S (fun e he => graphon_eval_aem W e (hS_edges e he))
  -- AEMeasurability of the full integrand
  have h_aem : AEMeasurable (fun x : V → α =>
      (∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
      (∏ e ∈ S, U.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
       ∏ e ∈ S, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)))
      (Measure.pi (fun _ => μ)) :=
    hR_aem.mul (hSU_aem.sub hSW_aem)
  -- A.e. bound: each graphon eval is in [0,1] a.e., so products are in [0,1],
  -- difference is in [-1,1], and the full product is in [-1,1].
  have h_ae_bound : ∀ᵐ x ∂Measure.pi (fun _ : V => μ),
      (∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
      (∏ e ∈ S, U.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
       ∏ e ∈ S, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) ∈
      Set.Icc (-1 : ℝ) 1 := by
    -- Collect a.e. bounds for all graphon evals at edges in R and S
    have hR_ae : ∀ e ∈ R, ∀ᵐ x ∂Measure.pi (fun _ : V => μ),
        (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1 :=
      fun e he => graphonEval_mem_Icc_ae (f e) (hR_edges e he)
    have hSU_ae : ∀ e ∈ S, ∀ᵐ x ∂Measure.pi (fun _ : V => μ),
        U.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1 :=
      fun e he => graphonEval_mem_Icc_ae U (hS_edges e he)
    have hSW_ae : ∀ e ∈ S, ∀ᵐ x ∂Measure.pi (fun _ : V => μ),
        W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1 :=
      fun e he => graphonEval_mem_Icc_ae W (hS_edges e he)
    -- Combine into one a.e. statement using Finset induction
    have collect : ∀ (T' : Finset (Sym2 V)) (g : Sym2 V → (V → α) → ℝ),
        (∀ e ∈ T', ∀ᵐ x ∂Measure.pi (fun _ : V => μ), g e x ∈ Set.Icc 0 1) →
        ∀ᵐ x ∂Measure.pi (fun _ : V => μ), ∀ e ∈ T', g e x ∈ Set.Icc 0 1 := by
      intro T' g hg
      induction T' using Finset.induction with
      | empty => simp
      | @insert a s' _ ih =>
        have hs1 := hg a (Finset.mem_insert_self a s')
        have hs2 := ih (fun e he => hg e (Finset.mem_insert_of_mem he))
        filter_upwards [hs1, hs2] with x hx1 hx2 e he
        rcases Finset.mem_insert.mp he with rfl | he'
        · exact hx1
        · exact hx2 e he'
    have hR_all := collect R (fun e x => (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
      (fun e he => hR_ae e he)
    have hSU_all := collect S (fun e x => U.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
      (fun e he => hSU_ae e he)
    have hSW_all := collect S (fun e x => W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
      (fun e he => hSW_ae e he)
    filter_upwards [hR_all, hSU_all, hSW_all] with x hxR hxSU hxSW
    -- Now prove the pointwise bound
    have hR_prod_nn : 0 ≤ ∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) :=
      Finset.prod_nonneg (fun e he => (hxR e he).1)
    have hR_prod_le : ∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ≤ 1 :=
      Finset.prod_le_one (fun e he => (hxR e he).1) (fun e he => (hxR e he).2)
    have hSU_prod_nn : 0 ≤ ∏ e ∈ S, U.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) :=
      Finset.prod_nonneg (fun e he => (hxSU e he).1)
    have hSU_prod_le : ∏ e ∈ S, U.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ≤ 1 :=
      Finset.prod_le_one (fun e he => (hxSU e he).1) (fun e he => (hxSU e he).2)
    have hSW_prod_nn : 0 ≤ ∏ e ∈ S, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) :=
      Finset.prod_nonneg (fun e he => (hxSW e he).1)
    have hSW_prod_le : ∏ e ∈ S, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ≤ 1 :=
      Finset.prod_le_one (fun e he => (hxSW e he).1) (fun e he => (hxSW e he).2)
    -- The difference is in [-1, 1]
    have h_diff_lower : -1 ≤ ∏ e ∈ S, U.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
        ∏ e ∈ S, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) := by linarith
    have h_diff_upper : ∏ e ∈ S, U.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
        ∏ e ∈ S, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ≤ 1 := by linarith
    -- Product of [0,1] and [-1,1] is in [-1,1]
    set pR := ∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)
    set d := ∏ e ∈ S, U.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
             ∏ e ∈ S, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)
    constructor
    · -- Lower bound: pR * d ≥ -1
      -- Since 0 ≤ pR ≤ 1 and -1 ≤ d ≤ 1, we have pR * d ≥ -1
      nlinarith [sq_nonneg pR, sq_nonneg d]
    · -- Upper bound: pR * d ≤ 1
      nlinarith [sq_nonneg pR, sq_nonneg d]
  exact Integrable.of_mem_Icc (-1) 1 h_aem h_ae_bound

set_option maxHeartbeats 1600000 in
/-- Key helper for the counting lemma: weighted integral of graphon difference
bounded by cut norm.

Given a product of graphon evaluations at edges in `T` (each assigned an arbitrary
graphon via `f`), and a distinguished edge `e₀ ∉ T`, the integral of the product
times `(U_{e₀} - W_{e₀})` is bounded by `cutNormDiff U W`.

The proof decomposes `Measure.pi` via `measurePreserving_piEquivPiSubtypeProd` into
"pair" coordinates `(x_u, x_v)` (endpoints of `e₀`) and "rest" coordinates, then
applies Fubini (`integral_prod`). For each fixed rest assignment, edges in T partition
into those touching only `u₀`, those touching only `v₀`, and those touching neither.
Since `e₀ ∉ T`, no edge in T touches both `u₀` and `v₀`, so the weight factors as
`C(rest) · f(x_u) · g(x_v)`, and `abs_weighted_integral_diff_le` gives the bound.

See Lovász [2012], Theorem 10.23. -/
private lemma weighted_prod_graphon_diff_le
    (U W : Graphon α μ) (T : Finset (Sym2 V)) (e₀ : Sym2 V)
    (he₀T : e₀ ∉ T)
    (f : Sym2 V → Graphon α μ)
    (hT_edges : ∀ e ∈ T, (Quot.out e).1 ≠ (Quot.out e).2)
    (he₀_edge : (Quot.out e₀).1 ≠ (Quot.out e₀).2) :
    |∫ x : V → α,
      (∏ e ∈ T, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
      (U.toAEEqFun (x (Quot.out e₀).1, x (Quot.out e₀).2) -
       W.toAEEqFun (x (Quot.out e₀).1, x (Quot.out e₀).2))
    ∂Measure.pi (fun _ => μ)| ≤ cutNormDiff U W := by
  set u₀ := (Quot.out e₀).1 with hu₀_def
  set v₀ := (Quot.out e₀).2 with hv₀_def
  set F : (V → α) → ℝ := fun x =>
    (∏ e ∈ T, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
    (U.toAEEqFun (x u₀, x v₀) - W.toAEEqFun (x u₀, x v₀)) with hF_def
  set p : V → Prop := fun i => i = u₀ ∨ i = v₀ with hp_def
  set equiv := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => α) p
  set π := Measure.pi (fun _ : V => μ)
  set π_pair := Measure.pi (fun _ : {i : V // p i} => μ)
  set π_rest := Measure.pi (fun _ : {i : V // ¬p i} => μ)
  -- Rewrite integral via the decomposition
  have h_rewrite : ∫ x, F x ∂π = ∫ y, F (equiv.symm y) ∂(π_pair.prod π_rest) := by
    have mp := measurePreserving_piEquivPiSubtypeProd (fun _ : V => μ) p
    have key := mp.integral_comp' (fun y => F (equiv.symm y))
    convert key using 1
    congr 1; ext x; congr 1
    exact (equiv.symm_apply_apply x).symm
  rw [show ∫ x, (∏ e ∈ T, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
    (U.toAEEqFun (x u₀, x v₀) - W.toAEEqFun (x u₀, x v₀)) ∂π = ∫ x, F x ∂π from rfl]
  rw [h_rewrite]
  -- Integrability
  have hF_int : Integrable (fun y => F (equiv.symm y)) (π_pair.prod π_rest) := by
    have hF_pi : Integrable F π := by
      have := counting_integrable_term U W {e₀} T f
        (by intro e he; simp only [Finset.mem_singleton] at he; rw [he]; exact he₀_edge)
        hT_edges
      simp only [Finset.prod_singleton] at this; exact this
    have mp := measurePreserving_piEquivPiSubtypeProd (fun _ : V => μ) p
    rw [show (fun y => F (equiv.symm y)) = F ∘ equiv.symm from rfl]
    rw [← mp.map_eq, integrable_map_equiv equiv]
    convert hF_pi using 1; ext x; simp [Function.comp]
  -- Fubini + triangle inequality + per-section bound
  calc |∫ y, F (equiv.symm y) ∂(π_pair.prod π_rest)|
      = |∫ rest, (∫ pair, F (equiv.symm (pair, rest)) ∂π_pair) ∂π_rest| := by
        rw [integral_prod_symm _ hF_int]
    _ ≤ ∫ rest, |∫ pair, F (equiv.symm (pair, rest)) ∂π_pair| ∂π_rest :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _, cutNormDiff U W ∂π_rest := by
        apply integral_mono_ae
        · exact hF_int.integral_prod_right.norm
        · exact integrable_const _
        · -- Per-section bound: for a.e. rest, |inner integral| ≤ cutNormDiff U W
          -- First derive: under π, all edge evals in T are a.e. in [0,1]
          have h_all_evals_ae : ∀ᵐ x ∂π, ∀ e ∈ T,
              (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1 := by
            have h_each : ∀ e ∈ T, ∀ᵐ x ∂π,
                (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1 :=
              fun e he => graphonEval_mem_Icc_ae (f e) (hT_edges e he)
            -- Combine finitely many a.e. properties
            have : ∀ (T' : Finset (Sym2 V)),
                (∀ e ∈ T', ∀ᵐ x ∂π,
                  (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1) →
                ∀ᵐ x ∂π, ∀ e ∈ T',
                  (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1 := by
              intro T'
              induction T' using Finset.induction with
              | empty => intro _; simp
              | @insert a s' _ ih =>
                intro h_each'
                filter_upwards [h_each' a (Finset.mem_insert_self a s'),
                  ih (fun e he => h_each' e (Finset.mem_insert_of_mem he))]
                  with x hx1 hx2 e he
                rcases Finset.mem_insert.mp he with rfl | he'
                · exact hx1
                · exact hx2 e he'
            exact this T h_each
          -- Push through equiv: under π_pair.prod π_rest, the same bound holds
          have h_decomp_ae : ∀ᵐ y ∂(π_pair.prod π_rest), ∀ e ∈ T,
              (f e).toAEEqFun (equiv.symm y (Quot.out e).1,
                                equiv.symm y (Quot.out e).2) ∈ Set.Icc 0 1 := by
            have mp := measurePreserving_piEquivPiSubtypeProd (fun _ : V => μ) p
            exact (mp.symm equiv).quasiMeasurePreserving.ae h_all_evals_ae
          -- Swap to get rest first: under π_rest.prod π_pair
          have h_decomp_swap : ∀ᵐ y ∂(π_rest.prod π_pair), ∀ e ∈ T,
              (f e).toAEEqFun (equiv.symm y.swap (Quot.out e).1,
                                equiv.symm y.swap (Quot.out e).2) ∈ Set.Icc 0 1 := by
            have h_swap_mp : MeasurePreserving Prod.swap (π_rest.prod π_pair) (π_pair.prod π_rest) :=
              Measure.measurePreserving_swap
            exact h_swap_mp.quasiMeasurePreserving.ae h_decomp_ae
          -- Fubini: for a.e. rest, for a.e. pair, all evals in [0,1]
          have h_ae_rest : ∀ᵐ rest ∂π_rest, ∀ᵐ pair ∂π_pair, ∀ e ∈ T,
              (f e).toAEEqFun (equiv.symm (pair, rest) (Quot.out e).1,
                                equiv.symm (pair, rest) (Quot.out e).2) ∈ Set.Icc 0 1 :=
            Measure.ae_ae_of_ae_prod h_decomp_swap
          filter_upwards [h_ae_rest] with rest h_pair_ae
          -- Key subtypes for the pair coordinates
          set u₀s : {i : V // p i} := ⟨u₀, Or.inl rfl⟩
          set v₀s : {i : V // p i} := ⟨v₀, Or.inr rfl⟩
          have huv_s : u₀s ≠ v₀s := fun h => he₀_edge (congr_arg Subtype.val h)
          -- The substitution function: sub(a, b)(i) = a if i=u₀, b if i=v₀, rest(i) otherwise
          have h_not_p : ∀ i, i ≠ u₀ → i ≠ v₀ → ¬p i := by
            intro i h1 h2 hi; rcases hi with rfl | rfl <;> contradiction
          set sub : α → α → V → α := fun a b i =>
            if h1 : i = u₀ then a else if h2 : i = v₀ then b
            else rest ⟨i, h_not_p i h1 h2⟩
          -- equiv.symm(pair, rest) agrees with sub(pair u₀s, pair v₀s)
          have h_equiv_sub : ∀ (pair : {i // p i} → α) (i : V),
              equiv.symm (pair, rest) i = sub (pair u₀s) (pair v₀s) i := by
            intro pair i
            -- equiv.symm (pair, rest) i = if p i then pair ⟨i,_⟩ else rest ⟨i,_⟩
            have h_symm_def : equiv.symm (pair, rest) i =
                if h : p i then pair ⟨i, h⟩ else rest ⟨i, h⟩ := by
              simp [equiv, MeasurableEquiv.piEquivPiSubtypeProd,
                Equiv.piEquivPiSubtypeProd]
            by_cases hi_u : i = u₀
            · -- i = u₀: p i holds, equiv gives pair ⟨u₀, _⟩ = pair u₀s
              subst hi_u
              rw [h_symm_def, dif_pos (Or.inl rfl : p u₀)]
              simp only [sub, dite_true]; exact congr_arg pair (Subtype.ext rfl)
            · by_cases hi_v : i = v₀
              · -- i = v₀: p i holds, equiv gives pair ⟨v₀, _⟩ = pair v₀s
                subst hi_v
                rw [h_symm_def, dif_pos (Or.inr rfl : p v₀)]
                simp only [sub, dif_neg hi_u, dite_true]; exact congr_arg pair (Subtype.ext rfl)
              · -- i ≠ u₀, i ≠ v₀: ¬p i, both sides give rest
                rw [h_symm_def, dif_neg (h_not_p i hi_u hi_v)]
                simp only [sub, dif_neg hi_u, dif_neg hi_v]
          -- Rewrite the integrand using sub
          have h_integrand_eq : ∀ (pair : {i // p i} → α),
              F (equiv.symm (pair, rest)) =
              (∏ e ∈ T, (f e).toAEEqFun
                (sub (pair u₀s) (pair v₀s) (Quot.out e).1,
                 sub (pair u₀s) (pair v₀s) (Quot.out e).2)) *
              (U.toAEEqFun (pair u₀s, pair v₀s) -
               W.toAEEqFun (pair u₀s, pair v₀s)) := by
            intro pair
            -- Key substitution equalities
            have h_sub_u : sub (pair u₀s) (pair v₀s) u₀ = pair u₀s := by
              simp only [sub, dite_true]
            have h_sub_v : sub (pair u₀s) (pair v₀s) v₀ = pair v₀s := by
              simp only [sub, dif_neg (Ne.symm he₀_edge), dite_true]
            simp only [F, hF_def]
            have h_coord : ∀ (i : V), equiv.symm (pair, rest) i =
                sub (pair u₀s) (pair v₀s) i := h_equiv_sub pair
            simp_rw [h_coord]
            rw [h_sub_u, h_sub_v]
          -- Map from π_pair to μ × μ via φ(pair) = (pair u₀s, pair v₀s)
          set φ : ({i // p i} → α) → α × α := fun pair => (pair u₀s, pair v₀s)
          have hφ_meas : Measurable φ :=
            Measurable.prodMk (measurable_pi_apply _) (measurable_pi_apply _)
          have h_map_φ : Measure.map φ π_pair = μ.prod μ := by
            have h_indep : ProbabilityTheory.IndepFun
                (fun pair : {i // p i} → α => pair u₀s)
                (fun pair : {i // p i} → α => pair v₀s)
                π_pair := by
              have := (ProbabilityTheory.iIndepFun_pi
                (μ := fun _ : {i // p i} => μ)
                (fun _ => aemeasurable_id)).indepFun huv_s
              simpa only [id] using this
            rw [show φ = fun pair => ((fun pair : {i // p i} → α => pair u₀s) pair,
                (fun pair : {i // p i} → α => pair v₀s) pair) from rfl]
            rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
              (measurable_pi_apply _).aemeasurable
              (measurable_pi_apply _).aemeasurable |>.mp h_indep,
              (measurePreserving_eval (fun _ : {i // p i} => μ) u₀s).map_eq,
              (measurePreserving_eval (fun _ : {i // p i} => μ) v₀s).map_eq]
          -- No edge in T has both u₀ and v₀ as endpoints
          have h_no_uv : ∀ e ∈ T,
              ¬((Quot.out e).1 = u₀ ∧ (Quot.out e).2 = v₀) ∧
              ¬((Quot.out e).1 = v₀ ∧ (Quot.out e).2 = u₀) := by
            intro e he
            have h_out_e : s((Quot.out e).1, (Quot.out e).2) = e := Quot.out_eq e
            have h_out_e₀ : s((Quot.out e₀).1, (Quot.out e₀).2) = e₀ := Quot.out_eq e₀
            constructor
            · rintro ⟨h1, h2⟩
              apply he₀T
              have : e = e₀ := by
                rw [← h_out_e, ← h_out_e₀, h1, h2]
              rw [this] at he; exact he
            · rintro ⟨h1, h2⟩
              apply he₀T
              have : e = e₀ := by
                rw [← h_out_e, ← h_out_e₀, h1, h2, Sym2.eq_swap]
              rw [this] at he; exact he
          -- Split T based on whether edge touches v₀
          set touchesV : Sym2 V → Bool := fun e =>
            decide ((Quot.out e).1 = v₀) || decide ((Quot.out e).2 = v₀)
          set T_u := T.filter (fun e => !touchesV e)
          set T_v := T.filter (fun e => touchesV e)
          have h_T_disj : Disjoint T_u T_v := by
            rw [Finset.disjoint_filter]; intro e _; simp
          -- For e ∈ T_u: weight depends only on a (not on b)
          have h_Tu_no_v : ∀ e ∈ T_u, (Quot.out e).1 ≠ v₀ ∧ (Quot.out e).2 ≠ v₀ := by
            intro e he
            have hmem := (Finset.mem_filter.mp he).2
            simp only [T_u, touchesV] at hmem
            constructor
            · intro h; simp [h] at hmem
            · intro h; simp [h] at hmem
          -- For e ∈ T_v: touching v₀ but not u₀ (since both would make e = e₀)
          have h_Tv_no_u : ∀ e ∈ T_v, (Quot.out e).1 ≠ u₀ ∧ (Quot.out e).2 ≠ u₀ := by
            intro e he
            have heT := (Finset.mem_filter.mp he).1
            have h_touches : (Quot.out e).1 = v₀ ∨ (Quot.out e).2 = v₀ := by
              simp only [T_v, Finset.mem_filter, touchesV, Bool.or_eq_true,
                decide_eq_true_eq] at he
              exact he.2
            have h_nb := h_no_uv e heT
            -- h_nb.1 : ¬(.1 = u₀ ∧ .2 = v₀)
            -- h_nb.2 : ¬(.1 = v₀ ∧ .2 = u₀)
            constructor
            · intro h_eq  -- (Quot.out e).1 = u₀
              rcases h_touches with h | h
              · -- .1 = v₀, but also .1 = u₀, contradicts u₀ ≠ v₀
                exact he₀_edge (h_eq.symm.trans h)
              · -- .2 = v₀, and .1 = u₀ → contradicts h_nb.1
                exact h_nb.1 ⟨h_eq, h⟩
            · intro h_eq  -- (Quot.out e).2 = u₀
              rcases h_touches with h | h
              · -- .1 = v₀, and .2 = u₀ → contradicts h_nb.2
                exact h_nb.2 ⟨h, h_eq⟩
              · -- .2 = v₀, but also .2 = u₀, contradicts u₀ ≠ v₀
                exact he₀_edge (h_eq.symm.trans h)
          -- For e ∈ T_u: weight(e, a, b) = weight(e, a, b') for all b, b'
          -- Helper: sub a b i doesn't depend on b when i ≠ v₀
          have sub_indep_b : ∀ a b₁ b₂ i, i ≠ v₀ → sub a b₁ i = sub a b₂ i := by
            intro a b₁ b₂ i hne
            simp only [sub, dif_neg hne]
          -- Helper: sub a b i doesn't depend on a when i ≠ u₀
          have sub_indep_a : ∀ a₁ a₂ b i, i ≠ u₀ → sub a₁ b i = sub a₂ b i := by
            intro a₁ a₂ b i hne
            simp only [sub, dif_neg hne]
          have h_Tu_indep : ∀ e ∈ T_u, ∀ a b₁ b₂,
              (f e).toAEEqFun (sub a b₁ (Quot.out e).1, sub a b₁ (Quot.out e).2) =
              (f e).toAEEqFun (sub a b₂ (Quot.out e).1, sub a b₂ (Quot.out e).2) := by
            intro e he a b₁ b₂
            have ⟨hne1, hne2⟩ := h_Tu_no_v e he
            rw [sub_indep_b a b₁ b₂ _ hne1, sub_indep_b a b₁ b₂ _ hne2]
          -- For e ∈ T_v: weight(e, a, b) = weight(e, a', b) for all a, a'
          have h_Tv_indep : ∀ e ∈ T_v, ∀ a₁ a₂ b,
              (f e).toAEEqFun (sub a₁ b (Quot.out e).1, sub a₁ b (Quot.out e).2) =
              (f e).toAEEqFun (sub a₂ b (Quot.out e).1, sub a₂ b (Quot.out e).2) := by
            intro e he a₁ a₂ b
            have ⟨hne1, hne2⟩ := h_Tv_no_u e he
            -- Since (.1) ≠ u₀ and (.2) ≠ u₀, the a argument is irrelevant
            have h1 : sub a₁ b (Quot.out e).1 = sub a₂ b (Quot.out e).1 := by
              simp only [sub, dif_neg hne1]
            have h2 : sub a₁ b (Quot.out e).2 = sub a₂ b (Quot.out e).2 := by
              simp only [sub, dif_neg hne2]
            rw [h1, h2]
          -- Define weight factors (clipped to [0,1])
          haveI : Nonempty α := by
            by_contra h; rw [not_nonempty_iff] at h
            exact absurd (Measure.eq_zero_of_isEmpty μ) (IsProbabilityMeasure.ne_zero μ)
          set b₀ := Classical.arbitrary α
          set a₀ := Classical.arbitrary α
          set f_raw : α → ℝ := fun a =>
            ∏ e ∈ T_u, (f e).toAEEqFun
              (sub a b₀ (Quot.out e).1, sub a b₀ (Quot.out e).2)
          set g_raw : α → ℝ := fun b =>
            ∏ e ∈ T_v, (f e).toAEEqFun
              (sub a₀ b (Quot.out e).1, sub a₀ b (Quot.out e).2)
          set f_clip : α → ℝ := fun a => max 0 (min 1 (f_raw a))
          set g_clip : α → ℝ := fun b => max 0 (min 1 (g_raw b))
          -- The original product factors: ∏_T w_e(sub a b) = f_raw(a) * g_raw(b)
          have h_prod_factor : ∀ a b,
              ∏ e ∈ T, (f e).toAEEqFun (sub a b (Quot.out e).1, sub a b (Quot.out e).2) =
              f_raw a * g_raw b := by
            intro a b
            have h_split : T = T_u ∪ T_v := by
              ext e; simp only [T_u, T_v, Finset.mem_union, Finset.mem_filter]
              constructor
              · intro he; by_cases h : touchesV e = true
                · exact Or.inr ⟨he, h⟩
                · exact Or.inl ⟨he, by simp [h]⟩
              · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
            rw [h_split, Finset.prod_union h_T_disj]
            congr 1
            · apply Finset.prod_congr rfl; intro e he
              exact h_Tu_indep e he a b b₀
            · apply Finset.prod_congr rfl; intro e he
              exact h_Tv_indep e he a a₀ b
          -- Measurability helpers
          have sub_a_meas : ∀ i, Measurable (fun a => sub a b₀ i) := by
            intro i
            by_cases h1 : i = u₀
            · simp only [sub, dif_pos h1]; exact measurable_id
            · simp only [sub, dif_neg h1]
              by_cases h2 : i = v₀
              · simp only [dif_pos h2]; exact measurable_const
              · simp only [dif_neg h2]; exact measurable_const
          have sub_b_meas : ∀ i, Measurable (fun b => sub a₀ b i) := by
            intro i
            by_cases h1 : i = u₀
            · simp only [sub, dif_pos h1]; exact measurable_const
            · simp only [sub, dif_neg h1]
              by_cases h2 : i = v₀
              · simp only [dif_pos h2]; exact measurable_id
              · simp only [dif_neg h2]; exact measurable_const
          have hf_raw_meas : Measurable f_raw := by
            apply Finset.measurable_prod; intro e _
            exact (f e).toAEEqFun.measurable.comp
              (Measurable.prodMk (sub_a_meas _) (sub_a_meas _))
          have hg_raw_meas : Measurable g_raw := by
            apply Finset.measurable_prod; intro e _
            exact (f e).toAEEqFun.measurable.comp
              (Measurable.prodMk (sub_b_meas _) (sub_b_meas _))
          have hf_clip_meas : Measurable f_clip :=
            Measurable.max measurable_const (Measurable.min measurable_const hf_raw_meas)
          have hg_clip_meas : Measurable g_clip :=
            Measurable.max measurable_const (Measurable.min measurable_const hg_raw_meas)
          -- Everywhere bounds for clipped functions
          have hf_clip_bound : ∀ x, f_clip x ∈ Set.Icc 0 1 :=
            fun x => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
          have hg_clip_bound : ∀ x, g_clip x ∈ Set.Icc 0 1 :=
            fun x => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
          -- From h_pair_ae, derive: for a.e. pair, f_raw(pair u₀s) ∈ [0,1]
          -- Each T_u edge eval doesn't depend on pair v₀s (by h_Tu_indep),
          -- so from h_pair_ae, the eval with b₀ is in [0,1] for a.e. pair too.
          have h_fraw_ae_pair : ∀ᵐ pair ∂π_pair, f_raw (pair u₀s) ∈ Set.Icc 0 1 := by
            filter_upwards [h_pair_ae] with pair h_all
            -- For each e ∈ T_u, the eval is in [0,1]
            have h_each_Tu : ∀ e ∈ T_u, (f e).toAEEqFun
                (sub (pair u₀s) b₀ (Quot.out e).1,
                 sub (pair u₀s) b₀ (Quot.out e).2) ∈ Set.Icc 0 1 := by
              intro e he
              have heT := (Finset.mem_filter.mp he).1
              -- h_all says the eval with equiv.symm(pair, rest) is in [0,1]
              have h_bound := h_all e heT
              -- Rewrite using h_equiv_sub to get sub form
              simp_rw [h_equiv_sub pair] at h_bound
              -- By h_Tu_indep, changing v₀s to b₀ doesn't matter
              rw [h_Tu_indep e he (pair u₀s) (pair v₀s) b₀] at h_bound
              exact h_bound
            exact ⟨Finset.prod_nonneg (fun e he => (h_each_Tu e he).1),
              Finset.prod_le_one (fun e he => (h_each_Tu e he).1)
                (fun e he => (h_each_Tu e he).2)⟩
          -- Similarly: for a.e. pair, g_raw(pair v₀s) ∈ [0,1]
          have h_graw_ae_pair : ∀ᵐ pair ∂π_pair, g_raw (pair v₀s) ∈ Set.Icc 0 1 := by
            filter_upwards [h_pair_ae] with pair h_all
            have h_each_Tv : ∀ e ∈ T_v, (f e).toAEEqFun
                (sub a₀ (pair v₀s) (Quot.out e).1,
                 sub a₀ (pair v₀s) (Quot.out e).2) ∈ Set.Icc 0 1 := by
              intro e he
              have heT := (Finset.mem_filter.mp he).1
              have h_bound := h_all e heT
              simp_rw [h_equiv_sub pair] at h_bound
              rw [h_Tv_indep e he (pair u₀s) a₀ (pair v₀s)] at h_bound
              exact h_bound
            exact ⟨Finset.prod_nonneg (fun e he => (h_each_Tv e he).1),
              Finset.prod_le_one (fun e he => (h_each_Tv e he).1)
                (fun e he => (h_each_Tv e he).2)⟩
          -- A.e. under π_pair, f_clip = f_raw and g_clip = g_raw
          have hf_eq_ae_pair : ∀ᵐ pair ∂π_pair,
              f_clip (pair u₀s) = f_raw (pair u₀s) := by
            filter_upwards [h_fraw_ae_pair] with pair ⟨ha0, ha1⟩
            simp only [f_clip, min_eq_right ha1, max_eq_right ha0]
          have hg_eq_ae_pair : ∀ᵐ pair ∂π_pair,
              g_clip (pair v₀s) = g_raw (pair v₀s) := by
            filter_upwards [h_graw_ae_pair] with pair ⟨hb0, hb1⟩
            simp only [g_clip, min_eq_right hb1, max_eq_right hb0]
          -- Now: rewrite integrand and use abs_weighted_pi_integral_diff_le
          -- Step 1: Rewrite integral using h_integrand_eq and h_prod_factor
          have h_integral_rw : ∫ pair, F (equiv.symm (pair, rest)) ∂π_pair =
              ∫ pair : {i // p i} → α,
                f_raw (pair u₀s) * g_raw (pair v₀s) *
                (U.toAEEqFun (pair u₀s, pair v₀s) -
                 W.toAEEqFun (pair u₀s, pair v₀s))
              ∂π_pair := by
            apply integral_congr_ae
            filter_upwards with pair
            rw [h_integrand_eq pair, h_prod_factor (pair u₀s) (pair v₀s)]
          -- Step 2: Replace f_raw with f_clip and g_raw with g_clip (a.e. equal)
          have h_integral_clip : ∫ pair : {i // p i} → α,
                f_raw (pair u₀s) * g_raw (pair v₀s) *
                (U.toAEEqFun (pair u₀s, pair v₀s) -
                 W.toAEEqFun (pair u₀s, pair v₀s))
              ∂π_pair =
              ∫ pair : {i // p i} → α,
                f_clip (pair u₀s) * g_clip (pair v₀s) *
                (U.toAEEqFun (pair u₀s, pair v₀s) -
                 W.toAEEqFun (pair u₀s, pair v₀s))
              ∂π_pair := by
            apply integral_congr_ae
            filter_upwards [hf_eq_ae_pair, hg_eq_ae_pair] with pair hu hv
            rw [hu, hv]
          -- Step 3: Apply abs_weighted_pi_integral_diff_le
          rw [h_integral_rw, h_integral_clip]
          exact abs_weighted_pi_integral_diff_le U W u₀s v₀s huv_s
            f_clip g_clip hf_clip_meas hg_clip_meas hf_clip_bound hg_clip_bound
    _ = cutNormDiff U W := by
        simp

/-- Strengthened counting lemma with weighted prefix product.

For a set of edges `S` (each with distinct endpoints), a prefix product of graphon
evaluations at edges in `R` (disjoint from `S`), the integral of the prefix times
the difference of products is bounded by `|S| * cutNormDiff`.

This is the induction step used to prove the counting lemma. -/
private lemma weighted_homDensity_sub_le
    (U W : Graphon α μ) (S : Finset (Sym2 V))
    (R : Finset (Sym2 V))
    (f : Sym2 V → Graphon α μ)
    (hRS : Disjoint R S)
    (hS_edges : ∀ e ∈ S, (Quot.out e).1 ≠ (Quot.out e).2)
    (hR_edges : ∀ e ∈ R, (Quot.out e).1 ≠ (Quot.out e).2) :
    |∫ x : V → α,
      (∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
      (∏ e ∈ S, U.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
       ∏ e ∈ S, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
    ∂Measure.pi (fun _ => μ)| ≤ S.card * cutNormDiff U W := by
  induction S using Finset.induction generalizing R f with
  | empty =>
    simp
  | @insert e₀ S' he₀ ih =>
    have he₀_edge : (Quot.out e₀).1 ≠ (Quot.out e₀).2 :=
      hS_edges e₀ (Finset.mem_insert_self e₀ S')
    have hS'_edges : ∀ e ∈ S', (Quot.out e).1 ≠ (Quot.out e).2 :=
      fun e he => hS_edges e (Finset.mem_insert_of_mem he)
    -- Key: e₀ ∉ R (from disjointness)
    have he₀R : e₀ ∉ R :=
      Finset.disjoint_right.mp hRS (Finset.mem_insert_self e₀ S')
    -- Set up R' = insert e₀ R, f' = Function.update f e₀ U
    set R' := insert e₀ R with hR'_def
    set f' : Sym2 V → Graphon α μ := Function.update f e₀ U with hf'_def
    -- Set up f'' for Term 2
    set f'' : Sym2 V → Graphon α μ := fun e => if e ∈ S' then W else f e with hf''_def
    -- Algebraic identity: the integrand splits as Term1 + Term2
    have h_eq : ∀ x : V → α,
        (∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
        (∏ e ∈ insert e₀ S', U.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
         ∏ e ∈ insert e₀ S', W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) =
        ((∏ e ∈ R', (f' e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
         (∏ e ∈ S', U.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
          ∏ e ∈ S', W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))) +
        ((∏ e ∈ R ∪ S', (f'' e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
         (U.toAEEqFun (x (Quot.out e₀).1, x (Quot.out e₀).2) -
          W.toAEEqFun (x (Quot.out e₀).1, x (Quot.out e₀).2))) := by
      intro x
      -- Simplify prod over R' = insert e₀ R with f' (update)
      have hR'_prod : ∏ e ∈ R', (f' e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) =
          U.toAEEqFun (x (Quot.out e₀).1, x (Quot.out e₀).2) *
          ∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) := by
        rw [hR'_def, Finset.prod_insert he₀R]
        congr 1
        · show (Function.update f e₀ U e₀).toAEEqFun _ = _
          rw [Function.update_self]
        · apply Finset.prod_congr rfl
          intro e he
          show (Function.update f e₀ U e).toAEEqFun _ = _
          have hne : e ≠ e₀ := fun heq => he₀R (heq ▸ he)
          rw [Function.update_of_ne hne]
      -- Simplify prod over R ∪ S' with f''
      have hRS'_prod : ∏ e ∈ R ∪ S', (f'' e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) =
          (∏ e ∈ R, (f e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
          (∏ e ∈ S', W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) := by
        rw [Finset.prod_union (Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hRS)]
        congr 1
        · apply Finset.prod_congr rfl
          intro e he
          simp only [hf''_def]
          have : e ∉ S' := Finset.disjoint_left.mp
            (Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hRS) he
          simp [this]
        · apply Finset.prod_congr rfl
          intro e he; simp only [hf''_def, if_pos he]
      rw [hR'_prod, hRS'_prod, Finset.prod_insert he₀, Finset.prod_insert he₀]
      ring
    -- Integrability of both terms
    have hR'_edges : ∀ e ∈ R', (Quot.out e).1 ≠ (Quot.out e).2 := by
      intro e he; rw [hR'_def] at he
      rcases Finset.mem_insert.mp he with rfl | he'
      · exact he₀_edge
      · exact hR_edges e he'
    have hRS'_edges : ∀ e ∈ R ∪ S', (Quot.out e).1 ≠ (Quot.out e).2 := by
      intro e he; rcases Finset.mem_union.mp he with he' | he'
      · exact hR_edges e he'
      · exact hS'_edges e he'
    have h_int1 : Integrable (fun x : V → α =>
        (∏ e ∈ R', (f' e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
        (∏ e ∈ S', U.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
         ∏ e ∈ S', W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)))
        (Measure.pi (fun _ => μ)) :=
      counting_integrable_term U W S' R' f' hS'_edges hR'_edges
    have h_int2 : Integrable (fun x : V → α =>
        (∏ e ∈ R ∪ S', (f'' e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
        (U.toAEEqFun (x (Quot.out e₀).1, x (Quot.out e₀).2) -
         W.toAEEqFun (x (Quot.out e₀).1, x (Quot.out e₀).2)))
        (Measure.pi (fun _ => μ)) := by
      -- The integrand is bounded a.e. by 2 (product of [0,1] times [-1,1])
      -- on a probability space, so it is integrable.
      have h_aux := counting_integrable_term U W {e₀} (R ∪ S') f''
        (by intro e he; simp only [Finset.mem_singleton] at he; rw [he]; exact he₀_edge)
        hRS'_edges
      -- Convert ∏ e ∈ {e₀}, G_e(x) to G_{e₀}(x) via Finset.prod_singleton
      simp only [Finset.prod_singleton] at h_aux
      exact h_aux
    -- Rewrite using the algebraic identity
    simp_rw [h_eq]
    rw [integral_add h_int1 h_int2]
    -- Triangle inequality + bounds
    have hR'S'_disj : Disjoint R' S' := by
      rw [hR'_def]
      exact Finset.disjoint_insert_left.mpr ⟨he₀, hRS.mono_right (Finset.subset_insert _ _)⟩
    have he₀_not_RS' : e₀ ∉ R ∪ S' := by
      rw [Finset.mem_union, not_or]; exact ⟨he₀R, he₀⟩
    calc |∫ x, _ ∂_ + ∫ x, _ ∂_|
        ≤ |∫ x : V → α,
            (∏ e ∈ R', (f' e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
            (∏ e ∈ S', U.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
             ∏ e ∈ S', W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
            ∂Measure.pi (fun _ => μ)| +
          |∫ x : V → α,
            (∏ e ∈ R ∪ S', (f'' e).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
            (U.toAEEqFun (x (Quot.out e₀).1, x (Quot.out e₀).2) -
             W.toAEEqFun (x (Quot.out e₀).1, x (Quot.out e₀).2))
            ∂Measure.pi (fun _ => μ)| := abs_add_le _ _
      _ ≤ S'.card * cutNormDiff U W + cutNormDiff U W :=
          add_le_add (ih R' f' hR'S'_disj hS'_edges hR'_edges)
            (weighted_prod_graphon_diff_le U W (R ∪ S') e₀ he₀_not_RS' f''
              hRS'_edges he₀_edge)
      _ = (insert e₀ S').card * cutNormDiff U W := by
          rw [Finset.card_insert_of_notMem he₀]; push_cast; ring

/-- The counting lemma: homomorphism density difference is bounded by cut norm.

For any graph F and graphons U, W on the same probability space:
`|t(F, U) - t(F, W)| ≤ |E(F)| · ‖U - W‖_□`

This is the key result showing that cut norm controls homomorphism densities. -/
theorem homDensity_sub_le (F : SimpleGraph V) [DecidableRel F.Adj]
    (U W : Graphon α μ) :
    |homDensity F U - homDensity F W| ≤ F.edgeFinset.card * cutNormDiff U W := by
  -- Express as integral of difference of products
  have h_edges : ∀ e ∈ F.edgeFinset, (Quot.out e).1 ≠ (Quot.out e).2 :=
    fun e he => edge_out_ne (SimpleGraph.mem_edgeFinset.mp he)
  -- homDensity = ∫ ∏ G_e dπ, so the difference = ∫ (∏ U_e - ∏ W_e) dπ
  -- = ∫ 1 * (∏ U_e - ∏ W_e) dπ = ∫ (∏_{e ∈ ∅} ...) * (∏ U_e - ∏ W_e) dπ
  have h_diff : homDensity F U - homDensity F W =
      ∫ x : V → α,
        (∏ e ∈ (∅ : Finset (Sym2 V)),
          U.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
        (∏ e ∈ F.edgeFinset, U.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) -
         ∏ e ∈ F.edgeFinset, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))
      ∂Measure.pi (fun _ => μ) := by
    simp only [Finset.prod_empty, one_mul]
    show (∫ x, homDensityIntegrand F U x ∂_) - (∫ x, homDensityIntegrand F W x ∂_) = _
    rw [← integral_sub (homDensityIntegrand_integrable F U) (homDensityIntegrand_integrable F W)]
    rfl
  rw [h_diff]
  exact weighted_homDensity_sub_le U W F.edgeFinset ∅ (fun _ => U)
    (Finset.disjoint_empty_left _) h_edges (by simp)

/-- Corollary: graphs with small cut distance have similar homomorphism densities.

The proof uses that homDensity is preserved under pullbacks (homDensity_pullback_mp):
- For any φ, ψ measure-preserving: homDensity F (pullback U φ) = homDensity F U
- So |homDensity F U - homDensity F W| = |homDensity F (pullback U φ) - homDensity F (pullback W ψ)|
- By homDensity_sub_le: ≤ |E(F)| * cutNormDiff (pullback U φ) (pullback W ψ)
- Taking inf over φ, ψ gives the bound by cutDistance -/
theorem homDensity_sub_le_of_cutDistance (F : SimpleGraph V) [DecidableRel F.Adj]
    (U W : Graphon α μ) :
    |homDensity F U - homDensity F W| ≤ F.edgeFinset.card * cutDistance U W := by
  -- The LHS is constant for any reparametrizations of U and W
  -- by homDensity_pullback_mp: homDensity F (pullback U φ hφ) = homDensity F U
  unfold cutDistance
  -- For each d in the infimum set, we have LHS ≤ |E(F)| * d
  -- Therefore LHS ≤ |E(F)| * sInf {...}
  have h_bdd : BddBelow {d : ℝ | ∃ (φ ψ : α → α) (hφ : MeasurePreserving φ μ μ)
      (hψ : MeasurePreserving ψ μ μ), d = cutNormDiff (pullback U φ hφ) (pullback W ψ hψ)} := by
    use 0
    intro d ⟨φ, ψ, hφ, hψ, hd⟩
    rw [hd]
    exact cutNormDiff_nonneg (pullback U φ hφ) (pullback W ψ hψ)
  have h_nonempty : {d : ℝ | ∃ (φ ψ : α → α) (hφ : MeasurePreserving φ μ μ)
      (hψ : MeasurePreserving ψ μ μ), d = cutNormDiff (pullback U φ hφ) (pullback W ψ hψ)}.Nonempty :=
    cutDistance_set_nonempty U W
  -- LHS ≤ |E(F)| * d for all d in the set
  have h_forall : ∀ d ∈ {d : ℝ | ∃ (φ ψ : α → α) (hφ : MeasurePreserving φ μ μ)
      (hψ : MeasurePreserving ψ μ μ), d = cutNormDiff (pullback U φ hφ) (pullback W ψ hψ)},
      |homDensity F U - homDensity F W| ≤ F.edgeFinset.card * d := by
    intro d ⟨φ, ψ, hφ, hψ, hd⟩
    -- By homDensity_pullback_mp, homDensity is preserved under pullback
    rw [← homDensity_pullback_mp F U φ hφ, ← homDensity_pullback_mp F W ψ hψ, hd]
    -- Now apply homDensity_sub_le
    exact homDensity_sub_le F (pullback U φ hφ) (pullback W ψ hψ)
  -- Conclude: LHS ≤ |E(F)| * d for all d implies LHS ≤ |E(F)| * sInf
  by_cases hcard : F.edgeFinset.card = 0
  · -- If no edges, LHS = 0 and RHS = 0 * cutDistance = 0
    -- First show homDensity F U = homDensity F W = 1 for empty graphs
    have h_empty : F.edgeFinset = ∅ := Finset.card_eq_zero.mp hcard
    have h_hom_eq : homDensity F U = homDensity F W := by
      simp only [homDensity_eq_integral, homDensityIntegrand, h_empty, Finset.prod_empty]
    rw [h_hom_eq, sub_self, abs_zero, hcard, Nat.cast_zero, zero_mul]
  · -- Non-empty graph: use csInf property
    have hcard_pos : (0 : ℝ) < F.edgeFinset.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard)
    -- LHS / |E(F)| ≤ d for all d ∈ S, so LHS / |E(F)| ≤ sInf S
    have h_div : |homDensity F U - homDensity F W| / F.edgeFinset.card ≤ sInf
        {d : ℝ | ∃ (φ ψ : α → α) (hφ : MeasurePreserving φ μ μ)
         (hψ : MeasurePreserving ψ μ μ), d = cutNormDiff (pullback U φ hφ) (pullback W ψ hψ)} := by
      apply le_csInf h_nonempty
      intro d hd
      have hle := h_forall d hd
      rw [div_le_iff₀ hcard_pos]
      calc |homDensity F U - homDensity F W|
          ≤ F.edgeFinset.card * d := hle
        _ = d * F.edgeFinset.card := mul_comm _ _
    rw [div_le_iff₀ hcard_pos] at h_div
    calc |homDensity F U - homDensity F W|
        ≤ sInf {d : ℝ | ∃ (φ ψ : α → α) (hφ : MeasurePreserving φ μ μ)
            (hψ : MeasurePreserving ψ μ μ), d = cutNormDiff (pullback U φ hφ) (pullback W ψ hψ)} *
            F.edgeFinset.card := h_div
      _ = F.edgeFinset.card * sInf _ := mul_comm _ _

/-- If cut distance is zero, homomorphism densities are equal.

This is a key consequence: weakly isomorphic graphons have the same
homomorphism densities for all graphs F. -/
theorem homDensity_eq_of_cutDistance_zero (F : SimpleGraph V) [DecidableRel F.Adj]
    (U W : Graphon α μ) (h : cutDistance U W = 0) :
    homDensity F U = homDensity F W := by
  have hle := homDensity_sub_le_of_cutDistance F U W
  rw [h, mul_zero] at hle
  have habs : |homDensity F U - homDensity F W| = 0 :=
    le_antisymm hle (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

end Counting

/-! ### Continuity properties -/

section Continuity

variable [IsProbabilityMeasure μ]

/-- Homomorphism density difference is bounded by edge count times cut norm difference.

This is the quantitative version of continuity with respect to cut norm.

**Note**: We use `max 1 F.edgeFinset.card` in the denominator to handle the empty graph case.
For empty graphs, both homomorphism densities equal 1, so the bound is trivially satisfied. -/
theorem homDensity_continuous_cutNormDiff (F : SimpleGraph V) [DecidableRel F.Adj]
    (U W : Graphon α μ) (ε : ℝ) (hε : ε > 0)
    (h : cutNormDiff U W < ε / max 1 F.edgeFinset.card) :
    |homDensity F U - homDensity F W| < ε := by
  by_cases hF : F.edgeFinset.card = 0
  · -- Empty graph: both densities are 1
    have hEmpty : F.edgeFinset = ∅ := Finset.card_eq_zero.mp hF
    have hU : homDensity F U = 1 := by
      unfold homDensity
      simp only [hEmpty, Finset.prod_empty]
      simp only [integral_const]
      simp
    have hW : homDensity F W = 1 := by
      unfold homDensity
      simp only [hEmpty, Finset.prod_empty]
      simp only [integral_const]
      simp
    simp only [hU, hW, sub_self, abs_zero]
    exact hε
  · have hcard_pos : 0 < F.edgeFinset.card := Nat.pos_of_ne_zero hF
    have hmax_eq : max 1 F.edgeFinset.card = F.edgeFinset.card :=
      max_eq_right (Nat.one_le_iff_ne_zero.mpr hF)
    simp only [hmax_eq] at h
    calc |homDensity F U - homDensity F W|
        ≤ F.edgeFinset.card * cutNormDiff U W := homDensity_sub_le F U W
      _ < F.edgeFinset.card * (ε / F.edgeFinset.card) := by
          apply mul_lt_mul_of_pos_left h
          exact Nat.cast_pos.mpr hcard_pos
      _ = ε := by field_simp

end Continuity

end Graphon
