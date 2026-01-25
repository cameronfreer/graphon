/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Step
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic

/-!
# Homomorphism Densities

This file defines homomorphism densities for graphons, which measure how
frequently a fixed graph pattern appears in a graphon.

## Main definitions

* `Graphon.homDensity` - The homomorphism density `t(F, W)` of a graph `F` in a graphon `W`

## Main results

* `Graphon.homDensity_nonneg` - Homomorphism density is nonnegative
* `Graphon.homDensity_le_one` - Homomorphism density is at most 1

## Implementation notes

The homomorphism density `t(F, W)` for a graph `F` on vertex set `V` and graphon `W` is
defined as the integral over all maps `x : V → [0,1]` of the product of `W(x(u), x(v))`
over all edges `{u, v}` of `F`.

### Technical note on a.e. bounds

The integrand bounds (nonneg, ≤ 1, integrability) require lifting the graphon's
a.e. bound from `μ × μ` to `Measure.pi (fun _ => μ)`. The key fact is that for
probability measures with independent coordinates, the pair projection
`x ↦ (x v₁, x v₂)` maps `Measure.pi` to `μ × μ` when `v₁ ≠ v₂`. This is
implicit in `measurePreserving_piFinTwo` and related results.

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Section 7.1
-/

open MeasureTheory Set Filter Finset

open scoped unitInterval

namespace Graphon

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

section HomDensity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The homomorphism density `t(F, W)` of a simple graph `F` in a graphon `W`.

This measures the probability that a random map from the vertices of `F` to the
probability space preserves adjacency (in expectation). Formally:

`t(F, W) = ∫_{x : V → α} ∏_{e ∈ E(F)} W(x(u_e), x(v_e)) dμ^V`

The product uses `Quot.out` to extract a canonical representative pair from each
edge in `edgeFinset`. Since `W` is symmetric a.e. and the integral marginalizes
over all vertex mappings, the choice of representative does not affect the result.

For a finite graph `G` on `n` vertices, `t(F, W_G) = hom(F, G) / n^|V(F)|`
where `hom(F, G)` is the number of graph homomorphisms from `F` to `G`. -/
noncomputable def homDensity (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon α μ) : ℝ :=
  ∫ x : V → α, ∏ e ∈ F.edgeFinset, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)
    ∂Measure.pi (fun _ => μ)

/-- The integrand in the homomorphism density formula. -/
noncomputable def homDensityIntegrand (F : SimpleGraph V) [DecidableRel F.Adj]
    (W : Graphon α μ) (x : V → α) : ℝ :=
  ∏ e ∈ F.edgeFinset, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)

theorem homDensity_eq_integral (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon α μ) :
    homDensity F W = ∫ x, homDensityIntegrand F W x ∂Measure.pi (fun _ => μ) := rfl

/-- The homomorphism density of the empty graph is 1.

An empty graph has no edges, so the integrand is a product over an empty set,
which equals 1. The integral of 1 over a probability space is 1. -/
theorem homDensity_bot (W : Graphon α μ) :
    homDensity (⊥ : SimpleGraph V) W = 1 := by
  -- The empty graph has no edges, so the integrand is a product over ∅, which is 1.
  -- The integral of 1 over a probability space is 1.
  unfold homDensity
  convert integral_const (1 : ℝ) using 1
  · congr 1
    ext x
    apply prod_eq_one
    intro e he
    -- e is an edge in the bottom graph, which has no edges
    simp only [SimpleGraph.mem_edgeFinset] at he
    simp only [SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false] at he
  · simp

/-- Helper: for edges in simple graphs, the two vertices are distinct. -/
theorem edge_out_ne {F : SimpleGraph V} [DecidableRel F.Adj] {e : Sym2 V}
    (he : e ∈ F.edgeSet) : (Quot.out e).1 ≠ (Quot.out e).2 := by
  have h_not_diag := F.not_isDiag_of_mem_edgeSet he
  have h_eq : e = Sym2.mk (Quot.out e) := (Quot.out_eq e).symm
  rw [h_eq, Sym2.mk_isDiag_iff] at h_not_diag
  exact h_not_diag

/-- For probability measures, the graphon value at a pair projection is in [0,1] a.e.

This key technical lemma shows that for distinct indices `v₁ ≠ v₂ : V`, the composition
`x ↦ W(x v₁, x v₂)` takes values in [0,1] for a.e. `x : V → α` under `Measure.pi`.

The proof uses that for distinct coordinates, `eval v₁` and `eval v₂` are independent
under `Measure.pi`. By `measurePreserving_eval`, the marginal distributions equal `μ`,
and by independence, the pair `(x v₁, x v₂)` has distribution `μ × μ`. Since the
graphon's a.e. bound holds on `μ × μ`, it lifts to `Measure.pi`. -/
theorem graphonEval_mem_Icc_ae (W : Graphon α μ) {v₁ v₂ : V} (hne : v₁ ≠ v₂) :
    ∀ᵐ x ∂Measure.pi (fun _ : V => μ), W.toAEEqFun (x v₁, x v₂) ∈ Set.Icc 0 1 := by
  -- The pair map (x ↦ (x v₁, x v₂)) is measurable
  have h_meas : Measurable (fun x : V → α => (x v₁, x v₂)) :=
    Measurable.prodMk (measurable_pi_apply _) (measurable_pi_apply _)
  -- For probability measures, the coordinate projections are independent
  have h_indep : ProbabilityTheory.iIndepFun (fun i (x : V → α) => x i)
      (Measure.pi (fun _ : V => μ)) :=
    ProbabilityTheory.iIndepFun_pi (fun _ => aemeasurable_id)
  -- Get pairwise independence for v₁ ≠ v₂
  have h_indep_pair := h_indep.indepFun hne
  -- By independence, the pair map has product distribution
  have h_map : Measure.map (fun x => (x v₁, x v₂)) (Measure.pi (fun _ : V => μ)) =
      (Measure.map (fun x => x v₁) (Measure.pi (fun _ : V => μ))).prod
      (Measure.map (fun x => x v₂) (Measure.pi (fun _ : V => μ))) := by
    rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      (measurable_pi_apply _).aemeasurable (measurable_pi_apply _).aemeasurable] at h_indep_pair
    exact h_indep_pair
  -- The marginals are μ (by measure-preserving property of eval)
  have h_marg₁ : Measure.map (fun x => x v₁) (Measure.pi (fun _ : V => μ)) = μ :=
    (MeasureTheory.measurePreserving_eval (fun _ : V => μ) v₁).map_eq
  have h_marg₂ : Measure.map (fun x => x v₂) (Measure.pi (fun _ : V => μ)) = μ :=
    (MeasureTheory.measurePreserving_eval (fun _ : V => μ) v₂).map_eq
  -- So the pair map is measure-preserving to μ × μ
  have h_map_eq : Measure.map (fun x => (x v₁, x v₂)) (Measure.pi (fun _ : V => μ)) =
      μ.prod μ := by
    rw [h_map, h_marg₁, h_marg₂]
  -- Now use QuasiMeasurePreserving.ae to lift the a.e. bound
  have h_qmp : Measure.QuasiMeasurePreserving (fun x : V → α => (x v₁, x v₂))
      (Measure.pi (fun _ : V => μ)) (μ.prod μ) := by
    constructor
    · exact h_meas
    · rw [h_map_eq]
  exact h_qmp.ae W.ae_mem_Icc

/-- The integrand in the homomorphism density is nonnegative a.e.

This follows because each factor `W(x(u), x(v))` is nonnegative a.e. (W takes values
in [0,1] a.e.) and a product of nonnegative terms is nonnegative. -/
theorem homDensityIntegrand_nonneg_ae (F : SimpleGraph V) [DecidableRel F.Adj]
    (W : Graphon α μ) : 0 ≤ᵐ[Measure.pi (fun _ : V => μ)] fun x => homDensityIntegrand F W x := by
  -- Use that each edge evaluation is in [0,1] a.e., then the product is nonneg a.e.
  have h_edges : ∀ e ∈ F.edgeFinset,
      ∀ᵐ x ∂Measure.pi (fun _ : V => μ),
        W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1 :=
    fun e he => graphonEval_mem_Icc_ae W (edge_out_ne (SimpleGraph.mem_edgeFinset.mp he))
  -- Finite intersection of a.e. properties is a.e. (by induction on finset)
  have h_all : ∀ᵐ x ∂Measure.pi (fun _ : V => μ),
      ∀ e ∈ F.edgeFinset, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1 := by
    have aux : ∀ (s : Finset (Sym2 V)),
        (∀ e ∈ s, ∀ᵐ (x : V → α) ∂Measure.pi fun _ => μ,
          W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1) →
        ∀ᵐ (x : V → α) ∂Measure.pi fun _ => μ,
          ∀ e ∈ s, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1 := by
      intro s
      refine Finset.induction_on s ?empty ?insert
      case empty => simp
      case insert =>
        intro a s' _ ih hs
        simp only [Finset.mem_insert, forall_eq_or_imp] at hs ⊢
        filter_upwards [hs.1, ih hs.2] with x hx1 hx2
        exact ⟨hx1, hx2⟩
    exact aux F.edgeFinset h_edges
  filter_upwards [h_all] with x hx
  unfold homDensityIntegrand
  apply prod_nonneg
  intro e he
  exact (hx e he).1

/-- The integrand in the homomorphism density is at most 1 a.e.

This follows because each factor `W(x(u), x(v))` is at most 1 a.e. (W takes values
in [0,1] a.e.) and a product of terms in [0,1] is in [0,1]. -/
theorem homDensityIntegrand_le_one_ae (F : SimpleGraph V) [DecidableRel F.Adj]
    (W : Graphon α μ) :
    (fun x => homDensityIntegrand F W x) ≤ᵐ[Measure.pi (fun _ : V => μ)] fun _ => (1 : ℝ) := by
  -- Use that each edge evaluation is in [0,1] a.e., then the product is ≤ 1 a.e.
  have h_edges : ∀ e ∈ F.edgeFinset,
      ∀ᵐ x ∂Measure.pi (fun _ : V => μ),
        W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1 :=
    fun e he => graphonEval_mem_Icc_ae W (edge_out_ne (SimpleGraph.mem_edgeFinset.mp he))
  -- Finite intersection of a.e. properties is a.e. (same induction as nonneg)
  have h_all : ∀ᵐ x ∂Measure.pi (fun _ : V => μ),
      ∀ e ∈ F.edgeFinset, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1 := by
    have aux : ∀ (s : Finset (Sym2 V)),
        (∀ e ∈ s, ∀ᵐ (x : V → α) ∂Measure.pi fun _ => μ,
          W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1) →
        ∀ᵐ (x : V → α) ∂Measure.pi fun _ => μ,
          ∀ e ∈ s, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1 := by
      intro s
      refine Finset.induction_on s ?empty ?insert
      case empty => simp
      case insert =>
        intro a s' _ ih hs
        simp only [Finset.mem_insert, forall_eq_or_imp] at hs ⊢
        filter_upwards [hs.1, ih hs.2] with x hx1 hx2
        exact ⟨hx1, hx2⟩
    exact aux F.edgeFinset h_edges
  filter_upwards [h_all] with x hx
  unfold homDensityIntegrand
  -- Product of terms in [0,1] is ≤ 1
  apply prod_le_one
  · intro e he
    exact (hx e he).1
  · intro e he
    exact (hx e he).2

/-- The homomorphism density integrand takes values in [0, 1] a.e.

This combines the nonnegativity and upper bound. -/
theorem homDensityIntegrand_mem_Icc_ae (F : SimpleGraph V) [DecidableRel F.Adj]
    (W : Graphon α μ) :
    ∀ᵐ x ∂Measure.pi (fun _ : V => μ), homDensityIntegrand F W x ∈ Set.Icc 0 1 := by
  filter_upwards [homDensityIntegrand_nonneg_ae F W, homDensityIntegrand_le_one_ae F W]
  intro x hx_nonneg hx_le_one
  exact ⟨hx_nonneg, hx_le_one⟩

/-- The homomorphism density integrand is ae-measurable.

**Technical note**: The proof requires showing that the composition
`x ↦ W(x v₁, x v₂)` is ae-measurable on `Measure.pi`. The graphon is
ae-strongly-measurable on `μ × μ`, and we need to lift this to the
pushforward measure `Measure.map (x ↦ (x v₁, x v₂)) (Measure.pi _)`.
For probability measures with independent coordinates, this pushforward
equals `μ × μ` when `v₁ ≠ v₂` (which holds for simple graph edges). -/
theorem homDensityIntegrand_aemeasurable (F : SimpleGraph V) [DecidableRel F.Adj]
    (W : Graphon α μ) : AEMeasurable (homDensityIntegrand F W) (Measure.pi (fun _ : V => μ)) := by
  unfold homDensityIntegrand
  apply Finset.aemeasurable_fun_prod
  intro e he
  -- The pair projection map is measurable
  have h_pair : Measurable (fun x : V → α => (x (Quot.out e).1, x (Quot.out e).2)) :=
    Measurable.prodMk (measurable_pi_apply _) (measurable_pi_apply _)
  -- The edge vertices are distinct
  have hne := edge_out_ne (SimpleGraph.mem_edgeFinset.mp he)
  -- Use the same argument as graphonEval_mem_Icc_ae to show the map equals μ × μ
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
  -- Now use AEMeasurable.comp_measurable
  have h_graphon_aem : AEMeasurable W.toAEEqFun (μ.prod μ) := W.toAEEqFun.aemeasurable
  -- Substitute to get aemeasurable w.r.t. the pushforward measure
  have h_aem_map : AEMeasurable W.toAEEqFun
      (Measure.map (fun x => (x (Quot.out e).1, x (Quot.out e).2)) (Measure.pi (fun _ : V => μ))) := by
    rw [h_map_eq]; exact h_graphon_aem
  exact h_aem_map.comp_measurable h_pair

/-- The homomorphism density integrand is integrable over the product measure. -/
theorem homDensityIntegrand_integrable (F : SimpleGraph V) [DecidableRel F.Adj]
    (W : Graphon α μ) : Integrable (homDensityIntegrand F W) (Measure.pi (fun _ : V => μ)) :=
  Integrable.of_mem_Icc 0 1 (homDensityIntegrand_aemeasurable F W)
    (homDensityIntegrand_mem_Icc_ae F W)

/-- Homomorphism density is nonnegative.

This is the integral of an a.e. nonnegative function over a measure space. -/
theorem homDensity_nonneg (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon α μ) :
    0 ≤ homDensity F W := by
  rw [homDensity_eq_integral]
  apply integral_nonneg_of_ae
  exact homDensityIntegrand_nonneg_ae F W

/-- Homomorphism density is at most 1.

This follows because the integrand is bounded by 1 a.e. and we integrate over a
probability space (so the integral of the constant 1 is 1). -/
theorem homDensity_le_one (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon α μ) :
    homDensity F W ≤ 1 := by
  -- Use integral_mono_ae: ∫ f ≤ ∫ g when f ≤ᵐ g and both are integrable
  rw [homDensity_eq_integral]
  have h1 : Integrable (fun _ : V → α => (1 : ℝ)) (Measure.pi (fun _ : V => μ)) :=
    integrable_const 1
  calc ∫ x, homDensityIntegrand F W x ∂Measure.pi (fun _ => μ)
      ≤ ∫ _, (1 : ℝ) ∂Measure.pi (fun _ : V => μ) :=
        integral_mono_ae (homDensityIntegrand_integrable F W) h1
          (homDensityIntegrand_le_one_ae F W)
    _ = 1 := by simp

/-- Homomorphism density is in `[0, 1]`. -/
theorem homDensity_mem_Icc (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon α μ) :
    homDensity F W ∈ Set.Icc 0 1 :=
  ⟨homDensity_nonneg F W, homDensity_le_one F W⟩

end HomDensity

end Graphon
