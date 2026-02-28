/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.HomDensity
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Pullbacks of Graphons

This file defines pullbacks of graphons along measure-preserving maps and proves
that homomorphism densities are invariant under pullbacks.

## Main definitions

* `Graphon.pullback` - The pullback of a graphon along a measure-preserving map
* `Graphon.WeakIso` - Weak isomorphism: graphons related by a measure-preserving pullback

## Main results

* `Graphon.pullback_ae` - The pullback equals W composed with the product map, a.e.
* `Graphon.homDensity_pullback` - `t(F, W^φ) = t(F, W)` for measure-preserving φ

## Implementation notes

Given a measure-preserving map `φ : α → β` from `(α, μ)` to `(β, ν)`, the pullback
`W^φ : α × α → ℝ` of a graphon `W : β × β → ℝ` is defined by `W^φ(x, y) = W(φ(x), φ(y))`.

The key insight is that `Prod.map φ φ : α × α → β × β` is measure-preserving when
`φ` is measure-preserving (by `MeasurePreserving.prod`), so we can use
`AEEqFun.compMeasurePreserving` to define the pullback.

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Section 7.3
-/

open MeasureTheory Set Filter Finset

open scoped unitInterval

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}

/-! ### Pullback of a symmetric kernel -/

namespace SymmKernel

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The product map `Prod.map φ φ` is measure-preserving when `φ` is.

This is a specialized version of `MeasurePreserving.prod` for the case where
both factors use the same map. -/
theorem measurePreserving_prodMap_self {φ : α → β} (hφ : MeasurePreserving φ μ ν) :
    MeasurePreserving (Prod.map φ φ) (μ.prod μ) (ν.prod ν) :=
  hφ.prod hφ

/-- The pullback of a symmetric kernel along a measure-preserving map.

Given a symmetric kernel `W : β × β → ℝ` and a measure-preserving map `φ : α → β`,
the pullback `W^φ(x, y) = W(φ(x), φ(y))` is again a symmetric kernel on `α`. -/
def pullback (W : SymmKernel β ν) (φ : α → β) (hφ : MeasurePreserving φ μ ν) :
    SymmKernel α μ where
  toAEEqFun := W.toAEEqFun.compMeasurePreserving (Prod.map φ φ) (measurePreserving_prodMap_self hφ)
  symm' := by
    -- We need: W(φ(y), φ(x)) =ᵐ W(φ(x), φ(y))
    -- This follows from W's symmetry: W(a, b) =ᵐ W(b, a)
    have h_coeFn := AEEqFun.coeFn_compMeasurePreserving W.toAEEqFun
        (measurePreserving_prodMap_self hφ)
    have h_coeFn_swap := ae_prod_swap h_coeFn
    -- Get W's symmetry lifted through the measure-preserving map
    have h_W_symm : ∀ᵐ p ∂(μ.prod μ), W.toAEEqFun (Prod.map φ φ p.swap) =
        W.toAEEqFun (Prod.map φ φ p) := by
      have hqmp : Measure.QuasiMeasurePreserving (Prod.map φ φ) (μ.prod μ) (ν.prod ν) :=
        (measurePreserving_prodMap_self hφ).quasiMeasurePreserving
      have h := hqmp.ae W.symm'
      filter_upwards [h] with p hp
      simp only [Prod.swap, Prod.map] at hp ⊢
      exact hp
    filter_upwards [h_coeFn, h_coeFn_swap, h_W_symm] with p hp hp_swap hW
    simp only [Function.comp_apply] at hp hp_swap ⊢
    rw [hp_swap, hp, hW]

/-- The underlying `AEEqFun` of a symmetric kernel pullback. -/
theorem pullback_toAEEqFun (W : SymmKernel β ν) (φ : α → β) (hφ : MeasurePreserving φ μ ν) :
    (pullback W φ hφ).toAEEqFun =
      W.toAEEqFun.compMeasurePreserving (Prod.map φ φ) (measurePreserving_prodMap_self hφ) :=
  rfl

/-- The pullback equals W composed with the product map, a.e. -/
theorem pullback_ae (W : SymmKernel β ν) (φ : α → β) (hφ : MeasurePreserving φ μ ν) :
    ∀ᵐ p ∂(μ.prod μ), (pullback W φ hφ).toAEEqFun p = W.toAEEqFun (φ p.1, φ p.2) := by
  have h := AEEqFun.coeFn_compMeasurePreserving W.toAEEqFun (measurePreserving_prodMap_self hφ)
  filter_upwards [h] with p hp
  simp only [pullback_toAEEqFun, Function.comp_apply] at hp ⊢
  exact hp

end SymmKernel

/-! ### Pullback of a graphon -/

namespace Graphon

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The pullback of a graphon along a measure-preserving map.

Given a graphon `W : β × β → [0,1]` and a measure-preserving map `φ : α → β`,
the pullback `W^φ(x, y) = W(φ(x), φ(y))` is again a graphon on `α`.

This operation is fundamental for defining the cut distance:
`δ□(U, W) = inf_φ ‖U - W^φ‖_□`

Key property: `t(F, W^φ) = t(F, W)` for all graphs F (proved in `homDensity_pullback`). -/
def pullback (W : Graphon β ν) (φ : α → β) (hφ : MeasurePreserving φ μ ν) :
    Graphon α μ where
  toSymmKernel := W.toSymmKernel.pullback φ hφ
  ae_mem_Icc := by
    have h_coeFn := AEEqFun.coeFn_compMeasurePreserving W.toAEEqFun
        (SymmKernel.measurePreserving_prodMap_self hφ)
    have hqmp : Measure.QuasiMeasurePreserving (Prod.map φ φ) (μ.prod μ) (ν.prod ν) :=
      (SymmKernel.measurePreserving_prodMap_self hφ).quasiMeasurePreserving
    have h_W_Icc := hqmp.ae W.ae_mem_Icc
    filter_upwards [h_coeFn, h_W_Icc] with p hp hW
    simp only [Function.comp_apply] at hp
    simp only [SymmKernel.pullback_toAEEqFun]
    rw [hp]
    exact hW

/-- The underlying `AEEqFun` of a pullback equals the composition with the product map. -/
theorem pullback_toAEEqFun (W : Graphon β ν) (φ : α → β) (hφ : MeasurePreserving φ μ ν) :
    (pullback W φ hφ).toAEEqFun =
      W.toAEEqFun.compMeasurePreserving (Prod.map φ φ) (SymmKernel.measurePreserving_prodMap_self hφ) :=
  rfl

/-- The pullback equals W composed with the product map, a.e. -/
theorem pullback_ae (W : Graphon β ν) (φ : α → β) (hφ : MeasurePreserving φ μ ν) :
    ∀ᵐ p ∂(μ.prod μ), (pullback W φ hφ).toAEEqFun p = W.toAEEqFun (φ p.1, φ p.2) :=
  W.toSymmKernel.pullback_ae φ hφ

/-- Pullback by the identity is the original graphon. -/
@[simp]
theorem pullback_id (W : Graphon α μ) : pullback W id (MeasurePreserving.id μ) = W := by
  -- Use that compMeasurePreserving with id is the identity
  have h := AEEqFun.coeFn_compMeasurePreserving W.toAEEqFun
      (SymmKernel.measurePreserving_prodMap_self (MeasurePreserving.id μ))
  have h' : ∀ᵐ p ∂(μ.prod μ), (pullback W id (MeasurePreserving.id μ)).toAEEqFun p =
      W.toAEEqFun p := by
    filter_upwards [h] with p hp
    simp only [pullback_toAEEqFun, Function.comp_apply] at hp ⊢
    exact hp
  -- Chain the ext lemmas
  apply Graphon.ext
  apply SymmKernel.ext
  exact AEEqFun.ext h'

/-- Pullback is functorial: `(W^φ)^ψ = W^(φ ∘ ψ)`. -/
theorem pullback_pullback {γ : Type*} [MeasurableSpace γ] {τ : Measure γ}
    [IsProbabilityMeasure τ]
    (W : Graphon β ν) (φ : α → β) (hφ : MeasurePreserving φ μ ν)
    (ψ : γ → α) (hψ : MeasurePreserving ψ τ μ) :
    pullback (pullback W φ hφ) ψ hψ = pullback W (φ ∘ ψ) (hφ.comp hψ) := by
  have h1 := pullback_ae W φ hφ
  have h2 := pullback_ae (pullback W φ hφ) ψ hψ
  have h3 := pullback_ae W (φ ∘ ψ) (hφ.comp hψ)
  -- Lift h1 to the τ × τ measure
  have h1' : ∀ᵐ p ∂(τ.prod τ), (pullback W φ hφ).toAEEqFun (ψ p.1, ψ p.2) =
      W.toAEEqFun (φ (ψ p.1), φ (ψ p.2)) := by
    have hqmp : Measure.QuasiMeasurePreserving (Prod.map ψ ψ) (τ.prod τ) (μ.prod μ) :=
      (SymmKernel.measurePreserving_prodMap_self hψ).quasiMeasurePreserving
    exact hqmp.ae h1
  have h_eq : ∀ᵐ p ∂(τ.prod τ),
      (pullback (pullback W φ hφ) ψ hψ).toAEEqFun p = (pullback W (φ ∘ ψ) (hφ.comp hψ)).toAEEqFun p := by
    filter_upwards [h2, h3, h1'] with p hp2 hp3 hp1'
    rw [hp2, hp1']
    simp only [Function.comp_apply] at hp3 ⊢
    rw [← hp3]
  -- Chain the ext lemmas
  apply Graphon.ext
  apply SymmKernel.ext
  exact AEEqFun.ext h_eq

/-- If two measure-preserving maps agree a.e., their pullbacks are equal.

This is used to transfer cutNormDiff bounds from a general MP map to a
MeasurableEquiv witness obtained via Rokhlin alignment. -/
theorem pullback_congr_ae (W : Graphon α μ) {f g : α → α}
    (hf : MeasurePreserving f μ μ) (hg : MeasurePreserving g μ μ)
    (h : f =ᶠ[ae μ] g) : pullback W f hf = pullback W g hg := by
  apply Graphon.ext; apply SymmKernel.ext; apply AEEqFun.ext
  have h1 := pullback_ae W f hf
  have h2 := pullback_ae W g hg
  have h_prod_ae : ∀ᵐ p ∂(μ.prod μ), (f p.1, f p.2) = (g p.1, g p.2) := by
    have h_fst : ∀ᵐ p ∂(μ.prod μ), f p.1 = g p.1 :=
      Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst h
    have h_snd : ∀ᵐ p ∂(μ.prod μ), f p.2 = g p.2 :=
      Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd h
    filter_upwards [h_fst, h_snd] with p hp1 hp2
    exact Prod.ext hp1 hp2
  filter_upwards [h1, h2, h_prod_ae] with p hp1 hp2 hp_eq
  rw [hp1, hp2, hp_eq]

/-! ### Weak isomorphism -/

/-- Two graphons are weakly isomorphic if one is a pullback of the other.

This is a one-sided (asymmetric) relation: `WeakIso U W` means `U = W^φ` for some
measure-preserving `φ`. This is NOT an equivalence relation.

**Important distinction**:
- This definition uses any measure-preserving map `φ : α → β`
- The `homDensity_pullback` theorem requires `φ` to be a measurable equivalence
  (`φ : α ≃ᵐ β`) for the change of variables formula

The cut distance δ□(U, W) = 0 corresponds to the symmetric closure: there exist
measure-preserving maps in BOTH directions making U and W equal via pullback.

For full weak isomorphism equivalence, one would quotient by this symmetric closure. -/
def WeakIso (U : Graphon α μ) (W : Graphon β ν) : Prop :=
  ∃ (φ : α → β) (hφ : MeasurePreserving φ μ ν), U = pullback W φ hφ

/-- Reflexivity: a graphon is weakly isomorphic to itself via the identity. -/
theorem WeakIso.refl (W : Graphon α μ) : WeakIso W W :=
  ⟨id, MeasurePreserving.id μ, (pullback_id W).symm⟩

/-- Weak isomorphism is preserved under pullback. -/
theorem WeakIso.pullback {U : Graphon α μ} {W : Graphon β ν}
    {γ : Type*} [MeasurableSpace γ] {τ : Measure γ} [IsProbabilityMeasure τ]
    (h : WeakIso U W) (ψ : γ → α) (hψ : MeasurePreserving ψ τ μ) :
    WeakIso (pullback U ψ hψ) W := by
  obtain ⟨φ, hφ, hU⟩ := h
  refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
  rw [hU]
  exact pullback_pullback W φ hφ ψ hψ

/-! ### Homomorphism density is invariant under pullback -/

section HomDensityPullback

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The map `(V → α) → (V → β)` induced by `φ : α → β` via post-composition. -/
def piMap (φ : α → β) : (V → α) → (V → β) := fun x v => φ (x v)

/-- `piMap φ` is measurable when `φ` is measurable. -/
theorem measurable_piMap {φ : α → β} (hφ : Measurable φ) : Measurable (piMap φ : (V → α) → V → β) :=
  measurable_pi_lambda _ (fun v => hφ.comp (measurable_pi_apply v))

/-- `piMap φ` is measure-preserving when `φ` is. -/
theorem measurePreserving_piMap {φ : α → β} (hφ : MeasurePreserving φ μ ν) :
    MeasurePreserving (piMap φ : (V → α) → V → β)
      (Measure.pi (fun _ : V => μ)) (Measure.pi (fun _ : V => ν)) :=
  measurePreserving_pi _ _ (fun _ => hφ)

/-- `piMap φ` is a measurable equivalence when `φ` is. -/
def piMapEquiv (φ : α ≃ᵐ β) : (V → α) ≃ᵐ (V → β) :=
  MeasurableEquiv.piCongrRight (fun _ => φ)

/-- The homomorphism density integrand commutes with pullback.

For any graph `F`, graphon `W`, and measure-preserving `φ`:
`homDensityIntegrand F (W^φ) x = homDensityIntegrand F W (piMap φ x)` a.e. -/
theorem homDensityIntegrand_pullback_ae (F : SimpleGraph V) [DecidableRel F.Adj]
    (W : Graphon β ν) (φ : α → β) (hφ : MeasurePreserving φ μ ν) :
    ∀ᵐ x ∂Measure.pi (fun _ : V => μ),
      homDensityIntegrand F (pullback W φ hφ) x = homDensityIntegrand F W (piMap φ x) := by
  -- The pullback agrees with W composed with (φ × φ) a.e.
  have h_pullback := pullback_ae W φ hφ
  -- We need to lift this to the product space (V → α)
  -- For each edge e, the map x ↦ (x v₁, x v₂) pushes forward to (φ x v₁, φ x v₂)
  -- First, collect the a.e. equalities for all edges
  have h_edges : ∀ e ∈ F.edgeFinset,
      ∀ᵐ x ∂Measure.pi (fun _ : V => μ),
        (pullback W φ hφ).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) =
          W.toAEEqFun (φ (x (Quot.out e).1), φ (x (Quot.out e).2)) := by
    intro e he
    -- The pair map is measure-preserving from Measure.pi to μ × μ
    have hne := edge_out_ne (SimpleGraph.mem_edgeFinset.mp he)
    have h_pair : Measurable (fun x : V → α => (x (Quot.out e).1, x (Quot.out e).2)) :=
      Measurable.prodMk (measurable_pi_apply _) (measurable_pi_apply _)
    -- Use independence to get the pair distribution
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
    have hqmp : Measure.QuasiMeasurePreserving (fun x : V → α => (x (Quot.out e).1, x (Quot.out e).2))
        (Measure.pi (fun _ : V => μ)) (μ.prod μ) := by
      constructor
      · exact h_pair
      · rw [h_map_eq]
    exact hqmp.ae h_pullback
  -- Combine all edges using finite intersection
  have h_all : ∀ᵐ x ∂Measure.pi (fun _ : V => μ),
      ∀ e ∈ F.edgeFinset, (pullback W φ hφ).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) =
          W.toAEEqFun (φ (x (Quot.out e).1), φ (x (Quot.out e).2)) := by
    have aux : ∀ (s : Finset (Sym2 V)),
        (∀ e ∈ s, ∀ᵐ (x : V → α) ∂Measure.pi fun _ => μ,
          (pullback W φ hφ).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) =
            W.toAEEqFun (φ (x (Quot.out e).1), φ (x (Quot.out e).2))) →
        ∀ᵐ (x : V → α) ∂Measure.pi fun _ => μ,
          ∀ e ∈ s, (pullback W φ hφ).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) =
            W.toAEEqFun (φ (x (Quot.out e).1), φ (x (Quot.out e).2)) := by
      intro s
      refine Finset.induction_on s ?empty ?insert
      case empty => simp
      case insert =>
        intro a s' _ ih hs
        simp only [Finset.mem_insert, forall_eq_or_imp] at hs ⊢
        filter_upwards [hs.1, ih hs.2] with x hx1 hx2
        exact ⟨hx1, hx2⟩
    exact aux F.edgeFinset h_edges
  -- Now conclude with the product formula
  filter_upwards [h_all] with x hx
  unfold homDensityIntegrand piMap
  apply Finset.prod_congr rfl
  intro e he
  exact hx e he

/-- **Main theorem**: Homomorphism density is invariant under pullback.

For any graph `F`, graphon `W`, and measure-preserving map `φ : α → β`:
`t(F, W^φ) = t(F, W)`

This is a fundamental property that makes the cut distance well-defined:
weakly isomorphic graphons have the same homomorphism densities for all graphs. -/
theorem homDensity_pullback (F : SimpleGraph V) [DecidableRel F.Adj]
    (W : Graphon β ν) (φ : α ≃ᵐ β) (hφ : MeasurePreserving φ μ ν) :
    homDensity F (pullback W φ hφ) = homDensity F W := by
  unfold homDensity
  -- Use MeasurePreserving.integral_comp' for the measure-preserving equivalence
  have h_mp' : MeasurePreserving (piMapEquiv (V := V) φ)
      (Measure.pi (fun _ : V => μ)) (Measure.pi (fun _ : V => ν)) :=
    measurePreserving_pi _ _ (fun _ => hφ)
  -- The key step: change of variables
  calc ∫ x, ∏ e ∈ F.edgeFinset, (pullback W φ hφ).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)
        ∂Measure.pi (fun _ => μ)
      = ∫ x, homDensityIntegrand F (pullback W φ hφ) x ∂Measure.pi (fun _ => μ) := by rfl
    _ = ∫ x, homDensityIntegrand F W (piMap (V := V) φ x) ∂Measure.pi (fun _ => μ) := by
        apply integral_congr_ae
        exact homDensityIntegrand_pullback_ae F W φ hφ
    _ = ∫ x, homDensityIntegrand F W ((piMapEquiv (V := V) φ) x) ∂Measure.pi (fun _ => μ) := by rfl
    _ = ∫ y, homDensityIntegrand F W y ∂Measure.pi (fun _ => ν) := by
        exact h_mp'.integral_comp' _
    _ = ∫ y, ∏ e ∈ F.edgeFinset, W.toAEEqFun (y (Quot.out e).1, y (Quot.out e).2)
        ∂Measure.pi (fun _ => ν) := by rfl

/-- General version: Homomorphism density is invariant under pullback for any
    measure-preserving map (not just equivalences).

For any graph `F`, graphon `W`, and measure-preserving map `φ : α → β`:
`t(F, W^φ) = t(F, W)`

This uses `integral_map` instead of `integral_comp'`, so it doesn't require
`φ` to be a bijection. -/
theorem homDensity_pullback_mp (F : SimpleGraph V) [DecidableRel F.Adj]
    (W : Graphon β ν) (φ : α → β) (hφ : MeasurePreserving φ μ ν) :
    homDensity F (pullback W φ hφ) = homDensity F W := by
  unfold homDensity
  -- piMap φ is measure-preserving
  have h_mp' : MeasurePreserving (piMap φ : (V → α) → V → β)
      (Measure.pi (fun _ : V => μ)) (Measure.pi (fun _ : V => ν)) :=
    measurePreserving_piMap hφ
  -- The integrand is aemeasurable
  have h_aem : AEMeasurable (homDensityIntegrand F W) (Measure.pi (fun _ => ν)) :=
    homDensityIntegrand_aemeasurable F W
  -- AEMeasurable implies AEStronglyMeasurable for ℝ (second countable)
  have h_aesm : AEStronglyMeasurable (homDensityIntegrand F W)
      (Measure.map (piMap φ) (Measure.pi (fun _ => μ))) := by
    rw [h_mp'.map_eq]
    exact h_aem.aestronglyMeasurable
  -- The key step: change of variables using integral_map
  calc ∫ x, ∏ e ∈ F.edgeFinset, (pullback W φ hφ).toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)
        ∂Measure.pi (fun _ => μ)
      = ∫ x, homDensityIntegrand F (pullback W φ hφ) x ∂Measure.pi (fun _ => μ) := by rfl
    _ = ∫ x, homDensityIntegrand F W (piMap (V := V) φ x) ∂Measure.pi (fun _ => μ) := by
        apply integral_congr_ae
        exact homDensityIntegrand_pullback_ae F W φ hφ
    _ = ∫ y, homDensityIntegrand F W y ∂(Measure.map (piMap φ) (Measure.pi (fun _ => μ))) := by
        rw [integral_map (measurable_piMap hφ.measurable).aemeasurable h_aesm]
    _ = ∫ y, homDensityIntegrand F W y ∂Measure.pi (fun _ => ν) := by
        rw [h_mp'.map_eq]
    _ = ∫ y, ∏ e ∈ F.edgeFinset, W.toAEEqFun (y (Quot.out e).1, y (Quot.out e).2)
        ∂Measure.pi (fun _ => ν) := by rfl

/-- Weakly isomorphic graphons have the same homomorphism densities. -/
theorem homDensity_weakIso (F : SimpleGraph V) [DecidableRel F.Adj]
    {U : Graphon α μ} {W : Graphon β ν}
    (φ : α ≃ᵐ β) (hφ : MeasurePreserving φ μ ν) (h : U = pullback W φ hφ) :
    homDensity F U = homDensity F W := by
  rw [h]
  exact homDensity_pullback F W φ hφ

end HomDensityPullback

end Graphon
