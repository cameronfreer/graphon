/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.Independence.Conditional

/-!
# Conditioning on σ-algebras that represent each other modulo the measure

If `m₂ ≤ m₁` and every `m₁`-measurable set is almost everywhere equal to an `m₂`-measurable one,
then conditioning on `m₁` and on `m₂` give the same answer:

`μ[f | m₁] =ᵐ[μ] μ[f | m₂]`

and consequently mutual conditional independence given `m₁` is the same statement as mutual
conditional independence given `m₂`.

This is the recurring situation in which a σ-algebra has a concrete realization — a factor map —
that generates it only *eventwise* modulo the measure. The raw σ-algebras are then genuinely
different objects, and no equality between them is available or claimed; what is available is
this transfer of everything conditional expectation can see.

## The proof does not lift the hypothesis to functions

The tempting route is to show that `μ[f | m₁]`, being `m₁`-strongly measurable, is a.e. equal to
an `m₂`-measurable function, and then conclude. That route is blocked: eventual measurability is
strictly weaker than being a.e. equal to a measurable function — Mathlib's
`MeasureTheory.EventuallyMeasurable` says so explicitly and leaves the equivalence as a TODO —
so the lift would mean redoing simple-function approximation.

It is unnecessary. Run the uniqueness argument in the other direction: take `μ[f | m₂]` as the
*candidate* for `m₁`. It is `m₂`-strongly measurable, hence `m₁`-strongly measurable because the
containment `m₂ ≤ m₁` is raw; and its set integrals over `m₁`-sets are computed by moving to an
`m₂` representative, where `setIntegral_condExp` applies. Uniqueness of the conditional
expectation at `m₁` then finishes. The hypothesis is used only on *sets*, which is the form it
naturally arrives in.

## Contents

* `MeasureTheory.condExp_eq_condExp_of_ae_representable`;
* `ProbabilityTheory.iCondIndepFun_congr_of_ae_representable` — the conditioning transfer.
-/

open MeasureTheory Filter

namespace MeasureTheory

variable {α E : Type*} {m₁ m₂ m₀ : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Conditioning is insensitive to replacing a σ-algebra by one that represents it modulo the
measure.** No equality of σ-algebras is assumed or asserted: only that `m₂ ≤ m₁` and that every
`m₁`-set has an `m₂`-representative almost everywhere. -/
theorem condExp_eq_condExp_of_ae_representable [IsFiniteMeasure μ] (hm₂₁ : m₂ ≤ m₁) (hm₁ : m₁ ≤ m₀)
    (hrep : ∀ s, MeasurableSet[m₁] s → ∃ t, MeasurableSet[m₂] t ∧ s =ᵐ[μ] t)
    {f : α → E} (hf : Integrable f μ) :
    μ[f | m₁] =ᵐ[μ] μ[f | m₂] := by
  have hm₂ : m₂ ≤ m₀ := hm₂₁.trans hm₁
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm₁ hf
    (fun s _ _ => integrable_condExp.integrableOn) (fun s hs _ => ?_) ?_).symm
  · -- move to an `m₂` representative, where `setIntegral_condExp` computes the integral
    obtain ⟨t, ht, hst⟩ := hrep s hs
    rw [setIntegral_congr_set hst, setIntegral_congr_set hst, setIntegral_condExp hm₂ hf ht]
  · -- the candidate is `m₂`-strongly measurable, hence `m₁`-strongly measurable
    exact (stronglyMeasurable_condExp.mono hm₂₁).aestronglyMeasurable

end MeasureTheory

namespace ProbabilityTheory

variable {α : Type*} {m₁ m₂ : MeasurableSpace α} [m₀ : MeasurableSpace α]
  [StandardBorelSpace α] {μ : Measure α}

/-- **Mutual conditional independence transfers between σ-algebras that represent each other
modulo the measure.** The conditioning factor may be replaced by any eventwise realization of it
without changing the statement — which is what lets a concrete factor map stand in for an
abstractly defined conditioning σ-algebra.

The standard Borel hypothesis is not needed for the underlying conditional-expectation statement
`MeasureTheory.condExp_eq_condExp_of_ae_representable`, which is stated for an arbitrary finite
measure. It appears here only because `ProbabilityTheory.iCondIndepFun` is itself defined through
`condExpKernel`, which Mathlib provides only over a standard Borel space. -/
theorem iCondIndepFun_congr_of_ae_representable [IsProbabilityMeasure μ]
    (hm₂₁ : m₂ ≤ m₁) (hm₁ : m₁ ≤ m₀)
    (hrep : ∀ s, MeasurableSet[m₁] s → ∃ t, MeasurableSet[m₂] t ∧ s =ᵐ[μ] t)
    {ι : Type*} {β : ι → Type*} [mβ : ∀ i, MeasurableSpace (β i)] {X : ∀ i, α → β i}
    (hX : ∀ i, Measurable (X i)) :
    iCondIndepFun m₁ hm₁ X μ ↔ iCondIndepFun m₂ (hm₂₁.trans hm₁) X μ := by
  have key : ∀ E : Set α, MeasurableSet E → (μ⟦E | m₁⟧) =ᵐ[μ] (μ⟦E | m₂⟧) := by
    intro E hE
    exact condExp_eq_condExp_of_ae_representable hm₂₁ hm₁ hrep
      ((integrable_const (1 : ℝ)).indicator hE)
  have hprod : ∀ (S : Finset ι) (sets : ∀ i, Set (β i)),
      (∀ i ∈ S, MeasurableSet[mβ i] (sets i)) →
      (((μ⟦⋂ i ∈ S, X i ⁻¹' sets i | m₁⟧) =ᵐ[μ] ∏ i ∈ S, (μ⟦X i ⁻¹' sets i | m₁⟧)) ↔
        ((μ⟦⋂ i ∈ S, X i ⁻¹' sets i | m₂⟧) =ᵐ[μ] ∏ i ∈ S, (μ⟦X i ⁻¹' sets i | m₂⟧))) := by
    intro S sets hsets
    have hinter : MeasurableSet (⋂ i ∈ S, X i ⁻¹' sets i) :=
      MeasurableSet.biInter S.countable_toSet fun i hi => (hX i) (hsets i hi)
    have hfac : (∏ i ∈ S, (μ⟦X i ⁻¹' sets i | m₁⟧)) =ᵐ[μ] ∏ i ∈ S, (μ⟦X i ⁻¹' sets i | m₂⟧) := by
      have hall : ∀ᵐ x ∂μ, ∀ i ∈ S,
          (μ⟦X i ⁻¹' sets i | m₁⟧) x = (μ⟦X i ⁻¹' sets i | m₂⟧) x :=
        (ae_ball_iff S.countable_toSet).2 fun i hi => key _ ((hX i) (hsets i hi))
      filter_upwards [hall] with x hx
      simp only [Finset.prod_apply]
      exact Finset.prod_congr rfl fun i hi => hx i hi
    constructor
    · exact fun hcond => ((key _ hinter).symm.trans hcond).trans hfac
    · exact fun hcond => ((key _ hinter).trans hcond).trans hfac.symm
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul _ _ hX,
    iCondIndepFun_iff_condExp_inter_preimage_eq_mul _ _ hX]
  exact ⟨fun h S sets hsets => (hprod S sets hsets).1 (h S hsets),
    fun h S sets hsets => (hprod S sets hsets).2 (h S hsets)⟩

end ProbabilityTheory
