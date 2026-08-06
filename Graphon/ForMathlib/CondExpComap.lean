/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.Independence.Conditional

/-!
# Conditional expectation and conditional independence along a factor map

If `T` carries `P` to `μ`, then conditioning under `μ` on a sub-σ-algebra `m` is computed under
`P` by conditioning on the pullback algebra `m.comap T`:

`(μ[g | m]) ∘ T =ᵐ[P] P[g ∘ T | m.comap T]`

and consequently mutual conditional independence of a family under `μ` pulls back to mutual
conditional independence of the composed family under `P`, conditioned on the pullback algebra.

This is how facts proved on a factor — here, a marginal of a coupling — are consumed on the
coupling itself: every function in sight factors through the projection, and the conditioning
algebra travels by `comap`. Mathlib's `CondIndepFun.comp` composes on the *codomain* side only;
the domain-side transport along a measure-preserving map is what this file adds.

## Proof

The usual uniqueness argument, with the transported function as candidate: `(μ[g | m]) ∘ T` is
`m.comap T`-strongly measurable outright, and its integral over a pullback set `T ⁻¹' s` is
computed by the change-of-variables formula, `setIntegral_condExp` on the factor, and the same
formula back. No structure on the fibres of `T` is used.

## Contents

* `MeasureTheory.condExp_comp_measurePreserving`;
* `ProbabilityTheory.condExp_set_comp_measurePreserving` — the single-event form, shared by both
  independence transports;
* `ProbabilityTheory.condIndepFun_comp_measurePreserving` — the two-function transport;
* `ProbabilityTheory.iCondIndepFun_comp_measurePreserving` — the family transport.

`[StandardBorelSpace]` hypotheses appear only on the conditional-independence statements, forced
by Mathlib defining conditional independence through `condExpKernel`; the
conditional-expectation transport itself is for arbitrary finite measures.
-/

open MeasureTheory

namespace MeasureTheory

variable {α β E : Type*} {m : MeasurableSpace β} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {P : Measure α} {μ : Measure β} {T : α → β}

/-- **Conditional expectation along a factor map.** If `T` carries `P` to `μ`, conditioning under
`μ` on `m` and transporting agrees a.e. with conditioning the transported function under `P` on
the pullback algebra `m.comap T`. -/
theorem condExp_comp_measurePreserving [IsFiniteMeasure μ] (hT : MeasurePreserving T P μ)
    (hm : m ≤ mβ) {g : β → E} (hg : Integrable g μ) :
    (μ[g | m]) ∘ T =ᵐ[P] P[g ∘ T | m.comap T] := by
  haveI : IsFiniteMeasure P := by
    constructor
    rw [← Set.preimage_univ (f := T), ← Measure.map_apply hT.measurable MeasurableSet.univ,
      hT.map_eq]
    exact measure_lt_top μ _
  have hmc : m.comap T ≤ mα :=
    (MeasurableSpace.comap_mono hm).trans (measurable_iff_comap_le.mp hT.measurable)
  have hTm : @Measurable α β (m.comap T) m T := fun s hs => ⟨s, hs, rfl⟩
  refine ae_eq_condExp_of_forall_setIntegral_eq hmc (hT.integrable_comp_of_integrable hg)
    (fun s _ _ => (hT.integrable_comp_of_integrable integrable_condExp).integrableOn)
    (fun F hF _ => ?_)
    (stronglyMeasurable_condExp.comp_measurable hTm).aestronglyMeasurable
  obtain ⟨s, hs, rfl⟩ := hF
  have hsβ : MeasurableSet s := hm s hs
  calc ∫ x in T ⁻¹' s, ((μ[g | m]) ∘ T) x ∂P
      = ∫ y in s, (μ[g | m]) y ∂μ := by
        rw [← hT.map_eq, setIntegral_map hsβ
          (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
          hT.measurable.aemeasurable]
        rfl
    _ = ∫ y in s, g y ∂μ := setIntegral_condExp hm hg hs
    _ = ∫ x in T ⁻¹' s, (g ∘ T) x ∂P := by
        rw [← hT.map_eq, setIntegral_map hsβ (hT.map_eq ▸ hg.aestronglyMeasurable)
          hT.measurable.aemeasurable]
        rfl

end MeasureTheory

namespace ProbabilityTheory

section SetTransport

variable {α β : Type*} {m' : MeasurableSpace β} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
  {P : Measure α} {μ : Measure β} [IsFiniteMeasure μ] {T : α → β}

/-- **The single-event form**: the conditional probability of a pulled-back event, conditioned on
the pullback algebra, is the transported conditional probability of the event. No standard Borel
hypothesis — this is pure conditional expectation. -/
theorem condExp_set_comp_measurePreserving (hT : MeasurePreserving T P μ) (hm' : m' ≤ mβ)
    {E : Set β} (hE : MeasurableSet E) :
    (P⟦T ⁻¹' E | m'.comap T⟧) =ᵐ[P] (μ⟦E | m'⟧) ∘ T := by
  have htrans := condExp_comp_measurePreserving hT hm'
    (g := E.indicator fun _ => (1 : ℝ)) ((integrable_const (1 : ℝ)).indicator hE)
  rw [show (E.indicator fun _ => (1 : ℝ)) ∘ T = (T ⁻¹' E).indicator fun _ => (1 : ℝ) from
    funext fun x => (Set.indicator_comp_right T).symm] at htrans
  exact htrans.symm

end SetTransport

variable {α β : Type*} {m' : MeasurableSpace β} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
  [StandardBorelSpace α] [StandardBorelSpace β]
  {P : Measure α} {μ : Measure β} [IsFiniteMeasure P] [IsFiniteMeasure μ] {T : α → β}

/-- **Conditional independence of a pair pulls back along a factor map**: two functions
conditionally independent under the factor law, given `m'`, compose with the factor map to
functions conditionally independent under the source law, given the pullback algebra. -/
theorem condIndepFun_comp_measurePreserving (hT : MeasurePreserving T P μ) (hm' : m' ≤ mβ)
    {γ γ' : Type*} {mγ : MeasurableSpace γ} {mγ' : MeasurableSpace γ'}
    {f : β → γ} {g : β → γ'} (hf : Measurable f) (hg : Measurable g)
    (h : CondIndepFun m' hm' f g μ) :
    CondIndepFun (m'.comap T)
      ((MeasurableSpace.comap_mono hm').trans (measurable_iff_comap_le.mp hT.measurable))
      (f ∘ T) (g ∘ T) P := by
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg] at h
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul (hf.comp hT.measurable)
    (hg.comp hT.measurable)]
  intro s t hs ht
  have h₁ : (P⟦(f ∘ T) ⁻¹' s ∩ (g ∘ T) ⁻¹' t | m'.comap T⟧)
      =ᵐ[P] (μ⟦f ⁻¹' s ∩ g ⁻¹' t | m'⟧) ∘ T := by
    rw [show (f ∘ T) ⁻¹' s ∩ (g ∘ T) ⁻¹' t = T ⁻¹' (f ⁻¹' s ∩ g ⁻¹' t) by
      rw [Set.preimage_inter, Set.preimage_comp, Set.preimage_comp]]
    exact condExp_set_comp_measurePreserving hT hm' ((hf hs).inter (hg ht))
  have h₂ : (P⟦(f ∘ T) ⁻¹' s | m'.comap T⟧) =ᵐ[P] (μ⟦f ⁻¹' s | m'⟧) ∘ T := by
    rw [Set.preimage_comp]
    exact condExp_set_comp_measurePreserving hT hm' (hf hs)
  have h₃ : (P⟦(g ∘ T) ⁻¹' t | m'.comap T⟧) =ᵐ[P] (μ⟦g ⁻¹' t | m'⟧) ∘ T := by
    rw [Set.preimage_comp]
    exact condExp_set_comp_measurePreserving hT hm' (hg ht)
  have hpull := hT.quasiMeasurePreserving.ae_eq_comp (h s t hs ht)
  filter_upwards [h₁, h₂, h₃, hpull] with x hx1 hx2 hx3 hx4
  rw [hx1, hx2, hx3]
  exact hx4

/-- **Mutual conditional independence pulls back along a factor map.** A family that is mutually
conditionally independent under the factor law, given `m'`, is — after composing with the factor
map — mutually conditionally independent under the source law, given the pullback algebra
`m'.comap T`. -/
theorem iCondIndepFun_comp_measurePreserving (hT : MeasurePreserving T P μ) (hm' : m' ≤ mβ)
    {ι : Type*} {γ : ι → Type*} [mγ : ∀ i, MeasurableSpace (γ i)] {Y : ∀ i, β → γ i}
    (hY : ∀ i, Measurable (Y i)) (h : iCondIndepFun m' hm' Y μ) :
    iCondIndepFun (m'.comap T)
      ((MeasurableSpace.comap_mono hm').trans (measurable_iff_comap_le.mp hT.measurable))
      (fun i => Y i ∘ T) P := by
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul _ _ hY] at h
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul _ _
    fun i => (hY i).comp hT.measurable]
  intro S sets hsets
  have hkey := h S hsets
  have key : ∀ E : Set β, MeasurableSet E →
      (P⟦T ⁻¹' E | m'.comap T⟧) =ᵐ[P] (μ⟦E | m'⟧) ∘ T :=
    fun _ hE => condExp_set_comp_measurePreserving hT hm' hE
  have hinter : MeasurableSet (⋂ i ∈ S, Y i ⁻¹' sets i) :=
    MeasurableSet.biInter S.countable_toSet fun i hi => (hY i) (hsets i hi)
  -- the accumulated event
  have h₁ : (P⟦⋂ i ∈ S, (Y i ∘ T) ⁻¹' sets i | m'.comap T⟧)
      =ᵐ[P] (μ⟦⋂ i ∈ S, Y i ⁻¹' sets i | m'⟧) ∘ T := by
    have hpre : ⋂ i ∈ S, (Y i ∘ T) ⁻¹' sets i = T ⁻¹' ⋂ i ∈ S, Y i ⁻¹' sets i := by
      simp [Set.preimage_comp, Set.preimage_iInter]
    rw [hpre]
    exact key _ hinter
  -- each factor
  have h₂ : ∀ i ∈ S, (P⟦(Y i ∘ T) ⁻¹' sets i | m'.comap T⟧)
      =ᵐ[P] (μ⟦Y i ⁻¹' sets i | m'⟧) ∘ T := by
    intro i hi
    rw [Set.preimage_comp]
    exact key _ ((hY i) (hsets i hi))
  -- pull the factor-law identity back along `T`
  have hpull : (μ⟦⋂ i ∈ S, Y i ⁻¹' sets i | m'⟧) ∘ T
      =ᵐ[P] (∏ i ∈ S, (μ⟦Y i ⁻¹' sets i | m'⟧)) ∘ T :=
    hT.quasiMeasurePreserving.ae_eq_comp hkey
  have hfac : (∏ i ∈ S, (P⟦(Y i ∘ T) ⁻¹' sets i | m'.comap T⟧))
      =ᵐ[P] ∏ i ∈ S, ((μ⟦Y i ⁻¹' sets i | m'⟧) ∘ T) := by
    have hall : ∀ᵐ x ∂P, ∀ i ∈ S, (P⟦(Y i ∘ T) ⁻¹' sets i | m'.comap T⟧) x
        = ((μ⟦Y i ⁻¹' sets i | m'⟧) ∘ T) x :=
      (ae_ball_iff S.countable_toSet).2 h₂
    filter_upwards [hall] with x hx
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl fun i hi => hx i hi
  have hprodcomp : (∏ i ∈ S, (μ⟦Y i ⁻¹' sets i | m'⟧)) ∘ T
      = ∏ i ∈ S, ((μ⟦Y i ⁻¹' sets i | m'⟧) ∘ T) := by
    funext x
    simp [Finset.prod_apply]
  have hclose := hfac.symm
  rw [← hprodcomp] at hclose
  exact h₁.trans (hpull.trans hclose)

end ProbabilityTheory
