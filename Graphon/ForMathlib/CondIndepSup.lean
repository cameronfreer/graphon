/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.Independence.Conditional

/-!
# Two closure properties of conditional independence

Both are glue Mathlib does not currently provide.

* **Joining the conditioning algebra to one side is free**: from `m₁ ⊥⊥ m₂ ∣ m'` conclude
  `m₁ ⊥⊥ (m' ⊔ m₂) ∣ m'`. Whatever the conditioning algebra already knows cannot carry new
  dependence. Proved through the π-system `{e ∩ f | e ∈ m', f ∈ m₂}` generating the join: on such
  a set the `m'`-measurable part pulls out of the conditional expectation as an indicator
  (`condExp_indicator`), and the base product identity finishes pointwise.

* **`CondIndepFun` respects almost-everywhere equality of the functions** — the conditional
  analogue of `IndepFun.congr`. Conditional independence of functions is characterized by
  conditional expectations of indicator preimages, and every term depends on the functions only
  through their a.e. pointwise values. This is what lets a variable that is only a.e. equal to a
  conditioning-measurable one be absorbed into a side of a conditional independence.

Neither statement mentions this repository's signatures. The `[StandardBorelSpace Ω]` hypotheses
come with Mathlib's definition of `CondIndep`/`CondIndepFun` through `condExpKernel`.
-/

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {m' m₁ m₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {hm' : m' ≤ mΩ}

/-- **Joining the conditioning algebra to one side of a conditional independence is free**:
if `m₁ ⊥⊥ m₂ ∣ m'`, then `m₁ ⊥⊥ (m' ⊔ m₂) ∣ m'`. -/
theorem CondIndep.sup_right (h : CondIndep m' m₁ m₂ hm' μ) (h1 : m₁ ≤ mΩ) (h2 : m₂ ≤ mΩ) :
    CondIndep m' m₁ (m' ⊔ m₂) hm' μ := by
  rw [condIndep_iff _ _ _ _ h1 h2] at h
  set p₂ : Set (Set Ω) :=
    {s | ∃ e f, MeasurableSet[m'] e ∧ MeasurableSet[m₂] f ∧ s = e ∩ f} with hp₂def
  have hgen : m' ⊔ m₂ = MeasurableSpace.generateFrom p₂ := by
    refine le_antisymm (sup_le ?_ ?_) (MeasurableSpace.generateFrom_le ?_)
    · exact fun s hs => MeasurableSpace.measurableSet_generateFrom
        ⟨s, Set.univ, hs, MeasurableSet.univ, (Set.inter_univ s).symm⟩
    · exact fun s hs => MeasurableSpace.measurableSet_generateFrom
        ⟨Set.univ, s, MeasurableSet.univ, hs, (Set.univ_inter s).symm⟩
    · rintro s ⟨e, f, he, hf, rfl⟩
      exact ((le_sup_left : m' ≤ m' ⊔ m₂) e he).inter ((le_sup_right : m₂ ≤ m' ⊔ m₂) f hf)
  have hpi₂ : IsPiSystem p₂ := by
    rintro s ⟨e, f, he, hf, rfl⟩ t ⟨e', f', he', hf', rfl⟩ -
    exact ⟨e ∩ e', f ∩ f', he.inter he', hf.inter hf', by rw [Set.inter_inter_inter_comm]⟩
  refine CondIndepSets.condIndep h1 (sup_le hm' h2)
    (@MeasurableSpace.isPiSystem_measurableSet Ω m₁) hpi₂
    (@MeasurableSpace.generateFrom_measurableSet Ω m₁).symm hgen ?_
  refine (condIndepSets_iff _ _ _ _ (fun s hs => h1 s hs) ?_ μ).mpr ?_
  · rintro s ⟨e, f, he, hf, rfl⟩
    exact (hm' e he).inter (h2 f hf)
  rintro t1 t2 ht1 ⟨e, f, he, hf, rfl⟩
  have ht1' : MeasurableSet t1 := h1 t1 ht1
  have hf' : MeasurableSet f := h2 f hf
  -- the `m'`-measurable part pulls out of the conditional expectation as an indicator
  have key : ∀ {g : Set Ω}, MeasurableSet g →
      (μ⟦e ∩ g | m'⟧) =ᵐ[μ] e.indicator (μ⟦g | m'⟧) := by
    intro g hg
    have hcond := condExp_indicator (μ := μ) (m := m')
      ((integrable_const (1 : ℝ)).indicator hg) he
    rw [show e.indicator (g.indicator fun _ => (1 : ℝ)) = (e ∩ g).indicator fun _ => (1 : ℝ) from
      Set.indicator_indicator e g _] at hcond
    exact hcond
  have hmain : (μ⟦t1 ∩ (e ∩ f) | m'⟧) =ᵐ[μ] e.indicator (μ⟦t1 ∩ f | m'⟧) := by
    rw [Set.inter_left_comm]
    exact key (ht1'.inter hf')
  filter_upwards [hmain, h t1 f ht1 hf, key hf'] with x hx1 hx2 hx3
  rw [hx1, Pi.mul_apply, hx3]
  by_cases hxe : x ∈ e
  · rw [Set.indicator_of_mem hxe, Set.indicator_of_mem hxe, hx2, Pi.mul_apply]
  · rw [Set.indicator_of_notMem hxe, Set.indicator_of_notMem hxe, mul_zero]

/-- **`CondIndepFun` respects a.e. equality of the functions** — the conditional analogue of
`IndepFun.congr`. -/
theorem CondIndepFun.congr {β β' : Type*} {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {f f' : Ω → β} {g g' : Ω → β'} (h : CondIndepFun m' hm' f g μ)
    (hfm : Measurable f) (hgm : Measurable g) (hfm' : Measurable f') (hgm' : Measurable g')
    (hff' : f =ᵐ[μ] f') (hgg' : g =ᵐ[μ] g') : CondIndepFun m' hm' f' g' μ := by
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hfm hgm] at h
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hfm' hgm']
  intro s t hs ht
  have hsets : ∀ {A B : Set Ω}, A =ᵐ[μ] B → (μ⟦A | m'⟧) =ᵐ[μ] μ⟦B | m'⟧ := by
    intro A B hAB
    refine condExp_congr_ae ?_
    filter_upwards [Filter.eventuallyEq_set.mp hAB] with x hx
    by_cases hxA : x ∈ A
    · rw [Set.indicator_of_mem hxA, Set.indicator_of_mem (hx.mp hxA)]
    · rw [Set.indicator_of_notMem hxA, Set.indicator_of_notMem fun hB => hxA (hx.mpr hB)]
  have h1 : f' ⁻¹' s =ᵐ[μ] f ⁻¹' s := Filter.eventuallyEq_set.mpr <| by
    filter_upwards [hff'] with x hx
    rw [Set.mem_preimage, Set.mem_preimage, hx]
  have h2 : g' ⁻¹' t =ᵐ[μ] g ⁻¹' t := Filter.eventuallyEq_set.mpr <| by
    filter_upwards [hgg'] with x hx
    rw [Set.mem_preimage, Set.mem_preimage, hx]
  calc (μ⟦f' ⁻¹' s ∩ g' ⁻¹' t | m'⟧)
      =ᵐ[μ] μ⟦f ⁻¹' s ∩ g ⁻¹' t | m'⟧ := hsets (h1.inter h2)
    _ =ᵐ[μ] fun ω => (μ⟦f ⁻¹' s | m'⟧) ω * (μ⟦g ⁻¹' t | m'⟧) ω := h s t hs ht
    _ =ᵐ[μ] fun ω => (μ⟦f' ⁻¹' s | m'⟧) ω * (μ⟦g' ⁻¹' t | m'⟧) ω :=
        ((hsets h1).symm.mul (hsets h2).symm)

/-- **The conditioning σ-algebra may be replaced by an equal one.** The dependent `≤` proof is
handled by proof irrelevance once the σ-algebra equality is substituted. Shared glue: the rank-one
coupling and screening arguments both need it, and so does any transport of a conditional
independence statement whose conditioning map has been reindexed. -/
theorem CondIndepFun.congr_cond {Ω β γ : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    [MeasurableSpace β] [MeasurableSpace γ] {f : Ω → β} {g : Ω → γ}
    {m₁ m₂ : MeasurableSpace Ω} {h1 : m₁ ≤ mΩ} (h : CondIndepFun m₁ h1 f g μ)
    (h12 : m₁ = m₂) (h2 : m₂ ≤ mΩ) : CondIndepFun m₂ h2 f g μ := by
  subst h12
  exact h

end ProbabilityTheory
