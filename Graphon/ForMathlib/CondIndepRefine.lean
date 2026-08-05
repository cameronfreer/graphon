/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Independence.Conditional

/-!
# Refining the conditioning algebra of mutual conditional independence

A family of σ-algebras that is mutually conditionally independent given `m'` remains mutually
conditionally independent given any larger algebra `m₂ ≥ m'` that is itself conditionally
independent of the family's join given `m'`.

This is the "useless extra information" principle: enlarging the conditioning from `m'` to `m₂`
cannot destroy independence when everything `m₂` adds is itself conditionally independent of the
family.

## The engine, kept private

The proof rests on a projection identity: if `m₁` and `m₂` are conditionally independent given
`m' ≤ m₂`, then for every `m₁`-set `E`,

`μ⟦E | m₂⟧ =ᵐ[μ] μ⟦E | m'⟧`.

The candidate `μ⟦E | m'⟧` is `m'`-strongly measurable, hence `m₂`-strongly measurable because the
containment `m' ≤ m₂` is raw; and its set integral over an `m₂`-set `F` is computed by the
pull-out property of conditional expectation together with the product identity of conditional
independence: both `∫ x in F, μ⟦E | m'⟧ x` and `∫ x in F, 1_E x` equal
`∫ x, (μ⟦E | m'⟧ * μ⟦F | m'⟧) x`. Uniqueness of the conditional expectation at `m₂` finishes.

The identity is deliberately private: its natural generality — integrable functions rather than
indicators, one-sided measurability hypotheses — is not yet pinned down by a second consumer, and
the σ-algebra-level refinement theorem is the only interface currently consumed.

## Contents

* `ProbabilityTheory.iCondIndep_of_condIndep_iSup` — the refinement theorem.

The `StandardBorelSpace` hypothesis is inherited from Mathlib's definition of `CondIndep` and
`iCondIndep` through `condExpKernel`; the underlying argument does not use it.
-/

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {m₁ m₂ m' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- **The projection identity** (private engine): conditioning an `m₁`-event on `m₂` sees only
`m'` when `m₁` and `m₂` are conditionally independent given `m' ≤ m₂`. -/
private theorem condExp_set_ae_eq_of_condIndep (hm' : m' ≤ mΩ) (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ)
    (hm'₂ : m' ≤ m₂) (hci : CondIndep m' m₁ m₂ hm' μ) {E : Set Ω} (hE : MeasurableSet[m₁] E) :
    (μ⟦E | m₂⟧) =ᵐ[μ] μ⟦E | m'⟧ := by
  rw [condIndep_iff _ _ _ _ hm₁ hm₂] at hci
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm₂
    ((integrable_const (1 : ℝ)).indicator (hm₁ E hE))
    (fun F _ _ => integrable_condExp.integrableOn) (fun F hF _ => ?_)
    (stronglyMeasurable_condExp.mono hm'₂).aestronglyMeasurable).symm
  have hFm : MeasurableSet F := hm₂ F hF
  have hmul : F.indicator (μ⟦E | m'⟧) = (μ⟦E | m'⟧) * F.indicator fun ω => (1 : ℝ) := by
    funext x
    by_cases hx : x ∈ F <;> simp [hx]
  have hfg : Integrable ((μ⟦E | m'⟧) * F.indicator fun ω => (1 : ℝ)) μ := by
    rw [← hmul]; exact integrable_condExp.indicator hFm
  calc ∫ x in F, (μ⟦E | m'⟧) x ∂μ
      = ∫ x, F.indicator (μ⟦E | m'⟧) x ∂μ := (integral_indicator hFm).symm
    _ = ∫ x, ((μ⟦E | m'⟧) * F.indicator fun ω => (1 : ℝ)) x ∂μ := by rw [hmul]
    _ = ∫ x, (μ[(μ⟦E | m'⟧) * F.indicator fun ω => (1 : ℝ) | m']) x ∂μ :=
        (integral_condExp hm').symm
    _ = ∫ x, ((μ⟦E | m'⟧) * μ⟦F | m'⟧) x ∂μ :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left stronglyMeasurable_condExp hfg
          ((integrable_const (1 : ℝ)).indicator hFm))
    _ = ∫ x, (μ⟦E ∩ F | m'⟧) x ∂μ := (integral_congr_ae (hci E F hE hF)).symm
    _ = ∫ x, (E ∩ F).indicator (fun ω => (1 : ℝ)) x ∂μ := integral_condExp hm'
    _ = ∫ x in F, E.indicator (fun ω => (1 : ℝ)) x ∂μ := by
        rw [Set.inter_comm E F, ← Set.indicator_indicator, integral_indicator hFm]

/-- **Refining the conditioning of mutual conditional independence.** If the family `m` is
mutually conditionally independent given `m'`, and the larger algebra `m₂ ≥ m'` is conditionally
independent of the join `⨆ i, m i` given `m'`, then the family is mutually conditionally
independent given `m₂`.

The single hypothesis `hci` covers both uses of the projection identity — the accumulated finite
intersection and each individual factor are all events of the join. -/
theorem iCondIndep_of_condIndep_iSup {ι : Type*} {m : ι → MeasurableSpace Ω}
    (hm' : m' ≤ mΩ) (hm₂ : m₂ ≤ mΩ) (hm'₂ : m' ≤ m₂) (hm : ∀ i, m i ≤ mΩ)
    (h : iCondIndep m' hm' m μ) (hci : CondIndep m' (⨆ i, m i) m₂ hm' μ) :
    iCondIndep m₂ hm₂ m μ := by
  have hsup : (⨆ i, m i) ≤ mΩ := iSup_le hm
  rw [iCondIndep_iff _ _ _ hm] at h
  rw [iCondIndep_iff _ _ _ hm]
  intro s f H
  have hkey : ∀ {E : Set Ω}, MeasurableSet[⨆ i, m i] E → (μ⟦E | m₂⟧) =ᵐ[μ] μ⟦E | m'⟧ :=
    fun hE => condExp_set_ae_eq_of_condIndep hm' hsup hm₂ hm'₂ hci hE
  have hE : MeasurableSet[⨆ i, m i] (⋂ i ∈ s, f i) :=
    Finset.measurableSet_biInter s fun i hi => le_iSup m i _ (H i hi)
  have hfacs : ∀ᵐ x ∂μ, ∀ i ∈ s, (μ⟦f i | m₂⟧) x = (μ⟦f i | m'⟧) x :=
    (ae_ball_iff s.countable_toSet).2 fun i hi => hkey (le_iSup m i _ (H i hi))
  have hprod : (∏ i ∈ s, (μ⟦f i | m₂⟧)) =ᵐ[μ] ∏ i ∈ s, (μ⟦f i | m'⟧) := by
    filter_upwards [hfacs] with x hx
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl fun i hi => hx i hi
  exact (hkey hE).trans ((h s H).trans hprod.symm)

end ProbabilityTheory
