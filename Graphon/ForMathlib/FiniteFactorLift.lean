/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.ForMathlib.CouplingGluing

/-!
# Lifting a countable-factor joint law to the carriers

Step 3 of the step-approximation programme: a joint law on a **countable** pair of factor
spaces, whose marginals are the pushed-forward carrier marginals, lifts to a carrier-level
joint law with the original carrier marginals and **exact** pushforward back to the factor
law. Built from normalized restrictions to factor cells. Zero-mass cells contribute zero: the
factor law's atom over a null cell vanishes by marginal compatibility (proved first, so no
`0⁻¹` arithmetic is ever relied on), and the restriction to a null cell is the zero measure.

The countability and measurable-singleton hypotheses are stated explicitly on each factor —
nothing relies on a hidden discrete measurable-space instance.

**Deliberately not claimed**: preservation of either original pair coupling — that would
reintroduce arbitrary-carrier disintegration.
-/

open MeasureTheory

namespace MeasureTheory

open scoped ENNReal

variable {γ₁ γ₂ ι₁ ι₂ : Type*} [MeasurableSpace γ₁] [MeasurableSpace γ₂]
  [MeasurableSpace ι₁] [MeasurableSpace ι₂]
  [Countable ι₁] [MeasurableSingletonClass ι₁] [Countable ι₂] [MeasurableSingletonClass ι₂]

/-- **The countable-factor lift**: the factor law's atoms spread over the normalized products
of the corresponding restricted carrier measures. -/
noncomputable def finiteFactorLift (μ₁ : Measure γ₁) (μ₂ : Measure γ₂)
    (q₁ : γ₁ → ι₁) (q₂ : γ₂ → ι₂) (lam : Measure (ι₁ × ι₂)) : Measure (γ₁ × γ₂) :=
  Measure.sum fun ij : ι₁ × ι₂ =>
    (lam {ij} * (μ₁ (q₁ ⁻¹' {ij.1}))⁻¹ * (μ₂ (q₂ ⁻¹' {ij.2}))⁻¹) •
      (μ₁.restrict (q₁ ⁻¹' {ij.1})).prod (μ₂.restrict (q₂ ⁻¹' {ij.2}))

variable {μ₁ : Measure γ₁} {μ₂ : Measure γ₂} {q₁ : γ₁ → ι₁} {q₂ : γ₂ → ι₂}
  {lam : Measure (ι₁ × ι₂)}

omit [Countable ι₁] [MeasurableSingletonClass ι₁] in
/-- Mapping a fiber restriction through its factor map gives a scaled Dirac mass. -/
theorem map_restrict_preimage_singleton (hq : Measurable q₁) (i : ι₁) :
    (μ₁.restrict (q₁ ⁻¹' {i})).map q₁ = μ₁ (q₁ ⁻¹' {i}) • Measure.dirac i := by
  ext E hE
  rw [Measure.map_apply hq hE, Measure.restrict_apply (hq hE), Measure.smul_apply,
    Measure.dirac_apply' _ hE, smul_eq_mul]
  by_cases hi : i ∈ E
  · rw [Set.indicator_of_mem hi, Pi.one_apply, mul_one]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hi, h⟩⟩
  · rw [Set.indicator_of_notMem hi, mul_zero]
    have : q₁ ⁻¹' E ∩ q₁ ⁻¹' {i} = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      exact fun hx hxi => hi (hxi ▸ hx)
    rw [this, measure_empty]

omit [Countable ι₁] [Countable ι₂] [MeasurableSingletonClass ι₂] in
/-- **The zero-cell guard**: marginal compatibility forces the factor law's atom over a null
first-coordinate cell to vanish. Proved before any normalization is touched, so the zero-cell
summand is eliminated outright rather than by `0⁻¹` arithmetic. -/
theorem atom_eq_zero_of_fiber_null_fst (hq₁ : Measurable q₁)
    (hfst : lam.map Prod.fst = μ₁.map q₁) {i : ι₁} (h0 : μ₁ (q₁ ⁻¹' {i}) = 0) (j : ι₂) :
    lam {(i, j)} = 0 := by
  have hfib : lam (Prod.fst ⁻¹' {i}) = 0 := by
    rw [← Measure.map_apply measurable_fst (measurableSet_singleton i), hfst,
      Measure.map_apply hq₁ (measurableSet_singleton i)]
    exact h0
  exact measure_mono_null (fun p hp => by
    simp only [Set.mem_singleton_iff] at hp
    simp [Set.mem_preimage, hp]) hfib

omit [Countable ι₁] [Countable ι₂] [MeasurableSingletonClass ι₁] in
/-- The symmetric zero-cell guard for the second coordinate. -/
theorem atom_eq_zero_of_fiber_null_snd (hq₂ : Measurable q₂)
    (hsnd : lam.map Prod.snd = μ₂.map q₂) {j : ι₂} (h0 : μ₂ (q₂ ⁻¹' {j}) = 0) (i : ι₁) :
    lam {(i, j)} = 0 := by
  have hfib : lam (Prod.snd ⁻¹' {j}) = 0 := by
    rw [← Measure.map_apply measurable_snd (measurableSet_singleton j), hsnd,
      Measure.map_apply hq₂ (measurableSet_singleton j)]
    exact h0
  exact measure_mono_null (fun p hp => by
    simp only [Set.mem_singleton_iff] at hp
    simp [Set.mem_preimage, hp]) hfib

end MeasureTheory
