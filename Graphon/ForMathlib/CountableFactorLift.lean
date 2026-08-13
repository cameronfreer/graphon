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
noncomputable def countableFactorLift (μ₁ : Measure γ₁) (μ₂ : Measure γ₂)
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

/-! ### The carrier marginals — proved first, validating the normalization -/

variable [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]

/-- **The first carrier marginal is exact.** Per summand the second coordinate integrates out,
its normalization cancels (the zero-mass case is eliminated by the guard, not by arithmetic),
the factor law's fiber mass recovers each cell restriction by marginal compatibility, and the
cell restrictions sum to the carrier measure. -/
theorem countableFactorLift_map_fst (hq₁ : Measurable q₁) (hq₂ : Measurable q₂)
    (hfst : lam.map Prod.fst = μ₁.map q₁) (hsnd : lam.map Prod.snd = μ₂.map q₂) :
    (countableFactorLift μ₁ μ₂ q₁ q₂ lam).map Prod.fst = μ₁ := by
  ext E hE
  rw [Measure.map_apply measurable_fst hE, countableFactorLift,
    Measure.sum_apply_of_countable]
  have hterm : ∀ ij : ι₁ × ι₂,
      ((lam {ij} * (μ₁ (q₁ ⁻¹' {ij.1}))⁻¹ * (μ₂ (q₂ ⁻¹' {ij.2}))⁻¹) •
        (μ₁.restrict (q₁ ⁻¹' {ij.1})).prod (μ₂.restrict (q₂ ⁻¹' {ij.2})))
        (Prod.fst ⁻¹' E) =
      lam {ij} * (μ₁ (q₁ ⁻¹' {ij.1}))⁻¹ * μ₁ (E ∩ q₁ ⁻¹' {ij.1}) := by
    rintro ⟨i, j⟩
    rw [Measure.smul_apply, smul_eq_mul,
      show Prod.fst ⁻¹' E = E ×ˢ (Set.univ : Set γ₂) from Set.ext fun p =>
        ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩,
      Measure.prod_prod, Measure.restrict_apply hE, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter]
    by_cases h0 : μ₂ (q₂ ⁻¹' {j}) = 0
    · rw [atom_eq_zero_of_fiber_null_snd hq₂ hsnd h0 i]
      simp
    · rw [mul_assoc (lam {(i, j)} * (μ₁ (q₁ ⁻¹' {i}))⁻¹), mul_comm ((μ₂ (q₂ ⁻¹' {j}))⁻¹),
        mul_assoc (μ₁ (E ∩ q₁ ⁻¹' {i})), ENNReal.mul_inv_cancel h0 (measure_ne_top μ₂ _),
        mul_one]
  rw [tsum_congr hterm, ENNReal.tsum_prod']
  have hj : ∀ i : ι₁, ∑' j : ι₂, lam {(i, j)} * (μ₁ (q₁ ⁻¹' {i}))⁻¹ * μ₁ (E ∩ q₁ ⁻¹' {i})
      = μ₁ (q₁ ⁻¹' {i}) * (μ₁ (q₁ ⁻¹' {i}))⁻¹ * μ₁ (E ∩ q₁ ⁻¹' {i}) := by
    intro i
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
    congr 2
    have hcover : Prod.fst ⁻¹' ({i} : Set ι₁) = ⋃ j : ι₂, {((i : ι₁), (j : ι₂))} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion]
      exact ⟨fun h => ⟨p.2, by rw [← h]⟩, fun ⟨j, hj⟩ => by rw [hj]⟩
    calc ∑' j : ι₂, lam {(i, j)} = lam (⋃ j : ι₂, {((i : ι₁), (j : ι₂))}) :=
          (measure_iUnion (fun j k hjk => by
              simp only [Set.disjoint_singleton, ne_eq, Prod.mk.injEq, true_and]
              exact fun h => hjk h)
            (fun j => measurableSet_singleton _)).symm
      _ = lam (Prod.fst ⁻¹' {i}) := by rw [hcover]
      _ = (lam.map Prod.fst) {i} := (Measure.map_apply measurable_fst
            (measurableSet_singleton i)).symm
      _ = (μ₁.map q₁) {i} := by rw [hfst]
      _ = μ₁ (q₁ ⁻¹' {i}) := Measure.map_apply hq₁ (measurableSet_singleton i)
  rw [tsum_congr hj]
  have hi : ∀ i : ι₁, μ₁ (q₁ ⁻¹' {i}) * (μ₁ (q₁ ⁻¹' {i}))⁻¹ * μ₁ (E ∩ q₁ ⁻¹' {i})
      = μ₁ (E ∩ q₁ ⁻¹' {i}) := by
    intro i
    by_cases h0 : μ₁ (q₁ ⁻¹' {i}) = 0
    · rw [h0, measure_mono_null Set.inter_subset_right h0]
      simp
    · rw [ENNReal.mul_inv_cancel h0 (measure_ne_top μ₁ _), one_mul]
  rw [tsum_congr hi,
    ← measure_iUnion (fun j k hjk => Set.disjoint_left.mpr fun x hx hx' =>
        hjk (by rw [← hx.2, ← hx'.2]))
      (fun i => hE.inter (hq₁ (measurableSet_singleton i))),
    show (⋃ i : ι₁, E ∩ q₁ ⁻¹' {i}) = E from by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun ⟨i, hx, _⟩ => hx, fun hx => ⟨q₁ x, hx, rfl⟩⟩]

/-- **The second carrier marginal is exact.** Mirror of the first. -/
theorem countableFactorLift_map_snd (hq₁ : Measurable q₁) (hq₂ : Measurable q₂)
    (hfst : lam.map Prod.fst = μ₁.map q₁) (hsnd : lam.map Prod.snd = μ₂.map q₂) :
    (countableFactorLift μ₁ μ₂ q₁ q₂ lam).map Prod.snd = μ₂ := by
  ext E hE
  rw [Measure.map_apply measurable_snd hE, countableFactorLift,
    Measure.sum_apply_of_countable]
  have hterm : ∀ ij : ι₁ × ι₂,
      ((lam {ij} * (μ₁ (q₁ ⁻¹' {ij.1}))⁻¹ * (μ₂ (q₂ ⁻¹' {ij.2}))⁻¹) •
        (μ₁.restrict (q₁ ⁻¹' {ij.1})).prod (μ₂.restrict (q₂ ⁻¹' {ij.2})))
        (Prod.snd ⁻¹' E) =
      lam {ij} * (μ₂ (q₂ ⁻¹' {ij.2}))⁻¹ * μ₂ (E ∩ q₂ ⁻¹' {ij.2}) := by
    rintro ⟨i, j⟩
    rw [Measure.smul_apply, smul_eq_mul,
      show Prod.snd ⁻¹' E = (Set.univ : Set γ₁) ×ˢ E from Set.ext fun p =>
        ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩,
      Measure.prod_prod, Measure.restrict_apply MeasurableSet.univ, Measure.restrict_apply hE,
      Set.univ_inter]
    by_cases h0 : μ₁ (q₁ ⁻¹' {i}) = 0
    · rw [atom_eq_zero_of_fiber_null_fst hq₁ hfst h0 j]
      simp
    · rw [show lam {(i, j)} * (μ₁ (q₁ ⁻¹' {i}))⁻¹ * (μ₂ (q₂ ⁻¹' {j}))⁻¹ *
          (μ₁ (q₁ ⁻¹' {i}) * μ₂ (E ∩ q₂ ⁻¹' {j})) =
        lam {(i, j)} * (μ₂ (q₂ ⁻¹' {j}))⁻¹ * μ₂ (E ∩ q₂ ⁻¹' {j}) *
          ((μ₁ (q₁ ⁻¹' {i}))⁻¹ * μ₁ (q₁ ⁻¹' {i})) from by ring,
        ENNReal.inv_mul_cancel h0 (measure_ne_top μ₁ _), mul_one]
  rw [tsum_congr hterm, ENNReal.tsum_prod', ENNReal.tsum_comm]
  have hi : ∀ j : ι₂, ∑' i : ι₁, lam {(i, j)} * (μ₂ (q₂ ⁻¹' {j}))⁻¹ * μ₂ (E ∩ q₂ ⁻¹' {j})
      = μ₂ (q₂ ⁻¹' {j}) * (μ₂ (q₂ ⁻¹' {j}))⁻¹ * μ₂ (E ∩ q₂ ⁻¹' {j}) := by
    intro j
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
    congr 2
    have hcover : Prod.snd ⁻¹' ({j} : Set ι₂) = ⋃ i : ι₁, {((i : ι₁), (j : ι₂))} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion]
      exact ⟨fun h => ⟨p.1, by rw [← h]⟩, fun ⟨i, hi⟩ => by rw [hi]⟩
    calc ∑' i : ι₁, lam {(i, j)} = lam (⋃ i : ι₁, {((i : ι₁), (j : ι₂))}) :=
          (measure_iUnion (fun i k hik => by
              simp only [Set.disjoint_singleton, ne_eq, Prod.mk.injEq, and_true]
              exact fun h => hik h)
            (fun i => measurableSet_singleton _)).symm
      _ = lam (Prod.snd ⁻¹' {j}) := by rw [hcover]
      _ = (lam.map Prod.snd) {j} := (Measure.map_apply measurable_snd
            (measurableSet_singleton j)).symm
      _ = (μ₂.map q₂) {j} := by rw [hsnd]
      _ = μ₂ (q₂ ⁻¹' {j}) := Measure.map_apply hq₂ (measurableSet_singleton j)
  rw [tsum_congr hi]
  have hjj : ∀ j : ι₂, μ₂ (q₂ ⁻¹' {j}) * (μ₂ (q₂ ⁻¹' {j}))⁻¹ * μ₂ (E ∩ q₂ ⁻¹' {j})
      = μ₂ (E ∩ q₂ ⁻¹' {j}) := by
    intro j
    by_cases h0 : μ₂ (q₂ ⁻¹' {j}) = 0
    · rw [h0, measure_mono_null Set.inter_subset_right h0]
      simp
    · rw [ENNReal.mul_inv_cancel h0 (measure_ne_top μ₂ _), one_mul]
  rw [tsum_congr hjj,
    ← measure_iUnion (fun j k hjk => Set.disjoint_left.mpr fun x hx hx' =>
        hjk (by rw [← hx.2, ← hx'.2]))
      (fun j => hE.inter (hq₂ (measurableSet_singleton j))),
    show (⋃ j : ι₂, E ∩ q₂ ⁻¹' {j}) = E from by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun ⟨j, hx, _⟩ => hx, fun hx => ⟨q₂ x, hx, rfl⟩⟩]

/-- **The lift is a probability measure** — derived from the exact first carrier marginal
evaluated at `univ`, independently of the factor-law round-trip. -/
theorem isProbabilityMeasure_countableFactorLift [IsProbabilityMeasure μ₁]
    (hq₁ : Measurable q₁) (hq₂ : Measurable q₂)
    (hfst : lam.map Prod.fst = μ₁.map q₁) (hsnd : lam.map Prod.snd = μ₂.map q₂) :
    IsProbabilityMeasure (countableFactorLift μ₁ μ₂ q₁ q₂ lam) := by
  constructor
  rw [← Set.preimage_univ (f := (Prod.fst : γ₁ × γ₂ → γ₁)),
    ← Measure.map_apply measurable_fst MeasurableSet.univ,
    countableFactorLift_map_fst hq₁ hq₂ hfst hsnd]
  exact measure_univ

end MeasureTheory
