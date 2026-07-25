/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Countable generation of sub-σ-algebras modulo null sets (R4 converse piece 3, #107)

The generic, signature-free toolkit behind the coherent factor realization: a sub-σ-algebra of
a separable measure space is generated, **modulo null sets**, by a countable family of events,
and a countable family of events yields an honest factor map to a Cantor-type space.

Nothing here mentions relational structures; the whole file is a Mathlib-upstream candidate
(tracked on #24).

## Design note: what "modulo null sets" means

The mod-null statement is deliberately **eventwise**:

`∀ E, MeasurableSet[m] E → ∃ E', MeasurableSet[generateFrom G] E' ∧ E' =ᵐ[μ] E`

and *not* an equality of measurable spaces "modulo null sets". A σ-algebra-level formulation
would force a choice between `Measure.trim` and `Measure.completion` at every use site and
generate diamonds between them; the eventwise form composes without any such commitment, and it
is exactly what the factor recursion consumes.

## Contents

* `MeasureTheory.Measure.MeasureDense.exists_generateFrom_ae_eq_of_ne_top` — the upgrade from
  *approximation* to *a.e. representatives*: if `G` is measure-dense for the trimmed measure,
  every `m`-measurable event of finite trimmed measure agrees a.e. with a
  `generateFrom G`-measurable one. Proved by summable symmetric-difference approximation and
  Borel–Cantelli — measure density alone gives only approximation, which is not the consumer
  API. No countability of `G` is required; countability matters only when `G` is turned into a
  factor space. `exists_generateFrom_ae_eq` is the `[IsFiniteMeasure μ]` corollary.
* `MeasureTheory.measure_symmDiff_threshold_le` — the threshold estimate
  `ν (E ∆ {x | 1/2 < f x}) ≤ 2 * ‖1_E - f‖₁`, which converts an `L¹`-dense family of
  *functions* into a measure-dense family of *sets*. This is the bridge from separability of
  `Lᵖ` to separability of the measure.
* `MeasurableSpace.comap_mapNatBool` — the missing companion to Mathlib's
  `measurable_mapNatBool`: a countably generated σ-algebra is *literally* the pullback of the
  Cantor-space σ-algebra along `mapNatBool`, with no `SeparatesPoints` hypothesis, since
  injectivity of the factor map is irrelevant to the pullback identity.
-/

open Filter MeasurableSpace Set

open scoped ENNReal symmDiff Topology

namespace MeasureTheory

-- `μ` is declared before `m` so that instance synthesis puts `μ` on the ambient `m0`
-- while later `MeasurableSet`/`MeasureDense` obligations default to the sub-σ-algebra `m`;
-- with the reverse order every `Measure.MeasureDense` field application needs `@`.
variable {X : Type*} {m0 : MeasurableSpace X} {μ : Measure X} {m : MeasurableSpace X}

/-! ### From approximation to a.e. representatives -/

section AeGenerate

/-- **A geometric approximating sequence** drawn from a measure-dense family: an `m`-measurable
event of finite trimmed measure is approximated by members of `G` with summable errors. Split
out of `Measure.MeasureDense.exists_generateFrom_ae_eq_of_ne_top` because the summability
bookkeeping is independent of the Borel–Cantelli step. -/
private theorem exists_seq_measure_symmDiff_le (hm : m ≤ m0)
    {G : Set (Set X)} (hG : (μ.trim hm).MeasureDense G) {E : Set X}
    (hE : MeasurableSet[m] E) (hμE : (μ.trim hm) E ≠ ∞) :
    ∃ t : ℕ → Set X, (∀ n, t n ∈ G) ∧ ∀ n, μ (E ∆ t n) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
  have hchoose : ∀ n : ℕ, ∃ t ∈ G, μ (E ∆ t) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro n
    obtain ⟨t, htG, hlt⟩ := hG.approx E hE hμE ((2 : ℝ)⁻¹ ^ n) (by positivity)
    refine ⟨t, htG, ?_⟩
    have hmeas : MeasurableSet[m] (E ∆ t) := hE.symmDiff (hG.measurable t htG)
    have htrim : (μ.trim hm) (E ∆ t) = μ (E ∆ t) := trim_measurableSet_eq hm hmeas
    rw [htrim] at hlt
    refine hlt.le.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos two_pos]
    norm_num
  choose t htG ht using hchoose
  exact ⟨t, htG, ht⟩

/-- **Measure density upgrades to a.e. representatives.** If `G` is measure-dense for the
trimmed measure `μ.trim hm`, then every `m`-measurable event of finite trimmed measure has a
`generateFrom G`-measurable a.e. representative.

This is the statement the factor construction consumes: measure density by itself provides only
*approximation*, whereas the recursion needs actual representatives. The gap is closed by
choosing approximants with summable errors and applying Borel–Cantelli — the representative is
`limsup t n`, and `E ∆ limsup t n` is contained in the limsup of the error sets.

No countability of `G` is needed here; countability matters only when `G` is turned into a
factor space. -/
theorem Measure.MeasureDense.exists_generateFrom_ae_eq_of_ne_top (hm : m ≤ m0)
    {G : Set (Set X)} (hG : (μ.trim hm).MeasureDense G) {E : Set X}
    (hE : MeasurableSet[m] E) (hμE : (μ.trim hm) E ≠ ∞) :
    ∃ E', MeasurableSet[generateFrom G] E' ∧ E' =ᵐ[μ] E := by
  obtain ⟨t, htG, ht⟩ := exists_seq_measure_symmDiff_le hm hG hE hμE
  have hsum : ∑' n, μ (E ∆ t n) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum ht)
    rw [ENNReal.tsum_geometric]
    simp
  refine ⟨limsup t atTop, ?_, ?_⟩
  · rw [limsup_eq_iInf_iSup_of_nat]
    exact MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun _ =>
      MeasurableSet.iUnion fun _ => measurableSet_generateFrom (htG _)
  · -- a.e. `x` lies outside all but finitely many error sets, and there `limsup t` matches `E`
    rw [Filter.eventuallyEq_set]
    filter_upwards [ae_eventually_notMem hsum] with x hx
    rw [mem_limsup_iff_frequently_mem]
    constructor
    · intro hfreq
      by_contra hxE
      have hout : ∀ᶠ n in atTop, x ∉ t n := by
        filter_upwards [hx] with n hn hmem
        exact hn (Set.mem_symmDiff.mpr (Or.inr ⟨hmem, hxE⟩))
      obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually hout).exists
      exact hn2 hn1
    · intro hxE
      refine Filter.Eventually.frequently ?_
      filter_upwards [hx] with n hn
      by_contra hmem
      exact hn (Set.mem_symmDiff.mpr (Or.inl ⟨hxE, hmem⟩))

/-- **Measure density upgrades to a.e. representatives, finite-measure form** — the shape the
`R4` factor construction uses, where the ambient measure is a probability measure and the
finiteness side condition is automatic. -/
theorem Measure.MeasureDense.exists_generateFrom_ae_eq (hm : m ≤ m0) [IsFiniteMeasure μ]
    {G : Set (Set X)} (hG : (μ.trim hm).MeasureDense G) {E : Set X}
    (hE : MeasurableSet[m] E) :
    ∃ E', MeasurableSet[generateFrom G] E' ∧ E' =ᵐ[μ] E :=
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  hG.exists_generateFrom_ae_eq_of_ne_top hm hE (measure_ne_top _ _)

end AeGenerate

/-! ### The threshold estimate -/

section Threshold

/-- **The threshold estimate**: thresholding an `L¹` function at `1/2` produces a set whose
symmetric difference with `E` is controlled by the `L¹` distance to the indicator of `E`,

`ν (E ∆ {x | 1/2 < f x}) ≤ 2 * ‖1_E - f‖₁`.

This is what converts an `L¹`-dense family of functions into a measure-dense family of *sets*,
and hence the separability of `Lᵖ` into the separability of the measure. The proof is Markov's
inequality applied to `1_E - f`, which has norm at least `1/2` on the symmetric difference:
where `E` holds but the threshold fails the difference is at least `1 - 1/2`, and where the
threshold holds but `E` fails it exceeds `1/2`. -/
theorem measure_symmDiff_threshold_le (ν : Measure X) {E : Set X} {f : X → ℝ}
    (hE : MeasurableSet E) (hf : AEStronglyMeasurable f ν) :
    ν (E ∆ {x | 1 / 2 < f x}) ≤ 2 * eLpNorm (E.indicator (fun _ => (1 : ℝ)) - f) 1 ν := by
  set g : X → ℝ := E.indicator (fun _ => (1 : ℝ)) - f with hg
  have hgmeas : AEStronglyMeasurable g ν :=
    (stronglyMeasurable_const.indicator hE).aestronglyMeasurable.sub hf
  -- on the symmetric difference the difference has norm at least `1/2`
  have hsub : E ∆ {x | 1 / 2 < f x} ⊆ {x | (2 : ℝ≥0∞)⁻¹ ≤ ‖g x‖ₑ} := by
    intro x hx
    have hle : (1 : ℝ) / 2 ≤ ‖g x‖ := by
      rcases Set.mem_symmDiff.mp hx with ⟨hxE, hxT⟩ | ⟨hxT, hxE⟩
      · have hfx : f x ≤ 1 / 2 := not_lt.mp hxT
        have : g x = 1 - f x := by
          simp only [hg, Pi.sub_apply, Set.indicator_of_mem hxE]
        rw [Real.norm_eq_abs, this, abs_of_nonneg (by linarith)]
        linarith
      · have hfx : (1 : ℝ) / 2 < f x := hxT
        have : g x = -f x := by
          simp only [hg, Pi.sub_apply, Set.indicator_of_notMem hxE, zero_sub]
        rw [Real.norm_eq_abs, this, abs_neg, abs_of_nonneg (by linarith)]
        linarith
    have h2 : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) := by
      rw [ENNReal.ofReal_div_of_pos two_pos]
      simp
    rw [Set.mem_setOf_eq, h2, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hle
  -- Markov's inequality for the `1`-seminorm
  have hmarkov : (2 : ℝ≥0∞)⁻¹ * ν {x | (2 : ℝ≥0∞)⁻¹ ≤ ‖g x‖ₑ} ≤ eLpNorm g 1 ν := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact mul_meas_ge_le_lintegral₀ hgmeas.enorm _
  calc ν (E ∆ {x | 1 / 2 < f x})
      ≤ ν {x | (2 : ℝ≥0∞)⁻¹ ≤ ‖g x‖ₑ} := measure_mono hsub
    _ = 2 * ((2 : ℝ≥0∞)⁻¹ * ν {x | (2 : ℝ≥0∞)⁻¹ ≤ ‖g x‖ₑ}) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero (by norm_num), one_mul]
    _ ≤ 2 * eLpNorm g 1 ν := by gcongr

end Threshold

end MeasureTheory

/-! ### The Cantor factor of a countably generated σ-algebra -/

namespace MeasurableSpace

/-- **The Cantor factor is exact**: a countably generated σ-algebra is *literally* the pullback
of the Cantor-space σ-algebra along `MeasurableSpace.mapNatBool` — no null sets involved. This
is the missing companion to Mathlib's `measurable_mapNatBool` / `injective_mapNatBool`: it needs
`CountablyGenerated` but **not** `SeparatesPoints`, since injectivity of the factor map is
irrelevant to the pullback identity. -/
theorem comap_mapNatBool (X : Type*) [m : MeasurableSpace X] [CountablyGenerated X] :
    MeasurableSpace.comap (mapNatBool X) inferInstance = m := by
  refine le_antisymm (measurable_mapNatBool X).comap_le ?_
  conv_lhs => rw [← generateFrom_natGeneratingSequence X]
  refine generateFrom_le fun s hs => ?_
  obtain ⟨n, rfl⟩ := hs
  refine ⟨(fun f : ℕ → Bool => f n) ⁻¹' {true},
    (measurable_pi_apply n) (measurableSet_singleton true), ?_⟩
  ext x
  simp [mapNatBool]

end MeasurableSpace
