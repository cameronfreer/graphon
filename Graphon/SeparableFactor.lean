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

* `MeasureTheory.Measure.MeasureDense.exists_generateFrom_ae_eq` — the upgrade from
  *approximation* to *a.e. representatives*: if `G` is countable and measure-dense for the
  trimmed measure, every `m`-measurable event agrees a.e. with a `generateFrom G`-measurable
  one. Proved by summable symmetric-difference approximation and Borel–Cantelli — measure
  density alone gives only approximation, which is not the consumer API.
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

/-- **A geometric approximating sequence** drawn from a measure-dense family: every
`m`-measurable event is approximated by members of `G` with summable errors. Split out of
`Measure.MeasureDense.exists_generateFrom_ae_eq` because the summability bookkeeping is
independent of the Borel–Cantelli step. -/
private theorem exists_seq_measure_symmDiff_le (hm : m ≤ m0) [IsFiniteMeasure μ]
    {G : Set (Set X)} (hG : (μ.trim hm).MeasureDense G) {E : Set X}
    (hE : MeasurableSet[m] E) :
    ∃ t : ℕ → Set X, (∀ n, t n ∈ G) ∧ ∀ n, μ (E ∆ t n) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  have hchoose : ∀ n : ℕ, ∃ t ∈ G, μ (E ∆ t) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro n
    obtain ⟨t, htG, hlt⟩ :=
      hG.approx E hE (measure_ne_top _ _) ((2 : ℝ)⁻¹ ^ n) (by positivity)
    refine ⟨t, htG, ?_⟩
    have hmeas : MeasurableSet[m] (E ∆ t) := hE.symmDiff (hG.measurable t htG)
    have htrim : (μ.trim hm) (E ∆ t) = μ (E ∆ t) := trim_measurableSet_eq hm hmeas
    rw [htrim] at hlt
    refine hlt.le.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos two_pos]
    norm_num
  choose t htG ht using hchoose
  exact ⟨t, htG, ht⟩

/-- **Measure density upgrades to a.e. representatives.** If a countable family `G` is
measure-dense for the trimmed measure `μ.trim hm`, then every `m`-measurable event has a
`generateFrom G`-measurable a.e. representative.

This is the statement the factor construction consumes: measure density by itself provides only
*approximation*, whereas the recursion needs actual representatives. The gap is closed by
choosing approximants with summable errors and applying Borel–Cantelli — the representative is
`limsup t n`, and `E ∆ limsup t n` is contained in the limsup of the error sets. -/
theorem Measure.MeasureDense.exists_generateFrom_ae_eq (hm : m ≤ m0) [IsFiniteMeasure μ]
    {G : Set (Set X)} (hG : (μ.trim hm).MeasureDense G) {E : Set X}
    (hE : MeasurableSet[m] E) :
    ∃ E', MeasurableSet[generateFrom G] E' ∧ E' =ᵐ[μ] E := by
  obtain ⟨t, htG, ht⟩ := exists_seq_measure_symmDiff_le hm hG hE
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

end AeGenerate

end MeasureTheory
