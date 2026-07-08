/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib

/-!
# The atomless standard-Borel measure-isomorphism theorem (Rokhlin campaign, R1)

This file builds, from the ground up, the measure-theoretic core that the graphon program's
four remaining `sorry`s (`exists_common_coupling_maps`, `cutNormDiff_pullback_le`,
`exists_controlled_cell_alignment`, `exists_mpEquiv_cutNormDiff_lt_add` in
`Graphon/CutDistance.lean`) all reduce to (see `docs/rokhlin-scoping.md` §7–8):

> An atomless standard-Borel probability space `(α, μ)` is measure-preservingly isomorphic
> mod 0 to `([0,1], Lebesgue)`.

It is deliberately **independent of graphons** — pure Mathlib-style measure theory, and a
plausible upstreaming target.

## Roadmap (R1)

* **R1b** `continuous_cdf_of_noAtoms` — the CDF of an atomless probability measure on `ℝ` is
  continuous. **PROVED.**
* **R1c** `cdf_map_eq_volume_restrict` — the *probability integral transform*: the CDF pushes
  an atomless probability measure on `ℝ` to Lebesgue measure on `[0,1]`. *(the crux; stated)*
* **R1d** the quantile map is a mod-0 inverse of the CDF (a.e. inverse both directions).
* **R1e** transport a general atomless standard-Borel probability space to the real line via
  `embeddingReal`, then assemble the everywhere `≃ᵐ`.

Then **R2** derives the four cores by conjugating through the isomorphism.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Function

namespace Graphon.MeasureIso

/-- **R1b — CDF continuity from atomlessness.** The cumulative distribution function of an
atomless probability measure on `ℝ` is continuous. (A general CDF is only right-continuous;
the left jumps are exactly the atoms, `cdf ν x − leftLim (cdf ν) x = ν {x}`, which vanish.) -/
theorem continuous_cdf_of_noAtoms (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    Continuous (cdf ν) := by
  have hleft : ∀ x, leftLim (cdf ν) x = cdf ν x := by
    intro x
    have hsing : (cdf ν).measure {x} = 0 := by rw [measure_cdf]; exact measure_singleton x
    rw [StieltjesFunction.measure_singleton] at hsing
    have hle : leftLim (cdf ν) x ≤ cdf ν x := (cdf ν).mono.leftLim_le le_rfl
    have hz : cdf ν x - leftLim (cdf ν) x ≤ 0 := ENNReal.ofReal_eq_zero.mp hsing
    exact le_antisymm hle (by linarith)
  rw [continuous_iff_continuousAt]
  intro x
  rw [(cdf ν).mono.continuousAt_iff_leftLim_eq_rightLim, hleft x,
    ((cdf ν).right_continuous x).rightLim_eq]

/-- The `ν`-measure of the sublevel set `{x | cdf ν x ≤ y}` is `y` (for `y < 1`). This is the
analytic heart of the probability integral transform: closedness of the sublevel set (CDF
continuity) plus the boundary value `cdf ν (sSup S) = y` (from the limit `cdf ν → 1`) pin the
set down to `Iic (sSup S)`, whose measure is `cdf ν (sSup S) = y` via `ofReal_cdf`. -/
private lemma cdf_sublevel_measure (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν]
    (y : ℝ) (hy1 : y < 1) :
    ν {x | cdf ν x ≤ y} = ENNReal.ofReal y := by
  set S : Set ℝ := {x | cdf ν x ≤ y} with hS
  have hScl : IsClosed S := isClosed_Iic.preimage (continuous_cdf_of_noAtoms ν)
  have hevt : ∀ᶠ x in atTop, y < cdf ν x :=
    (tendsto_cdf_atTop ν).eventually (eventually_gt_nhds hy1)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hevt
  have hSbdd : BddAbove S := by
    refine ⟨M, fun x hx => ?_⟩
    by_contra hxM
    exact absurd (hM x (le_of_lt (not_le.mp hxM))) (not_lt.2 hx)
  by_cases hSne : S.Nonempty
  · set q := sSup S with hq
    have hq_mem : q ∈ S := hScl.csSup_mem hSne hSbdd
    have hSeq : S = Iic q := by
      ext x
      constructor
      · intro hx; exact le_csSup hSbdd hx
      · intro hx
        exact le_trans ((cdf ν).mono hx) hq_mem
    have hcdfq : cdf ν q = y := by
      refine le_antisymm hq_mem ?_
      have htend : Tendsto (cdf ν) (𝓝[>] q) (𝓝 (cdf ν q)) :=
        ((continuous_cdf_of_noAtoms ν).tendsto q).mono_left nhdsWithin_le_nhds
      have hevt2 : ∀ᶠ x in 𝓝[>] q, y ≤ cdf ν x := by
        refine Filter.eventually_of_mem self_mem_nhdsWithin (fun x hx => ?_)
        have : x ∉ S := fun hxS => absurd (le_csSup hSbdd hxS) (not_le.2 hx)
        exact le_of_lt (not_le.mp this)
      exact ge_of_tendsto htend hevt2
    rw [hSeq, ← ofReal_cdf ν q, hcdfq]
  · rw [not_nonempty_iff_eq_empty] at hSne
    have hyle : y ≤ 0 := by
      have hfor : ∀ᶠ x in atBot, y ≤ cdf ν x := by
        refine Filter.Eventually.of_forall (fun x => ?_)
        have : x ∉ S := by rw [hSne]; simp
        exact le_of_lt (not_le.mp this)
      exact ge_of_tendsto (tendsto_cdf_atBot ν) hfor
    have hνS : ν S = 0 := by rw [hSne]; exact measure_empty
    rw [ENNReal.ofReal_eq_zero.mpr hyle]
    exact hνS

/-- **R1c — the probability integral transform (crux).** For an atomless probability measure
`ν` on `ℝ`, its CDF pushes `ν` forward to Lebesgue measure on the unit interval:
`(cdf ν)_* ν = volume.restrict (Icc 0 1)`.

Proof: by `ext_of_Iic` it suffices to match `(cdf ν)_* ν (Iic y)` with `volume.restrict (Icc 0 1)
(Iic y)` for every `y`. The former is `ν {x | cdf ν x ≤ y}`; the latter is `volume (Iic y ∩ Icc 0
1)`. For `y < 1` both equal `ENNReal.ofReal y` (`cdf_sublevel_measure`, and `Iic y ∩ Icc 0 1 =
Icc 0 y`); for `y ≥ 1` both equal `1` (the sublevel set is `univ` since `cdf ≤ 1 ≤ y`, and
`Iic y ∩ Icc 0 1 = Icc 0 1`). -/
theorem cdf_map_eq_volume_restrict (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    Measure.map (cdf ν) ν = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  have hmeas : Measurable (cdf ν) := (cdf ν).mono.measurable
  haveI : IsProbabilityMeasure (Measure.map (cdf ν) ν) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine Measure.ext_of_Iic _ _ (fun y => ?_)
  rw [Measure.map_apply hmeas measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  rcases lt_or_ge y 1 with hy1 | hy1
  · -- `y < 1`: sublevel measure is `y`, and `Iic y ∩ Icc 0 1 = Icc 0 y` has volume `y`.
    have hrset : Iic y ∩ Icc (0 : ℝ) 1 = Icc 0 y := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨hxy, hx0, _⟩; exact ⟨hx0, hxy⟩
      · rintro ⟨hx0, hxy⟩; exact ⟨hxy, hx0, le_of_lt (lt_of_le_of_lt hxy hy1)⟩
    rw [hrset, Real.volume_Icc, sub_zero]
    exact cdf_sublevel_measure ν y hy1
  · -- `y ≥ 1`: sublevel set is `univ` (`cdf ≤ 1 ≤ y`), and `Iic y ∩ Icc 0 1 = Icc 0 1`.
    have hset : cdf ν ⁻¹' Iic y = univ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact le_trans (cdf_le_one ν x) hy1
    have hrset : Iic y ∩ Icc (0 : ℝ) 1 = Icc 0 1 := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc, and_iff_right_iff_imp]
      rintro ⟨_, hx1⟩; exact le_trans hx1 hy1
    rw [hset, hrset, measure_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]

end Graphon.MeasureIso
