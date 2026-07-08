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

/-- **R1c — the probability integral transform (crux).** For an atomless probability measure
`ν` on `ℝ`, its CDF pushes `ν` forward to Lebesgue measure on the unit interval:
`(cdf ν)_* ν = volume.restrict (Icc 0 1)`.

Proof route (see `docs/rokhlin-scoping.md` §8, R1c): `cdf ν` is monotone (measurable) and
continuous (`continuous_cdf_of_noAtoms`) with `cdf ν → 0` at `-∞` and `→ 1` at `+∞`, so it maps
`ℝ` onto `Icc 0 1` (an interval, by IVT + the limits) with, for `a < b`,
`ν (cdf ν ⁻¹' Ioc c d) = d − c` — established on the `Ioc`-generated π-system via
`StieltjesFunction.measure_Ioc` (`ν (a, b] = cdf ν b − cdf ν a`) and continuity/surjectivity,
then extended to all Borel sets. Identify the result with `volume.restrict (Icc 0 1)` by
uniqueness on the `Iic`/`Ioc` π-system. -/
theorem cdf_map_eq_volume_restrict (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    Measure.map (cdf ν) ν = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  sorry

end Graphon.MeasureIso
