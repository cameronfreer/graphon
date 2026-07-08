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

/-! ### R1d — the quantile map as a mod-0 inverse of the CDF -/

/-- **R1d — the quantile (generalized-inverse) map.** `cdfQuantile ν u` is the least `x` whose
CDF value is at least `u`. By the ℝ conventions `sInf ∅ = sInf univ = 0`, it equals `0` for
`u ≤ 0` (the sublevel set is all of `ℝ`) and for `u > 1` (the sublevel set is empty); on the
open interval `Ioo 0 1` it is a genuine two-sided inverse of the (continuous) CDF. -/
noncomputable def cdfQuantile (ν : Measure ℝ) (u : ℝ) : ℝ := sInf {x | u ≤ cdf ν x}

variable {ν : Measure ℝ}

/-- The super-level set `{x | u ≤ cdf ν x}` is closed (CDF continuity). -/
private lemma setOf_cdf_ge_isClosed (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν]
    (u : ℝ) : IsClosed {x | u ≤ cdf ν x} := by
  have hpre : {x : ℝ | u ≤ cdf ν x} = cdf ν ⁻¹' Ici u := by ext x; simp [mem_Ici]
  rw [hpre]
  exact isClosed_Ici.preimage (continuous_cdf_of_noAtoms ν)

/-- For `u < 1` the super-level set is nonempty (`cdf ν → 1` at `atTop`). -/
private lemma setOf_cdf_ge_nonempty (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν]
    (u : ℝ) (hu1 : u < 1) : {x | u ≤ cdf ν x}.Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop ν).eventually (eventually_gt_nhds hu1)).exists
  exact ⟨x, le_of_lt hx⟩

/-- For `0 < u` the super-level set is bounded below (`cdf ν → 0` at `atBot`). -/
private lemma setOf_cdf_ge_bddBelow (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν]
    (u : ℝ) (hu0 : 0 < u) : BddBelow {x | u ≤ cdf ν x} := by
  obtain ⟨M, hM⟩ :=
    eventually_atBot.mp ((tendsto_cdf_atBot ν).eventually (eventually_lt_nhds hu0))
  refine ⟨M, fun x hx => ?_⟩
  by_contra hxM
  exact absurd hx (not_le.mpr (hM x (le_of_lt (not_le.mp hxM))))

/-- Membership of the infimum in the super-level set: `u ≤ cdf ν (cdfQuantile ν u)`
for `u ∈ Ioo 0 1`. -/
private lemma le_cdf_cdfQuantile (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν]
    (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) : u ≤ cdf ν (cdfQuantile ν u) :=
  (setOf_cdf_ge_isClosed ν u).csInf_mem (setOf_cdf_ge_nonempty ν u hu1)
    (setOf_cdf_ge_bddBelow ν u hu0)

/-- The Galois characterization on `Ioo 0 1`: `cdfQuantile ν u ≤ x ↔ u ≤ cdf ν x`. -/
private lemma cdfQuantile_le_iff (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν]
    (u x : ℝ) (hu0 : 0 < u) (hu1 : u < 1) : cdfQuantile ν u ≤ x ↔ u ≤ cdf ν x := by
  constructor
  · intro h
    exact le_trans (le_cdf_cdfQuantile ν u hu0 hu1) ((cdf ν).mono h)
  · intro h
    exact csInf_le (setOf_cdf_ge_bddBelow ν u hu0) h

/-- The quantile is `0` on `(-∞, 0]`: the super-level set is all of `ℝ` (`cdf ≥ 0 ≥ u`). -/
private lemma cdfQuantile_of_nonpos (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν]
    (u : ℝ) (hu : u ≤ 0) : cdfQuantile ν u = 0 := by
  have huniv : {x : ℝ | u ≤ cdf ν x} = univ := by
    ext x; simp only [mem_setOf_eq, mem_univ, iff_true]
    exact le_trans hu (cdf_nonneg ν x)
  show sInf {x | u ≤ cdf ν x} = 0
  rw [huniv, Real.sInf_univ]

/-- The quantile is `0` on `(1, ∞)`: the super-level set is empty (`cdf ≤ 1 < u`). -/
private lemma cdfQuantile_of_gt_one (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν]
    (u : ℝ) (hu : 1 < u) : cdfQuantile ν u = 0 := by
  have hempty : {x : ℝ | u ≤ cdf ν x} = ∅ := by
    ext x; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
    exact lt_of_le_of_lt (cdf_le_one ν x) hu
  show sInf {x | u ≤ cdf ν x} = 0
  rw [hempty, Real.sInf_empty]

/-- **Section lemma (the crux workhorse).** On `Ioo 0 1` the quantile is a right inverse of the
continuous CDF: `cdf ν (cdfQuantile ν u) = u`. The lower bound `u ≤ cdf ν q` is membership of
the infimum in the (closed) super-level set; the upper bound `cdf ν q ≤ u` comes from the
left-limit of the CDF at `q`, all points below `q` lying outside the super-level set. -/
private lemma cdf_cdfQuantile_of_mem_Ioo (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν]
    (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) : cdf ν (cdfQuantile ν u) = u := by
  refine le_antisymm ?_ (le_cdf_cdfQuantile ν u hu0 hu1)
  have htend : Tendsto (cdf ν) (𝓝[<] (cdfQuantile ν u)) (𝓝 (cdf ν (cdfQuantile ν u))) :=
    ((continuous_cdf_of_noAtoms ν).tendsto _).mono_left nhdsWithin_le_nhds
  have hevt : ∀ᶠ x in 𝓝[<] (cdfQuantile ν u), cdf ν x ≤ u := by
    refine eventually_of_mem self_mem_nhdsWithin (fun x hx => ?_)
    have hxlt : x < cdfQuantile ν u := hx
    have hxA : ¬ u ≤ cdf ν x := fun hmem =>
      absurd (csInf_le (setOf_cdf_ge_bddBelow ν u hu0) hmem) (not_le.mpr hxlt)
    exact le_of_lt (not_le.mp hxA)
  exact le_of_tendsto htend hevt

/-- **R1d — measurability of the quantile map.** Although `cdfQuantile ν` is not globally
monotone (it drops back to `0` outside `[0,1]`), each sublevel set `{u | cdfQuantile ν u ≤ c}`
splits, by the region of `u`, into the manifestly measurable pieces coming from the constant
value `0` on `Iic 0 ∪ Ioi 1`, the Galois identity on `Ioo 0 1`, and the single point `{1}`. -/
theorem measurable_cdfQuantile (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    Measurable (cdfQuantile ν) := by
  apply measurable_of_Iic
  intro c
  have hconst : ∀ P : Prop, MeasurableSet {_u : ℝ | P} := by
    intro P
    rcases Classical.em P with hP | hP
    · rw [show {_u : ℝ | P} = univ from by ext; simp [hP]]; exact MeasurableSet.univ
    · rw [show {_u : ℝ | P} = ∅ from by ext; simp [hP]]; exact MeasurableSet.empty
  have hset : cdfQuantile ν ⁻¹' Iic c
      = ((Iic 0 ∪ Ioi 1) ∩ {_u : ℝ | (0 : ℝ) ≤ c})
        ∪ (Ioo 0 1 ∩ Iic (cdf ν c))
        ∪ ({(1 : ℝ)} ∩ {_u : ℝ | cdfQuantile ν 1 ≤ c}) := by
    ext u
    simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_Ioo, mem_Ioi,
      mem_singleton_iff, mem_setOf_eq]
    rcases le_or_gt u 0 with h | h0
    · rw [cdfQuantile_of_nonpos ν u h]
      constructor
      · intro hc; exact Or.inl (Or.inl ⟨Or.inl h, hc⟩)
      · rintro ((⟨_, hc⟩ | ⟨⟨hu0, _⟩, _⟩) | ⟨he, _⟩)
        · exact hc
        · linarith
        · linarith
    · rcases lt_trichotomy u 1 with hu1 | heq | hgt
      · rw [cdfQuantile_le_iff ν u c h0 hu1]
        constructor
        · intro hc; exact Or.inl (Or.inr ⟨⟨h0, hu1⟩, hc⟩)
        · rintro ((⟨h' | h', _⟩ | ⟨_, hc⟩) | ⟨he, _⟩)
          · linarith
          · linarith
          · exact hc
          · linarith
      · subst heq
        constructor
        · intro hc; exact Or.inr ⟨rfl, hc⟩
        · rintro ((⟨h' | h', _⟩ | ⟨⟨_, h'⟩, _⟩) | ⟨_, hc⟩)
          · linarith
          · linarith
          · linarith
          · exact hc
      · rw [cdfQuantile_of_gt_one ν u hgt]
        constructor
        · intro hc; exact Or.inl (Or.inl ⟨Or.inr hgt, hc⟩)
        · rintro ((⟨_, hc⟩ | ⟨⟨_, h'⟩, _⟩) | ⟨he, _⟩)
          · exact hc
          · linarith
          · linarith
  rw [hset]
  exact (((measurableSet_Iic.union measurableSet_Ioi).inter (hconst _)).union
    (measurableSet_Ioo.inter measurableSet_Iic)).union
    (measurableSet_singleton 1 |>.inter (hconst _))

/-- The pair `{0, 1}` is `volume`-null (both singletons are null). -/
private lemma ae_not_mem_zero_one :
    ∀ᵐ u ∂(volume : Measure ℝ), u ∉ ({0, 1} : Set ℝ) := by
  rw [ae_iff]
  simp only [not_not, setOf_mem_eq]
  exact ((Set.countable_singleton (1 : ℝ)).insert 0).measure_zero volume

/-- **R1d — first a.e. inverse.** On `[0,1]` (equipped with Lebesgue measure) the CDF is a left
inverse of the quantile: `cdf ν (cdfQuantile ν u) = u` for a.e. `u`, since the exceptional set
lies in the `volume`-null pair `{0, 1}`. -/
theorem cdf_cdfQuantile_ae (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    (fun u => cdf ν (cdfQuantile ν u)) =ᵐ[volume.restrict (Set.Icc 0 1)] id := by
  refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
  filter_upwards [ae_not_mem_zero_one] with u hu huIcc
  have hu0 : u ≠ 0 := fun h => hu (by simp [h])
  have hu1 : u ≠ 1 := fun h => hu (by simp [h])
  have h0 : 0 < u := lt_of_le_of_ne huIcc.1 (Ne.symm hu0)
  have h1 : u < 1 := lt_of_le_of_ne huIcc.2 hu1
  exact cdf_cdfQuantile_of_mem_Ioo ν u h0 h1

/-- **R1d — the quantile transform (the isomorphism identity).** The quantile pushes Lebesgue
measure on `[0,1]` forward to `ν`. By `ext_of_Iic` it suffices to match `Iic`-measures: the
preimage `cdfQuantile ν ⁻¹' Iic t ∩ Icc 0 1` agrees, up to the null pair `{0, 1}`, with
`Ioc 0 (cdf ν t)` (Galois identity on `Ioo 0 1`), whose volume is `cdf ν t = ν (Iic t)`. -/
theorem map_cdfQuantile_volume_restrict (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    Measure.map (cdfQuantile ν) (volume.restrict (Set.Icc (0 : ℝ) 1)) = ν := by
  have hmeas : Measurable (cdfQuantile ν) := measurable_cdfQuantile ν
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    simp [Real.volume_Icc]
  haveI : IsProbabilityMeasure (Measure.map (cdfQuantile ν) (volume.restrict (Set.Icc (0 : ℝ) 1)))
      := Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine Measure.ext_of_Iic _ _ (fun t => ?_)
  rw [Measure.map_apply hmeas measurableSet_Iic, Measure.restrict_apply (hmeas measurableSet_Iic)]
  have hae : (((cdfQuantile ν ⁻¹' Iic t) ∩ Icc (0 : ℝ) 1 : Set ℝ)) =ᵐ[volume]
      (Ioc (0 : ℝ) (cdf ν t) : Set ℝ) := by
    rw [eventuallyEq_set]
    filter_upwards [ae_not_mem_zero_one] with u hu
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Icc, mem_Ioc]
    have hu0 : u ≠ 0 := fun h => hu (by simp [h])
    have hu1 : u ≠ 1 := fun h => hu (by simp [h])
    rcases lt_trichotomy u 0 with hlt | heq | hgt
    · constructor
      · rintro ⟨_, h0, _⟩; linarith
      · rintro ⟨h0, _⟩; linarith
    · exact absurd heq hu0
    · rcases lt_trichotomy u 1 with h1 | h1 | h1
      · rw [cdfQuantile_le_iff ν u t hgt h1]
        constructor
        · rintro ⟨hut, _, _⟩; exact ⟨hgt, hut⟩
        · rintro ⟨_, hut⟩; exact ⟨hut, le_of_lt hgt, le_of_lt h1⟩
      · exact absurd h1 hu1
      · constructor
        · rintro ⟨_, _, hle1⟩; linarith
        · rintro ⟨_, hut⟩
          exact absurd (le_trans hut (cdf_le_one ν t)) (by linarith)
  rw [measure_congr hae, Real.volume_Ioc, sub_zero, ← ofReal_cdf ν t]

/-- **R1d — second a.e. inverse.** The quantile is a left inverse of the CDF `ν`-a.e.:
`cdfQuantile ν (cdf ν x) = x` for a.e. `x`. Since `cdf ν x > 0` a.e.-`ν` (the left tail
`{cdf ≤ 0}` is `ν`-null) we get `cdfQuantile ν (cdf ν x) ≤ x` a.e.; combined with the equal
pushforwards `map (cdfQuantile ν ∘ cdf ν) ν = ν` (via the two transport identities) and the
monotone bounded `arctan` test, the a.e. inequality is forced to an a.e. equality. -/
theorem cdfQuantile_cdf_ae (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    (fun x => cdfQuantile ν (cdf ν x)) =ᵐ[ν] id := by
  have hmeasQ : Measurable (cdfQuantile ν) := measurable_cdfQuantile ν
  have hmeasCdf : Measurable (cdf ν) := (cdf ν).mono.measurable
  -- `cdf ν x > 0` for a.e. `x` (the left tail `{cdf ≤ 0}` has `ν`-measure `0`).
  have hpos : ∀ᵐ x ∂ν, 0 < cdf ν x := by
    have h0 : ν {x | cdf ν x ≤ 0} = 0 := by
      have := cdf_sublevel_measure ν 0 (by norm_num)
      simpa using this
    rw [ae_iff]; simp only [not_lt]; exact h0
  -- Pointwise (a.e.) `cdfQuantile ν (cdf ν x) ≤ x`.
  have hle : ∀ᵐ x ∂ν, cdfQuantile ν (cdf ν x) ≤ x := by
    filter_upwards [hpos] with x hx
    exact csInf_le (setOf_cdf_ge_bddBelow ν (cdf ν x) hx) (le_refl (cdf ν x))
  -- Equal pushforwards: `map (cdfQuantile ν ∘ cdf ν) ν = ν`.
  have hmap : Measure.map (fun x => cdfQuantile ν (cdf ν x)) ν = ν := by
    rw [show (fun x => cdfQuantile ν (cdf ν x)) = cdfQuantile ν ∘ cdf ν from rfl,
      ← Measure.map_map hmeasQ hmeasCdf, cdf_map_eq_volume_restrict ν,
      map_cdfQuantile_volume_restrict ν]
  -- `arctan` is bounded, hence integrable against the finite measure `ν`.
  have habs : ∀ y : ℝ, ‖Real.arctan y‖ ≤ Real.pi / 2 := fun y => by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan y), le_of_lt (Real.arctan_lt_pi_div_two y)⟩
  have hIg : Integrable (fun x => Real.arctan (cdfQuantile ν (cdf ν x))) ν :=
    Integrable.of_bound
      ((Real.continuous_arctan.measurable.comp (hmeasQ.comp hmeasCdf)).aestronglyMeasurable)
      (Real.pi / 2) (Filter.Eventually.of_forall (fun x => habs _))
  have hIid : Integrable (fun x => Real.arctan x) ν :=
    Integrable.of_bound Real.continuous_arctan.aestronglyMeasurable (Real.pi / 2)
      (Filter.Eventually.of_forall (fun x => habs x))
  -- Equal integrals of `arctan` after the equal pushforwards.
  have hInt : ∫ x, Real.arctan (cdfQuantile ν (cdf ν x)) ∂ν = ∫ x, Real.arctan x ∂ν := by
    have hm := integral_map (μ := ν) (φ := fun x => cdfQuantile ν (cdf ν x))
      (f := Real.arctan) (hmeasQ.comp hmeasCdf).aemeasurable
      Real.continuous_arctan.aestronglyMeasurable
    rw [hmap] at hm
    rw [← hm]
  -- `arctan` monotone: `arctan (G (cdf x)) ≤ arctan x` a.e.
  have hmono : ∀ᵐ x ∂ν,
      Real.arctan (cdfQuantile ν (cdf ν x)) ≤ Real.arctan x := by
    filter_upwards [hle] with x hx
    exact Real.arctan_strictMono.monotone hx
  -- The nonnegative difference has zero integral, hence vanishes a.e.
  have hnonneg : 0 ≤ᵐ[ν] (fun x => Real.arctan x - Real.arctan (cdfQuantile ν (cdf ν x))) := by
    filter_upwards [hmono] with x hx
    simp only [Pi.zero_apply]; linarith
  have hzero : ∫ x, (Real.arctan x - Real.arctan (cdfQuantile ν (cdf ν x))) ∂ν = 0 := by
    rw [integral_sub hIid hIg, hInt, sub_self]
  have hvanish := (integral_eq_zero_iff_of_nonneg_ae hnonneg (hIid.sub hIg)).mp hzero
  filter_upwards [hvanish] with x hx
  have heq : Real.arctan (cdfQuantile ν (cdf ν x)) = Real.arctan x := by
    simp only [Pi.zero_apply] at hx; linarith
  exact Real.arctan_injective heq

/-! ### R1e — the mod-0 measure isomorphism, packaged and assembled

We package a measure-preserving isomorphism *mod 0* as a bundled `Mod0MeasureIso` structure
(two measurable maps that push each measure to the other and are mutually inverse a.e.), prove
it composes (`Mod0MeasureIso.trans`), instantiate it on the real line via the CDF/quantile pair
(`realMod0MeasureIso`), and transport a general atomless standard-Borel probability space to the
real line via `embeddingReal` (`embeddingRealMod0MeasureIso`). Composing the two yields the main
theorem: every atomless standard-Borel probability space is isomorphic mod 0 to
`([0,1], Lebesgue)` (`atomless_standardBorel_mod0MeasureIso_unitInterval`). -/

/-- **R1e — a measure-preserving isomorphism mod 0.** A pair of measurable maps `toFun`, `invFun`
that push `μ` and `ν` onto each other and are two-sided inverses almost everywhere. -/
structure Mod0MeasureIso (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) where
  toFun : α → β
  invFun : β → α
  measurable_toFun : Measurable toFun
  measurable_invFun : Measurable invFun
  map_toFun : Measure.map toFun μ = ν
  map_invFun : Measure.map invFun ν = μ
  left_inv_ae : (fun x => invFun (toFun x)) =ᵐ[μ] id
  right_inv_ae : (fun y => toFun (invFun y)) =ᵐ[ν] id

/-- **R1e — composition of mod-0 isomorphisms.** The a.e.-inverse identities are chained by
pulling each factor's a.e. identity back through the other map, using that the pushforward
equalities make the maps `QuasiMeasurePreserving` (so `ν`-a.e. statements become `μ`-a.e.
statements after precomposition, via `QuasiMeasurePreserving.ae_eq`). -/
def Mod0MeasureIso.trans {α β γ} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure β} {ξ : Measure γ}
    (e : Mod0MeasureIso α β μ ν) (f : Mod0MeasureIso β γ ν ξ) : Mod0MeasureIso α γ μ ξ where
  toFun := f.toFun ∘ e.toFun
  invFun := e.invFun ∘ f.invFun
  measurable_toFun := f.measurable_toFun.comp e.measurable_toFun
  measurable_invFun := e.measurable_invFun.comp f.measurable_invFun
  map_toFun := by
    rw [← Measure.map_map f.measurable_toFun e.measurable_toFun, e.map_toFun, f.map_toFun]
  map_invFun := by
    rw [← Measure.map_map e.measurable_invFun f.measurable_invFun, f.map_invFun, e.map_invFun]
  left_inv_ae := by
    have hqmp : Measure.QuasiMeasurePreserving e.toFun μ ν := by
      refine ⟨e.measurable_toFun, ?_⟩
      rw [e.map_toFun]
    have h1 := hqmp.ae_eq f.left_inv_ae
    filter_upwards [h1, e.left_inv_ae] with x hx1 hx2
    simp only [Function.comp_apply, id_eq] at hx1 hx2 ⊢
    rw [hx1]; exact hx2
  right_inv_ae := by
    have hqmp : Measure.QuasiMeasurePreserving f.invFun ξ ν := by
      refine ⟨f.measurable_invFun, ?_⟩
      rw [f.map_invFun]
    have h2 := hqmp.ae_eq e.right_inv_ae
    filter_upwards [h2, f.right_inv_ae] with y hy1 hy2
    simp only [Function.comp_apply, id_eq] at hy1 hy2 ⊢
    rw [hy1]; exact hy2

/-- **R1e — the real-line instance.** The CDF/quantile pair of an atomless probability measure
`ν` on `ℝ` is a mod-0 isomorphism between `(ℝ, ν)` and `([0,1], Lebesgue)`. -/
noncomputable def realMod0MeasureIso (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    Mod0MeasureIso ℝ ℝ ν (volume.restrict (Set.Icc 0 1)) where
  toFun := cdf ν
  invFun := cdfQuantile ν
  measurable_toFun := (cdf ν).mono.measurable
  measurable_invFun := measurable_cdfQuantile ν
  map_toFun := cdf_map_eq_volume_restrict ν
  map_invFun := map_cdfQuantile_volume_restrict ν
  left_inv_ae := cdfQuantile_cdf_ae ν
  right_inv_ae := cdf_cdfQuantile_ae ν

/-- The pushforward of an atomless measure by a measurable embedding is atomless: each singleton
has an at-most-singleton preimage, which is null. -/
private lemma noAtoms_map_of_injective {α β} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [NoAtoms μ] {f : α → β} (hf : MeasurableEmbedding f) :
    NoAtoms (Measure.map f μ) := by
  refine ⟨fun y => ?_⟩
  rw [hf.map_apply]
  have hsub : (f ⁻¹' {y}).Subsingleton := by
    intro a ha b hb
    simp only [mem_preimage, mem_singleton_iff] at ha hb
    exact hf.injective (ha.trans hb.symm)
  exact hsub.measure_zero μ

/-- **R1e — the standard-Borel embedding instance.** A standard-Borel space `α` measurably embeds
into `ℝ` via `embeddingReal`; that embedding is a mod-0 isomorphism from `(α, μ)` to the
pushforward `(ℝ, map (embeddingReal α) μ)`. The right inverse holds `ν`-a.e. because `ν` is
concentrated on the range of the embedding. -/
noncomputable def embeddingRealMod0MeasureIso (α) [MeasurableSpace α] [StandardBorelSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] [Nonempty α] :
    Mod0MeasureIso α ℝ μ (Measure.map (embeddingReal α) μ) :=
  let he := measurableEmbedding_embeddingReal α
  { toFun := embeddingReal α
    invFun := he.invFun
    measurable_toFun := he.measurable
    measurable_invFun := he.measurable_invFun
    map_toFun := rfl
    map_invFun := by
      rw [Measure.map_map he.measurable_invFun he.measurable]
      have : he.invFun ∘ embeddingReal α = id := funext he.leftInverse_invFun
      rw [this, Measure.map_id]
    left_inv_ae := ae_of_all _ he.leftInverse_invFun
    right_inv_ae := by
      haveI : IsProbabilityMeasure (Measure.map (embeddingReal α) μ) :=
        Measure.isProbabilityMeasure_map he.measurable.aemeasurable
      have hrange : Measure.map (embeddingReal α) μ (range (embeddingReal α))ᶜ = 0 := by
        have h1 : Measure.map (embeddingReal α) μ (range (embeddingReal α)) = 1 := by
          rw [he.map_apply, preimage_range, measure_univ]
        rw [measure_compl he.measurableSet_range (measure_ne_top _ _), h1, measure_univ,
          tsub_self]
      have hmem : ∀ᵐ y ∂(Measure.map (embeddingReal α) μ), y ∈ range (embeddingReal α) := by
        rw [ae_iff]; exact hrange
      filter_upwards [hmem] with y hy
      obtain ⟨x, rfl⟩ := hy
      simp only [id_eq]
      rw [he.leftInverse_invFun x] }

/-- **R1e — the atomless standard-Borel measure-isomorphism theorem.** Every atomless
standard-Borel probability space `(α, μ)` is measure-preservingly isomorphic mod 0 to
`([0,1], Lebesgue)`. Assembled by embedding `α` into `ℝ` and composing with the real-line
CDF/quantile isomorphism of the (atomless, probability) pushforward measure. -/
theorem atomless_standardBorel_mod0MeasureIso_unitInterval (α) [MeasurableSpace α]
    [StandardBorelSpace α] (μ : Measure α) [IsProbabilityMeasure μ] [NoAtoms μ] :
    Nonempty (Mod0MeasureIso α ℝ μ (volume.restrict (Set.Icc 0 1))) := by
  have hne : Nonempty α := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 : (μ Set.univ) = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at h1
    exact zero_ne_one h1
  haveI : IsProbabilityMeasure (Measure.map (embeddingReal α) μ) :=
    Measure.isProbabilityMeasure_map (measurableEmbedding_embeddingReal α).measurable.aemeasurable
  haveI : NoAtoms (Measure.map (embeddingReal α) μ) :=
    noAtoms_map_of_injective (measurableEmbedding_embeddingReal α)
  exact ⟨(embeddingRealMod0MeasureIso α μ).trans
    (realMod0MeasureIso (Measure.map (embeddingReal α) μ))⟩

end Graphon.MeasureIso
