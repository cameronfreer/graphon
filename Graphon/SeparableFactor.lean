/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable

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
* `MeasureTheory.isSeparable_trim` — **separability descends to a sub-σ-algebra**:
  `IsSeparable μ → IsSeparable (μ.trim hm)`. This is the theorem the coherent factor
  realization rests on and it is not in Mathlib. Stated as a theorem rather than an instance:
  with both `m` and `m0` in scope an instance invites measurable-space instance drift at every
  use site.
* `MeasureTheory.exists_measurable_comap_ae_generates` — **factor existence for one
  sub-σ-algebra**:
  over a separable finite measure, `m ≤ m0` admits an `m`-measurable Cantor-space factor map
  whose pullback sits inside `m` and captures every `m`-event modulo null sets. This is the
  single-algebra statement only — see its docstring for why it does not extend to a coherent
  family.
* `MeasurableSpace.comap_mapNatBool` — the missing companion to Mathlib's
  `measurable_mapNatBool`: a countably generated σ-algebra is *literally* the pullback of the
  Cantor-space σ-algebra along `mapNatBool`, with no `SeparatesPoints` hypothesis, since
  injectivity of the factor map is irrelevant to the pullback identity.
-/

open Filter MeasurableSpace Set

open scoped ENNReal symmDiff Topology

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

namespace MeasureTheory

-- `μ` is declared before `m` so that instance synthesis puts `μ` on the ambient `m0`
-- while later `MeasurableSet`/`MeasureDense` obligations default to the sub-σ-algebra `m`;
-- with the reverse order every `Measure.MeasureDense` field application needs `@`.
variable {X : Type*} {m0 : MeasurableSpace X} {μ : Measure X} {m : MeasurableSpace X}

/-! ### Monotonicity of measure density -/

section Mono

variable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}

/-- **A larger family of measurable sets is still measure-dense.** Not in Mathlib, and needed
whenever a dense family is enlarged — e.g. when a chosen family is embedded into a bigger
indexed one. Both hypotheses are necessary: the inclusion gives the approximation, and
measurability of the larger family is not implied by it. -/
theorem Measure.MeasureDense.mono {𝒜 ℬ : Set (Set Y)} (h𝒜 : ν.MeasureDense 𝒜) (hsub : 𝒜 ⊆ ℬ)
    (hmeas : ∀ s ∈ ℬ, MeasurableSet s) : ν.MeasureDense ℬ where
  measurable := hmeas
  approx := fun s hs hfin ε hε => by
    obtain ⟨t, ht, hlt⟩ := h𝒜.approx s hs hfin ε hε
    exact ⟨t, hsub ht, hlt⟩

end Mono

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

/-! ### Separability descends to a sub-σ-algebra -/

section SeparableTrim

/-- **Separability descends to `Measure.trim`.** If `μ` is separable on the ambient
σ-algebra `m0`, the trimmed measure is separable on any sub-σ-algebra `m ≤ m0`.

This is the theorem the coherent factor realization rests on, and it is not in Mathlib. The
route is: `Lp ℝ 1 μ` is second-countable because `μ` is separable; the subgroup
`lpMeasSubgroup ℝ m 1 μ` of `m`-measurable classes inherits second countability as a subtype;
`lpMeasSubgroupToLpTrimIso` transports it to `Lp ℝ 1 (μ.trim hm)`; a countable dense family
there is thresholded at `1/2` into a countable family of `m`-measurable *sets*, and
`measure_symmDiff_threshold_le` turns `L¹` density of the functions into measure density of the
sets.

Exposed as a theorem rather than an instance: with both `m` and `m0` in scope, an instance would
be a standing invitation to measurable-space instance drift at every use site. -/
theorem isSeparable_trim (hm : m ≤ m0) [@IsSeparable X m0 μ] :
    @IsSeparable X m (μ.trim hm) := by
  classical
  haveI : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  haveI : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.one_ne_top⟩
  -- second countability transports from `Lp ℝ 1 μ` to `Lp ℝ 1 (μ.trim hm)`
  haveI : SecondCountableTopology (Lp ℝ 1 (μ.trim hm)) :=
    (lpMeasSubgroupToLpTrimIso ℝ 1 μ hm).symm.toHomeomorph.secondCountableTopology
  obtain ⟨D, hDcount, hDdense⟩ :=
    TopologicalSpace.exists_countable_dense (Lp ℝ 1 (μ.trim hm))
  -- threshold each dense function at `1/2`, using an honestly `m`-measurable representative
  refine ⟨(fun f : Lp ℝ 1 (μ.trim hm) =>
      {x | 1 / 2 < (Lp.aestronglyMeasurable f).mk _ x}) '' D,
    hDcount.image _, ?_, ?_⟩
  · rintro - ⟨f, -, rfl⟩
    exact measurableSet_lt measurable_const (Lp.aestronglyMeasurable f).stronglyMeasurable_mk.measurable
  · intro E hE hEtop ε hε
    -- the indicator of `E` lies in `L¹` of the trimmed measure
    set F : X → ℝ := E.indicator fun _ => (1 : ℝ) with hF
    have hind : MemLp F 1 (μ.trim hm) := memLp_indicator_const 1 hE 1 (Or.inr hEtop)
    set fE : Lp ℝ 1 (μ.trim hm) := hind.toLp F with hfE
    -- pick a dense function within `ε / 4` of it
    obtain ⟨g, hgD, hgdist⟩ := Metric.mem_closure_iff.mp (hDdense fE) (ε / 4) (by linarith)
    refine ⟨{x | 1 / 2 < (Lp.aestronglyMeasurable g).mk _ x}, ⟨g, hgD, rfl⟩, ?_⟩
    have hgmk : (Lp.aestronglyMeasurable g).mk _ =ᵐ[μ.trim hm] g :=
      (Lp.aestronglyMeasurable g).ae_eq_mk.symm
    -- the threshold estimate, with the `L¹` error rewritten as the `Lp` distance
    have hkey : (μ.trim hm) (E ∆ {x | 1 / 2 < (Lp.aestronglyMeasurable g).mk _ x}) ≤
        2 * eLpNorm ((fE : X → ℝ) - (g : X → ℝ)) 1 (μ.trim hm) := by
      refine (measure_symmDiff_threshold_le (μ.trim hm) (E := E)
        (f := (Lp.aestronglyMeasurable g).mk _) hE
        (Lp.aestronglyMeasurable g).stronglyMeasurable_mk.aestronglyMeasurable).trans ?_
      gcongr
      refine le_of_eq (eLpNorm_congr_ae ?_)
      filter_upwards [hgmk, hind.coeFn_toLp] with x hx hy
      simp only [Pi.sub_apply]
      rw [hx, hy]
    refine lt_of_le_of_lt hkey ?_
    -- and the `Lp` distance is at most `ε / 4`
    have hdist : eLpNorm ((fE : X → ℝ) - (g : X → ℝ)) 1 (μ.trim hm) < ENNReal.ofReal (ε / 4) := by
      rw [dist_eq_norm, Lp.norm_def] at hgdist
      calc eLpNorm ((fE : X → ℝ) - (g : X → ℝ)) 1 (μ.trim hm)
          = eLpNorm ((fE - g : Lp ℝ 1 (μ.trim hm)) : X → ℝ) 1 (μ.trim hm) :=
            (eLpNorm_congr_ae (Lp.coeFn_sub _ _)).symm
        _ < ENNReal.ofReal (ε / 4) := by
            rw [← ENNReal.ofReal_toReal (Lp.memLp (fE - g)).eLpNorm_ne_top]
            exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hgdist
    calc 2 * eLpNorm ((fE : X → ℝ) - (g : X → ℝ)) 1 (μ.trim hm)
        ≤ 2 * ENNReal.ofReal (ε / 4) := by gcongr
      _ < ENNReal.ofReal ε := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
          exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)

end SeparableTrim

/-! ### The factor map of a single sub-σ-algebra -/

section Factor

/-- **Factor existence for one sub-σ-algebra**: over a separable finite measure, any
sub-σ-algebra `m ≤ m0` admits a Cantor-space factor map `q` such that

* `q` is `m`-measurable — equivalently `comap q ≤ m`, via `Measurable.comap_le`, so only the
  measurability is stated; and
* every `m`-event agrees a.e. with a `comap q`-event.

So `comap q` captures `m` exactly modulo null sets, while remaining an honest pullback — the
statement never asserts an equality of σ-algebras "modulo null sets".

This assembles the three preceding results: `isSeparable_trim` produces a countable
measure-dense family for the trimmed measure, that family generates a countably generated
sub-σ-algebra whose Cantor factor is exact by `comap_mapNatBool`, and
`Measure.MeasureDense.exists_generateFrom_ae_eq` supplies the a.e. representatives.

**This is the single-algebra statement only.** It is deliberately *not* the tool for a coherent
family: `mapNatBool` is built from a typeclass-chosen generating sequence, which provides
neither literal index inclusion for `C ⊆ A` nor equivariance between different members of a
family. A coherent family needs a common index set chosen up front. -/
theorem exists_measurable_comap_ae_generates (hm : m ≤ m0) [@IsSeparable X m0 μ]
    [IsFiniteMeasure μ] :
    ∃ q : X → (ℕ → Bool), Measurable[m] q ∧
      ∀ E, MeasurableSet[m] E →
        ∃ E', MeasurableSet[MeasurableSpace.comap q inferInstance] E' ∧ E' =ᵐ[μ] E := by
  obtain ⟨G, hGcount, hG⟩ := (isSeparable_trim (μ := μ) hm).1
  -- the family generates a countably generated sub-σ-algebra of `m`.
  -- `generateFrom G` is spelled out rather than abbreviated: a local of type
  -- `MeasurableSpace X` would become the most recent instance candidate and hijack the
  -- `MeasurableSet` obligations that must stay on `m`.
  haveI : @CountablyGenerated X (generateFrom G) :=
    @CountablyGenerated.mk X (generateFrom G) ⟨G, hGcount, rfl⟩
  have hGm : ∀ s ∈ G, MeasurableSet[m] s := hG.measurable
  have hm'm : generateFrom G ≤ m := generateFrom_le hGm
  refine ⟨@mapNatBool X (generateFrom G) _, ?_, ?_⟩
  · exact (@measurable_mapNatBool X (generateFrom G) _).mono hm'm le_rfl
  · intro E hE
    rw [@comap_mapNatBool X (generateFrom G) _]
    exact hG.exists_generateFrom_ae_eq hm hE

end Factor

end MeasureTheory

