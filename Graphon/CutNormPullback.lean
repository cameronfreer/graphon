/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.CutDistance

/-!
# Cross-carrier cut-norm contraction under measure-preserving pullback

`cutNormDiff_pullback_le_measurePreserving`: pulling two graphons back along a
measure-preserving map **between different carriers** does not increase their cut-norm
difference. Step 1 of the step-approximation programme.

**No standard Borel hypothesis.** The same-carrier `cutNormDiff_pullback_le` carries
`[StandardBorelSpace α]`, but its proof is a pure Radon–Nikodym argument: the weight of a
rectangle side `S` is the density of `(μ.restrict S).map φ` against the target measure — a
sub-probability density, `[0,1]`-valued almost everywhere — and the weighted rectangle
integral is dominated by the cut norm (`abs_weighted_integral_diff_le`, itself proved by
layer cake with no regularity of the carrier). This file states the theorem in the generality
the proof supports: arbitrary probability carriers on both sides. Zero-mass rectangle sides
need no special treatment — the density of a zero measure is zero.

Deliberately **not** here: pushing couplings to quotients is the companion result in
`Graphon.ForMathlib.CouplingGluing`; lifting glued couplings back, step-kernel cost transport,
and any triangle-inequality claim are later units of the programme.
-/

open MeasureTheory
open scoped ENNReal

namespace Graphon

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **Cross-carrier cut-norm contraction**: pulling back along a measure-preserving map between
arbitrary probability carriers does not increase the cut-norm difference. No standard Borel
hypothesis — the weights are Radon–Nikodym densities of the mapped restricted measures. -/
theorem cutNormDiff_pullback_le_measurePreserving (U W : Graphon β ν) (φ : α → β)
    (hφ : MeasurePreserving φ μ ν) :
    cutNormDiff (pullback U φ hφ) (pullback W φ hφ) ≤ cutNormDiff U W := by
  classical
  unfold cutNormDiff
  apply Real.iSup_le _ (cutNormDiff_nonneg U W)
  intro S; apply Real.iSup_le _ (cutNormDiff_nonneg U W)
  intro hS; apply Real.iSup_le _ (cutNormDiff_nonneg U W)
  intro T; apply Real.iSup_le _ (cutNormDiff_nonneg U W)
  intro hT
  set D : β × β → ℝ := fun q ↦ U.toAEEqFun q - W.toAEEqFun q with hD
  have hD_sm : StronglyMeasurable D :=
    U.toAEEqFun.stronglyMeasurable.sub W.toAEEqFun.stronglyMeasurable
  have hD_int : Integrable D (ν.prod ν) :=
    (SymmKernel.graphon_integrable U).sub (SymmKernel.graphon_integrable W)
  have hstep1 : rectIntegralDiff (pullback U φ hφ) (pullback W φ hφ) S T =
      ∫ p in S ×ˢ T, D (φ p.1, φ p.2) ∂(μ.prod μ) := by
    unfold rectIntegralDiff
    apply setIntegral_congr_ae (hS.prod hT)
    filter_upwards [pullback_ae U φ hφ, pullback_ae W φ hφ] with p hU hW _
    rw [hU, hW]
  set νS : Measure β := Measure.map φ (μ.restrict S) with hνS
  set νT : Measure β := Measure.map φ (μ.restrict T) with hνT
  have hle : ∀ R : Set α, Measure.map φ (μ.restrict R) ≤ ν := by
    intro R
    refine Measure.le_iff.mpr fun E hE ↦ ?_
    rw [Measure.map_apply hφ.measurable hE, Measure.restrict_apply (hφ.measurable hE)]
    calc μ (φ ⁻¹' E ∩ R) ≤ μ (φ ⁻¹' E) := measure_mono Set.inter_subset_left
      _ = ν E := hφ.measure_preimage hE.nullMeasurableSet
  have hleS : νS ≤ ν := hνS ▸ hle S
  have hleT : νT ≤ ν := hνT ▸ hle T
  have hacS : νS ≪ ν := Measure.absolutelyContinuous_of_le hleS
  have hacT : νT ≪ ν := Measure.absolutelyContinuous_of_le hleT
  haveI : IsFiniteMeasure νS := ⟨lt_of_le_of_lt (hleS Set.univ) (measure_lt_top ν _)⟩
  haveI : IsFiniteMeasure νT := ⟨lt_of_le_of_lt (hleT Set.univ) (measure_lt_top ν _)⟩
  set f0 : β → ℝ := fun a ↦ (νS.rnDeriv ν a).toReal with hf0
  set g0 : β → ℝ := fun b ↦ (νT.rnDeriv ν b).toReal with hg0
  have hf0_meas : Measurable f0 := (Measure.measurable_rnDeriv νS ν).ennreal_toReal
  have hg0_meas : Measurable g0 := (Measure.measurable_rnDeriv νT ν).ennreal_toReal
  have hf0_le : ∀ᵐ a ∂ν, f0 a ≤ 1 := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hleS] with a ha
    calc (νS.rnDeriv ν a).toReal ≤ (1 : ℝ≥0∞).toReal :=
          ENNReal.toReal_mono ENNReal.one_ne_top ha
      _ = 1 := ENNReal.toReal_one
  have hg0_le : ∀ᵐ b ∂ν, g0 b ≤ 1 := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hleT] with b hb
    calc (νT.rnDeriv ν b).toReal ≤ (1 : ℝ≥0∞).toReal :=
          ENNReal.toReal_mono ENNReal.one_ne_top hb
      _ = 1 := ENNReal.toReal_one
  have hkey : ∫ p in S ×ˢ T, D (φ p.1, φ p.2) ∂(μ.prod μ) =
      ∫ x, ∫ y, f0 x * g0 y * D (x, y) ∂ν ∂ν := by
    have hΦmeas : Measurable (Prod.map φ φ) := hφ.measurable.prodMap hφ.measurable
    have hmapΦ : Measure.map (Prod.map φ φ) ((μ.prod μ).restrict (S ×ˢ T)) = νS.prod νT := by
      rw [← Measure.prod_restrict, ← Measure.map_prod_map _ _ hφ.measurable hφ.measurable]
    have hF_int : Integrable (fun q : β × β ↦ f0 q.1 * g0 q.2 * D q) (ν.prod ν) := by
      refine Integrable.mono' hD_int.abs
        ((((hf0_meas.comp measurable_fst).mul (hg0_meas.comp measurable_snd)).mul
          hD_sm.measurable).aestronglyMeasurable) ?_
      have h1 : ∀ᵐ q ∂(ν.prod ν), f0 q.1 ≤ 1 :=
        Measure.quasiMeasurePreserving_fst.ae hf0_le
      have h2 : ∀ᵐ q ∂(ν.prod ν), g0 q.2 ≤ 1 :=
        Measure.quasiMeasurePreserving_snd.ae hg0_le
      filter_upwards [h1, h2] with q hq1 hq2
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |f0 q.1| * |g0 q.2| * |D q| ≤ 1 * 1 * |D q| := by
            gcongr
            · exact ((abs_of_nonneg ENNReal.toReal_nonneg).le.trans hq1)
            · exact ((abs_of_nonneg ENNReal.toReal_nonneg).le.trans hq2)
        _ = |D q| := by ring
    calc ∫ p in S ×ˢ T, D (φ p.1, φ p.2) ∂(μ.prod μ)
        = ∫ p, D (Prod.map φ φ p) ∂((μ.prod μ).restrict (S ×ˢ T)) := rfl
      _ = ∫ q, D q ∂(Measure.map (Prod.map φ φ) ((μ.prod μ).restrict (S ×ˢ T))) :=
          (integral_map hΦmeas.aemeasurable hD_sm.aestronglyMeasurable).symm
      _ = ∫ q, D q ∂(νS.prod νT) := by rw [hmapΦ]
      _ = ∫ q, D q
            ∂((ν.prod ν).withDensity fun q ↦ νS.rnDeriv ν q.1 * νT.rnDeriv ν q.2) := by
          rw [← MeasureTheory.prod_withDensity (Measure.measurable_rnDeriv νS ν)
              (Measure.measurable_rnDeriv νT ν),
            Measure.withDensity_rnDeriv_eq νS ν hacS, Measure.withDensity_rnDeriv_eq νT ν hacT]
      _ = ∫ q, (νS.rnDeriv ν q.1 * νT.rnDeriv ν q.2).toReal • D q ∂(ν.prod ν) := by
          refine integral_withDensity_eq_integral_toReal_smul
            (((Measure.measurable_rnDeriv νS ν).comp measurable_fst).mul
              ((Measure.measurable_rnDeriv νT ν).comp measurable_snd)) ?_ D
          have h1 : ∀ᵐ q ∂(ν.prod ν), νS.rnDeriv ν q.1 < ∞ :=
            Measure.quasiMeasurePreserving_fst.ae (Measure.rnDeriv_lt_top νS ν)
          have h2 : ∀ᵐ q ∂(ν.prod ν), νT.rnDeriv ν q.2 < ∞ :=
            Measure.quasiMeasurePreserving_snd.ae (Measure.rnDeriv_lt_top νT ν)
          filter_upwards [h1, h2] with q hq1 hq2
          exact ENNReal.mul_lt_top hq1 hq2
      _ = ∫ q : β × β, f0 q.1 * g0 q.2 * D q ∂(ν.prod ν) := by
          congr 1; funext q
          rw [smul_eq_mul, ENNReal.toReal_mul]
      _ = ∫ x, ∫ y, f0 x * g0 y * D (x, y) ∂ν ∂ν := integral_prod _ hF_int
  set f : β → ℝ := fun a ↦ min (f0 a) 1 with hf
  set g : β → ℝ := fun b ↦ min (g0 b) 1 with hg
  have hf_meas : Measurable f := hf0_meas.min measurable_const
  have hg_meas : Measurable g := hg0_meas.min measurable_const
  have hf_bound : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := fun x ↦
    ⟨le_min ENNReal.toReal_nonneg zero_le_one, min_le_right _ _⟩
  have hg_bound : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1 := fun x ↦
    ⟨le_min ENNReal.toReal_nonneg zero_le_one, min_le_right _ _⟩
  have hf_ae : (f : β → ℝ) =ᵐ[ν] f0 := by
    filter_upwards [hf0_le] with a ha using min_eq_left ha
  have hg_ae : (g : β → ℝ) =ᵐ[ν] g0 := by
    filter_upwards [hg0_le] with b hb using min_eq_left hb
  have hcongr : ∫ x, ∫ y, f0 x * g0 y * D (x, y) ∂ν ∂ν =
      ∫ x, ∫ y, f x * g y * D (x, y) ∂ν ∂ν := by
    apply integral_congr_ae
    filter_upwards [hf_ae] with x hx
    apply integral_congr_ae
    filter_upwards [hg_ae] with y hy
    rw [hx, hy]
  calc |rectIntegralDiff (pullback U φ hφ) (pullback W φ hφ) S T|
      = |∫ x, ∫ y, f x * g y * (U.toAEEqFun (x, y) - W.toAEEqFun (x, y)) ∂ν ∂ν| := by
        rw [hstep1, hkey, hcongr]
    _ ≤ cutNormDiff U W :=
        abs_weighted_integral_diff_le U W f g hf_meas hg_meas hf_bound hg_bound

/-- **Rectangle transport**: the rectangle integral of a pulled-back difference over a
pulled-back rectangle equals the original rectangle integral — change of variables along the
measure-preserving map, restricted to the rectangle sides. -/
theorem rectIntegralDiff_pullback_preimage (U W : Graphon β ν) (φ : α → β)
    (hφ : MeasurePreserving φ μ ν) {S T : Set β} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    rectIntegralDiff (pullback U φ hφ) (pullback W φ hφ) (φ ⁻¹' S) (φ ⁻¹' T) =
      rectIntegralDiff U W S T := by
  set D : β × β → ℝ := fun q ↦ U.toAEEqFun q - W.toAEEqFun q with hD
  have hD_sm : StronglyMeasurable D :=
    U.toAEEqFun.stronglyMeasurable.sub W.toAEEqFun.stronglyMeasurable
  have hstep : rectIntegralDiff (pullback U φ hφ) (pullback W φ hφ) (φ ⁻¹' S) (φ ⁻¹' T) =
      ∫ p in (φ ⁻¹' S) ×ˢ (φ ⁻¹' T), D (φ p.1, φ p.2) ∂(μ.prod μ) := by
    unfold rectIntegralDiff
    apply setIntegral_congr_ae ((hφ.measurable hS).prod (hφ.measurable hT))
    filter_upwards [pullback_ae U φ hφ, pullback_ae W φ hφ] with p hU hW _
    rw [hU, hW]
  have hΦ : MeasurePreserving (Prod.map φ φ)
      ((μ.restrict (φ ⁻¹' S)).prod (μ.restrict (φ ⁻¹' T)))
      ((ν.restrict S).prod (ν.restrict T)) :=
    (hφ.restrict_preimage hS).prod (hφ.restrict_preimage hT)
  rw [hstep]
  unfold rectIntegralDiff
  calc ∫ p in (φ ⁻¹' S) ×ˢ (φ ⁻¹' T), D (φ p.1, φ p.2) ∂(μ.prod μ)
      = ∫ p, D (φ p.1, φ p.2) ∂((μ.restrict (φ ⁻¹' S)).prod (μ.restrict (φ ⁻¹' T))) := by
        rw [Measure.prod_restrict]
    _ = ∫ p, D (Prod.map φ φ p) ∂((μ.restrict (φ ⁻¹' S)).prod (μ.restrict (φ ⁻¹' T))) := rfl
    _ = ∫ q, D q ∂(Measure.map (Prod.map φ φ)
          ((μ.restrict (φ ⁻¹' S)).prod (μ.restrict (φ ⁻¹' T)))) :=
        (integral_map hΦ.measurable.aemeasurable hD_sm.aestronglyMeasurable).symm
    _ = ∫ q, D q ∂((ν.restrict S).prod (ν.restrict T)) := by rw [hΦ.map_eq]
    _ = ∫ q in S ×ˢ T, D q ∂(ν.prod ν) := by rw [Measure.prod_restrict]

/-- **Cross-carrier cut-norm expansion bound**: the original cut-norm difference is attained
among the pulled-back kernels — every rectangle test on the target lifts to the pulled-back
rectangle test on the source with the same value. -/
theorem le_cutNormDiff_pullback_measurePreserving (U W : Graphon β ν) (φ : α → β)
    (hφ : MeasurePreserving φ μ ν) :
    cutNormDiff U W ≤ cutNormDiff (pullback U φ hφ) (pullback W φ hφ) := by
  have hnn := cutNormDiff_nonneg (pullback U φ hφ) (pullback W φ hφ)
  unfold cutNormDiff
  apply Real.iSup_le _ hnn
  intro S; apply Real.iSup_le _ hnn
  intro hS; apply Real.iSup_le _ hnn
  intro T; apply Real.iSup_le _ hnn
  intro hT
  calc |rectIntegralDiff U W S T|
      = |rectIntegralDiff (pullback U φ hφ) (pullback W φ hφ) (φ ⁻¹' S) (φ ⁻¹' T)| := by
        rw [rectIntegralDiff_pullback_preimage U W φ hφ hS hT]
    _ ≤ cutNormDiff (pullback U φ hφ) (pullback W φ hφ) :=
        abs_rectIntegralDiff_le _ _ (hφ.measurable hS) (hφ.measurable hT)

/-- **Cross-carrier cut-norm isometry**: for kernels that factor through the map — both
compared kernels are pullbacks along the same measure-preserving map — the pullback is an
exact cut-norm isometry, not merely a contraction. Combines the contraction
(`cutNormDiff_pullback_le_measurePreserving`) with rectangle transport. -/
theorem cutNormDiff_pullback_eq_measurePreserving (U W : Graphon β ν) (φ : α → β)
    (hφ : MeasurePreserving φ μ ν) :
    cutNormDiff (pullback U φ hφ) (pullback W φ hφ) = cutNormDiff U W :=
  le_antisymm (cutNormDiff_pullback_le_measurePreserving U W φ hφ)
    (le_cutNormDiff_pullback_measurePreserving U W φ hφ)

/-- **Generic Lipschitz stability of coupling cost under changing both marginal kernels**:
for two measure-preserving maps out of a common carrier — coupling projections are the
intended instance — the pulled-back cut-norm difference moves by at most the sum of the two
marginal cut-norm differences. Two triangle inequalities plus the cross-carrier contraction,
once along each map. -/
theorem abs_cutNormDiff_pullback_sub_le {γ : Type*} [MeasurableSpace γ] {ρ : Measure γ}
    [IsProbabilityMeasure ρ] (U U' : Graphon β ν) (W W' : Graphon γ ρ)
    (φ : α → β) (ψ : α → γ) (hφ : MeasurePreserving φ μ ν) (hψ : MeasurePreserving ψ μ ρ) :
    |cutNormDiff (pullback U φ hφ) (pullback W ψ hψ) -
        cutNormDiff (pullback U' φ hφ) (pullback W' ψ hψ)| ≤
      cutNormDiff U U' + cutNormDiff W W' := by
  have key : ∀ (A A' : Graphon β ν) (B B' : Graphon γ ρ),
      cutNormDiff (pullback A φ hφ) (pullback B ψ hψ) ≤
        cutNormDiff A A' + cutNormDiff B B' +
          cutNormDiff (pullback A' φ hφ) (pullback B' ψ hψ) := by
    intro A A' B B'
    calc cutNormDiff (pullback A φ hφ) (pullback B ψ hψ)
        ≤ cutNormDiff (pullback A φ hφ) (pullback A' φ hφ) +
            cutNormDiff (pullback A' φ hφ) (pullback B ψ hψ) := cutNormDiff_triangle _ _ _
      _ ≤ cutNormDiff (pullback A φ hφ) (pullback A' φ hφ) +
            (cutNormDiff (pullback A' φ hφ) (pullback B' ψ hψ) +
              cutNormDiff (pullback B' ψ hψ) (pullback B ψ hψ)) := by
          gcongr
          exact cutNormDiff_triangle _ _ _
      _ ≤ cutNormDiff A A' +
            (cutNormDiff (pullback A' φ hφ) (pullback B' ψ hψ) + cutNormDiff B' B) := by
          gcongr
          · exact cutNormDiff_pullback_le_measurePreserving A A' φ hφ
          · exact cutNormDiff_pullback_le_measurePreserving B' B ψ hψ
      _ = cutNormDiff A A' + cutNormDiff B B' +
            cutNormDiff (pullback A' φ hφ) (pullback B' ψ hψ) := by
          rw [cutNormDiff_symm B' B]; ring
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · have h := key U U' W W'
    linarith
  · have h := key U' U W' W
    rw [cutNormDiff_symm U' U, cutNormDiff_symm W' W] at h
    linarith

end Graphon
