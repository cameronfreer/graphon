/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.StepCostTransport
import Graphon.FiniteFactorApproximation

/-!
# The coupling triangle inequality across arbitrary carriers

Step 5b of the step-approximation programme (#107 remains open): the assembly.

`cutNormDiff_gluedOuterCoupling_le` — **the finite-level triangle**: on standard-Borel factors,
the cost of the glued outer coupling is at most the sum of the two input costs. Every cost is
pulled back to the glued triple law, where a single `cutNormDiff_triangle` applies; the
cross-carrier isometry identifies each pulled-back cost with the original one, so no error is
incurred by the transport.

The standard-Borel hypothesis here is discharged at the point of use by the **finite** factors
of `FiniteFactorApproximation`; the graphon carriers themselves stay arbitrary.
-/

open MeasureTheory

namespace Graphon

section FiniteTriangle

variable {ι₁ ι₂ ι₃ : Type*}
  [MeasurableSpace ι₁] [StandardBorelSpace ι₁] [Nonempty ι₁]
  [MeasurableSpace ι₂] [StandardBorelSpace ι₂] [Nonempty ι₂]
  [MeasurableSpace ι₃] [StandardBorelSpace ι₃] [Nonempty ι₃]
  {ν₁ : Measure ι₁} {ν₂ : Measure ι₂} {ν₃ : Measure ι₃}
  [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] [IsProbabilityMeasure ν₃]
  {lam₁₂ : Measure (ι₁ × ι₂)} {lam₂₃ : Measure (ι₂ × ι₃)}
  [IsProbabilityMeasure lam₁₂] [IsProbabilityMeasure lam₂₃]

/-- **The triangle inequality at the factor level.** The cost of the glued outer coupling is at
most the sum of the two input costs — exactly, with no error term. All three costs are pulled
back to the glued triple law, where one application of `cutNormDiff_triangle` finishes; the
cross-carrier isometry (`cutNormDiff_pullback_eq_measurePreserving`) identifies each pulled-back
cost with the corresponding original, so the transport is lossless. -/
theorem cutNormDiff_gluedOuterCoupling_le (K₁ : Graphon ι₁ ν₁) (K₂ : Graphon ι₂ ν₂)
    (K₃ : Graphon ι₃ ν₃) (hmid : lam₂₃.map Prod.fst = lam₁₂.map Prod.snd)
    (hfst₁₂ : MeasurePreserving Prod.fst lam₁₂ ν₁)
    (hsnd₁₂ : MeasurePreserving Prod.snd lam₁₂ ν₂)
    (hfst₂₃ : MeasurePreserving Prod.fst lam₂₃ ν₂)
    (hsnd₂₃ : MeasurePreserving Prod.snd lam₂₃ ν₃)
    (hfst₁₃ : MeasurePreserving Prod.fst (gluedOuterCoupling lam₁₂ lam₂₃) ν₁)
    (hsnd₁₃ : MeasurePreserving Prod.snd (gluedOuterCoupling lam₁₂ lam₂₃) ν₃) :
    cutNormDiff (pullback K₁ Prod.fst hfst₁₃) (pullback K₃ Prod.snd hsnd₁₃) ≤
      cutNormDiff (pullback K₁ Prod.fst hfst₁₂) (pullback K₂ Prod.snd hsnd₁₂) +
        cutNormDiff (pullback K₂ Prod.fst hfst₂₃) (pullback K₃ Prod.snd hsnd₂₃) := by
  have hg₁₂ : MeasurePreserving (fun w : ι₁ × ι₂ × ι₃ => (w.1, w.2.1))
      (gluedCoupling lam₁₂ lam₂₃) lam₁₂ :=
    ⟨measurable_fst.prodMk measurable_snd.fst, gluedCoupling_map_fst_snd⟩
  have hg₂₃ : MeasurePreserving (fun w : ι₁ × ι₂ × ι₃ => w.2)
      (gluedCoupling lam₁₂ lam₂₃) lam₂₃ :=
    ⟨measurable_snd, gluedCoupling_map_snd_trd hmid⟩
  have hg₁₃ : MeasurePreserving (fun w : ι₁ × ι₂ × ι₃ => (w.1, w.2.2))
      (gluedCoupling lam₁₂ lam₂₃) (gluedOuterCoupling lam₁₂ lam₂₃) :=
    ⟨measurable_fst.prodMk measurable_snd.snd, rfl⟩
  have hp₁ : MeasurePreserving (fun w : ι₁ × ι₂ × ι₃ => w.1)
      (gluedCoupling lam₁₂ lam₂₃) ν₁ := hfst₁₂.comp hg₁₂
  have hp₂ : MeasurePreserving (fun w : ι₁ × ι₂ × ι₃ => w.2.1)
      (gluedCoupling lam₁₂ lam₂₃) ν₂ := hsnd₁₂.comp hg₁₂
  have hp₃ : MeasurePreserving (fun w : ι₁ × ι₂ × ι₃ => w.2.2)
      (gluedCoupling lam₁₂ lam₂₃) ν₃ := hsnd₂₃.comp hg₂₃
  have e₁₂ : cutNormDiff (pullback K₁ _ hp₁) (pullback K₂ _ hp₂) =
      cutNormDiff (pullback K₁ Prod.fst hfst₁₂) (pullback K₂ Prod.snd hsnd₁₂) := by
    rw [← cutNormDiff_pullback_eq_measurePreserving (pullback K₁ Prod.fst hfst₁₂)
      (pullback K₂ Prod.snd hsnd₁₂) _ hg₁₂, pullback_pullback, pullback_pullback]
    rfl
  have e₂₃ : cutNormDiff (pullback K₂ _ hp₂) (pullback K₃ _ hp₃) =
      cutNormDiff (pullback K₂ Prod.fst hfst₂₃) (pullback K₃ Prod.snd hsnd₂₃) := by
    rw [← cutNormDiff_pullback_eq_measurePreserving (pullback K₂ Prod.fst hfst₂₃)
      (pullback K₃ Prod.snd hsnd₂₃) _ hg₂₃, pullback_pullback, pullback_pullback]
    rfl
  have e₁₃ : cutNormDiff (pullback K₁ _ hp₁) (pullback K₃ _ hp₃) =
      cutNormDiff (pullback K₁ Prod.fst hfst₁₃) (pullback K₃ Prod.snd hsnd₁₃) := by
    rw [← cutNormDiff_pullback_eq_measurePreserving (pullback K₁ Prod.fst hfst₁₃)
      (pullback K₃ Prod.snd hsnd₁₃) _ hg₁₃, pullback_pullback, pullback_pullback]
    rfl
  rw [← e₁₂, ← e₂₃, ← e₁₃]
  exact cutNormDiff_triangle _ _ _

end FiniteTriangle

section Assembly

variable {Ω₁ Ω₂ Ω₃ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
  {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {μ₃ : Measure Ω₃}
  [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure μ₃]

/-- **The coupling triangle inequality across arbitrary carriers.** Given couplings of
`(U₁, U₂)` and `(U₂, U₃)` and a finite-factor approximation of each graphon — with the **same**
approximation of the middle graphon used on both sides — there is a coupling of `(U₁, U₃)` whose
cost is at most the sum of the two given costs plus `2 * (e₁ + e₂ + e₃)`.

The carriers `Ω₁, Ω₂, Ω₃` are arbitrary probability spaces: **no standard-Borel hypothesis**.
Gluing happens on the finite factors, where standard Borel is automatic. The chain is: push both
couplings to the finite factors (their middle marginals agree precisely because the middle
approximation is shared), glue there, lift the glued factor law back to the carriers by
`countableFactorLift`, transport the cost exactly, and pay one approximation error at each of the
three cost comparisons — `(e₁ + e₃) + (e₁ + e₂) + (e₂ + e₃) = 2 * (e₁ + e₂ + e₃)`. -/
theorem exists_coupling_cutNormDiff_le_add_add
    {U₁ : Graphon Ω₁ μ₁} {U₂ : Graphon Ω₂ μ₂} {U₃ : Graphon Ω₃ μ₃} {e₁ e₂ e₃ : ℝ}
    (A₁ : FiniteFactorApproximation U₁ e₁) (A₂ : FiniteFactorApproximation U₂ e₂)
    (A₃ : FiniteFactorApproximation U₃ e₃)
    (π₁₂ : Measure (Ω₁ × Ω₂)) [IsProbabilityMeasure π₁₂]
    (hfst₁₂ : MeasurePreserving Prod.fst π₁₂ μ₁) (hsnd₁₂ : MeasurePreserving Prod.snd π₁₂ μ₂)
    (π₂₃ : Measure (Ω₂ × Ω₃)) [IsProbabilityMeasure π₂₃]
    (hfst₂₃ : MeasurePreserving Prod.fst π₂₃ μ₂) (hsnd₂₃ : MeasurePreserving Prod.snd π₂₃ μ₃) :
    ∃ (π₁₃ : Measure (Ω₁ × Ω₃)) (_ : IsProbabilityMeasure π₁₃)
      (h₁ : MeasurePreserving Prod.fst π₁₃ μ₁) (h₃ : MeasurePreserving Prod.snd π₁₃ μ₃),
      cutNormDiff (pullback U₁ Prod.fst h₁) (pullback U₃ Prod.snd h₃) ≤
        cutNormDiff (pullback U₁ Prod.fst hfst₁₂) (pullback U₂ Prod.snd hsnd₁₂) +
          cutNormDiff (pullback U₂ Prod.fst hfst₂₃) (pullback U₃ Prod.snd hsnd₂₃) +
          2 * (e₁ + e₂ + e₃) := by
  have hq₁ : Measurable A₁.factor := A₁.factor_mp.measurable
  have hq₂ : Measurable A₂.factor := A₂.factor_mp.measurable
  have hq₃ : Measurable A₃.factor := A₃.factor_mp.measurable
  haveI : IsProbabilityMeasure (π₁₂.map (Prod.map A₁.factor A₂.factor)) :=
    isProbabilityMeasure_map_prodMap hq₁ hq₂
  haveI : IsProbabilityMeasure (π₂₃.map (Prod.map A₂.factor A₃.factor)) :=
    isProbabilityMeasure_map_prodMap hq₂ hq₃
  -- The marginals of the two factor laws; the middle ones agree because `A₂` is shared.
  have hl₁₂f : (π₁₂.map (Prod.map A₁.factor A₂.factor)).map Prod.fst = A₁.law := by
    rw [map_prodMap_map_fst hq₁ hq₂, hfst₁₂.map_eq, A₁.factor_mp.map_eq]
  have hl₁₂s : (π₁₂.map (Prod.map A₁.factor A₂.factor)).map Prod.snd = A₂.law := by
    rw [map_prodMap_map_snd hq₁ hq₂, hsnd₁₂.map_eq, A₂.factor_mp.map_eq]
  have hl₂₃f : (π₂₃.map (Prod.map A₂.factor A₃.factor)).map Prod.fst = A₂.law := by
    rw [map_prodMap_map_fst hq₂ hq₃, hfst₂₃.map_eq, A₂.factor_mp.map_eq]
  have hl₂₃s : (π₂₃.map (Prod.map A₂.factor A₃.factor)).map Prod.snd = A₃.law := by
    rw [map_prodMap_map_snd hq₂ hq₃, hsnd₂₃.map_eq, A₃.factor_mp.map_eq]
  have hmid : (π₂₃.map (Prod.map A₂.factor A₃.factor)).map Prod.fst =
      (π₁₂.map (Prod.map A₁.factor A₂.factor)).map Prod.snd := by rw [hl₂₃f, hl₁₂s]
  -- The glued factor law and its marginals.
  have hl₁₃f : (gluedOuterCoupling (π₁₂.map (Prod.map A₁.factor A₂.factor))
      (π₂₃.map (Prod.map A₂.factor A₃.factor))).map Prod.fst = A₁.law := by
    rw [gluedOuterCoupling_map_fst, hl₁₂f]
  have hl₁₃s : (gluedOuterCoupling (π₁₂.map (Prod.map A₁.factor A₂.factor))
      (π₂₃.map (Prod.map A₂.factor A₃.factor))).map Prod.snd = A₃.law := by
    rw [gluedOuterCoupling_map_snd hmid, hl₂₃s]
  -- Measure-preserving witnesses at the factor level.
  have m₁₂f : MeasurePreserving Prod.fst (π₁₂.map (Prod.map A₁.factor A₂.factor)) A₁.law :=
    ⟨measurable_fst, hl₁₂f⟩
  have m₁₂s : MeasurePreserving Prod.snd (π₁₂.map (Prod.map A₁.factor A₂.factor)) A₂.law :=
    ⟨measurable_snd, hl₁₂s⟩
  have m₂₃f : MeasurePreserving Prod.fst (π₂₃.map (Prod.map A₂.factor A₃.factor)) A₂.law :=
    ⟨measurable_fst, hl₂₃f⟩
  have m₂₃s : MeasurePreserving Prod.snd (π₂₃.map (Prod.map A₂.factor A₃.factor)) A₃.law :=
    ⟨measurable_snd, hl₂₃s⟩
  have m₁₃f : MeasurePreserving Prod.fst (gluedOuterCoupling
      (π₁₂.map (Prod.map A₁.factor A₂.factor)) (π₂₃.map (Prod.map A₂.factor A₃.factor)))
      A₁.law := ⟨measurable_fst, hl₁₃f⟩
  have m₁₃s : MeasurePreserving Prod.snd (gluedOuterCoupling
      (π₁₂.map (Prod.map A₁.factor A₂.factor)) (π₂₃.map (Prod.map A₂.factor A₃.factor)))
      A₃.law := ⟨measurable_snd, hl₁₃s⟩
  -- The lift of the glued factor law to the carriers.
  haveI : IsProbabilityMeasure (countableFactorLift μ₁ μ₃ A₁.factor A₃.factor
      (gluedOuterCoupling (π₁₂.map (Prod.map A₁.factor A₂.factor))
        (π₂₃.map (Prod.map A₂.factor A₃.factor)))) :=
    isProbabilityMeasure_countableFactorLift hq₁ hq₃
      (hl₁₃f.trans A₁.factor_mp.map_eq.symm) (hl₁₃s.trans A₃.factor_mp.map_eq.symm)
  have h₁ := measurePreserving_fst_countableFactorLift (μ₁ := μ₁) (μ₂ := μ₃)
    A₁.factor_mp A₃.factor_mp hl₁₃f hl₁₃s
  have h₃ := measurePreserving_snd_countableFactorLift (μ₁ := μ₁) (μ₂ := μ₃)
    A₁.factor_mp A₃.factor_mp hl₁₃f hl₁₃s
  refine ⟨_, inferInstance, h₁, h₃, ?_⟩
  -- Exact cost transport at each of the three couplings, with one approximation error each.
  have b₁₃ := abs_cutNormDiff_pullback_sub_stepCost_le
    (countableFactorLift μ₁ μ₃ A₁.factor A₃.factor
      (gluedOuterCoupling (π₁₂.map (Prod.map A₁.factor A₂.factor))
        (π₂₃.map (Prod.map A₂.factor A₃.factor))))
    U₁ U₃ A₁.kernel A₃.kernel A₁.factor_mp A₃.factor_mp
    (measurePreserving_prodMap_countableFactorLift A₁.factor_mp A₃.factor_mp hl₁₃f hl₁₃s)
    h₁ h₃ m₁₃f m₁₃s
  have b₁₂ := abs_cutNormDiff_pullback_sub_stepCost_le π₁₂ U₁ U₂ A₁.kernel A₂.kernel
    A₁.factor_mp A₂.factor_mp ⟨hq₁.prodMap hq₂, rfl⟩ hfst₁₂ hsnd₁₂ m₁₂f m₁₂s
  have b₂₃ := abs_cutNormDiff_pullback_sub_stepCost_le π₂₃ U₂ U₃ A₂.kernel A₃.kernel
    A₂.factor_mp A₃.factor_mp ⟨hq₂.prodMap hq₃, rfl⟩ hfst₂₃ hsnd₂₃ m₂₃f m₂₃s
  -- The factor-level triangle, and the three approximation errors.
  have tri := cutNormDiff_gluedOuterCoupling_le A₁.kernel A₂.kernel A₃.kernel hmid
    m₁₂f m₁₂s m₂₃f m₂₃s m₁₃f m₁₃s
  have hA₁ := A₁.error_lt
  have hA₂ := A₂.error_lt
  have hA₃ := A₃.error_lt
  rw [abs_le] at b₁₃ b₁₂ b₂₃
  linarith [b₁₃.1, b₁₃.2, b₁₂.1, b₁₂.2, b₂₃.1, b₂₃.2]

/-- **The triangle inequality up to an arbitrarily small error.** No approximation data is
supplied: `exists_finiteFactorApproximation` is invoked at scale `ε / 6` for each graphon, and
the three shared errors contribute `2 * (ε/6 + ε/6 + ε/6) = ε`. The middle graphon's
approximation is chosen once and reused on both sides, which is what makes the two factor laws
share a middle marginal and lets them be glued. -/
theorem exists_coupling_cutNormDiff_le_add_add_of_pos
    (U₁ : Graphon Ω₁ μ₁) (U₂ : Graphon Ω₂ μ₂) (U₃ : Graphon Ω₃ μ₃) {ε : ℝ} (hε : 0 < ε)
    (π₁₂ : Measure (Ω₁ × Ω₂)) [IsProbabilityMeasure π₁₂]
    (hfst₁₂ : MeasurePreserving Prod.fst π₁₂ μ₁) (hsnd₁₂ : MeasurePreserving Prod.snd π₁₂ μ₂)
    (π₂₃ : Measure (Ω₂ × Ω₃)) [IsProbabilityMeasure π₂₃]
    (hfst₂₃ : MeasurePreserving Prod.fst π₂₃ μ₂) (hsnd₂₃ : MeasurePreserving Prod.snd π₂₃ μ₃) :
    ∃ (π₁₃ : Measure (Ω₁ × Ω₃)) (_ : IsProbabilityMeasure π₁₃)
      (h₁ : MeasurePreserving Prod.fst π₁₃ μ₁) (h₃ : MeasurePreserving Prod.snd π₁₃ μ₃),
      cutNormDiff (pullback U₁ Prod.fst h₁) (pullback U₃ Prod.snd h₃) ≤
        cutNormDiff (pullback U₁ Prod.fst hfst₁₂) (pullback U₂ Prod.snd hsnd₁₂) +
          cutNormDiff (pullback U₂ Prod.fst hfst₂₃) (pullback U₃ Prod.snd hsnd₂₃) + ε := by
  have hε6 : (0 : ℝ) < ε / 6 := by linarith
  obtain ⟨A₁⟩ := exists_finiteFactorApproximation U₁ hε6
  obtain ⟨A₂⟩ := exists_finiteFactorApproximation U₂ hε6
  obtain ⟨A₃⟩ := exists_finiteFactorApproximation U₃ hε6
  obtain ⟨π₁₃, hprob, h₁, h₃, hle⟩ := exists_coupling_cutNormDiff_le_add_add A₁ A₂ A₃
    π₁₂ hfst₁₂ hsnd₁₂ π₂₃ hfst₂₃ hsnd₂₃
  exact ⟨π₁₃, hprob, h₁, h₃, by linarith⟩

end Assembly

end Graphon
