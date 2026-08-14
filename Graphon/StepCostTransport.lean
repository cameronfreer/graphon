/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.CutNormPullback
import Graphon.ForMathlib.CountableFactorLift

/-!
# Step-kernel cost transport across the countable-factor lift

Step 4 of the step-approximation programme (#107 remains open).

* `cutNormDiff_pullback_prod_factor` — **exact cost transport**: the coupling cost of two
  pulled-back step kernels under any coupling that pushes to the factor law equals the
  quotient step-kernel cost under the factor law itself. Pure composition: pullback
  functoriality rewrites both costs as pullbacks along the factor-pair map, and the
  cross-carrier cut-norm isometry (`cutNormDiff_pullback_eq_measurePreserving`) collapses
  that map.
* `measurePreserving_prodMap_countableFactorLift` and the `fst`/`snd` companions — the
  step-3 exact-pushforward theorems packaged as `MeasurePreserving` witnesses for the lift.
* `cutNormDiff_pullback_countableFactorLift` — the cost transport instantiated at the
  countable-factor lift: quotient step-kernel cost under `lam` equals pulled-back
  step-kernel cost under `countableFactorLift lam`, exactly. The probability instance on
  the lift is a binder discharged by `isProbabilityMeasure_countableFactorLift`.
* `abs_cutNormDiff_pullback_sub_stepCost_le` — **the approximation bound** step 5 consumes:
  the coupling cost of two graphons differs from the quotient step-kernel cost by at most
  the sum of the two carrier-side step-approximation errors.

Deliberately **not** here: existence of step approximations, finite coupling gluing, and
the triangle assembly — later units of the programme.
-/

open MeasureTheory

namespace Graphon

variable {γ₁ γ₂ ι₁ ι₂ : Type*} [MeasurableSpace γ₁] [MeasurableSpace γ₂]
  [MeasurableSpace ι₁] [MeasurableSpace ι₂]
  {μ₁ : Measure γ₁} {μ₂ : Measure γ₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
  {ν₁ : Measure ι₁} {ν₂ : Measure ι₂} [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
  {q₁ : γ₁ → ι₁} {q₂ : γ₂ → ι₂} {lam : Measure (ι₁ × ι₂)} [IsProbabilityMeasure lam]

/-- **Exact cost transport**: for any coupling `π` of the carriers that pushes to the factor
law `lam` under the factor-pair map, the coupling cost of the pulled-back step kernels under
`π` equals the quotient step-kernel cost under `lam` — an equality, not an estimate. -/
theorem cutNormDiff_pullback_prod_factor (π : Measure (γ₁ × γ₂)) [IsProbabilityMeasure π]
    (K₁ : Graphon ι₁ ν₁) (K₂ : Graphon ι₂ ν₂)
    (hq₁mp : MeasurePreserving q₁ μ₁ ν₁) (hq₂mp : MeasurePreserving q₂ μ₂ ν₂)
    (hΦ : MeasurePreserving (Prod.map q₁ q₂) π lam)
    (hfstπ : MeasurePreserving Prod.fst π μ₁) (hsndπ : MeasurePreserving Prod.snd π μ₂)
    (hfstlam : MeasurePreserving Prod.fst lam ν₁)
    (hsndlam : MeasurePreserving Prod.snd lam ν₂) :
    cutNormDiff (pullback (pullback K₁ q₁ hq₁mp) Prod.fst hfstπ)
        (pullback (pullback K₂ q₂ hq₂mp) Prod.snd hsndπ) =
      cutNormDiff (pullback K₁ Prod.fst hfstlam) (pullback K₂ Prod.snd hsndlam) := by
  rw [pullback_pullback K₁ q₁ hq₁mp Prod.fst hfstπ,
    pullback_pullback K₂ q₂ hq₂mp Prod.snd hsndπ,
    ← cutNormDiff_pullback_eq_measurePreserving (pullback K₁ Prod.fst hfstlam)
      (pullback K₂ Prod.snd hsndlam) (Prod.map q₁ q₂) hΦ,
    pullback_pullback K₁ Prod.fst hfstlam (Prod.map q₁ q₂) hΦ,
    pullback_pullback K₂ Prod.snd hsndlam (Prod.map q₁ q₂) hΦ]
  rfl

section CountableFactorLift

variable [Countable ι₁] [MeasurableSingletonClass ι₁]
  [Countable ι₂] [MeasurableSingletonClass ι₂]

omit [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] [IsProbabilityMeasure lam] in
/-- The factor-pair map is measure-preserving from the countable-factor lift to the factor
law — the step-3 round-trip packaged as a `MeasurePreserving` witness. -/
theorem measurePreserving_prodMap_countableFactorLift
    (hq₁mp : MeasurePreserving q₁ μ₁ ν₁) (hq₂mp : MeasurePreserving q₂ μ₂ ν₂)
    (hfst : lam.map Prod.fst = ν₁) (hsnd : lam.map Prod.snd = ν₂) :
    MeasurePreserving (Prod.map q₁ q₂) (countableFactorLift μ₁ μ₂ q₁ q₂ lam) lam :=
  ⟨hq₁mp.measurable.prodMap hq₂mp.measurable,
    countableFactorLift_map_prodMap hq₁mp.measurable hq₂mp.measurable
      (hfst.trans hq₁mp.map_eq.symm) (hsnd.trans hq₂mp.map_eq.symm)⟩

omit [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] [IsProbabilityMeasure lam] in
/-- The first projection is measure-preserving from the countable-factor lift to the first
carrier — the step-3 exact first marginal packaged as a `MeasurePreserving` witness. -/
theorem measurePreserving_fst_countableFactorLift
    (hq₁mp : MeasurePreserving q₁ μ₁ ν₁) (hq₂mp : MeasurePreserving q₂ μ₂ ν₂)
    (hfst : lam.map Prod.fst = ν₁) (hsnd : lam.map Prod.snd = ν₂) :
    MeasurePreserving Prod.fst (countableFactorLift μ₁ μ₂ q₁ q₂ lam) μ₁ :=
  ⟨measurable_fst,
    countableFactorLift_map_fst hq₁mp.measurable hq₂mp.measurable
      (hfst.trans hq₁mp.map_eq.symm) (hsnd.trans hq₂mp.map_eq.symm)⟩

omit [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] [IsProbabilityMeasure lam] in
/-- The second projection is measure-preserving from the countable-factor lift to the second
carrier — the step-3 exact second marginal packaged as a `MeasurePreserving` witness. -/
theorem measurePreserving_snd_countableFactorLift
    (hq₁mp : MeasurePreserving q₁ μ₁ ν₁) (hq₂mp : MeasurePreserving q₂ μ₂ ν₂)
    (hfst : lam.map Prod.fst = ν₁) (hsnd : lam.map Prod.snd = ν₂) :
    MeasurePreserving Prod.snd (countableFactorLift μ₁ μ₂ q₁ q₂ lam) μ₂ :=
  ⟨measurable_snd,
    countableFactorLift_map_snd hq₁mp.measurable hq₂mp.measurable
      (hfst.trans hq₁mp.map_eq.symm) (hsnd.trans hq₂mp.map_eq.symm)⟩

/-- **Cost transport at the countable-factor lift**: the quotient step-kernel cost under the
factor law `lam` equals the pulled-back step-kernel cost under `countableFactorLift lam`,
exactly. The probability instance on the lift is discharged by
`isProbabilityMeasure_countableFactorLift`. -/
theorem cutNormDiff_pullback_countableFactorLift
    [IsProbabilityMeasure (countableFactorLift μ₁ μ₂ q₁ q₂ lam)]
    (K₁ : Graphon ι₁ ν₁) (K₂ : Graphon ι₂ ν₂)
    (hq₁mp : MeasurePreserving q₁ μ₁ ν₁) (hq₂mp : MeasurePreserving q₂ μ₂ ν₂)
    (hfst : lam.map Prod.fst = ν₁) (hsnd : lam.map Prod.snd = ν₂) :
    cutNormDiff
        (pullback (pullback K₁ q₁ hq₁mp) Prod.fst
          (measurePreserving_fst_countableFactorLift hq₁mp hq₂mp hfst hsnd))
        (pullback (pullback K₂ q₂ hq₂mp) Prod.snd
          (measurePreserving_snd_countableFactorLift hq₁mp hq₂mp hfst hsnd)) =
      cutNormDiff (pullback K₁ Prod.fst ⟨measurable_fst, hfst⟩)
        (pullback K₂ Prod.snd ⟨measurable_snd, hsnd⟩) :=
  cutNormDiff_pullback_prod_factor _ K₁ K₂ hq₁mp hq₂mp
    (measurePreserving_prodMap_countableFactorLift hq₁mp hq₂mp hfst hsnd)
    (measurePreserving_fst_countableFactorLift hq₁mp hq₂mp hfst hsnd)
    (measurePreserving_snd_countableFactorLift hq₁mp hq₂mp hfst hsnd)
    ⟨measurable_fst, hfst⟩ ⟨measurable_snd, hsnd⟩

end CountableFactorLift

/-- **The approximation bound step 5 consumes**: under any coupling `π` pushing to the factor
law, the coupling cost of two graphons differs from the quotient step-kernel cost under the
factor law by at most the sum of the two carrier-side step-approximation errors. Lipschitz
stability replaces each graphon by its pulled-back step kernel; exact cost transport replaces
the resulting cost by the quotient cost. -/
theorem abs_cutNormDiff_pullback_sub_stepCost_le (π : Measure (γ₁ × γ₂))
    [IsProbabilityMeasure π] (U₁ : Graphon γ₁ μ₁) (U₂ : Graphon γ₂ μ₂)
    (K₁ : Graphon ι₁ ν₁) (K₂ : Graphon ι₂ ν₂)
    (hq₁mp : MeasurePreserving q₁ μ₁ ν₁) (hq₂mp : MeasurePreserving q₂ μ₂ ν₂)
    (hΦ : MeasurePreserving (Prod.map q₁ q₂) π lam)
    (hfstπ : MeasurePreserving Prod.fst π μ₁) (hsndπ : MeasurePreserving Prod.snd π μ₂)
    (hfstlam : MeasurePreserving Prod.fst lam ν₁)
    (hsndlam : MeasurePreserving Prod.snd lam ν₂) :
    |cutNormDiff (pullback U₁ Prod.fst hfstπ) (pullback U₂ Prod.snd hsndπ) -
        cutNormDiff (pullback K₁ Prod.fst hfstlam) (pullback K₂ Prod.snd hsndlam)| ≤
      cutNormDiff U₁ (pullback K₁ q₁ hq₁mp) + cutNormDiff U₂ (pullback K₂ q₂ hq₂mp) := by
  rw [← cutNormDiff_pullback_prod_factor π K₁ K₂ hq₁mp hq₂mp hΦ hfstπ hsndπ hfstlam hsndlam]
  exact abs_cutNormDiff_pullback_sub_le U₁ (pullback K₁ q₁ hq₁mp) U₂ (pullback K₂ q₂ hq₂mp)
    Prod.fst Prod.snd hfstπ hsndπ

end Graphon
