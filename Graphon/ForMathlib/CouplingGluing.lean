/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.ForMathlib.RelativeFactorCoupling

/-!
# Gluing two couplings over a shared marginal

Two couplings sharing their middle marginal — `π₁₂` of `(μ₁, μ₂)` and `π₂₃` of `(μ₂, μ₃)` —
glue to a joint law on `Ω₁ × Ω₂ × Ω₃` whose `(1,2)`-projection is `π₁₂`, whose
`(2,3)`-projection is `π₂₃`, and whose `(1,3)`-projection is therefore a coupling of
`(μ₁, μ₃)`. This is the measure-theoretic core of the triangle inequality for coupling-defined
distances (Janson, *Graphons, cut norm and distance*, Lemma 6.5).

## The construction is the relative joining — no conditional-weight formulas

The glued law is `relativeFactorCoupling π₁₂ π₂₃ Prod.snd Prod.fst` — the relatively
independent joining of the two couplings over their common middle factor — reordered to
`Ω₁ × Ω₂ × Ω₃`. Both disintegrations are `condDistrib`s, defined almost everywhere under the
middle marginal, so **zero-mass middle atoms never produce a division by zero**: there is no
hand-written conditional-weight formula to fail there. The regressions below run the middle
through a Dirac mass — every other middle point has measure zero — precisely to exercise that
branch.

The middle coordinate is read off the *first* component of the joining; the common-factor
identity (the two middle readings agree almost everywhere) is what makes the
`(2,3)`-projection exact and not merely almost-sure.

## Scope

Everything here is for standard Borel carriers — which includes every finite or countable
discrete carrier, the case the step-approximation route consumes. **This does not by itself
establish the arbitrary-carrier triangle inequality**: that requires, separately, stability of
the reduction under step approximation, which no statement in this file addresses.
-/

open MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω₁ Ω₂ Ω₃ : Type*}
  [MeasurableSpace Ω₁] [StandardBorelSpace Ω₁] [Nonempty Ω₁]
  [MeasurableSpace Ω₂] [StandardBorelSpace Ω₂] [Nonempty Ω₂]
  [MeasurableSpace Ω₃] [StandardBorelSpace Ω₃] [Nonempty Ω₃]
  (π₁₂ : Measure (Ω₁ × Ω₂)) (π₂₃ : Measure (Ω₂ × Ω₃))
  [IsProbabilityMeasure π₁₂] [IsProbabilityMeasure π₂₃]

/-- **The glued coupling**: the relative joining of the two couplings over their common middle
marginal, reordered to the triple product. -/
noncomputable def gluedCoupling : Measure (Ω₁ × Ω₂ × Ω₃) :=
  (relativeFactorCoupling π₁₂ π₂₃ Prod.snd Prod.fst).map fun p => (p.1.1, p.1.2, p.2.2)

variable {π₁₂ π₂₃}

instance : IsProbabilityMeasure (gluedCoupling π₁₂ π₂₃) := by
  rw [gluedCoupling]
  haveI := isProbabilityMeasure_relativeFactorCoupling
    (μ := π₁₂) (ν := π₂₃) (r := (Prod.fst : Ω₂ × Ω₃ → Ω₂)) measurable_snd
  exact Measure.isProbabilityMeasure_map
    ((measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd.snd)).aemeasurable)

/-- **The `(1,2)`-projection is the first coupling.** Exact. -/
theorem gluedCoupling_map_fst_snd :
    (gluedCoupling π₁₂ π₂₃).map (fun w => (w.1, w.2.1)) = π₁₂ := by
  rw [gluedCoupling, Measure.map_map (measurable_fst.prodMk measurable_snd.fst)
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd.snd)),
    show ((fun w : Ω₁ × Ω₂ × Ω₃ => (w.1, w.2.1)) ∘
        fun p : (Ω₁ × Ω₂) × Ω₂ × Ω₃ => (p.1.1, p.1.2, p.2.2)) = Prod.fst from rfl,
    map_fst_relativeFactorCoupling measurable_snd]

/-- **The `(2,3)`-projection is the second coupling.** Exact — the middle is read off the first
component, and the common-factor identity moves it to the second before `map_snd` applies. -/
theorem gluedCoupling_map_snd_trd (h : π₂₃.map Prod.fst = π₁₂.map Prod.snd) :
    (gluedCoupling π₁₂ π₂₃).map (fun w => w.2) = π₂₃ := by
  rw [gluedCoupling, Measure.map_map measurable_snd
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd.snd)),
    show ((fun w : Ω₁ × Ω₂ × Ω₃ => w.2) ∘
        fun p : (Ω₁ × Ω₂) × Ω₂ × Ω₃ => (p.1.1, p.1.2, p.2.2)) =
      fun p : (Ω₁ × Ω₂) × Ω₂ × Ω₃ => (p.1.2, p.2.2) from rfl]
  have hcf := comp_fst_ae_eq_comp_snd_relativeFactorCoupling
    (μ := π₁₂) (ν := π₂₃) measurable_snd measurable_fst h
  rw [Measure.map_congr (g := fun p : (Ω₁ × Ω₂) × Ω₂ × Ω₃ => (p.2.1, p.2.2)) ?_]
  · rw [show (fun p : (Ω₁ × Ω₂) × Ω₂ × Ω₃ => (p.2.1, p.2.2)) = Prod.snd from rfl,
      map_snd_relativeFactorCoupling measurable_fst h]
  · filter_upwards [hcf] with p hp
    exact Prod.ext hp rfl

/-- The first marginal of the `(1,3)`-projection is `μ₁`. Exact. -/
theorem gluedCoupling_map_fst :
    (gluedCoupling π₁₂ π₂₃).map Prod.fst = π₁₂.map Prod.fst := by
  have : (Prod.fst : Ω₁ × Ω₂ × Ω₃ → Ω₁) =
      Prod.fst ∘ fun w : Ω₁ × Ω₂ × Ω₃ => (w.1, w.2.1) := rfl
  rw [this, ← Measure.map_map measurable_fst (measurable_fst.prodMk measurable_snd.fst),
    gluedCoupling_map_fst_snd]

/-- The last marginal of the `(1,3)`-projection is `μ₃`. Exact. -/
theorem gluedCoupling_map_trd (h : π₂₃.map Prod.fst = π₁₂.map Prod.snd) :
    (gluedCoupling π₁₂ π₂₃).map (fun w => w.2.2) = π₂₃.map Prod.snd := by
  have : (fun w : Ω₁ × Ω₂ × Ω₃ => w.2.2) =
      Prod.snd ∘ fun w : Ω₁ × Ω₂ × Ω₃ => w.2 := rfl
  rw [this, ← Measure.map_map measurable_snd measurable_snd,
    gluedCoupling_map_snd_trd h]

/-! ### The induced outer coupling -/

/-- **The induced coupling of the outer marginals**: forget the shared middle coordinate in the
glued triple law. -/
noncomputable def gluedOuterCoupling (π₁₂ : Measure (Ω₁ × Ω₂))
    (π₂₃ : Measure (Ω₂ × Ω₃)) [IsProbabilityMeasure π₁₂] [IsProbabilityMeasure π₂₃] :
    Measure (Ω₁ × Ω₃) :=
  (gluedCoupling π₁₂ π₂₃).map fun w => (w.1, w.2.2)

instance : IsProbabilityMeasure (gluedOuterCoupling π₁₂ π₂₃) := by
  rw [gluedOuterCoupling]
  exact Measure.isProbabilityMeasure_map (measurable_fst.prodMk measurable_snd.snd).aemeasurable

/-- The first marginal of the induced outer coupling is the first marginal of `π₁₂`. Exact. -/
theorem gluedOuterCoupling_map_fst :
    (gluedOuterCoupling π₁₂ π₂₃).map Prod.fst = π₁₂.map Prod.fst := by
  rw [gluedOuterCoupling, Measure.map_map measurable_fst
    (measurable_fst.prodMk measurable_snd.snd)]
  exact gluedCoupling_map_fst

/-- The second marginal of the induced outer coupling is the second marginal of `π₂₃`. Exact. -/
theorem gluedOuterCoupling_map_snd (h : π₂₃.map Prod.fst = π₁₂.map Prod.snd) :
    (gluedOuterCoupling π₁₂ π₂₃).map Prod.snd = π₂₃.map Prod.snd := by
  rw [gluedOuterCoupling, Measure.map_map measurable_snd
    (measurable_fst.prodMk measurable_snd.snd)]
  exact gluedCoupling_map_trd h

/-! ### Zero-mass middle-atom regressions

The middle marginal is a Dirac mass, so every other middle point is a zero-mass atom; the
projections hold regardless, because the construction never divides by a middle weight. -/

example (x z : Bool) :
    (gluedCoupling ((Measure.dirac x).prod (Measure.dirac true))
        ((Measure.dirac true).prod (Measure.dirac z))).map (fun w => (w.1, w.2.1)) =
      (Measure.dirac x).prod (Measure.dirac true) :=
  gluedCoupling_map_fst_snd

example (x z : Bool) :
    (gluedCoupling ((Measure.dirac x).prod (Measure.dirac true))
        ((Measure.dirac true).prod (Measure.dirac z))).map (fun w => w.2) =
      (Measure.dirac true).prod (Measure.dirac z) :=
  gluedCoupling_map_snd_trd (by simp)

end MeasureTheory
