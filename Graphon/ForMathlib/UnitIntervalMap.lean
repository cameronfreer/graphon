/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Kernel.Representation

/-!
# Measure-preserving maps from the unit interval

Mathlib's kernel representation theorem already gives the exact measurable map needed in
Janson's Theorem A.9: every probability measure on a standard Borel space is the pushforward of
Lebesgue measure on `I = [0,1]`.  This file supplies the missing `MeasurePreserving` packaging.

No atomlessness hypothesis is present.  The private regression examples at the end instantiate
the theorem for a Dirac law, a finite atomic Bernoulli law, and a mixed atomic--continuous law.
-/

open MeasureTheory unitInterval

namespace MeasureTheory.Measure

/-- **Janson A.9, packaged for Mathlib**: every standard Borel probability space receives a
measure-preserving map from the unit interval.  This is a prescribed-pushforward statement; no
pointwise surjectivity is claimed or needed.  Atoms are allowed. -/
theorem exists_measurePreserving_from_unitInterval {Y : Type*} [Nonempty Y]
    {mY : MeasurableSpace Y} [StandardBorelSpace Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] :
    ∃ f : I → Y, MeasurePreserving f (volume : Measure I) μ := by
  obtain ⟨f, hf, hmap⟩ := μ.exists_measurable_map_eq
  exact ⟨f, hf, hmap⟩

/-! The following examples are compile-time regressions for the absence of an atomlessness
hypothesis.  They are deliberately private: the public theorem above is the API. -/

private example (x : I) :
    ∃ f : I → I, MeasurePreserving f (volume : Measure I) (Measure.dirac x) :=
  (Measure.dirac x).exists_measurePreserving_from_unitInterval

private example (p : I) :
    ∃ f : I → Bool,
      MeasurePreserving f (volume : Measure I) (ProbabilityTheory.bernoulliMeasure false true p) :=
  (ProbabilityTheory.bernoulliMeasure false true p).exists_measurePreserving_from_unitInterval

private example (p : I) :
    let source := (ProbabilityTheory.bernoulliMeasure false true p).prod (volume : Measure I)
    let mixed := source.map (fun bx : Bool × I => if bx.1 then 0 else (bx.2 : ℝ))
    ∃ f : I → ℝ, MeasurePreserving f (volume : Measure I) mixed := by
  dsimp only
  letI : IsProbabilityMeasure
      ((ProbabilityTheory.bernoulliMeasure false true p).prod (volume : Measure I)) :=
    inferInstance
  have hmeas : Measurable (fun bx : Bool × I => if bx.1 then 0 else (bx.2 : ℝ)) := by
    exact Measurable.ite (measurable_fst (measurableSet_singleton true)) measurable_const
      (measurable_subtype_coe.comp measurable_snd)
  letI : IsProbabilityMeasure
      (((ProbabilityTheory.bernoulliMeasure false true p).prod (volume : Measure I)).map
        (fun bx : Bool × I => if bx.1 then 0 else (bx.2 : ℝ))) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  exact Measure.exists_measurePreserving_from_unitInterval _

end MeasureTheory.Measure
