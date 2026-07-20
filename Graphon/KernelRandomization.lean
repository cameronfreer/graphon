/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.Kernel.Representation
import Graphon.SamplerSources

/-!
# Kernel randomization from the uniform source on `[0,1]` (R4 converse piece 1, #107)

The small adapter from Mathlib's kernel representation theorem
(`ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval`, Kallenberg Lemma 4.22) to
the project's uniform source `uniform01 : Measure ℝ`: any Markov kernel into a standard
Borel space is the pushforward of `uniform01` by a jointly measurable deterministic map, and
any probability measure on a standard Borel space is a pushforward of `uniform01`. Outside
`[0,1]` the map factors through `Set.projIcc` — only measurability and agreement on the
support matter.

* `ProbabilityTheory.Kernel.exists_measurable_map_eq_uniform01` — the kernel form;
* `MeasureTheory.Measure.exists_measurable_map_eq_uniform01` — the single-measure corollary.

This is the randomization ("noise outsourcing") input for the converse representation
theorem: each regular conditional distribution along the factor filtration is to be realized
as a measurable function of the lower factors and one fresh uniform.
-/

open Set unitInterval Function

namespace MeasureTheory

/-- `uniform01` is the pushforward of the uniform measure on the subtype `I = [0,1]` along
the inclusion. -/
theorem uniform01_eq_map_volume_coe :
    uniform01 = (volume : Measure I).map ((↑) : I → ℝ) :=
  unitInterval.measurePreserving_coe.map_eq.symm

/-- Projecting `uniform01` back onto the subtype recovers the uniform measure on `I` —
`Set.projIcc` retracts the inclusion, and `uniform01` is supported on `[0,1]`. -/
theorem uniform01_map_projIcc :
    uniform01.map (projIcc (0 : ℝ) 1 zero_le_one) = (volume : Measure I) := by
  rw [uniform01_eq_map_volume_coe,
    Measure.map_map continuous_projIcc.measurable measurable_subtype_coe,
    show projIcc (0 : ℝ) 1 zero_le_one ∘ ((↑) : I → ℝ) = id from
      funext fun x => projIcc_val zero_le_one x,
    Measure.map_id]

end MeasureTheory

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {X Y : Type*} {mX : MeasurableSpace X} [Nonempty Y] {mY : MeasurableSpace Y}
    [StandardBorelSpace Y]

/-- **Kernel randomization from `uniform01`**: a Markov kernel into a standard Borel space
is the pushforward of the project's uniform source by a jointly measurable deterministic
map — Mathlib's `exists_measurable_map_eq_unitInterval` (Kallenberg Lemma 4.22) with the
`[0,1]`-subtype input adapted to `ℝ` through `Set.projIcc`. -/
theorem exists_measurable_map_eq_uniform01 (κ : Kernel X Y) [IsMarkovKernel κ] :
    ∃ f : X → ℝ → Y, Measurable (uncurry f) ∧ ∀ x, uniform01.map (f x) = κ x := by
  obtain ⟨f₀, hf₀, hf₀κ⟩ := κ.exists_measurable_map_eq_unitInterval
  refine ⟨fun x r => f₀ x (projIcc (0 : ℝ) 1 zero_le_one r), ?_, fun x => ?_⟩
  · have hproj : Measurable (projIcc (0 : ℝ) 1 zero_le_one) := continuous_projIcc.measurable
    exact hf₀.comp (measurable_fst.prodMk (hproj.comp measurable_snd))
  · show uniform01.map (f₀ x ∘ projIcc (0 : ℝ) 1 zero_le_one) = κ x
    rw [← Measure.map_map hf₀.of_uncurry_left continuous_projIcc.measurable,
      uniform01_map_projIcc, hf₀κ x]

end ProbabilityTheory.Kernel

/-- **Measure randomization from `uniform01`**: a probability measure on a standard Borel
space is a pushforward of the project's uniform source by a measurable map. -/
theorem MeasureTheory.Measure.exists_measurable_map_eq_uniform01 {Y : Type*} [Nonempty Y]
    {mY : MeasurableSpace Y} [StandardBorelSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ] :
    ∃ f : ℝ → Y, Measurable f ∧ uniform01.map f = μ := by
  obtain ⟨f, hf, hfμ⟩ := (ProbabilityTheory.Kernel.const Unit μ).exists_measurable_map_eq_uniform01
  exact ⟨f (), hf.of_uncurry_left, by simpa using hfμ ()⟩
