/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Change of variables in the source of a composition-product

Pulling a kernel back along a measurable map in its source, and pushing the resulting
composition-product forward by that same map, is the same as moving the map onto the measure:

`(μ ⊗ₘ κ.comap e he).map (Prod.map e id) = μ.map e ⊗ₘ κ`

with the composition-level corollary `(κ.comap e he) ∘ₘ μ = κ ∘ₘ μ.map e` obtained by taking the
second marginal.

Mathlib has `Kernel.comap` and `Measure.compProd` but not their interaction. The statement is
proved on measurable rectangles, where both sides are the same integral after a change of
variables.

## `e` need only be measurable

An earlier private version of the first identity in `Graphon.RelStepKernel` asked for a measurable
*equivalence*. Nothing in the argument uses an inverse: the preimage step is definitional for
`Prod.map e id`, and `setLIntegral_map` needs only measurability. Consumers that want to *cancel*
the pushforward — to conclude equality of the arguments rather than of the images — need
`MeasurableEmbedding e`, but that is their hypothesis to carry, not this one's; surjectivity is
never used on either side.
-/

open MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- **Change of variables for `⊗ₘ` in the source.** Pushing `μ ⊗ₘ κ.comap e` forward by
`e × id` is `μ.map e ⊗ₘ κ`. -/
theorem Measure.map_prodMap_compProd_comap (μ : Measure α) [IsFiniteMeasure μ] {e : α → β}
    (he : Measurable e) (κ : Kernel β γ) [IsFiniteKernel κ] :
    (μ ⊗ₘ κ.comap e he).map (Prod.map e id) = μ.map e ⊗ₘ κ := by
  haveI : IsFiniteMeasure (μ.map e) := Measure.isFiniteMeasure_map _ _
  refine Measure.ext_prod fun {s t} hs ht => ?_
  have hpre : (Prod.map e id) ⁻¹' (s ×ˢ t) = (e ⁻¹' s) ×ˢ t := rfl
  rw [Measure.map_apply (he.prodMap measurable_id) (hs.prod ht), hpre,
    Measure.compProd_apply_prod (he hs) ht, Measure.compProd_apply_prod hs ht,
    setLIntegral_map hs (Kernel.measurable_coe κ ht) he]
  rfl

/-- **Change of variables for `∘ₘ` in the source**, the second marginal of
`Measure.map_prodMap_compProd_comap`. -/
theorem Measure.comp_comap (μ : Measure α) [IsFiniteMeasure μ] {e : α → β} (he : Measurable e)
    (κ : Kernel β γ) [IsFiniteKernel κ] :
    (κ.comap e he) ∘ₘ μ = κ ∘ₘ (μ.map e) := by
  haveI : IsFiniteMeasure (μ.map e) := Measure.isFiniteMeasure_map _ _
  have hsnd := congrArg Measure.snd (Measure.map_prodMap_compProd_comap μ he κ)
  rwa [Measure.snd, Measure.snd, Measure.map_map measurable_snd (he.prodMap measurable_id),
    show (Prod.snd ∘ Prod.map e (id : γ → γ)) = Prod.snd from rfl,
    ← Measure.snd, ← Measure.snd, Measure.snd_compProd, Measure.snd_compProd] at hsnd

end MeasureTheory
