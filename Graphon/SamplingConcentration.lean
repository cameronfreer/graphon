/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.SamplingICL

/-!
# Concentration scaffold for the First Sampling Lemma

The First Sampling Lemma (`first_sampling_lemma`, **proved 2026-07-08** in
`Graphon/SamplingLemma.lean`) was the sampling route's one analytic sorry. This file
decomposes it along the classical two-stage analysis: all statements here are proved
or packaged as hypotheses of a proved reduction.

**The two-stage decomposition** (Lovász, *Large Networks and Graph Limits*, §10.5–10.6):
condition on the sampled points `x : Fin k → α`, and interpolate through the *weighted*
sampled graphon `H_{W,x} := sampleWeightedGraphonOn W x` (matrix entries `W(xᵢ, xⱼ)` on
the equal-measure `k`-partition):

1. **Point sampling** (`PointSamplingEvent`): with probability `≥ 1 − η₁` over `x`,
   `d_□(W, H_{W,x}) < ε/2` — the genuinely analytic step (Lemma 10.11 / Azuma).
2. **Rounding** (`RoundingEvent`): conditionally on (a.e.) `x`, the Bernoulli edge
   rounding `G` of `H_{W,x}` satisfies `d_□(H_{W,x}, K_G) < ε/2` with conditional
   probability `≥ 1 − η₂` — a finite union bound over cuts.

`sampleGoodMassOn_of_events` (PROVED) recombines the two stages into the good-mass
bound demanded by `first_sampling_lemma`; the deterministic triangle route
`cutDistance_ofSimpleGraphOn_le` is the gluing inequality. Both events were established
with `W`-uniform `k` (`point_sampling_event_of_large_k`, `rounding_event_of_large_k`),
completing `first_sampling_lemma` (2026-07-08, `Graphon/SamplingLemma.lean`).

## Main declarations

* `Graphon.sampleMassAt` — the conditional edge distribution at fixed sampled points,
  with `sampleMass W G = ∫ x, sampleMassAt W x G`
* `Graphon.sampleWeightedGraphonOn` — the weighted sampled step graphon `H_{W,x}`
* `Graphon.cutDistance_ofSimpleGraphOn_le` — the deterministic triangle route
* `Graphon.PointSamplingEvent`, `Graphon.RoundingEvent` — the two concentration events
* `Graphon.sampleGoodMassOn_of_events` — the PROVED reduction: both events ⟹ the
  good-mass bound of `first_sampling_lemma`
-/

open MeasureTheory Set Filter Finset

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

variable [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

section ConditionalDistribution

open scoped Classical

variable {k : ℕ}

/-- **The conditional edge distribution**: the probability that the sampled graph equals
`G`, conditioned on the sampled points being `x`. (Definitionally the integrand of
`sampleMass`.) -/
noncomputable def sampleMassAt (W : Graphon α μ) (x : Fin k → α)
    (G : SimpleGraph (Fin k)) : ℝ :=
  sampleIntegrand W G x

omit [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ] in
/-- The unconditional mass integrates the conditional one over the sampled points. -/
theorem sampleMass_eq_integral_sampleMassAt (W : Graphon α μ) (G : SimpleGraph (Fin k)) :
    sampleMass W G = ∫ x : Fin k → α, sampleMassAt W x G ∂Measure.pi (fun _ ↦ μ) := rfl

omit [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ] in
/-- The conditional masses form a probability distribution at every point. -/
theorem sampleMassAt_sum_eq_one (W : Graphon α μ) (x : Fin k → α) :
    ∑ G : SimpleGraph (Fin k), sampleMassAt W x G = 1 :=
  sum_sampleIntegrand_eq_one W x

omit [StandardBorelSpace α] [NoAtoms μ] in
/-- The conditional masses are nonnegative for a.e. sampled points. -/
theorem sampleMassAt_nonneg_ae (W : Graphon α μ) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin k ↦ μ),
      ∀ G : SimpleGraph (Fin k), 0 ≤ sampleMassAt W x G := by
  filter_upwards [ae_top_edges_mem_Icc (k := k) W] with x hx G
  refine mul_nonneg (Finset.prod_nonneg fun e he ↦ ?_)
    (Finset.prod_nonneg fun e he ↦ ?_)
  · exact (hx e (SimpleGraph.edgeFinset_mono le_top he)).1
  · have := (hx e (Finset.sdiff_subset he)).2
    linarith

end ConditionalDistribution

section WeightedSample

open scoped Classical

variable {k : ℕ} [NeZero k]

/-- **The weighted sampled step graphon** `H_{W,x}`: on the chosen equal-measure
`k`-partition (the same `equipartition k` used by `ofSimpleGraphOn`), the cell `(i, j)`
carries the entry `W(xᵢ, xⱼ)` — clamped into `[0,1]` and evaluated at the
`(min, max)`-ordered pair, so the coefficients are pointwise symmetric and bounded (the
clamp and the ordering are invisible a.e. in `x` since `W` is a.e. `[0,1]`-valued and
a.e. symmetric). -/
noncomputable def sampleWeightedGraphonOn (W : Graphon α μ) (x : Fin k → α) :
    Graphon α μ :=
  mkStepGraphon (equipartition k)
    (fun S T ↦
      if hST : (∃ i, equipartitionCell (α := α) (μ := μ) k i = S) ∧
          (∃ j, equipartitionCell (α := α) (μ := μ) k j = T)
      then min 1 (max 0 (W.toAEEqFun
        (x (min hST.1.choose hST.2.choose), x (max hST.1.choose hST.2.choose))))
      else 0)
    (fun S _ T _ ↦ by
      by_cases h1 : (∃ i, equipartitionCell (α := α) (μ := μ) k i = S) ∧
          (∃ j, equipartitionCell (α := α) (μ := μ) k j = T)
      · rw [dif_pos h1, dif_pos ⟨h1.2, h1.1⟩]
        rw [min_comm h1.2.choose h1.1.choose, max_comm h1.2.choose h1.1.choose]
      · rw [dif_neg h1, dif_neg (fun hc ↦ h1 ⟨hc.2, hc.1⟩)])
    (fun S _ T _ ↦ by
      by_cases h1 : (∃ i, equipartitionCell (α := α) (μ := μ) k i = S) ∧
          (∃ j, equipartitionCell (α := α) (μ := μ) k j = T)
      · rw [dif_pos h1]
        exact ⟨le_min zero_le_one (le_max_left 0 _), min_le_left 1 _⟩
      · rw [dif_neg h1]
        exact ⟨le_refl 0, zero_le_one⟩)

/-- **The deterministic triangle route**: closeness of `W` to the weighted sample and of
the weighted sample to the rounded graph combine into goodness of the sampled graph. -/
theorem cutDistance_ofSimpleGraphOn_le (W : Graphon α μ) (x : Fin k → α)
    (G : SimpleGraph (Fin k)) :
    cutDistance W (ofSimpleGraphOn G) ≤
      cutDistance W (sampleWeightedGraphonOn W x) +
        cutDistance (sampleWeightedGraphonOn W x) (ofSimpleGraphOn G) :=
  cutDistance_triangle _ _ _

/-- **Stage 1 — point-sampling concentration** (event form): with probability `≥ 1 − η`
over the sampled points, the weighted sampled graphon is `ε`-close to `W`. The
measurable witness set is part of the data (measurability of `x ↦ d_□(W, H_{W,x})` is
not needed anywhere). This is the genuinely analytic content of the First Sampling
Lemma (Lovász Lemma 10.11 / Azuma–Hoeffding). -/
def PointSamplingEvent (W : Graphon α μ) (k : ℕ) [NeZero k] (ε η : ℝ) : Prop :=
  ∃ X : Set (Fin k → α), MeasurableSet X ∧
    1 - η ≤ ((Measure.pi fun _ : Fin k ↦ μ) X).toReal ∧
    ∀ x ∈ X, cutDistance W (sampleWeightedGraphonOn W x) < ε

/-- **Stage 2 — rounding concentration** (event form): for a.e. sampled points, the
Bernoulli edge rounding lands `ε`-close to the weighted sampled graphon with conditional
probability `≥ 1 − η`. A finite union bound over cuts (proved:
`rounding_event_of_large_k`, `Graphon/SamplingRounding.lean`; the a.e. qualifier
absorbs the pointwise pathologies of the `L⁰` representative). -/
def RoundingEvent (W : Graphon α μ) (k : ℕ) [NeZero k] (ε η : ℝ) : Prop :=
  ∀ᵐ x ∂Measure.pi (fun _ : Fin k ↦ μ),
    1 - η ≤ ∑ G ∈ Finset.univ.filter
      (fun G : SimpleGraph (Fin k) ↦
        cutDistance (sampleWeightedGraphonOn W x) (ofSimpleGraphOn G) < ε),
      sampleMassAt W x G

/-- **The recombination** (PROVED): the two concentration events at accuracy `ε/2` yield
the good-mass bound demanded by `first_sampling_lemma` at accuracy `ε`. Both events were
subsequently established with `W`-uniform `k` (`point_sampling_event_of_large_k`,
`rounding_event_of_large_k`), completing the First Sampling Lemma — no new independent
assumption is introduced anywhere in the chain. -/
theorem sampleGoodMassOn_of_events (W : Graphon α μ) (k : ℕ) [NeZero k] (ε η₁ η₂ : ℝ)
    (hη₂ : 0 ≤ η₂)
    (hpt : PointSamplingEvent W k (ε / 2) η₁)
    (hrd : RoundingEvent W k (ε / 2) η₂) :
    1 - η₁ - η₂ ≤ sampleGoodMassOn W k ε := by
  classical
  obtain ⟨X, hX_meas, hX_mass, hX_good⟩ := hpt
  set GoodSet : Finset (SimpleGraph (Fin k)) :=
    Finset.univ.filter (fun G ↦ cutDistance W (ofSimpleGraphOn G) < ε) with hGoodSet
  -- The good mass as an integral of the conditional good mass.
  have hgood_int : sampleGoodMassOn W k ε =
      ∫ x : Fin k → α, ∑ G ∈ GoodSet, sampleMassAt W x G ∂Measure.pi (fun _ ↦ μ) := by
    rw [show sampleGoodMassOn W k ε = ∑ G ∈ GoodSet, sampleMass W G from by
      rw [hGoodSet, Finset.sum_filter]; rfl]
    exact (integral_finsetSum _ fun G _ ↦ sampleIntegrand_integrable W G).symm
  -- The a.e. pointwise lower bound by the indicator of the point-sampling event.
  have hbound : ∀ᵐ x ∂Measure.pi (fun _ : Fin k ↦ μ),
      X.indicator (fun _ ↦ (1 - η₂ : ℝ)) x ≤ ∑ G ∈ GoodSet, sampleMassAt W x G := by
    filter_upwards [hrd, sampleMassAt_nonneg_ae (k := k) W] with x hrd_x hnn
    by_cases hxX : x ∈ X
    · rw [Set.indicator_of_mem hxX]
      refine le_trans hrd_x (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun G hG _ ↦ hnn G)
      intro G hG
      rw [Finset.mem_filter] at hG ⊢
      refine ⟨Finset.mem_univ G, ?_⟩
      calc cutDistance W (ofSimpleGraphOn G)
          ≤ cutDistance W (sampleWeightedGraphonOn W x) +
              cutDistance (sampleWeightedGraphonOn W x) (ofSimpleGraphOn G) :=
            cutDistance_ofSimpleGraphOn_le W x G
        _ < ε / 2 + ε / 2 := add_lt_add (hX_good x hxX) hG.2
        _ = ε := by ring
    · rw [Set.indicator_of_notMem hxX]
      exact Finset.sum_nonneg fun G _ ↦ hnn G
  -- Integrate the bound.
  have hint : ∫ x : Fin k → α, X.indicator (fun _ ↦ (1 - η₂ : ℝ)) x
        ∂Measure.pi (fun _ ↦ μ) ≤
      ∫ x : Fin k → α, ∑ G ∈ GoodSet, sampleMassAt W x G ∂Measure.pi (fun _ ↦ μ) := by
    refine integral_mono_ae ?_ ?_ hbound
    · exact (integrable_const _).indicator hX_meas
    · exact integrable_finsetSum _ fun G _ ↦ sampleIntegrand_integrable W G
  have hind : ∫ x : Fin k → α, X.indicator (fun _ ↦ (1 - η₂ : ℝ)) x
        ∂Measure.pi (fun _ ↦ μ) =
      (1 - η₂) * ((Measure.pi fun _ : Fin k ↦ μ) X).toReal := by
    rw [integral_indicator_const _ hX_meas, smul_eq_mul, mul_comm]; rfl
  have hmuX_le : ((Measure.pi fun _ : Fin k ↦ μ) X).toReal ≤ 1 := by
    have : (Measure.pi fun _ : Fin k ↦ μ) X ≤ 1 := le_trans (measure_mono (Set.subset_univ X))
      (le_of_eq (measure_univ))
    exact le_trans (ENNReal.toReal_mono ENNReal.one_ne_top this) (by simp)
  calc 1 - η₁ - η₂
      ≤ (1 - η₂) * ((Measure.pi fun _ : Fin k ↦ μ) X).toReal := by nlinarith [hX_mass]
    _ = ∫ x : Fin k → α, X.indicator (fun _ ↦ (1 - η₂ : ℝ)) x
          ∂Measure.pi (fun _ ↦ μ) := hind.symm
    _ ≤ ∫ x : Fin k → α, ∑ G ∈ GoodSet, sampleMassAt W x G ∂Measure.pi (fun _ ↦ μ) :=
        hint
    _ = sampleGoodMassOn W k ε := hgood_int.symm

end WeightedSample

end Graphon
