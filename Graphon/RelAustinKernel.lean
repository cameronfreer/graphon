/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelAustinEnriched
import Graphon.RelStepKernel

/-!
# The enriched kernel layer: unit 3 (R4 converse, #107, #197)

Route **A** (Austin) only. No Kallenberg machinery, and nothing here asserts that the two routes'
outputs agree.

The conditional kernels of the base-extended object: the whole rank-`n` layer given the enriched
lower factor, and the exact-anchor layer at each rank-`n` support given the enriched boundary.

**Which identities are exact and which are almost everywhere.** The defining disintegrations and
marginal recoveries are *exact* measure equalities — `condDistrib` is characterized by them.
Comparisons between different versions of a conditional kernel are almost everywhere, and each such
statement names the measure it holds under. The two are not interchangeable and the distinction is
kept visible throughout.

`enrichedStepKernel` is **not** `stepKernel`: their conditioning spaces differ, and the Austin base
genuinely refines the conditioning. What does hold is that forgetting the base from the enriched
disintegration returns the ordinary joint law exactly.

## Scope

For an arbitrary coherent basis, under ambient countability only — no selected basis and no
`Fintype S.Srt`. Rank zero is not handled here; it takes the existing rank-one route, and nothing
in this module manufactures an `A = ∅` realization theorem.

Contains no randomization map, uniforms, source splitting, fresh rank-`n` latent layer,
`RankSuccessor`, or Kallenberg machinery: those belong to the assembly unit.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

namespace InfiniteRelExchangeableLaw

variable {S : RelSignature} [Countable S.Srt] [Countable S.Rel]
  {M : InfiniteRelExchangeableLaw S} {n : ℕ} {C : M.RankRepresentation n}

/-! ### Measurability of the adapter maps -/

omit [Countable S.Srt] [Countable S.Rel] in
theorem measurable_enrichedBoundaryMap (B : CoherentBasis M) (m : ℕ)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measurable (enrichedBoundaryMap B m A) :=
  ((B.measurable_boundaryMap A).comp measurable_fst).prodMk measurable_snd

omit [Countable S.Srt] [Countable S.Rel] in
theorem measurable_enrichedExactMap (B : CoherentBasis M) (m : ℕ)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measurable (enrichedExactMap B m A) :=
  (B.measurable_exactMap A).comp measurable_fst

/-! ### The named laws -/

/-- The law of the enriched lower factor. -/
noncomputable def enrichedLowerLaw (O : AustinEnrichedObject C) (B : CoherentBasis M) :
    Measure (EnrichedLowerSpace B n) :=
  O.law.map (enrichedLowerMap B n)

/-- The law of the enriched boundary at `A`. -/
noncomputable def enrichedBoundaryLaw (O : AustinEnrichedObject C) (B : CoherentBasis M)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measure (EnrichedBoundarySpace B n A) :=
  O.law.map (enrichedBoundaryMap B n A)

instance (O : AustinEnrichedObject C) (B : CoherentBasis M) :
    IsProbabilityMeasure (enrichedLowerLaw O B) := by
  haveI := O.isProbabilityMeasure_law
  rw [enrichedLowerLaw]
  exact Measure.isProbabilityMeasure_map (measurable_enrichedLowerMap B n).aemeasurable

instance (O : AustinEnrichedObject C) (B : CoherentBasis M)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    IsProbabilityMeasure (enrichedBoundaryLaw O B A) := by
  haveI := O.isProbabilityMeasure_law
  rw [enrichedBoundaryLaw]
  exact Measure.isProbabilityMeasure_map (measurable_enrichedBoundaryMap B n A).aemeasurable

/-! ### The kernels -/

/-- **The layer kernel**: the whole rank-`n` layer given the enriched lower factor. -/
noncomputable def enrichedLayerKernel (O : AustinEnrichedObject C) (B : CoherentBasis M) :
    Kernel (EnrichedLowerSpace B n) (B.RankLayerSpace n) :=
  haveI := O.isProbabilityMeasure_law
  condDistrib (enrichedLayerMap B n) (enrichedLowerMap B n) O.law

/-- **The enriched step kernel at `A`**: the exact-anchor layer given the enriched boundary. Not
`stepKernel` — the conditioning space is larger, and the Austin base genuinely refines it. -/
noncomputable def enrichedStepKernel (O : AustinEnrichedObject C) (B : CoherentBasis M)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Kernel (EnrichedBoundarySpace B n A) (B.ExactSpace A) :=
  haveI := O.isProbabilityMeasure_law
  condDistrib (enrichedExactMap B n A) (enrichedBoundaryMap B n A) O.law

instance (O : AustinEnrichedObject C) (B : CoherentBasis M) :
    IsMarkovKernel (enrichedLayerKernel O B) := by
  haveI := O.isProbabilityMeasure_law
  rw [enrichedLayerKernel]
  infer_instance

instance (O : AustinEnrichedObject C) (B : CoherentBasis M)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    IsMarkovKernel (enrichedStepKernel O B A) := by
  haveI := O.isProbabilityMeasure_law
  rw [enrichedStepKernel]
  infer_instance

/-! ### The exact disintegrations

These are **exact** measure equalities, not almost-everywhere statements: `condDistrib` is
characterized by them. -/

/-- **Disintegration of the layer.** -/
theorem compProd_enrichedLayerKernel (O : AustinEnrichedObject C) (B : CoherentBasis M) :
    enrichedLowerLaw O B ⊗ₘ enrichedLayerKernel O B =
      O.law.map fun p => (enrichedLowerMap B n p, enrichedLayerMap B n p) := by
  haveI := O.isProbabilityMeasure_law
  rw [enrichedLowerLaw, enrichedLayerKernel]
  exact compProd_map_condDistrib (measurable_enrichedLayerMap B n).aemeasurable

/-- **Disintegration at a support.** -/
theorem compProd_enrichedStepKernel (O : AustinEnrichedObject C) (B : CoherentBasis M)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    enrichedBoundaryLaw O B A ⊗ₘ enrichedStepKernel O B A =
      O.law.map fun p => (enrichedBoundaryMap B n A p, enrichedExactMap B n A p) := by
  haveI := O.isProbabilityMeasure_law
  rw [enrichedBoundaryLaw, enrichedStepKernel]
  exact compProd_map_condDistrib (measurable_enrichedExactMap B n A).aemeasurable

/-- **Marginal recovery for the layer.** -/
theorem enrichedLayerKernel_comp_enrichedLowerLaw (O : AustinEnrichedObject C)
    (B : CoherentBasis M) :
    enrichedLayerKernel O B ∘ₘ enrichedLowerLaw O B = O.law.map (enrichedLayerMap B n) := by
  haveI := O.isProbabilityMeasure_law
  rw [enrichedLowerLaw, enrichedLayerKernel]
  exact condDistrib_comp_map (measurable_enrichedLowerMap B n).aemeasurable
    (measurable_enrichedLayerMap B n).aemeasurable

/-- **Marginal recovery at a support.** -/
theorem enrichedStepKernel_comp_enrichedBoundaryLaw (O : AustinEnrichedObject C)
    (B : CoherentBasis M) (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    enrichedStepKernel O B A ∘ₘ enrichedBoundaryLaw O B A =
      O.law.map (enrichedExactMap B n A) := by
  haveI := O.isProbabilityMeasure_law
  rw [enrichedBoundaryLaw, enrichedStepKernel]
  exact condDistrib_comp_map (measurable_enrichedBoundaryMap B n A).aemeasurable
    (measurable_enrichedExactMap B n A).aemeasurable

end InfiniteRelExchangeableLaw

end RelSignature
