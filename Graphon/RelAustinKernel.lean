/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelAustinEnriched
import Graphon.RelStepKernel
import Graphon.ForMathlib.CondExpRepresentable

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

**Base redundancy** (`AustinEnrichedObject.exists_comap_snd_ae_eq_of_enrichedLowerMap`): every
enriched-lower-factor event is, modulo the enriched law, a base event. This is what the
representation's below-rank fixing completeness buys the enriched layer. It is strictly a
below-rank statement: an exact-layer event at a support of cardinality `n` is not represented
through the block and the base by anything here.

## Scope

For an arbitrary coherent basis, under ambient countability only, with no basis selected here.
Rank zero is not handled here; it takes the existing rank-one route, and nothing
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

/-! ### Base redundancy

**Every enriched-lower-factor event is, modulo the enriched law, a base event.** This is the
consequence of below-rank fixing completeness the enriched layer consumes: the lower factor reads
only fixing events at supports of cardinality `< n`, each of which has a local latent
representative under `C.P` (`lower_fixing_complete`), and the original latents are recovered from
the base by `map_original`. Representability is closed under joins, so the base half of the
enriched lower factor comes for free.

This is a statement **strictly below rank `n`**. An exact-layer event at a support of cardinality
`n` lies in the fixing algebra at that support, and nothing here represents it through the block
and the base — that remains the exact-rank content of the route. -/

/-- A fixing event below rank `n`, pulled back to the enriched space, has a base representative. -/
private theorem exists_comap_snd_ae_eq_of_fixingAlgebra (O : AustinEnrichedObject C)
    {A : Finset (Σ s : S.Srt, Vinfinite S s)} (hA : A.card < n)
    {E : Set (RelStructure S (Vinfinite S))} (hE : MeasurableSet[RelStructure.fixingAlgebra A] E) :
    ∃ E', MeasurableSet[MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × AustinBaseSpace S n → _) inferInstance] E' ∧
      Prod.fst ⁻¹' E =ᵐ[O.law] E' := by
  haveI := O.isProbabilityMeasure_law
  haveI := C.isProbabilityMeasure_P
  obtain ⟨E', ⟨U, hU, rfl⟩, hE'⟩ := C.lower_fixing_complete A hA E hE
  have hψ : Measure.QuasiMeasurePreserving
      (fun p : RelStructure S (Vinfinite S) × AustinBaseSpace S n =>
        (p.1, restrictOriginalLatents S n p.2.1)) O.law C.P :=
    ⟨measurable_fst.prodMk ((measurable_restrictOriginalLatents n).comp measurable_snd.fst),
      O.map_original ▸ Measure.AbsolutelyContinuous.rfl⟩
  refine ⟨Prod.snd ⁻¹' ((localLatents A n ∘ restrictOriginalLatents S n ∘ Prod.fst) ⁻¹' U),
    ⟨_, ((measurable_localLatents A n).comp
      ((measurable_restrictOriginalLatents n).comp measurable_fst)) hU, rfl⟩, ?_⟩
  exact hψ.preimage_ae_eq hE'

/-- **Base redundancy**: every event measurable for the enriched lower factor agrees, modulo the
enriched law, with an event measurable for the base alone. -/
theorem AustinEnrichedObject.exists_comap_snd_ae_eq_of_enrichedLowerMap
    (O : AustinEnrichedObject C) (B : CoherentBasis M)
    {E : Set (RelStructure S (Vinfinite S) × AustinBaseSpace S n)}
    (hE : MeasurableSet[MeasurableSpace.comap (enrichedLowerMap B n) inferInstance] E) :
    ∃ E', MeasurableSet[MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × AustinBaseSpace S n → _) inferInstance] E' ∧
      E =ᵐ[O.law] E' := by
  haveI := O.isProbabilityMeasure_law
  have hsplit : MeasurableSpace.comap (enrichedLowerMap B n) inferInstance =
      MeasurableSpace.comap (B.lowerFactorMap n ∘ Prod.fst) inferInstance ⊔
        MeasurableSpace.comap
          (Prod.snd : RelStructure S (Vinfinite S) × AustinBaseSpace S n → _) inferInstance :=
    MeasurableSpace.comap_prodMk (B.lowerFactorMap n ∘ Prod.fst) Prod.snd
  rw [hsplit] at hE
  refine eventuallyMeasurableSet_sup (fun s hs => ?_) hE
  -- the lower factor reads only fixing events below rank `n`
  have hle : MeasurableSpace.comap (B.lowerFactorMap n ∘ Prod.fst) inferInstance ≤
      eventuallyMeasurableSpace (MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × AustinBaseSpace S n → _) inferInstance)
        (ae O.law) := by
    rw [← MeasurableSpace.comap_comp]
    refine (MeasurableSpace.comap_mono (B.comap_lowerFactorMap_le n)).trans ?_
    rw [RelStructure.lowerRankAlgebra, MeasurableSpace.comap_iSup]
    refine iSup_le fun A => ?_
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun hA => ?_
    rintro _ ⟨E₀, hE₀, rfl⟩
    obtain ⟨E', hE'meas, hE'⟩ := exists_comap_snd_ae_eq_of_fixingAlgebra O hA hE₀
    exact ⟨E', hE'meas, hE'⟩
  exact hle s hs

end InfiniteRelExchangeableLaw

end RelSignature
