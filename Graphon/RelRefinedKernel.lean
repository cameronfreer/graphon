/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRefinedRealization
import Graphon.RelAustinKernel

/-!
# The refined kernels (R4 converse, #107, #197)

The conditional kernels of the refined law `ν = refinedLaw F Q`: the whole rank-`n` layer given
the refined lower observation `L p = (B.lowerFactorMap n p.1, p.2)`, and the exact-anchor layer
at a rank-`n` support `A` given the refined boundary observation
`H_A p = (B.boundaryMap A p.1, p.2)`. These kernels are distinct from the enriched kernels of
`Graphon.RelAustinKernel`: their conditioning carries the refined base.

**Which identities are exact and which are almost everywhere.** The disintegrations and marginal
recoveries are exact measure equalities. Comparisons between versions of a conditional kernel
are almost everywhere under a named marginal, here `refinedLowerLaw F n Q`.

## Contents

* `RefinedLowerSpace`, `RefinedBoundarySpace`, the observations, and the marginal laws
  `refinedLowerLaw`, `refinedBoundaryLaw`; `boundaryProjection` with the exact identity
  `H_A = p_A ∘ L` and `refinedLowerLaw_map_boundaryProjection`.
* `exists_comap_snd_ae_eq_of_refinedLowerMap` — **refined base redundancy**: every
  `L`-measurable event has a refined-base-measurable representative modulo `ν`, transferred
  through the exact forgetting map from the enriched redundancy theorem and closed under the
  retained refined coordinates; `exists_comap_snd_ae_eq_of_refinedBoundaryMap` through `p_A`.
* `refinedLayerKernel`, `refinedStepKernel` — the two conditional kernels, Markov, with the
  exact disintegrations and marginal recoveries.
* `condDistrib_ae_eq_comap_of_ae_representable` — conditioning on a finer observation whose
  events are all represented by a coarser one gives the coarser conditional law, pulled back.
* `refinedLayerKernel_map_ae_eq_refinedStepKernel` — **the support comparison**: projecting
  the layer kernel to the exact component at `A` is the step kernel at `p_A ℓ`, for
  `refinedLowerLaw`-almost every `ℓ`.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {α β γ Ω : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
  [mγ : MeasurableSpace γ] [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  {μ : Measure α} [IsFiniteMeasure μ]

/-- **Conditioning on a finer observation that is represented by a coarser one.** If every event
of `comap X` has a representative in `comap (g ∘ X)` modulo `μ`, then the conditional law given
`X` is, `μ.map X`-almost everywhere, the conditional law given `g ∘ X` read at `g`. -/
theorem condDistrib_ae_eq_comap_of_ae_representable {X : α → β} {g : β → γ} {Y : α → Ω}
    (hX : Measurable X) (hg : Measurable g) (hY : Measurable Y)
    (hrep : ∀ s, MeasurableSet[mβ.comap X] s →
      ∃ t, MeasurableSet[mγ.comap (g ∘ X)] t ∧ s =ᵐ[μ] t) :
    condDistrib Y X μ =ᵐ[μ.map X] (condDistrib Y (g ∘ X) μ).comap g hg := by
  refine condDistrib_ae_eq_of_measure_eq_compProd X hY.aemeasurable ?_
  have hXY : Measurable fun x => (X x, Y x) := hX.prodMk hY
  have hgX : Measurable (g ∘ X) := hg.comp hX
  -- rectangles
  have hrect : ∀ {s : Set β} {t : Set Ω}, MeasurableSet s → MeasurableSet t →
      μ.map (fun x => (X x, Y x)) (s ×ˢ t) =
        (μ.map X ⊗ₘ (condDistrib Y (g ∘ X) μ).comap g hg) (s ×ˢ t) := by
    intro s t hs ht
    obtain ⟨u, hu, hsu⟩ := hrep (X ⁻¹' s) ⟨s, hs, rfl⟩
    rw [Measure.map_apply hXY (hs.prod ht), Measure.compProd_apply_prod hs ht,
      Measure.restrict_map hX hs, lintegral_map (Kernel.measurable_coe _ ht) hX]
    simp only [Kernel.comap_apply]
    have hcd := setLIntegral_condDistrib_of_measurableSet (μ := μ) hgX hY.aemeasurable ht hu
    simp only [Function.comp_apply] at hcd
    rw [setLIntegral_congr hsu, hcd, ← measure_congr (hsu.inter (Filter.EventuallyEq.refl _ _))]
    rfl
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨s, hs, t, ht, rfl⟩
    exact hrect hs ht
  · simpa only [Set.univ_prod_univ] using hrect MeasurableSet.univ MeasurableSet.univ

end ProbabilityTheory

namespace RelSignature

open InfiniteRelExchangeableLaw

universe u

variable {S : RelSignature.{u}}

namespace InfiniteRelExchangeableLaw

variable [Countable S.Srt] [Countable S.Rel] {M : InfiniteRelExchangeableLaw S}
  {B : CoherentBasis M} (F : FiniteActiveExtension B) (n : ℕ) {C : M.RankRepresentation n}

/-! ### Spaces, observations, marginal laws -/

/-- The lower factor with the refined base. -/
abbrev RefinedLowerSpace := B.LowerFactorSpace n × RefinedBaseSpace F n

/-- The boundary at `A` with the refined base. -/
abbrev RefinedBoundarySpace (A : Finset (Σ s : S.Srt, Vinfinite S s)) :=
  B.BoundarySpace A × RefinedBaseSpace F n

/-- The refined lower observation `L`. -/
noncomputable def refinedLowerMap :
    RelStructure S (Vinfinite S) × RefinedBaseSpace F n → RefinedLowerSpace F n :=
  fun p => (B.lowerFactorMap n p.1, p.2)

/-- The refined boundary observation `H_A`. -/
noncomputable def refinedBoundaryMap (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    RelStructure S (Vinfinite S) × RefinedBaseSpace F n → RefinedBoundarySpace F n A :=
  fun p => (B.boundaryMap A p.1, p.2)

/-- The rank-`n` layer, read on the refined space. -/
noncomputable def refinedLayerMap :
    RelStructure S (Vinfinite S) × RefinedBaseSpace F n → B.RankLayerSpace n :=
  fun p => B.rankLayerMap n p.1

/-- The exact-anchor layer at `A`, read on the refined space. -/
noncomputable def refinedExactMap (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    RelStructure S (Vinfinite S) × RefinedBaseSpace F n → B.ExactSpace A :=
  fun p => B.exactMap A p.1

omit [Countable S.Srt] [Countable S.Rel] in
theorem measurable_refinedLowerMap : Measurable (refinedLowerMap F n) :=
  ((B.measurable_lowerFactorMap' n).comp measurable_fst).prodMk measurable_snd

omit [Countable S.Srt] [Countable S.Rel] in
theorem measurable_refinedBoundaryMap (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measurable (refinedBoundaryMap F n A) :=
  ((B.measurable_boundaryMap A).comp measurable_fst).prodMk measurable_snd

omit [Countable S.Srt] [Countable S.Rel] in
theorem measurable_refinedLayerMap : Measurable (refinedLayerMap F n) :=
  (B.measurable_rankLayerMap n).comp measurable_fst

omit [Countable S.Srt] [Countable S.Rel] in
theorem measurable_refinedExactMap (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measurable (refinedExactMap F n A) :=
  (B.measurable_exactMap A).comp measurable_fst

/-- The projection `p_A` from the refined lower observation to the refined boundary at a
rank-`n` support. -/
def boundaryProjection (A : RankSupport S n) :
    RefinedLowerSpace F n → RefinedBoundarySpace F n A.1 :=
  Prod.map (B.lowerToBoundaryProjection A.2) id

omit [Countable S.Srt] [Countable S.Rel] in
theorem measurable_boundaryProjection (A : RankSupport S n) :
    Measurable (boundaryProjection F n A) :=
  (B.measurable_lowerToBoundaryProjection A.2).prodMap measurable_id

omit [Countable S.Srt] [Countable S.Rel] in
/-- **Exact**: `H_A = p_A ∘ L`. -/
theorem refinedBoundaryMap_eq_boundaryProjection_comp (A : RankSupport S n) :
    refinedBoundaryMap F n A.1 = boundaryProjection F n A ∘ refinedLowerMap F n := rfl

omit [Countable S.Srt] [Countable S.Rel] in
/-- The exact-anchor map at `A` is the exact projection of the layer. -/
theorem refinedExactMap_eq_projection_comp (A : RankSupport S n) :
    refinedExactMap F n A.1 = B.rankLayerToExactProjection A.2 ∘ refinedLayerMap F n := rfl

variable (Q : PooledRankExtension C)

/-- The law of the refined lower observation, `λ`. -/
noncomputable def refinedLowerLaw : Measure (RefinedLowerSpace F n) :=
  (refinedLaw F Q).map (refinedLowerMap F n)

/-- The law of the refined boundary observation at `A`, `λ_A`. -/
noncomputable def refinedBoundaryLaw (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measure (RefinedBoundarySpace F n A) :=
  (refinedLaw F Q).map (refinedBoundaryMap F n A)

instance : IsProbabilityMeasure (refinedLowerLaw F n Q) :=
  Measure.isProbabilityMeasure_map (measurable_refinedLowerMap F n).aemeasurable

instance (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    IsProbabilityMeasure (refinedBoundaryLaw F n Q A) :=
  Measure.isProbabilityMeasure_map (measurable_refinedBoundaryMap F n A).aemeasurable

/-- `λ.map p_A = λ_A`, exactly. -/
theorem refinedLowerLaw_map_boundaryProjection (A : RankSupport S n) :
    (refinedLowerLaw F n Q).map (boundaryProjection F n A) = refinedBoundaryLaw F n Q A.1 := by
  rw [refinedLowerLaw, refinedBoundaryLaw,
    Measure.map_map (measurable_boundaryProjection F n A) (measurable_refinedLowerMap F n)]
  rfl

/-! ### Refined base redundancy -/

/-- **Refined base redundancy**: every event measurable for the refined lower observation
agrees, modulo `ν`, with an event measurable for the refined base alone. The below-rank
redundancy of the enriched object is transferred through the exact forgetting map, and closed
under adjoining the retained refined coordinates. -/
theorem exists_comap_snd_ae_eq_of_refinedLowerMap (W : PooledPollingWitness C Q)
    {E : Set (RelStructure S (Vinfinite S) × RefinedBaseSpace F n)}
    (hE : MeasurableSet[MeasurableSpace.comap (refinedLowerMap F n) inferInstance] E) :
    ∃ E', MeasurableSet[MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × RefinedBaseSpace F n → _) inferInstance] E' ∧
      E =ᵐ[refinedLaw F Q] E' := by
  set O := austinEnrichedObject Q W with hO
  haveI := O.isProbabilityMeasure_law
  have hsplit : MeasurableSpace.comap (refinedLowerMap F n) inferInstance =
      MeasurableSpace.comap (B.lowerFactorMap n ∘ Prod.fst) inferInstance ⊔
        MeasurableSpace.comap
          (Prod.snd : RelStructure S (Vinfinite S) × RefinedBaseSpace F n → _) inferInstance :=
    MeasurableSpace.comap_prodMk (B.lowerFactorMap n ∘ Prod.fst) Prod.snd
  rw [hsplit] at hE
  refine eventuallyMeasurableSet_sup (fun s hs => ?_) hE
  obtain ⟨u, hu, rfl⟩ := hs
  -- the forgetting map
  set φ : RelStructure S (Vinfinite S) × RefinedBaseSpace F n →
      RelStructure S (Vinfinite S) × AustinBaseSpace S n := Prod.map id Prod.fst with hφ
  have hφm : Measurable φ := measurable_id.prodMap measurable_fst
  have hφq : Measure.QuasiMeasurePreserving φ (refinedLaw F Q) O.law :=
    (MeasurePreserving.mk hφm (refinedLaw_map_forget F Q W)).quasiMeasurePreserving
  -- the enriched event and its base representative
  obtain ⟨E', hE'm, hE'⟩ := O.exists_comap_snd_ae_eq_of_enrichedLowerMap B
    (E := (B.lowerFactorMap n ∘ Prod.fst) ⁻¹' u) ⟨Prod.fst ⁻¹' u, measurable_fst hu, rfl⟩
  obtain ⟨v, hv, rfl⟩ := hE'm
  refine ⟨Prod.snd ⁻¹' (Prod.fst ⁻¹' v), ⟨Prod.fst ⁻¹' v, measurable_fst hv, rfl⟩, ?_⟩
  have h := hφq.preimage_ae_eq hE'
  exact h

/-- Boundary redundancy, through `p_A`. -/
theorem exists_comap_snd_ae_eq_of_refinedBoundaryMap (W : PooledPollingWitness C Q)
    (A : RankSupport S n)
    {E : Set (RelStructure S (Vinfinite S) × RefinedBaseSpace F n)}
    (hE : MeasurableSet[MeasurableSpace.comap (refinedBoundaryMap F n A.1) inferInstance] E) :
    ∃ E', MeasurableSet[MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × RefinedBaseSpace F n → _) inferInstance] E' ∧
      E =ᵐ[refinedLaw F Q] E' := by
  refine exists_comap_snd_ae_eq_of_refinedLowerMap F n Q W ?_
  rw [refinedBoundaryMap_eq_boundaryProjection_comp, ← MeasurableSpace.comap_comp] at hE
  exact MeasurableSpace.comap_mono (measurable_boundaryProjection F n A).comap_le E hE

omit [Countable S.Srt] [Countable S.Rel] in
/-- The refined base is read by the refined boundary observation. -/
theorem comap_snd_le_comap_refinedBoundaryMap (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × RefinedBaseSpace F n → _) inferInstance ≤
      MeasurableSpace.comap (refinedBoundaryMap F n A) inferInstance := by
  have h : (Prod.snd : RelStructure S (Vinfinite S) × RefinedBaseSpace F n → _) =
      Prod.snd ∘ refinedBoundaryMap F n A := rfl
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono measurable_snd.comap_le

/-! ### The kernels -/

/-- **The refined layer kernel**: the rank-`n` layer given the refined lower observation. -/
noncomputable def refinedLayerKernel : Kernel (RefinedLowerSpace F n) (B.RankLayerSpace n) :=
  condDistrib (refinedLayerMap F n) (refinedLowerMap F n) (refinedLaw F Q)

/-- **The refined step kernel at `A`**: the exact-anchor layer given the refined boundary. -/
noncomputable def refinedStepKernel (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Kernel (RefinedBoundarySpace F n A) (B.ExactSpace A) :=
  condDistrib (refinedExactMap F n A) (refinedBoundaryMap F n A) (refinedLaw F Q)

instance : IsMarkovKernel (refinedLayerKernel F n Q) := by
  rw [refinedLayerKernel]; infer_instance

instance (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    IsMarkovKernel (refinedStepKernel F n Q A) := by
  rw [refinedStepKernel]; infer_instance

/-- **Disintegration of the layer**, exact. -/
theorem compProd_refinedLayerKernel :
    refinedLowerLaw F n Q ⊗ₘ refinedLayerKernel F n Q =
      (refinedLaw F Q).map fun p => (refinedLowerMap F n p, refinedLayerMap F n p) := by
  rw [refinedLowerLaw, refinedLayerKernel]
  exact compProd_map_condDistrib (measurable_refinedLayerMap F n).aemeasurable

/-- **Disintegration at a support**, exact. -/
theorem compProd_refinedStepKernel (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    refinedBoundaryLaw F n Q A ⊗ₘ refinedStepKernel F n Q A =
      (refinedLaw F Q).map fun p => (refinedBoundaryMap F n A p, refinedExactMap F n A p) := by
  rw [refinedBoundaryLaw, refinedStepKernel]
  exact compProd_map_condDistrib (measurable_refinedExactMap F n A).aemeasurable

/-- **Marginal recovery for the layer**, exact. -/
theorem refinedLayerKernel_comp_refinedLowerLaw :
    refinedLayerKernel F n Q ∘ₘ refinedLowerLaw F n Q =
      (refinedLaw F Q).map (refinedLayerMap F n) := by
  rw [refinedLowerLaw, refinedLayerKernel]
  exact condDistrib_comp_map (measurable_refinedLowerMap F n).aemeasurable
    (measurable_refinedLayerMap F n).aemeasurable

/-- **Marginal recovery at a support**, exact. -/
theorem refinedStepKernel_comp_refinedBoundaryLaw (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    refinedStepKernel F n Q A ∘ₘ refinedBoundaryLaw F n Q A =
      (refinedLaw F Q).map (refinedExactMap F n A) := by
  rw [refinedBoundaryLaw, refinedStepKernel]
  exact condDistrib_comp_map (measurable_refinedBoundaryMap F n A).aemeasurable
    (measurable_refinedExactMap F n A).aemeasurable

/-! ### The support comparison -/

/-- Conditioning the exact-anchor layer at `A` on `L` or on `H_A` gives the same conditional
law: both observations are represented, modulo `ν`, by the refined base. -/
theorem condDistrib_refinedExactMap_ae_eq (W : PooledPollingWitness C Q) (A : RankSupport S n) :
    condDistrib (refinedExactMap F n A.1) (refinedLowerMap F n) (refinedLaw F Q)
      =ᵐ[refinedLowerLaw F n Q]
        (refinedStepKernel F n Q A.1).comap (boundaryProjection F n A)
          (measurable_boundaryProjection F n A) := by
  rw [refinedLowerLaw, refinedStepKernel, refinedBoundaryMap_eq_boundaryProjection_comp]
  refine condDistrib_ae_eq_comap_of_ae_representable (measurable_refinedLowerMap F n)
    (measurable_boundaryProjection F n A) (measurable_refinedExactMap F n A.1) fun s hs => ?_
  obtain ⟨t, ht, hst⟩ := exists_comap_snd_ae_eq_of_refinedLowerMap F n Q W hs
  refine ⟨t, ?_, hst⟩
  rw [← refinedBoundaryMap_eq_boundaryProjection_comp]
  exact comap_snd_le_comap_refinedBoundaryMap F n A.1 t ht

/-- **The support comparison**: for `λ`-almost every `ℓ`, the layer kernel at `ℓ` projected to
the exact component at `A` is the step kernel at `p_A ℓ`. -/
theorem refinedLayerKernel_map_ae_eq_refinedStepKernel (W : PooledPollingWitness C Q)
    (A : RankSupport S n) :
    (fun ℓ => (refinedLayerKernel F n Q ℓ).map (B.rankLayerToExactProjection A.2))
      =ᵐ[refinedLowerLaw F n Q]
        fun ℓ => refinedStepKernel F n Q A.1 (boundaryProjection F n A ℓ) := by
  have h1 : condDistrib (B.rankLayerToExactProjection A.2 ∘ refinedLayerMap F n)
      (refinedLowerMap F n) (refinedLaw F Q) =ᵐ[(refinedLaw F Q).map (refinedLowerMap F n)]
      (condDistrib (refinedLayerMap F n) (refinedLowerMap F n) (refinedLaw F Q)).map
        (B.rankLayerToExactProjection A.2) :=
    condDistrib_comp (μ := refinedLaw F Q) (refinedLowerMap F n)
      (measurable_refinedLayerMap F n).aemeasurable (B.measurable_rankLayerToExactProjection A.2)
  rw [← refinedExactMap_eq_projection_comp] at h1
  have h2 := condDistrib_refinedExactMap_ae_eq F n Q W A
  rw [refinedLowerLaw] at h2 ⊢
  filter_upwards [h1, h2] with ℓ h1ℓ h2ℓ
  rw [refinedLayerKernel, ← Kernel.map_apply _ (B.measurable_rankLayerToExactProjection A.2),
    ← h1ℓ, h2ℓ, Kernel.comap_apply]

end InfiniteRelExchangeableLaw

end RelSignature
