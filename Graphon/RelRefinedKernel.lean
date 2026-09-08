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
* `refinedLayerKernel_map_ae_eq_refinedStepKernel` — **the support comparison**: projecting
  the layer kernel to the exact component at `A` is the step kernel at `p_A ℓ`, for
  `refinedLowerLaw`-almost every `ℓ`.
* `layerReindex` — the layer cube as the product of the exact layers over the rank-`n`
  supports, with the definitional exact observation identity.
* `iCondIndepFun_refinedExactMap_refinedLowerMap` — mutual conditional independence of the
  exact layers given the refined lower observation, by refined base redundancy.
* `layerCylinder`, `exactCylinder`, `cylinderAnchors` — the countable determining family of
  Boolean-coordinate cylinders, a π-system generating the layer cube's σ-algebra.
* `refinedLayerKernel_map_ae_eq_infinitePi` — **the product identity**: for
  `refinedLowerLaw`-almost every `ℓ`, the reindexed layer kernel at `ℓ` is the infinite product
  of the step kernels at `p_A ℓ`, as an equality of measures on one conull set.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {α β γ Ω : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
  [mγ : MeasurableSpace γ] [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  {μ : Measure α} [IsFiniteMeasure μ]

/-- **Conditioning on a finer observation that is represented by a coarser one.** If every event
of `comap X` has a representative in `comap (g ∘ X)` modulo `μ`, then the conditional law given
`X` is, `μ.map X`-almost everywhere, the conditional law given `g ∘ X` read at `g`. -/
private theorem condDistrib_ae_eq_comap_of_ae_representable {X : α → β} {g : β → γ} {Y : α → Ω}
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

/-! ### The reindexing of the layer by supports -/

variable (B) in
/-- The anchor of a layer index, as a rank-`n` support. -/
def layerAnchor (j : B.RankLayerIndex n) : RankSupport S n := ⟨B.anchor j.1, j.2⟩

variable (B) in
/-- A layer index as an exact index at its anchor. -/
def layerExactIndex (j : B.RankLayerIndex n) : B.ExactIndex (layerAnchor B n j).1 := ⟨j.1, rfl⟩

variable (B) in
/-- **The reindexing**: the layer cube is the product over the rank-`n` supports of the exact
layers, through `rankLayerToExactProjection` at each support. -/
noncomputable def layerReindex :
    B.RankLayerSpace n ≃ᵐ (∀ A : RankSupport S n, B.ExactSpace A.1) where
  toFun f A := B.rankLayerToExactProjection A.2 f
  invFun g j := g (layerAnchor B n j) (layerExactIndex B n j)
  left_inv f := by
    funext j
    exact congrArg f (Subtype.ext rfl)
  right_inv g := by
    funext A i
    rcases A with ⟨A, hA⟩
    rcases i with ⟨i, hi⟩
    cases hi
    rfl
  measurable_toFun := measurable_pi_lambda _ fun A => B.measurable_rankLayerToExactProjection A.2
  measurable_invFun := by
    show Measurable fun g : ∀ A : RankSupport S n, B.ExactSpace A.1 =>
      fun j => g (layerAnchor B n j) (layerExactIndex B n j)
    exact measurable_pi_lambda _ fun _ => (measurable_pi_apply _).comp (measurable_pi_apply _)

omit [Countable S.Srt] [Countable S.Rel] in
@[simp] theorem layerReindex_apply (f : B.RankLayerSpace n) (A : RankSupport S n) :
    layerReindex B n f A = B.rankLayerToExactProjection A.2 f := rfl

omit [Countable S.Srt] [Countable S.Rel] in
@[simp] theorem layerReindex_symm_apply (g : ∀ A : RankSupport S n, B.ExactSpace A.1)
    (j : B.RankLayerIndex n) :
    (layerReindex B n).symm g j = g (layerAnchor B n j) (layerExactIndex B n j) := rfl

omit [Countable S.Srt] [Countable S.Rel] in
/-- **The exact observation identity**: reindexing the layer map reads the exact-anchor map at
every support. Definitional. -/
theorem layerReindex_comp_refinedLayerMap :
    ⇑(layerReindex B n) ∘ refinedLayerMap F n =
      fun p (A : RankSupport S n) => refinedExactMap F n A.1 p := by
  funext p A
  rfl

/-! ### Mutuality under the lower conditioning -/

/-- **Mutual conditional independence of the exact layers given the refined lower observation**,
transferred from the refined base through refined base redundancy. -/
theorem iCondIndepFun_refinedExactMap_refinedLowerMap (W : PooledPollingWitness C Q) :
    iCondIndepFun (MeasurableSpace.comap (refinedLowerMap F n) inferInstance)
      (measurable_refinedLowerMap F n).comap_le
      (fun A : RankSupport S n => refinedExactMap F n A.1) (refinedLaw F Q) := by
  have hle : MeasurableSpace.comap
      (Prod.snd : RelStructure S (Vinfinite S) × RefinedBaseSpace F n → _) inferInstance ≤
      MeasurableSpace.comap (refinedLowerMap F n) inferInstance := by
    have h : (Prod.snd : RelStructure S (Vinfinite S) × RefinedBaseSpace F n → _) =
        Prod.snd ∘ refinedLowerMap F n := rfl
    rw [h, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono measurable_snd.comap_le
  exact (iCondIndepFun_congr_of_ae_representable hle (measurable_refinedLowerMap F n).comap_le
    (fun _ hs => exists_comap_snd_ae_eq_of_refinedLowerMap F n Q W hs)
    (fun A : RankSupport S n => measurable_refinedExactMap F n A.1)).mpr
    (iCondIndepFun_exactMap_refinedLaw F Q)

/-! ### The countable determining family -/

variable (B) in
/-- A finite Boolean-coordinate cylinder of the layer cube. -/
def layerCylinder (T : List (B.RankLayerIndex n × Bool)) : Set (B.RankLayerSpace n) :=
  {f | ∀ x ∈ T, f x.1 = x.2}

variable (B) in
/-- The coordinates of a cylinder anchored at `A`, as a cylinder of the exact layer at `A`. -/
def exactCylinder (T : List (B.RankLayerIndex n × Bool)) (A : RankSupport S n) :
    Set (B.ExactSpace A.1) :=
  {y | ∀ x ∈ T, ∀ h : B.anchor x.1.1 = A.1, y ⟨x.1.1, h⟩ = x.2}

open scoped Classical in
variable (B) in
/-- The anchors of a cylinder's coordinates. -/
noncomputable def cylinderAnchors (T : List (B.RankLayerIndex n × Bool)) :
    Finset (RankSupport S n) :=
  (T.map fun x => layerAnchor B n x.1).toFinset

omit [Countable S.Srt] [Countable S.Rel] in
theorem measurableSet_layerCylinder (T : List (B.RankLayerIndex n × Bool)) :
    MeasurableSet (layerCylinder B n T) := by
  have h : layerCylinder B n T = ⋂ x ∈ T, (fun f : B.RankLayerSpace n => f x.1) ⁻¹' {x.2} := by
    ext f
    simp [layerCylinder]
  rw [h]
  exact Set.Finite.measurableSet_biInter (List.finite_toSet T) fun x _ =>
    measurable_pi_apply x.1 (measurableSet_singleton x.2)

omit [Countable S.Srt] [Countable S.Rel] in
theorem measurableSet_exactCylinder (T : List (B.RankLayerIndex n × Bool)) (A : RankSupport S n) :
    MeasurableSet (exactCylinder B n T A) := by
  have h : exactCylinder B n T A = ⋂ x ∈ T, ⋂ h : B.anchor x.1.1 = A.1,
      (fun y : B.ExactSpace A.1 => y ⟨x.1.1, h⟩) ⁻¹' {x.2} := by
    ext y
    simp [exactCylinder]
  rw [h]
  exact Set.Finite.measurableSet_biInter (List.finite_toSet T) fun x _ =>
    MeasurableSet.iInter fun _ => measurable_pi_apply _ (measurableSet_singleton x.2)

omit [Countable S.Srt] [Countable S.Rel] in
theorem layerCylinder_append (T₁ T₂ : List (B.RankLayerIndex n × Bool)) :
    layerCylinder B n (T₁ ++ T₂) = layerCylinder B n T₁ ∩ layerCylinder B n T₂ := by
  ext f
  simp [layerCylinder, or_imp, forall_and]

omit [Countable S.Srt] [Countable S.Rel] in
theorem isPiSystem_layerCylinder : IsPiSystem (Set.range (layerCylinder B n)) := by
  rintro _ ⟨T₁, rfl⟩ _ ⟨T₂, rfl⟩ -
  exact ⟨T₁ ++ T₂, layerCylinder_append n T₁ T₂⟩

omit [Countable S.Srt] [Countable S.Rel] in
/-- The Boolean-coordinate cylinders generate the layer cube's σ-algebra. -/
theorem generateFrom_layerCylinder :
    MeasurableSpace.generateFrom (Set.range (layerCylinder B n)) =
      (inferInstance : MeasurableSpace (B.RankLayerSpace n)) := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) ?_
  · rintro _ ⟨T, rfl⟩
    exact measurableSet_layerCylinder n T
  · refine iSup_le fun j => ?_
    refine Measurable.comap_le (measurable_to_bool ?_)
    refine MeasurableSpace.measurableSet_generateFrom ⟨[(j, true)], ?_⟩
    ext f
    simp [layerCylinder]

omit [Countable S.Srt] [Countable S.Rel] in
/-- A cylinder, reindexed, is the finite product of its exact cylinders. -/
theorem layerReindex_symm_preimage_layerCylinder (T : List (B.RankLayerIndex n × Bool)) :
    (layerReindex B n).symm ⁻¹' layerCylinder B n T =
      Set.pi (cylinderAnchors B n T) (exactCylinder B n T) := by
  classical
  ext g
  simp only [Set.mem_preimage, layerCylinder, Set.mem_setOf_eq, Set.mem_pi, exactCylinder,
    cylinderAnchors, Finset.mem_coe, List.mem_toFinset, List.mem_map, layerReindex_symm_apply]
  constructor
  · rintro h A - x hx hA
    rcases A with ⟨A, hA'⟩
    cases hA
    exact h x hx
  · intro h x hx
    exact h (layerAnchor B n x.1) ⟨x, hx, rfl⟩ x hx rfl

omit [Countable S.Srt] [Countable S.Rel] in
/-- The layer observation lies in a cylinder exactly when each exact observation lies in the
corresponding exact cylinder. -/
theorem preimage_layerCylinder_refinedLayerMap (T : List (B.RankLayerIndex n × Bool)) :
    refinedLayerMap F n ⁻¹' layerCylinder B n T =
      ⋂ A ∈ cylinderAnchors B n T, refinedExactMap F n A.1 ⁻¹' exactCylinder B n T A := by
  classical
  ext p
  simp only [Set.mem_preimage, layerCylinder, Set.mem_setOf_eq, Set.mem_iInter, exactCylinder,
    cylinderAnchors, List.mem_toFinset, List.mem_map]
  constructor
  · rintro h A - x hx hA
    rcases A with ⟨A, hA'⟩
    cases hA
    exact h x hx
  · intro h x hx
    exact h (layerAnchor B n x.1) ⟨x, hx, rfl⟩ x hx rfl

/-! ### The product identity -/

/-- **The cylinder identity**: for `λ`-almost every `ℓ`, the layer kernel gives a cylinder the
product over its anchors of the step kernels' masses of the exact cylinders. Independence is
used between supports only. -/
theorem ae_refinedLayerKernel_layerCylinder (W : PooledPollingWitness C Q)
    (T : List (B.RankLayerIndex n × Bool)) :
    ∀ᵐ ℓ ∂refinedLowerLaw F n Q,
      refinedLayerKernel F n Q ℓ (layerCylinder B n T) =
        ∏ A ∈ cylinderAnchors B n T,
          refinedStepKernel F n Q A.1 (boundaryProjection F n A ℓ) (exactCylinder B n T A) := by
  set ν := refinedLaw F Q with hν
  set L := refinedLowerMap F n with hL
  have hLm : Measurable L := measurable_refinedLowerMap F n
  have hcyl := measurableSet_layerCylinder n T
  have hex : ∀ A, MeasurableSet (exactCylinder B n T A) := measurableSet_exactCylinder n T
  -- the real-valued identity under `ν`
  have h1 : (fun a => (refinedLayerKernel F n Q (L a)).real (layerCylinder B n T)) =ᵐ[ν]
      ν⟦refinedLayerMap F n ⁻¹' layerCylinder B n T | MeasurableSpace.comap L inferInstance⟧ :=
    condDistrib_ae_eq_condExp hLm (measurable_refinedLayerMap F n) hcyl
  rw [preimage_layerCylinder_refinedLayerMap F n T] at h1
  have h3 := (iCondIndepFun_iff_condExp_inter_preimage_eq_mul _ _
    (fun A : RankSupport S n => measurable_refinedExactMap F n A.1)).mp
    (iCondIndepFun_refinedExactMap_refinedLowerMap F n Q W) (cylinderAnchors B n T)
    (sets := fun A => exactCylinder B n T A) (fun A _ => hex A)
  have h4 : ∀ A : RankSupport S n,
      ν⟦refinedExactMap F n A.1 ⁻¹' exactCylinder B n T A | MeasurableSpace.comap L inferInstance⟧
        =ᵐ[ν] fun a =>
          (condDistrib (refinedExactMap F n A.1) L ν (L a)).real (exactCylinder B n T A) :=
    fun A => (condDistrib_ae_eq_condExp hLm (measurable_refinedExactMap F n A.1) (hex A)).symm
  have h5 : ∀ A : RankSupport S n, ∀ᵐ a ∂ν,
      condDistrib (refinedExactMap F n A.1) L ν (L a) =
        refinedStepKernel F n Q A.1 (boundaryProjection F n A (L a)) := by
    intro A
    have h := condDistrib_refinedExactMap_ae_eq F n Q W A
    rw [refinedLowerLaw] at h
    filter_upwards [ae_of_ae_map hLm.aemeasurable h] with a ha
    rw [ha, Kernel.comap_apply]
  have hreal : ∀ᵐ a ∂ν,
      (refinedLayerKernel F n Q (L a)).real (layerCylinder B n T) =
        ∏ A ∈ cylinderAnchors B n T,
          (refinedStepKernel F n Q A.1 (boundaryProjection F n A (L a))).real
            (exactCylinder B n T A) := by
    filter_upwards [h1, h3, (Filter.eventually_all_finset (cylinderAnchors B n T)).mpr
      fun A _ => h4 A, (Filter.eventually_all_finset (cylinderAnchors B n T)).mpr
      fun A _ => h5 A] with a ha1 ha3 ha4 ha5
    rw [ha1, ha3, Finset.prod_apply]
    exact Finset.prod_congr rfl fun A hA => by rw [ha4 A hA, ha5 A hA]
  -- transfer to `λ`
  have hmeas : MeasurableSet {ℓ : RefinedLowerSpace F n |
      (refinedLayerKernel F n Q ℓ).real (layerCylinder B n T) =
        ∏ A ∈ cylinderAnchors B n T,
          (refinedStepKernel F n Q A.1 (boundaryProjection F n A ℓ)).real
            (exactCylinder B n T A)} := by
    refine measurableSet_eq_fun ?_ (Finset.measurable_prod _ fun A _ => ?_)
    · exact ((refinedLayerKernel F n Q).measurable_coe hcyl).ennreal_toReal
    · exact (((refinedStepKernel F n Q A.1).measurable_coe (hex A)).comp
        (measurable_boundaryProjection F n A)).ennreal_toReal
  have hlam := (ae_map_iff hLm.aemeasurable hmeas).mpr hreal
  rw [refinedLowerLaw]
  filter_upwards [hlam] with ℓ hℓ
  simp only [measureReal_def] at hℓ
  rw [← ENNReal.toReal_prod] at hℓ
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.prod_ne_top fun A _ => measure_ne_top _ _)).mp hℓ

/-- **The product identity.** For `λ`-almost every `ℓ`, the layer kernel at `ℓ`, reindexed by
supports, **is** the product of the step kernels at `p_A ℓ`: an equality of measures on the
product of the exact layers, obtained on one conull set from the countable family of
Boolean-coordinate cylinders by measure uniqueness. -/
theorem refinedLayerKernel_map_ae_eq_infinitePi (W : PooledPollingWitness C Q) :
    (fun ℓ => (refinedLayerKernel F n Q ℓ).map (layerReindex B n))
      =ᵐ[refinedLowerLaw F n Q]
        fun ℓ => Measure.infinitePi fun A : RankSupport S n =>
          refinedStepKernel F n Q A.1 (boundaryProjection F n A ℓ) := by
  have hall := ae_all_iff.mpr fun T => ae_refinedLayerKernel_layerCylinder F n Q W T
  filter_upwards [hall] with ℓ hℓ
  set κ : ∀ A : RankSupport S n, Measure (B.ExactSpace A.1) := fun A =>
    refinedStepKernel F n Q A.1 (boundaryProjection F n A ℓ) with hκ
  haveI : ∀ A, IsProbabilityMeasure (κ A) := fun A => inferInstance
  have hcube : refinedLayerKernel F n Q ℓ = (Measure.infinitePi κ).map (layerReindex B n).symm := by
    refine ext_of_generate_finite _ (generateFrom_layerCylinder n).symm
      (isPiSystem_layerCylinder n) ?_ ?_
    · rintro _ ⟨T, rfl⟩
      rw [hℓ T, (layerReindex B n).symm.map_apply, layerReindex_symm_preimage_layerCylinder n,
        Measure.infinitePi_pi κ fun A _ => measurableSet_exactCylinder n T A]
    · haveI : IsProbabilityMeasure ((Measure.infinitePi κ).map (layerReindex B n).symm) :=
        Measure.isProbabilityMeasure_map (layerReindex B n).symm.measurable.aemeasurable
      rw [measure_univ, measure_univ]
  rw [hcube, Measure.map_map (layerReindex B n).measurable (layerReindex B n).symm.measurable,
    (layerReindex B n).self_comp_symm, Measure.map_id]

end InfiniteRelExchangeableLaw

end RelSignature
