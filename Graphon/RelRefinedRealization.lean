/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelInsertion
import Graphon.RelAustinEnriched
import Graphon.RelFiniteActiveBasis
import Graphon.RelSingletonPeel
import Graphon.ForMathlib.CondExpRepresentable

/-!
# The refined realization (R4 converse, #107, #197)

The refined polling conditioning `𝔅_fix` is realized as a standard Borel observation, for the
canonical pooled construction and an arbitrary raw coherent basis `B` with a finite-active
extension `F`. The refined base retains the Austin base literally and adds, at every mixed
support, the finite-active factor of its identified support. Original-support factors remain
target observations and are not part of the base.

## Contents

* `RefinedBaseSpace`, `refinedBaseObs` — the refined base and its observation on the pooled
  space; `refinedObs`, `refinedLaw` — the refined enriched law, a pushforward of `Q.law`.
* `refinedLaw_map_forget`, `refinedLaw_map_fst`, `refinedLaw_map_original` — forgetting the
  added factor coordinates returns the enriched law exactly; the structure marginal is the law;
  structure with original latents is `C.P`. These are measure equalities only.
* `refinedCond_le_fixBase`, `exists_refinedCond_ae_eq_of_fixBase` — the two halves of the
  conditioning comparison between the observation's pullback and `𝔅_fix`: exact containment one
  way, eventwise representability modulo `Q.law` the other. Never a σ-algebra equality.
* `iCondIndepFun_originalFaFactor_refinedCond` — the finite-event mutuality packaged as mutual
  conditional independence of the original-support finite-active factors, moved to the
  observation's pullback.
* `iCondIndepFun_factorMap_refinedLaw` — **the kernel seam's input**: under the refined law,
  the raw factors `B.factorMap A ∘ Prod.fst` are mutually conditionally independent given the
  refined base; `iCondIndepFun_exactMap_refinedLaw` for the exact layers, and
  `condExp_iInter_fixing_eq_prod_refinedLaw` for arbitrary raw fixing events, eventwise.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

open InfiniteRelExchangeableLaw

universe u

variable {S : RelSignature.{u}}

/-! ### Carrier identities -/

/-- Restricting the identified carrier along the doubling embedding reads the original half. -/
theorem restrict_doubleEmb_poolStructureEquiv (Y : RelStructure S (PoolVertex S)) :
    RelStructure.restrict (doubleEmb S) (poolStructureEquiv S Y) = restrictOriginal S Y := by
  funext c
  change Y (RelCoord.map (fun s => ((poolVertexEquiv S s).symm : Vinfinite S s → PoolVertex S s))
    (RelCoord.map (fun s => (doubleEmb S s : Vinfinite S s → Vinfinite S s)) c)) =
    Y (RelCoord.map (fun s => (originalVertex S s : Vinfinite S s → PoolVertex S s)) c)
  rw [← RelCoord.map_comp]
  congr 2
  funext s x
  exact (poolVertexEquiv S s).symm_apply_apply (Sum.inl x)

/-- The identified support of an original-half support is the doubled support. -/
theorem identifiedSupport_supportImage_originalVertex (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    identifiedSupport (supportImage (originalVertex S) A) = doubleSupport A := by
  classical
  ext v
  simp only [identifiedSupport, doubleSupport, supportImage, Finset.mem_image]
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨Sigma.map id (fun s => ⇑(originalVertex S s)) u, ⟨u, hu, rfl⟩, rfl⟩

namespace InfiniteRelExchangeableLaw

variable [Countable S.Srt] [Countable S.Rel] {M : InfiniteRelExchangeableLaw S} {n : ℕ}
  {C : M.RankRepresentation n} {B : CoherentBasis M} (F : FiniteActiveExtension B)

/-! ### The refined base and law -/

/-- **The refined base**: the Austin base together with the finite-active factor at the
identified support of every mixed rank-`n` support. -/
abbrev RefinedBaseSpace (n : ℕ) :=
  AustinBaseSpace S n × (∀ X : MixedClusterIndex S n, F.FaFactorSpace (identifiedSupport X.1))

instance : StandardBorelSpace (RefinedBaseSpace F n) := inferInstance

open scoped Classical in
/-- The refined base observation on the pooled space: the source polling conditioning paired
with the mixed factor maps read on the identified carrier. -/
noncomputable def refinedBaseObs :
    RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → RefinedBaseSpace F n :=
  fun p => (sourcePollingCond p,
    fun X => F.faFactorMap (identifiedSupport X.1) (poolStructureEquiv S p.1))

open scoped Classical in
omit [Countable S.Srt] in
theorem measurable_refinedBaseObs : Measurable (refinedBaseObs F (n := n)) :=
  measurable_sourcePollingCond.prodMk (measurable_pi_lambda _ fun _ =>
    (F.measurable_faFactorMap' _).comp ((poolStructureEquiv S).measurable.comp measurable_fst))

/-- The refined enriched observation: the original structure with the refined base. -/
noncomputable def refinedObs :
    RelStructure S (PoolVertex S) × PooledRankLatentSpace S n →
      RelStructure S (Vinfinite S) × RefinedBaseSpace F n :=
  fun p => (restrictOriginal S p.1, refinedBaseObs F p)

omit [Countable S.Srt] in
theorem measurable_refinedObs : Measurable (refinedObs F (n := n)) :=
  ((measurable_restrict _).comp measurable_fst).prodMk (measurable_refinedBaseObs F)

/-- **The refined law**: the pushforward of the pooled law along the refined observation. -/
noncomputable def refinedLaw (Q : PooledRankExtension C) :
    Measure (RelStructure S (Vinfinite S) × RefinedBaseSpace F n) :=
  (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)).map
    (refinedObs F)

instance (Q : PooledRankExtension C) : IsProbabilityMeasure (refinedLaw F Q) := by
  haveI := C.isProbabilityMeasure_P
  exact Measure.isProbabilityMeasure_map (measurable_refinedObs F).aemeasurable

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
/-- Forgetting the added factor coordinates is the compression to the enriched object. -/
theorem forget_comp_refinedObs :
    Prod.map id Prod.fst ∘ refinedObs F (n := n) = pooledToEnrichedObject := rfl

open scoped Classical in
/-- **Forgetting the added factor coordinates returns the enriched law exactly.** A measure
equality; no independence is asserted by forgetting coordinates. -/
theorem refinedLaw_map_forget (Q : PooledRankExtension C) (W : PooledPollingWitness C Q) :
    (refinedLaw F Q).map (Prod.map id Prod.fst) = (austinEnrichedObject Q W).law := by
  rw [refinedLaw, Measure.map_map (measurable_id.prodMap measurable_fst) (measurable_refinedObs F),
    forget_comp_refinedObs]
  show _ = (enrichedPollingLaw Q).map compressEnriched
  rw [enrichedPollingLaw, Measure.map_map measurable_compressEnriched measurable_enrichedPollingMap,
    compressEnriched_comp_enrichedPollingMap]

/-- The structure marginal of the refined law is the exchangeable law. -/
theorem refinedLaw_map_fst (Q : PooledRankExtension C) :
    (refinedLaw F Q).map Prod.fst = (M.law : Measure (RelStructure S (Vinfinite S))) := by
  haveI := C.isProbabilityMeasure_P
  rw [refinedLaw, Measure.map_map measurable_fst (measurable_refinedObs F), ← C.map_fst,
    ← Q.map_restrict_embedding (originalVertex S), Measure.map_map measurable_fst
      ((measurable_restrict _).prodMap (measurable_latentRestrictOver _ n))]
  rfl

/-- Reading the structure together with the original latents returns `C.P` exactly. -/
theorem refinedLaw_map_original (Q : PooledRankExtension C) :
    (refinedLaw F Q).map (fun p => (p.1, restrictOriginalLatents S n p.2.1.1)) = C.P := by
  have hm : Measurable (fun p : RelStructure S (Vinfinite S) × RefinedBaseSpace F n =>
      (p.1, restrictOriginalLatents S n p.2.1.1)) :=
    measurable_fst.prodMk ((measurable_restrictOriginalLatents n).comp measurable_snd.fst.fst)
  rw [refinedLaw, Measure.map_map hm (measurable_refinedObs F),
    ← Q.map_restrict_embedding (originalVertex S)]
  rfl

/-! ### The conditioning comparison -/

/-- The pullback of the refined base observation on the pooled space. -/
@[implicit_reducible]
noncomputable def refinedCond (n : ℕ) :
    MeasurableSpace (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) :=
  MeasurableSpace.comap (refinedBaseObs F (n := n)) inferInstance

omit [Countable S.Srt] in
theorem refinedCond_le : refinedCond F n ≤
    (inferInstance : MeasurableSpace (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) :=
  (measurable_refinedBaseObs F).comap_le

open scoped Classical in
omit [Countable S.Srt] in
/-- The pooled block at a mixed support is measurable for the pooled finite-active fixing
algebra of that support. -/
theorem measurable_blockMapOver_pooledFiniteActiveFixingAlgebra
    (X : Finset (Σ s : S.Srt, PoolVertex S s)) :
    Measurable[pooledFiniteActiveFixingAlgebra X] (blockMapOver (S := S) X) := by
  set e : ∀ s, PoolVertex S s ↪ Vinfinite S s := fun s => (poolVertexEquiv S s).toEmbedding
  have hfac : blockMapOver (S := S) X =
      (blockSpaceCongr e X ∘ blockMapOver (supportImage e X)) ∘ poolStructureEquiv S := by
    funext Y
    rw [← blockMapOver_restrict e X]
    exact congrArg (blockMapOver X) ((poolStructureEquiv S).symm_apply_apply Y).symm
  rw [hfac]
  have h1 : Measurable[RelStructure.finiteActiveFixingAlgebra (supportImage e X)]
      (blockMapOver (S := S) (supportImage e X)) :=
    (measurable_blockMap_fixingAlgebra (supportImage e X)).mono
      (RelStructure.fixingAlgebra_le_finiteActiveFixingAlgebra _) le_rfl
  have h2 : Measurable (blockSpaceCongr e X) :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  exact (h2.comp h1).comp (measurable_iff_comap_le.mpr le_rfl)

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
/-- The latent generators lie in the refined conditioning. -/
theorem fixBaseGen_inl_le_refinedCond (I : PooledRankLatentIndex S n) :
    fixBaseGen n (.inl I) ≤ refinedCond F n := by
  have h : (fun p : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n => p.2 I) =
      (fun b : RefinedBaseSpace F n => b.1.1 I) ∘ refinedBaseObs F := rfl
  show MeasurableSpace.comap _ _ ≤ _
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono
    ((measurable_pi_apply I).comp measurable_fst.fst).comap_le

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
/-- The mixed factor coordinates lie in the refined conditioning. -/
theorem comap_faFactorMap_mixed_le_refinedCond (X : MixedClusterIndex S n) :
    MeasurableSpace.comap
      (F.faFactorMap (identifiedSupport X.1) ∘ poolStructureEquiv S ∘ Prod.fst) inferInstance ≤
      refinedCond F n := by
  have h : F.faFactorMap (identifiedSupport X.1) ∘ poolStructureEquiv S ∘
      (Prod.fst : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → _) =
      (fun b : RefinedBaseSpace F n => b.2 X) ∘ refinedBaseObs F := rfl
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono ((measurable_pi_apply X).comp measurable_snd).comap_le

open scoped Classical in
omit [Countable S.Srt] in
/-- **Exact containment**: the refined conditioning lies inside `𝔅_fix`. The retained raw
blocks enter through their fixing-algebra measurability. -/
theorem refinedCond_le_fixBase : refinedCond F n ≤ fixBase n := by
  rw [fixBase_eq_iSup]
  set m : MeasurableSpace (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) :=
    ⨆ i, fixBaseGen (S := S) n i with hm
  have hlat : Measurable[m]
      (fun p : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n => p.2) :=
    measurable_pi_iff.mpr fun I => measurable_iff_comap_le.mpr
      (le_iSup (fixBaseGen (S := S) n) (.inl I))
  have hclu : Measurable[m] (pollingClusters (S := S) (n := n)) :=
    measurable_pi_iff.mpr fun X =>
      ((measurable_blockMapOver_pooledFiniteActiveFixingAlgebra X.1).comp
        (measurable_iff_comap_le.mpr le_rfl)).mono (le_iSup (fixBaseGen (S := S) n) (.inr X))
        le_rfl
  have hfac : Measurable[m]
      (fun p : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n =>
        fun X : MixedClusterIndex S n =>
          F.faFactorMap (identifiedSupport X.1) (poolStructureEquiv S p.1)) :=
    measurable_pi_iff.mpr fun X =>
      (((F.measurable_faFactorMap _).comp (measurable_iff_comap_le.mpr le_rfl)).comp
        (measurable_iff_comap_le.mpr le_rfl)).mono (le_iSup (fixBaseGen (S := S) n) (.inr X))
        le_rfl
  exact Measurable.comap_le ((hlat.prodMk hclu).prodMk hfac)

/-- The pooled structure, identified with the original carrier, pushes `Q.law` to the law. -/
theorem map_poolStructureEquiv_fst (Q : PooledRankExtension C) :
    (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)).map
      (poolStructureEquiv S ∘ Prod.fst) = (M.law : Measure (RelStructure S (Vinfinite S))) := by
  rw [← Measure.map_map (poolStructureEquiv S).measurable measurable_fst]
  exact Q.map_fst_poolStructureEquiv

theorem quasiMeasurePreserving_poolStructureEquiv_fst (Q : PooledRankExtension C) :
    Measure.QuasiMeasurePreserving (poolStructureEquiv S ∘ Prod.fst)
      (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))
      (M.law : Measure (RelStructure S (Vinfinite S))) :=
  (MeasurePreserving.mk ((poolStructureEquiv S).measurable.comp measurable_fst)
    (map_poolStructureEquiv_fst Q)).quasiMeasurePreserving

open scoped Classical in
/-- **Eventwise representability**: every `𝔅_fix`-event has a representative in the refined
conditioning, modulo `Q.law`. Eventwise, never as a σ-algebra equality. -/
theorem exists_refinedCond_ae_eq_of_fixBase (Q : PooledRankExtension C)
    {E : Set (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)}
    (hE : MeasurableSet[fixBase n] E) :
    ∃ E', MeasurableSet[refinedCond F n] E' ∧
      E' =ᵐ[(Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))] E := by
  set μ : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) :=
    (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) with hμ
  -- generators
  have hgen : ∀ (i : FixBaseIndex S n) (G : Set _), MeasurableSet[fixBaseGen n i] G →
      ∃ G', MeasurableSet[refinedCond F n] G' ∧ G' =ᵐ[μ] G := by
    rintro (I | X) G hG
    · exact ⟨G, fixBaseGen_inl_le_refinedCond F I G hG, Filter.EventuallyEq.rfl⟩
    · obtain ⟨G₀, hG₀, rfl⟩ := hG
      obtain ⟨G₁, hG₁, rfl⟩ := hG₀
      obtain ⟨G₂, hG₂, hae⟩ := F.exists_comap_faFactorMap_ae_eq (identifiedSupport X.1) hG₁
      refine ⟨(poolStructureEquiv S ∘ Prod.fst) ⁻¹' G₂, ?_, ?_⟩
      · exact comap_faFactorMap_mixed_le_refinedCond F X _
          (by obtain ⟨s, hs, rfl⟩ := hG₂; exact ⟨s, hs, by rw [Set.preimage_comp]⟩)
      · exact (quasiMeasurePreserving_poolStructureEquiv_fst Q).preimage_ae_eq hae
  -- cylinders
  have hcyl : ∀ (t : Finset (FixBaseIndex S n))
      (f : FixBaseIndex S n → Set (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)),
      (∀ i ∈ t, MeasurableSet[fixBaseGen n i] (f i)) →
      ∃ E', MeasurableSet[refinedCond F n] E' ∧ E' =ᵐ[μ] ⋂ i ∈ t, f i := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro f _
      exact ⟨Set.univ, MeasurableSet.univ, by simp⟩
    | insert i t hit ih =>
      intro f hf
      obtain ⟨G', hG'm, hG'⟩ := hgen i (f i) (hf i (Finset.mem_insert_self i t))
      obtain ⟨E', hE'm, hE'⟩ := ih f fun j hj => hf j (Finset.mem_insert_of_mem hj)
      refine ⟨G' ∩ E', hG'm.inter hE'm, ?_⟩
      rw [Finset.set_biInter_insert]
      exact hG'.inter hE'
  refine MeasurableSpace.induction_on_inter (m := fixBase n)
    (C := fun E _ => ∃ E', MeasurableSet[refinedCond F n] E' ∧ E' =ᵐ[μ] E)
    fixBase_eq_generateFrom isPiSystem_fixBaseCylinders ?_ ?_ ?_ ?_ E hE
  · exact ⟨∅, @MeasurableSet.empty _ (refinedCond F n), Filter.EventuallyEq.rfl⟩
  · rintro H ⟨t, -, f, hf, rfl⟩
    exact hcyl t f hf
  · rintro H - ⟨E', hE'm, hE'⟩
    exact ⟨E'ᶜ, hE'm.compl, hE'.compl⟩
  · intro f _ _ ih
    choose g hgm hg using ih
    exact ⟨⋃ i, g i, MeasurableSet.iUnion hgm, Filter.EventuallyEq.countable_iUnion hg⟩

/-! ### Raw-factor mutuality -/

/-- The original-support finite-active factor, read on the pooled space. -/
noncomputable def originalFaFactor (A : RankSupport S n) :
    RelStructure S (PoolVertex S) × PooledRankLatentSpace S n →
      F.FaFactorSpace (doubleSupport A.1) :=
  F.faFactorMap (doubleSupport A.1) ∘ poolStructureEquiv S ∘ Prod.fst

omit [Countable S.Srt] [Countable S.Rel] in
theorem measurable_originalFaFactor (A : RankSupport S n) :
    Measurable (originalFaFactor F A) :=
  (F.measurable_faFactorMap' _).comp ((poolStructureEquiv S).measurable.comp measurable_fst)

omit [Countable S.Srt] [Countable S.Rel] in
/-- A measurable event of the original-support factor is a pooled finite-active fixing event of
the original image of the support. -/
theorem measurableSet_preimage_faFactorMap_doubleSupport (A : RankSupport S n)
    {s : Set (F.FaFactorSpace (doubleSupport A.1))} (hs : MeasurableSet s) :
    MeasurableSet[pooledFiniteActiveFixingAlgebra (supportImage (originalVertex S) A.1)]
      (poolStructureEquiv S ⁻¹' (F.faFactorMap (doubleSupport A.1) ⁻¹' s)) := by
  refine ⟨F.faFactorMap (doubleSupport A.1) ⁻¹' s, ?_, rfl⟩
  show MeasurableSet[RelStructure.finiteActiveFixingAlgebra
    (identifiedSupport (supportImage (originalVertex S) A.1))] _
  rw [identifiedSupport_supportImage_originalVertex]
  exact F.comap_faFactorMap_le _ _ ⟨s, hs, rfl⟩

open scoped Classical in
/-- **Mutual conditional independence of the original-support factors given `𝔅_fix`.** -/
theorem iCondIndepFun_originalFaFactor_fixBase (Q : PooledRankExtension C) :
    iCondIndepFun (fixBase n) (fixStage_le _) (originalFaFactor F)
      (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) := by
  haveI := C.isProbabilityMeasure_P
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul _ _ (measurable_originalFaFactor F)]
  intro T sets hsets
  let E : RankSupport S n → Set (RelStructure S (PoolVertex S)) := fun A =>
    if A ∈ T then poolStructureEquiv S ⁻¹' (F.faFactorMap (doubleSupport A.1) ⁻¹' sets A) else ∅
  have hE : ∀ A, MeasurableSet[pooledFiniteActiveFixingAlgebra
      (supportImage (originalVertex S) A.1)] (E A) := by
    intro A
    by_cases hA : A ∈ T
    · simp only [E, if_pos hA]
      exact measurableSet_preimage_faFactorMap_doubleSupport F A (hsets A hA)
    · simp only [E, if_neg hA]
      exact @MeasurableSet.empty _ (pooledFiniteActiveFixingAlgebra _)
  have hpre : ∀ A ∈ T, originalFaFactor F A ⁻¹' sets A = Prod.fst ⁻¹' E A := by
    intro A hA
    simp only [E, if_pos hA, originalFaFactor, Set.preimage_comp]
  have h := condExp_iInter_fixing_eq_prod Q T hE
  rw [Set.iInter₂_congr hpre]
  refine h.trans (Filter.EventuallyEq.of_eq ?_)
  exact Finset.prod_congr rfl fun A hA => by rw [hpre A hA]

open scoped Classical in
/-- The same mutuality, given the refined conditioning. -/
theorem iCondIndepFun_originalFaFactor_refinedCond (Q : PooledRankExtension C) :
    iCondIndepFun (refinedCond F n) (refinedCond_le F) (originalFaFactor F)
      (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) := by
  haveI := C.isProbabilityMeasure_P
  exact (iCondIndepFun_congr_of_ae_representable (refinedCond_le_fixBase F) (fixStage_le _)
    (fun _ hs => let ⟨t, ht, h⟩ := exists_refinedCond_ae_eq_of_fixBase F Q hs; ⟨t, ht, h.symm⟩)
    (measurable_originalFaFactor F)).mp (iCondIndepFun_originalFaFactor_fixBase F Q)

/-- **The comparison with the raw factor**: projecting the original-support finite-active factor
to the raw coordinates is, modulo `Q.law`, the raw factor map read on the original half. -/
theorem toRaw_comp_originalFaFactor_ae_eq (Q : PooledRankExtension C) (A : RankSupport S n) :
    F.toRaw A.1 ∘ originalFaFactor F A
      =ᵐ[(Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))]
        B.factorMap A.1 ∘ restrictOriginal S ∘ Prod.fst := by
  have h := (quasiMeasurePreserving_poolStructureEquiv_fst Q).ae_eq_comp
    (F.toRaw_faFactorMap_ae_eq A.1)
  refine h.trans (Filter.EventuallyEq.of_eq ?_)
  funext p
  simp only [Function.comp_apply]
  rw [restrict_doubleEmb_poolStructureEquiv]

/-- Conditional expectations of finite intersections and their products are stable under
almost-everywhere modification of the events. -/
private theorem condExp_iInter_eq_prod_congr_ae {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ι : Type*} (T : Finset ι) {s t : ι → Set Ω} (hst : ∀ i ∈ T, s i =ᵐ[μ] t i)
    (h : (μ⟦⋂ i ∈ T, s i | m⟧) =ᵐ[μ] ∏ i ∈ T, (μ⟦s i | m⟧)) :
    (μ⟦⋂ i ∈ T, t i | m⟧) =ᵐ[μ] ∏ i ∈ T, (μ⟦t i | m⟧) := by
  have hinter : (⋂ i ∈ T, s i) =ᵐ[μ] ⋂ i ∈ T, t i :=
    Filter.EventuallyEq.countable_bInter T.countable_toSet hst
  have hprod : (∏ i ∈ T, (μ⟦s i | m⟧)) =ᵐ[μ] ∏ i ∈ T, (μ⟦t i | m⟧) := by
    have : ∀ i ∈ T, (μ⟦s i | m⟧) =ᵐ[μ] (μ⟦t i | m⟧) := fun i hi =>
      condExp_congr_ae (indicator_ae_eq_of_ae_eq_set (hst i hi))
    filter_upwards [(Filter.eventually_all_finset T).mpr this] with x hx
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl fun i hi => hx i hi
  exact ((condExp_congr_ae (indicator_ae_eq_of_ae_eq_set hinter)).symm.trans h).trans hprod

/-- Mutual conditional independence is stable under almost-everywhere modification of the
functions. -/
private theorem iCondIndepFun_congr_ae {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {hm : m ≤ mΩ} {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {f g : ∀ i, Ω → β i} (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hfg : ∀ i, f i =ᵐ[μ] g i) (h : iCondIndepFun m hm f μ) : iCondIndepFun m hm g μ := by
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul _ _ hg]
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul _ _ hf] at h
  intro T sets hsets
  exact condExp_iInter_eq_prod_congr_ae T (fun i _ => (hfg i).preimage (sets i)) (h T hsets)

/-- Mutual conditional independence of the raw factors read on the original half, given the
refined conditioning, on the pooled space. -/
theorem iCondIndepFun_factorMap_restrictOriginal_refinedCond (Q : PooledRankExtension C) :
    iCondIndepFun (refinedCond F n) (refinedCond_le F)
      (fun A : RankSupport S n => B.factorMap A.1 ∘ restrictOriginal S ∘ Prod.fst)
      (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) := by
  haveI := C.isProbabilityMeasure_P
  have h := Kernel.iIndepFun.comp (iCondIndepFun_originalFaFactor_refinedCond F Q)
    (fun A : RankSupport S n => F.toRaw A.1) (fun A => F.measurable_toRaw A.1)
  exact iCondIndepFun_congr_ae
    (fun A => (F.measurable_toRaw A.1).comp (measurable_originalFaFactor F A))
    (fun A => (B.measurable_factorMap' A.1).comp ((measurable_restrict _).comp measurable_fst))
    (fun A => toRaw_comp_originalFaFactor_ae_eq F Q A) h

/-- **The kernel seam's input.** Under the refined law, the raw factors at the rank-`n` supports
are mutually conditionally independent given the refined base. The conditioning is the refined
base; nothing here descends to the Austin base. -/
theorem iCondIndepFun_factorMap_refinedLaw (Q : PooledRankExtension C) :
    iCondIndepFun (MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × RefinedBaseSpace F n → _) inferInstance)
      measurable_snd.comap_le
      (fun A : RankSupport S n => B.factorMap A.1 ∘ Prod.fst) (refinedLaw F Q) := by
  haveI := C.isProbabilityMeasure_P
  refine Austin.iCondIndepFun_of_map (measurable_refinedObs F) measurable_snd.comap_le
    (fun A : RankSupport S n => (B.measurable_factorMap' A.1).comp measurable_fst) ?_
  refine Austin.iCondIndepFun_congr_cond
    (iCondIndepFun_factorMap_restrictOriginal_refinedCond F Q) ?_ _
  rw [refinedCond, MeasurableSpace.comap_comp]
  rfl

/-- The exact layers, by their measurable projection from the raw factor. -/
theorem iCondIndepFun_exactMap_refinedLaw (Q : PooledRankExtension C) :
    iCondIndepFun (MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × RefinedBaseSpace F n → _) inferInstance)
      measurable_snd.comap_le
      (fun A : RankSupport S n => B.exactMap A.1 ∘ Prod.fst) (refinedLaw F Q) :=
  Kernel.iIndepFun.comp (iCondIndepFun_factorMap_refinedLaw F Q)
    (fun A : RankSupport S n => fun x => (B.factorSpaceProdEquiv A.1 x).2)
    (fun A => (B.factorSpaceProdEquiv A.1).measurable.snd)

/-- **Arbitrary raw fixing events**, eventwise: for a choice of a `fixingAlgebra`-event at each
rank-`n` support, the conditional probability of any finite intersection under the refined law
is the product of the conditional probabilities, by the raw basis's representation theorem. -/
theorem condExp_iInter_fixing_eq_prod_refinedLaw (Q : PooledRankExtension C)
    (T : Finset (RankSupport S n)) {E : RankSupport S n → Set (RelStructure S (Vinfinite S))}
    (hE : ∀ A, MeasurableSet[RelStructure.fixingAlgebra A.1] (E A)) :
    ((refinedLaw F Q)⟦⋂ A ∈ T, Prod.fst ⁻¹' E A | MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × RefinedBaseSpace F n → _) inferInstance⟧)
      =ᵐ[refinedLaw F Q]
    ∏ A ∈ T, ((refinedLaw F Q)⟦Prod.fst ⁻¹' E A | MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × RefinedBaseSpace F n → _) inferInstance⟧) := by
  classical
  choose E' hE'm hE' using fun A => B.exists_comap_factorMap_ae_eq A.1 (hE A)
  choose s hs hsE using fun A => hE'm A
  have hq : Measure.QuasiMeasurePreserving
      (Prod.fst : RelStructure S (Vinfinite S) × RefinedBaseSpace F n → _) (refinedLaw F Q)
      (M.law : Measure (RelStructure S (Vinfinite S))) :=
    (MeasurePreserving.mk measurable_fst (refinedLaw_map_fst F Q)).quasiMeasurePreserving
  have h := (iCondIndepFun_iff_condExp_inter_preimage_eq_mul _ _
    (fun A : RankSupport S n => (B.measurable_factorMap' A.1).comp measurable_fst)).mp
    (iCondIndepFun_factorMap_refinedLaw F Q) T (sets := s) (fun A _ => hs A)
  refine condExp_iInter_eq_prod_congr_ae T (fun A _ => ?_) h
  have : (B.factorMap A.1 ∘ Prod.fst) ⁻¹' s A =
      (Prod.fst : RelStructure S (Vinfinite S) × RefinedBaseSpace F n → _) ⁻¹' E' A := by
    rw [← hsE A, Set.preimage_comp]
  rw [this]
  exact hq.preimage_ae_eq (hE' A)

end InfiniteRelExchangeableLaw

end RelSignature
