/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRankOneCoupling
import Graphon.RelSingletonPeel
import Graphon.ForMathlib.CondExpRepresentable
import Graphon.ForMathlib.CondIndepRefine
import Graphon.ForMathlib.CondIndepSup

/-!
# The rank-one conditioning ladder (R4 converse piece 3, #107)

Under the rank-one coupling clauses, the singleton blocks — composed with the structure
projection — are **mutually** conditionally independent given the full latent σ-algebra
`comap Prod.snd`. This is the support-free core of the `screening` field; the per-support
statement is a later specialization.

## The ladder

The conditioning algebra climbs and then descends, each rung by a merged tool:

1. the singleton peel (#173) under the law, pulled to the coupling along `Prod.fst` (#175) —
   conditioning `invariantAlgebra.comap fst`;
2. **down** to `comap (lowerFactorMap 1 ∘ fst)` by the representable-conditioning transfer
   (#163), whose hypothesis is the eventwise generation of the rank-one factor (#157) pulled
   along `fst`;
3. **up** to the join with the latent algebra by the independent-refinement theorem (#174),
   whose hypothesis is the coupling's conditional-independence clause (#161/#177) joined
   freely with the conditioning (#176);
4. **down** to the latent algebra alone by #163 again, the representability of the join
   supplied by the resolution identity and `eventuallyMeasurableSet_sup` (#176).

Every conditioning move is modulo the coupling measure. No identification of the latent
σ-algebra with the invariant algebra is asserted anywhere — the available statements are
eventwise, and that is all the ladder uses.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

namespace CoherentBasis

universe u

variable {S : RelSignature.{u}} {M : InfiniteRelExchangeableLaw S} (B : CoherentBasis M)

open scoped Classical in
/-- The singleton block at `v`, read through the structure coordinate of the rank-one
coupling space. Named so the family is fully typed at every use site. -/
def singletonBlockRead (S : RelSignature.{u}) (v : Σ s : S.Srt, Vinfinite S s) :
    RelStructure S (Vinfinite S) × RankLatentSpace S 1 →
      BlockSpace ({v} : Finset (Σ s : S.Srt, Vinfinite S s)) :=
  blockMap ({v} : Finset (Σ s : S.Srt, Vinfinite S s)) ∘ Prod.fst

open scoped Classical in
theorem measurable_singletonBlockRead [Countable S.Rel] (v : Σ s : S.Srt, Vinfinite S s) :
    Measurable (singletonBlockRead S v) :=
  (measurable_blockMap _).comp measurable_fst

open scoped Classical in
/-- **The conditioning ladder.** Under a coupling of the law with the rank-one latents —
structure marginal the law, rank-one factor resolved by a measurable latent read, structure and
latent conditionally independent given the factor — the singleton blocks are **mutually**
conditionally independent given the full latent σ-algebra. -/
theorem iCondIndepFun_blockMap_singleton_comap_snd [Fintype S.Srt] [Countable S.Rel]
    {P : Measure (RelStructure S (Vinfinite S) × RankLatentSpace S 1)}
    [IsProbabilityMeasure P]
    (hfst : P.map Prod.fst = (M.law : Measure (RelStructure S (Vinfinite S))))
    {g : RankLatentSpace S 1 → B.LowerFactorSpace 1} (hg : Measurable g)
    (hres : B.lowerFactorMap 1 ∘ Prod.fst =ᵐ[P] g ∘ Prod.snd)
    (hci : CondIndepFun (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance)
      ((B.measurable_lowerFactorMap' 1).comp measurable_fst).comap_le Prod.fst Prod.snd P) :
    iCondIndepFun (MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
        RankLatentSpace S 1 → RankLatentSpace S 1) inferInstance)
      measurable_snd.comap_le
      (singletonBlockRead S) P := by
  classical
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  have hMP : MeasurePreserving Prod.fst P (M.law : Measure (RelStructure S (Vinfinite S))) :=
    ⟨measurable_fst, hfst⟩
  have hblockmeas : ∀ v : Σ s : S.Srt, Vinfinite S s,
      Measurable (singletonBlockRead S v) :=
    fun v => measurable_singletonBlockRead v
  -- rung 1: the peel, pulled to the coupling along `fst`
  have h1 : iCondIndepFun (RelStructure.invariantAlgebra.comap Prod.fst)
      ((MeasurableSpace.comap_mono (RelStructure.invariantAlgebra_le (S := S))).trans
        (measurable_iff_comap_le.mp hMP.measurable))
      (singletonBlockRead S) P :=
    iCondIndepFun_comp_measurePreserving hMP (RelStructure.invariantAlgebra_le (S := S))
      (fun v => measurable_blockMap _) (M.iCondIndepFun_blockMap_singleton)
  -- rung 2: down to the rank-one factor pullback, by eventwise representability
  have hFI : MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance ≤
      RelStructure.invariantAlgebra.comap
        (Prod.fst : RelStructure S (Vinfinite S) × RankLatentSpace S 1 → _) := by
    rw [← MeasurableSpace.comap_comp]
    refine MeasurableSpace.comap_mono ?_
    have hle := B.comap_lowerFactorMap_le 1
    rwa [RelStructure.lowerRankAlgebra_one] at hle
  have hrepFI : ∀ s, MeasurableSet[RelStructure.invariantAlgebra.comap
      (Prod.fst : RelStructure S (Vinfinite S) × RankLatentSpace S 1 → _)] s →
      ∃ t, MeasurableSet[MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance] t ∧
        s =ᵐ[P] t := by
    rintro s ⟨E, hE, rfl⟩
    obtain ⟨E', hE'meas, hE'ae⟩ := B.exists_comap_lowerFactorMap_one_ae_eq hE
    obtain ⟨D, hD, rfl⟩ := hE'meas
    refine ⟨(B.lowerFactorMap 1 ∘ Prod.fst) ⁻¹' D, ⟨D, hD, rfl⟩, ?_⟩
    refine Filter.eventuallyEq_set.mpr ?_
    have hpull := hMP.quasiMeasurePreserving.tendsto_ae.eventually
      (Filter.eventuallyEq_set.mp hE'ae)
    filter_upwards [hpull] with p hp
    simpa [Set.preimage_comp] using hp.symm
  have h2 : iCondIndepFun
      (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance)
      (hFI.trans ((MeasurableSpace.comap_mono (RelStructure.invariantAlgebra_le (S := S))).trans
        (measurable_iff_comap_le.mp hMP.measurable)))
      (singletonBlockRead S) P :=
    (iCondIndepFun_congr_of_ae_representable hFI _ hrepFI hblockmeas).mp h1
  -- rung 3: up to the join with the latent algebra, by independent refinement
  have hciAlg : CondIndep (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance)
      (MeasurableSpace.comap (Prod.fst : RelStructure S (Vinfinite S) ×
        RankLatentSpace S 1 → _) inferInstance)
      (MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
        RankLatentSpace S 1 → _) inferInstance)
      ((B.measurable_lowerFactorMap' 1).comp measurable_fst).comap_le P :=
    (condIndepFun_iff_condIndep _ _ _ _ _).mp hci
  have hsupBlocks : (⨆ v : Σ s : S.Srt, Vinfinite S s, MeasurableSpace.comap
      (singletonBlockRead S v) inferInstance) ≤
      MeasurableSpace.comap (Prod.fst : RelStructure S (Vinfinite S) ×
        RankLatentSpace S 1 → _) inferInstance :=
    iSup_le fun v => by
      rw [show singletonBlockRead S v
            = blockMap ({v} : Finset (Σ s : S.Srt, Vinfinite S s)) ∘ Prod.fst from rfl,
        ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (measurable_iff_comap_le.mp (measurable_blockMap _))
  have h3 : CondIndep (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance)
      (⨆ v : Σ s : S.Srt, Vinfinite S s, MeasurableSpace.comap
        (singletonBlockRead S v) inferInstance)
      (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance ⊔
        MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
          RankLatentSpace S 1 → _) inferInstance)
      ((B.measurable_lowerFactorMap' 1).comp measurable_fst).comap_le P := by
    refine CondIndep.sup_right ?_ (hsupBlocks.trans (measurable_iff_comap_le.mp measurable_fst))
      measurable_snd.comap_le
    exact condIndep_of_condIndep_of_le_left hciAlg hsupBlocks
  have h4 : iCondIndepFun
      (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance ⊔
        MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
          RankLatentSpace S 1 → _) inferInstance)
      (sup_le (((B.measurable_lowerFactorMap' 1).comp measurable_fst).comap_le)
        measurable_snd.comap_le)
      (singletonBlockRead S) P := by
    rw [iCondIndepFun_iff_iCondIndep] at h2 ⊢
    exact iCondIndep_of_condIndep_iSup _ _ le_sup_left
      (fun v => (hblockmeas v).comap_le) h2 h3
  -- rung 4: down to the latent algebra alone, by representability of the join
  have hrepJ : ∀ s, MeasurableSet[MeasurableSpace.comap
      (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance ⊔
        MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
          RankLatentSpace S 1 → _) inferInstance] s →
      ∃ t, MeasurableSet[MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
        RankLatentSpace S 1 → _) inferInstance] t ∧ s =ᵐ[P] t := by
    refine fun s hs => eventuallyMeasurableSet_sup ?_ hs
    rintro u ⟨D, hD, rfl⟩
    refine ⟨(g ∘ Prod.snd) ⁻¹' D, ⟨g ⁻¹' D, hg hD, by rw [Set.preimage_comp]⟩, ?_⟩
    refine Filter.eventuallyEq_set.mpr ?_
    filter_upwards [hres] with p hp
    simp only [Set.mem_preimage, Function.comp_apply]
    rw [show B.lowerFactorMap 1 p.1 = g p.2 from hp]
  exact (iCondIndepFun_congr_of_ae_representable le_sup_right _ hrepJ hblockmeas).mp h4

end CoherentBasis

end RelSignature
