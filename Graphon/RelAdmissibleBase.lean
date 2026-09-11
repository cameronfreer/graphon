/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelAdmissible
import Graphon.RelRankOneRepresentation

/-!
# The admissible rank-one base (R4 converse, #107)

Every exchangeable law has an **admissible** rank-one representation, under ambient countability
only, with nullary relations and nondissociated laws allowed:
`exists_admissible_rankRepresentation_one`.

The route, in the order it is banked:

* **Source-level mutuality for disjoint finite sets.** The singleton peel generalizes to the full
  induced structures on a family with small overlap at rank one, i.e. pairwise disjoint sets:
  each induced structure is measurable for the fixing algebra of its set, and at each insertion
  the target set and the union of the accumulated sets meet in the empty set, so every stage
  conditions on the same invariant σ-algebra. This is
  `iCondIndepFun_inducedMap_of_smallOverlap_one`.
* **The conditioning ladder**, generalized from the singleton blocks to any family that is
  mutually conditionally independent given the invariant σ-algebra under the law: eventwise
  representation by the rank-one factor, independent refinement through the canonical
  coupling's conditional-independence clause, and the factor's recovery from the latent.
  This is `iCondIndepFun_comap_snd_of_invariant`.
* **Assembly** with the existing construction `rankOneRepOf`, whose coupling is the canonical
  rank-one latent coupling. No field is added and no arbitrary rank-one representation is
  assumed admissible.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

universe u

variable {S : RelSignature.{u}}

open scoped Classical in
/-- **The full induced structure on `A` is measurable for `fixingAlgebra A`**: every coordinate
inside `A` is fixed by a relabeling fixing `A` pointwise. -/
theorem measurable_inducedMap_fixingAlgebra [Countable S.Rel]
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measurable[RelStructure.fixingAlgebra A] (inducedMap (S := S) A) := by
  classical
  have key : ∀ cc : RelCoord S (Vinfinite S), cc.support ⊆ A →
      MeasurableSet[RelStructure.fixingAlgebra A]
        {X : RelStructure S (Vinfinite S) | X cc = true} := by
    intro cc hcc
    refine ⟨?_, fun σ hσ => ?_⟩
    · have hm : MeasurableSet
          ((fun X : RelStructure S (Vinfinite S) => X cc) ⁻¹' ({true} : Set Bool)) :=
        (measurable_pi_apply cc) (measurableSet_singleton true)
      exact hm
    have hfun : (fun i => (σ (S.argSort cc.1 i)) (cc.2 i)) = cc.2 := by
      funext i
      have hv : cc.taggedValue i ∈ A := hcc ((RelCoord.mem_support_iff cc _).mpr ⟨i, rfl⟩)
      exact hσ.2 _ hv
    have hcoord : RelCoord.map (fun s => ⇑(σ s)) cc = cc := by
      show (⟨cc.1, fun i => (σ (S.argSort cc.1 i)) (cc.2 i)⟩ : RelCoord S (Vinfinite S)) = cc
      rw [hfun]
    ext X
    show (RelStructure.relabel σ X) cc = true ↔ X cc = true
    rw [show (RelStructure.relabel σ X) cc = X (RelCoord.map (fun s => ⇑(σ s)) cc) from rfl,
      hcoord]
  letI : MeasurableSpace (RelStructure S (Vinfinite S)) := RelStructure.fixingAlgebra A
  refine measurable_pi_iff.mpr fun c => measurable_to_bool ?_
  convert key c.1 c.2 using 1
  ext X
  simp [inducedMap]

namespace InfiniteRelExchangeableLaw

open scoped Classical in
/-- Small overlap at rank one is pairwise disjointness. -/
theorem disjoint_of_smallOverlap_one {k : ℕ} {A : Fin k → Finset (Σ s : S.Srt, Vinfinite S s)}
    (hA : SmallOverlap 1 A) {i j : Fin k} (hij : i ≠ j) : A i ∩ A j = ∅ := by
  classical
  ext x
  simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
  intro hxi hxj
  have := hA i j hij {x} (Finset.singleton_subset_iff.mpr hxi) (Finset.singleton_subset_iff.mpr hxj)
  simp at this

open scoped Classical in
/-- **Source-level mutuality for disjoint finite sets.** The full induced structures on a family
with small overlap at rank one are mutually conditionally independent given the invariant
σ-algebra, for an arbitrary exchangeable law. At each insertion the target set and the union of
the accumulated sets meet in the empty set. -/
theorem iCondIndepFun_inducedMap_of_smallOverlap_one [Countable S.Rel]
    (M : InfiniteRelExchangeableLaw S) {k : ℕ} (A : Fin k → Finset (Σ s : S.Srt, Vinfinite S s))
    (hA : SmallOverlap 1 A) :
    iCondIndepFun RelStructure.invariantAlgebra (RelStructure.invariantAlgebra_le (S := S))
      (fun i => inducedMap (S := S) (A i)) (M.law : Measure (RelStructure S (Vinfinite S))) := by
  classical
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  have hY : ∀ i, Measurable[RelStructure.fixingAlgebra (A i)] (inducedMap (S := S) (A i)) :=
    fun i => measurable_inducedMap_fixingAlgebra (A i)
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul _ _
    fun i => (hY i).mono (RelStructure.fixingAlgebra_le _) le_rfl]
  intro T sets
  induction T using Finset.induction_on with
  | empty =>
      intro _
      simp only [Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ, Finset.prod_empty,
        Set.indicator_univ]
      rw [condExp_const (μ := (M.law : Measure (RelStructure S (Vinfinite S))))
        RelStructure.invariantAlgebra_le (1 : ℝ)]
      rfl
  | insert v s hvs ih =>
      intro hsets
      have ihs := ih fun i hi => hsets i (Finset.mem_insert_of_mem hi)
      -- the accumulated event is measurable for the fixing algebra of the accumulated union
      have hE : MeasurableSet[RelStructure.fixingAlgebra (s.biUnion A)]
          (⋂ i ∈ s, inducedMap (S := S) (A i) ⁻¹' sets i) := by
        refine Finset.measurableSet_biInter s fun i hi => ?_
        exact RelStructure.fixingAlgebra_mono (Finset.subset_biUnion_of_mem A hi) _
          (hY i (hsets i (Finset.mem_insert_of_mem hi)))
      have hF : MeasurableSet[RelStructure.fixingAlgebra (A v)]
          (inducedMap (S := S) (A v) ⁻¹' sets v) :=
        hY v (hsets v (Finset.mem_insert_self v s))
      -- the inserted set is disjoint from the accumulated union
      have hinter : A v ∩ s.biUnion A = ∅ := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.notMem_empty, iff_false, not_and,
          not_exists]
        intro hxv i hi hxi
        have hne : v ≠ i := fun h => hvs (h ▸ hi)
        have := disjoint_of_smallOverlap_one hA hne
        have hx : x ∈ A v ∩ A i := Finset.mem_inter.mpr ⟨hxv, hxi⟩
        rw [this] at hx
        exact Finset.notMem_empty x hx
      have hci := M.condIndep_fixingAlgebra (A v) (s.biUnion A)
      rw [condIndep_iff _ _ _ _ (RelStructure.fixingAlgebra_le (A v))
        (RelStructure.fixingAlgebra_le (s.biUnion A))] at hci
      have key := hci _ _ hF hE
      rw [hinter, RelStructure.fixingAlgebra_empty] at key
      rw [Finset.set_biInter_insert, Finset.prod_insert hvs]
      exact key.trans (Filter.EventuallyEq.mul (Filter.EventuallyEq.refl _ _) ihs)

end InfiniteRelExchangeableLaw

namespace CoherentBasis

variable {M : InfiniteRelExchangeableLaw S} (B : CoherentBasis M) [Countable S.Srt]

open scoped Classical in
/-- **The conditioning ladder, generalized.** Under a coupling of the law with the rank-one
latents — structure marginal the law, rank-one factor resolved by a measurable latent read,
structure and latent conditionally independent given the factor — any family of structure
observations that is mutually conditionally independent given the invariant σ-algebra under
the law is mutually conditionally independent given the full latent σ-algebra under the
coupling. The canonical coupling's conditional-independence clause is consumed at the
refinement rung; recovery alone would not justify the extra information in the latent. -/
theorem iCondIndepFun_comap_snd_of_invariant [Countable S.Rel]
    {P : Measure (RelStructure S (Vinfinite S) × RankLatentSpace S 1)}
    [IsProbabilityMeasure P]
    (hfst : P.map Prod.fst = (M.law : Measure (RelStructure S (Vinfinite S))))
    {g : RankLatentSpace S 1 → B.LowerFactorSpace 1} (hg : Measurable g)
    (hres : B.lowerFactorMap 1 ∘ Prod.fst =ᵐ[P] g ∘ Prod.snd)
    (hci : CondIndepFun (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance)
      ((B.measurable_lowerFactorMap' 1).comp measurable_fst).comap_le Prod.fst Prod.snd P)
    {ι : Type*} {γ : ι → Type*} [∀ i, MeasurableSpace (γ i)]
    {Y : ∀ i, RelStructure S (Vinfinite S) → γ i} (hY : ∀ i, Measurable (Y i))
    (hinv : iCondIndepFun RelStructure.invariantAlgebra (RelStructure.invariantAlgebra_le (S := S))
      Y (M.law : Measure (RelStructure S (Vinfinite S)))) :
    iCondIndepFun (MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
        RankLatentSpace S 1 → RankLatentSpace S 1) inferInstance)
      measurable_snd.comap_le (fun i => Y i ∘ Prod.fst) P := by
  classical
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  have hMP : MeasurePreserving Prod.fst P (M.law : Measure (RelStructure S (Vinfinite S))) :=
    ⟨measurable_fst, hfst⟩
  have hmeas : ∀ i, Measurable (Y i ∘ (Prod.fst : RelStructure S (Vinfinite S) ×
      RankLatentSpace S 1 → _)) := fun i => (hY i).comp measurable_fst
  -- rung 1: the source statement, pulled to the coupling along `fst`
  have h1 : iCondIndepFun (RelStructure.invariantAlgebra.comap Prod.fst)
      ((MeasurableSpace.comap_mono (RelStructure.invariantAlgebra_le (S := S))).trans
        (measurable_iff_comap_le.mp hMP.measurable))
      (fun i => Y i ∘ Prod.fst) P :=
    iCondIndepFun_comp_measurePreserving hMP (RelStructure.invariantAlgebra_le (S := S)) hY hinv
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
      (fun i => Y i ∘ Prod.fst) P :=
    (iCondIndepFun_congr_of_ae_representable hFI _ hrepFI hmeas).mp h1
  -- rung 3: up to the join with the latent algebra, by independent refinement
  have hciAlg : CondIndep (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance)
      (MeasurableSpace.comap (Prod.fst : RelStructure S (Vinfinite S) ×
        RankLatentSpace S 1 → _) inferInstance)
      (MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
        RankLatentSpace S 1 → _) inferInstance)
      ((B.measurable_lowerFactorMap' 1).comp measurable_fst).comap_le P :=
    (condIndepFun_iff_condIndep _ _ _ _ _).mp hci
  have hsupY : (⨆ i, MeasurableSpace.comap (Y i ∘ Prod.fst) inferInstance) ≤
      MeasurableSpace.comap (Prod.fst : RelStructure S (Vinfinite S) ×
        RankLatentSpace S 1 → _) inferInstance :=
    iSup_le fun i => by
      rw [← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (measurable_iff_comap_le.mp (hY i))
  have h3 : CondIndep (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance)
      (⨆ i, MeasurableSpace.comap (Y i ∘ Prod.fst) inferInstance)
      (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance ⊔
        MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
          RankLatentSpace S 1 → _) inferInstance)
      ((B.measurable_lowerFactorMap' 1).comp measurable_fst).comap_le P := by
    refine CondIndep.sup_right ?_ (hsupY.trans (measurable_iff_comap_le.mp measurable_fst))
      measurable_snd.comap_le
    exact condIndep_of_condIndep_of_le_left hciAlg hsupY
  have h4 : iCondIndepFun
      (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance ⊔
        MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
          RankLatentSpace S 1 → _) inferInstance)
      (sup_le (((B.measurable_lowerFactorMap' 1).comp measurable_fst).comap_le)
        measurable_snd.comap_le)
      (fun i => Y i ∘ Prod.fst) P := by
    rw [iCondIndepFun_iff_iCondIndep] at h2 ⊢
    exact iCondIndep_of_condIndep_iSup _ _ le_sup_left
      (fun i => (hmeas i).comap_le) h2 h3
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
  exact (iCondIndepFun_congr_of_ae_representable le_sup_right _ hrepJ hmeas).mp h4

end CoherentBasis

/-- **The admissible rank-one base**: every exchangeable law has an admissible rank-one
representation, the canonical construction `rankOneRepOf`. -/
theorem InfiniteRelExchangeableLaw.exists_admissible_rankRepresentation_one
    [Countable S.Srt] [Countable S.Rel] (M : InfiniteRelExchangeableLaw S) :
    ∃ C : M.RankRepresentation 1, C.Admissible := by
  classical
  obtain ⟨B⟩ := M.nonempty_coherentBasis
  obtain ⟨f, g, hg, hprob, hfst, hsnd, hinv, hres, hci⟩ := B.exists_rankOneLatentCoupling
  refine ⟨B.rankOneRepOf f g hg hprob hfst hsnd hinv hres (hci measurable_id),
    fun k A hA => ?_⟩
  haveI := hprob
  exact B.iCondIndepFun_comap_snd_of_invariant hfst hg hres (hci measurable_id)
    (fun i => measurable_inducedMap (A i))
    (M.iCondIndepFun_inducedMap_of_smallOverlap_one A hA)

end RelSignature
