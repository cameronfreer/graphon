/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelTernaryParityRegression
import Graphon.RelInsertion

/-!
# The ternary parity regression: base removal fails (R4 converse, #107, #197)

The explicit failure, on the pooled extension of the ternary parity representation, of the
statement that conditioning a rank-two fixing event on the refined base `𝔅_fix` agrees with
conditioning on the original latents. Two mixed pair events, at the supports `{u, s}` and
`{v, s}` with `s` a spare vertex, both lie in `𝔅_fix`, and their symmetric difference is,
almost surely, the original pair event at `{u, v}`: so the latter is `𝔅_fix`-measurable modulo
the law and its conditional probability given `𝔅_fix` is its own indicator. Given the original
latents, which are independent of the structure, it is the constant `1/2`.

Several mixed fixing factors can jointly reveal original pair information even when the
singleton fixing factors are trivial.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

namespace TernaryParityRegression

open InfiniteRelExchangeableLaw

/-- The pooled pair event: some pooled third vertex witnesses the relation. -/
def pooledPairEvent (a b : PoolVertex ternarySig ()) :
    Set (RelStructure ternarySig (PoolVertex ternarySig)) :=
  {Y | ∃ w, w ≠ a ∧ w ≠ b ∧ Y (ternaryCoord a b w) = true}

/-- The identification carries the pooled pair event to the pair event at the identified
vertices. -/
theorem preimage_pairEvent_poolStructureEquiv (a b : PoolVertex ternarySig ()) :
    poolStructureEquiv ternarySig ⁻¹'
        pairEvent (poolVertexEquiv ternarySig () a) (poolVertexEquiv ternarySig () b) =
      pooledPairEvent a b := by
  ext Y
  simp only [Set.mem_preimage, pairEvent, pooledPairEvent, Set.mem_setOf_eq]
  have hcoord : ∀ z : ℕ, poolStructureEquiv ternarySig Y
      (ternaryCoord (poolVertexEquiv ternarySig () a) (poolVertexEquiv ternarySig () b) z) =
      Y (ternaryCoord a b ((poolVertexEquiv ternarySig ()).symm z)) := by
    intro z
    show Y (RelCoord.map (fun s => ((poolVertexEquiv ternarySig s).symm : ℕ → _)) _) = _
    congr 1
    refine Sigma.ext rfl (heq_of_eq ?_)
    funext i; fin_cases i
    · exact Equiv.symm_apply_apply _ _
    · exact Equiv.symm_apply_apply _ _
    · rfl
  constructor
  · rintro ⟨z, hza, hzb, hz⟩
    refine ⟨(poolVertexEquiv ternarySig ()).symm z, ?_, ?_, ?_⟩
    · intro h; apply hza; rw [← h, Equiv.apply_symm_apply]
    · intro h; apply hzb; rw [← h, Equiv.apply_symm_apply]
    · rw [← hcoord]; exact hz
  · rintro ⟨w, hwa, hwb, hw⟩
    refine ⟨poolVertexEquiv ternarySig () w, ?_, ?_, ?_⟩
    · exact (poolVertexEquiv ternarySig ()).injective.ne hwa
    · exact (poolVertexEquiv ternarySig ()).injective.ne hwb
    · rw [hcoord, Equiv.symm_apply_apply]; exact hw

/-- The pooled pair support. -/
def pooledPair (a b : PoolVertex ternarySig ()) : Finset (Σ _ : Unit, PoolVertex ternarySig ()) :=
  {⟨(), a⟩, ⟨(), b⟩}

theorem identifiedSupport_pooledPair (a b : PoolVertex ternarySig ()) :
    identifiedSupport (S := ternarySig) (pooledPair a b) =
      pairSupport (poolVertexEquiv ternarySig () a) (poolVertexEquiv ternarySig () b) := by
  classical
  ext v
  simp only [identifiedSupport, supportImage, pooledPair, pairSupport, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨w, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨⟨(), a⟩, Or.inl rfl, rfl⟩
    · exact ⟨⟨(), b⟩, Or.inr rfl, rfl⟩

/-- The pooled pair event lies in the pooled finite-active fixing algebra of its support. -/
theorem measurableSet_pooled_pooledPairEvent (a b : PoolVertex ternarySig ()) :
    MeasurableSet[pooledFiniteActiveFixingAlgebra (pooledPair a b)] (pooledPairEvent a b) := by
  show MeasurableSet[MeasurableSpace.comap (poolStructureEquiv ternarySig)
    (RelStructure.finiteActiveFixingAlgebra (identifiedSupport (S := ternarySig)
      (pooledPair a b)))] _
  rw [identifiedSupport_pooledPair]
  exact ⟨_, RelStructure.fixingAlgebra_le_finiteActiveFixingAlgebra _ _
    (measurableSet_fixingAlgebra_pairEvent _ _), preimage_pairEvent_poolStructureEquiv a b⟩

/-- The three vertices: two original, one spare. -/
abbrev o₀ : PoolVertex ternarySig () := Sum.inl 0
abbrev o₁ : PoolVertex ternarySig () := Sum.inl 1
abbrev s₀ : PoolVertex ternarySig () := Sum.inr 0

theorem equiv_o₀ : poolVertexEquiv ternarySig () o₀ = 0 := by
  simp [poolVertexEquiv, Equiv.natSumNatEquivNat_apply]
theorem equiv_o₁ : poolVertexEquiv ternarySig () o₁ = 2 := by
  simp [poolVertexEquiv, Equiv.natSumNatEquivNat_apply]
theorem equiv_s₀ : poolVertexEquiv ternarySig () s₀ = 1 := by
  simp [poolVertexEquiv, Equiv.natSumNatEquivNat_apply]

/-- The mixed support `{o₀, s₀}` as a mixed cluster index. -/
def mixed₀ : MixedClusterIndex ternarySig 2 :=
  ⟨pooledPair o₀ s₀, by decide, ⟨⟨(), s₀⟩, by simp [pooledPair], rfl⟩⟩

/-- The mixed support `{o₁, s₀}` as a mixed cluster index. -/
def mixed₁ : MixedClusterIndex ternarySig 2 :=
  ⟨pooledPair o₁ s₀, by decide, ⟨⟨(), s₀⟩, by simp [pooledPair], rfl⟩⟩

/-- The pooled extension of the ternary rank-two representation. -/
noncomputable abbrev Q : PooledRankExtension rankTwoRep := rankTwoRep.pooledExtension

/-- The pooled law. -/
noncomputable abbrev μQ : Measure (RelStructure ternarySig (PoolVertex ternarySig) ×
    PooledRankLatentSpace ternarySig 2) :=
  (Q.law : Measure (RelStructure ternarySig (PoolVertex ternarySig) ×
    PooledRankLatentSpace ternarySig 2))

instance : IsProbabilityMeasure μQ := Q.law.2

/-- The identified structure. -/
noncomputable abbrev idStructure : RelStructure ternarySig (PoolVertex ternarySig) ×
    PooledRankLatentSpace ternarySig 2 → RelStructure ternarySig (Vinfinite ternarySig) :=
  poolStructureEquiv ternarySig ∘ Prod.fst

theorem measurable_idStructure : Measurable idStructure :=
  (poolStructureEquiv ternarySig).measurable.comp measurable_fst

/-- The identified latents. -/
noncomputable abbrev idLatents : RelStructure ternarySig (PoolVertex ternarySig) ×
    PooledRankLatentSpace ternarySig 2 → RankLatentSpace ternarySig 2 :=
  latentRestrictOver (fun s => (poolVertexEquiv ternarySig s).symm.toEmbedding) 2 ∘ Prod.snd

theorem measurable_idLatents : Measurable idLatents :=
  (measurable_latentRestrictOver _ 2).comp measurable_snd

theorem map_idPair : μQ.map (fun p => (idStructure p, idLatents p)) = rankTwoCoupling := by
  have h := Q.map_poolVertexEquiv
  exact h

theorem map_idStructure : μQ.map idStructure = ternaryLaw := by
  rw [show idStructure = Prod.fst ∘ fun p => (idStructure p, idLatents p) from rfl,
    ← Measure.map_map measurable_fst (measurable_idStructure.prodMk measurable_idLatents),
    map_idPair,
    rankTwoCoupling_map_fst]

theorem map_idLatents : μQ.map idLatents = rankLatentSource ternarySig 2 := by
  rw [show idLatents = Prod.snd ∘ fun p => (idStructure p, idLatents p) from rfl,
    ← Measure.map_map measurable_snd (measurable_idStructure.prodMk measurable_idLatents),
    map_idPair,
    rankTwoCoupling_map_snd]

/-- The identified structure and latents are independent under the pooled law. -/
theorem indepFun_idStructure_idLatents : IndepFun idStructure idLatents μQ := by
  refine (indepFun_iff_map_prod_eq_prod_map_map measurable_idStructure.aemeasurable
    measurable_idLatents.aemeasurable).mpr ?_
  rw [map_idPair, map_idStructure, map_idLatents]
  rfl

/-- The pooled pair event at the two original vertices, read on the pooled space. -/
noncomputable abbrev F : Set (RelStructure ternarySig (PoolVertex ternarySig) ×
    PooledRankLatentSpace ternarySig 2) :=
  Prod.fst ⁻¹' pooledPairEvent o₀ o₁

theorem F_eq : F = idStructure ⁻¹' pairEvent 0 2 := by
  rw [show F = Prod.fst ⁻¹' (poolStructureEquiv ternarySig ⁻¹'
    pairEvent (poolVertexEquiv ternarySig () o₀) (poolVertexEquiv ternarySig () o₁)) from by
      rw [preimage_pairEvent_poolStructureEquiv], equiv_o₀, equiv_o₁]
  rfl

/-- The symmetric difference, written out. -/
def sdiff' {α : Type*} (A B : Set α) : Set α := (A \ B) ∪ (B \ A)

theorem measurableSet_sdiff' {α : Type*} {m : MeasurableSpace α} {A B : Set α}
    (hA : MeasurableSet[m] A) (hB : MeasurableSet[m] B) : MeasurableSet[m] (sdiff' A B) :=
  (hA.diff hB).union (hB.diff hA)

theorem preimage_sdiff' {α β : Type*} (f : α → β) (A B : Set β) :
    f ⁻¹' sdiff' A B = sdiff' (f ⁻¹' A) (f ⁻¹' B) := rfl

/-- The two mixed pair events, combined. -/
noncomputable abbrev G : Set (RelStructure ternarySig (PoolVertex ternarySig) ×
    PooledRankLatentSpace ternarySig 2) :=
  sdiff' (Prod.fst ⁻¹' pooledPairEvent o₀ s₀) (Prod.fst ⁻¹' pooledPairEvent o₁ s₀)

/-- Under the law, the parities agree exactly on the range of the array. -/
theorem pairEvent_ae_eq_sdiff' :
    pairEvent 0 2 =ᵐ[ternaryLaw] sdiff' (pairEvent 0 1) (pairEvent 2 1) := by
  have hpre : arr ⁻¹' pairEvent 0 2 = arr ⁻¹' sdiff' (pairEvent 0 1) (pairEvent 2 1) := by
    ext ω
    simp only [Set.mem_preimage, sdiff', Set.mem_union, Set.mem_sdiff, mem_pairEvent_arr]
    cases colour ω 0 <;> cases colour ω 1 <;> cases colour ω 2 <;> simp
  have hm : MeasurableSet (sdiff' (pairEvent 0 1) (pairEvent 2 1)) :=
    measurableSet_sdiff' (measurableSet_pairEvent 0 1) (measurableSet_pairEvent 2 1)
  rw [ternaryLaw, ae_eq_set]
  constructor
  · rw [Measure.map_apply measurable_arr ((measurableSet_pairEvent 0 2).diff hm),
      Set.preimage_sdiff, hpre, Set.sdiff_self, measure_empty]
  · rw [Measure.map_apply measurable_arr (hm.diff (measurableSet_pairEvent 0 2)),
      Set.preimage_sdiff, hpre, Set.sdiff_self, measure_empty]

/-- **The mixed events reveal the original pair event**: modulo the law, the original pair event
is the symmetric difference of the two mixed pair events. -/
theorem F_ae_eq_G : F =ᵐ[μQ] G := by
  have hq : Measure.QuasiMeasurePreserving idStructure μQ ternaryLaw :=
    (MeasurePreserving.mk measurable_idStructure map_idStructure).quasiMeasurePreserving
  have hmixed : G = idStructure ⁻¹' sdiff' (pairEvent 0 1) (pairEvent 2 1) := by
    show sdiff' (Prod.fst ⁻¹' pooledPairEvent o₀ s₀) (Prod.fst ⁻¹' pooledPairEvent o₁ s₀) = _
    rw [preimage_sdiff', ← preimage_pairEvent_poolStructureEquiv o₀ s₀,
      ← preimage_pairEvent_poolStructureEquiv o₁ s₀, equiv_o₀, equiv_o₁, equiv_s₀]
    rfl
  have key := hq.preimage_ae_eq pairEvent_ae_eq_sdiff'
  rw [← hmixed] at key
  calc F = idStructure ⁻¹' pairEvent 0 2 := F_eq
    _ =ᵐ[μQ] _ := key

/-- The two mixed pair events lie in `𝔅_fix`. -/
theorem measurableSet_fixBase_G : MeasurableSet[fixBase 2] G := by
  have h0 : MeasurableSet[fixBase 2] (Prod.fst ⁻¹' pooledPairEvent o₀ s₀) :=
    fixBaseGen_le (.inr mixed₀) _ ⟨_, measurableSet_pooled_pooledPairEvent o₀ s₀, rfl⟩
  have h1 : MeasurableSet[fixBase 2] (Prod.fst ⁻¹' pooledPairEvent o₁ s₀) :=
    fixBaseGen_le (.inr mixed₁) _ ⟨_, measurableSet_pooled_pooledPairEvent o₁ s₀, rfl⟩
  exact measurableSet_sdiff' h0 h1

/-- The original latents, read on the pooled space. -/
noncomputable abbrev origLatents :
    MeasurableSpace (RelStructure ternarySig (PoolVertex ternarySig) ×
      PooledRankLatentSpace ternarySig 2) :=
  MeasurableSpace.comap (restrictOriginalLatents ternarySig 2 ∘ Prod.snd) inferInstance

theorem origLatents_le_comap_idLatents :
    origLatents ≤ MeasurableSpace.comap idLatents inferInstance := by
  have hemb : (fun s => (doubleEmb ternarySig s).trans
      (poolVertexEquiv ternarySig s).symm.toEmbedding) = originalVertex ternarySig := by
    funext s
    ext x
    show (poolVertexEquiv ternarySig s).symm (poolVertexEquiv ternarySig s (Sum.inl x)) = Sum.inl x
    exact Equiv.symm_apply_apply _ _
  have h : restrictOriginalLatents ternarySig 2 ∘ Prod.snd =
      latentRestrictOver (doubleEmb ternarySig) 2 ∘ idLatents := by
    show latentRestrictOver (originalVertex ternarySig) 2 ∘ Prod.snd =
      (latentRestrictOver (doubleEmb ternarySig) 2 ∘
        latentRestrictOver (fun s => (poolVertexEquiv ternarySig s).symm.toEmbedding) 2) ∘
          Prod.snd
    rw [latentRestrictOver_comp, hemb]
  show MeasurableSpace.comap (restrictOriginalLatents ternarySig 2 ∘ Prod.snd) inferInstance ≤ _
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_latentRestrictOver _ 2).comap_le

/-- **Conditioning on the original latents gives the constant one half.** -/
theorem condExp_origLatents_eq_half :
    μQ⟦F | origLatents⟧ =ᵐ[μQ] fun _ => (1 / 2 : ℝ) := by
  have hFm : MeasurableSet[MeasurableSpace.comap idStructure inferInstance] F := by
    rw [F_eq]; exact ⟨_, measurableSet_pairEvent 0 2, rfl⟩
  have hindep : Indep (MeasurableSpace.comap idStructure inferInstance) origLatents μQ :=
    indep_of_indep_of_le_right indepFun_idStructure_idLatents origLatents_le_comap_idLatents
  have h := condExp_indep_eq measurable_idStructure.comap_le
    (((measurable_restrictOriginalLatents 2).comp measurable_snd).comap_le)
    ((stronglyMeasurable_const : StronglyMeasurable[MeasurableSpace.comap idStructure inferInstance]
      fun _ => (1 : ℝ)).indicator hFm) hindep
  have hFmeas : MeasurableSet F := by
    rw [F_eq]; exact measurable_idStructure (measurableSet_pairEvent 0 2)
  refine h.trans (Filter.EventuallyEq.of_eq (funext fun _ => ?_))
  rw [integral_indicator_const _ hFmeas, smul_eq_mul, mul_one, F_eq, measureReal_def,
    ← Measure.map_apply measurable_idStructure (measurableSet_pairEvent 0 2), map_idStructure,
    ternaryLaw_pairEvent (by decide), ENNReal.toReal_div]
  norm_num

/-- **Conditioning on `𝔅_fix` gives the indicator itself.** -/
theorem condExp_fixBase_eq_indicator :
    μQ⟦F | fixBase 2⟧ =ᵐ[μQ] F.indicator fun _ => (1 : ℝ) := by
  have hGm : MeasurableSet[fixBase 2] G := measurableSet_fixBase_G
  have h1 : μQ⟦F | fixBase 2⟧ =ᵐ[μQ] μQ⟦G | fixBase 2⟧ :=
    condExp_congr_ae (indicator_ae_eq_of_ae_eq_set F_ae_eq_G)
  have h2 : μQ⟦G | fixBase 2⟧ = G.indicator fun _ => (1 : ℝ) :=
    condExp_of_stronglyMeasurable (fixStage_le _)
      ((stronglyMeasurable_const : StronglyMeasurable[fixBase 2] fun _ => (1 : ℝ)).indicator hGm)
      ((integrable_const 1).indicator (fixStage_le _ _ hGm))
  refine h1.trans ?_
  rw [h2]
  exact (indicator_ae_eq_of_ae_eq_set F_ae_eq_G).symm

/-- **Base removal fails**: the two conditional probabilities of the original pair event, given
`𝔅_fix` and given the original latents, are not almost everywhere equal. -/
theorem not_condExp_fixBase_ae_eq_condExp_origLatents :
    ¬ (μQ⟦F | fixBase 2⟧ =ᵐ[μQ] μQ⟦F | origLatents⟧) := by
  intro h
  have hae : F.indicator (fun _ => (1 : ℝ)) =ᵐ[μQ] fun _ => (1 / 2 : ℝ) :=
    condExp_fixBase_eq_indicator.symm.trans (h.trans condExp_origLatents_eq_half)
  have hfalse : ∀ᵐ ω ∂μQ, False := by
    filter_upwards [hae] with ω hω
    by_cases hωF : ω ∈ F
    · rw [Set.indicator_of_mem hωF] at hω; norm_num at hω
    · rw [Set.indicator_of_notMem hωF] at hω; norm_num at hω
  exact IsProbabilityMeasure.ne_zero μQ
    (ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hfalse))

end TernaryParityRegression

end RelSignature
