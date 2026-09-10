/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelAdmissible
import Graphon.RelBipartiteRegression
import Graphon.RelIidEdgeRegression

/-!
# Admissibility of the positive regressions (R4 converse, #107)

Both existing successor witnesses — the bipartite rank `1 → 2` witness and the i.i.d.-edge rank
`2 → 3` witness — have admissible inputs and admissible outputs. The outputs are structures that
are functions of their latents. The inputs are independent products, where admissibility is
unconditional mutual independence of induced structures on families with small overlap: those
read disjoint blocks of the i.i.d. source.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

/-- Independence of a family pulled back along a measurable map. -/
theorem iIndepFun_comp_of_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {T : α → β} (hT : Measurable T) {ι : Type*} {γ : ι → Type*}
    [∀ i, MeasurableSpace (γ i)] {X : ∀ i, β → γ i} (hX : ∀ i, Measurable (X i))
    (h : iIndepFun X (μ.map T)) : iIndepFun (fun i => X i ∘ T) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S sets hsets
  have h1 := h S hsets
  have e1 : (μ.map T) (⋂ i ∈ S, X i ⁻¹' sets i) = μ (⋂ i ∈ S, (X i ∘ T) ⁻¹' sets i) := by
    rw [Measure.map_apply hT (Finset.measurableSet_biInter S fun i hi => (hX i) (hsets i hi)),
      Set.preimage_iInter₂]
    rfl
  have e2 : ∀ i ∈ S, (μ.map T) (X i ⁻¹' sets i) = μ ((X i ∘ T) ⁻¹' sets i) := fun i hi => by
    rw [Measure.map_apply hT ((hX i) (hsets i hi))]
    rfl
  rw [e1, Finset.prod_congr rfl e2] at h1
  exact h1

/-- Independence of a family pushed forward along a measurable map. -/
theorem iIndepFun_of_comp_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {T : α → β} (hT : Measurable T) {ι : Type*} {γ : ι → Type*}
    [∀ i, MeasurableSpace (γ i)] {X : ∀ i, β → γ i} (hX : ∀ i, Measurable (X i))
    (h : iIndepFun (fun i => X i ∘ T) μ) : iIndepFun X (μ.map T) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S sets hsets
  have h1 := h S hsets
  have e1 : (μ.map T) (⋂ i ∈ S, X i ⁻¹' sets i) = μ (⋂ i ∈ S, (X i ∘ T) ⁻¹' sets i) := by
    rw [Measure.map_apply hT (Finset.measurableSet_biInter S fun i hi => (hX i) (hsets i hi)),
      Set.preimage_iInter₂]
    rfl
  have e2 : ∀ i ∈ S, (μ.map T) (X i ⁻¹' sets i) = μ ((X i ∘ T) ⁻¹' sets i) := fun i hi => by
    rw [Measure.map_apply hT ((hX i) (hsets i hi))]
    rfl
  rw [e1, Finset.prod_congr rfl e2]
  exact h1

namespace BipartiteRegression

open InfiniteRelExchangeableLaw

/-- **The bipartite rank-two representation is admissible.** -/
theorem admissible_rankTwoRep : rankTwoRep.Admissible := by
  refine rankTwoRep.admissible_of_ae_eq_snd (measurable_arr.comp measurable_freshLayer) ?_
  show (fun p : RelStructure digraphSig (Vinfinite digraphSig) × RankLatentSpace digraphSig 2 =>
    p.1) =ᵐ[rankTwoCoupling] fun p => (arr ∘ freshLayer) p.2
  rw [rankTwoCoupling]
  exact (ae_map_iff measurable_rankTwoMap.aemeasurable (measurableSet_eq_fun measurable_fst
    ((measurable_arr.comp measurable_freshLayer).comp measurable_snd))).mpr
    (Filter.Eventually.of_forall fun _ => rfl)

/-- The singleton supports inside a vertex set. -/
def SingletonsIn (A : Finset (Σ _ : Unit, ℕ)) := {s : RankSupport digraphSig 1 // s.1 ⊆ A}

/-- The induced structure on `A` read off the colours at the singletons inside `A`. -/
noncomputable def inducedDecoder (A : Finset (Σ _ : Unit, ℕ)) (x : SingletonsIn A → ℝ) :
    InducedSpace (S := digraphSig) A :=
  fun c => xor (decide (x ⟨vertexSupport (c.1.2 0), fun v hv => by
      rw [show v = ⟨(), c.1.2 0⟩ from Finset.mem_singleton.mp hv]
      exact c.2 ((c.1.mem_support_iff _).mpr ⟨0, rfl⟩)⟩ ≤ 1 / 2))
    (decide (x ⟨vertexSupport (c.1.2 1), fun v hv => by
      rw [show v = ⟨(), c.1.2 1⟩ from Finset.mem_singleton.mp hv]
      exact c.2 ((c.1.mem_support_iff _).mpr ⟨1, rfl⟩)⟩ ≤ 1 / 2))

theorem measurable_inducedDecoder (A : Finset (Σ _ : Unit, ℕ)) :
    Measurable (inducedDecoder A) :=
  measurable_pi_lambda _ fun _ =>
    Measurable.comp (g := fun p : Bool × Bool => xor p.1 p.2) Measurable.of_discrete
      ((measurable_decideLe (measurable_pi_apply _)).prodMk
        (measurable_decideLe (measurable_pi_apply _)))

theorem inducedMap_arr (A : Finset (Σ _ : Unit, ℕ)) (ω : Colours) :
    inducedMap A (arr ω) = inducedDecoder A fun s => ω s.1 := by
  funext c
  rfl

/-- **The bipartite rank-one representation is admissible**: with pairwise disjoint sets the
induced structures read disjoint blocks of the i.i.d. colours. -/
theorem admissible_rankOneRep : rankOneRep.Admissible := by
  have hind : IndepFun (Prod.fst : RelStructure digraphSig (Vinfinite digraphSig) ×
      RankLatentSpace digraphSig 1 → _) Prod.snd rankOneCoupling := by
    refine (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
      measurable_snd.aemeasurable).mpr ?_
    rw [show (fun p : RelStructure digraphSig (Vinfinite digraphSig) ×
      RankLatentSpace digraphSig 1 => (p.1, p.2)) = id from rfl, Measure.map_id,
      rankOneCoupling_map_fst, rankOneCoupling_map_snd]
    rfl
  refine (rankOneRep.admissible_iff_iIndepFun_of_indep hind).mpr fun k A hA => ?_
  -- pull back along the structure marginal to the colour source
  have hP : rankOneRep.P = rankOneCoupling := rfl
  rw [hP]
  refine iIndepFun_comp_of_map measurable_fst (fun i => measurable_inducedMap (A i)) ?_
  rw [rankOneCoupling_map_fst, bipartiteLaw]
  refine iIndepFun_of_comp_map measurable_arr (fun i => measurable_inducedMap (A i)) ?_
  -- the blocks of singleton supports inside the sets are disjoint
  have hinj : Function.Injective fun p : Σ i : Fin k, SingletonsIn (A i) => p.2.1 := by
    rintro ⟨i, s⟩ ⟨j, t⟩ h
    simp only at h
    by_cases hij : i = j
    · subst hij
      exact congrArg _ (Subtype.ext h)
    · exact absurd (hA i j hij s.1.1 s.2 (h ▸ t.2)) (by rw [s.1.2]; exact lt_irrefl 1)
  have hblocks := iIndepFun_infinitePi_blocks (fun _ : RankSupport digraphSig 1 => uniform01) hinj
  rw [iidUniformSource]
  have := hblocks.comp (fun i => inducedDecoder (A i)) (fun i => measurable_inducedDecoder (A i))
  exact this.congr fun i =>
    Filter.EventuallyEq.of_eq (funext fun ω => (inducedMap_arr (A i) ω).symm)

end BipartiteRegression

namespace IidEdgeRegression

open InfiniteRelExchangeableLaw

/-- **The i.i.d.-edge rank-three representation is admissible.** -/
theorem admissible_rankThreeRep : rankThreeRep.Admissible := by
  refine rankThreeRep.admissible_of_ae_eq_snd (measurable_arr.comp measurable_freshLayer) ?_
  show (fun p : RelStructure digraphSig (Vinfinite digraphSig) × RankLatentSpace digraphSig 3 =>
    p.1) =ᵐ[rankThreeCoupling] fun p => (arr ∘ freshLayer) p.2
  rw [rankThreeCoupling]
  exact (ae_map_iff measurable_rankThreeMap.aemeasurable (measurableSet_eq_fun measurable_fst
    ((measurable_arr.comp measurable_freshLayer).comp measurable_snd))).mpr
    (Filter.Eventually.of_forall fun _ => rfl)

/-- The two-point supports inside a vertex set. -/
def PairsIn (A : Finset (Σ _ : Unit, ℕ)) := {s : RankSupport digraphSig 2 // s.1 ⊆ A}

open scoped Classical in
/-- The induced structure on `A` read off the edge uniforms at the pairs inside `A`. -/
noncomputable def inducedDecoder (A : Finset (Σ _ : Unit, ℕ)) (x : PairsIn A → ℝ) :
    InducedSpace (S := digraphSig) A :=
  fun c => if h : c.1.support.card = 2 then decide (x ⟨⟨c.1.support, h⟩, c.2⟩ ≤ 1 / 2) else false

open scoped Classical in
theorem measurable_inducedDecoder (A : Finset (Σ _ : Unit, ℕ)) :
    Measurable (inducedDecoder A) := by
  refine measurable_pi_lambda _ fun c => ?_
  by_cases h : c.1.support.card = 2
  · simp only [inducedDecoder, dif_pos h]
    exact measurable_decideLe (measurable_pi_apply _)
  · simp only [inducedDecoder, dif_neg h]
    exact measurable_const

open scoped Classical in
theorem inducedMap_arr (A : Finset (Σ _ : Unit, ℕ)) (e : Edges) :
    inducedMap A (arr e) = inducedDecoder A fun s => e s.1 := by
  funext c
  rfl

/-- **The i.i.d.-edge rank-two representation is admissible**: with pairwise overlaps below two
vertices the induced structures read disjoint blocks of the i.i.d. edges. -/
theorem admissible_rankTwoRep : rankTwoRep.Admissible := by
  classical
  have hind : IndepFun (Prod.fst : RelStructure digraphSig (Vinfinite digraphSig) ×
      RankLatentSpace digraphSig 2 → _) Prod.snd rankTwoCoupling := by
    refine (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
      measurable_snd.aemeasurable).mpr ?_
    rw [show (fun p : RelStructure digraphSig (Vinfinite digraphSig) ×
      RankLatentSpace digraphSig 2 => (p.1, p.2)) = id from rfl, Measure.map_id,
      rankTwoCoupling, Measure.map_fst_prod, Measure.map_snd_prod]
    simp
  refine (rankTwoRep.admissible_iff_iIndepFun_of_indep hind).mpr fun k A hA => ?_
  have hP : rankTwoRep.P = rankTwoCoupling := rfl
  have hfst : rankTwoCoupling.map Prod.fst = iidEdgeLaw := by
    rw [rankTwoCoupling, Measure.map_fst_prod]; simp
  rw [hP]
  refine iIndepFun_comp_of_map measurable_fst (fun i => measurable_inducedMap (A i)) ?_
  rw [hfst, iidEdgeLaw]
  refine iIndepFun_of_comp_map measurable_arr (fun i => measurable_inducedMap (A i)) ?_
  have hinj : Function.Injective fun p : Σ i : Fin k, PairsIn (A i) => p.2.1 := by
    rintro ⟨i, s⟩ ⟨j, t⟩ h
    simp only at h
    by_cases hij : i = j
    · subst hij
      exact congrArg _ (Subtype.ext h)
    · exact absurd (hA i j hij s.1.1 s.2 (h ▸ t.2)) (by rw [s.1.2]; exact lt_irrefl 2)
  have hblocks := iIndepFun_infinitePi_blocks (fun _ : RankSupport digraphSig 2 => uniform01) hinj
  rw [iidUniformSource]
  have := hblocks.comp (fun i => inducedDecoder (A i)) (fun i => measurable_inducedDecoder (A i))
  exact this.congr fun i =>
    Filter.EventuallyEq.of_eq (funext fun e => (inducedMap_arr (A i) e).symm)

end IidEdgeRegression

end RelSignature
