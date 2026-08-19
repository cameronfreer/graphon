/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRankSuccessorContract
import Graphon.InfiniteDigraph
import Graphon.ForMathlib.CondIndepSup
import Mathlib.Probability.ConditionalExpectation

/-!
# The i.i.d.-edge regression for the successor contract (R4 converse, #107, #196)

A hand-built rank `2 → 3` successor witness over `digraphSig`, testing **staging and recovery**
together — where the bipartite regression tested independence and symmetry.

The law is the symmetric i.i.d.-edge law: one uniform per two-point support, with

`X_uv = X_vu = 1{U_{u,v} ≤ 1/2}` and `X_uu = false`.

Keying the array by a coordinate's *support* makes both facts definitional: the two directed
coordinates of a block share a support and therefore a value, and the diagonal has a one-element
support so it falls in the default branch. Blocks at **distinct** two-point supports are i.i.d.,
being distinct coordinates of the source. Making `X_uv` and `X_vu` independently directed would
introduce an equivariant-orientation problem without testing staging any better.

## Shape of the regression

* the rank-two coupling is defined **independently** as `iidEdgeLaw.prod (rankLatentSource 2)`,
  so independence of the edges from the old latents is literal;
* the rank-three coupling is built from `rankLatentSource 3`, retaining the whole latent point and
  decoding the array from its fresh rank-two layer;
* the truncation identity is proved immediately, before either representation is packaged.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RelSignature

namespace IidEdgeRegression

/-- The edge layer: one uniform per two-point support. -/
abbrev Edges := RankSupport digraphSig 2 → ℝ

open scoped Classical in
/-- **The symmetric i.i.d.-edge array**, keyed by a coordinate's support. Both directed
coordinates of a two-point block share a support, hence a value; the diagonal has a one-element
support and is `false`. -/
noncomputable def arr (e : Edges) : RelStructure digraphSig (Vinfinite digraphSig) :=
  fun c => if h : c.support.card = 2 then decide (e ⟨c.support, h⟩ ≤ 1 / 2) else false

open scoped Classical in
/-- **Symmetry is definitional**: the two directed coordinates of a block share a support. -/
theorem arr_symm (e : Edges) (u v : ℕ) :
    arr e (digraphCoord u v) = arr e (digraphCoord v u) := by
  have hsupp : (digraphCoord u v : RelCoord digraphSig (Vinfinite digraphSig)).support =
      (digraphCoord v u : RelCoord digraphSig (Vinfinite digraphSig)).support := by
    refine Finset.ext fun w => ?_
    rw [RelCoord.mem_support_iff, RelCoord.mem_support_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
  simp only [arr, hsupp]

open scoped Classical in
/-- **The diagonal is `false`**: its support has one element, not two. -/
@[simp] theorem arr_diagonal (e : Edges) (v : ℕ) : arr e (digraphCoord v v) = false := by
  have hsupp : (digraphCoord v v : RelCoord digraphSig (Vinfinite digraphSig)).support =
      {⟨(), v⟩} := by
    refine Finset.ext fun w => ?_
    rw [RelCoord.mem_support_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> rfl
    · rintro rfl
      exact ⟨0, rfl⟩
  rw [arr, dif_neg]
  rw [hsupp, Finset.card_singleton]
  omega

open scoped Classical in
theorem measurable_arr : Measurable arr := by
  refine measurable_pi_lambda _ fun c => ?_
  by_cases h : (c : RelCoord digraphSig (Vinfinite digraphSig)).support.card = 2
  · have hfun : (fun e : Edges => arr e c) = fun e => decide (e ⟨c.support, h⟩ ≤ 1 / 2) := by
      funext e; rw [arr, dif_pos h]
    rw [hfun]
    exact measurable_decideLe (measurable_pi_apply _)
  · have hfun : (fun e : Edges => arr e c) = fun _ => false := by
      funext e; rw [arr, dif_neg h]
    rw [hfun]
    exact measurable_const

/-- **The i.i.d.-edge law**, defined from the edge layer alone. -/
noncomputable def iidEdgeLaw : Measure (RelStructure digraphSig (Vinfinite digraphSig)) :=
  (iidUniformSource (RankSupport digraphSig 2)).map arr

instance : IsProbabilityMeasure iidEdgeLaw :=
  Measure.isProbabilityMeasure_map measurable_arr.aemeasurable

/-! ### Equivariance and exchangeability

Relabeling the vertices reindexes the edge layer along `rankSupportPerm`, because a coordinate's
support transports covariantly and its cardinality is preserved. Exchangeability is then the
invariance of an i.i.d. product under a coordinate permutation. -/

open scoped Classical in
set_option maxHeartbeats 400000 in
/-- **Equivariance of the array**: relabeling the vertices is reindexing the edge layer. -/
theorem arr_comp_supportPerm (σ : ∀ _ : Unit, Equiv.Perm ℕ) (e : Edges) :
    arr (fun A => e (rankSupportPerm σ 2 A)) = RelStructure.relabel σ (arr e) := by
  funext c
  have hinj : Function.Injective (Sigma.map id (fun s => ⇑(σ s)) :
      (Σ s : Unit, Vinfinite digraphSig s) → Σ s : Unit, Vinfinite digraphSig s) :=
    Function.injective_id.sigma_map fun s => (σ s).injective
  have hmem : ∀ v, v ∈ (RelCoord.map (fun s => ⇑(σ s)) c).support ↔
      ∃ a ∈ c.support, Sigma.map id (fun s => ⇑(σ s)) a = v := by
    intro v
    constructor
    · intro hv
      obtain ⟨i, hi⟩ := (RelCoord.mem_support_iff _ _).mp hv
      exact ⟨c.taggedValue i, (RelCoord.mem_support_iff _ _).mpr ⟨i, rfl⟩, hi⟩
    · rintro ⟨a, ha, hav⟩
      obtain ⟨i, hi⟩ := (RelCoord.mem_support_iff _ _).mp ha
      refine (RelCoord.mem_support_iff _ _).mpr ⟨i, ?_⟩
      rw [← hav, ← hi]
      rfl
  have hcard : (RelCoord.map (fun s => ⇑(σ s)) c).support.card = c.support.card := by
    refine Finset.card_nbij' (Sigma.map id fun s => ⇑(σ s)⁻¹) (Sigma.map id fun s => ⇑(σ s))
      (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_)
    · obtain ⟨a, ha, rfl⟩ := (hmem v).mp hv
      obtain ⟨s, x⟩ := a
      simpa [Sigma.map] using ha
    · exact (hmem _).mpr ⟨v, hv, rfl⟩
    · obtain ⟨a, _, rfl⟩ := (hmem v).mp hv
      obtain ⟨s, x⟩ := a
      simp [Sigma.map]
    · obtain ⟨s, x⟩ := v
      simp [Sigma.map]
  show arr (fun A => e (rankSupportPerm σ 2 A)) c = arr e (RelCoord.map (fun s => ⇑(σ s)) c)
  simp only [arr]
  split_ifs with h₁ h₂ h₂
  · refine congrArg (fun r : ℝ => decide (r ≤ 1 / 2)) (congrArg e (Subtype.ext ?_))
    refine Finset.ext fun v => ?_
    exact (mem_rankSupportPerm σ 2 (Subtype.mk c.support h₁ : RankSupport digraphSig 2) v).trans
      (hmem v).symm
  · exact absurd (hcard.trans h₁) h₂
  · exact absurd (hcard.symm.trans h₂) h₁
  · rfl

/-- **Exchangeability**: the law is invariant under every sortwise relabeling. -/
theorem iidEdgeLaw_map_relabel (σ : ∀ _ : Unit, Equiv.Perm ℕ) :
    iidEdgeLaw.map (RelStructure.relabel σ) = iidEdgeLaw := by
  rw [iidEdgeLaw, Measure.map_map (measurable_relabel σ) measurable_arr,
    show RelStructure.relabel σ ∘ arr =
      arr ∘ (fun e : Edges => fun A => e (rankSupportPerm σ 2 A)) from by
        funext e
        exact (arr_comp_supportPerm σ e).symm,
    ← Measure.map_map measurable_arr
      (measurable_pi_lambda _ fun _ => measurable_pi_apply _),
    iidUniformSource,
    Measure.infinitePi_map_comp_equiv (fun _ : RankSupport digraphSig 2 => uniform01)
      (rankSupportPerm σ 2)]

/-- The i.i.d.-edge law as an exchangeable law on the infinite structure space. -/
noncomputable def iidEdgeExchangeable : InfiniteRelExchangeableLaw digraphSig where
  law := ⟨iidEdgeLaw, inferInstance⟩
  exchangeable := iidEdgeLaw_map_relabel

/-! ### The product-right conditional-independence lemma

Kept **private**: it has one consumer (rank-two screening below), which is below the promotion bar
for `Graphon/ForMathlib/`. Neither Mathlib nor TauCeti has it — `condExp_indep_eq` supplies the
constant conditional expectation of a left-coordinate observation, but not the intersection
identity that conditional independence needs. Recorded as a prospective upstream candidate.

Stated for an arbitrary conditioning σ-algebra below `comap Prod.snd`, so conditioning on a
function of the right coordinate is a corollary rather than the definition.

Two elaboration points are load-bearing. `CondIndepFun` takes the conditioning algebra *before* the
ambient measurable space, so the conclusion is written in explicit `@` form. And an abstract
`m' : MeasurableSpace (α × β)` binder **enters local instance search**, shadowing the product
instance throughout the proof body; the opening `letI` restores the intended ambient instance
without weakening the statement. -/

private theorem comap_fst_le_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    MeasurableSpace.comap (Prod.fst : α × β → α) inferInstance ≤
      (Prod.instMeasurableSpace : MeasurableSpace (α × β)) := by
  rintro S ⟨T, hT, rfl⟩
  exact measurable_fst hT

private theorem comap_snd_le_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    MeasurableSpace.comap (Prod.snd : α × β → β) inferInstance ≤
      (Prod.instMeasurableSpace : MeasurableSpace (α × β)) := by
  rintro S ⟨T, hT, rfl⟩
  exact measurable_snd hT

open scoped Classical in
/-- Under a product measure, a left-coordinate observation is conditionally independent of a
right-coordinate observation given **any** σ-algebra below the right coordinate's. -/
private theorem condIndepFun_of_prod_right {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    [StandardBorelSpace α] [StandardBorelSpace β] [Nonempty α] [Nonempty β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m' : MeasurableSpace (α × β)}
    (hm' : m' ≤ MeasurableSpace.comap (Prod.snd : α × β → β) inferInstance)
    {f : α → γ} {g : β → δ} (hf : Measurable f) (hg : Measurable g) :
    @ProbabilityTheory.CondIndepFun (α × β) m' Prod.instMeasurableSpace
      (StandardBorelSpace.prod) (hm'.trans comap_snd_le_prod)
      γ δ inferInstance inferInstance
      (f ∘ (Prod.fst : α × β → α)) (g ∘ (Prod.snd : α × β → β)) (μ.prod ν) inferInstance := by
  letI mΩ : MeasurableSpace (α × β) := Prod.instMeasurableSpace
  have hmAmbient : m' ≤ (Prod.instMeasurableSpace : MeasurableSpace (α × β)) :=
    hm'.trans comap_snd_le_prod
  have hfst : Measurable (f ∘ (Prod.fst : α × β → α)) := hf.comp measurable_fst
  have hsnd : Measurable (g ∘ (Prod.snd : α × β → β)) := hg.comp measurable_snd
  have hcoord : Indep (MeasurableSpace.comap (Prod.fst : α × β → α) inferInstance)
      (MeasurableSpace.comap (Prod.snd : α × β → β) inferInstance) (μ.prod ν) :=
    indepFun_prod measurable_id measurable_id
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hfst hsnd]
  intro s t hs ht
  set A : Set (α × β) := (f ∘ (Prod.fst : α × β → α)) ⁻¹' s with hAdef
  set B : Set (α × β) := (g ∘ (Prod.snd : α × β → β)) ⁻¹' t with hBdef
  have hAmem : MeasurableSet[MeasurableSpace.comap (Prod.fst : α × β → α) inferInstance] A :=
    ⟨f ⁻¹' s, hf hs, rfl⟩
  have hBmem : MeasurableSet[MeasurableSpace.comap (Prod.snd : α × β → β) inferInstance] B :=
    ⟨g ⁻¹' t, hg ht, rfl⟩
  have hAmeas : MeasurableSet A := hfst hs
  have hBmeas : MeasurableSet B := hsnd ht
  have hAconst : (μ.prod ν)⟦A | m'⟧ =ᵐ[μ.prod ν] fun _ => ((μ.prod ν) A).toReal := by
    have hInd : Indep (MeasurableSpace.comap (Prod.fst : α × β → α) inferInstance) m'
        (μ.prod ν) := indep_of_indep_of_le_right hcoord hm'
    refine (condExp_indep_eq (μ := μ.prod ν) comap_fst_le_prod hmAmbient
      (stronglyMeasurable_const.indicator hAmem) hInd).trans
      (Filter.Eventually.of_forall fun _ => ?_)
    rw [integral_indicator_const (1 : ℝ) hAmeas, smul_eq_mul, mul_one, measureReal_def]
  have hInter : (μ.prod ν)⟦A ∩ B | m'⟧ =ᵐ[μ.prod ν]
      fun ω => ((μ.prod ν) A).toReal * ((μ.prod ν)⟦B | m'⟧) ω := by
    refine (ae_eq_condExp_of_forall_setIntegral_eq hmAmbient
      ((integrable_const (1 : ℝ)).indicator (hAmeas.inter hBmeas))
      (fun S _ _ => (integrable_condExp.const_mul _).integrableOn)
      (fun S hSm _ => ?_) (stronglyMeasurable_condExp.const_mul _).aestronglyMeasurable).symm
    have hSamb : MeasurableSet S := hmAmbient _ hSm
    have hmul : (μ.prod ν) (A ∩ (S ∩ B)) = (μ.prod ν) A * (μ.prod ν) (S ∩ B) := by
      simpa using hcoord A (S ∩ B) hAmem ((hm' _ hSm).inter hBmem)
    rw [integral_const_mul,
      setIntegral_condExp hmAmbient ((integrable_const (1 : ℝ)).indicator hBmeas) hSm,
      setIntegral_indicator hBmeas, setIntegral_indicator (hAmeas.inter hBmeas),
      integral_const, integral_const, measureReal_restrict_apply_univ,
      measureReal_restrict_apply_univ,
      show S ∩ (A ∩ B) = A ∩ (S ∩ B) from Set.inter_left_comm _ _ _,
      measureReal_def, measureReal_def, hmul, ENNReal.toReal_mul]
    ring
  filter_upwards [hInter, hAconst] with ω h1 h2
  rw [h1, h2]

/-! ### The two couplings, described independently

The rank-two coupling is a product, so independence of the edges from the old latents is literal.
The rank-three coupling is built from the rank-three source and decodes the array from its fresh
rank-two layer. The truncation identity is proved immediately, before either representation is
packaged. -/

/-- **The rank-two coupling**: the i.i.d.-edge law together with an *independent* rank-two latent
array. Defined without reference to the rank-three object. -/
noncomputable def rankTwoCoupling :
    Measure (RelStructure digraphSig (Vinfinite digraphSig) × RankLatentSpace digraphSig 2) :=
  iidEdgeLaw.prod (rankLatentSource digraphSig 2)

instance : IsProbabilityMeasure rankTwoCoupling := by
  rw [rankTwoCoupling]; infer_instance

@[simp] theorem rankTwoCoupling_map_fst : rankTwoCoupling.map Prod.fst = iidEdgeLaw := by
  rw [rankTwoCoupling, Measure.map_fst_prod]; simp

@[simp] theorem rankTwoCoupling_map_snd :
    rankTwoCoupling.map Prod.snd = rankLatentSource digraphSig 2 := by
  rw [rankTwoCoupling, Measure.map_snd_prod]; simp

/-- The fresh rank-two layer of a rank-three latent point. -/
noncomputable def freshLayer (ω : RankLatentSpace digraphSig 3) : Edges :=
  (rankLatentSpaceSuccEquiv 2 ω).2

theorem measurable_freshLayer : Measurable freshLayer :=
  (rankLatentSpaceSuccEquiv 2).measurable.snd

theorem map_freshLayer :
    (rankLatentSource digraphSig 3).map freshLayer =
      iidUniformSource (RankSupport digraphSig 2) := by
  have hfl : freshLayer = Prod.snd ∘ (rankLatentSpaceSuccEquiv 2) := rfl
  rw [hfl, ← Measure.map_map measurable_snd (rankLatentSpaceSuccEquiv 2).measurable,
    rankLatentSource_map_rankLatentSpaceSuccEquiv, Measure.map_snd_prod]
  simp

/-- **The rank-three coupling**: the array is decoded from the fresh rank-two layer, and the whole
rank-three latent point is retained. -/
noncomputable def rankThreeCoupling :
    Measure (RelStructure digraphSig (Vinfinite digraphSig) × RankLatentSpace digraphSig 3) :=
  (rankLatentSource digraphSig 3).map fun ω => (arr (freshLayer ω), ω)

theorem measurable_rankThreeMap :
    Measurable fun ω : RankLatentSpace digraphSig 3 => (arr (freshLayer ω), ω) :=
  (measurable_arr.comp measurable_freshLayer).prodMk measurable_id

instance : IsProbabilityMeasure rankThreeCoupling := by
  rw [rankThreeCoupling]
  exact Measure.isProbabilityMeasure_map measurable_rankThreeMap.aemeasurable

@[simp] theorem rankThreeCoupling_map_fst : rankThreeCoupling.map Prod.fst = iidEdgeLaw := by
  rw [rankThreeCoupling, Measure.map_map measurable_fst measurable_rankThreeMap,
    show (Prod.fst ∘ fun ω : RankLatentSpace digraphSig 3 => (arr (freshLayer ω), ω)) =
      arr ∘ freshLayer from rfl,
    ← Measure.map_map measurable_arr measurable_freshLayer, map_freshLayer, iidEdgeLaw]

@[simp] theorem rankThreeCoupling_map_snd :
    rankThreeCoupling.map Prod.snd = rankLatentSource digraphSig 3 := by
  rw [rankThreeCoupling, Measure.map_map measurable_snd measurable_rankThreeMap,
    show (Prod.snd ∘ fun ω : RankLatentSpace digraphSig 3 => (arr (freshLayer ω), ω)) = id from rfl,
    Measure.map_id]

/-- **The truncation identity — the gate**: truncating the rank-three coupling's latents to rank
two returns the *independently defined* rank-two coupling. The fresh edge layer splits off from
the old latents, the array reads only the former and the truncation only the latter. -/
theorem rankThreeCoupling_truncation :
    rankThreeCoupling.map (Prod.map id (rankLatentProjection (S := digraphSig) (Nat.le_succ 2))) =
      rankTwoCoupling := by
  rw [rankThreeCoupling,
    Measure.map_map (measurable_id.prodMap
        (measurable_rankLatentProjection (S := digraphSig) (Nat.le_succ 2)))
      measurable_rankThreeMap,
    show (Prod.map (id : RelStructure digraphSig (Vinfinite digraphSig) → _)
        (rankLatentProjection (S := digraphSig) (Nat.le_succ 2)) ∘
        fun ω : RankLatentSpace digraphSig 3 => (arr (freshLayer ω), ω)) =
      (Prod.map arr (id : RankLatentSpace digraphSig 2 → _)) ∘ Prod.swap ∘
        (rankLatentSpaceSuccEquiv 2) from rfl,
    ← Measure.map_map (measurable_arr.prodMap measurable_id)
      (measurable_swap.comp (rankLatentSpaceSuccEquiv 2).measurable),
    ← Measure.map_map measurable_swap (rankLatentSpaceSuccEquiv 2).measurable,
    rankLatentSource_map_rankLatentSpaceSuccEquiv, Measure.prod_swap,
    ← Measure.map_prod_map _ _ measurable_arr measurable_id, Measure.map_id,
    rankTwoCoupling, iidEdgeLaw]

/-! ### Blocks read a single edge coordinate

Two pointwise lemmas, proved before any measure is touched: a block below rank two is constant
`false`, and a block at a two-point support reads exactly the edge coordinate keyed by that
support. Everything downstream — recovery at both ranks and screening at rank two — is a
consequence of these. -/

open scoped Classical in
/-- A block whose support does not have two elements is constant `false`. -/
theorem blockMap_arr_of_card_ne_two {A : Finset (Σ _ : Unit, ℕ)} (hA : A.card ≠ 2) (e : Edges) :
    blockMap (S := digraphSig) A (arr e) = fun _ => false := by
  funext c
  show arr e c.1 = false
  rw [arr, dif_neg]
  rw [c.2]
  exact hA

open scoped Classical in
/-- A block at a two-point support reads exactly the edge coordinate keyed by that support. -/
theorem blockMap_arr_of_card_eq_two {A : Finset (Σ _ : Unit, ℕ)} (hA : A.card = 2) (e : Edges) :
    blockMap (S := digraphSig) A (arr e) =
      fun _ => decide (e (Subtype.mk A hA : RankSupport digraphSig 2) ≤ 1 / 2) := by
  funext c
  show arr e c.1 = _
  rw [arr, dif_pos (by rw [c.2]; exact hA)]
  exact congrArg (fun r : ℝ => decide (r ≤ 1 / 2)) (congrArg e (Subtype.ext c.2))

/-! ### Rank-two invariance and recovery -/

/-- **Rank-two invariance**: the coupling is a product of two invariant factors. -/
theorem rankTwoCoupling_invariant (σ : FinSuppPerm digraphSig) :
    rankTwoCoupling.map (Prod.map (RelStructure.relabel σ.1) (⇑(rankLatentRelabel σ 2))) =
      rankTwoCoupling := by
  rw [rankTwoCoupling, ← Measure.map_prod_map _ _ (measurable_relabel σ.1)
      (rankLatentRelabel σ 2).measurable,
    iidEdgeLaw_map_relabel, rankLatentSource_map_rankLatentRelabel]

open scoped Classical in
/-- **Rank-two local recovery**: below rank two every block is constant `false`, so the decoder
is a constant and reads no latent at all. -/
theorem lower_recovers_rank_two (A : Finset (Σ _ : Unit, ℕ)) (hA : A.card < 2) :
    ∃ g : LocalLatentSpace (S := digraphSig) A 2 → BlockSpace (S := digraphSig) A, Measurable g ∧
      blockMap (S := digraphSig) A ∘ Prod.fst =ᵐ[rankTwoCoupling]
        g ∘ localLatents (S := digraphSig) A 2 ∘ Prod.snd := by
  refine ⟨fun _ _ => false, measurable_const, ?_⟩
  have hset : MeasurableSet {X : RelStructure digraphSig (Vinfinite digraphSig) |
      blockMap (S := digraphSig) A X = fun _ => false} :=
    measurableSet_eq_fun (measurable_blockMap (S := digraphSig) A) measurable_const
  refine (ae_map_iff measurable_fst.aemeasurable hset).mp ?_
  rw [rankTwoCoupling_map_fst, iidEdgeLaw]
  refine (ae_map_iff measurable_arr.aemeasurable hset).mpr
    (Filter.Eventually.of_forall fun e => ?_)
  exact blockMap_arr_of_card_ne_two (by omega) e

/-! ### Rank three: deterministic recovery and a vacuous screening clause

At rank three recovery is the substantive clause — a two-point block is decoded from the latent
coordinate at its own support, which the rank-three array carries. Screening, by contrast, is
vacuous: over a binary signature no coordinate reads three vertices, so a three-point block space
is a single point. -/

/-- The fresh rank-two layer of a rank-three latent point reads the coordinate at that support. -/
theorem freshLayer_apply (ω : RankLatentSpace digraphSig 3) (A : Finset (Σ _ : Unit, ℕ))
    (hA : A.card = 2) :
    freshLayer ω (Subtype.mk A hA : RankSupport digraphSig 2) =
      ω (Subtype.mk A (by omega) : RankLatentIndex digraphSig 3) := rfl

open scoped Classical in
/-- **The rank-three decoder** at a two-point support: read the local latent at that very
support. -/
noncomputable def twoPointDecoder (A : Finset (Σ _ : Unit, ℕ)) (hA : A.card = 2) :
    LocalLatentSpace (S := digraphSig) A 3 → BlockSpace (S := digraphSig) A :=
  fun ℓ _ => decide (ℓ ⟨Subtype.mk A (by omega), Finset.Subset.refl A⟩ ≤ 1 / 2)

open scoped Classical in
theorem measurable_twoPointDecoder (A : Finset (Σ _ : Unit, ℕ)) (hA : A.card = 2) :
    Measurable (twoPointDecoder A hA) :=
  measurable_pi_lambda _ fun _ => measurable_decideLe (measurable_pi_apply _)

open scoped Classical in
/-- **Rank-three local recovery**: below rank three a block is either constant `false` or, at a
two-point support, decoded from the latent coordinate at that support — which the rank-three
array carries, since `2 < 3`. This is the staging clause the regression exists to exercise. -/
theorem lower_recovers_rank_three (A : Finset (Σ _ : Unit, ℕ)) (hA : A.card < 3) :
    ∃ g : LocalLatentSpace (S := digraphSig) A 3 → BlockSpace (S := digraphSig) A, Measurable g ∧
      blockMap (S := digraphSig) A ∘ Prod.fst =ᵐ[rankThreeCoupling]
        g ∘ localLatents (S := digraphSig) A 3 ∘ Prod.snd := by
  by_cases h2 : A.card = 2
  · refine ⟨twoPointDecoder A h2, measurable_twoPointDecoder A h2, ?_⟩
    rw [rankThreeCoupling]
    refine (ae_map_iff measurable_rankThreeMap.aemeasurable ?_).mpr
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact measurableSet_eq_fun ((measurable_blockMap (S := digraphSig) A).comp measurable_fst)
        ((measurable_twoPointDecoder A h2).comp
          ((measurable_localLatents (S := digraphSig) A 3).comp measurable_snd))
    · show blockMap (S := digraphSig) A (arr (freshLayer ω)) = _
      rw [blockMap_arr_of_card_eq_two h2, freshLayer_apply ω A h2]
      rfl
  · refine ⟨fun _ _ => false, measurable_const, ?_⟩
    rw [rankThreeCoupling]
    refine (ae_map_iff measurable_rankThreeMap.aemeasurable ?_).mpr
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact measurableSet_eq_fun ((measurable_blockMap (S := digraphSig) A).comp measurable_fst)
        measurable_const
    · exact blockMap_arr_of_card_ne_two h2 (freshLayer ω)

/-- Over a binary signature a coordinate reads at most two vertices. -/
theorem card_support_le_two (c : RelCoord digraphSig (Vinfinite digraphSig)) :
    c.support.card ≤ 2 := RelCoord.card_support_le c

open scoped Classical in
/-- **No coordinate has a three-point support**, so a rank-three block space is a single point —
which is why the rank-three screening clause carries no probabilistic content. -/
theorem isEmpty_blockIndex_of_card_eq_three {A : Finset (Σ _ : Unit, ℕ)} (hA : A.card = 3) :
    IsEmpty (BlockIndex (S := digraphSig) A) :=
  ⟨fun c => by
    have := card_support_le_two c.1
    rw [c.2, hA] at this
    omega⟩

open scoped Classical in
/-- **Rank-three screening**: at a three-point support the block space is a single point, so the
block is a constant and conditional independence is immediate. -/
theorem screening_rank_three (A : Finset (Σ _ : Unit, ℕ)) (hA : A.card = 3) :
    CondIndepFun (MeasurableSpace.comap
        (localLatents (S := digraphSig) A 3 ∘ Prod.snd) inferInstance)
      (((measurable_localLatents (S := digraphSig) A 3).comp measurable_snd).comap_le)
      (blockMap (S := digraphSig) A ∘ Prod.fst) (restObservation 3 A) rankThreeCoupling := by
  haveI := isEmpty_blockIndex_of_card_eq_three hA
  haveI : Unique (BlockSpace (S := digraphSig) A) := Pi.uniqueOfIsEmpty _
  have hconst : (blockMap (S := digraphSig) A ∘ Prod.fst :
      RelStructure digraphSig (Vinfinite digraphSig) × RankLatentSpace digraphSig 3 →
        BlockSpace (S := digraphSig) A) = fun _ => default :=
    funext fun _ => Subsingleton.elim _ _
  rw [hconst]
  exact condIndepFun_const_left (default : BlockSpace (S := digraphSig) A)
    (restObservation (S := digraphSig) 3 A)

end IidEdgeRegression

end RelSignature
