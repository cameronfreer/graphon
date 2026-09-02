/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRankSuccessorContract
import Graphon.InfiniteDigraph
import Graphon.DigraphCoordSupport
import Graphon.ForMathlib.CondIndepSup
import Mathlib.Probability.ConditionalExpectation

/-!
# The i.i.d.-edge regression for the successor contract (R4 converse, #107, #196)

A hand-built rank `2 → 3` successor witness over `digraphSig`, testing **staging and recovery**
together — where the bipartite regression tested independence and symmetry.

The law is the symmetric i.i.d.-edge law: one uniform per two-point support, with

`X_uv = X_vu = 1{U_{u,v} ≤ 1/2}` and `X_uu = false`.

Keying the array by a coordinate's *support* gives both facts by construction: the two directed
coordinates of a block share a support and therefore a value, and the diagonal has a one-element
support so it falls in the default branch. Each still needs its support computed — see `arr_symm`
and `arr_diagonal` — but neither needs a choice of orientation. Blocks at **distinct** two-point supports are i.i.d.,
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
/-- **Symmetry by construction**: the two directed coordinates of a block share a support. -/
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

/-! ### Conditional independence from unconditional independence

Kept **private**: it has one consumer (rank-two screening below), which is below the promotion bar
for `Graphon/ForMathlib/`. `condExp_indep_eq` supplies the constant conditional expectation of an
`m₁`-observation, but the remaining content is the intersection identity
`E[1_{A ∩ B} | m'] = μ(A) · E[1_B | m']` for `A` in `m₁` and `B` in `m₂`, which no available lemma
provides. Recorded as a prospective upstream candidate.

**If `m₁` is independent of `m₂`, then conditioning on anything inside `m₂` cannot create a
dependence.** Stated for abstract σ-algebras rather than for the two coordinates of a product,
because the consumer's ambient measure is a *pushforward* of a product, and the current API only
transports conditional independence **backward**. A source-level proof would therefore require a
new forward law-transport theorem; this regression instead transports the unconditional
independence, which the existing API does supply, and applies the conditioning lemma on the
coupling.

One elaboration point is load-bearing: an abstract `MeasurableSpace Ω` binder **enters local
instance search** and can shadow the ambient instance throughout the proof body. The conclusion is
therefore written in explicit `@` form and the proof opens with a `letI` restoring the intended
ambient instance, neither of which weakens the statement. -/

private theorem condIndepFun_of_indep_of_le {Ω γ δ : Type*} [mΩ : MeasurableSpace Ω]
    [hsb : StandardBorelSpace Ω] [MeasurableSpace γ] [MeasurableSpace δ]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m' m₁ m₂ : MeasurableSpace Ω} (h1 : m₁ ≤ mΩ) (h2 : m₂ ≤ mΩ) (hm' : m' ≤ m₂)
    (hindep : Indep m₁ m₂ μ) {f : Ω → γ} {g : Ω → δ}
    (hf : Measurable[m₁] f) (hg : Measurable[m₂] g) :
    @ProbabilityTheory.CondIndepFun Ω m' mΩ hsb (hm'.trans h2) γ δ inferInstance inferInstance
      f g μ inferInstance := by
  letI : MeasurableSpace Ω := mΩ
  have hmAmbient : m' ≤ mΩ := hm'.trans h2
  have hfm : Measurable f := hf.mono h1 le_rfl
  have hgm : Measurable g := hg.mono h2 le_rfl
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hfm hgm]
  intro s t hs ht
  set A : Set Ω := f ⁻¹' s with hAdef
  set B : Set Ω := g ⁻¹' t with hBdef
  have hAmem : MeasurableSet[m₁] A := hf hs
  have hBmem : MeasurableSet[m₂] B := hg ht
  have hAmeas : MeasurableSet A := hfm hs
  have hBmeas : MeasurableSet B := hgm ht
  have hAconst : μ⟦A | m'⟧ =ᵐ[μ] fun _ => (μ A).toReal := by
    have hInd : Indep m₁ m' μ := indep_of_indep_of_le_right hindep hm'
    refine (condExp_indep_eq (μ := μ) h1 hmAmbient
      (stronglyMeasurable_const.indicator hAmem) hInd).trans
      (Filter.Eventually.of_forall fun _ => ?_)
    rw [integral_indicator_const (1 : ℝ) hAmeas, smul_eq_mul, mul_one, measureReal_def]
  have hInter : μ⟦A ∩ B | m'⟧ =ᵐ[μ] fun ω => (μ A).toReal * (μ⟦B | m'⟧) ω := by
    refine (ae_eq_condExp_of_forall_setIntegral_eq hmAmbient
      ((integrable_const (1 : ℝ)).indicator (hAmeas.inter hBmeas))
      (fun S _ _ => (integrable_condExp.const_mul _).integrableOn)
      (fun S hSm _ => ?_) (stronglyMeasurable_condExp.const_mul _).aestronglyMeasurable).symm
    have hmul : μ (A ∩ (S ∩ B)) = μ A * μ (S ∩ B) := by
      simpa using hindep A (S ∩ B) hAmem ((hm' _ hSm).inter hBmem)
    rw [integral_const_mul,
      setIntegral_condExp hmAmbient ((integrable_const (1 : ℝ)).indicator hBmeas) hSm,
      setIntegral_indicator hBmeas, setIntegral_indicator (hAmeas.inter hBmeas),
      integral_const, integral_const, measureReal_restrict_apply_univ,
      measureReal_restrict_apply_univ,
      show S ∩ (A ∩ B) = A ∩ (S ∩ B) from Set.inter_left_comm _ _ _,
      measureReal_def, measureReal_def, hmul, ENNReal.toReal_mul]
    ring
  filter_upwards [hInter, hAconst] with ω hi ha
  rw [hi, ha]

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
array carries, since `2 < 3`. This is the staging clause the regression exists to exercise.

The rank hypothesis is not consumed: for this law recovery happens to hold at *every* support,
since a block whose support does not have two elements is constant. The hypothesis is kept because
`lower_recovers` supplies it. -/
theorem lower_recovers_rank_three (A : Finset (Σ _ : Unit, ℕ)) (_hA : A.card < 3) :
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

/-! ### Rank-two screening

At a two-point support the block reads **one** coordinate of the edge source, while the remainder
reads the *other* coordinates together with the whole latent array — an independent factor. So the
block is independent of the remainder outright, and screening follows from independence rather than
from determinism. That is the case the bipartite regression could not exercise: there the rank-two
block was a function of the latents visible at its support, so screening was immediate.

The argument accordingly establishes the *unconditional* independence and transports that. This is
an API constraint, not a mathematical one: for these observables, with conditioning generated by a
function, conditional independence is determined by their joint law and would transport too — but
the repository has only backward transport (`condIndepFun_comp_measurePreserving` and its
relatives), so using it here would mean proving a forward law-transport theorem first. Pushing the
unconditional independence forward needs no new theorem. -/

private theorem indepFun_of_map {Ω Ω' γ δ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace γ] [MeasurableSpace δ] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω'} (hT : Measurable T) {f : Ω' → γ} {g : Ω' → δ}
    (hf : Measurable f) (hg : Measurable g) (h : IndepFun (f ∘ T) (g ∘ T) μ) :
    IndepFun f g (μ.map T) := by
  haveI : IsProbabilityMeasure (μ.map T) := Measure.isProbabilityMeasure_map hT.aemeasurable
  rw [indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable,
    Measure.map_map (hf.prodMk hg) hT, Measure.map_map hf hT, Measure.map_map hg hT]
  exact (indepFun_iff_map_prod_eq_prod_map_map (hf.comp hT).aemeasurable
    (hg.comp hT).aemeasurable).mp h

/-- The edge coordinate at the distinguished support. -/
private abbrev AtIdx (A₀ : RankSupport digraphSig 2) := {x : RankSupport digraphSig 2 // x = A₀}

/-- The edge coordinates away from the distinguished support. -/
private abbrev OffIdx (A₀ : RankSupport digraphSig 2) :=
  {x : RankSupport digraphSig 2 // ¬(x = A₀)}

open scoped Classical in
/-- **Splitting the edge source at one coordinate.** -/
private theorem iidUniformSource_split (A₀ : RankSupport digraphSig 2) :
    (iidUniformSource (RankSupport digraphSig 2)).map
        (fun u : Edges => ((fun B : AtIdx A₀ => u B.1), (fun B : OffIdx A₀ => u B.1))) =
      (iidUniformSource (AtIdx A₀)).prod (iidUniformSource (OffIdx A₀)) := by
  have hpre : Measurable fun (u : Edges) (i : AtIdx A₀ ⊕ OffIdx A₀) =>
      u (Equiv.sumCompl (fun x : RankSupport digraphSig 2 => x = A₀) i) :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  rw [show (fun u : Edges => ((fun B : AtIdx A₀ => u B.1), (fun B : OffIdx A₀ => u B.1))) =
      ⇑(MeasurableEquiv.sumPiEquivProdPi fun _ : AtIdx A₀ ⊕ OffIdx A₀ => ℝ) ∘
        (fun (u : Edges) (i : AtIdx A₀ ⊕ OffIdx A₀) =>
          u (Equiv.sumCompl (fun x : RankSupport digraphSig 2 => x = A₀) i)) from rfl,
    ← Measure.map_map (MeasurableEquiv.sumPiEquivProdPi
      fun _ : AtIdx A₀ ⊕ OffIdx A₀ => ℝ).measurable hpre,
    iidUniformSource,
    Measure.infinitePi_map_comp_equiv _
      (Equiv.sumCompl (fun x : RankSupport digraphSig 2 => x = A₀)),
    Measure.infinitePi_map_sumPiEquivProdPi]
  rfl

/-- The source observation: the distinguished edge coordinate, against everything else. -/
private def srcObs (A₀ : RankSupport digraphSig 2) :
    Edges × RankLatentSpace digraphSig 2 →
      (AtIdx A₀ → ℝ) × ((OffIdx A₀ → ℝ) × RankLatentSpace digraphSig 2) :=
  fun p => ((fun B => p.1 B.1), ((fun B => p.1 B.1), p.2))

private theorem measurable_srcObs (A₀ : RankSupport digraphSig 2) : Measurable (srcObs A₀) :=
  ((measurable_pi_lambda _ fun _ => measurable_fst.eval)).prodMk
    ((measurable_pi_lambda _ fun _ => measurable_fst.eval).prodMk measurable_snd)

private theorem map_srcObs (A₀ : RankSupport digraphSig 2) :
    ((iidUniformSource (RankSupport digraphSig 2)).prod
        (rankLatentSource digraphSig 2)).map (srcObs A₀) =
      (iidUniformSource (AtIdx A₀)).prod
        ((iidUniformSource (OffIdx A₀)).prod (rankLatentSource digraphSig 2)) := by
  have hsplit : Measurable
      (fun u : Edges => ((fun B : AtIdx A₀ => u B.1), (fun B : OffIdx A₀ => u B.1))) :=
    (measurable_pi_lambda _ fun _ => measurable_pi_apply _).prodMk
      (measurable_pi_lambda _ fun _ => measurable_pi_apply _)
  rw [show srcObs A₀ = ⇑(MeasurableEquiv.prodAssoc) ∘
      Prod.map (fun u : Edges => ((fun B : AtIdx A₀ => u B.1), (fun B : OffIdx A₀ => u B.1)))
        (id : RankLatentSpace digraphSig 2 → _) from rfl,
    ← Measure.map_map (MeasurableEquiv.prodAssoc).measurable (hsplit.prodMap measurable_id),
    ← Measure.map_prod_map _ _ hsplit measurable_id, iidUniformSource_split, Measure.map_id,
    Measure.prodAssoc_prod]

private theorem indepFun_srcObs (A₀ : RankSupport digraphSig 2) :
    IndepFun (fun p => (srcObs A₀ p).1) (fun p => (srcObs A₀ p).2)
      ((iidUniformSource (RankSupport digraphSig 2)).prod (rankLatentSource digraphSig 2)) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map (measurable_srcObs A₀).fst.aemeasurable
      (measurable_srcObs A₀).snd.aemeasurable,
    show (fun p => ((srcObs A₀ p).1, (srcObs A₀ p).2)) = srcObs A₀ from rfl,
    show (fun p => (srcObs A₀ p).1) = Prod.fst ∘ srcObs A₀ from rfl,
    show (fun p => (srcObs A₀ p).2) = Prod.snd ∘ srcObs A₀ from rfl,
    ← Measure.map_map measurable_fst (measurable_srcObs A₀),
    ← Measure.map_map measurable_snd (measurable_srcObs A₀),
    map_srcObs A₀, Measure.map_fst_prod, Measure.map_snd_prod]
  simp

open scoped Classical in
/-- The block at the distinguished support, read off its own edge coordinate. -/
private noncomputable def blockDecoder (A₀ : RankSupport digraphSig 2) :
    (AtIdx A₀ → ℝ) → BlockSpace (S := digraphSig) A₀.1 :=
  fun t _ => decide (t ⟨A₀, rfl⟩ ≤ 1 / 2)

open scoped Classical in
private theorem measurable_blockDecoder (A₀ : RankSupport digraphSig 2) :
    Measurable (blockDecoder A₀) :=
  measurable_pi_lambda _ fun _ => measurable_decideLe (measurable_pi_apply _)

open scoped Classical in
/-- The remainder, read off the other edge coordinates and the latent array. -/
private noncomputable def restDecoder (A₀ : RankSupport digraphSig 2) :
    (OffIdx A₀ → ℝ) × RankLatentSpace digraphSig 2 →
      RestSpace (S := digraphSig) 2 A₀.1 × RankLatentSpace digraphSig 2 :=
  fun q => (fun c => if h : c.1.support.card = 2 then
      decide (q.1 ⟨⟨c.1.support, h⟩, fun hEq => c.2.2 (congrArg Subtype.val hEq)⟩ ≤ 1 / 2)
    else false, q.2)

open scoped Classical in
private theorem measurable_restDecoder (A₀ : RankSupport digraphSig 2) :
    Measurable (restDecoder A₀) := by
  refine (measurable_pi_lambda _ fun c => ?_).prodMk measurable_snd
  by_cases h : c.1.support.card = 2
  · simp only [dif_pos h]
    exact measurable_decideLe measurable_fst.eval
  · simp only [dif_neg h]
    exact measurable_const

open scoped Classical in
private theorem block_comp (A₀ : RankSupport digraphSig 2) :
    (blockMap (S := digraphSig) A₀.1 ∘ Prod.fst) ∘
        Prod.map arr (id : RankLatentSpace digraphSig 2 → _) =
      blockDecoder A₀ ∘ fun p => (srcObs A₀ p).1 := by
  funext p
  show blockMap (S := digraphSig) A₀.1 (arr p.1) = _
  rw [blockMap_arr_of_card_eq_two A₀.2]
  rfl

open scoped Classical in
private theorem rest_comp (A₀ : RankSupport digraphSig 2) :
    restObservation (S := digraphSig) 2 A₀.1 ∘
        Prod.map arr (id : RankLatentSpace digraphSig 2 → _) =
      restDecoder A₀ ∘ fun p => (srcObs A₀ p).2 := by
  funext p
  refine Prod.ext ?_ rfl
  funext c
  rfl

open scoped Classical in
/-- **The block is independent of the remainder**: they read disjoint edge coordinates, and the
latent array is an independent factor. -/
private theorem indepFun_block_rest (A₀ : RankSupport digraphSig 2) :
    IndepFun (blockMap (S := digraphSig) A₀.1 ∘ Prod.fst)
      (restObservation (S := digraphSig) 2 A₀.1) rankTwoCoupling := by
  have hcoupling : rankTwoCoupling =
      ((iidUniformSource (RankSupport digraphSig 2)).prod
        (rankLatentSource digraphSig 2)).map
          (Prod.map arr (id : RankLatentSpace digraphSig 2 → _)) := by
    rw [rankTwoCoupling, iidEdgeLaw, ← Measure.map_prod_map _ _ measurable_arr measurable_id,
      Measure.map_id]
  rw [hcoupling]
  refine indepFun_of_map (measurable_arr.prodMap measurable_id)
    ((measurable_blockMap (S := digraphSig) A₀.1).comp measurable_fst)
    (measurable_restObservation 2 A₀.1) ?_
  rw [block_comp A₀, rest_comp A₀]
  exact (indepFun_srcObs A₀).comp (measurable_blockDecoder A₀) (measurable_restDecoder A₀)

open scoped Classical in
/-- **Rank-two screening**: at a two-point support the block is conditionally independent of the
rank-truncated remainder given the latents visible there — because it is independent of that
remainder outright, and the conditioning algebra sits inside the remainder's. -/
theorem screening_rank_two (A : Finset (Σ _ : Unit, ℕ)) (hA : A.card = 2) :
    CondIndepFun (MeasurableSpace.comap
        (localLatents (S := digraphSig) A 2 ∘ Prod.snd) inferInstance)
      (((measurable_localLatents (S := digraphSig) A 2).comp measurable_snd).comap_le)
      (blockMap (S := digraphSig) A ∘ Prod.fst) (restObservation 2 A) rankTwoCoupling := by
  have hm' : MeasurableSpace.comap
      (localLatents (S := digraphSig) A 2 ∘ Prod.snd) inferInstance ≤
        MeasurableSpace.comap (restObservation (S := digraphSig) 2 A) inferInstance := by
    rw [show (localLatents (S := digraphSig) A 2 ∘ Prod.snd) =
        (localLatents (S := digraphSig) A 2 ∘ Prod.snd) ∘
          restObservation (S := digraphSig) 2 A from rfl,
      ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono
      ((measurable_localLatents (S := digraphSig) A 2).comp measurable_snd).comap_le
  exact condIndepFun_of_indep_of_le
    ((measurable_blockMap (S := digraphSig) A).comp measurable_fst).comap_le
    (measurable_restObservation (S := digraphSig) 2 A).comap_le hm'
    ((IndepFun_iff_Indep _ _ _).mp (indepFun_block_rest (⟨A, hA⟩ : RankSupport digraphSig 2)))
    (comap_measurable _) (comap_measurable _)

/-! ### Rank-three invariance, the two representations, and the successor witness -/

open scoped Classical in
/-- The fresh layer intertwines the rank-three latent action with the vertex action. -/
theorem freshLayer_rankLatentRelabel (σ : FinSuppPerm digraphSig)
    (ω : RankLatentSpace digraphSig 3) :
    freshLayer (rankLatentRelabel σ 3 ω) = fun A => freshLayer ω (rankSupportPerm σ.1 2 A) := by
  funext A
  show (rankLatentSpaceSuccEquiv 2 (rankLatentRelabel σ 3 ω)).2 A = _
  rw [show rankLatentSpaceSuccEquiv 2 (rankLatentRelabel σ 3 ω) =
      MeasurableEquiv.prodCongr (rankLatentRelabel σ 2) (rankSupportLatentRelabel σ 2)
        (rankLatentSpaceSuccEquiv 2 ω) from
    congrFun (rankLatentSpaceSuccEquiv_rankLatentRelabel σ 2) ω]
  rfl

open scoped Classical in
/-- **The exact pointwise joint action** at rank three. -/
theorem jointMap_rankLatentRelabel (σ : FinSuppPerm digraphSig)
    (ω : RankLatentSpace digraphSig 3) :
    (arr (freshLayer (rankLatentRelabel σ 3 ω)), rankLatentRelabel σ 3 ω) =
      Prod.map (RelStructure.relabel σ.1) (⇑(rankLatentRelabel σ 3))
        (arr (freshLayer ω), ω) := by
  refine Prod.ext ?_ rfl
  show arr (freshLayer (rankLatentRelabel σ 3 ω)) = RelStructure.relabel σ.1 (arr (freshLayer ω))
  rw [freshLayer_rankLatentRelabel, arr_comp_supportPerm]

/-- **Rank-three invariance**: the joint action, then source invariance. -/
theorem rankThreeCoupling_invariant (σ : FinSuppPerm digraphSig) :
    rankThreeCoupling.map (Prod.map (RelStructure.relabel σ.1) (⇑(rankLatentRelabel σ 3))) =
      rankThreeCoupling := by
  rw [rankThreeCoupling, Measure.map_map
      ((measurable_relabel σ.1).prodMap (rankLatentRelabel σ 3).measurable)
      measurable_rankThreeMap,
    show (Prod.map (RelStructure.relabel σ.1) (⇑(rankLatentRelabel σ 3)) ∘
        fun ω : RankLatentSpace digraphSig 3 => (arr (freshLayer ω), ω)) =
      (fun ω : RankLatentSpace digraphSig 3 => (arr (freshLayer ω), ω)) ∘
        (rankLatentRelabel σ 3) from by
      funext ω
      exact (jointMap_rankLatentRelabel σ ω).symm,
    ← Measure.map_map measurable_rankThreeMap (rankLatentRelabel σ 3).measurable,
    rankLatentSource_map_rankLatentRelabel]

/-- **The rank-three representation** of the i.i.d.-edge law. Defined first: the rank-two
representation's fixing completeness descends from it along the truncation identity. -/
noncomputable def rankThreeRep : iidEdgeExchangeable.RankRepresentation 3 where
  P := rankThreeCoupling
  isProbabilityMeasure_P := inferInstance
  map_fst := rankThreeCoupling_map_fst
  map_snd := rankThreeCoupling_map_snd
  invariant := rankThreeCoupling_invariant
  lower_recovers := lower_recovers_rank_three
  fixing_complete := fun _ _ E hE =>
    ⟨(arr ∘ freshLayer) ⁻¹' E,
      (measurable_arr.comp measurable_freshLayer) (RelStructure.fixingAlgebra_le _ E hE),
      snd_preimage_ae_eq_fst_preimage_map_graph (measurable_arr.comp measurable_freshLayer)
        (RelStructure.fixingAlgebra_le _ E hE)⟩
  screening := screening_rank_three

/-- **The rank-two representation** of the same law. -/
noncomputable def rankTwoRep : iidEdgeExchangeable.RankRepresentation 2 where
  P := rankTwoCoupling
  isProbabilityMeasure_P := inferInstance
  map_fst := rankTwoCoupling_map_fst
  map_snd := rankTwoCoupling_map_snd
  invariant := rankTwoCoupling_invariant
  lower_recovers := lower_recovers_rank_two
  fixing_complete :=
    -- the rank-two coupling is an independent product, so this is not read off a function of
    -- the latents; it descends from the rank-three representation along the gate identity
    rankThreeRep.fixing_complete_of_map_truncate (Nat.le_succ 2) rankThreeCoupling_truncation
  screening := screening_rank_two

/-- **The successor witness**: the rank-three representation truncates back to the
*independently defined* rank-two one, on the nose. -/
noncomputable def iidEdgeSuccessor :
    InfiniteRelExchangeableLaw.RankSuccessor rankTwoRep where
  next := rankThreeRep
  truncation := rankThreeCoupling_truncation

/-! ### Nondegeneracy and the decoding identity

Two statements recording that the regression is not vacuous. The half-threshold makes each edge
present with probability exactly one half, so no block is almost surely constant and the screening
clause has content; and at rank three the edge at a two-point support is visibly the thresholded
latent coordinate keyed by that support. -/

open scoped Classical in
/-- The source mass of a half-threshold event at one coordinate is exactly one half. -/
theorem iidUniformSource_threshold (A₀ : RankSupport digraphSig 2) :
    iidUniformSource (RankSupport digraphSig 2) {u : Edges | u A₀ ≤ 1 / 2} =
      ENNReal.ofReal (1 / 2) := by
  have hset : {u : Edges | u A₀ ≤ 1 / 2} =
      Set.pi (↑({A₀} : Finset (RankSupport digraphSig 2))) fun _ => Set.Iic (1 / 2 : ℝ) := by
    ext u
    simp
  rw [hset, iidUniformSource,
    Measure.infinitePi_pi (μ := fun _ : RankSupport digraphSig 2 => uniform01)
      (fun i _ => measurableSet_Iic),
    Finset.prod_singleton, uniform01_Iic (by norm_num)]

open scoped Classical in
/-- **Nondegeneracy**: each edge at a two-point support is present with probability exactly one
half. The block is therefore not almost surely constant, so rank-two screening is a genuine
conditional-independence statement rather than a determinism statement in disguise. -/
theorem iidEdgeLaw_edge_eq_half {u v : ℕ} (huv : u ≠ v) :
    iidEdgeLaw {X | X (digraphCoord u v) = true} = ENNReal.ofReal (1 / 2) := by
  have hcard := card_support_digraphCoord huv
  have hmeas : MeasurableSet {X : RelStructure digraphSig (Vinfinite digraphSig) |
      X (digraphCoord u v) = true} := by
    have h : Measurable fun X : RelStructure digraphSig (Vinfinite digraphSig) =>
        X (digraphCoord u v) := measurable_pi_apply _
    exact h (measurableSet_singleton true)
  have hpre : arr ⁻¹' {X : RelStructure digraphSig (Vinfinite digraphSig) |
      X (digraphCoord u v) = true} =
      {e : Edges | e (Subtype.mk _ hcard : RankSupport digraphSig 2) ≤ 1 / 2} := by
    ext e
    show arr e (digraphCoord u v) = true ↔ _
    rw [arr, dif_pos hcard]
    exact decide_eq_true_iff
  rw [iidEdgeLaw, Measure.map_apply measurable_arr hmeas, hpre,
    iidUniformSource_threshold]

open scoped Classical in
/-- **The decoding identity**: under the rank-three coupling the edge at a two-point support is
the thresholded latent coordinate keyed by that support — the staging property in its most
concrete form. -/
theorem ae_edge_eq_decode {u v : ℕ} (huv : u ≠ v) :
    (fun p : RelStructure digraphSig (Vinfinite digraphSig) × RankLatentSpace digraphSig 3 =>
        p.1 (digraphCoord u v)) =ᵐ[rankThreeCoupling]
      fun p => decide (p.2 (Subtype.mk (digraphCoord u v).support
        (by rw [card_support_digraphCoord huv]; omega) : RankLatentIndex digraphSig 3) ≤ 1 / 2) := by
  have hcard := card_support_digraphCoord huv
  rw [rankThreeCoupling]
  refine (ae_map_iff measurable_rankThreeMap.aemeasurable ?_).mpr
    (Filter.Eventually.of_forall fun ω => ?_)
  · exact measurableSet_eq_fun (measurable_fst.eval)
      (measurable_decideLe (measurable_snd.eval))
  · show arr (freshLayer ω) (digraphCoord u v) = _
    rw [arr, dif_pos hcard]
    rfl

end IidEdgeRegression

end RelSignature
