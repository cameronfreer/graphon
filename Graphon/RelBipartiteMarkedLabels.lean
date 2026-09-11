/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelBipartiteScreening
import Graphon.RelPooledFixingSeam

/-!
# Marked labels in the pooled bipartite law (R4 converse, #107, #197)

A bit-valued positive test of the mechanism that survives the screening failure: the pooled
structure, read at supports marked by one spare vertex, supplies consistent labels that the
original singleton fixing factors cannot.

In the pooled extension of the bipartite rank-one representation, fix the spare vertex `s₀` and
read at each original vertex `v` the marked label `label v Y := Y (o_v, s₀)`. The labels are
observations of the pooled structure; no hidden colours enter their definition. Their joint law
is the fair product, they are independent of the retained old latent, the original edge at
`(u, v)` is almost surely the parity `label u ⊕ label v`, the original structure–old-latent
marginal is recovered exactly, and the labels are natural under original-vertex relabelings
fixing the mark.

This is a regression for a viable mechanism. It asserts nothing about general admissibility
preservation and packages no successor.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RelSignature

namespace BipartiteRegression

open InfiniteRelExchangeableLaw ColourLaw

/-- The spare mark. -/
abbrev mark : PoolVertex digraphSig () := Sum.inr 0

/-- **The marked label** at an original vertex: the pooled edge to the mark. -/
def label (v : ℕ) (Y : RelStructure digraphSig (PoolVertex digraphSig)) : Bool :=
  Y (digraphCoord (Sum.inl v) mark)

/-- The pooled extension of the bipartite rank-one representation. -/
noncomputable abbrev Q : PooledRankExtension rankOneRep := rankOneRep.pooledExtension

/-- The pooled law. -/
noncomputable abbrev μQ : Measure (RelStructure digraphSig (PoolVertex digraphSig) ×
    PooledRankLatentSpace digraphSig 1) :=
  (Q.law : Measure (RelStructure digraphSig (PoolVertex digraphSig) ×
    PooledRankLatentSpace digraphSig 1))

instance : IsProbabilityMeasure μQ := Q.law.2

/-- All marked labels, read on the pooled space. -/
def labels (p : RelStructure digraphSig (PoolVertex digraphSig) ×
    PooledRankLatentSpace digraphSig 1) : ℕ → Bool :=
  fun v => label v p.1

theorem measurable_labels : Measurable labels :=
  measurable_pi_lambda _ fun _ => (measurable_pi_apply _).comp measurable_fst

/-! ### The identified structure and latents -/

/-- The identified structure. -/
noncomputable abbrev idStructure : RelStructure digraphSig (PoolVertex digraphSig) ×
    PooledRankLatentSpace digraphSig 1 → RelStructure digraphSig (Vinfinite digraphSig) :=
  poolStructureEquiv digraphSig ∘ Prod.fst

theorem measurable_idStructure : Measurable idStructure :=
  (poolStructureEquiv digraphSig).measurable.comp measurable_fst

/-- The identified latents. -/
noncomputable abbrev idLatents : RelStructure digraphSig (PoolVertex digraphSig) ×
    PooledRankLatentSpace digraphSig 1 → RankLatentSpace digraphSig 1 :=
  latentRestrictOver (fun s => (poolVertexEquiv digraphSig s).symm.toEmbedding) 1 ∘ Prod.snd

theorem measurable_idLatents : Measurable idLatents :=
  (measurable_latentRestrictOver _ 1).comp measurable_snd

theorem map_idPair : μQ.map (fun p => (idStructure p, idLatents p)) = rankOneCoupling :=
  Q.map_poolVertexEquiv

theorem map_idStructure : μQ.map idStructure = bipartiteLaw := by
  rw [show idStructure = Prod.fst ∘ fun p => (idStructure p, idLatents p) from rfl,
    ← Measure.map_map measurable_fst (measurable_idStructure.prodMk measurable_idLatents),
    map_idPair, rankOneCoupling_map_fst]

theorem map_idLatents : μQ.map idLatents = rankLatentSource digraphSig 1 := by
  rw [show idLatents = Prod.snd ∘ fun p => (idStructure p, idLatents p) from rfl,
    ← Measure.map_map measurable_snd (measurable_idStructure.prodMk measurable_idLatents),
    map_idPair, rankOneCoupling_map_snd]

theorem indepFun_idStructure_idLatents : IndepFun idStructure idLatents μQ := by
  refine (indepFun_iff_map_prod_eq_prod_map_map measurable_idStructure.aemeasurable
    measurable_idLatents.aemeasurable).mpr ?_
  rw [map_idPair, map_idStructure, map_idLatents]
  rfl

/-! ### The labels read the identified structure at the marked pairs -/

theorem poolVertexEquiv_inl (v : ℕ) : poolVertexEquiv digraphSig () (Sum.inl v) = 2 * v := by
  simp [poolVertexEquiv, Equiv.natSumNatEquivNat_apply]

theorem poolVertexEquiv_mark : poolVertexEquiv digraphSig () mark = 1 := by
  simp [poolVertexEquiv, Equiv.natSumNatEquivNat_apply]

theorem poolStructureEquiv_digraphCoord (Y : RelStructure digraphSig (PoolVertex digraphSig))
    (a b : ℕ) :
    poolStructureEquiv digraphSig Y (digraphCoord a b) =
      Y (digraphCoord ((poolVertexEquiv digraphSig ()).symm a)
        ((poolVertexEquiv digraphSig ()).symm b)) := by
  show Y (RelCoord.map (fun s => ((poolVertexEquiv digraphSig s).symm : ℕ → _)) _) = _
  congr 1
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext i; fin_cases i <;> rfl

/-- The labels are the identified structure at the marked pairs `(2v, 1)`. -/
def labelsOf (X : RelStructure digraphSig (Vinfinite digraphSig)) : ℕ → Bool :=
  fun v => X (digraphCoord (2 * v) 1)

theorem measurable_labelsOf : Measurable labelsOf :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

theorem poolVertexEquiv_symm_two_mul (v : ℕ) :
    (poolVertexEquiv digraphSig ()).symm (2 * v) = Sum.inl v := by
  rw [Equiv.symm_apply_eq, poolVertexEquiv_inl]

theorem poolVertexEquiv_symm_one : (poolVertexEquiv digraphSig ()).symm 1 = mark := by
  rw [Equiv.symm_apply_eq, poolVertexEquiv_mark]

theorem labels_eq : labels = labelsOf ∘ idStructure := by
  funext p v
  show label v p.1 = poolStructureEquiv digraphSig p.1 (digraphCoord (2 * v) 1)
  rw [poolStructureEquiv_digraphCoord, poolVertexEquiv_symm_two_mul, poolVertexEquiv_symm_one]
  rfl

theorem labelsOf_arr (ω : Colours) :
    labelsOf (arr ω) = fun v => xor (colour ω (2 * v)) (colour ω 1) := rfl

/-! ### The joint fair-product law -/

/-- The fair bit. -/
noncomputable def fairBit : Measure Bool := uniform01.map fun t : ℝ => decide (t ≤ 1 / 2)

instance : IsProbabilityMeasure fairBit :=
  Measure.isProbabilityMeasure_map (measurable_decideLe measurable_id).aemeasurable

theorem fairBit_map_not : fairBit.map not = fairBit := ColourLaw.uniform01_map_decide_not

theorem measurable_decideHalf : Measurable fun t : ℝ => decide (t ≤ 1 / 2) :=
  measurable_decideLe measurable_id

theorem fairBit_false : fairBit {false} = 1 / 2 := by
  rw [fairBit, Measure.map_apply measurable_decideHalf (measurableSet_singleton _),
    show (fun t : ℝ => decide (t ≤ 1 / 2)) ⁻¹' {false} = (Set.Iic (1 / 2 : ℝ))ᶜ from by
      ext t; simp, ColourLaw.uniform01_Iic_half_compl]

theorem fairBit_true : fairBit {true} = 1 / 2 := by
  rw [fairBit, Measure.map_apply measurable_decideHalf (measurableSet_singleton _),
    show (fun t : ℝ => decide (t ≤ 1 / 2)) ⁻¹' {true} = Set.Iic (1 / 2 : ℝ) from by
      ext t; simp, ColourLaw.uniform01_Iic_half]

/-- The even colours. -/
noncomputable def evens (ω : Colours) : ℕ → Bool := fun v => colour ω (2 * v)

/-- The colour at the identified mark. -/
noncomputable def markBit (ω : Colours) : Bool := colour ω 1

theorem measurable_evens : Measurable evens :=
  measurable_pi_lambda _ fun v => measurable_colour (2 * v)

theorem measurable_markBit : Measurable markBit := measurable_colour 1

/-- The even singleton supports and the odd singleton supports, as two disjoint blocks. -/
def blockIdx (p : Σ _ : Bool, ℕ) : RankSupport digraphSig 1 :=
  if p.1 then vertexSupport (2 * p.2) else vertexSupport (2 * p.2 + 1)

theorem blockIdx_injective : Function.Injective blockIdx := by
  rintro ⟨b, x⟩ ⟨b', y⟩ h
  cases b <;> cases b' <;> simp only [blockIdx, Bool.false_eq_true, ↓reduceIte] at h <;>
    have := vertexSupport_injective h
  · exact congrArg (fun v : ℕ => (⟨false, v⟩ : Σ _ : Bool, ℕ)) (by omega)
  · omega
  · omega
  · exact congrArg (fun v : ℕ => (⟨true, v⟩ : Σ _ : Bool, ℕ)) (by omega)

/-- The even colours are independent of the mark's colour. -/
theorem indepFun_evens_markBit :
    IndepFun evens markBit (iidUniformSource (RankSupport digraphSig 1)) := by
  have hblocks := iIndepFun_infinitePi_blocks (fun _ : RankSupport digraphSig 1 => uniform01)
    blockIdx_injective
  rw [← iidUniformSource] at hblocks
  have h := hblocks.indepFun (i := true) (j := false) (by decide)
  refine (h.comp (φ := fun x : ℕ → ℝ => fun v => decide (x v ≤ 1 / 2))
    (ψ := fun x : ℕ → ℝ => decide (x 0 ≤ 1 / 2))
    (measurable_pi_lambda _ fun _ => measurable_decideLe (measurable_pi_apply _))
    (measurable_decideLe (measurable_pi_apply _))).congr ?_ ?_
  · exact Filter.EventuallyEq.of_eq (funext fun ω => funext fun v => by
      simp [blockIdx, evens, colour])
  · exact Filter.EventuallyEq.of_eq (funext fun ω => by simp [blockIdx, markBit, colour])

/-- The law of the even colours is the fair product. -/
theorem map_evens :
    (iidUniformSource (RankSupport digraphSig 1)).map evens =
      Measure.infinitePi fun _ : ℕ => fairBit := by
  have hread : Measurable fun (ω : Colours) (v : ℕ) => ω (vertexSupport (2 * v)) :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  have hinj : Function.Injective fun v : ℕ => vertexSupport (2 * v) := fun a b h => by
    have := vertexSupport_injective h; omega
  have hψ : Measurable fun (x : ℕ → ℝ) (v : ℕ) => decide (x v ≤ 1 / 2) :=
    measurable_pi_lambda _ fun v => measurable_decideLe (measurable_pi_apply v)
  rw [show evens = (fun (x : ℕ → ℝ) (v : ℕ) => decide (x v ≤ 1 / 2)) ∘
      fun (ω : Colours) (v : ℕ) => ω (vertexSupport (2 * v)) from rfl,
    ← Measure.map_map hψ hread,
    iidUniformSource, Measure.map_infinitePi_infinitePi_of_inj hinj,
    Measure.infinitePi_map_pi (μ := fun _ : ℕ => uniform01)
      (f := fun _ t => decide (t ≤ 1 / 2)) (fun _ => measurable_decideLe measurable_id)]
  rfl

/-- The fair product is invariant under flipping every bit. -/
theorem infinitePi_fairBit_map_not :
    (Measure.infinitePi fun _ : ℕ => fairBit).map (fun d : ℕ → Bool => fun v => !d v) =
      Measure.infinitePi fun _ : ℕ => fairBit := by
  rw [Measure.infinitePi_map_pi (μ := fun _ : ℕ => fairBit) (f := fun _ => not)
    (fun _ => Measurable.of_discrete)]
  simp only [fairBit_map_not]

theorem source_markBit_false :
    (iidUniformSource (RankSupport digraphSig 1)) {ω | markBit ω = false} = 1 / 2 := by
  have h : (iidUniformSource (RankSupport digraphSig 1)).map markBit = fairBit := by
    rw [show markBit = (fun t : ℝ => decide (t ≤ 1 / 2)) ∘ fun ω : Colours => ω (vertexSupport 1)
      from rfl, ← Measure.map_map measurable_decideHalf
        (measurable_pi_apply (vertexSupport 1) : Measurable fun ω : Colours => ω (vertexSupport 1)),
      iidUniformSource, Measure.infinitePi_map_eval]
    rfl
  rw [show {ω : Colours | markBit ω = false} = markBit ⁻¹' {false} from rfl,
    ← Measure.map_apply measurable_markBit (measurableSet_singleton _), h, fairBit_false]

theorem source_markBit_true :
    (iidUniformSource (RankSupport digraphSig 1)) {ω | markBit ω = true} = 1 / 2 := by
  have h : (iidUniformSource (RankSupport digraphSig 1)).map markBit = fairBit := by
    rw [show markBit = (fun t : ℝ => decide (t ≤ 1 / 2)) ∘ fun ω : Colours => ω (vertexSupport 1)
      from rfl, ← Measure.map_map measurable_decideHalf
        (measurable_pi_apply (vertexSupport 1) : Measurable fun ω : Colours => ω (vertexSupport 1)),
      iidUniformSource, Measure.infinitePi_map_eval]
    rfl
  rw [show {ω : Colours | markBit ω = true} = markBit ⁻¹' {true} from rfl,
    ← Measure.map_apply measurable_markBit (measurableSet_singleton _), h, fairBit_true]

/-- **The labels are jointly fair**: conditional on the mark's colour, flipping all the
independent original colours preserves their product law. -/
theorem map_labelsOf_bipartiteLaw :
    bipartiteLaw.map labelsOf = Measure.infinitePi fun _ : ℕ => fairBit := by
  set μ := iidUniformSource (RankSupport digraphSig 1) with hμ
  rw [bipartiteLaw, Measure.map_map measurable_labelsOf measurable_arr]
  have hcomp : labelsOf ∘ arr = fun ω : Colours => fun v => xor (evens ω v) (markBit ω) := rfl
  rw [hcomp]
  refine Measure.ext fun B hB => ?_
  have hm : Measurable fun ω : Colours => fun v => xor (evens ω v) (markBit ω) :=
    measurable_pi_lambda _ fun v =>
      Measurable.comp (g := fun p : Bool × Bool => xor p.1 p.2) Measurable.of_discrete
        (((measurable_pi_apply v).comp measurable_evens).prodMk measurable_markBit)
  rw [Measure.map_apply hm hB]
  have hind := indepFun_iff_measure_inter_preimage_eq_mul.mp indepFun_evens_markBit
  have hnot : Measurable fun d : ℕ → Bool => fun v => !d v :=
    measurable_pi_lambda _ fun v => Measurable.comp (g := not) Measurable.of_discrete
      (measurable_pi_apply v)
  have hnotm : MeasurableSet ((fun d : ℕ → Bool => fun v => !d v) ⁻¹' B) := hnot hB
  -- split by the mark's colour
  have hsplit : (fun ω : Colours => fun v => xor (evens ω v) (markBit ω)) ⁻¹' B =
      (evens ⁻¹' B ∩ markBit ⁻¹' {false}) ∪
        (evens ⁻¹' ((fun d : ℕ → Bool => fun v => !d v) ⁻¹' B) ∩ markBit ⁻¹' {true}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_inter_iff, Set.mem_singleton_iff]
    cases markBit ω <;> simp
  have hdisj : Disjoint (evens ⁻¹' B ∩ markBit ⁻¹' {false})
      (evens ⁻¹' ((fun d : ℕ → Bool => fun v => !d v) ⁻¹' B) ∩ markBit ⁻¹' {true}) := by
    rw [Set.disjoint_left]
    rintro ω ⟨-, h0⟩ ⟨-, h1⟩
    exact Bool.false_ne_true (h0.symm.trans h1)
  rw [hsplit, measure_union hdisj ((measurable_evens hnotm).inter
    (measurable_markBit (measurableSet_singleton _))),
    hind B {false} hB (measurableSet_singleton _),
    hind _ {true} hnotm (measurableSet_singleton _),
    ← Measure.map_apply measurable_evens hB, ← Measure.map_apply measurable_evens hnotm, map_evens,
    ← Measure.map_apply hnot hB, infinitePi_fairBit_map_not]
  rw [show markBit ⁻¹' {false} = {ω | markBit ω = false} from rfl,
    show markBit ⁻¹' {true} = {ω | markBit ω = true} from rfl, source_markBit_false,
    source_markBit_true, ← mul_add, one_div, ENNReal.inv_two_add_inv_two, mul_one]

theorem map_labels : μQ.map labels = Measure.infinitePi fun _ : ℕ => fairBit := by
  rw [labels_eq, ← Measure.map_map measurable_labelsOf measurable_idStructure, map_idStructure,
    map_labelsOf_bipartiteLaw]

/-! ### Independence from the retained old latent -/

/-- The old latent, read on the pooled space. -/
noncomputable abbrev oldLatent : RelStructure digraphSig (PoolVertex digraphSig) ×
    PooledRankLatentSpace digraphSig 1 → RankLatentSpace digraphSig 1 :=
  restrictOriginalLatents digraphSig 1 ∘ Prod.snd

theorem measurable_oldLatent : Measurable oldLatent :=
  (measurable_restrictOriginalLatents 1).comp measurable_snd

theorem oldLatent_eq : oldLatent = latentRestrictOver (doubleEmb digraphSig) 1 ∘ idLatents := by
  have hemb : (fun s => (doubleEmb digraphSig s).trans
      (poolVertexEquiv digraphSig s).symm.toEmbedding) = originalVertex digraphSig := by
    funext s
    ext x
    show (poolVertexEquiv digraphSig s).symm (poolVertexEquiv digraphSig s (Sum.inl x)) = Sum.inl x
    exact Equiv.symm_apply_apply _ _
  show latentRestrictOver (originalVertex digraphSig) 1 ∘ Prod.snd =
    (latentRestrictOver (doubleEmb digraphSig) 1 ∘
      latentRestrictOver (fun s => (poolVertexEquiv digraphSig s).symm.toEmbedding) 1) ∘ Prod.snd
  rw [latentRestrictOver_comp, hemb]

/-- **The labels are independent of the old latent.** -/
theorem indepFun_labels_oldLatent : IndepFun labels oldLatent μQ := by
  rw [labels_eq, oldLatent_eq]
  exact indepFun_idStructure_idLatents.comp measurable_labelsOf (measurable_latentRestrictOver _ 1)

/-- **Exact recovery** of the original structure–old-latent marginal. -/
theorem map_original :
    μQ.map (Prod.map (restrictOriginal digraphSig) (restrictOriginalLatents digraphSig 1)) =
      rankOneCoupling :=
  Q.map_restrictOriginal

theorem map_oldLatent : μQ.map oldLatent = rankLatentSource digraphSig 1 := by
  rw [show oldLatent = Prod.snd ∘
      Prod.map (restrictOriginal digraphSig) (restrictOriginalLatents digraphSig 1) from rfl,
    ← Measure.map_map measurable_snd ((measurable_restrictOriginal).prodMap
      (measurable_restrictOriginalLatents 1)), map_original, rankOneCoupling_map_snd]

/-- **The joint law of the labels and the old latent** is the product of the fair product with
the rank-one source. -/
theorem map_labels_oldLatent :
    μQ.map (fun p => (labels p, oldLatent p)) =
      (Measure.infinitePi fun _ : ℕ => fairBit).prod (rankLatentSource digraphSig 1) := by
  rw [← map_labels, ← map_oldLatent]
  exact indepFun_labels_oldLatent.map_prod_eq_prod_map_map measurable_labels.aemeasurable
    measurable_oldLatent.aemeasurable

/-! ### The XOR recovery identity -/

/-- The original edge is the parity of the two marked labels, on every colouring. -/
theorem restrict_doubleEmb_arr_eq_xor (ω : Colours) (u v : ℕ) :
    RelStructure.restrict (doubleEmb digraphSig) (arr ω) (digraphCoord u v) =
      xor (labelsOf (arr ω) u) (labelsOf (arr ω) v) := by
  show xor (colour ω (poolVertexEquiv digraphSig () (Sum.inl u)))
      (colour ω (poolVertexEquiv digraphSig () (Sum.inl v))) =
    xor (xor (colour ω (2 * u)) (colour ω 1)) (xor (colour ω (2 * v)) (colour ω 1))
  rw [poolVertexEquiv_inl, poolVertexEquiv_inl]
  cases colour ω (2 * u) <;> cases colour ω (2 * v) <;> cases colour ω 1 <;> rfl

/-- **XOR recovery**: almost surely, every original edge is the parity of its two labels. -/
theorem ae_restrictOriginal_eq_xor_labels :
    ∀ᵐ p ∂μQ, ∀ u v : ℕ,
      restrictOriginal digraphSig p.1 (digraphCoord u v) = xor (labels p u) (labels p v) := by
  have hq : Measure.QuasiMeasurePreserving idStructure μQ bipartiteLaw :=
    (MeasurePreserving.mk measurable_idStructure map_idStructure).quasiMeasurePreserving
  have hlaw : ∀ᵐ X ∂bipartiteLaw, ∀ u v : ℕ,
      RelStructure.restrict (doubleEmb digraphSig) X (digraphCoord u v) =
        xor (labelsOf X u) (labelsOf X v) := by
    have hset : MeasurableSet {X : RelStructure digraphSig (Vinfinite digraphSig) | ∀ u v : ℕ,
        RelStructure.restrict (doubleEmb digraphSig) X (digraphCoord u v) =
          xor (labelsOf X u) (labelsOf X v)} := by
      rw [Set.setOf_forall]
      refine MeasurableSet.iInter fun u => ?_
      rw [Set.setOf_forall]
      refine MeasurableSet.iInter fun v => ?_
      exact measurableSet_eq_fun ((measurable_pi_apply _).comp (measurable_restrict _))
        (Measurable.comp (g := fun p : Bool × Bool => xor p.1 p.2) Measurable.of_discrete
          (((measurable_pi_apply u).comp measurable_labelsOf).prodMk
            ((measurable_pi_apply v).comp measurable_labelsOf)))
    rw [bipartiteLaw]
    exact (ae_map_iff measurable_arr.aemeasurable hset).mpr
      (Filter.Eventually.of_forall fun ω u v => restrict_doubleEmb_arr_eq_xor ω u v)
  filter_upwards [hq.ae hlaw] with p hp u v
  have h1 := hp u v
  rw [show idStructure p = poolStructureEquiv digraphSig p.1 from rfl,
    restrict_doubleEmb_poolStructureEquiv] at h1
  rw [labels_eq]
  exact h1

/-! ### Naturality under original-vertex relabelings fixing the mark -/

/-- The split lift of an original-vertex permutation: it acts on the original half and fixes
every spare vertex, in particular the mark. -/
def splitLift (σ : Equiv.Perm ℕ) : ∀ _ : Unit, Equiv.Perm (PoolVertex digraphSig ()) :=
  fun _ => Equiv.sumCongr σ (Equiv.refl ℕ)

/-- **Naturality of the labels**, exact: relabeling the original vertices reindexes the labels. -/
theorem label_relabel_splitLift (σ : Equiv.Perm ℕ) (v : ℕ)
    (Y : RelStructure digraphSig (PoolVertex digraphSig)) :
    label v (RelStructure.relabel (splitLift σ) Y) = label (σ v) Y := by
  show Y (RelCoord.map (fun s => ⇑(splitLift σ s)) (digraphCoord (Sum.inl v) mark)) = Y _
  congr 1
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext i; fin_cases i <;> rfl

theorem labels_relabel_splitLift (σ : Equiv.Perm ℕ)
    (p : RelStructure digraphSig (PoolVertex digraphSig) × PooledRankLatentSpace digraphSig 1) :
    labels (Prod.map (RelStructure.relabel (splitLift σ))
      (pooledRankLatentRelabel (S := digraphSig) (splitLift σ) 1) p) = fun v => labels p (σ v) :=
  funext fun v => label_relabel_splitLift σ v p.1

/-- The label law is invariant under the lifted relabeling, by the pooled law's invariance. -/
theorem map_labels_relabel_splitLift (σ : Equiv.Perm ℕ) :
    μQ.map (fun p => labels (Prod.map (RelStructure.relabel (S := digraphSig) (splitLift σ))
      (pooledRankLatentRelabel (S := digraphSig) (splitLift σ) 1) p)) = μQ.map labels := by
  have hm : Measurable (Prod.map (RelStructure.relabel (S := digraphSig) (splitLift σ))
      (pooledRankLatentRelabel (S := digraphSig) (splitLift σ) 1)) :=
    (measurable_relabel _).prodMap
      (pooledRankLatentRelabel (S := digraphSig) (splitLift σ) 1).measurable
  rw [show (fun p => labels (Prod.map (RelStructure.relabel (S := digraphSig) (splitLift σ))
      (pooledRankLatentRelabel (S := digraphSig) (splitLift σ) 1) p)) = labels ∘ Prod.map
      (RelStructure.relabel (S := digraphSig) (splitLift σ))
      (pooledRankLatentRelabel (S := digraphSig) (splitLift σ) 1) from rfl,
    ← Measure.map_map measurable_labels hm, Q.invariant]

end BipartiteRegression

end RelSignature
