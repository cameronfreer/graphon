/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRankSuccessorContract
import Graphon.InfiniteDigraph
import Graphon.ForMathlib.CondIndepSup

/-!
# The bipartite regression for the successor contract (R4 converse, #107)

A hand-built rank `1 → 2` successor witness for the one-sort binary signature `digraphSig`, whose
purpose is to test that `RankSuccessor` is an expressive specification — **before** either general
route is attempted, so that the acceptance battery cannot be shaped by an implementation.

The array is the bipartite XOR law: each vertex carries an i.i.d. colour, and the edge `X_uv` is
the parity `colour u ⊕ colour v`.

## What makes this a regression rather than merely a construction

* the array law `bipartiteLaw` is defined **from the fresh singleton layer alone**, and the
  rank-one coupling `C` is defined as the independent product `bipartiteLaw × rankLatentSource 1`.
  Neither is read off the rank-two coupling, so the truncation identity compares two separately
  described couplings and genuinely uses the source factorization;
* the nonindependence witness is **numerical**, not merely functional: `X_01` and the matching
  colour-parity event have joint probability `1/2` against a product of marginals `1/4`. "The edge
  is a function of the colours" would also hold for a constant edge and would certify nothing;
* the rank-two decoder recovers **both** directed coordinates `X_uv` and `X_vu` of the
  support-`{u,v}` block as the same parity, so symmetry is exhibited as a property of this law
  rather than something hidden in the signature. The diagonal singleton block is constantly
  `false`, which the XOR definition delivers for free.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

namespace BipartiteRegression

/-- The fresh singleton layer of the rank-two latent cube: one uniform per vertex. -/
abbrev Colours := RankSupport digraphSig 1 → ℝ

/-- The singleton support at a vertex. -/
def vertexSupport (v : ℕ) : RankSupport digraphSig 1 :=
  ⟨{⟨(), v⟩}, Finset.card_singleton _⟩

/-- The colour of a vertex, read off its own fresh coordinate. -/
noncomputable def colour (ω : Colours) (v : ℕ) : Bool := decide (ω (vertexSupport v) ≤ 1 / 2)

/-- **The bipartite array**: the edge at an ordered pair is the parity of the two colours. The
diagonal is constantly `false` because `b ⊕ b = false`. -/
noncomputable def arr (ω : Colours) : RelStructure digraphSig (Vinfinite digraphSig) :=
  fun c => xor (colour ω (c.2 0)) (colour ω (c.2 1))

@[simp] theorem arr_apply (ω : Colours) (u v : ℕ) :
    arr ω (digraphCoord u v) = xor (colour ω u) (colour ω v) := rfl

/-- **The diagonal is constantly false** — the singleton-support block of this law carries no
information, which is what makes its rank-one recovery and screening deterministic. -/
@[simp] theorem arr_diagonal (ω : Colours) (v : ℕ) : arr ω (digraphCoord v v) = false := by
  simp [arr_apply]

/-- Thresholding a measurable real at `1/2` is measurable. -/
theorem measurable_decideLe {X : Type*} [MeasurableSpace X] {f : X → ℝ} (hf : Measurable f) :
    Measurable fun x => decide (f x ≤ 1 / 2) := by
  refine measurable_to_countable' fun b => ?_
  cases b
  · have hpre : (fun x => decide (f x ≤ 1 / 2)) ⁻¹' {false} = {x | f x ≤ 1 / 2}ᶜ := by
      ext x; simp
    rw [hpre]
    exact (measurableSet_le hf measurable_const).compl
  · have hpre : (fun x => decide (f x ≤ 1 / 2)) ⁻¹' {true} = {x | f x ≤ 1 / 2} := by
      ext x; simp
    rw [hpre]
    exact measurableSet_le hf measurable_const

theorem measurable_colour (v : ℕ) : Measurable fun ω : Colours => colour ω v := by
  refine measurable_to_countable' fun b => ?_
  cases b
  · have hpre : (fun ω : Colours => colour ω v) ⁻¹' {false}
        = {ω : Colours | ω (vertexSupport v) ≤ 1 / 2}ᶜ := by
      ext ω; simp [colour]
    rw [hpre]
    exact (measurableSet_le (measurable_pi_apply _) measurable_const).compl
  · have hpre : (fun ω : Colours => colour ω v) ⁻¹' {true}
        = {ω : Colours | ω (vertexSupport v) ≤ 1 / 2} := by
      ext ω; simp [colour]
    rw [hpre]
    exact measurableSet_le (measurable_pi_apply _) measurable_const

theorem measurable_arr : Measurable arr := by
  refine measurable_pi_lambda _ fun c => ?_
  exact (Measurable.of_discrete (f := fun p : Bool × Bool => xor p.1 p.2)).comp
    ((measurable_colour (c.2 0)).prodMk (measurable_colour (c.2 1)))

/-! ### The relabeling action on the fresh layer -/

open scoped Classical in
/-- A permutation of the vertices permutes the singleton supports. -/
noncomputable def supportPerm (σ : Equiv.Perm ℕ) :
    RankSupport digraphSig 1 ≃ RankSupport digraphSig 1 where
  toFun A := ⟨A.1.image (Sigma.map id fun _ => ⇑σ), by
    rw [Finset.card_image_of_injective _
      (Function.injective_id.sigma_map fun _ => σ.injective)]
    exact A.2⟩
  invFun A := ⟨A.1.image (Sigma.map id fun _ => ⇑σ.symm), by
    rw [Finset.card_image_of_injective _
      (Function.injective_id.sigma_map fun _ => σ.symm.injective)]
    exact A.2⟩
  left_inv A := Subtype.ext (by
    show (A.1.image (Sigma.map id fun _ => ⇑σ)).image (Sigma.map id fun _ => ⇑σ.symm) = A.1
    rw [Finset.image_image]
    refine (Finset.image_congr fun v _ => ?_).trans A.1.image_id
    obtain ⟨s, x⟩ := v
    show (⟨s, σ.symm (σ x)⟩ : Σ _ : Unit, ℕ) = ⟨s, x⟩
    rw [σ.symm_apply_apply])
  right_inv A := Subtype.ext (by
    show (A.1.image (Sigma.map id fun _ => ⇑σ.symm)).image (Sigma.map id fun _ => ⇑σ) = A.1
    rw [Finset.image_image]
    refine (Finset.image_congr fun v _ => ?_).trans A.1.image_id
    obtain ⟨s, x⟩ := v
    show (⟨s, σ (σ.symm x)⟩ : Σ _ : Unit, ℕ) = ⟨s, x⟩
    rw [σ.apply_symm_apply])

open scoped Classical in
@[simp] theorem supportPerm_vertexSupport (σ : Equiv.Perm ℕ) (v : ℕ) :
    supportPerm σ (vertexSupport v) = vertexSupport (σ v) := by
  refine Subtype.ext ?_
  show ({(⟨(), v⟩ : Σ _ : Unit, ℕ)} : Finset _).image (Sigma.map id fun _ => ⇑σ)
    = ({⟨(), σ v⟩} : Finset (Σ _ : Unit, ℕ))
  rw [Finset.image_singleton]
  rfl

theorem colour_comp_supportPerm (σ : Equiv.Perm ℕ) (ω : Colours) (v : ℕ) :
    colour (fun A => ω (supportPerm σ A)) v = colour ω (σ v) := by
  simp [colour]

/-- **Equivariance of the array**: relabeling the vertices is reindexing the fresh layer. -/
theorem arr_comp_supportPerm (σ : Equiv.Perm ℕ) (ω : Colours) :
    arr (fun A => ω (supportPerm σ A)) =
      RelStructure.relabel (fun _ : Unit => σ) (arr ω) := by
  funext c
  show xor (colour (fun A => ω (supportPerm σ A)) (c.2 0))
      (colour (fun A => ω (supportPerm σ A)) (c.2 1)) = _
  rw [colour_comp_supportPerm, colour_comp_supportPerm]
  rfl

/-! ### The array law -/

/-- **The bipartite law**, defined from the fresh singleton layer alone — deliberately *not* read
off the rank-two coupling, so that the truncation identity later compares two independently
described couplings. -/
noncomputable def bipartiteLaw :
    Measure (RelStructure digraphSig (Vinfinite digraphSig)) :=
  (iidUniformSource (RankSupport digraphSig 1)).map arr

instance : IsProbabilityMeasure bipartiteLaw :=
  Measure.isProbabilityMeasure_map measurable_arr.aemeasurable

theorem bipartiteLaw_map_relabel (σ : ∀ _ : Unit, Equiv.Perm ℕ) :
    bipartiteLaw.map (RelStructure.relabel σ) = bipartiteLaw := by
  rw [bipartiteLaw, Measure.map_map (measurable_relabel σ) measurable_arr,
    show RelStructure.relabel σ ∘ arr =
      arr ∘ (fun ω : Colours => fun A => ω (supportPerm (σ ()) A)) from by
        funext ω
        exact (arr_comp_supportPerm (σ ()) ω).symm,
    ← Measure.map_map measurable_arr
      (measurable_pi_lambda _ fun _ => measurable_pi_apply _),
    iidUniformSource,
    Measure.infinitePi_map_comp_equiv _ (supportPerm (σ ()))]

/-- The bipartite law as an exchangeable law on the infinite structure space. -/
noncomputable def bipartiteExchangeable : InfiniteRelExchangeableLaw digraphSig where
  law := ⟨bipartiteLaw, inferInstance⟩
  exchangeable := bipartiteLaw_map_relabel

/-! ### Blocks of this signature

For `digraphSig` every coordinate has a two-element or one-element support, never the empty one,
and a singleton support forces the diagonal coordinate. -/

instance : IsEmpty (BlockIndex (S := digraphSig) (∅ : Finset (Σ _ : Unit, ℕ))) :=
  ⟨fun c => by
    have hne := RelCoord.support_nonempty c.1 (by norm_num)
    rw [c.2] at hne
    exact absurd hne (by simp)⟩

instance : Unique (BlockSpace (S := digraphSig) (∅ : Finset (Σ _ : Unit, ℕ))) :=
  Pi.uniqueOfIsEmpty _

open scoped Classical in
/-- A coordinate whose support is the singleton `{v}` is the diagonal coordinate at `v`. -/
theorem eq_digraphCoord_of_support_singleton {v : ℕ}
    (c : BlockIndex (S := digraphSig) ({⟨(), v⟩} : Finset (Σ _ : Unit, ℕ))) :
    c.1 = digraphCoord v v := by
  have h0 : c.1.taggedValue 0 ∈ c.1.support := (RelCoord.mem_support_iff _ _).mpr ⟨0, rfl⟩
  have h1 : c.1.taggedValue 1 ∈ c.1.support := (RelCoord.mem_support_iff _ _).mpr ⟨1, rfl⟩
  rw [c.2, Finset.mem_singleton] at h0 h1
  have e0 : c.1.2 0 = v := congrArg Sigma.snd h0
  have e1 : c.1.2 1 = v := congrArg Sigma.snd h1
  refine congrArg (fun w' => (⟨c.1.1, w'⟩ : RelCoord digraphSig (Vinfinite digraphSig))) ?_
  funext i
  fin_cases i
  · exact e0
  · exact e1

open scoped Classical in
/-- **The singleton block of this law is constantly `false`** — it reads only the diagonal. -/
theorem blockMap_singleton_arr (ω : Colours) (v : ℕ) :
    blockMap ({⟨(), v⟩} : Finset (Σ _ : Unit, ℕ)) (arr ω) = fun _ => false := by
  funext c
  show arr ω c.1 = false
  rw [eq_digraphCoord_of_support_singleton c, arr_diagonal]

/-! ### The rank-one coupling, defined independently of the rank-two one -/

/-- **The rank-one coupling**: the bipartite law together with an *independent* global uniform
`U_∅`. At rank one the latent cube is exactly that one coordinate — it is not trivial, and this
coupling is described without reference to the rank-two object. -/
noncomputable def rankOneCoupling :
    Measure (RelStructure digraphSig (Vinfinite digraphSig) × RankLatentSpace digraphSig 1) :=
  bipartiteLaw.prod (rankLatentSource digraphSig 1)

instance : IsProbabilityMeasure rankOneCoupling := by
  rw [rankOneCoupling]; infer_instance

@[simp] theorem rankOneCoupling_map_fst : rankOneCoupling.map Prod.fst = bipartiteLaw := by
  rw [rankOneCoupling, Measure.map_fst_prod]
  simp

@[simp] theorem rankOneCoupling_map_snd :
    rankOneCoupling.map Prod.snd = rankLatentSource digraphSig 1 := by
  rw [rankOneCoupling, Measure.map_snd_prod]
  simp

open scoped Classical in
/-- The singleton block is a.e. constant under the bipartite law. -/
theorem ae_blockMap_singleton (v : ℕ) :
    ∀ᵐ X ∂bipartiteLaw, blockMap ({⟨(), v⟩} : Finset (Σ _ : Unit, ℕ)) X = fun _ => false := by
  rw [bipartiteLaw]
  refine (ae_map_iff measurable_arr.aemeasurable ?_).mpr ?_
  · exact (measurable_blockMap (S := digraphSig)
      ({⟨(), v⟩} : Finset (Σ _ : Unit, ℕ)))
      (measurableSet_singleton (x := (fun _ => false :
        BlockSpace (S := digraphSig) ({⟨(), v⟩} : Finset (Σ _ : Unit, ℕ)))))
  · exact Filter.Eventually.of_forall fun ω => blockMap_singleton_arr ω v

open scoped Classical in
/-- **The rank-one representation**, built directly from the independently described coupling. -/
noncomputable def rankOneRep : bipartiteExchangeable.RankRepresentation 1 where
  P := rankOneCoupling
  isProbabilityMeasure_P := inferInstance
  map_fst := rankOneCoupling_map_fst
  map_snd := rankOneCoupling_map_snd
  invariant := by
    intro σ
    have hfun : (Prod.map (RelStructure.relabel σ.1) (⇑(rankLatentRelabel σ 1)) :
        RelStructure digraphSig (Vinfinite digraphSig) × RankLatentSpace digraphSig 1 → _) =
        Prod.map (RelStructure.relabel σ.1) id := by
      funext p
      exact Prod.ext rfl (rankLatentRelabel_one_eq σ p.2)
    rw [rankOneCoupling, hfun,
      ← Measure.map_prod_map _ _ (measurable_relabel σ.1) measurable_id,
      bipartiteLaw_map_relabel, Measure.map_id]
  lower_recovers := by
    intro A hA
    have hA0 : A = ∅ := Finset.card_eq_zero.mp (Nat.lt_one_iff.mp hA)
    subst hA0
    exact ⟨fun _ => default, measurable_const,
      Filter.Eventually.of_forall fun _ => Subsingleton.elim _ _⟩
  screening := by
    intro A hA
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hA
    obtain ⟨u, v⟩ := a
    cases u
    have hae : blockMap ({⟨(), v⟩} : Finset (Σ _ : Unit, ℕ)) ∘ Prod.fst
        =ᵐ[rankOneCoupling] fun _ => (fun _ => false) := by
      have h := (Measure.quasiMeasurePreserving_fst (μ := bipartiteLaw)
        (ν := rankLatentSource digraphSig 1)).ae (ae_blockMap_singleton v)
      rw [rankOneCoupling]
      exact h
    exact CondIndepFun.congr
      (condIndepFun_const_left (fun _ => false) _)
      measurable_const (measurable_restObservation 1 _)
      ((measurable_blockMap (S := digraphSig) _).comp measurable_fst)
      (measurable_restObservation 1 _) hae.symm Filter.EventuallyEq.rfl

/-! ### The rank-two coupling and the three central identities

The identities are proved immediately after the definition, before invariance or screening add
noise. The third is the real gate: it visibly consumes the source factorization. -/

/-- The fresh singleton layer of a rank-two latent point. -/
noncomputable def freshLayer (ω : RankLatentSpace digraphSig 2) : Colours :=
  (rankLatentSpaceSuccEquiv 1 ω).2

theorem measurable_freshLayer : Measurable freshLayer :=
  (rankLatentSpaceSuccEquiv 1).measurable.snd

/-- **The rank-two coupling**: the array is built from the fresh singleton layer, and the whole
rank-two latent point is retained. -/
noncomputable def rankTwoCoupling :
    Measure (RelStructure digraphSig (Vinfinite digraphSig) × RankLatentSpace digraphSig 2) :=
  (rankLatentSource digraphSig 2).map fun ω => (arr (freshLayer ω), ω)

theorem measurable_rankTwoMap :
    Measurable fun ω : RankLatentSpace digraphSig 2 => (arr (freshLayer ω), ω) :=
  (measurable_arr.comp measurable_freshLayer).prodMk measurable_id

instance : IsProbabilityMeasure rankTwoCoupling := by
  rw [rankTwoCoupling]
  exact Measure.isProbabilityMeasure_map measurable_rankTwoMap.aemeasurable

/-- The fresh layer carries the i.i.d. singleton source — the second factor of the successor
split. -/
theorem map_freshLayer :
    (rankLatentSource digraphSig 2).map freshLayer =
      iidUniformSource (RankSupport digraphSig 1) := by
  have hfl : freshLayer = Prod.snd ∘ (rankLatentSpaceSuccEquiv 1) := rfl
  rw [hfl, ← Measure.map_map measurable_snd (rankLatentSpaceSuccEquiv 1).measurable,
    rankLatentSource_map_rankLatentSpaceSuccEquiv, Measure.map_snd_prod]
  simp

/-- **Identity 1**: the structure marginal is the bipartite law. -/
@[simp] theorem rankTwoCoupling_map_fst : rankTwoCoupling.map Prod.fst = bipartiteLaw := by
  rw [rankTwoCoupling, Measure.map_map measurable_fst measurable_rankTwoMap,
    show (Prod.fst ∘ fun ω : RankLatentSpace digraphSig 2 => (arr (freshLayer ω), ω)) =
      arr ∘ freshLayer from rfl,
    ← Measure.map_map measurable_arr measurable_freshLayer, map_freshLayer, bipartiteLaw]

/-- **Identity 2**: the latent marginal is the rank-two source. -/
@[simp] theorem rankTwoCoupling_map_snd :
    rankTwoCoupling.map Prod.snd = rankLatentSource digraphSig 2 := by
  rw [rankTwoCoupling, Measure.map_map measurable_snd measurable_rankTwoMap,
    show (Prod.snd ∘ fun ω : RankLatentSpace digraphSig 2 => (arr (freshLayer ω), ω)) = id from rfl,
    Measure.map_id]

/-- **Identity 3 — the gate**: truncating the rank-two coupling's latents to rank one returns the
*independently defined* rank-one coupling. This is where the source factorization is consumed:
`U_∅` splits off from the singleton layer, the array depends only on the latter, and the
truncation reads only the former. -/
theorem rankTwoCoupling_truncation :
    rankTwoCoupling.map (Prod.map id (rankLatentProjection (S := digraphSig) (Nat.le_succ 1))) =
      rankOneCoupling := by
  rw [rankTwoCoupling,
    Measure.map_map (measurable_id.prodMap
        (measurable_rankLatentProjection (S := digraphSig) (Nat.le_succ 1)))
      measurable_rankTwoMap,
    show (Prod.map (id : RelStructure digraphSig (Vinfinite digraphSig) → _)
        (rankLatentProjection (S := digraphSig) (Nat.le_succ 1)) ∘
        fun ω : RankLatentSpace digraphSig 2 => (arr (freshLayer ω), ω)) =
      (Prod.map arr (id : RankLatentSpace digraphSig 1 → _)) ∘ Prod.swap ∘
        (rankLatentSpaceSuccEquiv 1) from rfl,
    ← Measure.map_map (measurable_arr.prodMap measurable_id)
      (measurable_swap.comp (rankLatentSpaceSuccEquiv 1).measurable),
    ← Measure.map_map measurable_swap (rankLatentSpaceSuccEquiv 1).measurable,
    rankLatentSource_map_rankLatentSpaceSuccEquiv, Measure.prod_swap,
    ← Measure.map_prod_map _ _ measurable_arr measurable_id, Measure.map_id,
    rankOneCoupling, bipartiteLaw]

/-! ### Recovery below rank two

`lower_recovers` at rank two ranges over supports of cardinality `< 2`, so it sees only the empty
and singleton cases — never a two-point support. Both blocks are deterministic: the empty one is
vacuous for this signature, the singleton one is the constantly-false diagonal. The two-point
decoder plays no part here. -/

open scoped Classical in
theorem lower_recovers_rank_two (A : Finset (Σ _ : Unit, ℕ)) (hA : A.card < 2) :
    ∃ g : LocalLatentSpace (S := digraphSig) A 2 → BlockSpace (S := digraphSig) A,
      Measurable g ∧
      (fun p : RelStructure digraphSig (Vinfinite digraphSig) × RankLatentSpace digraphSig 2 =>
          blockMap (S := digraphSig) A p.1) =ᵐ[rankTwoCoupling]
        fun p => g (localLatents (S := digraphSig) A 2 p.2) := by
  have hcase : A.card = 0 ∨ A.card = 1 := by omega
  rcases hcase with h0 | h1
  · -- the empty support: no coordinate of this signature has empty support
    have hA0 : A = ∅ := Finset.card_eq_zero.mp h0
    subst hA0
    exact ⟨fun _ => default, measurable_const,
      Filter.Eventually.of_forall fun _ => Subsingleton.elim _ _⟩
  · -- a singleton support: the block is the constantly-false diagonal
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨u, v⟩ := a
    cases u
    refine ⟨fun _ => fun _ => false, measurable_const, ?_⟩
    have hmp : MeasurePreserving (Prod.fst :
        RelStructure digraphSig (Vinfinite digraphSig) × RankLatentSpace digraphSig 2 → _)
        rankTwoCoupling bipartiteLaw :=
      ⟨measurable_fst, rankTwoCoupling_map_fst⟩
    exact hmp.quasiMeasurePreserving.ae (ae_blockMap_singleton v)

/-! ### The two-point deterministic block

The organizing lemma for rank-two screening and for the public XOR identity: on a two-point
support the whole directed block — *both* coordinates `X_uv` and `X_vu` — is a deterministic
function of the two singleton latents visible there. Recovering both as the same parity is what
exhibits symmetry as a property of this law rather than of the signature. -/

/-- The two-point support at a pair of distinct vertices. -/
def pairSupport (u v : ℕ) : Finset (Σ _ : Unit, ℕ) := {⟨(), u⟩, ⟨(), v⟩}

@[simp] theorem mem_pairSupport_left (u v : ℕ) :
    (⟨(), u⟩ : Σ _ : Unit, ℕ) ∈ pairSupport u v := by simp [pairSupport]

@[simp] theorem mem_pairSupport_right (u v : ℕ) :
    (⟨(), v⟩ : Σ _ : Unit, ℕ) ∈ pairSupport u v := by simp [pairSupport]

open scoped Classical in
/-- A vertex of the pair, as a latent index visible at that support. -/
def pairLocalIndex (u v w : ℕ) (h : (⟨(), w⟩ : Σ _ : Unit, ℕ) ∈ pairSupport u v) :
    LocalLatentIndex (S := digraphSig) (pairSupport u v) 2 :=
  ⟨⟨{⟨(), w⟩}, by simp⟩, by simpa using h⟩

open scoped Classical in
/-- **The two-point decoder**: read the two singleton latents and return their parity, for every
coordinate of the block. -/
noncomputable def twoPointDecoder (u v : ℕ) :
    LocalLatentSpace (S := digraphSig) (pairSupport u v) 2 →
      BlockSpace (S := digraphSig) (pairSupport u v) := fun l _ =>
  xor (decide (l (pairLocalIndex u v u (mem_pairSupport_left u v)) ≤ 1 / 2))
    (decide (l (pairLocalIndex u v v (mem_pairSupport_right u v)) ≤ 1 / 2))

theorem measurable_twoPointDecoder (u v : ℕ) : Measurable (twoPointDecoder u v) := by
  refine measurable_pi_lambda _ fun _ => ?_
  exact (Measurable.of_discrete (f := fun p : Bool × Bool => xor p.1 p.2)).comp
    ((measurable_decideLe (measurable_pi_apply _)).prodMk
      (measurable_decideLe (measurable_pi_apply _)))

open scoped Classical in
/-- A coordinate of a two-point block is one of the two directed pairs. -/
theorem coord_of_pair {u v : ℕ} (huv : u ≠ v)
    (c : BlockIndex (S := digraphSig) (pairSupport u v)) :
    (c.1.2 0 = u ∧ c.1.2 1 = v) ∨ (c.1.2 0 = v ∧ c.1.2 1 = u) := by
  have h0 : c.1.taggedValue 0 ∈ c.1.support := (RelCoord.mem_support_iff _ _).mpr ⟨0, rfl⟩
  have h1 : c.1.taggedValue 1 ∈ c.1.support := (RelCoord.mem_support_iff _ _).mpr ⟨1, rfl⟩
  have hu : (⟨(), u⟩ : Σ _ : Unit, ℕ) ∈ c.1.support := by rw [c.2]; simp
  have hv : (⟨(), v⟩ : Σ _ : Unit, ℕ) ∈ c.1.support := by rw [c.2]; simp
  rw [c.2] at h0 h1
  rw [(RelCoord.mem_support_iff _ _)] at hu hv
  obtain ⟨iu, hiu⟩ := hu
  obtain ⟨iv, hiv⟩ := hv
  simp only [RelCoord.taggedValue, pairSupport, Finset.mem_insert, Finset.mem_singleton,
    Sigma.mk.injEq, heq_eq_eq, true_and] at h0 h1
  simp only [RelCoord.taggedValue, Sigma.mk.injEq, heq_eq_eq, true_and] at hiu hiv
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exfalso
    fin_cases iv <;> simp_all
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h0, h1⟩
  · exfalso
    fin_cases iu <;> simp_all

open scoped Classical in
/-- The fresh layer at a vertex is the rank-two latent at that singleton support. -/
theorem freshLayer_vertexSupport (ω : RankLatentSpace digraphSig 2) (w : ℕ) :
    freshLayer ω (vertexSupport w) = ω ⟨{⟨(), w⟩}, by simp⟩ := rfl

open scoped Classical in
/-- **The organizing lemma**: on a two-point support the whole directed block is the deterministic
parity of the two singleton latents visible there. Both `X_uv` and `X_vu` decode to the same
value, so the symmetry of this law is exhibited rather than assumed. -/
theorem blockMap_pair_arr {u v : ℕ} (huv : u ≠ v) (ω : RankLatentSpace digraphSig 2) :
    blockMap (S := digraphSig) (pairSupport u v) (arr (freshLayer ω)) =
      twoPointDecoder u v (localLatents (S := digraphSig) (pairSupport u v) 2 ω) := by
  funext c
  show arr (freshLayer ω) c.1 = _
  have hdec : ∀ w : ℕ, colour (freshLayer ω) w = decide (ω ⟨{⟨(), w⟩}, by simp⟩ ≤ 1 / 2) := by
    intro w
    rw [colour, freshLayer_vertexSupport]
  have hl : ∀ (w : ℕ) (h : (⟨(), w⟩ : Σ _ : Unit, ℕ) ∈ pairSupport u v),
      localLatents (S := digraphSig) (pairSupport u v) 2 ω (pairLocalIndex u v w h)
        = ω ⟨{⟨(), w⟩}, by simp⟩ := fun _ _ => rfl
  show xor (colour (freshLayer ω) (c.1.2 0)) (colour (freshLayer ω) (c.1.2 1)) = _
  rw [twoPointDecoder, hl u (mem_pairSupport_left u v), hl v (mem_pairSupport_right u v)]
  rcases coord_of_pair huv c with ⟨e0, e1⟩ | ⟨e0, e1⟩
  · rw [e0, e1, hdec, hdec]
  · rw [e0, e1, hdec, hdec, Bool.xor_comm]

/-! ### Rank-two screening

The arbitrary two-point support is normalized to `pairSupport u v` *first*, so that the
deterministic-block lemma applies directly and no dependent block or local-latent space has to be
transported across a later equality. -/

open scoped Classical in
/-- A support of cardinality two is a `pairSupport` at distinct vertices. -/
theorem exists_pairSupport_of_card_two {A : Finset (Σ _ : Unit, ℕ)} (hA : A.card = 2) :
    ∃ u v : ℕ, u ≠ v ∧ A = pairSupport u v := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hA
  refine ⟨a.2, b.2, fun h => hab ?_, rfl⟩
  exact Sigma.ext rfl (heq_of_eq h)

open scoped Classical in
/-- The decoder identity holds a.e. under the rank-two coupling. -/
theorem ae_blockMap_pair {u v : ℕ} (huv : u ≠ v) :
    (fun p : RelStructure digraphSig (Vinfinite digraphSig) × RankLatentSpace digraphSig 2 =>
        blockMap (S := digraphSig) (pairSupport u v) p.1) =ᵐ[rankTwoCoupling]
      fun p => twoPointDecoder u v (localLatents (S := digraphSig) (pairSupport u v) 2 p.2) := by
  rw [rankTwoCoupling]
  refine (ae_map_iff measurable_rankTwoMap.aemeasurable ?_).mpr
    (Filter.Eventually.of_forall fun ω => blockMap_pair_arr huv ω)
  exact measurableSet_eq_fun
    ((measurable_blockMap (S := digraphSig) _).comp measurable_fst)
    ((measurable_twoPointDecoder u v).comp
      ((measurable_localLatents (S := digraphSig) _ 2).comp measurable_snd))

open scoped Classical in
/-- **Rank-two screening**: at a two-point support the block is conditionally independent of the
rank-truncated remainder given the latents visible there — because it *is* a measurable function
of them. -/
theorem screening_rank_two (A : Finset (Σ _ : Unit, ℕ)) (hA : A.card = 2) :
    CondIndepFun (MeasurableSpace.comap
        (localLatents (S := digraphSig) A 2 ∘ Prod.snd) inferInstance)
      (((measurable_localLatents (S := digraphSig) A 2).comp measurable_snd).comap_le)
      (blockMap (S := digraphSig) A ∘ Prod.fst) (restObservation 2 A) rankTwoCoupling := by
  obtain ⟨u, v, huv, rfl⟩ := exists_pairSupport_of_card_two hA
  refine CondIndepFun.congr
    (condIndepFun_of_measurable_left
      ((measurable_twoPointDecoder u v).comp (comap_measurable _))
      (measurable_restObservation 2 _))
    ((measurable_twoPointDecoder u v).comp
      ((measurable_localLatents (S := digraphSig) _ 2).comp measurable_snd))
    (measurable_restObservation 2 _)
    ((measurable_blockMap (S := digraphSig) _).comp measurable_fst)
    (measurable_restObservation 2 _) (ae_blockMap_pair huv).symm Filter.EventuallyEq.rfl

/-! ### The joint action

One exact pointwise lemma, proved before any measure is touched, so that the inverse and
orientation conventions are isolated in a single place. -/

open scoped Classical in
/-- The finitely supported rank-support action agrees with the full-permutation helper. Kept local
to this file: the two serve genuinely different APIs. -/
theorem rankSupportEquiv_eq_supportPerm (σ : FinSuppPerm digraphSig)
    (A : RankSupport digraphSig 1) : rankSupportEquiv σ 1 A = supportPerm (σ.1 ()) A := by
  refine Subtype.ext ?_
  refine Finset.ext fun w => ?_
  simp only [rankSupportEquiv, supportPerm, Equiv.coe_fn_mk, Finset.mem_image]

open scoped Classical in
/-- The fresh layer intertwines the rank-two latent action with the vertex action. -/
theorem freshLayer_rankLatentRelabel (σ : FinSuppPerm digraphSig)
    (ω : RankLatentSpace digraphSig 2) :
    freshLayer (rankLatentRelabel σ 2 ω) = fun A => freshLayer ω (supportPerm (σ.1 ()) A) := by
  funext A
  show (rankLatentSpaceSuccEquiv 1 (rankLatentRelabel σ 2 ω)).2 A = _
  rw [show rankLatentSpaceSuccEquiv 1 (rankLatentRelabel σ 2 ω) =
      MeasurableEquiv.prodCongr (rankLatentRelabel σ 1) (rankSupportLatentRelabel σ 1)
        (rankLatentSpaceSuccEquiv 1 ω) from
    congrFun (rankLatentSpaceSuccEquiv_rankLatentRelabel σ 1) ω]
  show freshLayer ω (rankSupportEquiv σ 1 A) = _
  rw [rankSupportEquiv_eq_supportPerm]

open scoped Classical in
/-- **The exact pointwise joint action.** Relabeling the rank-two latent point and then building
the pair is the same as building the pair and acting diagonally. -/
theorem jointMap_rankLatentRelabel (σ : FinSuppPerm digraphSig)
    (ω : RankLatentSpace digraphSig 2) :
    (arr (freshLayer (rankLatentRelabel σ 2 ω)), rankLatentRelabel σ 2 ω) =
      Prod.map (RelStructure.relabel σ.1) (⇑(rankLatentRelabel σ 2))
        (arr (freshLayer ω), ω) := by
  refine Prod.ext ?_ rfl
  show arr (freshLayer (rankLatentRelabel σ 2 ω)) = RelStructure.relabel σ.1 (arr (freshLayer ω))
  rw [freshLayer_rankLatentRelabel, arr_comp_supportPerm]

/-- **Rank-two invariance**, now just `Measure.map_map`, the joint action, and source
invariance. -/
theorem rankTwoCoupling_invariant (σ : FinSuppPerm digraphSig) :
    rankTwoCoupling.map (Prod.map (RelStructure.relabel σ.1) (⇑(rankLatentRelabel σ 2))) =
      rankTwoCoupling := by
  rw [rankTwoCoupling,
    Measure.map_map ((measurable_relabel σ.1).prodMap (rankLatentRelabel σ 2).measurable)
      measurable_rankTwoMap,
    show (Prod.map (RelStructure.relabel σ.1) (⇑(rankLatentRelabel σ 2)) ∘
        fun ω : RankLatentSpace digraphSig 2 => (arr (freshLayer ω), ω)) =
      (fun ω : RankLatentSpace digraphSig 2 => (arr (freshLayer ω), ω)) ∘
        (⇑(rankLatentRelabel σ 2)) from by
      funext ω
      exact (jointMap_rankLatentRelabel σ ω).symm,
    ← Measure.map_map measurable_rankTwoMap (rankLatentRelabel σ 2).measurable,
    rankLatentSource_map_rankLatentRelabel]

/-! ### The representation and the successor witness -/

open scoped Classical in
/-- **The rank-two representation.** Every field is one of the theorems above. -/
noncomputable def rankTwoRep : bipartiteExchangeable.RankRepresentation 2 where
  P := rankTwoCoupling
  isProbabilityMeasure_P := inferInstance
  map_fst := rankTwoCoupling_map_fst
  map_snd := rankTwoCoupling_map_snd
  invariant := rankTwoCoupling_invariant
  lower_recovers := lower_recovers_rank_two
  screening := screening_rank_two

/-- **The successor witness**: a two-field literal whose truncation proof is exactly the gate
identity. This is the regression's headline — the contract is satisfied by an explicit rank
`1 → 2` example whose two couplings were described independently. -/
noncomputable def bipartiteSuccessor :
    InfiniteRelExchangeableLaw.RankSuccessor rankOneRep where
  next := rankTwoRep
  truncation := rankTwoCoupling_truncation

/-! ### The public XOR identity

A coordinate projection of the deterministic-block lemma — no second pushforward calculation. -/

open scoped Classical in
/-- The directed coordinate at a pair of distinct vertices lies in that pair's block. -/
theorem support_digraphCoord {u v : ℕ} :
    (digraphCoord u v : RelCoord digraphSig (Vinfinite digraphSig)).support = pairSupport u v := by
  refine Finset.ext fun w => ?_
  rw [RelCoord.mem_support_iff]
  simp only [pairSupport, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

open scoped Classical in
/-- **The XOR identity**: almost surely the edge at a pair of distinct vertices is the parity of
their two colours. Obtained by evaluating the block identity at one coordinate. -/
theorem ae_edge_xor {u v : ℕ} (huv : u ≠ v) :
    ∀ᵐ p ∂rankTwoCoupling, p.1 (digraphCoord u v) =
      xor (colour (freshLayer p.2) u) (colour (freshLayer p.2) v) := by
  filter_upwards [ae_blockMap_pair huv] with p hp
  have := congrFun hp ⟨digraphCoord u v, support_digraphCoord⟩
  rw [twoPointDecoder] at this
  rw [show p.1 (digraphCoord u v) =
      blockMap (S := digraphSig) (pairSupport u v) p.1
        ⟨digraphCoord u v, support_digraphCoord⟩ from rfl, this]
  rw [colour, colour, freshLayer_vertexSupport, freshLayer_vertexSupport]
  rfl

end BipartiteRegression

end RelSignature
