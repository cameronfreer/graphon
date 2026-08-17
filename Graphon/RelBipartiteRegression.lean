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
  simp [arr_apply, Bool.xor_self]

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

end BipartiteRegression

end RelSignature
