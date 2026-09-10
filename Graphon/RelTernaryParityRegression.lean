/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRankSuccessorContract

/-!
# The ternary parity regression: no exact successor (R4 converse, #107)

An adversarial example for the universal successor contract. One sort, one ternary relation,
and independent fair colours `c_v`: the relation holds at a pairwise distinct triple `(u, v, w)`
exactly when `c_u ⊕ c_v`, and never at a repeated triple. The array is exchangeable.

The rank-two coupling is the independent product `ternaryLaw × rankLatentSource 2`. It satisfies
every clause of `RankRepresentation`: blocks on at most two vertices are constantly false, so
recovery and screening are deterministic; and the empty and singleton fixing algebras are trivial
modulo the law, so below-rank fixing completeness holds with the representatives `∅` and `univ`.

The pair event `pairEvent u v` — some third vertex witnesses the relation at `(u, v, ·)` — lies
in the fixing algebra at `{u, v}`, and its indicator is the parity `c_u ⊕ c_v`. Three such
parities on a triangle cannot all hold, while under any exact rank-three successor the three
events would be independent given the old array, each of conditional probability `1/2`. Hence
this rank-two representation has **no** `RankSuccessor`.

## Contents

* `ternarySig`, `arr`, `ternaryLaw`, `ternaryExchangeable` — the law.
* `pairEvent` — the pair fixing events and their parity reading `mem_pairEvent_arr`.
* `rankTwoRep` — the independent rank-two representation.
* `fixing_trivial_of_card_lt_two` — triviality of the empty and singleton fixing algebras.
* `isEmpty_rankSuccessor`, `not_successorStatement` — the obstruction, and the refutation of the
  universal successor statement.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RelSignature

namespace TernaryParityRegression

/-- The one-sort, single ternary relation signature. -/
abbrev ternarySig : RelSignature where
  Srt := Unit
  Rel := Unit
  arity := fun _ => 3
  argSort := fun _ _ => ()

/-- The coordinate at an ordered vertex triple. -/
abbrev ternaryCoord {V : Type*} (a b c : V) : RelCoord ternarySig (fun _ => V) := ⟨(), ![a, b, c]⟩

/-- The fresh singleton layer of the rank-two latent cube: one uniform per vertex. -/
abbrev Colours := RankSupport ternarySig 1 → ℝ

/-- The singleton support at a vertex. -/
def vertexSupport (v : ℕ) : RankSupport ternarySig 1 :=
  ⟨{⟨(), v⟩}, Finset.card_singleton _⟩

theorem vertexSupport_injective : Function.Injective vertexSupport := by
  intro a b h
  have := congrArg Subtype.val h
  simpa [vertexSupport] using this

/-- The colour of a vertex, read off its own fresh coordinate. -/
noncomputable def colour (ω : Colours) (v : ℕ) : Bool := decide (ω (vertexSupport v) ≤ 1 / 2)

theorem measurable_colour (v : ℕ) : Measurable fun ω : Colours => colour ω v :=
  measurable_decideLe (measurable_pi_apply _)

/-- Pairwise distinctness of a triple. -/
def Distinct (a b c : ℕ) : Prop := a ≠ b ∧ a ≠ c ∧ b ≠ c

instance (a b c : ℕ) : Decidable (Distinct a b c) := by unfold Distinct; infer_instance

theorem distinct_map {σ : Equiv.Perm ℕ} {a b c : ℕ} :
    Distinct (σ a) (σ b) (σ c) ↔ Distinct a b c := by
  simp [Distinct, σ.injective.ne_iff]

/-- **The parity array from a Boolean colouring**: the relation holds at a pairwise distinct
triple exactly when the first two colours differ. -/
def arrOf (d : ℕ → Bool) : RelStructure ternarySig (Vinfinite ternarySig) :=
  fun c => if Distinct (c.2 0) (c.2 1) (c.2 2) then xor (d (c.2 0)) (d (c.2 1)) else false

/-- **The parity array** read off the fresh colour layer. -/
noncomputable def arr (ω : Colours) : RelStructure ternarySig (Vinfinite ternarySig) :=
  arrOf (colour ω)

theorem arrOf_apply (d : ℕ → Bool) (a b c : ℕ) :
    arrOf d (ternaryCoord a b c) =
      if Distinct a b c then xor (d a) (d b) else false := rfl

theorem measurable_arrOf : Measurable arrOf := by
  refine measurable_pi_lambda _ fun c => ?_
  by_cases h : Distinct (c.2 0) (c.2 1) (c.2 2)
  · simp only [arrOf, if_pos h]
    exact Measurable.comp (g := fun p : Bool × Bool => xor p.1 p.2)
      (f := fun d : ℕ → Bool => (d (c.2 0), d (c.2 1))) Measurable.of_discrete
      ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
  · simp only [arrOf, if_neg h]
    exact measurable_const

theorem measurable_colours : Measurable fun ω : Colours => fun v => colour ω v :=
  measurable_pi_lambda _ measurable_colour

theorem measurable_arr : Measurable arr := measurable_arrOf.comp measurable_colours

/-- The array depends on the colouring only through its differences. -/
theorem arrOf_xor_const (d : ℕ → Bool) (b : Bool) : arrOf (fun v => xor (d v) b) = arrOf d := by
  funext c
  simp only [arrOf]
  split_ifs
  · cases d (c.2 0) <;> cases d (c.2 1) <;> cases b <;> rfl
  · rfl

/-! ### The relabeling action on the fresh layer -/

/-- A permutation of the vertices permutes the singleton supports. -/
noncomputable def supportPerm (σ : Equiv.Perm ℕ) :
    RankSupport ternarySig 1 ≃ RankSupport ternarySig 1 :=
  rankSupportPerm (fun _ : Unit => σ) 1

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

theorem arrOf_comp (d : ℕ → Bool) (σ : Equiv.Perm ℕ) :
    arrOf (d ∘ σ) = RelStructure.relabel (fun _ : Unit => σ) (arrOf d) := by
  funext c
  show (if Distinct (c.2 0) (c.2 1) (c.2 2) then xor (d (σ (c.2 0))) (d (σ (c.2 1))) else false) =
    (if Distinct (σ (c.2 0)) (σ (c.2 1)) (σ (c.2 2)) then
      xor (d (σ (c.2 0))) (d (σ (c.2 1))) else false)
  by_cases h : Distinct (c.2 0) (c.2 1) (c.2 2)
  · rw [if_pos h, if_pos (distinct_map.mpr h)]
  · rw [if_neg h, if_neg (mt distinct_map.mp h)]

/-- **Equivariance of the array**: relabeling the vertices is reindexing the fresh layer. -/
theorem arr_comp_supportPerm (σ : Equiv.Perm ℕ) (ω : Colours) :
    arr (fun A => ω (supportPerm σ A)) = RelStructure.relabel (fun _ : Unit => σ) (arr ω) := by
  rw [arr, arr, ← arrOf_comp]
  exact congrArg arrOf (funext fun v => colour_comp_supportPerm σ ω v)

/-! ### The array law -/

/-- **The ternary parity law.** -/
noncomputable def ternaryLaw : Measure (RelStructure ternarySig (Vinfinite ternarySig)) :=
  (iidUniformSource (RankSupport ternarySig 1)).map arr

instance : IsProbabilityMeasure ternaryLaw :=
  Measure.isProbabilityMeasure_map measurable_arr.aemeasurable

theorem ternaryLaw_map_relabel (σ : ∀ _ : Unit, Equiv.Perm ℕ) :
    ternaryLaw.map (RelStructure.relabel σ) = ternaryLaw := by
  rw [ternaryLaw, Measure.map_map (measurable_relabel σ) measurable_arr,
    show RelStructure.relabel σ ∘ arr =
      arr ∘ (fun ω : Colours => fun A => ω (supportPerm (σ ()) A)) from by
        funext ω
        exact (arr_comp_supportPerm (σ ()) ω).symm,
    ← Measure.map_map measurable_arr (measurable_pi_lambda _ fun _ => measurable_pi_apply _),
    iidUniformSource, Measure.infinitePi_map_comp_equiv _ (supportPerm (σ ()))]

/-- The ternary parity law as an exchangeable law. -/
noncomputable def ternaryExchangeable : InfiniteRelExchangeableLaw ternarySig where
  law := ⟨ternaryLaw, inferInstance⟩
  exchangeable := ternaryLaw_map_relabel

/-! ### The pair fixing events -/

/-- **The pair event at `(u, v)`**: some third vertex witnesses the relation. -/
def pairEvent (u v : ℕ) : Set (RelStructure ternarySig (Vinfinite ternarySig)) :=
  {X | ∃ w, w ≠ u ∧ w ≠ v ∧ X (ternaryCoord u v w) = true}

/-- The pair support. -/
def pairSupport (u v : ℕ) : Finset (Σ _ : Unit, ℕ) := {⟨(), u⟩, ⟨(), v⟩}

theorem measurableSet_pairEvent (u v : ℕ) : MeasurableSet (pairEvent u v) := by
  have h : pairEvent u v = ⋃ w : ℕ, ⋃ _ : w ≠ u ∧ w ≠ v,
      (fun X : RelStructure ternarySig (Vinfinite ternarySig) => X (ternaryCoord u v w)) ⁻¹'
        {true} := by
    ext X
    simp [pairEvent, and_assoc]
  rw [h]
  exact MeasurableSet.iUnion fun w => MeasurableSet.iUnion fun _ =>
    measurable_pi_apply _ (measurableSet_singleton true)

/-- The pair event is invariant under every relabeling fixing `u` and `v`. -/
theorem relabel_preimage_pairEvent {u v : ℕ} (σ : ∀ _ : Unit, Equiv.Perm ℕ)
    (hu : σ () u = u) (hv : σ () v = v) :
    RelStructure.relabel σ ⁻¹' pairEvent u v = pairEvent u v := by
  ext X
  simp only [Set.mem_preimage, pairEvent, Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, hwu, hwv, hw⟩
    refine ⟨σ () w, ?_, ?_, ?_⟩
    · rw [← hu]; exact (σ ()).injective.ne hwu
    · rw [← hv]; exact (σ ()).injective.ne hwv
    · have : RelStructure.relabel σ X (ternaryCoord u v w) =
          X (ternaryCoord (σ () u) (σ () v) (σ () w)) := by
        show X (RelCoord.map (fun s => ⇑(σ s)) (ternaryCoord u v w)) = _
        congr 1
        refine Sigma.ext rfl (heq_of_eq ?_)
        funext i; fin_cases i <;> rfl
      rw [this, hu, hv] at hw
      exact hw
  · rintro ⟨w, hwu, hwv, hw⟩
    refine ⟨(σ ()).symm w, ?_, ?_, ?_⟩
    · intro h; apply hwu; rw [← hu, ← h, Equiv.apply_symm_apply]
    · intro h; apply hwv; rw [← hv, ← h, Equiv.apply_symm_apply]
    · show X (RelCoord.map (fun s => ⇑(σ s)) (ternaryCoord u v ((σ ()).symm w))) = true
      have : RelCoord.map (fun s => ⇑(σ s)) (ternaryCoord u v ((σ ()).symm w)) =
          ternaryCoord u v w := by
        refine Sigma.ext rfl (heq_of_eq ?_)
        funext i; fin_cases i
        · exact hu
        · exact hv
        · exact Equiv.apply_symm_apply _ _
      rw [this]; exact hw

/-- The pair event lies in the fixing algebra at `{u, v}`. -/
theorem measurableSet_fixingAlgebra_pairEvent (u v : ℕ) :
    MeasurableSet[RelStructure.fixingAlgebra (pairSupport u v)] (pairEvent u v) := by
  refine ⟨measurableSet_pairEvent u v, fun σ hσ => ?_⟩
  refine relabel_preimage_pairEvent σ ?_ ?_
  · exact hσ.2 ⟨(), u⟩ (by simp [pairSupport])
  · exact hσ.2 ⟨(), v⟩ (by simp [pairSupport])

/-- **The parity reading**: a colouring's array lies in the pair event exactly when the two
vertices are distinct and their colours differ. -/
theorem mem_pairEvent_arrOf {u v : ℕ} (d : ℕ → Bool) :
    arrOf d ∈ pairEvent u v ↔ u ≠ v ∧ xor (d u) (d v) = true := by
  constructor
  · rintro ⟨w, hwu, hwv, hw⟩
    rw [arrOf_apply] at hw
    split_ifs at hw with h
    exact ⟨h.1, hw⟩
  · rintro ⟨huv, hx⟩
    refine ⟨max u v + 1, ?_, ?_, ?_⟩
    · have := le_max_left u v; omega
    · have := le_max_right u v; omega
    · exact (arrOf_apply d u v _).trans ((if_pos ⟨huv, by have := le_max_left u v; omega,
        by have := le_max_right u v; omega⟩).trans hx)

theorem mem_pairEvent_arr {u v : ℕ} (ω : Colours) :
    arr ω ∈ pairEvent u v ↔ u ≠ v ∧ xor (colour ω u) (colour ω v) = true :=
  mem_pairEvent_arrOf _

/-- **Three parities on a triangle cannot all hold.** -/
theorem not_mem_triangle (d : ℕ → Bool) (a b c : ℕ) :
    arrOf d ∉ pairEvent a b ∩ pairEvent b c ∩ pairEvent a c := by
  rintro ⟨⟨hab, hbc⟩, hac⟩
  have h1 := (mem_pairEvent_arrOf d).mp hab
  have h2 := (mem_pairEvent_arrOf d).mp hbc
  have h3 := (mem_pairEvent_arrOf d).mp hac
  revert h1 h2 h3
  cases d a <;> cases d b <;> cases d c <;> simp

/-! ### Blocks below rank three are constant -/

/-- A coordinate whose support has fewer than three vertices repeats a vertex. -/
theorem not_distinct_of_card_lt_three {c : RelCoord ternarySig (Vinfinite ternarySig)}
    (hc : c.support.card < 3) : ¬ Distinct (c.2 0) (c.2 1) (c.2 2) := by
  classical
  have hninj : ¬ Function.Injective c.taggedValue := by
    intro hinj
    have h := Finset.card_le_card_of_injOn (s := Finset.univ) (t := c.support) c.taggedValue
      (fun i _ => (c.mem_support_iff _).mpr ⟨i, rfl⟩) hinj.injOn
    rw [Finset.card_univ, Fintype.card_fin] at h
    have h3 : ternarySig.arity c.1 = 3 := rfl
    omega
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hninj
  have hval : c.2 i = c.2 j := by
    have hij' : (⟨(), c.2 i⟩ : Σ _ : Unit, ℕ) = ⟨(), c.2 j⟩ := hij
    exact eq_of_heq (Sigma.mk.inj_iff.mp hij').2
  obtain ⟨u, f⟩ := c
  fin_cases i <;> fin_cases j <;> simp_all [Distinct]

open scoped Classical in
/-- **Every block on fewer than three vertices is constantly false.** -/
theorem blockMap_arrOf_of_card_lt_three {A : Finset (Σ _ : Unit, ℕ)} (hA : A.card < 3)
    (d : ℕ → Bool) : blockMap (S := ternarySig) A (arrOf d) = fun _ => false := by
  funext i
  obtain ⟨c, hc⟩ := i
  show arrOf d c = false
  have hnd : ¬ Distinct (c.2 0) (c.2 1) (c.2 2) := not_distinct_of_card_lt_three (hc ▸ hA)
  simp only [arrOf, if_neg hnd]

open scoped Classical in
theorem ae_blockMap_of_card_lt_three {A : Finset (Σ _ : Unit, ℕ)} (hA : A.card < 3) :
    ∀ᵐ X ∂ternaryLaw, blockMap (S := ternarySig) A X = fun _ => false := by
  rw [ternaryLaw]
  refine (ae_map_iff measurable_arr.aemeasurable ?_).mpr ?_
  · exact (measurable_blockMap (S := ternarySig) A)
      (measurableSet_singleton (x := (fun _ => false : BlockSpace (S := ternarySig) A)))
  · exact Filter.Eventually.of_forall fun ω => blockMap_arrOf_of_card_lt_three hA (colour ω)

/-! ### The rank-two cube and the relative colouring -/

/-- The rank-two latent cube. -/
abbrev Cube := RankLatentSpace ternarySig 2

/-- The fresh singleton layer of a rank-two latent point. -/
noncomputable def freshLayer (ω : Cube) : Colours := (rankLatentSpaceSuccEquiv 1 ω).2

theorem measurable_freshLayer : Measurable freshLayer :=
  (rankLatentSpaceSuccEquiv 1).measurable.snd

theorem source_map_freshLayer :
    (rankLatentSource ternarySig 2).map freshLayer =
      iidUniformSource (RankSupport ternarySig 1) := by
  have h : freshLayer = Prod.snd ∘ rankLatentSpaceSuccEquiv 1 := rfl
  rw [h, ← Measure.map_map measurable_snd (rankLatentSpaceSuccEquiv 1).measurable,
    rankLatentSource_map_rankLatentSpaceSuccEquiv, Measure.map_snd_prod]
  simp

/-- The law, read off the rank-two cube. -/
theorem ternaryLaw_eq_map_cube :
    ternaryLaw = (rankLatentSource ternarySig 2).map (arr ∘ freshLayer) := by
  rw [ternaryLaw, ← source_map_freshLayer, Measure.map_map measurable_arr measurable_freshLayer]

open scoped Classical in
theorem rankSupportEquiv_eq_supportPerm (σ : FinSuppPerm ternarySig)
    (A : RankSupport ternarySig 1) : rankSupportEquiv σ 1 A = supportPerm (σ.1 ()) A := by
  refine Subtype.ext ?_
  refine Finset.ext fun w => ?_
  simp only [rankSupportEquiv, supportPerm, rankSupportPerm, Equiv.coe_fn_mk, Finset.mem_image]

open scoped Classical in
theorem freshLayer_rankLatentRelabel (σ : FinSuppPerm ternarySig) (ω : Cube) :
    freshLayer (rankLatentRelabel σ 2 ω) = fun A => freshLayer ω (supportPerm (σ.1 ()) A) := by
  funext A
  show (rankLatentSpaceSuccEquiv 1 (rankLatentRelabel σ 2 ω)).2 A = _
  rw [show rankLatentSpaceSuccEquiv 1 (rankLatentRelabel σ 2 ω) =
      MeasurableEquiv.prodCongr (rankLatentRelabel σ 1) (rankSupportLatentRelabel σ 1)
        (rankLatentSpaceSuccEquiv 1 ω) from
    congrFun (rankLatentSpaceSuccEquiv_rankLatentRelabel σ 1) ω]
  show freshLayer ω (rankSupportEquiv σ 1 A) = _
  rw [rankSupportEquiv_eq_supportPerm]

/-- **Exact equivariance on the cube.** -/
theorem arr_freshLayer_rankLatentRelabel (σ : FinSuppPerm ternarySig) (ω : Cube) :
    arr (freshLayer (rankLatentRelabel σ 2 ω)) = RelStructure.relabel σ.1 (arr (freshLayer ω)) := by
  rw [freshLayer_rankLatentRelabel, arr_comp_supportPerm]

/-- The singleton latent index at a vertex. -/
def singIndex (w : ℕ) : RankLatentIndex ternarySig 2 :=
  ⟨{⟨(), w⟩}, by simp⟩

theorem singIndex_injective : Function.Injective singIndex := by
  intro a b h
  have := congrArg Subtype.val h
  simpa [singIndex] using this

/-- The colour of a vertex reads the singleton coordinate. -/
theorem colour_freshLayer (ω : Cube) (w : ℕ) :
    colour (freshLayer ω) w = decide (ω (singIndex w) ≤ 1 / 2) := by
  show decide ((rankLatentSpaceSuccEquiv 1 ω).2 (vertexSupport w) ≤ 1 / 2) = _
  rfl

/-- The colouring relative to a reference vertex `v`: the difference of colours. -/
noncomputable def relColour (v : ℕ) (ω : Cube) : ℕ → Bool :=
  fun w => xor (colour (freshLayer ω) w) (colour (freshLayer ω) v)

/-- The colouring with the reference vertex blanked out. -/
noncomputable def offColour (v : ℕ) (ω : Cube) : ℕ → Bool :=
  fun w => if w = v then false else colour (freshLayer ω) w

/-- Flipping every colour except the reference vertex. -/
def flipOff (v : ℕ) (b : Bool) (d : ℕ → Bool) : ℕ → Bool :=
  fun w => if w = v then false else xor (d w) b

theorem measurable_flipOff (v : ℕ) (b : Bool) : Measurable (flipOff v b) :=
  measurable_pi_lambda _ fun w => by
    by_cases h : w = v
    · simp only [flipOff, if_pos h]; exact measurable_const
    · simp only [flipOff, if_neg h]
      exact Measurable.comp (g := fun x : Bool => xor x b) Measurable.of_discrete
        (measurable_pi_apply w)

theorem relColour_eq_flipOff (v : ℕ) (ω : Cube) :
    relColour v ω = flipOff v (colour (freshLayer ω) v) (offColour v ω) := by
  funext w
  by_cases h : w = v
  · subst h; simp [relColour, flipOff]
  · simp [relColour, flipOff, offColour, h]

theorem arr_freshLayer_eq_arrOf_relColour (v : ℕ) (ω : Cube) :
    arr (freshLayer ω) = arrOf (relColour v ω) :=
  (arrOf_xor_const _ _).symm

theorem measurable_offColour (v : ℕ) : Measurable (offColour v) :=
  measurable_pi_lambda _ fun w => by
    by_cases h : w = v
    · simp only [offColour, if_pos h]; exact measurable_const
    · simp only [offColour, if_neg h]
      exact (measurable_colour w).comp measurable_freshLayer

theorem measurable_relColour (v : ℕ) : Measurable (relColour v) :=
  measurable_pi_lambda _ fun w =>
    Measurable.comp (g := fun p : Bool × Bool => xor p.1 p.2) Measurable.of_discrete
      (((measurable_colour w).comp measurable_freshLayer).prodMk
        ((measurable_colour v).comp measurable_freshLayer))

/-! ### The local window at a vertex is independent of the relative colouring -/

/-- The singleton support at `v`. -/
def vertexFinset (v : ℕ) : Finset (Σ _ : Unit, ℕ) := {⟨(), v⟩}

/-- The local window at `v`. -/
noncomputable abbrev window (v : ℕ) :=
  localLatents (S := ternarySig) (vertexFinset v) 2

theorem measurable_window (v : ℕ) : Measurable (window v) :=
  measurable_localLatents (S := ternarySig) _ 2

/-- The reference colour is a function of the local window. -/
theorem colour_v_eq_window (v : ℕ) (ω : Cube) :
    colour (freshLayer ω) v =
      decide (window v ω ⟨singIndex v, by simp [singIndex, vertexFinset]⟩ ≤ 1 / 2) :=
  colour_freshLayer ω v

open scoped Classical in
/-- The blanked colouring reads only singleton coordinates away from `v`, the window reads only
coordinates inside `{v}`: they are independent. -/
theorem indepFun_offColour_window (v : ℕ) :
    IndepFun (offColour v) (window v) (rankLatentSource ternarySig 2) := by
  set μ := rankLatentSource ternarySig 2 with hμ
  set m : RankLatentIndex ternarySig 2 → MeasurableSpace Cube :=
    fun i => MeasurableSpace.comap (fun ω : Cube => ω i) inferInstance with hm
  have hind : iIndep m μ := by
    have h := iIndepFun_infinitePi (P := fun _ : RankLatentIndex ternarySig 2 => uniform01)
      (X := fun _ x => x) fun _ => measurable_id
    exact h
  set Sset : Set (RankLatentIndex ternarySig 2) := {i | ∃ w, w ≠ v ∧ i = singIndex w} with hS
  set Tset : Set (RankLatentIndex ternarySig 2) := {i | i.1 ⊆ vertexFinset v} with hT
  have hST : Disjoint Sset Tset := by
    rw [Set.disjoint_left]
    rintro i ⟨w, hwv, rfl⟩ hi
    apply hwv
    have := hi (Finset.mem_singleton_self (⟨(), w⟩ : Σ _ : Unit, ℕ))
    simpa [vertexFinset] using this
  have hdisj := indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le) hind hST
  have hoffm : @Measurable Cube (ℕ → Bool) (⨆ i ∈ Sset, m i) _ (offColour v) := by
    letI : MeasurableSpace Cube := ⨆ i ∈ Sset, m i
    refine measurable_pi_iff.mpr fun w => ?_
    by_cases h : w = v
    · simp only [offColour, if_pos h]; exact measurable_const
    · simp only [offColour, if_neg h]
      rw [show (fun ω : Cube => colour (freshLayer ω) w) =
          fun ω => decide (ω (singIndex w) ≤ 1 / 2) from funext fun ω => colour_freshLayer ω w]
      refine measurable_decideLe ?_
      exact Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ∈ Sset) => m i)
        (singIndex w) ⟨w, h, rfl⟩)
  have hwinm : @Measurable Cube (LocalLatentSpace (S := ternarySig) (vertexFinset v) 2)
      (⨆ i ∈ Tset, m i) _ (window v) := by
    letI : MeasurableSpace Cube := ⨆ i ∈ Tset, m i
    refine measurable_pi_iff.mpr fun B => ?_
    exact Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ∈ Tset) => m i) B.1 B.2)
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hdisj hoffm.comap_le)
    hwinm.comap_le

/-- The uniform threshold bit is fair. -/
theorem uniform01_Iic_half : uniform01 (Set.Iic (1 / 2 : ℝ)) = 1 / 2 := by
  rw [uniform01_Iic (by norm_num)]
  rw [show (1 / 2 : ℝ) = ((1 : ℝ) / 2) from rfl]
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]

theorem uniform01_map_decide_not :
    (uniform01.map fun t : ℝ => decide (t ≤ 1 / 2)).map not =
      uniform01.map fun t : ℝ => decide (t ≤ 1 / 2) := by
  have hm : Measurable fun t : ℝ => decide (t ≤ 1 / 2) := measurable_decideLe measurable_id
  rw [Measure.map_map Measurable.of_discrete hm]
  refine Measure.ext_of_singleton fun b => ?_
  rw [Measure.map_apply (Measurable.of_discrete.comp hm) (measurableSet_singleton b),
    Measure.map_apply hm (measurableSet_singleton b)]
  have h1 : (fun t : ℝ => decide (t ≤ 1 / 2)) ⁻¹' {true} = Set.Iic (1 / 2 : ℝ) := by
    ext t; simp
  have h2 : (fun t : ℝ => decide (t ≤ 1 / 2)) ⁻¹' {false} = (Set.Iic (1 / 2 : ℝ))ᶜ := by
    ext t; simp
  have hc : uniform01 (Set.Iic (1 / 2 : ℝ))ᶜ = 1 / 2 := by
    rw [prob_compl_eq_one_sub measurableSet_Iic, uniform01_Iic_half, one_div,
      ENNReal.one_sub_inv_two]
  cases b
  · rw [show (not ∘ fun t : ℝ => decide (t ≤ 1 / 2)) ⁻¹' {false} =
        (fun t : ℝ => decide (t ≤ 1 / 2)) ⁻¹' {true} from by ext t; simp, h1, h2,
      uniform01_Iic_half, hc]
  · rw [show (not ∘ fun t : ℝ => decide (t ≤ 1 / 2)) ⁻¹' {true} =
        (fun t : ℝ => decide (t ≤ 1 / 2)) ⁻¹' {false} from by ext t; simp, h1, h2,
      uniform01_Iic_half, hc]

/-- The law of the blanked colouring is invariant under flipping all colours off `v`. -/
theorem map_offColour_flip (v : ℕ) :
    (rankLatentSource ternarySig 2).map (flipOff v true ∘ offColour v) =
      (rankLatentSource ternarySig 2).map (offColour v) := by
  set g : ℕ → ℝ → Bool := fun w t => if w = v then false else decide (t ≤ 1 / 2) with hg
  set g' : ℕ → ℝ → Bool := fun w t => if w = v then false else !decide (t ≤ 1 / 2) with hg'
  have hgm : ∀ w, Measurable (g w) := fun w => by
    by_cases h : w = v
    · simp only [hg, if_pos h]; exact measurable_const
    · simp only [hg, if_neg h]; exact measurable_decideLe measurable_id
  have hgm' : ∀ w, Measurable (g' w) := fun w => by
    by_cases h : w = v
    · simp only [hg', if_pos h]; exact measurable_const
    · simp only [hg', if_neg h]
      exact Measurable.comp (g := not) Measurable.of_discrete (measurable_decideLe measurable_id)
  have hread : Measurable fun (ω : Cube) (w : ℕ) => ω (singIndex w) :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  have hoff : offColour v = (fun (x : ℕ → ℝ) (w : ℕ) => g w (x w)) ∘
      fun (ω : Cube) (w : ℕ) => ω (singIndex w) := by
    funext ω w
    simp only [offColour, Function.comp_apply, hg, colour_freshLayer]
  have hflip : flipOff v true ∘ offColour v = (fun (x : ℕ → ℝ) (w : ℕ) => g' w (x w)) ∘
      fun (ω : Cube) (w : ℕ) => ω (singIndex w) := by
    funext ω w
    show (if w = v then false else xor (offColour v ω w) true) =
      (if w = v then false else !decide (ω (singIndex w) ≤ 1 / 2))
    by_cases h : w = v
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      show xor (if w = v then false else colour (freshLayer ω) w) true = _
      rw [if_neg h, colour_freshLayer, Bool.xor_true]
  have hsrc : (rankLatentSource ternarySig 2).map (fun (ω : Cube) (w : ℕ) => ω (singIndex w)) =
      Measure.infinitePi fun _ : ℕ => uniform01 := by
    rw [rankLatentSource, iidUniformSource]
    exact Measure.map_infinitePi_infinitePi_of_inj singIndex_injective
  have hψ : Measurable fun (x : ℕ → ℝ) (w : ℕ) => g w (x w) :=
    measurable_pi_lambda _ fun w => (hgm w).comp (measurable_pi_apply w)
  have hψ' : Measurable fun (x : ℕ → ℝ) (w : ℕ) => g' w (x w) :=
    measurable_pi_lambda _ fun w => (hgm' w).comp (measurable_pi_apply w)
  rw [hflip, hoff, ← Measure.map_map hψ' hread, ← Measure.map_map hψ hread, hsrc,
    Measure.infinitePi_map_pi (μ := fun _ : ℕ => uniform01) (f := g') hgm',
    Measure.infinitePi_map_pi (μ := fun _ : ℕ => uniform01) (f := g) hgm]
  congr 1
  funext w
  by_cases h : w = v
  · simp only [hg, hg', if_pos h]
  · simp only [hg, hg', if_neg h]
    rw [← uniform01_map_decide_not, Measure.map_map Measurable.of_discrete
      (measurable_decideLe measurable_id : Measurable fun t : ℝ => decide (t ≤ 1 / 2))]
    rfl

/-- **The relative colouring is independent of the local window at `v`.** -/
theorem indepFun_relColour_window (v : ℕ) :
    IndepFun (relColour v) (window v) (rankLatentSource ternarySig 2) := by
  set μ := rankLatentSource ternarySig 2 with hμ
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro B C hB hC
  have hoff := (indepFun_iff_measure_inter_preimage_eq_mul.mp (indepFun_offColour_window v))
  -- the two window events reading the reference bit
  set C₀ : Set (LocalLatentSpace (S := ternarySig) (vertexFinset v) 2) :=
    {ℓ | decide (ℓ ⟨singIndex v, by simp [singIndex, vertexFinset]⟩ ≤ 1 / 2) = false} with hC₀
  set C₁ : Set (LocalLatentSpace (S := ternarySig) (vertexFinset v) 2) :=
    {ℓ | decide (ℓ ⟨singIndex v, by simp [singIndex, vertexFinset]⟩ ≤ 1 / 2) = true} with hC₁
  have hC₀m : MeasurableSet C₀ :=
    (measurable_decideLe (measurable_pi_apply _)) (measurableSet_singleton false)
  have hC₁m : MeasurableSet C₁ :=
    (measurable_decideLe (measurable_pi_apply _)) (measurableSet_singleton true)
  have hbit : ∀ ω : Cube, colour (freshLayer ω) v = false ↔ window v ω ∈ C₀ := fun ω => by
    rw [colour_v_eq_window]; rfl
  have hbit' : ∀ ω : Cube, colour (freshLayer ω) v = true ↔ window v ω ∈ C₁ := fun ω => by
    rw [colour_v_eq_window]; rfl
  -- split the relative-colour event by the reference bit
  have hsplit : ∀ D : Set (LocalLatentSpace (S := ternarySig) (vertexFinset v) 2),
      relColour v ⁻¹' B ∩ window v ⁻¹' D =
        (offColour v ⁻¹' B ∩ window v ⁻¹' (D ∩ C₀)) ∪
          (offColour v ⁻¹' (flipOff v true ⁻¹' B) ∩ window v ⁻¹' (D ∩ C₁)) := by
    intro D
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_union, relColour_eq_flipOff]
    rcases hcv : colour (freshLayer ω) v with _ | _
    · have h0 : window v ω ∈ C₀ := (hbit ω).mp hcv
      have h1 : window v ω ∉ C₁ := fun h => by
        have := (hbit' ω).mpr h; rw [hcv] at this; exact Bool.false_ne_true this
      have hid : flipOff v false (offColour v ω) = offColour v ω := by
        funext w; by_cases h : w = v <;> simp [flipOff, offColour, h]
      rw [hid]
      constructor
      · rintro ⟨hB', hD⟩; exact Or.inl ⟨hB', hD, h0⟩
      · rintro (⟨hB', hD, -⟩ | ⟨-, -, h⟩)
        · exact ⟨hB', hD⟩
        · exact absurd h h1
    · have h1 : window v ω ∈ C₁ := (hbit' ω).mp hcv
      have h0 : window v ω ∉ C₀ := fun h => by
        have := (hbit ω).mpr h; rw [hcv] at this; exact Bool.false_ne_true this.symm
      constructor
      · rintro ⟨hB', hD⟩; exact Or.inr ⟨hB', hD, h1⟩
      · rintro (⟨-, -, h⟩ | ⟨hB', hD, -⟩)
        · exact absurd h h0
        · exact ⟨hB', hD⟩
  have hdisj : ∀ D : Set (LocalLatentSpace (S := ternarySig) (vertexFinset v) 2),
      Disjoint (offColour v ⁻¹' B ∩ window v ⁻¹' (D ∩ C₀))
        (offColour v ⁻¹' (flipOff v true ⁻¹' B) ∩ window v ⁻¹' (D ∩ C₁)) := by
    intro D
    rw [Set.disjoint_left]
    rintro ω ⟨-, -, h0⟩ ⟨-, -, h1⟩
    have := ((hbit ω).mpr h0).symm.trans ((hbit' ω).mpr h1)
    exact Bool.false_ne_true this
  have hflipB : MeasurableSet (flipOff v true ⁻¹' B) := measurable_flipOff v true hB
  have hlaw : μ (offColour v ⁻¹' (flipOff v true ⁻¹' B)) = μ (offColour v ⁻¹' B) := by
    rw [← Set.preimage_comp, ← Measure.map_apply ((measurable_flipOff v true).comp
      (measurable_offColour v)) hB, map_offColour_flip,
      Measure.map_apply (measurable_offColour v) hB]
  -- the general identity
  have key : ∀ D : Set (LocalLatentSpace (S := ternarySig) (vertexFinset v) 2), MeasurableSet D →
      μ (relColour v ⁻¹' B ∩ window v ⁻¹' D) = μ (offColour v ⁻¹' B) * μ (window v ⁻¹' D) := by
    intro D hD
    rw [hsplit D, measure_union (hdisj D)
      (((measurable_offColour v) hflipB).inter ((measurable_window v) (hD.inter hC₁m))),
      hoff B (D ∩ C₀) hB (hD.inter hC₀m), hoff (flipOff v true ⁻¹' B) (D ∩ C₁) hflipB
        (hD.inter hC₁m), hlaw, ← mul_add, Set.preimage_inter, Set.preimage_inter,
      ← measure_union ?_ ((measurable_window v) hD |>.inter ((measurable_window v) hC₁m))]
    · congr 1
      rw [← Set.inter_union_distrib_left]
      congr 1
      have hcover : window v ⁻¹' C₀ ∪ window v ⁻¹' C₁ = Set.univ := by
        ext ω
        simp only [Set.mem_union, Set.mem_preimage, Set.mem_univ, iff_true]
        rcases h : colour (freshLayer ω) v with _ | _
        · exact Or.inl ((hbit ω).mp h)
        · exact Or.inr ((hbit' ω).mp h)
      rw [hcover, Set.inter_univ]
    · rw [Set.disjoint_left]
      rintro ω ⟨-, h0⟩ ⟨-, h1⟩
      exact Bool.false_ne_true (((hbit ω).mpr h0).symm.trans ((hbit' ω).mpr h1))
  have hB' : μ (relColour v ⁻¹' B) = μ (offColour v ⁻¹' B) := by
    have := key Set.univ MeasurableSet.univ
    simpa using this
  rw [key C hC, hB']

/-! ### Triviality of the empty and singleton fixing algebras -/

/-- **Fixing events at fewer than two vertices are null or conull.** The pullback to the rank-two
cube is invariant under every permutation fixing the support, hence almost surely a function of
the local window there; but it is also a function of the relative colouring, which is
independent of that window. A set independent of itself is trivial. -/
theorem fixing_trivial_of_card_lt_two {A : Finset (Σ _ : Unit, ℕ)} (hA : A.card < 2)
    {E : Set (RelStructure ternarySig (Vinfinite ternarySig))}
    (hE : MeasurableSet[RelStructure.fixingAlgebra A] E) :
    ternaryLaw E = 0 ∨ ternaryLaw E = 1 := by
  classical
  -- reduce to a singleton support
  obtain ⟨v, hAv⟩ : ∃ v : ℕ, A ⊆ vertexFinset v := by
    rcases Nat.lt_succ_iff.mp hA |>.eq_or_lt with h1 | h0
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
      obtain ⟨u, w⟩ := a
      cases u
      exact ⟨w, le_rfl⟩
    · have : A = ∅ := Finset.card_eq_zero.mp (Nat.lt_one_iff.mp h0)
      exact ⟨0, by rw [this]; exact Finset.empty_subset _⟩
  have hE' : MeasurableSet[RelStructure.fixingAlgebra (vertexFinset v)] E :=
    RelStructure.fixingAlgebra_mono hAv E hE
  set μ := rankLatentSource ternarySig 2 with hμ
  set D : Set Cube := (arr ∘ freshLayer) ⁻¹' E with hD
  have hDm : MeasurableSet D := (measurable_arr.comp measurable_freshLayer) hE'.1
  have hlaw : ternaryLaw E = μ D := by
    rw [ternaryLaw_eq_map_cube, Measure.map_apply (measurable_arr.comp measurable_freshLayer) hE'.1]
  -- invariance of the pullback
  have hinv : ∀ σ : FinSuppPerm ternarySig, SortwiseFixing (vertexFinset v) σ.1 →
      rankLatentRelabel σ 2 ⁻¹' D =ᵐ[μ] D := by
    intro σ hσ
    refine Filter.EventuallyEq.of_eq ?_
    rw [hD, ← Set.preimage_comp,
      show (arr ∘ freshLayer) ∘ rankLatentRelabel σ 2 =
        RelStructure.relabel σ.1 ∘ (arr ∘ freshLayer) from
        funext fun ω => arr_freshLayer_rankLatentRelabel σ ω,
      Set.preimage_comp, hE'.2 σ.1 hσ]
  obtain ⟨D', ⟨C, hC, rfl⟩, hD'⟩ :=
    rankLatentSource_exists_local_ae_eq_of_ae_invariant (vertexFinset v) hDm hinv
  -- the pullback is a function of the relative colouring
  have hDrel : D = relColour v ⁻¹' (arrOf ⁻¹' E) := by
    ext ω
    simp only [hD, Set.mem_preimage, Function.comp_apply, arr_freshLayer_eq_arrOf_relColour v]
  have hBm : MeasurableSet (arrOf ⁻¹' E) := measurable_arrOf hE'.1
  have hind := (indepFun_iff_measure_inter_preimage_eq_mul.mp (indepFun_relColour_window v))
    (arrOf ⁻¹' E) C hBm hC
  have hsq : μ D = μ D * μ D := by
    calc μ D = μ (D ∩ window v ⁻¹' C) := by
          refine (measure_congr ?_).symm
          exact ((Filter.EventuallyEq.refl _ D).inter hD').trans
            (Filter.EventuallyEq.of_eq (Set.inter_self D))
      _ = μ D * μ (window v ⁻¹' C) := by rw [hDrel]; exact hind
      _ = μ D * μ D := by rw [measure_congr hD']
  rw [hlaw]
  rcases eq_or_ne (μ D) 0 with h0 | h0
  · exact Or.inl h0
  · right
    have h1 : 1 * μ D = μ D * μ D := by rw [one_mul]; exact hsq
    exact ((ENNReal.mul_left_inj h0 (measure_ne_top _ _)).mp h1).symm

/-! ### The independent rank-two representation -/

/-- **The rank-two coupling**: the law with an independent rank-two latent array. -/
noncomputable def rankTwoCoupling :
    Measure (RelStructure ternarySig (Vinfinite ternarySig) × Cube) :=
  ternaryLaw.prod (rankLatentSource ternarySig 2)

instance : IsProbabilityMeasure rankTwoCoupling := by
  rw [rankTwoCoupling]; infer_instance

@[simp] theorem rankTwoCoupling_map_fst : rankTwoCoupling.map Prod.fst = ternaryLaw := by
  rw [rankTwoCoupling, Measure.map_fst_prod]
  simp

@[simp] theorem rankTwoCoupling_map_snd :
    rankTwoCoupling.map Prod.snd = rankLatentSource ternarySig 2 := by
  rw [rankTwoCoupling, Measure.map_snd_prod]
  simp

open scoped Classical in
theorem ae_blockMap_coupling {A : Finset (Σ _ : Unit, ℕ)} (hA : A.card < 3) :
    (fun p : RelStructure ternarySig (Vinfinite ternarySig) × Cube =>
        blockMap (S := ternarySig) A p.1) =ᵐ[rankTwoCoupling] fun _ => fun _ => false := by
  have hmp : MeasurePreserving (Prod.fst :
      RelStructure ternarySig (Vinfinite ternarySig) × Cube → _) rankTwoCoupling ternaryLaw :=
    ⟨measurable_fst, rankTwoCoupling_map_fst⟩
  exact hmp.quasiMeasurePreserving.ae (ae_blockMap_of_card_lt_three hA)

open scoped Classical in
/-- **The independent rank-two representation.** Every clause of the contract holds. -/
noncomputable def rankTwoRep : ternaryExchangeable.RankRepresentation 2 where
  P := rankTwoCoupling
  isProbabilityMeasure_P := inferInstance
  map_fst := rankTwoCoupling_map_fst
  map_snd := rankTwoCoupling_map_snd
  invariant := by
    intro σ
    rw [rankTwoCoupling, ← Measure.map_prod_map _ _ (measurable_relabel σ.1)
      (rankLatentRelabel σ 2).measurable, ternaryLaw_map_relabel,
      rankLatentSource_map_rankLatentRelabel]
  lower_recovers := fun A hA =>
    ⟨fun _ => fun _ => false, measurable_const, ae_blockMap_coupling (by omega)⟩
  fixing_complete := by
    intro A hA E hE
    have hEmeas : MeasurableSet E := hE.1
    have hfst : rankTwoCoupling (Prod.fst ⁻¹' E) = ternaryLaw E := by
      rw [← rankTwoCoupling_map_fst, Measure.map_apply measurable_fst hEmeas]
    rcases fixing_trivial_of_card_lt_two hA hE with h0 | h1
    · refine ⟨∅, MeasurableSet.empty, ?_⟩
      rw [Set.preimage_empty]
      exact (ae_eq_empty.mpr (hfst.trans h0)).symm
    · refine ⟨Set.univ, MeasurableSet.univ, ?_⟩
      rw [Set.preimage_univ]
      exact (ae_eq_univ.mpr ((prob_compl_eq_zero_iff (measurable_fst hEmeas)).mpr
        (hfst.trans h1))).symm
  screening := fun A hA =>
    CondIndepFun.congr (condIndepFun_const_left (fun _ => false) _) measurable_const
      (measurable_restObservation 2 _)
      ((measurable_blockMap (S := ternarySig) _).comp measurable_fst)
      (measurable_restObservation 2 _) (ae_blockMap_coupling (by omega)).symm
      Filter.EventuallyEq.rfl

/-! ### The pair event has probability one half -/

theorem uniform01_Iic_half_compl : uniform01 (Set.Iic (1 / 2 : ℝ))ᶜ = 1 / 2 := by
  rw [prob_compl_eq_one_sub measurableSet_Iic, uniform01_Iic_half, one_div,
    ENNReal.one_sub_inv_two]

/-- Two distinct vertices' colours are two independent fair bits. -/
theorem source_colour_pair {u v : ℕ} (huv : u ≠ v) (b : Bool) :
    iidUniformSource (RankSupport ternarySig 1)
      {ω | colour ω u = b ∧ colour ω v = !b} = 1 / 4 := by
  classical
  have hne : vertexSupport u ≠ vertexSupport v := fun h => huv (vertexSupport_injective h)
  set t : RankSupport ternarySig 1 → Set ℝ := fun A =>
    if A = vertexSupport u then (if b then Set.Iic (1 / 2 : ℝ) else (Set.Iic (1 / 2 : ℝ))ᶜ)
    else (if b then (Set.Iic (1 / 2 : ℝ))ᶜ else Set.Iic (1 / 2 : ℝ)) with ht
  have hset : {ω : Colours | colour ω u = b ∧ colour ω v = !b} =
      Set.pi ({vertexSupport u, vertexSupport v} : Finset (RankSupport ternarySig 1)) t := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, ht,
      if_neg hne.symm, colour]
    cases b <;> simp
  have hmeas : ∀ A ∈ ({vertexSupport u, vertexSupport v} :
      Finset (RankSupport ternarySig 1)), MeasurableSet (t A) := by
    intro A _
    simp only [ht]
    split_ifs <;> first | exact measurableSet_Iic | exact measurableSet_Iic.compl
  rw [hset, iidUniformSource, Measure.infinitePi_pi _ hmeas, Finset.prod_pair hne]
  simp only [ht, if_pos rfl, if_neg hne.symm]
  have h4 : (2 : ℝ≥0∞)⁻¹ * 2⁻¹ = 4⁻¹ := by
    rw [← ENNReal.mul_inv (by simp) (by simp)]; norm_num
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, uniform01_Iic_half_compl, uniform01_Iic_half]
    rw [one_div, one_div, h4]
  · simp only [↓reduceIte, uniform01_Iic_half_compl, uniform01_Iic_half]
    rw [one_div, one_div, h4]

theorem ternaryLaw_pairEvent {u v : ℕ} (huv : u ≠ v) : ternaryLaw (pairEvent u v) = 1 / 2 := by
  classical
  rw [ternaryLaw, Measure.map_apply measurable_arr (measurableSet_pairEvent u v)]
  have hpre : arr ⁻¹' pairEvent u v =
      {ω : Colours | colour ω u = true ∧ colour ω v = !true} ∪
        {ω | colour ω u = false ∧ colour ω v = !false} := by
    ext ω
    simp only [Set.mem_preimage, mem_pairEvent_arr, Set.mem_union, Set.mem_setOf_eq, huv,
      ne_eq, not_false_eq_true, true_and, Bool.not_true, Bool.not_false]
    cases colour ω u <;> cases colour ω v <;> simp
  have hdisj : Disjoint {ω : Colours | colour ω u = true ∧ colour ω v = !true}
      {ω | colour ω u = false ∧ colour ω v = !false} := by
    rw [Set.disjoint_left]
    rintro ω ⟨h1, -⟩ ⟨h2, -⟩
    rw [h1] at h2
    exact Bool.false_ne_true h2.symm
  have hm : ∀ b : Bool, MeasurableSet {ω : Colours | colour ω u = b ∧ colour ω v = !b} :=
    fun b => ((measurable_colour u) (measurableSet_singleton b)).inter
      ((measurable_colour v) (measurableSet_singleton (!b)))
  rw [hpre, measure_union hdisj (hm false), source_colour_pair huv, source_colour_pair huv,
    ← two_mul, one_div, one_div, show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
    ENNReal.mul_inv (by simp) (by simp), ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp),
    one_mul]

/-- The three pair events on a triangle are jointly null. -/
theorem ternaryLaw_triangle (a b c : ℕ) :
    ternaryLaw (pairEvent a b ∩ pairEvent b c ∩ pairEvent a c) = 0 := by
  rw [ternaryLaw, Measure.map_apply measurable_arr
    (((measurableSet_pairEvent a b).inter (measurableSet_pairEvent b c)).inter
      (measurableSet_pairEvent a c))]
  have h : arr ⁻¹' (pairEvent a b ∩ pairEvent b c ∩ pairEvent a c) = ∅ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    exact not_mem_triangle (colour ω) a b c
  rw [h, measure_empty]

/-! ### No exact rank-three successor -/

/-- The pair support as a rank-two support. -/
def pairIdx (u v : ℕ) (huv : u ≠ v) : RankSupport ternarySig 2 :=
  ⟨pairSupport u v, Finset.card_pair fun h => huv (congrArg Sigma.snd h)⟩

theorem card_pairSupport {u v : ℕ} (huv : u ≠ v) : (pairSupport u v).card = 2 :=
  (pairIdx u v huv).2

/-- The section of the rank-three local window at a pair: the old coordinates from `o`, the fresh
pair coordinate from `t`. -/
noncomputable def sect (u v : ℕ) (o : Cube) (t : ℝ) :
    LocalLatentSpace (S := ternarySig) (pairSupport u v) 3 :=
  fun B => if h : B.1.1.card < 2 then o ⟨B.1.1, h⟩ else t

theorem measurable_sect_uncurry (u v : ℕ) :
    Measurable fun p : Cube × ℝ => sect u v p.1 p.2 := by
  refine measurable_pi_lambda _ fun B => ?_
  by_cases h : B.1.1.card < 2
  · simp only [sect, dif_pos h]; exact (measurable_pi_apply _).comp measurable_fst
  · simp only [sect, dif_neg h]; exact measurable_snd

/-- The local window at a pair, read on the successor split of the cube. -/
theorem localLatents_succEquiv_symm {u v : ℕ} (huv : u ≠ v) (o : Cube)
    (x : RankSupport ternarySig 2 → ℝ) :
    localLatents (S := ternarySig) (pairSupport u v) 3 ((rankLatentSpaceSuccEquiv 2).symm (o, x)) =
      sect u v o (x (pairIdx u v huv)) := by
  funext B
  show Sum.elim o x (rankLatentIndexSuccEquiv 2 B.1) = _
  by_cases h : B.1.1.card < 2
  · simp only [rankLatentIndexSuccEquiv, Equiv.coe_fn_mk, dif_pos h, Sum.elim_inl, sect]
  · have hB : B.1.1 = pairSupport u v := by
      refine Finset.eq_of_subset_of_card_le B.2 ?_
      rw [card_pairSupport huv]
      omega
    simp only [rankLatentIndexSuccEquiv, Equiv.coe_fn_mk, dif_neg h, Sum.elim_inr, sect]
    exact congrArg x (Subtype.ext hB)

/-- Truncation to rank two is the first component of the successor split. -/
theorem rankLatentProjection_eq_fst_succEquiv :
    rankLatentProjection (S := ternarySig) (Nat.le_succ 2) =
      Prod.fst ∘ rankLatentSpaceSuccEquiv 2 := by
  funext ω A
  rfl

theorem rankLatentProjection_succEquiv_symm (o : Cube) (x : RankSupport ternarySig 2 → ℝ) :
    rankLatentProjection (S := ternarySig) (Nat.le_succ 2)
      ((rankLatentSpaceSuccEquiv 2).symm (o, x)) = o := by
  rw [rankLatentProjection_eq_fst_succEquiv, Function.comp_apply,
    MeasurableEquiv.apply_symm_apply]

theorem source_three_eq :
    rankLatentSource ternarySig 3 =
      ((rankLatentSource ternarySig 2).prod (iidUniformSource (RankSupport ternarySig 2))).map
        (rankLatentSpaceSuccEquiv 2).symm := by
  rw [← rankLatentSource_map_rankLatentSpaceSuccEquiv, MeasurableEquiv.map_symm_map]

/-- **The obstruction**: the independent rank-two representation of the ternary parity law has
no exact rank-three successor. -/
theorem isEmpty_rankSuccessor : IsEmpty (InfiniteRelExchangeableLaw.RankSuccessor rankTwoRep) := by
  classical
  refine ⟨fun D => ?_⟩
  set next := D.next with hnext
  haveI := next.isProbabilityMeasure_P
  set P := next.P with hP
  have hprojm : Measurable (rankLatentProjection (S := ternarySig) (Nat.le_succ 2)) :=
    measurable_rankLatentProjection (S := ternarySig) (Nat.le_succ 2)
  -- the structure marginal and the latent marginal
  have hfst : P.map Prod.fst = ternaryLaw := next.map_fst
  have hsnd : P.map Prod.snd = rankLatentSource ternarySig 3 := next.map_snd
  have hold : P.map (rankLatentProjection (S := ternarySig) (Nat.le_succ 2) ∘ Prod.snd) =
      rankLatentSource ternarySig 2 := by
    rw [← Measure.map_map hprojm measurable_snd, hsnd, rankLatentProjection_eq_fst_succEquiv,
      ← Measure.map_map measurable_fst (rankLatentSpaceSuccEquiv 2).measurable,
      rankLatentSource_map_rankLatentSpaceSuccEquiv, Measure.map_fst_prod]
    simp only [measure_univ, one_smul]
  -- the structure is independent of the old array, by exact truncation
  have hind : IndepFun (Prod.fst : RelStructure ternarySig (Vinfinite ternarySig) ×
      RankLatentSpace ternarySig 3 → _)
      (rankLatentProjection (S := ternarySig) (Nat.le_succ 2) ∘ Prod.snd) P := by
    refine (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
      (hprojm.comp measurable_snd).aemeasurable).mpr ?_
    rw [hfst, hold]
    exact D.truncation
  -- the local representatives at the pairs
  have hrep : ∀ u v : ℕ, u ≠ v → ∃ U : Set (LocalLatentSpace (S := ternarySig) (pairSupport u v) 3),
      MeasurableSet U ∧ Prod.fst ⁻¹' pairEvent u v =ᵐ[P]
        Prod.snd ⁻¹' (localLatents (S := ternarySig) (pairSupport u v) 3 ⁻¹' U) := by
    intro u v huv
    obtain ⟨E', ⟨U, hU, rfl⟩, hE'⟩ := next.lower_fixing_complete (pairSupport u v)
      (by rw [card_pairSupport huv]; omega) (pairEvent u v)
      (measurableSet_fixingAlgebra_pairEvent u v)
    exact ⟨U, hU, hE'⟩
  -- the fresh-coordinate mass of a representative is one half at almost every old point
  have hhalf : ∀ u v : ℕ, ∀ huv : u ≠ v,
      ∀ U : Set (LocalLatentSpace (S := ternarySig) (pairSupport u v) 3), MeasurableSet U →
      Prod.fst ⁻¹' pairEvent u v =ᵐ[P]
        Prod.snd ⁻¹' (localLatents (S := ternarySig) (pairSupport u v) 3 ⁻¹' U) →
      (fun o : Cube => uniform01 {t | sect u v o t ∈ U}) =ᵐ[rankLatentSource ternarySig 2]
        fun _ => 1 / 2 := by
    intro u v huv U hU hae
    have hsectm : MeasurableSet {p : Cube × ℝ | sect u v p.1 p.2 ∈ U} :=
      measurable_sect_uncurry u v hU
    have hφ : Measurable fun o : Cube => uniform01 {t | sect u v o t ∈ U} :=
      measurable_measure_prodMk_left hsectm
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hφ measurable_const fun B hB _ => ?_
    rw [setLIntegral_const]
    have hV : MeasurableSet (localLatents (S := ternarySig) (pairSupport u v) 3 ⁻¹' U) :=
      (measurable_localLatents (S := ternarySig) _ 3) hU
    have h1 : P (Prod.fst ⁻¹' pairEvent u v ∩
        (rankLatentProjection (S := ternarySig) (Nat.le_succ 2) ∘ Prod.snd) ⁻¹' B) =
        1 / 2 * (rankLatentSource ternarySig 2) B := by
      rw [(indepFun_iff_measure_inter_preimage_eq_mul.mp hind) _ _
        (measurableSet_pairEvent u v) hB, ← Measure.map_apply measurable_fst
        (measurableSet_pairEvent u v), hfst, ternaryLaw_pairEvent huv,
        ← Measure.map_apply (hprojm.comp measurable_snd) hB, hold]
    have h2 : P (Prod.fst ⁻¹' pairEvent u v ∩
        (rankLatentProjection (S := ternarySig) (Nat.le_succ 2) ∘ Prod.snd) ⁻¹' B) =
        ∫⁻ o in B, uniform01 {t | sect u v o t ∈ U} ∂(rankLatentSource ternarySig 2) := by
      rw [measure_congr (hae.inter (Filter.EventuallyEq.refl _ _)),
        show Prod.snd ⁻¹' (localLatents (S := ternarySig) (pairSupport u v) 3 ⁻¹' U) ∩
          (rankLatentProjection (S := ternarySig) (Nat.le_succ 2) ∘ Prod.snd) ⁻¹' B =
          Prod.snd ⁻¹' (localLatents (S := ternarySig) (pairSupport u v) 3 ⁻¹' U ∩
            rankLatentProjection (S := ternarySig) (Nat.le_succ 2) ⁻¹' B) from rfl,
        ← Measure.map_apply measurable_snd (hV.inter (hprojm hB)), hsnd, source_three_eq,
        MeasurableEquiv.map_apply, Measure.prod_apply
          ((rankLatentSpaceSuccEquiv 2).symm.measurable (hV.inter (hprojm hB))),
        ← lintegral_indicator hB]
      refine lintegral_congr fun o => ?_
      by_cases hoB : o ∈ B
      · rw [Set.indicator_of_mem hoB]
        have hS : MeasurableSet {t | sect u v o t ∈ U} :=
          ((measurable_sect_uncurry u v).comp measurable_prodMk_left) hU
        have hset : Prod.mk o ⁻¹' ((rankLatentSpaceSuccEquiv 2).symm ⁻¹'
            (localLatents (S := ternarySig) (pairSupport u v) 3 ⁻¹' U ∩
              rankLatentProjection (S := ternarySig) (Nat.le_succ 2) ⁻¹' B)) =
            (fun x : RankSupport ternarySig 2 → ℝ => x (pairIdx u v huv)) ⁻¹'
              {t | sect u v o t ∈ U} := by
          ext x
          simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq,
            localLatents_succEquiv_symm huv, rankLatentProjection_succEquiv_symm, hoB, and_true]
        rw [hset, ← Measure.map_apply (measurable_pi_apply (pairIdx u v huv) :
          Measurable fun x : RankSupport ternarySig 2 → ℝ => x (pairIdx u v huv)) hS,
          iidUniformSource, Measure.infinitePi_map_eval]
      · rw [Set.indicator_of_notMem hoB]
        have hempty : Prod.mk o ⁻¹' ((rankLatentSpaceSuccEquiv 2).symm ⁻¹'
            (localLatents (S := ternarySig) (pairSupport u v) 3 ⁻¹' U ∩
              rankLatentProjection (S := ternarySig) (Nat.le_succ 2) ⁻¹' B)) = ∅ := by
          ext x
          simp only [Set.mem_preimage, Set.mem_inter_iff, rankLatentProjection_succEquiv_symm,
            hoB, and_false, Set.mem_empty_iff_false]
        rw [hempty, measure_empty]
    rw [← h2, h1, mul_comm]
  -- the three pairs of the triangle
  obtain ⟨U01, hU01, hae01⟩ := hrep 0 1 (by decide)
  obtain ⟨U12, hU12, hae12⟩ := hrep 1 2 (by decide)
  obtain ⟨U02, hU02, hae02⟩ := hrep 0 2 (by decide)
  have h01 := hhalf 0 1 (by decide) U01 hU01 hae01
  have h12 := hhalf 1 2 (by decide) U12 hU12 hae12
  have h02 := hhalf 0 2 (by decide) U02 hU02 hae02
  set T : Set (RelStructure ternarySig (Vinfinite ternarySig) × RankLatentSpace ternarySig 3) :=
    Prod.fst ⁻¹' (pairEvent 0 1 ∩ pairEvent 1 2 ∩ pairEvent 0 2) with hT
  -- the joint mass is zero, by parity
  have hT0 : P T = 0 := by
    rw [hT, ← Measure.map_apply measurable_fst (((measurableSet_pairEvent 0 1).inter
      (measurableSet_pairEvent 1 2)).inter (measurableSet_pairEvent 0 2)), hfst,
      ternaryLaw_triangle]
  -- the joint mass is one eighth, by the representatives
  set V01 := localLatents (S := ternarySig) (pairSupport 0 1) 3 ⁻¹' U01 with hV01
  set V12 := localLatents (S := ternarySig) (pairSupport 1 2) 3 ⁻¹' U12 with hV12
  set V02 := localLatents (S := ternarySig) (pairSupport 0 2) 3 ⁻¹' U02 with hV02
  have hVm : MeasurableSet (V01 ∩ V12 ∩ V02) :=
    (((measurable_localLatents (S := ternarySig) _ 3) hU01).inter
      ((measurable_localLatents (S := ternarySig) _ 3) hU12)).inter
      ((measurable_localLatents (S := ternarySig) _ 3) hU02)
  have hTV : T =ᵐ[P] Prod.snd ⁻¹' (V01 ∩ V12 ∩ V02) := by
    rw [hT, Set.preimage_inter, Set.preimage_inter, hV01, hV12, hV02, Set.preimage_inter,
      Set.preimage_inter]
    exact (hae01.inter hae12).inter hae02
  have hne1 : pairIdx 0 1 (by decide) ≠ pairIdx 1 2 (by decide) := by
    intro h
    have := congrArg (fun A : RankSupport ternarySig 2 => (⟨(), 0⟩ : Σ _ : Unit, ℕ) ∈ A.1) h
    simp [pairIdx, pairSupport] at this
  have hne2 : pairIdx 0 1 (by decide) ≠ pairIdx 0 2 (by decide) := by
    intro h
    have := congrArg (fun A : RankSupport ternarySig 2 => (⟨(), 1⟩ : Σ _ : Unit, ℕ) ∈ A.1) h
    simp [pairIdx, pairSupport] at this
  have hne3 : pairIdx 1 2 (by decide) ≠ pairIdx 0 2 (by decide) := by
    intro h
    have := congrArg (fun A : RankSupport ternarySig 2 => (⟨(), 1⟩ : Σ _ : Unit, ℕ) ∈ A.1) h
    simp [pairIdx, pairSupport] at this
  set tset : Cube → RankSupport ternarySig 2 → Set ℝ := fun o p =>
    if p = pairIdx 0 1 (by decide) then {t | sect 0 1 o t ∈ U01}
    else if p = pairIdx 1 2 (by decide) then {t | sect 1 2 o t ∈ U12}
    else {t | sect 0 2 o t ∈ U02} with htset
  have hsec : ∀ o : Cube, Prod.mk o ⁻¹' ((rankLatentSpaceSuccEquiv 2).symm ⁻¹' (V01 ∩ V12 ∩ V02)) =
      Set.pi ({pairIdx 0 1 (by decide), pairIdx 1 2 (by decide), pairIdx 0 2 (by decide)} :
        Finset (RankSupport ternarySig 2)) (tset o) := by
    intro o
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, hV01, hV12, hV02,
      localLatents_succEquiv_symm (u := 0) (v := 1) (by decide),
      localLatents_succEquiv_symm (u := 1) (v := 2) (by decide),
      localLatents_succEquiv_symm (u := 0) (v := 2) (by decide)]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩ p hp
      rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · simp only [htset, if_pos rfl]; exact h1
      · simp only [htset, if_neg hne1.symm]; exact h2
      · simp only [htset, if_neg hne2.symm, if_neg hne3.symm]; exact h3
    · intro h
      have h1 := h (pairIdx 0 1 (by decide)) (by simp)
      have h2 := h (pairIdx 1 2 (by decide)) (by simp)
      have h3 := h (pairIdx 0 2 (by decide)) (by simp)
      simp only [htset, if_pos rfl] at h1
      simp only [htset, if_neg hne1.symm] at h2
      simp only [htset, if_neg hne2.symm, if_neg hne3.symm] at h3
      exact ⟨⟨h1, h2⟩, h3⟩
  have hsm : ∀ o : Cube, ∀ p ∈ ({pairIdx 0 1 (by decide), pairIdx 1 2 (by decide),
      pairIdx 0 2 (by decide)} : Finset (RankSupport ternarySig 2)), MeasurableSet (tset o p) := by
    intro o p _
    simp only [htset]
    split_ifs
    · exact ((measurable_sect_uncurry 0 1).comp measurable_prodMk_left) hU01
    · exact ((measurable_sect_uncurry 1 2).comp measurable_prodMk_left) hU12
    · exact ((measurable_sect_uncurry 0 2).comp measurable_prodMk_left) hU02
  have h8 : (1 / 2 : ℝ≥0∞) * (1 / 2 * (1 / 2)) = 1 / 8 := by
    simp only [one_div]
    rw [← ENNReal.mul_inv (by simp) (by simp), ← ENNReal.mul_inv (by simp) (by simp)]
    norm_num
  have hT8 : P T = 1 / 8 := by
    rw [measure_congr hTV, ← Measure.map_apply measurable_snd hVm, hsnd, source_three_eq,
      MeasurableEquiv.map_apply,
      Measure.prod_apply ((rankLatentSpaceSuccEquiv 2).symm.measurable hVm)]
    have hae : (fun o : Cube => iidUniformSource (RankSupport ternarySig 2)
        (Prod.mk o ⁻¹' ((rankLatentSpaceSuccEquiv 2).symm ⁻¹' (V01 ∩ V12 ∩ V02))))
        =ᵐ[(rankLatentSource ternarySig 2)] fun _ => (1 / 2 : ℝ≥0∞) * (1 / 2 * (1 / 2)) := by
      filter_upwards [h01, h12, h02] with o e1 e2 e3
      rw [hsec o, iidUniformSource, Measure.infinitePi_pi _ (hsm o),
        Finset.prod_insert (by simp [hne1, hne2]), Finset.prod_insert (by simp [hne3]),
        Finset.prod_singleton]
      simp only [htset, if_pos rfl, if_neg hne1.symm, if_neg hne2.symm, if_neg hne3.symm,
        ite_true]
      rw [e1, e2, e3]
    rw [lintegral_congr_ae hae, lintegral_const, measure_univ, mul_one, h8]
  rw [hT0] at hT8
  exact absurd hT8.symm (by simp)

/-- **The universal successor statement is false**: the old target, quantified over every current
representation, is refuted. -/
theorem not_successorStatement : ¬ InfiniteRelExchangeableLaw.SuccessorStatement ternarySig :=
  fun h =>
  isEmpty_rankSuccessor.false (h ternaryExchangeable 2 rankTwoRep).some

end TernaryParityRegression

end RelSignature
