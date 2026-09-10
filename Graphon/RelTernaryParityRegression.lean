/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRankSuccessorContract
import Graphon.RelAdmissible
import Graphon.RelColourLaw

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

open ColourLaw

/-- The one-sort, single ternary relation signature. -/
abbrev ternarySig : RelSignature := oneSortSig 3

/-- The coordinate at an ordered vertex triple. -/
abbrev ternaryCoord {V : Type*} (a b c : V) : RelCoord ternarySig (fun _ => V) := ⟨(), ![a, b, c]⟩

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
noncomputable def arr (ω : Colours 3) : RelStructure ternarySig (Vinfinite ternarySig) :=
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

theorem measurable_arr : Measurable arr := measurable_arrOf.comp measurable_colours

/-- The array depends on the colouring only through its differences. -/
theorem arrOf_xor_const (d : ℕ → Bool) (b : Bool) : arrOf (fun v => xor (d v) b) = arrOf d := by
  funext c
  simp only [arrOf]
  split_ifs
  · cases d (c.2 0) <;> cases d (c.2 1) <;> cases b <;> rfl
  · rfl

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
theorem arr_comp_supportPerm (σ : Equiv.Perm ℕ) (ω : Colours 3) :
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
      arr ∘ (fun ω : Colours 3 => fun A => ω (supportPerm (σ ()) A)) from by
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

theorem mem_pairEvent_arr {u v : ℕ} (ω : Colours 3) :
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

/-- The ternary law is the colour law of `arrOf`. -/
theorem ternaryLaw_eq_colourLaw : ternaryLaw = colourLaw arrOf := rfl

theorem arrOf_comp' (σ : Equiv.Perm ℕ) (d : ℕ → Bool) :
    arrOf (d ∘ σ) = RelStructure.relabel (fun _ : Unit => σ) (arrOf d) := arrOf_comp d σ

theorem ternaryLaw_eq_map_cube :
    ternaryLaw = (rankLatentSource ternarySig 2).map (arr ∘ freshLayer) :=
  colourLaw_eq_map_cube measurable_arrOf

/-- **Fixing events at fewer than two vertices are null or conull.** -/
theorem fixing_trivial_of_card_lt_two {A : Finset (Σ _ : Unit, ℕ)} (hA : A.card < 2)
    {E : Set (RelStructure ternarySig (Vinfinite ternarySig))}
    (hE : MeasurableSet[RelStructure.fixingAlgebra A] E) :
    ternaryLaw E = 0 ∨ ternaryLaw E = 1 :=
  ColourLaw.fixing_trivial_of_card_lt_two measurable_arrOf arrOf_comp' arrOf_xor_const hA hE

open scoped Classical in
theorem arr_freshLayer_rankLatentRelabel (σ : FinSuppPerm ternarySig) (ω : Cube 3) :
    arr (freshLayer (rankLatentRelabel σ 2 ω)) = RelStructure.relabel σ.1 (arr (freshLayer ω)) := by
  rw [freshLayer_rankLatentRelabel, arr_comp_supportPerm]

/-- The singleton latent index at a vertex. -/
theorem arr_freshLayer_eq_arrOf_relColour (v : ℕ) (ω : Cube 3) :
    arr (freshLayer ω) = arrOf (relColour v ω) :=
  (arrOf_xor_const _ _).symm

/-! ### The independent rank-two representation -/

/-- **The rank-two coupling**: the law with an independent rank-two latent array. -/
noncomputable def rankTwoCoupling :
    Measure (RelStructure ternarySig (Vinfinite ternarySig) × Cube 3) :=
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
    (fun p : RelStructure ternarySig (Vinfinite ternarySig) × Cube 3 =>
        blockMap (S := ternarySig) A p.1) =ᵐ[rankTwoCoupling] fun _ => fun _ => false := by
  have hmp : MeasurePreserving (Prod.fst :
      RelStructure ternarySig (Vinfinite ternarySig) × Cube 3 → _) rankTwoCoupling ternaryLaw :=
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

theorem ternaryLaw_pairEvent {u v : ℕ} (huv : u ≠ v) : ternaryLaw (pairEvent u v) = 1 / 2 := by
  classical
  rw [ternaryLaw, Measure.map_apply measurable_arr (measurableSet_pairEvent u v)]
  have hpre : arr ⁻¹' pairEvent u v =
      {ω : Colours 3 | colour ω u = true ∧ colour ω v = !true} ∪
        {ω | colour ω u = false ∧ colour ω v = !false} := by
    ext ω
    simp only [Set.mem_preimage, mem_pairEvent_arr, Set.mem_union, Set.mem_setOf_eq, huv,
      ne_eq, not_false_eq_true, true_and, Bool.not_true, Bool.not_false]
    cases colour ω u <;> cases colour ω v <;> simp
  have hdisj : Disjoint {ω : Colours 3 | colour ω u = true ∧ colour ω v = !true}
      {ω | colour ω u = false ∧ colour ω v = !false} := by
    rw [Set.disjoint_left]
    rintro ω ⟨h1, -⟩ ⟨h2, -⟩
    rw [h1] at h2
    exact Bool.false_ne_true h2.symm
  have hm : ∀ b : Bool, MeasurableSet {ω : Colours 3 | colour ω u = b ∧ colour ω v = !b} :=
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

/-- The section of the rank-three local window 3 at a pair: the old coordinates from `o`, the fresh
pair coordinate from `t`. -/
noncomputable def sect (u v : ℕ) (o : Cube 3) (t : ℝ) :
    LocalLatentSpace (S := ternarySig) (pairSupport u v) 3 :=
  fun B => if h : B.1.1.card < 2 then o ⟨B.1.1, h⟩ else t

theorem measurable_sect_uncurry (u v : ℕ) :
    Measurable fun p : Cube 3 × ℝ => sect u v p.1 p.2 := by
  refine measurable_pi_lambda _ fun B => ?_
  by_cases h : B.1.1.card < 2
  · simp only [sect, dif_pos h]; exact (measurable_pi_apply _).comp measurable_fst
  · simp only [sect, dif_neg h]; exact measurable_snd

/-- The local window 3 at a pair, read on the successor split of the cube. -/
theorem localLatents_succEquiv_symm {u v : ℕ} (huv : u ≠ v) (o : Cube 3)
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

theorem rankLatentProjection_succEquiv_symm (o : Cube 3) (x : RankSupport ternarySig 2 → ℝ) :
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
      (fun o : Cube 3 => uniform01 {t | sect u v o t ∈ U}) =ᵐ[rankLatentSource ternarySig 2]
        fun _ => 1 / 2 := by
    intro u v huv U hU hae
    have hsectm : MeasurableSet {p : Cube 3 × ℝ | sect u v p.1 p.2 ∈ U} :=
      measurable_sect_uncurry u v hU
    have hφ : Measurable fun o : Cube 3 => uniform01 {t | sect u v o t ∈ U} :=
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
  set tset : Cube 3 → RankSupport ternarySig 2 → Set ℝ := fun o p =>
    if p = pairIdx 0 1 (by decide) then {t | sect 0 1 o t ∈ U01}
    else if p = pairIdx 1 2 (by decide) then {t | sect 1 2 o t ∈ U12}
    else {t | sect 0 2 o t ∈ U02} with htset
  have hsec : ∀ o : Cube 3,
      Prod.mk o ⁻¹' ((rankLatentSpaceSuccEquiv 2).symm ⁻¹' (V01 ∩ V12 ∩ V02)) =
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
  have hsm : ∀ o : Cube 3, ∀ p ∈ ({pairIdx 0 1 (by decide), pairIdx 1 2 (by decide),
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
    have hae : (fun o : Cube 3 => iidUniformSource (RankSupport ternarySig 2)
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

/-! ### Admissibility: the independent coupling fails it, the coloured coupling satisfies it -/

/-- The three test sets, pairwise meeting in one vertex. -/
def triSets : Fin 3 → Finset (Σ _ : Unit, ℕ) :=
  ![{⟨(), 0⟩, ⟨(), 1⟩, ⟨(), 3⟩}, {⟨(), 1⟩, ⟨(), 2⟩, ⟨(), 4⟩}, {⟨(), 0⟩, ⟨(), 2⟩, ⟨(), 5⟩}]

theorem card_inter_triSets : ∀ i j : Fin 3, i ≠ j → (triSets i ∩ triSets j).card = 1 := by
  decide

theorem smallOverlap_triSets : SmallOverlap (S := ternarySig) 2 triSets := by
  intro i j hij B hBi hBj
  have h := Finset.card_le_card (Finset.subset_inter hBi hBj)
  rw [card_inter_triSets i j hij] at h
  omega

/-- The witnessing coordinate of each test set. -/
def triCoord : Fin 3 → RelCoord ternarySig (Vinfinite ternarySig) :=
  ![ternaryCoord 0 1 3, ternaryCoord 1 2 4, ternaryCoord 0 2 5]

theorem triCoord_support_subset : ∀ i, (triCoord i).support ⊆ triSets i := by
  intro i v hv
  rw [RelCoord.mem_support_iff] at hv
  obtain ⟨k, rfl⟩ := hv
  fin_cases i <;> fin_cases k <;> simp [triCoord, triSets, RelCoord.taggedValue]

/-- The witnessing coordinate as an induced index. -/
def triIdx (i : Fin 3) : InducedIndex (S := ternarySig) (triSets i) :=
  ⟨triCoord i, triCoord_support_subset i⟩

/-- Each witnessing coordinate reads a pair parity. -/
theorem arrOf_triCoord (d : ℕ → Bool) :
    (arrOf d (triCoord 0) = xor (d 0) (d 1)) ∧ (arrOf d (triCoord 1) = xor (d 1) (d 2)) ∧
      (arrOf d (triCoord 2) = xor (d 0) (d 2)) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [triCoord, arrOf_apply, Distinct]

/-- The event that the witnessing coordinate holds. -/
def triEvent (i : Fin 3) : Set (RelStructure ternarySig (Vinfinite ternarySig)) :=
  (fun X : RelStructure ternarySig (Vinfinite ternarySig) => X (triCoord i)) ⁻¹' {true}

theorem measurableSet_triEvent (i : Fin 3) : MeasurableSet (triEvent i) :=
  measurable_pi_apply _ (measurableSet_singleton true)

theorem ternaryLaw_triEvent (i : Fin 3) : ternaryLaw (triEvent i) = 1 / 2 := by
  rw [ternaryLaw, Measure.map_apply measurable_arr (measurableSet_triEvent i)]
  have key : ∀ a b : ℕ, a ≠ b →
      (∀ ω : Colours 3, arr ω (triCoord i) = xor (colour ω a) (colour ω b)) →
      (iidUniformSource (RankSupport ternarySig 1)) (arr ⁻¹' triEvent i) = 1 / 2 := by
    intro a b hab hx
    have : arr ⁻¹' triEvent i = arr ⁻¹' pairEvent a b := by
      ext ω
      simp only [Set.mem_preimage, triEvent, Set.mem_singleton_iff, mem_pairEvent_arr, hx, hab,
        ne_eq, not_false_eq_true, true_and]
    rw [this, ← Measure.map_apply measurable_arr (measurableSet_pairEvent a b), ← ternaryLaw,
      ternaryLaw_pairEvent hab]
  fin_cases i
  · exact key 0 1 (by decide) fun ω => (arrOf_triCoord (colour ω)).1
  · exact key 1 2 (by decide) fun ω => (arrOf_triCoord (colour ω)).2.1
  · exact key 0 2 (by decide) fun ω => (arrOf_triCoord (colour ω)).2.2

theorem ternaryLaw_triEvent_inter : ternaryLaw (⋂ i, triEvent i) = 0 := by
  rw [ternaryLaw, Measure.map_apply measurable_arr (MeasurableSet.iInter measurableSet_triEvent)]
  have : arr ⁻¹' (⋂ i, triEvent i) = ∅ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iInter, triEvent, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨h0, h1, h2⟩ := arrOf_triCoord (colour ω)
    by_contra h
    push Not at h
    have e0 := h 0; have e1 := h 1; have e2 := h 2
    rw [arr, h0] at e0; rw [arr, h1] at e1; rw [arr, h2] at e2
    revert e0 e1 e2
    cases colour ω 0 <;> cases colour ω 1 <;> cases colour ω 2 <;> simp
  rw [this, measure_empty]

/-- The witnessing event on the induced structure. -/
def triSet (i : Fin 3) : Set (InducedSpace (S := ternarySig) (triSets i)) :=
  (fun x : InducedSpace (S := ternarySig) (triSets i) => x (triIdx i)) ⁻¹' {true}

theorem measurableSet_triSet (i : Fin 3) : MeasurableSet (triSet i) :=
  (measurable_pi_apply (triIdx i)) MeasurableSet.of_discrete

/-- **The independent coupling is not admissible**: three induced structures with pairwise
single-vertex overlaps read three parities of a triangle. -/
theorem not_admissible_rankTwoRep : ¬ rankTwoRep.Admissible := by
  intro h
  have hind : IndepFun (Prod.fst : RelStructure ternarySig (Vinfinite ternarySig) × Cube 3 → _)
      Prod.snd rankTwoCoupling := by
    refine (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
      measurable_snd.aemeasurable).mpr ?_
    rw [show (fun p : RelStructure ternarySig (Vinfinite ternarySig) × Cube 3 => (p.1, p.2)) = id
      from rfl, Measure.map_id, rankTwoCoupling_map_fst, rankTwoCoupling_map_snd]
    rfl
  have h' := (rankTwoRep.admissible_iff_iIndepFun_of_indep hind).mp h 3 triSets
    smallOverlap_triSets
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h'
  have key := h' Finset.univ (sets := triSet) (fun i _ => measurableSet_triSet i)
  have hpre : ∀ i, (inducedMap (triSets i) ∘
      (Prod.fst : RelStructure ternarySig (Vinfinite ternarySig) × Cube 3 → _)) ⁻¹' triSet i =
      Prod.fst ⁻¹' triEvent i := fun i => rfl
  simp only [hpre, Finset.mem_univ, Set.iInter_true] at key
  have hP : rankTwoRep.P = rankTwoCoupling := rfl
  have hfst : ∀ i, rankTwoCoupling (Prod.fst ⁻¹' triEvent i) = 1 / 2 := fun i => by
    rw [← Measure.map_apply measurable_fst (measurableSet_triEvent i), rankTwoCoupling_map_fst,
      ternaryLaw_triEvent]
  rw [hP, ← Set.preimage_iInter, ← Measure.map_apply measurable_fst
    (MeasurableSet.iInter measurableSet_triEvent), rankTwoCoupling_map_fst,
    ternaryLaw_triEvent_inter, Fin.prod_univ_three, hfst, hfst, hfst] at key
  norm_num at key

/-! ### The coloured coupling -/

/-- **The coloured coupling**: the singleton latents carry the colours. -/
noncomputable def colourCoupling :
    Measure (RelStructure ternarySig (Vinfinite ternarySig) × Cube 3) :=
  (rankLatentSource ternarySig 2).map fun ω => (arr (freshLayer ω), ω)

theorem measurable_colourMap : Measurable fun ω : Cube 3 => (arr (freshLayer ω), ω) :=
  (measurable_arr.comp measurable_freshLayer).prodMk measurable_id

instance : IsProbabilityMeasure colourCoupling := by
  rw [colourCoupling]
  exact Measure.isProbabilityMeasure_map measurable_colourMap.aemeasurable

@[simp] theorem colourCoupling_map_fst : colourCoupling.map Prod.fst = ternaryLaw := by
  rw [colourCoupling, Measure.map_map measurable_fst measurable_colourMap,
    show (Prod.fst ∘ fun ω : Cube 3 => (arr (freshLayer ω), ω)) = arr ∘ freshLayer from rfl]
  exact ternaryLaw_eq_map_cube.symm

@[simp] theorem colourCoupling_map_snd :
    colourCoupling.map Prod.snd = rankLatentSource ternarySig 2 := by
  rw [colourCoupling, Measure.map_map measurable_snd measurable_colourMap,
    show (Prod.snd ∘ fun ω : Cube 3 => (arr (freshLayer ω), ω)) = id from rfl, Measure.map_id]

theorem colourCoupling_invariant (σ : FinSuppPerm ternarySig) :
    colourCoupling.map (Prod.map (RelStructure.relabel σ.1) (⇑(rankLatentRelabel σ 2))) =
      colourCoupling := by
  rw [colourCoupling,
    Measure.map_map ((measurable_relabel σ.1).prodMap (rankLatentRelabel σ 2).measurable)
      measurable_colourMap,
    show (Prod.map (RelStructure.relabel σ.1) (⇑(rankLatentRelabel σ 2)) ∘
        fun ω : Cube 3 => (arr (freshLayer ω), ω)) =
      (fun ω : Cube 3 => (arr (freshLayer ω), ω)) ∘ (⇑(rankLatentRelabel σ 2)) from by
      funext ω
      show Prod.map (RelStructure.relabel σ.1) (rankLatentRelabel σ 2) (arr (freshLayer ω), ω) =
        (arr (freshLayer (rankLatentRelabel σ 2 ω)), rankLatentRelabel σ 2 ω)
      exact Prod.ext (arr_freshLayer_rankLatentRelabel σ ω).symm rfl,
    ← Measure.map_map measurable_colourMap (rankLatentRelabel σ 2).measurable,
    rankLatentSource_map_rankLatentRelabel]

open scoped Classical in
theorem ae_blockMap_colourCoupling {A : Finset (Σ _ : Unit, ℕ)} (hA : A.card < 3) :
    (fun p : RelStructure ternarySig (Vinfinite ternarySig) × Cube 3 =>
        blockMap (S := ternarySig) A p.1) =ᵐ[colourCoupling] fun _ => fun _ => false := by
  have hmp : MeasurePreserving (Prod.fst :
      RelStructure ternarySig (Vinfinite ternarySig) × Cube 3 → _) colourCoupling ternaryLaw :=
    ⟨measurable_fst, colourCoupling_map_fst⟩
  exact hmp.quasiMeasurePreserving.ae (ae_blockMap_of_card_lt_three hA)

open scoped Classical in
/-- **The coloured rank-two representation.** -/
noncomputable def colourRep : ternaryExchangeable.RankRepresentation 2 where
  P := colourCoupling
  isProbabilityMeasure_P := inferInstance
  map_fst := colourCoupling_map_fst
  map_snd := colourCoupling_map_snd
  invariant := colourCoupling_invariant
  lower_recovers := fun A hA =>
    ⟨fun _ => fun _ => false, measurable_const, ae_blockMap_colourCoupling (by omega)⟩
  fixing_complete := fun _ _ E hE =>
    ⟨(arr ∘ freshLayer) ⁻¹' E,
      (measurable_arr.comp measurable_freshLayer) (RelStructure.fixingAlgebra_le _ E hE),
      snd_preimage_ae_eq_fst_preimage_map_graph (measurable_arr.comp measurable_freshLayer)
        (RelStructure.fixingAlgebra_le _ E hE)⟩
  screening := fun A hA =>
    CondIndepFun.congr (condIndepFun_const_left (fun _ => false) _) measurable_const
      (measurable_restObservation 2 _)
      ((measurable_blockMap (S := ternarySig) _).comp measurable_fst)
      (measurable_restObservation 2 _) (ae_blockMap_colourCoupling (by omega)).symm
      Filter.EventuallyEq.rfl

/-- **The coloured coupling is admissible**: the structure is a function of its latents. -/
theorem admissible_colourRep : colourRep.Admissible := by
  refine colourRep.admissible_of_ae_eq_snd (measurable_arr.comp measurable_freshLayer) ?_
  show (fun p : RelStructure ternarySig (Vinfinite ternarySig) × Cube 3 => p.1)
    =ᵐ[colourCoupling] fun p => (arr ∘ freshLayer) p.2
  rw [colourCoupling]
  exact (ae_map_iff measurable_colourMap.aemeasurable (measurableSet_eq_fun measurable_fst
    ((measurable_arr.comp measurable_freshLayer).comp measurable_snd))).mpr
    (Filter.Eventually.of_forall fun _ => rfl)

end TernaryParityRegression

end RelSignature
