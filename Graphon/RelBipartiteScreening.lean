/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelAdmissibleRegressions
import Graphon.RelColourLaw
import Graphon.ForMathlib.CondExpRepresentable

/-!
# The bipartite screening test (R4 converse, #107)

A negative test for the mechanism "randomize the existing fixing factor at each overlap". The
bipartite rank-one representation is admissible. Take the three pair sets `{0,1}`, `{1,2}`,
`{0,2}`, pairwise meeting in one vertex — the overlap case that admissibility at rank one does
not cover — and condition on the old array joined with the three singleton fixing algebras.
The singleton fixing algebras are trivial modulo the bipartite law (`fixing_trivial_bipartite`,
by the relative-colouring argument of `Graphon.RelColourLaw`), so that conditioning is, modulo
the law, conditioning on the old array alone, and the three edge parities of a triangle are not
mutually independent: `not_iCondIndepFun_singletonFixing`.

The same input has an exact admissible successor (`bipartiteSuccessor`, `admissible_rankTwoRep`),
recorded alongside in `screening_fails_but_successor_exists`. The successor's vertex colours are
not functions of the original structure's singleton fixing factors — flipping every colour
preserves the structure — so the construction must supply additional latent information beyond
the existing fixing factors, even when those are trivial.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RelSignature

namespace BipartiteRegression

open InfiniteRelExchangeableLaw ColourLaw

/-- The parity structure map. -/
def parityOf (d : ℕ → Bool) : RelStructure digraphSig (Vinfinite digraphSig) :=
  fun c => xor (d (c.2 0)) (d (c.2 1))

theorem measurable_parityOf : Measurable parityOf :=
  measurable_pi_lambda _ fun c =>
    Measurable.comp (g := fun p : Bool × Bool => xor p.1 p.2)
      (f := fun d : ℕ → Bool => (d (c.2 0), d (c.2 1))) Measurable.of_discrete
      ((measurable_pi_apply _).prodMk (measurable_pi_apply _))

theorem parityOf_comp (σ : Equiv.Perm ℕ) (d : ℕ → Bool) :
    parityOf (d ∘ σ) = RelStructure.relabel (fun _ : Unit => σ) (parityOf d) := rfl

theorem parityOf_xor_const (d : ℕ → Bool) (b : Bool) :
    parityOf (fun v => xor (d v) b) = parityOf d := by
  funext c
  simp only [parityOf]
  cases d (c.2 0) <;> cases d (c.2 1) <;> cases b <;> rfl

/-- The bipartite law is the colour law of the parity map. -/
theorem bipartiteLaw_eq_colourLaw : bipartiteLaw = colourLaw (k := 2) parityOf := rfl

/-- **Singleton and empty fixing events are trivial under the bipartite law.** -/
theorem fixing_trivial_bipartite {A : Finset (Σ _ : Unit, ℕ)} (hA : A.card < 2)
    {E : Set (RelStructure digraphSig (Vinfinite digraphSig))}
    (hE : MeasurableSet[RelStructure.fixingAlgebra A] E) :
    bipartiteLaw E = 0 ∨ bipartiteLaw E = 1 := by
  rw [bipartiteLaw_eq_colourLaw]
  exact ColourLaw.fixing_trivial_of_card_lt_two measurable_parityOf parityOf_comp
    parityOf_xor_const hA hE

/-! ### The conditioning and the three pair sets -/

/-- The old array joined with the singleton fixing algebras at `0`, `1`, `2`. -/
@[implicit_reducible]
noncomputable def singletonFixingCond :
    MeasurableSpace (RelStructure digraphSig (Vinfinite digraphSig) ×
      RankLatentSpace digraphSig 1) :=
  MeasurableSpace.comap Prod.snd inferInstance ⊔
    ⨆ v ∈ ({0, 1, 2} : Finset ℕ), MeasurableSpace.comap Prod.fst
      (RelStructure.fixingAlgebra ({⟨(), v⟩} : Finset (Σ _ : Unit, ℕ)))

theorem singletonFixingCond_le : singletonFixingCond ≤
    (inferInstance : MeasurableSpace (RelStructure digraphSig (Vinfinite digraphSig) ×
      RankLatentSpace digraphSig 1)) := by
  refine sup_le measurable_snd.comap_le (iSup_le fun v => iSup_le fun _ => ?_)
  exact (MeasurableSpace.comap_mono (RelStructure.fixingAlgebra_le _)).trans
    measurable_fst.comap_le

/-- **Every event of the conditioning is, modulo the coupling, an event of the old array**: the
singleton fixing events are trivial. -/
theorem exists_comap_snd_ae_eq_of_singletonFixingCond
    {s : Set (RelStructure digraphSig (Vinfinite digraphSig) × RankLatentSpace digraphSig 1)}
    (hs : MeasurableSet[singletonFixingCond] s) :
    ∃ t, MeasurableSet[MeasurableSpace.comap
      (Prod.snd : RelStructure digraphSig (Vinfinite digraphSig) ×
        RankLatentSpace digraphSig 1 → _) inferInstance] t ∧ s =ᵐ[rankOneCoupling] t := by
  refine (sup_le (le_eventuallyMeasurableSpace) (iSup_le fun v => iSup_le fun _ => ?_)) s hs
  rintro _ ⟨E, hE, rfl⟩
  have hfst : rankOneCoupling (Prod.fst ⁻¹' E) = bipartiteLaw E := by
    rw [← rankOneCoupling_map_fst, Measure.map_apply measurable_fst hE.1]
  rcases fixing_trivial_bipartite (by simp) hE with h0 | h1
  · exact ⟨∅, @MeasurableSet.empty _ (MeasurableSpace.comap Prod.snd inferInstance),
      ae_eq_empty.mpr (hfst.trans h0)⟩
  · exact ⟨Set.univ, @MeasurableSet.univ _ (MeasurableSpace.comap Prod.snd inferInstance),
      ae_eq_univ.mpr
      ((prob_compl_eq_zero_iff (measurable_fst hE.1)).mpr (hfst.trans h1))⟩

/-- The three pair sets, pairwise meeting in one vertex. -/
def pairSets : Fin 3 → Finset (Σ _ : Unit, ℕ) :=
  ![{⟨(), 0⟩, ⟨(), 1⟩}, {⟨(), 1⟩, ⟨(), 2⟩}, {⟨(), 0⟩, ⟨(), 2⟩}]

/-- The witnessing edge coordinate of each pair set. -/
def pairCoord : Fin 3 → RelCoord digraphSig (Vinfinite digraphSig) :=
  ![digraphCoord 0 1, digraphCoord 1 2, digraphCoord 0 2]

theorem pairCoord_support_subset : ∀ i, (pairCoord i).support ⊆ pairSets i := by
  intro i v hv
  rw [RelCoord.mem_support_iff] at hv
  obtain ⟨k, rfl⟩ := hv
  fin_cases i <;> fin_cases k <;> simp [pairCoord, pairSets, RelCoord.taggedValue]

/-- The witnessing coordinate as an induced index. -/
def pairIdx (i : Fin 3) : InducedIndex (S := digraphSig) (pairSets i) :=
  ⟨pairCoord i, pairCoord_support_subset i⟩

/-- The edge event of a pair set. -/
def pairEvent (i : Fin 3) : Set (RelStructure digraphSig (Vinfinite digraphSig)) :=
  (fun X : RelStructure digraphSig (Vinfinite digraphSig) => X (pairCoord i)) ⁻¹' {true}

theorem measurableSet_pairEvent (i : Fin 3) : MeasurableSet (pairEvent i) :=
  measurable_pi_apply _ (measurableSet_singleton true)

/-- The witnessing event on the induced structure. -/
def pairSet (i : Fin 3) : Set (InducedSpace (S := digraphSig) (pairSets i)) :=
  (fun x : InducedSpace (S := digraphSig) (pairSets i) => x (pairIdx i)) ⁻¹' {true}

theorem measurableSet_pairSet (i : Fin 3) : MeasurableSet (pairSet i) :=
  (measurable_pi_apply (pairIdx i)) MeasurableSet.of_discrete

theorem arr_pairCoord (ω : Colours) :
    (arr ω (pairCoord 0) = xor (colour ω 0) (colour ω 1)) ∧
      (arr ω (pairCoord 1) = xor (colour ω 1) (colour ω 2)) ∧
      (arr ω (pairCoord 2) = xor (colour ω 0) (colour ω 2)) :=
  ⟨rfl, rfl, rfl⟩

theorem uniform01_Iic_half_compl' : uniform01 (Set.Iic (1 / 2 : ℝ))ᶜ = 1 / 2 := by
  rw [prob_compl_eq_one_sub measurableSet_Iic, ColourLaw.uniform01_Iic_half, one_div,
    ENNReal.one_sub_inv_two]

/-- Each edge event has probability one half. -/
theorem bipartiteLaw_pairEvent (i : Fin 3) : bipartiteLaw (pairEvent i) = 1 / 2 := by
  rw [bipartiteLaw, Measure.map_apply measurable_arr (measurableSet_pairEvent i)]
  have key : ∀ a b : ℕ, a ≠ b →
      (∀ ω : Colours, arr ω (pairCoord i) = xor (colour ω a) (colour ω b)) →
      (iidUniformSource (RankSupport digraphSig 1)) (arr ⁻¹' pairEvent i) = 1 / 2 := by
    intro a b hab hx
    have hpre : arr ⁻¹' pairEvent i =
        {ω : Colours | colour ω a = true ∧ colour ω b = !true} ∪
          {ω | colour ω a = false ∧ colour ω b = !false} := by
      ext ω
      simp only [Set.mem_preimage, pairEvent, Set.mem_singleton_iff, hx, Set.mem_union,
        Set.mem_setOf_eq, Bool.not_true, Bool.not_false]
      cases colour ω a <;> cases colour ω b <;> simp
    have hdisj : Disjoint {ω : Colours | colour ω a = true ∧ colour ω b = !true}
        {ω | colour ω a = false ∧ colour ω b = !false} := by
      rw [Set.disjoint_left]
      rintro ω ⟨h1, -⟩ ⟨h2, -⟩
      rw [h1] at h2
      exact Bool.false_ne_true h2.symm
    have hm : ∀ b' : Bool, MeasurableSet {ω : Colours | colour ω a = b' ∧ colour ω b = !b'} :=
      fun b' => ((measurable_colour a) (measurableSet_singleton b')).inter
        ((measurable_colour b) (measurableSet_singleton (!b')))
    rw [hpre, measure_union hdisj (hm false)]
    have h1 := ColourLaw.source_colour_pair (k := 2) hab true
    have h2 := ColourLaw.source_colour_pair (k := 2) hab false
    rw [show ({ω : Colours | colour ω a = true ∧ colour ω b = !true}) =
      {ω : ColourLaw.Colours 2 | ColourLaw.colour ω a = true ∧ ColourLaw.colour ω b = !true}
      from rfl, show ({ω : Colours | colour ω a = false ∧ colour ω b = !false}) =
      {ω : ColourLaw.Colours 2 | ColourLaw.colour ω a = false ∧ ColourLaw.colour ω b = !false}
      from rfl, h1, h2, ← two_mul, one_div, one_div, show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
      ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
      ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
  fin_cases i
  · exact key 0 1 (by decide) fun ω => (arr_pairCoord ω).1
  · exact key 1 2 (by decide) fun ω => (arr_pairCoord ω).2.1
  · exact key 0 2 (by decide) fun ω => (arr_pairCoord ω).2.2

/-- Three edge parities of a triangle cannot all hold. -/
theorem bipartiteLaw_pairEvent_inter : bipartiteLaw (⋂ i, pairEvent i) = 0 := by
  rw [bipartiteLaw, Measure.map_apply measurable_arr (MeasurableSet.iInter measurableSet_pairEvent)]
  have : arr ⁻¹' (⋂ i, pairEvent i) = ∅ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iInter, pairEvent, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨h0, h1, h2⟩ := arr_pairCoord ω
    by_contra h
    push Not at h
    have e0 := h 0; have e1 := h 1; have e2 := h 2
    rw [h0] at e0; rw [h1] at e1; rw [h2] at e2
    revert e0 e1 e2
    cases colour ω 0 <;> cases colour ω 1 <;> cases colour ω 2 <;> simp
  rw [this, measure_empty]

/-- **Screening by the existing singleton fixing factors fails**: conditional on the old array
joined with the three singleton fixing algebras, the induced structures on the three pair sets
are not mutually independent. -/
theorem not_iCondIndepFun_singletonFixing :
    ¬ iCondIndepFun singletonFixingCond singletonFixingCond_le
      (fun i => inducedMap (S := digraphSig) (pairSets i) ∘ Prod.fst) rankOneCoupling := by
  intro h
  have hind : IndepFun (Prod.fst : RelStructure digraphSig (Vinfinite digraphSig) ×
      RankLatentSpace digraphSig 1 → _) Prod.snd rankOneCoupling := by
    refine (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
      measurable_snd.aemeasurable).mpr ?_
    rw [show (fun p : RelStructure digraphSig (Vinfinite digraphSig) ×
      RankLatentSpace digraphSig 1 => (p.1, p.2)) = id from rfl, Measure.map_id,
      rankOneCoupling_map_fst, rankOneCoupling_map_snd]
    rfl
  -- descend the conditioning to the old array: the fixing events are trivial
  have h1 := (iCondIndepFun_congr_of_ae_representable (le_sup_left) singletonFixingCond_le
    (fun _ hs => exists_comap_snd_ae_eq_of_singletonFixingCond hs)
    (fun i => ((measurable_inducedMap (S := digraphSig) (pairSets i)).comp measurable_fst :
      Measurable (inducedMap (S := digraphSig) (pairSets i) ∘ (Prod.fst : RelStructure digraphSig
        (Vinfinite digraphSig) × RankLatentSpace digraphSig 1 → _))))).mp h
  have hP : rankOneRep.P = rankOneCoupling := rfl
  have h2 := (rankOneRep.iCondIndepFun_snd_iff_iIndepFun hind
    (fun i => measurable_inducedMap (S := digraphSig) (pairSets i))).mp h1
  rw [hP, iIndepFun_iff_measure_inter_preimage_eq_mul] at h2
  have key := h2 Finset.univ (sets := pairSet) (fun i _ => measurableSet_pairSet i)
  have hpre : ∀ i, (inducedMap (S := digraphSig) (pairSets i) ∘
      (Prod.fst : RelStructure digraphSig (Vinfinite digraphSig) ×
        RankLatentSpace digraphSig 1 → _)) ⁻¹' pairSet i = Prod.fst ⁻¹' pairEvent i :=
    fun i => rfl
  simp only [hpre, Finset.mem_univ, Set.iInter_true] at key
  have hfst : ∀ i, rankOneCoupling (Prod.fst ⁻¹' pairEvent i) = 1 / 2 := fun i => by
    rw [← Measure.map_apply measurable_fst (measurableSet_pairEvent i), rankOneCoupling_map_fst,
      bipartiteLaw_pairEvent]
  rw [← Set.preimage_iInter, ← Measure.map_apply measurable_fst
    (MeasurableSet.iInter measurableSet_pairEvent), rankOneCoupling_map_fst,
    bipartiteLaw_pairEvent_inter, Fin.prod_univ_three, hfst, hfst, hfst] at key
  norm_num at key

/-- **The distinction**: screening by the existing fixing factors fails, yet the same admissible
input has an exact successor whose output is admissible. -/
theorem screening_fails_but_successor_exists :
    (¬ iCondIndepFun singletonFixingCond singletonFixingCond_le
      (fun i => inducedMap (S := digraphSig) (pairSets i) ∘ Prod.fst) rankOneCoupling) ∧
    Nonempty (InfiniteRelExchangeableLaw.RankSuccessor rankOneRep) ∧ rankTwoRep.Admissible :=
  ⟨not_iCondIndepFun_singletonFixing, ⟨bipartiteSuccessor⟩, admissible_rankTwoRep⟩

end BipartiteRegression

end RelSignature
