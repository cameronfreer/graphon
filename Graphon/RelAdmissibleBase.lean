/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelAdmissible
import Graphon.RelRankOneRepresentation

/-!
# The admissible rank-one base (R4 converse, #107)

Every exchangeable law has an **admissible** rank-one representation, under ambient countability
only, with nullary relations and nondissociated laws allowed:
`exists_admissible_rankRepresentation_one`.

The proof has three parts:

* **Source-level mutuality for disjoint finite sets.** The singleton peel generalizes to the full
  induced structures on a family with small overlap at rank one, i.e. pairwise disjoint sets:
  each induced structure is measurable for the fixing algebra of its set, and at each insertion
  the target set and the union of the accumulated sets meet in the empty set, so every stage
  conditions on the same invariant σ-algebra. This is
  `iCondIndepFun_inducedMap_of_smallOverlap_one`.
* **The conditioning ladder** of `Graphon.RelRankOneScreening`, in its general form
  `CoherentBasis.iCondIndepFun_comap_snd_of_invariant`: eventwise representation by the rank-one
  factor, independent refinement through the canonical coupling's conditional-independence
  clause, and the factor's recovery from the latent.
* **Assembly** with the existing construction `rankOneRepOf`, whose coupling is the canonical
  rank-one latent coupling. No field is added and no arbitrary rank-one representation is
  assumed admissible.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

universe u

variable {S : RelSignature.{u}}

open scoped Classical in
/-- **The full induced structure on `A` is measurable for `fixingAlgebra A`**: every coordinate
inside `A` is fixed by a relabeling fixing `A` pointwise. -/
theorem measurable_inducedMap_fixingAlgebra [Countable S.Rel]
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measurable[RelStructure.fixingAlgebra A] (inducedMap (S := S) A) := by
  classical
  have key : ∀ cc : RelCoord S (Vinfinite S), cc.support ⊆ A →
      MeasurableSet[RelStructure.fixingAlgebra A]
        {X : RelStructure S (Vinfinite S) | X cc = true} := by
    intro cc hcc
    refine ⟨?_, fun σ hσ => ?_⟩
    · have hm : MeasurableSet
          ((fun X : RelStructure S (Vinfinite S) => X cc) ⁻¹' ({true} : Set Bool)) :=
        (measurable_pi_apply cc) (measurableSet_singleton true)
      exact hm
    have hfun : (fun i => (σ (S.argSort cc.1 i)) (cc.2 i)) = cc.2 := by
      funext i
      have hv : cc.taggedValue i ∈ A := hcc ((RelCoord.mem_support_iff cc _).mpr ⟨i, rfl⟩)
      exact hσ.2 _ hv
    have hcoord : RelCoord.map (fun s => ⇑(σ s)) cc = cc := by
      show (⟨cc.1, fun i => (σ (S.argSort cc.1 i)) (cc.2 i)⟩ : RelCoord S (Vinfinite S)) = cc
      rw [hfun]
    ext X
    show (RelStructure.relabel σ X) cc = true ↔ X cc = true
    rw [show (RelStructure.relabel σ X) cc = X (RelCoord.map (fun s => ⇑(σ s)) cc) from rfl,
      hcoord]
  letI : MeasurableSpace (RelStructure S (Vinfinite S)) := RelStructure.fixingAlgebra A
  refine measurable_pi_iff.mpr fun c => measurable_to_bool ?_
  convert key c.1 c.2 using 1
  ext X
  simp [inducedMap]

namespace InfiniteRelExchangeableLaw

open scoped Classical in
/-- Small overlap at rank one is pairwise disjointness. -/
theorem disjoint_of_smallOverlap_one {k : ℕ} {A : Fin k → Finset (Σ s : S.Srt, Vinfinite S s)}
    (hA : SmallOverlap 1 A) {i j : Fin k} (hij : i ≠ j) : A i ∩ A j = ∅ := by
  classical
  ext x
  simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
  intro hxi hxj
  have := hA i j hij {x} (Finset.singleton_subset_iff.mpr hxi) (Finset.singleton_subset_iff.mpr hxj)
  simp at this

open scoped Classical in
/-- **Source-level mutuality for disjoint finite sets.** The full induced structures on a family
with small overlap at rank one are mutually conditionally independent given the invariant
σ-algebra, for an arbitrary exchangeable law. At each insertion the target set and the union of
the accumulated sets meet in the empty set. -/
theorem iCondIndepFun_inducedMap_of_smallOverlap_one [Countable S.Rel]
    (M : InfiniteRelExchangeableLaw S) {k : ℕ} (A : Fin k → Finset (Σ s : S.Srt, Vinfinite S s))
    (hA : SmallOverlap 1 A) :
    iCondIndepFun RelStructure.invariantAlgebra (RelStructure.invariantAlgebra_le (S := S))
      (fun i => inducedMap (S := S) (A i)) (M.law : Measure (RelStructure S (Vinfinite S))) := by
  classical
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  have hY : ∀ i, Measurable[RelStructure.fixingAlgebra (A i)] (inducedMap (S := S) (A i)) :=
    fun i => measurable_inducedMap_fixingAlgebra (A i)
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul _ _
    fun i => (hY i).mono (RelStructure.fixingAlgebra_le _) le_rfl]
  intro T sets
  induction T using Finset.induction_on with
  | empty =>
      intro _
      simp only [Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ, Finset.prod_empty,
        Set.indicator_univ]
      rw [condExp_const (μ := (M.law : Measure (RelStructure S (Vinfinite S))))
        RelStructure.invariantAlgebra_le (1 : ℝ)]
      rfl
  | insert v s hvs ih =>
      intro hsets
      have ihs := ih fun i hi => hsets i (Finset.mem_insert_of_mem hi)
      -- the accumulated event is measurable for the fixing algebra of the accumulated union
      have hE : MeasurableSet[RelStructure.fixingAlgebra (s.biUnion A)]
          (⋂ i ∈ s, inducedMap (S := S) (A i) ⁻¹' sets i) := by
        refine Finset.measurableSet_biInter s fun i hi => ?_
        exact RelStructure.fixingAlgebra_mono (Finset.subset_biUnion_of_mem A hi) _
          (hY i (hsets i (Finset.mem_insert_of_mem hi)))
      have hF : MeasurableSet[RelStructure.fixingAlgebra (A v)]
          (inducedMap (S := S) (A v) ⁻¹' sets v) :=
        hY v (hsets v (Finset.mem_insert_self v s))
      -- the inserted set is disjoint from the accumulated union
      have hinter : A v ∩ s.biUnion A = ∅ := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.notMem_empty, iff_false, not_and,
          not_exists]
        intro hxv i hi hxi
        have hne : v ≠ i := fun h => hvs (h ▸ hi)
        have := disjoint_of_smallOverlap_one hA hne
        have hx : x ∈ A v ∩ A i := Finset.mem_inter.mpr ⟨hxv, hxi⟩
        rw [this] at hx
        exact Finset.notMem_empty x hx
      have hci := M.condIndep_fixingAlgebra (A v) (s.biUnion A)
      rw [condIndep_iff _ _ _ _ (RelStructure.fixingAlgebra_le (A v))
        (RelStructure.fixingAlgebra_le (s.biUnion A))] at hci
      have key := hci _ _ hF hE
      rw [hinter, RelStructure.fixingAlgebra_empty] at key
      rw [Finset.set_biInter_insert, Finset.prod_insert hvs]
      exact key.trans (Filter.EventuallyEq.mul (Filter.EventuallyEq.refl _ _) ihs)

end InfiniteRelExchangeableLaw

/-- **The admissible rank-one base**: every exchangeable law has an admissible rank-one
representation, the canonical construction `rankOneRepOf`. -/
theorem InfiniteRelExchangeableLaw.exists_admissible_rankRepresentation_one
    [Countable S.Srt] [Countable S.Rel] (M : InfiniteRelExchangeableLaw S) :
    ∃ C : M.RankRepresentation 1, C.Admissible := by
  classical
  obtain ⟨B⟩ := M.nonempty_coherentBasis
  obtain ⟨f, g, hg, hprob, hfst, hsnd, hinv, hres, hci⟩ := B.exists_rankOneLatentCoupling
  refine ⟨B.rankOneRepOf f g hg hprob hfst hsnd hinv hres (hci measurable_id),
    fun k A hA => ?_⟩
  haveI := hprob
  exact B.iCondIndepFun_comap_snd_of_invariant hfst hg hres (hci measurable_id)
    (fun i => measurable_inducedMap (A i))
    (M.iCondIndepFun_inducedMap_of_smallOverlap_one A hA)

end RelSignature
