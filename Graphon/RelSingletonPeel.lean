/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelFixingCondIndep
import Graphon.RelRankRepresentation

/-!
# The singleton peel (R4 converse piece 3, #107)

Mutual conditional independence at rank one, for **any** vertex-indexed family whose members are
measurable for their own singleton fixing algebra.

The argument never mentions a coherent basis, a factor map, or any particular reading of the
structure. It depends on one thing only: distinct singletons are disjoint, so the two-set theorem
`InfiniteRelExchangeableLaw.condIndep_fixingAlgebra` conditions on
`fixingAlgebra ∅ = invariantAlgebra` at every stage of the peel, and the conditioning algebra
never moves.

## Why this is the right level of generality

Both consumers are instances: the coherent-basis exact layers `exactMap {v}`, and the raw
relation blocks `blockMap {v}`. Neither is more fundamental, and phrasing the peel against either
would force the other to be obtained by a transfer lemma that does not exist. The hypothesis
`Measurable[fixingAlgebra {v}] (Y v)` is exactly what the argument consumes.

This module also carries the raw-block instance, so that `Graphon.RelRankRepresentation` stays
interface-only: the specification must not depend on the conditional-independence proof layer.

## Where it stops

Above rank one the peel fails, and not for a technical reason. Distinct supports of equal rank
can meet — `card_inter_lt_of_ne` gives only that they meet in *strictly lower* rank — so a stage
of the peel would condition on `fixingAlgebra` of a nonempty intersection, a strictly larger
algebra. Conditional independence is not preserved under enlarging the conditioning, so the
stages no longer compose.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

open scoped Classical in
/-- **The block at `A` is measurable for `fixingAlgebra A`.** Every tagged value occurring in a
coordinate of support `A` lies in `A`, so a relabeling fixing `A` pointwise fixes the coordinate
itself — no null sets, and no reference to any basis. -/
theorem measurable_blockMap_fixingAlgebra [Countable S.Rel]
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measurable[RelStructure.fixingAlgebra A] (blockMap A) := by
  classical
  have key : ∀ cc : RelCoord S (Vinfinite S), cc.support = A →
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
      have hv : cc.taggedValue i ∈ A := by
        rw [← hcc]
        exact (RelCoord.mem_support_iff cc _).mpr ⟨i, rfl⟩
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
  simp [blockMap, blockMapOver]

namespace InfiniteRelExchangeableLaw

universe u

variable {S : RelSignature.{u}}

open scoped Classical in
/-- **The singleton peel.** A vertex-indexed family, each member measurable for the fixing algebra
of its own vertex, is **mutually** conditionally independent given the invariant σ-algebra — for
an arbitrary exchangeable law, with no dissociation and no `NoNullary`.

Stated over the whole vertex index rather than a fixed finite family: `iCondIndepFun` already
quantifies over finite subfamilies. -/
theorem iCondIndepFun_of_fixingAlgebra_singleton [Countable S.Rel]
    (M : InfiniteRelExchangeableLaw S) {β : (Σ s : S.Srt, Vinfinite S s) → Type*}
    [∀ v, MeasurableSpace (β v)] {Y : ∀ v, RelStructure S (Vinfinite S) → β v}
    (hY : ∀ v, Measurable[RelStructure.fixingAlgebra {v}] (Y v)) :
    iCondIndepFun RelStructure.invariantAlgebra (RelStructure.invariantAlgebra_le (S := S)) Y
      (M.law : Measure (RelStructure S (Vinfinite S))) := by
  classical
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul _ _
    fun v => (hY v).mono (RelStructure.fixingAlgebra_le _) le_rfl]
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
      -- the accumulated event is measurable for the fixing algebra of the accumulated support
      have hE : MeasurableSet[RelStructure.fixingAlgebra s]
          (⋂ i ∈ s, Y i ⁻¹' sets i) := by
        refine Finset.measurableSet_biInter s fun i hi => ?_
        exact RelStructure.fixingAlgebra_mono (Finset.singleton_subset_iff.mpr hi) _
          (hY i (hsets i (Finset.mem_insert_of_mem hi)))
      have hF : MeasurableSet[RelStructure.fixingAlgebra
          ({v} : Finset (Σ s : S.Srt, Vinfinite S s))] (Y v ⁻¹' sets v) :=
        hY v (hsets v (Finset.mem_insert_self v s))
      -- the peeled singleton is disjoint from the accumulated support
      have hinter : ({v} : Finset (Σ s : S.Srt, Vinfinite S s)) ∩ s = ∅ := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
        rintro rfl
        exact hvs
      have hci := M.condIndep_fixingAlgebra ({v} : Finset (Σ s : S.Srt, Vinfinite S s)) s
      rw [condIndep_iff _ _ _ _
        (RelStructure.fixingAlgebra_le ({v} : Finset (Σ s : S.Srt, Vinfinite S s)))
        (RelStructure.fixingAlgebra_le s)] at hci
      have key := hci _ _ hF hE
      rw [hinter, RelStructure.fixingAlgebra_empty] at key
      rw [Finset.set_biInter_insert, Finset.prod_insert hvs]
      exact key.trans (Filter.EventuallyEq.mul (Filter.EventuallyEq.refl _ _) ihs)

open scoped Classical in
/-- **Mutual conditional independence of the raw singleton blocks** given the invariant
σ-algebra, for an arbitrary exchangeable law. An instance of the peel above, phrased entirely in
raw relation coordinates — no coherent basis appears. -/
theorem iCondIndepFun_blockMap_singleton [Countable S.Rel]
    (M : InfiniteRelExchangeableLaw S) :
    iCondIndepFun RelStructure.invariantAlgebra (RelStructure.invariantAlgebra_le (S := S))
      (fun v : Σ s : S.Srt, Vinfinite S s => blockMap ({v} : Finset (Σ s : S.Srt, Vinfinite S s)))
      (M.law : Measure (RelStructure S (Vinfinite S))) :=
  M.iCondIndepFun_of_fixingAlgebra_singleton fun _ => measurable_blockMap_fixingAlgebra _

end InfiniteRelExchangeableLaw

end RelSignature
