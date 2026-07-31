/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelFixingCondIndep
import Graphon.RelFactorLaws

/-!
# The rank-one mutual conditional independence (R4 converse piece 3, #107)

The rank-one instance of the target: the exact-anchor layers at the *singletons* are **mutually**
conditionally independent given the invariant σ-algebra,

`iCondIndepFun (fun v => exactMap {v}) invariantAlgebra M.law`.

At rank one the conditioning factor is `lowerRankAlgebra 1 = invariantAlgebra`, so this is a
multi-sorted de Finetti statement about an arbitrary exchangeable law — no dissociation, no
`NoNullary`.

## Why no de Finetti machinery is needed

Mutual conditional independence does not follow from pairwise conditional independence in
general, and this is exactly the higher-rank obstruction recorded in `Graphon.RelRankAlgebra`.
At rank one it can nevertheless be obtained from the *two-set* theorem
`InfiniteRelExchangeableLaw.condIndep_fixingAlgebra` by peeling one vertex at a time:

* peel a vertex `v` off the finite family;
* bundle the remaining events into a single event measurable for `fixingAlgebra s`, where `s` is
  the set of remaining vertices — legitimate because `fixingAlgebra` is monotone;
* `{v} ∩ s = ∅`, so the two-set theorem conditions on `fixingAlgebra ∅ = invariantAlgebra`,
  which is the conditioning algebra we want and does not change as the peel proceeds;
* multiply by the induction hypothesis.

The step that fails at higher rank is the third: for supports of rank `n > 1` the peeled support
meets the accumulated union in something of *positive* rank, so the two-set theorem conditions
on a different — and larger — algebra at each stage, and conditional independence is not
preserved under enlarging the conditioning. Here the remaining union stays disjoint from the
peeled singleton, so the conditioning algebra is the same throughout and the products compose.

Consequently the rank-one case needs no de Finetti representation, no mixing measure, and no
identification of a mixing measure with an invariant conditional distribution.
-/

open MeasureTheory MeasurableSpace ProbabilityTheory

namespace RelSignature

namespace CoherentBasis

universe u

variable {S : RelSignature.{u}} {M : InfiniteRelExchangeableLaw S} (B : CoherentBasis M)

open scoped Classical in
/-- The exact-anchor layer at `A` is measurable for `fixingAlgebra A`, not merely for the
ambient algebra — the sharpening of `measurable_exactMap` that the peel needs. -/
theorem measurable_exactMap_fixingAlgebra (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measurable[RelStructure.fixingAlgebra A] (B.exactMap A) :=
  ((B.factorSpaceProdEquiv A).measurable.comp (B.measurable_factorMap A)).snd

open scoped Classical in
/-- **Mutual conditional independence of the singleton exact layers given the invariant
σ-algebra** — the rank-one instance of the rankwise theorem, for an arbitrary exchangeable law.

Stated over the whole vertex index rather than for a fixed finite family: `iCondIndepFun` already
quantifies over finite subfamilies, so finite families are a corollary. -/
theorem iCondIndepFun_exactMap_singleton [Fintype S.Srt] [Countable S.Rel] :
    iCondIndepFun RelStructure.invariantAlgebra (RelStructure.invariantAlgebra_le (S := S))
      (fun v : Σ s : S.Srt, Vinfinite S s => B.exactMap {v})
      (M.law : Measure (RelStructure S (Vinfinite S))) := by
  classical
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul _ _
    fun v => B.measurable_exactMap ({v} : Finset (Σ s : S.Srt, Vinfinite S s))]
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
          (⋂ i ∈ s, B.exactMap ({i} : Finset (Σ s : S.Srt, Vinfinite S s)) ⁻¹' sets i) := by
        refine Finset.measurableSet_biInter s fun i hi => ?_
        exact RelStructure.fixingAlgebra_mono (Finset.singleton_subset_iff.mpr hi) _
          (B.measurable_exactMap_fixingAlgebra _ (hsets i (Finset.mem_insert_of_mem hi)))
      have hF : MeasurableSet[RelStructure.fixingAlgebra
          ({v} : Finset (Σ s : S.Srt, Vinfinite S s))]
          (B.exactMap ({v} : Finset (Σ s : S.Srt, Vinfinite S s)) ⁻¹' sets v) :=
        B.measurable_exactMap_fixingAlgebra _ (hsets v (Finset.mem_insert_self v s))
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

end CoherentBasis

end RelSignature
