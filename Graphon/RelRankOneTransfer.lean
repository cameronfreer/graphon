/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelLowerFactor
import Graphon.UniformFactorCoupling

/-!
# The rank-one transfer step, I(1) (R4 converse piece 3, #107)

The instantiation of `ProbabilityTheory.relativeFactorCoupling` at `q = lowerFactorMap 1`: the
base of the rank recursion, in which the rank-one factor of an exchangeable law is carried by a
single uniform latent that says nothing further about the structure.

## The rank-one factor is relabeling invariant, on the nose

`LowerIndex 1` consists of the indices anchored at a set of cardinality `< 1`, i.e. at `∅`, and a
basis event anchored at `∅` is measurable for `fixingAlgebra ∅ = invariantAlgebra` — so it is
literally invariant under every finitely supported sortwise relabeling, not merely invariant
modulo the law. Hence `lowerFactorMap 1 ∘ relabel σ = lowerFactorMap 1` as functions
(`lowerFactorMap_one_relabel`), and the equivariance square of `Graphon.RelLowerFactor` degenerates
at rank one: no transport of the factor space is needed, and the conditioning factor of the
coupling does not move with `σ`.

That is what makes the coupling itself relabeling invariant
(`map_prodMap_relabel_rankOneCoupling`): the relabeling acts inside the fibres of the factor, so
it preserves each disintegration fibre and never disturbs the outer integration. At higher rank
this fails — the factor map is only *equivariant*, not invariant — and the corresponding statement
will have to move the factor space by `lowerFactorSpaceEquiv` on the other side.

## What I(1) has to say, and what it must not leave out

`exists_rankOneUniformCoupling` bundles the six clauses. The marginals and the common-factor
identity are not by themselves the full statement: they say the latent *resolves* the factor, but
nothing about what else the latent might know. Without the conditional-independence clause the
latent could encode arbitrary further information about the part of the structure that rank one
leaves unresolved, which would make the recursion's next step unsound. The clause is stated in
its strongest form — conditional independence of the *whole* structure coordinate from the
latent — so the reading for any particular unresolved part follows by measurable composition;
`condIndepFun_comp_fst_snd_rankOne` records that transfer explicitly.

No σ-algebra equality between the latent and the factor is claimed. The latent may carry strictly
more than `lowerFactorMap 1` reads; conditional independence is exactly the statement that the
surplus is irrelevant to the structure.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

namespace CoherentBasis

universe u

variable {S : RelSignature.{u}} {M : InfiniteRelExchangeableLaw S} (B : CoherentBasis M)

/-! ### Rank one is invariant, not merely equivariant -/

/-- A rank-one basis index is anchored at the empty set. -/
theorem anchor_eq_empty_of_lowerIndex_one (i : B.LowerIndex 1) : B.anchor i.1 = ∅ :=
  Finset.card_eq_zero.mp (by have := i.2; omega)

open scoped Classical in
/-- **The rank-one factor map is relabeling invariant on the nose.** Its coordinates are basis
events anchored at `∅`, hence `invariantAlgebra`-measurable, hence literally fixed by every
finitely supported sortwise relabeling — no null sets and no transport of the factor space. -/
theorem lowerFactorMap_one_relabel (σ : FinSuppPerm S) :
    B.lowerFactorMap 1 ∘ RelStructure.relabel σ.1 = B.lowerFactorMap 1 := by
  classical
  funext X i
  have hmem := B.event_mem i.1
  rw [B.anchor_eq_empty_of_lowerIndex_one i, RelStructure.fixingAlgebra_empty] at hmem
  have hiff : (RelStructure.relabel σ.1 X ∈ B.event i.1) ↔ (X ∈ B.event i.1) :=
    Set.ext_iff.mp (hmem.2 σ.1 σ.2) X
  show decide (RelStructure.relabel σ.1 X ∈ B.event i.1) = decide (X ∈ B.event i.1)
  exact decide_eq_decide.mpr hiff

/-! ### The rank-one coupling -/

variable [Countable S.Rel]

/-- **Relabeling compatibility of the rank-one coupling.** Every finitely supported sortwise
relabeling of the structure coordinate preserves the coupling. It fixes the rank-one factor
exactly, so it acts within the fibres of the disintegration. -/
theorem map_prodMap_relabel_rankOneCoupling (f : ℝ → B.LowerFactorSpace 1) (σ : FinSuppPerm S) :
    (relativeFactorCoupling (M.law : Measure (RelStructure S (Vinfinite S))) uniform01
        (B.lowerFactorMap 1) f).map (Prod.map (RelStructure.relabel σ.1) id) =
      relativeFactorCoupling (M.law : Measure (RelStructure S (Vinfinite S))) uniform01
        (B.lowerFactorMap 1) f :=
  map_prodMap_relativeFactorCoupling (B.measurable_lowerFactorMap' 1)
    (M.measurePreserving_relabel σ.1) (B.lowerFactorMap_one_relabel σ)

/-- **I(1)**: the rank-one factor of an arbitrary exchangeable law is carried by a uniform latent
that says nothing further about the structure.

The six clauses: `f` is measurable; the coupling is a probability measure; its structure marginal
is the original law; its latent marginal is uniform; the latent **resolves** the rank-one factor,
`lowerFactorMap 1 X = f ξ` almost surely; and the structure and the latent are **conditionally
independent given that factor**.

The last clause is the one that cannot be dropped. The marginals and the resolution identity
together still permit a latent that encodes information about everything rank one does not
resolve; conditional independence is what forbids it, and it is stated over the whole structure
coordinate so that the reading for any particular unresolved part follows by composition
(`condIndepFun_comp_fst_snd_rankOne`).

Relabeling compatibility holds for this coupling as for any other and is recorded separately in
`map_prodMap_relabel_rankOneCoupling`. -/
theorem exists_rankOneUniformCoupling :
    ∃ f : ℝ → B.LowerFactorSpace 1, Measurable f ∧
      IsProbabilityMeasure (relativeFactorCoupling
        (M.law : Measure (RelStructure S (Vinfinite S))) uniform01 (B.lowerFactorMap 1) f) ∧
      (relativeFactorCoupling (M.law : Measure (RelStructure S (Vinfinite S))) uniform01
        (B.lowerFactorMap 1) f).map Prod.fst = (M.law : Measure (RelStructure S (Vinfinite S))) ∧
      (relativeFactorCoupling (M.law : Measure (RelStructure S (Vinfinite S))) uniform01
        (B.lowerFactorMap 1) f).map Prod.snd = uniform01 ∧
      B.lowerFactorMap 1 ∘ Prod.fst =ᵐ[relativeFactorCoupling
        (M.law : Measure (RelStructure S (Vinfinite S))) uniform01 (B.lowerFactorMap 1) f]
          f ∘ Prod.snd ∧
      CondIndepFun (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance)
        ((B.measurable_lowerFactorMap' 1).comp measurable_fst).comap_le Prod.fst Prod.snd
        (relativeFactorCoupling (M.law : Measure (RelStructure S (Vinfinite S))) uniform01
          (B.lowerFactorMap 1) f) :=
  exists_relativeFactorCoupling_uniform01 (M.law : Measure (RelStructure S (Vinfinite S)))
    (B.measurable_lowerFactorMap' 1)

/-- **The transfer clause at rank one.** The latent is conditionally independent, given the
rank-one factor, of *every* measurable reading of the structure — in particular of whatever the
rank-one factor leaves unresolved. This is the form the next step of the recursion consumes. -/
theorem condIndepFun_comp_fst_snd_rankOne {f : ℝ → B.LowerFactorSpace 1} (hf : Measurable f)
    (hfq : uniform01.map f =
      (M.law : Measure (RelStructure S (Vinfinite S))).map (B.lowerFactorMap 1))
    {Y : Type*} [MeasurableSpace Y] {g : RelStructure S (Vinfinite S) → Y} (hg : Measurable g) :
    CondIndepFun (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance)
      ((B.measurable_lowerFactorMap' 1).comp measurable_fst).comap_le (g ∘ Prod.fst) Prod.snd
      (relativeFactorCoupling (M.law : Measure (RelStructure S (Vinfinite S))) uniform01
        (B.lowerFactorMap 1) f) :=
  condIndepFun_comp_fst_snd_relativeFactorCoupling (B.measurable_lowerFactorMap' 1) hf hfq hg

end CoherentBasis

end RelSignature
