/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelCoherentBasis

/-!
# Boundary and exact layers of the coherent factors (R4 converse piece 3, #107)

The factor at a finite tagged vertex set `A` splits by **anchor**, into the coordinates carried
over from proper subsets of `A` and the coordinates whose anchor is exactly `A`:

* `BoundaryIndex A` — indices whose anchor is a **proper** subset of `A`;
* `ExactIndex A` — the **exact-anchor layer**: indices whose anchor is exactly `A`;
* `FactorSpace A ≃ᵐ BoundarySpace A × ExactSpace A`.

This is a partition of *coordinates by anchor*, not of *information*. Anchors are not minimal:
a Boolean expression can carry anchor `A` while naming an event that is already measurable over
a proper subset — the seeds at `A` live in `fixingAlgebra A`, which contains `fixingAlgebra C`
for every `C ⊆ A`. So the exact-anchor layer is not "the new information at `A`", and nothing
in the splitting alone rules out redundancy between layers.

## Why this decomposition

The recursion that builds the representing kernels is by `|A|`, with **one kernel per finite
`A`**, conditioned on the whole proper-subset boundary at once. The two obvious alternatives are
both wrong:

* **Kernels for every pair `C ⊆ A`** are redundant, and would force compatibility conditions
  between different versions of conditional distributions — each only defined a.e.
* **A linear chain** over some enumeration introduces an arbitrary ordering, and lets the value
  at `A` depend on sets incomparable to `A`, which violates the subset-locality of the
  Aldous–Hoover–Kallenberg formula.

Sampling only `ExactSpace A`, rather than resampling all of `FactorSpace A`, means the recursion
never overwrites coordinate slots already generated at proper subsets — that much *is* structural,
from the coordinate partition. Consistency with lower-anchor events that an exact-anchor
coordinate happens to duplicate semantically is a different matter: it is an almost-sure/support
property of `stepKernel`, which conditions on the boundary, and not something the partition
delivers on its own.

## Contents

* the boundary/exact index and space splitting, with `factorSpaceProdEquiv`;
* `factorLaw`, `boundaryLaw`, and `exactLaw` — the pushforwards of the law along the
  corresponding maps, with `boundaryLaw_eq_map` and `exactLaw_eq_map` identifying the latter two
  as the marginals of the first;
* `factorLaw_map_factorProjection` — projection consistency;
* `factorLaw_map_factorSpaceEquiv` — relabeling invariance, from exchangeability of the law.

The conditional kernel of the exact layer given the boundary is the next step, and is where
the standard Borel structure of these spaces is used.
-/

open MeasureTheory MeasurableSpace

namespace RelSignature

namespace CoherentBasis

universe u

variable {S : RelSignature.{u}} {M : InfiniteRelExchangeableLaw S} (B : CoherentBasis M)

/-! ### The boundary and exact layers -/

/-- Indices whose anchor is a **proper** subset of `A`: the coordinates at `A` carried over from
strictly smaller vertex sets. -/
def BoundaryIndex (A : Finset (Σ s : S.Srt, Vinfinite S s)) := {i : B.ι // B.anchor i ⊂ A}

/-- **The exact-anchor layer**: indices whose anchor is exactly `A`.

Note that this is an anchor condition, not a minimality condition — an expression anchored at
`A` may still name an event measurable over a proper subset, since `fixingAlgebra C ≤
fixingAlgebra A` for `C ⊆ A`. The layer is disjoint from the boundary layer as a set of
*coordinates*; semantic non-redundancy is not claimed here. -/
def ExactIndex (A : Finset (Σ s : S.Srt, Vinfinite S s)) := {i : B.ι // B.anchor i = A}

instance (A : Finset (Σ s : S.Srt, Vinfinite S s)) : Countable (B.BoundaryIndex A) :=
  Subtype.countable

instance (A : Finset (Σ s : S.Srt, Vinfinite S s)) : Countable (B.ExactIndex A) :=
  Subtype.countable

/-- The boundary layer of the factor space. -/
abbrev BoundarySpace (A : Finset (Σ s : S.Srt, Vinfinite S s)) := B.BoundaryIndex A → Bool

/-- The exact layer of the factor space. -/
abbrev ExactSpace (A : Finset (Σ s : S.Srt, Vinfinite S s)) := B.ExactIndex A → Bool

instance (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    StandardBorelSpace (B.BoundarySpace A) := inferInstance

instance (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    StandardBorelSpace (B.ExactSpace A) := inferInstance

open scoped Classical in
/-- **The factor space splits as boundary times exact**: an index anchored inside `A` is
anchored either properly inside it or exactly at it, and never both. -/
noncomputable def factorSpaceProdEquiv (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    B.FactorSpace A ≃ᵐ B.BoundarySpace A × B.ExactSpace A where
  toFun f := (fun i => f ⟨i.1, le_of_lt i.2⟩, fun i => f ⟨i.1, le_of_eq i.2⟩)
  invFun p i :=
    if h : B.anchor i.1 = A then p.2 ⟨i.1, h⟩ else p.1 ⟨i.1, lt_of_le_of_ne i.2 h⟩
  left_inv f := by
    funext i
    by_cases h : B.anchor i.1 = A
    · simp only [dif_pos h]
      rfl
    · simp only [dif_neg h]
      rfl
  right_inv p := by
    refine Prod.ext ?_ ?_
    · funext i
      simp only [dif_neg (ne_of_lt i.2)]
      rfl
    · funext i
      simp only [dif_pos i.2]
      rfl
  measurable_toFun := by
    refine Measurable.prod ?_ ?_ <;>
      exact measurable_pi_lambda _ fun _ => measurable_pi_apply _
  measurable_invFun := by
    refine measurable_pi_lambda _ fun i => ?_
    -- the branch condition does not depend on the point, so `dif_pos`/`dif_neg` suffice;
    -- rewriting with `h` itself would also rewrite inside the subtype and break the match
    by_cases h : B.anchor i.1 = A
    · have hfun : (fun p : B.BoundarySpace A × B.ExactSpace A =>
          if h' : B.anchor i.1 = A then p.2 ⟨i.1, h'⟩
            else p.1 ⟨i.1, lt_of_le_of_ne i.2 h'⟩) =
          fun p => p.2 ⟨i.1, h⟩ := funext fun _ => dif_pos h
      exact hfun ▸ measurable_snd.eval
    · have hfun : (fun p : B.BoundarySpace A × B.ExactSpace A =>
          if h' : B.anchor i.1 = A then p.2 ⟨i.1, h'⟩
            else p.1 ⟨i.1, lt_of_le_of_ne i.2 h'⟩) =
          fun p => p.1 ⟨i.1, lt_of_le_of_ne i.2 h⟩ := funext fun _ => dif_neg h
      exact hfun ▸ measurable_fst.eval

/-- The boundary half of the factor map. -/
noncomputable def boundaryMap (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    RelStructure S (Vinfinite S) → B.BoundarySpace A :=
  fun X => (B.factorSpaceProdEquiv A (B.factorMap A X)).1

/-- The exact half of the factor map. -/
noncomputable def exactMap (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    RelStructure S (Vinfinite S) → B.ExactSpace A :=
  fun X => (B.factorSpaceProdEquiv A (B.factorMap A X)).2

theorem measurable_boundaryMap (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measurable (B.boundaryMap A) :=
  ((B.factorSpaceProdEquiv A).measurable.comp (B.measurable_factorMap' A)).fst

theorem measurable_exactMap (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measurable (B.exactMap A) :=
  ((B.factorSpaceProdEquiv A).measurable.comp (B.measurable_factorMap' A)).snd

/-! ### The factor laws -/

/-- **The factor law at `A`**: the law of the factor map under `M`. -/
noncomputable def factorLaw (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measure (B.FactorSpace A) :=
  (M.law : Measure (RelStructure S (Vinfinite S))).map (B.factorMap A)

/-- **The boundary law at `A`** — the conditioning measure of the step kernel. -/
noncomputable def boundaryLaw (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measure (B.BoundarySpace A) :=
  (M.law : Measure (RelStructure S (Vinfinite S))).map (B.boundaryMap A)

/-- **The exact law at `A`**. -/
noncomputable def exactLaw (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measure (B.ExactSpace A) :=
  (M.law : Measure (RelStructure S (Vinfinite S))).map (B.exactMap A)

instance (A : Finset (Σ s : S.Srt, Vinfinite S s)) : IsProbabilityMeasure (B.factorLaw A) := by
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  exact Measure.isProbabilityMeasure_map (B.measurable_factorMap' A).aemeasurable

instance (A : Finset (Σ s : S.Srt, Vinfinite S s)) : IsProbabilityMeasure (B.boundaryLaw A) := by
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  exact Measure.isProbabilityMeasure_map (B.measurable_boundaryMap A).aemeasurable

instance (A : Finset (Σ s : S.Srt, Vinfinite S s)) : IsProbabilityMeasure (B.exactLaw A) := by
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  exact Measure.isProbabilityMeasure_map (B.measurable_exactMap A).aemeasurable

/-- **The boundary law is a marginal of the factor law**, through the product decomposition. -/
theorem boundaryLaw_eq_map (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    B.boundaryLaw A = (B.factorLaw A).map (fun p => (B.factorSpaceProdEquiv A p).1) := by
  rw [boundaryLaw, factorLaw, Measure.map_map
    (((B.factorSpaceProdEquiv A).measurable).fst) (B.measurable_factorMap' A)]
  rfl

/-- **The exact law is the other marginal of the factor law**, symmetric to
`boundaryLaw_eq_map`. Used when checking that `stepKernel` disintegrates the factor law. -/
theorem exactLaw_eq_map (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    B.exactLaw A = (B.factorLaw A).map (fun p => (B.factorSpaceProdEquiv A p).2) := by
  rw [exactLaw, factorLaw, Measure.map_map
    (((B.factorSpaceProdEquiv A).measurable).snd) (B.measurable_factorMap' A)]
  rfl

/-- **Projection consistency**: the factor laws are compatible along the sub-index inclusions.
Immediate, since `factorProjection_factorMap` is `rfl`. -/
theorem factorLaw_map_factorProjection {C A : Finset (Σ s : S.Srt, Vinfinite S s)} (hCA : C ⊆ A) :
    (B.factorLaw A).map (B.factorProjection hCA) = B.factorLaw C := by
  rw [factorLaw, Measure.map_map (B.measurable_factorProjection hCA) (B.measurable_factorMap' A),
    B.factorProjection_factorMap hCA]
  rfl

open scoped Classical in
/-- **Relabeling invariance of the factor laws**: transporting the factor law at the image
vertex set along `factorSpaceEquiv` returns the factor law at `A`. This is where
exchangeability of `M` enters — everything before it was law-free. -/
theorem factorLaw_map_factorSpaceEquiv (σ : FinSuppPerm S)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    (B.factorLaw (A.image (Sigma.map id fun s => ⇑(σ.1 s)))).map (B.factorSpaceEquiv σ A) =
      B.factorLaw A := by
  rw [factorLaw, Measure.map_map (B.factorSpaceEquiv σ A).measurable
    (B.measurable_factorMap' _), B.factorMap_comp_relabel σ A, ← Measure.map_map
    (B.measurable_factorMap' A) (measurable_relabel σ.1), M.exchangeable σ.1]
  rfl

end CoherentBasis

end RelSignature
