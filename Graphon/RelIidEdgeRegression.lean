/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRankSuccessorContract
import Graphon.InfiniteDigraph
import Graphon.ForMathlib.CondIndepSup

/-!
# The i.i.d.-edge regression for the successor contract (R4 converse, #107, #196)

A hand-built rank `2 → 3` successor witness over `digraphSig`, testing **staging and recovery**
together — where the bipartite regression tested independence and symmetry.

The law is the symmetric i.i.d.-edge law: one uniform per two-point support, with

`X_uv = X_vu = 1{U_{u,v} ≤ 1/2}` and `X_uu = false`.

Keying the array by a coordinate's *support* makes both facts definitional: the two directed
coordinates of a block share a support and therefore a value, and the diagonal has a one-element
support so it falls in the default branch. Blocks at **distinct** two-point supports are i.i.d.,
being distinct coordinates of the source. Making `X_uv` and `X_vu` independently directed would
introduce an equivariant-orientation problem without testing staging any better.

## Shape of the regression

* the rank-two coupling is defined **independently** as `iidEdgeLaw.prod (rankLatentSource 2)`,
  so independence of the edges from the old latents is literal;
* the rank-three coupling is built from `rankLatentSource 3`, retaining the whole latent point and
  decoding the array from its fresh rank-two layer;
* the truncation identity is proved immediately, before either representation is packaged.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RelSignature

namespace IidEdgeRegression

/-- The edge layer: one uniform per two-point support. -/
abbrev Edges := RankSupport digraphSig 2 → ℝ

open scoped Classical in
/-- **The symmetric i.i.d.-edge array**, keyed by a coordinate's support. Both directed
coordinates of a two-point block share a support, hence a value; the diagonal has a one-element
support and is `false`. -/
noncomputable def arr (e : Edges) : RelStructure digraphSig (Vinfinite digraphSig) :=
  fun c => if h : c.support.card = 2 then decide (e ⟨c.support, h⟩ ≤ 1 / 2) else false

open scoped Classical in
/-- **Symmetry is definitional**: the two directed coordinates of a block share a support. -/
theorem arr_symm (e : Edges) (u v : ℕ) :
    arr e (digraphCoord u v) = arr e (digraphCoord v u) := by
  have hsupp : (digraphCoord u v : RelCoord digraphSig (Vinfinite digraphSig)).support =
      (digraphCoord v u : RelCoord digraphSig (Vinfinite digraphSig)).support := by
    refine Finset.ext fun w => ?_
    rw [RelCoord.mem_support_iff, RelCoord.mem_support_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
  simp only [arr, hsupp]

open scoped Classical in
/-- **The diagonal is `false`**: its support has one element, not two. -/
@[simp] theorem arr_diagonal (e : Edges) (v : ℕ) : arr e (digraphCoord v v) = false := by
  have hsupp : (digraphCoord v v : RelCoord digraphSig (Vinfinite digraphSig)).support =
      {⟨(), v⟩} := by
    refine Finset.ext fun w => ?_
    rw [RelCoord.mem_support_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> rfl
    · rintro rfl
      exact ⟨0, rfl⟩
  rw [arr, dif_neg]
  rw [hsupp, Finset.card_singleton]
  omega

open scoped Classical in
theorem measurable_arr : Measurable arr := by
  refine measurable_pi_lambda _ fun c => ?_
  by_cases h : (c : RelCoord digraphSig (Vinfinite digraphSig)).support.card = 2
  · have hfun : (fun e : Edges => arr e c) = fun e => decide (e ⟨c.support, h⟩ ≤ 1 / 2) := by
      funext e; rw [arr, dif_pos h]
    rw [hfun]
    exact measurable_decideLe (measurable_pi_apply _)
  · have hfun : (fun e : Edges => arr e c) = fun _ => false := by
      funext e; rw [arr, dif_neg h]
    rw [hfun]
    exact measurable_const

/-- **The i.i.d.-edge law**, defined from the edge layer alone. -/
noncomputable def iidEdgeLaw : Measure (RelStructure digraphSig (Vinfinite digraphSig)) :=
  (iidUniformSource (RankSupport digraphSig 2)).map arr

instance : IsProbabilityMeasure iidEdgeLaw :=
  Measure.isProbabilityMeasure_map measurable_arr.aemeasurable

end IidEdgeRegression

end RelSignature
