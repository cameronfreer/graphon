/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelFactorLaws
import Mathlib.Probability.Kernel.CondDistrib

/-!
# The step kernel of a coherent factor (R4 converse piece 3, #107)

One kernel per finite tagged vertex set `A`: the conditional distribution of the exact-anchor
layer at `A` given the whole proper-subset boundary.

`stepKernel A : Kernel (BoundarySpace A) (ExactSpace A)` is `condDistrib` of the exact-anchor
map given the boundary map. The standard Borel structure of `ExactSpace A` — countable index,
Boolean values — is exactly the hypothesis `condDistrib` needs, which is what the factor-space
packaging was for.

Everything here is valid for an **arbitrary** exchangeable law. In particular the `A = ∅` base
case is deliberately *not* treated: its determinism uses dissociation, whereas `stepKernel`
should stay available without it. That base case belongs to the later realization/recursion
layer.

## Central identities

* `compProd_stepKernel` — the disintegration
  `boundaryLaw A ⊗ₘ stepKernel A = M.law.map fun ω => (boundaryMap A ω, exactMap A ω)`;
* `stepKernel_comp_boundaryLaw` — marginal recovery `stepKernel A ∘ₘ boundaryLaw A = exactLaw A`;
* `factorLaw_map_prodEquiv` — the same statement read through the product decomposition.
-/

open MeasureTheory MeasurableSpace ProbabilityTheory

namespace RelSignature

namespace CoherentBasis

universe u

variable {S : RelSignature.{u}} {M : InfiniteRelExchangeableLaw S} (B : CoherentBasis M)

/-! ### The step kernel -/

/-- **The step kernel at `A`**: the conditional distribution of the exact-anchor layer given the
boundary layer. One kernel per finite `A`, conditioned on the whole proper-subset boundary at
once — not one per pair `C ⊆ A`, and not a chain. -/
noncomputable def stepKernel (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Kernel (B.BoundarySpace A) (B.ExactSpace A) :=
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  condDistrib (B.exactMap A) (B.boundaryMap A)
    (M.law : Measure (RelStructure S (Vinfinite S)))

instance (A : Finset (Σ s : S.Srt, Vinfinite S s)) : IsMarkovKernel (B.stepKernel A) := by
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  rw [stepKernel]
  infer_instance

/-- **Disintegration**: the joint law of the boundary and exact-anchor layers is the boundary
law composed with the step kernel. -/
theorem compProd_stepKernel (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    B.boundaryLaw A ⊗ₘ B.stepKernel A =
      (M.law : Measure (RelStructure S (Vinfinite S))).map
        (fun ω => (B.boundaryMap A ω, B.exactMap A ω)) := by
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  rw [boundaryLaw, stepKernel]
  exact compProd_map_condDistrib (B.measurable_exactMap A).aemeasurable

/-- **Marginal recovery**: composing the step kernel with the boundary law returns the exact
law. -/
theorem stepKernel_comp_boundaryLaw (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    B.stepKernel A ∘ₘ B.boundaryLaw A = B.exactLaw A := by
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  rw [boundaryLaw, stepKernel, exactLaw]
  exact condDistrib_comp_map (B.measurable_boundaryMap A).aemeasurable
    (B.measurable_exactMap A).aemeasurable

/-- The factor map is the pair of its two layers, by definition of the layer maps. -/
theorem factorSpaceProdEquiv_factorMap (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    (fun ω => B.factorSpaceProdEquiv A (B.factorMap A ω)) =
      fun ω => (B.boundaryMap A ω, B.exactMap A ω) := rfl

/-- **The disintegration read through the product decomposition**: pushing the factor law along
`factorSpaceProdEquiv` gives the boundary law composed with the step kernel. -/
theorem factorLaw_map_prodEquiv (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    (B.factorLaw A).map (B.factorSpaceProdEquiv A) = B.boundaryLaw A ⊗ₘ B.stepKernel A := by
  rw [compProd_stepKernel, factorLaw, Measure.map_map (B.factorSpaceProdEquiv A).measurable
    (B.measurable_factorMap' A)]
  rfl

/-! ### Relabeling transport -/

open scoped Classical in
/-- **Exact transport of the joint law**: pushing the boundary-and-exact joint law at the image
vertex set along the two layer equivalences returns the joint law at `A`.

This is an equality of measures, not an a.e. statement: it follows from equivariance of the
splitting (`prodMap_comp_factorSpaceProdEquiv`, definitional) together with relabeling
invariance of the factor law, which is where exchangeability enters. -/
theorem map_prodMap_compProd_stepKernel (σ : FinSuppPerm S)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    (B.boundaryLaw (A.image (Sigma.map id fun s => ⇑(σ.1 s))) ⊗ₘ
        B.stepKernel (A.image (Sigma.map id fun s => ⇑(σ.1 s)))).map
        (Prod.map (B.boundarySpaceEquiv σ A) (B.exactSpaceEquiv σ A)) =
      B.boundaryLaw A ⊗ₘ B.stepKernel A := by
  have hmeas : Measurable (Prod.map (B.boundarySpaceEquiv σ A) (B.exactSpaceEquiv σ A)) :=
    ((B.boundarySpaceEquiv σ A).measurable.comp measurable_fst).prod
      ((B.exactSpaceEquiv σ A).measurable.comp measurable_snd)
  rw [← B.factorLaw_map_prodEquiv, ← B.factorLaw_map_prodEquiv,
    Measure.map_map hmeas (B.factorSpaceProdEquiv _).measurable,
    B.prodMap_comp_factorSpaceProdEquiv σ A,
    ← Measure.map_map (B.factorSpaceProdEquiv A).measurable (B.factorSpaceEquiv σ A).measurable,
    B.factorLaw_map_factorSpaceEquiv σ A]

end CoherentBasis


end RelSignature
