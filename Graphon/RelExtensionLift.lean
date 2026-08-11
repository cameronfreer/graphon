/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRankRepresentation
import Graphon.RelStationaryExtension
import Graphon.ForMathlib.RelativeFactorCoupling

/-!
# The split-equivariant extension lift (R4 converse, #107)

The joint law of a rank-`n` representation and a stationary extension, glued over their common
structure marginal: `(X, U_{<n})` from the representation, `X⁺` from the extension, coupled by
the relative joining over `X`.

**This lift is split-equivariant, and only split-equivariant.** The invariance proved here is
under the split diagonal action — `σ` on `X`, `rankLatentRelabel σ n` on the old latents,
`Equiv.sumCongr (σ s) 1` on `X⁺`. Mixed pooled permutations do **not** act on this object: for
a boundary-crossing `ρ`, `restrictOriginal (relabel ρ X⁺)` reads pool vertices and is not
`relabel σ (restrictOriginal X⁺)` for any original-carrier `σ` — the factor square of the
two-sided transport does not exist — and `RankLatentSpace S n` indexes latents by
original-carrier supports only, so a boundary-crossing permutation has no action on the old
latents at all. Obtaining a pooled latent law with a genuine mixed action is the separate
pooled-latent extension gate on #107, not this file.

The joining's conditional clause `(X, U_{<n}) ⊥⊥ X⁺ ∣ σ(X)` is recorded; it does **not**
manufacture correlated latents (guard 3): whatever the pool knows beyond `X` is untouched, and
whatever `U_{<n}` encodes beyond `X` says nothing about `X⁺`.

Recovery and screening need no *new* transfer infrastructure: both are statements about the
`(X, U_{<n})`-marginal, that marginal is exactly the representation's coupling
(`extensionLift_map_fst`), and consumers transport along `Prod.fst` with the existing
measure-preserving/`comap` machinery.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

namespace InfiniteRelExchangeableLaw

universe u

variable {S : RelSignature.{u}} [Countable S.Srt] [Countable S.Rel]
  {M : InfiniteRelExchangeableLaw S}

open scoped Classical in
/-- **The extension lift**: the representation's coupling and the extended law, glued by the
relative joining over their common structure marginal. -/
noncomputable def RankRepresentation.extensionLift {n : ℕ} (C : M.RankRepresentation n)
    (E : StationaryExtension M) :
    Measure ((RelStructure S (Vinfinite S) × RankLatentSpace S n) ×
      RelStructure S (PoolVertex S)) :=
  haveI := C.isProbabilityMeasure_P
  relativeFactorCoupling C.P (E.law : Measure (RelStructure S (PoolVertex S)))
    Prod.fst (restrictOriginal S)

namespace RankRepresentation

variable {n : ℕ} (C : M.RankRepresentation n) (E : StationaryExtension M)

/-- The common-factor identity: both inputs have the law as their structure marginal. -/
theorem extensionLift_factor_eq :
    (E.law : Measure (RelStructure S (PoolVertex S))).map (restrictOriginal S) =
      C.P.map Prod.fst := by
  rw [E.map_restrictOriginal, C.map_fst]

/-- The first marginal of the lift is the representation's coupling. Recovery and screening
pull back through this identity — no *new* transfer infrastructure is needed; consumers use the
existing measure-preserving/`comap` transport along `Prod.fst`. -/
theorem extensionLift_map_fst : (C.extensionLift E).map Prod.fst = C.P := by
  haveI := C.isProbabilityMeasure_P
  exact map_fst_relativeFactorCoupling measurable_fst

/-- The second marginal of the lift is the extended law. -/
theorem extensionLift_map_snd :
    (C.extensionLift E).map Prod.snd = (E.law : Measure (RelStructure S (PoolVertex S))) := by
  haveI := C.isProbabilityMeasure_P
  exact map_snd_relativeFactorCoupling measurable_restrictOriginal (C.extensionLift_factor_eq E)

instance : IsProbabilityMeasure (C.extensionLift E) := by
  haveI := C.isProbabilityMeasure_P
  exact isProbabilityMeasure_relativeFactorCoupling measurable_fst

/-- **The common-factor identity — the defining "glued over the same `X`" law**: the structure
read off the representation pair agrees almost everywhere with the original restriction of the
extended array. Exact marginals plus conditional independence do not expose this; it is the
clause that says both coordinates carry one and the same `X`. -/
theorem extensionLift_commonFactor :
    (Prod.fst : RelStructure S (Vinfinite S) × RankLatentSpace S n →
        RelStructure S (Vinfinite S)) ∘ Prod.fst
      =ᵐ[C.extensionLift E] restrictOriginal S ∘ Prod.snd := by
  haveI := C.isProbabilityMeasure_P
  exact comp_fst_ae_eq_comp_snd_relativeFactorCoupling measurable_fst
    measurable_restrictOriginal (C.extensionLift_factor_eq E)

open scoped Classical in
/-- **Split-diagonal invariance** — and deliberately nothing stronger: `σ` acts on the
structure, on the old latents, and on the original half of the pooled carrier, fixing the pool
half. Mixed pooled permutations do not act on this object; see the module header. -/
theorem extensionLift_map_split (σ : FinSuppPerm S) :
    (C.extensionLift E).map
      (Prod.map (Prod.map (RelStructure.relabel σ.1) (rankLatentRelabel σ n))
        (RelStructure.relabel fun s => Equiv.sumCongr (σ.1 s) 1)) =
      C.extensionLift E := by
  haveI := C.isProbabilityMeasure_P
  refine map_prodMap_relativeFactorCoupling_two_sided measurable_fst
    measurable_restrictOriginal (C.extensionLift_factor_eq E)
    (RelStructure.congrCarrier (S := S) fun s => (σ.1 s).symm).measurableEmbedding
    ⟨(M.measurePreserving_relabel σ.1).measurable.prodMap
      (rankLatentRelabel σ n).measurable, C.invariant σ⟩
    ⟨measurable_relabel _, E.invariant _⟩ (Filter.EventuallyEq.of_eq rfl)
    (Filter.EventuallyEq.of_eq (funext fun X => ?_))
  exact (restrictOriginal_relabel_sumCongr σ.1 (fun _ => 1) X).symm

open scoped Classical in
/-- **The joining's conditional clause**: the representation pair and the extended array are
conditionally independent given the common structure factor — a variable on the lift space.
This does not manufacture correlated latents: it says the pool's surplus over `X` and the old
latents' surplus over `X` are mutually uninformative, nothing more. -/
theorem condIndepFun_fst_snd_extensionLift :
    CondIndepFun (MeasurableSpace.comap ((Prod.fst : RelStructure S (Vinfinite S) ×
        RankLatentSpace S n → RelStructure S (Vinfinite S)) ∘ Prod.fst) inferInstance)
      (measurable_fst.comp measurable_fst).comap_le Prod.fst Prod.snd (C.extensionLift E) := by
  haveI := C.isProbabilityMeasure_P
  exact condIndepFun_fst_snd_relativeFactorCoupling measurable_fst measurable_restrictOriginal
    (C.extensionLift_factor_eq E)

end RankRepresentation

end InfiniteRelExchangeableLaw

end RelSignature
