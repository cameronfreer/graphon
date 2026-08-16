/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelPooledLatents
import Graphon.RelRankInjectionInvariance

/-!
# The pooled rank extension (R4 converse, #107)

Stage 2 of the pooled-latent extension gate: the joint object carrying a **genuine mixed action**
on both the structure and the latents.

`PooledRankExtension C` has exactly three fields — the joint law on the pooled structure space
times the pooled latent cube, the exact restriction of that law to `C.P` along the two original
restrictions, and invariance under the **full** pooled permutation family. There is no
independence field: an independent pool would recreate the defect of the rejected factor
coupling, and nothing here needs one.

`RankRepresentation.pooledExtension` is the cheap constructor. Both of its laws come from the
joint self-injection invariance theorem `RankRepresentation.map_prodMap_restrict_self`, through
the bridges of `Graphon.RelPooledLatents`:

* writing `pv` for `poolVertexEquiv` and `ov` for `originalVertex`, the transport is `comap pv` on
  structures and restriction along `pv` on latents;
* `restrictOriginal ∘ transport` is `comap (pv ∘ ov)`, and `pv ∘ ov` is a **self-injection** of
  the original carrier — that is `map_restrictOriginal`;
* `relabel ρ ∘ transport = transport ∘ relabel κ` for the conjugate `κ = pv ∘ ρ ∘ pv⁻¹`, a
  **permutation** of the original carrier — that is `invariant`, for every mixed `ρ`, since a
  permutation is in particular an injection.

The structure deliberately carries **no mixed-window field**: the joint mixed-window marginal, and
current-rank recovery and screening on mixed pooled supports, are separate derived consequences of
these three fields rather than part of the primitive. Nothing route-specific belongs here.
-/

open MeasureTheory

namespace RelSignature

namespace InfiniteRelExchangeableLaw

universe u

variable {S : RelSignature.{u}} [Countable S.Srt] [Countable S.Rel]
  {M : InfiniteRelExchangeableLaw S} {n : ℕ}

/-- **A pooled rank extension** of a rank-`n` representation: a joint law on the pooled structure
space and the pooled latent cube, restricting to the representation on the original coordinates
and invariant under every sortwise permutation of the pooled carrier — mixed permutations
included, which is the load-bearing quantifier. No independence clause of any kind. -/
structure PooledRankExtension (C : M.RankRepresentation n) where
  /-- The joint law on the pooled structure space and the pooled latent cube. -/
  law : ProbabilityMeasure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)
  /-- Its restriction to the original structure and original-support latents is the
  representation. -/
  map_restrictOriginal :
    (law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)).map
      (Prod.map (restrictOriginal S) (restrictOriginalLatents S n)) = C.P
  /-- Invariance under the **full** pooled permutation family, acting diagonally on the structure
  and on the pooled latents. -/
  invariant : ∀ ρ : ∀ s, Equiv.Perm (PoolVertex S s),
    (law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)).map
        (Prod.map (RelStructure.relabel ρ) (pooledRankLatentRelabel ρ n)) =
      (law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))

namespace RankRepresentation

variable (C : M.RankRepresentation n)

/-- The joint transport of the representation onto the pooled carrier: `comap poolVertexEquiv` on
structures, restriction along `poolVertexEquiv` on latents. -/
noncomputable def pooledTransport :
    RelStructure S (Vinfinite S) × RankLatentSpace S n →
      RelStructure S (PoolVertex S) × PooledRankLatentSpace S n :=
  Prod.map (RelStructure.congrCarrier fun s => (poolVertexEquiv S s).symm)
    (latentRestrictOver (fun s => (poolVertexEquiv S s).toEmbedding) n)

omit [Countable S.Srt] [Countable S.Rel] in
theorem measurable_pooledTransport :
    Measurable (pooledTransport (S := S) (n := n)) :=
  (RelStructure.congrCarrier _).measurable.prodMap
    (measurable_latentRestrictOver _ n)

/-- The self-injection of the original carrier obtained by embedding into the pool and
identifying back. -/
def originalSelfInjection (S : RelSignature.{u}) (s : S.Srt) :
    Vinfinite S s ↪ Vinfinite S s :=
  (originalVertex S s).trans (poolVertexEquiv S s).toEmbedding

/-- **The cheap pooled extension.** Both laws are `map_prodMap_restrict_self` in disguise. -/
noncomputable def pooledExtension : PooledRankExtension C where
  law :=
    ⟨C.P.map pooledTransport, by
      haveI := C.isProbabilityMeasure_P
      exact Measure.isProbabilityMeasure_map measurable_pooledTransport.aemeasurable⟩
  map_restrictOriginal := by
    haveI := C.isProbabilityMeasure_P
    rw [ProbabilityMeasure.coe_mk,
      Measure.map_map ((measurable_restrictOriginal).prodMap
        (measurable_restrictOriginalLatents n)) measurable_pooledTransport]
    have hcomp :
        Prod.map (restrictOriginal S) (restrictOriginalLatents S n) ∘
            pooledTransport (S := S) (n := n) =
          Prod.map (RelStructure.restrict (originalSelfInjection S))
            (rankLatentReindex (originalSelfInjection S) n) := by
      funext p
      refine Prod.ext ?_ ?_
      · rfl
      · show restrictOriginalLatents S n
            (latentRestrictOver (fun s => (poolVertexEquiv S s).toEmbedding) n p.2)
          = rankLatentReindex (originalSelfInjection S) n p.2
        rw [rankLatentReindex_eq_latentRestrictOver, restrictOriginalLatents]
        exact congrFun (latentRestrictOver_comp (fun s => originalVertex S s)
          (fun s => (poolVertexEquiv S s).toEmbedding) n) p.2
    rw [hcomp, C.map_prodMap_restrict_self (originalSelfInjection S)]
  invariant := by
    intro ρ
    haveI := C.isProbabilityMeasure_P
    set κ : ∀ s, Equiv.Perm (Vinfinite S s) :=
      fun s => (poolVertexEquiv S s).symm.trans ((ρ s).trans (poolVertexEquiv S s)) with hκ
    -- the representation is invariant under the conjugate permutation, by #194
    have hinvκ : C.P.map (Prod.map (RelStructure.relabel κ) (latentRelabelOver κ n)) = C.P := by
      have h := C.map_prodMap_restrict_self (fun s => (κ s).toEmbedding)
      rwa [rankLatentReindex_eq_latentRestrictOver, latentRestrictOver_toEmbedding] at h
    -- the transport intertwines the pooled action with the conjugate one
    have hjoint :
        Prod.map (RelStructure.relabel ρ) (pooledRankLatentRelabel ρ n) ∘
            pooledTransport (S := S) (n := n) =
          pooledTransport ∘ Prod.map (RelStructure.relabel κ) (latentRelabelOver κ n) := by
      funext p
      refine Prod.ext ?_ ?_
      · show RelStructure.relabel ρ
            (RelStructure.congrCarrier (fun s => (poolVertexEquiv S s).symm) p.1)
          = RelStructure.congrCarrier (fun s => (poolVertexEquiv S s).symm)
              (RelStructure.relabel κ p.1)
        rw [RelStructure.congrCarrier_relabel]
        congr 1
        funext s
        refine Equiv.ext fun x => ?_
        simp [hκ]
      · show pooledRankLatentRelabel ρ n
            (latentRestrictOver (fun s => (poolVertexEquiv S s).toEmbedding) n p.2)
          = latentRestrictOver (fun s => (poolVertexEquiv S s).toEmbedding) n
              (latentRelabelOver κ n p.2)
        exact (congrFun (latentRestrictOver_latentRelabelOver_conj
          (fun s => poolVertexEquiv S s) ρ n) p.2).symm
    have hκmeas : Measurable
        (Prod.map (RelStructure.relabel κ) (latentRelabelOver κ n) :
          RelStructure S (Vinfinite S) × RankLatentSpace S n →
            RelStructure S (Vinfinite S) × RankLatentSpace S n) :=
      (measurable_relabel κ).prodMap (latentRelabelOver κ n).measurable
    rw [ProbabilityMeasure.coe_mk,
      Measure.map_map (((measurable_relabel ρ)).prodMap
        (pooledRankLatentRelabel ρ n).measurable) measurable_pooledTransport,
      hjoint, ← Measure.map_map measurable_pooledTransport hκmeas, hinvκ]

/-- The cheap extension's law, unfolded. -/
@[simp] theorem pooledExtension_law_coe :
    ((C.pooledExtension).law :
        Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) =
      C.P.map pooledTransport := rfl

end RankRepresentation

end InfiniteRelExchangeableLaw

end RelSignature
