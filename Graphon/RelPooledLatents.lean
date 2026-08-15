/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelLatentGeometry
import Graphon.RelPoolGeometry
import Graphon.RelRankLatents
import Graphon.RelRankInjectionInvariance

/-!
# Pooled latent geometry and the mixed action (R4 converse, #107)

Stage 1 of the pooled-latent extension gate: the **law-free** latent geometry over the pooled
carrier. Everything here is the carrier-parametric core of `Graphon.RelLatentGeometry`
instantiated at `PoolVertex S`, plus the restriction to the original-support latents that relates
the pooled cube to the rank-`n` cube.

## Contents

* `PooledRankLatentIndex` / `PooledRankLatentSpace` / `pooledRankLatentSource` — pooled supports
  below the rank, their cube, and its i.i.d. uniform source;
* `pooledRankLatentRelabel` — the action of the **full** pooled permutation family
  `∀ s, Equiv.Perm (PoolVertex S s)`, with identity and composition laws and exact source
  invariance;
* `restrictOriginalLatents` — the measurable restriction to latents indexed by original supports;
* `restrictOriginalLatents_pooledRankLatentRelabel` — the **honest moved-window naturality**: a
  mixed permutation does not commute with restriction to the original latents; what holds is that
  restricting after relabeling is restriction along the moved embedding. The split case is the
  corollary `restrictOriginalLatents_sumCongr`.

* the **extensional bridges** `rankLatentRelabel_eq_latentRelabelOver` and
  `rankLatentReindex_eq_latentRestrictOver` — the rank-indexed action and the self-injection
  reindexing of `Graphon.RelRankInjectionInvariance` *are* the carrier-parametric operations at
  `Vinfinite S`. They are equalities, not `rfl`: the two constructions pick different `Decidable`
  instances under `open scoped Classical`, which is invisible propositionally. These are what let
  `RankRepresentation.invariant` and the self-injection invariance theorem be applied through the
  generic pooled API.

Deliberately absent: any law, `RankRepresentation`, recovery, screening, or coupling. Those enter
at stages 2 and 3 of the gate.
-/

open MeasureTheory

namespace RelSignature

universe u

variable {S : RelSignature.{u}}

/-! ### The pooled latent cube -/

/-- **Pooled supports** of cardinality below `n`: supports drawn from the pooled carrier, mixing
original and pool vertices freely. -/
abbrev PooledRankLatentIndex (S : RelSignature.{u}) (n : ℕ) :=
  LatentIndexOver S (PoolVertex S) n

/-- The pooled latent cube. -/
abbrev PooledRankLatentSpace (S : RelSignature.{u}) (n : ℕ) :=
  LatentSpaceOver S (PoolVertex S) n

/-- The pooled latent source: independent uniforms on all pooled supports below `n`. -/
noncomputable def pooledRankLatentSource (S : RelSignature.{u}) (n : ℕ) :
    Measure (PooledRankLatentSpace S n) :=
  latentSourceOver S (PoolVertex S) n

instance (n : ℕ) : IsProbabilityMeasure (pooledRankLatentSource S n) := by
  rw [pooledRankLatentSource]; infer_instance

/-! ### The full mixed action -/

/-- **The mixed pooled action** on the latent cube, by the full sortwise permutation family of the
pooled carrier — permutations moving vertices between the two halves included. -/
noncomputable def pooledRankLatentRelabel (ρ : ∀ s, Equiv.Perm (PoolVertex S s)) (n : ℕ) :
    PooledRankLatentSpace S n ≃ᵐ PooledRankLatentSpace S n :=
  latentRelabelOver ρ n

@[simp] theorem pooledRankLatentRelabel_apply (ρ : ∀ s, Equiv.Perm (PoolVertex S s)) (n : ℕ)
    (ω : PooledRankLatentSpace S n) (A : PooledRankLatentIndex S n) :
    pooledRankLatentRelabel ρ n ω A = ω (latentIndexPerm ρ n A) := rfl

@[simp] theorem pooledRankLatentRelabel_one (n : ℕ) :
    pooledRankLatentRelabel (S := S) (fun _ => 1) n = MeasurableEquiv.refl _ := by
  refine MeasurableEquiv.ext (funext fun ω => funext fun A => ?_)
  rw [pooledRankLatentRelabel_apply, latentIndexPerm_one]
  rfl

theorem pooledRankLatentRelabel_comp (ρ τ : ∀ s, Equiv.Perm (PoolVertex S s)) (n : ℕ) :
    pooledRankLatentRelabel (S := S) (fun s => ρ s * τ s) n =
      (pooledRankLatentRelabel ρ n).trans (pooledRankLatentRelabel τ n) := by
  refine MeasurableEquiv.ext (funext fun ω => funext fun A => ?_)
  rw [pooledRankLatentRelabel_apply, latentIndexPerm_comp]
  rfl

/-- **Exact invariance of the pooled source** under the full mixed action. -/
theorem pooledRankLatentSource_map_pooledRankLatentRelabel [Countable S.Srt]
    (ρ : ∀ s, Equiv.Perm (PoolVertex S s)) (n : ℕ) :
    (pooledRankLatentSource S n).map (pooledRankLatentRelabel ρ n) =
      pooledRankLatentSource S n :=
  latentSourceOver_map_latentRelabelOver ρ n

/-! ### Restriction to the original-support latents -/

/-- **Restriction to the original latents**: read the pooled coordinates indexed by supports
drawn from the original half. Its codomain is the rank-`n` cube itself, since `RankLatentIndex`
is the carrier-parametric index at `Vinfinite S`. -/
noncomputable def restrictOriginalLatents (S : RelSignature.{u}) (n : ℕ) :
    PooledRankLatentSpace S n → RankLatentSpace S n :=
  latentRestrictOver (fun s => originalVertex S s) n

theorem measurable_restrictOriginalLatents (n : ℕ) :
    Measurable (restrictOriginalLatents S n) :=
  measurable_latentRestrictOver _ n

@[simp] theorem restrictOriginalLatents_apply (n : ℕ) (ω : PooledRankLatentSpace S n)
    (A : RankLatentIndex S n) :
    restrictOriginalLatents S n ω A = ω (latentIndexEmbed (fun s => originalVertex S s) n A) :=
  rfl

/-- **The moved-window naturality.** Restricting to the original latents after a pooled
relabeling is restriction along the *moved* embedding. This holds for **every** pooled
permutation, mixed ones included — and it is the honest statement: a permutation carrying
original vertices into the pool half does not commute with restriction to the original latents,
and no such law is available. -/
theorem restrictOriginalLatents_pooledRankLatentRelabel
    (ρ : ∀ s, Equiv.Perm (PoolVertex S s)) (n : ℕ) :
    restrictOriginalLatents S n ∘ pooledRankLatentRelabel ρ n =
      latentRestrictOver (fun s => (originalVertex S s).trans (ρ s).toEmbedding) n :=
  latentRestrictOver_latentRelabelOver _ ρ n

/-- **The split corollary**: a permutation of the original half alone commutes with restriction
to the original latents, acting there through the carrier-parametric action at `Vinfinite S`. -/
theorem restrictOriginalLatents_sumCongr (σ : ∀ s, Equiv.Perm (Vinfinite S s)) (n : ℕ) :
    restrictOriginalLatents S n ∘
        pooledRankLatentRelabel (fun s => Equiv.sumCongr (σ s) (Equiv.refl _)) n =
      latentRelabelOver σ n ∘ restrictOriginalLatents S n :=
  latentRestrictOver_latentRelabelOver_of_intertwines _ _ σ (fun _ _ => rfl) n

/-! ### Bridges to the rank-indexed API

The rank-indexed operations were built before the carrier-parametric core and choose their own
`Decidable` instances; they agree with the generic ones extensionally but not by `rfl`. -/

theorem rankLatentIndexEquiv_eq_latentIndexPerm (σ : FinSuppPerm S) (n : ℕ)
    (A : RankLatentIndex S n) :
    rankLatentIndexEquiv σ n A = latentIndexPerm (fun s => σ.1 s) n A := by
  classical
  refine Subtype.ext (Finset.ext fun v => ?_)
  rw [rankLatentIndexEquiv_apply_coe, latentIndexPerm_apply_coe]
  simp [Finset.mem_image]

/-- **Bridge**: the rank-indexed relabeling is the carrier-parametric action at `Vinfinite S`. -/
theorem rankLatentRelabel_eq_latentRelabelOver (σ : FinSuppPerm S) (n : ℕ) :
    rankLatentRelabel σ n = latentRelabelOver (fun s => σ.1 s) n := by
  refine MeasurableEquiv.ext (funext fun ω => funext fun A => ?_)
  show ω (rankLatentIndexEquiv σ n A) = ω (latentIndexPerm _ n A)
  rw [rankLatentIndexEquiv_eq_latentIndexPerm]

theorem rankLatentIndexInj_eq_latentIndexEmbed (ι : ∀ s, Vinfinite S s ↪ Vinfinite S s) (n : ℕ)
    (A : RankLatentIndex S n) :
    rankLatentIndexInj ι n A = latentIndexEmbed ι n A := by
  classical
  refine Subtype.ext (Finset.ext fun v => ?_)
  rw [rankLatentIndexInj_coe, latentIndexEmbed_coe]
  simp [Finset.mem_image]

/-- **Bridge**: the self-injection reindexing of `Graphon.RelRankInjectionInvariance` is
restriction along that injection in the carrier-parametric core. This is where #194's invariance
theorem meets the generic pooled API. -/
theorem rankLatentReindex_eq_latentRestrictOver (ι : ∀ s, Vinfinite S s ↪ Vinfinite S s)
    (n : ℕ) :
    rankLatentReindex ι n = latentRestrictOver ι n := by
  funext ω A
  show ω (rankLatentIndexInj ι n A) = ω (latentIndexEmbed ι n A)
  rw [rankLatentIndexInj_eq_latentIndexEmbed]

end RelSignature
