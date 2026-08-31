/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelAustinPolling
import Graphon.RelLowerFactor
import Graphon.RelFactorLaws
import Graphon.RelRankSuccessor

/-!
# The Austin base and its action: unit 2, law-free checkpoint (R4 converse, #107, #197)

Route **A** (Austin) only. No Kallenberg machinery, and nothing here asserts that the two routes'
outputs agree.

The **auxiliary base** carried alongside the representation is
`AustinBaseSpace S n = PooledRankLatentSpace S n × ClusterSpace S n`: the pooled lower-rank latents
together with the mixed clusters. It is the equivariant lower-rank base over which the enriched
kernel will later be built — not a family of fresh rank-`n` coordinates, and not relational data.
Every pooled latent index has cardinality `< n`, so the base carries no rank-`n` block.

This module is deliberately **law-free apart from one invariance**: it fixes the action and proves
it strict, before any bundle, kernel, or conditional-distribution statement is written.
Equivariance cannot be repaired downstream, so it is established first.

## Contents

* `poolLift` — the split lift of a finitely supported relabeling: act on the original half, fix
  the spare half. Its `Sum.isRight` preservation is what keeps mixed clusters mixed.
* `mixedClusterLift`, with identity and composition laws — the induced permutation of the cluster
  index.
* `austinBaseRelabel`, with identity and composition laws as **function equalities** — the action
  on the base. A pinned definition, not an opaque structure field.
* `enrichedPollingMap_naturality` — **one global square** covering the structure, the original
  latents, the pooled latents and the clusters simultaneously. Stated generically in the cluster
  index, so genuinely mixed and all-spare indices are both covered.
* `enrichedPollingLaw_map_austinBaseRelabel` — exact invariance of the pushed enriched law,
  derived from that square together with the extension's own invariance.

The adapter spaces `EnrichedLowerSpace` and `EnrichedBoundarySpace` are introduced here only so
that their standard-Borel structure is available; their maps and commuting laws belong to the
bundle that follows.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

namespace InfiniteRelExchangeableLaw

variable {S : RelSignature} [Countable S.Srt] [Countable S.Rel]
  {M : InfiniteRelExchangeableLaw S} {n : ℕ}

/-! ### The auxiliary base -/

variable (S n) in
/-- **The Austin base**: pooled lower-rank latents together with the mixed clusters. The
equivariant lower-rank base of the construction; it carries no rank-`n` block, since every pooled
latent index has cardinality `< n` and every cluster index carries a spare vertex. -/
abbrev AustinBaseSpace := PooledRankLatentSpace S n × ClusterSpace S n

instance : StandardBorelSpace (AustinBaseSpace S n) := inferInstance

/-! ### The split lift -/

/-- **The split lift** of a finitely supported relabeling: act on the original half, fix the spare
half. Restricting to split permutations is what makes the original-latent component natural; a
boundary-crossing permutation has no such law. -/
def poolLift (σ : FinSuppPerm S) : ∀ s, Equiv.Perm (PoolVertex S s) :=
  fun s => Equiv.sumCongr (σ.1 s) (Equiv.refl _)

omit [Countable S.Srt] [Countable S.Rel] in
/-- The split lift preserves the spare half, which is what keeps mixed clusters mixed. -/
@[simp] theorem isRight_poolLift (σ : FinSuppPerm S) (s : S.Srt) (x : PoolVertex S s) :
    Sum.isRight (poolLift σ s x) = Sum.isRight x := by
  cases x <;> rfl

omit [Countable S.Srt] [Countable S.Rel] in
@[simp] theorem poolLift_one (s : S.Srt) :
    poolLift (S := S) 1 s = Equiv.refl _ :=
  Equiv.ext fun x => by cases x <;> rfl

omit [Countable S.Srt] [Countable S.Rel] in
theorem poolLift_mul (σ τ : FinSuppPerm S) (s : S.Srt) :
    poolLift (σ * τ) s = poolLift σ s * poolLift τ s :=
  Equiv.ext fun x => by cases x <;> rfl

/-! ### The induced action on cluster indices -/

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
/-- Round trip of the split lift on supports, proved by membership so that no `DecidableEq`
instance enters the statement. -/
private theorem supportImage_poolLift_inv (σ : FinSuppPerm S)
    (A : Finset (Σ s : S.Srt, PoolVertex S s)) :
    supportImage (fun s => (poolLift σ⁻¹ s).toEmbedding)
      (supportImage (fun s => (poolLift σ s).toEmbedding) A) = A := by
  have hx : ∀ (s : S.Srt) (x : PoolVertex S s), poolLift σ⁻¹ s (poolLift σ s x) = x := by
    intro s x
    rw [show poolLift σ⁻¹ s (poolLift σ s x) = (poolLift σ⁻¹ s * poolLift σ s) x from rfl,
      ← poolLift_mul]
    simp
  refine Finset.ext fun v => ?_
  rw [mem_supportImage_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_supportImage_iff] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    obtain ⟨s, x⟩ := u
    show (⟨s, poolLift σ⁻¹ s (poolLift σ s x)⟩ : Σ s : S.Srt, PoolVertex S s) ∈ A
    rw [hx]
    exact hu
  · intro hv
    obtain ⟨s, x⟩ := v
    refine ⟨Sigma.map id (fun s => ⇑(poolLift σ s)) ⟨s, x⟩,
      (mem_supportImage_iff _ _ _).mpr ⟨⟨s, x⟩, hv, rfl⟩, ?_⟩
    show (⟨s, poolLift σ⁻¹ s (poolLift σ s x)⟩ : Σ s : S.Srt, PoolVertex S s) = ⟨s, x⟩
    rw [hx]

open scoped Classical in
/-- **The split lift permutes the mixed cluster indices**: it preserves cardinality, and preserves
the presence of a spare vertex, so a mixed index stays mixed — including the all-spare ones. -/
noncomputable def mixedClusterLift (σ : FinSuppPerm S) (n : ℕ) :
    MixedClusterIndex S n ≃ MixedClusterIndex S n where
  toFun A := ⟨supportImage (fun s => (poolLift σ s).toEmbedding) A.1, by
    refine ⟨by rw [card_supportImage]; exact A.2.1, ?_⟩
    obtain ⟨v, hv, hvr⟩ := A.2.2
    exact ⟨Sigma.map id (fun s => ⇑(poolLift σ s)) v,
      (mem_supportImage_iff _ _ _).mpr ⟨v, hv, rfl⟩, by
        rw [show (Sigma.map id (fun s => ⇑(poolLift σ s)) v).2 = poolLift σ v.1 v.2 from rfl,
          isRight_poolLift]
        exact hvr⟩⟩
  invFun A := ⟨supportImage (fun s => (poolLift σ⁻¹ s).toEmbedding) A.1, by
    refine ⟨by rw [card_supportImage]; exact A.2.1, ?_⟩
    obtain ⟨v, hv, hvr⟩ := A.2.2
    exact ⟨Sigma.map id (fun s => ⇑(poolLift σ⁻¹ s)) v,
      (mem_supportImage_iff _ _ _).mpr ⟨v, hv, rfl⟩, by
        rw [show (Sigma.map id (fun s => ⇑(poolLift σ⁻¹ s)) v).2 = poolLift σ⁻¹ v.1 v.2 from rfl,
          isRight_poolLift]
        exact hvr⟩⟩
  left_inv A := Subtype.ext (supportImage_poolLift_inv σ A.1)
  right_inv A := Subtype.ext (by
    have h := supportImage_poolLift_inv σ⁻¹ A.1
    rwa [inv_inv] at h)

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
@[simp] theorem mixedClusterLift_coe (σ : FinSuppPerm S) (n : ℕ) (A : MixedClusterIndex S n) :
    (mixedClusterLift σ n A).1 = supportImage (fun s => (poolLift σ s).toEmbedding) A.1 := rfl

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
private theorem supportImage_poolLift_one (A : Finset (Σ s : S.Srt, PoolVertex S s)) :
    supportImage (fun s => (poolLift (S := S) 1 s).toEmbedding) A = A := by
  refine Finset.ext fun v => ?_
  rw [mem_supportImage_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨s, x⟩ := w
    show (⟨s, poolLift (S := S) 1 s x⟩ : Σ s : S.Srt, PoolVertex S s) ∈ A
    rw [poolLift_one]
    exact hw
  · intro hv
    obtain ⟨s, x⟩ := v
    refine ⟨⟨s, x⟩, hv, ?_⟩
    show (⟨s, poolLift (S := S) 1 s x⟩ : Σ s : S.Srt, PoolVertex S s) = ⟨s, x⟩
    rw [poolLift_one]
    rfl

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
private theorem supportImage_poolLift_mul (σ τ : FinSuppPerm S)
    (A : Finset (Σ s : S.Srt, PoolVertex S s)) :
    supportImage (fun s => (poolLift (σ * τ) s).toEmbedding) A =
      supportImage (fun s => (poolLift σ s).toEmbedding)
        (supportImage (fun s => (poolLift τ s).toEmbedding) A) := by
  refine Finset.ext fun v => ?_
  rw [mem_supportImage_iff, mem_supportImage_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨s, x⟩ := w
    refine ⟨Sigma.map id (fun s => ⇑(poolLift τ s)) ⟨s, x⟩,
      (mem_supportImage_iff _ _ _).mpr ⟨⟨s, x⟩, hw, rfl⟩, ?_⟩
    show (⟨s, poolLift σ s (poolLift τ s x)⟩ : Σ s : S.Srt, PoolVertex S s) =
      ⟨s, poolLift (σ * τ) s x⟩
    rw [poolLift_mul]
    rfl
  · rintro ⟨w, hw, rfl⟩
    rw [mem_supportImage_iff] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    obtain ⟨s, x⟩ := u
    refine ⟨⟨s, x⟩, hu, ?_⟩
    show (⟨s, poolLift (σ * τ) s x⟩ : Σ s : S.Srt, PoolVertex S s) =
      ⟨s, poolLift σ s (poolLift τ s x)⟩
    rw [poolLift_mul]
    rfl

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
@[simp] theorem mixedClusterLift_one (n : ℕ) :
    mixedClusterLift (S := S) 1 n = Equiv.refl _ :=
  Equiv.ext fun A => Subtype.ext (supportImage_poolLift_one A.1)

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
theorem mixedClusterLift_mul (σ τ : FinSuppPerm S) (n : ℕ) :
    mixedClusterLift (S := S) (σ * τ) n =
      (mixedClusterLift τ n).trans (mixedClusterLift σ n) :=
  Equiv.ext fun A => Subtype.ext (supportImage_poolLift_mul σ τ A.1)

/-! ### The action on the base -/

open scoped Classical in
/-- **The action on the Austin base**: the pooled latents move by the split lift, and each cluster
coordinate is re-read at the moved index and transported by `blockSpaceCongr`. A pinned definition
rather than an opaque field, so its laws are checkable. -/
noncomputable def austinBaseRelabel (σ : FinSuppPerm S) (n : ℕ) :
    AustinBaseSpace S n → AustinBaseSpace S n :=
  fun z => (pooledRankLatentRelabel (poolLift σ) n z.1,
    fun A => blockSpaceCongr (fun s => (poolLift σ s).toEmbedding) A.1
      (z.2 (mixedClusterLift σ n A)))

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
theorem measurable_austinBaseRelabel (σ : FinSuppPerm S) (n : ℕ) :
    Measurable (austinBaseRelabel (S := S) σ n) :=
  ((pooledRankLatentRelabel (poolLift σ) n).measurable.comp measurable_fst).prodMk
    (measurable_pi_lambda _ fun A =>
      (blockSpaceCongr (fun s => (poolLift σ s).toEmbedding) A.1).measurable.comp
        (measurable_snd.eval))

/-! ### The laws of the action

Note the **orientation**: `pooledRankLatentRelabel_comp` is contravariant (`Equiv.trans f g` applies
`f` first), so the action composes as `austinBaseRelabel (σ * τ) = austinBaseRelabel τ ∘
austinBaseRelabel σ`. -/

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
/-- **Pointwise cluster naturality**: relabeling the pooled structure and reading a cluster
coordinate is reading the moved cluster at the moved coordinate. Stated at the block coordinate so
that no fibre transport appears in the statement, and generically in the cluster index, so
genuinely mixed and all-spare indices are covered alike. -/
theorem pollingClusters_relabel (σ : FinSuppPerm S)
    (p : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)
    (A : MixedClusterIndex S n) (c : BlockIndexOver (PoolVertex S) A.1) :
    pollingClusters (Prod.map (RelStructure.relabel (poolLift σ))
        (pooledRankLatentRelabel (poolLift σ) n) p) A c =
      pollingClusters p (mixedClusterLift σ n A)
        (blockIndexCongr (fun s => (poolLift σ s).toEmbedding) A.1 c) := rfl

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
/-- **The one cast this development needs.** Reading a cluster coordinate at equal indices, with
the fibres identified by substituting the index equality and the coordinates compared as raw
relation coordinates. Isolated here deliberately: the alternative — weakening
`MixedClusterIndex`'s reducibility — would expose a substantive subtype's implementation globally
in order to solve a local elaboration problem. -/
private theorem cluster_eval_congr (z : ClusterSpace S n) {A B : MixedClusterIndex S n}
    (hAB : A = B) {c : BlockIndexOver (PoolVertex S) A.1}
    {d : BlockIndexOver (PoolVertex S) B.1} (hcd : (c.1 : RelCoord S (PoolVertex S)) = d.1) :
    z A c = z B d := by
  subst hAB
  exact congrArg (z A) (Subtype.ext hcd)

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
/-- Pointwise evaluation of the base action on a cluster coordinate: a `Bool`-valued identity, so
no dependent fibre appears. The bridge through which the function-level laws are proved. -/
theorem austinBaseRelabel_apply_cluster (σ : FinSuppPerm S) (n : ℕ) (z : AustinBaseSpace S n)
    (A : MixedClusterIndex S n) (c : BlockIndexOver (PoolVertex S) A.1) :
    (austinBaseRelabel σ n z).2 A c =
      z.2 (mixedClusterLift σ n A)
        (blockIndexCongr (fun s => (poolLift σ s).toEmbedding) A.1 c) := rfl

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
/-- **Identity law**, pointwise. -/
theorem austinBaseRelabel_apply_cluster_one (n : ℕ) (z : AustinBaseSpace S n)
    (A : MixedClusterIndex S n) (c : BlockIndexOver (PoolVertex S) A.1) :
    (austinBaseRelabel (S := S) 1 n z).2 A c = z.2 A c := by
  rw [austinBaseRelabel_apply_cluster]
  refine cluster_eval_congr z.2 (Subtype.ext (supportImage_poolLift_one A.1)) ?_
  show RelCoord.map (fun s => ⇑(poolLift (S := S) 1 s)) c.1 = c.1
  rw [show poolLift (S := S) 1 = fun _ => 1 from funext fun s => by rw [poolLift_one]; rfl]
  rfl

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
/-- **Composition law**, pointwise, in the contravariant orientation forced by
`pooledRankLatentRelabel_comp`. -/
theorem austinBaseRelabel_apply_cluster_mul (σ τ : FinSuppPerm S) (n : ℕ)
    (z : AustinBaseSpace S n) (A : MixedClusterIndex S n)
    (c : BlockIndexOver (PoolVertex S) A.1) :
    (austinBaseRelabel (S := S) (σ * τ) n z).2 A c =
      (austinBaseRelabel τ n (austinBaseRelabel σ n z)).2 A c := by
  rw [austinBaseRelabel_apply_cluster, austinBaseRelabel_apply_cluster,
    austinBaseRelabel_apply_cluster]
  refine cluster_eval_congr z.2 (Subtype.ext (supportImage_poolLift_mul σ τ A.1)) ?_
  show RelCoord.map (fun s => ⇑(poolLift (σ * τ) s)) c.1 =
    RelCoord.map (fun s => ⇑(poolLift σ s)) (RelCoord.map (fun s => ⇑(poolLift τ s)) c.1)
  rw [show (fun s => ⇑(poolLift (σ * τ) s)) =
      (fun s x => poolLift σ s (poolLift τ s x)) from
    funext fun s => funext fun x => by rw [poolLift_mul]; rfl]
  rfl

/-! ### The function-level laws -/

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
@[simp] theorem austinBaseRelabel_one (n : ℕ) :
    austinBaseRelabel (S := S) 1 n = id := by
  funext z
  refine Prod.ext ?_ ?_
  · show pooledRankLatentRelabel (poolLift (S := S) 1) n z.1 = z.1
    rw [show poolLift (S := S) 1 = fun _ => 1 from funext fun s => by rw [poolLift_one]; rfl,
      pooledRankLatentRelabel_one]
    rfl
  · funext A
    funext c
    exact austinBaseRelabel_apply_cluster_one n z A c

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
theorem austinBaseRelabel_mul (σ τ : FinSuppPerm S) (n : ℕ) :
    austinBaseRelabel (S := S) (σ * τ) n =
      austinBaseRelabel τ n ∘ austinBaseRelabel σ n := by
  funext z
  refine Prod.ext ?_ ?_
  · show pooledRankLatentRelabel (poolLift (σ * τ)) n z.1 =
      pooledRankLatentRelabel (poolLift τ) n (pooledRankLatentRelabel (poolLift σ) n z.1)
    rw [show poolLift (σ * τ) = fun s => poolLift σ s * poolLift τ s from
        funext fun s => poolLift_mul σ τ s,
      pooledRankLatentRelabel_comp]
    rfl
  · funext A
    funext c
    exact austinBaseRelabel_apply_cluster_mul σ τ n z A c

/-! ### The global naturality square, and the invariance it yields -/

variable (S n) in
open scoped Classical in
/-- The action on the pooled objects by the split lift. -/
noncomputable def pooledAction (σ : FinSuppPerm S) :
    RelStructure S (PoolVertex S) × PooledRankLatentSpace S n →
      RelStructure S (PoolVertex S) × PooledRankLatentSpace S n :=
  Prod.map (RelStructure.relabel (poolLift σ)) (pooledRankLatentRelabel (poolLift σ) n)

variable (S n) in
open scoped Classical in
/-- The action on the enriched objects: the representation coordinates move by `σ`, the auxiliary
base by `austinBaseRelabel`. -/
noncomputable def enrichedAction (σ : FinSuppPerm S) :
    EnrichedSpace S n → EnrichedSpace S n :=
  Prod.map (Prod.map (RelStructure.relabel σ.1) (rankLatentRelabel σ n)) (austinBaseRelabel σ n)

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
theorem measurable_enrichedAction (σ : FinSuppPerm S) (n : ℕ) :
    Measurable (enrichedAction S n σ) :=
  ((measurable_relabel σ.1).prodMap (rankLatentRelabel σ n).measurable).prodMap
    (measurable_austinBaseRelabel σ n)

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
theorem measurable_pooledAction (σ : FinSuppPerm S) (n : ℕ) :
    Measurable (pooledAction S n σ) :=
  (measurable_relabel (poolLift σ)).prodMap (pooledRankLatentRelabel (poolLift σ) n).measurable

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
/-- **One square for all four components.** Enriching after acting on the pooled objects is acting
on the enriched objects after enriching. The structure and pooled-latent components are
definitional, the clusters are `pollingClusters_relabel`, and the original latents are the split
corollary `restrictOriginalLatents_sumCongr`. An exact function equality. -/
theorem enrichedPollingMap_naturality (σ : FinSuppPerm S) (n : ℕ) :
    enrichedPollingMap ∘ pooledAction S n σ =
      enrichedAction S n σ ∘ (enrichedPollingMap (S := S) (n := n)) := by
  funext p
  dsimp only [Function.comp_apply, enrichedAction, pooledAction, enrichedPollingMap, Prod.map]
  refine Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_)
  · have h := congrFun (restrictOriginalLatents_sumCongr σ.1 n) p.2
    rw [rankLatentRelabel_eq_latentRelabelOver]
    exact h
  · funext A
    funext c
    exact pollingClusters_relabel σ p A c

open scoped Classical in
/-- **Exact invariance of the enriched law.** Nothing but `Measure.map_map`, the naturality square,
and the extension's own invariance — no almost-everywhere reasoning and no component rewriting. -/
theorem enrichedPollingLaw_map_enrichedAction {C : M.RankRepresentation n}
    (Q : PooledRankExtension C) (σ : FinSuppPerm S) :
    (enrichedPollingLaw Q).map (enrichedAction S n σ) = enrichedPollingLaw Q := by
  rw [enrichedPollingLaw,
    Measure.map_map (measurable_enrichedAction σ n) measurable_enrichedPollingMap,
    ← enrichedPollingMap_naturality σ n,
    ← Measure.map_map measurable_enrichedPollingMap (measurable_pooledAction σ n),
    show (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)).map
        (pooledAction S n σ) = Q.law from Q.invariant (poolLift σ)]

/-! ### The bundle

Compressing the enriched law drops the *original* rank-`n` latents, which are redundant: on the
image of `enrichedPollingMap` they are `restrictOriginalLatents` of the pooled array, so nothing is
lost and `map_original` recovers `C.P` from the pooled component alone. -/

open scoped Classical in
/-- Forget the redundant original-latent coordinate. -/
noncomputable def compressEnriched :
    EnrichedSpace S n → RelStructure S (Vinfinite S) × AustinBaseSpace S n :=
  fun q => (q.1.1, q.2)

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
theorem measurable_compressEnriched :
    Measurable (compressEnriched (S := S) (n := n)) :=
  (measurable_fst.fst).prodMk measurable_snd

open scoped Classical in
/-- **The base-extended law**: the representation's structure together with the Austin base, over
the existing signature. No synthetic relational signature is introduced, and the pooled real
latents remain real — they are never encoded as Boolean relation coordinates. -/
structure AustinEnrichedObject (C : M.RankRepresentation n) where
  /-- The joint law of the structure and the auxiliary base. -/
  law : Measure (RelStructure S (Vinfinite S) × AustinBaseSpace S n)
  /-- It is a probability measure. -/
  isProbabilityMeasure_law : IsProbabilityMeasure law
  /-- Its structure marginal is the exchangeable law. -/
  map_fst : law.map Prod.fst = (M.law : Measure (RelStructure S (Vinfinite S)))
  /-- **Recovery of the representation**: reading the structure together with the original-support
  latents of the pooled array returns `C.P` exactly. -/
  map_original :
    law.map (fun p => (p.1, restrictOriginalLatents S n p.2.1)) = C.P
  /-- Invariance under the diagonal action. -/
  invariant : ∀ σ : FinSuppPerm S,
    law.map (Prod.map (RelStructure.relabel σ.1) (austinBaseRelabel σ n)) = law
  /-- **Mutual** conditional independence of the whole rank-`n` block family given the base. -/
  mutualCondIndep :
    iCondIndepFun (MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × AustinBaseSpace S n → _) inferInstance)
      measurable_snd.comap_le
      (fun A : RankSupport S n => blockMap A.1 ∘ Prod.fst) law

open scoped Classical in
/-- The compressed observation, read directly on the pooled space. -/
noncomputable def pooledToEnrichedObject :
    RelStructure S (PoolVertex S) × PooledRankLatentSpace S n →
      RelStructure S (Vinfinite S) × AustinBaseSpace S n :=
  fun p => (restrictOriginal S p.1, (p.2, pollingClusters p))

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
theorem compressEnriched_comp_enrichedPollingMap :
    compressEnriched ∘ (enrichedPollingMap (S := S) (n := n)) = pooledToEnrichedObject := rfl

open scoped Classical in
omit [Countable S.Srt] in
theorem measurable_pooledToEnrichedObject :
    Measurable (pooledToEnrichedObject (S := S) (n := n)) :=
  ((measurable_restrict _).comp measurable_fst).prodMk
    (measurable_snd.prodMk measurable_pollingClusters)

open scoped Classical in
/-- **The bundle exists.** The law is the exact pushforward of the enriched polling law; the four
laws are transports of results already established, and the mutual conditional independence is the
unit-1 witness moved forward by the route-local transport rather than reproved. -/
noncomputable def austinEnrichedObject [Fintype S.Srt] {C : M.RankRepresentation n}
    (Q : PooledRankExtension C) (W : PooledPollingWitness C Q) :
    AustinEnrichedObject C where
  law := (enrichedPollingLaw Q).map compressEnriched
  isProbabilityMeasure_law := by
    haveI : IsProbabilityMeasure (enrichedPollingLaw Q) := inferInstance
    exact Measure.isProbabilityMeasure_map measurable_compressEnriched.aemeasurable
  map_fst := by
    haveI := C.isProbabilityMeasure_P
    rw [Measure.map_map measurable_fst measurable_compressEnriched,
      show (Prod.fst ∘ compressEnriched (S := S) (n := n)) = Prod.fst ∘ Prod.fst from rfl,
      ← Measure.map_map measurable_fst measurable_fst, enrichedPollingLaw_map_fst, C.map_fst]
  map_original := by
    haveI := C.isProbabilityMeasure_P
    have hm : Measurable (fun p : RelStructure S (Vinfinite S) × AustinBaseSpace S n =>
        (p.1, restrictOriginalLatents S n p.2.1)) :=
      measurable_fst.prodMk ((measurable_restrictOriginalLatents n).comp (measurable_snd.fst))
    rw [Measure.map_map hm measurable_compressEnriched, enrichedPollingLaw,
      Measure.map_map (hm.comp measurable_compressEnriched) measurable_enrichedPollingMap,
      show ((fun p : RelStructure S (Vinfinite S) × AustinBaseSpace S n =>
            (p.1, restrictOriginalLatents S n p.2.1)) ∘ compressEnriched) ∘
          (enrichedPollingMap (S := S) (n := n)) =
        Prod.map (RelStructure.restrict (originalVertex S))
          (latentRestrictOver (fun s => originalVertex S s) n) from rfl]
    exact Q.map_restrict_embedding (originalVertex S)
  invariant := fun σ => by
    rw [Measure.map_map ((measurable_relabel σ.1).prodMap (measurable_austinBaseRelabel σ n))
        measurable_compressEnriched,
      show (Prod.map (RelStructure.relabel σ.1) (austinBaseRelabel σ n) ∘
          compressEnriched (S := S) (n := n)) =
        compressEnriched ∘ enrichedAction S n σ from rfl,
      ← Measure.map_map measurable_compressEnriched (measurable_enrichedAction σ n),
      enrichedPollingLaw_map_enrichedAction Q σ]
  mutualCondIndep := by
    haveI := C.isProbabilityMeasure_P
    refine Austin.iCondIndepFun_of_map measurable_compressEnriched measurable_snd.comap_le
      (fun A : RankSupport S n => (measurable_blockMap A.1).comp measurable_fst) ?_
    have h := W.mutualCondIndep
    refine Austin.iCondIndepFun_congr_cond h ?_ _
    show MeasurableSpace.comap (pollingCond S n) inferInstance =
      (MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × AustinBaseSpace S n → _)
        inferInstance).comap compressEnriched
    rw [MeasurableSpace.comap_comp]
    rfl

/-! ### Adapter spaces

Introduced here only so that their standard-Borel structure is available and inferred rather than
assumed; their maps and commuting laws belong to the bundle that follows. Stated for an arbitrary
coherent basis — selecting one via `nonempty_coherentBasis` is what would introduce
`[Fintype S.Srt]`, and that is deliberately not done here. -/

/-- The lower-factor space extended by the Austin base. -/
abbrev EnrichedLowerSpace (B : CoherentBasis M) (m : ℕ) :=
  B.LowerFactorSpace m × AustinBaseSpace S m

/-- The boundary space at `A` extended by the Austin base. -/
abbrev EnrichedBoundarySpace (B : CoherentBasis M) (m : ℕ)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :=
  B.BoundarySpace A × AustinBaseSpace S m

instance (B : CoherentBasis M) (m : ℕ) :
    StandardBorelSpace (EnrichedLowerSpace B m) := inferInstance

instance (B : CoherentBasis M) (m : ℕ) (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    StandardBorelSpace (EnrichedBoundarySpace B m A) := inferInstance

/-! ### The adapter into the coherent-basis factor API

For an arbitrary coherent basis: selecting one via `nonempty_coherentBasis` is what would introduce
`[Fintype S.Srt]`, and that is deliberately not done here. The four commuting laws are exact, and
the last is the unit-2 regression for eventual exact truncation. -/

variable (B : CoherentBasis M)

/-- The lower factor, extended by the base. -/
noncomputable def enrichedLowerMap (m : ℕ) :
    RelStructure S (Vinfinite S) × AustinBaseSpace S m → EnrichedLowerSpace B m :=
  fun p => (B.lowerFactorMap m p.1, p.2)

/-- The boundary at `A`, extended by the base. -/
noncomputable def enrichedBoundaryMap (m : ℕ) (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    RelStructure S (Vinfinite S) × AustinBaseSpace S m → EnrichedBoundarySpace B m A :=
  fun p => (B.boundaryMap A p.1, p.2)

/-- The rank-`m` layer. The base is **not** attached: the layer is where the fresh rank-`m`
information lives, and the base is the lower-rank data it is read against. -/
noncomputable def enrichedLayerMap (m : ℕ) :
    RelStructure S (Vinfinite S) × AustinBaseSpace S m → B.RankLayerSpace m :=
  fun p => B.rankLayerMap m p.1

/-- The exact-anchor layer at `A`. -/
noncomputable def enrichedExactMap (m : ℕ) (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    RelStructure S (Vinfinite S) × AustinBaseSpace S m → B.ExactSpace A :=
  fun p => B.exactMap A p.1

omit [Countable S.Srt] [Countable S.Rel] in
/-- **First commuting law**: projecting the extended lower factor to the boundary, leaving the base
untouched, is the extended boundary map. -/
theorem lowerToBoundary_comp_enrichedLowerMap {m : ℕ}
    {A : Finset (Σ s : S.Srt, Vinfinite S s)} (hA : A.card = m) :
    Prod.map (B.lowerToBoundaryProjection hA) (id : AustinBaseSpace S m → _) ∘
        enrichedLowerMap B m = enrichedBoundaryMap B m A := rfl

omit [Countable S.Srt] [Countable S.Rel] in
/-- **Second commuting law**: the exact-anchor layer factors through the rank-`m` layer. -/
theorem rankLayerToExact_comp_enrichedLayerMap {m : ℕ}
    {A : Finset (Σ s : S.Srt, Vinfinite S s)} (hA : A.card = m) :
    B.rankLayerToExactProjection hA ∘ enrichedLayerMap B m = enrichedExactMap B m A := rfl

omit [Countable S.Srt] [Countable S.Rel] in
theorem measurable_enrichedLowerMap (m : ℕ) : Measurable (enrichedLowerMap B m) :=
  ((B.measurable_lowerFactorMap' m).comp measurable_fst).prodMk measurable_snd

omit [Countable S.Srt] [Countable S.Rel] in
theorem measurable_enrichedLayerMap (m : ℕ) : Measurable (enrichedLayerMap B m) :=
  (B.measurable_rankLayerMap m).comp measurable_fst

/-- **Third commuting law**: forgetting the auxiliary base from the joint lower/layer observation
returns the corresponding pushforward of `M.law`. The base carries no structural information — it
is the lower-rank randomness the structure is read against. -/
theorem map_forget_base {C : M.RankRepresentation n} (O : AustinEnrichedObject C) :
    (O.law.map fun p => ((enrichedLowerMap B n p).1, enrichedLayerMap B n p)) =
      (M.law : Measure (RelStructure S (Vinfinite S))).map
        fun X => (B.lowerFactorMap n X, B.rankLayerMap n X) := by
  haveI := O.isProbabilityMeasure_law
  have hjoint : Measurable fun X : RelStructure S (Vinfinite S) =>
      (B.lowerFactorMap n X, B.rankLayerMap n X) :=
    (B.measurable_lowerFactorMap' n).prodMk (B.measurable_rankLayerMap n)
  rw [show (fun p : RelStructure S (Vinfinite S) × AustinBaseSpace S n =>
        ((enrichedLowerMap B n p).1, enrichedLayerMap B n p)) =
      (fun X => (B.lowerFactorMap n X, B.rankLayerMap n X)) ∘ Prod.fst from rfl,
    ← Measure.map_map hjoint measurable_fst, O.map_fst]

/-- **The unit-2 regression for exact truncation**: recombining the lower and layer coordinates
through `lowerFactorSpaceSuccEquiv.symm` returns the rank-`(n+1)` lower-factor law, on the nose.

This is an equality of pushed measures with the auxiliary base **forgotten** and no
almost-everywhere weakening: an a.e. version, or one retaining a base coordinate, would not
constrain the successor construction where it has to be constrained. -/
theorem map_recombine {C : M.RankRepresentation n} (O : AustinEnrichedObject C) :
    ((O.law.map fun p => ((enrichedLowerMap B n p).1, enrichedLayerMap B n p)).map
        (B.lowerFactorSpaceSuccEquiv n).symm) =
      (M.law : Measure (RelStructure S (Vinfinite S))).map (B.lowerFactorMap (n + 1)) := by
  haveI := O.isProbabilityMeasure_law
  rw [map_forget_base B O,
    Measure.map_map (B.lowerFactorSpaceSuccEquiv n).symm.measurable
      ((B.measurable_lowerFactorMap' n).prodMk (B.measurable_rankLayerMap n)),
    show ((B.lowerFactorSpaceSuccEquiv n).symm ∘
        fun X => (B.lowerFactorMap n X, B.rankLayerMap n X)) =
      B.lowerFactorMap (n + 1) from funext fun X => by
        show (B.lowerFactorSpaceSuccEquiv n).symm
            (B.lowerFactorMap n X, B.rankLayerMap n X) = B.lowerFactorMap (n + 1) X
        rw [← B.lowerFactorSpaceSuccEquiv_lowerFactorMap n X,
          (B.lowerFactorSpaceSuccEquiv n).symm_apply_apply]]

end InfiniteRelExchangeableLaw

end RelSignature
