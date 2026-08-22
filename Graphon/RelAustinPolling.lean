/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelPooledAcceptance
import Graphon.RelPollingInfrastructure
import Graphon.ForMathlib.CondExpComap

/-!
# Pooled polling: the Austin route, unit 1 (R4 converse, #107, #197)

Route **A** (Austin) only. Nothing from the Kallenberg spine appears here, and nothing in this
module asserts that the two routes' outputs agree — they prove the same statement by different
means and will not produce canonically equal representations.

Austin's Proposition 3.12 (arXiv:0801.1698) runs its polling argument with finitely supported
swaps into a **spare vertex set**. The pooled carrier is exactly that spare set: `originalVertex`
and `poolVertex` are two disjoint embeddings of the original carrier into `PoolVertex`, and a
`PooledRankExtension` is invariant under the *full* pooled permutation family, so the swaps are
available without a finite-support or uniform-bound side condition.

## What this unit fixes

* `pollingObs` — the **concrete** polling observation, not an existential factor: the whole pooled
  rank-`n` latent array together with the structure read on the spare copy. Every latent index of
  `RankLatentIndex S n` has cardinality `< n`, so this is proper-subset data by construction and
  carries no rank-`n` block; the spare-copy structure is the poll. Conditioning on the whole joint
  object would make the conclusion vacuous, which is why the observation is pinned here rather
  than quantified over.
* `pooledBlock` — the rank-`n` block family, read through the canonical identification
  `pooledJointEquiv`. Reading it through `originalVertex` instead would be equally meaningful but
  would not transport *exactly*: composing two restrictions restricts along the composite
  embedding, which is not the identity, and the export below would acquire an irreducible
  reindexing. The spare copy still enters — through `pollingObs`, which is where the poll belongs.
* `PooledPollingWitness` — the obligations a polling argument must discharge, with the mutual
  conclusion as the load-bearing field.

## The mutual conclusion, and why pairwise would not do

The field is `iCondIndepFun` over the **entire** rank-`n` block family — mutual conditional
independence, not pairwise and not one-block-against-the-rest. That is Austin's actual conclusion,
and the weaker forms are genuinely weaker: the bipartite regression of #196 exhibits blocks that
are pairwise related in ways a family-level statement rules out, which is exactly why the battery
was built before either route was attempted.

## Transport

`PooledPollingWitness.iCondIndepFun_blockMap` moves the conclusion from `Q.law` to `C.P`. The
direction matters. `map_restrict_embedding` maps the pooled law *forward* onto `C.P` and is not
invertible, so this is **not** a pullback along a restriction; the transport runs along the
canonical measurable equivalence `pooledJointEquiv` and its **inverse** measure-preserving map,
whose law identity is `PooledRankExtension.map_poolVertexEquiv` — which is
`Q.map_restrict_embedding` at the canonical embedding. The gate theorem is therefore a compiled
proof dependency of the export, not a citation.

## Scope

* `[Fintype S.Srt]` is carried by this module, matching the polling/fixing-algebra stack it builds
  on. The pooled API itself remains countable-only; removing the hypothesis is a separate
  generalization and deliberately not attempted here.
* Rank zero is not this module's business. The successor at `n = 0` is supplied by
  `nonempty_rankRepresentation_one` together with `truncation_zero`, which is also what respects
  `stepKernel`'s deliberate lack of an `A = ∅` realization theorem.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

namespace InfiniteRelExchangeableLaw

variable {S : RelSignature} [Countable S.Srt] [Countable S.Rel]
  {M : InfiniteRelExchangeableLaw S} {n : ℕ}

attribute [local instance] RankRepresentation.isProbabilityMeasure_P

/-- **The conditioning σ-algebra may be replaced by an equal one**, for a family. The `CondIndepFun`
form is shared glue in `ForMathlib/CondIndepSup.lean`; this is its `iCondIndepFun` counterpart, kept
private until a second consumer appears. Needed because the conditioning algebra occurs in a
dependent position — the `≤` proof mentions it — so `rw` cannot reach it. -/
private theorem iCondIndepFun_congr_cond {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ι : Type*} {γ : ι → Type*} [∀ i, MeasurableSpace (γ i)] {Y : ∀ i, Ω → γ i}
    {m₁ m₂ : MeasurableSpace Ω} {h1 : m₁ ≤ mΩ} (h : iCondIndepFun m₁ h1 Y μ)
    (h12 : m₁ = m₂) (h2 : m₂ ≤ mΩ) : iCondIndepFun m₂ h2 Y μ := by
  subst h12
  exact h

/-! ### The polling observation -/

variable (S n) in
/-- The codomain of the polling observation: the pooled rank-`n` latent array together with a
structure on the spare copy. -/
abbrev PollingSpace :=
  PooledRankLatentSpace S n × RelStructure S (Vinfinite S)

variable (S n) in
/-- **The polling observation.** The whole pooled rank-`n` latent array — every index of which has
cardinality `< n`, hence is proper-subset data carrying no rank-`n` block — together with the
structure read on the **spare** copy of the carrier, which is the poll. Pinned concretely: an
arbitrary conditioning factor would make the mutual conclusion vacuous. -/
noncomputable def pollingObs :
    RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → PollingSpace S n :=
  fun p => (p.2, RelStructure.restrict (poolVertex S) p.1)

variable (S n) in
theorem measurable_pollingObs : Measurable (pollingObs S n) :=
  measurable_snd.prodMk ((measurable_restrict _).comp measurable_fst)

/-! ### The rank-`n` block family -/

/-- **The rank-`n` block family on the pooled space**, read through the canonical identification.
Indexed by the original rank-`n` supports, with a fixed codomain per index, which is what lets the
export below be an exact identification rather than a reindexing. -/
noncomputable def pooledBlock (A : RankSupport S n) :
    RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → BlockSpace (S := S) A.1 :=
  fun p => blockMap A.1 (pooledJointEquiv S n p).1

theorem measurable_pooledBlock (A : RankSupport S n) : Measurable (pooledBlock (S := S) (n := n) A) :=
  (measurable_blockMap A.1).comp ((pooledJointEquiv S n).measurable.fst)

omit [Countable S.Srt] [Countable S.Rel] in
/-- Composing the pooled block family with the inverse identification returns the block of the
original structure, on the nose. -/
theorem pooledBlock_comp_symm (A : RankSupport S n) :
    pooledBlock (S := S) (n := n) A ∘ (pooledJointEquiv S n).symm =
      blockMap A.1 ∘ Prod.fst := by
  funext p
  show blockMap A.1 (pooledJointEquiv S n ((pooledJointEquiv S n).symm p)).1 = _
  rw [MeasurableEquiv.apply_symm_apply]
  rfl

/-! ### The witness -/

variable [Fintype S.Srt]

/-- **What a polling argument must supply.** The mutual conditional independence of the *entire*
rank-`n` block family given the polling observation — Austin's Proposition 3.12 conclusion in this
setting. The observation is not a field: it is pinned by `pollingObs`, so that a witness cannot
discharge the obligation by conditioning on more than proper-subset and spare-pool data. -/
structure PooledPollingWitness (C : M.RankRepresentation n) (Q : PooledRankExtension C) where
  /-- **Mutual** conditional independence of the whole rank-`n` block family, given the polling
  observation. Pairwise independence, or one block against the rest, would not suffice. -/
  mutualCondIndep :
    iCondIndepFun (MeasurableSpace.comap (pollingObs S n) inferInstance)
      (measurable_pollingObs S n).comap_le
      (fun A : RankSupport S n => pooledBlock (S := S) (n := n) A)
      (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))

namespace PooledPollingWitness

variable {C : M.RankRepresentation n} {Q : PooledRankExtension C}

/-- **The exact consequence under `C.P`.** The rank-`n` blocks of the representation are mutually
conditionally independent given the polling observation transported to the original carrier.

The transport is along the canonical equivalence's **inverse** measure-preserving map, not along
the non-invertible restriction: `map_restrict_embedding` pushes the pooled law forward onto `C.P`,
and it is exactly that identity — through `map_poolVertexEquiv` and
`measurePreserving_pooledJointEquiv` — which makes the inverse measure preserving. The gate
theorem is a compiled dependency of this proof. -/
theorem iCondIndepFun_blockMap (W : PooledPollingWitness C Q) :
    iCondIndepFun
      (MeasurableSpace.comap (pollingObs S n ∘ (pooledJointEquiv S n).symm) inferInstance)
      ((measurable_pollingObs S n).comp (pooledJointEquiv S n).symm.measurable).comap_le
      (fun A : RankSupport S n => blockMap A.1 ∘ Prod.fst) C.P := by
  haveI := C.isProbabilityMeasure_P
  have hsymm : MeasurePreserving ((pooledJointEquiv S n).symm) C.P
      (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) :=
    MeasurePreserving.symm _ Q.measurePreserving_pooledJointEquiv
  have h := iCondIndepFun_comp_measurePreserving hsymm
    (measurable_pollingObs S n).comap_le
    (fun A : RankSupport S n => measurable_pooledBlock A) W.mutualCondIndep
  have hfam : (fun A : RankSupport S n =>
        pooledBlock (S := S) (n := n) A ∘ (pooledJointEquiv S n).symm) =
      fun A : RankSupport S n => blockMap A.1 ∘ Prod.fst :=
    funext fun A => pooledBlock_comp_symm A
  rw [hfam] at h
  exact iCondIndepFun_congr_cond h MeasurableSpace.comap_comp _

end PooledPollingWitness

end InfiniteRelExchangeableLaw

end RelSignature
