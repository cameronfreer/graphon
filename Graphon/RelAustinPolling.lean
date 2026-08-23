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
swaps into a **spare vertex set**. The pooled carrier is exactly that: `PoolVertex S s` is
`Vinfinite S s ⊕ Vinfinite S s`, with `originalVertex = Sum.inl` and `poolVertex = Sum.inr`, so the
two halves are disjoint definitionally; and a `PooledRankExtension` is invariant under the *full*
pooled permutation family, so the swaps carry no finite-support or uniform-bound side condition.

## The geometry, and a trap it sets

The observed blocks are confined to the **original** half: `originalBlock A` reads the block at
`supportImage (originalVertex S) A`, every vertex of which is a `Sum.inl`. The poll is confined to
supports containing at least one `Sum.inr`. The two families are therefore disjoint by
construction, which is the whole point — a block that could itself lie in the poll would make the
conditional independence say nothing.

Reading the blocks instead through the canonical identification `pooledJointEquiv` is tempting,
because it makes the transport to `C.P` an exact identification. It is **wrong here**:
`poolVertexEquiv` is a bijection `PoolVertex ≃ Vinfinite`, so blocks read through it range across
*both* summands rather than being confined to the original half, while the poll reads the spare
half — the two would overlap.

## The seam is an enriched law, not `C.P`

Austin's polling data must survive into the next law; forgetting it into a bare `C.P` statement
would discard exactly what the successor construction consumes. That data is the family of
**mixed** clusters — pooled rank-`n` blocks that are *not wholly original* — and not merely the
induced structure on the spare half. "Mixed" is exactly that negation: an all-spare support
qualifies, its original part being empty and therefore proper.

* `pollingClusters` — the mixed cluster observation, indexed by `MixedClusterIndex`: pooled
  rank-`n` supports containing at least one spare vertex, all-spare supports included. Each such
  support has a *proper* original part, since at least one of its `n` vertices is spare; for an
  all-spare support that part is empty, which is proper as well.
* `enrichedPollingLaw` — the pushforward of `Q.law` retaining the original structure and old
  latents together with the clusters.
* `enrichedPollingLaw_map_fst` — the first marginal is `C.P` exactly, proved through
  `Q.map_restrict_embedding (originalVertex S)`. The gate theorem is a compiled dependency here,
  not a citation.

The conditioning is pinned by `pollingCond`: the old latents together with the clusters. It is a
definition rather than a witness field, because an existential conditioning factor could be taken
to be the whole joint object and would make the conclusion vacuous. Every index of
`RankLatentIndex S n` has cardinality `< n`, so the latent half of the conditioning is
proper-subset data carrying no rank-`n` block.

## Scope

* `[Fintype S.Srt]` is carried by the witness, matching the polling/fixing-algebra stack it is to
  be built from. The pooled API itself remains countable-only; removing the hypothesis is a
  separate generalization and deliberately not attempted here.
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

/-! ### Weak union for conditional independence

The graphoid axiom this development turns on, and which neither Mathlib nor this repository has:
**if `X` is conditionally independent of `(Y, Z)` given `W`, and `W` is contained in `Z`, then `X`
is conditionally independent of `Y` given `Z` alone.** The containment `W ≤ Z` is what lets the
conclusion condition on exactly `Z` rather than on an unsimplified `W ⊔ Z`.

Kept **private**: one consumer. When #198 needs the same axiom it should move to `ForMathlib/`.

The proof is the standard one. The key step is that enlarging the conditioning from `W` to any
algebra between `W` and `Y ⊔ Z` does not change the conditional probability of an `X`-event —
proved by conditional-expectation uniqueness, with the product identity supplying the set
integrals. Applying that at `Y ⊔ Z` and at `Z`, and then peeling with the tower property, gives the
result. -/

private theorem condExp_eq_of_between {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {mW mX mYZ m : MeasurableSpace Ω}
    (hW : mW ≤ mΩ) (hm : m ≤ mΩ) (hWm : mW ≤ m) (hmYZ : m ≤ mYZ)
    {A : Set Ω} (hAX : MeasurableSet[mX] A) (hA : MeasurableSet[mΩ] A)
    (h : ∀ t1 t2, MeasurableSet[mX] t1 → MeasurableSet[mYZ] t2 →
      (μ⟦t1 ∩ t2 | mW⟧) =ᵐ[μ] (μ⟦t1 | mW⟧) * (μ⟦t2 | mW⟧)) :
    (μ⟦A | m⟧) =ᵐ[μ] (μ⟦A | mW⟧) := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm
    ((integrable_const (1 : ℝ)).indicator hA)
    (fun S _ _ => integrable_condExp.integrableOn)
    (fun S hSm _ => ?_)
    ((stronglyMeasurable_condExp.mono hWm).aestronglyMeasurable)).symm
  have hSamb : MeasurableSet[mΩ] S := hm _ hSm
  have hprod := h A S hAX (hmYZ _ hSm)
  -- the pull-out identity, integrated
  have hmulind : (μ⟦A | mW⟧) * S.indicator (fun _ => (1 : ℝ)) = S.indicator (μ⟦A | mW⟧) := by
    funext x
    by_cases hx : x ∈ S <;> simp [hx, Set.indicator_of_mem, Set.indicator_of_notMem]
  have hpull : μ[(μ⟦A | mW⟧) * S.indicator (fun _ => (1 : ℝ)) | mW]
      =ᵐ[μ] (μ⟦A | mW⟧) * (μ⟦S | mW⟧) :=
    condExp_mul_of_stronglyMeasurable_left stronglyMeasurable_condExp
      (by rw [hmulind]; exact integrable_condExp.indicator hSamb)
      ((integrable_const (1 : ℝ)).indicator hSamb)
  calc ∫ x in S, (μ⟦A | mW⟧) x ∂μ
      = ∫ x, ((μ⟦A | mW⟧) * S.indicator fun _ => (1 : ℝ)) x ∂μ := by
        rw [← integral_indicator hSamb]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ S <;> simp [hx, Set.indicator_of_mem, Set.indicator_of_notMem]
    _ = ∫ x, (μ[(μ⟦A | mW⟧) * S.indicator fun _ => (1 : ℝ) | mW]) x ∂μ :=
        (integral_condExp hW).symm
    _ = ∫ x, ((μ⟦A | mW⟧) * (μ⟦S | mW⟧)) x ∂μ := integral_congr_ae hpull
    _ = ∫ x, (μ⟦A ∩ S | mW⟧) x ∂μ := (integral_congr_ae hprod).symm
    _ = ∫ x, (A ∩ S).indicator (fun _ => (1 : ℝ)) x ∂μ := integral_condExp hW
    _ = ∫ x in S, A.indicator (fun _ => (1 : ℝ)) x ∂μ := by
        rw [integral_indicator (hA.inter hSamb), setIntegral_indicator hA, Set.inter_comm]

private theorem condIndep_weak_union {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {mW mX mY mZ : MeasurableSpace Ω}
    (hW : mW ≤ mΩ) (hX : mX ≤ mΩ) (hY : mY ≤ mΩ) (hZ : mZ ≤ mΩ) (hWZ : mW ≤ mZ)
    (h : CondIndep mW mX (mY ⊔ mZ) hW μ) :
    CondIndep mZ mX mY hZ μ := by
  have hYZ : mY ⊔ mZ ≤ mΩ := sup_le hY hZ
  rw [condIndep_iff _ _ _ hW hX hYZ] at h
  rw [condIndep_iff _ _ _ hZ hX hY]
  intro A B hA hB
  have hAamb : MeasurableSet[mΩ] A := hX _ hA
  have hBamb : MeasurableSet[mΩ] B := hY _ hB
  have hBYZ : MeasurableSet[mY ⊔ mZ] B := (le_sup_left : mY ≤ mY ⊔ mZ) _ hB
  -- the conditional probability of an `X`-event is the same at `W`, at `Z`, and at `Y ⊔ Z`
  have hZeq : (μ⟦A | mZ⟧) =ᵐ[μ] (μ⟦A | mW⟧) :=
    condExp_eq_of_between (mΩ := mΩ) hW hZ hWZ le_sup_right hA hAamb h
  have hYZeq : (μ⟦A | mY ⊔ mZ⟧) =ᵐ[μ] (μ⟦A | mW⟧) :=
    condExp_eq_of_between (mΩ := mΩ) hW hYZ (hWZ.trans le_sup_right) le_rfl hA hAamb h
  -- peel `B` off inside the larger algebra, then descend by the tower property
  have hpull : μ[(A ∩ B).indicator (fun _ => (1 : ℝ)) | mY ⊔ mZ]
      =ᵐ[μ] (μ⟦A | mW⟧) * B.indicator fun _ => (1 : ℝ) := by
    have hmul : ((A ∩ B).indicator fun _ => (1 : ℝ)) =
        (A.indicator fun _ => (1 : ℝ)) * B.indicator fun _ => (1 : ℝ) := by
      funext x
      by_cases hx : x ∈ A <;> by_cases hy : x ∈ B <;>
        simp [hx, hy, Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_inter_iff]
    rw [hmul]
    refine (condExp_mul_of_stronglyMeasurable_right
      (stronglyMeasurable_const.indicator hBYZ)
      ?_ ((integrable_const (1 : ℝ)).indicator hAamb)).trans ?_
    · rw [← hmul]; exact (integrable_const (1 : ℝ)).indicator (hAamb.inter hBamb)
    · exact Filter.EventuallyEq.mul hYZeq Filter.EventuallyEq.rfl
  have htower : (μ⟦A ∩ B | mZ⟧) =ᵐ[μ] μ[μ[(A ∩ B).indicator (fun _ => (1 : ℝ)) | mY ⊔ mZ] | mZ] :=
    (condExp_condExp_of_le le_sup_right hYZ).symm
  refine htower.trans ?_
  refine ((condExp_congr_ae hpull).trans ?_)
  refine (condExp_mul_of_stronglyMeasurable_left
    (stronglyMeasurable_condExp.mono hWZ)
    ?_ ((integrable_const (1 : ℝ)).indicator hBamb)).trans ?_
  · have hmulB : (μ⟦A | mW⟧) * B.indicator (fun _ => (1 : ℝ)) = B.indicator (μ⟦A | mW⟧) := by
      funext x
      by_cases hx : x ∈ B <;> simp [hx, Set.indicator_of_mem, Set.indicator_of_notMem]
    rw [hmulB]
    exact integrable_condExp.indicator hBamb
  · exact (Filter.EventuallyEq.mul hZeq.symm Filter.EventuallyEq.rfl)

/-! ### Blocks on the original half -/

open scoped Classical in
/-- **The rank-`n` block family on the original half.** Every vertex of
`supportImage (originalVertex S) A` is a `Sum.inl`, so this family is disjoint from the poll below
by construction. -/
noncomputable def originalBlock (A : RankSupport S n) :
    RelStructure S (PoolVertex S) × PooledRankLatentSpace S n →
      BlockSpaceOver (PoolVertex S) (supportImage (originalVertex S) A.1) :=
  fun p => blockMapOver _ p.1

open scoped Classical in
omit [Countable S.Srt] in
theorem measurable_originalBlock (A : RankSupport S n) :
    Measurable (originalBlock (S := S) (n := n) A) :=
  (measurable_blockMapOver _).comp measurable_fst

/-! ### The mixed clusters -/

open scoped Classical in
/-- **Mixed cluster indices**: pooled rank-`n` supports that are **not wholly original**, i.e.
containing at least one spare vertex. All-spare supports are included — "mixed" is the negation of
"wholly original", not a demand that both halves be met. The original part of such a support is a
*proper* subset of it, since at least one of its `n` vertices is spare, and for an all-spare
support that part is empty; this is the sense in which the clusters are indexed by proper original
subsets. -/
def MixedClusterIndex (S : RelSignature) (n : ℕ) :=
  {A : Finset (Σ s : S.Srt, PoolVertex S s) // A.card = n ∧ ∃ v ∈ A, Sum.isRight v.2}

open scoped Classical in
instance : Countable (MixedClusterIndex S n) := Subtype.countable

open scoped Classical in
/-- The cluster observation space. -/
abbrev ClusterSpace (S : RelSignature) (n : ℕ) :=
  (A : MixedClusterIndex S n) → BlockSpaceOver (PoolVertex S) A.1

open scoped Classical in
/-- **The mixed cluster observation** — the poll. Each coordinate is a pooled rank-`n` block that
is not wholly original; no coordinate is an original-half block, since every index carries a spare
vertex. -/
noncomputable def pollingClusters :
    RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → ClusterSpace S n :=
  fun p A => blockMapOver A.1 p.1

open scoped Classical in
omit [Countable S.Srt] in
theorem measurable_pollingClusters : Measurable (pollingClusters (S := S) (n := n)) :=
  measurable_pi_lambda _ fun A => (measurable_blockMapOver A.1).comp measurable_fst

/-! ### The enriched law -/

variable (S n) in
/-- The enriched observation space: the original structure and old latents, together with the
**auxiliary** polling data — the whole pooled rank-`n` latent array and the clusters.

The pooled latent array is carried *alongside* the original marginal rather than replacing it, so
the first component is untouched and `enrichedPollingLaw_map_fst` stays literally what it was. It
is needed because the peel permutations move original vertices into the spare half: an original
latent index is then sent to a mixed one, so the original latent array is **not** stable under
those permutations, while the pooled array is — they merely permute pooled indices among
themselves. Every pooled index still has cardinality `< n`, so no rank-`n` block is revealed. -/
abbrev EnrichedSpace :=
  (RelStructure S (Vinfinite S) × RankLatentSpace S n) ×
    (PooledRankLatentSpace S n × ClusterSpace S n)

open scoped Classical in
/-- **The enriched polling map**: restrict to the original half, and retain the poll. -/
noncomputable def enrichedPollingMap :
    RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → EnrichedSpace S n :=
  fun p => (Prod.map (restrictOriginal S) (restrictOriginalLatents S n) p, (p.2, pollingClusters p))

open scoped Classical in
theorem measurable_enrichedPollingMap : Measurable (enrichedPollingMap (S := S) (n := n)) :=
  (((measurable_restrict _).comp measurable_fst).prodMk
    ((measurable_restrictOriginalLatents n).comp measurable_snd)).prodMk
      (measurable_snd.prodMk measurable_pollingClusters)

open scoped Classical in
/-- **The enriched polling law.** Austin's polling data survives here: the clusters are retained
alongside the original structure and old latents, rather than being forgotten into a bare `C.P`
statement. -/
noncomputable def enrichedPollingLaw {C : M.RankRepresentation n} (Q : PooledRankExtension C) :
    Measure (EnrichedSpace S n) :=
  (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)).map
    enrichedPollingMap

open scoped Classical in
instance {C : M.RankRepresentation n} (Q : PooledRankExtension C) :
    IsProbabilityMeasure (enrichedPollingLaw Q) := by
  rw [enrichedPollingLaw]
  exact Measure.isProbabilityMeasure_map measurable_enrichedPollingMap.aemeasurable

open scoped Classical in
/-- **The enriched law refines the representation**: forgetting the clusters returns `C.P` exactly.
Proved through `Q.map_restrict_embedding` at the **original-vertex** embedding, so the pooled gate
theorem is a compiled dependency of everything downstream. -/
theorem enrichedPollingLaw_map_fst {C : M.RankRepresentation n} (Q : PooledRankExtension C) :
    (enrichedPollingLaw Q).map Prod.fst = C.P := by
  rw [enrichedPollingLaw, Measure.map_map measurable_fst measurable_enrichedPollingMap,
    show (Prod.fst ∘ enrichedPollingMap (S := S) (n := n)) =
      Prod.map (RelStructure.restrict (originalVertex S))
        (latentRestrictOver (fun s => originalVertex S s) n) from rfl]
  exact Q.map_restrict_embedding (originalVertex S)

/-! ### The conditioning -/

variable (S n) in
/-- **The polling conditioning**, pinned concretely: the whole pooled rank-`n` latent array
together with the mixed clusters — that is, the auxiliary component. Not a witness field: an
existential factor could be taken to be the whole joint object and would make the conclusion
vacuous.

Reading the *pooled* array rather than its original part is what makes the conditioning stable
under the permutations the peel uses; every index still has cardinality `< n`, so the latent half
carries no rank-`n` block. -/
noncomputable def pollingCond :
    EnrichedSpace S n → PooledRankLatentSpace S n × ClusterSpace S n :=
  fun q => q.2

variable (S n) in
theorem measurable_pollingCond : Measurable (pollingCond S n) := measurable_snd

/-! ### The witness -/

variable [Fintype S.Srt]

/-- **What the polling argument must supply**: mutual conditional independence of the *entire*
rank-`n` block family of the original structure, given the old latents and the mixed clusters,
under the enriched law.

`iCondIndepFun` over the whole family is Austin's Proposition 3.12 conclusion. Pairwise
independence, or one block against the rest, would be strictly weaker, and the adversarial battery
of #196 exists to keep that distinction honest. -/
structure PooledPollingWitness (C : M.RankRepresentation n) (Q : PooledRankExtension C) where
  /-- **Mutual** conditional independence of the whole rank-`n` block family. -/
  mutualCondIndep :
    iCondIndepFun (MeasurableSpace.comap (pollingCond S n) inferInstance)
      (measurable_pollingCond S n).comap_le
      (fun A : RankSupport S n => blockMap A.1 ∘ Prod.fst ∘ Prod.fst)
      (enrichedPollingLaw Q)

end InfiniteRelExchangeableLaw

end RelSignature
