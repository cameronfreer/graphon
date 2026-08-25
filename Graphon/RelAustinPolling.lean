/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelPooledAcceptance
import Graphon.ForMathlib.CondExpComap

/-!
# Pooled polling: the Austin route, unit 1 (R4 converse, #107, #197)

Route **A** (Austin) only. Nothing from the Kallenberg spine appears here, and nothing in this
module asserts that the two routes' outputs agree — they prove the same statement by different
means and will not produce canonically equal representations.

## What is Austin's here, and what is not

The **construction** follows Austin (arXiv:0801.1698): a spare vertex reservoir, mixed clusters
straddling it, and an enriched law that carries the polling data forward. `PoolVertex S s` is
`Vinfinite S s ⊕ Vinfinite S s`, with `originalVertex = Sum.inl` and `poolVertex = Sum.inr`, so the
two halves are disjoint definitionally, and a `PooledRankExtension` is invariant under the *full*
pooled permutation family.

The **conditional-independence engine is not Austin's**, and this module does not reprove his
Proposition 3.12. `RankRepresentation.screening` is a field — an inductive hypothesis assumed at
rank `n` — and its remainder already contains every other rank-`≤ n` block together with the whole
pooled latent array. Weak union converts that directly into the mutual statement, so the
tail-polling argument is not needed at this inductive stage and no tail machinery appears here.
Stating otherwise would credit this file with a theorem it does not contain.

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

/-- **The conditioning σ-algebra may be replaced by an equal one**, for a family. The
`CondIndepFun` form is shared glue in `ForMathlib/CondIndepSup.lean`; this is its `iCondIndepFun`
counterpart, private under the standing promotion rule. Needed because the conditioning algebra
occurs in a dependent position — the `≤` proof mentions it — so `rw` cannot reach it. -/
private theorem iCondIndepFun_congr_cond {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ι : Type*} {γ : ι → Type*} [∀ i, MeasurableSpace (γ i)] {Y : ∀ i, Ω → γ i}
    {m₁ m₂ : MeasurableSpace Ω} {h1 : m₁ ≤ mΩ} (h : iCondIndepFun m₁ h1 Y μ)
    (h12 : m₁ = m₂) (h2 : m₂ ≤ mΩ) : iCondIndepFun m₂ h2 Y μ := by
  subst h12
  exact h

/-! ### Weak union for conditional independence

The graphoid axiom this development turns on, and which neither Mathlib nor this repository has:
**if `X` is conditionally independent of `(Y, Z)` given `W`, and `W` is contained in `Z`, then `X`
is conditionally independent of `Y` given `Z` alone.** The containment `W ≤ Z` is what lets the
conclusion condition on exactly `Z` rather than on an unsimplified `W ⊔ Z`.

Kept **private** under the standing promotion rule: private at one consumer, extracted to
`ForMathlib/` once a second independent consumer exists.

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
the first component is untouched and `enrichedPollingLaw_map_fst` stays literally what it was. The pooled array is the right lower-rank factor because `Q.screening`'s remainder
`restObservationOver n A` already contains it in full, and weak union conditions on exactly that
factor. Every pooled index has cardinality `< n`, so no rank-`n` block is revealed. -/
abbrev EnrichedSpace :=
  (RelStructure S (Vinfinite S) × RankLatentSpace S n) ×
    (PooledRankLatentSpace S n × ClusterSpace S n)

open scoped Classical in
/-- **The enriched polling map**: restrict to the original half, and retain the poll. -/
noncomputable def enrichedPollingMap :
    RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → EnrichedSpace S n :=
  fun p => (Prod.map (restrictOriginal S) (restrictOriginalLatents S n) p, (p.2, pollingClusters p))

open scoped Classical in
omit [Countable S.Srt] in
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
omit [Countable S.Srt] [Countable S.Rel] in
theorem measurable_pollingCond : Measurable (pollingCond S n) := measurable_snd

/-! ### The source-level conditioning

Steps 1–4 of the construction run under `Q.law`, on the pooled space, and only the final descent
moves to the enriched law. `sourcePollingCond` is the conditioning read there, and it is the
*same* observation: `pollingCond ∘ enrichedPollingMap` is definitionally `sourcePollingCond`, so
no transport is needed to relate the two statements. -/

open scoped Classical in
/-- The polling conditioning read directly on the pooled space. -/
noncomputable def sourcePollingCond :
    RelStructure S (PoolVertex S) × PooledRankLatentSpace S n →
      PooledRankLatentSpace S n × ClusterSpace S n :=
  fun p => (p.2, pollingClusters p)

open scoped Classical in
omit [Countable S.Srt] in
theorem measurable_sourcePollingCond : Measurable (sourcePollingCond (S := S) (n := n)) :=
  measurable_snd.prodMk measurable_pollingClusters

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
/-- **The two conditionings agree**, definitionally: conditioning on the enriched law and
conditioning on the pooled law are the same observation composed with the enriching map. -/
theorem pollingCond_comp_enrichedPollingMap :
    pollingCond S n ∘ enrichedPollingMap = sourcePollingCond (S := S) (n := n) := rfl

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
/-- **Check 1**: the local conditioning at any pooled support is measurable from the source polling
conditioning — it is a coordinate projection of the pooled latent component. This is the `W ≤ Z`
hypothesis of weak union, discharged concretely rather than assumed. -/
theorem comap_localLatents_le_sourcePollingCond (A : Finset (Σ s : S.Srt, PoolVertex S s)) :
    MeasurableSpace.comap
        (localLatentsOver A n ∘ (Prod.snd :
          RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → _)) inferInstance ≤
      MeasurableSpace.comap (sourcePollingCond (S := S) (n := n)) inferInstance := by
  rw [show (localLatentsOver A n ∘ (Prod.snd :
        RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → _)) =
      (localLatentsOver A n ∘ Prod.fst) ∘ sourcePollingCond from rfl,
    ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono
    ((measurable_localLatentsOver A n).comp measurable_fst).comap_le

/-! ### What the screening remainder supplies

`Q.screening` gives conditional independence of the block at a pooled support `A` from
`restObservationOver n A` — the other rank-`≤ n` blocks together with the whole pooled latent
array. Weak union needs that remainder to dominate *both* the accumulated `F`-blocks and the whole
polling conditioning. `restToPollingData` exhibits that as a single measurable factorization rather
than as a bare algebra inequality, so it records exactly which information the remainder supplies
and lets `CondIndepFun.comp` consume the screening statement directly. -/

open scoped Classical in
omit [Countable S.Rel] in
/-- A support in the image of the original half carries no spare vertex. -/
theorem isRight_eq_false_of_mem_supportImage_original
    {X : Finset (Σ s : S.Srt, Vinfinite S s)} {v : Σ s : S.Srt, PoolVertex S s}
    (hv : v ∈ supportImage (originalVertex S) X) : Sum.isRight v.2 = false := by
  obtain ⟨w, -, rfl⟩ := (mem_supportImage_iff _ _ _).mp hv
  rfl

open scoped Classical in
omit [Countable S.Rel] in
/-- **Separation, original against original**: distinct rank-`n` supports have distinct images,
since `supportImage` is injective. -/
theorem supportImage_ne_of_ne {B e : RankSupport S n} (h : B ≠ e) :
    supportImage (originalVertex S) B.1 ≠ supportImage (originalVertex S) e.1 :=
  fun heq => h (Subtype.ext (supportImage_injective _ heq))

open scoped Classical in
/-- **Separation, cluster against original**: a mixed cluster carries a spare vertex, while the
image of an original support is wholly original. -/
theorem mixedCluster_ne_supportImage (Ac : MixedClusterIndex S n) (e : RankSupport S n) :
    Ac.1 ≠ supportImage (originalVertex S) e.1 := by
  obtain ⟨v, hv, hvr⟩ := Ac.2.2
  intro heq
  rw [heq] at hv
  rw [isRight_eq_false_of_mem_supportImage_original hv] at hvr
  exact absurd hvr (by simp)

open scoped Classical in
/-- The accumulated block observation space, indexed by a finite family of rank-`n` supports. -/
abbrev FBlockSpace (F : Finset (RankSupport S n)) :=
  (B : {x : RankSupport S n // x ∈ F}) →
    BlockSpaceOver (PoolVertex S) (supportImage (originalVertex S) B.1.1)

open scoped Classical in
/-- **The screening remainder computes both sides of the weak-union hypothesis**: the accumulated
`F`-blocks and the entire polling conditioning are read off `restObservationOver n A` alone. -/
noncomputable def restToPollingData (e : RankSupport S n) (F : Finset (RankSupport S n))
    (heF : e ∉ F) :
    RestSpaceOver (PoolVertex S) n (supportImage (originalVertex S) e.1) ×
        PooledRankLatentSpace S n →
      FBlockSpace F × (PooledRankLatentSpace S n × ClusterSpace S n) :=
  fun q =>
    (fun B c => q.1 ⟨c.1, by
        refine ⟨?_, ?_⟩
        · rw [c.2, card_supportImage]; exact le_of_eq B.1.2
        · rw [c.2]; exact supportImage_ne_of_ne fun h => heF (h ▸ B.2)⟩,
      (q.2, fun Ac c => q.1 ⟨c.1, by
        refine ⟨?_, ?_⟩
        · rw [c.2]; exact le_of_eq Ac.2.1
        · rw [c.2]; exact mixedCluster_ne_supportImage Ac e⟩))

open scoped Classical in
theorem measurable_restToPollingData (e : RankSupport S n) (F : Finset (RankSupport S n))
    (heF : e ∉ F) : Measurable (restToPollingData e F heF) :=
  (measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ => measurable_fst.eval).prodMk
    (measurable_snd.prodMk
      (measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ => measurable_fst.eval))

open scoped Classical in
/-- **The exact factorization.** Both the accumulated blocks and the polling conditioning are
functions of the screening remainder, on the nose. -/
theorem restToPollingData_comp (e : RankSupport S n) (F : Finset (RankSupport S n)) (heF : e ∉ F) :
    (fun p : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n =>
        ((fun B : {x : RankSupport S n // x ∈ F} => originalBlock B.1 p), sourcePollingCond p)) =
      restToPollingData e F heF ∘ restObservationOver n (supportImage (originalVertex S) e.1) :=
  rfl

/-! ### The conditioning algebra is the fixed one

Named rather than left to `simp`: the forward descent at the end of the construction has to be
visibly exact, and that requires an explicit identity between the algebra the source statement
conditions on and the pullback of `pollingCond`. -/

open scoped Classical in
omit [Countable S.Srt] [Countable S.Rel] in
/-- **Check 3**: the source conditioning algebra *is* the pullback of the enriched conditioning. -/
theorem comap_pollingCond_comp_enrichedPollingMap :
    MeasurableSpace.comap (pollingCond S n ∘ enrichedPollingMap) inferInstance =
      MeasurableSpace.comap (sourcePollingCond (S := S) (n := n)) inferInstance :=
  congrArg (fun f => MeasurableSpace.comap f inferInstance) pollingCond_comp_enrichedPollingMap

/-! ### The insertion identity

The peel step, assembled from the pieces above: `Q.screening` at the original image of `e`, its
remainder pushed through `restToPollingData`, `comap_prodMk` to split the resulting algebra into
the accumulated blocks joined with the polling conditioning, and weak union to drop back to the
polling conditioning alone. Stated as a direct conditional-expectation identity so that it feeds
`Finset.induction_on` with `Set.biInter_insert` and `Finset.prod_insert`, without any dependent
tuple reindexing inside the induction. -/

open scoped Classical in
private theorem polling_condExp_insert {C : M.RankRepresentation n} (Q : PooledRankExtension C)
    (e : RankSupport S n) (F : Finset (RankSupport S n)) (heF : e ∉ F)
    (sets : ∀ A : RankSupport S n,
      Set (BlockSpaceOver (PoolVertex S) (supportImage (originalVertex S) A.1)))
    (hsets : ∀ A, A ∈ insert e F → MeasurableSet (sets A)) :
    ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        originalBlock e ⁻¹' sets e ∩ ⋂ A ∈ F, originalBlock A ⁻¹' sets A |
        MeasurableSpace.comap (sourcePollingCond (S := S) (n := n)) inferInstance⟧)
      =ᵐ[(Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))]
    ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        originalBlock e ⁻¹' sets e |
        MeasurableSpace.comap (sourcePollingCond (S := S) (n := n)) inferInstance⟧) *
      ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        ⋂ A ∈ F, originalBlock A ⁻¹' sets A |
        MeasurableSpace.comap (sourcePollingCond (S := S) (n := n)) inferInstance⟧) := by
  haveI := C.isProbabilityMeasure_P
  have hA₀ : (supportImage (originalVertex S) e.1).card = n := by
    rw [card_supportImage]; exact e.2
  -- the paired observation: accumulated blocks against the polling conditioning
  set Y : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → FBlockSpace F :=
    fun p B => originalBlock B.1 p with hY
  have hYmeas : Measurable Y :=
    measurable_pi_lambda _ fun B => measurable_originalBlock B.1
  -- screening, with its remainder pushed through the factorization
  have hcomp := (Q.screening (supportImage (originalVertex S) e.1) hA₀).comp
    (measurable_id (α := BlockSpaceOver (PoolVertex S) (supportImage (originalVertex S) e.1)))
    (measurable_restToPollingData e F heF)
  rw [condIndepFun_iff_condIndep] at hcomp
  have hpair : (restToPollingData e F heF ∘
      restObservationOver n (supportImage (originalVertex S) e.1)) =
      fun p => (Y p, sourcePollingCond p) := (restToPollingData_comp e F heF).symm
  rw [hpair, show (Prod.instMeasurableSpace :
      MeasurableSpace (FBlockSpace F × (PooledRankLatentSpace S n × ClusterSpace S n))) =
        MeasurableSpace.prod _ _ from rfl,
    MeasurableSpace.comap_prodMk] at hcomp
  -- weak union: drop the accumulated blocks out of the conditioning
  have hwu := condIndep_weak_union
    (((measurable_localLatentsOver (supportImage (originalVertex S) e.1) n).comp
      measurable_snd).comap_le)
    ((measurable_id.comp (measurable_originalBlock e)).comap_le)
    hYmeas.comap_le (measurable_sourcePollingCond (S := S) (n := n)).comap_le
    (comap_localLatents_le_sourcePollingCond (supportImage (originalVertex S) e.1)) hcomp
  -- read off the event identity
  rw [condIndep_iff _ _ _ (measurable_sourcePollingCond (S := S) (n := n)).comap_le
    ((measurable_id.comp (measurable_originalBlock e)).comap_le) hYmeas.comap_le] at hwu
  refine hwu _ _ ⟨sets e, hsets e (Finset.mem_insert_self _ _), rfl⟩ ?_
  refine MeasurableSet.biInter F.countable_toSet fun A hA => ?_
  exact ⟨(fun x : FBlockSpace F => x ⟨A, hA⟩) ⁻¹' sets A,
    (measurable_pi_apply _) (hsets A (Finset.mem_insert_of_mem hA)), rfl⟩

/-! ### The source-level mutual theorem

Named rather than inlined into the witness: it is the load-bearing consumer of
`polling_condExp_insert` and the direct input to the forward descent, so keeping it separate makes
it independently reviewable and leaves the final constructor carrying no probability argument of
its own. -/

open scoped Classical in
/-- **Mutual conditional independence of the whole rank-`n` block family under `Q.law`**, given the
polling conditioning. The peel is structurally the singleton peel: the empty stage is a constant,
and each insertion is discharged by `polling_condExp_insert` against the induction hypothesis, with
the conditioning algebra fixed throughout. -/
theorem PooledRankExtension.iCondIndepFun_originalBlock_sourcePollingCond
    {C : M.RankRepresentation n} (Q : PooledRankExtension C) :
    iCondIndepFun (MeasurableSpace.comap (sourcePollingCond (S := S) (n := n)) inferInstance)
      (measurable_sourcePollingCond (S := S) (n := n)).comap_le
      (fun A : RankSupport S n => originalBlock (S := S) (n := n) A)
      (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) := by
  haveI := C.isProbabilityMeasure_P
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul _ _
    fun A => measurable_originalBlock (S := S) (n := n) A]
  intro T sets
  induction T using Finset.induction_on with
  | empty =>
      intro _
      simp only [Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ, Finset.prod_empty,
        Set.indicator_univ]
      rw [condExp_const (measurable_sourcePollingCond (S := S) (n := n)).comap_le (1 : ℝ)]
      rfl
  | insert e F heF ih =>
      intro hsets
      have ihs := ih fun A hA => hsets A (Finset.mem_insert_of_mem hA)
      rw [Finset.set_biInter_insert, Finset.prod_insert heF]
      exact (polling_condExp_insert Q e F heF sets hsets).trans
        (Filter.EventuallyEq.mul Filter.EventuallyEq.rfl ihs)

/-! ### Transport to the enriched law

Two obligations, both discharged by named identities so that nothing is coerced ad hoc inside the
witness constructor: the conditioning algebra (check 3) and the block **codomains**. The source
family lands in `BlockSpaceOver (PoolVertex S) (supportImage (originalVertex S) A)`, whereas the
witness reads `blockMap A` on the restricted original structure; `blockSpaceCongr` is the
measurable equivalence between them and `blockMapOver_restrict` is the naturality that relates the
two readings exactly. -/

/-- Familywise composition on the codomain, the `iCondIndepFun` counterpart of `CondIndepFun.comp`
and built the same way, from the kernel-level lemma. Private under the standing promotion rule. -/
private theorem iCondIndepFun_comp {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {m' : MeasurableSpace Ω} {hm' : m' ≤ mΩ}
    {ι : Type*} {β γ : ι → Type*} [∀ i, MeasurableSpace (β i)] [∀ i, MeasurableSpace (γ i)]
    {f : ∀ i, Ω → β i} (h : iCondIndepFun m' hm' f μ)
    (φ : ∀ i, β i → γ i) (hφ : ∀ i, Measurable (φ i)) :
    iCondIndepFun m' hm' (fun i => φ i ∘ f i) μ :=
  Kernel.iIndepFun.comp h φ hφ

open scoped Classical in
omit [Countable S.Srt] in
/-- **The block codomains agree, exactly.** Reading a block of the restricted original structure is
reading the pooled block at the image support and transporting along `blockSpaceCongr`. -/
theorem enrichedBlock_comp_enrichedPollingMap (A : RankSupport S n) :
    ((blockMap A.1 ∘ Prod.fst ∘ Prod.fst) ∘ enrichedPollingMap :
      RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → BlockSpace (S := S) A.1) =
      blockSpaceCongr (originalVertex S) A.1 ∘ originalBlock (S := S) (n := n) A := by
  funext p
  exact congrFun (blockMapOver_restrict (originalVertex S) A.1) p.1

/-- **Forward transport of mutual conditional independence along a measurable map.** Brought in
privately, adjacent to its one consumer, under the standing promotion rule; the general form is
proved and preserved on its own branch and moves to `ForMathlib/` when a second independent
consumer exists. No injectivity is needed — `enrichedPollingMap` forgets the spare half of the
structure — which is exactly why neither direction of the existing transport API applies. -/
private theorem iCondIndepFun_of_map {α β : Type*} {m' : MeasurableSpace β}
    [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    [StandardBorelSpace α] [StandardBorelSpace β]
    {P : Measure α} [IsFiniteMeasure P] {T : α → β}
    (hT : Measurable T) (hm' : m' ≤ mβ)
    {ι : Type*} {γ : ι → Type*} [mγ : ∀ i, MeasurableSpace (γ i)] {Y : ∀ i, β → γ i}
    (hY : ∀ i, Measurable (Y i))
    (h : iCondIndepFun (m'.comap T)
      ((MeasurableSpace.comap_mono hm').trans (measurable_iff_comap_le.mp hT))
      (fun i => Y i ∘ T) P) :
    iCondIndepFun m' hm' Y (P.map T) := by
  haveI : IsFiniteMeasure (P.map T) := Measure.isFiniteMeasure_map P T
  have hTmp : MeasurePreserving T P (P.map T) := ⟨hT, rfl⟩
  have key : ∀ E : Set β, MeasurableSet E →
      (P⟦T ⁻¹' E | m'.comap T⟧) =ᵐ[P] ((P.map T)⟦E | m'⟧) ∘ T :=
    fun _ hE => condExp_set_comp_measurePreserving hTmp hm' hE
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul _ _ hY]
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul _ _ fun i => (hY i).comp hT] at h
  intro S sets hsets
  have hsrc := h S hsets
  have hinter : MeasurableSet (⋂ i ∈ S, Y i ⁻¹' sets i) :=
    MeasurableSet.biInter S.countable_toSet fun i hi => (hY i) (hsets i hi)
  have hpre : ⋂ i ∈ S, (Y i ∘ T) ⁻¹' sets i = T ⁻¹' ⋂ i ∈ S, Y i ⁻¹' sets i := by
    simp [Set.preimage_comp, Set.preimage_iInter]
  rw [hpre] at hsrc
  have h₁ := key _ hinter
  have hfac : ∀ᵐ x ∂P, ∀ i ∈ S, (P⟦(Y i ∘ T) ⁻¹' sets i | m'.comap T⟧) x
      = (((P.map T)⟦Y i ⁻¹' sets i | m'⟧) ∘ T) x := by
    refine (ae_ball_iff S.countable_toSet).2 fun i hi => ?_
    rw [Set.preimage_comp]
    exact key _ ((hY i) (hsets i hi))
  have hcomp : ((P.map T)⟦⋂ i ∈ S, Y i ⁻¹' sets i | m'⟧) ∘ T
      =ᵐ[P] (∏ i ∈ S, ((P.map T)⟦Y i ⁻¹' sets i | m'⟧)) ∘ T := by
    filter_upwards [h₁, hsrc, hfac] with x e₁ esrc efac
    simp only [Function.comp_apply] at e₁ ⊢
    rw [← e₁, esrc]
    show (∏ i ∈ S, (P⟦(Y i ∘ T) ⁻¹' sets i | m'.comap T⟧)) x = _
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl fun i hi => efac i hi
  have hmeas : MeasurableSet {y : β | ((P.map T)⟦⋂ i ∈ S, Y i ⁻¹' sets i | m'⟧) y =
      (∏ i ∈ S, ((P.map T)⟦Y i ⁻¹' sets i | m'⟧)) y} := by
    refine measurableSet_eq_fun (stronglyMeasurable_condExp.mono hm').measurable ?_
    have heq : (∏ i ∈ S, ((P.map T)⟦Y i ⁻¹' sets i | m'⟧)) =
        fun y : β => ∏ i ∈ S, ((P.map T)⟦Y i ⁻¹' sets i | m'⟧) y :=
      funext fun y => Finset.prod_apply y S _
    rw [heq]
    exact Finset.measurable_prod S fun i _ => (stronglyMeasurable_condExp.mono hm').measurable
  exact (ae_map_iff hT.aemeasurable hmeas).mpr hcomp

/-! ### The witness -/

variable [Fintype S.Srt]

/-- **The polling conclusion**: mutual conditional independence of the *entire* rank-`n` block
family of the original structure, given the pooled latents and the mixed clusters, under the
enriched law.

`iCondIndepFun` over the whole family is the shape Austin's Proposition 3.12 delivers, but here it
is obtained from the assumed rank-`n` screening contract by weak union rather than by a tail-polling
argument. Pairwise independence, or one block against the rest, would be strictly weaker, and the
adversarial battery of #196 exists to keep that distinction honest. -/
structure PooledPollingWitness (C : M.RankRepresentation n) (Q : PooledRankExtension C) where
  /-- **Mutual** conditional independence of the whole rank-`n` block family. -/
  mutualCondIndep :
    iCondIndepFun (MeasurableSpace.comap (pollingCond S n) inferInstance)
      (measurable_pollingCond S n).comap_le
      (fun A : RankSupport S n => blockMap A.1 ∘ Prod.fst ∘ Prod.fst)
      (enrichedPollingLaw Q)

open scoped Classical in
/-- **The polling witness exists**, for every pooled rank extension. Pure transport: the
probability content is `iCondIndepFun_originalBlock_sourcePollingCond`, and this constructor only
moves it along `enrichedPollingMap`, matching the block codomains by `blockSpaceCongr` and the
conditioning algebra by the named identity. -/
noncomputable def pooledPollingWitness {C : M.RankRepresentation n} (Q : PooledRankExtension C) :
    PooledPollingWitness C Q where
  mutualCondIndep := by
    haveI := C.isProbabilityMeasure_P
    -- step 1: transport the codomains
    have h1 := iCondIndepFun_comp Q.iCondIndepFun_originalBlock_sourcePollingCond
      (fun A : RankSupport S n => (blockSpaceCongr (originalVertex S) A.1 : _ → _))
      fun A => (blockSpaceCongr (originalVertex S) A.1).measurable
    -- step 2: read the transported family as the enriched blocks precomposed with the map
    have h2 : (fun A : RankSupport S n =>
        (blockSpaceCongr (originalVertex S) A.1 : _ → _) ∘ originalBlock (S := S) (n := n) A) =
        fun A : RankSupport S n =>
          (blockMap A.1 ∘ Prod.fst ∘ Prod.fst) ∘ enrichedPollingMap :=
      funext fun A => (enrichedBlock_comp_enrichedPollingMap A).symm
    rw [h2] at h1
    -- step 3: match the conditioning algebra to the pullback of the enriched one
    have halg : MeasurableSpace.comap (sourcePollingCond (S := S) (n := n)) inferInstance =
        (MeasurableSpace.comap (pollingCond S n) inferInstance).comap enrichedPollingMap :=
      (MeasurableSpace.comap_comp.trans comap_pollingCond_comp_enrichedPollingMap).symm
    have h3 := iCondIndepFun_congr_cond h1 halg
      ((MeasurableSpace.comap_mono (measurable_pollingCond S n).comap_le).trans
        (measurable_iff_comap_le.mp measurable_enrichedPollingMap))
    -- step 4: push forward
    exact iCondIndepFun_of_map measurable_enrichedPollingMap
      (measurable_pollingCond S n).comap_le
      (fun A : RankSupport S n =>
        (measurable_blockMap A.1).comp (measurable_fst.comp measurable_fst)) h3

end InfiniteRelExchangeableLaw

end RelSignature
