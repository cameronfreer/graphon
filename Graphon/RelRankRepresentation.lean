/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRankLatents
import Graphon.RelObservationGeometry
import Graphon.RelLatentLocalization
import Graphon.RelEqualityPattern
import Graphon.RelInfiniteLaw

/-!
# The joint representation interface (R4 converse piece 3, #107)

The specification a rank-`n` representation must satisfy. **Interface only: no existence theorem
is proved or claimed here**, at any rank.

## Why the primitive is a coupling

The previous design took a map `RankLatentSpace n → LowerFactorSpace n` and *derived* the joint
law as a relatively independent joining over the intrinsic factor. That derivation is what failed:
it makes the latents conditionally independent of the structure given the intrinsic factor, so
when that factor is trivial the latents are independent of the array. Austin's random complete
bipartite graph `X_{uv} = z_u ⊕ z_v` (arXiv:0801.1698, §3.6) has trivial rank-2 factor and hidden
colours that are correlated with the array while individually unrecoverable from it, so no such
joining can represent it.

The primitive here is therefore the coupling `P` itself. The decoder direction is unchanged —
structure recovered *from* latents — which was never the problem.

## Local, and rank-truncated

Two further constraints, both load-bearing:

* **Recovery is local.** Global recovery of the whole lower factor from the whole latent cube
  would let a decoder read unrelated coordinates elsewhere in the universe, and would not descend
  to the eventual label-free kernels. Each block at `A` is recovered from `localLatents A`.
* **Screening is rank-truncated.** Higher-rank coordinates containing `A` legitimately share the
  latents at `A`, so screening a block from *all* higher ranks would be false. The rank-`n` block
  at `A` is screened from the other blocks of rank at most `n`.

## Staging: `U_A` is not in scope at rank `n`

For `A.card = n`, the coordinate `U_A` is absent from `RankLatentSpace S n` outright, since
`RankLatentIndex S n` ranges over supports of cardinality *strictly below* `n`
(`rankLatentIndex_ne_of_card_eq`). So `screening` may put the entire `RankLatentSpace S n` on the
far side without contradiction, and `B ⊆ A` within `RankLatentIndex n` automatically means
`B ⊊ A`. Kallenberg's Lemma 7.24 is staged the same way — its coupled array is truncated below
the working dimension, and the fresh uniforms enter only at the successor step, here supplied by
the `RankLatentSpace (n+1) ≃ᵐ RankLatentSpace n × (RankSupport S n → ℝ)` split.

## Acceptance tests

Two examples, each blind to the other's failure mode; a specification in this family needs both.

* **Bipartite colours** `X_{uv} = z_u ⊕ z_v` — *correlation*: hidden lower-rank latents may be
  correlated with the array while individually unrecoverable. This refutes factor-law coding, and
  passes here with `screening` non-vacuous, since the edge is a deterministic function of the two
  colours.
* **I.i.d. edges** `X_{uv} = U_{uv}` — *staging*: the top-rank latent is absent during screening
  and introduced only at randomization. The bipartite example cannot detect a rank off-by-one,
  because its edges use no rank-2 latent at all.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

variable {S : RelSignature}

/-- **The staging lemma**: at rank `n` the latent array carries no coordinate at a support of
cardinality `n`. This is why `screening` may place the whole of `RankLatentSpace S n` opposite the
rank-`n` block, and why `B ⊆ A` needs no separate properness side condition. -/
theorem rankLatentIndex_ne_of_card_eq {A : Finset (Σ s : S.Srt, Vinfinite S s)} {n : ℕ}
    (hA : A.card = n) (B : RankLatentIndex S n) : B.1 ≠ A := by
  intro h
  exact absurd B.2 (by rw [h, hA]; omega)

/-- Consequently a visible support at a rank-`n` set is a *proper* subset of it. -/
theorem rankLatentIndex_ssubset_of_card_eq {A : Finset (Σ s : S.Srt, Vinfinite S s)} {n : ℕ}
    (hA : A.card = n) (B : LocalLatentIndex A n) : B.1.1 ⊂ A :=
  ⟨B.2, fun h => rankLatentIndex_ne_of_card_eq hA B.1 (Finset.Subset.antisymm B.2 h)⟩

/-! ### Blocks of raw relation coordinates -/

open scoped Classical in
/-- Raw relation coordinates whose tagged support is exactly `A`. Raw coordinates, not basis
events: the eventual descent to label-free kernels is indexed by these. -/
@[reducible] def BlockIndex (A : Finset (Σ s : S.Srt, Vinfinite S s)) :=
  BlockIndexOver (Vinfinite S) A

open scoped Classical in
instance [Countable S.Rel] (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Countable (BlockIndex A) := Subtype.countable

open scoped Classical in
/-- The rank-`A` block of the structure. -/
abbrev BlockSpace (A : Finset (Σ s : S.Srt, Vinfinite S s)) := BlockIndex A → Bool

open scoped Classical in
/-- Read the block at `A` off a structure. -/
def blockMap (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    RelStructure S (Vinfinite S) → BlockSpace A := blockMapOver A

open scoped Classical in
theorem measurable_blockMap [Countable S.Rel] (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measurable (blockMap A) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-! ### The rank-truncated remainder -/

open scoped Classical in
/-- Coordinates of rank at most `n` other than those at `A`. The truncation is essential:
coordinates of rank above `n` that contain `A` legitimately share `A`'s latents, so screening
against them would be false. -/
@[reducible] def RestIndex (n : ℕ) (A : Finset (Σ s : S.Srt, Vinfinite S s)) :=
  RestIndexOver (Vinfinite S) n A

open scoped Classical in
instance [Countable S.Rel] (n : ℕ) (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Countable (RestIndex n A) := Subtype.countable

open scoped Classical in
/-- The remaining rank-`≤ n` structure. -/
abbrev RestSpace (n : ℕ) (A : Finset (Σ s : S.Srt, Vinfinite S s)) := RestIndex n A → Bool

open scoped Classical in
/-- **The rank-truncated remainder observation**: the other blocks of rank at most `n`, together
with the whole latent array — which at rank `n` contains no coordinate at `A`. -/
def restObservation (n : ℕ) (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    RelStructure S (Vinfinite S) × RankLatentSpace S n → RestSpace n A × RankLatentSpace S n :=
  restObservationOver n A

open scoped Classical in
theorem measurable_restObservation [Countable S.Rel] (n : ℕ)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) : Measurable (restObservation n A) :=
  (measurable_pi_lambda _ fun _ => measurable_fst.eval).prodMk measurable_snd

/-- Pushing an almost-everywhere equality of measurable sets forward along a measurable map. -/
private theorem ae_eq_map_of_preimage_ae_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {f : α → β} (hf : Measurable f) {s t : Set β}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (h : f ⁻¹' s =ᵐ[μ] f ⁻¹' t) :
    s =ᵐ[μ.map f] t := by
  rw [ae_eq_set] at h ⊢
  rw [Measure.map_apply hf (hs.diff ht), Measure.map_apply hf (ht.diff hs), Set.preimage_sdiff,
    Set.preimage_sdiff]
  exact h

/-! ### The specification -/

namespace InfiniteRelExchangeableLaw

universe u

variable {S : RelSignature.{u}}

open scoped Classical in
/-- **A joint rank-`n` representation.** The primitive is the coupling `P`, not a coding map.

Deliberately independent of `CoherentBasis`: the specification mentions only the law, the raw
relation coordinates, and the latent array. The refuted design was phrased against the basis and
its factor maps, and that dependence is part of what led it to a factor-law primitive.

**No existence theorem accompanies this definition, at any rank.** Whether a non-trivial
`RankRepresentation n` exists is the actual content of the converse, and is exactly what the
refuted `RankCoding` design mistook for a bookkeeping step. Constructing one is expected to need
a stationary extension to a fresh auxiliary vertex pool, transfer along that extension, and the
polling clusters of Austin's Proposition 3.12. -/
structure RankRepresentation [Countable S.Srt] [Countable S.Rel] (M : InfiniteRelExchangeableLaw S)
    (n : ℕ) where
  /-- The coupling of the structure with the rank-`n` latents. -/
  P : Measure (RelStructure S (Vinfinite S) × RankLatentSpace S n)
  /-- It is a probability measure. -/
  isProbabilityMeasure_P : IsProbabilityMeasure P
  /-- Its structure marginal is the law. -/
  map_fst : P.map Prod.fst = (M.law : Measure (RelStructure S (Vinfinite S)))
  /-- Its latent marginal is the i.i.d. source. -/
  map_snd : P.map Prod.snd = rankLatentSource S n
  /-- **Joint relabeling invariance**: a relabeling acts on both coordinates at once. -/
  invariant : ∀ σ : FinSuppPerm S,
    P.map (Prod.map (RelStructure.relabel σ.1) (rankLatentRelabel σ n)) = P
  /-- **Local recovery**: each block below rank `n` is a function of the latents visible at its
  own support — not of the latent array at large. -/
  lower_recovers : ∀ A : Finset (Σ s : S.Srt, Vinfinite S s), A.card < n →
    ∃ g : LocalLatentSpace A n → BlockSpace A, Measurable g ∧
      blockMap A ∘ Prod.fst =ᵐ[P] g ∘ localLatents A n ∘ Prod.snd
  /-- **Fixing completeness below the working rank**, whole-array form: every event of a fixing
  algebra at a support of cardinality `< n` has, modulo the coupling, a representative read off
  the latent array. This is a **one-sided, modulo-null** completeness property — the latents
  capture the fixing information, not conversely — and it is **not** an identification of the
  fixing σ-algebra with a latent σ-algebra. It is required only strictly below rank `n`: at
  `A.card = n` the missing fixing information is exactly what the fresh rank-`n` latent must
  encode, so demanding it there would reject valid successors. The **local-window** form,
  measurability for `localLatents A n ∘ Prod.snd`, is not a separate field: it is derived once,
  for every representation, by `lower_fixing_complete` through the relative Hewitt–Savage theorem
  for the source. -/
  fixing_complete : ∀ A : Finset (Σ s : S.Srt, Vinfinite S s), A.card < n →
    ∀ E, MeasurableSet[RelStructure.fixingAlgebra A] E →
      ∃ D : Set (RankLatentSpace S n), MeasurableSet D ∧ Prod.snd ⁻¹' D =ᵐ[P] Prod.fst ⁻¹' E
  /-- **Local screening-off**, rank-truncated: the rank-`n` block at `A` is conditionally
  independent of the other rank-`≤ n` blocks and the latent array, given the latents visible at
  `A`. Kallenberg's `X̃_A ⊥⊥_{ξ̂_A} (X ∖ X̃_A, ξ)` at the working rank. -/
  screening : ∀ A : Finset (Σ s : S.Srt, Vinfinite S s), A.card = n →
    CondIndepFun (MeasurableSpace.comap (localLatents A n ∘ Prod.snd) inferInstance)
      ((measurable_localLatents A n).comp measurable_snd).comap_le
      (blockMap A ∘ Prod.fst) (restObservation n A) P

/-! ### Derived local fixing completeness

The primitive field is whole-array; locality is a theorem. The route: transfer invariance of the
structure event to its latent representative through joint invariance and the exact fixing action
on the structure, localize on the source by
`rankLatentSource_exists_local_ae_eq_of_ae_invariant`, and pull the localized representative back
through `Prod.snd`. -/

namespace RankRepresentation

variable {M : InfiniteRelExchangeableLaw S} {n : ℕ} [Countable S.Srt] [Countable S.Rel]

/-- **Invariance transfer**: the latent representative of a fixing-invariant structure event is
almost surely invariant, under the source, for every permutation fixing `A`. -/
private theorem relabel_preimage_ae_eq_of_snd_preimage_ae_eq (R : M.RankRepresentation n)
    {A : Finset (Σ s : S.Srt, Vinfinite S s)} {E : Set (RelStructure S (Vinfinite S))}
    (hE : MeasurableSet[RelStructure.fixingAlgebra A] E) {D : Set (RankLatentSpace S n)}
    (hD : MeasurableSet D) (hDE : Prod.snd ⁻¹' D =ᵐ[R.P] Prod.fst ⁻¹' E)
    (σ : FinSuppPerm S) (hσ : SortwiseFixing A σ.1) :
    rankLatentRelabel σ n ⁻¹' D =ᵐ[rankLatentSource S n] D := by
  haveI := R.isProbabilityMeasure_P
  have hΦ : MeasurePreserving
      (Prod.map (RelStructure.relabel σ.1) (rankLatentRelabel σ n)) R.P R.P :=
    ⟨(measurable_relabel σ.1).prodMap (rankLatentRelabel σ n).measurable, R.invariant σ⟩
  have h1 := hΦ.quasiMeasurePreserving.preimage_ae_eq hDE
  rw [show Prod.map (RelStructure.relabel σ.1) (rankLatentRelabel σ n) ⁻¹' (Prod.fst ⁻¹' E) =
      Prod.fst ⁻¹' E from by
      show Prod.fst ⁻¹' (RelStructure.relabel σ.1 ⁻¹' E) = _
      rw [hE.2 σ.1 hσ]] at h1
  rw [← R.map_snd]
  exact ae_eq_map_of_preimage_ae_eq measurable_snd ((rankLatentRelabel σ n).measurable hD) hD
    (h1.trans hDE.symm)

/-- **Local fixing completeness**, derived: every event of a fixing algebra below rank `n` has,
modulo the coupling, a representative measurable for the local latent window at its support. -/
theorem lower_fixing_complete (R : M.RankRepresentation n)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) (hA : A.card < n)
    (E : Set (RelStructure S (Vinfinite S))) (hE : MeasurableSet[RelStructure.fixingAlgebra A] E) :
    ∃ E', MeasurableSet[MeasurableSpace.comap (localLatents A n ∘ Prod.snd) inferInstance] E' ∧
      Prod.fst ⁻¹' E =ᵐ[R.P] E' := by
  haveI := R.isProbabilityMeasure_P
  obtain ⟨D, hD, hDE⟩ := R.fixing_complete A hA E hE
  obtain ⟨D', ⟨U, hU, rfl⟩, hD'⟩ := rankLatentSource_exists_local_ae_eq_of_ae_invariant A hD
    fun σ hσ => relabel_preimage_ae_eq_of_snd_preimage_ae_eq R hE hD hDE σ hσ
  refine ⟨Prod.snd ⁻¹' (localLatents A n ⁻¹' U), ⟨U, hU, rfl⟩, ?_⟩
  have hqmp : Measure.QuasiMeasurePreserving
      (Prod.snd : RelStructure S (Vinfinite S) × RankLatentSpace S n → _)
      R.P (rankLatentSource S n) :=
    ⟨measurable_snd, R.map_snd ▸ Measure.AbsolutelyContinuous.rfl⟩
  exact hDE.symm.trans (hqmp.preimage_ae_eq hD'.symm)

/-- **Fixing completeness descends along truncation.** A representative of a fixing event below
rank `m` is local at its support, and every local latent coordinate at a support of cardinality
`< m` is already a rank-`m` coordinate, so the localized representative is a rank-`m` event. -/
theorem fixing_complete_of_map_truncate {m : ℕ} (h : m ≤ n) (R : M.RankRepresentation n)
    {P : Measure (RelStructure S (Vinfinite S) × RankLatentSpace S m)}
    (hP : R.P.map (Prod.map id (rankLatentProjection h)) = P)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) (hA : A.card < m)
    (E : Set (RelStructure S (Vinfinite S))) (hE : MeasurableSet[RelStructure.fixingAlgebra A] E) :
    ∃ D : Set (RankLatentSpace S m), MeasurableSet D ∧ Prod.snd ⁻¹' D =ᵐ[P] Prod.fst ⁻¹' E := by
  haveI := R.isProbabilityMeasure_P
  obtain ⟨E', ⟨U, hU, rfl⟩, hE'⟩ := R.lower_fixing_complete A (hA.trans_le h) E hE
  let ρ : RankLatentSpace S m → LocalLatentSpace A n := fun ω B =>
    ω ⟨B.1.1, (Finset.card_le_card B.2).trans_lt hA⟩
  have hρ : Measurable ρ := measurable_pi_lambda _ fun _ => measurable_pi_apply _
  refine ⟨ρ ⁻¹' U, hρ hU, ?_⟩
  subst hP
  refine ae_eq_map_of_preimage_ae_eq (measurable_id.prodMap (measurable_rankLatentProjection h))
    (measurable_snd (hρ hU)) (measurable_fst (RelStructure.fixingAlgebra_le A E hE)) ?_
  exact hE'.symm

end RankRepresentation

end InfiniteRelExchangeableLaw

/-! ### Fixing completeness of deterministic couplings -/

/-- A coupling in which the structure is a measurable function of the latent array is fixing
complete outright: the preimage of the structure event under that function is the representative,
with an exact rather than merely almost-sure identity on the graph. -/
theorem snd_preimage_ae_eq_fst_preimage_map_graph {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {F : α → β} (hF : Measurable F) {E : Set β}
    (hE : MeasurableSet E) :
    Prod.snd ⁻¹' (F ⁻¹' E) =ᵐ[μ.map fun ω => (F ω, ω)] Prod.fst ⁻¹' E :=
  ae_eq_map_of_preimage_ae_eq (hF.prodMk measurable_id) (measurable_snd (hF hE))
    (measurable_fst hE) (Filter.Eventually.of_forall fun _ => rfl)

end RelSignature
