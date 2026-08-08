/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelPoolGeometry
import Graphon.RelRestrictionBlocks

/-!
# The stationary extension (R4 converse, #107)

Layer 2 of the approved contract: the extended law on the pooled carrier. The primitive is an
**extended law**, not an independent joining — the pool observations remain jointly distributed
with the original array through the same structure, and no relative-independence claim of any
kind is made (an independent pool would recreate the defect of the rejected factor coupling:
nothing correlated to offer).

## Contents

* `StationaryExtension` — the minimal structure: a probability law on the pooled structure
  space whose original restriction is the law and which is invariant under **every** sortwise
  permutation of the pooled carrier (mixed permutations included — the load-bearing
  quantifier);
* `StationaryExtension.law_map_restrict_window` — the **exact mixed-window marginal**: the
  restriction along any sortwise finite embedding into the pooled carrier has the rank-`n`
  marginal of the original law. The explicit acceptance test of the contract; this is what the
  polling and successor consumers cite;
* `StationaryExtension.extensionCoupling` with exact `map_fst` / `map_snd` — the induced
  coupling of the original restriction with the whole extended array. The shared-array property
  is definitional;
* `InfiniteRelExchangeableLaw.nonempty_stationaryExtension` — the **cheap existence theorem**:
  both summands together are again a countably infinite carrier, so the law transports along
  `poolVertexEquiv`. Existence is deliberately cheap and is *not* the induction step: the hard
  theorem is extracting correlated auxiliary latents with recovery and screening from an
  extension, and that theorem is not touched here.

All measure identities in this file are exact; nothing is almost-everywhere.
-/

open MeasureTheory

namespace RelSignature

universe u

variable {S : RelSignature.{u}}

/-! ### The stationary extension -/

/-- **A stationary extension of an exchangeable law**: a probability law on the pooled
structure space whose restriction to the original vertices is the law, invariant under
**every** sortwise permutation of the pooled carrier — mixed permutations included, which is
the load-bearing quantifier for polling.

Deliberately minimal. Latent recovery, screening, conditional independence, a coherent basis,
`RankRepresentation`, and any independence of the pool from the original array are all
**excluded**: they belong to the theorem extracting higher-rank latents from an extension, and
an independence clause would recreate the defect of the rejected relative-factor coupling. -/
structure StationaryExtension (M : InfiniteRelExchangeableLaw S) where
  /-- The extended law on the pooled structure space. -/
  law : ProbabilityMeasure (RelStructure S (PoolVertex S))
  /-- Its restriction to the original vertices is the law. -/
  map_restrictOriginal : (law : Measure (RelStructure S (PoolVertex S))).map
    (restrictOriginal S) = (M.law : Measure (RelStructure S (Vinfinite S)))
  /-- Invariance under every sortwise permutation of the pooled carrier — including
  permutations moving vertices between the original and pool halves. -/
  invariant : ∀ ρ : ∀ s, Equiv.Perm (PoolVertex S s),
    (law : Measure (RelStructure S (PoolVertex S))).map (RelStructure.relabel ρ) =
      (law : Measure (RelStructure S (PoolVertex S)))

namespace StationaryExtension

variable {M : InfiniteRelExchangeableLaw S} (E : StationaryExtension M)

/-- **The exact mixed-window marginal** — the contract's explicit acceptance test: the
restriction of the extension along **any** sortwise finite embedding into the pooled carrier —
windows mixing original and pool vertices freely — is the rank-`n` marginal of the original
law. Proof: a permutation of the pooled carrier moves the window into the original half
(`restrict_relabel`, the moved-window law), invariance absorbs it, and the original restriction
then computes the marginal by `law_map_restrict`. -/
theorem law_map_restrict_window {n : S.Srt → ℕ} (e : ∀ s, Fin (n s) ↪ PoolVertex S s) :
    (E.law : Measure (RelStructure S (PoolVertex S))).map (RelStructure.restrict e) =
      (M.law : Measure (RelStructure S (Vinfinite S))).map (RelStructure.restrictFin n) := by
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  -- a sortwise permutation of the pooled carrier moves the window into the original half
  have hmove : ∀ s, ∃ ρ : Equiv.Perm (PoolVertex S s),
      ∀ i : Fin (n s), ρ (e s i) = originalVertex S s (Fin.valEmbedding i) := by
    intro s
    obtain ⟨σf, hσf⟩ := exists_perm_extend ((e s).trans (poolVertexEquiv S s).toEmbedding)
    obtain ⟨σg, hσg⟩ := exists_perm_extend
      ((Fin.valEmbedding.trans (originalVertex S s)).trans (poolVertexEquiv S s).toEmbedding)
    refine ⟨(poolVertexEquiv S s).symm.permCongr (σf.symm.trans σg), fun i => ?_⟩
    have hf : σf.symm ((poolVertexEquiv S s) (e s i)) = (i : ℕ) :=
      σf.injective (by rw [Equiv.apply_symm_apply, hσf i]; rfl)
    apply (poolVertexEquiv S s).injective
    calc (poolVertexEquiv S s) ((poolVertexEquiv S s).symm.permCongr
          (σf.symm.trans σg) (e s i))
        = σg (σf.symm ((poolVertexEquiv S s) (e s i))) := by
          simp [Equiv.permCongr_apply]
      _ = σg (i : ℕ) := by rw [hf]
      _ = (poolVertexEquiv S s) (originalVertex S s (Fin.valEmbedding i)) := by
          rw [hσg i]; rfl
  choose ρ hρ using hmove
  have hwindow : (fun s => (e s).trans (ρ s).toEmbedding) =
      fun s => Fin.valEmbedding.trans (originalVertex S s) := by
    funext s
    ext i
    exact hρ s i
  rw [← E.invariant ρ,
    Measure.map_map (measurable_restrict e) (measurable_relabel ρ),
    show RelStructure.restrict (S := S) e ∘ RelStructure.relabel ρ =
      RelStructure.restrict (fun s => (e s).trans (ρ s).toEmbedding) from
        funext fun X => RelStructure.restrict_relabel e ρ X,
    hwindow,
    show RelStructure.restrict (S := S) (fun s => Fin.valEmbedding.trans (originalVertex S s)) =
      RelStructure.restrictFin n ∘ restrictOriginal S from rfl,
    ← Measure.map_map (RelSignature.measurable_restrictFin n) (measurable_restrictOriginal),
    E.map_restrictOriginal]

/-! ### The induced coupling -/

/-- **The induced coupling** of the original restriction with the whole extended array. The
shared-array property is definitional: both coordinates are read off the same structure. No
independence between them is claimed — that exclusion is the point of the design. -/
noncomputable def extensionCoupling :
    ProbabilityMeasure (RelStructure S (Vinfinite S) × RelStructure S (PoolVertex S)) :=
  ⟨(E.law : Measure (RelStructure S (PoolVertex S))).map fun X => (restrictOriginal S X, X),
    Measure.isProbabilityMeasure_map
      (measurable_restrictOriginal.prodMk measurable_id).aemeasurable⟩

/-- The first marginal of the induced coupling is the original law. Exact. -/
theorem extensionCoupling_map_fst :
    (E.extensionCoupling : Measure (RelStructure S (Vinfinite S) ×
        RelStructure S (PoolVertex S))).map Prod.fst =
      (M.law : Measure (RelStructure S (Vinfinite S))) := by
  rw [extensionCoupling, ProbabilityMeasure.coe_mk,
    Measure.map_map measurable_fst (measurable_restrictOriginal.prodMk measurable_id :
      Measurable fun X : RelStructure S (PoolVertex S) => (restrictOriginal S X, X)),
    show (Prod.fst ∘ fun X : RelStructure S (PoolVertex S) => (restrictOriginal S X, X)) =
      restrictOriginal S from rfl,
    E.map_restrictOriginal]

/-- The second marginal of the induced coupling is the extended law. Exact. -/
theorem extensionCoupling_map_snd :
    (E.extensionCoupling : Measure (RelStructure S (Vinfinite S) ×
        RelStructure S (PoolVertex S))).map Prod.snd =
      (E.law : Measure (RelStructure S (PoolVertex S))) := by
  rw [extensionCoupling, ProbabilityMeasure.coe_mk,
    Measure.map_map measurable_snd (measurable_restrictOriginal.prodMk measurable_id :
      Measurable fun X : RelStructure S (PoolVertex S) => (restrictOriginal S X, X)),
    show (Prod.snd ∘ fun X : RelStructure S (PoolVertex S) => (restrictOriginal S X, X)) =
      id from rfl,
    Measure.map_id]

end StationaryExtension

/-! ### The cheap existence theorem -/

open scoped Classical in
/-- **Every exchangeable law has a stationary extension** — deliberately cheap: both summands
together are again a countably infinite carrier, so the law transports along the fixed sortwise
identification. This is *not* the induction step. The hard theorem is extracting correlated
auxiliary latents with recovery and screening from an extension; nothing here touches it, and
mistaking this construction for progress on the induction would repeat the `RankCoding`
failure. -/
theorem InfiniteRelExchangeableLaw.nonempty_stationaryExtension
    (M : InfiniteRelExchangeableLaw S) : Nonempty (StationaryExtension M) := by
  classical
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  set T : RelStructure S (Vinfinite S) ≃ᵐ RelStructure S (PoolVertex S) :=
    RelStructure.congrCarrier (fun s => (poolVertexEquiv S s).symm) with hTdef
  refine ⟨⟨⟨(M.law : Measure (RelStructure S (Vinfinite S))).map T,
    Measure.isProbabilityMeasure_map T.measurable.aemeasurable⟩, ?_, ?_⟩⟩
  · -- the original restriction of the transported law is the law
    rw [ProbabilityMeasure.coe_mk,
      Measure.map_map measurable_restrictOriginal T.measurable,
      show restrictOriginal S ∘ ⇑T = RelStructure.restrict
        (fun s => (originalVertex S s).trans (poolVertexEquiv S s).toEmbedding) from rfl,
      M.law_map_restrict_self fun s => (originalVertex S s).trans (poolVertexEquiv S s).toEmbedding]
  · -- invariance under every sortwise permutation of the pooled carrier
    intro ρ
    rw [ProbabilityMeasure.coe_mk]
    have hconj : ∀ X, RelStructure.relabel ρ (T X) =
        T (RelStructure.relabel
          (fun s => (poolVertexEquiv S s).symm.trans ((ρ s).trans (poolVertexEquiv S s))) X) := by
      intro X
      rw [hTdef, RelStructure.congrCarrier_relabel]
      congr 1
      funext s
      ext x
      simp
    rw [Measure.map_map (measurable_relabel ρ) T.measurable,
      show RelStructure.relabel ρ ∘ ⇑T = ⇑T ∘ RelStructure.relabel
        (fun s => (poolVertexEquiv S s).symm.trans ((ρ s).trans (poolVertexEquiv S s))) from
        funext hconj,
      ← Measure.map_map T.measurable (measurable_relabel _), M.exchangeable]

end RelSignature
