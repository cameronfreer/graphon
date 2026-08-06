/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRankOneTransfer
import Graphon.RelRankLatents
import Graphon.ForMathlib.CondExpComap

/-!
# The rank-one coupling on the latent space (R4 converse piece 3, #107)

The #161 coupling `relativeFactorCoupling M.law uniform01 (lowerFactorMap 1) f` lives on
`RelStructure × ℝ`. The `RankRepresentation` interface asks for a coupling with the rank-one
**latent space** `RankLatentSpace S 1` — the one-coordinate cube the recursion indexes by
supports — as its second factor. This module transports the coupling
(`rankOneLatentCoupling`) and all its clauses through
`rankLatentOneEquiv : RankLatentSpace S 1 ≃ᵐ ℝ`, applied on the second coordinate only.

Two clauses deserve comment.

* **Joint relabeling invariance** comes out in the `RankRepresentation` shape: the relabeling
  acts on both coordinates at once. At rank one `rankLatentRelabel σ 1` is the identity on
  points (`rankLatentRelabel_one_eq`), so the latent side of the joint action collapses and
  #161's structure-side invariance `map_prodMap_relabel_rankOneCoupling` is exactly what is
  needed. At higher rank neither simplification is available.
* **Conditional independence** transports along the *reverse* direction: the second-coordinate
  equivalence is measure-preserving from the transported coupling back to the original, the pair
  transport `condIndepFun_comp_measurePreserving` moves the clause, `MeasurableSpace.comap_comp`
  collapses the conditioning — the equivalence does not touch the first coordinate — and
  Mathlib's `CondIndepFun.comp` straightens the codomain.

As in #161, the conditional-independence clause is stated for **every** measurable reading of
the structure, so any unresolved reading follows by composition; and no σ-algebra equality
between the latent and the factor is claimed — the latent may carry strictly more than
`lowerFactorMap 1` reads, and conditional independence is exactly the statement that the
surplus says nothing further about the structure.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

universe u

/-- The second-coordinate transport: identity on the structure, `rankLatentOneEquiv.symm` on the
latent. Mentions no basis and no law, so it lives at the signature level. -/
noncomputable def rankOneLatentEquiv (S : RelSignature.{u}) :
    RelStructure S (Vinfinite S) × ℝ ≃ᵐ RelStructure S (Vinfinite S) × RankLatentSpace S 1 :=
  (MeasurableEquiv.refl (RelStructure S (Vinfinite S))).prodCongr rankLatentOneEquiv.symm

theorem rankOneLatentEquiv_coe (S : RelSignature.{u}) :
    ⇑(rankOneLatentEquiv S) = Prod.map id ⇑(rankLatentOneEquiv (S := S)).symm := rfl

theorem rankOneLatentEquiv_symm_coe (S : RelSignature.{u}) :
    ⇑(rankOneLatentEquiv S).symm = Prod.map id ⇑(rankLatentOneEquiv (S := S)) := rfl

namespace CoherentBasis

variable {S : RelSignature.{u}} {M : InfiniteRelExchangeableLaw S} (B : CoherentBasis M)

open scoped Classical in
/-- **The rank-one coupling, on the latent space**: the #161 coupling with its latent coordinate
transported into the rank-one latent cube. -/
noncomputable def rankOneLatentCoupling [Countable S.Srt] [Countable S.Rel]
    (f : ℝ → B.LowerFactorSpace 1) :
    Measure (RelStructure S (Vinfinite S) × RankLatentSpace S 1) :=
  (relativeFactorCoupling (M.law : Measure (RelStructure S (Vinfinite S))) uniform01
    (B.lowerFactorMap 1) f).map (rankOneLatentEquiv S)

instance [Countable S.Srt] [Countable S.Rel] (f : ℝ → B.LowerFactorSpace 1) :
    IsFiniteMeasure (B.rankOneLatentCoupling f) := by
  rw [rankOneLatentCoupling]
  exact Measure.isFiniteMeasure_map _ _

/-- Conditional independence is insensitive to replacing the conditioning σ-algebra by an equal
one; the inclusion proofs move by proof irrelevance. -/
private theorem condIndepFun_congr_cond {Ω β γ : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    [MeasurableSpace β] [MeasurableSpace γ] {f : Ω → β} {g : Ω → γ}
    {m₁ m₂ : MeasurableSpace Ω} (h12 : m₁ = m₂) {h1 : m₁ ≤ mΩ} (h2 : m₂ ≤ mΩ)
    (h : CondIndepFun m₁ h1 f g μ) : CondIndepFun m₂ h2 f g μ := by
  subst h12
  exact h

open scoped Classical in
/-- **The transported clauses.** There are a coding `f` and a measurable latent read `g` for
which the rank-one latent coupling is a probability measure with the law and the latent
source as marginals, is invariant under the joint relabeling action, resolves the rank-one
factor through `g`, and makes the latent conditionally independent — given the rank-one
factor — of every measurable reading of the structure. -/
theorem exists_rankOneLatentCoupling [Countable S.Srt] [Countable S.Rel] :
    ∃ (f : ℝ → B.LowerFactorSpace 1) (g : RankLatentSpace S 1 → B.LowerFactorSpace 1),
      Measurable g ∧
      IsProbabilityMeasure (B.rankOneLatentCoupling f) ∧
      (B.rankOneLatentCoupling f).map Prod.fst
        = (M.law : Measure (RelStructure S (Vinfinite S))) ∧
      (B.rankOneLatentCoupling f).map Prod.snd = rankLatentSource S 1 ∧
      (∀ σ : FinSuppPerm S, (B.rankOneLatentCoupling f).map
        (Prod.map (RelStructure.relabel σ.1) (rankLatentRelabel σ 1))
          = B.rankOneLatentCoupling f) ∧
      B.lowerFactorMap 1 ∘ Prod.fst =ᵐ[B.rankOneLatentCoupling f] g ∘ Prod.snd ∧
      ∀ {Y : Type*} [MeasurableSpace Y] {h : RelStructure S (Vinfinite S) → Y},
        Measurable h →
        CondIndepFun (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance)
          ((B.measurable_lowerFactorMap' 1).comp measurable_fst).comap_le
          (h ∘ Prod.fst) Prod.snd (B.rankOneLatentCoupling f) := by
  classical
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  obtain ⟨f, hf, hprob, hfst, hsnd, hres, hci⟩ := B.exists_rankOneUniformCoupling
  haveI : IsProbabilityMeasure (relativeFactorCoupling
      (M.law : Measure (RelStructure S (Vinfinite S))) uniform01 (B.lowerFactorMap 1) f) :=
    hprob
  set e : RankLatentSpace S 1 ≃ᵐ ℝ := rankLatentOneEquiv with he
  -- the reverse direction of the transport is measure-preserving
  have hTsymm : MeasurePreserving (⇑(rankOneLatentEquiv S).symm) (B.rankOneLatentCoupling f)
      (relativeFactorCoupling (M.law : Measure (RelStructure S (Vinfinite S))) uniform01
        (B.lowerFactorMap 1) f) := by
    refine ⟨(rankOneLatentEquiv S).symm.measurable, ?_⟩
    rw [rankOneLatentCoupling,
      Measure.map_map (rankOneLatentEquiv S).symm.measurable (rankOneLatentEquiv S).measurable]
    simp [MeasurableEquiv.symm_comp_self]
  refine ⟨f, f ∘ e, hf.comp e.measurable, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- probability
    rw [rankOneLatentCoupling]
    exact Measure.isProbabilityMeasure_map (rankOneLatentEquiv S).measurable.aemeasurable
  · -- structure marginal
    rw [rankOneLatentCoupling,
      Measure.map_map measurable_fst (rankOneLatentEquiv S).measurable,
      show Prod.fst ∘ ⇑(rankOneLatentEquiv S) = Prod.fst from rfl, hfst]
  · -- latent marginal
    rw [rankOneLatentCoupling,
      Measure.map_map measurable_snd (rankOneLatentEquiv S).measurable,
      show Prod.snd ∘ ⇑(rankOneLatentEquiv S) = ⇑e.symm ∘ Prod.snd from rfl,
      ← Measure.map_map e.symm.measurable measurable_snd, hsnd, he,
      ← rankLatentSource_map_rankLatentOneEquiv (S := S),
      Measure.map_map rankLatentOneEquiv.symm.measurable rankLatentOneEquiv.measurable]
    simp [MeasurableEquiv.symm_comp_self]
  · -- joint relabeling invariance
    intro σ
    have hjoint : Prod.map (RelStructure.relabel σ.1) (⇑(rankLatentRelabel σ 1)) ∘
        ⇑(rankOneLatentEquiv S)
        = ⇑(rankOneLatentEquiv S) ∘ Prod.map (RelStructure.relabel σ.1) id := by
      funext p
      simp [rankOneLatentEquiv_coe, Prod.map, rankLatentRelabel_one_eq]
    rw [rankOneLatentCoupling,
      Measure.map_map (((M.measurePreserving_relabel σ.1).measurable).prodMap
        (rankLatentRelabel σ 1).measurable) (rankOneLatentEquiv S).measurable, hjoint,
      ← Measure.map_map (rankOneLatentEquiv S).measurable
        (((M.measurePreserving_relabel σ.1).measurable).prodMap measurable_id),
      B.map_prodMap_relabel_rankOneCoupling f σ]
  · -- resolution of the rank-one factor by the latent
    have htrans := hTsymm.quasiMeasurePreserving.ae_eq_comp hres
    rw [show (B.lowerFactorMap 1 ∘ Prod.fst) ∘ ⇑(rankOneLatentEquiv S).symm
          = B.lowerFactorMap 1 ∘ Prod.fst from rfl,
      show (f ∘ Prod.snd) ∘ ⇑(rankOneLatentEquiv S).symm = (f ∘ ⇑e) ∘ Prod.snd from rfl]
        at htrans
    exact htrans
  · -- conditional independence given the rank-one factor
    intro Y _ h hmeas
    have base : CondIndepFun
        (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance)
        ((B.measurable_lowerFactorMap' 1).comp measurable_fst).comap_le
        (h ∘ Prod.fst) Prod.snd
        (relativeFactorCoupling (M.law : Measure (RelStructure S (Vinfinite S))) uniform01
          (B.lowerFactorMap 1) f) :=
      hci.comp hmeas measurable_id
    have moved := condIndepFun_comp_measurePreserving hTsymm
      ((B.measurable_lowerFactorMap' 1).comp measurable_fst).comap_le
      (hmeas.comp measurable_fst) measurable_snd base
    have hstraight := moved.comp measurable_id e.symm.measurable
    rw [show id ∘ (h ∘ Prod.fst) ∘ ⇑(rankOneLatentEquiv S).symm = h ∘ Prod.fst from rfl,
      show ⇑e.symm ∘ Prod.snd ∘ ⇑(rankOneLatentEquiv S).symm = Prod.snd from
        funext fun p => e.symm_apply_apply _] at hstraight
    exact condIndepFun_congr_cond (by rw [MeasurableSpace.comap_comp]; rfl) _ hstraight

end CoherentBasis

end RelSignature
