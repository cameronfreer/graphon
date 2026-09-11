/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRankOneCoupling
import Graphon.RelRankOneRecovery
import Graphon.RelRankOneScreening
import Graphon.RelBasisSaturation

/-!
# The rank-one representation exists (R4 converse piece 3, #107)

**Every exchangeable law has a rank-one `RankRepresentation`.** The base case of the coupled
rank recursion, assembled from the five step-3 units. No dissociation, no `NoNullary`, and no
basis in the statement: a coherent basis is chosen inside the proof
(`nonempty_coherentBasis`) and never escapes.

The fields, by provenance:

* the coupling and its marginals, probability, and joint relabeling invariance are the
  transported #161 coupling (`exists_rankOneLatentCoupling`);
* `lower_recovers` is the nullary-block recovery (`exists_blockMap_recovery_of_card_lt_one`);
* `fixing_complete` reads a fixing event below rank one off the lower-rank factor
  (`exists_comap_factorMap_ae_eq`, `comap_factorMap_le_comap_lowerFactorMap`) and transports it
  across the coupling's recovery identity;
* `screening` is the per-support specialization (`condIndepFun_blockMap_restObservation_one`)
  of the conditioning ladder (`iCondIndepFun_blockMap_singleton_comap_snd`), fed by the
  coupling's conditional-independence clause at the identity reading.

Everything conditional is modulo the coupling measure. In particular **no identification of
the invariant σ-algebra with the σ-algebra of the latent is asserted** — the latent resolves
the rank-one factor and is conditionally independent of everything else, which is strictly
weaker and is all the recursion consumes.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

universe u

variable {S : RelSignature.{u}}

/-- **The rank-one representation built from a rank-one latent coupling.** The fields are the
transported coupling clauses, the nullary-block recovery, fixing completeness read off the
lower-rank factor, and the conditioning ladder. -/
noncomputable def CoherentBasis.rankOneRepOf [Countable S.Srt] [Countable S.Rel]
    {M : InfiniteRelExchangeableLaw S} (B : CoherentBasis M) (f : ℝ → B.LowerFactorSpace 1)
    (g : RankLatentSpace S 1 → B.LowerFactorSpace 1) (hg : Measurable g)
    (hprob : IsProbabilityMeasure (B.rankOneLatentCoupling f))
    (hfst : (B.rankOneLatentCoupling f).map Prod.fst =
      (M.law : Measure (RelStructure S (Vinfinite S))))
    (hsnd : (B.rankOneLatentCoupling f).map Prod.snd = rankLatentSource S 1)
    (hinv : ∀ σ : FinSuppPerm S, (B.rankOneLatentCoupling f).map
      (Prod.map (RelStructure.relabel σ.1) (rankLatentRelabel σ 1)) = B.rankOneLatentCoupling f)
    (hres : B.lowerFactorMap 1 ∘ Prod.fst =ᵐ[B.rankOneLatentCoupling f] g ∘ Prod.snd)
    (hci : CondIndepFun (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance)
      ((B.measurable_lowerFactorMap' 1).comp measurable_fst).comap_le
      Prod.fst Prod.snd (B.rankOneLatentCoupling f)) :
    M.RankRepresentation 1 :=
  haveI := hprob
  { P := B.rankOneLatentCoupling f
    isProbabilityMeasure_P := hprob
    map_fst := hfst
    map_snd := hsnd
    invariant := hinv
    lower_recovers := fun A hA => B.exists_blockMap_recovery_of_card_lt_one hfst hg hres A hA
    fixing_complete := fun A hA E hE => by
      classical
      have hqmp : Measure.QuasiMeasurePreserving
          (Prod.fst : RelStructure S (Vinfinite S) × RankLatentSpace S 1 → _)
          (B.rankOneLatentCoupling f) (M.law : Measure (RelStructure S (Vinfinite S))) :=
        ⟨measurable_fst, hfst ▸ Measure.AbsolutelyContinuous.rfl⟩
      obtain ⟨E₀, hE₀meas, hE₀ae⟩ := B.exists_comap_factorMap_ae_eq A hE
      obtain ⟨T, hT, hTE⟩ := B.comap_factorMap_le_comap_lowerFactorMap hA _ hE₀meas
      refine ⟨g ⁻¹' T, hg hT, ?_⟩
      have h1 : Prod.fst ⁻¹' E =ᵐ[B.rankOneLatentCoupling f] Prod.fst ⁻¹' E₀ :=
        hqmp.preimage_ae_eq hE₀ae.symm
      have h2 : Prod.fst ⁻¹' E₀ =ᵐ[B.rankOneLatentCoupling f] Prod.snd ⁻¹' (g ⁻¹' T) := by
        rw [← hTE]
        refine Filter.eventuallyEq_set.mpr ?_
        filter_upwards [hres] with p hp
        show p.1 ∈ B.lowerFactorMap 1 ⁻¹' T ↔ p ∈ Prod.snd ⁻¹' (g ⁻¹' T)
        simp only [Set.mem_preimage]
        rw [show B.lowerFactorMap 1 p.1 = g p.2 from hp]
      exact (h1.trans h2).symm
    screening := fun A hA => by
      classical
      obtain ⟨g₀, hg₀, hrec⟩ := B.exists_blockMap_recovery_of_card_lt_one hfst hg hres
        (∅ : Finset (Σ s : S.Srt, Vinfinite S s)) (by simp)
      exact condIndepFun_blockMap_restObservation_one
        (B.iCondIndepFun_blockMap_singleton_comap_snd hfst hg hres hci)
        hg₀ hrec A hA }

/-- **The rank-one representation exists**, for an arbitrary exchangeable law: a coupling of
the law with the rank-one latents satisfying all `RankRepresentation` clauses — marginals,
joint relabeling invariance, local recovery of everything below rank one, and rank-truncated
local screening at every rank-one support. -/
theorem InfiniteRelExchangeableLaw.nonempty_rankRepresentation_one
    [Countable S.Srt] [Countable S.Rel] (M : InfiniteRelExchangeableLaw S) :
    Nonempty (M.RankRepresentation 1) := by
  classical
  obtain ⟨B⟩ := M.nonempty_coherentBasis
  obtain ⟨f, g, hg, hprob, hfst, hsnd, hinv, hres, hci⟩ := B.exists_rankOneLatentCoupling
  exact ⟨B.rankOneRepOf f g hg hprob hfst hsnd hinv hres (hci measurable_id)⟩

end RelSignature
