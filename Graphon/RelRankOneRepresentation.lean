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
  haveI := hprob
  obtain ⟨g₀, hg₀, hrec⟩ := B.exists_blockMap_recovery_of_card_lt_one hfst hg hres
    (∅ : Finset (Σ s : S.Srt, Vinfinite S s)) (by simp)
  have hladder := B.iCondIndepFun_blockMap_singleton_comap_snd hfst hg hres
    (hci measurable_id)
  have hqmp : Measure.QuasiMeasurePreserving
      (Prod.fst : RelStructure S (Vinfinite S) × RankLatentSpace S 1 → _)
      (B.rankOneLatentCoupling f) (M.law : Measure (RelStructure S (Vinfinite S))) :=
    ⟨measurable_fst, hfst ▸ Measure.AbsolutelyContinuous.rfl⟩
  refine ⟨⟨B.rankOneLatentCoupling f, hprob, hfst, hsnd, hinv,
    fun A hA => B.exists_blockMap_recovery_of_card_lt_one hfst hg hres A hA,
    fun A hA E hE => ?_,
    fun A hA => condIndepFun_blockMap_restObservation_one hladder hg₀ hrec A hA⟩⟩
  -- fixing completeness: a representative read off the lower-rank factor, transported to the
  -- coupling and across the recovery identity
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

end RelSignature
