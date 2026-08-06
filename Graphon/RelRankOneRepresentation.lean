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
    [Fintype S.Srt] [Countable S.Rel] (M : InfiniteRelExchangeableLaw S) :
    Nonempty (M.RankRepresentation 1) := by
  classical
  obtain ⟨B⟩ := M.nonempty_coherentBasis
  obtain ⟨f, g, hg, hprob, hfst, hsnd, hinv, hres, hci⟩ := B.exists_rankOneLatentCoupling
  haveI := hprob
  obtain ⟨g₀, hg₀, hrec⟩ := B.exists_blockMap_recovery_of_card_lt_one hfst hg hres
    (∅ : Finset (Σ s : S.Srt, Vinfinite S s)) (by simp)
  have hladder := B.iCondIndepFun_blockMap_singleton_comap_snd hfst hg hres
    (hci measurable_id)
  exact ⟨⟨B.rankOneLatentCoupling f, hprob, hfst, hsnd, hinv,
    fun A hA => B.exists_blockMap_recovery_of_card_lt_one hfst hg hres A hA,
    fun A hA => condIndepFun_blockMap_restObservation_one hladder hg₀ hrec A hA⟩⟩

end RelSignature
