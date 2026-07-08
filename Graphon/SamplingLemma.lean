/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.SamplingPointwise

/-!
# The First Sampling Lemma — assembly

Recombines the two proved concentration events into the space-generic First Sampling
Lemma, and re-hosts its downstream consumer `sampling_quantitative_icl` (moved verbatim
from `Graphon/SamplingICL.lean`, where the import direction — the event theorems live
downstream of `SamplingICL` — prevented the assembly).

* `Graphon.first_sampling_lemma` — PROVED: `point_sampling_event_of_large_k` (the AFKK
  point-sampling half, `Graphon/SamplingPointwise.lean`) + `rounding_event_of_large_k`
  (the finite-Chernoff rounding half, `Graphon/SamplingRounding.lean`) recombined via
  `sampleGoodMassOn_of_events` at accuracies `(ε/2, η/4)`.
* `Graphon.sampling_quantitative_icl` — sampling ⟹ the `K`-independent quantitative
  ICL, by the event-intersection argument (unchanged).

Axiom accounting: both theorems are `cutDistance`-level, so they carry the project's remaining
measure-theory gap — the four corrected Rokhlin cores (`exists_common_coupling_maps`,
`cutNormDiff_pullback_le`, `exists_controlled_cell_alignment`, `exists_mpEquiv_cutNormDiff_lt_add`,
via `cutDistance_triangle`), each a consequence of the atomless standard-Borel
measure-isomorphism theorem — and nothing else beyond the standard axioms.
-/

open MeasureTheory

namespace Graphon

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

open scoped Classical

/-- **The First Sampling Lemma** (space-generic interface; PROVED).

For every accuracy `ε` and failure probability `η`, some sample size `k` works for
EVERY graphon on the space simultaneously: the sampled graph `G(k, W)` lies within cut
distance `ε` of `W` with probability greater than `1 − η`. The `W`-uniformity of `k` is
the point — it is what makes the quantitative ICL below partition-size-independent,
breaking the circularity documented at `headline_parameter_selection`.

Proof: recombination (`sampleGoodMassOn_of_events`) of the two concentration events at
accuracy `ε/2` and failure probabilities `η/4`:
`point_sampling_event_of_large_k` (the analytic AFKK half) and
`rounding_event_of_large_k` (the finite union bound over cuts), each with `W`-uniform
threshold. Classical reference: Lovász, *Large Networks and Graph Limits*, Lemma 10.16;
BCLSV, "Convergent sequences I", Thm 4.6. -/
theorem first_sampling_lemma (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ k : ℕ, ∀ W : Graphon α μ, 1 - η < sampleGoodMassOn W (k + 1) ε := by
  have hε2 : 0 < ε / 2 := by positivity
  have hη4 : 0 < η / 4 := by positivity
  obtain ⟨K₁, hpt⟩ :=
    point_sampling_event_of_large_k (α := α) (μ := μ) (ε / 2) (η / 4) hε2 hη4
  obtain ⟨K₂, hrd⟩ :=
    rounding_event_of_large_k (α := α) (μ := μ) (ε / 2) (η / 4) hε2 hη4
  refine ⟨max K₁ K₂, fun W ↦ ?_⟩
  haveI : NeZero (max K₁ K₂ + 1) := ⟨Nat.succ_ne_zero _⟩
  have h₁ : K₁ ≤ max K₁ K₂ + 1 := (le_max_left _ _).trans (Nat.le_succ _)
  have h₂ : K₂ ≤ max K₁ K₂ + 1 := (le_max_right _ _).trans (Nat.le_succ _)
  have hmass := sampleGoodMassOn_of_events W (max K₁ K₂ + 1) ε (η / 4) (η / 4) hη4.le
    (hpt _ h₁ inferInstance W) (hrd _ h₂ inferInstance W)
  linarith

/-- **Sampling ⇒ the partition-size-independent quantitative ICL** — the non-circular
inverse counting lemma. The parameters `(δ, m)` depend only on `ε` (through
`first_sampling_lemma`), on NO partition cardinality: this is the `K`-independence that
`headline_parameter_selection` documents as impossible for regularity bookkeeping.

**Proof (event intersection)**: sample at accuracy `ε/2`, failure probability `1/4`, so
both `U` and `W` have own-good mass `> 3/4`. Hom-density `δ`-closeness makes the sampled
distributions `< 1/4`-close in total variation, so `U`'s good event keeps mass `> 1/2`
under `W`'s distribution; together with `W`'s own good event (mass `> 3/4`) the two
events must intersect. A common good graph `G` gives
`d(U, W) ≤ d(U, K_G) + d(K_G, W) < ε`. No `cutDistance U W ≤ ρ` hypothesis enters
anywhere (that would be circular for inverse counting); only the generic event transfer
`sum_sampleMass_event_sub_le` is used. -/
theorem sampling_quantitative_icl (ε : ℝ) (hε : 0 < ε) :
    ∃ (δ : ℝ) (_ : 0 < δ) (m : ℕ),
      ∀ U W : Graphon α μ,
        (∀ (F : SimpleGraph (Fin m)) [DecidableRel F.Adj],
          |homDensity F U - homDensity F W| < δ) →
        cutDistance U W < ε := by
  classical
  obtain ⟨k, hk⟩ := first_sampling_lemma (α := α) (μ := μ) (ε / 2) (1 / 4)
    (by positivity) (by norm_num)
  set m := k + 1 with hm
  refine ⟨1 / (4 ^ (m * m) * 8), by positivity, m, ?_⟩
  intro U W hclose
  -- Total variation between the sampled distributions is < 1/4.
  have htv : ∑ G : SimpleGraph (Fin m), |sampleMass U G - sampleMass W G| ≤
      2 ^ (m * m) * (2 ^ (m * m) * (1 / (4 ^ (m * m) * 8))) :=
    sampleDistribution_tv_close_of_homDensity_close U W _
      (fun F _ ↦ (hclose F).le)
  have htv4 : ∑ G : SimpleGraph (Fin m), |sampleMass U G - sampleMass W G| < 1 / 4 := by
    refine lt_of_le_of_lt htv ?_
    have h4 : ((4 : ℝ)) ^ (m * m) = 2 ^ (m * m) * 2 ^ (m * m) := by
      rw [← mul_pow]; norm_num
    rw [show (2 : ℝ) ^ (m * m) * (2 ^ (m * m) * (1 / (4 ^ (m * m) * 8))) =
        (2 ^ (m * m) * 2 ^ (m * m)) / (4 ^ (m * m) * 8) by ring, ← h4]
    rw [div_lt_iff₀ (by positivity)]
    have hpos : (0 : ℝ) < 4 ^ (m * m) := by positivity
    nlinarith [hpos]
  -- The U-good event, under both distributions.
  set A : Finset (SimpleGraph (Fin m)) :=
    Finset.univ.filter (fun G ↦ cutDistance U (ofSimpleGraphOn G) < ε / 2) with hA
  have hUA : sampleGoodMassOn U m (ε / 2) = ∑ G ∈ A, sampleMass U G := by
    rw [hA, Finset.sum_filter]; rfl
  set B : Finset (SimpleGraph (Fin m)) :=
    Finset.univ.filter (fun G ↦ cutDistance W (ofSimpleGraphOn G) < ε / 2) with hB
  have hWB : sampleGoodMassOn W m (ε / 2) = ∑ G ∈ B, sampleMass W G := by
    rw [hB, Finset.sum_filter]; rfl
  -- U's good event has W-mass > 1/2 (event transfer); W's own good event has mass > 3/4.
  have hWA : (1 : ℝ) / 2 < ∑ G ∈ A, sampleMass W G := by
    have h1 := sum_sampleMass_event_sub_le U W A _ htv4.le
    have h2 := hk U
    rw [hUA] at h2
    linarith
  have hWB' : (3 : ℝ) / 4 < ∑ G ∈ B, sampleMass W G := by
    have h2 := hk W
    rw [hWB] at h2
    linarith
  -- The two events intersect: otherwise their masses would sum past the total 1.
  have hinter : (A ∩ B).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hdisj : Disjoint A B := Finset.disjoint_iff_inter_eq_empty.mpr hempty
    have hunion : ∑ G ∈ A ∪ B, sampleMass W G =
        ∑ G ∈ A, sampleMass W G + ∑ G ∈ B, sampleMass W G :=
      Finset.sum_union hdisj
    have hle : ∑ G ∈ A ∪ B, sampleMass W G ≤ 1 := by
      rw [← sampleMass_sum_eq_one (k := m) W]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun G _ _ ↦ sampleMass_nonneg W G)
    linarith
  -- A common good graph closes the triangle.
  obtain ⟨G, hG⟩ := hinter
  rw [Finset.mem_inter, hA, hB, Finset.mem_filter, Finset.mem_filter] at hG
  calc cutDistance U W
      ≤ cutDistance U (ofSimpleGraphOn G) + cutDistance (ofSimpleGraphOn G) W :=
        cutDistance_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        refine add_lt_add hG.1.2 ?_
        rw [cutDistance_symm]
        exact hG.2.2
    _ = ε := by ring

end Graphon
