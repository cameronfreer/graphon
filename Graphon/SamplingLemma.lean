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

* `Graphon.first_sampling_lemma_of_large_k` — the asymptotic form (`G(k, W) → W` in
  probability, uniformly over graphons): `point_sampling_event_of_large_k` (the AFKK
  point-sampling half, `Graphon/SamplingPointwise.lean`) + `rounding_event_of_large_k`
  (the finite-Chernoff rounding half, `Graphon/SamplingRounding.lean`) recombined via
  `sampleGoodMassOn_of_events` at accuracies `(ε/2, η/4)`, retaining the quantified `k`.
* `Graphon.first_sampling_lemma` — the single-sample-size interface, derived.
* `Graphon.exists_simpleGraph_cutDistance_lt_of_large_k` /
  `Graphon.exists_simpleGraph_cutDistance_lt` — every graphon is `ε`-approximated in cut
  distance by a finite simple graph, indeed on every sufficiently large exact vertex
  count, with the threshold uniform over graphons.
* `Graphon.exists_tendsto_cutDistance_ofSimpleGraphOn` — every graphon is a cut-distance
  limit of finite simple graphs.
* `Graphon.sampling_quantitative_icl` — sampling ⟹ the `K`-independent quantitative
  ICL, by the event-intersection argument (unchanged).

Axiom accounting: both theorems are fully axiom-clean (standard axioms only). The four
corrected Rokhlin cores they rest on (`exists_common_coupling_maps`, `cutNormDiff_pullback_le`,
`exists_controlled_cell_alignment`, `exists_mpEquiv_cutNormDiff_lt_add`, via
`cutDistance_triangle`) were all proved in campaigns R2–R3 from the atomless standard-Borel
measure-isomorphism theorem (`Graphon/MeasureIso.lean`, `Graphon/Overlay.lean`).
-/

open MeasureTheory

namespace Graphon

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ]

open scoped Classical

/-- **The First Sampling Lemma, asymptotic form** — `G(k, W) → W` in probability,
uniformly over all graphons on the space.

For every accuracy `ε` and failure probability `η` there is a threshold `K` such that at
EVERY nonzero sample size `k ≥ K` (the `NeZero k` hypothesis; `sampleGoodMassOn` needs a
vertex to exist) and for EVERY graphon `W` simultaneously, the sampled graph `G(k, W)`
lies within cut distance `ε` of `W` with probability greater than `1 − η`.

Both concentration halves (`point_sampling_event_of_large_k`,
`rounding_event_of_large_k`) already hold for all sufficiently large `k` uniformly in
`W`; this statement simply retains that strength, where `first_sampling_lemma` returns a
single sample size. Classical reference: Lovász, *Large Networks and Graph Limits*,
Lemma 10.16; BCLSV, "Convergent sequences I", Thm 4.6. -/
theorem first_sampling_lemma_of_large_k (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ K : ℕ, ∀ k, K ≤ k → ∀ (_ : NeZero k), ∀ W : Graphon α μ,
      1 - η < sampleGoodMassOn W k ε := by
  have hε2 : 0 < ε / 2 := by positivity
  have hη4 : 0 < η / 4 := by positivity
  obtain ⟨K₁, hpt⟩ :=
    point_sampling_event_of_large_k (α := α) (μ := μ) (ε / 2) (η / 4) hε2 hη4
  obtain ⟨K₂, hrd⟩ :=
    rounding_event_of_large_k (α := α) (μ := μ) (ε / 2) (η / 4) hε2 hη4
  refine ⟨max K₁ K₂, fun k hk hkz W ↦ ?_⟩
  have h₁ : K₁ ≤ k := (le_max_left _ _).trans hk
  have h₂ : K₂ ≤ k := (le_max_right _ _).trans hk
  have hmass := sampleGoodMassOn_of_events W k ε (η / 4) (η / 4) hη4.le
    (hpt _ h₁ hkz W) (hrd _ h₂ hkz W)
  linarith

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
@[blueprint "thm:first-sampling"
  (title := /-- First Sampling Lemma -/)]
theorem first_sampling_lemma (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ k : ℕ, ∀ W : Graphon α μ, 1 - η < sampleGoodMassOn W (k + 1) ε := by
  obtain ⟨K, hK⟩ := first_sampling_lemma_of_large_k (α := α) (μ := μ) ε η hε hη
  exact ⟨K, fun W ↦ hK (K + 1) (Nat.le_succ K) ⟨Nat.succ_ne_zero K⟩ W⟩

/-- Positive good mass exhibits a good graph: if the `G(k, W)`-mass of the event
`d_□(W, K_G) < ε` is positive, some simple graph on `k` vertices realizes it. -/
theorem exists_cutDistance_lt_of_sampleGoodMassOn_pos {W : Graphon α μ} {k : ℕ} [NeZero k]
    {ε : ℝ} (h : 0 < sampleGoodMassOn W k ε) :
    ∃ G : SimpleGraph (Fin k), cutDistance W (ofSimpleGraphOn G) < ε := by
  by_contra hno
  push Not at hno
  have hzero : sampleGoodMassOn W k ε = 0 :=
    Finset.sum_eq_zero fun G _ ↦ if_neg (not_lt.mpr (hno G))
  rw [hzero] at h
  exact lt_irrefl 0 h

/-- **Finite approximation at every sufficiently large size, uniformly**: for every
`ε > 0` there is a threshold `K` such that every graphon is within cut distance `ε` of
(the embedded graphon of) some simple graph on exactly `k` vertices, for every nonzero
`k ≥ K` simultaneously (the `NeZero k` hypothesis). -/
theorem exists_simpleGraph_cutDistance_lt_of_large_k {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k, K ≤ k → ∀ (_ : NeZero k), ∀ W : Graphon α μ,
      ∃ G : SimpleGraph (Fin k), cutDistance W (ofSimpleGraphOn G) < ε := by
  obtain ⟨K, hK⟩ := first_sampling_lemma_of_large_k (α := α) (μ := μ) ε (1 / 2) hε
    (by norm_num)
  refine ⟨K, fun k hk hkz W ↦ ?_⟩
  have := hK k hk hkz W
  exact exists_cutDistance_lt_of_sampleGoodMassOn_pos (by linarith)

/-- **Finite approximation**: every graphon is within any positive cut distance of the
embedded graphon of a finite simple graph (successor-indexed, so no `NeZero` witness is
threaded through the existential — matching the `first_sampling_lemma` interface). -/
theorem exists_simpleGraph_cutDistance_lt (W : Graphon α μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (G : SimpleGraph (Fin (k + 1))),
      cutDistance W (ofSimpleGraphOn G) < ε := by
  obtain ⟨K, hK⟩ := exists_simpleGraph_cutDistance_lt_of_large_k (α := α) (μ := μ) hε
  obtain ⟨G, hG⟩ := hK (K + 1) (Nat.le_succ _) ⟨Nat.succ_ne_zero _⟩ W
  exact ⟨K, G, hG⟩

/-- **Every graphon is a cut-distance limit of finite simple graphs**: there is a
sequence of simple graphs, the `k`-th on `k + 1` vertices, whose embedded graphons
converge to `W` in cut distance. -/
theorem exists_tendsto_cutDistance_ofSimpleGraphOn (W : Graphon α μ) :
    ∃ G : (k : ℕ) → SimpleGraph (Fin (k + 1)),
      Filter.Tendsto (fun k ↦ cutDistance W (ofSimpleGraphOn (G k)))
        Filter.atTop (nhds 0) := by
  -- Take a cut-distance-minimizing graph at every size.
  choose G _hGmem hGmin using fun k : ℕ ↦
    Finset.exists_min_image (Finset.univ : Finset (SimpleGraph (Fin (k + 1))))
      (fun G ↦ cutDistance W (ofSimpleGraphOn G)) ⟨⊥, Finset.mem_univ _⟩
  refine ⟨G, Metric.tendsto_atTop.mpr fun ε hε ↦ ?_⟩
  obtain ⟨K, hK⟩ := exists_simpleGraph_cutDistance_lt_of_large_k (α := α) (μ := μ) hε
  refine ⟨K, fun n hn ↦ ?_⟩
  obtain ⟨G', hG'⟩ := hK (n + 1) (hn.trans (Nat.le_succ _)) ⟨Nat.succ_ne_zero _⟩ W
  have hmin := hGmin n G' (Finset.mem_univ _)
  have hnn := cutDistance_nonneg W (ofSimpleGraphOn (G n))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
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
