/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.SamplingLaw
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs

/-!
# Examples of sample laws: the constant graphon is the binomial random graph (issue #21)

The sample law of the constant graphon with value `p` is exactly Mathlib's binomial
random-graph distribution `G(V, p)` (`SimpleGraph.binomialRandom`):

* `Graphon.sampleMass_constGraphon` — the graphon-side mass computation
  `sampleMass (constGraphon p) G = p^{e(G)} (1-p)^{\binom{k}{2} - e(G)}`;
* `Graphon.sampleLaw_const_eq_binomial` — equality of measures with `G(Fin k, p)`,
  via `Measure.ext_of_singleton` and Mathlib's `binomialRandom_singleton` (reused, not
  reproved);
* endpoint `simp` corollaries: at `p = 0` the law is `dirac ⊥`, at `p = 1` it is
  `dirac ⊤`.

This file exists so that the binomial-random-graph import stays out of
`Graphon/SamplingLaw.lean`. The stochastic-block-model law is deliberately deferred
(see issue #21).
-/

open MeasureTheory Set Filter Finset unitInterval

open scoped ENNReal Classical

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

variable [IsProbabilityMeasure μ] {k : ℕ}

/-- **The sample mass of a constant graphon**: every edge is present independently with
probability `p`, so the mass of `G` is `p^{e(G)} (1-p)^{\binom{k}{2} - e(G)}`. -/
theorem sampleMass_constGraphon (p : Set.Icc (0 : ℝ) 1) (G : SimpleGraph (Fin k)) :
    sampleMass (constGraphon (α := α) (μ := μ) p) G =
      (p : ℝ) ^ G.edgeFinset.card *
        (1 - (p : ℝ)) ^ (k.choose 2 - G.edgeFinset.card) := by
  classical
  -- a.e., every sampled pair evaluates the constant graphon to `p`.
  have hae : ∀ᵐ x ∂Measure.pi (fun _ : Fin k ↦ μ),
      ∀ e : Sym2 (Fin k), e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset →
        (constGraphon (α := α) (μ := μ) p).toAEEqFun
          (x (Quot.out e).1, x (Quot.out e).2) = (p : ℝ) := by
    rw [MeasureTheory.ae_all_iff]
    intro e
    by_cases he : e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset
    · have hne : (Quot.out e).1 ≠ (Quot.out e).2 := by
        intro hcontra
        apply (⊤ : SimpleGraph (Fin k)).not_isDiag_of_mem_edgeSet
          (SimpleGraph.mem_edgeFinset.mp he)
        rw [← e.out_eq]
        exact Sym2.mk_isDiag_iff.mpr hcontra
      have hconst : ∀ᵐ z ∂(μ.prod μ),
          (constGraphon (α := α) (μ := μ) p).toAEEqFun z =
            Function.const (α × α) (p : ℝ) z :=
        AEEqFun.coeFn_const _ _
      have h := ae_pairMap_of_prod (Quot.out e).1 (Quot.out e).2 hne hconst
      filter_upwards [h] with x hx _
      exact hx
    · filter_upwards with x hmem
      exact absurd hmem he
  have hcard : ((⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset).card
      = k.choose 2 - G.edgeFinset.card := by
    rw [Finset.card_sdiff,
      Finset.inter_eq_left.mpr (SimpleGraph.edgeFinset_mono le_top)]
    congr 1
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
  have hpt : ∀ᵐ x ∂Measure.pi (fun _ : Fin k ↦ μ),
      sampleIntegrand (constGraphon (α := α) (μ := μ) p) G x =
        (p : ℝ) ^ G.edgeFinset.card *
          (1 - (p : ℝ)) ^ (k.choose 2 - G.edgeFinset.card) := by
    filter_upwards [hae] with x hx
    have h1 : (∏ e ∈ G.edgeFinset,
        (constGraphon (α := α) (μ := μ) p).toAEEqFun
          (x (Quot.out e).1, x (Quot.out e).2)) = (p : ℝ) ^ G.edgeFinset.card := by
      rw [← Finset.prod_const]
      exact Finset.prod_congr rfl fun e he =>
        hx e (SimpleGraph.edgeFinset_mono le_top he)
    have h2 : (∏ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset,
        (1 - (constGraphon (α := α) (μ := μ) p).toAEEqFun
          (x (Quot.out e).1, x (Quot.out e).2))) =
        (1 - (p : ℝ)) ^ (k.choose 2 - G.edgeFinset.card) := by
      rw [← hcard, ← Finset.prod_const]
      exact Finset.prod_congr rfl fun e he => by rw [hx e (Finset.sdiff_subset he)]
    rw [sampleIntegrand, h1, h2]
  rw [sampleMass, integral_congr_ae hpt, integral_const]
  simp

/-- **The constant graphon samples the binomial random graph**: the sample law of
`constGraphon p` on `k` vertices is Mathlib's `G(Fin k, p)`. The singleton mass formula
`SimpleGraph.binomialRandom_singleton` is reused from Mathlib; the graphon-side
computation is `sampleMass_constGraphon`. -/
theorem sampleLaw_const_eq_binomial (p : Set.Icc (0 : ℝ) 1) (k : ℕ) :
    (sampleLaw (constGraphon (α := α) (μ := μ) p) k : Measure (SimpleGraph (Fin k))) =
      SimpleGraph.binomialRandom (Fin k) p := by
  change (samplePMF (constGraphon (α := α) (μ := μ) p) k).toMeasure = _
  refine Measure.ext_of_singleton fun G => ?_
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton G), samplePMF_apply,
    sampleMass_constGraphon, SimpleGraph.binomialRandom_singleton]
  have h1p : (0 : ℝ) ≤ 1 - (p : ℝ) := by linarith [p.2.2]
  rw [ENNReal.ofReal_mul (pow_nonneg p.2.1 _), ENNReal.ofReal_pow p.2.1,
    ENNReal.ofReal_pow h1p]
  have hncard : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have hcardV : Nat.card (Fin k) = k := by simp
  have hp : ENNReal.ofReal (p : ℝ) = (toNNReal p : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
  have hσ : ENNReal.ofReal (1 - (p : ℝ)) = (toNNReal (σ p) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
  rw [hp, hσ, hncard, hcardV]

/-- At `p = 0` the sample law is the point mass at the empty graph. -/
@[simp] theorem sampleLaw_const_zero (k : ℕ) :
    (sampleLaw (constGraphon (α := α) (μ := μ) 0) k : Measure (SimpleGraph (Fin k))) =
      Measure.dirac (⊥ : SimpleGraph (Fin k)) := by
  rw [sampleLaw_const_eq_binomial]
  exact SimpleGraph.binomialRandom_zero (Fin k)

/-- At `p = 1` the sample law is the point mass at the complete graph. -/
@[simp] theorem sampleLaw_const_one (k : ℕ) :
    (sampleLaw (constGraphon (α := α) (μ := μ) 1) k : Measure (SimpleGraph (Fin k))) =
      Measure.dirac (⊤ : SimpleGraph (Fin k)) := by
  rw [sampleLaw_const_eq_binomial]
  exact SimpleGraph.binomialRandom_one (Fin k)

end Graphon
