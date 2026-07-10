/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.CutNorm
import Graphon.HomDensity

/-!
# Sampling Random Graphs from Graphons

This file defines the finite distribution of the W-random graph `G(k, W)` and the
expected edge density, WITHOUT introducing random variables: the probability mass of
each graph is defined directly as an integral.

## Main definitions

* `Graphon.sampleMass` — the probability that `G(k, W)` equals a given graph `G`:
  `∫ x, ∏_{e ∈ E(G)} W(xᵢ,xⱼ) · ∏_{e ∉ E(G)} (1 − W(xᵢ,xⱼ))`
* `Graphon.sampleGraphExpectedDensity` — Expected edge density of sampled graph

## Main results

* `Graphon.sampleMass_nonneg` — masses are nonnegative
* `Graphon.sampleMass_sum_eq_one` — masses sum to 1 over all graphs on `Fin k`
* `Graphon.sampleMass_eq_sum_homDensity` — each mass is a finite signed sum of
  homomorphism densities of graphs on `Fin k` (inclusion–exclusion)
* `Graphon.sampleMass_close_of_homDensity_close` — hom-density closeness on `Fin k`
  controls each mass difference
* `Graphon.sampleDistribution_tv_close_of_homDensity_close` — hence total-variation
  closeness of the sampled graph distributions (the bridge for the BCLSV sampling route
  to `headline_parameter_selection`)
* `Graphon.sampleGraphExpectedDensity_eq` — Expected density equals ∫∫ W
* `Graphon.sampleGraphExpectedDensity_mem_Icc` — Expected density is in [0, 1]

## Implementation notes

The sampling process for G(n, W) is:
1. Sample n i.i.d. points x₁, ..., xₙ uniformly from [0,1]
2. Connect vertices i and j (i < j) independently with probability W(xᵢ, xⱼ)

This is a two-level randomness: first the positions, then the edges.

The key result established here is that the expected edge density equals the
integral of the graphon. Concentration is proved in `Graphon/SamplingConcentration.lean`
/ `SamplingPointwise.lean` / `SamplingRounding.lean`, culminating in the First Sampling
Lemma (`Graphon/SamplingLemma.lean`); convergence in `Graphon/Convergence.lean`.

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Section 10.2-10.3
-/

open MeasureTheory Set Filter Finset

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

/-! ### Sampling definition -/

section Sampling

variable [IsProbabilityMeasure μ]

/-- The expected edge density of a graph sampled from a graphon.

For a graphon W, if we sample n points x₁,...,xₙ and connect i~j with
probability W(xᵢ,xⱼ), the expected edge density is ∫∫ W(x,y) dμ(x) dμ(y).

Note: This is the expected density over both the position randomness and
the edge randomness. -/
noncomputable def sampleGraphExpectedDensity (W : Graphon α μ) : ℝ :=
  ∫ p, W.toAEEqFun p ∂(μ.prod μ)

/-- The expected edge density equals the double integral of the graphon. -/
theorem sampleGraphExpectedDensity_eq (W : Graphon α μ) :
    sampleGraphExpectedDensity W = ∫ x, (∫ y, W.toAEEqFun (x, y) ∂μ) ∂μ := by
  unfold sampleGraphExpectedDensity
  -- Apply Fubini's theorem
  exact integral_prod W.toAEEqFun (SymmKernel.graphon_integrable W)

/-- The expected edge density is in [0,1]. -/
theorem sampleGraphExpectedDensity_mem_Icc (W : Graphon α μ) :
    sampleGraphExpectedDensity W ∈ Set.Icc 0 1 := by
  constructor
  · -- Nonnegativity from W ≥ 0 a.e.
    unfold sampleGraphExpectedDensity
    apply integral_nonneg_of_ae
    filter_upwards [W.ae_mem_Icc] with p hp
    exact hp.1
  · -- Upper bound from W ≤ 1 a.e. and μ being probability measure
    unfold sampleGraphExpectedDensity
    -- ∫ W ≤ ∫ 1 = 1 since W ≤ 1 a.e. and μ is probability measure
    calc ∫ p, W.toAEEqFun p ∂(μ.prod μ)
        ≤ ∫ _, (1 : ℝ) ∂(μ.prod μ) := by
          apply integral_mono_ae (SymmKernel.graphon_integrable W) (integrable_const 1)
          filter_upwards [W.ae_mem_Icc] with p hp
          exact hp.2
      _ = ((μ.prod μ) univ).toReal := by rw [integral_const, smul_eq_mul, mul_one]; rfl
      _ = 1 := by
          have h_prob : IsProbabilityMeasure (μ.prod μ) := inferInstance
          simp [h_prob.measure_univ]

end Sampling

/-! ### The sampled graph distribution

The distribution of the W-random graph `G(k, W)` on `Fin k`, given by explicit
probability masses. Everything here is finite algebra plus integrals: no random
variables, no concentration. -/

section SampleDistribution

open scoped Classical

variable [IsProbabilityMeasure μ] {k : ℕ}

/-- Members of `⊤.edgeFinset` are non-diagonal. -/
private theorem not_isDiag_of_mem_top {e : Sym2 (Fin k)}
    (he : e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset) : ¬ e.IsDiag :=
  (⊤ : SimpleGraph (Fin k)).not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp he)

omit [IsProbabilityMeasure μ] in
/-- The hom-density integrand of a generated graph is the plain edge product over the
generating (non-diagonal) finset. Proved in place so the `edgeFinset` `Fintype` instance
is whatever the goal carries (instance-diamond safe). -/
private theorem homDensityIntegrand_fromEdgeSet {S : Finset (Sym2 (Fin k))}
    (hS : ∀ e ∈ S, ¬ e.IsDiag) (W : Graphon α μ) (x : Fin k → α) :
    homDensityIntegrand (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin k)))) W x =
      ∏ e ∈ S, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) := by
  rw [homDensityIntegrand]
  refine Finset.prod_congr ?_ fun _ _ ↦ rfl
  ext e
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff,
    Finset.mem_coe, Sym2.mem_diagSet]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun hdiag ↦ hS e h hdiag⟩⟩

/-- Crude edge-count bound: `|E(⊤)| ≤ k·k` on `Fin k`. -/
private theorem top_edgeFinset_card_le :
    (⊤ : SimpleGraph (Fin k)).edgeFinset.card ≤ k * k := by
  calc (⊤ : SimpleGraph (Fin k)).edgeFinset.card
      ≤ Fintype.card (Sym2 (Fin k)) := Finset.card_le_univ _
    _ = (k + 1).choose 2 := by rw [Sym2.card, Fintype.card_fin]
    _ ≤ k * k := by
        rw [Nat.choose_two_right]
        simp only [Nat.add_sub_cancel]
        rcases Nat.eq_zero_or_pos k with hk | hk
        · simp [hk]
        · refine Nat.div_le_of_le_mul ?_
          calc (k + 1) * k ≤ 2 * k * k :=
                Nat.mul_le_mul_right k (by omega : k + 1 ≤ 2 * k)
            _ = 2 * (k * k) := by ring

/-- The integrand of the sampled-graph mass: edges of `G` contribute `W`, non-edges
contribute `1 − W`. -/
noncomputable def sampleIntegrand (W : Graphon α μ) (G : SimpleGraph (Fin k))
    (x : Fin k → α) : ℝ :=
  (∏ e ∈ G.edgeFinset, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) *
    ∏ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset,
      (1 - W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2))

/-- **The sampled graph distribution**: the probability that the W-random graph
`G(k, W)` equals `G`. Sample `k` i.i.d. positions, then include each pair `{i, j}` as an
edge independently with probability `W(xᵢ, xⱼ)`; integrating out the positions gives
this mass directly, with no random-variable formalism. -/
noncomputable def sampleMass (W : Graphon α μ) (G : SimpleGraph (Fin k)) : ℝ :=
  ∫ x : Fin k → α, sampleIntegrand W G x ∂Measure.pi (fun _ ↦ μ)

omit [IsProbabilityMeasure μ] in
/-- Pointwise inclusion–exclusion: the sampled-graph integrand is a signed sum of plain
edge products over supergraph edge sets. -/
private theorem sampleIntegrand_eq_sum (W : Graphon α μ) (G : SimpleGraph (Fin k))
    (x : Fin k → α) :
    sampleIntegrand W G x =
      ∑ S ∈ ((⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset).powerset,
        (-1 : ℝ) ^ S.card *
          ∏ e ∈ G.edgeFinset ∪ S, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) := by
  set w : Sym2 (Fin k) → ℝ := fun e ↦ W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)
    with hw
  have hexp : ∏ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset, (1 - w e) =
      ∑ S ∈ ((⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset).powerset,
        (-1 : ℝ) ^ S.card * ∏ e ∈ S, w e := by
    have h1 : ∀ e, 1 - w e = -w e + 1 := fun e ↦ by ring
    calc ∏ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset, (1 - w e)
        = ∏ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset, (-w e + 1) :=
          Finset.prod_congr rfl fun e _ ↦ h1 e
      _ = ∑ S ∈ ((⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset).powerset,
            (∏ e ∈ S, -w e) *
              ∏ e ∈ ((⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset) \ S, (1 : ℝ) :=
          Finset.prod_add _ _ _
      _ = ∑ S ∈ ((⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset).powerset,
            (-1 : ℝ) ^ S.card * ∏ e ∈ S, w e := by
          refine Finset.sum_congr rfl fun S _ ↦ ?_
          rw [Finset.prod_const_one, mul_one,
            show (fun e ↦ -w e) = fun e ↦ (-1 : ℝ) * w e from funext fun e ↦ by ring,
            Finset.prod_mul_distrib, Finset.prod_const]
  calc sampleIntegrand W G x
      = (∏ e ∈ G.edgeFinset, w e) *
          ∑ S ∈ ((⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset).powerset,
            (-1 : ℝ) ^ S.card * ∏ e ∈ S, w e := by rw [sampleIntegrand, ← hexp]
    _ = ∑ S ∈ ((⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset).powerset,
          (-1 : ℝ) ^ S.card * ∏ e ∈ G.edgeFinset ∪ S, w e := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S hS ↦ ?_
        have hdisj : Disjoint G.edgeFinset S :=
          Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hS)
            Finset.sdiff_disjoint.symm
        rw [Finset.prod_union hdisj]
        ring

/-- The union of `G`'s edges with a set of non-edges contains no diagonal pairs. -/
private theorem union_not_isDiag {G : SimpleGraph (Fin k)} {S : Finset (Sym2 (Fin k))}
    (hS : S ∈ ((⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset).powerset) :
    ∀ e ∈ G.edgeFinset ∪ S, ¬ e.IsDiag := by
  intro e he
  rcases Finset.mem_union.mp he with h | h
  · exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp h)
  · exact not_isDiag_of_mem_top
      (((Finset.mem_powerset.mp hS).trans Finset.sdiff_subset) h)

omit [IsProbabilityMeasure μ] in
/-- The sampled-graph integrand as a function: a signed sum of hom-density integrands
of graphs on `Fin k`. -/
private theorem sampleIntegrand_eq_sum_integrand (W : Graphon α μ)
    (G : SimpleGraph (Fin k)) :
    sampleIntegrand W G = fun x ↦
      ∑ S ∈ ((⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset).powerset,
        (-1 : ℝ) ^ S.card *
          homDensityIntegrand (SimpleGraph.fromEdgeSet (↑(G.edgeFinset ∪ S))) W x := by
  funext x
  rw [sampleIntegrand_eq_sum]
  refine Finset.sum_congr rfl fun S hS ↦ ?_
  rw [homDensityIntegrand_fromEdgeSet (union_not_isDiag hS)]

/-- The sampled-graph integrand is integrable (as a finite signed sum of integrable
hom-density integrands). Public: used by the concentration scaffold. -/
theorem sampleIntegrand_integrable (W : Graphon α μ) (G : SimpleGraph (Fin k)) :
    Integrable (sampleIntegrand W G) (Measure.pi (fun _ : Fin k ↦ μ)) := by
  rw [sampleIntegrand_eq_sum_integrand]
  exact integrable_finsetSum _ fun S _ ↦
    (homDensityIntegrand_integrable _ W).const_mul _

/-- **Mass expansion**: each sampled-graph mass is a finite signed sum of homomorphism
densities of graphs on `Fin k` (inclusion–exclusion over the non-edges of `G`). -/
theorem sampleMass_eq_sum_homDensity (W : Graphon α μ) (G : SimpleGraph (Fin k)) :
    sampleMass W G =
      ∑ S ∈ ((⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset).powerset,
        (-1 : ℝ) ^ S.card *
          homDensity
            (SimpleGraph.fromEdgeSet (↑(G.edgeFinset ∪ S) : Set (Sym2 (Fin k)))) W := by
  rw [sampleMass, sampleIntegrand_eq_sum_integrand]
  rw [integral_finsetSum _ fun S _ ↦ (homDensityIntegrand_integrable _ W).const_mul _]
  exact Finset.sum_congr rfl fun S _ ↦ by
    rw [integral_const_mul, ← homDensity_eq_integral]

/-- All edge evaluations over `⊤` lie in `[0,1]` almost everywhere (public: used by the
concentration scaffold for a.e. nonnegativity of conditional masses). -/
theorem ae_top_edges_mem_Icc (W : Graphon α μ) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin k ↦ μ),
      ∀ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset,
        W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1 := by
  have h_edges : ∀ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset,
      ∀ᵐ x ∂Measure.pi (fun _ : Fin k ↦ μ),
        W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1 :=
    fun e he ↦ graphonEval_mem_Icc_ae W (edge_out_ne (SimpleGraph.mem_edgeFinset.mp he))
  revert h_edges
  generalize (⊤ : SimpleGraph (Fin k)).edgeFinset = s
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s' _ ih hs
    simp only [Finset.mem_insert, forall_eq_or_imp] at hs ⊢
    filter_upwards [hs.1, ih hs.2] with x hx1 hx2
    exact ⟨hx1, hx2⟩

/-- Sampled-graph masses are nonnegative. -/
theorem sampleMass_nonneg (W : Graphon α μ) (G : SimpleGraph (Fin k)) :
    0 ≤ sampleMass W G := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_top_edges_mem_Icc W] with x hx
  refine mul_nonneg (Finset.prod_nonneg fun e he ↦ ?_) (Finset.prod_nonneg fun e he ↦ ?_)
  · exact (hx e (SimpleGraph.edgeFinset_mono le_top he)).1
  · have := (hx e (Finset.sdiff_subset he)).2
    linarith

omit [IsProbabilityMeasure μ] in
/-- Pointwise: the sampled-graph integrands sum to `1` over all graphs on `Fin k`
(public: this is the conditional-distribution normalization used by the concentration
scaffold). -/
theorem sum_sampleIntegrand_eq_one (W : Graphon α μ) (x : Fin k → α) :
    ∑ G : SimpleGraph (Fin k), sampleIntegrand W G x = 1 := by
  set w : Sym2 (Fin k) → ℝ := fun e ↦ W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)
  have hbij : ∑ G : SimpleGraph (Fin k), sampleIntegrand W G x =
      ∑ S ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset.powerset,
        (∏ e ∈ S, w e) * ∏ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset \ S, (1 - w e) := by
    refine Finset.sum_nbij' (fun G ↦ G.edgeFinset)
      (fun S ↦ SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin k)))) ?_ ?_ ?_ ?_ ?_
    · exact fun G _ ↦ Finset.mem_powerset.mpr (SimpleGraph.edgeFinset_mono le_top)
    · exact fun S _ ↦ Finset.mem_univ _
    · intro G _
      rw [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet]
    · intro S hS
      ext e
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet,
        Set.mem_sdiff, Finset.mem_coe, Sym2.mem_diagSet]
      exact ⟨fun h ↦ h.1, fun h ↦ ⟨h,
        fun hdiag ↦ not_isDiag_of_mem_top ((Finset.mem_powerset.mp hS) h) hdiag⟩⟩
    · exact fun G _ ↦ rfl
  rw [hbij, ← Finset.prod_add]
  calc ∏ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset, (w e + (1 - w e))
      = ∏ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset, (1 : ℝ) :=
        Finset.prod_congr rfl fun e _ ↦ by ring
    _ = 1 := Finset.prod_const_one

/-- **The sampled-graph masses form a probability distribution**: they sum to `1`. -/
theorem sampleMass_sum_eq_one (W : Graphon α μ) :
    ∑ G : SimpleGraph (Fin k), sampleMass W G = 1 := by
  have hswap : ∑ G : SimpleGraph (Fin k), sampleMass W G =
      ∫ x : Fin k → α, ∑ G : SimpleGraph (Fin k), sampleIntegrand W G x
        ∂Measure.pi (fun _ ↦ μ) :=
    (integral_finsetSum _ fun G _ ↦ sampleIntegrand_integrable W G).symm
  rw [hswap]
  calc ∫ x : Fin k → α, ∑ G : SimpleGraph (Fin k), sampleIntegrand W G x
        ∂Measure.pi (fun _ ↦ μ)
      = ∫ _ : Fin k → α, (1 : ℝ) ∂Measure.pi (fun _ ↦ μ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        exact sum_sampleIntegrand_eq_one W x
    _ = 1 := by simp

/-- **Mass closeness from hom-density closeness**: if all hom densities of graphs on
`Fin k` agree within `δ`, each sampled-graph mass agrees within `2^(k·k) · δ`. -/
theorem sampleMass_close_of_homDensity_close (U W : Graphon α μ) (δ : ℝ)
    (h : ∀ (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
      |homDensity F U - homDensity F W| ≤ δ)
    (G : SimpleGraph (Fin k)) :
    |sampleMass U G - sampleMass W G| ≤ 2 ^ (k * k) * δ := by
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) (by simpa using h (⊥ : SimpleGraph (Fin k)))
  rw [sampleMass_eq_sum_homDensity, sampleMass_eq_sum_homDensity,
    ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _)
    (le_trans (Finset.sum_le_sum (g := fun _ ↦ δ) fun S _ ↦ ?_) ?_)
  · rw [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact h _
  · rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hδ
    rw [Finset.card_powerset]
    have h1 : ((⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset).card ≤ k * k :=
      le_trans (Finset.card_le_card Finset.sdiff_subset) top_edgeFinset_card_le
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) h1

/-- There are at most `2^(k·k)` graphs on `Fin k`. -/
private theorem card_simpleGraph_le : Fintype.card (SimpleGraph (Fin k)) ≤ 2 ^ (k * k) := by
  have hinj : Function.Injective
      (fun G : SimpleGraph (Fin k) ↦ G.edgeFinset) := fun G₁ G₂ hGG ↦ by
    have h2 : G₁.edgeFinset = G₂.edgeFinset := hGG
    have h3 : (↑G₁.edgeFinset : Set (Sym2 (Fin k))) = ↑G₂.edgeFinset := by rw [h2]
    rw [SimpleGraph.coe_edgeFinset, SimpleGraph.coe_edgeFinset] at h3
    exact SimpleGraph.edgeSet_inj.mp h3
  calc Fintype.card (SimpleGraph (Fin k))
      ≤ Fintype.card (Finset (Sym2 (Fin k))) := Fintype.card_le_of_injective _ hinj
    _ = 2 ^ Fintype.card (Sym2 (Fin k)) := Fintype.card_finset
    _ ≤ 2 ^ (k * k) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        calc Fintype.card (Sym2 (Fin k)) = (k + 1).choose 2 := by
              rw [Sym2.card, Fintype.card_fin]
          _ ≤ k * k := by
              rw [Nat.choose_two_right]
              simp only [Nat.add_sub_cancel]
              rcases Nat.eq_zero_or_pos k with hk | hk
              · simp [hk]
              · refine Nat.div_le_of_le_mul ?_
                calc (k + 1) * k ≤ 2 * k * k :=
                      Nat.mul_le_mul_right k (by omega : k + 1 ≤ 2 * k)
                  _ = 2 * (k * k) := by ring

/-- **Total-variation closeness from hom-density closeness** — the deliverable bridge
for the BCLSV sampling route: if all hom densities of graphs on `Fin k` agree within
`δ`, the sampled graph distributions of `U` and `W` agree within `4^(k·k) · δ` in
(twice the) total variation distance. -/
theorem sampleDistribution_tv_close_of_homDensity_close (U W : Graphon α μ) (δ : ℝ)
    (h : ∀ (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
      |homDensity F U - homDensity F W| ≤ δ) :
    ∑ G : SimpleGraph (Fin k), |sampleMass U G - sampleMass W G| ≤
      2 ^ (k * k) * (2 ^ (k * k) * δ) := by
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) (by simpa using h (⊥ : SimpleGraph (Fin k)))
  calc ∑ G : SimpleGraph (Fin k), |sampleMass U G - sampleMass W G|
      ≤ ∑ _G : SimpleGraph (Fin k), 2 ^ (k * k) * δ :=
        Finset.sum_le_sum fun G _ ↦ sampleMass_close_of_homDensity_close U W δ h G
    _ = (Fintype.card (SimpleGraph (Fin k)) : ℝ) * (2 ^ (k * k) * δ) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ ≤ 2 ^ (k * k) * (2 ^ (k * k) * δ) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast card_simpleGraph_le

omit [IsProbabilityMeasure μ] in
/-- **Event extraction from total variation**: any event's probabilities under the two
sampled distributions differ by at most the (summed) total variation distance. -/
theorem sum_sampleMass_event_sub_le (U W : Graphon α μ)
    (A : Finset (SimpleGraph (Fin k))) (tv : ℝ)
    (htv : ∑ G : SimpleGraph (Fin k), |sampleMass U G - sampleMass W G| ≤ tv) :
    ∑ G ∈ A, sampleMass U G - ∑ G ∈ A, sampleMass W G ≤ tv := by
  calc ∑ G ∈ A, sampleMass U G - ∑ G ∈ A, sampleMass W G
      = ∑ G ∈ A, (sampleMass U G - sampleMass W G) := (Finset.sum_sub_distrib _ _).symm
    _ ≤ ∑ G ∈ A, |sampleMass U G - sampleMass W G| :=
        Finset.sum_le_sum fun G _ ↦ le_abs_self _
    _ ≤ ∑ G : SimpleGraph (Fin k), |sampleMass U G - sampleMass W G| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
          (fun G _ _ ↦ abs_nonneg _)
    _ ≤ tv := htv

end SampleDistribution


end Graphon
