/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.SamplingLaw
import Graphon.InverseCounting

/-!
# The exact finite-sampling formula (issue #33, existence step 5, part 1)

Sampling `k` vertices from the embedded graphon of a finite graph `H` on `n` vertices
is exactly uniform sampling of a vertex map `Fin k → Fin n` followed by pulling back:

* `Graphon.homDensity_ofSimpleGraphOn` — the homomorphism density of `F` in the
  embedded graphon is the average over all maps `f` of the indicator
  `F ≤ H.comap f` (the now-public step-graphon engine
  `homDensity_mkStepGraphon_eq_weightedHomSum`, specialized to the equipartition);
* `Graphon.sampleMass_ofSimpleGraphOn` — **the exact finite-sampling formula**:
  `sampleMass (ofSimpleGraphOn H) G = n⁻ᵏ ∑_f [H.comap f = G]`, by
  `upperSum_injective` (both sides have upper transform equal to the hom density).

The collision bound (splitting maps into injective and noninjective) and the
identification of the empirical mixing limits build on this.
-/

open MeasureTheory

open scoped Classical

namespace Graphon

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ]

/-- The coefficient of `ofSimpleGraphOn` at a pair of equipartition cells is the
adjacency indicator. -/
private theorem ofSimpleGraphOn_coeff {n : ℕ} [NeZero n] (H : SimpleGraph (Fin n))
    (i j : Fin n) :
    (fun S T ↦
      if hST : (∃ i', equipartitionCell (α := α) (μ := μ) n i' = S) ∧
          (∃ j', equipartitionCell (α := α) (μ := μ) n j' = T)
      then (if H.Adj hST.1.choose hST.2.choose then (1 : ℝ) else 0) else 0)
      (equipartitionCell (α := α) (μ := μ) n i)
      (equipartitionCell (α := α) (μ := μ) n j) =
      if H.Adj i j then 1 else 0 := by
  have hex : (∃ i', equipartitionCell (α := α) (μ := μ) n i' =
      equipartitionCell (α := α) (μ := μ) n i) ∧
      (∃ j', equipartitionCell (α := α) (μ := μ) n j' =
        equipartitionCell (α := α) (μ := μ) n j) := ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
  simp only [dif_pos hex]
  rw [equipartitionCell_injective n hex.1.choose_spec,
    equipartitionCell_injective n hex.2.choose_spec]

/-- Adjacency at the `Quot.out` representatives of a member edge. -/
private theorem adj_out_of_mem_edgeFinset {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    G.Adj (Quot.out e).1 (Quot.out e).2 := by
  have hmem := SimpleGraph.mem_edgeFinset.mp he
  rwa [← e.out_eq] at hmem

/-- The 0/1 edge product is the subgraph indicator. -/
private theorem prod_adj_indicator {n k : ℕ} (H : SimpleGraph (Fin n))
    (F : SimpleGraph (Fin k)) [DecidableRel F.Adj] (σ : Fin k → Fin n) :
    (∏ e ∈ F.edgeFinset,
      if H.Adj (σ (Quot.out e).1) (σ (Quot.out e).2) then (1 : ℝ) else 0) =
      if F ≤ H.comap σ then 1 else 0 := by
  by_cases hle : F ≤ H.comap σ
  · rw [if_pos hle]
    exact Finset.prod_eq_one fun e he =>
      if_pos (hle (adj_out_of_mem_edgeFinset he))
  · rw [if_neg hle]
    have hle' : ¬ ∀ a b, F.Adj a b → (H.comap σ).Adj a b :=
      fun hall => hle fun {a b} hab => hall a b hab
    push Not at hle'
    obtain ⟨a, b, hFab, hnab⟩ := hle'
    refine Finset.prod_eq_zero
      (SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet F).mpr hFab)) ?_
    rw [if_neg]
    intro hadj
    have hrel : Sym2.Rel (Fin k) (Quot.out s(a, b)) (a, b) := by
      apply (Equivalence.quot_mk_eq_iff Sym2.Rel.is_equivalence _ _).mp
      simp only [Quot.out_eq]
    rcases Sym2.rel_iff'.mp hrel with h | h
    · rw [h] at hadj
      exact hnab hadj
    · rw [show Quot.out s(a, b) = (b, a) by simpa [Prod.swap] using h] at hadj
      exact hnab ((H.comap σ).adj_symm hadj)

/-- **Hom densities in an embedded finite graph are map averages**: the density of `F`
in `ofSimpleGraphOn H` is the proportion of vertex maps `f` with `F ≤ H.comap f`. -/
theorem homDensity_ofSimpleGraphOn {n : ℕ} [NeZero n] (H : SimpleGraph (Fin n))
    {k : ℕ} (F : SimpleGraph (Fin k)) [DecidableRel F.Adj] :
    homDensity F (ofSimpleGraphOn (α := α) (μ := μ) H) =
      ((n : ℝ)⁻¹) ^ k *
        ∑ f : Fin k → Fin n, if F ≤ H.comap f then 1 else 0 := by
  have hengine := homDensity_mkStepGraphon_eq_weightedHomSum
    (equipartition (α := α) (μ := μ) n)
    (fun S T ↦
      if hST : (∃ i', equipartitionCell (α := α) (μ := μ) n i' = S) ∧
          (∃ j', equipartitionCell (α := α) (μ := μ) n j' = T)
      then (if H.Adj hST.1.choose hST.2.choose then (1 : ℝ) else 0) else 0)
    (fun S _ T _ ↦ by
      by_cases h1 : (∃ i, equipartitionCell (α := α) (μ := μ) n i = S) ∧
          (∃ j, equipartitionCell (α := α) (μ := μ) n j = T)
      · rw [dif_pos h1, dif_pos ⟨h1.2, h1.1⟩]
        by_cases hadj : H.Adj h1.1.choose h1.2.choose
        · rw [if_pos hadj, if_pos (H.adj_symm hadj)]
        · rw [if_neg hadj, if_neg (fun hc ↦ hadj (H.adj_symm hc))]
      · rw [dif_neg h1, dif_neg (fun hc ↦ h1 ⟨hc.2, hc.1⟩)])
    (fun S _ T _ ↦ by split_ifs <;> norm_num)
    (equipartitionCell (α := α) (μ := μ) n) (equipartitionCell_mem n)
    (equipartitionCell_surjOn n) (equipartitionCell_injective n) k F
  rw [show ofSimpleGraphOn (α := α) (μ := μ) H = mkStepGraphon _ _ _ _ from rfl, hengine]
  unfold weightedHomSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hw : (∏ _v : Fin k, (μ (equipartitionCell (α := α) (μ := μ) n (σ _v))).toReal) =
      ((n : ℝ)⁻¹) ^ k := by
    rw [Finset.prod_congr rfl fun v _ => equipartitionCell_measure n (σ v),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hc : (∏ e ∈ F.edgeFinset,
      (fun S T ↦
        if hST : (∃ i', equipartitionCell (α := α) (μ := μ) n i' = S) ∧
            (∃ j', equipartitionCell (α := α) (μ := μ) n j' = T)
        then (if H.Adj hST.1.choose hST.2.choose then (1 : ℝ) else 0) else 0)
        (equipartitionCell (α := α) (μ := μ) n (σ (Quot.out e).1))
        (equipartitionCell (α := α) (μ := μ) n (σ (Quot.out e).2))) =
      if F ≤ H.comap σ then 1 else 0 := by
    rw [Finset.prod_congr rfl fun e _ =>
      ofSimpleGraphOn_coeff H (σ (Quot.out e).1) (σ (Quot.out e).2)]
    exact prod_adj_indicator H F σ
  rw [hw, hc]

/-- **The exact finite-sampling formula** (Diaconis–Janson existence, step 5 part 1):
the sample mass of `G` under the embedded graphon of `H` is the proportion of vertex
maps `f : Fin k → Fin n` with `H.comap f = G`. -/
theorem sampleMass_ofSimpleGraphOn {n : ℕ} [NeZero n] (H : SimpleGraph (Fin n))
    {k : ℕ} (G : SimpleGraph (Fin k)) :
    sampleMass (ofSimpleGraphOn (α := α) (μ := μ) H) G =
      ((n : ℝ)⁻¹) ^ k *
        ∑ f : Fin k → Fin n, if H.comap f = G then 1 else 0 := by
  have key : (fun G : SimpleGraph (Fin k) =>
      sampleMass (ofSimpleGraphOn (α := α) (μ := μ) H) G) = fun G =>
      ((n : ℝ)⁻¹) ^ k * ∑ f : Fin k → Fin n, if H.comap f = G then 1 else 0 := by
    apply upperSum_injective
    intro F
    rw [upperSum_sampleMass, homDensity_ofSimpleGraphOn]
    simp only [upperSum]
    have hswap : ∀ (f : Fin k → Fin n) (G : SimpleGraph (Fin k)),
        (if F ≤ G then (if H.comap f = G then ((n : ℝ)⁻¹) ^ k else 0) else 0) =
        if G = H.comap f then
          (if F ≤ H.comap f then ((n : ℝ)⁻¹) ^ k else 0) else 0 := by
      intro f G
      by_cases h1 : G = H.comap f
      · subst h1
        simp
      · rw [if_neg h1, if_neg (fun h => h1 (Eq.symm h))]
        split <;> rfl
    calc ((n : ℝ)⁻¹) ^ k * ∑ f : Fin k → Fin n, (if F ≤ H.comap f then (1 : ℝ) else 0)
        = ∑ f : Fin k → Fin n, (if F ≤ H.comap f then ((n : ℝ)⁻¹) ^ k else 0) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun f _ => by split <;> simp
      _ = ∑ f : Fin k → Fin n, ∑ G : SimpleGraph (Fin k),
            (if F ≤ G then (if H.comap f = G then ((n : ℝ)⁻¹) ^ k else 0) else 0) := by
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [Finset.sum_congr rfl fun G _ => hswap f G,
            Finset.sum_ite_eq' Finset.univ (H.comap f)
              (fun _ => if F ≤ H.comap f then ((n : ℝ)⁻¹) ^ k else 0)]
          simp
      _ = ∑ G : SimpleGraph (Fin k), ∑ f : Fin k → Fin n,
            (if F ≤ G then (if H.comap f = G then ((n : ℝ)⁻¹) ^ k else 0) else 0) :=
          Finset.sum_comm
      _ = ∑ G : SimpleGraph (Fin k),
            (if F ≤ G then ((n : ℝ)⁻¹) ^ k *
              ∑ f : Fin k → Fin n, (if H.comap f = G then (1 : ℝ) else 0) else 0) := by
          refine Finset.sum_congr rfl fun G _ => ?_
          split
          · rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun f _ => by split <;> simp
          · simp
  exact congrFun key G

end Graphon
