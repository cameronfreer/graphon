/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Sampling
import Graphon.Compactness

/-!
# The sampling route to the quantitative inverse counting lemma

This file hosts the space-generic good-mass layer over the sampled graph distribution
(`Graphon/Sampling.lean`) and derives the partition-size-independent quantitative
inverse counting lemma from the (sorried) First Sampling Lemma.

Everything is stated over an arbitrary atomless standard Borel probability space: the
classical sampling lemma is not inherently about `[0,1]` — the unit interval is just a
convenient presentation — and the space-generic statement is the honest interface, since
transferring cut distances between spaces would require the measure isomorphism theorem
(`α ≅ ([0,1], volume)` mod 0), which mathlib currently lacks (it is Rokhlin-adjacent and
will be developed with that blocker).

## Main declarations

* `Graphon.exists_partition_with_measures` — partitions with prescribed cell measures
  (moved from `Graphon/InverseCounting.lean`)
* `Graphon.ofSimpleGraphOn` — the finite-graph step-graphon embedding on an arbitrary
  atomless standard Borel space (equal-measure cells)
* `Graphon.sampleGoodMassOn` — probability that the sampled graph lands within cut
  distance `ε` of `W`
* `Graphon.first_sampling_lemma` — THE analytic gap of the sampling route (sorried):
  some `k` works for every graphon on the space simultaneously
* `Graphon.sampling_quantitative_icl` — sampling ⟹ the `K`-independent quantitative
  ICL, by the event-intersection argument (PROVED)

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Lemma 10.16
* Borgs–Chayes–Lovász–Sós–Vesztergombi, *Convergent sequences of dense graphs I*,
  Theorem 4.6
-/

open MeasureTheory Set Filter Finset

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

variable [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

/-- Build a `MeasurablePartition` with `K` cells having prescribed measures. (Moved here
from `Graphon/InverseCounting.lean`, 2026-07-07, and de-privatized so the sampling layer
can build finite-graph embeddings on arbitrary atomless standard Borel spaces.) -/
theorem exists_partition_with_measures {K : ℕ}
    (w : Fin K → ℝ) (hw_nn : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1) :
    ∃ (P : MeasurablePartition α μ) (ι : Fin K → Set α),
      (∀ i, ι i ∈ P.parts) ∧
      Function.Injective ι ∧
      (∀ S ∈ P.parts, ∃ i, ι i = S) ∧
      P.parts.card = K ∧
      ∀ i, (μ (ι i)).toReal = w i := by
  -- K = 0 impossible
  rcases Nat.eq_zero_or_pos K with rfl | hK_pos
  · simp at hw_sum
  -- Derive Infinite α
  haveI : Infinite α := by
    by_contra h; rw [not_infinite_iff_finite] at h; haveI := h
    exact absurd (Set.Finite.measure_zero Set.finite_univ μ) (by simp [measure_univ])
  -- K distinct points
  set ξ : Fin K → α := (Infinite.natEmbedding α) ∘ Fin.val
  have hξ_inj : Function.Injective ξ := (Infinite.natEmbedding α).injective.comp Fin.val_injective
  -- Reserve set R (finite, null, measurable)
  have hR_finite : (Set.range ξ).Finite := Set.finite_range ξ
  have hR_meas : MeasurableSet (Set.range ξ) := hR_finite.measurableSet
  have hR_null : μ (Set.range ξ) = 0 := hR_finite.measure_zero μ
  -- Working set S₀ = univ \ R
  set S₀ := Set.univ \ Set.range ξ with hS₀_def
  have hS₀_meas : MeasurableSet S₀ := MeasurableSet.univ.diff hR_meas
  have hS₀_eq : μ S₀ = 1 := by
    have : μ Set.univ = μ S₀ + μ (Set.range ξ) := by
      rw [← measure_union (Set.disjoint_sdiff_left) hR_meas, Set.sdiff_union_self,
          Set.union_eq_self_of_subset_right (Set.subset_univ _)]
    rw [measure_univ, hR_null, add_zero] at this; exact this.symm
  -- Recursive carving of S₀: build C_i ⊆ S₀ with μ(C_i) = ofReal(w i)
  -- Process indices 0..K-2 by IVT, last index absorbs remainder
  suffices h_carve : ∃ C : Fin K → Set α,
      (∀ i, MeasurableSet (C i)) ∧ (∀ i, C i ⊆ S₀) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      μ (S₀ \ ⋃ i, C i) = 0 ∧ (∀ i, μ (C i) = ENNReal.ofReal (w i)) by
    obtain ⟨C, hCm, hCs, hCd, hCcov, hCe⟩ := h_carve
    -- Decorate: ι i = C i ∪ {ξ i}
    set ι : Fin K → Set α := fun i => C i ∪ {ξ i}
    -- ι i are pairwise disjoint
    have hι_disj : ∀ i j, i ≠ j → Disjoint (ι i) (ι j) := by
      intro i j hij
      apply Disjoint.union_left
      · apply Disjoint.union_right
        · exact hCd i j hij
        · rw [Set.disjoint_left]; intro x hx hξ
          rw [Set.mem_singleton_iff] at hξ; subst hξ
          exact (hCs i hx).2 ⟨j, rfl⟩
      · apply Disjoint.union_right
        · rw [Set.disjoint_left]; intro x hx hC
          rw [Set.mem_singleton_iff] at hx; subst hx
          exact (hCs j hC).2 ⟨i, rfl⟩
        · rw [Set.disjoint_left]; intro x hx hy
          rw [Set.mem_singleton_iff] at hx hy
          exact hij (hξ_inj (hx ▸ hy))
    -- ι is injective
    have hι_inj : Function.Injective ι := by
      intro i j hij
      by_contra hne
      exact Set.disjoint_left.mp (hι_disj i j hne) (Set.mem_union_right _ (Set.mem_singleton _))
        (hij ▸ Set.mem_union_right _ (Set.mem_singleton _))
    -- ι i are measurable
    have hι_meas : ∀ i, MeasurableSet (ι i) :=
      fun i => (hCm i).union (measurableSet_singleton _)
    -- μ(ι i) = ofReal(w i) (singleton has measure 0)
    have hι_measure : ∀ i, μ (ι i) = ENNReal.ofReal (w i) := by
      intro i; show μ (C i ∪ {ξ i}) = _
      have h_disj : Disjoint (C i) {ξ i} := by
        rw [Set.disjoint_left]; intro x hx hξ
        rw [Set.mem_singleton_iff] at hξ; subst hξ
        exact (hCs i hx).2 ⟨i, rfl⟩
      rw [measure_union h_disj (measurableSet_singleton _),
          MeasureTheory.NoAtoms.measure_singleton, add_zero, hCe i]
    -- Build MeasurablePartition
    haveI : DecidableEq (Set α) := Classical.decEq _
    set parts := Finset.image ι Finset.univ
    have h_card : parts.card = K := by
      rw [Finset.card_image_of_injective _ hι_inj, Finset.card_univ, Fintype.card_fin]
    refine ⟨⟨parts, fun S hS => ?_, ?_, ?_⟩, ι, ?_, hι_inj, ?_, h_card, ?_⟩
    -- measurable_parts
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (show S ∈ Finset.image ι Finset.univ from hS)
      exact hι_meas i
    -- pairwiseDisjoint
    · intro S hS T hT hne
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (show S ∈ Finset.image ι Finset.univ from hS)
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (show T ∈ Finset.image ι Finset.univ from hT)
      exact hι_disj i j (fun h => hne (congrArg ι h))
    -- ae_covers: complement ⊆ S₀ \ ⋃ C i, which is null
    · rw [ae_iff]
      refine le_antisymm ?_ (zero_le)
      calc μ {x | ¬∃ S ∈ parts, x ∈ S}
          ≤ μ (S₀ \ ⋃ i, C i) := measure_mono (fun x hx => by
            push Not at hx -- hx : ∀ S ∈ parts, x ∉ S
            refine ⟨⟨Set.mem_univ _, fun hxR => ?_⟩, fun hxC => ?_⟩
            · obtain ⟨j, rfl⟩ := hxR
              exact hx (ι j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
                (Set.mem_union_right _ rfl)
            · rw [Set.mem_iUnion] at hxC; obtain ⟨i, hi⟩ := hxC
              exact hx (ι i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
                (Set.mem_union_left _ hi))
        _ = 0 := hCcov
    -- ι i ∈ parts
    · exact fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    -- surjectivity
    · intro S hS; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS; exact ⟨i, rfl⟩
    -- measures
    · intro i; rw [hι_measure i, ENNReal.toReal_ofReal (hw_nn i)]
  -- Now prove h_carve: build C by recursion on K
  -- Helper: carve n cells from measurable set S with prescribed measures
  suffices h_gen : ∀ (n : ℕ) (S : Set α) (hS : MeasurableSet S) (hS_ne_top : μ S ≠ ⊤)
      (w' : Fin n → ℝ) (hw'_nn : ∀ i, 0 ≤ w' i)
      (hw'_sum : ENNReal.ofReal (∑ i, w' i) = μ S),
      ∃ C : Fin n → Set α,
        (∀ i, MeasurableSet (C i)) ∧ (∀ i, C i ⊆ S) ∧
        (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
        μ (S \ ⋃ i, C i) = 0 ∧ (∀ i, μ (C i) = ENNReal.ofReal (w' i)) by
    have hS₀_ne_top : μ S₀ ≠ ⊤ := by rw [hS₀_eq]; exact ENNReal.one_ne_top
    have hw_ofReal : ENNReal.ofReal (∑ i, w i) = μ S₀ := by
      rw [hS₀_eq, hw_sum, ENNReal.ofReal_one]
    exact h_gen K S₀ hS₀_meas hS₀_ne_top w hw_nn hw_ofReal
  intro n; induction n with
  | zero =>
    intro S hS hS_ne_top w' _ hw'_sum
    refine ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, ?_, fun i => i.elim0⟩
    simp only [Set.iUnion_of_empty, Set.sdiff_empty]; simpa using hw'_sum.symm
  | succ n ih =>
    intro S hS hS_ne_top w' hw'_nn hw'_sum
    -- Carve first cell C₀ ⊆ S with μ(C₀) = ENNReal.ofReal(w' 0)
    have h_w0_le : ENNReal.ofReal (w' 0) ≤ μ S := by
      rw [← hw'_sum]; apply ENNReal.ofReal_le_ofReal
      exact Finset.single_le_sum (fun i _ => hw'_nn i) (Finset.mem_univ 0)
    obtain ⟨C₀, hC₀m, hC₀s, hC₀e⟩ := exists_measurable_subset_of_measure hS h_w0_le
    -- Remaining space S' = S \ C₀
    set S' := S \ C₀ with hS'_def
    have hS'm : MeasurableSet S' := hS.diff hC₀m
    have hS'_ne_top : μ S' ≠ ⊤ := ne_top_of_le_ne_top hS_ne_top (measure_mono sdiff_subset)
    have hw'_rest_sum : ENNReal.ofReal (∑ i : Fin n, w' i.succ) = μ S' := by
      rw [measure_sdiff hC₀s hC₀m.nullMeasurableSet (by rw [hC₀e]; exact ENNReal.ofReal_ne_top),
          hC₀e, ← hw'_sum, Fin.sum_univ_succ,
          ENNReal.ofReal_add (hw'_nn 0) (Finset.sum_nonneg (fun i _ => hw'_nn _))]
      exact (ENNReal.add_sub_cancel_left ENNReal.ofReal_ne_top).symm
    obtain ⟨C', hC'm, hC's, hC'd, hC'cov, hC'e⟩ :=
      ih S' hS'm hS'_ne_top (fun i => w' i.succ) (fun i => hw'_nn _) hw'_rest_sum
    refine ⟨Fin.cons C₀ C', ?_, ?_, ?_, ?_, ?_⟩
    -- Measurable
    · intro i; refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_zero]; exact hC₀m
      · rw [Fin.cons_succ]; exact hC'm j
    -- Subset
    · intro i; refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_zero]; exact hC₀s
      · rw [Fin.cons_succ]; exact (hC's j).trans sdiff_subset
    -- Disjoint: introduce hij AFTER case split so types are correct
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
        intro hij <;> simp only [Fin.cons_zero, Fin.cons_succ]
      · exact absurd rfl hij
      · exact Set.disjoint_of_subset_right (hC's _) disjoint_sdiff_right
      · exact (Set.disjoint_of_subset_right (hC's _) disjoint_sdiff_right).symm
      · exact hC'd _ _ (fun h => hij (congrArg Fin.succ h))
    -- Coverage: S \ ⋃ i, Fin.cons C₀ C' i = 0
    · -- S \ ⋃ i, T i = S' \ ⋃ i, C' i where T i = Fin.cons C₀ C'
      -- Key: ⋃ i, T i = C₀ ∪ ⋃ j, C' j, so S \ (C₀ ∪ ⋃ C') = (S \ C₀) \ ⋃ C' = S' \ ⋃ C'
      suffices h : ∀ x, x ∈ S \ ⋃ i, @Fin.cons _ (fun _ => Set α) C₀ C' i →
          x ∈ S' \ ⋃ j, C' j by
        exact le_antisymm (le_trans (measure_mono h) (le_of_eq hC'cov)) (zero_le)
      intro x ⟨hxS, hxU⟩
      simp only [Set.mem_iUnion, not_exists] at hxU
      refine ⟨⟨hxS, fun hxC₀ => hxU 0 (by rw [Fin.cons_zero]; exact hxC₀)⟩, ?_⟩
      simp only [Set.mem_iUnion, not_exists]
      intro j hj; exact hxU j.succ (by rw [Fin.cons_succ]; exact hj)
    -- Measures match
    · intro i; refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_zero]; exact hC₀e
      · rw [Fin.cons_succ]; exact hC'e j


section GoodMass

open scoped Classical

/-- The existence package for a chosen equal-measure `k`-cell partition. -/
private theorem equipartition_exists (k : ℕ) [NeZero k] :
    ∃ (P : MeasurablePartition α μ) (ι : Fin k → Set α),
      (∀ i, ι i ∈ P.parts) ∧ Function.Injective ι ∧ (∀ S ∈ P.parts, ∃ i, ι i = S) ∧
      P.parts.card = k ∧ ∀ i, (μ (ι i)).toReal = (k : ℝ)⁻¹ :=
  exists_partition_with_measures (α := α) (μ := μ) (fun _ : Fin k ↦ (k : ℝ)⁻¹)
    (fun _ ↦ by positivity)
    (by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne k)))

/-- A chosen equal-measure `k`-cell partition (shared by every finite-graph and
weighted-sample embedding at level `k`, so their step graphons live on the SAME
partition). -/
noncomputable def equipartition (k : ℕ) [NeZero k] : MeasurablePartition α μ :=
  (equipartition_exists (α := α) (μ := μ) k).choose

/-- The chosen enumeration of the cells of `equipartition k`. -/
noncomputable def equipartitionCell (k : ℕ) [NeZero k] : Fin k → Set α :=
  (equipartition_exists (α := α) (μ := μ) k).choose_spec.choose

theorem equipartitionCell_mem (k : ℕ) [NeZero k] (i : Fin k) :
    equipartitionCell (α := α) (μ := μ) k i ∈ (equipartition (α := α) (μ := μ) k).parts :=
  (equipartition_exists (α := α) (μ := μ) k).choose_spec.choose_spec.1 i

theorem equipartitionCell_injective (k : ℕ) [NeZero k] :
    Function.Injective (equipartitionCell (α := α) (μ := μ) k) :=
  (equipartition_exists (α := α) (μ := μ) k).choose_spec.choose_spec.2.1

theorem equipartitionCell_surjOn (k : ℕ) [NeZero k] :
    ∀ S ∈ (equipartition (α := α) (μ := μ) k).parts,
      ∃ i, equipartitionCell (α := α) (μ := μ) k i = S :=
  (equipartition_exists (α := α) (μ := μ) k).choose_spec.choose_spec.2.2.1

theorem equipartitionCell_measure (k : ℕ) [NeZero k] (i : Fin k) :
    (μ (equipartitionCell (α := α) (μ := μ) k i)).toReal = (k : ℝ)⁻¹ :=
  (equipartition_exists (α := α) (μ := μ) k).choose_spec.choose_spec.2.2.2.2 i

/-- **The finite-graph embedding on an arbitrary atomless standard Borel space**: the
step graphon of `G` over the chosen equal-measure `k`-cell partition
(`equipartition k`), with `0/1` coefficients given by adjacency. The generic analogue
of `ofSimpleGraph` (which is the `[0,1]`-interval presentation). Downstream uses treat
this as opaque. -/
noncomputable def ofSimpleGraphOn {k : ℕ} [NeZero k] (G : SimpleGraph (Fin k)) :
    Graphon α μ :=
  mkStepGraphon (equipartition k)
    (fun S T ↦
      if hST : (∃ i, equipartitionCell (α := α) (μ := μ) k i = S) ∧
          (∃ j, equipartitionCell (α := α) (μ := μ) k j = T)
      then (if G.Adj hST.1.choose hST.2.choose then 1 else 0) else 0)
    (fun S _ T _ ↦ by
      by_cases h1 : (∃ i, equipartitionCell (α := α) (μ := μ) k i = S) ∧
          (∃ j, equipartitionCell (α := α) (μ := μ) k j = T)
      · rw [dif_pos h1, dif_pos ⟨h1.2, h1.1⟩]
        by_cases hadj : G.Adj h1.1.choose h1.2.choose
        · rw [if_pos hadj, if_pos (G.adj_symm hadj)]
        · rw [if_neg hadj, if_neg (fun hc ↦ hadj (G.adj_symm hc))]
      · rw [dif_neg h1, dif_neg (fun hc ↦ h1 ⟨hc.2, hc.1⟩)])
    (fun S _ T _ ↦ by split_ifs <;> norm_num)

/-- The mass of "good" sampled graphs: those whose embedded step graphon lies within
cut distance `ε` of `W`. -/
noncomputable def sampleGoodMassOn (W : Graphon α μ) (k : ℕ) [NeZero k] (ε : ℝ) : ℝ :=
  ∑ G : SimpleGraph (Fin k),
    if cutDistance W (ofSimpleGraphOn G) < ε then sampleMass W G else 0

/-- The good mass is nonnegative. -/
theorem sampleGoodMassOn_nonneg (W : Graphon α μ) (k : ℕ) [NeZero k] (ε : ℝ) :
    0 ≤ sampleGoodMassOn W k ε :=
  Finset.sum_nonneg fun G _ ↦ by
    split_ifs
    · exact sampleMass_nonneg W G
    · exact le_refl 0

/-- The good mass is at most 1. -/
theorem sampleGoodMassOn_le_one (W : Graphon α μ) (k : ℕ) [NeZero k] (ε : ℝ) :
    sampleGoodMassOn W k ε ≤ 1 := by
  calc sampleGoodMassOn W k ε
      ≤ ∑ G : SimpleGraph (Fin k), sampleMass W G :=
        Finset.sum_le_sum fun G _ ↦ by
          split_ifs
          · exact le_refl _
          · exact sampleMass_nonneg W G
    _ = 1 := sampleMass_sum_eq_one W

/-- The good mass is monotone in the accuracy `ε`. -/
theorem sampleGoodMassOn_mono (W : Graphon α μ) (k : ℕ) [NeZero k] {ε₁ ε₂ : ℝ}
    (h : ε₁ ≤ ε₂) : sampleGoodMassOn W k ε₁ ≤ sampleGoodMassOn W k ε₂ := by
  refine Finset.sum_le_sum fun G _ ↦ ?_
  by_cases h1 : cutDistance W (ofSimpleGraphOn G) < ε₁
  · rw [if_pos h1, if_pos (lt_of_lt_of_le h1 h)]
  · rw [if_neg h1]
    split_ifs
    · exact sampleMass_nonneg W G
    · exact le_refl 0

/-- **Complement form**: the bad mass is `1` minus the good mass. -/
theorem one_sub_sampleGoodMassOn (W : Graphon α μ) (k : ℕ) [NeZero k] (ε : ℝ) :
    1 - sampleGoodMassOn W k ε =
      ∑ G : SimpleGraph (Fin k),
        if ε ≤ cutDistance W (ofSimpleGraphOn G) then sampleMass W G else 0 := by
  have hsplit : ∀ G : SimpleGraph (Fin k),
      sampleMass W G =
        (if cutDistance W (ofSimpleGraphOn G) < ε then sampleMass W G else 0) +
          (if ε ≤ cutDistance W (ofSimpleGraphOn G) then sampleMass W G else 0) := by
    intro G
    by_cases h : cutDistance W (ofSimpleGraphOn G) < ε
    · rw [if_pos h, if_neg (not_le.mpr h), add_zero]
    · rw [if_neg h, if_pos (not_lt.mp h), zero_add]
  calc 1 - sampleGoodMassOn W k ε
      = (∑ G : SimpleGraph (Fin k), sampleMass W G) - sampleGoodMassOn W k ε := by
        rw [sampleMass_sum_eq_one]
    _ = ∑ G : SimpleGraph (Fin k),
          if ε ≤ cutDistance W (ofSimpleGraphOn G) then sampleMass W G else 0 := by
        rw [Finset.sum_congr rfl fun G _ ↦ hsplit G, Finset.sum_add_distrib]
        unfold sampleGoodMassOn
        ring

/-- **Good-mass extraction** — the coupling bridge. If `U` and `W` are within cut
distance `ρ` and their sampled distributions are within total variation `tv`, then a
`(1−η)`-good mass for `U` at accuracy `ε` yields a `(1−η−tv)`-good mass for `W` at the
slackened accuracy `ε + ρ`. The slack `ρ` is unavoidable (the good events differ), and
this lemma is NOT used in the ICL derivation below (that would be circular); it is the
general-purpose coupling form. -/
theorem sampleGoodMassOn_extract {k : ℕ} [NeZero k] (U W : Graphon α μ) (ε η ρ tv : ℝ)
    (hUW : cutDistance U W ≤ ρ)
    (htv : ∑ G : SimpleGraph (Fin k), |sampleMass U G - sampleMass W G| ≤ tv)
    (hU : 1 - η < sampleGoodMassOn U k ε) :
    1 - η - tv < sampleGoodMassOn W k (ε + ρ) := by
  set A : Finset (SimpleGraph (Fin k)) :=
    Finset.univ.filter (fun G ↦ cutDistance U (ofSimpleGraphOn G) < ε) with hA
  have hgoodU : sampleGoodMassOn U k ε = ∑ G ∈ A, sampleMass U G := by
    rw [hA, Finset.sum_filter]; rfl
  have hsubset : ∀ G ∈ A, cutDistance W (ofSimpleGraphOn G) < ε + ρ := by
    intro G hG
    rw [hA, Finset.mem_filter] at hG
    calc cutDistance W (ofSimpleGraphOn G)
        ≤ cutDistance W U + cutDistance U (ofSimpleGraphOn G) :=
          cutDistance_triangle _ _ _
      _ < ρ + ε := by
          rw [cutDistance_symm] at hUW ⊢
          exact add_lt_add_of_le_of_lt (by rwa [cutDistance_symm]) hG.2
      _ = ε + ρ := by ring
  have hWA : ∑ G ∈ A, sampleMass W G ≤ sampleGoodMassOn W k (ε + ρ) := by
    rw [show sampleGoodMassOn W k (ε + ρ) =
        ∑ G ∈ Finset.univ.filter
          (fun G : SimpleGraph (Fin k) ↦ cutDistance W (ofSimpleGraphOn G) < ε + ρ),
          sampleMass W G from by rw [Finset.sum_filter]; rfl]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun G _ _ ↦ sampleMass_nonneg W G)
    intro G hG
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ G, hsubset G hG⟩
  have hextract := sum_sampleMass_event_sub_le U W A tv htv
  linarith [hgoodU ▸ hU]

/-- **The First Sampling Lemma** (space-generic interface) — the sole remaining analytic
gap of the sampling route.

For every accuracy `ε` and failure probability `η`, some sample size `k` works for
EVERY graphon on the space simultaneously: the sampled graph `G(k, W)` lies within cut
distance `ε` of `W` with probability greater than `1 − η`. The `W`-uniformity of `k` is
the point — it is what makes the quantitative ICL below partition-size-independent,
breaking the circularity documented at `headline_parameter_selection`.

Classical proof (future target): Lovász, *Large Networks and Graph Limits*, Lemma 10.16
(First Sampling Lemma, `δ_□(W, W[x]) ≤ 22/√(log k)` in expectation) via Azuma–Hoeffding
concentration for the cut norm of samples, or BCLSV, "Convergent sequences I", Thm 4.6.
The classical argument is space-agnostic once the sampled graph is embedded on an
equal-measure partition of the same space; alternatively it can be proved on `[0,1]`
and transferred once the measure isomorphism theorem (Rokhlin-adjacent) exists. -/
theorem first_sampling_lemma (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ k : ℕ, ∀ W : Graphon α μ, 1 - η < sampleGoodMassOn W (k + 1) ε := by
  sorry

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

end GoodMass

end Graphon
