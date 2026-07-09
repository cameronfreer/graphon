/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.Regularity

/-!
# The overlay theorem: an MP bijection nearly achieves the cut distance (Rokhlin campaign, R3)

This file proves the last live Rokhlin core, `exists_mpEquiv_cutNormDiff_lt_add`: on an
atomless standard Borel probability space, the cut distance — an infimum over pairs of
measure-preserving *maps* — is achieved up to any `ε > 0` by pulling back one graphon along a
single measure-preserving **bijection**, leaving the other bare. This is the classical
overlay / bijection-density fact (Borgs–Chayes–Lovász–Sós–Vesztergombi Lemma 3.5, Janson
Theorem 6.9), needed by the completeness telescope in `Graphon/Compactness.lean`.

It lives in its own file because the proof needs the Frieze–Kannan `regularity` lemma and the
atomless carving primitives of `Graphon/Regularity.lean`, which sit *downstream* of
`Graphon/CutDistance.lean` in the import graph.

The proof follows `docs/overlay-scoping.md` §4: **no Birkhoff / rational approximation.**
For *step* graphons, the value of any coupling `(φ, ψ)` is realized **exactly** by an MP
bijection: the coupling matrix `λ_{ik} = μ(φ⁻¹(S_i) ∩ ψ⁻¹(T_k))` has row and column sums
equal to the cell measures, so (atomlessly) both partitions can be refined into cells of
mass exactly `λ_{ik}`, and `exists_controlled_cell_alignment` — applied twice, once for the
answer bijection and once for a proof-only transfer — turns the matched refinements into the
required measure-preserving `α ≃ᵐ α`. The only `ε` comes from step approximation.

## Roadmap (R3)

* **O1** `exists_disjoint_subsets_of_measures` — carve finitely many disjoint subsets of
  prescribed masses out of a measurable set; `MeasurablePartition.ofCells` — assemble a
  partition from disjoint cells plus a waste cell.
* **O2** the exact step-overlay transfer (double alignment).
* **O3** assembly: `exists_mpEquiv_cutNormDiff_lt_add` (relocated here from
  `Graphon/CutDistance.lean`).
-/

open MeasureTheory Set Filter Finset

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

/-! ### O1: prescribed-mass carving and partition assembly -/

section Carving

variable [IsProbabilityMeasure μ]

/-- **Prescribed-mass carving.** Out of a measurable set `C`, carve finitely many pairwise
disjoint measurable subsets of any prescribed masses `r i` with `∑ i, r i ≤ μ C`.

This generalizes `exists_equal_chunks_inside` (equal masses `1/q`) to arbitrary prescribed
masses; it is the finite-matrix carving step of the overlay construction
(`docs/overlay-scoping.md` §4, step 1). -/
theorem exists_disjoint_subsets_of_measures [StandardBorelSpace α] [NoAtoms μ] :
    ∀ {n : ℕ} {C : Set α}, MeasurableSet C → ∀ r : Fin n → ℝ≥0∞, ∑ i, r i ≤ μ C →
    ∃ A : Fin n → Set α, (∀ i, MeasurableSet (A i)) ∧ (∀ i, A i ⊆ C) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧ ∀ i, μ (A i) = r i := by
  intro n
  induction n with
  | zero =>
    intro C _ r _
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro C hC r hr
    -- Carve the head cell of mass `r 0`.
    have hr0 : r 0 ≤ μ C :=
      le_trans (Finset.single_le_sum (fun i _ => zero_le) (Finset.mem_univ 0)) hr
    obtain ⟨A₀, hA₀meas, hA₀sub, hA₀μ⟩ := exists_measurable_subset_of_measure hC hr0
    -- Recurse on the complement within `C` with the tail masses.
    have hC' : MeasurableSet (C \ A₀) := hC.diff hA₀meas
    have hsum' : ∑ i : Fin n, r i.succ ≤ μ (C \ A₀) := by
      have hdiff : μ (C \ A₀) = μ C - r 0 := by
        rw [measure_sdiff hA₀sub hA₀meas.nullMeasurableSet (measure_ne_top μ A₀), hA₀μ]
      have h := hr
      rw [Fin.sum_univ_succ] at h
      rw [hdiff]
      exact ENNReal.le_sub_of_add_le_left (ne_top_of_le_ne_top (measure_ne_top μ C) hr0) h
    obtain ⟨A', hA'meas, hA'sub, hA'disj, hA'μ⟩ := ih hC' (fun i => r i.succ) hsum'
    refine ⟨Fin.cons A₀ A', fun i => ?_, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
    · obtain rfl | ⟨a, rfl⟩ := Fin.eq_zero_or_eq_succ i
      · simpa using hA₀meas
      · simpa using hA'meas a
    · obtain rfl | ⟨a, rfl⟩ := Fin.eq_zero_or_eq_succ i
      · simpa using hA₀sub
      · simpa using (hA'sub a).trans sdiff_subset
    · have hdisj₀ : ∀ a : Fin n, Disjoint A₀ (A' a) := fun a =>
        disjoint_sdiff_right.mono_right (hA'sub a)
      obtain rfl | ⟨a, rfl⟩ := Fin.eq_zero_or_eq_succ i <;>
        obtain rfl | ⟨b, rfl⟩ := Fin.eq_zero_or_eq_succ j
      · exact absurd rfl hij
      · simpa using hdisj₀ b
      · simpa using (hdisj₀ a).symm
      · simpa using hA'disj (fun h => hij (congrArg Fin.succ h))
    · obtain rfl | ⟨a, rfl⟩ := Fin.eq_zero_or_eq_succ i
      · simpa using hA₀μ
      · simpa using hA'μ a

end Carving

/-! ### O1: partition from disjoint cells plus a waste cell -/

/-- Assemble a `MeasurablePartition` from finitely many pairwise disjoint measurable cells,
adding the complement of their union as a waste cell. Every input cell is a part
(`mem_ofCells_parts`). -/
noncomputable def _root_.MeasurablePartition.ofCells {n : ℕ} (A : Fin n → Set α)
    (hmeas : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    MeasurablePartition α μ where
  parts := insert ((⋃ i, A i)ᶜ) (Finset.univ.image A)
  measurable_parts := by
    intro S hS
    rcases Finset.mem_insert.mp hS with rfl | hS
    · exact (MeasurableSet.iUnion hmeas).compl
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hS
      exact hmeas i
  pairwiseDisjoint := by
    intro S hS T hT hST
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_image,
      Finset.coe_univ, Set.image_univ, Set.mem_range] at hS hT
    rcases hS with rfl | ⟨i, rfl⟩ <;> rcases hT with rfl | ⟨j, rfl⟩
    · exact absurd rfl hST
    · exact disjoint_compl_left.mono_right (Set.subset_iUnion A j)
    · exact disjoint_compl_right.mono_left (Set.subset_iUnion A i)
    · exact hdisj fun h => hST (congrArg A h)
  ae_covers := Eventually.of_forall fun x => by
    by_cases hx : x ∈ ⋃ i, A i
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact ⟨A i, Finset.mem_insert_of_mem (Finset.mem_image_of_mem A (Finset.mem_univ i)), hi⟩
    · exact ⟨_, Finset.mem_insert_self _ _, hx⟩

/-- Each input cell is a part of `MeasurablePartition.ofCells`. -/
theorem _root_.MeasurablePartition.mem_ofCells_parts {n : ℕ} {A : Fin n → Set α}
    {hmeas : ∀ i, MeasurableSet (A i)}
    {hdisj : Pairwise (fun i j => Disjoint (A i) (A j))} (i : Fin n) :
    A i ∈ (MeasurablePartition.ofCells (μ := μ) A hmeas hdisj).parts :=
  Finset.mem_insert_of_mem (Finset.mem_image_of_mem A (Finset.mem_univ i))

end Graphon
