/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.InvariantAction
import Graphon.RestrictionIndependence
import Mathlib.MeasureTheory.Measure.MeasuredSets

/-!
# Ergodic decomposition of exchangeable graph laws (issue #59, part 2)

Commit 1: the geometric and approximation infrastructure for the fixed-fiber ergodicity
argument (a permutation-invariant event has `M.law`-measure `0` or `1`).

* `InfiniteGraph.FinSupp.one` / `.inv` / `.mul` — the finitely supported permutations of
  `ℕ` are closed under identity, inverse, and composition (a subgroup of `Equiv.Perm ℕ`);
* `InfiniteGraph.swapBlock k` — the involution swapping the block `[0, k)` with `[k, 2k)`
  (fixing everything past `2k`), a finitely supported permutation;
* `InfiniteGraph.restrictFin_relabel_swapBlock` — relabeling by `swapBlock k` moves the
  initial `k`-window onto the `k`-tail window:
  `restrictFin k (relabel (swapBlock k) G) = restrictFin k (drop k G)`; hence
* `InfiniteGraph.relabel_swapBlock_preimage_mem_tailAlgebra` — the `swapBlock k`
  relabeling carries every `initialAlgebra k` event into a `tailAlgebra k` event;
* `Graphon.InfiniteExchangeableGraphLaw.exists_initialAlgebra_measure_symmDiff_lt` —
  **in-measure approximation by initial cylinders**: every Borel event is approximated in
  `M.law`-measure by an event depending on only finitely many vertices (via
  `exists_measure_symmDiff_lt_of_generateFrom_isSetRing`, the initial cylinders being a
  set-ring that generates the Borel σ-algebra).
-/

open MeasureTheory Set

open scoped ENNReal symmDiff

namespace InfiniteGraph

/-! ### The finitely supported permutations form a subgroup -/

/-- The identity is finitely supported. -/
theorem FinSupp.one : FinSupp (1 : Equiv.Perm ℕ) := ⟨0, fun _ _ => rfl⟩

/-- The inverse of a finitely supported permutation is finitely supported. -/
theorem FinSupp.inv {σ : Equiv.Perm ℕ} (hσ : FinSupp σ) : FinSupp σ⁻¹ := by
  obtain ⟨N, hN⟩ := hσ
  refine ⟨N, fun x hx => ?_⟩
  calc σ⁻¹ x = σ⁻¹ (σ x) := by rw [hN x hx]
    _ = x := σ.symm_apply_apply x

/-- The composition of two finitely supported permutations is finitely supported. -/
theorem FinSupp.mul {σ τ : Equiv.Perm ℕ} (hσ : FinSupp σ) (hτ : FinSupp τ) :
    FinSupp (σ * τ) := by
  obtain ⟨Nσ, hσ⟩ := hσ
  obtain ⟨Nτ, hτ⟩ := hτ
  refine ⟨max Nσ Nτ, fun x hx => ?_⟩
  rw [Equiv.Perm.mul_apply, hτ x ((le_max_right Nσ Nτ).trans hx),
    hσ x ((le_max_left Nσ Nτ).trans hx)]

/-! ### The block swap `[0, k) ↔ [k, 2k)` -/

/-- The block-swap function: exchange `[0, k)` with `[k, 2k)`, fixing the rest. -/
def swapBlockFun (k i : ℕ) : ℕ := if i < k then i + k else if i < 2 * k then i - k else i

theorem swapBlockFun_involutive (k : ℕ) : Function.Involutive (swapBlockFun k) := by
  intro i
  simp only [swapBlockFun]
  split_ifs <;> omega

/-- **The block swap** `[0, k) ↔ [k, 2k)`: a finitely supported involution of `ℕ`. -/
def swapBlock (k : ℕ) : Equiv.Perm ℕ := (swapBlockFun_involutive k).toPerm

@[simp] theorem swapBlock_apply (k i : ℕ) : swapBlock k i = swapBlockFun k i :=
  congrFun (swapBlockFun_involutive k).coe_toPerm i

theorem swapBlock_apply_of_lt (k : ℕ) {i : ℕ} (hi : i < k) : swapBlock k i = i + k := by
  simp only [swapBlock_apply, swapBlockFun, if_pos hi]

/-- The block swap is finitely supported (it fixes everything past `2k`). -/
theorem finSupp_swapBlock (k : ℕ) : FinSupp (swapBlock k) := by
  refine ⟨2 * k, fun x hx => ?_⟩
  simp only [swapBlock_apply, swapBlockFun]
  split_ifs <;> omega

/-! ### The block swap carries initial cylinders to tail cylinders -/

/-- **The block swap moves the initial window onto the tail window**: the graph induced
on the first `k` vertices after relabeling by `swapBlock k` equals the graph induced on
`{k, …, 2k−1}` — the first `k` vertices of the `k`-tail. -/
theorem restrictFin_relabel_swapBlock (k : ℕ) (G : InfiniteGraph) :
    restrictFin k (relabel (swapBlock k) G) = restrictFin k (drop k G) := by
  rw [restrictFin_relabel (swapBlock k) (Fin.addNatEmb k)
      (fun a => by
        have : ((Fin.addNatEmb k a : Fin (k + k)) : ℕ) = (a : ℕ) + k := by
          simp [Fin.addNatEmb]
        rw [this]; exact swapBlock_apply_of_lt k a.isLt),
    restrictFin_drop k k G]

/-- **The block-swap relabeling carries an `initialAlgebra k` event into a `tailAlgebra k`
event**: it moves dependence on the first `k` vertices to dependence on `{k, …, 2k−1}`,
which is contained in the tail `{k, k+1, …}`. -/
theorem relabel_swapBlock_preimage_mem_tailAlgebra (k : ℕ) {B : Set InfiniteGraph}
    (hB : MeasurableSet[initialAlgebra k] B) :
    MeasurableSet[tailAlgebra k] (relabel (swapBlock k) ⁻¹' B) := by
  obtain ⟨S, hS, rfl⟩ := hB
  refine ⟨restrictFin k ⁻¹' S, measurable_restrictFin k hS, ?_⟩
  ext G
  simp only [Set.mem_preimage]
  rw [← restrictFin_relabel_swapBlock k G]

/-! ### In-measure approximation by initial cylinders -/

/-- The events depending on only finitely many vertices form a ring of sets. -/
theorem isSetRing_iUnion_initialAlgebra :
    MeasureTheory.IsSetRing
      (⋃ k, {A : Set InfiniteGraph | MeasurableSet[initialAlgebra k] A}) where
  empty_mem := by
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨0, @MeasurableSet.empty _ (initialAlgebra 0)⟩
  union_mem := by
    intro s t hs ht
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hs ht ⊢
    obtain ⟨k, hs⟩ := hs
    obtain ⟨l, ht⟩ := ht
    exact ⟨max k l, (initialAlgebra_mono (le_max_left k l) _ hs).union
      (initialAlgebra_mono (le_max_right k l) _ ht)⟩
  sdiff_mem := by
    intro s t hs ht
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hs ht ⊢
    obtain ⟨k, hs⟩ := hs
    obtain ⟨l, ht⟩ := ht
    exact ⟨max k l, (initialAlgebra_mono (le_max_left k l) _ hs).diff
      (initialAlgebra_mono (le_max_right k l) _ ht)⟩

/-- The Borel σ-algebra is generated by the finite-vertex events. -/
theorem generateFrom_iUnion_initialAlgebra :
    (inferInstance : MeasurableSpace InfiniteGraph) =
      MeasurableSpace.generateFrom
        (⋃ k, {A : Set InfiniteGraph | MeasurableSet[initialAlgebra k] A}) :=
  ((MeasurableSpace.generateFrom_iUnion_measurableSet initialAlgebra).trans
    iSup_initialAlgebra_eq).symm

end InfiniteGraph

namespace Graphon.InfiniteExchangeableGraphLaw

/-- **In-measure approximation by initial cylinders**: every Borel event `s` is
approximated in `M.law`-measure, to within any `ε > 0`, by an event `t` depending on only
the first `k` vertices for some `k`. The initial cylinders form a set-ring generating the
Borel σ-algebra, so `exists_measure_symmDiff_lt_of_generateFrom_isSetRing` applies. -/
theorem exists_initialAlgebra_measure_symmDiff_lt (M : Graphon.InfiniteExchangeableGraphLaw)
    {s : Set InfiniteGraph} (hs : MeasurableSet s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ k, ∃ t, MeasurableSet[InfiniteGraph.initialAlgebra k] t ∧
      (M.law : Measure InfiniteGraph) (t ∆ s) < ε := by
  haveI : IsProbabilityMeasure (M.law : Measure InfiniteGraph) := M.law.2
  obtain ⟨t, ht, hlt⟩ := MeasureTheory.exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (μ := (M.law : Measure InfiniteGraph)) InfiniteGraph.isSetRing_iUnion_initialAlgebra
    ⟨{Set.univ}, Set.countable_singleton _, by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Set.mem_iUnion.mpr ⟨0, @MeasurableSet.univ _ (InfiniteGraph.initialAlgebra 0)⟩, by
      rw [Set.sUnion_singleton, Set.compl_univ, measure_empty]⟩
    InfiniteGraph.generateFrom_iUnion_initialAlgebra hs hε
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ht
  exact ⟨k, t, hk, hlt⟩

end Graphon.InfiniteExchangeableGraphLaw
