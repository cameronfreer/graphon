/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.Floor

/-!
# Step Graphons

Step graphons are graphons that are piecewise constant on a finite measurable
partition of the probability space. They form a dense subset of the space of
graphons (in cut distance) and provide the key bridge between finite graphs
and graphons.

## Main definitions

* `MeasurablePartition` - A finite measurable partition of a probability space
* `Graphon.ofSimpleGraph` - Construct a graphon from a finite simple graph

## Main results

* `Graphon.ofSimpleGraph_symm_ae` - The graphon of a simple graph is symmetric a.e.
* `Graphon.ofSimpleGraph_ae_mem_Icc` - Values are in [0,1] a.e.

## Implementation notes

The graphon `ofSimpleGraph G` for a simple graph `G` on `n` vertices is defined
on the unit interval by partitioning `[0,1]` into `n` equal parts and setting
`W(x,y) = 1` if the parts containing `x` and `y` are adjacent in `G`, and `0`
otherwise.

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Chapter 7
-/

open MeasureTheory Set Filter Finset

open scoped unitInterval

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ### Measurable partitions -/

/-- A finite measurable partition of a measure space.

This is a finite collection of pairwise disjoint measurable sets that cover
the space almost everywhere. Used to define step graphons. -/
structure MeasurablePartition (α : Type*) [MeasurableSpace α] (μ : Measure α) where
  /-- The parts of the partition as a finset of sets -/
  parts : Finset (Set α)
  /-- Each part is measurable -/
  measurable_parts : ∀ S ∈ parts, MeasurableSet S
  /-- The parts are pairwise disjoint -/
  pairwiseDisjoint : (parts : Set (Set α)).PairwiseDisjoint id
  /-- The parts cover the space almost everywhere -/
  ae_covers : ∀ᵐ x ∂μ, ∃ S ∈ parts, x ∈ S

namespace MeasurablePartition

variable (P : MeasurablePartition α μ)

/-- The number of parts in the partition. -/
def card : ℕ := P.parts.card

/-- A part of the partition is measurable. -/
theorem measurableSet_part {S : Set α} (hS : S ∈ P.parts) : MeasurableSet S :=
  P.measurable_parts S hS

end MeasurablePartition

/-! ### Graphon from simple graph -/

namespace Graphon

variable [IsProbabilityMeasure μ]

section SimpleGraph

variable {n : ℕ} [NeZero n]

/-- The indicator function for adjacency in a simple graph, as a real number.

Returns 1 if vertices `i` and `j` are adjacent, 0 otherwise. -/
def adjIndicator (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i j : Fin n) : ℝ :=
  if G.Adj i j then 1 else 0

-- These theorems don't need [NeZero n] but it's in scope from the section variable
set_option linter.unusedSectionVars false in
/-- The `adjIndicator` is symmetric since adjacency is symmetric. -/
theorem adjIndicator_symm (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i j : Fin n) :
    adjIndicator G i j = adjIndicator G j i := by
  simp only [adjIndicator, G.adj_comm]

set_option linter.unusedSectionVars false in
/-- The `adjIndicator` takes values in `[0,1]`. -/
theorem adjIndicator_mem_Icc (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i j : Fin n) :
    adjIndicator G i j ∈ Set.Icc 0 1 := by
  simp only [adjIndicator, Set.mem_Icc]
  split_ifs <;> norm_num

set_option linter.unusedSectionVars false in
/-- The `adjIndicator` is 0 or 1. -/
theorem adjIndicator_eq_zero_or_one (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i j : Fin n) :
    adjIndicator G i j = 0 ∨ adjIndicator G i j = 1 := by
  simp only [adjIndicator]
  split_ifs <;> simp

/-- Map a point in the unit interval to its corresponding vertex in `Fin n`.

For `x ∈ [0,1]`, returns `⌊n * x⌋` clamped to `Fin n`. This maps the interval
`[k/n, (k+1)/n)` to vertex `k`. -/
noncomputable def toVertex (n : ℕ) [NeZero n] (x : I) : Fin n :=
  ⟨min (n - 1) ⌊(n : ℝ) * x.val⌋₊, by
    have h : min (n - 1) ⌊(n : ℝ) * x.val⌋₊ ≤ n - 1 := Nat.min_le_left _ _
    have hn : 0 < n := NeZero.pos n
    omega⟩

set_option linter.unusedSectionVars false in
/-- The function `x ↦ min (n-1) ⌊n*x⌋₊` as a function `ℝ → ℕ` is measurable. -/
theorem measurable_minFloor_nat : Measurable (fun x : ℝ => min (n - 1) ⌊(n : ℝ) * x⌋₊) :=
  Measurable.min measurable_const (Measurable.nat_floor (measurable_const.mul measurable_id))

/-- The function `x ↦ min (n-1) ⌊n*x⌋₊` is measurable as a real-valued function. -/
theorem measurable_minFloor : Measurable (fun x : ℝ => (↑(min (n - 1) ⌊(n : ℝ) * x⌋₊) : ℝ)) :=
  measurable_from_nat.comp measurable_minFloor_nat

/-- The `toVertex` function is measurable. -/
theorem measurable_toVertex : Measurable (toVertex n : I → Fin n) := by
  -- Use measurable_to_countable': show preimage of each singleton is measurable
  apply measurable_to_countable'
  intro i
  -- The preimage is an interval in I, which is measurable
  -- toVertex n x = i iff min (n-1) ⌊n * x.val⌋₊ = i.val
  have heq : toVertex n ⁻¹' {i} =
      (Subtype.val : I → ℝ) ⁻¹' {x | min (n - 1) ⌊(n : ℝ) * x⌋₊ = i.val} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    simp only [toVertex, Fin.ext_iff]
  rw [heq]
  -- The preimage under measurable_subtype_coe of a measurable set is measurable
  apply MeasurableSet.preimage _ measurable_subtype_coe
  -- The set {x | min (n-1) ⌊n*x⌋₊ = i.val} is measurable in ℝ
  -- Cast to ℝ and rewrite as intersection of two half-open conditions
  have hset : {x : ℝ | min (n - 1) ⌊(n : ℝ) * x⌋₊ = i.val} =
      {x : ℝ | (i.val : ℝ) ≤ (↑(min (n - 1) ⌊(n : ℝ) * x⌋₊) : ℝ)} ∩
      {x : ℝ | (↑(min (n - 1) ⌊(n : ℝ) * x⌋₊) : ℝ) ≤ (i.val : ℝ)} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Nat.cast_le]
    omega
  rw [hset]
  apply MeasurableSet.inter
  · -- Goal: {x | i.val ≤ min ...} is measurable
    exact measurableSet_le measurable_const measurable_minFloor
  · -- Goal: {x | min ... ≤ i.val} is measurable
    exact measurableSet_le measurable_minFloor measurable_const

/-- The function mapping pairs to adjacency indicators is measurable. -/
theorem measurable_adjIndicator_comp_toVertex (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Measurable (fun p : I × I => adjIndicator G (toVertex n p.1) (toVertex n p.2)) := by
  -- Factor as composition: (toVertex × toVertex) then adjIndicator
  -- adjIndicator is measurable from Fin n × Fin n (finite, discrete) to ℝ
  have h : (fun p : I × I => adjIndicator G (toVertex n p.1) (toVertex n p.2)) =
      (fun q : Fin n × Fin n => adjIndicator G q.1 q.2) ∘
      (fun p : I × I => (toVertex n p.1, toVertex n p.2)) := rfl
  rw [h]
  apply Measurable.comp
  · exact measurable_of_finite _
  · exact Measurable.prodMk (measurable_toVertex.comp measurable_fst)
                            (measurable_toVertex.comp measurable_snd)

/-- The function mapping pairs to adjacency indicators is strongly measurable. -/
theorem stronglyMeasurable_adjIndicator_comp_toVertex (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    StronglyMeasurable (fun p : I × I => adjIndicator G (toVertex n p.1) (toVertex n p.2)) :=
  (measurable_adjIndicator_comp_toVertex G).stronglyMeasurable

/-- The graphon associated to a simple graph on `Fin n`.

Given a simple graph `G` on `n` vertices, we construct a graphon on `[0,1]` by:
1. Partitioning `[0,1]` into `n` equal intervals
2. Setting `W(x,y) = 1` if the vertices corresponding to `x` and `y` are adjacent
3. Setting `W(x,y) = 0` otherwise

This is the fundamental bridge between finite graphs and graphons. The homomorphism
density `t(F, W_G)` equals `hom(F, G) / n^|V(F)|`. -/
noncomputable def ofSimpleGraph (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : GraphonI := by
  let f : I × I → ℝ := fun p => adjIndicator G (toVertex n p.1) (toVertex n p.2)
  let hf : AEStronglyMeasurable f (volume.prod volume) :=
    (stronglyMeasurable_adjIndicator_comp_toVertex G).aestronglyMeasurable
  refine ⟨⟨AEEqFun.mk f hf, ?symm⟩, ?mem_Icc⟩
  case symm =>
    have h := AEEqFun.coeFn_mk f hf
    have h_swap := ae_prod_swap h
    filter_upwards [h, h_swap] with p hp hp_swap
    simp only [f, Prod.swap] at hp hp_swap ⊢
    rw [hp_swap, hp, adjIndicator_symm]
  case mem_Icc =>
    have h := AEEqFun.coeFn_mk f hf
    filter_upwards [h] with p hp
    simp only [f] at hp ⊢
    rw [hp]
    exact adjIndicator_mem_Icc G _ _

/-- The graphon of a simple graph at a point equals the adjacency indicator (a.e.). -/
theorem ofSimpleGraph_apply (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∀ᵐ p ∂(volume.prod volume : Measure (I × I)),
      (ofSimpleGraph G).toAEEqFun p =
        adjIndicator G (toVertex n p.1) (toVertex n p.2) :=
  AEEqFun.coeFn_mk _ _

/-- The graphon of the empty graph is zero almost everywhere. -/
theorem ofSimpleGraph_bot_ae :
    ∀ᵐ p ∂(volume.prod volume : Measure (I × I)),
      (ofSimpleGraph (⊥ : SimpleGraph (Fin n))).toAEEqFun p = 0 := by
  filter_upwards [ofSimpleGraph_apply (⊥ : SimpleGraph (Fin n))] with p hp
  simp only [hp, adjIndicator, SimpleGraph.bot_adj, ite_false]

/-- The graphon of the complete graph equals 1 off the diagonal.

Note: On the diagonal (where `toVertex n p.1 = toVertex n p.2`), the value is 0
because simple graphs have no self-loops. -/
theorem ofSimpleGraph_top_ae :
    ∀ᵐ p ∂(volume.prod volume : Measure (I × I)),
      (ofSimpleGraph (⊤ : SimpleGraph (Fin n))).toAEEqFun p =
        if toVertex n p.1 = toVertex n p.2 then 0 else 1 := by
  filter_upwards [ofSimpleGraph_apply (⊤ : SimpleGraph (Fin n))] with p hp
  simp only [hp, adjIndicator, SimpleGraph.top_adj, ne_eq, ite_not]

end SimpleGraph

end Graphon
