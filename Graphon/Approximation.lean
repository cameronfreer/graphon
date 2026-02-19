/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Step
import Graphon.CutDistance

/-!
# Approximation of Graphons by Step Functions

This file develops the theory of approximating graphons by step functions,
which is central to the regularity lemma and compactness of graphon space.

## Main definitions

* `Graphon.rectAverage` - Average value of a graphon over a rectangle
* `Graphon.Refines` - Partition refinement relation

## Main results

* `Graphon.rectAverage_mem_Icc` - Rectangle averages are in [0, 1]
* `Graphon.rectAverage_symm` - Rectangle averages are symmetric

## Implementation notes

Given a measurable partition P of α, the stepified graphon takes the average value
on each rectangle S × T for S, T ∈ P:
`(stepify P W)(x, y) = (1/(μ(S)μ(T))) ∫_{S×T} W dμ×μ` for x ∈ S, y ∈ T

The full stepification construction requires building an AEEqFun from piecewise
definitions, which is deferred to future work.

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Section 9.2-9.3
-/

open MeasureTheory Set Filter Finset

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

/-! ### Rectangle averages -/

section RectAverage

variable [IsProbabilityMeasure μ]

/-- The average value of a graphon over a rectangle S × T.

This is the building block for stepification:
`rectAverage W S T = (1/(μ(S)μ(T))) ∫_{S×T} W dμ×μ` -/
noncomputable def rectAverage (W : Graphon α μ) (S T : Set α) : ℝ :=
  if hS : μ S = 0 then 0
  else if hT : μ T = 0 then 0
  else (μ S).toReal⁻¹ * (μ T).toReal⁻¹ *
    ∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ)

/-- The rectangle average is in [0, 1] for graphons. -/
theorem rectAverage_mem_Icc (W : Graphon α μ) (S T : Set α)
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    rectAverage W S T ∈ Set.Icc 0 1 := by
  unfold rectAverage
  split_ifs with hμS_zero hμT_zero
  · exact ⟨le_refl 0, zero_le_one⟩
  · exact ⟨le_refl 0, zero_le_one⟩
  · -- The integral is between 0 and μ(S)μ(T), so the average is in [0,1]
    -- Since W ∈ [0,1] a.e., we have 0 ≤ ∫_{S×T} W ≤ μ(S×T) = μ(S)μ(T)
    have hS_pos : 0 < (μ S).toReal := ENNReal.toReal_pos hμS_zero (measure_lt_top μ S).ne
    have hT_pos : 0 < (μ T).toReal := ENNReal.toReal_pos hμT_zero (measure_lt_top μ T).ne
    -- Bounds on the integral
    have h_int_nonneg : 0 ≤ ∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ) := by
      apply setIntegral_nonneg_of_ae_restrict
      exact ae_restrict_of_ae (W.ae_mem_Icc.mono fun p hp => hp.1)
    have h_int_le : ∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ) ≤ (μ S).toReal * (μ T).toReal := by
      calc ∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ)
          ≤ ∫ _ in S ×ˢ T, (1 : ℝ) ∂(μ.prod μ) := by
            apply setIntegral_mono_ae_restrict
            · exact (SymmKernel.graphon_integrable W).integrableOn
            · exact integrable_const 1
            · exact ae_restrict_of_ae (W.ae_mem_Icc.mono fun p hp => hp.2)
        _ = ((μ.prod μ) (S ×ˢ T)).toReal := by
            rw [setIntegral_const, smul_eq_mul, mul_one]; rfl
        _ = (μ S).toReal * (μ T).toReal := by
            rw [Measure.prod_prod]; simp only [ENNReal.toReal_mul]
    constructor
    · -- Lower bound: 0
      apply mul_nonneg
      apply mul_nonneg (inv_nonneg.mpr hS_pos.le) (inv_nonneg.mpr hT_pos.le)
      exact h_int_nonneg
    · -- Upper bound: 1
      calc (μ S).toReal⁻¹ * (μ T).toReal⁻¹ * ∫ p in S ×ˢ T, W.toAEEqFun p ∂(μ.prod μ)
          ≤ (μ S).toReal⁻¹ * (μ T).toReal⁻¹ * ((μ S).toReal * (μ T).toReal) := by
            apply mul_le_mul_of_nonneg_left h_int_le
            apply mul_nonneg (inv_nonneg.mpr hS_pos.le) (inv_nonneg.mpr hT_pos.le)
        _ = 1 := by field_simp

/-- The rectangle average is symmetric. -/
theorem rectAverage_symm (W : Graphon α μ) (S T : Set α)
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    rectAverage W S T = rectAverage W T S := by
  unfold rectAverage
  split_ifs with h1 h2 h3 _
  · rfl
  · rfl
  · rfl
  · -- Use symmetry of W
    rw [mul_comm (μ S).toReal⁻¹ (μ T).toReal⁻¹]
    congr 1
    -- The integral over S × T equals the integral over T × S by symmetry of W
    exact SymmKernel.rectIntegral_symm W.toSymmKernel hS hT

/-- Rectangle average of zero graphon is zero. -/
theorem rectAverage_zero (S T : Set α) : rectAverage (zero : Graphon α μ) S T = 0 := by
  unfold rectAverage
  split_ifs with hS hT
  · rfl
  · rfl
  · simp only [mul_eq_zero]
    right
    -- The integral of 0 is 0
    apply setIntegral_eq_zero_of_ae_eq_zero
    have h : ∀ᵐ p ∂(μ.prod μ), (zero : Graphon α μ).toAEEqFun p = 0 :=
      (AEEqFun.coeFn_const (α × α) (0 : ℝ))
    exact h.mono fun p hp _ => hp

/-- Rectangle average of one graphon is one (for positive measure sets). -/
theorem rectAverage_one {S T : Set α} (hS : μ S ≠ 0) (hT : μ T ≠ 0)
    (hSm : MeasurableSet S) (hTm : MeasurableSet T) :
    rectAverage (one : Graphon α μ) S T = 1 := by
  unfold rectAverage
  simp only [hS, hT, dite_false]
  -- The one graphon has toAEEqFun = 1 a.e.
  have h_one : ∀ᵐ p ∂(μ.prod μ), (one : Graphon α μ).toAEEqFun p = 1 :=
    (AEEqFun.coeFn_const (α × α) (1 : ℝ))
  -- Use setIntegral_congr_ae to replace toAEEqFun with 1
  conv_lhs => rw [setIntegral_congr_ae (hSm.prod hTm) (h_one.mono fun p hp _ => hp)]
  -- Now we have ∫ p in S ×ˢ T, 1 = (μ.prod μ)(S ×ˢ T)
  rw [MeasureTheory.setIntegral_one_eq_measureReal, MeasureTheory.measureReal_prod_prod]
  -- The result follows by field arithmetic: (μ S)⁻¹ * (μ T)⁻¹ * (μ S * μ T) = 1
  simp only [Measure.real, ENNReal.toReal]
  have hS_nnreal : (0 : ℝ) < (μ S).toNNReal := ENNReal.toNNReal_pos hS (measure_lt_top μ S).ne
  have hT_nnreal : (0 : ℝ) < (μ T).toNNReal := ENNReal.toNNReal_pos hT (measure_lt_top μ T).ne
  field_simp [hS_nnreal.ne', hT_nnreal.ne']

end RectAverage

/-! ### Refinement -/

section Refinement

variable [IsProbabilityMeasure μ]

/-- A partition Q refines P if every part of Q is contained in some part of P. -/
def Refines (Q P : MeasurablePartition α μ) : Prop :=
  ∀ T ∈ Q.parts, ∃ S ∈ P.parts, T ⊆ S

/-- Refinement is reflexive. -/
theorem Refines.refl (P : MeasurablePartition α μ) : Refines P P :=
  fun T hT => ⟨T, hT, Subset.refl T⟩

/-- Refinement is transitive. -/
theorem Refines.trans {P Q R : MeasurablePartition α μ}
    (hPQ : Refines Q P) (hQR : Refines R Q) : Refines R P := by
  intro T hT
  obtain ⟨S, hS, hTS⟩ := hQR T hT
  obtain ⟨U, hU, hSU⟩ := hPQ S hS
  exact ⟨U, hU, hTS.trans hSU⟩

end Refinement

/-! ### Partition splitting -/

section Split

variable [IsProbabilityMeasure μ]

/-- Split one part of a partition into two pieces.

Given partition P and a part S ∈ P.parts, and a measurable subset S₁ ⊆ S,
construct the refinement Q that replaces S with S₁ and S \ S₁.

**Preconditions**:
- S ∈ P.parts
- S₁ ⊆ S is measurable
- Both S₁ and S \ S₁ have positive measure (to be non-trivial)

**Implementation note**: Uses classical decidability for Finset operations on Set α. -/
noncomputable def MeasurablePartition.splitPart (P : MeasurablePartition α μ)
    (S : Set α) (hS : S ∈ P.parts) (S₁ : Set α) (hS₁_meas : MeasurableSet S₁)
    (hS₁_sub : S₁ ⊆ S) (_hS₁_pos : μ S₁ ≠ 0) (_hS₂_pos : μ (S \ S₁) ≠ 0) :
    MeasurablePartition α μ := by
  classical
  exact {
    -- Replace S with {S₁, S \ S₁} in parts
    parts := (P.parts.erase S) ∪ {S₁, S \ S₁}
    measurable_parts := fun T hT => by
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
          Finset.mem_singleton] at hT
      rcases hT with ⟨_, hT_in⟩ | (rfl | rfl)
      · exact P.measurableSet_part hT_in
      · exact hS₁_meas
      · exact (P.measurableSet_part hS).diff hS₁_meas
    pairwiseDisjoint := fun T₁ hT₁ T₂ hT₂ hne => by
      simp only [Finset.coe_union, Finset.coe_erase, Finset.coe_insert,
          Finset.coe_singleton, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff,
          Set.mem_insert_iff] at hT₁ hT₂
      rcases hT₁ with ⟨hT₁_in, hT₁_ne⟩ | (hT₁_eq | hT₁_eq)
      <;> rcases hT₂ with ⟨hT₂_in, hT₂_ne⟩ | (hT₂_eq | hT₂_eq)
      · exact P.pairwiseDisjoint hT₁_in hT₂_in hne
      · subst hT₂_eq; exact (P.pairwiseDisjoint hT₁_in hS hT₁_ne).mono_right hS₁_sub
      · subst hT₂_eq; exact (P.pairwiseDisjoint hT₁_in hS hT₁_ne).mono_right diff_subset
      · subst hT₁_eq; exact ((P.pairwiseDisjoint hT₂_in hS hT₂_ne).mono_right hS₁_sub).symm
      · subst hT₁_eq; subst hT₂_eq; exact absurd rfl hne
      · subst hT₁_eq; subst hT₂_eq; exact Set.disjoint_sdiff_right
      · subst hT₁_eq; exact ((P.pairwiseDisjoint hT₂_in hS hT₂_ne).mono_right diff_subset).symm
      · subst hT₁_eq; subst hT₂_eq; exact Set.disjoint_sdiff_right.symm
      · subst hT₁_eq; subst hT₂_eq; exact absurd rfl hne
    ae_covers := by
      filter_upwards [P.ae_covers] with x ⟨T, hT, hx⟩
      by_cases hTS : T = S
      · by_cases hx₁ : x ∈ S₁
        · exact ⟨S₁, Finset.mem_union_right _ (Finset.mem_insert_self _ _), hx₁⟩
        · exact ⟨S \ S₁, Finset.mem_union_right _
            (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), hTS ▸ hx, hx₁⟩
      · exact ⟨T, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hTS, hT⟩), hx⟩
  }

/-- Splitting a part produces a refinement. -/
theorem MeasurablePartition.splitPart_refines (P : MeasurablePartition α μ)
    (S : Set α) (hS : S ∈ P.parts) (S₁ : Set α) (hS₁_meas : MeasurableSet S₁)
    (hS₁_sub : S₁ ⊆ S) (hS₁_pos : μ S₁ ≠ 0) (hS₂_pos : μ (S \ S₁) ≠ 0) :
    Refines (MeasurablePartition.splitPart P S hS S₁ hS₁_meas hS₁_sub hS₁_pos hS₂_pos) P := by
  classical
  intro T hT
  simp only [splitPart, Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
      Finset.mem_singleton] at hT
  rcases hT with ⟨_, hT_in⟩ | (rfl | rfl)
  · exact ⟨T, hT_in, Subset.refl T⟩
  · exact ⟨S, hS, hS₁_sub⟩
  · exact ⟨S, hS, diff_subset⟩

/-- Splitting adds at most one part. -/
theorem MeasurablePartition.splitPart_card (P : MeasurablePartition α μ)
    (S : Set α) (hS : S ∈ P.parts) (S₁ : Set α) (hS₁_meas : MeasurableSet S₁)
    (hS₁_sub : S₁ ⊆ S) (hS₁_pos : μ S₁ ≠ 0) (hS₂_pos : μ (S \ S₁) ≠ 0) :
    (MeasurablePartition.splitPart P S hS S₁ hS₁_meas hS₁_sub hS₁_pos hS₂_pos).parts.card
      ≤ P.parts.card + 1 := by
  classical
  simp only [splitPart]
  calc ((P.parts.erase S) ∪ {S₁, S \ S₁}).card
      ≤ (P.parts.erase S).card + ({S₁, S \ S₁} : Finset (Set α)).card := Finset.card_union_le _ _
    _ ≤ (P.parts.card - 1) + 2 := by
        apply add_le_add
        · rw [Finset.card_erase_of_mem hS]
        · exact Finset.card_insert_le S₁ {S \ S₁}
    _ ≤ P.parts.card + 1 := by
        have h_pos : 1 ≤ P.parts.card := Finset.one_le_card.mpr ⟨S, hS⟩
        omega

/-- Split every part of a partition by a measurable set A.

For each S ∈ P.parts, we include S ∩ A and S \ A in the new partition
(keeping all pieces, even null ones — this simplifies ae_covers).

This is the global splitting operation needed for the Frieze-Kannan
regularity proof when both within-variances are large. -/
noncomputable def MeasurablePartition.splitAllParts (P : MeasurablePartition α μ)
    (A : Set α) (hA : MeasurableSet A) : MeasurablePartition α μ := by
  classical
  let pieces (S : Set α) : Finset (Set α) := {S ∩ A, S \ A}
  exact {
    parts := P.parts.biUnion pieces
    measurable_parts := fun T hT => by
      simp only [pieces, Finset.mem_biUnion, Finset.mem_insert,
          Finset.mem_singleton] at hT
      obtain ⟨S, hS_mem, rfl | rfl⟩ := hT
      · exact (P.measurableSet_part hS_mem).inter hA
      · exact (P.measurableSet_part hS_mem).diff hA
    pairwiseDisjoint := fun T₁ hT₁ T₂ hT₂ hne => by
      simp only [pieces, Finset.coe_biUnion, Finset.coe_insert, Finset.coe_singleton,
          Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff,
          Finset.mem_coe] at hT₁ hT₂
      obtain ⟨S₁, hS₁_mem, rfl | rfl⟩ := hT₁
        <;> obtain ⟨S₂, hS₂_mem, rfl | rfl⟩ := hT₂
      -- (S₁ ∩ A, S₂ ∩ A)
      · by_cases h : S₁ = S₂
        · subst h; exact absurd rfl hne
        · exact (P.pairwiseDisjoint hS₁_mem hS₂_mem h).mono
            Set.inter_subset_left Set.inter_subset_left
      -- (S₁ ∩ A, S₂ \ A)
      · by_cases h : S₁ = S₂
        · subst h; exact disjoint_inf_sdiff
        · exact (P.pairwiseDisjoint hS₁_mem hS₂_mem h).mono
            Set.inter_subset_left Set.diff_subset
      -- (S₁ \ A, S₂ ∩ A)
      · by_cases h : S₁ = S₂
        · subst h; exact disjoint_inf_sdiff.symm
        · exact (P.pairwiseDisjoint hS₁_mem hS₂_mem h).mono
            Set.diff_subset Set.inter_subset_left
      -- (S₁ \ A, S₂ \ A)
      · by_cases h : S₁ = S₂
        · subst h; exact absurd rfl hne
        · exact (P.pairwiseDisjoint hS₁_mem hS₂_mem h).mono
            Set.diff_subset Set.diff_subset
    ae_covers := by
      filter_upwards [P.ae_covers] with x ⟨S, hS_mem, hx⟩
      by_cases hxA : x ∈ A
      · exact ⟨S ∩ A, Finset.mem_biUnion.mpr ⟨S, hS_mem,
          Finset.mem_insert_self _ _⟩, hx, hxA⟩
      · exact ⟨S \ A, Finset.mem_biUnion.mpr ⟨S, hS_mem,
          Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩, hx, hxA⟩
  }

omit [IsProbabilityMeasure μ] in
/-- splitAllParts produces a refinement. -/
theorem MeasurablePartition.splitAllParts_refines (P : MeasurablePartition α μ)
    (A : Set α) (hA : MeasurableSet A) :
    Refines (MeasurablePartition.splitAllParts P A hA) P := by
  classical
  intro T hT
  simp only [splitAllParts, Finset.mem_biUnion, Finset.mem_insert,
      Finset.mem_singleton] at hT
  obtain ⟨S, hS_mem, rfl | rfl⟩ := hT
  · exact ⟨S, hS_mem, Set.inter_subset_left⟩
  · exact ⟨S, hS_mem, Set.diff_subset⟩

omit [IsProbabilityMeasure μ] in
/-- splitAllParts has at most 2 * P.parts.card parts. -/
theorem MeasurablePartition.splitAllParts_card (P : MeasurablePartition α μ)
    (A : Set α) (hA : MeasurableSet A) :
    (MeasurablePartition.splitAllParts P A hA).parts.card ≤ 2 * P.parts.card := by
  classical
  simp only [splitAllParts]
  calc (P.parts.biUnion fun S => ({S ∩ A, S \ A} : Finset (Set α))).card
      ≤ P.parts.sum (fun S => ({S ∩ A, S \ A} : Finset (Set α)).card) :=
        Finset.card_biUnion_le
    _ ≤ P.parts.sum (fun _ => 2) := by
        apply Finset.sum_le_sum
        intro S _
        exact Finset.card_insert_le _ _
    _ = 2 * P.parts.card := by simp [Finset.sum_const, mul_comm]

end Split

/-! ### Stepification -/

section Stepify

variable [IsProbabilityMeasure μ]

/-- The stepification function: piecewise constant on partition rectangles.

For a partition P and graphon W, `stepifyFun P W (x,y) = rectAverage W S T`
when `(x,y) ∈ S × T` for `S, T ∈ P.parts`. -/
noncomputable def stepifyFun (P : MeasurablePartition α μ) (W : Graphon α μ) :
    α × α → ℝ :=
  fun p => ∑ S ∈ P.parts, ∑ T ∈ P.parts,
    (S ×ˢ T).indicator (fun _ => rectAverage W S T) p

omit [IsProbabilityMeasure μ] in
/-- `stepifyFun` is measurable. -/
theorem stepifyFun_measurable (P : MeasurablePartition α μ) (W : Graphon α μ) :
    Measurable (stepifyFun P W) := by
  unfold stepifyFun
  apply Finset.measurable_sum
  intro S hS
  apply Finset.measurable_sum
  intro T hT
  exact measurable_const.indicator
    ((P.measurableSet_part hS).prod (P.measurableSet_part hT))

/-- `stepifyFun` is symmetric: `stepifyFun P W (y,x) = stepifyFun P W (x,y)`. -/
theorem stepifyFun_symm (P : MeasurablePartition α μ) (W : Graphon α μ)
    (p : α × α) :
    stepifyFun P W p.swap = stepifyFun P W p := by
  simp only [stepifyFun]
  -- LHS = ∑ S, ∑ T, (S ×ˢ T).indicator (c S T) p.swap
  -- For p.swap ∈ S ×ˢ T ↔ p ∈ T ×ˢ S, so swapping summation gives RHS
  -- Strategy: show LHS = ∑ S, ∑ T, (T ×ˢ S).indicator (c T S) p
  --         = ∑ T, ∑ S, (T ×ˢ S).indicator (c T S) p = RHS
  -- First, rewrite each indicator: (S ×ˢ T).indicator f p.swap = (T ×ˢ S).indicator f p
  have h_swap : ∀ (S T : Set α) (c : ℝ),
      (S ×ˢ T).indicator (fun _ => c) p.swap = (T ×ˢ S).indicator (fun _ => c) p := by
    intro S T c
    by_cases hp : p.swap ∈ S ×ˢ T
    · obtain ⟨h1, h2⟩ := Set.mem_prod.mp hp
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem (Set.mem_prod.mpr ⟨h2, h1⟩)]
    · rw [Set.indicator_of_notMem hp]
      symm
      apply Set.indicator_of_notMem
      intro h; apply hp
      obtain ⟨h1, h2⟩ := Set.mem_prod.mp h
      exact Set.mem_prod.mpr ⟨h2, h1⟩
  simp_rw [h_swap]
  -- Now LHS = ∑ S, ∑ T, (T ×ˢ S).indicator (c S T) p
  -- Now LHS = ∑ S, ∑ T, (T ×ˢ S).indicator (c S T) p
  -- After sum_comm: = ∑ T, ∑ S, (T ×ˢ S).indicator (c S T) p
  -- Rename T → A, S → B: = ∑ A, ∑ B, (A ×ˢ B).indicator (c B A) p
  -- Use rectAverage_symm: c B A = c A B
  -- So = ∑ A, ∑ B, (A ×ˢ B).indicator (c A B) p = RHS
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro B hB
  congr 1; ext _
  exact rectAverage_symm W B A (P.measurableSet_part hB) (P.measurableSet_part hA)

set_option linter.unusedSectionVars false in
/-- At every point in S × T, the stepification equals rectAverage W S T.

For any (x,y), if x ∈ S and y ∈ T for unique parts S, T ∈ P.parts,
then stepifyFun P W (x,y) = rectAverage W S T. -/
theorem stepifyFun_eq_rectAverage (P : MeasurablePartition α μ) (W : Graphon α μ)
    {p : α × α} {S : Set α} (hS : S ∈ P.parts) {T : Set α} (hT : T ∈ P.parts)
    (hp : p ∈ S ×ˢ T) : stepifyFun P W p = rectAverage W S T := by
  unfold stepifyFun
  rw [Finset.sum_eq_single_of_mem S hS, Finset.sum_eq_single_of_mem T hT]
  · exact Set.indicator_of_mem hp _
  · intro T' hT'_mem hT'_ne
    apply Set.indicator_of_notMem
    intro hp'
    obtain ⟨_, hp2⟩ := Set.mem_prod.mp hp
    obtain ⟨_, hp2'⟩ := Set.mem_prod.mp hp'
    have h_disj := P.pairwiseDisjoint (Finset.mem_coe.mpr hT) (Finset.mem_coe.mpr hT'_mem) hT'_ne.symm
    exact Set.disjoint_left.mp h_disj hp2 hp2'
  · intro S' hS'_mem hS'_ne
    apply Finset.sum_eq_zero
    intro T' _
    apply Set.indicator_of_notMem
    intro hp'
    obtain ⟨hp1, _⟩ := Set.mem_prod.mp hp
    obtain ⟨hp1', _⟩ := Set.mem_prod.mp hp'
    have h_disj := P.pairwiseDisjoint (Finset.mem_coe.mpr hS) (Finset.mem_coe.mpr hS'_mem) hS'_ne.symm
    exact Set.disjoint_left.mp h_disj hp1 hp1'

/-- `stepifyFun` takes values in [0,1] a.e. -/
theorem stepifyFun_mem_Icc_ae (P : MeasurablePartition α μ) (W : Graphon α μ) :
    ∀ᵐ p ∂(μ.prod μ), stepifyFun P W p ∈ Set.Icc 0 1 := by
  -- For a.e. p, p ∈ S × T for some S, T ∈ P.parts
  -- and stepifyFun P W p = rectAverage W S T ∈ [0,1]
  have h_covers := P.ae_covers
  -- Lift ae_covers to the product measure via quasiMeasurePreserving
  have h_fst : ∀ᵐ p ∂(μ.prod μ), ∃ S ∈ P.parts, p.1 ∈ S :=
    Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst) h_covers
  have h_snd : ∀ᵐ p ∂(μ.prod μ), ∃ T ∈ P.parts, p.2 ∈ T :=
    Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_snd) h_covers
  filter_upwards [h_fst, h_snd] with p ⟨S, hS, hpS⟩ ⟨T, hT, hpT⟩
  rw [stepifyFun_eq_rectAverage P W hS hT (Set.mem_prod.mpr ⟨hpS, hpT⟩)]
  exact rectAverage_mem_Icc W S T (P.measurableSet_part hS) (P.measurableSet_part hT)

/-- The stepification of a graphon with respect to a partition.

This is the step graphon that equals `rectAverage W S T` on each rectangle `S × T`
for parts `S, T ∈ P.parts`. -/
noncomputable def stepify (P : MeasurablePartition α μ) (W : Graphon α μ) :
    Graphon α μ where
  toSymmKernel := {
    toAEEqFun := AEEqFun.mk (stepifyFun P W)
        (stepifyFun_measurable P W).aestronglyMeasurable
    symm' := by
      have h_coeFn : ∀ᵐ p ∂(μ.prod μ),
          (AEEqFun.mk (stepifyFun P W)
            (stepifyFun_measurable P W).aestronglyMeasurable : (α × α) →ₘ[μ.prod μ] ℝ) p =
          stepifyFun P W p :=
        AEEqFun.coeFn_mk _ _
      have h_coeFn_swap := ae_prod_swap h_coeFn
      filter_upwards [h_coeFn, h_coeFn_swap] with p hp hp_swap
      rw [hp_swap, hp]
      exact stepifyFun_symm P W p
  }
  ae_mem_Icc := by
    have h_coeFn : ∀ᵐ p ∂(μ.prod μ),
        (AEEqFun.mk (stepifyFun P W)
          (stepifyFun_measurable P W).aestronglyMeasurable : (α × α) →ₘ[μ.prod μ] ℝ) p =
        stepifyFun P W p :=
      AEEqFun.coeFn_mk _ _
    filter_upwards [h_coeFn, stepifyFun_mem_Icc_ae P W] with p hp h_Icc
    rw [hp]; exact h_Icc

/-- The stepification agrees with the stepification function a.e. -/
theorem stepify_ae (P : MeasurablePartition α μ) (W : Graphon α μ) :
    ∀ᵐ p ∂(μ.prod μ), (stepify P W).toAEEqFun p = stepifyFun P W p :=
  AEEqFun.coeFn_mk _ _

-- Note: cutNormDiff_stepify_le was removed because the regularity lemma
-- (Regularity.lean) now provides `cutNormDiff W (stepify P W) ≤ ε` directly,
-- making a separate Cauchy-Schwarz bound on the defect unnecessary.

end Stepify

end Graphon
