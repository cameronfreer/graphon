/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.CutDistance
import Graphon.Regularity
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Compactness of Graphon Space

This file develops the compactness properties of the space of graphons
with respect to cut distance.

## Main definitions

* `Graphon.Quotient` - The quotient of graphons by weak isomorphism (δ□ = 0)
* `Graphon.cutDistanceQuotient` - Cut distance as a proper metric on the quotient

## Main results

* `Graphon.cutDistance_quotient_metric` - Cut distance is a metric on the quotient
* `Graphon.quotient_compact` - The quotient space is compact

## Implementation notes

The space of graphons modulo weak isomorphism, equipped with cut distance,
is a compact metric space. This is the fundamental compactness result that
enables the theory of graph limits.

The compactness follows from:
1. The regularity lemma gives total boundedness
2. Completeness follows from a martingale convergence argument

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Section 9.3
-/

open MeasureTheory Set Filter Finset

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

/-! ### Quotient by weak isomorphism -/

section Quotient

variable [IsProbabilityMeasure μ]

/-- Two graphons are weakly isomorphic iff their cut distance is zero. -/
def WeaklyIsomorphic (U W : Graphon α μ) : Prop :=
  cutDistance U W = 0

/-- Weak isomorphism is reflexive. -/
theorem WeaklyIsomorphic.refl (W : Graphon α μ) : WeaklyIsomorphic W W :=
  cutDistance_self W

/-- Weak isomorphism is symmetric.

Note: With the two-sided cut distance definition, this no longer requires `StandardBorelSpace`. -/
theorem WeaklyIsomorphic.symm {U W : Graphon α μ}
    (h : WeaklyIsomorphic U W) : WeaklyIsomorphic W U := by
  unfold WeaklyIsomorphic at *
  rw [cutDistance_symm]
  exact h

/-- Weak isomorphism is transitive (on standard Borel spaces). -/
theorem WeaklyIsomorphic.trans [StandardBorelSpace α] {U V W : Graphon α μ}
    (hUV : WeaklyIsomorphic U V) (hVW : WeaklyIsomorphic V W) :
    WeaklyIsomorphic U W := by
  unfold WeaklyIsomorphic at *
  -- Use triangle inequality: d(U,W) ≤ d(U,V) + d(V,W) = 0 + 0 = 0
  have h_tri := cutDistance_triangle U V W
  have h_nonneg := cutDistance_nonneg U W
  linarith

/-- Weak isomorphism is an equivalence relation (on standard Borel spaces).

Note: Only `trans` still requires `StandardBorelSpace` (for the triangle inequality). -/
theorem weaklyIsomorphic_equivalence [StandardBorelSpace α] :
    Equivalence (WeaklyIsomorphic (α := α) (μ := μ)) :=
  ⟨WeaklyIsomorphic.refl, WeaklyIsomorphic.symm, @WeaklyIsomorphic.trans _ _ _ _ _⟩

/-- Relationship between `WeaklyIsomorphic` and `WeakIso`:

`WeakIso U W` (one-sided pullback relation) implies `WeaklyIsomorphic U W` (cutDistance = 0).

The converse direction (cutDistance = 0 implies WeakIso in both directions) requires
additional structure on the probability space (e.g., standard Borel). -/
theorem WeakIso.weaklyIsomorphic {U W : Graphon α μ} (h : WeakIso U W) :
    WeaklyIsomorphic U W := by
  unfold WeaklyIsomorphic cutDistance
  obtain ⟨φ, hφ, hU⟩ := h
  -- Use φ and id as witnesses: U = pullback W φ so cutNormDiff (pullback U id) (pullback W φ) = 0
  apply le_antisymm
  · apply csInf_le
    · use 0
      intro d ⟨ψ₁, ψ₂, hψ₁, hψ₂, hd⟩
      rw [hd]
      exact cutNormDiff_nonneg (Graphon.pullback U ψ₁ hψ₁) (Graphon.pullback W ψ₂ hψ₂)
    · refine ⟨id, φ, MeasurePreserving.id μ, hφ, ?_⟩
      simp only [pullback_id]
      rw [hU]
      exact (cutNormDiff_self (Graphon.pullback W φ hφ)).symm
  · exact cutDistance_nonneg U W

end Quotient

/-! ### Total boundedness -/

section TotalBoundedness

variable [IsProbabilityMeasure μ] [StandardBorelSpace α]

/-- Step graphon from explicit coefficients on a partition.

Given a partition P and a symmetric coefficient function `c : Set α → Set α → ℝ`
valued in [0,1], builds the step graphon constant on each rectangle with value c S T. -/
noncomputable def mkStepFun (P : MeasurablePartition α μ) (c : Set α → Set α → ℝ) :
    α × α → ℝ :=
  fun p => ∑ S ∈ P.parts, ∑ T ∈ P.parts,
    (S ×ˢ T).indicator (fun _ => c S T) p

omit [StandardBorelSpace α] in
private theorem mkStepFun_measurable (P : MeasurablePartition α μ) (c : Set α → Set α → ℝ) :
    Measurable (mkStepFun P c) := by
  unfold mkStepFun
  apply Finset.measurable_sum; intro S hS
  apply Finset.measurable_sum; intro T hT
  exact measurable_const.indicator ((P.measurableSet_part hS).prod (P.measurableSet_part hT))

omit [StandardBorelSpace α] in
private theorem mkStepFun_eq_at (P : MeasurablePartition α μ) (c : Set α → Set α → ℝ)
    {p : α × α} {S : Set α} (hS : S ∈ P.parts) {T : Set α} (hT : T ∈ P.parts)
    (hp : p ∈ S ×ˢ T) : mkStepFun P c p = c S T := by
  unfold mkStepFun
  rw [Finset.sum_eq_single_of_mem S hS, Finset.sum_eq_single_of_mem T hT]
  · exact Set.indicator_of_mem hp _
  · intro T' hT'_mem hT'_ne; apply Set.indicator_of_notMem; intro hp'
    exact Set.disjoint_left.mp (P.pairwiseDisjoint (Finset.mem_coe.mpr hT)
      (Finset.mem_coe.mpr hT'_mem) hT'_ne.symm) (Set.mem_prod.mp hp).2 (Set.mem_prod.mp hp').2
  · intro S' hS'_mem hS'_ne; apply Finset.sum_eq_zero; intro T' _
    apply Set.indicator_of_notMem; intro hp'
    exact Set.disjoint_left.mp (P.pairwiseDisjoint (Finset.mem_coe.mpr hS)
      (Finset.mem_coe.mpr hS'_mem) hS'_ne.symm) (Set.mem_prod.mp hp).1 (Set.mem_prod.mp hp').1

omit [StandardBorelSpace α] in
private theorem mkStepFun_symm (P : MeasurablePartition α μ) (c : Set α → Set α → ℝ)
    (hc : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T = c T S) (p : α × α) :
    mkStepFun P c p.swap = mkStepFun P c p := by
  simp only [mkStepFun]
  have h_swap : ∀ (S T : Set α) (v : ℝ),
      (S ×ˢ T).indicator (fun _ => v) p.swap = (T ×ˢ S).indicator (fun _ => v) p := by
    intro S T v
    by_cases hp : p.swap ∈ S ×ˢ T
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem]
      exact Set.mem_prod.mpr ⟨(Set.mem_prod.mp hp).2, (Set.mem_prod.mp hp).1⟩
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem]; intro h
      exact hp (Set.mem_prod.mpr ⟨(Set.mem_prod.mp h).2, (Set.mem_prod.mp h).1⟩)
  simp_rw [h_swap]; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro A hA
  apply Finset.sum_congr rfl; intro B hB
  congr 1; ext _; exact hc B hB A hA

omit [StandardBorelSpace α] in
private theorem mkStepFun_mem_Icc_ae (P : MeasurablePartition α μ) (c : Set α → Set α → ℝ)
    (hc : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T ∈ Set.Icc 0 1) :
    ∀ᵐ p ∂(μ.prod μ), mkStepFun P c p ∈ Set.Icc 0 1 := by
  have h_fst : ∀ᵐ p ∂(μ.prod μ), ∃ S ∈ P.parts, p.1 ∈ S :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst P.ae_covers
  have h_snd : ∀ᵐ p ∂(μ.prod μ), ∃ T ∈ P.parts, p.2 ∈ T :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd P.ae_covers
  filter_upwards [h_fst, h_snd] with p ⟨S, hS, hpS⟩ ⟨T, hT, hpT⟩
  rw [mkStepFun_eq_at P c hS hT (Set.mem_prod.mpr ⟨hpS, hpT⟩)]
  exact hc S hS T hT

omit [StandardBorelSpace α] in
/-- Build a `Graphon` from explicit coefficients on a partition. -/
@[blueprint "def:mkStepGraphon"
  (title := /-- Step graphon from coefficients -/)]
noncomputable def mkStepGraphon (P : MeasurablePartition α μ) (c : Set α → Set α → ℝ)
    (hc_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T = c T S)
    (hc_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T ∈ Set.Icc 0 1) :
    Graphon α μ where
  toSymmKernel := {
    toAEEqFun := AEEqFun.mk (mkStepFun P c) (mkStepFun_measurable P c).aestronglyMeasurable
    symm' := by
      filter_upwards [AEEqFun.coeFn_mk (mkStepFun P c)
        (mkStepFun_measurable P c).aestronglyMeasurable,
        ae_prod_swap (AEEqFun.coeFn_mk (mkStepFun P c)
          (mkStepFun_measurable P c).aestronglyMeasurable)] with p hp hp_swap
      rw [hp_swap, hp]; exact mkStepFun_symm P c hc_symm p
  }
  ae_mem_Icc := by
    filter_upwards [AEEqFun.coeFn_mk (mkStepFun P c)
      (mkStepFun_measurable P c).aestronglyMeasurable,
      mkStepFun_mem_Icc_ae P c hc_mem] with p hp h_Icc
    rw [hp]; exact h_Icc

omit [StandardBorelSpace α] in
/-- cutNormDiff between step graphons on the same partition with close coefficients
    is controlled by the coefficient difference. -/
theorem cutNormDiff_mkStepGraphon_le (P : MeasurablePartition α μ)
    (c c' : Set α → Set α → ℝ)
    (hc_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T = c T S)
    (hc_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T ∈ Set.Icc 0 1)
    (hc'_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c' S T = c' T S)
    (hc'_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c' S T ∈ Set.Icc 0 1)
    (δ : ℝ) (hδ : ∀ S ∈ P.parts, ∀ T ∈ P.parts, |c S T - c' S T| ≤ δ) :
    cutNormDiff (mkStepGraphon P c hc_symm hc_mem)
               (mkStepGraphon P c' hc'_symm hc'_mem) ≤ δ := by
  -- Derive 0 ≤ δ from hypotheses
  have hδ_nn : 0 ≤ δ := by
    -- P.parts is nonempty since we have IsProbabilityMeasure
    have h_ne : P.parts.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      have h_ae := P.ae_covers
      have : ∀ᵐ _ ∂μ, False := by
        filter_upwards [h_ae] with x ⟨S, hS, _⟩
        simp [h] at hS
      exact absurd this (by
        rw [Filter.eventually_false_iff_eq_bot]
        exact (IsProbabilityMeasure.ae_neBot (μ := μ)).ne)
    obtain ⟨S, hS⟩ := h_ne
    exact le_trans (abs_nonneg _) (hδ S hS S hS)
  -- Key: the pointwise difference of the step functions is bounded by δ a.e.
  have h_diff_ae : ∀ᵐ p ∂(μ.prod μ), |mkStepFun P c p - mkStepFun P c' p| ≤ δ := by
    have h_fst : ∀ᵐ p ∂(μ.prod μ), ∃ S ∈ P.parts, p.1 ∈ S :=
      Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst P.ae_covers
    have h_snd : ∀ᵐ p ∂(μ.prod μ), ∃ T ∈ P.parts, p.2 ∈ T :=
      Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd P.ae_covers
    filter_upwards [h_fst, h_snd] with p ⟨S, hS, hpS⟩ ⟨T, hT, hpT⟩
    have hp : p ∈ S ×ˢ T := Set.mem_prod.mpr ⟨hpS, hpT⟩
    rw [mkStepFun_eq_at P c hS hT hp, mkStepFun_eq_at P c' hS hT hp]
    exact hδ S hS T hT
  -- Connect AEEqFun to mkStepFun
  set U := mkStepGraphon P c hc_symm hc_mem
  set W := mkStepGraphon P c' hc'_symm hc'_mem
  have hU_eq : ∀ᵐ p ∂(μ.prod μ), U.toAEEqFun p = mkStepFun P c p :=
    AEEqFun.coeFn_mk (mkStepFun P c) (mkStepFun_measurable P c).aestronglyMeasurable
  have hW_eq : ∀ᵐ p ∂(μ.prod μ), W.toAEEqFun p = mkStepFun P c' p :=
    AEEqFun.coeFn_mk (mkStepFun P c') (mkStepFun_measurable P c').aestronglyMeasurable
  -- The AEEqFun difference is bounded by δ a.e.
  have h_ae_bound : ∀ᵐ p ∂(μ.prod μ), |U.toAEEqFun p - W.toAEEqFun p| ≤ δ := by
    filter_upwards [hU_eq, hW_eq, h_diff_ae] with p hU hW hdiff
    rw [hU, hW]; exact hdiff
  -- Now unfold cutNormDiff and bound the iSup
  unfold cutNormDiff
  apply Real.iSup_le _ hδ_nn; intro S'
  apply Real.iSup_le _ hδ_nn; intro _
  apply Real.iSup_le _ hδ_nn; intro T'
  apply Real.iSup_le _ hδ_nn; intro _
  simp only [rectIntegralDiff]
  -- |∫_{S'×T'} (U-W)| ≤ ∫_{S'×T'} |U-W| ≤ ∫_{S'×T'} δ = δ · μ(S'×T') ≤ δ
  calc |∫ p in S' ×ˢ T', (U.toAEEqFun p - W.toAEEqFun p) ∂(μ.prod μ)|
      ≤ ∫ p in S' ×ˢ T', |U.toAEEqFun p - W.toAEEqFun p| ∂(μ.prod μ) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _ in S' ×ˢ T', δ ∂(μ.prod μ) := by
        apply setIntegral_mono_ae_restrict
        · exact ((SymmKernel.graphon_integrable U).sub
            (SymmKernel.graphon_integrable W)).abs.integrableOn
        · exact integrable_const δ
        · exact ae_restrict_of_ae h_ae_bound
    _ = (μ.prod μ).real (S' ×ˢ T') * δ := by
        rw [setIntegral_const, smul_eq_mul]
    _ ≤ 1 * δ := by
        apply mul_le_mul_of_nonneg_right _ hδ_nn
        rw [Measure.real]
        have h_le : (μ.prod μ) (S' ×ˢ T') ≤ 1 := by
          calc (μ.prod μ) (S' ×ˢ T') ≤ (μ.prod μ) univ := measure_mono (subset_univ _)
            _ = 1 := (inferInstance : IsProbabilityMeasure (μ.prod μ)).measure_univ
        exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by
          simp only [ENNReal.ofReal_one]; exact h_le)
    _ = δ := one_mul δ

/-- The space of graphons is totally bounded with respect to cut distance.

For any ε > 0, there exists a finite set of graphons such that every
graphon is within ε (in cut distance) of some element of the set.

This follows from the regularity lemma: step graphons with bounded
number of parts form an ε-net.

**Proof outline**:
1. Let k = regularityBound(ε/2) be the max number of partition parts
2. For any W, regularity gives P_W with ≤ k parts and cutNormDiff ≤ ε/2
3. stepify P_W W is a step graphon with coefficients in [0,1]
4. Quantize coefficients to grid with spacing δ, giving ε/2 error in cutNormDiff
5. Gridpoints on P_W = gridpoints on any other partition up to cutDistance 0
   (via measure-preserving map between partitions, needs StandardBorelSpace)
6. Triangle: W within ε of nearest gridpoint -/
@[blueprint "thm:totallyBounded"
  (title := /-- Total boundedness of graphon space -/)]
theorem totallyBounded (ε : ℝ) (hε : ε > 0) :
    ∃ (S : Finset (Graphon α μ)), ∀ W : Graphon α μ, ∃ V ∈ S, cutDistance W V ≤ ε := by
  -- Proof (Lovász [2012], Proposition 9.15):
  -- Fix a reference partition P₀. Build a finite net of grid step graphons on P₀.
  -- For any W: regularity gives P_W with cutNormDiff ≤ ε/2, round coefficients
  -- (error ≤ ε/2), then partition transfer (Rokhlin) maps to a net element.
  -- Triangle: cutDistance W (net element) ≤ ε/2 + ε/2 + 0 = ε.
  --
  -- Parameters
  set ε₂ := ε / 2 with hε₂_def
  have hε₂ : ε₂ > 0 := by positivity
  set N := Nat.ceil (2 / ε) with hN_def
  have hN_pos : 0 < N := Nat.ceil_pos.mpr (by positivity)
  have hδ_le : (1 : ℝ) / N ≤ ε / 2 := by
    have hN_le : (2 / ε : ℝ) ≤ N := Nat.le_ceil (2 / ε)
    rw [div_le_div_iff₀ (Nat.cast_pos.mpr hN_pos) (by norm_num : (0:ℝ) < 2)]
    rw [one_mul]
    calc (2 : ℝ) = ε * (2 / ε) := by field_simp
      _ ≤ ε * N := by apply mul_le_mul_of_nonneg_left hN_le hε.le
  -- Fix reference partition P₀
  obtain ⟨P₀, _, _⟩ := regularity (mkStepGraphon (trivialPartition (α := α) (μ := μ))
    (fun _ _ => 1/2)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => ⟨by norm_num, by norm_num⟩)) ε₂ hε₂
  -- Build finite net on P₀: all mkStepGraphon P₀ with symmetrized grid coefficients
  classical
  let toCoeff : (↑P₀.parts → ↑P₀.parts → Fin (N + 1)) → Set α → Set α → ℝ :=
    fun f S T =>
      if hS : S ∈ P₀.parts then
        if hT : T ∈ P₀.parts then
          ((f ⟨S, hS⟩ ⟨T, hT⟩ : ℕ) + (f ⟨T, hT⟩ ⟨S, hS⟩ : ℕ)) / (2 * N)
        else 0
      else 0
  have htoCoeff_symm : ∀ f, ∀ S ∈ P₀.parts, ∀ T ∈ P₀.parts,
      toCoeff f S T = toCoeff f T S := by
    intro f S hS T hT
    simp only [toCoeff, hS, hT, dif_pos]
    ring
  have htoCoeff_mem : ∀ f, ∀ S ∈ P₀.parts, ∀ T ∈ P₀.parts,
      toCoeff f S T ∈ Set.Icc 0 1 := by
    intro f S hS T hT
    simp only [toCoeff, hS, hT, dif_pos, Set.mem_Icc]
    constructor
    · positivity
    · have h1 : (f ⟨S, hS⟩ ⟨T, hT⟩ : ℕ) ≤ N := by omega
      have h2 : (f ⟨T, hT⟩ ⟨S, hS⟩ : ℕ) ≤ N := by omega
      rw [div_le_one (by positivity : (0 : ℝ) < 2 * N)]
      have h1' : (↑(f ⟨S, hS⟩ ⟨T, hT⟩ : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr h1
      have h2' : (↑(f ⟨T, hT⟩ ⟨S, hS⟩ : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr h2
      linarith
  let netMap : (↑P₀.parts → ↑P₀.parts → Fin (N + 1)) → Graphon α μ :=
    fun f => mkStepGraphon P₀ (toCoeff f) (htoCoeff_symm f) (htoCoeff_mem f)
  let net : Finset (Graphon α μ) := Finset.univ.image netMap
  use net
  -- For any W, find a close net element
  intro W
  obtain ⟨P_W, _, hP_W_close⟩ := regularity W ε₂ hε₂
  -- cutDistance W (stepify P_W W) ≤ ε/2
  have h_cd_step : cutDistance W (stepify P_W W) ≤ ε₂ :=
    (cutDistance_le_cutNormDiff W (stepify P_W W)).trans hP_W_close
  -- Round rectAverages to nearest grid point: ⌊a * N⌋ / N
  let roundCoeff : Set α → Set α → ℝ := fun S T =>
    if hS : S ∈ P_W.parts then
      if hT : T ∈ P_W.parts then
        (Nat.floor (rectAverage W S T * N) : ℝ) / N
      else 0
    else 0
  have hround_symm : ∀ S ∈ P_W.parts, ∀ T ∈ P_W.parts, roundCoeff S T = roundCoeff T S := by
    intro S hS T hT
    simp only [roundCoeff, hS, hT, dif_pos]
    congr 1
    rw [rectAverage_symm W S T (P_W.measurableSet_part hS) (P_W.measurableSet_part hT)]
  have hround_mem : ∀ S ∈ P_W.parts, ∀ T ∈ P_W.parts, roundCoeff S T ∈ Set.Icc 0 1 := by
    intro S hS T hT
    simp only [roundCoeff, hS, hT, dif_pos, Set.mem_Icc]
    have h_avg := rectAverage_mem_Icc W S T (P_W.measurableSet_part hS) (P_W.measurableSet_part hT)
    constructor
    · positivity
    · rw [div_le_one (Nat.cast_pos.mpr hN_pos)]
      have : rectAverage W S T * N ≤ N := by nlinarith [h_avg.2]
      exact_mod_cast Nat.floor_le_of_le (by exact_mod_cast this)
  -- Coefficient difference: |rectAverage - roundCoeff| ≤ 1/N
  have hround_close : ∀ S ∈ P_W.parts, ∀ T ∈ P_W.parts,
      |rectAverage W S T - roundCoeff S T| ≤ 1 / (N : ℝ) := by
    intro S hS T hT
    simp only [roundCoeff, hS, hT, dif_pos]
    have h_avg := rectAverage_mem_Icc W S T (P_W.measurableSet_part hS) (P_W.measurableSet_part hT)
    have hN_pos' : (0 : ℝ) < N := Nat.cast_pos.mpr hN_pos
    have h_nn : 0 ≤ rectAverage W S T * N := mul_nonneg h_avg.1 (Nat.cast_nonneg N)
    have h_floor_le : (Nat.floor (rectAverage W S T * N) : ℝ) ≤ rectAverage W S T * N :=
      Nat.floor_le h_nn
    have h_lt_floor_add : rectAverage W S T * ↑N < (Nat.floor (rectAverage W S T * ↑N) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    rw [abs_le]
    constructor
    · -- lower bound: -(1/N) ≤ a - ⌊aN⌋/N
      -- Since ⌊aN⌋ ≤ aN, we have ⌊aN⌋/N ≤ a, so a - ⌊aN⌋/N ≥ 0 ≥ -(1/N)
      have h_sub_nn : 0 ≤ rectAverage W S T - (↑⌊rectAverage W S T * ↑N⌋₊ : ℝ) / N := by
        rw [sub_nonneg, div_le_iff₀ hN_pos']
        linarith
      have h_inv_pos : (0 : ℝ) < 1 / N := div_pos one_pos hN_pos'
      linarith
    · -- upper bound: a - ⌊aN⌋/N ≤ 1/N, i.e., aN ≤ ⌊aN⌋ + 1
      rw [sub_le_iff_le_add]
      rw [show 1 / (↑N : ℝ) + (↑⌊rectAverage W S T * ↑N⌋₊ : ℝ) / ↑N =
        (↑⌊rectAverage W S T * ↑N⌋₊ + 1) / ↑N from by ring]
      rw [le_div_iff₀ hN_pos']
      linarith
  -- The rounded step graphon
  set V_round := mkStepGraphon P_W roundCoeff hround_symm hround_mem
  -- cutDistance (stepify P_W W) V_round ≤ ε/2
  -- Key: stepifyFun P_W W = mkStepFun P_W (rectAverage W) pointwise (by definition),
  -- so stepify and mkStepGraphon with rectAverage coefficients have the same AEEqFun.
  -- Then cutNormDiff_mkStepGraphon_le bounds the grid rounding error.
  -- rectAverage symmetry and [0,1] membership for mkStepGraphon
  have hRA_symm : ∀ S ∈ P_W.parts, ∀ T ∈ P_W.parts,
      rectAverage W S T = rectAverage W T S := by
    intro S hS T hT
    exact rectAverage_symm W S T (P_W.measurableSet_part hS) (P_W.measurableSet_part hT)
  have hRA_mem : ∀ S ∈ P_W.parts, ∀ T ∈ P_W.parts,
      rectAverage W S T ∈ Set.Icc 0 1 := by
    intro S hS T hT
    exact rectAverage_mem_Icc W S T (P_W.measurableSet_part hS) (P_W.measurableSet_part hT)
  -- The step graphon with rectAverage coefficients
  set V_avg := mkStepGraphon P_W (rectAverage W) hRA_symm hRA_mem
  -- stepify and mkStepGraphon with rectAverage have the same underlying function
  -- (stepifyFun P_W W = mkStepFun P_W (rectAverage W) by definition)
  have h_stepify_eq_avg : ∀ᵐ p ∂(μ.prod μ),
      (stepify P_W W).toAEEqFun p = V_avg.toAEEqFun p := by
    -- Both AEEqFuns are mk'd from the same function (stepifyFun = mkStepFun for rectAverage)
    have h_fun_eq : stepifyFun P_W W = mkStepFun P_W (rectAverage W) := rfl
    have h1 := stepify_ae P_W W  -- stepify agrees with stepifyFun a.e.
    have h2 : ∀ᵐ p ∂(μ.prod μ), V_avg.toAEEqFun p = mkStepFun P_W (rectAverage W) p :=
      AEEqFun.coeFn_mk _ _
    filter_upwards [h1, h2] with p hp1 hp2
    rw [hp1, h_fun_eq, hp2]
  -- cutNormDiff (stepify P_W W) V_avg = 0
  have h_cn_zero : cutNormDiff (stepify P_W W) V_avg = 0 := by
    unfold cutNormDiff rectIntegralDiff
    apply le_antisymm
    · apply Real.iSup_le _ le_rfl
      intro S'; apply Real.iSup_le _ le_rfl
      intro hS'; apply Real.iSup_le _ le_rfl
      intro T'; apply Real.iSup_le _ le_rfl
      intro hT'
      have : ∀ᵐ p ∂(μ.prod μ),
          (stepify P_W W).toAEEqFun p - V_avg.toAEEqFun p = 0 := by
        filter_upwards [h_stepify_eq_avg] with p hp
        rw [hp, sub_self]
      have h_zero : ∫ p in S' ×ˢ T', ((stepify P_W W).toAEEqFun p - V_avg.toAEEqFun p) ∂(μ.prod μ) = 0 := by
        rw [setIntegral_congr_ae (hS'.prod hT') (this.mono (fun p hp _ => hp))]
        simp
      rw [h_zero]
      simp
    · exact cutNormDiff_nonneg _ _
  -- cutNormDiff V_avg V_round ≤ 1/N by cutNormDiff_mkStepGraphon_le
  have h_cn_round : cutNormDiff V_avg V_round ≤ 1 / (N : ℝ) :=
    cutNormDiff_mkStepGraphon_le P_W (rectAverage W) roundCoeff hRA_symm hRA_mem
      hround_symm hround_mem (1 / N) hround_close
  -- cutNormDiff (stepify P_W W) V_round ≤ 0 + 1/N = 1/N ≤ ε/2
  have h_cd_round : cutDistance (stepify P_W W) V_round ≤ ε / 2 := by
    calc cutDistance (stepify P_W W) V_round
        ≤ cutNormDiff (stepify P_W W) V_round := cutDistance_le_cutNormDiff _ _
      _ ≤ cutNormDiff (stepify P_W W) V_avg + cutNormDiff V_avg V_round :=
          cutNormDiff_triangle _ _ _
      _ = 0 + cutNormDiff V_avg V_round := by rw [h_cn_zero]
      _ = cutNormDiff V_avg V_round := zero_add _
      _ ≤ 1 / (N : ℝ) := h_cn_round
      _ ≤ ε / 2 := hδ_le
  -- Final assembly via triangle inequality
  -- Need: exists V in net with cutDistance V_round V = 0 (partition transfer)
  suffices h_exists_close : ∃ V ∈ net, cutDistance V_round V = 0 by
    obtain ⟨V, hV_mem, hV_dist⟩ := h_exists_close
    exact ⟨V, hV_mem, by
      calc cutDistance W V
          ≤ cutDistance W (stepify P_W W) + cutDistance (stepify P_W W) V :=
            cutDistance_triangle W (stepify P_W W) V
        _ ≤ cutDistance W (stepify P_W W) +
            (cutDistance (stepify P_W W) V_round + cutDistance V_round V) := by
            linarith [cutDistance_triangle (stepify P_W W) V_round V]
        _ = cutDistance W (stepify P_W W) + cutDistance (stepify P_W W) V_round + 0 := by
            rw [hV_dist]; ring
        _ ≤ ε₂ + ε / 2 + 0 := by linarith [h_cd_step, h_cd_round]
        _ = ε := by rw [hε₂_def]; ring⟩
  -- **Partition transfer**: V_round on P_W matches some net element on P₀ via Rokhlin.
  -- Step 1: Get partition alignment e : α ≃ᵐ α mapping P₀-cells a.e. into P_W-cells
  obtain ⟨e, he, h_align⟩ := MeasurePreserving.exists_partition_alignment P₀ P_W
  -- Step 2: For each P₀-cell, extract the corresponding P_W-cell
  -- σ maps each P₀-cell to its aligned P_W-cell
  have h_σ : ∀ S ∈ P₀.parts, ∃ T ∈ P_W.parts,
      μ (S \ e ⁻¹' T) = 0 ∧ μ (e ⁻¹' T \ S) = 0 := h_align
  -- Use classical choice to extract σ
  choose σ hσ_mem hσ_null using fun S (hS : S ∈ P₀.parts) => h_σ S hS
  -- Step 3: Define the net function f
  -- roundCoeff(σ(S), σ(T)) = ⌊rectAverage(W, σ(S), σ(T)) * N⌋ / N
  -- The numerator ⌊...⌋ is in {0, ..., N}, so it's a valid Fin(N+1)
  let f : ↑P₀.parts → ↑P₀.parts → Fin (N + 1) := fun ⟨S, hS⟩ ⟨T, hT⟩ =>
    ⟨Nat.floor (rectAverage W (σ S hS) (σ T hT) * N), by
      have h_avg := rectAverage_mem_Icc W (σ S hS) (σ T hT)
        (P_W.measurableSet_part (hσ_mem S hS))
        (P_W.measurableSet_part (hσ_mem T hT))
      apply Nat.lt_succ_of_le
      exact Nat.floor_le_of_le (by exact_mod_cast (by nlinarith [h_avg.2] : rectAverage W (σ S hS) (σ T hT) * ↑N ≤ ↑N))⟩
  -- Step 4: toCoeff f agrees with roundCoeff ∘ σ on P₀.parts
  have h_coeff_eq : ∀ S (hS : S ∈ P₀.parts) T (hT : T ∈ P₀.parts),
      toCoeff f S T = roundCoeff (σ S hS) (σ T hT) := by
    intro S hS T hT
    simp only [toCoeff, hS, hT, dif_pos, f, roundCoeff,
      hσ_mem S hS, hσ_mem T hT]
    -- toCoeff f S T = (⌊a*N⌋ + ⌊b*N⌋) / (2*N) where a = rectAvg(σS, σT), b = rectAvg(σT, σS)
    -- Since rectAverage is symmetric: a = b, so this = 2⌊a*N⌋/(2*N) = ⌊a*N⌋/N
    have h_symm_avg := rectAverage_symm W (σ S hS) (σ T hT)
      (P_W.measurableSet_part (hσ_mem S hS)) (P_W.measurableSet_part (hσ_mem T hT))
    rw [h_symm_avg]
    field_simp
    ring
  -- Step 5: netMap f ∈ net
  have hf_mem : netMap f ∈ net := Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩
  -- Step 6: pullback V_round e and netMap f agree a.e.
  -- Key: for a.e. (x, y), if x ∈ S₁ ∈ P₀, y ∈ S₂ ∈ P₀, then
  --   pullback V_round e (x,y) = roundCoeff(σ(S₁), σ(S₂))
  --   netMap f (x,y) = toCoeff f S₁ S₂ = roundCoeff(σ(S₁), σ(S₂))
  -- So they agree.
  have h_pb_ae : ∀ᵐ p ∂(μ.prod μ),
      (pullback V_round e he).toAEEqFun p = (netMap f).toAEEqFun p := by
    -- Get a.e. facts
    have h_pb := pullback_ae V_round (⇑e) he
    have h_net : ∀ᵐ p ∂(μ.prod μ),
        (netMap f).toAEEqFun p = mkStepFun P₀ (toCoeff f) p :=
      AEEqFun.coeFn_mk _ _
    have h_vr : ∀ᵐ p ∂(μ.prod μ),
        V_round.toAEEqFun p = mkStepFun P_W roundCoeff p :=
      AEEqFun.coeFn_mk _ _
    -- Push h_vr through the product MP map (Prod.map e e) to get it at image points
    have h_vr_image : ∀ᵐ p ∂(μ.prod μ),
        V_round.toAEEqFun (e p.1, e p.2) = mkStepFun P_W roundCoeff (e p.1, e p.2) := by
      have h_mp : MeasurePreserving (Prod.map e e) (μ.prod μ) (μ.prod μ) :=
        MeasurePreserving.prod he he
      exact h_mp.quasiMeasurePreserving.ae h_vr
    -- a.e. x is in some P₀-cell, a.e. y is in some P₀-cell
    have h_fst : ∀ᵐ p ∂(μ.prod μ), ∃ S ∈ P₀.parts, p.1 ∈ S :=
      Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst P₀.ae_covers
    have h_snd : ∀ᵐ p ∂(μ.prod μ), ∃ S ∈ P₀.parts, p.2 ∈ S :=
      Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd P₀.ae_covers
    -- a.e. x ∈ S ∈ P₀ implies e(x) ∈ σ(S): finite union of null sets is null
    -- For each S ∈ P₀.parts: μ(S \ e⁻¹(σ S)) = 0, so the finite union has measure 0
    have h_align_ae : ∀ᵐ x ∂μ,
        ∀ (S : Set α) (hS : S ∈ P₀.parts), x ∈ S → e x ∈ σ S hS := by
      -- For each S, show the a.e. property
      suffices ∀ S hS, ∀ᵐ x ∂μ, x ∈ S → e x ∈ σ S hS by
        have h_finite := (ae_ball_iff P₀.parts.countable_toSet).mpr this
        filter_upwards [h_finite] with x hx S hS hmem
        exact hx S hS hmem
      intro S hS
      have h_null := (hσ_null S hS).1
      rw [Filter.eventually_iff]
      apply Filter.mem_of_superset (compl_mem_ae_iff.mpr h_null)
      intro x hx hxS
      by_contra h_ne
      exact hx (Set.mem_diff_of_mem hxS h_ne)
    have h_e_fst : ∀ᵐ p ∂(μ.prod μ),
        ∀ (S : Set α) (hS : S ∈ P₀.parts), p.1 ∈ S → e p.1 ∈ σ S hS :=
      Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst h_align_ae
    have h_e_snd : ∀ᵐ p ∂(μ.prod μ),
        ∀ (S : Set α) (hS : S ∈ P₀.parts), p.2 ∈ S → e p.2 ∈ σ S hS :=
      Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd h_align_ae
    -- a.e. e(x) is in some P_W-cell (push P_W.ae_covers through the MP map e)
    have h_e_covers : ∀ᵐ x ∂μ, ∃ T ∈ P_W.parts, e x ∈ T :=
      he.quasiMeasurePreserving.ae P_W.ae_covers
    have h_e_fst_W : ∀ᵐ p ∂(μ.prod μ), ∃ T ∈ P_W.parts, e p.1 ∈ T :=
      Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst h_e_covers
    have h_e_snd_W : ∀ᵐ p ∂(μ.prod μ), ∃ T ∈ P_W.parts, e p.2 ∈ T :=
      Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd h_e_covers
    filter_upwards [h_pb, h_net, h_vr_image, h_fst, h_snd,
      h_e_fst, h_e_snd, h_e_fst_W, h_e_snd_W]
      with p h_pb h_net h_vr_image ⟨S₁, hS₁, hpS₁⟩ ⟨S₂, hS₂, hpS₂⟩
        h_ef h_es ⟨T₁, hT₁, heT₁⟩ ⟨T₂, hT₂, heT₂⟩
    -- pullback side
    rw [h_pb]
    -- V_round at (e p.1, e p.2) = roundCoeff T₁ T₂ (where e p.i ∈ T_i)
    have h_vr_val : V_round.toAEEqFun (e p.1, e p.2) = roundCoeff T₁ T₂ := by
      rw [h_vr_image]
      exact mkStepFun_eq_at P_W roundCoeff hT₁ hT₂ (Set.mem_prod.mpr ⟨heT₁, heT₂⟩)
    rw [h_vr_val]
    -- netMap f side: (netMap f) at p = toCoeff f S₁ S₂
    rw [h_net]
    rw [mkStepFun_eq_at P₀ (toCoeff f) hS₁ hS₂ (Set.mem_prod.mpr ⟨hpS₁, hpS₂⟩)]
    -- Now: roundCoeff T₁ T₂ = toCoeff f S₁ S₂
    rw [h_coeff_eq S₁ hS₁ S₂ hS₂]
    -- Need: T₁ = σ S₁ hS₁ and T₂ = σ S₂ hS₂
    -- e p.1 ∈ σ(S₁) (from h_ef) and e p.1 ∈ T₁
    -- Since P_W is a partition, σ(S₁) = T₁
    congr 1
    · -- T₁ = σ S₁ hS₁: both contain e p.1, both in P_W.parts
      by_contra h_ne
      exact Set.disjoint_left.mp (P_W.pairwiseDisjoint (Finset.mem_coe.mpr (hσ_mem S₁ hS₁))
        (Finset.mem_coe.mpr hT₁) (Ne.symm h_ne)) (h_ef S₁ hS₁ hpS₁) heT₁
    · by_contra h_ne
      exact Set.disjoint_left.mp (P_W.pairwiseDisjoint (Finset.mem_coe.mpr (hσ_mem S₂ hS₂))
        (Finset.mem_coe.mpr hT₂) (Ne.symm h_ne)) (h_es S₂ hS₂ hpS₂) heT₂
  -- Step 7: cutNormDiff between pullback and netMap f is 0
  have h_cn_pb : cutNormDiff (pullback V_round e he) (netMap f) = 0 := by
    apply le_antisymm
    · unfold cutNormDiff rectIntegralDiff
      apply Real.iSup_le _ le_rfl; intro S'
      apply Real.iSup_le _ le_rfl; intro hS'
      apply Real.iSup_le _ le_rfl; intro T'
      apply Real.iSup_le _ le_rfl; intro hT'
      have h_zero_ae : ∀ᵐ p ∂(μ.prod μ),
          (pullback V_round e he).toAEEqFun p - (netMap f).toAEEqFun p = 0 := by
        filter_upwards [h_pb_ae] with p hp; rw [hp, sub_self]
      rw [setIntegral_congr_ae (hS'.prod hT')
        (h_zero_ae.mono (fun p hp _ => hp))]
      simp
    · exact cutNormDiff_nonneg _ _
  -- Step 8: Combine
  refine ⟨netMap f, hf_mem, le_antisymm ?_ (cutDistance_nonneg _ _)⟩
  calc cutDistance V_round (netMap f)
      ≤ cutDistance V_round (pullback V_round e he) +
        cutDistance (pullback V_round e he) (netMap f) :=
        cutDistance_triangle V_round (pullback V_round e he) (netMap f)
    _ = 0 + cutDistance (pullback V_round e he) (netMap f) := by
        rw [cutDistance_pullback_eq_zero]
    _ ≤ 0 + cutNormDiff (pullback V_round e he) (netMap f) := by
        linarith [cutDistance_le_cutNormDiff (pullback V_round e he) (netMap f)]
    _ = 0 := by rw [h_cn_pb]; ring

end TotalBoundedness

/-! ### Completeness -/

section Completeness

variable [IsProbabilityMeasure μ] [StandardBorelSpace α]

/-- A sequence of graphons is Cauchy with respect to cut distance. -/
def IsCauchy (W : ℕ → Graphon α μ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m n, m ≥ N → n ≥ N → cutDistance (W m) (W n) < ε

/-- One-sided ε-witness for cutDistance: for any ε > 0, there exists a single
measure-preserving map σ such that `cutNormDiff(pullback U σ, W) < cutDistance U W + ε`.

This absorbs the two-sided (φ,ψ) witnesses from `cutDistance_lt_add_of_pos` into a
single map σ = φ ∘ χ₂ ∘ χ₁⁻¹, using Rokhlin alignment to collapse the ψ side.

**Proof**: Get near-optimal (φ, ψ) from `cutDistance_lt_add_of_pos`, align `id` with `ψ`
via Rokhlin to get (χ₁, χ₂) with `χ₁ =ᵃᵉ ψ ∘ χ₂`. Set σ = φ ∘ χ₂ ∘ χ₁⁻¹. Then:
  cutNormDiff(pb(U,σ), W) = cutNormDiff(pb(U, φ∘χ₂), pb(W, χ₁))  [χ₁⁻¹ invariance]
    = cutNormDiff(pb(U, φ∘χ₂), pb(W, ψ∘χ₂))  [AE-congruence from alignment]
    = cutNormDiff(pb(U, φ), pb(W, ψ))  [χ₂ invariance]
    < cutDistance U W + ε.

**Depends on**: `MeasurePreserving.exists_common_extension` (Rokhlin axiom). -/
private theorem cutDistance_lt_add_of_pos_onesided
    (U W : Graphon α μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (σ : α → α) (hσ : MeasurePreserving σ μ μ),
      cutNormDiff (pullback U σ hσ) W < cutDistance U W + ε := by
  -- Get near-optimal two-sided maps
  obtain ⟨φ, ψ, hφ, hψ, h_opt⟩ := cutDistance_lt_add_of_pos U W hε
  -- Align id with ψ via Rokhlin: get χ₁, χ₂ with id ∘ χ₁ =ᵐ ψ ∘ χ₂
  obtain ⟨χ₁, χ₂, hχ₁, hχ₂, h_align⟩ :=
    MeasurePreserving.exists_common_extension_maps id (MeasurePreserving.id μ) ψ hψ
  -- Simplify id ∘ χ₁ to χ₁
  have h_align' : (↑χ₁ : α → α) =ᶠ[ae μ] ψ ∘ ↑χ₂ := by rwa [Function.id_comp] at h_align
  -- Set up helper measure-preserving compositions
  have hχ₁_symm : MeasurePreserving (↑χ₁.symm) μ μ := hχ₁.symm
  have hφχ₂ : MeasurePreserving (φ ∘ ↑χ₂) μ μ := hφ.comp hχ₂
  have hψχ₂ : MeasurePreserving (ψ ∘ ↑χ₂) μ μ := hψ.comp hχ₂
  -- Witness: σ = (φ ∘ χ₂) ∘ χ₁⁻¹, parenthesized for pullback_pullback
  refine ⟨(φ ∘ ↑χ₂) ∘ ↑χ₁.symm, hφχ₂.comp hχ₁_symm, ?_⟩
  -- AE-congruence: pb(W, χ₁) = pb(W, ψ ∘ χ₂)  [from χ₁ =ᵐ ψ ∘ χ₂]
  have h_align_pb : pullback W (↑χ₁) hχ₁ = pullback W (ψ ∘ ↑χ₂) hψχ₂ := by
    apply Graphon.ext; apply SymmKernel.ext; apply AEEqFun.ext
    have h1 := pullback_ae W (↑χ₁) hχ₁
    have h2 := pullback_ae W (ψ ∘ ↑χ₂) hψχ₂
    have h_prod_ae : ∀ᵐ p ∂(μ.prod μ),
        ((χ₁ : α → α) p.1, (χ₁ : α → α) p.2) = (ψ (χ₂ p.1), ψ (χ₂ p.2)) := by
      have h_fst : ∀ᵐ p ∂(μ.prod μ), (χ₁ : α → α) p.1 = ψ (χ₂ p.1) :=
        Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst h_align'
      have h_snd : ∀ᵐ p ∂(μ.prod μ), (χ₁ : α → α) p.2 = ψ (χ₂ p.2) :=
        Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd h_align'
      filter_upwards [h_fst, h_snd] with p hp1 hp2
      exact Prod.ext hp1 hp2
    filter_upwards [h1, h2, h_prod_ae] with p hp1 hp2 hp_eq
    rw [hp1, hp2]; simp only [Function.comp_apply] at hp_eq ⊢; rw [hp_eq]
  -- χ₂ invariance: cutNormDiff(pb(U, φ∘χ₂), pb(W, ψ∘χ₂)) = cutNormDiff(pb(U,φ), pb(W,ψ))
  have h_inv_χ₂ : cutNormDiff (pullback U (φ ∘ ↑χ₂) hφχ₂)
      (pullback W (ψ ∘ ↑χ₂) hψχ₂) =
      cutNormDiff (pullback U φ hφ) (pullback W ψ hψ) := by
    rw [show pullback U (φ ∘ ↑χ₂) hφχ₂ =
          pullback (pullback U φ hφ) χ₂ hχ₂ from
          (pullback_pullback U φ hφ (↑χ₂) hχ₂).symm,
        show pullback W (ψ ∘ ↑χ₂) hψχ₂ =
          pullback (pullback W ψ hψ) χ₂ hχ₂ from
          (pullback_pullback W ψ hψ (↑χ₂) hχ₂).symm]
    exact cutNormDiff_pullback_measurableEquiv _ _ χ₂ hχ₂
  -- χ₁⁻¹ invariance setup: pb(pb(W, χ₁), χ₁⁻¹) = W
  have h_pb_W_cancel : pullback (pullback W (↑χ₁) hχ₁) (↑χ₁.symm) hχ₁_symm = W := by
    rw [pullback_pullback]; simp only [show (↑χ₁ : α → α) ∘ ↑χ₁.symm = id from
      funext χ₁.apply_symm_apply, pullback_id]
  -- Main calc chain
  calc cutNormDiff (pullback U ((φ ∘ ↑χ₂) ∘ ↑χ₁.symm) (hφχ₂.comp hχ₁_symm)) W
      = cutNormDiff (pullback (pullback U (φ ∘ ↑χ₂) hφχ₂) (↑χ₁.symm) hχ₁_symm)
          (pullback (pullback W (↑χ₁) hχ₁) (↑χ₁.symm) hχ₁_symm) := by
        rw [(pullback_pullback U (φ ∘ ↑χ₂) hφχ₂ (↑χ₁.symm) hχ₁_symm).symm]
        congr 1; exact h_pb_W_cancel.symm
    _ = cutNormDiff (pullback U (φ ∘ ↑χ₂) hφχ₂) (pullback W (↑χ₁) hχ₁) :=
        cutNormDiff_pullback_measurableEquiv _ _ χ₁.symm hχ₁_symm
    _ = cutNormDiff (pullback U (φ ∘ ↑χ₂) hφχ₂) (pullback W (ψ ∘ ↑χ₂) hψχ₂) := by
        rw [h_align_pb]
    _ = cutNormDiff (pullback U φ hφ) (pullback W ψ hψ) := h_inv_χ₂
    _ < cutDistance U W + ε := h_opt

/-- MeasurableEquiv variant of `cutDistance_lt_add_of_pos_onesided`: for any ε > 0,
there exists a MeasurableEquiv σ with `cutNormDiff(pullback U σ, W) < cutDistance U W + ε`.

**Proof**: Get MP map f from onesided, upgrade to MeasurableEquiv via Rokhlin
(`exists_common_extension_maps f id`), transfer bound via `pullback_congr_ae`. -/
private theorem cutDistance_lt_add_of_pos_equiv
    (U W : Graphon α μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (σ : α ≃ᵐ α) (hσ : MeasurePreserving σ μ μ),
      cutNormDiff (pullback U σ hσ) W < cutDistance U W + ε := by
  -- Get one-sided MP map witness
  obtain ⟨f, hf, h_bound⟩ := cutDistance_lt_add_of_pos_onesided U W hε
  -- Upgrade to MeasurableEquiv: align f with id via Rokhlin
  obtain ⟨χ₁, χ₂, hχ₁, hχ₂, h_align⟩ :=
    MeasurePreserving.exists_common_extension_maps f hf id (MeasurePreserving.id μ)
  -- h_align : f ∘ χ₁ =ᵐ[μ] id ∘ χ₂ = χ₂
  -- So f =ᶠ[ae μ] χ₂ ∘ χ₁⁻¹ = (χ₁.symm.trans χ₂)
  have h_eq : f =ᶠ[ae μ] ↑(χ₁.symm.trans χ₂) := by
    have h_simp : id ∘ ↑χ₂ = ↑χ₂ := Function.id_comp _
    rw [h_simp] at h_align
    -- f ∘ χ₁ =ᵐ χ₂ → f =ᵐ χ₂ ∘ χ₁⁻¹ = χ₁.symm.trans χ₂
    have := hχ₁.symm.quasiMeasurePreserving.ae h_align
    filter_upwards [this] with x hx
    simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply] at hx
    simp only [MeasurableEquiv.coe_trans, Function.comp_apply]
    exact hx
  -- Transfer bound via pullback_congr_ae
  have hσ : MeasurePreserving (↑(χ₁.symm.trans χ₂)) μ μ := by
    show MeasurePreserving (↑χ₂ ∘ ↑χ₁.symm) μ μ
    exact hχ₂.comp hχ₁.symm
  refine ⟨χ₁.symm.trans χ₂, hσ, ?_⟩
  rw [← pullback_congr_ae U hf hσ h_eq]
  exact h_bound

/-- Telescoping realignment: given rapidly decaying consecutive cutDistances,
construct MeasurableEquiv maps `f_k` such that consecutive `cutNormDiff` after
pullback is summable.

**Proof**: At each step k, get MeasurableEquiv σ_k from `cutDistance_lt_add_of_pos_equiv`
with error 1/3^k. Build f_k by `Nat.rec`: f_0 = refl, f_{k+1} = f_k.trans σ_k.
The telescoping bound uses `pullback_pullback` + `cutNormDiff_pullback_measurableEquiv`
to cancel f_k, yielding cutNormDiff ≤ 1/2^k + 2/3^k which is summable. -/
private theorem exists_cutNormDiff_cauchy_realignment
    (V : ℕ → Graphon α μ)
    (h_rapid : ∀ k, cutDistance (V (k + 1)) (V k) ≤ 1 / 2 ^ k + 1 / 3 ^ k) :
    ∃ (f : ℕ → α ≃ᵐ α) (hf : ∀ k, MeasurePreserving (f k) μ μ)
      (δ : ℕ → ℝ) (_ : Summable δ) (_ : ∀ k, 0 ≤ δ k),
      ∀ k, cutNormDiff (pullback (V (k + 1)) (f (k + 1)) (hf (k + 1)))
                        (pullback (V k) (f k) (hf k)) ≤ δ k := by
  -- For each k, get MeasurableEquiv σ_k witnessing cutDistance bound
  have h_witness : ∀ k, ∃ (σ : α ≃ᵐ α) (hσ : MeasurePreserving σ μ μ),
      cutNormDiff (pullback (V (k + 1)) σ hσ) (V k) < cutDistance (V (k + 1)) (V k) + 1 / 3 ^ k := by
    intro k
    exact cutDistance_lt_add_of_pos_equiv (V (k + 1)) (V k) (by positivity)
  choose σ hσ h_σ_bound using h_witness
  -- Build f by recursion: f 0 = refl, f (k+1) = f k . trans (σ k)
  -- Note: (e₁.trans e₂) x = e₂ (e₁ x), so ⇑(f_k.trans σ_k) = σ_k ∘ f_k
  -- And pullback_pullback: pb(pb(W, σ_k), f_k) = pb(W, σ_k ∘ f_k) = pb(W, f_{k+1})
  let f : ℕ → α ≃ᵐ α := fun k => Nat.rec (MeasurableEquiv.refl α) (fun k prev => prev.trans (σ k)) k
  have hf : ∀ k, MeasurePreserving (f k) μ μ := by
    intro k; induction k with
    | zero => exact MeasurePreserving.id μ
    | succ k ih =>
      -- f (k+1) = (f k).trans (σ k), so ⇑(f (k+1)) = (σ k) ∘ (f k)
      show MeasurePreserving (↑(σ k) ∘ ↑(f k)) μ μ
      exact (hσ k).comp ih
  -- Set δ k = 1/2^k + 2/3^k
  let δ : ℕ → ℝ := fun k => 1 / 2 ^ k + 2 / 3 ^ k
  have hδ_pos : ∀ k, 0 ≤ δ k := fun k => by positivity
  have hδ_sum : Summable δ := by
    apply Summable.add
    · have : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ k) :=
        summable_geometric_of_lt_one (by positivity) (by norm_num)
      convert this using 1; ext k; rw [one_div, one_div, inv_pow]
    · have h : Summable (fun k : ℕ => ((1 : ℝ) / 3) ^ k) :=
        summable_geometric_of_lt_one (by positivity) (by norm_num)
      have h2 := h.mul_left 2
      simp only [one_div] at h2
      convert h2 using 1; ext k; rw [inv_pow]; ring
  refine ⟨f, hf, δ, hδ_sum, hδ_pos, fun k => ?_⟩
  -- Key calc: f (k+1) = f k . trans (σ k), so ⇑(f (k+1)) = σ_k ∘ f_k
  -- pb(V(k+1), f_{k+1}) = pb(V(k+1), σ_k ∘ f_k) = pb(pb(V(k+1), σ_k), f_k)
  -- cutNormDiff(pb(V(k+1), f_{k+1}), pb(V_k, f_k))
  --   = cutNormDiff(pb(pb(V(k+1), σ_k), f_k), pb(V_k, f_k))
  --   = cutNormDiff(pb(V(k+1), σ_k), V_k)    [by cutNormDiff_pullback_measurableEquiv]
  --   < cutDistance(V(k+1), V_k) + 1/3^k
  --   ≤ 1/2^k + 1/3^k + 1/3^k = 1/2^k + 2/3^k = δ k
  -- f (k+1) = (f k).trans (σ k), so pb(V(k+1), f_{k+1}) = pb(pb(V(k+1), σ_k), f_k)
  have h_comp : pullback (V (k + 1)) (↑(σ k) ∘ ↑(f k)) ((hσ k).comp (hf k)) =
      pullback (pullback (V (k + 1)) (σ k) (hσ k)) (↑(f k)) (hf k) :=
    (pullback_pullback (V (k + 1)) (↑(σ k)) (hσ k) (↑(f k)) (hf k)).symm
  -- The goal uses f (k+1) which is definitionally (σ k) ∘ (f k)
  show cutNormDiff (pullback (V (k + 1)) (↑(σ k) ∘ ↑(f k)) ((hσ k).comp (hf k)))
      (pullback (V k) (↑(f k)) (hf k)) ≤ δ k
  calc cutNormDiff (pullback (V (k + 1)) (↑(σ k) ∘ ↑(f k)) ((hσ k).comp (hf k)))
          (pullback (V k) (↑(f k)) (hf k))
      = cutNormDiff (pullback (pullback (V (k + 1)) (σ k) (hσ k)) (↑(f k)) (hf k))
          (pullback (V k) (↑(f k)) (hf k)) := by rw [h_comp]
    _ = cutNormDiff (pullback (V (k + 1)) (σ k) (hσ k)) (V k) :=
        cutNormDiff_pullback_measurableEquiv _ _ (f k) (hf k)
    _ ≤ cutDistance (V (k + 1)) (V k) + 1 / 3 ^ k := le_of_lt (h_σ_bound k)
    _ ≤ (1 / 2 ^ k + 1 / 3 ^ k) + 1 / 3 ^ k := by linarith [h_rapid k]
    _ = δ k := by ring

omit [StandardBorelSpace α] in
set_option maxHeartbeats 800000 in
/-- **Helper 1**: Summable consecutive bounds imply Cauchy in cutNormDiff.

Telescoping + triangle inequality: for m ≥ n, `cutNormDiff(A m, A n) ≤ ∑ δ` over
the intervening indices, bounded by the tail sum which vanishes. -/
private lemma cutNormDiff_cauchy_of_summable
    (A : ℕ → Graphon α μ) (δ : ℕ → ℝ)
    (hδ_pos : ∀ k, 0 ≤ δ k) (hδ_sum : Summable δ)
    (h_bound : ∀ k, cutNormDiff (A (k + 1)) (A k) ≤ δ k) :
    ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n → cutNormDiff (A m) (A n) ≤ ε := by
  -- Step 1: Telescoping for n + d
  have h_telescope : ∀ n d, cutNormDiff (A (n + d)) (A n) ≤ ∑ k ∈ Finset.range d, δ (n + k) := by
    intro n d
    induction d with
    | zero => simp [cutNormDiff_self]
    | succ d ih =>
      have h1 : n + (d + 1) = (n + d) + 1 := by omega
      calc cutNormDiff (A (n + (d + 1))) (A n)
          = cutNormDiff (A ((n + d) + 1)) (A n) := by rw [h1]
        _ ≤ cutNormDiff (A ((n + d) + 1)) (A (n + d)) + cutNormDiff (A (n + d)) (A n) :=
            cutNormDiff_triangle _ _ _
        _ ≤ δ (n + d) + ∑ k ∈ Finset.range d, δ (n + k) := add_le_add (h_bound _) ih
        _ = ∑ k ∈ Finset.range d, δ (n + k) + δ (n + d) := by ring
        _ = ∑ k ∈ Finset.range (d + 1), δ (n + k) := (Finset.sum_range_succ _ _).symm
  -- Step 2: Finite sum ≤ tail tsum
  have h_sum_le_tail : ∀ n d,
      ∑ k ∈ Finset.range d, δ (n + k) ≤ ∑' k, δ (n + k) := by
    intro n d
    have hδ_shift : Summable (fun k => δ (n + k)) :=
      hδ_sum.comp_injective (fun _ _ h => by omega)
    exact hδ_shift.sum_le_tsum (Finset.range d) (fun k _ => hδ_pos _)
  -- Step 3: Tail vanishes
  have h_tail : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∑' k, δ (n + k) ≤ ε := by
    intro ε hε
    have h_conv := hδ_sum.hasSum.tendsto_sum_nat
    rw [Metric.tendsto_atTop] at h_conv
    obtain ⟨N, hN⟩ := h_conv ε hε
    refine ⟨N, fun n hn => ?_⟩
    have h_shift : ∑' k, δ (n + k) = ∑' k, δ k - ∑ k ∈ Finset.range n, δ k := by
      have h1 := ((summable_nat_add_iff n).mpr hδ_sum).hasSum
      rw [hasSum_nat_add_iff n] at h1
      have := h1.tsum_eq; simp only [add_comm] at this; linarith
    rw [h_shift]
    have h_le : ∑ k ∈ Finset.range n, δ k ≤ ∑' k, δ k :=
      hδ_sum.sum_le_tsum _ (fun k _ => hδ_pos k)
    have h_dist := hN n hn; rw [Real.dist_eq] at h_dist
    have h_nonpos : ∑ k ∈ Finset.range n, δ k - ∑' k, δ k ≤ 0 := by linarith
    rw [abs_of_nonpos h_nonpos] at h_dist; linarith
  -- Step 4: Combine
  intro ε hε
  obtain ⟨N, hN⟩ := h_tail ε hε
  refine ⟨N, fun m n hm hn => ?_⟩
  rcases le_total m n with hmn | hnm
  · rw [cutNormDiff_symm]
    have heq : n = m + (n - m) := by omega
    calc cutNormDiff (A n) (A m)
        = cutNormDiff (A (m + (n - m))) (A m) := by rw [← heq]
      _ ≤ ∑ k ∈ Finset.range (n - m), δ (m + k) := h_telescope m (n - m)
      _ ≤ ∑' k, δ (m + k) := h_sum_le_tail m (n - m)
      _ ≤ ε := hN m hm
  · have heq : m = n + (m - n) := by omega
    calc cutNormDiff (A m) (A n)
        = cutNormDiff (A (n + (m - n))) (A n) := by rw [← heq]
      _ ≤ ∑ k ∈ Finset.range (m - n), δ (n + k) := h_telescope n (m - n)
      _ ≤ ∑' k, δ (n + k) := h_sum_le_tail n (m - n)
      _ ≤ ε := hN n hn

open MeasurableSpace in
/-- **Helper 2a**: Diagonal extraction — extract a subsequence where all rectangle
averages on all countable partition depths converge simultaneously.

Uses Tychonoff's theorem: the product space `[0,1]^I` (where `I` indexes all pairs
of partition cells at all depths) is compact and first-countable, so every sequence
has a convergent subsequence. Projecting gives coordinate-wise convergence. -/
private theorem exists_subseq_all_rectAvg_converge
    (A : ℕ → Graphon α μ) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ (k : ℕ) (S : Set α) (_ : S ∈ countablePartition α k)
        (T : Set α) (_ : T ∈ countablePartition α k),
      ∃ (c : ℝ), c ∈ Set.Icc 0 1 ∧
        Tendsto (fun n => rectAverage (A (φ n)) S T) atTop (nhds c) := by
  haveI (k : ℕ) : Finite ↥(countablePartition α k) := finite_countablePartition α k
  let I := Σ k : ℕ, ↥(countablePartition α k) × ↥(countablePartition α k)
  let x : ℕ → (I → Set.Icc (0:ℝ) 1) := fun n i =>
    ⟨rectAverage (A n) ↑i.2.1 ↑i.2.2,
     rectAverage_mem_Icc _ _ _
       (measurableSet_countablePartition _ i.2.1.2)
       (measurableSet_countablePartition _ i.2.2.2)⟩
  obtain ⟨L, φ, hφ, hconv⟩ := CompactSpace.tendsto_subseq x
  refine ⟨φ, hφ, fun k S hS T hT => ?_⟩
  have h_coord := (tendsto_pi_nhds.mp hconv) (⟨k, ⟨S, hS⟩, ⟨T, hT⟩⟩ : I)
  exact ⟨↑(L ⟨k, ⟨S, hS⟩, ⟨T, hT⟩⟩), (L ⟨k, ⟨S, hS⟩, ⟨T, hT⟩⟩).2,
    (continuous_subtype_val.tendsto _).comp h_coord⟩

omit [StandardBorelSpace α] in
/-- **Helper 1**: Rectangle integral differences telescope and are bounded by tail sums.

For `n ≤ m`, `|rectIntegralDiff(A n, A m, S, T)| ≤ ∑' k, δ(n + k)` via:
- Triangle: `|rect(A n, A m)| ≤ Σ_{k=n}^{m-1} |rect(A k, A(k+1))|`
- Each `|rect(A k, A(k+1))| ≤ cutNormDiff(A(k+1), A k) ≤ δ k`
- Finite sum ≤ tail tsum -/
private lemma rectIntegralDiff_le_tail_tsum
    (A : ℕ → Graphon α μ) (δ : ℕ → ℝ)
    (hδ_pos : ∀ k, 0 ≤ δ k) (hδ_sum : Summable δ)
    (h_bound : ∀ k, cutNormDiff (A (k + 1)) (A k) ≤ δ k)
    {n m : ℕ} (hnm : n ≤ m) {S T : Set α} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    |rectIntegralDiff (A n) (A m) S T| ≤ ∑' k, δ (n + k) := by
  -- Telescope: bound by finite sum Σ_{j ∈ range(m-n)} δ(n+j)
  have h_fin : |rectIntegralDiff (A n) (A m) S T| ≤
      ∑ j ∈ Finset.range (m - n), δ (n + j) := by
    induction m with
    | zero =>
      simp [Nat.le_zero.mp hnm, rectIntegralDiff]
    | succ m ih =>
      by_cases h : n ≤ m
      · have h_tri := rectIntegralDiff_triangle (A n) (A m) (A (m + 1)) S T
        have h_step : |rectIntegralDiff (A m) (A (m + 1)) S T| ≤ δ m := by
          calc |rectIntegralDiff (A m) (A (m + 1)) S T|
              ≤ cutNormDiff (A m) (A (m + 1)) := abs_rectIntegralDiff_le _ _ hS hT
            _ = cutNormDiff (A (m + 1)) (A m) := cutNormDiff_symm _ _
            _ ≤ δ m := h_bound m
        have h_rng : m + 1 - n = (m - n) + 1 := by omega
        rw [h_rng, Finset.sum_range_succ]
        have h_idx : n + (m - n) = m := by omega
        rw [h_idx]
        calc |rectIntegralDiff (A n) (A (m + 1)) S T|
            ≤ |rectIntegralDiff (A n) (A m) S T| +
              |rectIntegralDiff (A m) (A (m + 1)) S T| := h_tri
          _ ≤ ∑ j ∈ Finset.range (m - n), δ (n + j) + δ m := add_le_add (ih h) h_step
      · push_neg at h
        have heq : n = m + 1 := by omega
        subst heq
        simp only [Nat.sub_self, Finset.range_zero, Finset.sum_empty, rectIntegralDiff, sub_self,
          integral_zero, abs_zero, le_refl]
  -- Finite sum ≤ tail tsum
  calc |rectIntegralDiff (A n) (A m) S T|
      ≤ ∑ j ∈ Finset.range (m - n), δ (n + j) := h_fin
    _ ≤ ∑' k, δ (n + k) := by
        apply Summable.sum_le_tsum
        · intro j _; exact hδ_pos (n + j)
        · exact hδ_sum.comp_injective (fun _ _ h => by omega)

omit [StandardBorelSpace α] in
/-- Setwise integral convergence for all measurable sets via π-λ.

Given summable consecutive cutNormDiff bounds, the sequence `∫_E A(n) d(μ²)` converges
for every measurable set E in the product, not just rectangles. The proof uses
`MeasurableSpace.induction_on_inter` on the product π-system of measurable rectangles:
- **Rectangles**: convergence from `cauchySeq_of_dist_le_of_summable` + cutNormDiff bounds
- **Complement**: `∫_{Eᶜ} A(n) = ∫ A(n) - ∫_E A(n)` (both converge)
- **Countable disjoint union**: `∫_{⋃ f_i} A(n) = ∑' ∫_{f_i} A(n)` and
  `tendsto_tsum_of_dominated_convergence` with bound `(μ²)(f_i).toReal` -/
private theorem setIntegral_tendsto_of_summable_cutNormDiff
    (A : ℕ → Graphon α μ) (δ : ℕ → ℝ)
    (hδ_pos : ∀ k, 0 ≤ δ k) (hδ_sum : Summable δ)
    (h_bound : ∀ k, cutNormDiff (A (k + 1)) (A k) ≤ δ k) :
    ∀ (E : Set (α × α)), MeasurableSet E →
      ∃ L, Tendsto (fun n => ∫ p in E, (A n).toAEEqFun p ∂(μ.prod μ)) atTop (nhds L) ∧
        0 ≤ L ∧ L ≤ (μ.prod μ E).toReal := by
  -- Each A(n) is integrable and [0,1]-valued a.e.
  have hA_int : ∀ n, Integrable ((A n).toAEEqFun) (μ.prod μ) :=
    fun n => SymmKernel.graphon_integrable (A n)
  have hA_le1 : ∀ n, ∀ᵐ p ∂(μ.prod μ), (A n).toAEEqFun p ≤ 1 :=
    fun n => (A n).ae_le_one
  -- Set integral bounds: 0 ≤ ∫_E A(n) ≤ (μ²)(E).toReal
  have h_int_nn : ∀ n E, 0 ≤ ∫ p in E, (A n).toAEEqFun p ∂(μ.prod μ) :=
    fun n E => setIntegral_nonneg_of_ae (A n).ae_nonneg
  have h_int_le : ∀ n (E : Set (α × α)), MeasurableSet E →
      ∫ p in E, (A n).toAEEqFun p ∂(μ.prod μ) ≤ (μ.prod μ E).toReal := by
    intro n E _
    calc ∫ p in E, (A n).toAEEqFun p ∂μ.prod μ
        ≤ ∫ _ in E, (1 : ℝ) ∂μ.prod μ := by
          apply setIntegral_mono_ae_restrict (hA_int n).integrableOn (integrable_const _)
          exact ae_restrict_of_ae (hA_le1 n)
      _ = (μ.prod μ E).toReal := by
          rw [setIntegral_const, smul_eq_mul, mul_one]; rfl
  -- Set integral norm bound
  have h_norm_le : ∀ n (E : Set (α × α)), MeasurableSet E →
      ‖∫ p in E, (A n).toAEEqFun p ∂(μ.prod μ)‖ ≤ (μ.prod μ E).toReal := by
    intro n E hE
    rw [Real.norm_eq_abs, abs_of_nonneg (h_int_nn n E)]
    exact h_int_le n E hE
  -- Consecutive rect distance bound: dist(∫_{S×T} A(n), ∫_{S×T} A(n+1)) ≤ δ(n)
  have h_rect_dist : ∀ n (S T : Set α), MeasurableSet S → MeasurableSet T →
      dist (∫ p in S ×ˢ T, (A n).toAEEqFun p ∂(μ.prod μ))
           (∫ p in S ×ˢ T, (A (n + 1)).toAEEqFun p ∂(μ.prod μ)) ≤ δ n := by
    intro n S T hS hT
    rw [Real.dist_eq]
    have hsub : ∫ p in S ×ˢ T, (A n).toAEEqFun p ∂μ.prod μ -
        ∫ p in S ×ˢ T, (A (n + 1)).toAEEqFun p ∂μ.prod μ =
        rectIntegralDiff (A n) (A (n + 1)) S T := by
      simp only [rectIntegralDiff]
      rw [integral_sub (hA_int n).integrableOn (hA_int (n + 1)).integrableOn]
    rw [hsub]
    calc |rectIntegralDiff (A n) (A (n + 1)) S T|
        ≤ cutNormDiff (A n) (A (n + 1)) := abs_rectIntegralDiff_le _ _ hS hT
      _ = cutNormDiff (A (n + 1)) (A n) := cutNormDiff_symm _ _
      _ ≤ δ n := h_bound n
  -- ===== Pi-lambda induction =====
  refine MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_
  -- Case 1: Empty
  · exact ⟨0, by simp, le_refl _, by simp⟩
  -- Case 2: Basic (rectangles in the generating pi-system)
  · rintro _ ⟨S, hS, T, hT, rfl⟩
    -- The sequence is Cauchy: dist(f n, f (n+1)) ≤ δ n
    have h_cauchy : CauchySeq (fun n => ∫ p in S ×ˢ T, (A n).toAEEqFun p ∂(μ.prod μ)) :=
      cauchySeq_of_dist_le_of_summable δ (fun n => h_rect_dist n S T hS hT) hδ_sum
    -- Converges by completeness
    refine ⟨_, h_cauchy.tendsto_limUnder, ?_, ?_⟩
    · exact ge_of_tendsto' h_cauchy.tendsto_limUnder (fun n => h_int_nn n (S ×ˢ T))
    · exact le_of_tendsto' h_cauchy.tendsto_limUnder (fun n => h_int_le n (S ×ˢ T) (hS.prod hT))
  -- Case 3: Complement
  · intro E hE ⟨L_E, hL_E, _, _⟩
    -- First show ∫ A(n) converges (univ = univ × univ is a rectangle)
    have h_univ_cauchy : CauchySeq (fun n => ∫ p, (A n).toAEEqFun p ∂(μ.prod μ)) := by
      apply cauchySeq_of_dist_le_of_summable δ _ hδ_sum
      intro n
      have := h_rect_dist n univ univ MeasurableSet.univ MeasurableSet.univ
      simp only [univ_prod_univ, setIntegral_univ] at this
      exact this
    have hL_all := h_univ_cauchy.tendsto_limUnder
    -- ∫_{Eᶜ} A(n) = ∫ A(n) - ∫_E A(n)
    have h_compl : ∀ n, ∫ p in Eᶜ, (A n).toAEEqFun p ∂(μ.prod μ) =
        ∫ p, (A n).toAEEqFun p ∂(μ.prod μ) -
        ∫ p in E, (A n).toAEEqFun p ∂(μ.prod μ) := by
      intro n; have := integral_add_compl hE (hA_int n); linarith
    set L_all := limUnder atTop (fun n => ∫ p, (A n).toAEEqFun p ∂(μ.prod μ))
    refine ⟨L_all - L_E, ?_, ?_, ?_⟩
    · exact (tendsto_congr h_compl).mpr (hL_all.sub hL_E)
    · exact ge_of_tendsto' ((tendsto_congr h_compl).mpr (hL_all.sub hL_E))
        (fun n => h_int_nn n Eᶜ)
    · exact le_of_tendsto' ((tendsto_congr h_compl).mpr (hL_all.sub hL_E))
        (fun n => h_int_le n Eᶜ hE.compl)
  -- Case 4: Countable disjoint union
  · intro f h_disj hf_meas ih
    choose L_i hL_i hL_i_nn hL_i_le using fun i => ih i
    -- Summability of the bound (μ²)(f i).toReal
    have h_summable_bound : Summable (fun i => (μ.prod μ (f i)).toReal) := by
      have h_ne_top : ∀ i, μ.prod μ (f i) ≠ ⊤ :=
        fun i => ne_top_of_le_ne_top (measure_ne_top _ _) le_rfl
      have h_tsum_ne_top : ∑' i, μ.prod μ (f i) ≠ ⊤ := by
        rw [show ∑' i, μ.prod μ (f i) = μ.prod μ (⋃ i, f i) from
          (measure_iUnion h_disj (fun i => hf_meas i)).symm]
        exact ne_top_of_le_ne_top (measure_ne_top _ _) le_rfl
      exact ENNReal.summable_toReal h_tsum_ne_top
    have h_summable_L : Summable L_i :=
      Summable.of_nonneg_of_le hL_i_nn hL_i_le h_summable_bound
    -- ∫_{⋃ f_i} A(n) = ∑' ∫_{f_i} A(n)
    have h_sum : ∀ n, ∫ p in ⋃ i, f i, (A n).toAEEqFun p ∂(μ.prod μ) =
        ∑' i, ∫ p in f i, (A n).toAEEqFun p ∂(μ.prod μ) :=
      fun n => integral_iUnion (fun i => hf_meas i) h_disj (hA_int n).integrableOn
    -- Dominated convergence for tsum
    have h_tsum_tendsto : Tendsto (fun n => ∑' i, ∫ p in f i, (A n).toAEEqFun p ∂(μ.prod μ))
        atTop (nhds (∑' i, L_i i)) := by
      exact tendsto_tsum_of_dominated_convergence h_summable_bound
        (fun i => hL_i i) (Filter.Eventually.of_forall
          (fun n i => h_norm_le n (f i) (hf_meas i)))
    refine ⟨∑' i, L_i i, ?_, ?_, ?_⟩
    · exact (tendsto_congr h_sum).mpr h_tsum_tendsto
    · have : 0 ≤ ∑' i, L_i i := by
        simpa using h_summable_L.sum_le_tsum (∅ : Finset ℕ) (fun k _ => hL_i_nn k)
      exact this
    · have h_ne_top : ∀ i, μ.prod μ (f i) ≠ ⊤ :=
        fun i => ne_top_of_le_ne_top (measure_ne_top _ _) le_rfl
      calc ∑' i, L_i i
          ≤ ∑' i, (μ.prod μ (f i)).toReal :=
            h_summable_L.tsum_le_tsum (fun i => hL_i_le i) h_summable_bound
        _ = (μ.prod μ (⋃ i, f i)).toReal := by
            rw [measure_iUnion h_disj (fun i => hf_meas i)]
            exact (ENNReal.tsum_toReal_eq h_ne_top).symm

omit [StandardBorelSpace α] in
/-- **Helper 2**: Construct a symmetric finite measure from setwise limits of `∫_E A(n)`,
with tight rectangle integral bounds.

For each measurable rectangle S × T, the sequence `∫_{S×T} A(n)` is Cauchy with error
`≤ ∑' k, δ(n+k)` by `rectIntegralDiff_le_tail_tsum`. The limits define a set function
on rectangles, extended to a measure via π-λ. The measure is ≤ μ×μ (since A(n) ∈ [0,1])
and symmetric (from symmetry of each A(n)).

**Depends on**: `setIntegral_tendsto_of_summable_cutNormDiff` (π-λ convergence). -/
private theorem exists_limit_measure_of_summable
    (A : ℕ → Graphon α μ) (δ : ℕ → ℝ)
    (hδ_pos : ∀ k, 0 ≤ δ k) (hδ_sum : Summable δ)
    (h_bound : ∀ k, cutNormDiff (A (k + 1)) (A k) ≤ δ k) :
    ∃ ν : Measure (α × α), ν ≤ μ.prod μ ∧
      (∀ (S T : Set α), MeasurableSet S → MeasurableSet T → ν (S ×ˢ T) = ν (T ×ˢ S)) ∧
      (∀ (S T : Set α), MeasurableSet S → MeasurableSet T →
        ∀ n, |(∫ p in S ×ˢ T, (A n).toAEEqFun p ∂(μ.prod μ)) -
              (ν (S ×ˢ T)).toReal| ≤ ∑' k, δ (n + k)) := by
  -- Step 1: Get convergence for all measurable sets via π-λ helper
  have h_conv := setIntegral_tendsto_of_summable_cutNormDiff A δ hδ_pos hδ_sum h_bound
  -- Step 2: Choose limit values
  choose c hc hc_nn hc_le using fun E hE => h_conv E hE
  -- Auxiliary: integrability and bounds (reused below)
  have hA_int : ∀ n, Integrable ((A n).toAEEqFun) (μ.prod μ) :=
    fun n => SymmKernel.graphon_integrable (A n)
  have h_norm_le : ∀ n (E : Set (α × α)), MeasurableSet E →
      ‖∫ p in E, (A n).toAEEqFun p ∂(μ.prod μ)‖ ≤ (μ.prod μ E).toReal := by
    intro n E _
    rw [Real.norm_eq_abs, abs_of_nonneg (setIntegral_nonneg_of_ae (A n).ae_nonneg)]
    calc ∫ p in E, (A n).toAEEqFun p ∂μ.prod μ
        ≤ ∫ _ in E, (1 : ℝ) ∂μ.prod μ := by
          apply setIntegral_mono_ae_restrict (hA_int n).integrableOn (integrable_const _)
          exact ae_restrict_of_ae (A n).ae_le_one
      _ = (μ.prod μ E).toReal := by
          rw [setIntegral_const, smul_eq_mul, mul_one]; rfl
  -- Step 3: c(∅, _) = 0
  have hc_empty : c ∅ MeasurableSet.empty = 0 := by
    have : Tendsto (fun n => ∫ p in (∅ : Set (α × α)), (A n).toAEEqFun p ∂(μ.prod μ))
        atTop (nhds (c ∅ MeasurableSet.empty)) := hc ∅ MeasurableSet.empty
    simp only [setIntegral_empty] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  -- Step 4: Sigma-additivity for c
  have hc_additive : ∀ ⦃f : ℕ → Set (α × α)⦄ (hf : ∀ i, MeasurableSet (f i)),
      Pairwise (Function.onFun Disjoint f) →
      c (⋃ i, f i) (MeasurableSet.iUnion hf) = ∑' i, c (f i) (hf i) := by
    intro f hf h_disj
    -- The sequence for ⋃ f_i converges to c(⋃ f_i)
    have h_union_tendsto := hc (⋃ i, f i) (MeasurableSet.iUnion hf)
    -- Each ∫_{f_i} A(n) → c(f_i)
    have h_i_tendsto : ∀ i, Tendsto (fun n => ∫ p in f i, (A n).toAEEqFun p ∂(μ.prod μ))
        atTop (nhds (c (f i) (hf i))) := fun i => hc (f i) (hf i)
    -- Summability of bound
    have h_ne_top : ∀ i, μ.prod μ (f i) ≠ ⊤ :=
      fun i => ne_top_of_le_ne_top (measure_ne_top _ _) le_rfl
    have h_summable_bound : Summable (fun i => (μ.prod μ (f i)).toReal) := by
      have : ∑' i, μ.prod μ (f i) ≠ ⊤ := by
        rw [show ∑' i, μ.prod μ (f i) = μ.prod μ (⋃ i, f i) from
          (measure_iUnion h_disj hf).symm]
        exact ne_top_of_le_ne_top (measure_ne_top _ _) le_rfl
      exact ENNReal.summable_toReal this
    -- Summability of c(f_i)
    have h_summable_c : Summable (fun i => c (f i) (hf i)) :=
      Summable.of_nonneg_of_le (fun i => hc_nn (f i) (hf i))
        (fun i => hc_le (f i) (hf i)) h_summable_bound
    -- ∫_{⋃ f_i} A(n) = ∑' i, ∫_{f_i} A(n)
    have h_split : ∀ n, ∫ p in ⋃ i, f i, (A n).toAEEqFun p ∂(μ.prod μ) =
        ∑' i, ∫ p in f i, (A n).toAEEqFun p ∂(μ.prod μ) :=
      fun n => integral_iUnion hf h_disj (hA_int n).integrableOn
    -- ∑' → ∑' by Tannery
    have h_tsum_tendsto : Tendsto (fun n => ∑' i, ∫ p in f i, (A n).toAEEqFun p ∂(μ.prod μ))
        atTop (nhds (∑' i, c (f i) (hf i))) :=
      tendsto_tsum_of_dominated_convergence h_summable_bound
        h_i_tendsto (Filter.Eventually.of_forall (fun n i => h_norm_le n (f i) (hf i)))
    -- By uniqueness of limits
    exact tendsto_nhds_unique h_union_tendsto ((tendsto_congr h_split).mpr h_tsum_tendsto)
  -- Step 5: Construct the measure
  set ν := Measure.ofMeasurable (fun s hs => ENNReal.ofReal (c s hs))
    (by simp [hc_empty])
    (by
      intro f hf h_disj
      simp only []
      rw [hc_additive hf h_disj]
      exact ENNReal.ofReal_tsum_of_nonneg (fun i => hc_nn (f i) (hf i))
        (Summable.of_nonneg_of_le (fun i => hc_nn (f i) (hf i))
          (fun i => hc_le (f i) (hf i))
          (ENNReal.summable_toReal (by
            rw [show ∑' i, μ.prod μ (f i) = μ.prod μ (⋃ i, f i) from
              (measure_iUnion h_disj hf).symm]
            exact ne_top_of_le_ne_top (measure_ne_top _ _) le_rfl))))
    with hν_def
  refine ⟨ν, ?_, ?_, ?_⟩
  -- Step 6: ν ≤ μ.prod μ
  · exact Measure.le_iff.mpr fun E hE => by
      rw [hν_def, Measure.ofMeasurable_apply E hE]
      calc ENNReal.ofReal (c E hE)
          ≤ ENNReal.ofReal (μ.prod μ E).toReal :=
            ENNReal.ofReal_le_ofReal (hc_le E hE)
        _ = μ.prod μ E :=
            ENNReal.ofReal_toReal (ne_top_of_le_ne_top (measure_ne_top _ _) le_rfl)
  -- Step 7: Symmetry on rectangles
  · intro S T hS hT
    rw [hν_def, Measure.ofMeasurable_apply _ (hS.prod hT),
        Measure.ofMeasurable_apply _ (hT.prod hS)]
    congr 1
    -- c(S × T) = c(T × S) because the sequences are equal
    have h_seq_eq : ∀ n, ∫ p in S ×ˢ T, (A n).toAEEqFun p ∂(μ.prod μ) =
        ∫ p in T ×ˢ S, (A n).toAEEqFun p ∂(μ.prod μ) :=
      fun n => SymmKernel.rectIntegral_symm (A n).toSymmKernel hS hT
    exact tendsto_nhds_unique (hc (S ×ˢ T) (hS.prod hT))
      ((tendsto_congr h_seq_eq).mpr (hc (T ×ˢ S) (hT.prod hS)))
  -- Step 8: Rate bound on rectangles
  · intro S T hS hT n
    rw [hν_def, Measure.ofMeasurable_apply _ (hS.prod hT)]
    -- ν(S×T).toReal = c(S×T, _) since c ≥ 0
    rw [ENNReal.toReal_ofReal (hc_nn (S ×ˢ T) (hS.prod hT))]
    -- Use dist_le_tsum_of_dist_le_of_tendsto
    -- dist(f n, a) ≤ ∑' m, d(n + m) where d(k) = δ(k) and f(k) = ∫_{S×T} A(k)
    rw [show |_ - _| = dist _ _ from (Real.dist_eq _ _).symm]
    apply dist_le_tsum_of_dist_le_of_tendsto δ _ hδ_sum (hc (S ×ˢ T) (hS.prod hT))
    -- dist(f n, f (n+1)) ≤ δ n
    intro k
    rw [Real.dist_eq]
    have hsub : ∫ p in S ×ˢ T, (A k).toAEEqFun p ∂μ.prod μ -
        ∫ p in S ×ˢ T, (A (k + 1)).toAEEqFun p ∂μ.prod μ =
        rectIntegralDiff (A k) (A (k + 1)) S T := by
      simp only [rectIntegralDiff]
      rw [integral_sub (hA_int k).integrableOn (hA_int (k + 1)).integrableOn]
    rw [hsub]
    calc |rectIntegralDiff (A k) (A (k + 1)) S T|
        ≤ cutNormDiff (A k) (A (k + 1)) := abs_rectIntegralDiff_le _ _ hS hT
      _ = cutNormDiff (A (k + 1)) (A k) := cutNormDiff_symm _ _
      _ ≤ δ k := h_bound k

omit [StandardBorelSpace α] in
/-- **Helper 3**: Extract a graphon from a bounded symmetric measure via Radon-Nikodym.

Given `ν ≤ μ × μ` with symmetric rectangle values, Radon-Nikodym gives density L with:
- `0 ≤ L ≤ 1` a.e. (from `ν ≤ μ × μ`)
- `L(x,y) = L(y,x)` a.e. (from rectangle symmetry + π-λ uniqueness)
- `∫_{S×T} L = ν(S×T).toReal` for all measurable S, T

**Sorry**: Requires Radon-Nikodym derivative extraction (`ν.rnDeriv (μ.prod μ)`),
density bound proof, and symmetry via π-λ uniqueness. -/
private theorem exists_graphon_of_bounded_measure
    (ν : Measure (α × α)) (hν : ν ≤ μ.prod μ)
    (h_symm : ∀ (S T : Set α), MeasurableSet S → MeasurableSet T →
      ν (S ×ˢ T) = ν (T ×ˢ S)) :
    ∃ L : Graphon α μ, ∀ (S T : Set α), MeasurableSet S → MeasurableSet T →
      ∫ p in S ×ˢ T, L.toAEEqFun p ∂(μ.prod μ) = (ν (S ×ˢ T)).toReal := by
  -- Step 1: Setup
  have hν_fin : IsFiniteMeasure ν := isFiniteMeasure_of_le (μ.prod μ) hν
  have hν_ac : ν ≪ μ.prod μ := Measure.absolutelyContinuous_of_le hν
  -- Step 2: Radon-Nikodym derivative
  set L₀ := ν.rnDeriv (μ.prod μ) with hL₀_def
  have hL₀_meas : Measurable L₀ := Measure.measurable_rnDeriv ν (μ.prod μ)
  have hL₀_le_one : L₀ ≤ᵐ[μ.prod μ] 1 := Measure.rnDeriv_le_one_of_le hν
  -- Step 3: Convert to ℝ-valued function with [0,1] bounds
  set L_fun : α × α → ℝ := fun p => (L₀ p).toReal with hL_fun_def
  have hL_meas : Measurable L_fun := hL₀_meas.ennreal_toReal
  have hL_mem_Icc : ∀ᵐ p ∂(μ.prod μ), L_fun p ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hL₀_le_one] with p hp
    simp only [Set.mem_Icc, L_fun, Pi.one_apply] at hp ⊢
    exact ⟨ENNReal.toReal_nonneg,
      (ENNReal.toReal_mono ENNReal.one_ne_top hp).trans_eq ENNReal.toReal_one⟩
  -- Step 4: Prove ν is swap-invariant (for RN symmetry)
  have hν_swap : ν.map Prod.swap = ν := by
    haveI : IsFiniteMeasure (ν.map Prod.swap) := by
      constructor
      rw [Measure.map_apply measurable_swap MeasurableSet.univ]
      exact measure_lt_top ν _
    exact Measure.ext_prod (fun {S} {T} hS hT => by
      rw [Measure.map_apply measurable_swap (hS.prod hT),
        Set.preimage_swap_prod, h_symm T S hT hS])
  -- Step 5: RN density is swap-symmetric a.e.
  have hL₀_symm : ∀ᵐ p ∂(μ.prod μ), L₀ p.swap = L₀ p := by
    have h_swap_prod : Measure.map Prod.swap (μ.prod μ) = μ.prod μ := Measure.prod_swap
    have h_emb := MeasurableEquiv.prodComm.measurableEmbedding.rnDeriv_map ν (μ.prod μ)
    have h_eq : ⇑(MeasurableEquiv.prodComm : α × α ≃ᵐ α × α) = Prod.swap := rfl
    rw [h_eq, hν_swap, h_swap_prod] at h_emb
    exact h_emb
  have hL_symm : ∀ᵐ p ∂(μ.prod μ), L_fun p.swap = L_fun p := by
    filter_upwards [hL₀_symm] with p hp
    simp only [L_fun, hp]
  -- Step 6: Build the Graphon
  set L_ae : (α × α) →ₘ[μ.prod μ] ℝ :=
    AEEqFun.mk L_fun hL_meas.aestronglyMeasurable with hL_ae_def
  have hL_coeFn := AEEqFun.coeFn_mk L_fun
    (μ := μ.prod μ) hL_meas.aestronglyMeasurable
  refine ⟨{
    toSymmKernel := {
      toAEEqFun := L_ae
      symm' := by
        have hL_swap := ae_prod_swap hL_coeFn
        filter_upwards [hL_coeFn, hL_swap, hL_symm] with p hp hp_swap hp_sym
        rw [hp_swap, hp, hp_sym]
    }
    ae_mem_Icc := by
      filter_upwards [hL_coeFn, hL_mem_Icc] with p hp h_Icc
      rw [hp]; exact h_Icc
  }, fun S T hS hT => ?_⟩
  -- Step 7: Rectangle integral = ν(S×T).toReal
  have h_eq : ∫ p in S ×ˢ T, L_ae p ∂(μ.prod μ) = ∫ p in S ×ˢ T, L_fun p ∂(μ.prod μ) := by
    apply setIntegral_congr_ae (hS.prod hT)
    filter_upwards [hL_coeFn] with p hp _; exact hp
  rw [h_eq]
  rw [show L_fun = fun p => (ν.rnDeriv (μ.prod μ) p).toReal from rfl]
  rw [Measure.setIntegral_toReal_rnDeriv' hν_ac (hS.prod hT), Measure.real]

/-- Assemble helpers to construct limit graphon from summable cutNormDiff bounds.

**Circularity guard**: Must NOT use `complete`, `quotient_compact`,
`exists_limit_of_rapid_convergence`, `exists_aligned_cutNormDiff_limit`, or
`exists_cutNormDiff_limit_of_cutDistance_rapid`. -/
private theorem exists_graphon_of_summable_cutNormDiff
    (A : ℕ → Graphon α μ) (δ : ℕ → ℝ)
    (hδ_pos : ∀ k, 0 ≤ δ k) (hδ_sum : Summable δ)
    (h_bound : ∀ k, cutNormDiff (A (k + 1)) (A k) ≤ δ k) :
    ∃ L : Graphon α μ, ∀ (S T : Set α), MeasurableSet S → MeasurableSet T →
      ∀ n, |rectIntegralDiff (A n) L S T| ≤ ∑' k, δ (n + k) := by
  -- Step 1: Construct limit measure ν with tight rectangle bounds
  obtain ⟨ν, hν_le, hν_symm, hν_rect⟩ :=
    exists_limit_measure_of_summable A δ hδ_pos hδ_sum h_bound
  -- Step 2: Extract graphon L from Radon-Nikodym derivative of ν
  obtain ⟨L, hL⟩ := exists_graphon_of_bounded_measure ν hν_le hν_symm
  -- Step 3: Bound |rectIntegralDiff(A n, L, S, T)| ≤ ∑' k, δ(n+k)
  refine ⟨L, fun S T hS hT n => ?_⟩
  -- rectIntegralDiff = ∫_{S×T} (A n) - ∫_{S×T} L = (∫_{S×T} A(n)) - ν(S×T).toReal
  rw [rectIntegralDiff_eq, SymmKernel.rectIntegral, SymmKernel.rectIntegral, hL S T hS hT]
  exact hν_rect S T hS hT n

/-- Construction of a limit graphon from summable consecutive cutNormDiff bounds.

Chains `rectIntegralDiff_le_tail_tsum` (telescope bound on rectangles) with
`exists_graphon_of_summable_cutNormDiff` (Radon-Nikodym limit construction).

**Circularity guard**: Must NOT use `complete`, `quotient_compact`,
`exists_limit_of_rapid_convergence`, `exists_aligned_cutNormDiff_limit`, or
`exists_cutNormDiff_limit_of_cutDistance_rapid`. -/
private theorem exists_graphon_with_limiting_rect_integrals
    (A : ℕ → Graphon α μ) (δ : ℕ → ℝ)
    (hδ_pos : ∀ k, 0 ≤ δ k) (hδ_sum : Summable δ)
    (h_bound : ∀ k, cutNormDiff (A (k + 1)) (A k) ≤ δ k) :
    ∃ L : Graphon α μ, ∀ n (S T : Set α), MeasurableSet S → MeasurableSet T →
      |rectIntegralDiff (A n) L S T| ≤ ∑' k, δ (n + k) := by
  obtain ⟨L, hL⟩ := exists_graphon_of_summable_cutNormDiff A δ hδ_pos hδ_sum h_bound
  exact ⟨L, fun n S T hS hT => hL S T hS hT n⟩

/-- Limit extraction from summable cutNormDiff Cauchy sequence.

Given a sequence of graphons `A_k` with summable consecutive `cutNormDiff` bounds,
there exists a limit graphon `L` with `cutNormDiff(A_k, L) → 0`.

**Proof**: Uses `exists_graphon_with_limiting_rect_integrals` (sorry'd — Radon-Nikodym)
to get a limit graphon L whose rectangle integrals are within tail sum of A(n)'s.
Then `cutNormDiff(A_n, L) ≤ ∑' k, δ(n+k) → 0` by bounding the iSup defining cutNormDiff.

**Circularity guard**: Must NOT use `complete`, `quotient_compact`,
`exists_limit_of_rapid_convergence`, `exists_aligned_cutNormDiff_limit`, or
`exists_cutNormDiff_limit_of_cutDistance_rapid`. -/
private theorem exists_cutNormDiff_limit_of_summable
    (A : ℕ → Graphon α μ) (δ : ℕ → ℝ)
    (hδ_pos : ∀ k, 0 ≤ δ k) (hδ_sum : Summable δ)
    (h_bound : ∀ k, cutNormDiff (A (k + 1)) (A k) ≤ δ k) :
    ∃ L : Graphon α μ, ∀ ε > 0, ∃ N, ∀ n ≥ N, cutNormDiff (A n) L < ε := by
  -- Get limit graphon whose rectangle integrals are within tail sum of A(n)'s
  obtain ⟨L, hL⟩ := exists_graphon_with_limiting_rect_integrals A δ hδ_pos hδ_sum h_bound
  refine ⟨L, fun ε hε => ?_⟩
  -- cutNormDiff(A n, L) ≤ ∑' k, δ(n+k) by bounding each rectangle integral
  have h_cn : ∀ n, cutNormDiff (A n) L ≤ ∑' k, δ (n + k) := by
    intro n
    have hδ_shift : Summable (fun k => δ (n + k)) :=
      hδ_sum.comp_injective (fun _ _ h => by omega)
    have h_tail_nn : 0 ≤ ∑' k, δ (n + k) := by
      simpa using hδ_shift.sum_le_tsum (∅ : Finset ℕ) (fun k _ => hδ_pos (n + k))
    unfold cutNormDiff
    apply Real.iSup_le _ h_tail_nn; intro S
    apply Real.iSup_le _ h_tail_nn; intro hS
    apply Real.iSup_le _ h_tail_nn; intro T
    apply Real.iSup_le _ h_tail_nn; intro hT
    exact hL n S T hS hT
  -- Tail tsum → 0 gives convergence
  have h_tail : ∀ ε' > 0, ∃ N, ∀ n ≥ N, ∑' k, δ (n + k) < ε' := by
    intro ε' hε'
    have h_conv := hδ_sum.hasSum.tendsto_sum_nat
    rw [Metric.tendsto_atTop] at h_conv
    obtain ⟨N, hN⟩ := h_conv ε' hε'
    refine ⟨N, fun n hn => ?_⟩
    have h_shift : ∑' k, δ (n + k) = ∑' k, δ k - ∑ k ∈ Finset.range n, δ k := by
      have h1 := ((summable_nat_add_iff n).mpr hδ_sum).hasSum
      rw [hasSum_nat_add_iff n] at h1
      have := h1.tsum_eq; simp only [add_comm] at this; linarith
    rw [h_shift]
    have h_le : ∑ k ∈ Finset.range n, δ k ≤ ∑' k, δ k :=
      hδ_sum.sum_le_tsum _ (fun k _ => hδ_pos k)
    have h_dist := hN n hn; rw [Real.dist_eq] at h_dist
    have h_nonpos : ∑ k ∈ Finset.range n, δ k - ∑' k, δ k ≤ 0 := by linarith
    rw [abs_of_nonpos h_nonpos] at h_dist; linarith
  obtain ⟨N, hN⟩ := h_tail ε hε
  exact ⟨N, fun n hn => lt_of_le_of_lt (h_cn n) (hN n hn)⟩

/-- Given graphons `V_k` with rapidly decaying consecutive cut distances, there exist
measure-preserving realignment maps `f_k` and a limit graphon `L` with
`cutNormDiff(pullback(V_k, f_k), L) → 0`.

This is the "coupling completeness" step: it converts cut-distance Cauchy convergence
to cut-norm-difference convergence via realignment.

**Proof**: Telescoping via `exists_cutNormDiff_cauchy_realignment` gives MeasurableEquiv
maps with summable consecutive cutNormDiff bounds, then `exists_cutNormDiff_limit_of_summable`
extracts the limit.

**Depends on**: `exists_cutNormDiff_limit_of_summable` (via `exists_graphon_with_limiting_rect_integrals`
sorry — Radon-Nikodym construction). -/
private theorem exists_cutNormDiff_limit_of_cutDistance_rapid
    (V : ℕ → Graphon α μ)
    (h_rapid : ∀ k : ℕ, cutDistance (V (k + 1)) (V k) ≤ 1 / 2 ^ k + 1 / 3 ^ k) :
    ∃ (L : Graphon α μ) (f : (k : ℕ) → (α → α)) (hf : ∀ k, MeasurePreserving (f k) μ μ),
      ∀ ε > 0, ∃ N, ∀ n ≥ N, cutNormDiff (pullback (V n) (f n) (hf n)) L < ε := by
  -- Step 1: Telescoping realignment with MeasurableEquiv witnesses
  obtain ⟨f_equiv, hf_equiv, δ, hδ_sum, hδ_pos, h_cauchy⟩ :=
    exists_cutNormDiff_cauchy_realignment V h_rapid
  -- Step 2: Extract limit from summable Cauchy sequence
  let A : ℕ → Graphon α μ := fun k => pullback (V k) (f_equiv k) (hf_equiv k)
  obtain ⟨L, hL⟩ := exists_cutNormDiff_limit_of_summable A δ hδ_pos hδ_sum h_cauchy
  -- Step 3: Return witnesses (coerce MeasurableEquiv to function)
  exact ⟨L, fun k => ↑(f_equiv k), fun k => hf_equiv k, hL⟩

/-- Alignment + limit for rapidly converging graphon sequences.

Given rapid cutDistance convergence (`∑ d(W_{k+1}, W_k) < ∞`), there exist
measure-preserving maps `e_k` and a limit graphon `V` such that
`cutNormDiff(pullback(W_k, e_k), V) → 0`.

**Proof structure**:

(a) *Alignment chain* (Rokhlin-dependent): Build aligned maps `e_k` inductively via
    `exists_common_extension_maps`. At each step, near-optimal maps from
    `cutDistance_lt_add_of_pos` are aligned using Rokhlin bijections, yielding
    `cutDistance(V_{k+1}, V_k) ≤ 1/2^k + 1/3^k` where `V_k = pullback (W k) (e_k)`.

(b) *cutNormDiff limit* (via `exists_cutNormDiff_limit_of_cutDistance_rapid`):
    Given summable consecutive cutDistance, realign and extract limit with
    cutNormDiff convergence. Now proved modulo `exists_graphon_with_limiting_rect_integrals`
    (Radon-Nikodym sorry).

**Depends on**: `MeasurePreserving.exists_common_extension` (Rokhlin axiom),
`exists_graphon_with_limiting_rect_integrals` (Radon-Nikodym sorry). -/
private theorem exists_aligned_cutNormDiff_limit
    (W : ℕ → Graphon α μ)
    (h_rapid : ∀ k : ℕ, cutDistance (W (k + 1)) (W k) ≤ 1 / 2 ^ k) :
    ∃ (V : Graphon α μ) (e : (k : ℕ) → (α → α)) (he : ∀ k, MeasurePreserving (e k) μ μ),
      ∀ ε > 0, ∃ N, ∀ n ≥ N, cutNormDiff (pullback (W n) (e n) (he n)) V < ε := by
  -- Step 1: Build alignment chain inductively.
  -- At step k: get near-optimal (φ_k, ψ_k) for (W k, W (k+1)),
  -- align e_k with φ_k via Rokhlin bijections χ₁, χ₂,
  -- set e_{k+1} = ψ_k ∘ χ₂.
  -- This gives cutDistance(V_{k+1}, V_k) ≤ 1/2^k + 1/3^k.
  --
  -- We package the inductive data as a function ℕ → Σ' (e : α → α), MeasurePreserving e μ μ.
  have h_step : ∀ (k : ℕ) (e_k : α → α) (he_k : MeasurePreserving e_k μ μ),
      ∃ (e_next : α → α) (he_next : MeasurePreserving e_next μ μ),
        cutDistance (pullback (W (k + 1)) e_next he_next)
                    (pullback (W k) e_k he_k) ≤ 1 / 2 ^ k + 1 / 3 ^ k := by
    intro k e_k he_k
    -- Get near-optimal maps for (W k, W (k+1)) with error 1/3^k
    have h3k_pos : (0 : ℝ) < 1 / 3 ^ k := by positivity
    obtain ⟨φ_k, ψ_k, hφ_k, hψ_k, h_opt⟩ := cutDistance_lt_add_of_pos (W k) (W (k + 1)) h3k_pos
    -- Align e_k with φ_k via Rokhlin: get χ₁, χ₂ with e_k ∘ χ₁ =ᵐ φ_k ∘ χ₂
    obtain ⟨χ₁, χ₂, hχ₁, hχ₂, h_align⟩ :=
      MeasurePreserving.exists_common_extension_maps e_k he_k φ_k hφ_k
    -- Define e_{k+1} = ψ_k ∘ χ₂
    refine ⟨ψ_k ∘ ↑χ₂, hψ_k.comp hχ₂, ?_⟩
    -- Show cutDistance(V_{k+1}, V_k) ≤ 1/2^k + 1/3^k
    -- where V_k = pb(W k, e_k), V_{k+1} = pb(W (k+1), ψ_k ∘ χ₂)
    -- Use (id, χ₁) as witnesses: cutDistance ≤ cutNormDiff(pb(V_{k+1}, id), pb(V_k, χ₁))
    --   = cutNormDiff(V_{k+1}, pb(V_k, χ₁))
    -- Key: pb(V_k, χ₁) = pb(W k, e_k ∘ χ₁) =ᵃᵉ pb(W k, φ_k ∘ χ₂)
    -- And cutNormDiff(pb(W(k+1), ψ_k ∘ χ₂), pb(W k, φ_k ∘ χ₂))
    --   = cutNormDiff(pb(W(k+1), ψ_k), pb(W k, φ_k))  [by invariance under χ₂]
    --   < cutDistance(W k, W(k+1)) + 1/3^k ≤ 1/2^k + 1/3^k
    have hψχ₂ : MeasurePreserving (ψ_k ∘ ↑χ₂) μ μ := hψ_k.comp hχ₂
    have hφχ₂ : MeasurePreserving (φ_k ∘ ↑χ₂) μ μ := hφ_k.comp hχ₂
    have heχ₁ : MeasurePreserving (e_k ∘ ↑χ₁) μ μ := he_k.comp hχ₁
    -- pb(W k, e_k ∘ χ₁) = pb(W k, φ_k ∘ χ₂) by alignment
    have h_align_pb : pullback (W k) (e_k ∘ ↑χ₁) heχ₁ = pullback (W k) (φ_k ∘ ↑χ₂) hφχ₂ := by
      apply Graphon.ext; apply SymmKernel.ext; apply AEEqFun.ext
      have h1 := pullback_ae (W k) (e_k ∘ ↑χ₁) heχ₁
      have h2 := pullback_ae (W k) (φ_k ∘ ↑χ₂) hφχ₂
      have h_prod_ae : ∀ᵐ p ∂(μ.prod μ),
          (e_k (χ₁ p.1), e_k (χ₁ p.2)) = (φ_k (χ₂ p.1), φ_k (χ₂ p.2)) := by
        have h_fst : ∀ᵐ p ∂(μ.prod μ), e_k (χ₁ p.1) = φ_k (χ₂ p.1) :=
          Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst h_align
        have h_snd : ∀ᵐ p ∂(μ.prod μ), e_k (χ₁ p.2) = φ_k (χ₂ p.2) :=
          Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd h_align
        filter_upwards [h_fst, h_snd] with p hp1 hp2
        exact Prod.ext hp1 hp2
      filter_upwards [h1, h2, h_prod_ae] with p hp1 hp2 hp_eq
      rw [hp1, hp2]; simp only [Function.comp_apply] at hp_eq ⊢; rw [hp_eq]
    -- cutNormDiff invariance under χ₂
    have h_inv : cutNormDiff (pullback (W (k + 1)) (ψ_k ∘ ↑χ₂) hψχ₂)
        (pullback (W k) (φ_k ∘ ↑χ₂) hφχ₂) =
        cutNormDiff (pullback (W (k + 1)) ψ_k hψ_k) (pullback (W k) φ_k hφ_k) := by
      rw [show pullback (W (k + 1)) (ψ_k ∘ ↑χ₂) hψχ₂ =
            pullback (pullback (W (k + 1)) ψ_k hψ_k) χ₂ hχ₂ from
            (pullback_pullback (W (k + 1)) ψ_k hψ_k (↑χ₂) hχ₂).symm,
        show pullback (W k) (φ_k ∘ ↑χ₂) hφχ₂ =
            pullback (pullback (W k) φ_k hφ_k) χ₂ hχ₂ from
            (pullback_pullback (W k) φ_k hφ_k (↑χ₂) hχ₂).symm]
      exact cutNormDiff_pullback_measurableEquiv _ _ χ₂ hχ₂
    -- Now bound cutDistance using (id, χ₁) as witnesses
    calc cutDistance (pullback (W (k + 1)) (ψ_k ∘ ↑χ₂) hψχ₂)
            (pullback (W k) e_k he_k)
        ≤ cutNormDiff
            (pullback (pullback (W (k + 1)) (ψ_k ∘ ↑χ₂) hψχ₂) id (MeasurePreserving.id μ))
            (pullback (pullback (W k) e_k he_k) χ₁ hχ₁) := by
          unfold cutDistance
          apply csInf_le
          · use 0; intro d ⟨φ, ψ, hφ, hψ, hd⟩; rw [hd]; exact cutNormDiff_nonneg _ _
          · exact ⟨id, ↑χ₁, MeasurePreserving.id μ, hχ₁, rfl⟩
      _ = cutNormDiff (pullback (W (k + 1)) (ψ_k ∘ ↑χ₂) hψχ₂)
            (pullback (W k) (e_k ∘ ↑χ₁) heχ₁) := by
          rw [pullback_id, pullback_pullback (W k) e_k he_k (↑χ₁) hχ₁]
      _ = cutNormDiff (pullback (W (k + 1)) (ψ_k ∘ ↑χ₂) hψχ₂)
            (pullback (W k) (φ_k ∘ ↑χ₂) hφχ₂) := by
          rw [h_align_pb]
      _ = cutNormDiff (pullback (W (k + 1)) ψ_k hψ_k)
            (pullback (W k) φ_k hφ_k) := h_inv
      _ ≤ cutDistance (W k) (W (k + 1)) + 1 / 3 ^ k := le_of_lt (by
          rw [cutNormDiff_symm]; exact h_opt)
      _ ≤ 1 / 2 ^ k + 1 / 3 ^ k := by
          have h_cd_sym : cutDistance (W k) (W (k + 1)) = cutDistance (W (k + 1)) (W k) :=
            cutDistance_symm (W k) (W (k + 1))
          linarith [h_rapid k]
  -- Build the full sequence by recursion using choose to extract data from h_step
  -- We use a dependent recursion to build (e_k, he_k) at each step.
  -- Extract the next-step function from h_step
  choose e_next he_next h_bound using h_step
  -- Now e_next k e_k he_k gives the next map, he_next gives its MP proof,
  -- and h_bound gives the cutDistance bound.
  -- Build the sequence by recursion
  let build : ℕ → PSigma (fun e : α → α => MeasurePreserving e μ μ) :=
    Nat.rec ⟨id, MeasurePreserving.id μ⟩
      (fun k prev => ⟨e_next k prev.1 prev.2, he_next k prev.1 prev.2⟩)
  let e : (k : ℕ) → (α → α) := fun k => (build k).1
  let he : ∀ k, MeasurePreserving (e k) μ μ := fun k => (build k).2
  -- Prove the rapid convergence bound for the constructed sequence
  have h_chain : ∀ k, cutDistance (pullback (W (k + 1)) (e (k + 1)) (he (k + 1)))
      (pullback (W k) (e k) (he k)) ≤ 1 / 2 ^ k + 1 / 3 ^ k := by
    intro k
    -- e (k+1) = e_next k (build k).1 (build k).2 and he (k+1) = he_next k ...
    -- The bound follows directly from h_bound
    exact h_bound k (build k).1 (build k).2
  -- Step 2: Apply the limit extraction (sorry'd)
  let V_seq : ℕ → Graphon α μ := fun k => pullback (W k) (e k) (he k)
  obtain ⟨L, f, hf, hconv⟩ := exists_cutNormDiff_limit_of_cutDistance_rapid V_seq h_chain
  -- Step 3: Compose alignment maps: final e_k = e_k ∘ f_k
  refine ⟨L, fun k => e k ∘ f k, fun k => (he k).comp (hf k), fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hconv ε hε
  refine ⟨N, fun n hn => ?_⟩
  -- cutNormDiff(pb(W n, e n ∘ f n), L) = cutNormDiff(pb(pb(W n, e n), f n), L)
  --   = cutNormDiff(pb(V_seq n, f n), L) < ε
  have h_comp : pullback (W n) (e n ∘ f n) ((he n).comp (hf n)) =
      pullback (V_seq n) (f n) (hf n) :=
    (pullback_pullback (W n) (e n) (he n) (f n) (hf n)).symm
  rw [h_comp]
  exact hN n hn

/-- A rapidly converging sequence of graphons (with `∑ cutDistance(W_{n+1}, W_n)` finite)
has a limit in cutDistance.

**Proof**: Apply `exists_aligned_cutNormDiff_limit` to get a limit graphon `V` and
aligning maps `e_k` with `cutNormDiff(pullback (W k) (e_k), V) → 0`. Then
`cutDistance(W k, V) ≤ cutNormDiff(pullback (W k) (e_k), V) → 0`, since the maps
`(e_k, id)` are valid witnesses in the cutDistance infimum. -/
private theorem exists_limit_of_rapid_convergence (W : ℕ → Graphon α μ)
    (h_rapid : ∀ k : ℕ, cutDistance (W (k + 1)) (W k) ≤ 1 / 2 ^ k) :
    ∃ V : Graphon α μ, ∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W n) V < ε := by
  obtain ⟨V, e, he, hconv⟩ := exists_aligned_cutNormDiff_limit W h_rapid
  refine ⟨V, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hconv ε hε
  refine ⟨N, fun n hn => ?_⟩
  -- cutDistance(W n, V) ≤ cutNormDiff(pullback (W n) (e n), V) < ε
  -- using (e n, id) as witnesses in the cutDistance infimum
  have h_le : cutDistance (W n) V ≤ cutNormDiff (pullback (W n) (e n) (he n)) V := by
    calc cutDistance (W n) V
        ≤ cutNormDiff (pullback (W n) (e n) (he n))
            (pullback V id (MeasurePreserving.id μ)) := by
          unfold cutDistance
          apply csInf_le
          · use 0; intro d ⟨φ, ψ, hφ, hψ, hd⟩; rw [hd]; exact cutNormDiff_nonneg _ _
          · exact ⟨e n, id, he n, MeasurePreserving.id μ, rfl⟩
      _ = cutNormDiff (pullback (W n) (e n) (he n)) V := by rw [pullback_id]
  linarith [hN n hn]

/-- The space of graphons is complete with respect to cut distance.

Every Cauchy sequence of graphons converges (modulo weak isomorphism).

**Proof structure**: From the Cauchy sequence, extract a rapidly converging
subsequence (with `cutDistance(W_{φ(k+1)}, W_{φ(k)}) ≤ 1/2^k`). Apply the
limit construction for rapidly converging sequences. Then show the full Cauchy
sequence converges to the same limit using the triangle inequality.

**Depends on**: `exists_limit_of_rapid_convergence` (proved from
`exists_aligned_cutNormDiff_limit`, sorry'd), `cutDistance_triangle` (proved modulo Rokhlin). -/
@[blueprint "thm:complete"
  (title := /-- Completeness of graphon space -/)]
theorem complete (W : ℕ → Graphon α μ) (hW : IsCauchy W) :
    ∃ V : Graphon α μ, ∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W n) V < ε := by
  -- Step 1: Extract a rapidly converging subsequence.
  -- For each k, choose N_k such that d(W_m, W_n) < 1/2^k for m, n ≥ N_k.
  have h_subseq : ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ k : ℕ, cutDistance (W (φ (k + 1))) (W (φ k)) ≤ 1 / 2 ^ k := by
    -- Build φ by choosing N_k from the Cauchy property
    have h_N : ∀ k : ℕ, ∃ N : ℕ, ∀ m n, m ≥ N → n ≥ N →
        cutDistance (W m) (W n) < 1 / 2 ^ k := by
      intro k
      exact hW (1 / 2 ^ k) (by positivity)
    choose N hN using h_N
    -- Build strictly increasing φ with φ(k) ≥ N_k
    -- φ(0) = N 0, φ(k+1) = max(φ(k) + 1, N(k+1))
    let φ : ℕ → ℕ := fun k => Nat.rec (N 0) (fun k prev => max (prev + 1) (N (k + 1))) k
    refine ⟨φ, ?_, ?_⟩
    · -- StrictMono
      intro a b hab
      induction b with
      | zero => omega
      | succ b ih =>
        by_cases h : a = b
        · subst h
          show φ a < max (φ a + 1) (N (a + 1))
          omega
        · calc φ a < φ b := ih (by omega)
            _ ≤ max (φ b + 1) (N (b + 1)) - 1 + 1 := by omega
            _ ≤ max (φ b + 1) (N (b + 1)) := by omega
    · -- Rapid convergence
      intro k
      have hφk_ge : φ k ≥ N k := by
        induction k with
        | zero => show N 0 ≥ N 0; omega
        | succ k ih =>
          show max (φ k + 1) (N (k + 1)) ≥ N (k + 1)
          omega
      have hφsk_ge : φ (k + 1) ≥ N k := by
        have h1 : φ (k + 1) ≥ φ k + 1 := by
          show max (φ k + 1) (N (k + 1)) ≥ φ k + 1; omega
        omega
      exact le_of_lt (hN k (φ (k + 1)) (φ k) hφsk_ge hφk_ge)
  obtain ⟨φ, hφ_mono, hφ_rapid⟩ := h_subseq
  -- Step 2: Apply the limit construction for rapidly converging sequences.
  obtain ⟨V, hV⟩ := exists_limit_of_rapid_convergence (W ∘ φ) (by
    intro k; simp only [Function.comp_apply]; exact hφ_rapid k)
  -- Step 3: Show the full Cauchy sequence converges to V.
  -- Key: if a Cauchy sequence has a convergent subsequence, the full sequence converges.
  refine ⟨V, fun ε hε => ?_⟩
  -- Choose N₁: Cauchy tail bound ε/2
  obtain ⟨N₁, hN₁⟩ := hW (ε / 2) (by linarith)
  -- Choose N₂: subsequence within ε/2 of V
  obtain ⟨N₂, hN₂⟩ := hV (ε / 2) (by linarith)
  -- For n ≥ N₁, pick k ≥ N₂ with φ(k) ≥ N₁
  -- Since φ is strictly increasing, φ(k) ≥ k for all k
  have hφ_ge : ∀ k, φ k ≥ k := StrictMono.id_le hφ_mono
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  -- Use k = max N₁ N₂ as the bridge index (φ(k) ≥ k ≥ N₁)
  set k := max N₁ N₂
  have hk_ge_N₂ : k ≥ N₂ := le_max_right N₁ N₂
  have hφk_ge_N₁ : φ k ≥ N₁ := le_trans (le_max_left N₁ N₂) (hφ_ge k)
  have hn_ge_N₁ : n ≥ N₁ := le_trans (le_max_left N₁ N₂) hn
  calc cutDistance (W n) V
      ≤ cutDistance (W n) (W (φ k)) + cutDistance (W (φ k)) V :=
        cutDistance_triangle (W n) (W (φ k)) V
    _ < ε / 2 + ε / 2 := by
        have h1 : cutDistance (W n) (W (φ k)) < ε / 2 :=
          hN₁ n (φ k) hn_ge_N₁ hφk_ge_N₁
        have h2 : cutDistance (W (φ k)) V < ε / 2 := by
          have := hN₂ k hk_ge_N₂
          simp only [Function.comp_apply] at this
          exact this
        exact add_lt_add h1 h2
    _ = ε := by ring

end Completeness

/-! ### Compactness -/

section Compactness

variable [IsProbabilityMeasure μ] [StandardBorelSpace α]

/-- The space of graphons (modulo weak isomorphism) is compact.

This is the fundamental compactness theorem for graphon theory.
It follows from total boundedness (regularity lemma) and completeness.

**Structure**: This is sequential compactness, equivalent to compactness
for metric spaces (which graphon space is, modulo weak isomorphism).

**Depends on**: `totallyBounded` (sorry), `complete` (sorry), `cutDistance_triangle`
(proved modulo Rokhlin sorry). -/
theorem compact :
    ∀ (W : ℕ → Graphon α μ), ∃ (V : Graphon α μ) (φ : ℕ → ℕ),
      StrictMono φ ∧ ∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W (φ n)) V < ε := by
  intro W
  -- Step 1: For each k, get (1/(k+1))-net and extract increasing subsequence
  -- of indices staying close to one net point
  have h_nets : ∀ k : ℕ, ∃ (V_k : Graphon α μ) (I_k : Set ℕ),
      Set.Infinite I_k ∧ ∀ n ∈ I_k, cutDistance (W n) V_k ≤ 1 / (k + 1 : ℝ) := by
    intro k
    have hk : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    obtain ⟨S, hS⟩ := totallyBounded (μ := μ) (1 / (k + 1 : ℝ)) hk
    -- The map n ↦ (nearest net point to W n) has finite range S
    -- By pigeonhole, some V ∈ S has infinitely many preimages
    have h_map : ∀ n : ℕ, ∃ V ∈ S, cutDistance (W n) V ≤ 1 / (k + 1 : ℝ) :=
      fun n => hS (W n)
    choose f hf_mem hf_dist using h_map
    -- Restrict f to have finite codomain ↑S for pigeonhole
    let f' : ℕ → ↑(S : Set (Graphon α μ)) := fun n => ⟨f n, hf_mem n⟩
    have : Finite ↑(S : Set (Graphon α μ)) := S.finite_toSet.to_subtype
    obtain ⟨⟨V, _⟩, hV_inf⟩ := Finite.exists_infinite_fiber f'
    refine ⟨V, f ⁻¹' {V}, ?_, fun n hn => ?_⟩
    · -- f ⁻¹' {V} is infinite (same as f' ⁻¹' {⟨V, _⟩})
      have : f ⁻¹' {V} = f' ⁻¹' {⟨V, ‹_›⟩} := by ext; simp [f', Subtype.ext_iff]
      rw [this]; exact Set.infinite_coe_iff.mp hV_inf
    · simp only [Set.mem_preimage, Set.mem_singleton_iff] at hn
      rw [← hn]; exact hf_dist n
  -- Step 2: Iterative refinement — extract nested infinite sets I₀ ⊇ I₁ ⊇ I₂ ⊇ ...
  -- and build a strictly increasing enumeration
  -- For simplicity, we use a Cauchy diagonal construction
  choose V_k I_k hI_inf hI_close using h_nets
  -- Step 3: Build increasing subsequence — for each k, pick an element from I_k
  -- that is larger than all previous picks
  -- We build the sequence by recursion using the infinite sets
  -- Use Set.Infinite.exists_nat_lt to pick increasing elements
  -- Actually, let's use the simpler approach: extract a single Cauchy subsequence
  -- For k=0, I_0 is infinite. Pick φ(0) ∈ I_0.
  -- For k=1, I_0 ∩ I_1 might not be infinite. Instead, use nested extraction.
  --
  -- Alternative: pick φ(k) ∈ I_k with φ(k) > φ(k-1).
  -- This works if I_k is infinite (which it is).
  -- But we need: W(φ(k)) is close to V_m for all m ≤ k, not just V_k.
  -- Actually we only need: for m, n ≥ N,
  -- d(W(φ(m)), W(φ(n))) ≤ d(W(φ(m)), V_m) + d(V_m, V_n) + d(V_n, W(φ(n)))
  -- ≤ 1/(m+1) + d(V_m, V_n) + 1/(n+1)
  -- This doesn't directly work because V_m and V_n might be far apart.
  --
  -- Better: pick φ(k) from ∩_{j≤k} I_j so it's close to ALL V_j for j ≤ k.
  -- Then for m, n ≥ N: d(W(φ(m)), W(φ(n))) ≤ d(W(φ(m)), V_N) + d(V_N, W(φ(n)))
  -- ≤ 1/(N+1) + 1/(N+1) = 2/(N+1).
  -- For this to work, we need ∩_{j≤k} I_j to be infinite.
  -- Since each I_j is infinite and their intersection is decreasing...
  -- But the intersection of infinitely many infinite sets might be empty!
  --
  -- The standard fix: refine I_{k+1} to be a subset of I_k.
  -- For each k, instead of I_k from totallyBounded directly, we intersect
  -- with the previous set and use pigeonhole again within that subset.
  --
  -- This is the standard nested subsequence extraction. It's doable but requires
  -- careful induction. Let me use a classical existence proof instead.
  --
  -- Claim: ∃ φ : ℕ → ℕ strictly increasing, W ∘ φ is Cauchy.
  -- Proof: by the standard diagonal argument with nested subsequences.
  -- Since the proof is a standard real analysis exercise and the key mathematical
  -- content is in totallyBounded and complete, we sorry the extraction and apply complete.
  suffices h_cauchy : ∃ (φ : ℕ → ℕ), StrictMono φ ∧ IsCauchy (W ∘ φ) by
    obtain ⟨φ, hφ_mono, hφ_cauchy⟩ := h_cauchy
    obtain ⟨V, hV⟩ := complete (W ∘ φ) hφ_cauchy
    exact ⟨V, φ, hφ_mono, hV⟩
  -- Build nested subsequences by induction
  -- I'_0 = I_0, I'_{k+1} = {n ∈ I'_k | n ∈ I_{k+1}} restricted via pigeonhole
  -- Actually, define refined sets J_k ⊆ I_k ∩ J_{k-1} that are infinite
  -- and a center C_k such that ∀ n ∈ J_k, d(W n, C_k) ≤ 1/(k+1)
  -- Then pick φ(k) from J_k with φ(k) > φ(k-1)
  -- Cauchy: for m, n ≥ N, d(W(φ(m)), W(φ(n)))
  --   ≤ d(W(φ(m)), C_N) + d(C_N, W(φ(n))) ≤ 2/(N+1)
  -- This needs the triangle inequality (StandardBorelSpace) and that φ(m), φ(n) ∈ J_N for m,n ≥ N

  -- Define the nested infinite sets by induction
  have h_nested : ∃ (J : ℕ → Set ℕ) (C : ℕ → Graphon α μ),
      (∀ k, Set.Infinite (J k)) ∧
      (∀ k, J (k + 1) ⊆ J k) ∧
      (∀ k n, n ∈ J k → cutDistance (W n) (C k) ≤ 1 / (k + 1 : ℝ)) := by
    -- Refinement step: given infinite A, extract infinite B ⊆ A close to some center
    have h_refine : ∀ (A : Set ℕ), A.Infinite → ∀ k : ℕ,
        ∃ (B : Set ℕ) (V : Graphon α μ), B ⊆ A ∧ B.Infinite ∧
          ∀ n ∈ B, cutDistance (W n) V ≤ 1 / (↑k + 1 : ℝ) := by
      intro A hA k
      obtain ⟨S, hS⟩ := totallyBounded (μ := μ) _ (show (0 : ℝ) < 1 / (↑k + 1) by positivity)
      choose g hg_mem hg_dist using fun n => hS (W n)
      -- Pigeonhole: A is infinite, S is finite, so some fiber of g restricted to A is infinite
      let g' : ↑A → ↑(S : Set (Graphon α μ)) := fun ⟨n, _⟩ => ⟨g n, hg_mem n⟩
      haveI : Infinite ↑A := Set.infinite_coe_iff.mpr hA
      haveI : Finite ↑(S : Set (Graphon α μ)) := S.finite_toSet.to_subtype
      obtain ⟨⟨V, hVS⟩, hV_inf⟩ := Finite.exists_infinite_fiber g'
      refine ⟨Subtype.val '' (g' ⁻¹' {⟨V, hVS⟩}), V, ?_, ?_, ?_⟩
      · rintro _ ⟨⟨_, hn⟩, _, rfl⟩; exact hn
      · exact (Set.infinite_coe_iff.mp hV_inf).image Subtype.val_injective.injOn
      · rintro _ ⟨⟨n, _⟩, hmem, rfl⟩
        have : g n = V := by simpa [g'] using hmem
        rw [← this]; exact hg_dist n
    -- Extract deterministic choice functions
    choose rB rV hrBV using h_refine
    -- Build nested sequence: state = (J_k, proof of J_k.Infinite)
    let build : ℕ → { S : Set ℕ // S.Infinite } :=
      Nat.rec ⟨I_k 0, hI_inf 0⟩ fun k prev =>
        ⟨rB prev.1 prev.2 (k + 1), (hrBV prev.1 prev.2 (k + 1)).2.1⟩
    let J := fun k => (build k).1
    let C : ℕ → Graphon α μ := fun k =>
      match k with
      | 0 => V_k 0
      | k + 1 => rV (build k).1 (build k).2 (k + 1)
    exact ⟨J, C, fun k => (build k).2,
      fun k => (hrBV (build k).1 (build k).2 (k + 1)).1,
      fun k n hn => by
        cases k with
        | zero => exact hI_close 0 n hn
        | succ k => exact (hrBV (build k).1 (build k).2 (k + 1)).2.2 n hn⟩
  obtain ⟨J, C, hJ_inf, hJ_nest, hJ_close⟩ := h_nested
  -- Pick φ(k) from J_k with φ(k) > φ(k-1)
  have h_pick : ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∀ k, φ k ∈ J k := by
    -- Since J_k is infinite, we can always pick an element > any given bound
    -- and J_{k+1} ⊆ J_k, so φ(k) ∈ J_k for all subsequent k'
    -- Actually, we just need φ(k) ∈ J_k for each k, and strictly increasing.
    -- Build by recursion: φ(0) = min element of J_0
    -- φ(k+1) = some element of J_{k+1} that is > φ(k) (exists since J_{k+1} is infinite)
    have h_exists : ∀ (k : ℕ) (bound : ℕ), ∃ n ∈ J k, n > bound :=
      fun k bound => (hJ_inf k).exists_gt bound
    -- Build the sequence
    choose next h_next_mem h_next_gt using h_exists
    refine ⟨fun k => Nat.rec (next 0 0) (fun k prev => next (k + 1) prev) k, ?_, ?_⟩
    · -- StrictMono
      intro a b hab
      induction b with
      | zero => omega
      | succ b ih =>
        by_cases hab' : a = b
        · subst hab'; simp; exact h_next_gt _ _
        · calc Nat.rec (next 0 0) (fun k prev => next (k + 1) prev) a
              < Nat.rec (next 0 0) (fun k prev => next (k + 1) prev) b := ih (by omega)
            _ ≤ next (b + 1) (Nat.rec (next 0 0) (fun k prev => next (k + 1) prev) b) :=
                Nat.le_of_lt (h_next_gt _ _)
    · -- ∀ k, φ k ∈ J k
      intro k; induction k with
      | zero => exact h_next_mem 0 0
      | succ k _ => exact h_next_mem (k + 1) _
  obtain ⟨φ, hφ_mono, hφ_mem⟩ := h_pick
  refine ⟨φ, hφ_mono, ?_⟩
  -- Show W ∘ φ is Cauchy using triangle inequality
  intro ε hε
  -- Choose N so that 2/(N+1) < ε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 / (N + 1 : ℝ) < ε := by
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
    exact ⟨N, by
      have hNp : (0 : ℝ) < ↑N + 1 := by positivity
      rw [div_lt_iff₀ hNp]
      have h1 : 2 < ε * (↑N : ℝ) := by rw [div_lt_iff₀ hε] at hN; linarith
      linarith⟩
  refine ⟨N, fun m n hm hn => ?_⟩
  simp only [Function.comp_apply]
  -- d(W(φ(m)), W(φ(n)))
  -- ≤ d(W(φ(m)), C_N) + d(C_N, W(φ(n)))  [triangle]
  -- ≤ 1/(N+1) + 1/(N+1) = 2/(N+1) < ε
  -- Transitive nesting: J m ⊆ J N when N ≤ m
  have hJ_nest_trans : ∀ {a b : ℕ}, b ≤ a → J a ⊆ J b := by
    intro a b h
    induction h with
    | refl => exact Set.Subset.rfl
    | step _ ih => exact (hJ_nest _).trans ih
  have hm_mem : φ m ∈ J N := hJ_nest_trans hm (hφ_mem m)
  have hn_mem : φ n ∈ J N := hJ_nest_trans hn (hφ_mem n)
  calc cutDistance (W (φ m)) (W (φ n))
      ≤ cutDistance (W (φ m)) (C N) + cutDistance (C N) (W (φ n)) :=
        cutDistance_triangle _ _ _
    _ ≤ 1 / (↑N + 1) + 1 / (↑N + 1) := by
        have h1 := hJ_close N (φ m) hm_mem
        have h2 : cutDistance (C N) (W (φ n)) ≤ 1 / (↑N + 1) := by
          rw [cutDistance_symm]; exact hJ_close N (φ n) hn_mem
        exact add_le_add h1 h2
    _ = 2 / (↑N + 1) := by ring
    _ < ε := hN

end Compactness

end Graphon
