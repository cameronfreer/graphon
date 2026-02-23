/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.CutDistance
import Graphon.Regularity

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
private theorem cutNormDiff_mkStepGraphon_le (P : MeasurablePartition α μ)
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
  -- Partition transfer: V_round on P_W matches some net element on P₀.
  -- By Rokhlin's theorem (standard Borel probability spaces are isomorphic to [0,1]),
  -- there exists a MP bijection mapping P_W-cells to P₀-cells. Under this bijection,
  -- V_round transfers to a step graphon on P₀ with the same grid coefficients,
  -- which is in the net by construction. See `MeasurePreserving.exists_common_extension`
  -- in `CutDistance.lean` for the underlying Rokhlin axiom.
  sorry

end TotalBoundedness

/-! ### Completeness -/

section Completeness

variable [IsProbabilityMeasure μ] [StandardBorelSpace α]

/-- A sequence of graphons is Cauchy with respect to cut distance. -/
def IsCauchy (W : ℕ → Graphon α μ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m n, m ≥ N → n ≥ N → cutDistance (W m) (W n) < ε

/-- A rapidly converging sequence of graphons (with `∑ cutDistance(W_{n+1}, W_n)` finite)
has a limit in cutDistance.

**Sorry**: This is the core limit construction for graphon completeness.
The standard proof (Lovász [2012], Proposition 9.17) proceeds:
1. For each precision k, regularity gives step approximation with ≤ M(k) parts
2. Rectangle averages of W_n on the regularity partition are in [0,1]
3. Diagonal extraction over increasing scales: extract subsequence where all averages converge
4. Limiting averages define a step function at each scale
5. Step functions form a Cauchy sequence in L² (for step functions on a fixed partition,
   cut norm and L² norm are equivalent up to partition-dependent constants)
6. L² completeness gives limit V
7. V ∈ [0,1] a.e. and symmetric, hence a graphon
8. cutDistance(W_n, V) → 0 via triangle through step approximations

**Depends on**: Rokhlin's theorem (for aligning partitions across different graphons),
which is already axiomatized as `MeasurePreserving.exists_common_extension`. -/
private theorem exists_limit_of_rapid_convergence (W : ℕ → Graphon α μ)
    (h_rapid : ∀ k : ℕ, cutDistance (W (k + 1)) (W k) ≤ 1 / 2 ^ k) :
    ∃ V : Graphon α μ, ∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W n) V < ε := by
  sorry

/-- The space of graphons is complete with respect to cut distance.

Every Cauchy sequence of graphons converges (modulo weak isomorphism).

**Proof structure**: From the Cauchy sequence, extract a rapidly converging
subsequence (with `cutDistance(W_{φ(k+1)}, W_{φ(k)}) ≤ 1/2^k`). Apply the
limit construction for rapidly converging sequences. Then show the full Cauchy
sequence converges to the same limit using the triangle inequality.

**Depends on**: `exists_limit_of_rapid_convergence` (sorry, diagonal extraction
+ L² limit), `cutDistance_triangle` (proved modulo Rokhlin). -/
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
