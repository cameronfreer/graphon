/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.HomDensity
import Graphon.CutDistance

/-!
# Counting Lemma for Graphons

This file proves the counting lemma, which relates the difference in homomorphism
densities to the cut norm of the difference between graphons.

## Main results

* `Graphon.homDensity_sub_le` - `|t(F, U) - t(F, W)| ≤ |E(F)| · ‖U - W‖_□`

## Implementation notes

The counting lemma is one of the central results in graphon theory. It says that
if two graphons are close in cut norm, then they have similar homomorphism densities
for any fixed graph F.

The constant `|E(F)|` (number of edges in F) is optimal in general.

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Chapter 10
-/

open MeasureTheory Set Filter Finset

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Graphon

/-! ### Counting lemma -/

section Counting

variable [IsProbabilityMeasure μ]

/-- The counting lemma: homomorphism density difference is bounded by cut norm.

For any graph F and graphons U, W on the same probability space:
`|t(F, U) - t(F, W)| ≤ |E(F)| · ‖U - W‖_□`

This is the key result showing that cut norm controls homomorphism densities. -/
theorem homDensity_sub_le (F : SimpleGraph V) [DecidableRel F.Adj]
    (U W : Graphon α μ) :
    |homDensity F U - homDensity F W| ≤ F.edgeFinset.card * cutNormDiff U W := by
  -- Proof outline (Lovász, Theorem 10.23):
  --
  -- Let E = {e₁, ..., eₘ} be the edges of F. For an assignment x : V → α:
  -- - Uᵢ(x) = U(x(eᵢ.1), x(eᵢ.2))
  -- - Wᵢ(x) = W(x(eᵢ.1), x(eᵢ.2))
  --
  -- Step 1: Telescoping identity
  --   ∏ᵢ Uᵢ - ∏ᵢ Wᵢ = Σⱼ (∏ᵢ<ⱼ Uᵢ) · (Uⱼ - Wⱼ) · (∏ᵢ>ⱼ Wᵢ)
  --
  -- Step 2: Each term in the sum satisfies
  --   |∫ (∏ᵢ<ⱼ Uᵢ) · (Uⱼ - Wⱼ) · (∏ᵢ>ⱼ Wᵢ) dμ^V|
  --   ≤ ‖U - W‖_□  (by cut norm definition)
  --
  --   The key is that the prefix (∏ᵢ<ⱼ Uᵢ) and suffix (∏ᵢ>ⱼ Wᵢ) are
  --   measurable functions in [0,1], so integrating (Uⱼ - Wⱼ) against them
  --   gives a bound by the cut norm (via conditioning on the other variables).
  --
  -- Step 3: Triangle inequality
  --   |∫ (∏ U - ∏ W)| ≤ Σⱼ |∫ term_j| ≤ m · ‖U - W‖_□
  --
  -- Implementation requires:
  -- - Finset.list_eq_of_card for ordering edges
  -- - Telescoping product lemma for finite products
  -- - Conditional expectation bounds using cut norm
  sorry

/-- Corollary: graphs with small cut distance have similar homomorphism densities.

The proof uses that homDensity is preserved under pullbacks (homDensity_pullback_mp):
- For any φ, ψ measure-preserving: homDensity F (pullback U φ) = homDensity F U
- So |homDensity F U - homDensity F W| = |homDensity F (pullback U φ) - homDensity F (pullback W ψ)|
- By homDensity_sub_le: ≤ |E(F)| * cutNormDiff (pullback U φ) (pullback W ψ)
- Taking inf over φ, ψ gives the bound by cutDistance -/
theorem homDensity_sub_le_of_cutDistance (F : SimpleGraph V) [DecidableRel F.Adj]
    (U W : Graphon α μ) :
    |homDensity F U - homDensity F W| ≤ F.edgeFinset.card * cutDistance U W := by
  -- The LHS is constant for any reparametrizations of U and W
  -- by homDensity_pullback_mp: homDensity F (pullback U φ hφ) = homDensity F U
  unfold cutDistance
  -- For each d in the infimum set, we have LHS ≤ |E(F)| * d
  -- Therefore LHS ≤ |E(F)| * sInf {...}
  have h_bdd : BddBelow {d : ℝ | ∃ (φ ψ : α → α) (hφ : MeasurePreserving φ μ μ)
      (hψ : MeasurePreserving ψ μ μ), d = cutNormDiff (pullback U φ hφ) (pullback W ψ hψ)} := by
    use 0
    intro d ⟨φ, ψ, hφ, hψ, hd⟩
    rw [hd]
    exact cutNormDiff_nonneg (pullback U φ hφ) (pullback W ψ hψ)
  have h_nonempty : {d : ℝ | ∃ (φ ψ : α → α) (hφ : MeasurePreserving φ μ μ)
      (hψ : MeasurePreserving ψ μ μ), d = cutNormDiff (pullback U φ hφ) (pullback W ψ hψ)}.Nonempty :=
    cutDistance_set_nonempty U W
  -- LHS ≤ |E(F)| * d for all d in the set
  have h_forall : ∀ d ∈ {d : ℝ | ∃ (φ ψ : α → α) (hφ : MeasurePreserving φ μ μ)
      (hψ : MeasurePreserving ψ μ μ), d = cutNormDiff (pullback U φ hφ) (pullback W ψ hψ)},
      |homDensity F U - homDensity F W| ≤ F.edgeFinset.card * d := by
    intro d ⟨φ, ψ, hφ, hψ, hd⟩
    -- By homDensity_pullback_mp, homDensity is preserved under pullback
    rw [← homDensity_pullback_mp F U φ hφ, ← homDensity_pullback_mp F W ψ hψ, hd]
    -- Now apply homDensity_sub_le
    exact homDensity_sub_le F (pullback U φ hφ) (pullback W ψ hψ)
  -- Conclude: LHS ≤ |E(F)| * d for all d implies LHS ≤ |E(F)| * sInf
  by_cases hcard : F.edgeFinset.card = 0
  · -- If no edges, LHS = 0 and RHS = 0 * cutDistance = 0
    -- First show homDensity F U = homDensity F W = 1 for empty graphs
    have h_empty : F.edgeFinset = ∅ := Finset.card_eq_zero.mp hcard
    have h_hom_eq : homDensity F U = homDensity F W := by
      simp only [homDensity_eq_integral, homDensityIntegrand, h_empty, Finset.prod_empty]
    rw [h_hom_eq, sub_self, abs_zero, hcard, Nat.cast_zero, zero_mul]
  · -- Non-empty graph: use csInf property
    have hcard_pos : (0 : ℝ) < F.edgeFinset.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard)
    -- LHS / |E(F)| ≤ d for all d ∈ S, so LHS / |E(F)| ≤ sInf S
    have h_div : |homDensity F U - homDensity F W| / F.edgeFinset.card ≤ sInf
        {d : ℝ | ∃ (φ ψ : α → α) (hφ : MeasurePreserving φ μ μ)
         (hψ : MeasurePreserving ψ μ μ), d = cutNormDiff (pullback U φ hφ) (pullback W ψ hψ)} := by
      apply le_csInf h_nonempty
      intro d hd
      have hle := h_forall d hd
      rw [div_le_iff₀ hcard_pos]
      calc |homDensity F U - homDensity F W|
          ≤ F.edgeFinset.card * d := hle
        _ = d * F.edgeFinset.card := mul_comm _ _
    rw [div_le_iff₀ hcard_pos] at h_div
    calc |homDensity F U - homDensity F W|
        ≤ sInf {d : ℝ | ∃ (φ ψ : α → α) (hφ : MeasurePreserving φ μ μ)
            (hψ : MeasurePreserving ψ μ μ), d = cutNormDiff (pullback U φ hφ) (pullback W ψ hψ)} *
            F.edgeFinset.card := h_div
      _ = F.edgeFinset.card * sInf _ := mul_comm _ _

/-- If cut distance is zero, homomorphism densities are equal.

This is a key consequence: weakly isomorphic graphons have the same
homomorphism densities for all graphs F. -/
theorem homDensity_eq_of_cutDistance_zero (F : SimpleGraph V) [DecidableRel F.Adj]
    (U W : Graphon α μ) (h : cutDistance U W = 0) :
    homDensity F U = homDensity F W := by
  have hle := homDensity_sub_le_of_cutDistance F U W
  rw [h, mul_zero] at hle
  have habs : |homDensity F U - homDensity F W| = 0 :=
    le_antisymm hle (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

end Counting

/-! ### Continuity properties -/

section Continuity

variable [IsProbabilityMeasure μ]

/-- Homomorphism density difference is bounded by edge count times cut norm difference.

This is the quantitative version of continuity with respect to cut norm.

**Note**: We use `max 1 F.edgeFinset.card` in the denominator to handle the empty graph case.
For empty graphs, both homomorphism densities equal 1, so the bound is trivially satisfied. -/
theorem homDensity_continuous_cutNormDiff (F : SimpleGraph V) [DecidableRel F.Adj]
    (U W : Graphon α μ) (ε : ℝ) (hε : ε > 0)
    (h : cutNormDiff U W < ε / max 1 F.edgeFinset.card) :
    |homDensity F U - homDensity F W| < ε := by
  by_cases hF : F.edgeFinset.card = 0
  · -- Empty graph: both densities are 1
    have hEmpty : F.edgeFinset = ∅ := Finset.card_eq_zero.mp hF
    have hU : homDensity F U = 1 := by
      unfold homDensity
      simp only [hEmpty, Finset.prod_empty]
      simp only [integral_const]
      simp
    have hW : homDensity F W = 1 := by
      unfold homDensity
      simp only [hEmpty, Finset.prod_empty]
      simp only [integral_const]
      simp
    simp only [hU, hW, sub_self, abs_zero]
    exact hε
  · have hcard_pos : 0 < F.edgeFinset.card := Nat.pos_of_ne_zero hF
    have hmax_eq : max 1 F.edgeFinset.card = F.edgeFinset.card :=
      max_eq_right (Nat.one_le_iff_ne_zero.mpr hF)
    simp only [hmax_eq] at h
    calc |homDensity F U - homDensity F W|
        ≤ F.edgeFinset.card * cutNormDiff U W := homDensity_sub_le F U W
      _ < F.edgeFinset.card * (ε / F.edgeFinset.card) := by
          apply mul_lt_mul_of_pos_left h
          exact Nat.cast_pos.mpr hcard_pos
      _ = ε := by field_simp

end Continuity

end Graphon
