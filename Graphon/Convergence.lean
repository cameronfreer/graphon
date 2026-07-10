/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.InverseCounting

/-!
# Convergence of Graphon Sequences

This file establishes the main theorems characterizing convergence of
graphon sequences in cut distance, bringing together the counting lemma,
inverse counting lemma, and compactness results.

## Main results

* `Graphon.converges_iff_homDensity` — Cut distance convergence ⟺ hom density convergence
* `Graphon.exists_convergent_subsequence` — Every sequence has a convergent subsequence (compactness)
* `Graphon.isCauchy_iff_isConvergent` — Cauchy ⟺ convergent

## Implementation notes

This file brings together the key results:
- Counting lemma: cut distance bounds → hom density bounds
- Inverse counting lemma: hom density bounds → cut distance bounds
- Compactness: every sequence has convergent subsequence
- Completeness: Cauchy sequences converge

The main theorem is that the following are equivalent for a graphon sequence (Wₙ):
1. (Wₙ) converges in cut distance to some graphon W
2. (t(F, Wₙ)) converges for all finite graphs F
3. (Wₙ) is Cauchy in cut distance

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Chapter 11
-/

open MeasureTheory Set Filter

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

/-! ### Equivalent characterizations of convergence -/

section EquivalentConvergence

variable [IsProbabilityMeasure μ]

/-- A sequence of graphons is convergent in cut distance. -/
def IsConvergent (W : ℕ → Graphon α μ) : Prop :=
  ∃ V : Graphon α μ, ∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W n) V < ε

/-- A sequence of graphons has convergent homomorphism densities for all graphs.

Quantifies over graphs on `Fin k` for all `k : ℕ`; this is equivalent to
quantifying over all finite types since every `Fintype` embeds into some `Fin k`. -/
def HasConvergentHomDensities (W : ℕ → Graphon α μ) : Prop :=
  ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
    ∃ L : ℝ, ∀ ε > 0, ∃ N, ∀ n ≥ N, |homDensity F (W n) - L| < ε

/-- Main theorem: cut distance convergence is equivalent to homomorphism
    density convergence.

A sequence of graphons converges in cut distance if and only if all
homomorphism densities converge. -/
theorem converges_iff_homDensity [StandardBorelSpace α] [NoAtoms μ] (W : ℕ → Graphon α μ) :
    IsConvergent W ↔ HasConvergentHomDensities W := by
  constructor
  · -- Forward direction: counting lemma
    intro ⟨V, hV⟩
    intro k F _
    use homDensity F V
    intro ε hε
    -- By counting lemma: |t(F, Wₙ) - t(F, V)| ≤ |E(F)| · δ□(Wₙ, V)
    -- Choose N so δ□(Wₙ, V) < ε / max(1, |E(F)|)
    by_cases hF : F.edgeFinset.card = 0
    · -- Empty graph: homDensity is always 1, so trivially converges
      -- When edgeFinset is empty, ∏ e ∈ ∅, f e = 1, so homDensity = ∫ 1 dμ^V = 1
      use 0
      intro n _
      have h_empty : F.edgeFinset = ∅ := Finset.card_eq_zero.mp hF
      simp only [homDensity_eq_integral, homDensityIntegrand, h_empty, Finset.prod_empty,
          integral_const, smul_eq_mul, mul_one, sub_self, abs_zero, hε]
    · -- Non-empty graph: use counting lemma
      have hcard_pos : (0 : ℝ) < F.edgeFinset.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hF)
      obtain ⟨N, hN⟩ := hV (ε / F.edgeFinset.card) (div_pos hε hcard_pos)
      use N
      intro n hn
      -- |t(F, Wₙ) - t(F, V)| ≤ |E(F)| · δ□(Wₙ, V) < |E(F)| · (ε/|E(F)|) = ε
      calc |homDensity F (W n) - homDensity F V|
          ≤ F.edgeFinset.card * cutDistance (W n) V := homDensity_sub_le_of_cutDistance F (W n) V
        _ < F.edgeFinset.card * (ε / F.edgeFinset.card) := by
            apply mul_lt_mul_of_pos_left (hN n hn) hcard_pos
        _ = ε := mul_div_cancel₀ ε (ne_of_gt hcard_pos)
  · -- Backward direction: inverse counting lemma + compactness
    intro hconv
    -- Step 1: Extract convergent subsequence by compactness
    obtain ⟨V, φ, hφ_mono, hφ_conv⟩ := compact W
    -- Step 2: By counting lemma (forward), the subsequence's hom densities converge to V's
    -- Step 3: By uniqueness of convergent subsequence limits, the full sequence converges
    -- V is the limit: show ∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W n) V < ε
    -- Use cutDistance_tendsto_iff_homDensity_tendsto (backward direction)
    refine ⟨V, ?_⟩
    rw [show (∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W n) V < ε) ↔
        (∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
         ∀ ε > 0, ∃ N, ∀ n ≥ N, |homDensity F (W n) - homDensity F V| < ε) from
      cutDistance_tendsto_iff_homDensity_tendsto W V]
    -- Need: ∀ k F on Fin k, ∀ ε > 0, ∃ N, ∀ n ≥ N, |t(F, W n) - t(F, V)| < ε
    intro k F _ ε hε
    -- hconv gives: ∃ L_F, hom densities of W converge to L_F
    -- hφ_conv + counting lemma: hom densities of W ∘ φ converge to t(F, V)
    -- By uniqueness: L_F = t(F, V)
    -- So the full sequence hom densities converge to t(F, V)
    -- Get the limit L_F from hconv
    obtain ⟨L_F, hL_F⟩ := hconv k F
    -- Show L_F = homDensity F V by using the subsequence
    have hL_eq : L_F = homDensity F V := by
      -- The subsequence W ∘ φ → V in cutDistance
      -- By counting lemma: homDensity F (W (φ n)) → homDensity F V
      -- But also homDensity F (W (φ n)) → L_F (subsequence of convergent sequence)
      -- By uniqueness of limits: L_F = homDensity F V
      by_contra h_ne
      set δ := |L_F - homDensity F V| / 2 with hδ_def
      have hδ_pos : δ > 0 := div_pos (abs_pos.mpr (sub_ne_zero.mpr h_ne)) two_pos
      -- Get N₁ such that |t(F, W n) - L_F| < δ for n ≥ N₁
      obtain ⟨N₁, hN₁⟩ := hL_F δ hδ_pos
      -- Get N₂ such that |t(F, W(φ n)) - t(F, V)| < δ for n ≥ N₂
      -- (from counting lemma applied to convergent subsequence)
      by_cases hF_card : F.edgeFinset.card = 0
      · -- Empty graph case: all homDensity F U are equal (constant integrand)
        have h_empty : F.edgeFinset = ∅ := Finset.card_eq_zero.mp hF_card
        have h_const : ∀ (U : Graphon α μ), homDensity F U = ∫ _ : Fin k → α, 1 ∂Measure.pi (fun _ => μ) := by
          intro U; simp [homDensity_eq_integral, homDensityIntegrand, h_empty]
        -- Since all hom densities are equal, L_F must be this constant
        -- and homDensity F V is also this constant, so L_F = homDensity F V
        apply h_ne
        specialize hN₁ N₁ (le_refl _)
        rw [h_const (W N₁), abs_sub_comm] at hN₁
        -- hN₁ : |L_F - ∫ 1| < δ
        -- Unfold δ = |L_F - homDensity F V| / 2 and rewrite homDensity F V
        rw [hδ_def, h_const V] at hN₁
        -- hN₁ : |L_F - ∫ 1| < |L_F - ∫ 1| / 2
        rw [h_const V]
        linarith [abs_nonneg (L_F - ∫ _ : Fin k → α, (1 : ℝ) ∂Measure.pi (fun _ => μ))]
      · have hcard_pos : (0 : ℝ) < F.edgeFinset.card :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero hF_card)
        obtain ⟨N₂, hN₂⟩ := hφ_conv (δ / F.edgeFinset.card) (div_pos hδ_pos hcard_pos)
        set n := max N₁ N₂
        have h1 : |homDensity F (W (φ n)) - L_F| < δ :=
          hN₁ (φ n) (le_trans (le_trans (le_max_left _ _) (hφ_mono.id_le n)) (le_refl _))
        have h2 : |homDensity F (W (φ n)) - homDensity F V| < δ := by
          calc |homDensity F (W (φ n)) - homDensity F V|
              ≤ F.edgeFinset.card * cutDistance (W (φ n)) V :=
                homDensity_sub_le_of_cutDistance F (W (φ n)) V
            _ < F.edgeFinset.card * (δ / F.edgeFinset.card) := by
                apply mul_lt_mul_of_pos_left (hN₂ n (le_max_right _ _)) hcard_pos
            _ = δ := mul_div_cancel₀ δ (ne_of_gt hcard_pos)
        -- |L_F - t(F,V)| ≤ |L_F - t(F, W(φn))| + |t(F, W(φn)) - t(F,V)| < δ + δ = 2δ
        -- But 2δ = |L_F - t(F,V)|, so |L_F - t(F,V)| < |L_F - t(F,V)|, contradiction
        have h3 : |L_F - homDensity F V| ≤
            |L_F - homDensity F (W (φ n))| + |homDensity F (W (φ n)) - homDensity F V| := by
          calc |L_F - homDensity F V|
              = |(L_F - homDensity F (W (φ n))) + (homDensity F (W (φ n)) - homDensity F V)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
        rw [abs_sub_comm] at h1
        linarith
    rw [hL_eq] at hL_F
    exact hL_F ε hε

/-- Convergent sequences are Cauchy. -/
theorem IsConvergent.isCauchy [StandardBorelSpace α] [NoAtoms μ] (W : ℕ → Graphon α μ) (h : IsConvergent W) :
    IsCauchy W := by
  obtain ⟨V, hV⟩ := h
  intro ε hε
  obtain ⟨N, hN⟩ := hV (ε / 2) (half_pos hε)
  use N
  intro m n hm hn
  calc cutDistance (W m) (W n)
      ≤ cutDistance (W m) V + cutDistance V (W n) := cutDistance_triangle (W m) V (W n)
    _ = cutDistance (W m) V + cutDistance (W n) V := by rw [cutDistance_symm V (W n)]
    _ < ε / 2 + ε / 2 := add_lt_add (hN m hm) (hN n hn)
    _ = ε := add_halves ε

/-- Cauchy sequences are convergent (completeness). -/
theorem IsCauchy.isConvergent [StandardBorelSpace α] [NoAtoms μ] (W : ℕ → Graphon α μ) (h : IsCauchy W) :
    IsConvergent W := by
  obtain ⟨V, hV⟩ := complete W h
  exact ⟨V, hV⟩

/-- Cauchy ⟺ Convergent (on standard Borel spaces). -/
theorem isCauchy_iff_isConvergent [StandardBorelSpace α] [NoAtoms μ] (W : ℕ → Graphon α μ) :
    IsCauchy W ↔ IsConvergent W :=
  ⟨IsCauchy.isConvergent W, fun h => h.isCauchy W⟩

end EquivalentConvergence

/-! ### Compactness characterization -/

section CompactnessChar

variable [IsProbabilityMeasure μ] [StandardBorelSpace α]

/-- Every sequence has a convergent subsequence (sequential compactness). -/
theorem exists_convergent_subsequence [NoAtoms μ] (W : ℕ → Graphon α μ) :
    ∃ (V : Graphon α μ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W (φ n)) V < ε :=
  compact W

omit [StandardBorelSpace α] in
/-- The limit of a convergent sequence is unique up to weak isomorphism. -/
theorem limit_unique [StandardBorelSpace α] [NoAtoms μ] (W : ℕ → Graphon α μ) (U V : Graphon α μ)
    (hU : ∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W n) U < ε)
    (hV : ∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W n) V < ε) :
    WeaklyIsomorphic U V :=
  limit_unique_upto_weakIso W U V hU hV

end CompactnessChar

/-! ### Summary theorems -/

section Summary

variable [IsProbabilityMeasure μ]

/-- **Main Theorem**: Characterization of graph limit convergence.

The following are equivalent:
1. Cut distance convergence to some graphon W
2. All homomorphism densities converge
3. The sequence is Cauchy in cut distance

Moreover, any convergent sequence has a unique limit up to weak isomorphism,
and every sequence has a convergent subsequence.

**Hypothesis**: Requires `[StandardBorelSpace α]` for the Cauchy ↔ Convergent equivalence. -/
theorem graphLimit_characterization [StandardBorelSpace α] [NoAtoms μ] (W : ℕ → Graphon α μ) :
    (IsConvergent W ↔ HasConvergentHomDensities W) ∧
    (IsConvergent W ↔ IsCauchy W) ∧
    (∃ (φ : ℕ → ℕ), StrictMono φ ∧ IsConvergent (W ∘ φ)) :=
  ⟨converges_iff_homDensity W,
   (isCauchy_iff_isConvergent W).symm,
   let ⟨_, φ, hφ, hconv⟩ := exists_convergent_subsequence W
   ⟨φ, hφ, ⟨_, hconv⟩⟩⟩

end Summary

end Graphon
