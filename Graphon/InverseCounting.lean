/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Counting
import Graphon.Compactness

/-!
# Inverse Counting Lemma

This file proves the inverse counting lemma: if two graphons have similar
homomorphism densities for all graphs, then they are close in cut distance.

## Main results

* `Graphon.cutDistance_le_of_homDensity_close` - The inverse counting lemma

## Implementation notes

The counting lemma (in `Counting.lean`) shows:
  small cut distance ⟹ similar homomorphism densities

The inverse counting lemma shows the converse:
  similar homomorphism densities ⟹ small cut distance

Together, these establish that cut distance convergence is equivalent to
convergence of all homomorphism densities.

The proof uses:
1. Regularity lemma to approximate by step graphons
2. Counting lemma for step graphons
3. Compactness argument

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Section 10.6
-/

open MeasureTheory Set Filter Finset

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

/-! ### Inverse counting lemma -/

section InverseCounting

variable [IsProbabilityMeasure μ]

/-- Algebraic determination of graphons by homomorphism densities:
for any `ε > 0`, if two graphons have equal homomorphism densities for all finite
graphs, then their cut distance is at most `ε`.

**Sorry**: This is the core hard step of the inverse counting lemma
(Lovász [2012] Theorem 10.31). The proof requires:
1. Regularity lemma to approximate U, W by step graphons S_U, S_W
2. Counting lemma to show S_U, S_W have approximately equal hom densities
3. **Algebraic determination**: step graphon coefficients are uniquely determined
   (up to partition relabeling) by their homomorphism density sequences. This is
   a finite-dimensional moment problem: the polynomials `{t(F, ·) : F graph}`
   separate step functions up to measure-preserving rearrangement.
4. Construction of a near-optimal measure-preserving rearrangement from the
   coefficient matching, yielding small cut distance.

See Borgs--Chayes--Lovász--Sós--Vesztergombi [2008], Theorem 2.3. -/
private theorem cutDistance_le_of_homDensity_eq_aux (U W : Graphon α μ)
    (ε : ℝ) (hε : ε > 0)
    (h : ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
         homDensity F U = homDensity F W) :
    cutDistance U W ≤ ε := by
  sorry

/-- Two graphons with equal homomorphism densities for all graphs have
    cut distance zero (are weakly isomorphic).

This is the strong form of the inverse counting lemma. Quantifies over graphs on
`Fin k` for all `k`, which suffices since every finite graph is isomorphic to one
on `Fin k`.

The proof reduces to `cutDistance_le_of_homDensity_eq_aux`, which captures the
hard algebraic content: homomorphism densities form a complete system of
polynomial invariants for graphons (up to weak isomorphism).
See Lovász [2012], Theorem 10.31 and Borgs--Chayes--Lovász--Sós--Vesztergombi [2008]. -/
theorem cutDistance_zero_of_homDensity_eq
    (U W : Graphon α μ)
    (h : ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
         homDensity F U = homDensity F W) :
    cutDistance U W = 0 := by
  apply le_antisymm _ (cutDistance_nonneg U W)
  -- For any ε > 0, cutDistance U W ≤ ε. Since cutDistance U W ≥ 0, this forces = 0.
  by_contra h_pos
  push_neg at h_pos
  -- h_pos : 0 < cutDistance U W
  have h_half : cutDistance U W / 2 > 0 := by linarith
  have h_le := cutDistance_le_of_homDensity_eq_aux U W (cutDistance U W / 2) h_half h
  linarith

/-- The inverse counting lemma: similar homomorphism densities imply
    small cut distance.

For any ε > 0, there exists δ > 0 and a finite set of graphs F₁,...,Fₖ
such that if |t(Fᵢ, U) - t(Fᵢ, W)| < δ for all i, then δ□(U, W) < ε. -/
theorem cutDistance_le_of_homDensity_close [StandardBorelSpace α] (ε : ℝ) (hε : ε > 0) :
    ∃ (δ : ℝ) (_ : δ > 0) (k : ℕ),
    ∀ (U W : Graphon α μ),
      (∀ (F : SimpleGraph (Fin k)) [DecidableRel F.Adj], |homDensity F U - homDensity F W| < δ) →
      cutDistance U W < ε := by
  -- Proof by contradiction + compactness.
  -- If false, for each n, ∃ U_n W_n with Fin-n hom densities within 1/(n+1) but d ≥ ε.
  -- Extract convergent subsequences; limits have equal hom densities but d ≥ ε, contradiction.
  by_contra h_neg
  push_neg at h_neg
  have h_seq : ∀ n : ℕ, ∃ (U W : Graphon α μ),
      (∀ (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
        |homDensity F U - homDensity F W| < 1 / (↑n + 1 : ℝ)) ∧
      cutDistance U W ≥ ε :=
    fun n => h_neg (1 / (↑n + 1 : ℝ)) (by positivity) n
  choose U_seq W_seq h_close h_far using h_seq
  obtain ⟨U_lim, φ₁, hφ₁_mono, hφ₁_conv⟩ := compact U_seq
  obtain ⟨W_lim, φ₂, hφ₂_mono, hφ₂_conv⟩ := compact (W_seq ∘ φ₁)
  set φ := φ₁ ∘ φ₂ with hφ_def
  have hφ_mono : StrictMono φ := hφ₁_mono.comp hφ₂_mono
  have hU_conv : ∀ ε' > 0, ∃ N, ∀ n ≥ N, cutDistance (U_seq (φ n)) U_lim < ε' := by
    intro ε' hε'; obtain ⟨N, hN⟩ := hφ₁_conv ε' hε'
    exact ⟨N, fun n hn => hN (φ₂ n) (le_trans hn (hφ₂_mono.id_le n))⟩
  have hW_conv : ∀ ε' > 0, ∃ N, ∀ n ≥ N, cutDistance (W_seq (φ n)) W_lim < ε' :=
    fun ε' hε' => hφ₂_conv ε' hε'
  -- The limits have equal hom densities for all graphs (proof uses cutDistance_zero_of_homDensity_eq)
  -- We use the compactness-based contradiction directly:
  -- cutDistance(U_lim, W_lim) must be 0 (all hom densities agree by counting lemma + triangle)
  -- but cutDistance(U_n, W_n) ≥ ε forces cutDistance(U_lim, W_lim) ≥ ε, contradiction.
  --
  -- Show cutDistance(U_lim, W_lim) = 0:
  -- For any ε' > 0, cutDistance(U_lim, W_lim)
  --   ≤ d(U_lim, U(φ n)) + d(U(φ n), W(φ n)) + d(W(φ n), W_lim)  [triangle]
  -- d(U(φ n), W(φ n)) ≤ d(U(φ n), U_lim) + d(U_lim, W_lim) + d(W_lim, W(φ n))
  -- This doesn't directly give d(U_lim, W_lim) = 0.
  -- Instead: d(U_lim, W_lim) ≥ d(U(φ n), W(φ n)) - d(U(φ n), U_lim) - d(W(φ n), W_lim)
  --                           ≥ ε - small - small → ε.
  -- So cutDistance(U_lim, W_lim) ≥ ε.
  -- But we also need to show it's 0, requiring equal hom densities...
  -- Actually, the key contradiction is simpler:
  -- d(U(φn), W(φn)) ≤ d(U(φn), U_lim) + d(U_lim, W_lim) + d(W_lim, W(φn))
  -- By hypothesis, LHS ≥ ε. By convergence, the first and third terms → 0.
  -- So d(U_lim, W_lim) ≥ ε.
  -- Meanwhile, the hom densities of U_lim and W_lim must be equal
  -- (by counting lemma: convergence in cutDistance implies hom density convergence,
  -- and h_close gives the middle term vanishes).
  -- cutDistance_zero_of_homDensity_eq then gives d(U_lim, W_lim) = 0, contradiction.
  --
  -- First establish d(U_lim, W_lim) ≥ ε:
  have h_lim_far : cutDistance U_lim W_lim ≥ ε := by
    by_contra h_small
    push_neg at h_small
    -- d(U_lim, W_lim) < ε. But d(U(φn), W(φn)) ≥ ε and both converge.
    set δ₀ := (ε - cutDistance U_lim W_lim) / 3 with hδ₀_def
    have hδ₀_pos : δ₀ > 0 := by linarith [cutDistance_nonneg U_lim W_lim]
    obtain ⟨N₁, hN₁⟩ := hU_conv δ₀ hδ₀_pos
    obtain ⟨N₂, hN₂⟩ := hW_conv δ₀ hδ₀_pos
    set n := max N₁ N₂
    have := h_far (φ n)
    have := cutDistance_triangle (U_seq (φ n)) U_lim (W_seq (φ n))
    have := cutDistance_triangle U_lim W_lim (W_seq (φ n))
    have := cutDistance_symm W_lim (W_seq (φ n))
    have := hN₁ n (le_max_left _ _)
    have := hN₂ n (le_max_right _ _)
    linarith
  -- Show all Fin-k hom densities of U_lim and W_lim agree, giving d = 0.
  have h_eq_hom : ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
      homDensity F U_lim = homDensity F W_lim := by
    intro k F _
    -- For any ε' > 0, |t(F, U_lim) - t(F, W_lim)| < ε'
    -- by triangle: ≤ |t(F, U_lim) - t(F, U(φn))| + |t(F, U(φn)) - t(F, W(φn))|
    --             + |t(F, W(φn)) - t(F, W_lim)|
    -- First and third → 0 by counting lemma, second → 0 by h_close.
    by_contra h_ne
    set ε' := |homDensity F U_lim - homDensity F W_lim| / 4 with hε'_def
    have hε'_pos : ε' > 0 := div_pos (abs_pos.mpr (sub_ne_zero.mpr h_ne)) four_pos
    -- Get N₁: counting lemma for U subsequence
    by_cases hF_card : F.edgeFinset.card = 0
    · -- Empty graph: homDensity is ∫ 1 for both, hence equal
      have h_empty : F.edgeFinset = ∅ := Finset.card_eq_zero.mp hF_card
      apply h_ne
      simp [homDensity_eq_integral, homDensityIntegrand, h_empty]
    · have hcard_pos : (0 : ℝ) < F.edgeFinset.card :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero hF_card)
      obtain ⟨N_U, hN_U⟩ := hU_conv (ε' / F.edgeFinset.card) (div_pos hε'_pos hcard_pos)
      obtain ⟨N_W, hN_W⟩ := hW_conv (ε' / F.edgeFinset.card) (div_pos hε'_pos hcard_pos)
      -- Need n large enough for: (1) φ n ≥ k, (2) 1/(φ n + 1) < ε',
      -- (3) counting lemma bounds hold for both U and W subsequences.
      -- Get N_arch: for n ≥ N_arch, 1/(n + 1) < ε' (hence 1/(φ n + 1) ≤ 1/(n + 1) < ε')
      obtain ⟨N_arch, hN_arch⟩ : ∃ N : ℕ, 1 / (↑N + 1 : ℝ) < ε' := by
        obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε')
        refine ⟨m, ?_⟩
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ↑m + 1)]
        calc 1 = ε' * (1 / ε') := by field_simp
          _ < ε' * ↑m := by exact mul_lt_mul_of_pos_left hm hε'_pos
          _ ≤ ε' * (↑m + 1) := by linarith
      set n := max (max N_U N_W) (max N_arch k) with hn_def
      -- Key bounds on n
      have hn_U : n ≥ N_U := le_trans (le_max_left _ _) (le_max_left _ _)
      have hn_W : n ≥ N_W := le_trans (le_max_right _ _) (le_max_left _ _)
      have hn_arch : n ≥ N_arch := le_trans (le_max_left _ _) (le_max_right _ _)
      have hn_k : n ≥ k := le_trans (le_max_right _ _) (le_max_right _ _)
      -- φ n ≥ n ≥ k (since φ is strictly monotone)
      have hφn_ge_n : φ n ≥ n := hφ_mono.id_le n
      have hφn_ge_k : k ≤ φ n := le_trans hn_k hφn_ge_n
      -- Bound 1: |t(F, U_lim) - t(F, U(φ n))| ≤ |E| * cutDistance(...) < ε'
      have hU_bound : |homDensity F U_lim - homDensity F (U_seq (φ n))| < ε' := by
        calc |homDensity F U_lim - homDensity F (U_seq (φ n))|
            = |homDensity F (U_seq (φ n)) - homDensity F U_lim| := abs_sub_comm _ _
          _ ≤ F.edgeFinset.card * cutDistance (U_seq (φ n)) U_lim :=
              homDensity_sub_le_of_cutDistance F (U_seq (φ n)) U_lim
          _ < F.edgeFinset.card * (ε' / F.edgeFinset.card) :=
              mul_lt_mul_of_pos_left (hN_U n hn_U) hcard_pos
          _ = ε' := mul_div_cancel₀ ε' (ne_of_gt hcard_pos)
      -- Bound 2: |t(F, W(φ n)) - t(F, W_lim)| < ε'
      have hW_bound : |homDensity F (W_seq (φ n)) - homDensity F W_lim| < ε' := by
        calc |homDensity F (W_seq (φ n)) - homDensity F W_lim|
            ≤ F.edgeFinset.card * cutDistance (W_seq (φ n)) W_lim :=
              homDensity_sub_le_of_cutDistance F (W_seq (φ n)) W_lim
          _ < F.edgeFinset.card * (ε' / F.edgeFinset.card) :=
              mul_lt_mul_of_pos_left (hN_W n hn_W) hcard_pos
          _ = ε' := mul_div_cancel₀ ε' (ne_of_gt hcard_pos)
      -- Bound 3: |t(F, U(φ n)) - t(F, W(φ n))| < ε'
      -- Use h_close (φ n) on F.map (Fin.castLEEmb hφn_ge_k) : SimpleGraph (Fin (φ n))
      -- By homDensity_map_embedding, homDensity (F.map σ) W = homDensity F W.
      have hclose_bound : |homDensity F (U_seq (φ n)) - homDensity F (W_seq (φ n))| < ε' := by
        -- h_close (φ n) gives closeness for all graphs on Fin (φ n).
        -- F.map (Fin.castLEEmb hφn_ge_k) is such a graph.
        -- homDensity_map_embedding: homDensity (F.map f) W = homDensity F W
        -- Apply h_close to the mapped graph, then use the embedding invariance.
        have h_mapped : |homDensity F (U_seq (φ n)) - homDensity F (W_seq (φ n))| <
            1 / (↑(φ n) + 1 : ℝ) := by
          rw [← homDensity_map_embedding F (Fin.castLEEmb hφn_ge_k) (U_seq (φ n)),
              ← homDensity_map_embedding F (Fin.castLEEmb hφn_ge_k) (W_seq (φ n))]
          -- The goal now uses one DecidableRel instance; h_close uses another.
          -- Use homDensity_congr_decRel to align them.
          set F' := F.map (Fin.castLEEmb hφn_ge_k)
          have := h_close (φ n) (F := F')
          rwa [homDensity_congr_decRel F' _ _ (U_seq (φ n)),
               homDensity_congr_decRel F' _ _ (W_seq (φ n))]
        calc |homDensity F (U_seq (φ n)) - homDensity F (W_seq (φ n))|
            < 1 / (↑(φ n) + 1 : ℝ) := h_mapped
          _ ≤ 1 / (↑n + 1 : ℝ) := by
              apply div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 1) (by positivity)
              exact_mod_cast Nat.add_le_add_right hφn_ge_n 1
          _ ≤ 1 / (↑N_arch + 1 : ℝ) := by
              apply div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 1) (by positivity)
              exact_mod_cast Nat.add_le_add_right hn_arch 1
          _ < ε' := hN_arch
      -- Triangle inequality: |t(F, U_lim) - t(F, W_lim)| ≤ bound1 + bound3 + bound2 < 3ε'
      have h_triangle : |homDensity F U_lim - homDensity F W_lim| < 3 * ε' := by
        have h_split : homDensity F U_lim - homDensity F W_lim =
            (homDensity F U_lim - homDensity F (U_seq (φ n))) +
            (homDensity F (U_seq (φ n)) - homDensity F (W_seq (φ n))) +
            (homDensity F (W_seq (φ n)) - homDensity F W_lim) := by ring
        rw [h_split]
        calc |_ + _ + _|
            ≤ |homDensity F U_lim - homDensity F (U_seq (φ n)) +
              (homDensity F (U_seq (φ n)) - homDensity F (W_seq (φ n)))| +
              |homDensity F (W_seq (φ n)) - homDensity F W_lim| := abs_add_le _ _
          _ ≤ (|homDensity F U_lim - homDensity F (U_seq (φ n))| +
              |homDensity F (U_seq (φ n)) - homDensity F (W_seq (φ n))|) +
              |homDensity F (W_seq (φ n)) - homDensity F W_lim| :=
              add_le_add (abs_add_le _ _) le_rfl
          _ < (ε' + ε') + ε' :=
              add_lt_add (add_lt_add hU_bound hclose_bound) hW_bound
          _ = 3 * ε' := by ring
      -- But |t(F, U_lim) - t(F, W_lim)| = 4 * ε', contradiction
      have h_eq_4ε' : |homDensity F U_lim - homDensity F W_lim| = 4 * ε' := by
        simp [hε'_def, mul_div_cancel₀]
      linarith
  have h_zero : cutDistance U_lim W_lim = 0 := cutDistance_zero_of_homDensity_eq U_lim W_lim h_eq_hom
  linarith

/-- Corollary: a sequence converges in cut distance iff all homomorphism
    densities converge.

This is the fundamental characterization of graph limit convergence. -/
theorem cutDistance_tendsto_iff_homDensity_tendsto [StandardBorelSpace α]
    (W : ℕ → Graphon α μ) (V : Graphon α μ) :
    (∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W n) V < ε) ↔
    (∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
     ∀ ε > 0, ∃ N, ∀ n ≥ N, |homDensity F (W n) - homDensity F V| < ε) := by
  constructor
  · -- Forward: counting lemma
    intro hconv k F _ ε hε
    by_cases hF : F.edgeFinset.card = 0
    · -- Empty graph case: homDensity is always 1
      use 0
      intro n _
      have h_empty : F.edgeFinset = ∅ := Finset.card_eq_zero.mp hF
      simp only [homDensity_eq_integral, homDensityIntegrand, h_empty, Finset.prod_empty,
          sub_self, abs_zero, hε]
    · -- Non-empty graph: use counting lemma
      have hcard_pos : (0 : ℝ) < F.edgeFinset.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hF)
      obtain ⟨N, hN⟩ := hconv (ε / F.edgeFinset.card) (div_pos hε hcard_pos)
      use N
      intro n hn
      calc |homDensity F (W n) - homDensity F V|
          ≤ F.edgeFinset.card * cutDistance (W n) V := homDensity_sub_le_of_cutDistance F (W n) V
        _ < F.edgeFinset.card * (ε / F.edgeFinset.card) := by
            apply mul_lt_mul_of_pos_left (hN n hn) hcard_pos
        _ = ε := mul_div_cancel₀ ε (ne_of_gt hcard_pos)
  · -- Backward: inverse counting lemma
    intro hhom ε hε
    -- By cutDistance_le_of_homDensity_close: ∃ δ > 0, k such that
    -- all Fin-k hom densities within δ ⟹ cutDistance < ε
    obtain ⟨δ, hδ, k, hk⟩ := cutDistance_le_of_homDensity_close (α := α) (μ := μ) ε hε
    -- By hypothesis, for each F on Fin k, |t(F, W n) - t(F, V)| → 0
    -- Since there are only finitely many simple graphs on Fin k, we can find N
    -- such that all of them are within δ simultaneously.
    -- For each graph F on Fin k with DecidableRel:
    -- hhom k F gives: ∀ ε > 0, ∃ N, ∀ n ≥ N, |t(F, W n) - t(F, V)| < ε
    -- We need: ∃ N, ∀ n ≥ N, ∀ F on Fin k, |t(F, W n) - t(F, V)| < δ
    -- This follows because there are finitely many graphs on Fin k.
    -- Use the fact that SimpleGraph (Fin k) is Fintype.
    -- For each F : SimpleGraph (Fin k), hhom k F δ hδ gives an N_F.
    -- Take N = max over all F of N_F. Then for n ≥ N, all are within δ.
    -- The max exists because SimpleGraph (Fin k) is finite.
    -- Choose N_F for each F (using classical choice over the finite type)
    have h_finitely_many : ∀ (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
        ∃ N, ∀ n ≥ N, |homDensity F (W n) - homDensity F V| < δ :=
      fun F _ => hhom k F δ hδ
    -- Use classical choice to pick N_F for each F, then take max
    -- Since SimpleGraph (Fin k) is finite, we can take the sup
    classical
    choose N_F hN_F using fun (F : SimpleGraph (Fin k)) =>
      @h_finitely_many F (Classical.decRel _)
    use Finset.univ.sup N_F
    intro n hn
    apply hk
    intro F _
    have := hN_F F n (le_trans (Finset.le_sup (Finset.mem_univ F)) hn)
    convert this

end InverseCounting

/-! ### Uniqueness of limits -/

section Uniqueness

variable [IsProbabilityMeasure μ]

/-- If a sequence converges to two limits, they are weakly isomorphic.

Limits in the graphon space are unique up to weak isomorphism.

**Hypothesis**: Requires `[StandardBorelSpace α]` for the triangle inequality. -/
theorem limit_unique_upto_weakIso [StandardBorelSpace α]
    (W : ℕ → Graphon α μ) (U V : Graphon α μ)
    (hU : ∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W n) U < ε)
    (hV : ∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W n) V < ε) :
    WeaklyIsomorphic U V := by
  -- By triangle inequality: δ□(U, V) ≤ δ□(U, Wₙ) + δ□(Wₙ, V)
  -- Both terms → 0 as n → ∞
  unfold WeaklyIsomorphic
  apply le_antisymm
  · -- cutDistance U V ≤ 0
    -- Show: for all ε > 0, cutDistance U V ≤ ε
    -- Then use le_of_forall_le_of_dense or similar
    by_contra h_neg
    push_neg at h_neg
    -- h_neg : cutDistance U V > 0
    -- Let ε = cutDistance U V / 2
    set ε := cutDistance U V / 2 with hε_def
    have hε_pos : ε > 0 := by linarith
    obtain ⟨N₁, hN₁⟩ := hU ε hε_pos
    obtain ⟨N₂, hN₂⟩ := hV ε hε_pos
    set n := max N₁ N₂ with hn_def
    have hn₁ : n ≥ N₁ := le_max_left N₁ N₂
    have hn₂ : n ≥ N₂ := le_max_right N₁ N₂
    have h1 : cutDistance (W n) U < ε := hN₁ n hn₁
    have h2 : cutDistance (W n) V < ε := hN₂ n hn₂
    have h_tri : cutDistance U V ≤ cutDistance U (W n) + cutDistance (W n) V :=
      cutDistance_triangle U (W n) V
    have h_symm : cutDistance U (W n) = cutDistance (W n) U := cutDistance_symm U (W n)
    have h_bound : cutDistance U V < 2 * ε := by
      calc cutDistance U V
          ≤ cutDistance U (W n) + cutDistance (W n) V := h_tri
        _ = cutDistance (W n) U + cutDistance (W n) V := by rw [h_symm]
        _ < ε + ε := add_lt_add h1 h2
        _ = 2 * ε := by ring
    -- But 2 * ε = cutDistance U V, contradiction
    linarith
  · exact cutDistance_nonneg U V

/-- Homomorphism densities determine the graphon up to weak isomorphism.

If two graphons have identical homomorphism densities for all graphs on
`Fin k` for every `k`, they are weakly isomorphic. -/
theorem weaklyIsomorphic_of_homDensity_eq
    (U W : Graphon α μ)
    (h : ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
         homDensity F U = homDensity F W) :
    WeaklyIsomorphic U W :=
  cutDistance_zero_of_homDensity_eq U W h

end Uniqueness

end Graphon
