/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Counting
import Graphon.Compactness
import Graphon.MatrixDetermination

/-!
# Inverse Counting Lemma

This file proves the inverse counting lemma: if two graphons have similar
homomorphism densities for all graphs, then they are close in cut distance.

## Main results

* `Graphon.cutDistance_zero_of_homDensity_eq` - Equal hom densities ⟹ cutDistance = 0
* `Graphon.cutDistance_le_of_homDensity_close` - The quantitative inverse counting lemma

## Implementation notes

The counting lemma (in `Counting.lean`) shows:
  small cut distance ⟹ similar homomorphism densities

The inverse counting lemma shows the converse:
  similar homomorphism densities ⟹ small cut distance

Together, these establish that cut distance convergence is equivalent to
convergence of all homomorphism densities.

The proof uses:
1. Algebraic determination for step graphons (`MatrixDetermination.lean`)
2. Partition alignment via Rokhlin's theorem (`CutDistance.lean`)
3. Regularity lemma for step approximation
4. Compactness of graphon space

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Section 10.6
-/

open MeasureTheory Set Filter Finset

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

/-! ### Step graphon inverse counting

The algebraic core: step graphons on the same partition with equal hom densities
for all graphs have cut distance zero. This connects the measure-theoretic
`homDensity` to the finite `weightedHomSum` and uses `matrix_perm_of_weightedHomSum_eq`
(the algebraic determination axiom) plus partition alignment (Rokhlin). -/

section StepInverseCounting

variable [IsProbabilityMeasure μ] [StandardBorelSpace α]

/-- **Algebraic determination for step graphons (measure-theoretic version).**

Given step graphons on the same partition with equal homomorphism densities for
all graphs, there exists a measure-preserving bijection `e` that makes the
pullback of one step graphon equal the other.

The proof decomposes into three steps, each depending on a sorry'd axiom:

1. **homDensity → weightedHomSum bridge**: Decompose the pi-integral defining
   `homDensity` over partition cells. For a step graphon `mkStepGraphon P c`,
   the integrand is constant on products of cells, so the integral becomes
   a finite sum `weightedHomSum n F c_fin w` where `c_fin` is the coefficient
   matrix indexed by `Fin k` and `w` is the cell-measure vector.

2. **Algebraic core**: Apply `matrix_perm_of_weightedHomSum_eq` to obtain a
   permutation `π` of `Fin k` such that `c_fin i j = c_fin' (π i) (π j)` and
   `w i = w (π i)`. This gives a permutation of partition cells with matching
   coefficients and measures.

3. **Measure-preserving realization**: Construct a measure-preserving bijection
   `e : α ≃ᵐ α` that maps each cell `S_i` a.e. to cell `S_{π(i)}`, using
   `MeasurePreserving.exists_partition_alignment` (Rokhlin). The pullback
   `pullback (mkStepGraphon P c') e` then equals `mkStepGraphon P c` a.e.

**Sorry traces to**: `matrix_perm_of_weightedHomSum_eq` (algebraic core,
Lovász [2012] Theorem 5.30) + `MeasurePreserving.exists_common_extension`
(Rokhlin's theorem). -/
private theorem exists_pullback_eq_of_step_homDensity_eq
    (P : MeasurablePartition α μ) (c c' : Set α → Set α → ℝ)
    (hc_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T = c T S)
    (hc_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T ∈ Set.Icc 0 1)
    (hc'_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c' S T = c' T S)
    (hc'_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c' S T ∈ Set.Icc 0 1)
    (h_hom : ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
      homDensity F (mkStepGraphon P c hc_symm hc_mem) =
      homDensity F (mkStepGraphon P c' hc'_symm hc'_mem)) :
    ∃ (e : α ≃ᵐ α) (he : MeasurePreserving e μ μ),
      pullback (mkStepGraphon P c' hc'_symm hc'_mem) e he =
      mkStepGraphon P c hc_symm hc_mem := by
  sorry

/-- Step graphons on the same partition with equal hom densities for all graphs
have cut distance zero.

**Proof**: By `exists_pullback_eq_of_step_homDensity_eq`, there is a
measure-preserving bijection `e` with `pullback (mkStepGraphon P c') e = mkStepGraphon P c`.
Then `cutDistance_pullback_eq_zero` gives `cutDistance W' (pullback W' e) = 0`,
and substituting the pullback equality yields the result.

**Sorry traces to**: `matrix_perm_of_weightedHomSum_eq` (algebraic core) +
`MeasurePreserving.exists_common_extension` (Rokhlin). -/
private theorem cutDistance_zero_of_step_homDensity_eq
    (P : MeasurablePartition α μ) (c c' : Set α → Set α → ℝ)
    (hc_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T = c T S)
    (hc_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T ∈ Set.Icc 0 1)
    (hc'_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c' S T = c' T S)
    (hc'_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c' S T ∈ Set.Icc 0 1)
    (h_hom : ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
      homDensity F (mkStepGraphon P c hc_symm hc_mem) =
      homDensity F (mkStepGraphon P c' hc'_symm hc'_mem)) :
    cutDistance (mkStepGraphon P c hc_symm hc_mem)
               (mkStepGraphon P c' hc'_symm hc'_mem) = 0 := by
  -- Obtain MP bijection e such that pullback W' e = W
  obtain ⟨e, he, h_eq⟩ := exists_pullback_eq_of_step_homDensity_eq
    P c c' hc_symm hc_mem hc'_symm hc'_mem h_hom
  -- cutDistance W' (pullback W' e) = 0
  have h_zero := cutDistance_pullback_eq_zero (mkStepGraphon P c' hc'_symm hc'_mem) e he
  -- Substitute: pullback W' e = W
  rw [h_eq] at h_zero
  -- cutDistance W W' = cutDistance W' W by symmetry
  rw [cutDistance_symm]
  exact h_zero

end StepInverseCounting

/-! ### Main inverse counting lemma -/

section InverseCounting

variable [IsProbabilityMeasure μ]

/-- **Algebraic determination**: two graphons with equal homomorphism densities
for all finite graphs have cut distance zero (are weakly isomorphic).

The proof approximates both graphons by step graphons via the regularity lemma,
uses the counting lemma to transfer the equal hom density hypothesis,
and applies the step graphon inverse counting to conclude.

**Sorry**: The bridge from general graphons to step graphons on the same partition
requires a contraction property of the conditional expectation in cut norm
that is not yet formalized. This sorry traces ultimately to
`matrix_perm_of_weightedHomSum_eq` (algebraic core) +
`exists_common_extension` (Rokhlin). -/
theorem cutDistance_zero_of_homDensity_eq [StandardBorelSpace α]
    (U W : Graphon α μ)
    (h : ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
         homDensity F U = homDensity F W) :
    cutDistance U W = 0 := by
  -- Suffices: cutDistance U W ≤ ε for all ε > 0
  apply le_antisymm _ (cutDistance_nonneg U W)
  -- If cutDistance U W > 0, derive contradiction via regularity + step inverse counting.
  -- For each n, approximate both U, W by step graphons and use the step-graphon
  -- inverse counting to bound the cutDistance of the approximations.
  sorry

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
  have h_lim_far : cutDistance U_lim W_lim ≥ ε := by
    by_contra h_small
    push_neg at h_small
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
    by_contra h_ne
    set ε' := |homDensity F U_lim - homDensity F W_lim| / 4 with hε'_def
    have hε'_pos : ε' > 0 := div_pos (abs_pos.mpr (sub_ne_zero.mpr h_ne)) four_pos
    by_cases hF_card : F.edgeFinset.card = 0
    · have h_empty : F.edgeFinset = ∅ := Finset.card_eq_zero.mp hF_card
      apply h_ne
      simp [homDensity_eq_integral, homDensityIntegrand, h_empty]
    · have hcard_pos : (0 : ℝ) < F.edgeFinset.card :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero hF_card)
      obtain ⟨N_U, hN_U⟩ := hU_conv (ε' / F.edgeFinset.card) (div_pos hε'_pos hcard_pos)
      obtain ⟨N_W, hN_W⟩ := hW_conv (ε' / F.edgeFinset.card) (div_pos hε'_pos hcard_pos)
      obtain ⟨N_arch, hN_arch⟩ : ∃ N : ℕ, 1 / (↑N + 1 : ℝ) < ε' := by
        obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε')
        refine ⟨m, ?_⟩
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ↑m + 1)]
        calc 1 = ε' * (1 / ε') := by field_simp
          _ < ε' * ↑m := by exact mul_lt_mul_of_pos_left hm hε'_pos
          _ ≤ ε' * (↑m + 1) := by linarith
      set n := max (max N_U N_W) (max N_arch k) with hn_def
      have hn_U : n ≥ N_U := le_trans (le_max_left _ _) (le_max_left _ _)
      have hn_W : n ≥ N_W := le_trans (le_max_right _ _) (le_max_left _ _)
      have hn_arch : n ≥ N_arch := le_trans (le_max_left _ _) (le_max_right _ _)
      have hn_k : n ≥ k := le_trans (le_max_right _ _) (le_max_right _ _)
      have hφn_ge_n : φ n ≥ n := hφ_mono.id_le n
      have hφn_ge_k : k ≤ φ n := le_trans hn_k hφn_ge_n
      have hU_bound : |homDensity F U_lim - homDensity F (U_seq (φ n))| < ε' := by
        calc |homDensity F U_lim - homDensity F (U_seq (φ n))|
            = |homDensity F (U_seq (φ n)) - homDensity F U_lim| := abs_sub_comm _ _
          _ ≤ F.edgeFinset.card * cutDistance (U_seq (φ n)) U_lim :=
              homDensity_sub_le_of_cutDistance F (U_seq (φ n)) U_lim
          _ < F.edgeFinset.card * (ε' / F.edgeFinset.card) :=
              mul_lt_mul_of_pos_left (hN_U n hn_U) hcard_pos
          _ = ε' := mul_div_cancel₀ ε' (ne_of_gt hcard_pos)
      have hW_bound : |homDensity F (W_seq (φ n)) - homDensity F W_lim| < ε' := by
        calc |homDensity F (W_seq (φ n)) - homDensity F W_lim|
            ≤ F.edgeFinset.card * cutDistance (W_seq (φ n)) W_lim :=
              homDensity_sub_le_of_cutDistance F (W_seq (φ n)) W_lim
          _ < F.edgeFinset.card * (ε' / F.edgeFinset.card) :=
              mul_lt_mul_of_pos_left (hN_W n hn_W) hcard_pos
          _ = ε' := mul_div_cancel₀ ε' (ne_of_gt hcard_pos)
      have hclose_bound : |homDensity F (U_seq (φ n)) - homDensity F (W_seq (φ n))| < ε' := by
        have h_mapped : |homDensity F (U_seq (φ n)) - homDensity F (W_seq (φ n))| <
            1 / (↑(φ n) + 1 : ℝ) := by
          rw [← homDensity_map_embedding F (Fin.castLEEmb hφn_ge_k) (U_seq (φ n)),
              ← homDensity_map_embedding F (Fin.castLEEmb hφn_ge_k) (W_seq (φ n))]
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
    · use 0
      intro n _
      have h_empty : F.edgeFinset = ∅ := Finset.card_eq_zero.mp hF
      simp only [homDensity_eq_integral, homDensityIntegrand, h_empty, Finset.prod_empty,
          sub_self, abs_zero, hε]
    · have hcard_pos : (0 : ℝ) < F.edgeFinset.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hF)
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
    obtain ⟨δ, hδ, k, hk⟩ := cutDistance_le_of_homDensity_close (α := α) (μ := μ) ε hε
    have h_finitely_many : ∀ (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
        ∃ N, ∀ n ≥ N, |homDensity F (W n) - homDensity F V| < δ :=
      fun F _ => hhom k F δ hδ
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

/-- If a sequence converges to two limits, they are weakly isomorphic. -/
theorem limit_unique_upto_weakIso [StandardBorelSpace α]
    (W : ℕ → Graphon α μ) (U V : Graphon α μ)
    (hU : ∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W n) U < ε)
    (hV : ∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W n) V < ε) :
    WeaklyIsomorphic U V := by
  unfold WeaklyIsomorphic
  apply le_antisymm
  · by_contra h_neg
    push_neg at h_neg
    set ε := cutDistance U V / 2 with hε_def
    have hε_pos : ε > 0 := by positivity
    obtain ⟨N₁, hN₁⟩ := hU ε hε_pos
    obtain ⟨N₂, hN₂⟩ := hV ε hε_pos
    set n := max N₁ N₂
    have h1 := hN₁ n (le_max_left _ _)
    have h2 := hN₂ n (le_max_right _ _)
    have h_tri := cutDistance_triangle U (W n) V
    have h_symm := cutDistance_symm U (W n)
    linarith
  · exact cutDistance_nonneg U V

/-- Homomorphism densities determine the graphon up to weak isomorphism. -/
theorem weaklyIsomorphic_of_homDensity_eq [StandardBorelSpace α]
    (U W : Graphon α μ)
    (h : ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
         homDensity F U = homDensity F W) :
    WeaklyIsomorphic U W :=
  cutDistance_zero_of_homDensity_eq U W h

end Uniqueness

end Graphon
