/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.InjectionCounting
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Finite subgraph densities: `t`, `t_inj`, `t_ind` (#94, PR 1)

The three classical labeled subgraph densities of a finite target graph (Lovász, *Large
networks and graph limits*, §5.2), with their normalization conventions, and the direct
bridges to this repo's finite graphon-sampling formulas:

* `SimpleGraph.homCount` / `SimpleGraph.t` — adjacency-preserving vertex maps, normalized by
  all `n ^ k` maps (the homomorphism density);
* `SimpleGraph.injHomCount` / `SimpleGraph.tInj` — injective adjacency-preserving maps,
  normalized by the `n.descFactorial k` injective maps;
* `SimpleGraph.indCount` / `SimpleGraph.tInd` — injective maps pulling the target back to
  exactly `F` (labeled induced copies), same normalizer;
* `SimpleGraph.pullbackCount` — the all-maps exact-pullback count, the combinatorial content
  of the sampling mass;
* `SimpleGraph.pullbackCount` is the combinatorial content of the sampling mass; the analytic
  bridges to the empirical-graphon formulas live in `Graphon.SubgraphDensityBridges` (keeping
  this file's import closure to pure combinatorics).

**Small-host convention**: for `n < k` there are no injective maps, `n.descFactorial k = 0`,
and (division by zero being zero) `tInj` and `tInd` are *zero* — recorded as
`tInj_eq_zero_of_lt` / `tInd_eq_zero_of_lt`, which is what makes the Möbius sum identity
unconditional.

PR 2 of #94 adds, still in the pure closure: `tInj_eq_sum_tInd` — the **Möbius sum identity**
`t_inj(F, ·) = ∑_{F' ⊇ F} t_ind(F', ·)` (fiberwise classification of injective homomorphisms
by their exact pullback) — and the **collision comparisons** `abs_t_sub_tInj_le` /
`abs_pullbackCount_div_sub_tInd_le` (`≤ 2k²/n`, from the birthday bound), whose
empirical-graphon forms live in `Graphon.SubgraphDensityBridges`.
-/

open Finset

open scoped Classical

namespace SimpleGraph

variable {k n : ℕ}

/-- **The labeled homomorphism count**: vertex maps carrying every edge of `F` to an edge
of `H`. -/
noncomputable def homCount (F : SimpleGraph (Fin k)) (H : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ.filter fun f : Fin k → Fin n => F ≤ H.comap f).card

/-- **The injective homomorphism count**. -/
noncomputable def injHomCount (F : SimpleGraph (Fin k)) (H : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ.filter fun f : Fin k → Fin n =>
    Function.Injective f ∧ F ≤ H.comap f).card

/-- **The labeled induced-copy count**: injective vertex maps pulling `H` back to
exactly `F`. -/
noncomputable def indCount (F : SimpleGraph (Fin k)) (H : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ.filter fun f : Fin k → Fin n =>
    Function.Injective f ∧ H.comap f = F).card

/-- **The all-maps exact-pullback count** — the combinatorial content of the sampling mass
of the empirical graphon (no injectivity; collisions allowed). -/
noncomputable def pullbackCount (F : SimpleGraph (Fin k)) (H : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ.filter fun f : Fin k → Fin n => H.comap f = F).card

/-- **The homomorphism density** `t(F, H)`: the proportion of all `n ^ k` vertex maps that
are homomorphisms. -/
noncomputable def t (F : SimpleGraph (Fin k)) (H : SimpleGraph (Fin n)) : ℝ :=
  homCount F H / (n : ℝ) ^ k

/-- **The injective homomorphism density** `t_inj(F, H)`: the proportion of the
`n.descFactorial k` injective vertex maps that are homomorphisms. For `n < k` there are no
injective maps and the convention is `tInj = 0` (division by the zero descending factorial). -/
noncomputable def tInj (F : SimpleGraph (Fin k)) (H : SimpleGraph (Fin n)) : ℝ :=
  injHomCount F H / (n.descFactorial k : ℝ)

/-- **The induced density** `t_ind(F, H)`: the proportion of the `n.descFactorial k`
injective vertex maps that induce exactly `F`. For `n < k` there are no injective maps and
the convention is `tInd = 0` (division by the zero descending factorial). -/
noncomputable def tInd (F : SimpleGraph (Fin k)) (H : SimpleGraph (Fin n)) : ℝ :=
  indCount F H / (n.descFactorial k : ℝ)

/-! ### Normalization sanity -/

variable (F : SimpleGraph (Fin k)) (H : SimpleGraph (Fin n))

theorem homCount_le : homCount F H ≤ n ^ k := by
  calc homCount F H ≤ (Finset.univ : Finset (Fin k → Fin n)).card := card_filter_le _ _
    _ = n ^ k := by rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

theorem injHomCount_le : injHomCount F H ≤ n.descFactorial k := by
  rw [← Graphon.card_filter_injective_eq_descFactorial]
  refine card_le_card fun f hf => ?_
  rw [mem_filter] at hf ⊢
  exact ⟨hf.1, hf.2.1⟩

theorem indCount_le : indCount F H ≤ n.descFactorial k := by
  rw [← Graphon.card_filter_injective_eq_descFactorial]
  refine card_le_card fun f hf => ?_
  rw [mem_filter] at hf ⊢
  exact ⟨hf.1, hf.2.1⟩

theorem t_nonneg : 0 ≤ t F H := div_nonneg (Nat.cast_nonneg _) (by positivity)

theorem t_le_one : t F H ≤ 1 := by
  rcases Nat.eq_zero_or_pos (n ^ k) with h | h
  · rw [t, show ((n : ℝ) ^ k) = ((n ^ k : ℕ) : ℝ) by push_cast; ring, h]
    simp
  · rw [t, div_le_one (by exact_mod_cast h)]
    exact_mod_cast homCount_le F H

theorem tInj_nonneg : 0 ≤ tInj F H := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem tInj_le_one : tInj F H ≤ 1 := by
  rcases Nat.eq_zero_or_pos (n.descFactorial k) with h | h
  · rw [tInj, h]
    simp
  · rw [tInj, div_le_one (by exact_mod_cast h)]
    exact_mod_cast injHomCount_le F H

theorem tInd_nonneg : 0 ≤ tInd F H := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem tInd_le_one : tInd F H ≤ 1 := by
  rcases Nat.eq_zero_or_pos (n.descFactorial k) with h | h
  · rw [tInd, h]
    simp
  · rw [tInd, div_le_one (by exact_mod_cast h)]
    exact_mod_cast indCount_le F H

/-! ### The Möbius sum identity and the collision comparison (#94, PR 2) -/

/-- **Fiberwise classification**: an injective homomorphism pulls the host back to a unique
supergraph of `F`, so the injective homomorphism count is the sum of the induced-copy counts
over the supergraphs of `F`. -/
theorem injHomCount_eq_sum_indCount :
    injHomCount F H = ∑ F' ∈ Finset.univ.filter (fun F' : SimpleGraph (Fin k) => F ≤ F'),
      indCount F' H := by
  rw [injHomCount, Finset.card_eq_sum_card_fiberwise
    (f := fun f : Fin k → Fin n => H.comap f)
    (t := Finset.univ.filter fun F' : SimpleGraph (Fin k) => F ≤ F')
    (fun f hf => by
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      exact hf.2)]
  refine Finset.sum_congr rfl fun F' hF' => ?_
  rw [Finset.mem_filter] at hF'
  rw [indCount]
  congr 1
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hinj, -⟩, hcomap⟩
    exact ⟨hinj, hcomap⟩
  · rintro ⟨hinj, hcomap⟩
    exact ⟨⟨hinj, hcomap ▸ hF'.2⟩, hcomap⟩

/-- **The Möbius sum identity**: the injective density is the upper sum of the induced
densities over the supergraphs of `F` — unconditional, thanks to the small-host zero
convention on both sides. -/
theorem tInj_eq_sum_tInd :
    tInj F H = ∑ F' ∈ Finset.univ.filter (fun F' : SimpleGraph (Fin k) => F ≤ F'),
      tInd F' H := by
  simp only [tInj, tInd, injHomCount_eq_sum_indCount F H]
  push_cast
  rw [Finset.sum_div]

/-- The non-injective map count is the complement of the descending factorial. -/
theorem card_filter_not_injective_eq (k n : ℕ) :
    (Finset.univ.filter fun f : Fin k → Fin n => ¬ Function.Injective f).card =
      n ^ k - n.descFactorial k := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin k → Fin n)))
    (p := fun f : Fin k → Fin n => Function.Injective f)
  rw [Graphon.card_filter_injective_eq_descFactorial, card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin] at h
  omega

/-- The generic collision comparison: for any property `P` of vertex maps, the all-maps
proportion and the injective-maps proportion differ by at most twice the non-injective
proportion, which the birthday bound controls by `2k²/n`. -/
private theorem abs_div_pow_sub_div_descFactorial_le (P : (Fin k → Fin n) → Prop) :
    |((Finset.univ.filter P).card : ℝ) / (n : ℝ) ^ k -
        ((Finset.univ.filter fun f => Function.Injective f ∧ P f).card : ℝ) /
          (n.descFactorial k : ℝ)| ≤ 2 * (k : ℝ) ^ 2 / n := by
  have hsubBA : (Finset.univ.filter fun f : Fin k → Fin n => Function.Injective f ∧ P f)
      ⊆ Finset.univ.filter P := fun f hf => by
    rw [Finset.mem_filter] at hf ⊢
    exact ⟨hf.1, hf.2.2⟩
  rcases Nat.eq_zero_or_pos k with hk | hk
  · -- k = 0: every map is injective, the two proportions coincide
    subst hk
    have hall : (Finset.univ.filter fun f : Fin 0 → Fin n => Function.Injective f ∧ P f)
        = Finset.univ.filter P := by
      ext f
      simp [Function.injective_of_subsingleton f]
    rw [hall, Nat.descFactorial_zero, pow_zero]
    simp only [Nat.cast_one, sub_self, abs_zero]
    positivity
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- n = 0 < k: no maps at all
    subst hn
    haveI : IsEmpty (Fin k → Fin 0) := ⟨fun f => (f ⟨0, hk⟩).elim0⟩
    have h1 : (Finset.univ.filter P) = ∅ :=
      Finset.subset_empty.mp ((Finset.filter_subset _ _).trans Finset.univ_eq_empty.subset)
    have h2 : (Finset.univ.filter fun f : Fin k → Fin 0 =>
        Function.Injective f ∧ P f) = ∅ :=
      Finset.subset_empty.mp ((Finset.filter_subset _ _).trans Finset.univ_eq_empty.subset)
    rw [h1, h2]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div, sub_self, abs_zero]
    positivity
  have hN : (0 : ℝ) < (n : ℝ) ^ k := by positivity
  rcases Nat.eq_zero_or_pos (n.descFactorial k) with hd | hd
  · -- n < k: no injective maps; the all-maps proportion is at most 1 ≤ 2k²/n
    have hB : (Finset.univ.filter fun f : Fin k → Fin n =>
        Function.Injective f ∧ P f).card = 0 := by
      have hsub : (Finset.univ.filter fun f : Fin k → Fin n =>
          Function.Injective f ∧ P f) ⊆
          Finset.univ.filter fun f : Fin k → Fin n => Function.Injective f := fun f hf => by
        rw [Finset.mem_filter] at hf ⊢
        exact ⟨hf.1, hf.2.1⟩
      have hle := (Finset.card_le_card hsub).trans_eq
        (Graphon.card_filter_injective_eq_descFactorial k n)
      omega
    rw [hB]
    simp only [Nat.cast_zero, zero_div, sub_zero]
    rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hN.le)]
    have hA1 : ((Finset.univ.filter P).card : ℝ) / (n : ℝ) ^ k ≤ 1 := by
      rw [div_le_one hN]
      have := (Finset.card_filter_le Finset.univ P).trans_eq
        (by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin])
      exact_mod_cast this
    refine hA1.trans ?_
    rw [le_div_iff₀ (by exact_mod_cast hn)]
    have hkn : (n : ℝ) < (k : ℝ) := by
      exact_mod_cast Nat.descFactorial_eq_zero_iff_lt.mp hd
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith [hkn, hk1]
  -- main case: 1 ≤ k ≤ n
  have hdR : (0 : ℝ) < (n.descFactorial k : ℝ) := by exact_mod_cast hd
  have hBd : ((Finset.univ.filter fun f : Fin k → Fin n =>
      Function.Injective f ∧ P f).card : ℝ) ≤ (n.descFactorial k : ℝ) := by
    have hsub : (Finset.univ.filter fun f : Fin k → Fin n =>
        Function.Injective f ∧ P f) ⊆
        Finset.univ.filter fun f : Fin k → Fin n => Function.Injective f := fun f hf => by
      rw [Finset.mem_filter] at hf ⊢
      exact ⟨hf.1, hf.2.1⟩
    exact_mod_cast (Finset.card_le_card hsub).trans_eq
      (Graphon.card_filter_injective_eq_descFactorial k n)
  have hBA : ((Finset.univ.filter fun f : Fin k → Fin n =>
      Function.Injective f ∧ P f).card : ℝ) ≤ ((Finset.univ.filter P).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubBA
  have hdN : (n.descFactorial k : ℝ) ≤ (n : ℝ) ^ k := by
    exact_mod_cast (Nat.descFactorial_le_pow n k).trans_eq (by rfl)
  -- the all-maps count exceeds the injective count by at most the non-injective count
  have hABle : ((Finset.univ.filter P).card : ℝ) -
      ((Finset.univ.filter fun f => Function.Injective f ∧ P f).card : ℝ) ≤
      (n : ℝ) ^ k - (n.descFactorial k : ℝ) := by
    have hsplit : (Finset.univ.filter P).card ≤
        (Finset.univ.filter fun f : Fin k → Fin n => Function.Injective f ∧ P f).card +
          (Finset.univ.filter fun f : Fin k → Fin n => ¬ Function.Injective f).card := by
      have hcover : Finset.univ.filter P ⊆
          (Finset.univ.filter fun f : Fin k → Fin n => Function.Injective f ∧ P f) ∪
            (Finset.univ.filter fun f : Fin k → Fin n => ¬ Function.Injective f) := by
        intro f hf
        rw [Finset.mem_filter] at hf
        rcases Classical.em (Function.Injective f) with hinj | hinj
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hf.1, hinj, hf.2⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hf.1, hinj⟩)
      exact (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    have hnon : ((Finset.univ.filter fun f : Fin k → Fin n =>
        ¬ Function.Injective f).card : ℝ) = (n : ℝ) ^ k - (n.descFactorial k : ℝ) := by
      rw [card_filter_not_injective_eq]
      have hle : n.descFactorial k ≤ n ^ k := Nat.descFactorial_le_pow n k
      push_cast [Nat.cast_sub hle]
      ring
    have := (Nat.cast_le (α := ℝ)).mpr hsplit
    push_cast at this
    linarith [hnon ▸ this]
  -- collision bound in the required form
  have hcoll : (n : ℝ) ^ k - (n.descFactorial k : ℝ) ≤ (k : ℝ) ^ 2 * (n : ℝ) ^ (k - 1) := by
    have hbb := Graphon.card_not_injective_le k n
    have hnon : ((Finset.univ.filter fun f : Fin k → Fin n =>
        ¬ Function.Injective f).card : ℝ) = (n : ℝ) ^ k - (n.descFactorial k : ℝ) := by
      rw [card_filter_not_injective_eq]
      push_cast [Nat.cast_sub (Nat.descFactorial_le_pow n k)]
      ring
    rw [hnon] at hbb
    nlinarith [hbb]
  -- assemble
  set A := ((Finset.univ.filter P).card : ℝ)
  set B := ((Finset.univ.filter fun f => Function.Injective f ∧ P f).card : ℝ)
  set N := (n : ℝ) ^ k
  set d := (n.descFactorial k : ℝ)
  have hB0 : 0 ≤ B := Nat.cast_nonneg _
  have hN' : N ≠ 0 := hN.ne'
  have hd' : d ≠ 0 := hdR.ne'
  have key : |A / N - B / d| ≤ 2 * (N - d) / N := by
    have h1eq : A / N - B / d = (A - B) / N - B * (1 / d - 1 / N) := by
      field_simp
      ring
    have h2nn : 0 ≤ (A - B) / N := div_nonneg (by linarith [hBA]) hN.le
    have h3nn : 0 ≤ B * (1 / d - 1 / N) :=
      mul_nonneg hB0 (sub_nonneg.mpr (one_div_le_one_div_of_le hdR hdN))
    have h1 : (A - B) / N ≤ (N - d) / N := by gcongr
    have h2 : B * (1 / d - 1 / N) ≤ (N - d) / N := by
      calc B * (1 / d - 1 / N) ≤ d * (1 / d - 1 / N) :=
            mul_le_mul_of_nonneg_right hBd
              (sub_nonneg.mpr (one_div_le_one_div_of_le hdR hdN))
        _ = (N - d) / N := by
            field_simp
    have h4nn : 0 ≤ (N - d) / N := div_nonneg (by linarith [hdN]) hN.le
    have h5 : (N - d) / N + (N - d) / N = 2 * (N - d) / N := by ring
    rw [h1eq, abs_sub_le_iff]
    constructor
    · linarith [h1, h2, h3nn, h4nn, h5]
    · linarith [h1, h2, h2nn, h4nn, h5]
  have hfin : 2 * (N - d) / N ≤ 2 * (k : ℝ) ^ 2 / n := by
    have hpow : N = (n : ℝ) ^ (k - 1) * n := by
      show (n : ℝ) ^ k = _
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hk]
      rw [pow_succ, Nat.pred_eq_sub_one]
    calc 2 * (N - d) / N ≤ 2 * ((k : ℝ) ^ 2 * (n : ℝ) ^ (k - 1)) / N := by gcongr
      _ = 2 * (k : ℝ) ^ 2 / n := by
          rw [hpow]
          have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
          have hpow' : (0 : ℝ) < (n : ℝ) ^ (k - 1) := by positivity
          field_simp
  exact key.trans hfin

/-- **The collision comparison** (Lovász, *Large networks and graph limits*, (5.20)-style):
the homomorphism density and the injective homomorphism density differ by at most `2k²/n` —
the birthday bound on the non-injective proportion, applied on both sides of the
normalization change. -/
theorem abs_t_sub_tInj_le : |t F H - tInj F H| ≤ 2 * (k : ℝ) ^ 2 / n :=
  abs_div_pow_sub_div_descFactorial_le fun f => F ≤ H.comap f

/-- **The collision comparison for exact pullbacks**: the all-maps exact-pullback proportion
(the sampling mass of the empirical graphon) and the induced density differ by at most
`2k²/n`. -/
theorem abs_pullbackCount_div_sub_tInd_le :
    |(pullbackCount F H : ℝ) / (n : ℝ) ^ k - tInd F H| ≤ 2 * (k : ℝ) ^ 2 / n :=
  abs_div_pow_sub_div_descFactorial_le fun f => H.comap f = F

/-- **Small-host convention**: `tInj` vanishes when the host is smaller than the pattern. -/
theorem tInj_eq_zero_of_lt (h : n < k) : tInj F H = 0 := by
  rw [tInj, Nat.descFactorial_eq_zero_iff_lt.mpr h]
  simp

/-- **Small-host convention**: `tInd` vanishes when the host is smaller than the pattern. -/
theorem tInd_eq_zero_of_lt (h : n < k) : tInd F H = 0 := by
  rw [tInd, Nat.descFactorial_eq_zero_iff_lt.mpr h]
  simp

end SimpleGraph
