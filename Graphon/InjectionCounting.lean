/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Counting vertex maps: the birthday bound and injective-map counts (#94, shared infrastructure)

Pure finite combinatorics about maps `Fin k → Fin n`, extracted from the mixture-existence
collision estimate so the `t`/`t_inj`/`t_ind` subgraph-density interlude (#94) can share it:

* `Graphon.card_not_injective_le` — the union (birthday) bound: at most `k² · n^(k−1)` maps are
  non-injective;
* `Graphon.card_noninjective_div_card_le` — the proportion form, `≤ k²/(n + 1)`;
* `Graphon.inv_pow_eq_card_inv` — the inverse-power sampling weight is the reciprocal
  vertex-map count;
* `Graphon.card_filter_injective_eq_descFactorial` — the injective-map count is the descending
  factorial `n.descFactorial k` (the normalizer of `t_inj`/`t_ind`).
-/

namespace Graphon

/-- **The union (birthday) bound**: at most a `k²/m` proportion of vertex maps
`Fin k → Fin m` are non-injective. -/
theorem card_not_injective_le (k m : ℕ) :
    ((Finset.univ.filter fun f : Fin k → Fin m => ¬ Function.Injective f).card : ℝ) ≤
      (k * k : ℝ) * (m : ℝ) ^ (k - 1) := by
  classical
  have hsub : (Finset.univ.filter fun f : Fin k → Fin m => ¬ Function.Injective f) ⊆
      Finset.univ.offDiag.biUnion (fun ij =>
        Finset.univ.filter fun f : Fin k → Fin m => f ij.1 = f ij.2) := by
    intro f hf
    rw [Finset.mem_filter] at hf
    rw [Function.not_injective_iff] at hf
    obtain ⟨i, j, hfij, hij⟩ := hf.2
    exact Finset.mem_biUnion.mpr ⟨(i, j),
      Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hij⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfij⟩⟩
  have hpair : ∀ ij : Fin k × Fin k, ij ∈ Finset.univ.offDiag →
      (Finset.univ.filter fun f : Fin k → Fin m => f ij.1 = f ij.2).card ≤
        m ^ (k - 1) := by
    rintro ⟨i, j⟩ hij
    have hne : i ≠ j := (Finset.mem_offDiag.mp hij).2.2
    have hinj : Set.InjOn (fun f : Fin k → Fin m => fun v : {x : Fin k // x ≠ j} => f v)
        ↑(Finset.univ.filter fun f : Fin k → Fin m => f i = f j) := by
      intro f hf g hg hfg
      have hf2 : f i = f j := (Finset.mem_filter.mp (Finset.mem_coe.mp hf)).2
      have hg2 : g i = g j := (Finset.mem_filter.mp (Finset.mem_coe.mp hg)).2
      funext v
      by_cases hv : v = j
      · subst hv
        have hi : f i = g i := congrFun hfg ⟨i, hne⟩
        rw [← hf2, ← hg2]
        exact hi
      · exact congrFun hfg ⟨v, hv⟩
    calc (Finset.univ.filter fun f : Fin k → Fin m => f i = f j).card
        ≤ Fintype.card ({x : Fin k // x ≠ j} → Fin m) :=
          Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
      _ = m ^ (k - 1) := by
          rw [Fintype.card_fun, Fintype.card_fin]
          congr 1
          simp [Fintype.card_subtype_compl]
  calc ((Finset.univ.filter fun f : Fin k → Fin m => ¬ Function.Injective f).card : ℝ)
      ≤ ((Finset.univ.offDiag.biUnion (fun ij =>
          Finset.univ.filter fun f : Fin k → Fin m => f ij.1 = f ij.2)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ ij ∈ Finset.univ.offDiag,
          ((Finset.univ.filter fun f : Fin k → Fin m => f ij.1 = f ij.2).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _ij ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)), ((m : ℝ)) ^ (k - 1) := by
        refine Finset.sum_le_sum fun ij hij => ?_
        exact_mod_cast hpair ij hij
    _ ≤ (k * k : ℝ) * (m : ℝ) ^ (k - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : ((Finset.univ.offDiag : Finset (Fin k × Fin k)).card : ℝ) ≤
            (k * k : ℝ) := by
          have hn : (Finset.univ.offDiag : Finset (Fin k × Fin k)).card ≤ k * k := by
            rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
            omega
          exact_mod_cast hn
        have hnn : (0 : ℝ) ≤ (m : ℝ) ^ (k - 1) := by positivity
        exact mul_le_mul_of_nonneg_right hcard hnn

/-- The inverse-power sampling weight is the reciprocal vertex-map count. -/
theorem inv_pow_eq_card_inv (n k : ℕ) :
    ((n + 1 : ℕ) : ℝ)⁻¹ ^ k = (Fintype.card (Fin k → Fin (n + 1)) : ℝ)⁻¹ := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, inv_pow]
  push_cast
  rfl

/-- The non-injective proportion of vertex maps is at most `k²/(n + 1)` (birthday bound
plus arithmetic). -/
theorem card_noninjective_div_card_le (n k : ℕ) :
    ((Finset.univ.filter fun f : Fin k → Fin (n + 1) =>
        ¬ Function.Injective f).card : ℝ) /
      (Fintype.card (Fin k → Fin (n + 1)) : ℝ) ≤ (k * k : ℝ) / (n + 1) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [Finset.filter_false_of_mem fun f _ =>
      not_not_intro (Function.injective_of_subsingleton f)]
    simp
  · have hcnt := card_not_injective_le k (n + 1)
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast at hcnt ⊢
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc ((Finset.univ.filter fun f : Fin k → Fin (n + 1) =>
            ¬ Function.Injective f).card : ℝ) * ((n : ℝ) + 1)
        ≤ ((k : ℝ) * k * ((n : ℝ) + 1) ^ (k - 1)) * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hcnt (by positivity)
      _ = (k : ℝ) * k * ((n : ℝ) + 1) ^ k := by
          rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hk]

/-- **The injective-map count is the descending factorial**: there are exactly
`n.descFactorial k` injective maps `Fin k → Fin n` — the normalizer of the injective and
induced subgraph densities. -/
theorem card_filter_injective_eq_descFactorial (k n : ℕ) :
    (Finset.univ.filter fun f : Fin k → Fin n => Function.Injective f).card =
      n.descFactorial k := by
  classical
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fin n)),
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]

end Graphon
