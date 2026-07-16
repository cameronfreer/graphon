/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.SamplingFinite
import Graphon.InjectionCounting

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
* `Graphon.homDensity_ofSimpleGraphOn_eq_t` / `Graphon.sampleMass_ofSimpleGraphOn_eq` — the
  bridges: on the empirical graphon of `H`, the homomorphism density *is* `t`, and the
  sampling mass *is* the normalized exact-pullback count.

The Möbius relations among the three densities and the quantitative `t` vs `t_inj`
comparison are the second half of #94.
-/

open Finset MeasureTheory

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
`n.descFactorial k` injective vertex maps that are homomorphisms. -/
noncomputable def tInj (F : SimpleGraph (Fin k)) (H : SimpleGraph (Fin n)) : ℝ :=
  injHomCount F H / (n.descFactorial k : ℝ)

/-- **The induced density** `t_ind(F, H)`: the proportion of the `n.descFactorial k`
injective vertex maps that induce exactly `F`. -/
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

end SimpleGraph

/-! ### Bridges to the finite graphon-sampling formulas -/

namespace Graphon

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
  [StandardBorelSpace α] [NullSingletonClass μ]

/-- **The homomorphism density of the empirical graphon is `t`**: on the equipartition step
graphon of `H`, the analytic homomorphism density coincides with the combinatorial
density. -/
theorem homDensity_ofSimpleGraphOn_eq_t {n : ℕ} [NeZero n] (H : SimpleGraph (Fin n))
    {k : ℕ} (F : SimpleGraph (Fin k)) [DecidableRel F.Adj] :
    homDensity F (ofSimpleGraphOn (α := α) (μ := μ) H) = SimpleGraph.t F H := by
  rw [homDensity_ofSimpleGraphOn, SimpleGraph.t, SimpleGraph.homCount, Finset.sum_boole,
    inv_pow, inv_mul_eq_div]

/-- **The sampling mass of the empirical graphon is the normalized exact-pullback count**:
the probability that the `k`-sample of the empirical graphon of `H` equals `G` is the
proportion of all vertex maps pulling `H` back to exactly `G`. -/
theorem sampleMass_ofSimpleGraphOn_eq {n : ℕ} [NeZero n] (H : SimpleGraph (Fin n))
    {k : ℕ} (G : SimpleGraph (Fin k)) :
    sampleMass (ofSimpleGraphOn (α := α) (μ := μ) H) G =
      SimpleGraph.pullbackCount G H / (n : ℝ) ^ k := by
  rw [sampleMass_ofSimpleGraphOn, SimpleGraph.pullbackCount, Finset.sum_boole,
    inv_pow, inv_mul_eq_div]

end Graphon
