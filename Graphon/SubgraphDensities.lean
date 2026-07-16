/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.InjectionCounting
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Combinatorics.SimpleGraph.Finite
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
  of the sampling mass; the analytic
  bridges to the empirical-graphon formulas live in `Graphon.SubgraphDensityBridges` (keeping
  this file's import closure to pure combinatorics).

**Small-host convention**: for `n < k` there are no injective maps, `n.descFactorial k = 0`,
and (division by zero being zero) `tInj` and `tInd` are *zero* — recorded as
`tInj_eq_zero_of_lt` / `tInd_eq_zero_of_lt`, which is what makes the Möbius sum identity
unconditional.

PR 2 of #94 adds, still in the pure closure (source crosswalk: Lovász, *Large networks and
graph limits*, §5.2.3): `tInj_eq_sum_tInd` — the **zeta identity** (5.19),
`t_inj(F, ·) = ∑_{F' ⊇ F} t_ind(F', ·)`; `tInd_eq_sum_neg_one_pow_tInj` — the **inverse
Möbius identity** (5.20), `t_ind(F, ·) = ∑_{F' ⊇ F} (−1)^{|E(F') ∖ E(F)|} t_inj(F', ·)`;
and the **collision comparisons** (5.21) `abs_t_sub_tInj_le` /
`abs_pullbackCount_div_sub_tInd_le` (`≤ k²/n`), whose empirical-graphon forms live in
`Graphon.SubgraphDensityBridges`.
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

/-- Edges added on top of a graph's edge set survive `fromEdgeSet` intact: no diagonal
casualties, since both parts are genuine edges. -/
private theorem edgeSet_fromEdgeSet_union (F : SimpleGraph (Fin k))
    (S : Finset (Sym2 (Fin k))) (hS : ∀ e ∈ S, ¬ e.IsDiag) :
    (SimpleGraph.fromEdgeSet (↑(F.edgeFinset ∪ S) : Set (Sym2 (Fin k)))).edgeSet =
      ↑(F.edgeFinset ∪ S) := by
  rw [SimpleGraph.edgeSet_fromEdgeSet, sdiff_eq_left]
  rw [Set.disjoint_left]
  intro e he
  rw [Finset.coe_union, Set.mem_union] at he
  rcases he with he | he
  · exact fun hd => (SimpleGraph.not_isDiag_of_mem_edgeSet F
      (SimpleGraph.mem_edgeFinset.mp (Finset.mem_coe.mp he))) hd
  · exact fun hd => hS e (Finset.mem_coe.mp he) hd

/-- **The alternating interval sum**: over the graphs between `F` and `C`, the signed count
by added edges collapses to the indicator of `C = F` (the Boolean-lattice Möbius kernel). -/
private theorem sum_interval_neg_one_pow (F C : SimpleGraph (Fin k)) :
    ∑ F' ∈ Finset.univ.filter (fun F' : SimpleGraph (Fin k) => F ≤ F' ∧ F' ≤ C),
      (-1 : ℝ) ^ (F'.edgeFinset \ F.edgeFinset).card = if C = F then 1 else 0 := by
  by_cases hFC : F ≤ C
  · have hbij : ∑ F' ∈ Finset.univ.filter (fun F' : SimpleGraph (Fin k) => F ≤ F' ∧ F' ≤ C),
        (-1 : ℝ) ^ (F'.edgeFinset \ F.edgeFinset).card =
        ∑ S ∈ (C.edgeFinset \ F.edgeFinset).powerset, (-1 : ℝ) ^ S.card := by
      refine Finset.sum_nbij' (i := fun F' => F'.edgeFinset \ F.edgeFinset)
        (j := fun S => SimpleGraph.fromEdgeSet ↑(F.edgeFinset ∪ S)) ?_ ?_ ?_ ?_ ?_
      · intro F' hF'
        rw [Finset.mem_filter] at hF'
        exact Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff
          (SimpleGraph.edgeFinset_mono hF'.2.2) le_rfl)
      · intro S hS
        rw [Finset.mem_powerset] at hS
        have hSne : ∀ e ∈ S, ¬ e.IsDiag := fun e he =>
          SimpleGraph.not_isDiag_of_mem_edgeSet C
            (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hS he)).1)
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · rw [← SimpleGraph.edgeSet_subset_edgeSet, edgeSet_fromEdgeSet_union F S hSne,
            Finset.coe_union, SimpleGraph.coe_edgeFinset]
          exact Set.subset_union_left
        · rw [← SimpleGraph.edgeSet_subset_edgeSet, edgeSet_fromEdgeSet_union F S hSne,
            Finset.coe_union, SimpleGraph.coe_edgeFinset]
          refine Set.union_subset (SimpleGraph.edgeSet_mono hFC) fun e he =>
            SimpleGraph.mem_edgeFinset.mp
              (Finset.mem_sdiff.mp (hS (Finset.mem_coe.mp he))).1
      · intro F' hF'
        rw [Finset.mem_filter] at hF'
        rw [Finset.union_sdiff_of_subset (SimpleGraph.edgeFinset_mono hF'.2.1),
          SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet]
      · intro S hS
        rw [Finset.mem_powerset] at hS
        have hSne : ∀ e ∈ S, ¬ e.IsDiag := fun e he =>
          SimpleGraph.not_isDiag_of_mem_edgeSet C
            (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hS he)).1)
        apply Finset.coe_injective
        rw [Finset.coe_sdiff, SimpleGraph.coe_edgeFinset, edgeSet_fromEdgeSet_union F S hSne,
          Finset.coe_union, SimpleGraph.coe_edgeFinset,
          Set.union_sdiff_cancel_left (Set.disjoint_iff.mp (Set.disjoint_left.mpr fun e heF heS =>
            (Finset.mem_sdiff.mp (hS (Finset.mem_coe.mp heS))).2
              (SimpleGraph.mem_edgeFinset.mpr heF)))]
      · intro F' _
        rfl
    rw [hbij]
    have hz : (∑ S ∈ (C.edgeFinset \ F.edgeFinset).powerset, (-1 : ℝ) ^ S.card) =
        if C.edgeFinset \ F.edgeFinset = ∅ then 1 else 0 := by
      exact_mod_cast (Finset.sum_powerset_neg_one_pow_card
        (x := C.edgeFinset \ F.edgeFinset))
    rw [hz]
    congr 1
    rw [eq_iff_iff, Finset.sdiff_eq_empty_iff_subset,
      SimpleGraph.edgeFinset_subset_edgeFinset]
    exact ⟨fun h => le_antisymm h hFC, fun h => h.le⟩
  · rw [Finset.filter_false_of_mem fun F' _ hcon => hFC (hcon.1.trans hcon.2),
      Finset.sum_empty, if_neg fun hcon => hFC (le_of_eq hcon.symm)]

/-- **The inverse Möbius identity** (Lovász (5.20)): the induced density is the signed sum of
the injective densities over the supergraphs, with sign the parity of the added edges —
unconditional, by the small-host zero convention. -/
theorem tInd_eq_sum_neg_one_pow_tInj :
    tInd F H = ∑ F' ∈ Finset.univ.filter (fun F' : SimpleGraph (Fin k) => F ≤ F'),
      (-1 : ℝ) ^ (F'.edgeFinset \ F.edgeFinset).card * tInj F' H := by
  have hexp : ∀ F' : SimpleGraph (Fin k), ((injHomCount F' H : ℝ)) =
      ∑ f ∈ Finset.univ.filter (fun f : Fin k → Fin n => Function.Injective f),
        if F' ≤ H.comap f then (1 : ℝ) else 0 := by
    intro F'
    rw [Finset.sum_boole, injHomCount, Finset.filter_filter]
  have hnum : ((indCount F H : ℝ)) =
      ∑ F' ∈ Finset.univ.filter (fun F' : SimpleGraph (Fin k) => F ≤ F'),
        (-1 : ℝ) ^ (F'.edgeFinset \ F.edgeFinset).card * (injHomCount F' H : ℝ) := by
    simp_rw [hexp, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hinner : ∀ f : Fin k → Fin n,
        (∑ F' ∈ Finset.univ.filter (fun F' : SimpleGraph (Fin k) => F ≤ F'),
          (-1 : ℝ) ^ (F'.edgeFinset \ F.edgeFinset).card *
            (if F' ≤ H.comap f then (1 : ℝ) else 0)) =
        if H.comap f = F then (1 : ℝ) else 0 := by
      intro f
      rw [← sum_interval_neg_one_pow F (H.comap f)]
      simp only [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter, Finset.filter_filter]
    refine Eq.symm ?_
    calc (∑ f ∈ Finset.univ.filter (fun f : Fin k → Fin n => Function.Injective f),
          ∑ F' ∈ Finset.univ.filter (fun F' : SimpleGraph (Fin k) => F ≤ F'),
            (-1 : ℝ) ^ (F'.edgeFinset \ F.edgeFinset).card *
              (if F' ≤ H.comap f then (1 : ℝ) else 0))
        = ∑ f ∈ Finset.univ.filter (fun f : Fin k → Fin n => Function.Injective f),
            (if H.comap f = F then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl fun f _ => hinner f
      _ = ((indCount F H : ℝ)) := by
          rw [Finset.sum_boole, indCount, Finset.filter_filter]
  simp only [tInd, tInj]
  rw [hnum, Finset.sum_div]
  exact Finset.sum_congr rfl fun F' _ => by rw [mul_div_assoc]

/-- The generic collision comparison: for any property `P` of vertex maps, the all-maps
proportion and the injective-maps proportion differ by at most twice the non-injective
proportion's contribution on each side of the normalization change, which the birthday bound
controls by `k²/n`. (Lovász (5.21) states the sharper `choose k 2 / n`; the ordered-pair
union bound here gives `k²`.) -/
private theorem abs_div_pow_sub_div_descFactorial_le (P : (Fin k → Fin n) → Prop) :
    |((Finset.univ.filter P).card : ℝ) / (n : ℝ) ^ k -
        ((Finset.univ.filter fun f => Function.Injective f ∧ P f).card : ℝ) /
          (n.descFactorial k : ℝ)| ≤ (k : ℝ) ^ 2 / n := by
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
      rw [Graphon.card_filter_not_injective_eq]
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
      rw [Graphon.card_filter_not_injective_eq]
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
  have key : |A / N - B / d| ≤ (N - d) / N := by
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
    rw [h1eq, abs_sub_le_iff]
    constructor
    · linarith [h1, h2, h2nn, h3nn]
    · linarith [h1, h2, h2nn, h3nn]
  have hfin : (N - d) / N ≤ (k : ℝ) ^ 2 / n := by
    have hpow : N = (n : ℝ) ^ (k - 1) * n := by
      show (n : ℝ) ^ k = _
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hk]
      rw [pow_succ, Nat.pred_eq_sub_one]
    calc (N - d) / N ≤ ((k : ℝ) ^ 2 * (n : ℝ) ^ (k - 1)) / N := by gcongr
      _ = (k : ℝ) ^ 2 / n := by
          rw [hpow]
          have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
          have hpow' : (0 : ℝ) < (n : ℝ) ^ (k - 1) := by positivity
          field_simp
  exact key.trans hfin

/-- **The collision comparison** (Lovász, *Large networks and graph limits*, (5.21)-style):
the homomorphism density and the injective homomorphism density differ by at most `k²/n` —
both sides of the decomposition are bounded by the non-injective proportion, which the
birthday bound controls. -/
theorem abs_t_sub_tInj_le : |t F H - tInj F H| ≤ (k : ℝ) ^ 2 / n :=
  abs_div_pow_sub_div_descFactorial_le fun f => F ≤ H.comap f

/-- **The collision comparison for exact pullbacks**: the all-maps exact-pullback proportion
(the sampling mass of the empirical graphon) and the induced density differ by at most
`k²/n`. -/
theorem abs_pullbackCount_div_sub_tInd_le :
    |(pullbackCount F H : ℝ) / (n : ℝ) ^ k - tInd F H| ≤ (k : ℝ) ^ 2 / n :=
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
