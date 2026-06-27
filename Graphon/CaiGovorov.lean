/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The Cai–Govorov Vandermonde argument

This file formalizes the elementary "Vandermonde argument" of Cai and Govorov,
*On a Theorem of Lovász that hom(·, H) Determines the Isomorphism Type of H*
(ITCS 2020 / arXiv:1909.03693), §4. These are purely algebraic, graph-free
statements that drive the orbit-separation argument for weighted graphs.

## Main results

* `vandermonde_class_sums_zero` (Cai–Govorov Lemma 4.1): if `∑ i, a i * x i ^ j = 0`
  for all `j < |ι|`, then the coefficient sum over each level set of `x` vanishes
  (equivalently `∑ i, a i * f (x i) = 0` for *every* `f`, see
  `vandermonde_apply_eq_zero`). Crucially the values `x i` need **not** be distinct.

* `multivariate_vandermonde_class_sums_zero` (Cai–Govorov Corollary 4.2): the
  multivariate version. Indices are classified by their `s`-tuple `b i : Fin s → ℝ`;
  if `∑ i, a i * ∏ j, b i j ^ ℓ j = 0` for all exponent tuples `ℓ` bounded by `|ι|`,
  then the coefficient sum over each tuple-class vanishes.

The headline lemmas are stated in "class-sum" (level-set) form. The auxiliary
`*_apply_eq_zero` lemmas give the equivalent "`∀ f`" form which is the convenient
engine for the multivariate induction.
-/

open Finset Matrix

namespace Graphon.CaiGovorov

/-- A Vandermonde nonsingularity corollary over an arbitrary finite index type:
if the values `s i` are distinct and `∑ i, a i * s i ^ n = 0` for all `n < |ι|`,
then all coefficients vanish. -/
theorem vandermonde_coeffs_zero {ι : Type*} [Fintype ι]
    (s : ι → ℝ) (hs : Function.Injective s) (a : ι → ℝ)
    (h : ∀ n : ℕ, n < Fintype.card ι → ∑ i, a i * s i ^ n = 0) : a = 0 := by
  classical
  by_contra ha
  let e := Fintype.equivFin ι
  let s' : Fin (Fintype.card ι) → ℝ := fun k => s (e.symm k)
  let a' : Fin (Fintype.card ι) → ℝ := fun k => a (e.symm k)
  have hs' : Function.Injective s' := hs.comp e.symm.injective
  have ha' : a' ≠ 0 := by
    intro h0
    apply ha
    funext i
    have := congrFun h0 (e i)
    simpa [a', Equiv.symm_apply_apply] using this
  have hdet : (vandermonde s').det ≠ 0 := det_vandermonde_ne_zero_iff.mpr hs'
  have hvec : vecMul a' (vandermonde s') = 0 := by
    funext j
    simp only [vecMul, dotProduct, vandermonde_apply, Pi.zero_apply]
    have hreindex : ∑ k, a' k * s' k ^ (j : ℕ) = ∑ i, a i * s i ^ (j : ℕ) :=
      (Fintype.sum_equiv e (fun i => a i * s i ^ (j : ℕ)) (fun k => a' k * s' k ^ (j : ℕ))
        (fun i => by simp [a', s', Equiv.symm_apply_apply])).symm
    rw [hreindex]; exact h j j.isLt
  exact hdet (exists_vecMul_eq_zero_iff.mp ⟨a', ha', hvec⟩)

/-- Bridge from "level-set coefficient sums vanish" to the `∀ f` form. -/
theorem sum_apply_eq_zero_of_fibers {ι : Type*} [Fintype ι] {α : Type*} [DecidableEq α]
    (v : ι → α) (a : ι → ℝ)
    (h : ∀ c : α, ∑ i ∈ univ.filter (fun i => v i = c), a i = 0)
    (f : α → ℝ) : ∑ i, a i * f (v i) = 0 := by
  classical
  rw [show (∑ i, a i * f (v i)) = ∑ c ∈ univ.image v,
        ∑ i ∈ univ.filter (fun i => v i = c), a i * f (v i) from
      (sum_fiberwise_of_maps_to
        (fun i _ => mem_image_of_mem v (mem_univ i)) _).symm]
  apply sum_eq_zero
  intro c _
  have hfib : ∑ i ∈ univ.filter (fun i => v i = c), a i * f (v i)
       = (∑ i ∈ univ.filter (fun i => v i = c), a i) * f c := by
    rw [Finset.sum_mul]
    apply sum_congr rfl
    intro i hi
    rw [mem_filter] at hi
    rw [hi.2]
  rw [hfib, h c, zero_mul]

/-- Vandermonde nonsingularity over a finite set of distinct real nodes:
if `∑ d ∈ S, A d * d ^ n = 0` for all `n < |S|`, then `A` vanishes on `S`. -/
theorem finset_vandermonde_zero {S : Finset ℝ} (A : ℝ → ℝ)
    (h : ∀ n : ℕ, n < S.card → ∑ d ∈ S, A d * d ^ n = 0) :
    ∀ d ∈ S, A d = 0 := by
  classical
  have hpow : ∀ n : ℕ, n < Fintype.card {d // d ∈ S} →
      ∑ d : {d // d ∈ S}, A d.val * d.val ^ n = 0 := by
    intro n hn
    rw [Fintype.card_coe] at hn
    rw [Finset.sum_coe_sort S (fun d => A d * d ^ n)]
    exact h n hn
  have hz := vandermonde_coeffs_zero (fun d : {d // d ∈ S} => d.val)
      Subtype.val_injective (fun d => A d.val) hpow
  intro d hd
  have := congrFun hz ⟨d, hd⟩
  simpa using this

/-- **Cai–Govorov Lemma 4.1** (Vandermonde argument), level-set form.
If `∑ i, a i * x i ^ j = 0` for all `j < |ι|`, then for every value `c` the
coefficient sum over the level set `{i | x i = c}` vanishes. The values `x i`
need not be distinct. -/
theorem vandermonde_class_sums_zero {ι : Type*} [Fintype ι]
    (x a : ι → ℝ)
    (h : ∀ j : ℕ, j < Fintype.card ι → ∑ i, a i * x i ^ j = 0)
    (c : ℝ) :
    ∑ i ∈ univ.filter (fun i => x i = c), a i = 0 := by
  classical
  have hVcard : (univ.image x).card ≤ Fintype.card ι := by
    calc (univ.image x).card ≤ (univ : Finset ι).card := card_image_le
      _ = Fintype.card ι := card_univ
  have hgroup : ∀ n : ℕ, (∑ d ∈ univ.image x,
          (∑ i ∈ univ.filter (fun i => x i = d), a i) * d ^ n) = ∑ i, a i * x i ^ n := by
    intro n
    rw [← sum_fiberwise_of_maps_to
          (fun i _ => mem_image_of_mem x (mem_univ i))
          (fun i => a i * x i ^ n)]
    apply sum_congr rfl
    intro d _
    rw [Finset.sum_mul]
    apply sum_congr rfl
    intro i hi
    rw [mem_filter] at hi
    rw [hi.2]
  have key : ∀ d ∈ univ.image x,
      (∑ i ∈ univ.filter (fun i => x i = d), a i) = 0 := by
    refine finset_vandermonde_zero
      (fun d => ∑ i ∈ univ.filter (fun i => x i = d), a i) (fun n hn => ?_)
    rw [hgroup n]
    exact h n (lt_of_lt_of_le hn hVcard)
  by_cases hc : c ∈ univ.image x
  · exact key c hc
  · rw [Finset.filter_eq_empty_iff.mpr ?_, Finset.sum_empty]
    intro i _ hxi
    exact hc (hxi ▸ mem_image_of_mem x (mem_univ i))

/-- **Cai–Govorov Lemma 4.1**, `∀ f` form: if `∑ i, a i * x i ^ j = 0` for all
`j < |ι|`, then `∑ i, a i * f (x i) = 0` for *every* function `f`. -/
theorem vandermonde_apply_eq_zero {ι : Type*} [Fintype ι]
    (x a : ι → ℝ)
    (h : ∀ j : ℕ, j < Fintype.card ι → ∑ i, a i * x i ^ j = 0)
    (f : ℝ → ℝ) : ∑ i, a i * f (x i) = 0 :=
  sum_apply_eq_zero_of_fibers x a (vandermonde_class_sums_zero x a h) f

/-- **Cai–Govorov Corollary 4.2**, `∀ f` form: the multivariate Vandermonde
argument. If `∑ i, a i * ∏ j, b i j ^ ℓ j = 0` for every exponent tuple `ℓ`
bounded by `|ι|`, then `∑ i, a i * f (b i) = 0` for *every* `f`. -/
theorem multivariate_vandermonde_apply_eq_zero :
    ∀ (s : ℕ) {ι : Type*} [Fintype ι] (b : ι → Fin s → ℝ) (a : ι → ℝ),
      (∀ ℓ : Fin s → ℕ, (∀ j, ℓ j < Fintype.card ι) →
          ∑ i, a i * ∏ j, b i j ^ ℓ j = 0) →
      ∀ f : (Fin s → ℝ) → ℝ, ∑ i, a i * f (b i) = 0 := by
  intro s
  induction s with
  | zero =>
      intro ι _ b a h f
      have hsum : ∑ i, a i = 0 := by
        simpa using h Fin.elim0 (fun j => j.elim0)
      have key : ∀ i, f (b i) = f (fun _ => (0 : ℝ)) := fun i =>
        congrArg f (funext (fun j : Fin 0 => j.elim0))
      calc ∑ i, a i * f (b i)
          = ∑ i, a i * f (fun _ => (0 : ℝ)) := by
              apply sum_congr rfl; intro i _; rw [key i]
        _ = (∑ i, a i) * f (fun _ => (0 : ℝ)) := by rw [Finset.sum_mul]
        _ = 0 := by rw [hsum, zero_mul]
  | succ s ih =>
      intro ι _ b a h f
      -- (†) separation: ∀ g h2, ∑ i, a i * (g (b i 0) * h2 (tail (b i))) = 0
      have hsep : ∀ (g : ℝ → ℝ) (h2 : (Fin s → ℝ) → ℝ),
          ∑ i, a i * (g (b i 0) * h2 (fun j => b i j.succ)) = 0 := by
        intro g h2
        have hyp_tail : ∀ ℓ : Fin s → ℕ, (∀ j, ℓ j < Fintype.card ι) →
            ∑ i, (a i * g (b i 0)) * ∏ j, b i j.succ ^ ℓ j = 0 := by
          intro ℓ hℓ
          -- univariate `∀ f` form on values `b · 0`, coefficients `a · * ∏ tail`
          have hstepA : ∀ n : ℕ, n < Fintype.card ι →
              ∑ i, (a i * ∏ j, b i j.succ ^ ℓ j) * (b i 0) ^ n = 0 := by
            intro n hn
            have hbnd : ∀ j, (Fin.cons n ℓ : Fin (s + 1) → ℕ) j < Fintype.card ι := by
              intro j
              refine Fin.cases ?_ ?_ j
              · simpa using hn
              · intro j'; simpa using hℓ j'
            have heq : ∑ i, (a i * ∏ j, b i j.succ ^ ℓ j) * (b i 0) ^ n
                     = ∑ i, a i * ∏ j : Fin (s + 1), b i j ^ (Fin.cons n ℓ) j := by
              apply sum_congr rfl
              intro i _
              rw [Fin.prod_univ_succ]
              simp only [Fin.cons_zero, Fin.cons_succ]
              ring
            rw [heq]
            exact h (Fin.cons n ℓ) hbnd
          have happ := vandermonde_apply_eq_zero (fun i => b i 0)
              (fun i => a i * ∏ j, b i j.succ ^ ℓ j) hstepA g
          have hreorder : ∑ i, (a i * g (b i 0)) * ∏ j, b i j.succ ^ ℓ j
                        = ∑ i, (a i * ∏ j, b i j.succ ^ ℓ j) * g (b i 0) := by
            apply sum_congr rfl; intro i _; ring
          rw [hreorder]; exact happ
        have htail := ih (fun i j => b i j.succ) (fun i => a i * g (b i 0)) hyp_tail h2
        have hassoc : ∑ i, a i * (g (b i 0) * h2 (fun j => b i j.succ))
                    = ∑ i, (a i * g (b i 0)) * h2 (fun j => b i j.succ) := by
          apply sum_congr rfl; intro i _; ring
        rw [hassoc]; exact htail
      -- finish: classify by `v i = (b i 0, tail (b i))`, recover all of `f (b i)`
      have hfib : ∀ pq : ℝ × (Fin s → ℝ),
          ∑ i ∈ univ.filter (fun i => (b i 0, fun j => b i j.succ) = pq), a i = 0 := by
        intro pq
        have hsep' := hsep (fun y => if y = pq.1 then (1 : ℝ) else 0)
                           (fun y => if y = pq.2 then (1 : ℝ) else 0)
        rw [Finset.sum_filter]
        have hcongr : ∑ i, (if (b i 0, fun j => b i j.succ) = pq then a i else 0)
             = ∑ i, a i * ((if b i 0 = pq.1 then (1 : ℝ) else 0)
                          * (if (fun j => b i j.succ) = pq.2 then (1 : ℝ) else 0)) := by
          apply sum_congr rfl
          intro i _
          by_cases h1 : b i 0 = pq.1 <;>
            by_cases h2 : (fun j => b i j.succ) = pq.2 <;>
            simp [h1, h2, Prod.ext_iff]
        rw [hcongr]; exact hsep'
      have hgoal := sum_apply_eq_zero_of_fibers
          (fun i => (b i 0, fun j => b i j.succ)) a hfib
          (fun pq => f (Fin.cons pq.1 pq.2))
      have heqg : ∑ i, a i * f (b i)
                = ∑ i, a i * f (Fin.cons (b i 0) (fun j => b i j.succ)) := by
        apply sum_congr rfl
        intro i _
        congr 2
        exact (Fin.cons_self_tail (b i)).symm
      rw [heqg]; exact hgoal

/-- **Cai–Govorov Corollary 4.2**, level-set form. Indices are classified by their
tuple `b i`; under the bounded power-sum hypothesis, the coefficient sum over each
tuple-class vanishes. -/
theorem multivariate_vandermonde_class_sums_zero {s : ℕ} {ι : Type*} [Fintype ι]
    (b : ι → Fin s → ℝ) (a : ι → ℝ)
    (h : ∀ ℓ : Fin s → ℕ, (∀ j, ℓ j < Fintype.card ι) →
        ∑ i, a i * ∏ j, b i j ^ ℓ j = 0)
    (β : Fin s → ℝ) :
    ∑ i ∈ univ.filter (fun i => b i = β), a i = 0 := by
  classical
  have happ := multivariate_vandermonde_apply_eq_zero s b a h
    (fun y => if y = β then (1 : ℝ) else 0)
  rw [Finset.sum_filter]
  calc ∑ i, (if b i = β then a i else 0)
      = ∑ i, a i * (if b i = β then (1 : ℝ) else 0) := by
        apply sum_congr rfl; intro i _; by_cases hi : b i = β <;> simp [hi]
    _ = 0 := happ

/-- Univariate Lemma 4.1 with an explicit bound `N` on the number of distinct values of `x`
(in place of `|ι|`). -/
theorem vandermonde_class_sums_zero_of_bound {ι : Type*} [Fintype ι]
    (x a : ι → ℝ) (N : ℕ) (hN : (univ.image x).card ≤ N)
    (h : ∀ j : ℕ, j < N → ∑ i, a i * x i ^ j = 0) (c : ℝ) :
    ∑ i ∈ univ.filter (fun i => x i = c), a i = 0 := by
  classical
  have hgroup : ∀ n : ℕ, (∑ d ∈ univ.image x,
          (∑ i ∈ univ.filter (fun i => x i = d), a i) * d ^ n) = ∑ i, a i * x i ^ n := by
    intro n
    rw [← sum_fiberwise_of_maps_to
          (fun i _ => mem_image_of_mem x (mem_univ i))
          (fun i => a i * x i ^ n)]
    apply sum_congr rfl
    intro d _
    rw [Finset.sum_mul]
    apply sum_congr rfl
    intro i hi
    rw [mem_filter] at hi
    rw [hi.2]
  have key : ∀ d ∈ univ.image x,
      (∑ i ∈ univ.filter (fun i => x i = d), a i) = 0 := by
    refine finset_vandermonde_zero
      (fun d => ∑ i ∈ univ.filter (fun i => x i = d), a i) (fun n hn => ?_)
    rw [hgroup n]
    exact h n (lt_of_lt_of_le hn hN)
  by_cases hc : c ∈ univ.image x
  · exact key c hc
  · rw [Finset.filter_eq_empty_iff.mpr ?_, Finset.sum_empty]
    intro i _ hxi
    exact hc (hxi ▸ mem_image_of_mem x (mem_univ i))

/-- Univariate ∀f form with an explicit distinct-value bound. -/
theorem vandermonde_apply_eq_zero_of_bound {ι : Type*} [Fintype ι]
    (x a : ι → ℝ) (N : ℕ) (hN : (univ.image x).card ≤ N)
    (h : ∀ j : ℕ, j < N → ∑ i, a i * x i ^ j = 0) (f : ℝ → ℝ) :
    ∑ i, a i * f (x i) = 0 :=
  sum_apply_eq_zero_of_fibers x a (vandermonde_class_sums_zero_of_bound x a N hN h) f

/-- Multivariate ∀f form with a UNIFORM bound `M` such that every coordinate `j` of the
profile `b` takes at most `M` distinct values. -/
theorem multivariate_vandermonde_apply_eq_zero_of_bound :
    ∀ (s : ℕ) {ι : Type*} [Fintype ι] (b : ι → Fin s → ℝ) (a : ι → ℝ) (M : ℕ),
      (∀ j, (univ.image (fun i => b i j)).card ≤ M) →
      (∀ ℓ : Fin s → ℕ, (∀ j, ℓ j < M) → ∑ i, a i * ∏ j, b i j ^ ℓ j = 0) →
      ∀ f : (Fin s → ℝ) → ℝ, ∑ i, a i * f (b i) = 0 := by
  intro s
  induction s with
  | zero =>
      intro ι _ b a M hM h f
      have hsum : ∑ i, a i = 0 := by
        simpa using h Fin.elim0 (fun j => j.elim0)
      have key : ∀ i, f (b i) = f (fun _ => (0 : ℝ)) := fun i =>
        congrArg f (funext (fun j : Fin 0 => j.elim0))
      calc ∑ i, a i * f (b i)
          = ∑ i, a i * f (fun _ => (0 : ℝ)) := by
              apply sum_congr rfl; intro i _; rw [key i]
        _ = (∑ i, a i) * f (fun _ => (0 : ℝ)) := by rw [Finset.sum_mul]
        _ = 0 := by rw [hsum, zero_mul]
  | succ s ih =>
      intro ι _ b a M hM h f
      -- (†) separation: ∀ g h2, ∑ i, a i * (g (b i 0) * h2 (tail (b i))) = 0
      have hsep : ∀ (g : ℝ → ℝ) (h2 : (Fin s → ℝ) → ℝ),
          ∑ i, a i * (g (b i 0) * h2 (fun j => b i j.succ)) = 0 := by
        intro g h2
        have hyp_tail : ∀ ℓ : Fin s → ℕ, (∀ j, ℓ j < M) →
            ∑ i, (a i * g (b i 0)) * ∏ j, b i j.succ ^ ℓ j = 0 := by
          intro ℓ hℓ
          -- univariate `∀ f` form on values `b · 0`, coefficients `a · * ∏ tail`
          have hstepA : ∀ n : ℕ, n < M →
              ∑ i, (a i * ∏ j, b i j.succ ^ ℓ j) * (b i 0) ^ n = 0 := by
            intro n hn
            have hbnd : ∀ j, (Fin.cons n ℓ : Fin (s + 1) → ℕ) j < M := by
              intro j
              refine Fin.cases ?_ ?_ j
              · simpa using hn
              · intro j'; simpa using hℓ j'
            have heq : ∑ i, (a i * ∏ j, b i j.succ ^ ℓ j) * (b i 0) ^ n
                     = ∑ i, a i * ∏ j : Fin (s + 1), b i j ^ (Fin.cons n ℓ) j := by
              apply sum_congr rfl
              intro i _
              rw [Fin.prod_univ_succ]
              simp only [Fin.cons_zero, Fin.cons_succ]
              ring
            rw [heq]
            exact h (Fin.cons n ℓ) hbnd
          have happ := vandermonde_apply_eq_zero_of_bound (fun i => b i 0)
              (fun i => a i * ∏ j, b i j.succ ^ ℓ j) M (hM 0) hstepA g
          have hreorder : ∑ i, (a i * g (b i 0)) * ∏ j, b i j.succ ^ ℓ j
                        = ∑ i, (a i * ∏ j, b i j.succ ^ ℓ j) * g (b i 0) := by
            apply sum_congr rfl; intro i _; ring
          rw [hreorder]; exact happ
        have htail := ih (fun i j => b i j.succ) (fun i => a i * g (b i 0)) M
          (fun j => hM j.succ) hyp_tail h2
        have hassoc : ∑ i, a i * (g (b i 0) * h2 (fun j => b i j.succ))
                    = ∑ i, (a i * g (b i 0)) * h2 (fun j => b i j.succ) := by
          apply sum_congr rfl; intro i _; ring
        rw [hassoc]; exact htail
      -- finish: classify by `v i = (b i 0, tail (b i))`, recover all of `f (b i)`
      have hfib : ∀ pq : ℝ × (Fin s → ℝ),
          ∑ i ∈ univ.filter (fun i => (b i 0, fun j => b i j.succ) = pq), a i = 0 := by
        intro pq
        have hsep' := hsep (fun y => if y = pq.1 then (1 : ℝ) else 0)
                           (fun y => if y = pq.2 then (1 : ℝ) else 0)
        rw [Finset.sum_filter]
        have hcongr : ∑ i, (if (b i 0, fun j => b i j.succ) = pq then a i else 0)
             = ∑ i, a i * ((if b i 0 = pq.1 then (1 : ℝ) else 0)
                          * (if (fun j => b i j.succ) = pq.2 then (1 : ℝ) else 0)) := by
          apply sum_congr rfl
          intro i _
          by_cases h1 : b i 0 = pq.1 <;>
            by_cases h2 : (fun j => b i j.succ) = pq.2 <;>
            simp [h1, h2, Prod.ext_iff]
        rw [hcongr]; exact hsep'
      have hgoal := sum_apply_eq_zero_of_fibers
          (fun i => (b i 0, fun j => b i j.succ)) a hfib
          (fun pq => f (Fin.cons pq.1 pq.2))
      have heqg : ∑ i, a i * f (b i)
                = ∑ i, a i * f (Fin.cons (b i 0) (fun j => b i j.succ)) := by
        apply sum_congr rfl
        intro i _
        congr 2
        exact (Fin.cons_self_tail (b i)).symm
      rw [heqg]; exact hgoal

/-- Multivariate level-set form with a uniform distinct-value bound `M`. -/
theorem multivariate_vandermonde_class_sums_zero_of_bound {s : ℕ} {ι : Type*} [Fintype ι]
    (b : ι → Fin s → ℝ) (a : ι → ℝ) (M : ℕ)
    (hM : ∀ j, (univ.image (fun i => b i j)).card ≤ M)
    (h : ∀ ℓ : Fin s → ℕ, (∀ j, ℓ j < M) → ∑ i, a i * ∏ j, b i j ^ ℓ j = 0)
    (β : Fin s → ℝ) :
    ∑ i ∈ univ.filter (fun i => b i = β), a i = 0 := by
  classical
  have happ := multivariate_vandermonde_apply_eq_zero_of_bound s b a M hM h
    (fun y => if y = β then (1 : ℝ) else 0)
  rw [Finset.sum_filter]
  calc ∑ i, (if b i = β then a i else 0)
      = ∑ i, a i * (if b i = β then (1 : ℝ) else 0) := by
        apply sum_congr rfl; intro i _; by_cases hi : b i = β <;> simp [hi]
    _ = 0 := happ

end Graphon.CaiGovorov
