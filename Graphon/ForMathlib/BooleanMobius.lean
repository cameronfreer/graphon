/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Choose.Sum

/-!
# Möbius inversion on a finite Boolean lattice

This file pins the upper-transform convention used for graph parameters independently of graphs.
For `s ⊆ t`, the inverse coefficient is `(-1) ^ #(t \ s)`: the exponent counts elements
*added* to the lower set.  The small executable examples at the end guard this orientation.
-/

open Finset

namespace Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The upper zeta transform on the Boolean lattice of subsets of a finite type. -/
def booleanUpperZeta (p : Finset I → ℚ) (s : Finset I) : ℚ :=
  ∑ t : Finset I, if s ⊆ t then p t else 0

/-- The signed upper Möbius transform.  Its sign counts elements added above `s`. -/
def booleanUpperMobius (p : Finset I → ℚ) (s : Finset I) : ℚ :=
  ∑ t : Finset I, if s ⊆ t then (-1 : ℚ) ^ (t \ s).card * p t else 0

private theorem sum_Icc_neg_one_pow_sdiff (s u : Finset I) :
    ∑ t ∈ Icc s u, (-1 : ℚ) ^ (t \ s).card = if u = s then 1 else 0 := by
  by_cases hsu : s ⊆ u
  · rw [Icc_eq_image_powerset hsu, sum_image]
    · calc
        (∑ v ∈ (u \ s).powerset, (-1 : ℚ) ^ #((s ∪ v) \ s)) =
            ∑ v ∈ (u \ s).powerset, (-1 : ℚ) ^ v.card := by
              refine sum_congr rfl fun v hv => ?_
              rw [mem_powerset] at hv
              rw [union_sdiff_cancel_left]
              exact disjoint_left.mpr fun x hxs hxv =>
                (mem_sdiff.mp (hv hxv)).2 hxs
        _ = if u \ s = ∅ then 1 else 0 := by
              exact_mod_cast (sum_powerset_neg_one_pow_card (x := u \ s))
        _ = if u = s then 1 else 0 := by
              by_cases hus : u = s
              · subst u
                simp
              · rw [if_neg hus, if_neg]
                exact fun hdiff => hus (le_antisymm (sdiff_eq_empty_iff_subset.mp hdiff) hsu)
    · intro a ha b hb hab
      change a ∈ (u \ s).powerset at ha
      change b ∈ (u \ s).powerset at hb
      rw [mem_powerset] at ha hb
      have hda : Disjoint s a := disjoint_sdiff_self_left.symm.mono_right ha
      have hdb : Disjoint s b := disjoint_sdiff_self_left.symm.mono_right hb
      calc
        a = (s ∪ a) \ s := (union_sdiff_cancel_left hda).symm
        _ = (s ∪ b) \ s := congrArg (fun x => x \ s) hab
        _ = b := union_sdiff_cancel_left hdb
  · rw [Icc_eq_empty hsu, sum_empty, if_neg]
    exact fun hus => hsu hus.symm.le

/-- The signed upper Möbius transform inverts the upper zeta transform. -/
theorem booleanUpperMobius_booleanUpperZeta (p : Finset I → ℚ) :
    booleanUpperMobius (booleanUpperZeta p) = p := by
  funext s
  rw [booleanUpperMobius]
  simp_rw [booleanUpperZeta, mul_sum]
  have hexpand :
      (∑ t : Finset I,
          if s ⊆ t then ∑ u : Finset I, (-1 : ℚ) ^ #(t \ s) * if t ⊆ u then p u else 0
            else 0) =
        ∑ t : Finset I, ∑ u : Finset I,
          if s ⊆ t then (-1 : ℚ) ^ #(t \ s) * (if t ⊆ u then p u else 0) else 0 := by
    refine sum_congr rfl fun t _ => ?_
    by_cases hst : s ⊆ t <;> simp [hst]
  rw [hexpand, sum_comm]
  calc
    (∑ u : Finset I, ∑ t : Finset I,
        if s ⊆ t then (-1 : ℚ) ^ (t \ s).card * (if t ⊆ u then p u else 0) else 0)
        = ∑ u : Finset I,
            (∑ t ∈ Icc s u, (-1 : ℚ) ^ (t \ s).card) * p u := by
          refine sum_congr rfl fun u _ => ?_
          have hIcc : Icc s u = univ.filter (fun t : Finset I => s ⊆ t ∧ t ⊆ u) := by
            ext t
            simp
          rw [sum_mul, hIcc, sum_filter]
          refine sum_congr rfl fun t _ => ?_
          by_cases hst : s ⊆ t <;> by_cases htu : t ⊆ u <;> simp [hst, htu]
    _ = ∑ u : Finset I, (if u = s then 1 else 0) * p u := by
          apply sum_congr rfl
          intro u _
          rw [sum_Icc_neg_one_pow_sdiff]
    _ = p s := by simp

/-! Executable convention regressions. -/

private example : booleanUpperMobius (booleanUpperZeta (fun s : Finset (Fin 3) => s.card)) =
    fun s => s.card := booleanUpperMobius_booleanUpperZeta _

private example :
    booleanUpperMobius (fun s : Finset (Fin 2) => if s = univ then 1 else 0) ∅ = 1 := by
  norm_num [booleanUpperMobius]

private example :
    booleanUpperMobius (fun s : Finset (Fin 1) => if s = univ then 1 else 0) ∅ = -1 := by
  norm_num [booleanUpperMobius]

end Finset
