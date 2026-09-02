/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRankLatents
import Graphon.RelObservationGeometry
import Graphon.RelFixingAlgebra

/-!
# Localizing latent events at a support (R4 converse, #107)

Source-level machinery for the fixing-completeness API: an event of the latent cube that is
almost surely invariant under the permutations fixing `A` should have a representative reading
only the latent coordinates **visible at `A`**.

The layer is deliberately **route-neutral**. Nothing here mentions a `RankRepresentation`, an
exchangeable law, or a coherent basis, and the module sits strictly below the representation
contract so that the contract can consume it. In particular:

* invariance is accepted **almost everywhere**, not strictly. Strictifying it through an invariant
  hull would need countability of the relabeling group, hence `[Fintype S.Srt]`, which this layer
  does not have and should not acquire;
* there is no `A.card < n` hypothesis — that restriction belongs to the representation theorem
  built on top, not to the statement about the source.

This file currently holds the combinatorial input.

## Finite displacement

The load-bearing geometric fact: any finite family of latent indices can be pushed off itself, in
its nonlocal part, by one finitely supported sortwise permutation fixing `A` pointwise. Only the
finite union of the tagged supports of `A` and of the family is active, so every sort outside that
union takes the identity and no finiteness hypothesis on the sort type is introduced — the same
active-sort discipline as the finite-support agreement lemma it is built from.
-/

open MeasureTheory

namespace RelSignature

universe u

variable {S : RelSignature.{u}} {n : ℕ}

/-- **Finite displacement.** Any finite family of latent indices can be moved off itself, in its
nonlocal part, by a single finitely supported sortwise permutation fixing `A` pointwise.

Only the finite union of the tagged supports of `A` and of the family is active, so every sort
outside that union takes the identity and no finiteness hypothesis on the sort type is needed. -/
theorem exists_finSuppPerm_displacing (A : Finset (Σ s : S.Srt, Vinfinite S s))
    (F : Finset (RankLatentIndex S n)) :
    ∃ σ : FinSuppPerm S, SortwiseFixing A σ.1 ∧
      ∀ B ∈ F, ¬ (B.1 ⊆ A) → rankLatentIndexEquiv σ n B ∉ F := by
  classical
  -- the active tagged vertices, and a bound strictly above all of them
  set V : Finset (Σ s : S.Srt, Vinfinite S s) := A ∪ F.biUnion (fun B => B.1) with hV
  set Nb : ℕ := (V.sup fun v => v.2) + 1 with hNb
  have hlt : ∀ v ∈ V, v.2 < Nb := fun v hv =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun w : Σ s : S.Srt, Vinfinite S s => w.2) hv)
  have hAV : A ⊆ V := Finset.subset_union_left
  -- shift every active non-`A` vertex above the bound, fixing `A`
  have hinj : ∀ s : S.Srt, Function.Injective
      (fun v : ℕ => if (⟨s, v⟩ : Σ s : S.Srt, Vinfinite S s) ∈ A then v else v + Nb) := by
    intro s a b hab
    simp only at hab
    by_cases ha : (⟨s, a⟩ : Σ s : S.Srt, Vinfinite S s) ∈ A <;>
      by_cases hb : (⟨s, b⟩ : Σ s : S.Srt, Vinfinite S s) ∈ A
    · rw [if_pos ha, if_pos hb] at hab
      exact hab
    · rw [if_pos ha, if_neg hb] at hab
      have h1 : (a : ℕ) < Nb := hlt ⟨s, a⟩ (hAV ha)
      omega
    · rw [if_neg ha, if_pos hb] at hab
      have h1 : (b : ℕ) < Nb := hlt ⟨s, b⟩ (hAV hb)
      omega
    · rw [if_neg ha, if_neg hb] at hab
      omega
  obtain ⟨σ, hσ⟩ := exists_finSuppPerm_agree_on_finset
    (fun s => ⟨_, hinj s⟩ : ∀ s, Vinfinite S s ↪ Vinfinite S s) V
  have hσV : ∀ v ∈ V, σ.1 v.1 v.2 =
      if (⟨v.1, v.2⟩ : Σ s : S.Srt, Vinfinite S s) ∈ A then v.2 else v.2 + Nb :=
    fun v hv => hσ v hv
  refine ⟨σ, ⟨σ.2, fun v hv => ?_⟩, fun B hB hBA hmem => ?_⟩
  · rw [hσV v (hAV hv), if_pos (by simpa using hv)]
  · -- a vertex of `B` outside `A` is pushed above the bound, so the image leaves `V`
    obtain ⟨w, hwB, hwA⟩ := Finset.not_subset.mp hBA
    have hwV : w ∈ V := Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨B, hB, hwB⟩)
    have himg : (Sigma.map id (fun s => ⇑(σ.1 s)) w : Σ s : S.Srt, Vinfinite S s)
        ∈ (rankLatentIndexEquiv σ n B).1 := Finset.mem_image_of_mem _ hwB
    have hmemV : (Sigma.map id (fun s => ⇑(σ.1 s)) w : Σ s : S.Srt, Vinfinite S s) ∈ V :=
      Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨rankLatentIndexEquiv σ n B, hmem, himg⟩)
    have hval : (Sigma.map id (fun s => ⇑(σ.1 s)) w).2 = w.2 + Nb := by
      show σ.1 w.1 w.2 = w.2 + Nb
      rw [hσV w hwV, if_neg (by simpa using hwA)]
    have hbound := hlt _ hmemV
    rw [hval] at hbound
    exact absurd hbound (Nat.not_lt.mpr (Nat.le_add_left Nb w.2))

end RelSignature
