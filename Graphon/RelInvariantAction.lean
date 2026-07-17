/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRestrictionIndependence

/-!
# The finitely-supported relabeling action and its invariant σ-algebra (R3c step 1, #106)

The generic invariant-action layer for the relational extremality theory: the group of
finitely supported sortwise permutations of `ℕ`, the σ-algebra of strictly invariant events,
and ergodicity of an exchangeable relational law:

* `RelSignature.SortwiseFinSupp` — a sortwise family of permutations with common finite
  support, with closure under composition and inverse;
* `RelStructure.invariantAlgebra` — the measurable sets strictly invariant under every
  finitely supported sortwise relabeling;
* `InfiniteRelExchangeableLaw.IsErgodic` — every invariant event has law-measure `0` or `1`.

This mirrors the undirected `Graphon/InvariantAction.lean`; the ergodic ↔ extreme port and
the arrows into the dissociation triangle are the next R3c steps.
-/

open MeasureTheory

namespace RelSignature

variable {S : RelSignature}

/-! ### Finitely supported sortwise permutations -/

/-- **A sortwise family of permutations with common finite support**: beyond some `N`, every
sort's permutation is the identity. -/
def SortwiseFinSupp (σ : ∀ _ : S.Srt, Equiv.Perm ℕ) : Prop :=
  ∃ N, ∀ s (x : ℕ), N ≤ x → σ s x = x

theorem SortwiseFinSupp.one : SortwiseFinSupp (S := S) fun _ => 1 :=
  ⟨0, fun _ _ _ => rfl⟩

theorem SortwiseFinSupp.mul {σ τ : ∀ _ : S.Srt, Equiv.Perm ℕ}
    (hσ : SortwiseFinSupp σ) (hτ : SortwiseFinSupp τ) :
    SortwiseFinSupp fun s => σ s * τ s := by
  obtain ⟨N, hN⟩ := hσ
  obtain ⟨M, hM⟩ := hτ
  refine ⟨max N M, fun s x hx => ?_⟩
  show σ s (τ s x) = x
  rw [hM s x (le_trans (le_max_right N M) hx), hN s x (le_trans (le_max_left N M) hx)]

theorem SortwiseFinSupp.inv {σ : ∀ _ : S.Srt, Equiv.Perm ℕ} (hσ : SortwiseFinSupp σ) :
    SortwiseFinSupp fun s => (σ s)⁻¹ := by
  obtain ⟨N, hN⟩ := hσ
  refine ⟨N, fun s x hx => ?_⟩
  have := hN s x hx
  calc (σ s)⁻¹ x = (σ s)⁻¹ (σ s x) := by rw [this]
    _ = x := (σ s).symm_apply_apply x

/-! ### The invariant σ-algebra -/

/-- **The invariant σ-algebra**: measurable sets strictly invariant under every finitely
supported sortwise relabeling. -/
def RelStructure.invariantAlgebra : MeasurableSpace (RelStructure S (Vinfinite S)) where
  MeasurableSet' A := MeasurableSet A ∧
    ∀ σ, SortwiseFinSupp (S := S) σ → RelStructure.relabel σ ⁻¹' A = A
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ => Set.preimage_empty⟩
  measurableSet_compl := fun A hA => ⟨hA.1.compl, fun σ h => by
    rw [Set.preimage_compl, hA.2 σ h]⟩
  measurableSet_iUnion := fun f hf => ⟨MeasurableSet.iUnion fun i => (hf i).1, fun σ h => by
    rw [Set.preimage_iUnion]
    exact Set.iUnion_congr fun i => (hf i).2 σ h⟩

theorem RelStructure.invariantAlgebra_le :
    RelStructure.invariantAlgebra (S := S) ≤
      (inferInstance : MeasurableSpace (RelStructure S (Vinfinite S))) :=
  fun _ hA => hA.1

/-! ### Ergodicity -/

/-- **Ergodicity** of an exchangeable relational law: every event strictly invariant under
all finitely supported sortwise relabelings has law-measure `0` or `1`. -/
def InfiniteRelExchangeableLaw.IsErgodic (M : InfiniteRelExchangeableLaw S) : Prop :=
  ∀ A, MeasurableSet[RelStructure.invariantAlgebra] A →
    (M.law : Measure (RelStructure S (Vinfinite S))) A = 0 ∨
      (M.law : Measure (RelStructure S (Vinfinite S))) A = 1

end RelSignature
