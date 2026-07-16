/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelLawEquivalence

/-!
# Sortwise disjoint-block restrictions and finite-event factorization (AHK umbrella, R3a / #106)

The block machinery for the generic relational extremality theory: sortwise vertex shifts and
disjoint-block restrictions of the infinite structure space, the initial / tail / vertex-tail
σ-algebras, invariance of an exchangeable law under arbitrary injective relabelings and under
the shift, and **dissociation** as exact finite-event (block) factorization:

* `RelStructure.drop k` — the sortwise vertex shift (forget the first `k s` vertices of each
  sort), with `shiftEmb k l` the embedding of the next `l`-block after `k`;
* `InfiniteRelExchangeableLaw.law_map_restrict` — the law of **any** sortwise injective
  restriction depends only on the block sizes (extend to a permutation, use exchangeability);
* `InfiniteRelExchangeableLaw.law_map_drop` — shift invariance of the law;
* `RelStructure.initialAlgebra` / `tailAlgebra` / `vertexTailAlgebra` — the σ-algebras of the
  first-block, after-block, and tail events, with monotonicity and
  `iSup_initialAlgebra_eq` (the initial algebras generate);
* `InfiniteRelExchangeableLaw.IsDissociated` — **exact finite-event factorization**: the joint
  law of the first `k`-block and the following `l`-block is the product of the two marginals,
  for all block sizes.

This generalizes the undirected `Graphon/RestrictionIndependence.lean` design to arbitrary
finite-sort, countable-relation signatures. The equivalences (dissociated ↔ restriction-
independent ↔ tail-trivial, and the extreme/ergodic items) are R3b/R3c.
-/

open MeasureTheory RelSignature

namespace RelSignature

variable {S : RelSignature}

/-! ### The sortwise shift and block embeddings -/

/-- **The sortwise vertex shift**: forget the first `k s` vertices of each sort. -/
def RelStructure.drop (k : S.Srt → ℕ) :
    RelStructure S (Vinfinite S) → RelStructure S (Vinfinite S) :=
  RelStructure.comap fun s (n : ℕ) => n + k s

theorem measurable_drop (k : S.Srt → ℕ) :
    Measurable (RelStructure.drop (S := S) k) := by
  rw [measurable_pi_iff]
  intro c
  exact measurable_eval _

/-- **The `l`-block after `k`**: the sortwise embedding of `Fin (l s)` onto the vertices
`k s, k s + 1, …` of each sort. -/
def shiftEmb (k l : S.Srt → ℕ) : ∀ s, Fin (l s) ↪ ℕ := fun s =>
  ⟨fun i => (i : ℕ) + k s, fun a b h => by
    simp only at h
    exact Fin.val_injective (by omega)⟩

/-- Restricting to the `l`-block after `k` is restricting the shifted structure to its
initial `l`-block. -/
theorem restrict_shiftEmb_eq (k l : S.Srt → ℕ) :
    RelStructure.restrict (S := S) (shiftEmb k l) =
      RelStructure.restrictFin l ∘ RelStructure.drop k := rfl

/-! ### Restriction and shift invariance of an exchangeable law -/

variable [Fintype S.Srt] [Countable S.Rel]

/-- **The law of any sortwise injective restriction depends only on the block sizes**: extend
each injection to a permutation of `ℕ` and use exchangeability. -/
theorem InfiniteRelExchangeableLaw.law_map_restrict (M : InfiniteRelExchangeableLaw S)
    {n : S.Srt → ℕ} (e : ∀ s, Fin (n s) ↪ ℕ) :
    (M.law : Measure (RelStructure S (Vinfinite S))).map (RelStructure.restrict e) =
      (M.law : Measure (RelStructure S (Vinfinite S))).map (RelStructure.restrictFin n) := by
  choose σ hσ using fun s => exists_perm_extend (e s)
  have hcomp : RelStructure.restrict (S := S) e =
      RelStructure.restrictFin n ∘ RelStructure.relabel σ := by
    funext X
    show RelStructure.comap _ X = RelStructure.comap _ (RelStructure.comap _ X)
    rw [← RelStructure.comap_comp]
    congr 1
    funext s i
    exact (hσ s i).symm
  rw [hcomp, ← Measure.map_map (RelSignature.measurable_restrictFin n)
      (measurable_relabel σ), M.exchangeable σ]

/-- **Shift invariance**: forgetting the first `k`-block does not change the law. -/
theorem InfiniteRelExchangeableLaw.law_map_drop (M : InfiniteRelExchangeableLaw S)
    (k : S.Srt → ℕ) :
    (M.law : Measure (RelStructure S (Vinfinite S))).map (RelStructure.drop k) =
      (M.law : Measure (RelStructure S (Vinfinite S))) := by
  refine RelStructure.ext_of_map_restrictFin fun m => ?_
  rw [Measure.map_map (RelSignature.measurable_restrictFin m) (measurable_drop k),
    ← restrict_shiftEmb_eq, M.law_map_restrict (shiftEmb k m)]

end RelSignature
