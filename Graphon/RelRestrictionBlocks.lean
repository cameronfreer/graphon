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

/-! ### The initial, after-block, and vertex-tail σ-algebras -/

/-- **The initial σ-algebra**: events depending only on the first `n`-block. -/
@[reducible] noncomputable def RelStructure.initialAlgebra (n : S.Srt → ℕ) :
    MeasurableSpace (RelStructure S (Vinfinite S)) :=
  MeasurableSpace.comap (RelStructure.restrictFin n) inferInstance

theorem RelStructure.initialAlgebra_le (n : S.Srt → ℕ) :
    RelStructure.initialAlgebra (S := S) n ≤
      (inferInstance : MeasurableSpace (RelStructure S (Vinfinite S))) :=
  measurable_iff_comap_le.mp (RelSignature.measurable_restrictFin n)

/-- The initial σ-algebras are monotone in the block sizes. -/
theorem RelStructure.initialAlgebra_mono {n m : S.Srt → ℕ} (h : ∀ s, n s ≤ m s) :
    RelStructure.initialAlgebra (S := S) n ≤ RelStructure.initialAlgebra (S := S) m := by
  refine measurable_iff_comap_le.mp ?_
  rw [show RelStructure.restrictFin (S := S) n =
      RelStructure.restrictLE h ∘ RelStructure.restrictFin m from rfl]
  exact (RelSignature.measurable_restrictLE h).comp
    (@Measurable.of_comap_le _ _ (RelStructure.initialAlgebra m) _
      (RelStructure.restrictFin m) le_rfl)

/-- **The initial σ-algebras generate**: every cylinder is an initial event. -/
theorem RelStructure.iSup_initialAlgebra_eq :
    (⨆ n : S.Srt → ℕ, RelStructure.initialAlgebra (S := S) n) =
      (inferInstance : MeasurableSpace (RelStructure S (Vinfinite S))) := by
  refine le_antisymm (iSup_le RelStructure.initialAlgebra_le) ?_
  rw [← RelSignature.generateFrom_cylinders_eq]
  refine MeasurableSpace.generateFrom_le fun t ht => ?_
  simp only [RelSignature.cylinders, Set.mem_iUnion] at ht
  obtain ⟨n, T, hT, rfl⟩ := ht
  exact le_iSup (RelStructure.initialAlgebra (S := S)) n _
    (MeasurableSpace.measurableSet_comap.mpr ⟨T, hT, rfl⟩)

/-- **The after-block σ-algebra**: events depending only on the vertices after the first
`k`-block. -/
@[reducible] noncomputable def RelStructure.tailAlgebra (k : S.Srt → ℕ) :
    MeasurableSpace (RelStructure S (Vinfinite S)) :=
  MeasurableSpace.comap (RelStructure.drop k) inferInstance

theorem RelStructure.tailAlgebra_le (k : S.Srt → ℕ) :
    RelStructure.tailAlgebra (S := S) k ≤
      (inferInstance : MeasurableSpace (RelStructure S (Vinfinite S))) :=
  measurable_iff_comap_le.mp (measurable_drop k)

/-- The after-block σ-algebras are antitone (along the diagonal it suffices to shift more). -/
theorem RelStructure.tailAlgebra_antitone {k m : S.Srt → ℕ} (h : ∀ s, k s ≤ m s) :
    RelStructure.tailAlgebra (S := S) m ≤ RelStructure.tailAlgebra (S := S) k := by
  refine measurable_iff_comap_le.mp ?_
  rw [show RelStructure.drop (S := S) m =
      RelStructure.drop (fun s => m s - k s) ∘ RelStructure.drop k by
    funext X
    show RelStructure.comap _ X = RelStructure.comap _ (RelStructure.comap _ X)
    rw [← RelStructure.comap_comp]
    congr 1
    funext s i
    show i + m s = i + (m s - k s) + k s
    have := h s
    omega]
  exact (measurable_drop _).comp
    (@Measurable.of_comap_le _ _ (RelStructure.tailAlgebra k) _ (RelStructure.drop k) le_rfl)

/-- **The vertex-tail σ-algebra**: events invariant under forgetting any initial block
(the diagonal blocks are cofinal, `Fintype S.Srt`). -/
@[reducible] noncomputable def RelStructure.vertexTailAlgebra :
    MeasurableSpace (RelStructure S (Vinfinite S)) :=
  ⨅ k : ℕ, RelStructure.tailAlgebra (S := S) fun _ => k

/-! ### Dissociation: exact finite-event factorization -/

/-- **Dissociation** (exact finite-event factorization): for all block sizes `k`, `l`, the
joint law of the first `k`-block and the following `l`-block is the product of the `k`- and
`l`-marginals of the law. -/
def InfiniteRelExchangeableLaw.IsDissociated (M : InfiniteRelExchangeableLaw S) : Prop :=
  ∀ k l : S.Srt → ℕ,
    (M.law : Measure (RelStructure S (Vinfinite S))).map
        (fun X => (RelStructure.restrictFin k X, RelStructure.restrict (shiftEmb k l) X)) =
      ((M.law : Measure (RelStructure S (Vinfinite S))).map
          (RelStructure.restrictFin k)).prod
        ((M.law : Measure (RelStructure S (Vinfinite S))).map
          (RelStructure.restrictFin l))

/-- The joint block map is measurable. -/
theorem measurable_blockPair (k l : S.Srt → ℕ) :
    Measurable fun X : RelStructure S (Vinfinite S) =>
      (RelStructure.restrictFin k X, RelStructure.restrict (shiftEmb k l) X) :=
  (RelSignature.measurable_restrictFin k).prodMk
    (by rw [restrict_shiftEmb_eq]
        exact (RelSignature.measurable_restrictFin l).comp (measurable_drop k))

/-- **The marginals of the joint block law** are the block-size marginals of the law —
independently of any dissociation hypothesis (first coordinate directly; second by the
labeling-free restriction invariance). -/
theorem InfiniteRelExchangeableLaw.map_blockPair_fst (M : InfiniteRelExchangeableLaw S)
    (k l : S.Srt → ℕ) :
    ((M.law : Measure (RelStructure S (Vinfinite S))).map
        (fun X => (RelStructure.restrictFin k X,
          RelStructure.restrict (shiftEmb k l) X))).map Prod.fst =
      (M.law : Measure (RelStructure S (Vinfinite S))).map (RelStructure.restrictFin k) := by
  rw [Measure.map_map measurable_fst (measurable_blockPair k l)]
  rfl

theorem InfiniteRelExchangeableLaw.map_blockPair_snd (M : InfiniteRelExchangeableLaw S)
    (k l : S.Srt → ℕ) :
    ((M.law : Measure (RelStructure S (Vinfinite S))).map
        (fun X => (RelStructure.restrictFin k X,
          RelStructure.restrict (shiftEmb k l) X))).map Prod.snd =
      (M.law : Measure (RelStructure S (Vinfinite S))).map (RelStructure.restrictFin l) := by
  rw [Measure.map_map measurable_snd (measurable_blockPair k l)]
  exact M.law_map_restrict (shiftEmb k l)

end RelSignature
