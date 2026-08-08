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
  first-block, after-block, and tail events (the vertex tail as the meet over all size
  vectors, equal to the diagonal meet under `Fintype S.Srt`), with monotonicity,
  `iSup_initialAlgebra_eq` (the initial algebras generate), and the finite tail windows
  `tailWindowAlgebra` exhausting `tailAlgebra` (`iSup_tailWindowAlgebra_eq`);
* `InfiniteRelExchangeableLaw.IsDissociated` — **exact finite-event factorization**: the joint
  law of the block pair (`blockPair`) is the product of the two marginals, for all block
  sizes; by `IsDissociated.map_restrict_pair` this factorizes **arbitrary** sortwise
  injections with disjoint ranges, not only the canonical adjacent blocks.

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

/-- **The law of any sortwise injective self-restriction is the law**: every finite restriction
of both sides agrees, because restricting a self-restriction is restricting along the composed
finite embedding, whose law depends only on the block sizes. -/
theorem InfiniteRelExchangeableLaw.law_map_restrict_self (M : InfiniteRelExchangeableLaw S)
    (e : ∀ s, Vinfinite S s ↪ Vinfinite S s) :
    (M.law : Measure (RelStructure S (Vinfinite S))).map (RelStructure.restrict e) =
      (M.law : Measure (RelStructure S (Vinfinite S))) := by
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  haveI : IsFiniteMeasure ((M.law : Measure (RelStructure S (Vinfinite S))).map
      (RelStructure.restrict e)) :=
    Measure.isFiniteMeasure_map _ _
  refine RelStructure.ext_of_map_restrictFin fun n => ?_
  rw [Measure.map_map (RelSignature.measurable_restrictFin n) (measurable_restrict e),
    show RelStructure.restrictFin (S := S) n ∘ RelStructure.restrict e =
      RelStructure.restrict (fun s => (Fin.valEmbedding.trans (e s))) from rfl,
    M.law_map_restrict fun s => Fin.valEmbedding.trans (e s)]

/-- **Shift invariance**: forgetting the first `k`-block does not change the law — the shift
is a sortwise injective self-restriction. -/
theorem InfiniteRelExchangeableLaw.law_map_drop (M : InfiniteRelExchangeableLaw S)
    (k : S.Srt → ℕ) :
    (M.law : Measure (RelStructure S (Vinfinite S))).map (RelStructure.drop k) =
      (M.law : Measure (RelStructure S (Vinfinite S))) :=
  M.law_map_restrict_self fun s => ⟨fun n => n + k s, add_left_injective (k s)⟩

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

/-- **The vertex-tail σ-algebra**: events measurable after forgetting **any** initial block
(the meet over all size vectors). -/
@[reducible] noncomputable def RelStructure.vertexTailAlgebra :
    MeasurableSpace (RelStructure S (Vinfinite S)) :=
  ⨅ k : S.Srt → ℕ, RelStructure.tailAlgebra (S := S) k

theorem RelStructure.vertexTailAlgebra_le_tailAlgebra (k : S.Srt → ℕ) :
    RelStructure.vertexTailAlgebra (S := S) ≤ RelStructure.tailAlgebra (S := S) k :=
  iInf_le _ k

theorem RelStructure.vertexTailAlgebra_le :
    RelStructure.vertexTailAlgebra (S := S) ≤
      (inferInstance : MeasurableSpace (RelStructure S (Vinfinite S))) :=
  (RelStructure.vertexTailAlgebra_le_tailAlgebra fun _ => 0).trans
    (RelStructure.tailAlgebra_le fun _ => 0)

/-- **The diagonal blocks are cofinal** (`Fintype S.Srt`): the vertex-tail σ-algebra is
already the meet over the diagonal size vectors. -/
theorem RelStructure.vertexTailAlgebra_eq_iInf_diagonal [Fintype S.Srt] :
    RelStructure.vertexTailAlgebra (S := S) =
      ⨅ k : ℕ, RelStructure.tailAlgebra (S := S) fun _ => k := by
  refine le_antisymm (le_iInf fun k => iInf_le _ _) (le_iInf fun n => ?_)
  obtain ⟨N, hN⟩ := exists_const_ge n
  exact (iInf_le _ N).trans (RelStructure.tailAlgebra_antitone hN)

/-- **The finite tail window**: events depending only on the `l`-block after `k`. -/
@[reducible] noncomputable def RelStructure.tailWindowAlgebra (k l : S.Srt → ℕ) :
    MeasurableSpace (RelStructure S (Vinfinite S)) :=
  MeasurableSpace.comap (RelStructure.restrict (shiftEmb k l)) inferInstance

/-- **The finite tail windows exhaust the after-block σ-algebra**: pull the generation of the
Borel σ-algebra by initial blocks back through the shift. -/
theorem RelStructure.iSup_tailWindowAlgebra_eq (k : S.Srt → ℕ) :
    (⨆ l : S.Srt → ℕ, RelStructure.tailWindowAlgebra (S := S) k l) =
      RelStructure.tailAlgebra (S := S) k := by
  have h : ∀ l : S.Srt → ℕ, RelStructure.tailWindowAlgebra (S := S) k l =
      MeasurableSpace.comap (RelStructure.drop k) (RelStructure.initialAlgebra l) := by
    intro l
    rw [RelStructure.tailWindowAlgebra, restrict_shiftEmb_eq, RelStructure.initialAlgebra,
      MeasurableSpace.comap_comp]
  simp only [h]
  rw [← MeasurableSpace.comap_iSup, RelStructure.iSup_initialAlgebra_eq]

/-! ### Dissociation: exact finite-event factorization -/

/-- **The joint block map**: the first `k`-block together with the following `l`-block. -/
def blockPair (k l : S.Srt → ℕ) (X : RelStructure S (Vinfinite S)) :
    RelStructure S (Vfinite k) × RelStructure S (Vfinite l) :=
  (RelStructure.restrictFin k X, RelStructure.restrict (shiftEmb k l) X)

/-- **Dissociation** (exact finite-event factorization): for all block sizes `k`, `l`, the
joint law of the first `k`-block and the following `l`-block is the product of the `k`- and
`l`-marginals of the law. -/
def InfiniteRelExchangeableLaw.IsDissociated (M : InfiniteRelExchangeableLaw S) : Prop :=
  ∀ k l : S.Srt → ℕ,
    (M.law : Measure (RelStructure S (Vinfinite S))).map (blockPair k l) =
      ((M.law : Measure (RelStructure S (Vinfinite S))).map
          (RelStructure.restrictFin k)).prod
        ((M.law : Measure (RelStructure S (Vinfinite S))).map
          (RelStructure.restrictFin l))

/-- The joint block map is measurable. -/
theorem measurable_blockPair (k l : S.Srt → ℕ) :
    Measurable (blockPair (S := S) k l) :=
  (RelSignature.measurable_restrictFin k).prodMk
    (by rw [restrict_shiftEmb_eq]
        exact (RelSignature.measurable_restrictFin l).comp (measurable_drop k))

/-- **The marginals of the joint block law** are the block-size marginals of the law —
independently of any dissociation hypothesis (first coordinate directly; second by the
labeling-free restriction invariance). -/
theorem InfiniteRelExchangeableLaw.map_blockPair_fst (M : InfiniteRelExchangeableLaw S)
    (k l : S.Srt → ℕ) :
    ((M.law : Measure (RelStructure S (Vinfinite S))).map (blockPair k l)).map Prod.fst =
      (M.law : Measure (RelStructure S (Vinfinite S))).map (RelStructure.restrictFin k) := by
  rw [Measure.map_map measurable_fst (measurable_blockPair k l)]
  rfl

theorem InfiniteRelExchangeableLaw.map_blockPair_snd (M : InfiniteRelExchangeableLaw S)
    (k l : S.Srt → ℕ) :
    ((M.law : Measure (RelStructure S (Vinfinite S))).map (blockPair k l)).map Prod.snd =
      (M.law : Measure (RelStructure S (Vinfinite S))).map (RelStructure.restrictFin l) := by
  rw [Measure.map_map measurable_snd (measurable_blockPair k l)]
  exact M.law_map_restrict (shiftEmb k l)

/-- The sortwise combination of two disjoint-range injections into one block-sized
injection: the first block by `e`, the rest by `f`. -/
private def combineEmb {n m : S.Srt → ℕ} (e : ∀ s, Fin (n s) ↪ ℕ) (f : ∀ s, Fin (m s) ↪ ℕ)
    (hd : ∀ s (i : Fin (n s)) (j : Fin (m s)), e s i ≠ f s j) :
    ∀ s, Fin (n s + m s) ↪ ℕ := fun s =>
  ⟨fun i => if h : (i : ℕ) < n s then e s ⟨i, h⟩
    else f s ⟨(i : ℕ) - n s, by omega⟩, by
    intro a b hab
    simp only at hab
    split_ifs at hab with h1 h2 h2
    · exact Fin.val_injective (congrArg Fin.val ((e s).injective hab) :
        ((⟨(a : ℕ), h1⟩ : Fin (n s)) : ℕ) = _)
    · exact absurd hab (hd s _ _)
    · exact absurd hab.symm (hd s _ _)
    · have := congrArg Fin.val ((f s).injective hab)
      simp only at this
      exact Fin.val_injective (by omega)⟩

/-- **The joint law of disjoint blocks depends only on the block sizes** (pure
exchangeability, no dissociation): any two sortwise injections with disjoint ranges are, up
to a relabeling, the canonical adjacent blocks. -/
theorem InfiniteRelExchangeableLaw.law_map_restrict_pair
    (M : InfiniteRelExchangeableLaw S)
    {n m : S.Srt → ℕ} (e : ∀ s, Fin (n s) ↪ ℕ) (f : ∀ s, Fin (m s) ↪ ℕ)
    (hd : ∀ s (i : Fin (n s)) (j : Fin (m s)), e s i ≠ f s j) :
    (M.law : Measure (RelStructure S (Vinfinite S))).map
        (fun X => (RelStructure.restrict e X, RelStructure.restrict f X)) =
      (M.law : Measure (RelStructure S (Vinfinite S))).map (blockPair n m) := by
  choose σ hσ using fun s => exists_perm_extend (combineEmb e f hd s)
  have hpair : (fun X : RelStructure S (Vinfinite S) =>
      (RelStructure.restrict e X, RelStructure.restrict f X)) =
      blockPair n m ∘ RelStructure.relabel σ := by
    funext X
    refine Prod.ext ?_ ?_
    · show RelStructure.comap _ X = RelStructure.comap _ (RelStructure.comap _ X)
      rw [← RelStructure.comap_comp]
      congr 1
      funext s i
      have h := hσ s ⟨(i : ℕ), by omega⟩
      simp only [combineEmb, Function.Embedding.coeFn_mk] at h
      rw [dif_pos i.isLt] at h
      exact h.symm
    · show RelStructure.comap _ X = RelStructure.comap _ (RelStructure.comap _ X)
      rw [← RelStructure.comap_comp]
      congr 1
      funext s j
      have h := hσ s ⟨n s + (j : ℕ), by omega⟩
      simp only [combineEmb, Function.Embedding.coeFn_mk] at h
      rw [dif_neg (by omega)] at h
      have harg : (⟨n s + (j : ℕ) - n s, by omega⟩ : Fin (m s)) = j := by
        apply Fin.ext
        show n s + (j : ℕ) - n s = (j : ℕ)
        omega
      rw [harg] at h
      show (f s) j = σ s ((j : ℕ) + n s)
      rw [Nat.add_comm (j : ℕ) (n s), h]
  rw [hpair, ← Measure.map_map (measurable_blockPair n m) (measurable_relabel σ),
    M.exchangeable σ]

/-- **Dissociation factorizes arbitrary disjoint blocks**: for any two sortwise injections
with disjoint ranges, the joint law of the two restrictions is the product of the block-size
marginals. -/
theorem InfiniteRelExchangeableLaw.IsDissociated.map_restrict_pair
    {M : InfiniteRelExchangeableLaw S} (hM : M.IsDissociated)
    {n m : S.Srt → ℕ} (e : ∀ s, Fin (n s) ↪ ℕ) (f : ∀ s, Fin (m s) ↪ ℕ)
    (hd : ∀ s (i : Fin (n s)) (j : Fin (m s)), e s i ≠ f s j) :
    (M.law : Measure (RelStructure S (Vinfinite S))).map
        (fun X => (RelStructure.restrict e X, RelStructure.restrict f X)) =
      ((M.law : Measure (RelStructure S (Vinfinite S))).map
          (RelStructure.restrictFin n)).prod
        ((M.law : Measure (RelStructure S (Vinfinite S))).map
          (RelStructure.restrictFin m)) := by
  rw [M.law_map_restrict_pair e f hd, hM n m]

end RelSignature
