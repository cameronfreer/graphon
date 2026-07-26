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

This mirrors the undirected `Graphon/InvariantAction.lean`. The arrows into the dissociation
triangle live in `Graphon.RelErgodicLinks`, the ergodic ↔ extreme-point theorem in
`Graphon.RelErgodicExtreme`, and the five-way equivalence in `Graphon.RelExtremality`;
`invariantProbabilityMeasures` (below) is the convex set those results are stated over, with
the finitary-invariance bridge `mem_invariantProbabilityMeasures_iff_exists_law` identifying
it with the laws of `InfiniteRelExchangeableLaw`.
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

/-- **The finitely supported sortwise permutations, as a subgroup** of the full sortwise
permutation group. The closure proofs are exactly `SortwiseFinSupp.one`, `.mul`, and `.inv`.

This is the symmetry group the relational layer actually acts by. Stating it as a subgroup —
rather than carrying a raw permutation family plus a `SortwiseFinSupp` side condition — matters
downstream: the constructions there provide, and the arguments there use, closure under
finitely supported relabelings only; closure of a chosen countable event family under the full
permutation group is neither constructed nor countable in general. -/
def sortwiseFinSuppSubgroup (S : RelSignature) : Subgroup (∀ _ : S.Srt, Equiv.Perm ℕ) where
  carrier := {σ | SortwiseFinSupp (S := S) σ}
  mul_mem' := fun hσ hτ => SortwiseFinSupp.mul hσ hτ
  one_mem' := SortwiseFinSupp.one
  inv_mem' := fun hσ => SortwiseFinSupp.inv hσ

/-- **A finitely supported sortwise permutation family**, bundled with its support bound. A
`Group` by construction, so identity, composition, and inverses are all available without side
conditions. -/
abbrev FinSuppPerm (S : RelSignature) := sortwiseFinSuppSubgroup S

@[simp] theorem mem_sortwiseFinSuppSubgroup {σ : ∀ _ : S.Srt, Equiv.Perm ℕ} :
    σ ∈ sortwiseFinSuppSubgroup S ↔ SortwiseFinSupp (S := S) σ := Iff.rfl

theorem FinSuppPerm.sortwiseFinSupp (σ : FinSuppPerm S) : SortwiseFinSupp (S := S) σ.1 := σ.2


/-! ### The invariant σ-algebra -/

/-- **The invariant σ-algebra**: measurable sets strictly invariant under every finitely
supported sortwise relabeling. -/
@[implicit_reducible]
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

/-! ### The invariant probability simplex -/

/-- **The invariant probability measures**: the convex set of probability measures on the
infinite structure space invariant under every finitely supported sortwise relabeling. By
`mem_invariantProbabilityMeasures_iff_exists_law` (finite-restriction extensionality), these
are exactly the laws of `InfiniteRelExchangeableLaw` — finitary invariance already implies
invariance under every sortwise permutation. -/
def invariantProbabilityMeasures (S : RelSignature) :
    Set (Measure (RelStructure S (Vinfinite S))) :=
  {ν | (∀ σ, SortwiseFinSupp (S := S) σ → ν.map (RelStructure.relabel σ) = ν) ∧
    IsProbabilityMeasure ν}

/-- **Every injection of a finite window extends to a finitely supported permutation** —
the finitary strengthening of `exists_perm_extend`, by induction on the window with one
transposition per step. -/
theorem exists_finSupp_perm_extend {k : ℕ} (g : Fin k ↪ ℕ) :
    ∃ (π : Equiv.Perm ℕ) (N : ℕ), (∀ x, N ≤ x → π x = x) ∧ ∀ a : Fin k, π (a : ℕ) = g a := by
  induction k with
  | zero => exact ⟨1, 0, fun _ _ => rfl, fun a => a.elim0⟩
  | succ k ih =>
    obtain ⟨π₀, N₀, hN₀, hπ₀⟩ := ih ((Fin.castSuccEmb).trans g)
    set y := π₀ (k : ℕ) with hy
    set z := g (Fin.last k) with hz
    refine ⟨Equiv.swap y z * π₀, max (max N₀ (k + 1)) (max (y + 1) (z + 1)),
      fun x hx => ?_, fun a => ?_⟩
    · have hx₀ : N₀ ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
      have hxy : y < x := lt_of_lt_of_le (Nat.lt_succ_self y)
        (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx))
      have hxz : z < x := lt_of_lt_of_le (Nat.lt_succ_self z)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx))
      show Equiv.swap y z (π₀ x) = x
      rw [hN₀ x hx₀, Equiv.swap_apply_of_ne_of_ne hxy.ne' hxz.ne']
    · refine Fin.lastCases ?_ (fun a => ?_) a
      · show Equiv.swap y z (π₀ ((Fin.last k : Fin (k + 1)) : ℕ)) = z
        rw [show ((Fin.last k : Fin (k + 1)) : ℕ) = (k : ℕ) from rfl, ← hy,
          Equiv.swap_apply_left]
      · show Equiv.swap y z (π₀ ((a.castSucc : Fin (k + 1)) : ℕ)) = g a.castSucc
        rw [show ((a.castSucc : Fin (k + 1)) : ℕ) = (a : ℕ) from rfl, hπ₀ a]
        have h1 : ((Fin.castSuccEmb.trans g) a : ℕ) ≠ y := by
          rw [hy, ← hπ₀ a]
          intro hcon
          have := π₀.injective hcon
          omega
        have h2 : ((Fin.castSuccEmb.trans g) a : ℕ) ≠ z := by
          rw [hz]
          intro hcon
          have := g.injective (show g a.castSucc = g (Fin.last k) from hcon)
          exact absurd (congrArg Fin.val this) (by simp [Fin.castSucc]; omega)
        exact Equiv.swap_apply_of_ne_of_ne h1 h2

/-- **Finitary invariance implies full sortwise invariance**: a probability measure invariant
under every finitely supported sortwise relabeling is invariant under *every* sortwise
relabeling — by finite-restriction extensionality, since on each finite window an arbitrary
permutation family agrees with a finitely supported one. -/
theorem map_relabel_of_mem_invariantProbabilityMeasures [Fintype S.Srt]
    {ν : Measure (RelStructure S (Vinfinite S))} (hν : ν ∈ invariantProbabilityMeasures S)
    (σ : ∀ _ : S.Srt, Equiv.Perm ℕ) :
    ν.map (RelStructure.relabel σ) = ν := by
  haveI : IsProbabilityMeasure ν := hν.2
  haveI : IsProbabilityMeasure (ν.map (RelStructure.relabel σ)) :=
    Measure.isProbabilityMeasure_map (measurable_relabel σ).aemeasurable
  refine RelStructure.ext_of_map_restrictFin fun n => ?_
  rw [Measure.map_map (RelSignature.measurable_restrictFin n) (measurable_relabel σ)]
  -- the composite is restriction along the window values of σ
  set e : ∀ s, Fin (n s) ↪ ℕ := fun s =>
    ⟨fun i => σ s (i : ℕ), fun a b h => Fin.val_injective ((σ s).injective h)⟩ with he
  have hcomp : RelStructure.restrictFin n ∘ RelStructure.relabel σ =
      RelStructure.restrict (S := S) e := rfl
  rw [hcomp]
  -- a finitely supported family agreeing with σ on each window
  choose π N hsupp hagree using fun s => exists_finSupp_perm_extend (e s)
  have hτ : SortwiseFinSupp (S := S) π :=
    ⟨Finset.univ.sup N, fun s x hx =>
      hsupp s x (le_trans (Finset.le_sup (Finset.mem_univ s)) hx)⟩
  have hsplit : RelStructure.restrict (S := S) e =
      RelStructure.restrictFin n ∘ RelStructure.relabel π := by
    funext X
    show RelStructure.comap _ X = RelStructure.comap _ (RelStructure.comap _ X)
    rw [← RelStructure.comap_comp]
    congr 1
    funext s i
    exact (hagree s i).symm
  rw [hsplit, ← Measure.map_map (RelSignature.measurable_restrictFin n)
    (measurable_relabel π), hν.1 π hτ]

/-- **The invariant simplex is exactly the exchangeable laws** (packaging/range lemma): a
measure is finitarily invariant and probability iff it is the law of an infinite exchangeable
relational law. -/
theorem mem_invariantProbabilityMeasures_iff_exists_law [Fintype S.Srt]
    {ν : Measure (RelStructure S (Vinfinite S))} :
    ν ∈ invariantProbabilityMeasures S ↔
      ∃ M : InfiniteRelExchangeableLaw S,
        (M.law : Measure (RelStructure S (Vinfinite S))) = ν := by
  constructor
  · intro hν
    haveI : IsProbabilityMeasure ν := hν.2
    exact ⟨⟨⟨ν, inferInstance⟩, fun σ => map_relabel_of_mem_invariantProbabilityMeasures hν σ⟩,
      rfl⟩
  · rintro ⟨M, rfl⟩
    exact ⟨fun σ _ => M.exchangeable σ, M.law.2⟩

end RelSignature
