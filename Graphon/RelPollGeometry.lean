/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelFixingAlgebra

/-!
# The poll geometry (R4 converse, #107)

The combinatorial layout of Austin's polling argument, route-neutral and law-free: poll slots
along a two-sided `ℤ`-orbit transported to `ℕ`, the deep copies `pollBlock N D m` of a finite
tagged vertex set `D` laid out in those slots (with `pollBlock N D 0 = D`), and the **poll
permutation** `pollPerm N D`, which carries the copy in slot `m` onto the copy in slot `m + 1`
while fixing every vertex below the layout bound `N` outside `D`.

The two-sidedness is forced: a *unilateral* shift of the blocks is not a bijection (slot `0`
would have no preimage), so the negative half of the orbit serves as predecessor reservoir.

`pollPerm N D` moves vertices only on the sorts occurring in `D` (`pollPerm_finiteActive`), but
has **infinite** vertex support: it shifts every slot. This is the motion of the tail arguments —
the tail joins of `Graphon.RelFixingCondIndep` on the original carrier, and the reservoir stages
of the pooled fixing-factor polling — both of which consume it.
-/

open Function

namespace RelSignature

variable {S : RelSignature}

/-! ### The poll slots -/

section PollSlots

/-- A bijection `ℤ ≃ ℕ` normalized to send `0` to `0`: the index set of the chain of poll
blocks. A *unilateral* shift of the poll blocks cannot be a permutation — block `0` would have
no preimage — so the blocks are laid out along a two-sided `ℤ`-orbit and only the nonnegative
half is ever polled; the negative half is the predecessor reservoir that makes the shift
bijective. -/
noncomputable def pollEquivInt : ℤ ≃ ℕ :=
  (Denumerable.eqv ℤ).trans (Equiv.swap (Denumerable.eqv ℤ 0) 0)

theorem pollEquivInt_zero : pollEquivInt 0 = 0 := by
  show Equiv.swap (Denumerable.eqv ℤ 0) 0 (Denumerable.eqv ℤ 0) = 0
  exact Equiv.swap_apply_left _ _

/-- The slot of the `m`-th poll block: an injective `ℕ → ℕ` starting at `0`, obtained by
restricting the two-sided indexing to the nonnegative half. -/
noncomputable def pollIndex (m : ℕ) : ℕ := pollEquivInt (m : ℤ)

theorem pollIndex_zero : pollIndex 0 = 0 := by
  rw [pollIndex, Nat.cast_zero, pollEquivInt_zero]

/-- **The poll slots escape every bound**: for each `K` all but finitely many poll blocks sit
above `K`, since `pollIndex` is injective. This is what lets a finitely supported permutation
be dodged by going deep enough into the chain. -/
theorem exists_le_pollIndex (K : ℕ) : ∃ n, ∀ m, n ≤ m → K ≤ pollIndex m := by
  classical
  refine ⟨((Finset.range K).image fun k => (pollEquivInt.symm k).toNat).sup id + 1,
    fun m hm => ?_⟩
  by_contra hlt
  push Not at hlt
  have hmem : m ∈ (Finset.range K).image fun k => (pollEquivInt.symm k).toNat :=
    Finset.mem_image.mpr ⟨pollIndex m, Finset.mem_range.mpr hlt, by
      rw [pollIndex, pollEquivInt.symm_apply_apply, Int.toNat_natCast]⟩
  have := Finset.le_sup (f := id) hmem
  simp only [id] at this
  omega

/-- **The slot shift**: a permutation of `ℕ` carrying poll slot `m` to poll slot `m + 1` — the
translation by one of the two-sided orbit, transported to `ℕ`. -/
noncomputable def pollShift : Equiv.Perm ℕ :=
  pollEquivInt.symm.trans ((Equiv.addRight (1 : ℤ)).trans pollEquivInt)

theorem pollShift_pollIndex (m : ℕ) : pollShift (pollIndex m) = pollIndex (m + 1) := by
  show pollEquivInt ((Equiv.addRight (1 : ℤ)) (pollEquivInt.symm (pollEquivInt (m : ℤ)))) =
    pollEquivInt ((m + 1 : ℕ) : ℤ)
  rw [pollEquivInt.symm_apply_apply]
  norm_num

end PollSlots

section PollBlocks

variable {S : RelSignature}

open scoped Classical in
/-- **The polling permutation**: in the coordinates `x ↦ (x / N, x % N)` it shifts the slot of
every residue lying in `D` and fixes every other residue. It therefore fixes every tagged
vertex of index `< N` outside `D` — in particular all of `A` once `N` bounds `A ∪ B` — while
translating the `D`-shaped poll block in slot `m` onto the one in slot `m + 1`. -/
noncomputable def pollPerm (N : ℕ) [NeZero N]
    (D : Finset (Σ s : S.Srt, Vinfinite S s)) : ∀ _ : S.Srt, Equiv.Perm ℕ := fun s =>
  (Nat.divModEquiv N).trans
    ((Equiv.prodCongrLeft fun i : Fin N =>
        if (⟨s, (i : ℕ)⟩ : Σ s : S.Srt, Vinfinite S s) ∈ D then pollShift else Equiv.refl ℕ).trans
      (Nat.divModEquiv N).symm)

open scoped Classical in
theorem pollPerm_apply (N : ℕ) [NeZero N] (D : Finset (Σ s : S.Srt, Vinfinite S s))
    (s : S.Srt) (k : ℕ) {x : ℕ} (hx : x < N) :
    pollPerm N D s (k * N + x) =
      (if (⟨s, x⟩ : Σ s : S.Srt, Vinfinite S s) ∈ D then pollShift k else k) * N + x := by
  have hdiv : (k * N + x) / N = k := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.pos_of_neZero N), Nat.div_eq_of_lt hx, Nat.add_zero]
  have hmod : (k * N + x) % N = x := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hx]
  show ((Nat.divModEquiv N).symm ((Equiv.prodCongrLeft _) ((Nat.divModEquiv N) (k * N + x)))) = _
  simp only [Nat.divModEquiv_apply, Nat.divModEquiv_symm_apply, Equiv.prodCongrLeft_apply,
    Fin.ofNat_eq_cast, Fin.val_natCast, hdiv, hmod]
  split_ifs with h
  · rfl
  · rfl

open scoped Classical in
theorem pollPerm_apply_of_notMem (N : ℕ) [NeZero N]
    (D : Finset (Σ s : S.Srt, Vinfinite S s)) {v : Σ s : S.Srt, Vinfinite S s} (hv : v.2 < N)
    (hvD : v ∉ D) : pollPerm N D v.1 v.2 = v.2 := by
  have := pollPerm_apply N D v.1 0 hv
  rw [Nat.zero_mul, Nat.zero_add] at this
  rw [this, if_neg (by rwa [Sigma.eta]), Nat.zero_mul, Nat.zero_add]

open scoped Classical in
/-- **The polling permutation has finitely many active sorts**: it is the identity on every sort
not occurring in `D`. -/
theorem pollPerm_eq_one_of_notMem (N : ℕ) [NeZero N] (D : Finset (Σ s : S.Srt, Vinfinite S s))
    {s : S.Srt} (hs : s ∉ D.image Sigma.fst) : pollPerm N D s = 1 := by
  refine Equiv.ext fun x => ?_
  have hx := pollPerm_apply N D s (x / N) (Nat.mod_lt x (Nat.pos_of_neZero N))
  rw [Nat.div_add_mod' x N] at hx
  rw [hx, if_neg fun h => hs (Finset.mem_image_of_mem Sigma.fst h), Nat.div_add_mod' x N]
  rfl

open scoped Classical in
theorem pollPerm_finiteActive (N : ℕ) [NeZero N]
    (D : Finset (Σ s : S.Srt, Vinfinite S s)) : SortwiseFiniteActive (S := S) (pollPerm N D) :=
  ⟨D.image Sigma.fst, fun _ hs => pollPerm_eq_one_of_notMem N D hs⟩

open scoped Classical in
/-- **The `m`-th poll block**: the copy of `D` translated into poll slot `m`, so that slot `0`
is `D` itself. -/
noncomputable def pollBlock (N : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s)) (m : ℕ) :
    Finset (Σ s : S.Srt, Vinfinite S s) :=
  D.image fun v => ⟨v.1, pollIndex m * N + v.2⟩

theorem pollBlock_zero (N : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s)) :
    pollBlock N D 0 = D := by
  classical
  rw [pollBlock]
  refine (Finset.image_congr fun v _ => ?_).trans D.image_id
  rw [pollIndex_zero, Nat.zero_mul, Nat.zero_add, Sigma.eta, id]

/-- Every vertex of a poll block sits above its slot — the estimate that lets a finitely
supported permutation fix all sufficiently deep blocks. -/
theorem le_of_mem_pollBlock {N : ℕ} {D : Finset (Σ s : S.Srt, Vinfinite S s)} {m : ℕ}
    {v : Σ s : S.Srt, Vinfinite S s} (hv : v ∈ pollBlock N D m) : pollIndex m * N ≤ v.2 := by
  classical
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
  exact Nat.le_add_right _ _

open scoped Classical in
/-- **The shift moves each poll block to the next one.** -/
theorem pollBlock_image_pollPerm {N : ℕ} [NeZero N]
    {D : Finset (Σ s : S.Srt, Vinfinite S s)} (hD : ∀ v ∈ D, v.2 < N) (m : ℕ) :
    (pollBlock N D m).image (Sigma.map id fun s => ⇑(pollPerm N D s)) = pollBlock N D (m + 1) := by
  rw [pollBlock, pollBlock, Finset.image_image]
  refine Finset.image_congr fun v hv => ?_
  show (⟨v.1, pollPerm N D v.1 (pollIndex m * N + v.2)⟩ : Σ s : S.Srt, Vinfinite S s) = _
  rw [pollPerm_apply N D v.1 _ (hD v hv), if_pos (by rwa [Sigma.eta]), pollShift_pollIndex]

open scoped Classical in
/-- **The shift fixes the conditioning set** — every vertex of `C` is below `N` and outside
`D`, hence a fixed point of `pollPerm`. -/
theorem image_pollPerm_of_notMem {N : ℕ} [NeZero N]
    {C D : Finset (Σ s : S.Srt, Vinfinite S s)} (hC : ∀ v ∈ C, v.2 < N)
    (hCD : ∀ v ∈ C, v ∉ D) :
    C.image (Sigma.map id fun s => ⇑(pollPerm N D s)) = C := by
  refine (Finset.image_congr fun v hv => ?_).trans C.image_id
  show (⟨v.1, pollPerm N D v.1 v.2⟩ : Σ s : S.Srt, Vinfinite S s) = id v
  rw [pollPerm_apply_of_notMem N D (hC v hv) (hCD v hv), Sigma.eta, id]

end PollBlocks


end RelSignature
