/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRankAlgebra
import Graphon.RelPollingInfrastructure

/-!
# The family polling tail (R4 converse piece 3, #107)

The conditioning tower for the peel step of rankwise relative independence. Fix a finite family
`F` of rank-`n` supports and a distinguished member `A₀`. For each other member `A` write

`C_A = A ∩ A₀` (of rank `< n`, by `card_inter_lt_of_ne`) and `D_A = A \ A₀`,

and poll the `D_A` *together*, as one common copy of their union, so overlaps — hence equality
patterns — survive. The tower is

`rankTailAlgebra q = lowerRankAlgebra n ⊔ ⨆_{m ≥ q} ⨆_{A ∈ F.erase A₀} fixingAlgebra (C_A ∪ Q_m D_A)`.

The spacing bound `K` and the tail cutoff `q` are deliberately named differently: `K` is fixed
once, above the whole finite union *including* `A₀`, so every subset copy shares one geometry,
while `q` varies along the tail.

No nonemptiness hypothesis: the empty family and rank zero degenerate through the definitions.

## The shift is not finitely supported

`pollPerm K U` moves one block at *every* slot, so it displaces infinitely many vertices. Two
consequences for the peel argument, both easy to get wrong:

* the invariance of the conditioning factor must come from the **arbitrary-permutation** form of
  `comap_relabel_lowerRankAlgebra`, not a finite-support version;
* the distinguished `fixingAlgebra A₀`-event is **not** known to be exactly invariant under the
  shift. Its invariance is only modulo the law, from
  `InfiniteRelExchangeableLaw.relabel_preimage_ae_eq_of_fixingAlgebra`. Nothing structural breaks:
  the tail engine takes `f ∘ T =ᵐ f`, not a strict equality.

Finitely supported test permutations appear only in the *pairwise* argument's raw intersection
identification, which does not generalize here — see `RelStructure.rankTailAlgebra` below.
-/

open MeasureTheory

namespace RelSignature

variable {S : RelSignature}

/-! ### The polled union and its fixation of `A₀` -/

open scoped Classical in
/-- **The polled union**: the vertices of the non-distinguished members lying outside `A₀`,
collected into one set. Polling moves *this* — not each member separately — so the overlaps
between members, hence their equality patterns, survive. -/
noncomputable def pollUnion (F : Finset (Finset (Σ s : S.Srt, Vinfinite S s)))
    (A₀ : Finset (Σ s : S.Srt, Vinfinite S s)) : Finset (Σ s : S.Srt, Vinfinite S s) :=
  (F.erase A₀).biUnion fun A => A \ A₀

open scoped Classical in
/-- Each member's own polled part sits inside the common union — the copies are cut from one
block. -/
theorem sdiff_subset_pollUnion {F : Finset (Finset (Σ s : S.Srt, Vinfinite S s))}
    {A₀ A : Finset (Σ s : S.Srt, Vinfinite S s)} (hA : A ∈ F.erase A₀) :
    A \ A₀ ⊆ pollUnion F A₀ := by
  classical
  exact Finset.subset_biUnion_of_mem (fun A => A \ A₀) hA

open scoped Classical in
/-- The polled union is disjoint from `A₀` by construction. -/
theorem notMem_pollUnion_of_mem {F : Finset (Finset (Σ s : S.Srt, Vinfinite S s))}
    {A₀ : Finset (Σ s : S.Srt, Vinfinite S s)} {v : Σ s : S.Srt, Vinfinite S s} (hv : v ∈ A₀) :
    v ∉ pollUnion F A₀ := by
  classical
  simp only [pollUnion, Finset.mem_biUnion, not_exists]
  rintro A ⟨-, hmem⟩
  exact (Finset.mem_sdiff.mp hmem).2 hv

open scoped Classical in
/-- **The poll shift fixes `A₀` pointwise.** The shift moves only residues lying in the polled
union, and `A₀` is disjoint from it and below the spacing bound.

This is exact — a genuine pointwise fixation — even though the shift itself is *not* finitely
supported. What is only a.e. is the invariance of a `fixingAlgebra A₀`-*event* under the shift;
that comes separately from
`InfiniteRelExchangeableLaw.relabel_preimage_ae_eq_of_fixingAlgebra`. -/
theorem pollPerm_pollUnion_fixes {K : ℕ} [NeZero K]
    {F : Finset (Finset (Σ s : S.Srt, Vinfinite S s))}
    {A₀ : Finset (Σ s : S.Srt, Vinfinite S s)} (hK : ∀ v ∈ A₀, v.2 < K) :
    ∀ v ∈ A₀, pollPerm K (pollUnion F A₀) v.1 v.2 = v.2 := fun v hv =>
  pollPerm_apply_of_notMem K (pollUnion F A₀) (hK v hv) (notMem_pollUnion_of_mem hv)

open scoped Classical in
/-- **The family polling tail.** The conditioning factor of the peel step at cutoff `q`. -/
@[implicit_reducible]
noncomputable def RelStructure.rankTailAlgebra (n K : ℕ)
    (F : Finset (Finset (Σ s : S.Srt, Vinfinite S s)))
    (A₀ : Finset (Σ s : S.Srt, Vinfinite S s)) (q : ℕ) :
    MeasurableSpace (RelStructure S (Vinfinite S)) :=
  RelStructure.lowerRankAlgebra n ⊔
    ⨆ m, ⨆ _ : q ≤ m, ⨆ A ∈ F.erase A₀,
      RelStructure.fixingAlgebra ((A ∩ A₀) ∪ pollBlock K (A \ A₀) m)

open scoped Classical in
theorem RelStructure.rankTailAlgebra_le (n K : ℕ)
    (F : Finset (Finset (Σ s : S.Srt, Vinfinite S s)))
    (A₀ : Finset (Σ s : S.Srt, Vinfinite S s)) (q : ℕ) :
    RelStructure.rankTailAlgebra (S := S) n K F A₀ q ≤
      (inferInstance : MeasurableSpace (RelStructure S (Vinfinite S))) :=
  sup_le (RelStructure.lowerRankAlgebra_le n)
    (iSup₂_le fun _ _ => iSup₂_le fun _ _ => RelStructure.fixingAlgebra_le _)

open scoped Classical in
/-- **Antitone in the cutoff**: a later cutoff admits fewer generators. -/
theorem RelStructure.rankTailAlgebra_antitone (n K : ℕ)
    (F : Finset (Finset (Σ s : S.Srt, Vinfinite S s)))
    (A₀ : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Antitone (RelStructure.rankTailAlgebra (S := S) n K F A₀) := by
  intro p q hpq
  -- unfold both sides rather than unifying through the reducible definition, which blows up
  simp only [RelStructure.rankTailAlgebra]
  refine sup_le le_sup_left (iSup₂_le fun m hm => ?_)
  exact le_trans (le_iSup₂_of_le m (hpq.trans hm) le_rfl) le_sup_right

open scoped Classical in
/-- **The lower-rank factor sits inside every stage**, as a summand. -/
theorem RelStructure.lowerRankAlgebra_le_rankTailAlgebra (n K : ℕ)
    (F : Finset (Finset (Σ s : S.Srt, Vinfinite S s)))
    (A₀ : Finset (Σ s : S.Srt, Vinfinite S s)) (q : ℕ) :
    RelStructure.lowerRankAlgebra (S := S) n ≤ RelStructure.rankTailAlgebra n K F A₀ q :=
  le_sup_left

open scoped Classical in
/-- **At cutoff `0` the tower contains the original conditioning factor of the peel step.**
Poll slot `0` is the identity, and `(A ∩ A₀) ∪ (A \ A₀) = A`, so each other member's own fixing
algebra is a generator. -/
theorem RelStructure.le_rankTailAlgebra_zero (n K : ℕ)
    (F : Finset (Finset (Σ s : S.Srt, Vinfinite S s)))
    (A₀ : Finset (Σ s : S.Srt, Vinfinite S s)) :
    RelStructure.lowerRankAlgebra (S := S) n ⊔
        (⨆ A ∈ F.erase A₀, RelStructure.fixingAlgebra A) ≤
      RelStructure.rankTailAlgebra n K F A₀ 0 := by
  classical
  refine sup_le le_sup_left (iSup₂_le fun A hA => le_sup_right.trans' ?_)
  refine le_trans (le_of_eq ?_) (le_iSup₂_of_le 0 le_rfl (le_iSup₂_of_le A hA le_rfl))
  congr 1
  rw [pollBlock_zero]
  refine (Finset.ext fun v => ?_).symm
  by_cases h : v ∈ A₀ <;> simp [h]

end RelSignature
