/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelFixingAlgebra

/-!
# The lower-rank conditioning algebra (R4 converse piece 3, #107)

The conditioning factor for the rankwise relative-independence theorem: the join of the fixing
σ-algebras of *all* vertex sets of rank below `n`,

`lowerRankAlgebra n = ⨆ A, ⨆ (_ : A.card < n), fixingAlgebra A`.

## Why a single global factor

The target theorem is that, for a finite family `F` of **distinct** vertex sets of rank exactly
`n`, the exact-anchor layers at those sets are **mutually** — not merely pairwise —
conditionally independent given everything of lower rank:

`E[∏ A ∈ F, g A ∘ exactMap A | lowerRankAlgebra n] =ᵐ ∏ A ∈ F, E[g A ∘ exactMap A | lowerRankAlgebra n]`

The conditioning must be this one global algebra, not a chain and not a separate conditioning
per pair. Two things go wrong otherwise:

* pairwise conditional independence does **not** imply mutual conditional independence, so the
  finite-product identity cannot be assembled from two-set statements; and
* conditional independence is **not** preserved when the conditioning algebra is enlarged, so a
  statement proved against one conditioning factor cannot simply be re-read against another.

`RelSignature.InfiniteRelExchangeableLaw.condIndep_fixingAlgebra` therefore serves here as
infrastructure and as a regression check on the two-set case, not as the proof engine. The
engine is the finite-family form of Austin's Proposition 3.12 (arXiv:0801.1698), which peels one
member off the family using the Lemma 3.11 tail property, adapted sortwise.

This file is law-free: it defines the conditioning factor and its order theory only.

## Contents

* `RelStructure.lowerRankAlgebra` — the conditioning factor, with `_le` (below the ambient
  algebra), `_mono` (monotone in the rank bound), `fixingAlgebra_le_lowerRankAlgebra` (each
  low-rank factor sits inside it), and the degenerate values at ranks `0` and `1`.
-/

open MeasureTheory

namespace RelSignature

variable {S : RelSignature}

/-- **The lower-rank conditioning algebra**: the join of the fixing σ-algebras of all vertex
sets of cardinality strictly below `n`. -/
@[implicit_reducible]
noncomputable def RelStructure.lowerRankAlgebra (n : ℕ) :
    MeasurableSpace (RelStructure S (Vinfinite S)) :=
  ⨆ A : Finset (Σ s : S.Srt, Vinfinite S s), ⨆ _ : A.card < n, RelStructure.fixingAlgebra A

theorem RelStructure.lowerRankAlgebra_le (n : ℕ) :
    RelStructure.lowerRankAlgebra (S := S) n ≤
      (inferInstance : MeasurableSpace (RelStructure S (Vinfinite S))) :=
  iSup₂_le fun A _ => RelStructure.fixingAlgebra_le A

/-- Each low-rank fixing algebra sits inside the conditioning factor. -/
theorem RelStructure.fixingAlgebra_le_lowerRankAlgebra
    {A : Finset (Σ s : S.Srt, Vinfinite S s)} {n : ℕ} (h : A.card < n) :
    RelStructure.fixingAlgebra A ≤ RelStructure.lowerRankAlgebra (S := S) n :=
  le_iSup₂_of_le A h le_rfl

/-- **Monotone in the rank bound**: a larger bound admits more generators. -/
theorem RelStructure.lowerRankAlgebra_mono : Monotone (RelStructure.lowerRankAlgebra (S := S)) :=
  fun _ _ hmn => iSup₂_le fun _ hA =>
    RelStructure.fixingAlgebra_le_lowerRankAlgebra (lt_of_lt_of_le hA hmn)

/-- At rank bound `0` there are no generators. -/
theorem RelStructure.lowerRankAlgebra_zero :
    RelStructure.lowerRankAlgebra (S := S) 0 = ⊥ := by
  refine le_antisymm (iSup₂_le fun A hA => absurd hA (by omega)) bot_le

/-- At rank bound `1` the only generator is the empty set, so the conditioning factor is the
invariant σ-algebra — the factor that carries whatever global information the law has. This is
the base of the recursion, and the reason no `NoNullary` hypothesis is needed. -/
theorem RelStructure.lowerRankAlgebra_one :
    RelStructure.lowerRankAlgebra (S := S) 1 = RelStructure.invariantAlgebra := by
  refine le_antisymm (iSup₂_le fun A hA => ?_) ?_
  · rw [← RelStructure.fixingAlgebra_empty]
    have hA0 : A = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hA0
    exact le_rfl
  · rw [← RelStructure.fixingAlgebra_empty]
    exact RelStructure.fixingAlgebra_le_lowerRankAlgebra (by simp)

/-! ### Invariance under relabeling -/

open scoped Classical in
private theorem sigmaMap_injective (σ : FinSuppPerm S) :
    Function.Injective (Sigma.map id fun s => ⇑(σ.1 s) :
      (Σ s : S.Srt, Vinfinite S s) → Σ s : S.Srt, Vinfinite S s) := by
  have hinv : Function.LeftInverse
      (Sigma.map id fun s => ⇑((σ⁻¹ : FinSuppPerm S).1 s) :
        (Σ s : S.Srt, Vinfinite S s) → Σ s : S.Srt, Vinfinite S s)
      (Sigma.map id fun s => ⇑(σ.1 s)) := by
    rintro ⟨s, x⟩
    show (⟨s, (σ.1 s)⁻¹ (σ.1 s x)⟩ : Σ s : S.Srt, Vinfinite S s) = ⟨s, x⟩
    rw [show (σ.1 s)⁻¹ (σ.1 s x) = x from (σ.1 s).symm_apply_apply x]
  exact hinv.injective

open scoped Classical in
private theorem image_image_inv_rank (σ : FinSuppPerm S)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    (A.image (Sigma.map id fun s => ⇑((σ⁻¹ : FinSuppPerm S).1 s))).image
      (Sigma.map id fun s => ⇑(σ.1 s)) = A := by
  rw [Finset.image_image]
  refine (Finset.image_congr fun v _ => ?_).trans A.image_id
  obtain ⟨s, x⟩ := v
  show (⟨s, σ.1 s ((σ.1 s)⁻¹ x)⟩ : Σ s : S.Srt, Vinfinite S s) = ⟨s, x⟩
  rw [show σ.1 s ((σ.1 s)⁻¹ x) = x from (σ.1 s).apply_symm_apply x]

open scoped Classical in
/-- **The conditioning factor is relabeling invariant.** A finitely supported relabeling permutes
the vertex sets of each rank, so it permutes the generators of `lowerRankAlgebra n` among
themselves.

This is what lets the tail-shift equality of the peel argument decompose: the lower-rank summand
is carried to itself here, and each family member's poll block is carried to its successor by
`pollBlock_image_pollPerm_of_subset`. -/
theorem RelStructure.comap_relabel_lowerRankAlgebra (σ : FinSuppPerm S) (n : ℕ) :
    MeasurableSpace.comap (RelStructure.relabel σ.1)
        (RelStructure.lowerRankAlgebra (S := S) n) =
      RelStructure.lowerRankAlgebra n := by
  classical
  rw [RelStructure.lowerRankAlgebra]
  simp_rw [MeasurableSpace.comap_iSup, RelStructure.fixingAlgebra_comap_relabel σ.2]
  refine le_antisymm (iSup₂_le fun A hA => ?_) (iSup₂_le fun A hA => ?_)
  · exact le_iSup₂_of_le (A.image (Sigma.map id fun s => ⇑(σ.1 s)))
      (by rwa [Finset.card_image_of_injective _ (sigmaMap_injective σ)]) le_rfl
  · refine le_iSup₂_of_le (A.image (Sigma.map id fun s => ⇑((σ⁻¹ : FinSuppPerm S).1 s)))
      (by rwa [Finset.card_image_of_injective _ (sigmaMap_injective σ⁻¹)])
      (le_of_eq ?_)
    rw [image_image_inv_rank σ A]

/-! ### The rank bridge -/

open scoped Classical in
/-- **Distinct supports of the same rank meet in lower rank.** This is the exact bridge into
`lowerRankAlgebra`: in the peel argument every `C_A = A ∩ A₀` is a generator of the conditioning
factor, because `A` and `A₀` are distinct sets of the same cardinality. -/
theorem card_inter_lt_of_ne {A A₀ : Finset (Σ s : S.Srt, Vinfinite S s)} {n : ℕ}
    (hA : A.card = n) (hA₀ : A₀.card = n) (hne : A ≠ A₀) : (A ∩ A₀).card < n := by
  classical
  have hle : (A ∩ A₀).card ≤ n := hA ▸ Finset.card_le_card Finset.inter_subset_left
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    have h1 : A ∩ A₀ = A :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have h2 : A ⊆ A₀ := h1 ▸ Finset.inter_subset_right
    exact hne (Finset.eq_of_subset_of_card_le h2 (by omega))

end RelSignature
