/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelFixingStages

/-!
# The insertion step: the fresh cross swap (R4 converse, #107, #197)

The second analytic step of the pooled fixing-factor polling argument. Given the target support
`e`, a finite remainder family `F` of other rank-`n` supports, and a finite test event `H`, the
**fresh cross swap** exchanges the original copies of `D = (⋃ F) \ e` with the spare copies of a
fresh translate `D + K` of `D`, where `K` exceeds every vertex used by the target, the remainder,
and the test event. It is chosen **after** the test event: no single swap preserves every mixed
support, since its spare destination is itself a mixed support it disturbs.

## Contents

* `crossSwap K D` — the involution, sortwise; its support lies in both halves of the layout
  `D ∪ (D + K)`, so it is supported inside the stage-`0` reservoir of that layout
  (`crossSwap_fix_of_notMem`), fixes every original vertex outside `D` below `K`
  (`crossSwap_original_of_notMem`), and has finite support on both halves with finitely many
  active sorts (`pooledFiniteActive_crossSwap`).
* `crossSwap_image_original` — a remainder support meeting `D` is carried onto a **mixed**
  support; `crossSwap_mixed_of_fresh` — a mixed support whose vertices lie below `K` stays mixed.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

open InfiniteRelExchangeableLaw

universe u

variable {S : RelSignature.{u}}

/-! ### The fresh translate -/

/-- The translate of a vertex set of the original carrier by `K`, sortwise. -/
noncomputable def shiftSet (K : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Finset (Σ s : S.Srt, Vinfinite S s) := by
  classical
  exact D.image fun v => ⟨v.1, v.2 + K⟩

theorem mem_shiftSet {K : ℕ} {D : Finset (Σ s : S.Srt, Vinfinite S s)}
    {v : Σ s : S.Srt, Vinfinite S s} :
    v ∈ shiftSet K D ↔ ∃ w ∈ D, (⟨w.1, w.2 + K⟩ : Σ s : S.Srt, Vinfinite S s) = v := by
  classical
  simp only [shiftSet, Finset.mem_image]

/-! ### The cross swap -/

open scoped Classical in
/-- The cross swap on one sort: an original vertex of `D` goes to the spare copy of its
translate, a spare vertex of the translate comes back, everything else is fixed. -/
noncomputable def crossSwapFun (K : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s)) (s : S.Srt) :
    PoolVertex S s → PoolVertex S s
  | Sum.inl x => if (⟨s, x⟩ : Σ s : S.Srt, Vinfinite S s) ∈ D then Sum.inr (x + K) else Sum.inl x
  | Sum.inr y => if K ≤ y ∧ (⟨s, y - K⟩ : Σ s : S.Srt, Vinfinite S s) ∈ D then Sum.inl (y - K)
      else Sum.inr y

open scoped Classical in
theorem crossSwapFun_involutive (K : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s)) (s : S.Srt) :
    Function.Involutive (crossSwapFun (S := S) K D s) := by
  intro v
  rcases v with x | y
  · by_cases hx : (⟨s, x⟩ : Σ s : S.Srt, Vinfinite S s) ∈ D
    · have h1 : crossSwapFun (S := S) K D s (Sum.inl x) = Sum.inr (x + K) := if_pos hx
      have h2 : crossSwapFun (S := S) K D s (Sum.inr (x + K)) = Sum.inl (x + K - K) :=
        if_pos ⟨Nat.le_add_left _ _, by rw [Nat.add_sub_cancel]; exact hx⟩
      rw [h1, h2, Nat.add_sub_cancel]
    · have h1 : crossSwapFun (S := S) K D s (Sum.inl x) = Sum.inl x := if_neg hx
      rw [h1, h1]
  · by_cases hy : K ≤ y ∧ (⟨s, y - K⟩ : Σ s : S.Srt, Vinfinite S s) ∈ D
    · have h1 : crossSwapFun (S := S) K D s (Sum.inr y) = Sum.inl (y - K) := if_pos hy
      have h2 : crossSwapFun (S := S) K D s (Sum.inl (y - K)) = Sum.inr (y - K + K) := if_pos hy.2
      rw [h1, h2, Nat.sub_add_cancel hy.1]
    · have h1 : crossSwapFun (S := S) K D s (Sum.inr y) = Sum.inr y := if_neg hy
      rw [h1, h1]

open scoped Classical in
/-- **The fresh cross swap.** -/
noncomputable def crossSwap (K : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s)) :
    ∀ s, Equiv.Perm (PoolVertex S s) :=
  fun s => (crossSwapFun_involutive K D s).toPerm

open scoped Classical in
theorem crossSwap_apply (K : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s)) (s : S.Srt)
    (v : PoolVertex S s) : crossSwap (S := S) K D s v = crossSwapFun K D s v := rfl

open scoped Classical in
/-- An original vertex outside `D` is fixed. -/
theorem crossSwap_original_of_notMem (K : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s))
    {w : Σ s : S.Srt, Vinfinite S s} (hw : w ∉ D) :
    crossSwap (S := S) K D w.1 (originalVertex S w.1 w.2) = originalVertex S w.1 w.2 := by
  show crossSwapFun K D w.1 (Sum.inl w.2) = Sum.inl w.2
  simp [crossSwapFun, hw]

open scoped Classical in
/-- An original vertex of `D` goes to the spare copy of its translate. -/
theorem crossSwap_original_of_mem (K : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s))
    {w : Σ s : S.Srt, Vinfinite S s} (hw : w ∈ D) :
    crossSwap (S := S) K D w.1 (originalVertex S w.1 w.2) = poolVertex S w.1 (w.2 + K) := by
  show crossSwapFun K D w.1 (Sum.inl w.2) = Sum.inr (w.2 + K)
  simp [crossSwapFun, hw]

open scoped Classical in
/-- A spare vertex below `K` is fixed. -/
theorem crossSwap_pool_of_lt (K : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s)) (s : S.Srt)
    {y : ℕ} (hy : y < K) : crossSwap (S := S) K D s (Sum.inr y) = Sum.inr y := by
  show crossSwapFun K D s (Sum.inr y) = Sum.inr y
  simp [crossSwapFun, not_le.mpr hy]

open scoped Classical in
/-- **Every moved vertex lies in both halves of the layout `D ∪ (D + K)`.** -/
theorem mem_bothHalves_of_crossSwap_ne (K : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s))
    (v : Σ s : S.Srt, PoolVertex S s) (hv : crossSwap K D v.1 v.2 ≠ v.2) :
    v ∈ bothHalves (D ∪ shiftSet K D) := by
  obtain ⟨s, x | y⟩ := v
  · by_cases hx : (⟨s, x⟩ : Σ s : S.Srt, Vinfinite S s) ∈ D
    · exact Or.inl ⟨⟨s, x⟩, Finset.mem_union_left _ hx, rfl⟩
    · exact absurd (by simp [crossSwap_apply, crossSwapFun, hx]) hv
  · by_cases hy : K ≤ y ∧ (⟨s, y - K⟩ : Σ s : S.Srt, Vinfinite S s) ∈ D
    · refine Or.inr ⟨⟨s, y⟩,
        Finset.mem_union_right _ (mem_shiftSet.mpr ⟨⟨s, y - K⟩, hy.2, ?_⟩), rfl⟩
      show (⟨s, y - K + K⟩ : Σ s : S.Srt, Vinfinite S s) = ⟨s, y⟩
      rw [Nat.sub_add_cancel hy.1]
    · exact absurd (by simp [crossSwap_apply, crossSwapFun, hy]) hv

open scoped Classical in
/-- **The swap is supported inside the stage-`0` reservoir of the layout `D ∪ (D + K)`.** -/
theorem crossSwap_fix_of_notMem (N K : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s)) :
    ∀ v : Σ s : S.Srt, PoolVertex S s, v ∉ reservoir N (D ∪ shiftSet K D) 0 →
      crossSwap (S := S) K D v.1 v.2 = v.2 := by
  intro v hv
  by_contra hne
  refine hv (bothHalves_subset_reservoir N (D ∪ shiftSet K D) 0 ?_)
  rw [pollBlock_zero]
  exact mem_bothHalves_of_crossSwap_ne K D v hne

open scoped Classical in
/-- The swap has finite support on both halves and finitely many active sorts. -/
theorem pooledFiniteActive_crossSwap (K : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s)) :
    PooledFiniteActive (crossSwap (S := S) K D) := by
  refine ⟨⟨(D.sup fun v => v.2) + K + 1, fun s x hx => ⟨?_, ?_⟩⟩,
    ⟨D.image Sigma.fst, fun s hs => ?_⟩⟩
  · have hnot : (⟨s, x⟩ : Σ s : S.Srt, Vinfinite S s) ∉ D := fun h => by
      have h3 : x ≤ D.sup fun v : Σ s : S.Srt, Vinfinite S s => v.2 :=
        Finset.le_sup (f := fun v : Σ s : S.Srt, Vinfinite S s => v.2) h
      omega
    simp [crossSwap_apply, crossSwapFun, hnot]
  · have hnot : ¬ (K ≤ x ∧ (⟨s, x - K⟩ : Σ s : S.Srt, Vinfinite S s) ∈ D) := by
      rintro ⟨-, h⟩
      have h3 : x - K ≤ D.sup fun v : Σ s : S.Srt, Vinfinite S s => v.2 :=
        Finset.le_sup (f := fun v : Σ s : S.Srt, Vinfinite S s => v.2) h
      omega
    simp [crossSwap_apply, crossSwapFun, hnot]
  · have hnot : ∀ y : ℕ, (⟨s, y⟩ : Σ s : S.Srt, Vinfinite S s) ∉ D := fun y h =>
      hs (Finset.mem_image_of_mem Sigma.fst h)
    ext v
    rcases v with x | y <;> simp [crossSwap_apply, crossSwapFun, hnot]

open scoped Classical in
theorem crossSwap_eq_one (K : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s)) :
    ∃ T : Finset S.Srt, ∀ s, s ∉ T → crossSwap (S := S) K D s = 1 :=
  (pooledFiniteActive_crossSwap K D).2

/-! ### What the swap does to supports -/

open scoped Classical in
/-- **A support meeting `D` is carried onto a mixed support**: the vertices in `D` become spare.
-/
theorem crossSwap_mixed_of_meets (K : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s))
    {X : Finset (Σ s : S.Srt, PoolVertex S s)} {w : Σ s : S.Srt, Vinfinite S s} (hw : w ∈ D)
    (hwX : Sigma.map id (fun s => ⇑(originalVertex S s)) w ∈ X) :
    ∃ v ∈ X.image (Sigma.map id fun s => ⇑(crossSwap (S := S) K D s)), Sum.isRight v.2 := by
  refine ⟨_, Finset.mem_image_of_mem _ hwX, ?_⟩
  show Sum.isRight (crossSwap K D w.1 (originalVertex S w.1 w.2)) = true
  rw [crossSwap_original_of_mem K D hw]
  rfl

open scoped Classical in
/-- **A mixed support whose vertices lie below `K` stays mixed**: its spare vertices are fixed. -/
theorem crossSwap_mixed_of_fresh (K : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s))
    {X : Finset (Σ s : S.Srt, PoolVertex S s)} (hX : ∀ v ∈ X, poolValue v < K)
    (hmix : ∃ v ∈ X, Sum.isRight v.2) :
    ∃ v ∈ X.image (Sigma.map id fun s => ⇑(crossSwap (S := S) K D s)), Sum.isRight v.2 := by
  obtain ⟨v, hv, hvr⟩ := hmix
  refine ⟨_, Finset.mem_image_of_mem _ hv, ?_⟩
  obtain ⟨s, x | y⟩ := v
  · exact absurd hvr (by simp)
  · show Sum.isRight (crossSwap K D s (Sum.inr y)) = true
    rw [crossSwap_pool_of_lt K D s (y := y) (hX ⟨s, Sum.inr y⟩ hv)]
    rfl

/-! ### The conditional-expectation invariance

Before insertion: `q = E[f_e | 𝔅_fix]` is almost surely fixed by the cross swap. The stage
invariance theorem preserves the σ-algebra of the stage at the layout `D ∪ (D + K)`, which alone
fixes no function; combined with the tail identity `q =ᵐ E[f_e | ℱ 0]`, the transport of
conditional expectation along the measure-preserving swap, and the a.e. invariance of `f_e`, it
fixes `q`. -/

variable {n : ℕ} [Countable S.Srt] [Countable S.Rel] {M : InfiniteRelExchangeableLaw S}
  {C : M.RankRepresentation n}

/-- The cross swap as a joint relabeling of the pooled space. -/
noncomputable def crossSwapJoint (K : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s)) (n : ℕ) :
    RelStructure S (PoolVertex S) × PooledRankLatentSpace S n →
      RelStructure S (PoolVertex S) × PooledRankLatentSpace S n :=
  pooledJointRelabel (crossSwap K D) n

theorem measurePreserving_crossSwapJoint (Q : PooledRankExtension C) (K : ℕ)
    (D : Finset (Σ s : S.Srt, Vinfinite S s)) :
    MeasurePreserving (crossSwapJoint K D n)
      (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))
      (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) :=
  ⟨measurable_pooledJointRelabel _ n, Q.invariant _⟩

open scoped Classical in
/-- **The target's conditional probability given `𝔅_fix` is fixed by the cross swap**, almost
surely under the pooled law. -/
theorem condExp_fixBase_comp_crossSwapJoint (Q : PooledRankExtension C) (N : ℕ) [NeZero N]
    (K : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s))
    (hD₀ : ∀ v ∈ D ∪ shiftSet K D, v.2 < N)
    {A : Finset (Σ s : S.Srt, Vinfinite S s)} (hA : ∀ v ∈ A, v.2 < N)
    (hAD : ∀ v ∈ A, v ∉ D ∪ shiftSet K D)
    {E : Set (RelStructure S (PoolVertex S))}
    (hE : MeasurableSet[pooledFiniteActiveFixingAlgebra (supportImage (originalVertex S) A)] E) :
    ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        Prod.fst ⁻¹' E | fixBase n⟧) ∘ crossSwapJoint K D n
      =ᵐ[(Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))]
    ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        Prod.fst ⁻¹' E | fixBase n⟧) := by
  haveI := C.isProbabilityMeasure_P
  set μ : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) :=
    (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) with hμ
  obtain ⟨E₀, hE₀, hEeq⟩ := hE
  have hEmeas : MeasurableSet E := by
    rw [← hEeq]; exact (poolStructureEquiv S).measurable (hE₀.1)
  have hMP : MeasurePreserving (crossSwapJoint K D n) μ μ := measurePreserving_crossSwapJoint Q K D
  -- the tail identity, at the layout `D ∪ (D + K)`
  have htail := condExp_fixBase_eq_fixReservoirFiltration_zero N (D ∪ shiftSet K D) Q hD₀ hA hAD
    ⟨E₀, hE₀, hEeq⟩
  -- the swap fixes the stage-`0` conditioning algebra exactly
  have hstage : MeasurableSpace.comap (crossSwapJoint K D n)
      (fixReservoirFiltration N (D ∪ shiftSet K D) n 0) =
      fixReservoirFiltration N (D ∪ shiftSet K D) n 0 :=
    comap_pooledJointRelabel_fixStage_of_fix (crossSwap_eq_one K D)
      (crossSwap_fix_of_notMem N K D)
  -- and the target's event almost surely
  have hfix : ∀ v ∈ supportImage (originalVertex S) A, crossSwap (S := S) K D v.1 v.2 = v.2 := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := (mem_supportImage_iff _ _ _).mp hv
    exact crossSwap_original_of_notMem K D fun h => hAD w hw (Finset.mem_union_left _ h)
  have hinv := Q.relabel_preimage_ae_eq_of_pooledFiniteActiveFixingAlgebra_fst ⟨E₀, hE₀, hEeq⟩
    (crossSwap_eq_one K D) hfix
  have hfσ : (Prod.fst ⁻¹' E).indicator (fun _ => (1 : ℝ)) ∘ crossSwapJoint K D n
      =ᵐ[μ] (Prod.fst ⁻¹' E).indicator (fun _ => (1 : ℝ)) :=
    indicator_ae_eq_of_ae_eq_set hinv
  have hint : Integrable ((Prod.fst ⁻¹' E).indicator fun _ => (1 : ℝ)) μ :=
    (integrable_const 1).indicator (measurable_fst hEmeas)
  calc (μ⟦Prod.fst ⁻¹' E | fixBase n⟧) ∘ crossSwapJoint K D n
      =ᵐ[μ] (μ⟦Prod.fst ⁻¹' E | fixReservoirFiltration N (D ∪ shiftSet K D) n 0⟧) ∘
          crossSwapJoint K D n :=
        hMP.quasiMeasurePreserving.ae_eq_comp htail
    _ =ᵐ[μ] μ[(Prod.fst ⁻¹' E).indicator (fun _ => (1 : ℝ)) ∘ crossSwapJoint K D n |
          MeasurableSpace.comap (crossSwapJoint K D n)
            (fixReservoirFiltration N (D ∪ shiftSet K D) n 0)] :=
        (condExp_comp_of_measurePreserving (measurable_pooledJointRelabel _ n) hMP
          ((fixReservoirFiltration N (D ∪ shiftSet K D) n).le 0) hint).symm
    _ =ᵐ[μ] μ⟦Prod.fst ⁻¹' E | fixReservoirFiltration N (D ∪ shiftSet K D) n 0⟧ := by
        rw [hstage]
        exact condExp_congr_ae hfσ
    _ =ᵐ[μ] μ⟦Prod.fst ⁻¹' E | fixBase n⟧ := htail.symm

end RelSignature
