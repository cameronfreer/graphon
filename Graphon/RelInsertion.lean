/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelFixingStages

/-!
# The insertion step (R4 converse, #107, #197)

The second analytic step of the pooled fixing-factor polling argument, ending in the mutual
conditional independence of the pooled fixing events given `𝔅_fix`. Given the target support
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
* `crossSwap_mixed_of_meets` — a remainder support meeting `D` is carried onto a **mixed**
  support; `crossSwap_mixed_of_fresh` — a mixed support whose vertices lie below `K` stays mixed.
* `crossSwapJoint` — the swap acting on the enriched carrier, measure preserving, and leaving
  `𝔅_fix`-conditional expectations invariant (`condExp_fixBase_comp_crossSwapJoint`).
* `fixBaseCylinders` — the generating π-system of `𝔅_fix` (`fixBase_eq_generateFrom`).
* `setIntegral_insertion_cylinder` — the generator identity: over a remainder event and a
  cylinder, the target's fixing indicator integrates like its `𝔅_fix`-conditional probability.
* `setIntegral_insertion` — the identity on every `𝔅_fix`-event, by the π-λ theorem.
* `condExp_insertion` — the conditional factorization of the target against the remainder.
* `condExp_iInter_fixing_eq_prod` — **mutual** conditional independence of any finite family of
  pooled fixing events given `𝔅_fix`.
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

/-! ### `𝔅_fix` as an indexed join, and its generating π-system -/

/-- The generators of `𝔅_fix`: one latent coordinate, or the fixing algebra at one mixed
support. -/
abbrev FixBaseIndex (S : RelSignature.{u}) (n : ℕ) :=
  PooledRankLatentIndex S n ⊕ MixedClusterIndex S n

/-- The σ-algebra of one generator. -/
@[implicit_reducible]
noncomputable def fixBaseGen (n : ℕ) :
    FixBaseIndex S n →
      MeasurableSpace (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)
  | .inl I => MeasurableSpace.comap (fun p => p.2 I) inferInstance
  | .inr X => MeasurableSpace.comap
      (Prod.fst : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → _)
      (pooledFiniteActiveFixingAlgebra X.1)

omit [Countable S.Srt] [Countable S.Rel] in
open scoped Classical in
/-- **`𝔅_fix` is the join of its generators.** -/
theorem fixBase_eq_iSup : fixBase (S := S) n = ⨆ i, fixBaseGen n i := by
  rw [fixBase, fixStage, iSup_sum (f := fixBaseGen (S := S) n)]
  congr 1
  · -- the latent half is the join of the latent coordinates
    rw [latentStage, show (inferInstance : MeasurableSpace (AvoidLatentIndex S n ∅ → ℝ)) =
        MeasurableSpace.pi from rfl, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine le_antisymm (iSup_le fun I => ?_) (iSup_le fun I => ?_)
    · rw [MeasurableSpace.comap_comp]
      exact le_iSup (fun I : PooledRankLatentIndex S n => fixBaseGen (S := S) n (.inl I)) I.1
    · refine le_iSup_of_le ⟨I, fun _ _ h => h⟩ ?_
      rw [MeasurableSpace.comap_comp]
      exact le_rfl
  · rw [fixingStage]
    refine le_antisymm (iSup_le fun X => ?_) (iSup_le fun X => ?_)
    · exact le_iSup (fun X : MixedClusterIndex S n => fixBaseGen (S := S) n (.inr X)) X.1
    · exact le_iSup (fun X : MixedAvoiding S n ∅ => MeasurableSpace.comap
        (Prod.fst : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → _)
        (pooledFiniteActiveFixingAlgebra X.1.1)) ⟨X, fun _ _ h => h⟩

/-- The generating π-system: finite intersections of generator events. -/
def fixBaseCylinders (S : RelSignature.{u}) (n : ℕ) :
    Set (Set (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) :=
  piiUnionInter (fun i => {s | MeasurableSet[fixBaseGen (S := S) n i] s}) Set.univ

omit [Countable S.Srt] [Countable S.Rel] in
theorem isPiSystem_fixBaseCylinders : IsPiSystem (fixBaseCylinders S n) :=
  isPiSystem_piiUnionInter _ (fun i => @MeasurableSpace.isPiSystem_measurableSet _
    (fixBaseGen (S := S) n i)) _

omit [Countable S.Srt] [Countable S.Rel] in
theorem fixBase_eq_generateFrom :
    fixBase (S := S) n = MeasurableSpace.generateFrom (fixBaseCylinders S n) := by
  rw [fixBaseCylinders, generateFrom_piiUnionInter_measurableSet (fixBaseGen (S := S) n) Set.univ,
    fixBase_eq_iSup]
  simp only [Set.mem_univ, iSup_true]

omit [Countable S.Srt] [Countable S.Rel] in
theorem fixBaseGen_le (i : FixBaseIndex S n) : fixBaseGen (S := S) n i ≤ fixBase n := by
  rw [fixBase_eq_iSup]; exact le_iSup (fixBaseGen (S := S) n) i

/-- The pooled vertices a generator index reads: the latent support, or the mixed anchor. -/
def genSupport (n : ℕ) : FixBaseIndex S n → Finset (Σ s : S.Srt, PoolVertex S s)
  | .inl I => I.1
  | .inr X => X.1

/-! ### Transport of generator events under the cross swap -/

omit [Countable S.Srt] [Countable S.Rel] in
open scoped Classical in
/-- A latent-coordinate event is carried by any joint relabeling into the latent half. -/
theorem comap_pooledJointRelabel_fixBaseGen_inl (ρ : ∀ s, Equiv.Perm (PoolVertex S s))
    (I : PooledRankLatentIndex S n) :
    MeasurableSpace.comap (pooledJointRelabel ρ n) (fixBaseGen (S := S) n (.inl I)) ≤
      fixBase n := by
  rw [fixBaseGen, MeasurableSpace.comap_comp, fixBase_eq_iSup]
  refine le_trans (le_of_eq ?_) (le_iSup (fixBaseGen (S := S) n) (.inl (latentIndexPerm ρ n I)))
  rfl

omit [Countable S.Srt] [Countable S.Rel] in
open scoped Classical in
/-- A generator event at a mixed anchor is carried by a finite-active joint relabeling into the
fixing algebra at the moved anchor, which lies in `𝔅_fix` when that anchor stays mixed. -/
theorem comap_pooledJointRelabel_fixBaseGen_inr {ρ : ∀ s, Equiv.Perm (PoolVertex S s)}
    (hρfin : ∃ T : Finset S.Srt, ∀ s, s ∉ T → ρ s = 1) (X : MixedClusterIndex S n)
    (hmix : ∃ v ∈ X.1.image (Sigma.map id fun s => ⇑(ρ s)), Sum.isRight v.2) :
    MeasurableSpace.comap (pooledJointRelabel ρ n) (fixBaseGen (S := S) n (.inr X)) ≤
      fixBase n := by
  rw [fixBaseGen, MeasurableSpace.comap_comp, show (Prod.fst ∘ pooledJointRelabel ρ n :
      RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → RelStructure S (PoolVertex S)) =
      RelStructure.relabel ρ ∘ Prod.fst from rfl,
    ← MeasurableSpace.comap_comp, comap_relabel_pooledFiniteActiveFixingAlgebra hρfin,
    fixBase_eq_iSup]
  have hcard : (X.1.image (Sigma.map id fun s => ⇑(ρ s))).card = n := by
    rw [Finset.card_image_of_injective _ (Function.injective_id.sigma_map fun s => (ρ s).injective)]
    exact X.2.1
  exact le_iSup (fixBaseGen (S := S) n) (.inr ⟨_, hcard, hmix⟩)

omit [Countable S.Srt] [Countable S.Rel] in
open scoped Classical in
/-- Every generator event of a finite cylinder is carried into `𝔅_fix` by the cross swap, once
`K` exceeds the cylinder's footprint. -/
theorem comap_crossSwapJoint_fixBaseGen_le (K : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s))
    (i : FixBaseIndex S n) (hK : ∀ v ∈ genSupport n i, poolValue v < K) :
    MeasurableSpace.comap (crossSwapJoint K D n) (fixBaseGen (S := S) n i) ≤ fixBase n := by
  cases i with
  | inl I => exact comap_pooledJointRelabel_fixBaseGen_inl _ I
  | inr X =>
    exact comap_pooledJointRelabel_fixBaseGen_inr (crossSwap_eq_one K D) X
      (crossSwap_mixed_of_fresh K D (fun v hv => hK v hv) X.2.2)

omit [Countable S.Srt] [Countable S.Rel] in
open scoped Classical in
/-- A remainder support's fixing algebra is carried into `𝔅_fix` by the cross swap, provided
the support meets `D`. -/
theorem comap_crossSwapJoint_remainder_le (K : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s))
    (A : RankSupport S n) {w : Σ s : S.Srt, Vinfinite S s} (hwD : w ∈ D) (hwA : w ∈ A.1) :
    MeasurableSpace.comap (crossSwapJoint K D n) (MeasurableSpace.comap
      (Prod.fst : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → _)
      (pooledFiniteActiveFixingAlgebra (supportImage (originalVertex S) A.1))) ≤ fixBase n := by
  have hcard : (supportImage (originalVertex S) A.1).card = n := by
    rw [card_supportImage]; exact A.2
  have hmix : ∃ v ∈ (supportImage (originalVertex S) A.1).image
      (Sigma.map id fun s => ⇑(crossSwap (S := S) K D s)), Sum.isRight v.2 :=
    crossSwap_mixed_of_meets K D hwD ((mem_supportImage_iff _ _ _).mpr ⟨w, hwA, rfl⟩)
  -- reuse the mixed-anchor transport with the moved support supplied directly
  rw [MeasurableSpace.comap_comp, show (Prod.fst ∘ crossSwapJoint K D n :
      RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → RelStructure S (PoolVertex S)) =
      RelStructure.relabel (crossSwap K D) ∘ Prod.fst from rfl,
    ← MeasurableSpace.comap_comp,
    comap_relabel_pooledFiniteActiveFixingAlgebra (crossSwap_eq_one K D), fixBase_eq_iSup]
  have hcard' : ((supportImage (originalVertex S) A.1).image
      (Sigma.map id fun s => ⇑(crossSwap (S := S) K D s))).card = n := by
    rw [Finset.card_image_of_injective _
      (Function.injective_id.sigma_map fun s => (crossSwap K D s).injective)]
    exact hcard
  exact le_iSup (fixBaseGen (S := S) n) (.inr ⟨_, hcard', hmix⟩)

/-! ### The generator integral identity -/

omit [Countable S.Srt] [Countable S.Rel] in
open scoped Classical in
/-- The cross swap, as a joint relabeling, is an involution. -/
theorem crossSwapJoint_comp_self (K : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s)) (n : ℕ) :
    crossSwapJoint (S := S) K D n ∘ crossSwapJoint K D n = id := by
  have hmul : ∀ s, crossSwap (S := S) K D s * crossSwap K D s = 1 := fun s =>
    Equiv.ext fun x => crossSwapFun_involutive K D s x
  funext p
  refine Prod.ext ?_ ?_
  · show RelStructure.comap _ (RelStructure.comap _ p.1) = p.1
    rw [← RelStructure.comap_comp]
    convert RelStructure.comap_id p.1 using 2
    funext s x
    exact crossSwapFun_involutive K D s x
  · show pooledRankLatentRelabel (crossSwap K D) n (pooledRankLatentRelabel (crossSwap K D) n p.2)
      = p.2
    funext I
    rw [pooledRankLatentRelabel_apply, pooledRankLatentRelabel_apply]
    have h := congrFun (congrArg (fun e : PooledRankLatentIndex S n ≃ PooledRankLatentIndex S n =>
      ⇑e) (latentIndexPerm_comp (S := S) (crossSwap K D) (crossSwap K D) n)) I
    simp only [Equiv.trans_apply] at h
    rw [← h, show (fun s => crossSwap (S := S) K D s * crossSwap K D s) = fun _ => 1 from
      funext hmul, latentIndexPerm_one, Equiv.refl_apply]

omit [Countable S.Srt] [Countable S.Rel] in
open scoped Classical in
/-- The cross swap as a measurable equivalence of the pooled space. -/
noncomputable def crossSwapJointEquiv (K : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s)) (n : ℕ) :
    (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) ≃ᵐ
      (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) where
  toFun := crossSwapJoint K D n
  invFun := crossSwapJoint K D n
  left_inv := fun p => congrFun (crossSwapJoint_comp_self K D n) p
  right_inv := fun p => congrFun (crossSwapJoint_comp_self K D n) p
  measurable_toFun := measurable_pooledJointRelabel _ n
  measurable_invFun := measurable_pooledJointRelabel _ n

open scoped Classical in
/-- **The generator integral identity.** For the target `e`, a remainder family `F ∌ e` of rank-`n`
supports, `D ⊇ (⋃ F) \ e` disjoint from `e`, and a finite cylinder `⋂ i ∈ t, f i` of generator
events, with `K` above every vertex of the target, the remainder, and the cylinder's footprint
and `N` above the target and the layout `D ∪ (D + K)`:

`∫_{G ∩ H} 1_{E_e} = ∫_{G ∩ H} E[1_{E_e} | 𝔅_fix]`

where `G` is the intersection of the remainder's fixing events and `H` the cylinder. The cross
swap at `K` carries `G ∩ H` into `𝔅_fix` while fixing `1_{E_e}` and `E[1_{E_e} | 𝔅_fix]` almost
surely. -/
theorem setIntegral_insertion_cylinder (Q : PooledRankExtension C) (N : ℕ) [NeZero N] (K : ℕ)
    (D : Finset (Σ s : S.Srt, Vinfinite S s)) (e : RankSupport S n) (F : Finset (RankSupport S n))
    (heF : e ∉ F) (hDe : ∀ w ∈ D, w ∉ e.1) (hFD : ∀ A ∈ F, ∀ w ∈ A.1, w ∉ e.1 → w ∈ D)
    (hKe : ∀ w ∈ e.1, w.2 < K) (hN : ∀ v ∈ D ∪ shiftSet K D, v.2 < N) (hNe : ∀ w ∈ e.1, w.2 < N)
    {E : RankSupport S n → Set (RelStructure S (PoolVertex S))}
    (hE : ∀ A, MeasurableSet[pooledFiniteActiveFixingAlgebra (supportImage (originalVertex S) A.1)]
      (E A))
    (t : Finset (FixBaseIndex S n))
    {f : FixBaseIndex S n → Set (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)}
    (hf : ∀ i ∈ t, MeasurableSet[fixBaseGen n i] (f i))
    (hKt : ∀ i ∈ t, ∀ v ∈ genSupport n i, poolValue v < K) :
    ∫ x in (⋂ A ∈ F, Prod.fst ⁻¹' E A) ∩ ⋂ i ∈ t, f i,
        (Prod.fst ⁻¹' E e).indicator (fun _ => (1 : ℝ)) x
        ∂(Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) =
      ∫ x in (⋂ A ∈ F, Prod.fst ⁻¹' E A) ∩ ⋂ i ∈ t, f i,
        ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
          Prod.fst ⁻¹' E e | fixBase n⟧) x
        ∂(Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) := by
  haveI := C.isProbabilityMeasure_P
  set μ : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) :=
    (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) with hμ
  set σ := crossSwapJoint (S := S) K D n with hσ
  set G : Set (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) :=
    (⋂ A ∈ F, Prod.fst ⁻¹' E A) ∩ ⋂ i ∈ t, f i with hG
  set E' : Set (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) := Prod.fst ⁻¹' E e
    with hE'
  have hEmeas : ∀ A, MeasurableSet (E A) := fun A =>
    pooledFiniteActiveFixingAlgebra_le _ _ (hE A)
  have hE'meas : MeasurableSet E' := measurable_fst (hEmeas e)
  have hGmeas : MeasurableSet G := by
    refine (Finset.measurableSet_biInter F fun A _ => measurable_fst (hEmeas A)).inter
      (Finset.measurableSet_biInter t fun i hi => fixStage_le _ _ (fixBaseGen_le i _ (hf i hi)))
  have hMP : MeasurePreserving σ μ μ := measurePreserving_crossSwapJoint Q K D
  -- the swap carries `G` into `𝔅_fix`
  have hσG : MeasurableSet[fixBase n] (σ ⁻¹' G) := by
    rw [hG, Set.preimage_inter, Set.preimage_iInter₂, Set.preimage_iInter₂]
    refine MeasurableSet.inter ?_ ?_
    · refine MeasurableSet.biInter F.countable_toSet fun A hA => ?_
      -- a remainder support differs from the target, hence meets `D`
      have hne : A ≠ e := fun h => heF (h ▸ hA)
      obtain ⟨w, hwA, hwe⟩ : ∃ w ∈ A.1, w ∉ e.1 := by
        by_contra hall
        push Not at hall
        exact hne (Subtype.ext (Finset.eq_of_subset_of_card_le hall (by rw [A.2, e.2])))
      exact comap_crossSwapJoint_remainder_le K D A (hFD A hA w hwA hwe) hwA _
        ⟨_, ⟨E A, hE A, rfl⟩, rfl⟩
    · exact MeasurableSet.biInter t.countable_toSet fun i hi =>
        comap_crossSwapJoint_fixBaseGen_le K D i (hKt i hi) _ ⟨f i, hf i hi, rfl⟩
  -- the swap fixes the target's event almost surely, and its conditional probability
  have hAD : ∀ w ∈ e.1, w ∉ D ∪ shiftSet K D := by
    intro w hw hmem
    rcases Finset.mem_union.mp hmem with h | h
    · exact hDe w h hw
    · obtain ⟨u, -, hu⟩ := mem_shiftSet.mp h
      subst hu
      exact absurd (hKe _ hw) (not_lt.mpr (Nat.le_add_left K u.2))
  have hfix : ∀ v ∈ supportImage (originalVertex S) e.1, crossSwap (S := S) K D v.1 v.2 = v.2 := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := (mem_supportImage_iff _ _ _).mp hv
    exact crossSwap_original_of_notMem K D fun h => hAD w hw (Finset.mem_union_left _ h)
  have hinv : σ ⁻¹' E' =ᵐ[μ] E' :=
    Q.relabel_preimage_ae_eq_of_pooledFiniteActiveFixingAlgebra_fst (hE e) (crossSwap_eq_one K D)
      hfix
  have hqσ := condExp_fixBase_comp_crossSwapJoint Q N K D hN hNe hAD (hE e)
  have hint : Integrable (E'.indicator fun _ => (1 : ℝ)) μ :=
    (integrable_const 1).indicator hE'meas
  -- both sides as masses and set integrals
  rw [setIntegral_indicator hE'meas, setIntegral_const, smul_eq_mul, mul_one]
  have h1 : μ.real (G ∩ E') = μ.real (σ ⁻¹' G ∩ E') := by
    rw [measureReal_def, measureReal_def,
      ← hMP.measure_preimage (hGmeas.inter hE'meas).nullMeasurableSet, Set.preimage_inter,
      measure_congr ((Filter.EventuallyEq.refl _ _).inter hinv)]
  have h2 : μ.real (σ ⁻¹' G ∩ E') = ∫ x in σ ⁻¹' G, (μ⟦E' | fixBase n⟧) x ∂μ := by
    rw [setIntegral_condExp (fixStage_le _) hint hσG, setIntegral_indicator hE'meas,
      setIntegral_const, smul_eq_mul, mul_one]
  have h3 : ∫ x in σ ⁻¹' G, (μ⟦E' | fixBase n⟧) x ∂μ =
      ∫ x in G, ((μ⟦E' | fixBase n⟧) ∘ σ) x ∂μ := by
    have hpre := hMP.setIntegral_preimage_emb (crossSwapJointEquiv K D n).measurableEmbedding
      (μ⟦E' | fixBase n⟧) (σ ⁻¹' G)
    rw [← hpre, ← Set.preimage_comp, hσ, crossSwapJoint_comp_self, Set.preimage_id]
    rfl
  have h4 : ∫ x in G, ((μ⟦E' | fixBase n⟧) ∘ σ) x ∂μ = ∫ x in G, (μ⟦E' | fixBase n⟧) x ∂μ :=
    setIntegral_congr_ae hGmeas (hqσ.mono fun x hx _ => hx)
  rw [h1, h2, h3, h4]

/-! ### Extension to `𝔅_fix`, the factorization, and mutuality -/

/-- The set `D = (⋃ F) \ e`. -/
noncomputable def remainderSet (e : RankSupport S n) (F : Finset (RankSupport S n)) :
    Finset (Σ s : S.Srt, Vinfinite S s) := by
  classical
  exact (F.biUnion fun A => A.1) \ e.1

open scoped Classical in
/-- **The insertion identity on every `𝔅_fix`-event.** Extension of the generator identity by
the π-λ theorem: the cylinders form a π-system generating `𝔅_fix`, the identity is stable under
complement (using the cylinder `univ`) and countable disjoint union, and for each cylinder the
bounds `K` and `N` are chosen after it. -/
theorem setIntegral_insertion (Q : PooledRankExtension C) (e : RankSupport S n)
    (F : Finset (RankSupport S n)) (heF : e ∉ F)
    {E : RankSupport S n → Set (RelStructure S (PoolVertex S))}
    (hE : ∀ A, MeasurableSet[pooledFiniteActiveFixingAlgebra (supportImage (originalVertex S) A.1)]
      (E A))
    {H : Set (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)}
    (hH : MeasurableSet[fixBase n] H) :
    ∫ x in (⋂ A ∈ F, Prod.fst ⁻¹' E A) ∩ H, (Prod.fst ⁻¹' E e).indicator (fun _ => (1 : ℝ)) x
        ∂(Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) =
      ∫ x in (⋂ A ∈ F, Prod.fst ⁻¹' E A) ∩ H,
        ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
          Prod.fst ⁻¹' E e | fixBase n⟧) x
        ∂(Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) := by
  haveI := C.isProbabilityMeasure_P
  set μ : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) :=
    (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) with hμ
  set G : Set (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) :=
    ⋂ A ∈ F, Prod.fst ⁻¹' E A with hG
  set g₁ : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → ℝ :=
    (Prod.fst ⁻¹' E e).indicator fun _ => (1 : ℝ) with hg₁
  set g₂ : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → ℝ :=
    μ⟦Prod.fst ⁻¹' E e | fixBase n⟧ with hg₂
  have hEmeas : ∀ A, MeasurableSet (E A) := fun A =>
    pooledFiniteActiveFixingAlgebra_le _ _ (hE A)
  have hGmeas : MeasurableSet G :=
    Finset.measurableSet_biInter F fun A _ => measurable_fst (hEmeas A)
  have hg₁ : Integrable g₁ μ := (integrable_const 1).indicator (measurable_fst (hEmeas e))
  have hg₂ : Integrable g₂ μ := integrable_condExp
  -- the bounds, chosen after a cylinder
  set D := remainderSet e F with hD
  have hDe : ∀ w ∈ D, w ∉ e.1 := fun w hw => (Finset.mem_sdiff.mp hw).2
  have hFD : ∀ A ∈ F, ∀ w ∈ A.1, w ∉ e.1 → w ∈ D := fun A hA w hw hwe =>
    Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨A, hA, hw⟩, hwe⟩
  -- the generator case
  have hbasic : ∀ H ∈ fixBaseCylinders S n,
      ∫ x in G ∩ H, g₁ x ∂μ = ∫ x in G ∩ H, g₂ x ∂μ := by
    rintro H ⟨t, -, f, hf, rfl⟩
    set K : ℕ := ((t.biUnion (genSupport n)).sup poolValue ⊔ e.1.sup (fun v => v.2)) + 1 with hK
    set N : ℕ := ((D ∪ shiftSet K D) ∪ e.1).sup (fun v => v.2) + 1 with hN
    haveI : NeZero N := ⟨Nat.succ_ne_zero _⟩
    have hKe : ∀ w ∈ e.1, w.2 < K := fun w hw => Nat.lt_succ_of_le
      (le_trans (Finset.le_sup (f := fun v : Σ s : S.Srt, Vinfinite S s => v.2) hw)
        le_sup_right)
    have hKt : ∀ i ∈ t, ∀ v ∈ genSupport n i, poolValue v < K := fun i hi v hv =>
      Nat.lt_succ_of_le (le_trans (Finset.le_sup (f := poolValue)
        (Finset.mem_biUnion.mpr ⟨i, hi, hv⟩)) le_sup_left)
    have hN' : ∀ v ∈ D ∪ shiftSet K D, v.2 < N := fun v hv => Nat.lt_succ_of_le
      (Finset.le_sup (f := fun v : Σ s : S.Srt, Vinfinite S s => v.2) (Finset.mem_union_left _ hv))
    have hNe : ∀ w ∈ e.1, w.2 < N := fun w hw => Nat.lt_succ_of_le
      (Finset.le_sup (f := fun v : Σ s : S.Srt, Vinfinite S s => v.2) (Finset.mem_union_right _ hw))
    exact setIntegral_insertion_cylinder Q N K D e F heF hDe hFD hKe hN' hNe hE t
      (fun i hi => hf i hi) hKt
  -- the universal case, from the empty cylinder
  have huniv : ∫ x in G, g₁ x ∂μ = ∫ x in G, g₂ x ∂μ := by
    have h := hbasic Set.univ ⟨∅, by simp, fun _ => Set.univ,
      fun _ h => absurd h (Finset.notMem_empty _), by simp⟩
    simpa only [Set.inter_univ] using h
  -- the π-λ extension
  refine MeasurableSpace.induction_on_inter (m := fixBase n)
    (C := fun H _ => ∫ x in G ∩ H, g₁ x ∂μ = ∫ x in G ∩ H, g₂ x ∂μ)
    fixBase_eq_generateFrom isPiSystem_fixBaseCylinders ?_ (fun H hH => hbasic H hH) ?_ ?_ H hH
  · simp only [Set.inter_empty, Measure.restrict_empty, integral_zero_measure]
  · intro H hHm ih
    have hHm' : MeasurableSet H := fixStage_le _ _ hHm
    have hsplit : ∀ g : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → ℝ,
        Integrable g μ → ∫ x in G ∩ Hᶜ, g x ∂μ = ∫ x in G, g x ∂μ - ∫ x in G ∩ H, g x ∂μ := by
      intro g hg
      have h := integral_add_compl (μ := μ.restrict G) hHm' hg.integrableOn
      rw [Measure.restrict_restrict hHm', Measure.restrict_restrict hHm'.compl,
        Set.inter_comm H, Set.inter_comm Hᶜ] at h
      linarith
    rw [hsplit g₁ hg₁, hsplit g₂ hg₂, huniv, ih]
  · intro f hdisj hfm ih
    have hfm' : ∀ i, MeasurableSet (f i) := fun i => fixStage_le _ _ (hfm i)
    have hdisj' : Pairwise (Function.onFun Disjoint fun i => G ∩ f i) := fun i j hij =>
      Disjoint.mono Set.inter_subset_right Set.inter_subset_right (hdisj hij)
    rw [Set.inter_iUnion, integral_iUnion (fun i => hGmeas.inter (hfm' i)) hdisj' hg₁.integrableOn,
      integral_iUnion (fun i => hGmeas.inter (hfm' i)) hdisj' hg₂.integrableOn]
    exact tsum_congr fun i => ih i

open scoped Classical in
/-- **The conditional insertion identity**: the target's fixing event and the remainder's fixing
events factor under conditioning on `𝔅_fix`. -/
theorem condExp_insertion (Q : PooledRankExtension C) (e : RankSupport S n)
    (F : Finset (RankSupport S n)) (heF : e ∉ F)
    {E : RankSupport S n → Set (RelStructure S (PoolVertex S))}
    (hE : ∀ A, MeasurableSet[pooledFiniteActiveFixingAlgebra (supportImage (originalVertex S) A.1)]
      (E A)) :
    ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        Prod.fst ⁻¹' E e ∩ ⋂ A ∈ F, Prod.fst ⁻¹' E A | fixBase n⟧)
      =ᵐ[(Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))]
    ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        Prod.fst ⁻¹' E e | fixBase n⟧) *
      ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        ⋂ A ∈ F, Prod.fst ⁻¹' E A | fixBase n⟧) := by
  haveI := C.isProbabilityMeasure_P
  set μ : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) :=
    (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) with hμ
  set G : Set (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) :=
    ⋂ A ∈ F, Prod.fst ⁻¹' E A with hG
  set E' : Set (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) := Prod.fst ⁻¹' E e
    with hE'
  have hEmeas : ∀ A, MeasurableSet (E A) := fun A =>
    pooledFiniteActiveFixingAlgebra_le _ _ (hE A)
  have hGmeas : MeasurableSet G :=
    Finset.measurableSet_biInter F fun A _ => measurable_fst (hEmeas A)
  have hE'meas : MeasurableSet E' := measurable_fst (hEmeas e)
  set q : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → ℝ := μ⟦E' | fixBase n⟧
    with hq
  have hqmeas : StronglyMeasurable[fixBase n] q := stronglyMeasurable_condExp
  obtain ⟨hq0, hq1⟩ := condExp_indicator_bounds (μ := μ) (fixStage_le _) hE'meas
  have hqbdd : ∀ᵐ x ∂μ, ‖q x‖ ≤ 1 := by
    filter_upwards [hq0, hq1] with x h0 h1
    rw [Pi.zero_apply] at h0
    rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith, h1⟩
  have hG_int : Integrable (G.indicator fun _ => (1 : ℝ)) μ := (integrable_const 1).indicator hGmeas
  have hqG_int : Integrable (q * G.indicator fun _ => (1 : ℝ)) μ :=
    hG_int.bdd_mul (hqmeas.mono (fixStage_le _)).aestronglyMeasurable hqbdd
  have hpull : μ[q * G.indicator (fun _ => (1 : ℝ)) | fixBase n] =ᵐ[μ]
      q * μ[G.indicator (fun _ => (1 : ℝ)) | fixBase n] :=
    condExp_mul_of_stronglyMeasurable_left hqmeas hqG_int hG_int
  have hqG : q * G.indicator (fun _ => (1 : ℝ)) = G.indicator q := by
    ext x; by_cases hx : x ∈ G <;> simp [hx]
  -- the candidate `q · E[1_G | 𝔅_fix]` has the right set integrals
  refine (ae_eq_condExp_of_forall_setIntegral_eq (fixStage_le _)
    ((integrable_const 1).indicator (hE'meas.inter hGmeas)) (fun s _ _ => ?_) (fun s hs _ => ?_)
    ?_).symm
  · exact (integrable_condExp.bdd_mul (hqmeas.mono (fixStage_le _)).aestronglyMeasurable
      hqbdd).integrableOn
  · have hs' : MeasurableSet s := fixStage_le _ _ hs
    calc ∫ x in s, (q * μ[G.indicator (fun _ => (1 : ℝ)) | fixBase n]) x ∂μ
        = ∫ x in s, (μ[q * G.indicator (fun _ => (1 : ℝ)) | fixBase n]) x ∂μ :=
          setIntegral_congr_ae hs' (hpull.mono fun x hx _ => hx.symm)
      _ = ∫ x in s, (q * G.indicator (fun _ => (1 : ℝ))) x ∂μ :=
          setIntegral_condExp (fixStage_le _) hqG_int hs
      _ = ∫ x in G ∩ s, q x ∂μ := by
          rw [hqG, setIntegral_indicator hGmeas, Set.inter_comm]
      _ = ∫ x in G ∩ s, E'.indicator (fun _ => (1 : ℝ)) x ∂μ :=
          (setIntegral_insertion Q e F heF hE hs).symm
      _ = ∫ x in s, (E' ∩ G).indicator (fun _ => (1 : ℝ)) x ∂μ := by
          rw [Set.inter_comm E' G, ← Set.indicator_indicator, setIntegral_indicator hGmeas,
            Set.inter_comm]
  · exact (hqmeas.mul stronglyMeasurable_condExp).aestronglyMeasurable

open scoped Classical in
/-- **Mutual conditional independence of the fixing events given `𝔅_fix`.** For every finite
family of rank-`n` supports and every choice of a pooled finite-active fixing event at each
support, the conditional probability of the intersection is the product of the conditional
probabilities. -/
theorem condExp_iInter_fixing_eq_prod (Q : PooledRankExtension C)
    (T : Finset (RankSupport S n))
    {E : RankSupport S n → Set (RelStructure S (PoolVertex S))}
    (hE : ∀ A, MeasurableSet[pooledFiniteActiveFixingAlgebra (supportImage (originalVertex S) A.1)]
      (E A)) :
    ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        ⋂ A ∈ T, Prod.fst ⁻¹' E A | fixBase n⟧)
      =ᵐ[(Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))]
    ∏ A ∈ T, ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        Prod.fst ⁻¹' E A | fixBase n⟧) := by
  haveI := C.isProbabilityMeasure_P
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ, Finset.prod_empty]
    rw [Set.indicator_univ, condExp_const (fixStage_le _)]
    exact Filter.EventuallyEq.rfl
  | insert e F heF ih =>
    rw [Finset.set_biInter_insert, Finset.prod_insert heF]
    exact (condExp_insertion Q e F heF hE).trans
      ((Filter.EventuallyEq.refl _ _).mul ih)

end RelSignature
