/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelPollingStages

/-!
# The tail property of the reservoir stages (R4 converse, #107, #197)

The first analytic step of the pooled fixing-factor polling argument: a **reservoir tail lemma**,
proved by Austin's energy argument (the `L²` squeeze of the tail engine). It says that
conditioning a fixing event of the target support on the **full** polling base agrees with
conditioning on the stage avoiding the whole reservoir. The observable is a pooled finite-active
fixing event and the conditioning is the raw polling base with its reservoir stages; neither is
Austin's, whose Lemma 3.11 concerns a different observable and conditioning, and the distinction
matters for the insertion step that follows.

## The argument

Write `ℱ m` for the stage avoiding the reservoir at slot `m` (`reservoirFiltration`), increasing
in `m` with supremum the polling conditioning. The inverse synchronous shift `T` is measure
preserving under the pooled law (`Q.invariant`), pulls `ℱ (m + 1)` back to `ℱ m` exactly
(`comap_pooledJointRelabel_inv_reservoirFiltration`), and fixes the target's fixing event almost
surely (`relabel_preimage_ae_eq_of_pooledFiniteActiveFixingAlgebra_fst`, since the shift has
finitely many active sorts and fixes every original vertex below the bound outside `D`). The
tail engine `condExp_ae_eq_condExp_of_comap_eq` therefore identifies the conditional expectations
at adjacent stages (`condExp_reservoirFiltration_succ`); induction identifies every stage with
stage `0` (`condExp_reservoirFiltration_eq_zero`); and Lévy upward along the filtration
identifies the supremum with them (`condExp_sourcePollingCond_eq_reservoirFiltration_zero`).

Everything is modulo `Q.law`. No conditional-independence statement is made here: this is the
tail property alone, the input to the insertion step.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace RelSignature

open InfiniteRelExchangeableLaw

universe u

variable {S : RelSignature.{u}} {n : ℕ} [Countable S.Srt] [Countable S.Rel]
  {M : InfiniteRelExchangeableLaw S} {C : M.RankRepresentation n}

/-- The inverse synchronous shift, as a joint relabeling of the pooled space. -/
noncomputable def inverseShift (N : ℕ) [NeZero N] (D : Finset (Σ s : S.Srt, Vinfinite S s))
    (n : ℕ) :
    RelStructure S (PoolVertex S) × PooledRankLatentSpace S n →
      RelStructure S (PoolVertex S) × PooledRankLatentSpace S n :=
  pooledJointRelabel (fun s => (pooledPollPerm (S := S) N D s)⁻¹) n

theorem measurePreserving_inverseShift (Q : PooledRankExtension C) (N : ℕ) [NeZero N]
    (D : Finset (Σ s : S.Srt, Vinfinite S s)) :
    MeasurePreserving (inverseShift N D n)
      (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))
      (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) :=
  ⟨measurable_pooledJointRelabel _ n, Q.invariant _⟩

omit [Countable S.Srt] [Countable S.Rel] in
open scoped Classical in
/-- The inverse shift is the identity on every sort not occurring in `D`. -/
theorem inverseShift_eq_one (N : ℕ) [NeZero N] (D : Finset (Σ s : S.Srt, Vinfinite S s)) :
    ∃ T : Finset S.Srt, ∀ s, s ∉ T → (pooledPollPerm (S := S) N D s)⁻¹ = 1 :=
  ⟨D.image Sigma.fst, fun s hs => by rw [pooledPollPerm_eq_one N D s hs, inv_one]⟩

/-- **Adjacent stages agree.** For a fixing event `E` of the original image of a support whose
vertices lie below the bound and outside `D`, conditioning on stage `m + 1` and on stage `m` give
the same conditional probability, almost surely under the pooled law. -/
theorem condExp_reservoirFiltration_succ (Q : PooledRankExtension C) (N : ℕ) [NeZero N]
    (D : Finset (Σ s : S.Srt, Vinfinite S s)) (hD : ∀ v ∈ D, v.2 < N)
    {A : Finset (Σ s : S.Srt, Vinfinite S s)} (hA : ∀ v ∈ A, v.2 < N) (hAD : ∀ v ∈ A, v ∉ D)
    {E : Set (RelStructure S (PoolVertex S))}
    (hE : MeasurableSet[pooledFiniteActiveFixingAlgebra (supportImage (originalVertex S) A)] E)
    (m : ℕ) :
    ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        Prod.fst ⁻¹' E | reservoirFiltration N D n (m + 1)⟧)
      =ᵐ[(Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))]
    ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        Prod.fst ⁻¹' E | reservoirFiltration N D n m⟧) := by
  haveI := C.isProbabilityMeasure_P
  obtain ⟨E₀, hE₀, hEeq⟩ := hE
  have hEmeas : MeasurableSet E := by
    rw [← hEeq]; exact (poolStructureEquiv S).measurable (hE₀.1)
  have hAD' : ∀ v ∈ A, v.2 < N ∧ v ∉ D := fun v hv => ⟨hA v hv, hAD v hv⟩
  refine condExp_ae_eq_condExp_of_comap_eq (measurable_pooledJointRelabel _ n)
    (measurePreserving_inverseShift Q N D) ((reservoirFiltration N D n).le (m + 1))
    ((reservoirFiltration N D n).mono (Nat.le_succ m))
    (comap_pooledJointRelabel_inv_reservoirFiltration N D hD n m)
    (memLp_indicator_const 2 (measurable_fst hEmeas) 1 (Or.inr (measure_ne_top _ _))) ?_
  -- the indicator is a.e. fixed by the inverse shift
  have hfix : ∀ v ∈ supportImage (originalVertex S) A,
      (pooledPollPerm (S := S) N D v.1)⁻¹ v.2 = v.2 := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := (mem_supportImage_iff _ _ _).mp hv
    exact pooledPollPerm_inv_original_of_lt N D (hA w hw) (hAD w hw)
  have hinv := Q.relabel_preimage_ae_eq_of_pooledFiniteActiveFixingAlgebra_fst ⟨E₀, hE₀, hEeq⟩
    (inverseShift_eq_one N D) hfix
  have hcomp : (Prod.fst ⁻¹' E).indicator (fun _ => (1 : ℝ)) ∘
      pooledJointRelabel (fun s => (pooledPollPerm (S := S) N D s)⁻¹) n =
      (Prod.fst ⁻¹' (RelStructure.relabel (fun s => (pooledPollPerm N D s)⁻¹) ⁻¹' E)).indicator
        (fun _ => (1 : ℝ)) := rfl
  rw [hcomp]
  exact indicator_ae_eq_of_ae_eq_set hinv

/-- **Every stage agrees with stage `0`.** -/
theorem condExp_reservoirFiltration_eq_zero (Q : PooledRankExtension C) (N : ℕ) [NeZero N]
    (D : Finset (Σ s : S.Srt, Vinfinite S s)) (hD : ∀ v ∈ D, v.2 < N)
    {A : Finset (Σ s : S.Srt, Vinfinite S s)} (hA : ∀ v ∈ A, v.2 < N) (hAD : ∀ v ∈ A, v ∉ D)
    {E : Set (RelStructure S (PoolVertex S))}
    (hE : MeasurableSet[pooledFiniteActiveFixingAlgebra (supportImage (originalVertex S) A)] E)
    (m : ℕ) :
    ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        Prod.fst ⁻¹' E | reservoirFiltration N D n m⟧)
      =ᵐ[(Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))]
    ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        Prod.fst ⁻¹' E | reservoirFiltration N D n 0⟧) := by
  induction m with
  | zero => exact EventuallyEq.refl _ _
  | succ k ih => exact (condExp_reservoirFiltration_succ Q N D hD hA hAD hE k).trans ih

/-- **The tail property**: conditioning on the full polling base is conditioning on the stage
avoiding the whole reservoir. Lévy upward along the filtration, whose supremum is the polling
conditioning, applied to an almost surely constant sequence. -/
theorem condExp_sourcePollingCond_eq_reservoirFiltration_zero (Q : PooledRankExtension C)
    (N : ℕ) [NeZero N] (D : Finset (Σ s : S.Srt, Vinfinite S s)) (hD : ∀ v ∈ D, v.2 < N)
    {A : Finset (Σ s : S.Srt, Vinfinite S s)} (hA : ∀ v ∈ A, v.2 < N) (hAD : ∀ v ∈ A, v ∉ D)
    {E : Set (RelStructure S (PoolVertex S))}
    (hE : MeasurableSet[pooledFiniteActiveFixingAlgebra (supportImage (originalVertex S) A)] E) :
    ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        Prod.fst ⁻¹' E | MeasurableSpace.comap (sourcePollingCond (S := S) (n := n)) inferInstance⟧)
      =ᵐ[(Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))]
    ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        Prod.fst ⁻¹' E | reservoirFiltration N D n 0⟧) := by
  haveI := C.isProbabilityMeasure_P
  set μ : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) :=
    (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) with hμ
  set ℱ := reservoirFiltration (S := S) N D n with hℱ
  set f : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → ℝ :=
    (Prod.fst ⁻¹' E).indicator fun _ => (1 : ℝ) with hf
  -- Lévy upward: the stage conditional expectations converge a.e. to the supremum's
  have hlevy : ∀ᵐ x ∂μ, Tendsto (fun m => (μ[f | ℱ m]) x) atTop (𝓝 ((μ[f | ⨆ m, ℱ m]) x)) :=
    tendsto_ae_condExp f
  -- the sequence is a.e. constant
  have hconst : ∀ᵐ x ∂μ, ∀ m, (μ[f | ℱ m]) x = (μ[f | ℱ 0]) x :=
    ae_all_iff.mpr fun m => condExp_reservoirFiltration_eq_zero Q N D hD hA hAD hE m
  rw [← iSup_reservoirFiltration N D n]
  filter_upwards [hlevy, hconst] with x hx hcx
  have hx' : Tendsto (fun m => (μ[f | ℱ m]) x) atTop (𝓝 ((μ[f | ℱ 0]) x)) := by
    rw [show (fun m => (μ[f | ℱ m]) x) = fun _ => (μ[f | ℱ 0]) x from funext fun m => hcx m]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hx hx'

end RelSignature
