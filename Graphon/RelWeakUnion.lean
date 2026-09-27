/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.Independence.Conditional

/-!
# Weak union for conditional independence

The graphoid axiom: **if `X` is conditionally independent of `(Y, Z)` given `W`, and `W` is
contained in `Z`, then `X` is conditionally independent of `Y` given `Z` alone.** The
containment `W ≤ Z` is what lets the conclusion condition on exactly `Z` rather than on an
unsimplified `W ⊔ Z`.

Route-local: its consumers are the pooled polling module and the marked locality module of the
R4 converse. The helper stays private, having that theorem as its only consumer.

The proof is the standard one. The key step is that enlarging the conditioning from `W` to any
algebra between `W` and `Y ⊔ Z` does not change the conditional probability of an `X`-event —
proved by conditional-expectation uniqueness, with the product identity supplying the set
integrals. Applying that at `Y ⊔ Z` and at `Z`, and then peeling with the tower property, gives the
result.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

private theorem condExp_eq_of_between {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {mW mX mYZ m : MeasurableSpace Ω}
    (hW : mW ≤ mΩ) (hm : m ≤ mΩ) (hWm : mW ≤ m) (hmYZ : m ≤ mYZ)
    {A : Set Ω} (hAX : MeasurableSet[mX] A) (hA : MeasurableSet[mΩ] A)
    (h : ∀ t1 t2, MeasurableSet[mX] t1 → MeasurableSet[mYZ] t2 →
      (μ⟦t1 ∩ t2 | mW⟧) =ᵐ[μ] (μ⟦t1 | mW⟧) * (μ⟦t2 | mW⟧)) :
    (μ⟦A | m⟧) =ᵐ[μ] (μ⟦A | mW⟧) := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm
    ((integrable_const (1 : ℝ)).indicator hA)
    (fun S _ _ => integrable_condExp.integrableOn)
    (fun S hSm _ => ?_)
    ((stronglyMeasurable_condExp.mono hWm).aestronglyMeasurable)).symm
  have hSamb : MeasurableSet[mΩ] S := hm _ hSm
  have hprod := h A S hAX (hmYZ _ hSm)
  -- the pull-out identity, integrated
  have hmulind : (μ⟦A | mW⟧) * S.indicator (fun _ => (1 : ℝ)) = S.indicator (μ⟦A | mW⟧) := by
    funext x
    by_cases hx : x ∈ S <;> simp [hx, Set.indicator_of_mem, Set.indicator_of_notMem]
  have hpull : μ[(μ⟦A | mW⟧) * S.indicator (fun _ => (1 : ℝ)) | mW]
      =ᵐ[μ] (μ⟦A | mW⟧) * (μ⟦S | mW⟧) :=
    condExp_mul_of_stronglyMeasurable_left stronglyMeasurable_condExp
      (by rw [hmulind]; exact integrable_condExp.indicator hSamb)
      ((integrable_const (1 : ℝ)).indicator hSamb)
  calc ∫ x in S, (μ⟦A | mW⟧) x ∂μ
      = ∫ x, ((μ⟦A | mW⟧) * S.indicator fun _ => (1 : ℝ)) x ∂μ := by
        rw [← integral_indicator hSamb]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ S <;> simp [hx, Set.indicator_of_mem, Set.indicator_of_notMem]
    _ = ∫ x, (μ[(μ⟦A | mW⟧) * S.indicator fun _ => (1 : ℝ) | mW]) x ∂μ :=
        (integral_condExp hW).symm
    _ = ∫ x, ((μ⟦A | mW⟧) * (μ⟦S | mW⟧)) x ∂μ := integral_congr_ae hpull
    _ = ∫ x, (μ⟦A ∩ S | mW⟧) x ∂μ := (integral_congr_ae hprod).symm
    _ = ∫ x, (A ∩ S).indicator (fun _ => (1 : ℝ)) x ∂μ := integral_condExp hW
    _ = ∫ x in S, A.indicator (fun _ => (1 : ℝ)) x ∂μ := by
        rw [integral_indicator (hA.inter hSamb), setIntegral_indicator hA, Set.inter_comm]

/-- **Weak union.** If `X` is conditionally independent of `Y ⊔ Z` given `W`, and `W ≤ Z`, then
`X` is conditionally independent of `Y` given `Z`. -/
theorem condIndep_weak_union {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {mW mX mY mZ : MeasurableSpace Ω}
    (hW : mW ≤ mΩ) (hX : mX ≤ mΩ) (hY : mY ≤ mΩ) (hZ : mZ ≤ mΩ) (hWZ : mW ≤ mZ)
    (h : CondIndep mW mX (mY ⊔ mZ) hW μ) :
    CondIndep mZ mX mY hZ μ := by
  have hYZ : mY ⊔ mZ ≤ mΩ := sup_le hY hZ
  rw [condIndep_iff _ _ _ hW hX hYZ] at h
  rw [condIndep_iff _ _ _ hZ hX hY]
  intro A B hA hB
  have hAamb : MeasurableSet[mΩ] A := hX _ hA
  have hBamb : MeasurableSet[mΩ] B := hY _ hB
  have hBYZ : MeasurableSet[mY ⊔ mZ] B := (le_sup_left : mY ≤ mY ⊔ mZ) _ hB
  -- the conditional probability of an `X`-event is the same at `W`, at `Z`, and at `Y ⊔ Z`
  have hZeq : (μ⟦A | mZ⟧) =ᵐ[μ] (μ⟦A | mW⟧) :=
    condExp_eq_of_between (mΩ := mΩ) hW hZ hWZ le_sup_right hA hAamb h
  have hYZeq : (μ⟦A | mY ⊔ mZ⟧) =ᵐ[μ] (μ⟦A | mW⟧) :=
    condExp_eq_of_between (mΩ := mΩ) hW hYZ (hWZ.trans le_sup_right) le_rfl hA hAamb h
  -- peel `B` off inside the larger algebra, then descend by the tower property
  have hpull : μ[(A ∩ B).indicator (fun _ => (1 : ℝ)) | mY ⊔ mZ]
      =ᵐ[μ] (μ⟦A | mW⟧) * B.indicator fun _ => (1 : ℝ) := by
    have hmul : ((A ∩ B).indicator fun _ => (1 : ℝ)) =
        (A.indicator fun _ => (1 : ℝ)) * B.indicator fun _ => (1 : ℝ) := by
      funext x
      by_cases hx : x ∈ A <;> by_cases hy : x ∈ B <;>
        simp [hx, hy, Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_inter_iff]
    rw [hmul]
    refine (condExp_mul_of_stronglyMeasurable_right
      (stronglyMeasurable_const.indicator hBYZ)
      ?_ ((integrable_const (1 : ℝ)).indicator hAamb)).trans ?_
    · rw [← hmul]; exact (integrable_const (1 : ℝ)).indicator (hAamb.inter hBamb)
    · exact Filter.EventuallyEq.mul hYZeq Filter.EventuallyEq.rfl
  have htower : (μ⟦A ∩ B | mZ⟧) =ᵐ[μ] μ[μ[(A ∩ B).indicator (fun _ => (1 : ℝ)) | mY ⊔ mZ] | mZ] :=
    (condExp_condExp_of_le le_sup_right hYZ).symm
  refine htower.trans ?_
  refine ((condExp_congr_ae hpull).trans ?_)
  refine (condExp_mul_of_stronglyMeasurable_left
    (stronglyMeasurable_condExp.mono hWZ)
    ?_ ((integrable_const (1 : ℝ)).indicator hBamb)).trans ?_
  · have hmulB : (μ⟦A | mW⟧) * B.indicator (fun _ => (1 : ℝ)) = B.indicator (μ⟦A | mW⟧) := by
      funext x
      by_cases hx : x ∈ B <;> simp [hx, Set.indicator_of_mem, Set.indicator_of_notMem]
    rw [hmulB]
    exact integrable_condExp.indicator hBamb
  · exact (Filter.EventuallyEq.mul hZeq.symm Filter.EventuallyEq.rfl)

end RelSignature
