/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Lévy's downward theorem, L¹ version (R3 follow-up; Mathlib-upstream candidate, #24)

The narrow reverse-martingale convergence the relational extremality theory needs:
along an **antitone** sequence of sub-σ-algebras, conditional expectations converge in `L¹`
to the conditional expectation on the intersection. Mathlib has Lévy's *upward* theorem
(`Mathlib/Probability/Martingale/Convergence.lean`); this file provides the downward `L¹`
form by the orthogonal-projection route (no upcrossing/almost-everywhere machinery):

* `Submodule.starProjection_tendsto_iInf` — orthogonal projections onto an antitone sequence
  of subspaces converge to the projection onto the infimum (the antitone twin of
  `starProjection_tendsto_closure_iSup`, via orthogonal complements);
* `MeasureTheory.lpMeas_iInf_of_antitone` — the `L²`-subspace of an infimum σ-algebra is the
  intersection of the `L²`-subspaces (limsup representative trick);
* `MeasureTheory.tendsto_eLpNorm_condExp_iInf` — **Lévy downward, L¹**: for integrable `f`
  and antitone `𝒢`, `eLpNorm (μ[f|𝒢 n] − μ[f|⨅ n, 𝒢 n]) 1 μ → 0` (via the `L²` case and an
  `ε/3` density argument).
-/

open Filter Topology
open scoped ENNReal

/-! ### Antitone projection convergence -/

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Orthogonal projections along an antitone sequence of subspaces converge to the
projection onto the infimum** — the antitone twin of `starProjection_tendsto_closure_iSup`,
by passing to orthogonal complements. -/
theorem starProjection_tendsto_iInf [CompleteSpace E] (U : ℕ → Submodule 𝕜 E)
    [∀ i, (U i).HasOrthogonalProjection] [(⨅ i, U i).HasOrthogonalProjection]
    (hU : Antitone U) (x : E) :
    Tendsto (fun i => (U i).starProjection x) atTop (𝓝 ((⨅ i, U i).starProjection x)) := by
  have hmono : Monotone fun i => (U i)ᗮ := fun i j hij => Submodule.orthogonal_le (hU hij)
  have hcl : (⨆ i, (U i)ᗮ).topologicalClosure = (⨅ i, U i)ᗮ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, ← Submodule.iInf_orthogonal]
    congr 1
    exact iInf_congr fun i => Submodule.orthogonal_orthogonal (U i)
  have hcongr : ∀ (K K' : Submodule 𝕜 E) [K.HasOrthogonalProjection]
      [K'.HasOrthogonalProjection], K = K' → K.starProjection x = K'.starProjection x := by
    intro K K' _ _ h
    subst h
    rfl
  have hproj := Submodule.starProjection_tendsto_closure_iSup (fun i => (U i)ᗮ) hmono x
  rw [hcongr _ _ hcl] at hproj
  have hval : ∀ i, (U i).starProjection x = x - (U i)ᗮ.starProjection x := by
    intro i
    rw [Submodule.starProjection_orthogonal_val]
    exact (sub_sub_cancel x _).symm
  have hvalInf : (⨅ i, U i).starProjection x = x - (⨅ i, U i)ᗮ.starProjection x := by
    rw [Submodule.starProjection_orthogonal_val]
    exact (sub_sub_cancel x _).symm
  rw [hvalInf]
  exact (tendsto_const_nhds.sub hproj).congr fun i => (hval i).symm

end Submodule

/-! ### The `L²`-subspace of an infimum σ-algebra -/

namespace MeasureTheory

variable {α : Type*}

/-- `lpMeas` is monotone in the σ-algebra. -/
theorem lpMeas_mono {m m' m0 : MeasurableSpace α} {μ : Measure α} (h : m ≤ m') {p : ℝ≥0∞} :
    lpMeas ℝ ℝ m p μ ≤ lpMeas ℝ ℝ m' p μ := by
  intro f hf
  rw [mem_lpMeas_iff_aestronglyMeasurable] at hf ⊢
  obtain ⟨g, hg, hfg⟩ := hf
  exact ⟨g, hg.mono h, hfg⟩

/-- **The `Lᵖ`-subspace of an infimum σ-algebra is the intersection of the subspaces** along
an antitone sequence: a function a.e.-measurable for every `𝒢 n` has the a.e.-limsup
representative, which is measurable for the infimum. -/
theorem lpMeas_iInf_of_antitone {m0 : MeasurableSpace α} {μ : Measure α}
    (𝒢 : ℕ → MeasurableSpace α) (hanti : Antitone 𝒢) {p : ℝ≥0∞} :
    (⨅ n, lpMeas ℝ ℝ (𝒢 n) p μ) = lpMeas ℝ ℝ (⨅ n, 𝒢 n) p μ := by
  refine le_antisymm ?_ (le_iInf fun n => lpMeas_mono (iInf_le _ n))
  intro f hf
  simp only [Submodule.mem_iInf] at hf
  have hf' : ∀ n, AEStronglyMeasurable[𝒢 n] (⇑f) μ := fun n =>
    mem_lpMeas_iff_aestronglyMeasurable.mp (hf n)
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  have hgm : ∀ n, Measurable[𝒢 n] ((hf' n).mk ⇑f) := fun n =>
    (hf' n).stronglyMeasurable_mk.measurable
  refine ⟨fun ω => Filter.limsup (fun n => (hf' n).mk (⇑f) ω) Filter.atTop, ?_, ?_⟩
  · refine Measurable.stronglyMeasurable ?_
    intro t ht
    rw [MeasurableSpace.measurableSet_iInf]
    intro m
    have hm : Measurable[𝒢 m]
        fun ω => Filter.limsup (fun n => (hf' n).mk (⇑f) ω) Filter.atTop := by
      have hshift : (fun ω => Filter.limsup (fun n => (hf' n).mk (⇑f) ω) Filter.atTop) =
          fun ω => Filter.limsup (fun n => (hf' (n + m)).mk (⇑f) ω) Filter.atTop := by
        funext ω
        exact (Filter.limsup_nat_add (fun n => (hf' n).mk (⇑f) ω) m).symm
      rw [hshift]
      exact Measurable.limsup fun n => (hgm (n + m)).mono (hanti (Nat.le_add_left m n)) le_rfl
    exact hm ht
  · have hall : ∀ᵐ ω ∂μ, ∀ n, (⇑f) ω = (hf' n).mk (⇑f) ω :=
      ae_all_iff.mpr fun n => (hf' n).ae_eq_mk
    filter_upwards [hall] with ω hω
    rw [show (fun n => (hf' n).mk (⇑f) ω) = fun _ => f ω from funext fun n => (hω n).symm]
    exact (Filter.limsup_const _).symm

end MeasureTheory
