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
* `MeasureTheory.lpMeas_iInf_of_antitone` — the `Lᵖ`-subspace of an infimum σ-algebra is the
  intersection of the `Lᵖ`-subspaces (limsup representative trick);
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

/-- `lpMeas` is monotone in the σ-algebra. (`m0` is the ambient σ-algebra of `μ`, following
the `{m m0}` convention of the `ConditionalExpectation` files: it is determined by `μ` at
application sites and is *not* required to relate to `m` or `m'`, so the lemma applies with
sub-σ-algebras of any common ambient.) -/
theorem lpMeas_mono {m m' m0 : MeasurableSpace α} {μ : Measure α} (h : m ≤ m') {p : ℝ≥0∞} :
    lpMeas ℝ ℝ m p μ ≤ lpMeas ℝ ℝ m' p μ := by
  intro f hf
  rw [mem_lpMeas_iff_aestronglyMeasurable] at hf ⊢
  obtain ⟨g, hg, hfg⟩ := hf
  exact ⟨g, hg.mono h, hfg⟩

/-- **The `Lᵖ`-subspace of an infimum σ-algebra is the intersection of the subspaces** along
an antitone sequence: a function a.e.-measurable for every `𝒢 n` has the a.e.-limsup
representative, which is measurable for the infimum. (`m0` is the ambient σ-algebra of `μ`,
determined at application sites.) -/
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

/-! ### Lévy downward, `L²` version -/

/-- **Lévy's downward theorem, `L²` version**: for `f ∈ L²` and an antitone sequence of
sub-σ-algebras `𝒢`, the conditional expectations `μ[f|𝒢 n]` converge in `L²` to
`μ[f|⨅ n, 𝒢 n]`. Conditional expectation on `L²` is the orthogonal projection onto `lpMeas`,
so this is `Submodule.starProjection_tendsto_iInf` transported along
`lpMeas_iInf_of_antitone`. -/
theorem tendsto_eLpNorm_condExp_iInf_of_memLp {m0 : MeasurableSpace α} {μ : Measure α}
    [IsFiniteMeasure μ] (𝒢 : ℕ → MeasurableSpace α) (hanti : Antitone 𝒢)
    (h𝒢 : ∀ n, 𝒢 n ≤ m0) {f : α → ℝ} (hf : MemLp f 2 μ) :
    Tendsto (fun n => eLpNorm (μ[f|𝒢 n] - μ[f|⨅ n, 𝒢 n]) 2 μ) atTop (𝓝 0) := by
  have h_inf : (⨅ n, 𝒢 n) ≤ m0 := (iInf_le 𝒢 0).trans (h𝒢 0)
  haveI : ∀ n, Fact (𝒢 n ≤ m0) := fun n => ⟨h𝒢 n⟩
  haveI : Fact ((⨅ n, 𝒢 n) ≤ m0) := ⟨h_inf⟩
  have hUinf : (⨅ n, lpMeas ℝ ℝ (𝒢 n) 2 μ) = lpMeas ℝ ℝ (⨅ n, 𝒢 n) 2 μ :=
    lpMeas_iInf_of_antitone 𝒢 hanti
  haveI : (⨅ n, lpMeas ℝ ℝ (𝒢 n) 2 μ).HasOrthogonalProjection := by
    rw [hUinf]; infer_instance
  have hproj := Submodule.starProjection_tendsto_iInf (fun n => lpMeas ℝ ℝ (𝒢 n) 2 μ)
    (fun i j hij => lpMeas_mono (hanti hij)) (hf.toLp f)
  -- identify the projections with conditional expectations, a.e.
  have haen : ∀ n, ⇑((lpMeas ℝ ℝ (𝒢 n) 2 μ).starProjection (hf.toLp f)) =ᵐ[μ] μ[f|𝒢 n] := by
    intro n
    have hcoe : (lpMeas ℝ ℝ (𝒢 n) 2 μ).starProjection (hf.toLp f)
        = ↑(condExpL2 ℝ ℝ (h𝒢 n) (hf.toLp f)) := rfl
    rw [hcoe]
    exact hf.condExpL2_ae_eq_condExp (h𝒢 n)
  have hcongr : ∀ (K K' : Submodule ℝ (α →₂[μ] ℝ)) [K.HasOrthogonalProjection]
      [K'.HasOrthogonalProjection], K = K' →
      K.starProjection (hf.toLp f) = K'.starProjection (hf.toLp f) := by
    intro K K' _ _ h
    subst h
    rfl
  have haeinf : ⇑((⨅ n, lpMeas ℝ ℝ (𝒢 n) 2 μ).starProjection (hf.toLp f)) =ᵐ[μ]
      μ[f|⨅ n, 𝒢 n] := by
    rw [hcongr _ _ hUinf]
    have hcoe : (lpMeas ℝ ℝ (⨅ n, 𝒢 n) 2 μ).starProjection (hf.toLp f)
        = ↑(condExpL2 ℝ ℝ h_inf (hf.toLp f)) := rfl
    rw [hcoe]
    exact hf.condExpL2_ae_eq_condExp h_inf
  have hkey := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
    (fun n => (lpMeas ℝ ℝ (𝒢 n) 2 μ).starProjection (hf.toLp f))
    ((⨅ n, lpMeas ℝ ℝ (𝒢 n) 2 μ).starProjection (hf.toLp f))).mp hproj
  exact hkey.congr fun n => eLpNorm_congr_ae ((haen n).sub haeinf)

/-! ### Lévy downward, `L¹` version -/

/-- **Lévy's downward theorem, `L¹` version**: for integrable `f` and an antitone sequence of
sub-σ-algebras `𝒢`, the conditional expectations `μ[f|𝒢 n]` converge in `L¹` to
`μ[f|⨅ n, 𝒢 n]`. Proved by an `ε/3` argument from the `L²` case
(`tendsto_eLpNorm_condExp_iInf_of_memLp`), approximating `f` by a simple function. -/
theorem tendsto_eLpNorm_condExp_iInf {m0 : MeasurableSpace α} {μ : Measure α}
    [IsProbabilityMeasure μ] (𝒢 : ℕ → MeasurableSpace α) (hanti : Antitone 𝒢)
    (h𝒢 : ∀ n, 𝒢 n ≤ m0) {f : α → ℝ} (hf : Integrable f μ) :
    Tendsto (fun n => eLpNorm (μ[f|𝒢 n] - μ[f|⨅ n, 𝒢 n]) 1 μ) atTop (𝓝 0) := by
  have h_inf : (⨅ n, 𝒢 n) ≤ m0 := (iInf_le 𝒢 0).trans (h𝒢 0)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : (0 : ℝ≥0∞) < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨g, hg_lt, hg_mem⟩ :=
    (memLp_one_iff_integrable.mpr hf).exists_simpleFunc_eLpNorm_sub_lt ENNReal.one_ne_top hε3.ne'
  have hg_int : Integrable g μ := memLp_one_iff_integrable.mp hg_mem
  have hg2 : MemLp (⇑g) 2 μ := (g.memLp_top μ).mono_exponent le_top
  have hmid := tendsto_eLpNorm_condExp_iInf_of_memLp 𝒢 hanti h𝒢 hg2
  filter_upwards [hmid.eventually (eventually_lt_nhds hε3)] with n hn
  -- split `μ[f|𝒢 n] - μ[f|⨅ n, 𝒢 n]` through the simple approximant `g`, a.e.
  have hsplit : μ[f|𝒢 n] - μ[f|⨅ n, 𝒢 n] =ᵐ[μ]
      (μ[f - ⇑g|𝒢 n] + (μ[⇑g|𝒢 n] - μ[⇑g|⨅ n, 𝒢 n])) - μ[f - ⇑g|⨅ n, 𝒢 n] := by
    have h1 := condExp_sub hf hg_int (𝒢 n)
    have h2 := condExp_sub hf hg_int (⨅ n, 𝒢 n)
    filter_upwards [h1, h2] with ω h1ω h2ω
    simp only [Pi.add_apply, Pi.sub_apply] at h1ω h2ω ⊢
    rw [h1ω, h2ω]
    ring
  have hm1 : AEStronglyMeasurable (μ[f - ⇑g|𝒢 n]) μ :=
    (stronglyMeasurable_condExp.mono (h𝒢 n)).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (μ[⇑g|𝒢 n] - μ[⇑g|⨅ n, 𝒢 n]) μ :=
    ((stronglyMeasurable_condExp.mono (h𝒢 n)).sub
      (stronglyMeasurable_condExp.mono h_inf)).aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (μ[f - ⇑g|⨅ n, 𝒢 n]) μ :=
    (stronglyMeasurable_condExp.mono h_inf).aestronglyMeasurable
  have hb1 : eLpNorm (μ[f - ⇑g|𝒢 n]) 1 μ ≤ ε / 3 :=
    ((eLpNorm_condExp_le_eLpNorm _ le_rfl).trans_lt hg_lt).le
  have hb2 : eLpNorm (μ[⇑g|𝒢 n] - μ[⇑g|⨅ n, 𝒢 n]) 1 μ ≤ ε / 3 :=
    ((eLpNorm_le_eLpNorm_of_exponent_le one_le_two hm2).trans_lt hn).le
  have hb3 : eLpNorm (μ[f - ⇑g|⨅ n, 𝒢 n]) 1 μ ≤ ε / 3 :=
    ((eLpNorm_condExp_le_eLpNorm _ le_rfl).trans_lt hg_lt).le
  calc eLpNorm (μ[f|𝒢 n] - μ[f|⨅ n, 𝒢 n]) 1 μ
      = eLpNorm ((μ[f - ⇑g|𝒢 n] + (μ[⇑g|𝒢 n] - μ[⇑g|⨅ n, 𝒢 n])) - μ[f - ⇑g|⨅ n, 𝒢 n]) 1 μ :=
        eLpNorm_congr_ae hsplit
    _ ≤ eLpNorm (μ[f - ⇑g|𝒢 n] + (μ[⇑g|𝒢 n] - μ[⇑g|⨅ n, 𝒢 n])) 1 μ
          + eLpNorm (μ[f - ⇑g|⨅ n, 𝒢 n]) 1 μ :=
        eLpNorm_sub_le (hm1.add hm2) hm3 le_rfl
    _ ≤ (eLpNorm (μ[f - ⇑g|𝒢 n]) 1 μ + eLpNorm (μ[⇑g|𝒢 n] - μ[⇑g|⨅ n, 𝒢 n]) 1 μ)
          + eLpNorm (μ[f - ⇑g|⨅ n, 𝒢 n]) 1 μ :=
        add_le_add (eLpNorm_add_le hm1 hm2 le_rfl) le_rfl
    _ ≤ ε / 3 + ε / 3 + ε / 3 := add_le_add (add_le_add hb1 hb2) hb3
    _ = ε := ENNReal.add_thirds ε

/-- **Conditional expectation over a `0`-`1` σ-algebra is the mean**: if every `m'`-measurable
set has measure `0` or `1`, the conditional expectation of an integrable function is a.e. the
integral. -/
theorem condExp_ae_eq_integral_of_forall_zero_or_one {m0 : MeasurableSpace α}
    {μ : Measure α} [IsProbabilityMeasure μ] {m' : MeasurableSpace α} (hm' : m' ≤ m0)
    (htriv : ∀ s, MeasurableSet[m'] s → μ s = 0 ∨ μ s = 1) {f : α → ℝ}
    (hf : Integrable f μ) :
    μ[f|m'] =ᵐ[μ] fun _ => ∫ x, f x ∂μ := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm' hf
    (fun s _ _ => integrableOn_const) ?_
    stronglyMeasurable_const.aestronglyMeasurable).symm
  intro s hs _
  rcases htriv s hs with h0 | h1
  · rw [setIntegral_measure_zero _ h0, setIntegral_measure_zero _ h0]
  · have hcompl : μ sᶜ = 0 := by
      have := measure_compl (hm' s hs) (measure_ne_top μ s)
      rw [h1] at this
      simpa using this
    have hs_int : ∫ x in s, f x ∂μ = ∫ x, f x ∂μ := by
      rw [← integral_add_compl (hm' s hs) hf, setIntegral_measure_zero _ hcompl, add_zero]
    rw [hs_int, setIntegral_const]
    have hsr : μ.real s = 1 := by
      rw [Measure.real, h1, ENNReal.toReal_one]
    rw [hsr, one_smul]

end MeasureTheory
