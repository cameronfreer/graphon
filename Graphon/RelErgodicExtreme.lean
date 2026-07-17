/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelInvariantAction
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Dynamics.Ergodic.RadonNikodym
import Mathlib.Probability.ConditionalProbability

/-!
# Ergodic exchangeable relational laws are the extreme points (R3c step 2, #106)

Port of `Mathlib/Dynamics/Ergodic/Extreme.lean` from a single measure-preserving self-map to
the countable group of finitely supported sortwise relabelings acting on
`RelStructure S (Vinfinite S)`:

* `RelSignature.countable_setOf_sortwiseFinSupp` — with finitely many sorts, the finitely
  supported sortwise permutation families form a countable set;
* `InfiniteRelExchangeableLaw.measure_zero_or_one_of_ae_invariant` — the zero-one law
  upgrades from strictly invariant to almost-everywhere invariant events, via the countable
  invariant hull `⋃ σ, relabel σ ⁻¹' E` over the relabeling group;
* `InfiniteRelExchangeableLaw.eq_of_absolutelyContinuous` — a relabeling-invariant
  probability measure absolutely continuous with respect to an ergodic exchangeable law is
  equal to it (the Radon–Nikodym derivative is a.e. `1` by the zero-one law);
* `InfiniteRelExchangeableLaw.isErgodic_iff_mem_extremePoints` — the headline: ergodicity of
  an exchangeable relational law is equivalent to extremality among the relabeling-invariant
  probability measures.
-/

open MeasureTheory Measure Set Filter ProbabilityTheory
open scoped ENNReal

namespace RelSignature

variable {S : RelSignature}

/-! ### Composition laws for relabeling -/

/-- **Relabelings compose contravariantly**: relabeling by `τ` and then by `σ` is relabeling
by the pointwise product `fun s => τ s * σ s` (definitional, via `RelStructure.comap_comp`). -/
theorem RelStructure.relabel_relabel {V : S.Srt → Type*} (σ τ : ∀ s, Equiv.Perm (V s))
    (x : RelStructure S V) :
    RelStructure.relabel σ (RelStructure.relabel τ x) =
      RelStructure.relabel (fun s => τ s * σ s) x := rfl

/-- Relabeling by the identity family is the identity (definitional). -/
theorem RelStructure.relabel_one {V : S.Srt → Type*} (x : RelStructure S V) :
    RelStructure.relabel (fun s => (1 : Equiv.Perm (V s))) x = x := rfl

/-! ### Countability of the finitely supported relabeling group -/

/-- **With finitely many sorts, the finitely supported sortwise permutation families form a
countable set**: a family supported below `N` is determined by its values on `Fin N`, so each
level of the exhaustion injects into the countable type `S.Srt → Fin N → ℕ`. -/
theorem countable_setOf_sortwiseFinSupp [Fintype S.Srt] :
    Set.Countable {σ : ∀ _ : S.Srt, Equiv.Perm ℕ | SortwiseFinSupp σ} := by
  have hU : {σ : ∀ _ : S.Srt, Equiv.Perm ℕ | SortwiseFinSupp σ} =
      ⋃ N : ℕ, {σ : ∀ _ : S.Srt, Equiv.Perm ℕ | ∀ s (x : ℕ), N ≤ x → σ s x = x} := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    rfl
  rw [hU]
  refine Set.countable_iUnion fun N => ?_
  rw [← Set.countable_coe_iff]
  refine Function.Injective.countable (β := S.Srt → Fin N → ℕ)
    (f := fun σ => fun s (i : Fin N) => σ.1 s i) ?_
  rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ h
  refine Subtype.ext (funext fun s => Equiv.ext fun x => ?_)
  rcases lt_or_ge x N with hx | hx
  · exact congrFun (congrFun h s) ⟨x, hx⟩
  · rw [hσ s x hx, hτ s x hx]

/-! ### The zero-one law for almost invariant events -/

/-- **Almost invariant events obey the zero-one law**: if `E` is measurable and a.e. invariant
under every finitely supported sortwise relabeling, then its invariant hull — the union of its
preimages over the countable relabeling group — is measurable, strictly invariant, and a.e.
equal to `E`, so ergodicity forces `E` itself to be null or conull. -/
theorem InfiniteRelExchangeableLaw.measure_zero_or_one_of_ae_invariant [Fintype S.Srt]
    (M : InfiniteRelExchangeableLaw S) (hM : M.IsErgodic)
    {E : Set (RelStructure S (Vinfinite S))} (hEm : MeasurableSet E)
    (hE : ∀ σ, SortwiseFinSupp (S := S) σ →
      RelStructure.relabel σ ⁻¹' E =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))] E) :
    (M.law : Measure (RelStructure S (Vinfinite S))) E = 0 ∨
      (M.law : Measure (RelStructure S (Vinfinite S))) E = 1 := by
  classical
  have hGc : Set.Countable {σ : ∀ _ : S.Srt, Equiv.Perm ℕ | SortwiseFinSupp σ} :=
    countable_setOf_sortwiseFinSupp
  have hGne : Set.Nonempty {σ : ∀ _ : S.Srt, Equiv.Perm ℕ | SortwiseFinSupp σ} :=
    ⟨fun _ => 1, SortwiseFinSupp.one⟩
  have hE'm : MeasurableSet
      (⋃ σ ∈ {σ : ∀ _ : S.Srt, Equiv.Perm ℕ | SortwiseFinSupp σ},
        RelStructure.relabel σ ⁻¹' E) :=
    .biUnion hGc fun σ _ => measurable_relabel σ hEm
  have hinv : ∀ τ, SortwiseFinSupp (S := S) τ →
      RelStructure.relabel τ ⁻¹'
          (⋃ σ ∈ {σ : ∀ _ : S.Srt, Equiv.Perm ℕ | SortwiseFinSupp σ},
            RelStructure.relabel σ ⁻¹' E) =
        ⋃ σ ∈ {σ : ∀ _ : S.Srt, Equiv.Perm ℕ | SortwiseFinSupp σ},
          RelStructure.relabel σ ⁻¹' E := by
    intro τ hτ
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · rintro ⟨σ, hσ, hx⟩
      refine ⟨fun s => τ s * σ s, hτ.mul hσ, ?_⟩
      rw [← RelStructure.relabel_relabel]
      exact hx
    · rintro ⟨ρ, hρ, hx⟩
      refine ⟨fun s => (τ s)⁻¹ * ρ s, hτ.inv.mul hρ, ?_⟩
      have hcomp : RelStructure.relabel (fun s => (τ s)⁻¹ * ρ s) (RelStructure.relabel τ x) =
          RelStructure.relabel ρ x := by
        rw [RelStructure.relabel_relabel]
        congr 1
        funext s
        exact mul_inv_cancel_left (τ s) (ρ s)
      rw [hcomp]
      exact hx
  have haeE : (⋃ σ ∈ {σ : ∀ _ : S.Srt, Equiv.Perm ℕ | SortwiseFinSupp σ},
        RelStructure.relabel σ ⁻¹' E)
      =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))] E := by
    have h1 : (⋃ σ ∈ {σ : ∀ _ : S.Srt, Equiv.Perm ℕ | SortwiseFinSupp σ},
          RelStructure.relabel σ ⁻¹' E)
        =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))]
          ⋃ σ ∈ {σ : ∀ _ : S.Srt, Equiv.Perm ℕ | SortwiseFinSupp σ}, E :=
      Filter.EventuallyEq.countable_bUnion hGc fun σ hσ => hE σ hσ
    rwa [Set.biUnion_const hGne] at h1
  have h01 := hM _ ⟨hE'm, hinv⟩
  rwa [measure_congr haeE] at h01

/-! ### Absolute continuity and ergodicity -/

/-- **An invariant probability measure absolutely continuous with respect to an ergodic
exchangeable law equals it.** The Radon–Nikodym derivative is a.e. invariant under each
relabeling (`MeasurePreserving.rnDeriv_comp_aeEq`), so its sub- and super-level sets at `1`
are a.e. invariant, hence null or conull by the zero-one upgrade; strict monotonicity of the
set integral rules out the conull cases, so the derivative is a.e. `1`. -/
theorem InfiniteRelExchangeableLaw.eq_of_absolutelyContinuous [Fintype S.Srt]
    (M : InfiniteRelExchangeableLaw S) (hM : M.IsErgodic)
    {ν : Measure (RelStructure S (Vinfinite S))} [IsProbabilityMeasure ν]
    (hinv : ∀ σ, SortwiseFinSupp (S := S) σ → ν.map (RelStructure.relabel σ) = ν)
    (hac : ν ≪ (M.law : Measure (RelStructure S (Vinfinite S)))) :
    ν = (M.law : Measure (RelStructure S (Vinfinite S))) := by
  set μ : Measure (RelStructure S (Vinfinite S)) :=
    (M.law : Measure (RelStructure S (Vinfinite S))) with hμdef
  haveI : IsProbabilityMeasure μ := by rw [hμdef]; infer_instance
  set f : RelStructure S (Vinfinite S) → ℝ≥0∞ := ν.rnDeriv μ with hfdef
  have hfm : Measurable f := Measure.measurable_rnDeriv ν μ
  have hcomp : ∀ σ, SortwiseFinSupp (S := S) σ → f ∘ RelStructure.relabel σ =ᵐ[μ] f :=
    fun σ hσ => MeasurePreserving.rnDeriv_comp_aeEq
      ⟨measurable_relabel σ, hinv σ hσ⟩ ⟨measurable_relabel σ, M.exchangeable σ⟩
  -- level sets of the density are null or conull
  have hpre : ∀ B : Set ℝ≥0∞, MeasurableSet B → μ (f ⁻¹' B) = 0 ∨ μ (f ⁻¹' B) = 1 := by
    intro B hB
    refine M.measure_zero_or_one_of_ae_invariant hM (hfm hB) fun σ hσ => ?_
    rw [Filter.eventuallyEq_set]
    filter_upwards [hcomp σ hσ] with x hx
    have hfx : f (RelStructure.relabel σ x) = f x := hx
    simp only [Set.mem_preimage, hfx]
  have hE01 := hpre (Set.Iio 1) measurableSet_Iio
  have hF01 := hpre (Set.Ioi 1) measurableSet_Ioi
  -- the density cannot be a.e. below 1
  have hE0 : μ (f ⁻¹' Set.Iio 1) = 0 := by
    rcases hE01 with h | h
    · exact h
    · exfalso
      have hνE : ν (f ⁻¹' Set.Iio 1) = ∫⁻ x in f ⁻¹' Set.Iio 1, f x ∂μ :=
        (Measure.setLIntegral_rnDeriv hac _).symm
      have hlt : ∫⁻ x in f ⁻¹' Set.Iio 1, f x ∂μ < ∫⁻ _ in f ⁻¹' Set.Iio 1, 1 ∂μ := by
        refine setLIntegral_strict_mono (hfm measurableSet_Iio) ?_ measurable_const ?_ ?_
        · rw [h]; exact one_ne_zero
        · rw [← hνE]; exact measure_ne_top ν _
        · exact Filter.Eventually.of_forall fun x hx => hx
      have h1 : ν (f ⁻¹' Set.Iio 1) < 1 := by
        rwa [← hνE, setLIntegral_one, h] at hlt
      have hEc : ν (f ⁻¹' Set.Iio 1)ᶜ = 0 :=
        hac ((prob_compl_eq_zero_iff (hfm measurableSet_Iio)).mpr h)
      have h2 : ν (f ⁻¹' Set.Iio 1) = 1 := by
        have hadd : ν (f ⁻¹' Set.Iio 1) + ν (f ⁻¹' Set.Iio 1)ᶜ = ν Set.univ :=
          measure_add_measure_compl (hfm measurableSet_Iio)
        rwa [hEc, add_zero, measure_univ] at hadd
      exact absurd h2 h1.ne
  -- and it cannot be a.e. above 1
  have hF0 : μ (f ⁻¹' Set.Ioi 1) = 0 := by
    rcases hF01 with h | h
    · exact h
    · exfalso
      have hνF : ν (f ⁻¹' Set.Ioi 1) = ∫⁻ x in f ⁻¹' Set.Ioi 1, f x ∂μ :=
        (Measure.setLIntegral_rnDeriv hac _).symm
      have hlt : ∫⁻ _ in f ⁻¹' Set.Ioi 1, 1 ∂μ < ∫⁻ x in f ⁻¹' Set.Ioi 1, f x ∂μ := by
        refine setLIntegral_strict_mono (hfm measurableSet_Ioi) ?_ hfm ?_ ?_
        · rw [h]; exact one_ne_zero
        · rw [setLIntegral_one, h]; exact ENNReal.one_ne_top
        · exact Filter.Eventually.of_forall fun x hx => hx
      have h1 : (1 : ℝ≥0∞) < ν (f ⁻¹' Set.Ioi 1) := by
        rwa [setLIntegral_one, h, ← hνF] at hlt
      exact (h1.trans_le (prob_le_one (μ := ν))).false
  -- hence the density is a.e. 1 and the measures agree
  have hae1 : f =ᵐ[μ] fun _ => (1 : ℝ≥0∞) := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun x hx => ?_) (measure_union_null hE0 hF0)
    rcases lt_or_gt_of_ne (hx : f x ≠ 1) with hlt | hgt
    · exact Or.inl hlt
    · exact Or.inr hgt
  ext s hs
  calc ν s = ∫⁻ x in s, f x ∂μ := (Measure.setLIntegral_rnDeriv hac s).symm
    _ = ∫⁻ _ in s, 1 ∂μ :=
      lintegral_congr_ae (hae1.filter_mono (ae_mono Measure.restrict_le_self))
    _ = μ s := setLIntegral_one s

/-! ### The extreme-point characterization -/

/-- **The law of an exchangeable relational structure is an invariant probability measure**:
membership in the candidate set of the extreme-point characterization. -/
@[simp] theorem InfiniteRelExchangeableLaw.law_mem_invariantProbabilityMeasures
    (M : InfiniteRelExchangeableLaw S) :
    (M.law : Measure (RelStructure S (Vinfinite S))) ∈
      {ν : Measure (RelStructure S (Vinfinite S)) |
        (∀ σ, SortwiseFinSupp (S := S) σ → ν.map (RelStructure.relabel σ) = ν) ∧
        IsProbabilityMeasure ν} :=
  ⟨fun σ _ => M.exchangeable σ, inferInstance⟩

/-- **An extreme invariant probability measure is ergodic**: if some strictly invariant event
had intermediate measure, conditioning on it and its complement would exhibit the law as a
proper convex combination of two distinct invariant probability measures. -/
theorem InfiniteRelExchangeableLaw.isErgodic_of_mem_extremePoints
    (M : InfiniteRelExchangeableLaw S)
    (h : (M.law : Measure (RelStructure S (Vinfinite S))) ∈
      Set.extremePoints ℝ≥0∞
        {ν : Measure (RelStructure S (Vinfinite S)) |
          (∀ σ, SortwiseFinSupp (S := S) σ → ν.map (RelStructure.relabel σ) = ν) ∧
          IsProbabilityMeasure ν}) :
    M.IsErgodic := by
  set μ : Measure (RelStructure S (Vinfinite S)) :=
    (M.law : Measure (RelStructure S (Vinfinite S))) with hμdef
  haveI : IsProbabilityMeasure μ := by rw [hμdef]; infer_instance
  rintro A ⟨hAm, hAinv⟩
  by_contra H
  obtain ⟨hA0, hA1⟩ := not_or.mp H
  have hAc0 : μ Aᶜ ≠ 0 := by
    rw [Ne, prob_compl_eq_zero_iff hAm]
    exact hA1
  -- conditioning on a strictly invariant set preserves invariance
  have hcondmem : ∀ B : Set (RelStructure S (Vinfinite S)), MeasurableSet B →
      (∀ σ, SortwiseFinSupp (S := S) σ → RelStructure.relabel σ ⁻¹' B = B) → μ B ≠ 0 →
      μ[|B] ∈ {ν : Measure (RelStructure S (Vinfinite S)) |
        (∀ σ, SortwiseFinSupp (S := S) σ → ν.map (RelStructure.relabel σ) = ν) ∧
        IsProbabilityMeasure ν} := by
    intro B hBm hBinv hB0
    refine ⟨fun σ hσ => ?_, cond_isProbabilityMeasure hB0⟩
    have hres : (μ.restrict B).map (RelStructure.relabel σ) = μ.restrict B := by
      have hmp := MeasurePreserving.restrict_preimage
        (⟨measurable_relabel σ, M.exchangeable σ⟩ :
          MeasurePreserving (RelStructure.relabel σ) μ μ) hBm
      rw [hBinv σ hσ] at hmp
      exact hmp.map_eq
    show ((μ B)⁻¹ • μ.restrict B).map (RelStructure.relabel σ) = (μ B)⁻¹ • μ.restrict B
    rw [Measure.map_smul, hres]
  have hmemA := hcondmem A hAm hAinv hA0
  have hmemAc := hcondmem Aᶜ hAm.compl
    (fun σ hσ => by rw [Set.preimage_compl, hAinv σ hσ]) hAc0
  -- the law is a proper convex combination of the two conditional measures
  have hseg : μ ∈ openSegment ℝ≥0∞ μ[|A] μ[|Aᶜ] := by
    refine ⟨μ A, μ Aᶜ, pos_iff_ne_zero.mpr hA0, pos_iff_ne_zero.mpr hAc0, ?_, ?_⟩
    · rw [measure_add_measure_compl hAm, measure_univ]
    · have hA' : μ A • μ[|A] = μ.restrict A := by
        show μ A • ((μ A)⁻¹ • μ.restrict A) = μ.restrict A
        rw [smul_smul, ENNReal.mul_inv_cancel hA0 (measure_ne_top μ A), one_smul]
      have hAc' : μ Aᶜ • μ[|Aᶜ] = μ.restrict Aᶜ := by
        show μ Aᶜ • ((μ Aᶜ)⁻¹ • μ.restrict Aᶜ) = μ.restrict Aᶜ
        rw [smul_smul, ENNReal.mul_inv_cancel hAc0 (measure_ne_top μ Aᶜ), one_smul]
      rw [hA', hAc', Measure.restrict_add_restrict_compl hAm]
  have hcond : μ[|A] = μ := h.2 hmemA hmemAc hseg
  have hzero : μ Aᶜ = 0 := by
    rw [← hcond, ProbabilityTheory.cond_apply hAm, Set.inter_compl_self, measure_empty,
      mul_zero]
  exact hAc0 hzero

/-- **An ergodic exchangeable relational law is an extreme point** of the relabeling-invariant
probability measures: any measure appearing in a proper convex decomposition is absolutely
continuous, hence equal to the law by `eq_of_absolutelyContinuous`. -/
theorem InfiniteRelExchangeableLaw.mem_extremePoints_of_isErgodic [Fintype S.Srt]
    (M : InfiniteRelExchangeableLaw S) (hM : M.IsErgodic) :
    (M.law : Measure (RelStructure S (Vinfinite S))) ∈
      Set.extremePoints ℝ≥0∞
        {ν : Measure (RelStructure S (Vinfinite S)) |
          (∀ σ, SortwiseFinSupp (S := S) σ → ν.map (RelStructure.relabel σ) = ν) ∧
          IsProbabilityMeasure ν} := by
  rw [mem_extremePoints_iff_left]
  refine ⟨M.law_mem_invariantProbabilityMeasures, ?_⟩
  rintro ν₁ hν₁ ν₂ hν₂ ⟨a, b, ha, hb, hab, heq⟩
  haveI : IsProbabilityMeasure ν₁ := hν₁.2
  have hac : ν₁ ≪ (M.law : Measure (RelStructure S (Vinfinite S))) := by
    rw [← heq]
    exact (Measure.absolutelyContinuous_smul ha.ne').add_right _
  exact M.eq_of_absolutelyContinuous hM hν₁.1 hac

/-- **Ergodicity is extremality** (headline of R3c step 2): an exchangeable relational law is
ergodic for the finitely supported sortwise relabeling group if and only if it is an extreme
point of the set of relabeling-invariant probability measures on the infinite structure
space. -/
theorem InfiniteRelExchangeableLaw.isErgodic_iff_mem_extremePoints [Fintype S.Srt]
    (M : InfiniteRelExchangeableLaw S) :
    M.IsErgodic ↔ (M.law : Measure (RelStructure S (Vinfinite S))) ∈
      Set.extremePoints ℝ≥0∞
        {ν : Measure (RelStructure S (Vinfinite S)) |
          (∀ σ, SortwiseFinSupp (S := S) σ → ν.map (RelStructure.relabel σ) = ν) ∧
          IsProbabilityMeasure ν} :=
  ⟨M.mem_extremePoints_of_isErgodic, M.isErgodic_of_mem_extremePoints⟩

end RelSignature
