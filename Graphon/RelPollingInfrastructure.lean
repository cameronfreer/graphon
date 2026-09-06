/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelEqualityPattern
import Graphon.RelFixingAlgebra
import Graphon.RelErgodicLinks
import Mathlib.Probability.Independence.Conditional

/-!
# Polling infrastructure for the relative-independence arguments (R4, #107)

The reusable engine behind the polling arguments: the `L²`-squeeze tail property, measure
preservation of the sortwise action, and the upgrade of `fixingAlgebra`-invariance from finitely
supported to arbitrary permutations. Extracted from `Graphon.RelFixingCondIndep` when the
rankwise relative-independence argument became its second consumer.

Three declarations are public, and are the whole intended interface:

* `condExp_ae_eq_condExp_of_comap_eq` — **the tail engine** (Austin, arXiv:0801.1698, proof of
  Theorem 3.1, abstracted): a measure-preserving `T` that fixes `f` a.e. and pulls the
  conditioning algebra `m₁` back to a sub-algebra `m₂ ≤ m₁` forces `μ[f|m₁] =ᵐ[μ] μ[f|m₂]`;
* `InfiniteRelExchangeableLaw.measurePreserving_relabel` — the sortwise action is measure
  preserving under any exchangeable law, for *every* permutation family, not merely finitely
  supported ones;
* `InfiniteRelExchangeableLaw.relabel_preimage_ae_eq_of_fixingAlgebra_of_finiteActive` — a
  `fixingAlgebra A`-event is invariant modulo the law under every **finite-active** sortwise
  permutation fixing `A` (identity outside finitely many sorts), which is what supplies the
  engine's `f ∘ T =ᵐ f`; countable-only, since the approximating finitely supported permutation
  is the identity on the inactive sorts;
* `InfiniteRelExchangeableLaw.relabel_preimage_ae_eq_of_fixingAlgebra` — the `[Fintype S.Srt]`
  corollary for an arbitrary sortwise permutation fixing `A`.

The `L²` squeeze and the conditional-expectation transport along `MeasurableSpace.comap` remain
private: they are the proof of the tail engine, not part of its interface.
-/

open MeasureTheory

open scoped ENNReal symmDiff

namespace RelSignature

/-! ### Generic conditional-expectation tools -/

section CondExpTools

variable {Ω : Type*} {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The `L²` squeeze**: for nested conditioning algebras, if the energy of the fine
conditional expectation is at most that of the coarse one, the two conditional expectations
agree a.e. — Pythagoras for the orthogonal projections. -/
private theorem condExp_ae_eq_condExp_of_integral_sq_le
    (h21 : m₂ ≤ m₁) (h1 : m₁ ≤ mΩ) {f : Ω → ℝ} (hf : MemLp f 2 μ)
    (hle : ∫ x, (μ[f|m₁]) x ^ 2 ∂μ ≤ ∫ x, (μ[f|m₂]) x ^ 2 ∂μ) :
    μ[f|m₁] =ᵐ[μ] μ[f|m₂] := by
  have hgL2 : MemLp (μ[f|m₁]) 2 μ := hf.condExp one_le_two
  have heL2 : MemLp (μ[f|m₂]) 2 μ := hf.condExp one_le_two
  have htower : μ[μ[f|m₁]|m₂] =ᵐ[μ] μ[f|m₂] := condExp_condExp_of_le h21 h1
  have hpull : μ[μ[f|m₁] * μ[f|m₂]|m₂] =ᵐ[μ] μ[μ[f|m₁]|m₂] * μ[f|m₂] :=
    condExp_mul_of_aestronglyMeasurable_right
      stronglyMeasurable_condExp.aestronglyMeasurable
      (hgL2.integrable_mul heL2) (hgL2.integrable one_le_two)
  have hcross : ∫ x, (μ[f|m₁]) x * (μ[f|m₂]) x ∂μ = ∫ x, (μ[f|m₂]) x ^ 2 ∂μ := by
    calc ∫ x, (μ[f|m₁]) x * (μ[f|m₂]) x ∂μ
        = ∫ x, (μ[μ[f|m₁] * μ[f|m₂]|m₂]) x ∂μ :=
          (integral_condExp (h21.trans h1)).symm
      _ = ∫ x, (μ[μ[f|m₁]|m₂]) x * (μ[f|m₂]) x ∂μ := integral_congr_ae hpull
      _ = ∫ x, (μ[f|m₂]) x ^ 2 ∂μ := by
          refine integral_congr_ae (htower.mono fun x hx => ?_)
          show (μ[μ[f|m₁]|m₂]) x * (μ[f|m₂]) x = (μ[f|m₂]) x ^ 2
          rw [hx, sq]
  have hexp : ∫ x, ((μ[f|m₁]) x - (μ[f|m₂]) x) ^ 2 ∂μ =
      ∫ x, (μ[f|m₁]) x ^ 2 ∂μ - ∫ x, (μ[f|m₂]) x ^ 2 ∂μ := by
    have hptw : ∀ x, ((μ[f|m₁]) x - (μ[f|m₂]) x) ^ 2 =
        (μ[f|m₁]) x ^ 2 - 2 * ((μ[f|m₁]) x * (μ[f|m₂]) x) + (μ[f|m₂]) x ^ 2 := fun x => by
      ring
    have hsqg : Integrable (fun x => (μ[f|m₁]) x ^ 2) μ := hgL2.integrable_sq
    have hsqe : Integrable (fun x => (μ[f|m₂]) x ^ 2) μ := heL2.integrable_sq
    have hmul : Integrable (fun x => (μ[f|m₁]) x * (μ[f|m₂]) x) μ :=
      hgL2.integrable_mul heL2
    have hmul2 : Integrable (fun x => 2 * ((μ[f|m₁]) x * (μ[f|m₂]) x)) μ := hmul.const_mul 2
    calc ∫ x, ((μ[f|m₁]) x - (μ[f|m₂]) x) ^ 2 ∂μ
        = ∫ x, ((μ[f|m₁]) x ^ 2 - 2 * ((μ[f|m₁]) x * (μ[f|m₂]) x) + (μ[f|m₂]) x ^ 2) ∂μ := by
          simp only [hptw]
      _ = ∫ x, ((μ[f|m₁]) x ^ 2 - 2 * ((μ[f|m₁]) x * (μ[f|m₂]) x)) ∂μ +
            ∫ x, (μ[f|m₂]) x ^ 2 ∂μ :=
          integral_add
            (f := fun x => (μ[f|m₁]) x ^ 2 - 2 * ((μ[f|m₁]) x * (μ[f|m₂]) x))
            (g := fun x => (μ[f|m₂]) x ^ 2) (hsqg.sub hmul2) hsqe
      _ = ∫ x, (μ[f|m₁]) x ^ 2 ∂μ - 2 * ∫ x, (μ[f|m₁]) x * (μ[f|m₂]) x ∂μ +
            ∫ x, (μ[f|m₂]) x ^ 2 ∂μ := by
          rw [integral_sub (f := fun x => (μ[f|m₁]) x ^ 2)
              (g := fun x => 2 * ((μ[f|m₁]) x * (μ[f|m₂]) x)) hsqg hmul2,
            integral_const_mul]
      _ = ∫ x, (μ[f|m₁]) x ^ 2 ∂μ - ∫ x, (μ[f|m₂]) x ^ 2 ∂μ := by
          rw [hcross]; ring
  have hzero : ∫ x, ((μ[f|m₁]) x - (μ[f|m₂]) x) ^ 2 ∂μ = 0 :=
    le_antisymm (by rw [hexp]; linarith) (integral_nonneg fun x => sq_nonneg _)
  have hsq0 : (fun x => ((μ[f|m₁]) x - (μ[f|m₂]) x) ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
      (hgL2.sub heL2).integrable_sq).mp hzero
  filter_upwards [hsq0] with x hx
  have h0 : (μ[f|m₁]) x - (μ[f|m₂]) x = 0 := by
    have : ((μ[f|m₁]) x - (μ[f|m₂]) x) ^ 2 = 0 := hx
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  linarith

/-- **Transport**: conditional expectation commutes with a measure-preserving map, the
conditioning algebra pulled back along `MeasurableSpace.comap`. -/
theorem condExp_comp_of_measurePreserving
    {T : Ω → Ω} (hT : Measurable T) (hTμ : MeasurePreserving T μ μ)
    (hm : m₁ ≤ mΩ) {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f ∘ T | MeasurableSpace.comap T m₁] =ᵐ[μ] (μ[f | m₁]) ∘ T := by
  have hm' : MeasurableSpace.comap T m₁ ≤ mΩ :=
    (MeasurableSpace.comap_mono hm).trans hT.comap_le
  have key : ∀ (h : Ω → ℝ) (s' : Set Ω), AEStronglyMeasurable h μ → MeasurableSet s' →
      ∫ x in T ⁻¹' s', h (T x) ∂μ = ∫ y in s', h y ∂μ := by
    intro h s' hh hs'
    have hrestrict : μ.restrict s' = (μ.restrict (T ⁻¹' s')).map T := by
      conv_lhs => rw [← hTμ.map_eq]
      exact Measure.restrict_map hT hs'
    calc ∫ x in T ⁻¹' s', h (T x) ∂μ
        = ∫ y, h y ∂((μ.restrict (T ⁻¹' s')).map T) :=
          (integral_map hT.aemeasurable.restrict (by rw [← hrestrict]; exact hh.restrict)).symm
      _ = ∫ y in s', h y ∂μ := by rw [← hrestrict]
  have hfT : Integrable (f ∘ T) μ :=
    ((memLp_one_iff_integrable.mpr hf).comp_measurePreserving hTμ).integrable le_rfl
  have hgT : Integrable ((μ[f|m₁]) ∘ T) μ :=
    ((memLp_one_iff_integrable.mpr integrable_condExp).comp_measurePreserving
      hTμ).integrable le_rfl
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm' hfT
    (fun s _ _ => hgT.integrableOn) ?_ ?_).symm
  · rintro - ⟨s', hs', rfl⟩ -
    calc ∫ x in T ⁻¹' s', ((μ[f|m₁]) ∘ T) x ∂μ
        = ∫ y in s', (μ[f|m₁]) y ∂μ :=
          key (μ[f|m₁]) s' (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
            (hm _ hs')
      _ = ∫ y in s', f y ∂μ := setIntegral_condExp hm hf hs'
      _ = ∫ x in T ⁻¹' s', (f ∘ T) x ∂μ :=
          (key f s' hf.aestronglyMeasurable (hm _ hs')).symm
  · exact (stronglyMeasurable_condExp.comp_measurable
      (Measurable.of_comap_le le_rfl)).aestronglyMeasurable

/-- **The tail-property engine** (Austin, proof of Theorem 3.1, p. 99, abstracted): if a
measure-preserving `T` fixes `f` a.e. and pulls the conditioning algebra `m₁` back to a
sub-algebra `m₂ ≤ m₁`, the two conditional expectations agree a.e. — the energies agree by
measure preservation, and the squeeze concludes. -/
theorem condExp_ae_eq_condExp_of_comap_eq
    {T : Ω → Ω} (hT : Measurable T) (hTμ : MeasurePreserving T μ μ)
    (hm : m₁ ≤ mΩ) (h2m : m₂ ≤ m₁) (hcomap : MeasurableSpace.comap T m₁ = m₂)
    {f : Ω → ℝ} (hf : MemLp f 2 μ) (hfT : f ∘ T =ᵐ[μ] f) :
    μ[f|m₁] =ᵐ[μ] μ[f|m₂] := by
  have hint : Integrable f μ := hf.integrable one_le_two
  have htrans : μ[f|m₂] =ᵐ[μ] (μ[f|m₁]) ∘ T := by
    calc μ[f|m₂] = μ[f|MeasurableSpace.comap T m₁] := by rw [hcomap]
      _ =ᵐ[μ] μ[f ∘ T|MeasurableSpace.comap T m₁] := (condExp_congr_ae hfT).symm
      _ =ᵐ[μ] (μ[f|m₁]) ∘ T := condExp_comp_of_measurePreserving hT hTμ hm hint
  have henergy : ∫ x, (μ[f|m₂]) x ^ 2 ∂μ = ∫ x, (μ[f|m₁]) x ^ 2 ∂μ := by
    have hsq : (fun x => (μ[f|m₂]) x ^ 2) =ᵐ[μ] fun x => ((μ[f|m₁]) (T x)) ^ 2 :=
      htrans.mono fun x hx => by
        show (μ[f|m₂]) x ^ 2 = ((μ[f|m₁]) (T x)) ^ 2
        rw [hx]; rfl
    rw [integral_congr_ae hsq]
    have hG : AEStronglyMeasurable (fun y => (μ[f|m₁]) y ^ 2) (μ.map T) := by
      rw [hTμ.map_eq]
      exact ((stronglyMeasurable_condExp.mono hm).measurable.pow_const 2).aestronglyMeasurable
    rw [← integral_map hT.aemeasurable hG, hTμ.map_eq]
  exact condExp_ae_eq_condExp_of_integral_sq_le h2m hm hf henergy.ge

end CondExpTools

/-! ### Measure preservation under the exchangeable law -/

section MeasurePreserving

variable {S : RelSignature}

/-- The relabeling action is measure preserving under any exchangeable law — for **every**
sortwise permutation, not merely a finitely supported one, since the law is invariant under
the full sortwise action by definition. -/
theorem InfiniteRelExchangeableLaw.measurePreserving_relabel (M : InfiniteRelExchangeableLaw S)
    (σ : ∀ _ : S.Srt, Equiv.Perm ℕ) :
    MeasurePreserving (RelStructure.relabel σ)
      (M.law : Measure (RelStructure S (Vinfinite S)))
      (M.law : Measure (RelStructure S (Vinfinite S))) :=
  ⟨measurable_relabel σ, M.exchangeable σ⟩

end MeasurePreserving

/-! ### Arbitrary-permutation a.e. invariance of fixing-algebra events -/

section AeInvariance

variable {S : RelSignature}

/-- **Arbitrary-permutation a.e. invariance of finite-active fixing events** (the `f ∘ T =ᵐ f`
input of the tail engine): a `finiteActiveFixingAlgebra A`-event `E` — in particular any
`fixingAlgebra A`-event — is invariant under *every* sortwise permutation fixing `A` pointwise
with finitely many active sorts — no finite-support bound on
the vertices is required — modulo `M.law`. Only the active sorts need a common support bound
for the approximating finitely supported permutation; on the inactive sorts both are the
identity, which is what keeps `[Fintype S.Srt]` out. This
bridges Austin's literally-window-measurable colours (arXiv:0801.1698, Prop 3.12) to the
larger invariance-measurable `fixingAlgebra A`. Proof: approximate `E` in measure by an
initial cylinder `D` (`exists_initialAlgebra_measure_symmDiff_lt`, R3); build a finitely
supported `π` agreeing with `σ` on a window enlarged to contain both the cylinder block and
all of `A` (`exists_finSupp_perm_extend`) — since `σ` fixes `A` and the window covers `A`,
`π` fixes `A`, so `relabel π ⁻¹' E = E` exactly; then
`μ(σ⁻¹E ∆ E) ≤ μ(σ⁻¹(E ∆ D)) + μ(π⁻¹(D ∆ E)) = 2·μ(E ∆ D)` using `σ⁻¹D = π⁻¹D` (window
agreement) and measure preservation, and let the approximation error vanish. -/
theorem InfiniteRelExchangeableLaw.relabel_preimage_ae_eq_of_finiteActiveFixingAlgebra
    [Countable S.Rel] (M : InfiniteRelExchangeableLaw S)
    {A : Finset (Σ s : S.Srt, Vinfinite S s)} {E : Set (RelStructure S (Vinfinite S))}
    (hE : MeasurableSet[RelStructure.finiteActiveFixingAlgebra A] E)
    {σ : ∀ _ : S.Srt, Equiv.Perm ℕ} (hσfin : SortwiseFiniteActive (S := S) σ)
    (hσ : ∀ v ∈ A, σ v.1 v.2 = v.2) :
    RelStructure.relabel σ ⁻¹' E =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))] E := by
  classical
  set μ : Measure (RelStructure S (Vinfinite S)) :=
    (M.law : Measure (RelStructure S (Vinfinite S))) with hμ
  haveI : IsProbabilityMeasure μ := M.law.2
  have hEmeas : MeasurableSet E := hE.1
  have hMPσ : MeasurePreserving (RelStructure.relabel σ) μ μ := measurePreserving_relabel M σ
  have key : ∀ ε : ℝ≥0∞, 0 < ε → μ ((RelStructure.relabel σ ⁻¹' E) ∆ E) < ε := by
    intro ε hε
    obtain ⟨k, D, hDk, hDlt⟩ :=
      M.exists_initialAlgebra_measure_symmDiff_lt hEmeas (ENNReal.half_pos hε.ne')
    have hDmeas : MeasurableSet D := RelStructure.initialAlgebra_le k _ hDk
    set n : S.Srt → ℕ := fun s => max (k s) (A.sup (fun p => p.2) + 1) with hn
    have hkn : ∀ s, k s ≤ n s := fun s => le_max_left _ _
    have hAn : ∀ v ∈ A, v.2 < n v.1 := fun v hv =>
      lt_of_le_of_lt (Finset.le_sup hv)
        (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _))
    set e : ∀ s, Fin (n s) ↪ ℕ := fun s =>
      ⟨fun i => σ s (i : ℕ), fun a b h => Fin.val_injective ((σ s).injective h)⟩ with he
    obtain ⟨T, hT⟩ := hσfin
    choose π₀ N hsupp hagree₀ using fun s => exists_finSupp_perm_extend (e s)
    -- take the identity on the inactive sorts, where `σ` is the identity too
    set π : ∀ s : S.Srt, Equiv.Perm ℕ := fun s => if s ∈ T then π₀ s else 1 with hπdef
    have hagree : ∀ s (i : Fin (n s)), π s (i : ℕ) = σ s (i : ℕ) := by
      intro s i
      by_cases hs : s ∈ T
      · simp only [hπdef, if_pos hs]
        exact hagree₀ s i
      · simp only [hπdef, if_neg hs, hT s hs, Equiv.Perm.one_apply]
    have hπ_fs : SortwiseFinSupp (S := S) π := by
      refine ⟨T.sup N, fun s x hx => ?_⟩
      by_cases hs : s ∈ T
      · simp only [hπdef, if_pos hs]
        exact hsupp s x (le_trans (Finset.le_sup hs) hx)
      · simp only [hπdef, if_neg hs, Equiv.Perm.one_apply]
    have hπ_fix : ∀ v ∈ A, π v.1 v.2 = v.2 := by
      intro v hv
      have hval : π v.1 v.2 = σ v.1 v.2 := hagree v.1 ⟨v.2, hAn v hv⟩
      rw [hval]; exact hσ v hv
    have hπ_fa : SortwiseFiniteActive (S := S) π := ⟨T, fun s hs => by simp only [hπdef, if_neg hs]⟩
    have hπE : RelStructure.relabel π ⁻¹' E = E := hE.2 π ⟨hπ_fs, hπ_fix⟩ hπ_fa
    have hMPπ : MeasurePreserving (RelStructure.relabel π) μ μ := measurePreserving_relabel M π
    have hcompeq : RelStructure.restrictFin n ∘ RelStructure.relabel σ
        = RelStructure.restrictFin n ∘ RelStructure.relabel π := by
      funext X
      show RelStructure.comap (fun s => (Fin.valEmbedding : Fin (n s) → ℕ))
          (RelStructure.comap (fun s => ⇑(σ s)) X)
          = RelStructure.comap (fun s => (Fin.valEmbedding : Fin (n s) → ℕ))
          (RelStructure.comap (fun s => ⇑(π s)) X)
      rw [← RelStructure.comap_comp, ← RelStructure.comap_comp]
      congr 1
      funext s i
      exact (hagree s i).symm
    have hDn : MeasurableSet[RelStructure.initialAlgebra n] D :=
      RelStructure.initialAlgebra_mono hkn _ hDk
    obtain ⟨D₀, hD₀, hD₀eq⟩ := MeasurableSpace.measurableSet_comap.mp hDn
    have hσπD : RelStructure.relabel σ ⁻¹' D = RelStructure.relabel π ⁻¹' D := by
      rw [← hD₀eq, ← Set.preimage_comp, ← Set.preimage_comp, hcompeq]
    have h1 : μ ((RelStructure.relabel σ ⁻¹' E) ∆ (RelStructure.relabel σ ⁻¹' D)) = μ (E ∆ D) := by
      rw [← Set.preimage_symmDiff]
      exact hMPσ.measure_preimage (hEmeas.symmDiff hDmeas).nullMeasurableSet
    have h2 : μ ((RelStructure.relabel σ ⁻¹' D) ∆ E) = μ (D ∆ E) := by
      rw [hσπD,
        show (RelStructure.relabel π ⁻¹' D) ∆ E = RelStructure.relabel π ⁻¹' (D ∆ E) from by
          rw [Set.preimage_symmDiff, hπE]]
      exact hMPπ.measure_preimage (hDmeas.symmDiff hEmeas).nullMeasurableSet
    calc μ ((RelStructure.relabel σ ⁻¹' E) ∆ E)
        ≤ μ ((RelStructure.relabel σ ⁻¹' E) ∆ (RelStructure.relabel σ ⁻¹' D))
            + μ ((RelStructure.relabel σ ⁻¹' D) ∆ E) := measure_symmDiff_le _ _ _
      _ = μ (D ∆ E) + μ (D ∆ E) := by rw [h1, h2, symmDiff_comm E D]
      _ < ε := by
          rw [← ENNReal.add_halves ε]; exact ENNReal.add_lt_add hDlt hDlt
  rw [← measure_symmDiff_eq_zero_iff]
  by_contra hne
  exact absurd (key _ (pos_iff_ne_zero.mpr hne)) (lt_irrefl _)


/-- The raw-fixing-event form: `fixingAlgebra A ≤ finiteActiveFixingAlgebra A`. -/
theorem InfiniteRelExchangeableLaw.relabel_preimage_ae_eq_of_fixingAlgebra_of_finiteActive
    [Countable S.Rel] (M : InfiniteRelExchangeableLaw S)
    {A : Finset (Σ s : S.Srt, Vinfinite S s)} {E : Set (RelStructure S (Vinfinite S))}
    (hE : MeasurableSet[RelStructure.fixingAlgebra A] E)
    {σ : ∀ _ : S.Srt, Equiv.Perm ℕ} (hσfin : SortwiseFiniteActive (S := S) σ)
    (hσ : ∀ v ∈ A, σ v.1 v.2 = v.2) :
    RelStructure.relabel σ ⁻¹' E =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))] E :=
  M.relabel_preimage_ae_eq_of_finiteActiveFixingAlgebra
    (RelStructure.fixingAlgebra_le_finiteActiveFixingAlgebra A E hE) hσfin hσ

/-- The finite-active statement at `T = univ`: under finitely many sorts, every sortwise
permutation fixing `A` preserves each `fixingAlgebra A`-event modulo `M.law`. -/
theorem InfiniteRelExchangeableLaw.relabel_preimage_ae_eq_of_fixingAlgebra
    [Fintype S.Srt] [Countable S.Rel] (M : InfiniteRelExchangeableLaw S)
    {A : Finset (Σ s : S.Srt, Vinfinite S s)} {E : Set (RelStructure S (Vinfinite S))}
    (hE : MeasurableSet[RelStructure.fixingAlgebra A] E)
    {σ : ∀ _ : S.Srt, Equiv.Perm ℕ} (hσ : ∀ v ∈ A, σ v.1 v.2 = v.2) :
    RelStructure.relabel σ ⁻¹' E =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))] E :=
  M.relabel_preimage_ae_eq_of_fixingAlgebra_of_finiteActive hE
    (SortwiseFiniteActive.of_fintype σ) hσ

end AeInvariance

end RelSignature
