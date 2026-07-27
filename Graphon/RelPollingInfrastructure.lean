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
* `InfiniteRelExchangeableLaw.relabel_preimage_ae_eq_of_fixingAlgebra` — a
  `fixingAlgebra A`-event is invariant modulo the law under every sortwise permutation fixing
  `A`, which is what supplies the engine's `f ∘ T =ᵐ f`.

The `L²` squeeze and the conditional-expectation transport along `MeasurableSpace.comap` remain
private: they are the proof of the tail engine, not part of its interface.

Alongside the engine sits the **poll layout**: slots along a two-sided `ℤ`-orbit (`pollIndex`,
`pollShift` — a unilateral shift of the blocks is not a bijection), the residue-wise permutation
`pollPerm` that shifts every copy at once, and the blocks `pollBlock`. It moved here from
`Graphon.RelFixingCondIndep` when the rankwise argument needed the same layout rather than a
second copy of it.

The rankwise argument polls a *family* of supports, so it needs the layout to be cut from **one
common copy**: `pollBlock_subset` and `pollBlock_inter` say the blocks respect inclusion and
intersection — the translation is injective, so copying a union and then cutting agrees with
copying each member — and `pollBlock_image_pollPerm_of_subset` says the permutation built from
the whole polled set carries the block of every subset to that subset's next block. Together
these are what keep the overlaps, and hence the equality patterns, of a family of supports
intact under polling.
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
private theorem condExp_comp_of_measurePreserving
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

/-- **Arbitrary-permutation a.e. invariance of fixing-algebra events** (the `f ∘ T =ᵐ f`
input of the tail engine): a `fixingAlgebra A`-event `E` is invariant under *every* sortwise
permutation fixing `A` pointwise — not merely finitely supported ones — modulo `M.law`. This
bridges Austin's literally-window-measurable colours (arXiv:0801.1698, Prop 3.12) to the
larger invariance-measurable `fixingAlgebra A`. Proof: approximate `E` in measure by an
initial cylinder `D` (`exists_initialAlgebra_measure_symmDiff_lt`, R3); build a finitely
supported `π` agreeing with `σ` on a window enlarged to contain both the cylinder block and
all of `A` (`exists_finSupp_perm_extend`) — since `σ` fixes `A` and the window covers `A`,
`π` fixes `A`, so `relabel π ⁻¹' E = E` exactly; then
`μ(σ⁻¹E ∆ E) ≤ μ(σ⁻¹(E ∆ D)) + μ(π⁻¹(D ∆ E)) = 2·μ(E ∆ D)` using `σ⁻¹D = π⁻¹D` (window
agreement) and measure preservation, and let the approximation error vanish. -/
theorem InfiniteRelExchangeableLaw.relabel_preimage_ae_eq_of_fixingAlgebra
    [Fintype S.Srt] [Countable S.Rel] (M : InfiniteRelExchangeableLaw S) {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    {E : Set (RelStructure S (Vinfinite S))}
    (hE : MeasurableSet[RelStructure.fixingAlgebra A] E)
    {σ : ∀ _ : S.Srt, Equiv.Perm ℕ} (hσ : ∀ v ∈ A, σ v.1 v.2 = v.2) :
    RelStructure.relabel σ ⁻¹' E =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))] E := by
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
    choose π N hsupp hagree using fun s => exists_finSupp_perm_extend (e s)
    have hπ_fs : SortwiseFinSupp (S := S) π :=
      ⟨Finset.univ.sup N, fun s x hx =>
        hsupp s x (le_trans (Finset.le_sup (Finset.mem_univ s)) hx)⟩
    have hπ_fix : ∀ v ∈ A, π v.1 v.2 = v.2 := by
      intro v hv
      have hval : π v.1 v.2 = σ v.1 v.2 := hagree v.1 ⟨v.2, hAn v hv⟩
      rw [hval]; exact hσ v hv
    have hπE : RelStructure.relabel π ⁻¹' E = E := hE.2 π ⟨hπ_fs, hπ_fix⟩
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

end AeInvariance

/-! ### The poll layout: slots, blocks, and the shift -/

section PollSlots

/-- A bijection `ℤ ≃ ℕ` normalized to send `0` to `0`: the index set of the chain of poll
blocks. A *unilateral* shift of the poll blocks cannot be a permutation — block `0` would have
no preimage — so the blocks are laid out along a two-sided `ℤ`-orbit and only the nonnegative
half is ever polled; the negative half is the predecessor reservoir that makes the shift
bijective. -/
noncomputable def pollEquivInt : ℤ ≃ ℕ :=
  (Denumerable.eqv ℤ).trans (Equiv.swap (Denumerable.eqv ℤ 0) 0)

theorem pollEquivInt_zero : pollEquivInt 0 = 0 := by
  show Equiv.swap (Denumerable.eqv ℤ 0) 0 (Denumerable.eqv ℤ 0) = 0
  exact Equiv.swap_apply_left _ _

/-- The slot of the `m`-th poll block: an injective `ℕ → ℕ` starting at `0`, obtained by
restricting the two-sided indexing to the nonnegative half. -/
noncomputable def pollIndex (m : ℕ) : ℕ := pollEquivInt (m : ℤ)

theorem pollIndex_zero : pollIndex 0 = 0 := by
  rw [pollIndex, Nat.cast_zero, pollEquivInt_zero]

/-- **The poll slots escape every bound**: for each `K` all but finitely many poll blocks sit
above `K`, since `pollIndex` is injective. This is what lets a finitely supported permutation
be dodged by going deep enough into the chain. -/
theorem exists_le_pollIndex (K : ℕ) : ∃ n, ∀ m, n ≤ m → K ≤ pollIndex m := by
  classical
  refine ⟨((Finset.range K).image fun k => (pollEquivInt.symm k).toNat).sup id + 1,
    fun m hm => ?_⟩
  by_contra hlt
  push Not at hlt
  have hmem : m ∈ (Finset.range K).image fun k => (pollEquivInt.symm k).toNat :=
    Finset.mem_image.mpr ⟨pollIndex m, Finset.mem_range.mpr hlt, by
      rw [pollIndex, pollEquivInt.symm_apply_apply, Int.toNat_natCast]⟩
  have := Finset.le_sup (f := id) hmem
  simp only [id] at this
  omega

/-- **The slot shift**: a permutation of `ℕ` carrying poll slot `m` to poll slot `m + 1` — the
translation by one of the two-sided orbit, transported to `ℕ`. -/
noncomputable def pollShift : Equiv.Perm ℕ :=
  pollEquivInt.symm.trans ((Equiv.addRight (1 : ℤ)).trans pollEquivInt)

theorem pollShift_pollIndex (m : ℕ) : pollShift (pollIndex m) = pollIndex (m + 1) := by
  show pollEquivInt ((Equiv.addRight (1 : ℤ)) (pollEquivInt.symm (pollEquivInt (m : ℤ)))) =
    pollEquivInt ((m + 1 : ℕ) : ℤ)
  rw [pollEquivInt.symm_apply_apply]
  norm_num

end PollSlots

section PollBlocks

variable {S : RelSignature}

open scoped Classical in
/-- **The polling permutation**: in the coordinates `x ↦ (x / N, x % N)` it shifts the slot of
every residue lying in `D` and fixes every other residue. It therefore fixes every tagged
vertex of index `< N` outside `D` — in particular all of `A` once `N` bounds `A ∪ B` — while
translating the `D`-shaped poll block in slot `m` onto the one in slot `m + 1`. -/
noncomputable def pollPerm (N : ℕ) [NeZero N]
    (D : Finset (Σ s : S.Srt, Vinfinite S s)) : ∀ _ : S.Srt, Equiv.Perm ℕ := fun s =>
  (Nat.divModEquiv N).trans
    ((Equiv.prodCongrLeft fun i : Fin N =>
        if (⟨s, (i : ℕ)⟩ : Σ s : S.Srt, Vinfinite S s) ∈ D then pollShift else Equiv.refl ℕ).trans
      (Nat.divModEquiv N).symm)

open scoped Classical in
theorem pollPerm_apply (N : ℕ) [NeZero N] (D : Finset (Σ s : S.Srt, Vinfinite S s))
    (s : S.Srt) (k : ℕ) {x : ℕ} (hx : x < N) :
    pollPerm N D s (k * N + x) =
      (if (⟨s, x⟩ : Σ s : S.Srt, Vinfinite S s) ∈ D then pollShift k else k) * N + x := by
  have hdiv : (k * N + x) / N = k := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.pos_of_neZero N), Nat.div_eq_of_lt hx, Nat.add_zero]
  have hmod : (k * N + x) % N = x := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hx]
  show ((Nat.divModEquiv N).symm ((Equiv.prodCongrLeft _) ((Nat.divModEquiv N) (k * N + x)))) = _
  simp only [Nat.divModEquiv_apply, Nat.divModEquiv_symm_apply, Equiv.prodCongrLeft_apply,
    Fin.ofNat_eq_cast, Fin.val_natCast, hdiv, hmod]
  split_ifs with h
  · rfl
  · rfl

open scoped Classical in
theorem pollPerm_apply_of_notMem (N : ℕ) [NeZero N]
    (D : Finset (Σ s : S.Srt, Vinfinite S s)) {v : Σ s : S.Srt, Vinfinite S s} (hv : v.2 < N)
    (hvD : v ∉ D) : pollPerm N D v.1 v.2 = v.2 := by
  have := pollPerm_apply N D v.1 0 hv
  rw [Nat.zero_mul, Nat.zero_add] at this
  rw [this, if_neg (by rwa [Sigma.eta]), Nat.zero_mul, Nat.zero_add]

open scoped Classical in
/-- **The `m`-th poll block**: the copy of `D` translated into poll slot `m`, so that slot `0`
is `D` itself. -/
noncomputable def pollBlock (N : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s)) (m : ℕ) :
    Finset (Σ s : S.Srt, Vinfinite S s) :=
  D.image fun v => ⟨v.1, pollIndex m * N + v.2⟩

theorem pollBlock_zero (N : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s)) :
    pollBlock N D 0 = D := by
  classical
  rw [pollBlock]
  refine (Finset.image_congr fun v _ => ?_).trans D.image_id
  rw [pollIndex_zero, Nat.zero_mul, Nat.zero_add, Sigma.eta, id]

/-- Every vertex of a poll block sits above its slot — the estimate that lets a finitely
supported permutation fix all sufficiently deep blocks. -/
theorem le_of_mem_pollBlock {N : ℕ} {D : Finset (Σ s : S.Srt, Vinfinite S s)} {m : ℕ}
    {v : Σ s : S.Srt, Vinfinite S s} (hv : v ∈ pollBlock N D m) : pollIndex m * N ≤ v.2 := by
  classical
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
  exact Nat.le_add_right _ _

open scoped Classical in
/-- **The shift moves each poll block to the next one.** -/
theorem pollBlock_image_pollPerm {N : ℕ} [NeZero N]
    {D : Finset (Σ s : S.Srt, Vinfinite S s)} (hD : ∀ v ∈ D, v.2 < N) (m : ℕ) :
    (pollBlock N D m).image (Sigma.map id fun s => ⇑(pollPerm N D s)) = pollBlock N D (m + 1) := by
  rw [pollBlock, pollBlock, Finset.image_image]
  refine Finset.image_congr fun v hv => ?_
  show (⟨v.1, pollPerm N D v.1 (pollIndex m * N + v.2)⟩ : Σ s : S.Srt, Vinfinite S s) = _
  rw [pollPerm_apply N D v.1 _ (hD v hv), if_pos (by rwa [Sigma.eta]), pollShift_pollIndex]

open scoped Classical in
/-- **The shift fixes the conditioning set** — every vertex of `C` is below `N` and outside
`D`, hence a fixed point of `pollPerm`. -/
theorem image_pollPerm_of_notMem {N : ℕ} [NeZero N]
    {C D : Finset (Σ s : S.Srt, Vinfinite S s)} (hC : ∀ v ∈ C, v.2 < N)
    (hCD : ∀ v ∈ C, v ∉ D) :
    C.image (Sigma.map id fun s => ⇑(pollPerm N D s)) = C := by
  refine (Finset.image_congr fun v hv => ?_).trans C.image_id
  show (⟨v.1, pollPerm N D v.1 v.2⟩ : Σ s : S.Srt, Vinfinite S s) = id v
  rw [pollPerm_apply_of_notMem N D (hC v hv) (hCD v hv), Sigma.eta, id]

end PollBlocks
/-! ### One common copy: subsets and overlaps -/

open scoped Classical in
/-- **Blocks respect inclusion.** A subset of the polled set has its block inside the block of
the whole — the copies of different supports are cut from *one* common copy. -/
theorem pollBlock_subset {N : ℕ} {D U : Finset (Σ s : S.Srt, Vinfinite S s)} (h : D ⊆ U)
    (m : ℕ) : pollBlock N D m ⊆ pollBlock N U m :=
  Finset.image_subset_image h

open scoped Classical in
/-- **Blocks respect intersection**, hence preserve overlaps: the translation is injective, so
copying the union of several supports and then cutting agrees with copying each support. This is
what keeps the equality patterns of a family of supports intact under polling, and is the reason
the whole union must be moved by a single map. -/
theorem pollBlock_inter {N : ℕ} (D E : Finset (Σ s : S.Srt, Vinfinite S s)) (m : ℕ) :
    pollBlock N (D ∩ E) m = pollBlock N D m ∩ pollBlock N E m := by
  classical
  refine Finset.image_inter _ _ fun v w hvw => ?_
  obtain ⟨sv, xv⟩ := v
  obtain ⟨sw, xw⟩ := w
  obtain ⟨rfl, hx⟩ := Sigma.mk.injEq .. ▸ hvw
  simpa using hvw

open scoped Classical in
/-- **The shift of the polled set moves every sub-block.** The permutation is built from the
whole polled set `U`, but it carries the block of any `D ⊆ U` to the next block of `D` — one
map, all supports moved coherently. -/
theorem pollBlock_image_pollPerm_of_subset {N : ℕ} [NeZero N]
    {D U : Finset (Σ s : S.Srt, Vinfinite S s)} (hDU : D ⊆ U)
    (hU : ∀ v ∈ U, v.2 < N) (m : ℕ) :
    (pollBlock N D m).image (Sigma.map id fun s => ⇑(pollPerm N U s)) =
      pollBlock N D (m + 1) := by
  classical
  rw [pollBlock, pollBlock, Finset.image_image]
  refine Finset.image_congr fun v hv => ?_
  show (⟨v.1, pollPerm N U v.1 (pollIndex m * N + v.2)⟩ : Σ s : S.Srt, Vinfinite S s) = _
  rw [pollPerm_apply N U v.1 _ (hU v (hDU hv)), if_pos (by rw [Sigma.eta]; exact hDU hv),
    pollShift_pollIndex]

end RelSignature
