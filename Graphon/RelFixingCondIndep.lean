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
# Conditional independence of the fixing σ-algebras (R4 converse piece 2b, #107)

The relative-independence core of the converse representation theorem, following Austin,
*On exchangeable random variables and the statistics of large graphs and hypergraphs*
(Probab. Surveys 2008, arXiv:0801.1698), Lemma 3.11 and Proposition 3.12 (pp. 107–108),
whose mechanism is the `L²` "tail property" squeeze of the proof of Theorem 3.1 (p. 99);
the closest Kallenberg precursor is Lemma 7.6 (*Probabilistic Symmetries*, pp. 308–322).
Target (public, final layer): for **every** exchangeable law `M` — no dissociation —

`CondIndep (fixingAlgebra (A ∩ B)) (fixingAlgebra A) (fixingAlgebra B)
  (fixingAlgebra_le _) M.law`.

This first layer is the measure-theoretic engine, all `private`:

* the **`L²` squeeze** `condExp_ae_eq_condExp_of_integral_sq_le`: nested conditioning
  algebras whose conditional expectations have comparable energies produce equal
  conditional expectations (Pythagoras for the projections);
* **transport** `condExp_comp_of_measurePreserving`: conditional expectation commutes with
  a measure-preserving map along `MeasurableSpace.comap`;
* the **tail-property engine** `condExp_ae_eq_condExp_of_comap_eq` combining the two: if a
  measure-preserving `T` fixes `f` a.e. and pulls the conditioning algebra `m₁` back to a
  sub-algebra `m₂ ≤ m₁`, then `μ[f|m₁] =ᵐ[μ] μ[f|m₂]` — Austin's Theorem 3.1 step,
  abstracted.

No completion and no law enter any definition here. On top of the engine sit the **a.e.
invariance** of `fixingAlgebra A`-events under *every* sortwise permutation fixing `A`
(`relabel_preimage_ae_eq_of_fixingAlgebra`, the `f ∘ T =ᵐ f` input), and the **poll geometry**
the engine runs on:

* `pollIndex` / `pollShift` — poll slots along a two-sided `ℤ`-orbit transported to `ℕ`. The
  two-sidedness is forced: a *unilateral* shift of the blocks is not a bijection (slot `0`
  would have no preimage), so the negative half serves as predecessor reservoir;
* `pollBlock` / `pollPerm` — the copies `Q m` of `D = B \ A` in slot `m` (with `Q 0 = D`) and
  the sortwise permutation that carries `Q m` onto `Q (m+1)` while fixing every vertex below
  the layout bound outside `D`, in particular all of `A`;
* `pollTailAlgebra` — the tail **joins** `𝒯 n = ⨆_{m ≥ n} fixingAlgebra (C ∪ Q m)`, with
  `C = A ∩ B`. The individual `fixingAlgebra (C ∪ Q m)` are *not* usable: over distinct deep
  blocks they are pairwise incomparable (hence no antitone sequence for Lévy downward), and
  `fixingAlgebra (C ∪ Q m) ≤ fixingAlgebra B` is false — monotonicity would demand
  `C ∪ Q m ⊆ B`, while `Q m` lies outside `B`. The joins are antitone, dominate
  `fixingAlgebra B` at `n = 0`, satisfy `comap (relabel ρ) (𝒯 n) = 𝒯 (n+1)` exactly, and have
  `⨅ n, 𝒯 n = fixingAlgebra C` — the last a **raw** σ-algebra equality, no law and no null
  sets, available because the generators are fixing algebras rather than coordinate-generated
  window algebras (an earlier draft of this file carried such window algebras; the join route
  makes them unnecessary, so they are gone).

The layer closes with the **reduction** `condExp_fixingAlgebra_ae_eq_condExp_inter`:
`μ[f|fixingAlgebra B] =ᵐ μ[f|fixingAlgebra (A ∩ B)]` for `f` a.e. invariant under the
permutations fixing `A`, and its indicator form for a `fixingAlgebra A`-event. This is the
`(⋆)` half of Austin's Proposition 3.12; the conditional-independence assembly is the next
layer.
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
private theorem condExp_ae_eq_condExp_of_comap_eq
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
private theorem measurePreserving_relabel (M : InfiniteRelExchangeableLaw S)
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
private theorem relabel_preimage_ae_eq_of_fixingAlgebra [Fintype S.Srt] [Countable S.Rel]
    (M : InfiniteRelExchangeableLaw S) {A : Finset (Σ s : S.Srt, Vinfinite S s)}
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

/-! ### The poll blocks, the poll shift, and the tail joins -/

section PollSlots

/-- A bijection `ℤ ≃ ℕ` normalized to send `0` to `0`: the index set of the chain of poll
blocks. A *unilateral* shift of the poll blocks cannot be a permutation — block `0` would have
no preimage — so the blocks are laid out along a two-sided `ℤ`-orbit and only the nonnegative
half is ever polled; the negative half is the predecessor reservoir that makes the shift
bijective. -/
private noncomputable def pollEquivInt : ℤ ≃ ℕ :=
  (Denumerable.eqv ℤ).trans (Equiv.swap (Denumerable.eqv ℤ 0) 0)

private theorem pollEquivInt_zero : pollEquivInt 0 = 0 := by
  show Equiv.swap (Denumerable.eqv ℤ 0) 0 (Denumerable.eqv ℤ 0) = 0
  exact Equiv.swap_apply_left _ _

/-- The slot of the `m`-th poll block: an injective `ℕ → ℕ` starting at `0`, obtained by
restricting the two-sided indexing to the nonnegative half. -/
private noncomputable def pollIndex (m : ℕ) : ℕ := pollEquivInt (m : ℤ)

private theorem pollIndex_zero : pollIndex 0 = 0 := by
  rw [pollIndex, Nat.cast_zero, pollEquivInt_zero]

/-- **The poll slots escape every bound**: for each `K` all but finitely many poll blocks sit
above `K`, since `pollIndex` is injective. This is what lets a finitely supported permutation
be dodged by going deep enough into the chain. -/
private theorem exists_le_pollIndex (K : ℕ) : ∃ n, ∀ m, n ≤ m → K ≤ pollIndex m := by
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
private noncomputable def pollShift : Equiv.Perm ℕ :=
  pollEquivInt.symm.trans ((Equiv.addRight (1 : ℤ)).trans pollEquivInt)

private theorem pollShift_pollIndex (m : ℕ) : pollShift (pollIndex m) = pollIndex (m + 1) := by
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
private noncomputable def pollPerm (N : ℕ) [NeZero N]
    (D : Finset (Σ s : S.Srt, Vinfinite S s)) : ∀ _ : S.Srt, Equiv.Perm ℕ := fun s =>
  (Nat.divModEquiv N).trans
    ((Equiv.prodCongrLeft fun i : Fin N =>
        if (⟨s, (i : ℕ)⟩ : Σ s : S.Srt, Vinfinite S s) ∈ D then pollShift else Equiv.refl ℕ).trans
      (Nat.divModEquiv N).symm)

open scoped Classical in
private theorem pollPerm_apply (N : ℕ) [NeZero N] (D : Finset (Σ s : S.Srt, Vinfinite S s))
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
private theorem pollPerm_apply_of_notMem (N : ℕ) [NeZero N]
    (D : Finset (Σ s : S.Srt, Vinfinite S s)) {v : Σ s : S.Srt, Vinfinite S s} (hv : v.2 < N)
    (hvD : v ∉ D) : pollPerm N D v.1 v.2 = v.2 := by
  have := pollPerm_apply N D v.1 0 hv
  rw [Nat.zero_mul, Nat.zero_add] at this
  rw [this, if_neg (by rwa [Sigma.eta]), Nat.zero_mul, Nat.zero_add]

open scoped Classical in
/-- **The `m`-th poll block**: the copy of `D` translated into poll slot `m`, so that slot `0`
is `D` itself. -/
private noncomputable def pollBlock (N : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s)) (m : ℕ) :
    Finset (Σ s : S.Srt, Vinfinite S s) :=
  D.image fun v => ⟨v.1, pollIndex m * N + v.2⟩

private theorem pollBlock_zero (N : ℕ) (D : Finset (Σ s : S.Srt, Vinfinite S s)) :
    pollBlock N D 0 = D := by
  classical
  rw [pollBlock]
  refine (Finset.image_congr fun v _ => ?_).trans D.image_id
  rw [pollIndex_zero, Nat.zero_mul, Nat.zero_add, Sigma.eta, id]

/-- Every vertex of a poll block sits above its slot — the estimate that lets a finitely
supported permutation fix all sufficiently deep blocks. -/
private theorem le_of_mem_pollBlock {N : ℕ} {D : Finset (Σ s : S.Srt, Vinfinite S s)} {m : ℕ}
    {v : Σ s : S.Srt, Vinfinite S s} (hv : v ∈ pollBlock N D m) : pollIndex m * N ≤ v.2 := by
  classical
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
  exact Nat.le_add_right _ _

open scoped Classical in
/-- **The shift moves each poll block to the next one.** -/
private theorem pollBlock_image_pollPerm {N : ℕ} [NeZero N]
    {D : Finset (Σ s : S.Srt, Vinfinite S s)} (hD : ∀ v ∈ D, v.2 < N) (m : ℕ) :
    (pollBlock N D m).image (Sigma.map id fun s => ⇑(pollPerm N D s)) = pollBlock N D (m + 1) := by
  rw [pollBlock, pollBlock, Finset.image_image]
  refine Finset.image_congr fun v hv => ?_
  show (⟨v.1, pollPerm N D v.1 (pollIndex m * N + v.2)⟩ : Σ s : S.Srt, Vinfinite S s) = _
  rw [pollPerm_apply N D v.1 _ (hD v hv), if_pos (by rwa [Sigma.eta]), pollShift_pollIndex]

open scoped Classical in
/-- **The shift fixes the conditioning set** — every vertex of `C` is below `N` and outside
`D`, hence a fixed point of `pollPerm`. -/
private theorem image_pollPerm_of_notMem {N : ℕ} [NeZero N]
    {C D : Finset (Σ s : S.Srt, Vinfinite S s)} (hC : ∀ v ∈ C, v.2 < N)
    (hCD : ∀ v ∈ C, v ∉ D) :
    C.image (Sigma.map id fun s => ⇑(pollPerm N D s)) = C := by
  refine (Finset.image_congr fun v hv => ?_).trans C.image_id
  show (⟨v.1, pollPerm N D v.1 v.2⟩ : Σ s : S.Srt, Vinfinite S s) = id v
  rw [pollPerm_apply_of_notMem N D (hC v hv) (hCD v hv), Sigma.eta, id]

end PollBlocks

/-! ### Invariance under a single permutation -/

section PermInvariant

variable {S : RelSignature}

/-- **The invariance algebra of a single sortwise permutation**: the events literally fixed by
one relabeling. Each `fixingAlgebra A` with `σ` in its stabilizer is contained in it, and —
being a σ-algebra — so is any *join* of such; this is what transfers invariance from the
generators of the tail joins to the whole join. -/
@[implicit_reducible]
private def permInvariantAlgebra (σ : ∀ _ : S.Srt, Equiv.Perm ℕ) :
    MeasurableSpace (RelStructure S (Vinfinite S)) where
  MeasurableSet' E := MeasurableSet E ∧ RelStructure.relabel σ ⁻¹' E = E
  measurableSet_empty := ⟨MeasurableSet.empty, Set.preimage_empty⟩
  measurableSet_compl := fun E hE => ⟨hE.1.compl, by rw [Set.preimage_compl, hE.2]⟩
  measurableSet_iUnion := fun f hf => ⟨MeasurableSet.iUnion fun i => (hf i).1, by
    rw [Set.preimage_iUnion]
    exact Set.iUnion_congr fun i => (hf i).2⟩

private theorem fixingAlgebra_le_permInvariantAlgebra {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    {σ : ∀ _ : S.Srt, Equiv.Perm ℕ} (hσ : SortwiseFixing (S := S) A σ) :
    RelStructure.fixingAlgebra A ≤ permInvariantAlgebra σ := fun _ hE => ⟨hE.1, hE.2 σ hσ⟩

end PermInvariant

/-! ### The tail joins of the poll factors -/

section PollTail

variable {S : RelSignature}

open scoped Classical in
/-- The `m`-th **poll factor's** vertex set: the conditioning set together with the `m`-th poll
block. -/
private noncomputable def pollFactor (C D : Finset (Σ s : S.Srt, Vinfinite S s)) (N m : ℕ) :
    Finset (Σ s : S.Srt, Vinfinite S s) :=
  C ∪ pollBlock N D m

open scoped Classical in
private theorem mem_pollFactor {C D : Finset (Σ s : S.Srt, Vinfinite S s)} {N m : ℕ}
    {v : Σ s : S.Srt, Vinfinite S s} : v ∈ pollFactor C D N m ↔ v ∈ C ∨ v ∈ pollBlock N D m :=
  Finset.mem_union

/-- **The tail join of the poll factors**: `⨆_{m ≥ n} fixingAlgebra (C ∪ Q m)`.

This — not the individual `fixingAlgebra (C ∪ Q m)` — is the object the tail engine runs on.
Individual poll factors over distinct deep blocks are pairwise *incomparable*, so they form no
antitone sequence, and `fixingAlgebra (C ∪ Q m) ≤ fixingAlgebra B` fails outright (monotonicity
would demand `C ∪ Q m ⊆ B`, whereas `Q m` was placed outside `B`). The joins repair both
defects at once: they are antitone in `n`, they dominate `fixingAlgebra B` at `n = 0`, the
shift pulls `𝒯 n` back exactly onto `𝒯 (n+1)`, and their intersection is `fixingAlgebra C`. -/
@[implicit_reducible]
private noncomputable def pollTailAlgebra (C D : Finset (Σ s : S.Srt, Vinfinite S s))
    (N n : ℕ) : MeasurableSpace (RelStructure S (Vinfinite S)) :=
  ⨆ m, ⨆ _ : n ≤ m, RelStructure.fixingAlgebra (pollFactor C D N m)

private theorem pollTailAlgebra_antitone (C D : Finset (Σ s : S.Srt, Vinfinite S s)) (N : ℕ) :
    Antitone (pollTailAlgebra C D N) := fun _ _ hn =>
  iSup₂_le fun m hm => le_iSup₂_of_le m (hn.trans hm) le_rfl

private theorem pollTailAlgebra_le (C D : Finset (Σ s : S.Srt, Vinfinite S s)) (N n : ℕ) :
    pollTailAlgebra C D N n ≤ (inferInstance : MeasurableSpace (RelStructure S (Vinfinite S))) :=
  iSup₂_le fun _ _ => RelStructure.fixingAlgebra_le _

/-- **The polled algebra dominates the `B`-factor**: poll slot `0` is `D` itself, so for
`B = C ∪ D` the algebra `fixingAlgebra B` is literally one of the generators of `𝒯 0`. -/
private theorem fixingAlgebra_le_pollTailAlgebra_zero {B C D : Finset (Σ s : S.Srt, Vinfinite S s)}
    {N : ℕ} (hB : ∀ v, v ∈ B ↔ v ∈ C ∨ v ∈ D) :
    RelStructure.fixingAlgebra B ≤ pollTailAlgebra C D N 0 :=
  le_iSup₂_of_le 0 le_rfl (le_of_eq (by
    congr 1
    exact Finset.ext fun v => by rw [hB v, mem_pollFactor, pollBlock_zero]))

/-- **Transport of the tail joins**: pulling `𝒯 n` back along the poll shift is exactly
`𝒯 (n+1)` — an equality of measurable spaces, obtained generator-by-generator from
`fixingAlgebra_comap_relabel_of_fintype` and the reindexing `m ↦ m + 1`. This is the
hypothesis `comap T m₁ = m₂` of the tail engine, with `m₂ ≤ m₁` supplied by antitonicity. -/
private theorem comap_relabel_pollTailAlgebra [Fintype S.Srt]
    {C D : Finset (Σ s : S.Srt, Vinfinite S s)} {N : ℕ} [NeZero N] (hC : ∀ v ∈ C, v.2 < N)
    (hCD : ∀ v ∈ C, v ∉ D) (hD : ∀ v ∈ D, v.2 < N) (n : ℕ) :
    MeasurableSpace.comap (RelStructure.relabel (pollPerm N D))
        (pollTailAlgebra C D N n) = pollTailAlgebra C D N (n + 1) := by
  classical
  have hgen : ∀ m : ℕ, MeasurableSpace.comap (RelStructure.relabel (pollPerm N D))
      (RelStructure.fixingAlgebra (pollFactor C D N m)) =
      RelStructure.fixingAlgebra (pollFactor C D N (m + 1)) := by
    intro m
    rw [RelStructure.fixingAlgebra_comap_relabel_of_fintype]
    congr 1
    refine Finset.ext fun v => ?_
    rw [mem_pollFactor, Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rcases mem_pollFactor.mp hw with hwC | hwQ
      · exact Or.inl (by
          rw [← image_pollPerm_of_notMem hC hCD]; exact Finset.mem_image_of_mem _ hwC)
      · exact Or.inr (by
          rw [← pollBlock_image_pollPerm hD]; exact Finset.mem_image_of_mem _ hwQ)
    · rintro (hvC | hvQ)
      · obtain ⟨w, hw, rfl⟩ :=
          Finset.mem_image.mp (by rw [image_pollPerm_of_notMem hC hCD]; exact hvC)
        exact ⟨w, mem_pollFactor.mpr (Or.inl hw), rfl⟩
      · obtain ⟨w, hw, rfl⟩ :=
          Finset.mem_image.mp (by rw [pollBlock_image_pollPerm hD]; exact hvQ)
        exact ⟨w, mem_pollFactor.mpr (Or.inr hw), rfl⟩
  rw [pollTailAlgebra, pollTailAlgebra]
  simp_rw [MeasurableSpace.comap_iSup, hgen]
  refine le_antisymm (iSup₂_le fun m hm => le_iSup₂_of_le (m + 1) (by omega) le_rfl)
    (iSup₂_le fun m hm => ?_)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact le_iSup₂_of_le m' (by omega) le_rfl

/-- **The tail joins shrink to the conditioning factor**: `⨅ n, 𝒯 n = fixingAlgebra C`, a *raw*
equality of σ-algebras — no law, no null sets. This is available precisely because the
generators are fixing algebras rather than window algebras: a finitely supported permutation
fixing `C` fixes every sufficiently deep poll block outright, hence lies in the stabilizer of
every generator of `𝒯 n` for large `n`, hence fixes every event of the join. -/
private theorem iInf_pollTailAlgebra {C D : Finset (Σ s : S.Srt, Vinfinite S s)}
    {N : ℕ} [NeZero N] :
    (⨅ n, pollTailAlgebra C D N n) = RelStructure.fixingAlgebra C := by
  have hproj : ∀ (n : ℕ) (E : Set (RelStructure S (Vinfinite S))),
      MeasurableSet[⨅ k, pollTailAlgebra C D N k] E → MeasurableSet[pollTailAlgebra C D N n] E :=
    fun n => iInf_le (fun k => pollTailAlgebra C D N k) n
  have hforward : ∀ E : Set (RelStructure S (Vinfinite S)),
      MeasurableSet[⨅ k, pollTailAlgebra C D N k] E →
        MeasurableSet[RelStructure.fixingAlgebra C] E := by
    intro E hE
    refine ⟨pollTailAlgebra_le C D N 0 E (hproj 0 E hE), ?_⟩
    intro σ hσ
    obtain ⟨M, hM⟩ := hσ.1
    obtain ⟨n, hn⟩ := exists_le_pollIndex M
    have hfix : ∀ m, n ≤ m → SortwiseFixing (S := S) (pollFactor C D N m) σ := by
      intro m hm
      refine ⟨hσ.1, fun v hv => ?_⟩
      rcases mem_pollFactor.mp hv with hvC | hvQ
      · exact hσ.2 v hvC
      · refine hM v.1 v.2 (le_trans ?_ (le_of_mem_pollBlock hvQ))
        calc M = M * 1 := (Nat.mul_one M).symm
          _ ≤ pollIndex m * N :=
            Nat.mul_le_mul (hn m hm) (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
    have hle : pollTailAlgebra C D N n ≤ permInvariantAlgebra σ := by
      rw [pollTailAlgebra]
      exact iSup₂_le fun m hm => fixingAlgebra_le_permInvariantAlgebra (hfix m hm)
    exact (hle E (hproj n E hE)).2
  refine le_antisymm hforward (le_iInf fun n => ?_)
  rw [pollTailAlgebra]
  exact le_iSup₂_of_le n le_rfl
    (RelStructure.fixingAlgebra_mono fun v hv => mem_pollFactor.mpr (Or.inl hv))

end PollTail

/-! ### The core reduction: conditioning on `𝓕 B` collapses to `𝓕 (A ∩ B)` -/

section Reduction

open Filter Topology

variable {S : RelSignature}

/-- **The polled reduction**, in the raw form the poll geometry produces it: for a
square-integrable `f` that is a.e. invariant under every sortwise permutation fixing `A`,
conditioning on `fixingAlgebra B` is conditioning on `fixingAlgebra C`, whenever `B` splits as
`C ⊔ D` with `D` laid out below the bound `N` and disjoint from `A ∪ C`.

The proof is Austin's polling argument (arXiv:0801.1698, Prop. 3.12) run on the tail joins:
the shift `pollPerm N D` fixes `A`, so the tail engine gives `μ[f|𝒯 n] =ᵐ μ[f|𝒯 (n+1)]` at
every `n`; induction makes the whole sequence a.e. constant; Lévy downward
(`tendsto_eLpNorm_condExp_iInf`) identifies its `L¹` limit with `μ[f|⨅ n, 𝒯 n]`, which
`iInf_pollTailAlgebra` rewrites as `μ[f|fixingAlgebra C]`; and the tower property over
`fixingAlgebra B ≤ 𝒯 0` transfers the conclusion back to `B`.

No dissociation is used, and the degenerate case `B ⊆ A` needs no separate treatment: there
`D = ∅`, every poll block is empty, `𝒯 n = fixingAlgebra C` throughout, and each step above
holds trivially. -/
private theorem condExp_fixingAlgebra_ae_eq_of_poll [Fintype S.Srt]
    (M : InfiniteRelExchangeableLaw S)
    {A B C D : Finset (Σ s : S.Srt, Vinfinite S s)} {N : ℕ} [NeZero N]
    (hC : ∀ v ∈ C, v.2 < N) (hCD : ∀ v ∈ C, v ∉ D) (hD : ∀ v ∈ D, v.2 < N)
    (hA : ∀ v ∈ A, v.2 < N) (hAD : ∀ v ∈ A, v ∉ D)
    (hB : ∀ v, v ∈ B ↔ v ∈ C ∨ v ∈ D) (hCB : C ⊆ B)
    {f : RelStructure S (Vinfinite S) → ℝ}
    (hf : MemLp f 2 (M.law : Measure (RelStructure S (Vinfinite S))))
    (hinv : ∀ σ : ∀ _ : S.Srt, Equiv.Perm ℕ, (∀ v ∈ A, σ v.1 v.2 = v.2) →
      f ∘ RelStructure.relabel σ =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))] f) :
    (M.law : Measure (RelStructure S (Vinfinite S)))[f|RelStructure.fixingAlgebra B]
        =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))]
      (M.law : Measure (RelStructure S (Vinfinite S)))[f|RelStructure.fixingAlgebra C] := by
  set μ : Measure (RelStructure S (Vinfinite S)) :=
    (M.law : Measure (RelStructure S (Vinfinite S))) with hμ
  haveI : IsProbabilityMeasure μ := M.law.2
  have hint : Integrable f μ := hf.integrable one_le_two
  have hinf : (⨅ n, pollTailAlgebra C D N n) = RelStructure.fixingAlgebra C :=
    iInf_pollTailAlgebra
  -- the poll shift fixes every vertex of `A`, so stage-1b invariance applies to it
  have hfρ : f ∘ RelStructure.relabel (pollPerm N D) =ᵐ[μ] f :=
    hinv _ fun v hv => pollPerm_apply_of_notMem N D (hA v hv) (hAD v hv)
  -- step 1: the tail engine stabilizes the conditional expectations along the tail joins
  have hstep : ∀ n, μ[f|pollTailAlgebra C D N n] =ᵐ[μ] μ[f|pollTailAlgebra C D N (n + 1)] :=
    fun n => condExp_ae_eq_condExp_of_comap_eq (measurable_relabel _)
      (measurePreserving_relabel M _) (pollTailAlgebra_le C D N n)
      (pollTailAlgebra_antitone C D N (Nat.le_succ n))
      (comap_relabel_pollTailAlgebra hC hCD hD n) hf hfρ
  have hstab : ∀ n, μ[f|pollTailAlgebra C D N 0] =ᵐ[μ] μ[f|pollTailAlgebra C D N n] := by
    intro n
    induction n with
    | zero => exact EventuallyEq.refl _ _
    | succ k ih => exact ih.trans (hstep k)
  -- step 2: the `L¹` limit of an a.e. constant sequence is that constant
  have hlevy := tendsto_eLpNorm_condExp_iInf (pollTailAlgebra C D N)
    (pollTailAlgebra_antitone C D N) (pollTailAlgebra_le C D N) hint
  have hconst : ∀ n,
      eLpNorm (μ[f|pollTailAlgebra C D N n] - μ[f|⨅ k, pollTailAlgebra C D N k]) 1 μ =
      eLpNorm (μ[f|pollTailAlgebra C D N 0] - μ[f|⨅ k, pollTailAlgebra C D N k]) 1 μ :=
    fun n => eLpNorm_congr_ae ((hstab n).symm.sub (EventuallyEq.refl _ _))
  have hzero :
      eLpNorm (μ[f|pollTailAlgebra C D N 0] - μ[f|⨅ k, pollTailAlgebra C D N k]) 1 μ = 0 :=
    (tendsto_nhds_unique (by simpa only [hconst] using hlevy) tendsto_const_nhds).symm
  have hinfle : (⨅ k, pollTailAlgebra C D N k) ≤
      (inferInstance : MeasurableSpace (RelStructure S (Vinfinite S))) := by
    rw [hinf]; exact RelStructure.fixingAlgebra_le C
  have hT0 : μ[f|pollTailAlgebra C D N 0] =ᵐ[μ] μ[f|RelStructure.fixingAlgebra C] := by
    have hmeas : AEStronglyMeasurable
        (μ[f|pollTailAlgebra C D N 0] - μ[f|⨅ k, pollTailAlgebra C D N k]) μ :=
      ((stronglyMeasurable_condExp.mono (pollTailAlgebra_le C D N 0)).sub
        (stronglyMeasurable_condExp.mono hinfle)).aestronglyMeasurable
    have hsub := (eLpNorm_eq_zero_iff hmeas one_ne_zero).mp hzero
    rw [← hinf]
    filter_upwards [hsub] with x hx
    have hx0 : (μ[f|pollTailAlgebra C D N 0]) x - (μ[f|⨅ k, pollTailAlgebra C D N k]) x = 0 := hx
    linarith
  -- step 3: tower over `fixingAlgebra B ≤ 𝒯 0`
  calc μ[f|RelStructure.fixingAlgebra B]
      =ᵐ[μ] μ[μ[f|pollTailAlgebra C D N 0]|RelStructure.fixingAlgebra B] :=
        (condExp_condExp_of_le (fixingAlgebra_le_pollTailAlgebra_zero hB)
          (pollTailAlgebra_le C D N 0)).symm
    _ =ᵐ[μ] μ[μ[f|RelStructure.fixingAlgebra C]|RelStructure.fixingAlgebra B] :=
        condExp_congr_ae hT0
    _ = μ[f|RelStructure.fixingAlgebra C] :=
        condExp_of_stronglyMeasurable (RelStructure.fixingAlgebra_le B)
          (stronglyMeasurable_condExp.mono (RelStructure.fixingAlgebra_mono hCB))
          integrable_condExp

open scoped Classical in
/-- **The core reduction** (Austin, arXiv:0801.1698, Prop. 3.12; Kallenberg, *Probabilistic
Symmetries*, Lemma 7.6): for square-integrable `f` a.e. invariant under every sortwise
permutation fixing `A`, conditioning on `fixingAlgebra B` is conditioning on
`fixingAlgebra (A ∩ B)`. The poll blocks are the deep copies of `B \ A`, laid out above the
common bound of `A` and `B`. -/
private theorem condExp_fixingAlgebra_ae_eq_condExp_inter [Fintype S.Srt]
    (M : InfiniteRelExchangeableLaw S) (A B : Finset (Σ s : S.Srt, Vinfinite S s))
    {f : RelStructure S (Vinfinite S) → ℝ}
    (hf : MemLp f 2 (M.law : Measure (RelStructure S (Vinfinite S))))
    (hinv : ∀ σ : ∀ _ : S.Srt, Equiv.Perm ℕ, (∀ v ∈ A, σ v.1 v.2 = v.2) →
      f ∘ RelStructure.relabel σ =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))] f) :
    (M.law : Measure (RelStructure S (Vinfinite S)))[f|RelStructure.fixingAlgebra B]
        =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))]
      (M.law : Measure (RelStructure S (Vinfinite S)))[f|RelStructure.fixingAlgebra (A ∩ B)] := by
  set N : ℕ := max (A.sup fun v => v.2) (B.sup fun v => v.2) + 1 with hN
  haveI : NeZero N := ⟨Nat.succ_ne_zero _⟩
  have hAlt : ∀ v ∈ A, v.2 < N := fun v hv =>
    Nat.lt_succ_of_le (le_trans (Finset.le_sup hv) (le_max_left _ _))
  have hBlt : ∀ v ∈ B, v.2 < N := fun v hv =>
    Nat.lt_succ_of_le (le_trans (Finset.le_sup hv) (le_max_right _ _))
  refine condExp_fixingAlgebra_ae_eq_of_poll (D := B \ A) M
    (fun v hv => hAlt v (Finset.mem_inter.mp hv).1) (fun v hv hvD =>
      (Finset.mem_sdiff.mp hvD).2 (Finset.mem_inter.mp hv).1)
    (fun v hv => hBlt v (Finset.mem_sdiff.mp hv).1) hAlt
    (fun v hv hvD => (Finset.mem_sdiff.mp hvD).2 hv) (fun v => ?_)
    Finset.inter_subset_right hf hinv
  rw [Finset.mem_inter, Finset.mem_sdiff]
  by_cases hvA : v ∈ A <;> simp [hvA]

open scoped Classical in
/-- **The reduction for a fixing-algebra event** — the form the conditional-independence
assembly consumes: `E[1_E | 𝓕 B] =ᵐ E[1_E | 𝓕 (A ∩ B)]` for every `fixingAlgebra A`-event `E`.
The invariance hypothesis is supplied by stage 1b
(`relabel_preimage_ae_eq_of_fixingAlgebra`), which upgrades the finitary invariance built into
`fixingAlgebra A` to invariance under *every* sortwise permutation fixing `A`. -/
private theorem condExp_indicator_fixingAlgebra_ae_eq_condExp_inter [Fintype S.Srt]
    [Countable S.Rel] (M : InfiniteRelExchangeableLaw S)
    (A B : Finset (Σ s : S.Srt, Vinfinite S s)) {E : Set (RelStructure S (Vinfinite S))}
    (hE : MeasurableSet[RelStructure.fixingAlgebra A] E) :
    (M.law : Measure (RelStructure S (Vinfinite S)))[E.indicator fun _ => (1 : ℝ)|
          RelStructure.fixingAlgebra B]
        =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))]
      (M.law : Measure (RelStructure S (Vinfinite S)))[E.indicator fun _ => (1 : ℝ)|
        RelStructure.fixingAlgebra (A ∩ B)] := by
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  refine condExp_fixingAlgebra_ae_eq_condExp_inter M A B
    (memLp_indicator_const 2 hE.1 1 (Or.inr (measure_ne_top _ _))) fun σ hσ => ?_
  have hcomp : (E.indicator fun _ => (1 : ℝ)) ∘ RelStructure.relabel σ =
      (RelStructure.relabel σ ⁻¹' E).indicator fun _ => (1 : ℝ) := by
    funext X
    simp only [Function.comp_apply, Set.indicator_apply, Set.mem_preimage]
  rw [hcomp]
  exact indicator_ae_eq_of_ae_eq_set (relabel_preimage_ae_eq_of_fixingAlgebra M hE hσ)

end Reduction

end RelSignature
