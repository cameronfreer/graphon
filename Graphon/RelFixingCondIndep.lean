/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelEqualityPattern
import Graphon.RelFixingAlgebra
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
  abstracted;
* the private **window algebras** (events depending only on coordinates supported in a
  given set of tagged vertices) — the polling factors. Their identification with the raw
  `fixingAlgebra` happens only modulo the law, in a later layer; no completion enters any
  definition here.
-/

open MeasureTheory

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

/-! ### The private window (polling) algebras -/

section WindowAlgebras

variable {S : RelSignature}

/-- **The window algebra** of a set `W` of tagged vertices: events depending only on the
coordinates whose support lies inside `W` — the observable, coordinate-generated factor, in
contrast to the invariance-defined `fixingAlgebra`. -/
@[implicit_reducible]
private def windowAlgebra (W : Set (Σ s : S.Srt, Vinfinite S s)) :
    MeasurableSpace (RelStructure S (Vinfinite S)) :=
  MeasurableSpace.comap
    (fun (X : RelStructure S (Vinfinite S))
      (c : {c : RelCoord S (Vinfinite S) // ↑(RelCoord.support c) ⊆ W}) => X c.1)
    inferInstance

private theorem windowAlgebra_le (W : Set (Σ s : S.Srt, Vinfinite S s)) :
    windowAlgebra (S := S) W ≤
      (inferInstance : MeasurableSpace (RelStructure S (Vinfinite S))) := by
  have hproj : Measurable (fun (X : RelStructure S (Vinfinite S))
      (c : {c : RelCoord S (Vinfinite S) // ↑(RelCoord.support c) ⊆ W}) => X c.1) :=
    measurable_pi_iff.mpr fun c => measurable_pi_apply _
  exact hproj.comap_le

private theorem windowAlgebra_mono {W W' : Set (Σ s : S.Srt, Vinfinite S s)}
    (h : W ⊆ W') : windowAlgebra (S := S) W ≤ windowAlgebra (S := S) W' := by
  have hfactor : (fun (X : RelStructure S (Vinfinite S))
        (c : {c : RelCoord S (Vinfinite S) // ↑(RelCoord.support c) ⊆ W}) => X c.1) =
      (fun (Y : {c : RelCoord S (Vinfinite S) // ↑(RelCoord.support c) ⊆ W'} → Bool)
        (c : {c : RelCoord S (Vinfinite S) // ↑(RelCoord.support c) ⊆ W}) =>
          Y ⟨c.1, c.2.trans h⟩) ∘
      (fun (X : RelStructure S (Vinfinite S))
        (c : {c : RelCoord S (Vinfinite S) // ↑(RelCoord.support c) ⊆ W'}) => X c.1) := rfl
  have hr : Measurable (fun (Y : {c : RelCoord S (Vinfinite S) //
        ↑(RelCoord.support c) ⊆ W'} → Bool)
      (c : {c : RelCoord S (Vinfinite S) // ↑(RelCoord.support c) ⊆ W}) =>
        Y ⟨c.1, c.2.trans h⟩) :=
    measurable_pi_iff.mpr fun c => measurable_pi_apply _
  rw [windowAlgebra, windowAlgebra, hfactor, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hr.comap_le

end WindowAlgebras

end RelSignature
