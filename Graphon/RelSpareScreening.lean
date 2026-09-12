/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelLocality
import Graphon.RelAdmissibleBase
import Graphon.RelPooledAcceptance

/-!
# Purely spare screening

Fix a rank-`n` representation `C` with `0 < n` which is admissible in the sense of
`RankRepresentation.Admissible`. For two disjoint finite supports `A` and `B`, admissibility
makes the induced structures on `A` and on `B` conditionally independent given the whole latent
array, and locality makes the conditional probability of an `A`-cylinder a function of the
local latent window at `A`.

**Stage 1, the finite-cylinder identity** (`condExp_inter_eq_mul_of_disjoint`), combines the
two. For any measurable observation `ζ` of the latent array which reads at least the local
latent window at `A`, the conditional probability given `ζ` of an `A`-cylinder meeting a
`B`-cylinder and a whole-latent event factors as the product of the conditional probabilities
given `ζ`.

**Stage 2, the extension to full observations** (`condIndepFun_restrict_of_disjoint`), takes
two sortwise self-embeddings `e₀`, `e₁` of the carrier with disjoint ranges: the restriction of
the structure along `e₀` is conditionally independent of the pair (restriction along `e₁`,
whole latent array), given the restriction of the latent array along `e₀`. The generating
π-systems are the measurable cylinders of the two restrictions, crossed with the whole-latent
events on the second side; each generator is a finite cylinder of the form Stage 1 handles.

**The pooled instance** (`PooledRankExtension.condIndepFun_restrictOriginal_restrictPool`) reads
this through the exact joint carrier identification: in any pooled rank extension the original
structure is conditionally independent of the pair (purely spare structure, whole pooled latent
array), given the original old latents.

The statements concern the purely spare structure only. They say nothing about mixed
observations, the conditioning is exactly the σ-algebra of the original old latents, and no
mutual statement at the next rank is made.
-/

universe u

open MeasureTheory ProbabilityTheory

namespace RelSignature

namespace InfiniteRelExchangeableLaw

variable {S : RelSignature.{u}} {M : InfiniteRelExchangeableLaw S} {n : ℕ}

omit M in
/-- Two disjoint finite supports have small overlap at any positive rank. -/
theorem smallOverlap_pair_of_disjoint (hn : 0 < n) {A B : Finset (Σ s : S.Srt, Vinfinite S s)}
    (hAB : Disjoint A B) : SmallOverlap n ![A, B] := by
  classical
  intro i j hij D hDi hDj
  have hD : D ⊆ A ∩ B := by
    fin_cases i <;> fin_cases j <;> simp only [ne_eq, not_true_eq_false] at hij <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one] at hDi hDj <;>
      exact Finset.subset_inter (by assumption) (by assumption)
  rw [Finset.disjoint_iff_inter_eq_empty.mp hAB, Finset.subset_empty] at hD
  simpa [hD] using hn

variable [Countable S.Srt] [Countable S.Rel]

variable (n) in
/-- The σ-algebra of an observation `ζ` of the latent array, on the coupling space. -/
private noncomputable abbrev obsAlg {Z : Type*} [MeasurableSpace Z]
    (ζ : RankLatentSpace S n → Z) :
    MeasurableSpace (RelStructure S (Vinfinite S) × RankLatentSpace S n) :=
  MeasurableSpace.comap (ζ ∘ Prod.snd) inferInstance

namespace RankRepresentation

variable (C : M.RankRepresentation n)

/-- **The finite-cylinder identity.** For an admissible representation at positive rank, disjoint
finite supports `A` and `B`, a cylinder `U` of the induced structure on `A`, a cylinder `V` of the
induced structure on `B`, and a whole-latent event `L`: conditionally on the observation
`ζ ∘ Prod.snd` of the latent array, provided `ζ` reads at least the local latent window at `A`,
the probability of `U ∩ (V ∩ L)` is the product of the probabilities of `U` and of `V ∩ L`. -/
theorem condExp_inter_eq_mul_of_disjoint (hn : 0 < n) (hC : C.Admissible)
    {A B : Finset (Σ s : S.Srt, Vinfinite S s)} (hAB : Disjoint A B)
    {U : Set (InducedSpace (S := S) A)} (hU : MeasurableSet U)
    {V : Set (InducedSpace (S := S) B)} (hV : MeasurableSet V)
    {L : Set (RelStructure S (Vinfinite S) × RankLatentSpace S n)}
    (hL : MeasurableSet[MeasurableSpace.comap
      (Prod.snd : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) inferInstance] L)
    {Z : Type*} [MeasurableSpace Z] {ζ : RankLatentSpace S n → Z} (hζ : Measurable ζ)
    (hζA : MeasurableSpace.comap (localLatents A n) inferInstance ≤
      MeasurableSpace.comap ζ inferInstance) :
    C.P⟦(inducedMap A ∘ Prod.fst) ⁻¹' U ∩ ((inducedMap B ∘ Prod.fst) ⁻¹' V ∩ L) |
        MeasurableSpace.comap (ζ ∘ Prod.snd) inferInstance⟧
      =ᵐ[C.P]
    C.P⟦(inducedMap A ∘ Prod.fst) ⁻¹' U | MeasurableSpace.comap (ζ ∘ Prod.snd) inferInstance⟧ *
      C.P⟦(inducedMap B ∘ Prod.fst) ⁻¹' V ∩ L |
        MeasurableSpace.comap (ζ ∘ Prod.snd) inferInstance⟧ := by
  classical
  haveI := C.isProbabilityMeasure_P
  have hmΞ : latentAlg S n ≤ (inferInstance :
      MeasurableSpace (RelStructure S (Vinfinite S) × RankLatentSpace S n)) :=
    measurable_snd.comap_le
  have hm₀Ξ : obsAlg n ζ ≤ latentAlg S n := by
    show MeasurableSpace.comap (ζ ∘ Prod.snd) inferInstance ≤ _
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hζ.comap_le
  have hm₀ : localAlg n A ≤ obsAlg n ζ := by
    show MeasurableSpace.comap (localLatents A n ∘ Prod.snd) inferInstance ≤
      MeasurableSpace.comap (ζ ∘ Prod.snd) inferInstance
    rw [← MeasurableSpace.comap_comp, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hζA
  have hm₀' : obsAlg n ζ ≤ (inferInstance :
      MeasurableSpace (RelStructure S (Vinfinite S) × RankLatentSpace S n)) :=
    hm₀Ξ.trans hmΞ
  set FA : Set (RelStructure S (Vinfinite S) × RankLatentSpace S n) :=
    (inducedMap A ∘ Prod.fst) ⁻¹' U with hFAdef
  set FB : Set (RelStructure S (Vinfinite S) × RankLatentSpace S n) :=
    (inducedMap B ∘ Prod.fst) ⁻¹' V with hFBdef
  have hFA : MeasurableSet FA := ((measurable_inducedMap A).comp measurable_fst) hU
  have hFB : MeasurableSet FB := ((measurable_inducedMap B).comp measurable_fst) hV
  have hLm : MeasurableSet L := hmΞ _ hL
  -- admissibility on the disjoint pair
  have hprod : C.P⟦FA ∩ FB | latentAlg S n⟧ =ᵐ[C.P]
      C.P⟦FA | latentAlg S n⟧ * C.P⟦FB | latentAlg S n⟧ := by
    have hpair := hC 2 ![A, B] (smallOverlap_pair_of_disjoint hn hAB)
    rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul _ _
      (fun i => (measurable_inducedMap _).comp measurable_fst)] at hpair
    have := hpair Finset.univ
      (sets := Fin.cons (α := fun i => Set (InducedSpace (S := S) (![A, B] i))) U
        (Fin.cons V finZeroElim))
      (by intro i _; fin_cases i <;> [exact hU; exact hV])
    rw [Fin.prod_univ_two] at this
    have hset : FA ∩ FB = ⋂ i ∈ (Finset.univ : Finset (Fin 2)),
        (inducedMap (![A, B] i) ∘ Prod.fst) ⁻¹'
          Fin.cons (α := fun i => Set (InducedSpace (S := S) (![A, B] i))) U
            (Fin.cons V finZeroElim) i := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_univ, Fin.forall_fin_two,
        true_implies]
      exact Iff.rfl
    rw [hset]
    exact this
  -- locality of the `A`-cylinder
  have hloc : C.P⟦FA | latentAlg S n⟧ =ᵐ[C.P] C.P⟦FA | localAlg n A⟧ :=
    C.condExp_fixing_eq_local A ((measurable_inducedMap_fixingAlgebra A) hU)
  have hφm : StronglyMeasurable[obsAlg n ζ] (C.P⟦FA | localAlg n A⟧) :=
    stronglyMeasurable_condExp.mono hm₀
  have hφbd : ∀ᵐ p ∂C.P, ‖(C.P⟦FA | localAlg n A⟧) p‖ ≤ 1 := by
    obtain ⟨h0, h1⟩ := condExp_indicator_bounds (μ := C.P) (m := localAlg n A)
      (((measurable_localLatents A n).comp measurable_snd).comap_le) hFA
    filter_upwards [h0, h1] with p hp0 hp1
    simp only [Pi.zero_apply] at hp0
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith, hp1⟩
  have hLbd : ∀ p, norm (L.indicator (fun _ => (1 : ℝ)) p) ≤ 1 := fun p =>
    (norm_indicator_le_norm_self _ _).trans (by simp)
  have hLsm : StronglyMeasurable[latentAlg S n] (L.indicator (fun _ => (1 : ℝ))) := by
    letI : MeasurableSpace (RelStructure S (Vinfinite S) × RankLatentSpace S n) := latentAlg S n
    exact stronglyMeasurable_const.indicator hL
  -- rewrite the two intersections as products of indicators
  have hind1 : (FA ∩ (FB ∩ L)).indicator (fun _ => (1 : ℝ)) =
      L.indicator (fun _ => (1 : ℝ)) * (FA ∩ FB).indicator (fun _ => (1 : ℝ)) := by
    rw [show FA ∩ (FB ∩ L) = L ∩ (FA ∩ FB) by ext; simp only [Set.mem_inter_iff]; tauto]
    exact Set.inter_indicator_one
  have hind2 : (FB ∩ L).indicator (fun _ => (1 : ℝ)) =
      L.indicator (fun _ => (1 : ℝ)) * FB.indicator (fun _ => (1 : ℝ)) := by
    rw [Set.inter_comm]
    exact Set.inter_indicator_one
  have hint1 : Integrable
      (L.indicator (fun _ => (1 : ℝ)) * (FA ∩ FB).indicator (fun _ => (1 : ℝ))) C.P := by
    rw [← hind1]; exact (integrable_const 1).indicator (hFA.inter (hFB.inter hLm))
  have hint2 : Integrable
      (L.indicator (fun _ => (1 : ℝ)) * FB.indicator (fun _ => (1 : ℝ))) C.P := by
    rw [← hind2]; exact (integrable_const 1).indicator (hFB.inter hLm)
  -- the inner conditional expectation given the whole latent array
  have hinner : C.P⟦FA ∩ (FB ∩ L) | latentAlg S n⟧ =ᵐ[C.P]
      C.P⟦FA | localAlg n A⟧ * (L.indicator (fun _ => (1 : ℝ)) * C.P⟦FB | latentAlg S n⟧) := by
    calc C.P⟦FA ∩ (FB ∩ L) | latentAlg S n⟧
        = C.P[L.indicator (fun _ => (1 : ℝ)) * (FA ∩ FB).indicator (fun _ => (1 : ℝ)) |
            latentAlg S n] := by
          rw [hind1]
      _ =ᵐ[C.P] L.indicator (fun _ => (1 : ℝ)) * C.P⟦FA ∩ FB | latentAlg S n⟧ :=
          condExp_mul_of_stronglyMeasurable_left hLsm hint1
            ((integrable_const 1).indicator (hFA.inter hFB))
      _ =ᵐ[C.P] L.indicator (fun _ => (1 : ℝ)) *
            (C.P⟦FA | localAlg n A⟧ * C.P⟦FB | latentAlg S n⟧) := by
          filter_upwards [hprod, hloc] with p hp hq
          simp only [Pi.mul_apply] at hp hq ⊢
          rw [hp, hq]
      _ = C.P⟦FA | localAlg n A⟧ * (L.indicator (fun _ => (1 : ℝ)) * C.P⟦FB | latentAlg S n⟧) := by
          ext p; simp only [Pi.mul_apply]; ring
  -- the `B`-factor: pull the latent event back inside
  have hBfac : C.P[L.indicator (fun _ => (1 : ℝ)) * C.P⟦FB | latentAlg S n⟧ | obsAlg n ζ] =ᵐ[C.P]
      C.P⟦FB ∩ L | obsAlg n ζ⟧ := by
    have h1 : L.indicator (fun _ => (1 : ℝ)) * C.P⟦FB | latentAlg S n⟧ =ᵐ[C.P]
        C.P[L.indicator (fun _ => (1 : ℝ)) * FB.indicator (fun _ => (1 : ℝ)) | latentAlg S n] :=
      (condExp_mul_of_stronglyMeasurable_left hLsm hint2
        ((integrable_const 1).indicator hFB)).symm
    calc C.P[L.indicator (fun _ => (1 : ℝ)) * C.P⟦FB | latentAlg S n⟧ | obsAlg n ζ]
        =ᵐ[C.P] C.P[C.P[L.indicator (fun _ => (1 : ℝ)) * FB.indicator (fun _ => (1 : ℝ)) |
            latentAlg S n] | obsAlg n ζ] :=
          condExp_congr_ae h1
      _ =ᵐ[C.P] C.P[L.indicator (fun _ => (1 : ℝ)) * FB.indicator (fun _ => (1 : ℝ)) |
            obsAlg n ζ] :=
          condExp_condExp_of_le hm₀Ξ hmΞ
      _ = C.P⟦FB ∩ L | obsAlg n ζ⟧ := by rw [hind2]
  -- the `A`-factor: the local conditional probability is already `ζ`-measurable
  have hAfac : C.P⟦FA | localAlg n A⟧ =ᵐ[C.P] C.P⟦FA | obsAlg n ζ⟧ := by
    calc C.P⟦FA | localAlg n A⟧
        = C.P[C.P⟦FA | localAlg n A⟧ | obsAlg n ζ] :=
          (condExp_of_stronglyMeasurable hm₀' hφm integrable_condExp).symm
      _ =ᵐ[C.P] C.P[C.P⟦FA | latentAlg S n⟧ | obsAlg n ζ] := condExp_congr_ae hloc.symm
      _ =ᵐ[C.P] C.P⟦FA | obsAlg n ζ⟧ := condExp_condExp_of_le hm₀Ξ hmΞ
  -- assemble through the tower property
  have hint3 : Integrable (L.indicator (fun _ => (1 : ℝ)) * C.P⟦FB | latentAlg S n⟧) C.P :=
    integrable_condExp.bdd_mul (c := 1) (aestronglyMeasurable_const.indicator hLm)
      (Filter.Eventually.of_forall hLbd)
  calc C.P⟦FA ∩ (FB ∩ L) | obsAlg n ζ⟧
      =ᵐ[C.P] C.P[C.P⟦FA ∩ (FB ∩ L) | latentAlg S n⟧ | obsAlg n ζ] :=
        (condExp_condExp_of_le hm₀Ξ hmΞ).symm
    _ =ᵐ[C.P] C.P[C.P⟦FA | localAlg n A⟧ *
          (L.indicator (fun _ => (1 : ℝ)) * C.P⟦FB | latentAlg S n⟧) | obsAlg n ζ] :=
        condExp_congr_ae hinner
    _ =ᵐ[C.P] C.P⟦FA | localAlg n A⟧ *
          C.P[L.indicator (fun _ => (1 : ℝ)) * C.P⟦FB | latentAlg S n⟧ | obsAlg n ζ] :=
        condExp_mul_of_stronglyMeasurable_left hφm
          (hint3.bdd_mul (c := 1) (hφm.mono hm₀').aestronglyMeasurable hφbd) hint3
    _ =ᵐ[C.P] C.P⟦FA | obsAlg n ζ⟧ * C.P⟦FB ∩ L | obsAlg n ζ⟧ := by
        filter_upwards [hAfac, hBfac] with p hp hq
        simp only [Pi.mul_apply] at hp hq ⊢
        rw [hp, hq]

end RankRepresentation

/-! ### From cylinders to the full observations -/

open scoped Classical in
omit M [Countable S.Srt] [Countable S.Rel] in
/-- Pulling a measurable cylinder of the structure space back along a restriction gives a
cylinder of the induced structure on the image of the cylinder's supports. -/
private theorem restrict_preimage_cylinder (e : ∀ s, Vinfinite S s ↪ Vinfinite S s)
    (t : Finset (RelCoord S (Vinfinite S))) (T : Set (∀ _ : t, Bool)) :
    ∃ (A' : Finset (Σ s : S.Srt, Vinfinite S s))
      (U : Set (InducedSpace (S := S) (supportImage e A'))),
      (MeasurableSet T → MeasurableSet U) ∧
      RelStructure.restrict e ⁻¹' cylinder t T = inducedMap (supportImage e A') ⁻¹' U := by
  refine ⟨t.biUnion fun c => c.support, ?_, ?_, ?_⟩
  · have hsub : ∀ c : t, (RelCoord.map (fun s => ⇑(e s)) c.1).support ⊆
        supportImage e (t.biUnion fun c => c.support) := by
      intro c v hv
      rw [← supportImage_support, mem_supportImage_iff] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      exact (mem_supportImage_iff _ _ _).mpr
        ⟨w, Finset.mem_biUnion.mpr ⟨c.1, c.2, hw⟩, rfl⟩
    exact (fun u : InducedSpace (S := S) (supportImage e (t.biUnion fun c => c.support)) =>
      fun c : t => u ⟨RelCoord.map (fun s => ⇑(e s)) c.1, hsub c⟩) ⁻¹' T
  · intro hT
    exact (measurable_pi_lambda _ fun _ => measurable_pi_apply _) hT
  · ext X
    simp only [Set.mem_preimage, mem_cylinder]
    exact Iff.rfl

omit M [Countable S.Srt] [Countable S.Rel] in
/-- The local latents at the image of `A'` are read off the restriction along `e`. -/
private theorem comap_localLatents_supportImage_le (e : ∀ s, Vinfinite S s ↪ Vinfinite S s)
    (A' : Finset (Σ s : S.Srt, Vinfinite S s)) (n : ℕ) :
    MeasurableSpace.comap (localLatents (supportImage e A') n) inferInstance ≤
      MeasurableSpace.comap (latentRestrictOver e n) inferInstance := by
  classical
  have hfac : localLatents (supportImage e A') n =
      (⇑(localLatentSpaceCongr e A' n).symm ∘ localLatentsOver A' n) ∘
        latentRestrictOver e n := by
    rw [Function.comp_assoc, localLatentsOver_latentRestrictOver, ← Function.comp_assoc,
      MeasurableEquiv.symm_comp_self, Function.id_comp]
    rfl
  rw [hfac, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono
    ((localLatentSpaceCongr e A' n).symm.measurable.comp
      (measurable_localLatentsOver A' n)).comap_le

omit M [Countable S.Srt] [Countable S.Rel] in
/-- Images of supports under embeddings with disjoint ranges are disjoint. -/
private theorem disjoint_supportImage {e₀ e₁ : ∀ s, Vinfinite S s ↪ Vinfinite S s}
    (hdisj : ∀ s x y, e₀ s x ≠ e₁ s y) (A B : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Disjoint (supportImage e₀ A) (supportImage e₁ B) := by
  rw [Finset.disjoint_left]
  intro v hv₀ hv₁
  obtain ⟨w₀, -, rfl⟩ := (mem_supportImage_iff _ _ _).mp hv₀
  obtain ⟨w₁, -, h⟩ := (mem_supportImage_iff _ _ _).mp hv₁
  obtain ⟨s₀, x₀⟩ := w₀
  obtain ⟨s₁, x₁⟩ := w₁
  simp only [Sigma.map, id, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  exact hdisj _ _ _ (eq_of_heq h).symm

namespace RankRepresentation

variable (C : M.RankRepresentation n)

/-- **Screening of a restriction by a disjoint restriction and the whole latent array.** For an
admissible representation at positive rank and two sortwise self-embeddings `e₀`, `e₁` of the
carrier with disjoint ranges, the restriction of the structure along `e₀` is conditionally
independent of the pair (restriction along `e₁`, whole latent array), given the restriction of
the latent array along `e₀`. -/
theorem condIndepFun_restrict_of_disjoint (hn : 0 < n) (hC : C.Admissible)
    (e₀ e₁ : ∀ s, Vinfinite S s ↪ Vinfinite S s) (hdisj : ∀ s x y, e₀ s x ≠ e₁ s y) :
    haveI := C.isProbabilityMeasure_P
    CondIndepFun (MeasurableSpace.comap (latentRestrictOver e₀ n ∘ Prod.snd) inferInstance)
      ((measurable_latentRestrictOver e₀ n).comp measurable_snd).comap_le
      (RelStructure.restrict e₀ ∘ Prod.fst)
      (fun p : RelStructure S (Vinfinite S) × RankLatentSpace S n =>
        (RelStructure.restrict e₁ p.1, p.2)) C.P := by
  classical
  haveI := C.isProbabilityMeasure_P
  have hf : Measurable (RelStructure.restrict e₀ ∘
      (Prod.fst : RelStructure S (Vinfinite S) × RankLatentSpace S n → _)) :=
    (measurable_restrict _).comp measurable_fst
  have hg : Measurable (fun p : RelStructure S (Vinfinite S) × RankLatentSpace S n =>
      (RelStructure.restrict e₁ p.1, p.2)) :=
    ((measurable_restrict _).comp measurable_fst).prodMk measurable_snd
  have hspan : IsCountablySpanning
      (measurableCylinders fun _ : RelCoord S (Vinfinite S) => Bool) :=
    ⟨fun _ => Set.univ, fun _ => univ_mem_measurableCylinders _, Set.iUnion_const _⟩
  have hgen1 : MeasurableSpace.comap (RelStructure.restrict e₀ ∘
      (Prod.fst : RelStructure S (Vinfinite S) × RankLatentSpace S n → _)) inferInstance =
      MeasurableSpace.generateFrom (Set.preimage (RelStructure.restrict e₀ ∘ Prod.fst) ''
        measurableCylinders fun _ : RelCoord S (Vinfinite S) => Bool) := by
    rw [← MeasurableSpace.comap_generateFrom, generateFrom_measurableCylinders]
  have hgen2 : MeasurableSpace.comap (fun p : RelStructure S (Vinfinite S) × RankLatentSpace S n =>
      (RelStructure.restrict e₁ p.1, p.2)) inferInstance =
      MeasurableSpace.generateFrom (Set.preimage
        (fun p : RelStructure S (Vinfinite S) × RankLatentSpace S n =>
          (RelStructure.restrict e₁ p.1, p.2)) ''
        Set.image2 (· ×ˢ ·) (measurableCylinders fun _ : RelCoord S (Vinfinite S) => Bool)
          {t : Set (RankLatentSpace S n) | MeasurableSet t}) := by
    rw [← MeasurableSpace.comap_generateFrom, generateFrom_eq_prod
      generateFrom_measurableCylinders MeasurableSpace.generateFrom_measurableSet hspan
      isCountablySpanning_measurableSet]
  have hp1m : ∀ s ∈ Set.preimage (RelStructure.restrict e₀ ∘
      (Prod.fst : RelStructure S (Vinfinite S) × RankLatentSpace S n → _)) ''
        measurableCylinders (fun _ : RelCoord S (Vinfinite S) => Bool), MeasurableSet s := by
    rintro _ ⟨c, hc, rfl⟩
    exact hf (MeasurableSet.of_mem_measurableCylinders hc)
  have hp2m : ∀ s ∈ Set.preimage
      (fun p : RelStructure S (Vinfinite S) × RankLatentSpace S n =>
        (RelStructure.restrict e₁ p.1, p.2)) ''
      Set.image2 (· ×ˢ ·) (measurableCylinders fun _ : RelCoord S (Vinfinite S) => Bool)
        {t : Set (RankLatentSpace S n) | MeasurableSet t}, MeasurableSet s := by
    rintro _ ⟨_, ⟨c, hc, L, hL, rfl⟩, rfl⟩
    exact hg ((MeasurableSet.of_mem_measurableCylinders hc).prod hL)
  show CondIndep _ _ _ _ C.P
  refine CondIndepSets.condIndep hf.comap_le hg.comap_le
    (isPiSystem_measurableCylinders.comap _)
    ((isPiSystem_measurableCylinders.prod MeasurableSpace.isPiSystem_measurableSet).comap _)
    hgen1 hgen2 ((condIndepSets_iff _ _ _ _ hp1m hp2m _).mpr ?_)
  rintro _ _ ⟨c₁, hc₁, rfl⟩ ⟨_, ⟨c₂, hc₂, L, hL, rfl⟩, rfl⟩
  obtain ⟨t₁, T₁, hT₁, rfl⟩ := (mem_measurableCylinders _).mp hc₁
  obtain ⟨t₂, T₂, hT₂, rfl⟩ := (mem_measurableCylinders _).mp hc₂
  obtain ⟨A', U, hU, hAU⟩ := restrict_preimage_cylinder e₀ t₁ T₁
  obtain ⟨B', V, hV, hBV⟩ := restrict_preimage_cylinder e₁ t₂ T₂
  have h1 : (RelStructure.restrict e₀ ∘
      (Prod.fst : RelStructure S (Vinfinite S) × RankLatentSpace S n → _)) ⁻¹' cylinder t₁ T₁ =
      (inducedMap (supportImage e₀ A') ∘ Prod.fst) ⁻¹' U := by
    show Prod.fst ⁻¹' (RelStructure.restrict e₀ ⁻¹' cylinder t₁ T₁) =
      Prod.fst ⁻¹' (inducedMap (supportImage e₀ A') ⁻¹' U)
    rw [hAU]
  have h2 : (fun p : RelStructure S (Vinfinite S) × RankLatentSpace S n =>
        (RelStructure.restrict e₁ p.1, p.2)) ⁻¹' (cylinder t₂ T₂ ×ˢ L) =
      (inducedMap (supportImage e₁ B') ∘ Prod.fst) ⁻¹' V ∩ Prod.snd ⁻¹' L := by
    ext p
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff, Function.comp_apply]
    rw [← Set.mem_preimage, hBV]
    exact Iff.rfl
  rw [h1, h2]
  exact C.condExp_inter_eq_mul_of_disjoint hn hC (disjoint_supportImage hdisj A' B') (hU hT₁)
    (hV hT₂) ⟨L, hL, rfl⟩ (measurable_latentRestrictOver e₀ n)
    (comap_localLatents_supportImage_le e₀ A' n)

end RankRepresentation

/-! ### The pooled instance: purely spare screening -/

/-- **Purely spare screening.** Under an admissible representation at positive rank, in any
pooled rank extension the original structure is conditionally independent of the pair (purely
spare structure, whole pooled latent array), given the original old latents.

The spare observation is the purely spare restriction `restrictPool`, not a mixed observation;
the conditioning is exactly the σ-algebra of the original old latents. -/
theorem PooledRankExtension.condIndepFun_restrictOriginal_restrictPool {C : M.RankRepresentation n}
    (hn : 0 < n) (hC : C.Admissible) (Q : PooledRankExtension C) :
    CondIndepFun (MeasurableSpace.comap (restrictOriginalLatents S n ∘ Prod.snd) inferInstance)
      ((measurable_restrictOriginalLatents n).comp measurable_snd).comap_le
      (restrictOriginal S ∘ Prod.fst)
      (fun p : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n =>
        (restrictPool S p.1, p.2)) Q.law := by
  haveI := C.isProbabilityMeasure_P
  set ψ : ∀ s, Vinfinite S s ↪ PoolVertex S s := fun s => (poolVertexEquiv S s).symm.toEmbedding
    with hψ
  set e₀ : ∀ s, Vinfinite S s ↪ Vinfinite S s :=
    fun s => (originalVertex S s).trans (poolVertexEquiv S s).toEmbedding with he₀
  set e₁ : ∀ s, Vinfinite S s ↪ Vinfinite S s :=
    fun s => (poolVertex S s).trans (poolVertexEquiv S s).toEmbedding with he₁
  have hdisj : ∀ s x y, e₀ s x ≠ e₁ s y := fun s x y h =>
    Sum.inl_ne_inr ((poolVertexEquiv S s).injective h)
  set ψ' : ∀ s, PoolVertex S s ↪ Vinfinite S s := fun s => (poolVertexEquiv S s).toEmbedding
    with hψ'
  have hpull := (condIndepFun_comp_measurePreserving Q.measurePreserving_pooledJointEquiv
    ((measurable_latentRestrictOver e₀ n).comp measurable_snd).comap_le
    ((measurable_restrict _).comp measurable_fst)
    (show Measurable (fun p : RelStructure S (Vinfinite S) × RankLatentSpace S n =>
        (RelStructure.restrict e₁ p.1, p.2)) from
      ((measurable_restrict _).comp measurable_fst).prodMk measurable_snd)
    (C.condIndepFun_restrict_of_disjoint hn hC e₀ e₁ hdisj)).comp measurable_id
    (measurable_id.prodMap (measurable_latentRestrictOver ψ' n))
  have hcomp₀ : (fun s => ⇑(ψ s) ∘ ⇑(e₀ s)) =
      fun s => (⇑(originalVertex S s) : Vinfinite S s → PoolVertex S s) := by
    funext s x
    exact (poolVertexEquiv S s).symm_apply_apply (Sum.inl x)
  have hcomp₁ : (fun s => ⇑(ψ s) ∘ ⇑(e₁ s)) =
      fun s => (⇑(poolVertex S s) : Vinfinite S s → PoolVertex S s) := by
    funext s x
    exact (poolVertexEquiv S s).symm_apply_apply (Sum.inr x)
  have hlat : ∀ ω : PooledRankLatentSpace S n,
      latentRestrictOver ψ' n (latentRestrictOver ψ n ω) = ω := by
    intro ω
    funext A
    show ω (latentIndexEmbed ψ n (latentIndexEmbed ψ' n A)) = ω A
    congr 1
    rw [latentIndexEmbed_comp]
    refine Subtype.ext ?_
    ext v
    show v ∈ supportImage (fun s => (ψ' s).trans (ψ s)) A.1 ↔ v ∈ A.1
    rw [mem_supportImage_iff]
    have hid : ∀ w : Σ s : S.Srt, PoolVertex S s,
        Sigma.map id (fun s => ⇑((ψ' s).trans (ψ s))) w = w := by
      rintro ⟨s, x⟩
      show (⟨s, (poolVertexEquiv S s).symm (poolVertexEquiv S s x)⟩ : Σ s, PoolVertex S s) = ⟨s, x⟩
      rw [Equiv.symm_apply_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hid]
      exact hw
    · intro hv
      exact ⟨v, hv, hid v⟩
  have hf : id ∘ ((RelStructure.restrict e₀ ∘ Prod.fst) ∘ ⇑(pooledJointEquiv S n)) =
      restrictOriginal S ∘ Prod.fst := by
    rw [pooledJointEquiv_coe]
    funext p c
    show p.1 (RelCoord.map (fun s => (ψ s : Vinfinite S s → PoolVertex S s))
      (RelCoord.map (fun s => (e₀ s : Vinfinite S s → Vinfinite S s)) c)) =
      p.1 (RelCoord.map (fun s => (originalVertex S s : Vinfinite S s → PoolVertex S s)) c)
    rw [← RelCoord.map_comp, hcomp₀]
  have hg : Prod.map id (latentRestrictOver ψ' n) ∘
      ((fun p : RelStructure S (Vinfinite S) × RankLatentSpace S n =>
        (RelStructure.restrict e₁ p.1, p.2)) ∘ ⇑(pooledJointEquiv S n)) =
      fun p : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n =>
        (restrictPool S p.1, p.2) := by
    rw [pooledJointEquiv_coe]
    funext p
    refine Prod.ext ?_ (hlat p.2)
    funext c
    show p.1 (RelCoord.map (fun s => (ψ s : Vinfinite S s → PoolVertex S s))
      (RelCoord.map (fun s => (e₁ s : Vinfinite S s → Vinfinite S s)) c)) =
      p.1 (RelCoord.map (fun s => (poolVertex S s : Vinfinite S s → PoolVertex S s)) c)
    rw [← RelCoord.map_comp, hcomp₁]
  rw [hf, hg] at hpull
  refine hpull.congr_cond ?_ _
  rw [MeasurableSpace.comap_comp]
  congr 1
  rw [pooledJointEquiv_coe]
  funext p
  show latentRestrictOver e₀ n (latentRestrictOver ψ n p.2) = restrictOriginalLatents S n p.2
  rw [← Function.comp_apply (f := latentRestrictOver e₀ n), latentRestrictOver_comp]
  show latentRestrictOver (fun s => (e₀ s).trans (ψ s)) n p.2 =
    latentRestrictOver (fun s => originalVertex S s) n p.2
  congr 1
  funext s
  ext x
  exact (poolVertexEquiv S s).symm_apply_apply (Sum.inl x)

end InfiniteRelExchangeableLaw

end RelSignature
