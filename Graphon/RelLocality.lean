/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRankRepresentation
import Graphon.ForMathlib.CondExpComap

/-!
# Conditional-probability locality (R4 converse, #107)

For any rank-`n` representation `C`, finite support `A`, and event `E` of the fixing algebra at
`A`, the conditional probability of `E` given the whole latent array is almost surely the
conditional probability given the local latents at `A`:

`C.P⟦fst ⁻¹' E | σ(snd)⟧ =ᵐ C.P⟦fst ⁻¹' E | σ(localLatents A n ∘ snd)⟧`.

There is no restriction on `A.card`, no admissibility hypothesis, and no new field; the
statement localizes a conditional probability, not the event. Neither side conditions on any
auxiliary base.

The proof: the whole-latent conditional probability is a function of the latent array. By joint
invariance of the coupling and invariance of the event under relabelings fixing `A`, that
function is almost surely invariant under the corresponding latent relabelings. Each rational
superlevel set is therefore an almost surely invariant event of the source, hence has a local
representative by the source localization theorem; the countable family of representatives
assembles into a local measurable function almost surely equal to the conditional probability.
The tower property finishes.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

/-- Reading the supremum of the rationals below a nonnegative real recovers it. -/
theorem iSup_rat_lt_eq {x : ℝ} (hx : 0 ≤ x) :
    (⨆ q : ℚ, if (q : ℝ) < x then (q : ℝ) else 0) = x := by
  have hbdd : BddAbove (Set.range fun q : ℚ => if (q : ℝ) < x then (q : ℝ) else 0) := by
    refine ⟨x, ?_⟩
    rintro _ ⟨q, rfl⟩
    show (if (q : ℝ) < x then (q : ℝ) else 0) ≤ x
    split_ifs with h
    · exact h.le
    · exact hx
  refine le_antisymm (ciSup_le fun q => ?_) (le_of_forall_lt fun y hy => ?_)
  · show (if (q : ℝ) < x then (q : ℝ) else 0) ≤ x
    split_ifs with h
    · exact h.le
    · exact hx
  · obtain ⟨q, hyq, hqx⟩ := exists_rat_btwn hy
    refine lt_of_lt_of_le hyq (le_ciSup_of_le hbdd q ?_)
    show (q : ℝ) ≤ if (q : ℝ) < x then (q : ℝ) else 0
    rw [if_pos hqx]

namespace InfiniteRelExchangeableLaw

universe u

variable {S : RelSignature.{u}} {M : InfiniteRelExchangeableLaw S} {n : ℕ}
  [Countable S.Srt] [Countable S.Rel]

omit [Countable S.Rel] in
/-- The local latent σ-algebra at `A` lies inside the whole latent σ-algebra. -/
theorem comap_localLatents_snd_le (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    MeasurableSpace.comap (localLatents A n ∘ Prod.snd) inferInstance ≤
      MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) inferInstance := by
  rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_localLatents A n).comap_le

omit [Countable S.Srt] [Countable S.Rel] in
/-- The latent σ-algebra is stable under a latent relabeling. -/
theorem comap_rankLatentRelabel_comp_snd (σ : FinSuppPerm S) :
    MeasurableSpace.comap (rankLatentRelabel σ n ∘ Prod.snd) inferInstance =
      MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) inferInstance := by
  refine le_antisymm ?_ ?_
  · rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (rankLatentRelabel σ n).measurable.comap_le
  · have h : (Prod.snd : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) =
        (rankLatentRelabel σ n).symm ∘ (rankLatentRelabel σ n ∘ Prod.snd) := by
      funext p
      simp
    conv_lhs => rw [h, ← MeasurableSpace.comap_comp]
    refine MeasurableSpace.comap_mono ?_
    exact (rankLatentRelabel σ n).symm.measurable.comap_le

variable (S n) in
/-- The whole latent σ-algebra on the coupling space. -/
@[implicit_reducible]
noncomputable def latentAlg :
    MeasurableSpace (RelStructure S (Vinfinite S) × RankLatentSpace S n) :=
  MeasurableSpace.comap Prod.snd inferInstance

variable (n) in
/-- The local latent σ-algebra at `A` on the coupling space. -/
@[implicit_reducible]
noncomputable def localAlg (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    MeasurableSpace (RelStructure S (Vinfinite S) × RankLatentSpace S n) :=
  MeasurableSpace.comap (localLatents A n ∘ Prod.snd) inferInstance

namespace RankRepresentation

variable (C : M.RankRepresentation n)

/-- **Conditional-probability locality.** -/
theorem condExp_fixing_eq_local (A : Finset (Σ s : S.Srt, Vinfinite S s))
    {E : Set (RelStructure S (Vinfinite S))} (hE : MeasurableSet[RelStructure.fixingAlgebra A] E) :
    C.P⟦Prod.fst ⁻¹' E | MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) inferInstance⟧
      =ᵐ[C.P]
    C.P⟦Prod.fst ⁻¹' E | MeasurableSpace.comap (localLatents A n ∘ Prod.snd) inferInstance⟧ := by
  classical
  haveI := C.isProbabilityMeasure_P
  set μ := C.P with hμ
  have hmS_le : latentAlg S n ≤ (inferInstance :
      MeasurableSpace (RelStructure S (Vinfinite S) × RankLatentSpace S n)) :=
    measurable_snd.comap_le
  have hmL_le : localAlg n A ≤ (inferInstance :
      MeasurableSpace (RelStructure S (Vinfinite S) × RankLatentSpace S n)) :=
    ((measurable_localLatents A n).comp measurable_snd).comap_le
  have hLS : localAlg n A ≤ latentAlg S n := comap_localLatents_snd_le A
  set F : Set (RelStructure S (Vinfinite S) × RankLatentSpace S n) := Prod.fst ⁻¹' E with hF
  have hFm : MeasurableSet F := measurable_fst hE.1
  set g : RelStructure S (Vinfinite S) × RankLatentSpace S n → ℝ :=
    μ⟦F | latentAlg S n⟧ with hg
  have hgsm : StronglyMeasurable[latentAlg S n] g := stronglyMeasurable_condExp
  have hgm : Measurable[latentAlg S n] g := hgsm.measurable
  have hgint : Integrable g μ := integrable_condExp
  obtain ⟨hg0, hg1⟩ := condExp_indicator_bounds (μ := μ) hmS_le hFm
  -- invariance of `g` under the joint action of a relabeling fixing `A`
  have hginv : ∀ σ : FinSuppPerm S, SortwiseFixing A σ.1 →
      g ∘ Prod.map (RelStructure.relabel σ.1) (rankLatentRelabel σ n) =ᵐ[μ] g := by
    intro σ hσ
    set T := Prod.map (RelStructure.relabel σ.1) (rankLatentRelabel σ n) with hT
    have hTmp : MeasurePreserving T μ μ :=
      ⟨(measurable_relabel σ.1).prodMap (rankLatentRelabel σ n).measurable, C.invariant σ⟩
    have h := condExp_comp_measurePreserving hTmp hmS_le ((integrable_const (1 : ℝ)).indicator hFm)
    have hpre : T ⁻¹' F = F := by
      show Prod.fst ⁻¹' (RelStructure.relabel σ.1 ⁻¹' E) = Prod.fst ⁻¹' E
      rw [hE.2 σ.1 hσ]
    have hFT : (F.indicator fun _ => (1 : ℝ)) ∘ T = F.indicator fun _ => (1 : ℝ) := by
      funext p
      rw [Function.comp_apply, ← Set.indicator_comp_right, hpre]
      rfl
    have hcomap : (latentAlg S n).comap T = latentAlg S n := by
      show (MeasurableSpace.comap Prod.snd inferInstance).comap T = _
      rw [MeasurableSpace.comap_comp]
      exact comap_rankLatentRelabel_comp_snd σ
    rw [hFT, hcomap] at h
    exact h
  -- the rational superlevel sets of `g` are latent events, almost surely invariant on the source
  have hsuper : ∀ q : ℚ, ∃ D : Set (RankLatentSpace S n), MeasurableSet D ∧
      {p | (q : ℝ) < g p} = Prod.snd ⁻¹' D := by
    intro q
    have : MeasurableSet[latentAlg S n] {p | (q : ℝ) < g p} :=
      measurableSet_lt measurable_const hgm
    obtain ⟨D, hD, hDeq⟩ := this
    exact ⟨D, hD, hDeq.symm⟩
  choose D hDm hDeq using hsuper
  have hsnd : MeasurePreserving Prod.snd μ (rankLatentSource S n) := ⟨measurable_snd, C.map_snd⟩
  have hDinv : ∀ q : ℚ, ∀ σ : FinSuppPerm S, SortwiseFixing A σ.1 →
      rankLatentRelabel σ n ⁻¹' D q =ᵐ[rankLatentSource S n] D q := by
    intro q σ hσ
    have h1 : Prod.snd ⁻¹' (rankLatentRelabel σ n ⁻¹' D q) =ᵐ[μ] Prod.snd ⁻¹' D q := by
      have hset : Prod.snd ⁻¹' (rankLatentRelabel σ n ⁻¹' D q) =
          Prod.map (RelStructure.relabel σ.1) (rankLatentRelabel σ n) ⁻¹' {p | (q : ℝ) < g p} := by
        rw [hDeq q]; rfl
      rw [hset, ← hDeq q]
      refine Filter.eventuallyEq_set.mpr ?_
      filter_upwards [hginv σ hσ] with p hp
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Function.comp_apply] at hp ⊢
      rw [hp]
    rw [← C.map_snd]
    exact ae_eq_map_of_preimage_ae_eq measurable_snd ((rankLatentRelabel σ n).measurable (hDm q))
      (hDm q) h1
  -- local representatives, one per rational threshold
  have hloc : ∀ q : ℚ, ∃ U : Set (LocalLatentSpace A n), MeasurableSet U ∧
      localLatents A n ⁻¹' U =ᵐ[rankLatentSource S n] D q := by
    intro q
    obtain ⟨D', ⟨U, hU, rfl⟩, hD'⟩ :=
      rankLatentSource_exists_local_ae_eq_of_ae_invariant A (hDm q) (hDinv q)
    exact ⟨U, hU, hD'⟩
  choose U hUm hU using hloc
  -- the assembled local function
  set Ψ : RelStructure S (Vinfinite S) × RankLatentSpace S n → ℝ := fun p =>
    ⨆ q : ℚ, ((localLatents A n ∘ Prod.snd) ⁻¹' U q).indicator (fun _ => (q : ℝ)) p with hΨ
  have hΨm : Measurable[localAlg n A] Ψ := by
    letI : MeasurableSpace (RelStructure S (Vinfinite S) × RankLatentSpace S n) := localAlg n A
    refine Measurable.iSup fun q => ?_
    exact measurable_const.indicator ⟨U q, hUm q, rfl⟩
  -- `Ψ` agrees with `g` almost surely
  have hae : ∀ᵐ p ∂μ, ∀ q : ℚ, p ∈ (localLatents A n ∘ Prod.snd) ⁻¹' U q ↔ (q : ℝ) < g p := by
    rw [ae_all_iff]
    intro q
    have h := hsnd.quasiMeasurePreserving.preimage_ae_eq (hU q)
    rw [← hDeq q] at h
    exact Filter.eventuallyEq_set.mp h
  have hΨg : Ψ =ᵐ[μ] g := by
    filter_upwards [hae, hg0] with p hp hp0
    have : Ψ p = ⨆ q : ℚ, if (q : ℝ) < g p then (q : ℝ) else 0 := by
      simp only [hΨ]
      congr 1
      funext q
      by_cases hq : p ∈ (localLatents A n ∘ Prod.snd) ⁻¹' U q
      · rw [Set.indicator_of_mem hq, if_pos ((hp q).mp hq)]
      · rw [Set.indicator_of_notMem hq, if_neg (fun h => hq ((hp q).mpr h))]
    rw [this, iSup_rat_lt_eq hp0]
  -- the tower property
  have htower : μ⟦F | localAlg n A⟧ =ᵐ[μ] μ[g | localAlg n A] :=
    (condExp_condExp_of_le hLS hmS_le).symm
  have hΨint : Integrable Ψ μ := hgint.congr hΨg.symm
  have h2 : μ[g | localAlg n A] =ᵐ[μ] Ψ :=
    (condExp_congr_ae hΨg.symm).trans
      (Filter.EventuallyEq.of_eq
        (condExp_of_stronglyMeasurable hmL_le hΨm.stronglyMeasurable hΨint))
  exact (htower.trans (h2.trans hΨg)).symm

end RankRepresentation

end InfiniteRelExchangeableLaw

end RelSignature
