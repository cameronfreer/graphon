/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelLowerFactor
import Graphon.RelSingletonPeel
import Graphon.ForMathlib.CondExpComap
import Graphon.ForMathlib.CondExpRepresentable
import Graphon.ForMathlib.CondIndepRefine
import Graphon.ForMathlib.CondIndepSup

/-!
# The rank-one conditioning ladder (R4 converse piece 3, #107)

Under the rank-one coupling clauses, the singleton blocks — composed with the structure
projection — are **mutually** conditionally independent given the full latent σ-algebra
`comap Prod.snd`. This is the support-free core of the `screening` field; the per-support
statement is a later specialization.

## The ladder

The conditioning algebra climbs and then descends, each rung by a merged tool:

1. the singleton peel (#173) under the law, pulled to the coupling along `Prod.fst` (#175) —
   conditioning `invariantAlgebra.comap fst`;
2. **down** to `comap (lowerFactorMap 1 ∘ fst)` by the representable-conditioning transfer
   (#163), whose hypothesis is the eventwise generation of the rank-one factor (#157) pulled
   along `fst`;
3. **up** to the join with the latent algebra by the independent-refinement theorem (#174),
   whose hypothesis is the coupling's conditional-independence clause (#161/#177) joined
   freely with the conditioning (#176);
4. **down** to the latent algebra alone by #163 again, the representability of the join
   supplied by the resolution identity and `eventuallyMeasurableSet_sup` (#176).

Every conditioning move is modulo the coupling measure. No identification of the latent
σ-algebra with the invariant algebra is asserted anywhere — the available statements are
eventwise, and that is all the ladder uses.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

universe u

open scoped Classical in
/-- The singleton block at `v`, read through the structure coordinate of the rank-one
coupling space. Named so the family is fully typed at every use site; mentions no basis and
no law, so it lives at the signature level. -/
def singletonBlockRead (S : RelSignature.{u}) (v : Σ s : S.Srt, Vinfinite S s) :
    RelStructure S (Vinfinite S) × RankLatentSpace S 1 →
      BlockSpace ({v} : Finset (Σ s : S.Srt, Vinfinite S s)) :=
  blockMap ({v} : Finset (Σ s : S.Srt, Vinfinite S s)) ∘ Prod.fst

open scoped Classical in
theorem measurable_singletonBlockRead {S : RelSignature.{u}} [Countable S.Rel]
    (v : Σ s : S.Srt, Vinfinite S s) : Measurable (singletonBlockRead S v) :=
  (measurable_blockMap _).comp measurable_fst

open scoped Classical in
/-- **At rank one, local latents see everything**: every latent coordinate has empty support,
hence is visible at every `A`, so conditioning on the local latents is conditioning on the
whole latent coordinate. A raw σ-algebra equality — no measure in sight. -/
theorem comap_localLatents_one_snd {S : RelSignature.{u}} [Countable S.Srt]
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    MeasurableSpace.comap (localLatents A 1 ∘ (Prod.snd : RelStructure S (Vinfinite S) ×
        RankLatentSpace S 1 → RankLatentSpace S 1)) inferInstance =
      MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
        RankLatentSpace S 1 → RankLatentSpace S 1) inferInstance := by
  classical
  have hsub : ∀ Bi : RankLatentIndex S 1, Bi.1 ⊆ A := fun Bi => by
    rw [Finset.card_eq_zero.mp (Nat.lt_one_iff.mp Bi.2)]
    exact Finset.empty_subset A
  have hρmeas : Measurable (fun (ω : LocalLatentSpace A 1) Bi => ω ⟨Bi, hsub Bi⟩ :
      LocalLatentSpace A 1 → RankLatentSpace S 1) :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  refine le_antisymm ?_ ?_
  · rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_iff_comap_le.mp (measurable_localLatents A 1))
  · calc MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
          RankLatentSpace S 1 → RankLatentSpace S 1) inferInstance
        = MeasurableSpace.comap ((fun (ω : LocalLatentSpace A 1) Bi => ω ⟨Bi, hsub Bi⟩) ∘
            (localLatents A 1 ∘ Prod.snd)) inferInstance := rfl
      _ = MeasurableSpace.comap (localLatents A 1 ∘ Prod.snd)
            (MeasurableSpace.comap (fun (ω : LocalLatentSpace A 1) Bi => ω ⟨Bi, hsub Bi⟩)
              inferInstance) := (MeasurableSpace.comap_comp).symm
      _ ≤ MeasurableSpace.comap (localLatents A 1 ∘ Prod.snd) inferInstance :=
            MeasurableSpace.comap_mono (measurable_iff_comap_le.mp hρmeas)

/-- Conditional independence is insensitive to replacing the conditioning σ-algebra by an equal
one; the inclusion proofs move by proof irrelevance. -/
private theorem condIndepFun_congr_cond {Ω β γ : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    [MeasurableSpace β] [MeasurableSpace γ] {f : Ω → β} {g : Ω → γ}
    {m₁ m₂ : MeasurableSpace Ω} (h12 : m₁ = m₂) {h1 : m₁ ≤ mΩ} (h2 : m₂ ≤ mΩ)
    (h : CondIndepFun m₁ h1 f g μ) : CondIndepFun m₂ h2 f g μ := by
  subst h12
  exact h

open scoped Classical in
/-- **Per-support screening at rank one.** Given the ladder's conclusion — mutual conditional
independence of the singleton blocks given the full latent σ-algebra — and the nullary
recovery, the rank-one block at each support is conditionally independent of the rank-truncated
remainder given the latents visible at that support. This is the `screening` field of a
rank-one `RankRepresentation`, and it mentions no basis: everything it needs arrives through
its hypotheses. -/
theorem condIndepFun_blockMap_restObservation_one {S : RelSignature.{u}}
    [Countable S.Srt] [Countable S.Rel]
    {P : Measure (RelStructure S (Vinfinite S) × RankLatentSpace S 1)} [IsProbabilityMeasure P]
    (hladder : iCondIndepFun (MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
        RankLatentSpace S 1 → RankLatentSpace S 1) inferInstance)
      measurable_snd.comap_le (singletonBlockRead S) P)
    {g₀ : LocalLatentSpace (∅ : Finset (Σ s : S.Srt, Vinfinite S s)) 1 →
      BlockSpace (∅ : Finset (Σ s : S.Srt, Vinfinite S s))} (hg₀ : Measurable g₀)
    (hrec : blockMap (∅ : Finset (Σ s : S.Srt, Vinfinite S s)) ∘ Prod.fst
      =ᵐ[P] g₀ ∘ localLatents ∅ 1 ∘ Prod.snd)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) (hA : A.card = 1) :
    CondIndepFun (MeasurableSpace.comap (localLatents A 1 ∘ Prod.snd) inferInstance)
      ((measurable_localLatents A 1).comp measurable_snd).comap_le
      (blockMap A ∘ Prod.fst) (restObservation 1 A) P := by
  classical
  obtain ⟨v₀, rfl⟩ := Finset.card_eq_one.mp hA
  -- one versus the rest, at the σ-algebra level
  rw [iCondIndepFun_iff_iCondIndep] at hladder
  have hsplit := condIndep_iSup_of_disjoint
    (fun v => (measurable_singletonBlockRead v).comap_le) hladder
    (disjoint_compl_right (a := ({v₀} : Set (Σ s : S.Srt, Vinfinite S s))))
  have h1 := condIndep_of_condIndep_of_le_left hsplit
    (le_iSup₂ (f := fun (v : Σ s : S.Srt, Vinfinite S s)
      (_ : v ∈ ({v₀} : Set (Σ s : S.Srt, Vinfinite S s))) =>
        MeasurableSpace.comap (singletonBlockRead S v) inferInstance) v₀ rfl)
  -- enlarge the right side by the conditioning
  have hcomplle : (⨆ v ∈ (({v₀} : Set (Σ s : S.Srt, Vinfinite S s))ᶜ),
      MeasurableSpace.comap (singletonBlockRead S v) inferInstance) ≤
      MeasurableSpace.pi.prod inferInstance := by
    exact iSup₂_le fun v _ => (measurable_singletonBlockRead v).comap_le
  have h2 := CondIndep.sup_right h1 (measurable_singletonBlockRead v₀).comap_le hcomplle
  -- the rerouted remainder, measurable for the enlarged right side
  set R' : RelStructure S (Vinfinite S) × RankLatentSpace S 1 →
      RestSpace 1 ({v₀} : Finset (Σ s : S.Srt, Vinfinite S s)) × RankLatentSpace S 1 :=
    fun p => (fun c => if hc : c.1.support = ∅
      then g₀ (localLatents ∅ 1 p.2) ⟨c.1, hc⟩
      else p.1 c.1, p.2) with hR'def
  have hR'measJ : Measurable[(MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
        RankLatentSpace S 1 → RankLatentSpace S 1) inferInstance ⊔
      (⨆ v ∈ (({v₀} : Set (Σ s : S.Srt, Vinfinite S s))ᶜ),
        MeasurableSpace.comap (singletonBlockRead S v) inferInstance))] R' := by
    rw [hR'def]
    letI : MeasurableSpace (RelStructure S (Vinfinite S) × RankLatentSpace S 1) := (MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
        RankLatentSpace S 1 → RankLatentSpace S 1) inferInstance ⊔
      (⨆ v ∈ (({v₀} : Set (Σ s : S.Srt, Vinfinite S s))ᶜ),
        MeasurableSpace.comap (singletonBlockRead S v) inferInstance))
    have hsndJ : Measurable (Prod.snd : RelStructure S (Vinfinite S) ×
        RankLatentSpace S 1 → RankLatentSpace S 1) :=
      Measurable.of_comap_le le_sup_left
    refine Measurable.prodMk ?_ hsndJ
    refine measurable_pi_lambda _ fun c => ?_
    by_cases hc : c.1.support = ∅
    · simp only [dif_pos hc]
      exact (measurable_pi_apply _).comp
        ((hg₀.comp (measurable_localLatents _ _)).comp hsndJ)
    · simp only [dif_neg hc]
      obtain ⟨w, hw⟩ : ∃ w, c.1.support = {w} :=
        Finset.card_eq_one.mp (Nat.le_antisymm c.2.1
          (Nat.one_le_iff_ne_zero.mpr fun h0 => hc (Finset.card_eq_zero.mp h0)))
      have hwne : w ∈ (({v₀} : Set (Σ s : S.Srt, Vinfinite S s))ᶜ) := fun h =>
        c.2.2 (by rw [hw, Set.mem_singleton_iff.mp h])
      have hread : (fun p : RelStructure S (Vinfinite S) × RankLatentSpace S 1 => p.1 c.1)
          = fun p => singletonBlockRead S w p ⟨c.1, hw⟩ := rfl
      rw [hread]
      exact (measurable_pi_apply _).comp (Measurable.of_comap_le
        (le_trans (le_iSup₂ (f := fun (v : Σ s : S.Srt, Vinfinite S s)
          (_ : v ∈ (({v₀} : Set (Σ s : S.Srt, Vinfinite S s))ᶜ)) =>
            MeasurableSpace.comap (singletonBlockRead S v) inferInstance) w hwne)
          le_sup_right))
  have hJle : (MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
        RankLatentSpace S 1 → RankLatentSpace S 1) inferInstance ⊔
      (⨆ v ∈ (({v₀} : Set (Σ s : S.Srt, Vinfinite S s))ᶜ),
        MeasurableSpace.comap (singletonBlockRead S v) inferInstance)) ≤
      (inferInstance : MeasurableSpace (RelStructure S (Vinfinite S) × RankLatentSpace S 1)) :=
    sup_le measurable_snd.comap_le hcomplle
  have hR'amb : Measurable R' := hR'measJ.mono hJle le_rfl
  -- the remainder agrees with the rerouted remainder almost everywhere
  have hae : restObservation 1 ({v₀} : Finset (Σ s : S.Srt, Vinfinite S s)) =ᵐ[P] R' := by
    filter_upwards [hrec] with p hp
    rw [hR'def]
    refine Prod.ext ?_ rfl
    funext c
    by_cases hc : c.1.support = ∅
    · simp only [restObservation, restObservationOver, dif_pos hc]
      exact congrFun hp ⟨c.1, hc⟩
    · simp only [restObservation, restObservationOver, dif_neg hc]
  -- assemble
  have h3 := condIndep_of_condIndep_of_le_right h2 (measurable_iff_comap_le.mp hR'measJ)
  have h4 := (condIndepFun_iff_condIndep _ _ (singletonBlockRead S v₀) R' P).mpr h3
  have h5 := h4.congr (measurable_singletonBlockRead v₀) hR'amb
    (measurable_singletonBlockRead v₀) (measurable_restObservation 1 _)
    Filter.EventuallyEq.rfl hae.symm
  exact condIndepFun_congr_cond (comap_localLatents_one_snd _).symm _ h5

namespace CoherentBasis

variable {S : RelSignature.{u}} {M : InfiniteRelExchangeableLaw S} (B : CoherentBasis M)

open scoped Classical in
/-- **The conditioning ladder.** Under a coupling of the law with the rank-one latents —
structure marginal the law, rank-one factor resolved by a measurable latent read, structure and
latent conditionally independent given the factor — the singleton blocks are **mutually**
conditionally independent given the full latent σ-algebra. -/
theorem iCondIndepFun_blockMap_singleton_comap_snd [Fintype S.Srt] [Countable S.Rel]
    {P : Measure (RelStructure S (Vinfinite S) × RankLatentSpace S 1)}
    [IsProbabilityMeasure P]
    (hfst : P.map Prod.fst = (M.law : Measure (RelStructure S (Vinfinite S))))
    {g : RankLatentSpace S 1 → B.LowerFactorSpace 1} (hg : Measurable g)
    (hres : B.lowerFactorMap 1 ∘ Prod.fst =ᵐ[P] g ∘ Prod.snd)
    (hci : CondIndepFun (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance)
      ((B.measurable_lowerFactorMap' 1).comp measurable_fst).comap_le Prod.fst Prod.snd P) :
    iCondIndepFun (MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
        RankLatentSpace S 1 → RankLatentSpace S 1) inferInstance)
      measurable_snd.comap_le
      (singletonBlockRead S) P := by
  classical
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  have hMP : MeasurePreserving Prod.fst P (M.law : Measure (RelStructure S (Vinfinite S))) :=
    ⟨measurable_fst, hfst⟩
  have hblockmeas : ∀ v : Σ s : S.Srt, Vinfinite S s,
      Measurable (singletonBlockRead S v) :=
    fun v => measurable_singletonBlockRead v
  -- rung 1: the peel, pulled to the coupling along `fst`
  have h1 : iCondIndepFun (RelStructure.invariantAlgebra.comap Prod.fst)
      ((MeasurableSpace.comap_mono (RelStructure.invariantAlgebra_le (S := S))).trans
        (measurable_iff_comap_le.mp hMP.measurable))
      (singletonBlockRead S) P :=
    iCondIndepFun_comp_measurePreserving hMP (RelStructure.invariantAlgebra_le (S := S))
      (fun v => measurable_blockMap _) (M.iCondIndepFun_blockMap_singleton)
  -- rung 2: down to the rank-one factor pullback, by eventwise representability
  have hFI : MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance ≤
      RelStructure.invariantAlgebra.comap
        (Prod.fst : RelStructure S (Vinfinite S) × RankLatentSpace S 1 → _) := by
    rw [← MeasurableSpace.comap_comp]
    refine MeasurableSpace.comap_mono ?_
    have hle := B.comap_lowerFactorMap_le 1
    rwa [RelStructure.lowerRankAlgebra_one] at hle
  have hrepFI : ∀ s, MeasurableSet[RelStructure.invariantAlgebra.comap
      (Prod.fst : RelStructure S (Vinfinite S) × RankLatentSpace S 1 → _)] s →
      ∃ t, MeasurableSet[MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance] t ∧
        s =ᵐ[P] t := by
    rintro s ⟨E, hE, rfl⟩
    obtain ⟨E', hE'meas, hE'ae⟩ := B.exists_comap_lowerFactorMap_one_ae_eq hE
    obtain ⟨D, hD, rfl⟩ := hE'meas
    refine ⟨(B.lowerFactorMap 1 ∘ Prod.fst) ⁻¹' D, ⟨D, hD, rfl⟩, ?_⟩
    refine Filter.eventuallyEq_set.mpr ?_
    have hpull := hMP.quasiMeasurePreserving.tendsto_ae.eventually
      (Filter.eventuallyEq_set.mp hE'ae)
    filter_upwards [hpull] with p hp
    simpa [Set.preimage_comp] using hp.symm
  have h2 : iCondIndepFun
      (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance)
      (hFI.trans ((MeasurableSpace.comap_mono (RelStructure.invariantAlgebra_le (S := S))).trans
        (measurable_iff_comap_le.mp hMP.measurable)))
      (singletonBlockRead S) P :=
    (iCondIndepFun_congr_of_ae_representable hFI _ hrepFI hblockmeas).mp h1
  -- rung 3: up to the join with the latent algebra, by independent refinement
  have hciAlg : CondIndep (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance)
      (MeasurableSpace.comap (Prod.fst : RelStructure S (Vinfinite S) ×
        RankLatentSpace S 1 → _) inferInstance)
      (MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
        RankLatentSpace S 1 → _) inferInstance)
      ((B.measurable_lowerFactorMap' 1).comp measurable_fst).comap_le P :=
    (condIndepFun_iff_condIndep _ _ _ _ _).mp hci
  have hsupBlocks : (⨆ v : Σ s : S.Srt, Vinfinite S s, MeasurableSpace.comap
      (singletonBlockRead S v) inferInstance) ≤
      MeasurableSpace.comap (Prod.fst : RelStructure S (Vinfinite S) ×
        RankLatentSpace S 1 → _) inferInstance :=
    iSup_le fun v => by
      rw [show singletonBlockRead S v
            = blockMap ({v} : Finset (Σ s : S.Srt, Vinfinite S s)) ∘ Prod.fst from rfl,
        ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (measurable_iff_comap_le.mp (measurable_blockMap _))
  have h3 : CondIndep (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance)
      (⨆ v : Σ s : S.Srt, Vinfinite S s, MeasurableSpace.comap
        (singletonBlockRead S v) inferInstance)
      (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance ⊔
        MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
          RankLatentSpace S 1 → _) inferInstance)
      ((B.measurable_lowerFactorMap' 1).comp measurable_fst).comap_le P := by
    refine CondIndep.sup_right ?_ (hsupBlocks.trans (measurable_iff_comap_le.mp measurable_fst))
      measurable_snd.comap_le
    exact condIndep_of_condIndep_of_le_left hciAlg hsupBlocks
  have h4 : iCondIndepFun
      (MeasurableSpace.comap (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance ⊔
        MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
          RankLatentSpace S 1 → _) inferInstance)
      (sup_le (((B.measurable_lowerFactorMap' 1).comp measurable_fst).comap_le)
        measurable_snd.comap_le)
      (singletonBlockRead S) P := by
    rw [iCondIndepFun_iff_iCondIndep] at h2 ⊢
    exact iCondIndep_of_condIndep_iSup _ _ le_sup_left
      (fun v => (hblockmeas v).comap_le) h2 h3
  -- rung 4: down to the latent algebra alone, by representability of the join
  have hrepJ : ∀ s, MeasurableSet[MeasurableSpace.comap
      (B.lowerFactorMap 1 ∘ Prod.fst) inferInstance ⊔
        MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
          RankLatentSpace S 1 → _) inferInstance] s →
      ∃ t, MeasurableSet[MeasurableSpace.comap (Prod.snd : RelStructure S (Vinfinite S) ×
        RankLatentSpace S 1 → _) inferInstance] t ∧ s =ᵐ[P] t := by
    refine fun s hs => eventuallyMeasurableSet_sup ?_ hs
    rintro u ⟨D, hD, rfl⟩
    refine ⟨(g ∘ Prod.snd) ⁻¹' D, ⟨g ⁻¹' D, hg hD, by rw [Set.preimage_comp]⟩, ?_⟩
    refine Filter.eventuallyEq_set.mpr ?_
    filter_upwards [hres] with p hp
    simp only [Set.mem_preimage, Function.comp_apply]
    rw [show B.lowerFactorMap 1 p.1 = g p.2 from hp]
  exact (iCondIndepFun_congr_of_ae_representable le_sup_right _ hrepJ hblockmeas).mp h4

end CoherentBasis

end RelSignature
