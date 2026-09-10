/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRankSuccessorContract

/-!
# Admissible representations (R4 converse, #107)

A candidate strengthening of the inductive invariant, stated route-neutrally and separately from
`RankRepresentation`, which is left intact. The universal successor statement is refuted
(`Graphon.RelTernaryParityRegression`): an exact successor cannot be required of every current
representation. The repaired induction is to have the shape

`Admissible C → ∃ D : RankSuccessor C, Admissible D.next`

together with an admissible base case.

**The condition.** Conditional on the entire old latent array, the *full induced structures* on
any finite family of finite vertex sets are mutually independent whenever the sets pairwise meet
in fewer than `n` vertices. "Full induced structure" means every relation coordinate whose
support lies inside the set, not the block of the working rank alone; mutuality, not pairwise
independence, is required. The condition constrains higher-arity dependence before it becomes
visible at the working rank.

## Contents

* `InducedIndex`, `InducedSpace`, `inducedMap` — the full induced structure on a finite vertex
  set.
* `SmallOverlap` — pairwise intersections below the working rank.
* `RankRepresentation.Admissible` — the invariant.
* `admissible_zero` — at rank zero every representation is admissible: the overlap condition
  admits no two distinct sets.
* `admissible_of_ae_eq_snd` — a representation whose structure is almost surely a function of
  its latents is admissible.
* `admissible_iff_iIndepFun_of_indep` — for a coupling whose structure is independent of its
  latents, admissibility is unconditional mutual independence of the induced structures.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

universe u

variable {S : RelSignature.{u}}

/-! ### The full induced structure on a finite vertex set -/

/-- Coordinates whose tagged support lies inside `A`. -/
def InducedIndex (A : Finset (Σ s : S.Srt, Vinfinite S s)) :=
  {c : RelCoord S (Vinfinite S) // c.support ⊆ A}

instance [Countable S.Rel] (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Countable (InducedIndex (S := S) A) :=
  Subtype.countable

/-- The full induced structure on `A`. -/
abbrev InducedSpace (A : Finset (Σ s : S.Srt, Vinfinite S s)) := InducedIndex (S := S) A → Bool

/-- Read the full induced structure on `A` off a structure. -/
def inducedMap (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    RelStructure S (Vinfinite S) → InducedSpace (S := S) A :=
  fun X c => X c.1

theorem measurable_inducedMap (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measurable (inducedMap (S := S) A) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- Pairwise intersections below the working rank. -/
def SmallOverlap (n : ℕ) {ι : Type*} (A : ι → Finset (Σ s : S.Srt, Vinfinite S s)) : Prop :=
  ∀ i j, i ≠ j → ∀ B : Finset (Σ s : S.Srt, Vinfinite S s), B ⊆ A i → B ⊆ A j → B.card < n

namespace InfiniteRelExchangeableLaw

variable {M : InfiniteRelExchangeableLaw S} {n : ℕ} [Countable S.Srt] [Countable S.Rel]

/-- **Admissibility**: conditional on the whole latent array, the full induced structures on any
finite family of finite vertex sets with small pairwise overlap are mutually independent. -/
def RankRepresentation.Admissible (C : M.RankRepresentation n) : Prop :=
  haveI := C.isProbabilityMeasure_P
  ∀ (k : ℕ) (A : Fin k → Finset (Σ s : S.Srt, Vinfinite S s)), SmallOverlap n A →
    iCondIndepFun (MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) inferInstance)
      measurable_snd.comap_le
      (fun i => inducedMap (A i) ∘ Prod.fst) C.P

namespace RankRepresentation

variable (C : M.RankRepresentation n)

omit [Countable S.Srt] [Countable S.Rel] in
/-- A family with small overlap at rank zero has at most one member. -/
theorem subsingleton_of_smallOverlap_zero {k : ℕ} {A : Fin k → Finset (Σ s : S.Srt, Vinfinite S s)}
    (hA : SmallOverlap 0 A) : ∀ i j : Fin k, i = j := by
  intro i j
  by_contra hij
  exact absurd (hA i j hij ∅ (Finset.empty_subset _) (Finset.empty_subset _))
    (Nat.not_lt_zero _)

/-- **At rank zero every representation is admissible.** -/
theorem admissible_zero (C₀ : M.RankRepresentation 0) : C₀.Admissible := by
  intro k A hA
  haveI := C₀.isProbabilityMeasure_P
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul _ _
    (fun i => (measurable_inducedMap (A i)).comp measurable_fst)]
  intro T sets hsets
  rcases T.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simp only [Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ, Finset.prod_empty]
    rw [Set.indicator_univ, condExp_const measurable_snd.comap_le]
    exact Filter.EventuallyEq.rfl
  · have hT : T = {i} := by
      ext j
      simp only [Finset.mem_singleton]
      exact ⟨fun _ => subsingleton_of_smallOverlap_zero hA j i, fun h => h ▸ hi⟩
    subst hT
    simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left, Finset.prod_singleton]
    exact Filter.EventuallyEq.rfl

/-- **A structure that is almost surely a function of its latents gives an admissible
representation.** -/
theorem admissible_of_ae_eq_snd {g : RankLatentSpace S n → RelStructure S (Vinfinite S)}
    (hg : Measurable g) (hae : (fun p => p.1) =ᵐ[C.P] fun p => g p.2) : C.Admissible := by
  intro k A hA
  haveI := C.isProbabilityMeasure_P
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul _ _
    (fun i => (measurable_inducedMap (A i)).comp measurable_fst)]
  intro T sets hsets
  -- each event is a.e. an event of the latents
  have hev : ∀ i ∈ T, (inducedMap (A i) ∘ Prod.fst) ⁻¹' sets i =ᵐ[C.P]
      Prod.snd ⁻¹' ((inducedMap (A i) ∘ g) ⁻¹' sets i) := by
    intro i hi
    refine Filter.eventuallyEq_set.mpr ?_
    filter_upwards [hae] with p hp
    simp only [Set.mem_preimage, Function.comp_apply]
    rw [hp]
  have hmeas : ∀ i ∈ T, MeasurableSet[MeasurableSpace.comap
      (Prod.snd : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) inferInstance]
      (Prod.snd ⁻¹' ((inducedMap (A i) ∘ g) ⁻¹' sets i)) := fun i hi =>
    ⟨_, ((measurable_inducedMap (A i)).comp hg) (hsets i hi), rfl⟩
  have hinter : (⋂ i ∈ T, (inducedMap (A i) ∘ Prod.fst) ⁻¹' sets i) =ᵐ[C.P]
      ⋂ i ∈ T, Prod.snd ⁻¹' ((inducedMap (A i) ∘ g) ⁻¹' sets i) :=
    Filter.EventuallyEq.countable_bInter T.countable_toSet hev
  have hinterm : MeasurableSet[MeasurableSpace.comap
      (Prod.snd : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) inferInstance]
      (⋂ i ∈ T, Prod.snd ⁻¹' ((inducedMap (A i) ∘ g) ⁻¹' sets i)) :=
    Finset.measurableSet_biInter T hmeas
  -- conditional expectations of latent events are their indicators
  have hcond : ∀ s, MeasurableSet[MeasurableSpace.comap
      (Prod.snd : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) inferInstance] s →
      C.P⟦s | MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) inferInstance⟧ =
        s.indicator fun _ => (1 : ℝ) := fun s hs =>
    condExp_of_stronglyMeasurable measurable_snd.comap_le
      ((stronglyMeasurable_const : StronglyMeasurable[MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) inferInstance]
        fun _ => (1 : ℝ)).indicator hs)
      ((integrable_const 1).indicator (measurable_snd.comap_le _ hs))
  refine (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set hinter)).trans ?_
  rw [hcond _ hinterm]
  have hprod : (∏ i ∈ T, C.P⟦(inducedMap (A i) ∘ Prod.fst) ⁻¹' sets i | MeasurableSpace.comap
      (Prod.snd : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) inferInstance⟧)
      =ᵐ[C.P] ∏ i ∈ T, (Prod.snd ⁻¹' ((inducedMap (A i) ∘ g) ⁻¹' sets i)).indicator
        fun _ => (1 : ℝ) := by
    have : ∀ i ∈ T, C.P⟦(inducedMap (A i) ∘ Prod.fst) ⁻¹' sets i | MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) inferInstance⟧
        =ᵐ[C.P] (Prod.snd ⁻¹' ((inducedMap (A i) ∘ g) ⁻¹' sets i)).indicator
          fun _ => (1 : ℝ) := fun i hi => by
      refine (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set (hev i hi))).trans ?_
      rw [hcond _ (hmeas i hi)]
    filter_upwards [(Filter.eventually_all_finset T).mpr this] with p hp
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl fun i hi => hp i hi
  refine (Filter.EventuallyEq.of_eq ?_).trans hprod.symm
  funext p
  rw [Finset.prod_apply]
  by_cases h : p ∈ ⋂ i ∈ T, Prod.snd ⁻¹' ((inducedMap (A i) ∘ g) ⁻¹' sets i)
  · rw [Set.indicator_of_mem h]
    exact (Finset.prod_eq_one fun i hi => by
      rw [Set.indicator_of_mem (Set.mem_iInter₂.mp h i hi)]).symm
  · rw [Set.indicator_of_notMem h]
    rw [Set.mem_iInter₂] at h
    push Not at h
    obtain ⟨i, hi, hpi⟩ := h
    exact (Finset.prod_eq_zero hi (by rw [Set.indicator_of_notMem hpi])).symm

/-- **Conditioning on latents independent of the structure is no conditioning**: for functions of
the structure, mutual conditional independence given the latents is mutual independence. -/
theorem iCondIndepFun_snd_iff_iIndepFun
    (hind : IndepFun (Prod.fst : RelStructure S (Vinfinite S) × RankLatentSpace S n → _)
      Prod.snd C.P) {ι : Type*} {γ : ι → Type*} [∀ i, MeasurableSpace (γ i)]
    {X : ∀ i, RelStructure S (Vinfinite S) → γ i} (hX : ∀ i, Measurable (X i)) :
    haveI := C.isProbabilityMeasure_P
    iCondIndepFun (MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) inferInstance)
      measurable_snd.comap_le (fun i => X i ∘ Prod.fst) C.P ↔
    iIndepFun (fun i => X i ∘
      (Prod.fst : RelStructure S (Vinfinite S) × RankLatentSpace S n → _)) C.P := by
  haveI := C.isProbabilityMeasure_P
  have hm : ∀ i, Measurable (X i ∘
      (Prod.fst : RelStructure S (Vinfinite S) × RankLatentSpace S n → _)) :=
    fun i => (hX i).comp measurable_fst
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul _ _ hm,
    iIndepFun_iff_measure_inter_preimage_eq_mul]
  -- conditional expectations of structure events given the latents are their probabilities
  have hce : ∀ s : Set (RelStructure S (Vinfinite S) × RankLatentSpace S n),
      MeasurableSet[MeasurableSpace.comap
        (Prod.fst : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) inferInstance] s →
      C.P⟦s | MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) inferInstance⟧
        =ᵐ[C.P] fun _ => (C.P s).toReal := by
    intro s hs
    refine (condExp_indep_eq measurable_fst.comap_le measurable_snd.comap_le
      ((stronglyMeasurable_const : StronglyMeasurable[MeasurableSpace.comap
        (Prod.fst : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) inferInstance]
        fun _ => (1 : ℝ)).indicator hs) hind).trans ?_
    refine Filter.EventuallyEq.of_eq (funext fun _ => ?_)
    rw [integral_indicator_const _ (measurable_fst.comap_le _ hs), smul_eq_mul, mul_one,
      measureReal_def]
  have hsm : ∀ (T : Finset ι) (sets : ∀ i, Set (γ i)),
      (∀ i ∈ T, MeasurableSet (sets i)) → ∀ i ∈ T, MeasurableSet[MeasurableSpace.comap
        (Prod.fst : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) inferInstance]
        ((X i ∘ Prod.fst) ⁻¹' sets i) := fun T sets hsets i hi =>
    ⟨_, (hX i) (hsets i hi), rfl⟩
  have hprod : ∀ (T : Finset ι) (sets : ∀ i, Set (γ i)),
      (∀ i ∈ T, MeasurableSet (sets i)) →
      (∏ i ∈ T, C.P⟦(X i ∘ Prod.fst) ⁻¹' sets i | MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) inferInstance⟧)
        =ᵐ[C.P] fun _ => ∏ i ∈ T, (C.P ((X i ∘ Prod.fst) ⁻¹' sets i)).toReal := by
    intro T sets hsets
    have : ∀ i ∈ T, C.P⟦(X i ∘ Prod.fst) ⁻¹' sets i | MeasurableSpace.comap
        (Prod.snd : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) inferInstance⟧
        =ᵐ[C.P] fun _ => (C.P ((X i ∘ Prod.fst) ⁻¹' sets i)).toReal :=
      fun i hi => hce _ (hsm T sets hsets i hi)
    filter_upwards [(Filter.eventually_all_finset T).mpr this] with p hp
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl fun i hi => hp i hi
  constructor
  · intro h T sets hsets
    have hinter : MeasurableSet[MeasurableSpace.comap
        (Prod.fst : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) inferInstance]
        (⋂ i ∈ T, (X i ∘ Prod.fst) ⁻¹' sets i) :=
      Finset.measurableSet_biInter T (hsm T sets hsets)
    have h2 : (fun _ => (C.P (⋂ i ∈ T, (X i ∘ Prod.fst) ⁻¹' sets i)).toReal)
        =ᵐ[C.P] fun _ => ∏ i ∈ T, (C.P ((X i ∘ Prod.fst) ⁻¹' sets i)).toReal :=
      (hce _ hinter).symm.trans ((h T hsets).trans (hprod T sets hsets))
    obtain ⟨p, hp⟩ := h2.exists
    have := congrArg ENNReal.ofReal hp
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _), ← ENNReal.toReal_prod,
      ENNReal.ofReal_toReal (ENNReal.prod_ne_top fun i _ => measure_ne_top _ _)] at this
    exact this
  · intro h T sets hsets
    have hinter : MeasurableSet[MeasurableSpace.comap
        (Prod.fst : RelStructure S (Vinfinite S) × RankLatentSpace S n → _) inferInstance]
        (⋂ i ∈ T, (X i ∘ Prod.fst) ⁻¹' sets i) :=
      Finset.measurableSet_biInter T (hsm T sets hsets)
    refine (hce _ hinter).trans ((Filter.EventuallyEq.of_eq (funext fun _ => ?_)).trans
      (hprod T sets hsets).symm)
    rw [h T hsets, ENNReal.toReal_prod]

/-- **For a coupling whose structure is independent of its latents**, admissibility is
unconditional mutual independence of the induced structures. -/
theorem admissible_iff_iIndepFun_of_indep
    (hind : IndepFun (Prod.fst : RelStructure S (Vinfinite S) × RankLatentSpace S n → _)
      Prod.snd C.P) :
    C.Admissible ↔ ∀ (k : ℕ) (A : Fin k → Finset (Σ s : S.Srt, Vinfinite S s)), SmallOverlap n A →
      iIndepFun (fun i => inducedMap (A i) ∘
        (Prod.fst : RelStructure S (Vinfinite S) × RankLatentSpace S n → _)) C.P :=
  ⟨fun h k A hA => (C.iCondIndepFun_snd_iff_iIndepFun hind
      (fun i => measurable_inducedMap (A i))).mp (h k A hA),
    fun h k A hA => (C.iCondIndepFun_snd_iff_iIndepFun hind
      (fun i => measurable_inducedMap (A i))).mpr (h k A hA)⟩

end RankRepresentation

/-! ### The rank-zero base -/

/-- **The rank-zero representation** of a law without nullary relations: the law with the
one-point latent cube. Admissible by `admissible_zero`. -/
noncomputable def rankZeroRep (M : InfiniteRelExchangeableLaw S) (hS : NoNullary S) :
    M.RankRepresentation 0 where
  P := (M.law : Measure (RelStructure S (Vinfinite S))).prod (rankLatentSource S 0)
  isProbabilityMeasure_P := by
    haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
    infer_instance
  map_fst := by
    haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
    rw [Measure.map_fst_prod]; simp
  map_snd := by
    haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
    rw [Measure.map_snd_prod]; simp
  invariant := by
    intro σ
    haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
    have h : (⇑(rankLatentRelabel σ 0) : RankLatentSpace S 0 → RankLatentSpace S 0) = id :=
      funext fun ω => Subsingleton.elim _ _
    rw [h, ← Measure.map_prod_map _ _ (measurable_relabel σ.1) measurable_id, M.exchangeable,
      Measure.map_id]
  lower_recovers := fun _ hA => absurd hA (Nat.not_lt_zero _)
  fixing_complete := fun _ hA => absurd hA (Nat.not_lt_zero _)
  screening := by
    intro A hA
    haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
    haveI : Subsingleton (BlockSpace (S := S) A) := by
      classical
      refine ⟨fun x y => funext fun i => ?_⟩
      exfalso
      obtain ⟨c, hc⟩ := i
      have hne : c.support.Nonempty := by
        obtain ⟨j⟩ : Nonempty (Fin (S.arity c.1)) := ⟨⟨0, hS c.1⟩⟩
        exact ⟨c.taggedValue j, (c.mem_support_iff _).mpr ⟨j, rfl⟩⟩
      rw [hc, Finset.card_eq_zero.mp hA] at hne
      exact Finset.not_nonempty_empty hne
    classical
    exact CondIndepFun.congr (condIndepFun_const_left (fun _ => false : BlockSpace (S := S) A) _)
      measurable_const (measurable_restObservation 0 _)
      ((measurable_blockMap (S := S) A).comp measurable_fst) (measurable_restObservation 0 _)
      (Filter.EventuallyEq.of_eq (funext fun _ => Subsingleton.elim _ _)) Filter.EventuallyEq.rfl

end InfiniteRelExchangeableLaw

end RelSignature
