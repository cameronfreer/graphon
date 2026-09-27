/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelMarkedRowKernel
import Graphon.RelWeakUnion

/-!
# Rank one: joint-law locality of the marked rows

Fix a pooled rank extension `Q` of a rank-one representation and a finite original set `A`. The
full induced original structure on `A`, the marked rows of the vertices of `A`, and the purely
spare structure are all read off the marked observation at `A` by coordinate restriction.

**Outside-row separation.** Given the environment, the marked observation at `A`, together with
the pooled latent array, is conditionally independent of the marked rows of the original vertices
outside `A`. A marked cylinder at `A` never reads the original copy of a vertex outside `A`, so it
is fixed by the transpositions of such a vertex with sufficiently fresh spare vertices; the
finite-family peel product then starts from it. The marked observation and the outside rows are
indexed as one family, so the argument keeps the mutual form until the two groups are separated.
Adjoining the latent array enlarges the observed variable, not the conditioning, which stays
exactly the environment. No admissibility hypothesis and no bound on the cardinality of `A` enters.
-/

universe u

open MeasureTheory ProbabilityTheory

namespace RelSignature

variable {S : RelSignature.{u}}

/-! ### Exact coordinate factorizations through the marked observation -/

theorem markedSet_mono {A B : Finset (Σ s : S.Srt, Vinfinite S s)} (h : A ⊆ B) :
    markedSet (S := S) A ⊆ markedSet B := by
  rintro v (⟨a, ha, hA⟩ | ⟨b, hb⟩)
  · exact Or.inl ⟨a, ha, h hA⟩
  · exact Or.inr ⟨b, hb⟩

/-- The marked observation at a smaller set, read off the marked observation at a larger one. -/
def markedRestrict {A B : Finset (Σ s : S.Srt, Vinfinite S s)} (h : A ⊆ B) :
    MarkedSpace (S := S) B → MarkedSpace (S := S) A :=
  fun m c => m ⟨c.1, fun v hv => markedSet_mono h (c.2 v hv)⟩

theorem measurable_markedRestrict {A B : Finset (Σ s : S.Srt, Vinfinite S s)} (h : A ⊆ B) :
    Measurable (markedRestrict (S := S) h) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

theorem markedRestrict_markedObs {A B : Finset (Σ s : S.Srt, Vinfinite S s)} (h : A ⊆ B)
    (Y : RelStructure S (PoolVertex S)) : markedRestrict h (markedObs B Y) = markedObs A Y :=
  rfl

/-- An induced coordinate on `A`, read on the original copy, is a marked coordinate at `A`. -/
def InducedIndex.toMarked {A : Finset (Σ s : S.Srt, Vinfinite S s)} (c : InducedIndex (S := S) A) :
    MarkedCoord (S := S) A :=
  ⟨RelCoord.map (fun s => (originalVertex S s : Vinfinite S s → PoolVertex S s)) c.1, by
    intro v hv
    obtain ⟨i, rfl⟩ := (RelCoord.mem_support_iff _ _).mp hv
    exact Or.inl ⟨c.1.2 i, rfl, c.2 ((RelCoord.mem_support_iff _ _).mpr ⟨i, rfl⟩)⟩⟩

/-- The full induced original structure on `A`, read off the marked observation at `A`. -/
def markedToInduced (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    MarkedSpace (S := S) A → InducedSpace (S := S) A :=
  fun m c => m c.toMarked

theorem measurable_markedToInduced (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measurable (markedToInduced (S := S) A) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- **The induced original structure factors through the marked observation**, pointwise. -/
theorem inducedMap_restrictOriginal (A : Finset (Σ s : S.Srt, Vinfinite S s))
    (Y : RelStructure S (PoolVertex S)) :
    inducedMap A (restrictOriginal S Y) = markedToInduced A (markedObs A Y) :=
  rfl

/-- A coordinate of the spare copy, read on the pool, is a marked coordinate at every `A`. -/
def RelCoord.toMarkedSpare (A : Finset (Σ s : S.Srt, Vinfinite S s))
    (c : RelCoord S (Vinfinite S)) : MarkedCoord (S := S) A :=
  ⟨c.toSpare, by
    intro v hv
    obtain ⟨i, rfl⟩ := (RelCoord.mem_support_iff _ _).mp hv
    exact Or.inr ⟨c.2 i, rfl⟩⟩

/-- The purely spare structure, read off the marked observation at `A`. -/
def markedToSpare (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    MarkedSpace (S := S) A → RelStructure S (Vinfinite S) :=
  fun m c => m (c.toMarkedSpare A)

theorem measurable_markedToSpare (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measurable (markedToSpare (S := S) A) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- **The purely spare structure factors through the marked observation**, pointwise. -/
theorem restrictPool_eq_markedToSpare (A : Finset (Σ s : S.Srt, Vinfinite S s))
    (Y : RelStructure S (PoolVertex S)) : restrictPool S Y = markedToSpare A (markedObs A Y) :=
  rfl

/-- The marked rows of the vertices of `A`, read off the marked observation at `A`. -/
def markedToRows (A : Finset (RowIndex S)) :
    MarkedSpace (S := S) A → ∀ v : A, MarkedSpace (S := S) {v.1} :=
  fun m v => markedRestrict (Finset.singleton_subset_iff.mpr v.2) m

theorem measurable_markedToRows (A : Finset (RowIndex S)) :
    Measurable (markedToRows (S := S) A) :=
  measurable_pi_lambda _ fun _ => measurable_markedRestrict _

/-- **The rows inside `A` factor through the marked observation**, pointwise. -/
theorem restrict_rowsObs (A : Finset (RowIndex S)) (p : PooledOne S) :
    A.restrict (rowsObs p) = markedToRows A (markedObs A p.1) :=
  rfl

/-- **The environment factors through the marked observation and the latent array**,
pointwise. -/
theorem envObs_eq_markedToSpare (A : Finset (RowIndex S)) (p : PooledOne S) :
    envObs p = (markedToSpare A (markedObs A p.1), p.2) :=
  rfl

/-! ### The marked observation with the latent array, and the rows outside `A` -/

/-- The marked observation at `A` together with the pooled latent array. Adjoining the latent
array enlarges the observed variable, not the conditioning. -/
def markedLatentObs (A : Finset (RowIndex S)) :
    PooledOne S → MarkedSpace (S := S) A × PooledRankLatentSpace S 1 :=
  fun p => (markedObs A p.1, p.2)

theorem measurable_markedLatentObs (A : Finset (RowIndex S)) :
    Measurable (markedLatentObs (S := S) A) :=
  ((measurable_markedObs A).comp measurable_fst).prodMk measurable_snd

/-- The family of marked rows of the original vertices outside `A`. -/
def rowsOut (A : Finset (RowIndex S)) :
    PooledOne S → ∀ v : {v : RowIndex S // v ∉ A}, MarkedSpace (S := S) {v.1} :=
  fun p v => rowObs v.1 p

theorem measurable_rowsOut (A : Finset (RowIndex S)) : Measurable (rowsOut (S := S) A) :=
  measurable_pi_lambda _ fun v => measurable_rowObs v.1

/-- The generating π-system of the marked observation with the latent array: marked cylinders
crossed with latent events. -/
def markedLatentGenerators (A : Finset (RowIndex S)) : Set (Set (PooledOne S)) :=
  Set.preimage (markedLatentObs A) ''
    Set.image2 (· ×ˢ ·) (measurableCylinders fun _ : MarkedCoord (S := S) A => Bool)
      {L : Set (PooledRankLatentSpace S 1) | MeasurableSet L}

theorem isPiSystem_markedLatentGenerators (A : Finset (RowIndex S)) :
    IsPiSystem (markedLatentGenerators (S := S) A) :=
  (isPiSystem_measurableCylinders.prod MeasurableSpace.isPiSystem_measurableSet).comap _

theorem comap_markedLatentObs_eq_generateFrom (A : Finset (RowIndex S)) :
    MeasurableSpace.comap (markedLatentObs (S := S) A) inferInstance =
      MeasurableSpace.generateFrom (markedLatentGenerators A) := by
  have hspan : IsCountablySpanning
      (measurableCylinders fun _ : MarkedCoord (S := S) A => Bool) :=
    ⟨fun _ => Set.univ, fun _ => univ_mem_measurableCylinders _, Set.iUnion_const _⟩
  rw [markedLatentGenerators, ← MeasurableSpace.comap_generateFrom, generateFrom_eq_prod
    generateFrom_measurableCylinders MeasurableSpace.generateFrom_measurableSet hspan
    isCountablySpanning_measurableSet]

/-- **A marked cylinder at `A` is swap-fixed at every original vertex outside `A`**, beyond the
largest spare index it reads: its coordinates never read the original copy of such a vertex. -/
theorem swapFixed_markedCylinder {A : Finset (RowIndex S)} {v : RowIndex S} (hv : v ∉ A)
    (t : Finset (MarkedCoord (S := S) A)) (T : Set (t → Bool)) :
    SwapFixed v (t.sup fun c => c.1.spareBound) (cylEvent (fun c : t => c.1.1) T) := by
  refine swapFixed_cylEvent v (fun c : t => c.1.1) (fun c h => ?_)
    (fun c => Finset.le_sup (f := fun c : MarkedCoord (S := S) A => c.1.spareBound) c.2) T
  rcases c.1.2 _ h with ⟨a, ha, hA⟩ | ⟨b, hb⟩
  · have ha' : v.2 = a := Sum.inl.inj ha
    subst ha'
    exact hv hA
  · exact Sum.inl_ne_inr hb

/-- A generator of the marked observation with the latent array is measurable and swap-fixed
at every original vertex outside `A`, beyond a common bound. -/
theorem exists_swapFixed_of_mem_markedLatentGenerators {A : Finset (RowIndex S)}
    {K : Set (PooledOne S)} (hK : K ∈ markedLatentGenerators A) :
    MeasurableSet K ∧ ∃ b, ∀ v : RowIndex S, v ∉ A → SwapFixed v b K := by
  obtain ⟨_, ⟨C, hC, L, hL, rfl⟩, rfl⟩ := hK
  obtain ⟨t, T, hT, rfl⟩ := (mem_measurableCylinders _).mp hC
  have h : markedLatentObs A ⁻¹' ((cylinder t T : Set (MarkedSpace (S := S) A)) ×ˢ L) =
      cylEvent (fun c : t => c.1.1) T ∩ latentEvent L := Set.ext fun _ => Iff.rfl
  rw [h]
  exact ⟨(measurableSet_cylEvent _ hT).inter (measurable_snd (show MeasurableSet L from hL)),
    t.sup fun c => c.1.spareBound,
    fun v hv => (swapFixed_markedCylinder hv t T).inter (swapFixed_latentEvent v _ L)⟩

/-! ### Outside-row separation -/

section Option

variable {α ι : Type*}

private theorem biInter_option_of_mem {F : Finset (Option ι)} (hn : none ∈ F)
    (H : Option ι → Set α) : ⋂ j ∈ F, H j = (⋂ v ∈ F.eraseNone, H (some v)) ∩ H none := by
  ext x
  simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_eraseNone]
  refine ⟨fun h => ⟨fun v hv => h _ hv, h _ hn⟩, ?_⟩
  rintro ⟨h, h'⟩ (_ | v) hj
  · exact h'
  · exact h v hj

private theorem biInter_option_of_notMem {F : Finset (Option ι)} (hn : none ∉ F)
    (H : Option ι → Set α) : ⋂ j ∈ F, H j = ⋂ v ∈ F.eraseNone, H (some v) := by
  ext x
  simp only [Set.mem_iInter, Finset.mem_eraseNone]
  refine ⟨fun h v hv => h _ hv, ?_⟩
  rintro h (_ | v) hj
  · exact absurd hj hn
  · exact h v hj

private theorem prod_option_of_mem {M : Type*} [CommMonoid M] {F : Finset (Option ι)}
    (hn : none ∈ F) (f : Option ι → M) :
    ∏ j ∈ F, f j = (∏ v ∈ F.eraseNone, f (some v)) * f none := by
  classical
  conv_lhs => rw [← Finset.insert_eq_of_mem hn, ← Finset.insertNone_eraseNone,
    Finset.prod_insertNone]
  exact mul_comm _ _

private theorem prod_option_of_notMem {M : Type*} [CommMonoid M] {F : Finset (Option ι)}
    (hn : none ∉ F) (f : Option ι → M) : ∏ j ∈ F, f j = ∏ v ∈ F.eraseNone, f (some v) := by
  classical
  conv_lhs => rw [← Finset.erase_eq_of_notMem hn, ← Finset.map_some_eraseNone, Finset.prod_map]
  rfl

end Option

namespace InfiniteRelExchangeableLaw

variable {M : InfiniteRelExchangeableLaw S} [Countable S.Srt] [Countable S.Rel]
  {C : M.RankRepresentation 1} (Q : PooledRankExtension C)

/-- The observed family of the separation: the marked observation at `A` with the latent array,
and the rows outside `A`, one index each. -/
@[reducible] private def sepAlg (A : Finset (RowIndex S)) :
    Option {v : RowIndex S // v ∉ A} → MeasurableSpace (PooledOne S)
  | none => MeasurableSpace.comap (markedLatentObs A) inferInstance
  | some v => MeasurableSpace.comap (rowObs v.1) inferInstance

/-- The generating π-systems of the separation family. -/
private def sepGenerators (A : Finset (RowIndex S)) :
    Option {v : RowIndex S // v ∉ A} → Set (Set (PooledOne S))
  | none => markedLatentGenerators A
  | some v => rowCylinders v.1

private theorem condExp_iInter_sepGenerators (A : Finset (RowIndex S))
    (F : Finset (Option {v : RowIndex S // v ∉ A})) {H : Option {v : RowIndex S // v ∉ A} →
      Set (PooledOne S)} (hH : ∀ j ∈ F, H j ∈ sepGenerators A j) :
    Q.lawOne⟦⋂ j ∈ F, H j | envAlg S⟧ =ᵐ[Q.lawOne] ∏ j ∈ F, Q.lawOne⟦H j | envAlg S⟧ := by
  classical
  -- a cylinder presentation of each tested row
  have hpres : ∀ u : {v : RowIndex S // v ∉ A},
      ∃ q : Σ t : Finset (MarkedCoord (S := S) {u.1}), Set (t → Bool),
        MeasurableSet q.2 ∧ (some u ∈ F → H (some u) = rowEvent u.1 q.1 q.2) := by
    intro u
    by_cases hu : some u ∈ F
    · obtain ⟨t, T, hT, hHu⟩ := exists_rowEvent_of_mem_rowCylinders (hH _ hu)
      exact ⟨⟨t, T⟩, hT, fun _ => hHu⟩
    · exact ⟨⟨∅, Set.univ⟩, MeasurableSet.univ, fun h => absurd h hu⟩
  choose pres hpres using hpres
  -- the common swap-fixed set, with the decomposition of the tested family
  obtain ⟨K₀, hK₀meas, b, hb, hinter, hprod⟩ : ∃ K₀ : Set (PooledOne S), MeasurableSet K₀ ∧
      ∃ b, (∀ u : {v : RowIndex S // v ∉ A}, SwapFixed u.1 b K₀) ∧
        (⋂ j ∈ F, H j) = (⋂ u ∈ F.eraseNone, H (some u)) ∩ K₀ ∧
        (∏ j ∈ F, Q.lawOne⟦H j | envAlg S⟧) =
          (∏ u ∈ F.eraseNone, Q.lawOne⟦H (some u) | envAlg S⟧) * Q.lawOne⟦K₀ | envAlg S⟧ := by
    by_cases hn : none ∈ F
    · obtain ⟨hm, b, hb⟩ := exists_swapFixed_of_mem_markedLatentGenerators (hH none hn)
      exact ⟨H none, hm, b, fun u => hb u.1 u.2, biInter_option_of_mem hn H,
        prod_option_of_mem hn _⟩
    · refine ⟨Set.univ, MeasurableSet.univ, 0, fun u => swapFixed_univ u.1 0, ?_, ?_⟩
      · rw [biInter_option_of_notMem hn, Set.inter_univ]
      · rw [prod_option_of_notMem hn, Set.indicator_univ, condExp_const envAlg_le]
        exact (mul_one _).symm
  have h := Q.condExp_iInter_rowEvent_inter_eq_prod (fun u : {v : RowIndex S // v ∉ A} => u.1)
    Subtype.val_injective (fun u => (pres u).1) (fun u => (pres u).2) (fun u => (hpres u).1)
    hK₀meas hb F.eraseNone
  have h1 : (⋂ u ∈ F.eraseNone, H (some u)) =
      ⋂ u ∈ F.eraseNone, rowEvent u.1 (pres u).1 (pres u).2 :=
    Set.iInter₂_congr fun u hu => (hpres u).2 (Finset.mem_eraseNone.mp hu)
  have h2 : (∏ u ∈ F.eraseNone, Q.lawOne⟦H (some u) | envAlg S⟧) =
      ∏ u ∈ F.eraseNone, Q.lawOne⟦rowEvent u.1 (pres u).1 (pres u).2 | envAlg S⟧ :=
    Finset.prod_congr rfl fun u hu => by rw [(hpres u).2 (Finset.mem_eraseNone.mp hu)]
  rw [hinter, hprod, h1, h2]
  exact h

/-- **Outside-row separation.** Given the environment, the marked observation at a finite
original set `A`, together with the pooled latent array, is conditionally independent of the
marked rows of the original vertices outside `A`. No admissibility hypothesis and no bound on the
cardinality of `A` enters. -/
theorem PooledRankExtension.condIndep_markedLatentObs_rowsOut (A : Finset (RowIndex S)) :
    CondIndep (envAlg S) (MeasurableSpace.comap (markedLatentObs A) inferInstance)
      (MeasurableSpace.comap (rowsOut A) inferInstance) envAlg_le Q.lawOne := by
  have hle : ∀ j, sepAlg A j ≤ (inferInstance : MeasurableSpace (PooledOne S)) := by
    rintro (_ | v)
    · exact (measurable_markedLatentObs A).comap_le
    · exact (measurable_rowObs v.1).comap_le
  have hmeas : ∀ j, ∀ H ∈ sepGenerators A j, MeasurableSet H := by
    rintro (_ | v) H hH
    · exact (exists_swapFixed_of_mem_markedLatentGenerators hH).1
    · obtain ⟨t, T, hT, rfl⟩ := exists_rowEvent_of_mem_rowCylinders hH
      exact measurableSet_rowEvent v.1 t T hT
  have hind : iCondIndep (envAlg S) envAlg_le (sepAlg A) Q.lawOne := by
    refine iCondIndepSets.iCondIndep _ hle (sepGenerators A) ?_ ?_ ?_
    · rintro (_ | v)
      · exact isPiSystem_markedLatentGenerators A
      · exact isPiSystem_rowCylinders v.1
    · rintro (_ | v)
      · exact comap_markedLatentObs_eq_generateFrom A
      · exact comap_rowObs_eq_generateFrom v.1
    · rw [iCondIndepSets_iff _ _ _ hmeas]
      intro F H hH
      exact condExp_iInter_sepGenerators Q A F hH
  have hsep := condIndep_iSup_of_disjoint hle hind
    (S := {none}) (T := Set.range some) (Set.disjoint_singleton_left.mpr (by simp))
  refine condIndep_of_condIndep_of_le_right (condIndep_of_condIndep_of_le_left hsep ?_) ?_
  · exact le_iSup₂_of_le (f := fun j _ => sepAlg A j) none (Set.mem_singleton _) le_rfl
  · rw [iSup_range]
    show MeasurableSpace.comap (rowsOut A)
      (⨆ v, MeasurableSpace.comap (fun r : ∀ v : {v : RowIndex S // v ∉ A},
        MarkedSpace (S := S) {v.1} => r v) inferInstance) ≤ _
    rw [MeasurableSpace.comap_iSup]
    exact iSup_mono fun v => MeasurableSpace.comap_comp.le

/-- **Outside-row separation, in the stated form**: given the environment, the marked observation
at `A` is conditionally independent of the marked rows outside `A`. -/
theorem PooledRankExtension.condIndepFun_markedObs_rowsOut (A : Finset (RowIndex S)) :
    CondIndepFun (envAlg S) envAlg_le (fun p : PooledOne S => markedObs A p.1) (rowsOut A)
      Q.lawOne := by
  rw [condIndepFun_iff_condIndep]
  refine condIndep_of_condIndep_of_le_left (Q.condIndep_markedLatentObs_rowsOut A) ?_
  exact Measurable.comap_le (measurable_fst.comp (comap_measurable (markedLatentObs A)))

end InfiniteRelExchangeableLaw

end RelSignature
