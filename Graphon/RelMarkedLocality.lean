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

**Joint-law locality.** The environment and the rows of `A` are read off the marked observation
at `A` and the latent array, so weak union moves them into the conditioning: given the
environment and the rows of `A`, the rows outside `A` add nothing to the full induced original
structure on `A`. With `ν` the joint law of (environment, rows), `Γ` the conditional law of the
original structure given (environment, rows), and `γ_A` the conditional law of the induced
structure on `A` given the environment and the rows of `A`, the joint laws through `Γ` and
through `γ_A` are exact, and `Γ(e, r)` read on `A` is `γ_A(e, r|_A)` for `ν`-almost every
`(e, r)`. The environment stays in both kernels; nothing here removes it, and nothing assumes that
the rows recover the structure.
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

/-! ### The induced observation and the restriction of the rows -/

/-- The full induced original structure on `A`, as an observation on the coupling space. -/
def inducedObs (A : Finset (RowIndex S)) : PooledOne S → InducedSpace (S := S) A :=
  fun p => inducedMap A (restrictOriginal S p.1)

theorem measurable_inducedObs (A : Finset (RowIndex S)) : Measurable (inducedObs (S := S) A) :=
  (measurable_inducedMap A).comp (measurable_restrictOriginal.comp measurable_fst)

/-- Keep the environment and the rows of the vertices of `A`. -/
def restrictEnvRows (A : Finset (RowIndex S)) :
    (RelStructure S (Vinfinite S) × PooledRankLatentSpace S 1) ×
        (∀ v : RowIndex S, MarkedSpace (S := S) {v}) →
      (RelStructure S (Vinfinite S) × PooledRankLatentSpace S 1) ×
        (∀ v : A, MarkedSpace (S := S) {v.1}) :=
  fun x => (x.1, A.restrict x.2)

theorem measurable_restrictEnvRows (A : Finset (RowIndex S)) :
    Measurable (restrictEnvRows (S := S) A) :=
  measurable_fst.prodMk ((Finset.measurable_restrict A).comp measurable_snd)

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

/-! ### Joint-law locality -/

/-- **The joint law `ν` of (environment, rows).** -/
noncomputable abbrev PooledRankExtension.envRowsLaw :
    Measure ((RelStructure S (Vinfinite S) × PooledRankLatentSpace S 1) ×
      (∀ v : RowIndex S, MarkedSpace (S := S) {v})) :=
  Q.lawOne.map fun p => (envObs p, rowsObs p)

/-- **The kernel `Γ`**: the conditional law of the original structure given (environment,
rows). -/
noncomputable def PooledRankExtension.structureRowsKernel :
    Kernel ((RelStructure S (Vinfinite S) × PooledRankLatentSpace S 1) ×
      (∀ v : RowIndex S, MarkedSpace (S := S) {v})) (RelStructure S (Vinfinite S)) :=
  condDistrib (fun p : PooledOne S => restrictOriginal S p.1) (fun p => (envObs p, rowsObs p))
    Q.lawOne

instance : IsMarkovKernel Q.structureRowsKernel := by
  unfold PooledRankExtension.structureRowsKernel
  infer_instance

/-- **The local kernel `γ_A`**: the conditional law of the full induced original structure on
`A` given the environment and the rows of the vertices of `A`. -/
noncomputable def PooledRankExtension.localKernel (A : Finset (RowIndex S)) :
    Kernel ((RelStructure S (Vinfinite S) × PooledRankLatentSpace S 1) ×
      (∀ v : A, MarkedSpace (S := S) {v.1})) (InducedSpace (S := S) A) :=
  condDistrib (inducedObs A) (fun p => (envObs p, A.restrict (rowsObs p))) Q.lawOne

instance (A : Finset (RowIndex S)) : IsMarkovKernel (Q.localKernel A) := by
  unfold PooledRankExtension.localKernel
  infer_instance

/-- **The exact joint law through `Γ`.** -/
theorem PooledRankExtension.map_envRows_restrictOriginal_eq_compProd :
    Q.lawOne.map (fun p => ((envObs p, rowsObs p), restrictOriginal S p.1)) =
      Q.envRowsLaw ⊗ₘ Q.structureRowsKernel :=
  (compProd_map_condDistrib (measurable_restrictOriginal.comp measurable_fst).aemeasurable).symm

/-- **Outside rows add nothing to the induced structure on `A`, given the environment and the
rows of `A`**: weak union applied to the outside-row separation, the environment and the rows of
`A` being read off the marked observation at `A` and the latent array. -/
theorem PooledRankExtension.condIndep_rowsOut_inducedObs (A : Finset (RowIndex S)) :
    CondIndep (MeasurableSpace.comap (fun p => (envObs p, A.restrict (rowsObs p))) inferInstance)
      (MeasurableSpace.comap (rowsOut A) inferInstance)
      (MeasurableSpace.comap (inducedObs A) inferInstance)
      (measurable_envObs.prodMk ((Finset.measurable_restrict A).comp measurable_rowsObs)).comap_le
      Q.lawOne := by
  have hk : Measurable fun p : PooledOne S => (envObs p, A.restrict (rowsObs p)) :=
    measurable_envObs.prodMk ((Finset.measurable_restrict A).comp measurable_rowsObs)
  have hmarked : Measurable[MeasurableSpace.comap (markedLatentObs A) inferInstance]
      (markedLatentObs (S := S) A) := comap_measurable _
  have hind : MeasurableSpace.comap (inducedObs (S := S) A) inferInstance ≤
      MeasurableSpace.comap (markedLatentObs A) inferInstance :=
    Measurable.comap_le (f := inducedObs A)
      ((measurable_markedToInduced A).comp (measurable_fst.comp hmarked))
  have henv : MeasurableSpace.comap (fun p : PooledOne S => (envObs p, A.restrict (rowsObs p)))
      inferInstance ≤ MeasurableSpace.comap (markedLatentObs A) inferInstance :=
    Measurable.comap_le (f := fun p : PooledOne S => (envObs p, A.restrict (rowsObs p)))
      ((((measurable_markedToSpare A).comp (measurable_fst.comp hmarked)).prodMk
        (measurable_snd.comp hmarked)).prodMk
        ((measurable_markedToRows A).comp (measurable_fst.comp hmarked)))
  exact condIndep_weak_union envAlg_le (measurable_rowsOut A).comap_le
    (measurable_inducedObs A).comap_le hk.comap_le
    (Measurable.comap_le (f := envObs) (measurable_fst.comp (comap_measurable _)))
    (condIndep_of_condIndep_of_le_right (Q.condIndep_markedLatentObs_rowsOut A).symm
      (sup_le hind henv))

/-- **Locality in the split observation.** Conditioning the induced structure on `A` on the
environment, the rows of `A`, and the rows outside `A` is conditioning it on the environment and
the rows of `A`, almost everywhere under the law of the split observation. -/
theorem PooledRankExtension.condDistrib_inducedObs_split_ae_eq (A : Finset (RowIndex S)) :
    condDistrib (inducedObs A)
        (fun p => ((envObs p, A.restrict (rowsObs p)), rowsOut A p)) Q.lawOne
      =ᵐ[Q.lawOne.map fun p => ((envObs p, A.restrict (rowsObs p)), rowsOut A p)]
        (Q.localKernel A).prodMkRight _ := by
  have hk : Measurable fun p : PooledOne S => (envObs p, A.restrict (rowsObs p)) :=
    measurable_envObs.prodMk ((Finset.measurable_restrict A).comp measurable_rowsObs)
  refine (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight (measurable_inducedObs A)
    (measurable_rowsOut A) hk).mp ?_
  rw [condIndepFun_iff_condIndep]
  exact Q.condIndep_rowsOut_inducedObs A

/-- **Joint-law locality, exactly.** The joint law of (environment, rows) and the full induced
original structure on `A` is `ν` composed with the local kernel, read through the environment and
the rows of `A`. -/
theorem PooledRankExtension.map_envRows_inducedObs_eq_compProd (A : Finset (RowIndex S)) :
    Q.lawOne.map (fun p => ((envObs p, rowsObs p), inducedObs A p)) =
      Q.envRowsLaw ⊗ₘ
        (Q.localKernel A).comap (restrictEnvRows A) (measurable_restrictEnvRows A) := by
  classical
  set join := (MeasurableEquiv.piEquivPiSubtypeProd
    (fun v : RowIndex S => MarkedSpace (S := S) {v}) (· ∈ A)).symm with hjoin
  set ψ : ((RelStructure S (Vinfinite S) × PooledRankLatentSpace S 1) ×
      (∀ v : A, MarkedSpace (S := S) {v.1})) × (∀ v : {v : RowIndex S // v ∉ A},
        MarkedSpace (S := S) {v.1}) →
      (RelStructure S (Vinfinite S) × PooledRankLatentSpace S 1) ×
        (∀ v : RowIndex S, MarkedSpace (S := S) {v}) :=
    fun x => (x.1.1, join (x.1.2, x.2)) with hψ
  have hψm : Measurable ψ :=
    measurable_fst.fst.prodMk (join.measurable.comp (measurable_fst.snd.prodMk measurable_snd))
  have hk : Measurable fun p : PooledOne S =>
      ((envObs p, A.restrict (rowsObs p)), rowsOut A p) :=
    (measurable_envObs.prodMk ((Finset.measurable_restrict A).comp measurable_rowsObs)).prodMk
      (measurable_rowsOut A)
  -- the split observation recombines to (environment, rows)
  have hψk : ψ ∘ (fun p : PooledOne S => ((envObs p, A.restrict (rowsObs p)), rowsOut A p)) =
      fun p => (envObs p, rowsObs p) := by
    funext p
    exact Prod.ext rfl (join.apply_symm_apply (rowsObs p))
  -- the local kernel, pulled back along the recombination, ignores the outside rows
  have hcomap : (Q.localKernel A).prodMkRight (∀ v : {v : RowIndex S // v ∉ A},
      MarkedSpace (S := S) {v.1}) =
      ((Q.localKernel A).comap (restrictEnvRows A) (measurable_restrictEnvRows A)).comap ψ hψm := by
    ext x : 1
    rw [Kernel.prodMkRight_apply, Kernel.comap_apply, Kernel.comap_apply]
    congr 1
    refine Prod.ext rfl (funext fun v => ?_)
    show x.1.2 v = join (x.1.2, x.2) v.1
    rw [hjoin, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
    dsimp only
    rw [dif_pos v.2]
  calc Q.lawOne.map (fun p => ((envObs p, rowsObs p), inducedObs A p))
      = (Q.lawOne.map fun p => (((envObs p, A.restrict (rowsObs p)), rowsOut A p),
          inducedObs A p)).map (Prod.map ψ id) := by
        rw [Measure.map_map (hψm.prodMap measurable_id) (hk.prodMk (measurable_inducedObs A))]
        congr 1
        funext p
        exact Prod.ext (congrFun hψk p).symm rfl
    _ = ((Q.lawOne.map fun p => ((envObs p, A.restrict (rowsObs p)), rowsOut A p)) ⊗ₘ
          (Q.localKernel A).prodMkRight _).map (Prod.map ψ id) := by
        rw [← Measure.compProd_congr (Q.condDistrib_inducedObs_split_ae_eq A),
          compProd_map_condDistrib (measurable_inducedObs A).aemeasurable]
    _ = (Q.lawOne.map fun p => ((envObs p, A.restrict (rowsObs p)), rowsOut A p)).map ψ ⊗ₘ
          (Q.localKernel A).comap (restrictEnvRows A) (measurable_restrictEnvRows A) := by
        rw [hcomap]
        exact Measure.map_prodMap_compProd_comap _ hψm _
    _ = Q.envRowsLaw ⊗ₘ
          (Q.localKernel A).comap (restrictEnvRows A) (measurable_restrictEnvRows A) := by
        rw [Measure.map_map hψm hk, hψk]

/-- **Joint-law locality, as a kernel comparison.** For `ν`-almost every (environment, rows),
the conditional law of the original structure, read on `A`, is the local kernel at the
environment and the rows of `A`. -/
theorem PooledRankExtension.structureRowsKernel_map_inducedMap_ae_eq (A : Finset (RowIndex S)) :
    ∀ᵐ x ∂Q.envRowsLaw,
      (Q.structureRowsKernel x).map (inducedMap A) = Q.localKernel A (x.1, A.restrict x.2) := by
  have h1 := condDistrib_comp (μ := Q.lawOne) (mβ := Prod.instMeasurableSpace)
    (fun p => (envObs p, rowsObs p))
    (measurable_restrictOriginal.comp measurable_fst).aemeasurable (measurable_inducedMap A)
  have h2 := condDistrib_ae_eq_of_measure_eq_compProd (μ := Q.lawOne)
    (fun p => (envObs p, rowsObs p)) (measurable_inducedObs A).aemeasurable
    (Q.map_envRows_inducedObs_eq_compProd A)
  filter_upwards [h1, h2] with x hx1 hx2
  rw [← Kernel.map_apply _ (measurable_inducedMap A)]
  exact hx1.symm.trans hx2

end InfiniteRelExchangeableLaw

end RelSignature
