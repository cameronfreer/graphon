/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelMarkedRowIndependence

/-!
# Rank one: the conditional product law of the marked rows

The finite-family identity for row cylinders extends, through the generating π-systems of the
marked observations, to mutual conditional independence of the whole family of marked rows
given the environment. Naming the environment marginal, the conditional row kernels and the
conditional kernel of the whole row family, the conditional kernel of the family is the product
of the row kernels for almost every environment, an equality of measures obtained on one conull
set from a countable determining family of Boolean-coordinate cylinders, and the joint law of
(environment, rows) disintegrates exactly over the environment marginal.

This describes the conditional law of the rows alone. It says nothing about the joint
conditional law of the original structure together with the rows.
-/

universe u

open MeasureTheory ProbabilityTheory

namespace RelSignature

variable {S : RelSignature.{u}}

/-! ### The rows as observations -/

/-- The tagged original vertices, the index set of the rows. -/
abbrev RowIndex (S : RelSignature.{u}) := Σ s : S.Srt, Vinfinite S s

/-- The marked row of `v`, as an observation on the coupling space. -/
def rowObs (v : RowIndex S) : PooledOne S → MarkedSpace (S := S) {v} :=
  fun p => markedObs {v} p.1

theorem measurable_rowObs (v : RowIndex S) : Measurable (rowObs (S := S) v) :=
  (measurable_markedObs {v}).comp measurable_fst

/-- The whole family of marked rows. -/
def rowsObs : PooledOne S → ∀ v : RowIndex S, MarkedSpace (S := S) {v} :=
  fun p v => rowObs v p

theorem measurable_rowsObs : Measurable (rowsObs (S := S)) :=
  measurable_pi_lambda _ fun v => measurable_rowObs v

theorem rowObs_preimage_cylinder (v : RowIndex S) (t : Finset (MarkedCoord (S := S) {v}))
    (T : Set (t → Bool)) :
    rowObs v ⁻¹' (cylinder t T : Set (MarkedSpace (S := S) {v})) = rowEvent v t T := rfl

/-- The generating π-system of a row: the pullbacks of the measurable cylinders. -/
def rowCylinders (v : RowIndex S) : Set (Set (PooledOne S)) :=
  Set.preimage (rowObs v) '' measurableCylinders fun _ : MarkedCoord (S := S) {v} => Bool

theorem isPiSystem_rowCylinders (v : RowIndex S) : IsPiSystem (rowCylinders (S := S) v) :=
  isPiSystem_measurableCylinders.comap _

theorem comap_rowObs_eq_generateFrom (v : RowIndex S) :
    MeasurableSpace.comap (rowObs (S := S) v) inferInstance =
      MeasurableSpace.generateFrom (rowCylinders v) := by
  rw [rowCylinders, ← MeasurableSpace.comap_generateFrom, generateFrom_measurableCylinders]

theorem exists_rowEvent_of_mem_rowCylinders {v : RowIndex S} {H : Set (PooledOne S)}
    (hH : H ∈ rowCylinders (S := S) v) :
    ∃ (t : Finset (MarkedCoord (S := S) {v})) (T : Set (t → Bool)),
      MeasurableSet T ∧ H = rowEvent v t T := by
  obtain ⟨C, hC, rfl⟩ := hH
  obtain ⟨t, T, hT, rfl⟩ := (mem_measurableCylinders _).mp hC
  exact ⟨t, T, hT, rfl⟩

/-! ### The countable determining family -/

/-- A Boolean-coordinate cylinder of the row family: finitely many marked coordinates, at
finitely many vertices, with prescribed values. -/
private def rowsCylinder (T : List ((Σ v : RowIndex S, MarkedCoord (S := S) {v}) × Bool)) :
    Set (∀ v : RowIndex S, MarkedSpace (S := S) {v}) :=
  {f | ∀ x ∈ T, f x.1.1 x.1.2 = x.2}

/-- The coordinates of a cylinder at the vertex `v`, as a cylinder of the row of `v`. -/
private def rowsCylinderAt (T : List ((Σ v : RowIndex S, MarkedCoord (S := S) {v}) × Bool))
    (v : RowIndex S) : Set (MarkedSpace (S := S) {v}) :=
  {y | ∀ x ∈ T, ∀ h : x.1.1 = v, y ⟨x.1.2.1, h ▸ x.1.2.2⟩ = x.2}

open scoped Classical in
/-- The vertices of a cylinder's coordinates. -/
private noncomputable def rowsAnchors
    (T : List ((Σ v : RowIndex S, MarkedCoord (S := S) {v}) × Bool)) :
    Finset (RowIndex S) :=
  (T.map fun x => x.1.1).toFinset

private theorem measurableSet_rowsCylinder
    (T : List ((Σ v : RowIndex S, MarkedCoord (S := S) {v}) × Bool)) :
    MeasurableSet (rowsCylinder T) := by
  have h : rowsCylinder T = ⋂ x ∈ T,
      (fun f : ∀ v : RowIndex S, MarkedSpace (S := S) {v} => f x.1.1 x.1.2) ⁻¹' {x.2} := by
    ext f
    simp [rowsCylinder]
  rw [h]
  exact Set.Finite.measurableSet_biInter (List.finite_toSet T) fun x _ =>
    ((measurable_pi_apply x.1.2).comp (measurable_pi_apply x.1.1)) (measurableSet_singleton x.2)

private theorem measurableSet_rowsCylinderAt
    (T : List ((Σ v : RowIndex S, MarkedCoord (S := S) {v}) × Bool)) (v : RowIndex S) :
    MeasurableSet (rowsCylinderAt T v) := by
  have h : rowsCylinderAt T v = ⋂ x ∈ T, ⋂ h : x.1.1 = v,
      (fun y : MarkedSpace (S := S) {v} => y ⟨x.1.2.1, h ▸ x.1.2.2⟩) ⁻¹' {x.2} := by
    ext y
    simp [rowsCylinderAt]
  rw [h]
  exact Set.Finite.measurableSet_biInter (List.finite_toSet T) fun x _ =>
    MeasurableSet.iInter fun _ => measurable_pi_apply _ (measurableSet_singleton x.2)

private theorem rowsCylinder_append
    (T₁ T₂ : List ((Σ v : RowIndex S, MarkedCoord (S := S) {v}) × Bool)) :
    rowsCylinder (T₁ ++ T₂) = rowsCylinder T₁ ∩ rowsCylinder T₂ := by
  ext f
  simp [rowsCylinder, or_imp, forall_and]

private theorem isPiSystem_rowsCylinder : IsPiSystem (Set.range (rowsCylinder (S := S))) := by
  rintro _ ⟨T₁, rfl⟩ _ ⟨T₂, rfl⟩ -
  exact ⟨T₁ ++ T₂, rowsCylinder_append T₁ T₂⟩

/-- The Boolean-coordinate cylinders generate the σ-algebra of the row family. -/
private theorem generateFrom_rowsCylinder :
    MeasurableSpace.generateFrom (Set.range (rowsCylinder (S := S))) =
      (inferInstance : MeasurableSpace (∀ v : RowIndex S, MarkedSpace (S := S) {v})) := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) ?_
  · rintro _ ⟨T, rfl⟩
    exact measurableSet_rowsCylinder T
  · refine iSup_le fun v => ?_
    show MeasurableSpace.comap (fun f : ∀ v : RowIndex S, MarkedSpace (S := S) {v} => f v)
      (MeasurableSpace.pi : MeasurableSpace (MarkedSpace (S := S) {v})) ≤ _
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun c => ?_
    rw [MeasurableSpace.comap_comp]
    refine Measurable.comap_le (measurable_to_bool ?_)
    refine MeasurableSpace.measurableSet_generateFrom ⟨[(⟨v, c⟩, true)], ?_⟩
    ext f
    simp [rowsCylinder]

/-- A cylinder is the finite product of its cylinders at the anchors. -/
private theorem rowsCylinder_eq_pi
    (T : List ((Σ v : RowIndex S, MarkedCoord (S := S) {v}) × Bool)) :
    rowsCylinder T = Set.pi (rowsAnchors T) (rowsCylinderAt T) := by
  classical
  ext f
  simp only [rowsCylinder, Set.mem_setOf_eq, Set.mem_pi, rowsCylinderAt, rowsAnchors,
    Finset.mem_coe, List.mem_toFinset, List.mem_map]
  constructor
  · rintro h v - x hx rfl
    exact h x hx
  · intro h x hx
    exact h x.1.1 ⟨x, hx, rfl⟩ x hx rfl

/-- The preimage of a cylinder under the row family is the intersection of the row preimages. -/
private theorem rowsObs_preimage_rowsCylinder
    (T : List ((Σ v : RowIndex S, MarkedCoord (S := S) {v}) × Bool)) :
    rowsObs ⁻¹' rowsCylinder T = ⋂ v ∈ rowsAnchors T, rowObs v ⁻¹' rowsCylinderAt T v := by
  rw [rowsCylinder_eq_pi]
  ext p
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_iInter, Finset.mem_coe]
  exact Iff.rfl

namespace InfiniteRelExchangeableLaw

variable {M : InfiniteRelExchangeableLaw S} [Countable S.Srt] [Countable S.Rel]
  {C : M.RankRepresentation 1} (Q : PooledRankExtension C)

/-! ### The product identity for rows given as cylinder pullbacks -/

/-- **The finite-family product identity, for rows given as cylinder pullbacks**: a direct
corollary of the identity for row cylinders, after choosing a cylinder presentation of each tested
event. -/
theorem PooledRankExtension.condExp_iInter_eq_prod_of_rowCylinders (F : Finset (RowIndex S))
    {H : RowIndex S → Set (PooledOne S)} (hH : ∀ u ∈ F, H u ∈ rowCylinders (S := S) u) :
    Q.lawOne⟦⋂ u ∈ F, H u | envAlg S⟧ =ᵐ[Q.lawOne] ∏ u ∈ F, Q.lawOne⟦H u | envAlg S⟧ := by
  classical
  have hpres : ∀ u : RowIndex S,
      ∃ q : Σ t : Finset (MarkedCoord (S := S) {u}), Set (t → Bool),
        MeasurableSet q.2 ∧ (u ∈ F → H u = rowEvent u q.1 q.2) := by
    intro u
    by_cases hu : u ∈ F
    · obtain ⟨t, T, hT, hHu⟩ := exists_rowEvent_of_mem_rowCylinders (hH u hu)
      exact ⟨⟨t, T⟩, hT, fun _ => hHu⟩
    · exact ⟨⟨∅, Set.univ⟩, MeasurableSet.univ, fun h => absurd h hu⟩
  choose pres hpres using hpres
  have h := Q.condExp_iInter_rowEvent_eq_prod (fun u : RowIndex S => u) Function.injective_id
    (fun u => (pres u).1) (fun u => (pres u).2) (fun u => (hpres u).1) F
  have h1 : (⋂ u ∈ F, H u) = ⋂ u ∈ F, rowEvent u (pres u).1 (pres u).2 :=
    Set.iInter₂_congr fun u hu => (hpres u).2 hu
  have h2 : (∏ u ∈ F, Q.lawOne⟦H u | envAlg S⟧) =
      ∏ u ∈ F, Q.lawOne⟦rowEvent u (pres u).1 (pres u).2 | envAlg S⟧ :=
    Finset.prod_congr rfl fun u hu => by rw [(hpres u).2 hu]
  rw [h1, h2]
  exact h

/-- **Mutual conditional independence of the marked rows given the environment, at rank one.** -/
theorem PooledRankExtension.iCondIndepFun_rowObs :
    iCondIndepFun (envAlg S) envAlg_le (fun v : RowIndex S => rowObs (S := S) v) Q.lawOne := by
  rw [iCondIndepFun_iff_iCondIndep]
  refine iCondIndepSets.iCondIndep _ (fun v => (measurable_rowObs v).comap_le) rowCylinders
    isPiSystem_rowCylinders comap_rowObs_eq_generateFrom ?_
  have hmeas : ∀ (v : RowIndex S) (H : Set (PooledOne S)), H ∈ rowCylinders (S := S) v →
      MeasurableSet H := by
    intro v H hH
    obtain ⟨t, T, hT, rfl⟩ := exists_rowEvent_of_mem_rowCylinders hH
    exact measurableSet_rowEvent v t T hT
  rw [iCondIndepSets_iff _ _ _ hmeas]
  intro F H hH
  exact Q.condExp_iInter_eq_prod_of_rowCylinders F hH

/-! ### The named kernels -/

/-- The environment marginal `ν_E`. -/
noncomputable def PooledRankExtension.envLaw :
    Measure (RelStructure S (Vinfinite S) × PooledRankLatentSpace S 1) :=
  Q.lawOne.map envObs

instance : IsProbabilityMeasure Q.envLaw :=
  Measure.isProbabilityMeasure_map measurable_envObs.aemeasurable

/-- The conditional row kernel `k_v`: the conditional law of the marked row of `v` given the
environment. -/
noncomputable def PooledRankExtension.rowKernel (v : RowIndex S) :
    Kernel (RelStructure S (Vinfinite S) × PooledRankLatentSpace S 1) (MarkedSpace (S := S) {v}) :=
  condDistrib (rowObs v) envObs Q.lawOne

/-- The conditional kernel `κ` of the whole row family given the environment. -/
noncomputable def PooledRankExtension.rowsKernel :
    Kernel (RelStructure S (Vinfinite S) × PooledRankLatentSpace S 1)
      (∀ v : RowIndex S, MarkedSpace (S := S) {v}) :=
  condDistrib rowsObs envObs Q.lawOne

instance (v : RowIndex S) : IsMarkovKernel (Q.rowKernel v) := by
  unfold PooledRankExtension.rowKernel; infer_instance

instance : IsMarkovKernel Q.rowsKernel := by
  unfold PooledRankExtension.rowsKernel; infer_instance

/-! ### The conditional product law -/

/-- **The cylinder identity**: for almost every environment, the conditional kernel of the row
family gives a Boolean-coordinate cylinder the product of the row kernels' masses. -/
private theorem PooledRankExtension.ae_rowsKernel_rowsCylinder
    (T : List ((Σ v : RowIndex S, MarkedCoord (S := S) {v}) × Bool)) :
    ∀ᵐ e ∂Q.envLaw, Q.rowsKernel e (rowsCylinder T) =
      ∏ v ∈ rowsAnchors T, Q.rowKernel v e (rowsCylinderAt T v) := by
  have hcyl := measurableSet_rowsCylinder (S := S) T
  have hat : ∀ v, MeasurableSet (rowsCylinderAt T v) := measurableSet_rowsCylinderAt T
  have h1 : (fun p => (Q.rowsKernel (envObs p)).real (rowsCylinder T)) =ᵐ[Q.lawOne]
      Q.lawOne⟦rowsObs ⁻¹' rowsCylinder T | envAlg S⟧ :=
    condDistrib_ae_eq_condExp measurable_envObs measurable_rowsObs hcyl
  rw [rowsObs_preimage_rowsCylinder] at h1
  have h3 := (iCondIndepFun_iff_condExp_inter_preimage_eq_mul _ _
    (fun v : RowIndex S => measurable_rowObs (S := S) v)).mp Q.iCondIndepFun_rowObs
    (rowsAnchors T) (sets := fun v => rowsCylinderAt T v) (fun v _ => hat v)
  have h4 : ∀ v : RowIndex S,
      Q.lawOne⟦rowObs v ⁻¹' rowsCylinderAt T v | envAlg S⟧ =ᵐ[Q.lawOne]
        fun p => (Q.rowKernel v (envObs p)).real (rowsCylinderAt T v) :=
    fun v => (condDistrib_ae_eq_condExp measurable_envObs (measurable_rowObs v) (hat v)).symm
  have hreal : ∀ᵐ p ∂Q.lawOne,
      (Q.rowsKernel (envObs p)).real (rowsCylinder T) =
        ∏ v ∈ rowsAnchors T, (Q.rowKernel v (envObs p)).real (rowsCylinderAt T v) := by
    filter_upwards [h1, h3, (Filter.eventually_all_finset (rowsAnchors T)).mpr
      fun v _ => h4 v] with p hp1 hp3 hp4
    rw [hp1, hp3, Finset.prod_apply]
    exact Finset.prod_congr rfl fun v hv => by rw [hp4 v hv]
  have hmeas : MeasurableSet {e : RelStructure S (Vinfinite S) × PooledRankLatentSpace S 1 |
      (Q.rowsKernel e).real (rowsCylinder T) =
        ∏ v ∈ rowsAnchors T, (Q.rowKernel v e).real (rowsCylinderAt T v)} := by
    refine measurableSet_eq_fun ?_ (Finset.measurable_prod _ fun v _ => ?_)
    · exact (Q.rowsKernel.measurable_coe hcyl).ennreal_toReal
    · exact ((Q.rowKernel v).measurable_coe (hat v)).ennreal_toReal
  have hlam := (ae_map_iff measurable_envObs.aemeasurable hmeas).mpr hreal
  rw [PooledRankExtension.envLaw]
  filter_upwards [hlam] with e he
  simp only [measureReal_def] at he
  rw [← ENNReal.toReal_prod] at he
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.prod_ne_top fun v _ => measure_ne_top _ _)).mp he

/-- **The conditional product law of the rows.** For `ν_E`-almost every environment `e`, the
conditional kernel of the row family at `e` **is** the product of the row kernels at `e`: an
equality of measures, obtained on one conull set from the countable family of
Boolean-coordinate cylinders by measure uniqueness. -/
theorem PooledRankExtension.rowsKernel_ae_eq_infinitePi :
    ∀ᵐ e ∂Q.envLaw, Q.rowsKernel e = Measure.infinitePi fun v : RowIndex S => Q.rowKernel v e := by
  have hall := ae_all_iff.mpr fun T => Q.ae_rowsKernel_rowsCylinder T
  filter_upwards [hall] with e he
  haveI : ∀ v : RowIndex S, IsProbabilityMeasure (Q.rowKernel v e) := fun v => inferInstance
  refine ext_of_generate_finite _ generateFrom_rowsCylinder.symm isPiSystem_rowsCylinder ?_ ?_
  · rintro _ ⟨T, rfl⟩
    rw [he T, rowsCylinder_eq_pi, Measure.infinitePi_pi (fun v => Q.rowKernel v e)
      fun v _ => measurableSet_rowsCylinderAt T v]
  · rw [measure_univ, measure_univ]

/-- **The exact disintegration of (environment, rows) over the environment marginal.** -/
theorem PooledRankExtension.map_envObs_rowsObs_eq_compProd :
    Q.lawOne.map (fun p => (envObs p, rowsObs p)) = Q.envLaw ⊗ₘ Q.rowsKernel :=
  (compProd_map_condDistrib measurable_rowsObs.aemeasurable).symm

/-- **The integrated product law on measurable rectangles**: the joint law of (environment, rows)
gives a rectangle the integral over the environment set of the product of the row kernels. -/
theorem PooledRankExtension.map_envObs_rowsObs_prod
    {D : Set (RelStructure S (Vinfinite S) × PooledRankLatentSpace S 1)} (hD : MeasurableSet D)
    {T : Set (∀ v : RowIndex S, MarkedSpace (S := S) {v})} (hT : MeasurableSet T) :
    Q.lawOne.map (fun p => (envObs p, rowsObs p)) (D ×ˢ T) =
      ∫⁻ e in D, Measure.infinitePi (fun v : RowIndex S => Q.rowKernel v e) T ∂Q.envLaw := by
  rw [Q.map_envObs_rowsObs_eq_compProd, Measure.compProd_apply_prod hD hT]
  refine setLIntegral_congr_fun_ae hD ?_
  filter_upwards [Q.rowsKernel_ae_eq_infinitePi] with e he _
  rw [he]

end InfiniteRelExchangeableLaw

end RelSignature
