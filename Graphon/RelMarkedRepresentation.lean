/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelPooledFixingSeam

/-!
# The marked representation of fixing events

Fix a pooled rank extension `Q` of a representation `C`. For a finite original vertex set `A`,
the **marked observation** at `A` reads the pooled structure at every coordinate whose support
lies in the original copy of `A` together with the whole spare copy. It is not invariant under
permutations of the spare vertices: it distinguishes the marks.

The **marked representation theorem** says that every fixing event at `A` of the original
structure is, modulo the pooled structure marginal, an event of the marked observation at `A`.
The proof is a finite-motion approximation. A fixing event is approximated in measure by
cylinders of the original structure. Each cylinder reads finitely many original vertices; the
boundary swap of those outside `A`, a finitely supported pooled involution fixing `A` pointwise,
moves them into spare positions, so the transported cylinder is an event of the marked
observation. The pooled seam
makes the fixing event almost surely invariant under that permutation, and pooled invariance
makes the permutation measure preserving, so the transported cylinder approximates the fixing
event exactly as well as the original one did. A conditional expectation onto the marked
σ-algebra then identifies the fixing event with a marked event almost surely.

The theorem needs neither admissibility nor any bound on the cardinality of `A`.
-/

universe u

open MeasureTheory
open scoped symmDiff

namespace RelSignature

variable {S : RelSignature.{u}}

/-! ### The marked observation -/

/-- The marked vertex set at an original finite set `A`: its original copy and every spare
vertex. -/
def markedSet (A : Finset (Σ s : S.Srt, Vinfinite S s)) : Set (Σ s : S.Srt, PoolVertex S s) :=
  {v | (∃ a, v.2 = Sum.inl a ∧ (⟨v.1, a⟩ : Σ s : S.Srt, Vinfinite S s) ∈ A) ∨ ∃ b, v.2 = Sum.inr b}

/-- Pooled coordinates whose support lies in the marked vertex set at `A`. -/
def MarkedCoord (A : Finset (Σ s : S.Srt, Vinfinite S s)) :=
  {c : RelCoord S (PoolVertex S) // ∀ v ∈ c.support, v ∈ markedSet A}

instance [Countable S.Rel] (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Countable (MarkedCoord (S := S) A) := by
  unfold MarkedCoord
  infer_instance

/-- The marked observation space at `A`. -/
abbrev MarkedSpace (A : Finset (Σ s : S.Srt, Vinfinite S s)) := MarkedCoord (S := S) A → Bool

/-- **The marked observation** at `A`: the pooled structure read on the marked coordinates. -/
def markedObs (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    RelStructure S (PoolVertex S) → MarkedSpace (S := S) A :=
  fun Y c => Y c.1

theorem measurable_markedObs (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measurable (markedObs (S := S) A) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-! ### The boundary swap pushes a finite original set out of `A` into the spare copy -/

theorem boundarySwap_eq_one_of_forall_notMem (W : Finset (Σ s : S.Srt, Vinfinite S s)) {s : S.Srt}
    (hs : ∀ a, (⟨s, a⟩ : Σ s : S.Srt, Vinfinite S s) ∉ W) : boundarySwap W s = 1 := by
  classical
  ext x
  rcases x with a | b
  · show swapHalvesFun W s (Sum.inl a) = Sum.inl a
    simp only [swapHalvesFun]
    exact if_neg (hs a)
  · show swapHalvesFun W s (Sum.inr b) = Sum.inr b
    simp only [swapHalvesFun]
    exact if_neg (hs b)

theorem boundarySwap_inl_mem_markedSet (W A : Finset (Σ s : S.Srt, Vinfinite S s)) (s : S.Srt)
    (a : Vinfinite S s) (h : (⟨s, a⟩ : Σ s : S.Srt, Vinfinite S s) ∈ W ∨
      (⟨s, a⟩ : Σ s : S.Srt, Vinfinite S s) ∈ A) :
    (⟨s, boundarySwap W s (Sum.inl a)⟩ : Σ s : S.Srt, PoolVertex S s) ∈ markedSet A := by
  classical
  show (⟨s, swapHalvesFun W s (Sum.inl a)⟩ : Σ s : S.Srt, PoolVertex S s) ∈ markedSet A
  simp only [swapHalvesFun]
  split_ifs with hW
  · exact Or.inr ⟨a, rfl⟩
  · exact Or.inl ⟨a, rfl, h.resolve_left hW⟩

theorem boundarySwap_fixes_of_disjoint (W A : Finset (Σ s : S.Srt, Vinfinite S s))
    (hWA : Disjoint W A) :
    ∀ v ∈ supportImage (fun s => originalVertex S s) A, boundarySwap W v.1 v.2 = v.2 := by
  classical
  intro v hv
  obtain ⟨⟨s, a⟩, ha, rfl⟩ := (mem_supportImage_iff _ _ _).mp hv
  show swapHalvesFun W s (Sum.inl a) = Sum.inl a
  simp only [swapHalvesFun]
  rw [if_neg]
  exact fun h => Finset.disjoint_left.mp hWA h ha

namespace InfiniteRelExchangeableLaw

variable {M : InfiniteRelExchangeableLaw S} {n : ℕ} [Countable S.Srt] [Countable S.Rel]
  {C : M.RankRepresentation n}

/-- The pooled structure marginal of a pooled extension. -/
noncomputable abbrev PooledRankExtension.structureLaw (Q : PooledRankExtension C) :
    Measure (RelStructure S (PoolVertex S)) :=
  (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)).map Prod.fst

instance (Q : PooledRankExtension C) : IsProbabilityMeasure Q.structureLaw :=
  Measure.isProbabilityMeasure_map measurable_fst.aemeasurable

/-- The original marginal of the pooled structure marginal is the law. -/
theorem PooledRankExtension.structureLaw_map_restrictOriginal (Q : PooledRankExtension C) :
    Q.structureLaw.map (restrictOriginal S) = (M.law : Measure (RelStructure S (Vinfinite S))) := by
  haveI := C.isProbabilityMeasure_P
  rw [PooledRankExtension.structureLaw, Measure.map_map measurable_restrictOriginal measurable_fst,
    ← C.map_fst, ← Q.map_restrictOriginal, Measure.map_map measurable_fst
    (measurable_restrictOriginal.prodMap (measurable_restrictOriginalLatents n))]
  rfl

/-- Every pooled permutation preserves the pooled structure marginal. -/
theorem PooledRankExtension.measurePreserving_relabel_structureLaw (Q : PooledRankExtension C)
    (ρ : ∀ s, Equiv.Perm (PoolVertex S s)) :
    MeasurePreserving (RelStructure.relabel ρ) Q.structureLaw Q.structureLaw := by
  refine ⟨measurable_relabel ρ, ?_⟩
  conv_rhs => rw [PooledRankExtension.structureLaw, ← Q.invariant ρ]
  rw [PooledRankExtension.structureLaw, Measure.map_map (measurable_relabel ρ) measurable_fst,
    Measure.map_map measurable_fst
      ((measurable_relabel ρ).prodMap (pooledRankLatentRelabel ρ n).measurable)]
  rfl

/-- **A fixing event is almost surely invariant under a pooled motion fixing `A` with finitely
many active sorts.** The motion may have infinite vertex support; only finitely many sorts may
move. -/
theorem PooledRankExtension.relabel_preimage_restrictOriginal_ae_eq (Q : PooledRankExtension C)
    {A : Finset (Σ s : S.Srt, Vinfinite S s)} {F : Set (RelStructure S (Vinfinite S))}
    (hF : MeasurableSet[RelStructure.fixingAlgebra A] F)
    {ρ : ∀ s, Equiv.Perm (PoolVertex S s)} (hρfin : ∃ T : Finset S.Srt, ∀ s, s ∉ T → ρ s = 1)
    (hρ : ∀ v ∈ supportImage (fun s => originalVertex S s) A, ρ v.1 v.2 = v.2) :
    RelStructure.relabel ρ ⁻¹' (restrictOriginal S ⁻¹' F) =ᵐ[Q.structureLaw]
      restrictOriginal S ⁻¹' F := by
  obtain ⟨Ê, hÊ, hae⟩ := Q.exists_pooledFiniteActiveFixingAlgebra_ae_eq hF
  have hinv := Q.relabel_preimage_ae_eq_of_pooledFiniteActiveFixingAlgebra hÊ hρfin hρ
  have hpull := (Q.measurePreserving_relabel_structureLaw ρ).quasiMeasurePreserving.preimage_ae_eq
    hae
  exact hpull.symm.trans (hinv.trans hae)

/-- The pooled coordinate map carrying an original coordinate through the push-out. -/
noncomputable def boundarySwapEmb (W : Finset (Σ s : S.Srt, Vinfinite S s)) (s : S.Srt) :
    Vinfinite S s ↪ PoolVertex S s :=
  (originalVertex S s).trans (boundarySwap W s).toEmbedding

omit [Countable S.Srt] [Countable S.Rel] in
open scoped Classical in
/-- **A cylinder of the original structure, pushed out of `A`, is a marked event.** -/
theorem exists_markedObs_preimage_eq_relabel_boundarySwap
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) (t : Finset (RelCoord S (Vinfinite S)))
    (T : Set (∀ _ : t, Bool)) (hT : MeasurableSet T) :
    ∃ D : Set (MarkedSpace (S := S) A), MeasurableSet D ∧
      markedObs A ⁻¹' D =
        RelStructure.relabel (boundarySwap ((t.biUnion fun c => c.support) \ A)) ⁻¹'
          (restrictOriginal S ⁻¹' (cylinder t T : Set (RelStructure S (Vinfinite S)))) := by
  set W : Finset (Σ s : S.Srt, Vinfinite S s) := (t.biUnion fun c => c.support) \ A with hW
  have hsupp : ∀ c : t, ∀ v ∈ (RelCoord.map (fun s => ⇑(boundarySwapEmb W s)) c.1).support,
      v ∈ markedSet A := by
    intro c v hv
    rw [← supportImage_support, mem_supportImage_iff] at hv
    obtain ⟨⟨s, a⟩, ha, rfl⟩ := hv
    refine boundarySwap_inl_mem_markedSet W A s a ?_
    by_cases hA : (⟨s, a⟩ : Σ s : S.Srt, Vinfinite S s) ∈ A
    · exact Or.inr hA
    · exact Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨c.1, c.2, ha⟩, hA⟩)
  refine ⟨(fun Z : MarkedSpace (S := S) A => fun c : t =>
    Z ⟨RelCoord.map (fun s => ⇑(boundarySwapEmb W s)) c.1, hsupp c⟩) ⁻¹' T,
    (measurable_pi_lambda _ fun _ => measurable_pi_apply _) hT, ?_⟩
  ext Y
  simp only [Set.mem_preimage, mem_cylinder]
  exact Iff.rfl

/-- The marked σ-algebra at `A` on the pooled structure space. -/
noncomputable abbrev markedAlg (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    MeasurableSpace (RelStructure S (PoolVertex S)) :=
  MeasurableSpace.comap (markedObs (S := S) A) inferInstance

/-- **Approximation of a fixing event by marked events.** -/
theorem PooledRankExtension.exists_markedAlg_symmDiff_lt (Q : PooledRankExtension C)
    {A : Finset (Σ s : S.Srt, Vinfinite S s)} {F : Set (RelStructure S (Vinfinite S))}
    (hF : MeasurableSet[RelStructure.fixingAlgebra A] F) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : Set (RelStructure S (PoolVertex S)), MeasurableSet[markedAlg A] D ∧
      Q.structureLaw ((restrictOriginal S ⁻¹' F) ∆ D) < ENNReal.ofReal ε := by
  classical
  have hFm : MeasurableSet F := RelStructure.fixingAlgebra_le A _ hF
  have hF'm : MeasurableSet (restrictOriginal S ⁻¹' F) := measurable_restrictOriginal hFm
  have halg : IsSetAlgebra (measurableCylinders fun _ : RelCoord S (Vinfinite S) => Bool) :=
    ⟨empty_mem_measurableCylinders _, fun _ hs => compl_mem_measurableCylinders hs,
      fun _ _ hs ht => union_mem_measurableCylinders hs ht⟩
  have hdense : (M.law : Measure (RelStructure S (Vinfinite S))).MeasureDense
      (measurableCylinders fun _ : RelCoord S (Vinfinite S) => Bool) :=
    Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite (μ := M.law) halg
      generateFrom_measurableCylinders.symm
  obtain ⟨Cyl, hCyl, hlt⟩ := hdense.approx F hFm (measure_ne_top _ _) ε hε
  obtain ⟨t, T, hT, rfl⟩ := (mem_measurableCylinders _).mp hCyl
  set W : Finset (Σ s : S.Srt, Vinfinite S s) := (t.biUnion fun c => c.support) \ A with hW
  obtain ⟨D, hD, hDeq⟩ := exists_markedObs_preimage_eq_relabel_boundarySwap A t T hT
  refine ⟨markedObs A ⁻¹' D, ⟨D, hD, rfl⟩, ?_⟩
  rw [hDeq]
  have hρfin : ∃ Tf : Finset S.Srt, ∀ s, s ∉ Tf → boundarySwap W s = 1 :=
    ⟨W.image Sigma.fst, fun s hs => boundarySwap_eq_one_of_forall_notMem W fun a ha =>
      hs (Finset.mem_image.mpr ⟨_, ha, rfl⟩)⟩
  have hρ := boundarySwap_fixes_of_disjoint W A Finset.sdiff_disjoint
  have hinv := Q.relabel_preimage_restrictOriginal_ae_eq hF hρfin hρ
  have hmp := Q.measurePreserving_relabel_structureLaw (boundarySwap W)
  have hcylm : MeasurableSet
      (restrictOriginal S ⁻¹' (cylinder t T : Set (RelStructure S (Vinfinite S)))) :=
    measurable_restrictOriginal hT.cylinder
  calc Q.structureLaw ((restrictOriginal S ⁻¹' F) ∆ (RelStructure.relabel (boundarySwap W) ⁻¹'
          (restrictOriginal S ⁻¹' (cylinder t T : Set (RelStructure S (Vinfinite S))))))
      = Q.structureLaw ((RelStructure.relabel (boundarySwap W) ⁻¹' (restrictOriginal S ⁻¹' F)) ∆
          (RelStructure.relabel (boundarySwap W) ⁻¹'
            (restrictOriginal S ⁻¹' (cylinder t T : Set (RelStructure S (Vinfinite S)))))) :=
        measure_congr (ae_eq_set_symmDiff hinv.symm Filter.EventuallyEq.rfl)
    _ = Q.structureLaw (RelStructure.relabel (boundarySwap W) ⁻¹'
          ((restrictOriginal S ⁻¹' F) ∆
            (restrictOriginal S ⁻¹' (cylinder t T : Set (RelStructure S (Vinfinite S)))))) := by
        rw [Set.preimage_symmDiff]
    _ = Q.structureLaw ((restrictOriginal S ⁻¹' F) ∆
          (restrictOriginal S ⁻¹' (cylinder t T : Set (RelStructure S (Vinfinite S))))) :=
        hmp.measure_preimage (hF'm.symmDiff hcylm).nullMeasurableSet
    _ = (M.law : Measure (RelStructure S (Vinfinite S)))
          (F ∆ (cylinder t T : Set (RelStructure S (Vinfinite S)))) := by
        rw [← Q.structureLaw_map_restrictOriginal, Measure.map_apply measurable_restrictOriginal
          (hFm.symmDiff hT.cylinder), Set.preimage_symmDiff]
    _ < ENNReal.ofReal ε := hlt

/-- **The marked representation theorem.** Every fixing event at a finite original set `A` is,
modulo the pooled structure marginal, an event of the marked observation at `A`. -/
theorem PooledRankExtension.exists_markedObs_ae_eq (Q : PooledRankExtension C)
    {A : Finset (Σ s : S.Srt, Vinfinite S s)} {F : Set (RelStructure S (Vinfinite S))}
    (hF : MeasurableSet[RelStructure.fixingAlgebra A] F) :
    ∃ D : Set (MarkedSpace (S := S) A), MeasurableSet D ∧
      markedObs A ⁻¹' D =ᵐ[Q.structureLaw] restrictOriginal S ⁻¹' F := by
  classical
  have hF'm : MeasurableSet (restrictOriginal S ⁻¹' F) :=
    measurable_restrictOriginal (RelStructure.fixingAlgebra_le A _ hF)
  have hmM : markedAlg A ≤ (inferInstance : MeasurableSpace (RelStructure S (PoolVertex S))) :=
    (measurable_markedObs A).comap_le
  set f : RelStructure S (PoolVertex S) → ℝ :=
    (restrictOriginal S ⁻¹' F).indicator (fun _ => (1 : ℝ)) with hf
  have hfint : Integrable f Q.structureLaw := (integrable_const 1).indicator hF'm
  have hgm : StronglyMeasurable[markedAlg A] (Q.structureLaw[f | markedAlg A]) :=
    stronglyMeasurable_condExp
  -- the conditional expectation onto the marked σ-algebra is the indicator
  have hae : Q.structureLaw[f | markedAlg A] =ᵐ[Q.structureLaw] f := by
    have hzero : eLpNorm (f - Q.structureLaw[f | markedAlg A]) 1 Q.structureLaw = 0 := by
      refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
      obtain ⟨D, hD, hlt⟩ := Q.exists_markedAlg_symmDiff_lt hF (ε := (ε : ℝ) / 2) (by positivity)
      have hDm : MeasurableSet D := hmM _ hD
      set d : RelStructure S (PoolVertex S) → ℝ := D.indicator (fun _ => (1 : ℝ)) with hd
      have hdint : Integrable d Q.structureLaw := (integrable_const 1).indicator hDm
      have hdsm : StronglyMeasurable[markedAlg A] d := by
        letI : MeasurableSpace (RelStructure S (PoolVertex S)) := markedAlg A
        exact stronglyMeasurable_const.indicator hD
      have hdg : d - Q.structureLaw[f | markedAlg A] =ᵐ[Q.structureLaw]
          Q.structureLaw[d - f | markedAlg A] := by
        refine ((condExp_sub hdint hfint _).trans ?_).symm
        exact (Filter.EventuallyEq.of_eq
          (condExp_of_stronglyMeasurable hmM hdsm hdint)).sub Filter.EventuallyEq.rfl
      have h1 : eLpNorm (f - d) 1 Q.structureLaw =
          Q.structureLaw ((restrictOriginal S ⁻¹' F) ∆ D) := by
        rw [hf, hd, eLpNorm_indicator_sub_indicator,
          eLpNorm_indicator_const (hF'm.symmDiff hDm) one_ne_zero ENNReal.one_ne_top]
        simp
      have h2 : eLpNorm (d - Q.structureLaw[f | markedAlg A]) 1 Q.structureLaw ≤
          Q.structureLaw ((restrictOriginal S ⁻¹' F) ∆ D) := by
        rw [eLpNorm_congr_ae hdg]
        refine (eLpNorm_condExp_le_eLpNorm _ le_rfl).trans (le_of_eq ?_)
        rw [hf, hd, eLpNorm_indicator_sub_indicator,
          eLpNorm_indicator_const (hDm.symmDiff hF'm) one_ne_zero ENNReal.one_ne_top, symmDiff_comm]
        simp
      calc eLpNorm (f - Q.structureLaw[f | markedAlg A]) 1 Q.structureLaw
          = eLpNorm ((f - d) + (d - Q.structureLaw[f | markedAlg A])) 1 Q.structureLaw := by
            rw [sub_add_sub_cancel]
        _ ≤ eLpNorm (f - d) 1 Q.structureLaw +
            eLpNorm (d - Q.structureLaw[f | markedAlg A]) 1 Q.structureLaw :=
            eLpNorm_add_le (hfint.sub hdint).aestronglyMeasurable
              (hdint.sub integrable_condExp).aestronglyMeasurable le_rfl
        _ ≤ Q.structureLaw ((restrictOriginal S ⁻¹' F) ∆ D) +
            Q.structureLaw ((restrictOriginal S ⁻¹' F) ∆ D) := add_le_add h1.le h2
        _ ≤ ENNReal.ofReal ((ε : ℝ) / 2) + ENNReal.ofReal ((ε : ℝ) / 2) :=
            add_le_add hlt.le hlt.le
        _ = 0 + ε := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves, zero_add,
              ENNReal.ofReal_coe_nnreal]
    have hsub := (eLpNorm_eq_zero_iff (hfint.sub integrable_condExp).aestronglyMeasurable
      one_ne_zero).mp hzero
    filter_upwards [hsub] with x hx
    simp only [Pi.sub_apply, Pi.zero_apply] at hx
    exact (sub_eq_zero.mp hx).symm
  -- the marked event
  have hset : MeasurableSet[markedAlg A] ((Q.structureLaw[f | markedAlg A]) ⁻¹' {1}) :=
    hgm.measurable (measurableSet_singleton (1 : ℝ))
  obtain ⟨D, hD, hDeq⟩ := MeasurableSpace.measurableSet_comap.mp hset
  refine ⟨D, hD, ?_⟩
  rw [hDeq]
  filter_upwards [hae] with x hx
  show (x ∈ Q.structureLaw[f | markedAlg A] ⁻¹' {1}) = (x ∈ restrictOriginal S ⁻¹' F)
  rw [eq_iff_iff, Set.mem_preimage, Set.mem_singleton_iff, hx, hf]
  by_cases hxF : x ∈ restrictOriginal S ⁻¹' F <;> simp [hxF]

end InfiniteRelExchangeableLaw

end RelSignature
