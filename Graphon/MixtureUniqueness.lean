/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.ExchangeableGraphLaw
import Graphon.HomDensityAlgebra
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt

/-!
# Uniqueness of the graphon mixture (issue #33, bricks 3–4)

The mixing measure of a graphon mixture is determined by its finite marginals:

* `GraphonSpace.homDensityCoordBCF` / `GraphonSpace.homDensityGenerators` — the
  hom-density coordinates as bounded continuous functions; the generator set contains
  `1` (the empty graph on `Fin 0`) and is closed under multiplication
  (`homDensity_sum_finAdd`);
* `GraphonSpace.homDensityStarSubalgebra` — the **real linear span** of the generators,
  packaged directly as a `StarSubalgebra` (multiplication closure by nested
  `Submodule.span_induction`; star is trivial over `ℝ`) — deliberately NOT
  `Algebra.adjoin`, whose induction principle does not see the span structure;
* `GraphonSpace.integral_homDensityCoordSpan_eq` — equal mixture marginals give equal
  integrals on the span: each generator is a finite upper sum of `sampleMassCoord`s,
  whose integrals are the marginal masses (`mixturePMF_apply_toReal`);
* the mapped subalgebra separates points (`homDensityCoord_eq_all_iff`), so Mathlib's
  `ext_of_forall_mem_subalgebra_integral_eq_of_polish` yields
  **`GraphonSpace.mixtureExchangeableLaw_injective`** — the uniqueness half of the
  Diaconis–Janson correspondence.
-/

open MeasureTheory

open scoped Classical BoundedContinuousFunction

namespace GraphonSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

/-- The hom-density coordinates as bounded continuous functions on the compact graphon
space. -/
noncomputable def homDensityCoordBCF {k : ℕ} (F : SimpleGraph (Fin k)) :
    BoundedContinuousFunction (GraphonSpace α μ) ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨homDensityCoord F, continuous_homDensityCoord F⟩

@[simp] theorem homDensityCoordBCF_apply {k : ℕ} (F : SimpleGraph (Fin k))
    (x : GraphonSpace α μ) : homDensityCoordBCF F x = homDensityCoord F x := rfl

/-- The generator set of the coordinate algebra: all hom-density coordinates of finite
graphs on `Fin k`, over all `k`. -/
def homDensityGenerators : Set (BoundedContinuousFunction (GraphonSpace α μ) ℝ) :=
  {f | ∃ (k : ℕ) (F : SimpleGraph (Fin k)), f = homDensityCoordBCF F}

/-- `1` is a generator: the hom density of the empty graph on `Fin 0`. -/
theorem one_mem_homDensityGenerators :
    (1 : BoundedContinuousFunction (GraphonSpace α μ) ℝ) ∈
      homDensityGenerators (α := α) (μ := μ) := by
  refine ⟨0, ⊥, ?_⟩
  ext x
  obtain ⟨W, rfl⟩ := surjective_mk x
  simp only [BoundedContinuousFunction.coe_one, Pi.one_apply, homDensityCoordBCF_apply,
    homDensityCoord_mk]
  exact ((Graphon.homDensity_congr_decRel
      (⊥ : SimpleGraph (Fin 0)) _ _ W).trans
      (Graphon.homDensity_bot W)).symm

/-- The generators are closed under multiplication (`homDensity_sum_finAdd`). -/
theorem mul_mem_homDensityGenerators
    {f g : BoundedContinuousFunction (GraphonSpace α μ) ℝ}
    (hf : f ∈ homDensityGenerators (α := α) (μ := μ))
    (hg : g ∈ homDensityGenerators (α := α) (μ := μ)) :
    f * g ∈ homDensityGenerators (α := α) (μ := μ) := by
  obtain ⟨k, F, rfl⟩ := hf
  obtain ⟨l, H, rfl⟩ := hg
  refine ⟨k + l, (F ⊕g H).map finSumFinEquiv.toEmbedding, ?_⟩
  ext x
  obtain ⟨W, rfl⟩ := surjective_mk x
  simp only [BoundedContinuousFunction.coe_mul, Pi.mul_apply, homDensityCoordBCF_apply,
    homDensityCoord_mk]
  exact ((Graphon.homDensity_congr_decRel _ _ _ W).trans
    (Graphon.homDensity_sum_finAdd F H W)).symm

/-- The real linear span of the hom-density coordinates. -/
noncomputable def homDensityCoordSpan :
    Submodule ℝ (BoundedContinuousFunction (GraphonSpace α μ) ℝ) :=
  Submodule.span ℝ (homDensityGenerators (α := α) (μ := μ))

/-- The span is closed under multiplication (nested `span_induction`). -/
theorem mul_mem_homDensityCoordSpan
    {f g : BoundedContinuousFunction (GraphonSpace α μ) ℝ}
    (hf : f ∈ homDensityCoordSpan (α := α) (μ := μ))
    (hg : g ∈ homDensityCoordSpan (α := α) (μ := μ)) :
    f * g ∈ homDensityCoordSpan (α := α) (μ := μ) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    induction hg using Submodule.span_induction with
    | mem g hg => exact Submodule.subset_span (mul_mem_homDensityGenerators hf hg)
    | zero => simp
    | add g₁ g₂ _ _ ih₁ ih₂ => rw [mul_add]; exact Submodule.add_mem _ ih₁ ih₂
    | smul c g _ ih => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ih
  | zero => simp
  | add f₁ f₂ _ _ ih₁ ih₂ => rw [add_mul]; exact Submodule.add_mem _ ih₁ ih₂
  | smul c f _ ih => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ih

/-- **The hom-density coordinate algebra**: the span of the coordinates, packaged as a
`StarSubalgebra` of the bounded continuous functions on the graphon space. -/
noncomputable def homDensityStarSubalgebra :
    StarSubalgebra ℝ (BoundedContinuousFunction (GraphonSpace α μ) ℝ) where
  carrier := homDensityCoordSpan (α := α) (μ := μ)
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  mul_mem' := fun ha hb => mul_mem_homDensityCoordSpan ha hb
  one_mem' := Submodule.subset_span one_mem_homDensityGenerators
  algebraMap_mem' := fun r => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r (Submodule.subset_span one_mem_homDensityGenerators)
  star_mem' := fun {f} hf => by
    have hstar : star f = f := by
      ext x
      simp [BoundedContinuousFunction.star_apply]
    rwa [hstar]

@[simp] theorem mem_homDensityStarSubalgebra
    {f : BoundedContinuousFunction (GraphonSpace α μ) ℝ} :
    f ∈ homDensityStarSubalgebra (α := α) (μ := μ) ↔
      f ∈ homDensityCoordSpan (α := α) (μ := μ) := Iff.rfl

/-- **The integral of a hom-density coordinate against a mixing measure is the upper
mass of `F` under the corresponding mixture marginal** (the coordinate is a finite upper
sum of `sampleMassCoord`s, whose integrals are the marginal masses). -/
theorem integral_homDensityCoord (R : ProbabilityMeasure (GraphonSpace α μ)) {k : ℕ}
    (F : SimpleGraph (Fin k)) :
    ∫ x, homDensityCoord F x ∂(R : Measure (GraphonSpace α μ)) =
      ∑ G : SimpleGraph (Fin k), if F ≤ G then (mixturePMF R k G).toReal else 0 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (fun x => homDensityCoord_eq_sum_sampleMassCoord F x)),
    integral_finsetSum _ (fun G _ => ?_)]
  · refine Finset.sum_congr rfl fun G _ => ?_
    split
    · rw [mixturePMF_apply_toReal]
    · simp
  · split
    · exact (BoundedContinuousFunction.mkOfCompact
        ⟨sampleMassCoord G, continuous_sampleMassCoord G⟩).integrable _
    · exact integrable_zero _ _ _

/-- Equal mixture marginals give equal integrals of every generator. -/
private theorem integral_homDensityCoord_eq
    {P Q : ProbabilityMeasure (GraphonSpace α μ)}
    (h : ∀ k, mixturePMF P k = mixturePMF Q k) {k : ℕ} (F : SimpleGraph (Fin k)) :
    ∫ x, homDensityCoord F x ∂(P : Measure (GraphonSpace α μ)) =
      ∫ x, homDensityCoord F x ∂(Q : Measure (GraphonSpace α μ)) := by
  rw [integral_homDensityCoord P F, integral_homDensityCoord Q F]
  refine Finset.sum_congr rfl fun G _ => ?_
  split
  · rw [h k]
  · rfl

/-- Equal mixture marginals give equal integrals on the whole coordinate span. -/
theorem integral_homDensityCoordSpan_eq
    {P Q : ProbabilityMeasure (GraphonSpace α μ)}
    (h : ∀ k, mixturePMF P k = mixturePMF Q k) :
    ∀ f ∈ homDensityCoordSpan (α := α) (μ := μ),
      ∫ x, f x ∂(P : Measure (GraphonSpace α μ)) =
        ∫ x, f x ∂(Q : Measure (GraphonSpace α μ)) := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, F, rfl⟩ := hf
    simpa only [homDensityCoordBCF_apply] using integral_homDensityCoord_eq h F
  | zero => simp
  | add f g hfm hgm ihf ihg =>
    simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
    rw [integral_add (f.integrable _) (g.integrable _),
      integral_add (f.integrable _) (g.integrable _), ihf, ihg]
  | smul c f hfm ih =>
    simp only [BoundedContinuousFunction.coe_smul]
    rw [integral_smul, integral_smul, ih]

/-- The mapped coordinate algebra separates points of the graphon space. -/
theorem separatesPoints_homDensityStarSubalgebra :
    ((homDensityStarSubalgebra (α := α) (μ := μ)).map
      (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  intro x y hxy
  have hne : ¬ ∀ (k : ℕ) (F : SimpleGraph (Fin k)),
      homDensityCoord F x = homDensityCoord F y := by
    intro hall
    exact hxy (homDensityCoord_eq_all_iff.mp hall)
  push Not at hne
  obtain ⟨k, F, hF⟩ := hne
  refine ⟨_, ⟨BoundedContinuousFunction.toContinuousMapStarₐ ℝ (homDensityCoordBCF F),
    ⟨homDensityCoordBCF F, Submodule.subset_span ⟨k, F, rfl⟩, rfl⟩, rfl⟩, ?_⟩
  simpa using hF

/-- **Uniqueness of the graphon mixture** (Diaconis–Janson, uniqueness half): the
mixing measure is determined by its exchangeable graph law. -/
@[blueprint "thm:mixture-uniqueness"
  (title := /-- Uniqueness of the graphon mixture -/)]
theorem mixtureExchangeableLaw_injective :
    Function.Injective (mixtureExchangeableLaw :
      ProbabilityMeasure (GraphonSpace α μ) → Graphon.ExchangeableGraphLaw) := by
  intro P Q h
  have hmarg : ∀ k, mixturePMF P k = mixturePMF Q k := fun k =>
    congrArg (fun L : Graphon.ExchangeableGraphLaw => L.law k) h
  apply ProbabilityMeasure.toMeasure_injective
  exact MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_polish
    separatesPoints_homDensityStarSubalgebra
    (fun g hg => integral_homDensityCoordSpan_eq hmarg g hg)

end GraphonSpace
