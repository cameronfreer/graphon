/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.ExchangeableGraphLaw
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Weak convergence of graphon mixtures (issue #33, analytic layer)

The compactness/continuity infrastructure for the Diaconis–Janson representation
theorem (steps 3–4 of the #33 plan):

* `GraphonSpace.mixturePMF_toReal_eq_integral` — the mixture marginal masses are Bochner
  integrals of the continuous coordinates `sampleMassCoord`;
* `GraphonSpace.sampleMassCoordBCF` — the coordinates as bounded continuous functions
  (the graphon space is compact);
* `GraphonSpace.continuous_integral_sampleMassCoord` — the mixture coordinates
  `P ↦ ∫ sampleMassCoord G dP` are continuous in the topology of weak convergence, so
  the marginals of a weak limit are the limits of the marginals;
* `GraphonSpace.exists_subseq_tendsto` — **Prokhorov extraction**: every sequence of
  mixing measures on the compact metrizable graphon space has a weakly convergent
  subsequence (Mathlib's `CompactSpace (ProbabilityMeasure _)` + metrizability);
* `GraphonSpace.graphClass` / `GraphonSpace.empiricalMixing` — the graphon class of a
  finite simple graph, and the empirical mixing measure of an exchangeable law at
  size `n` (the pushforward of `L.law n` under `graphClass`).

The remaining #33 content is the collision-bound marginal identification (step 5) and
Stone–Weierstrass uniqueness (step 6).
-/

open MeasureTheory Filter Topology

open scoped ENNReal

namespace GraphonSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

/-- The mixture marginal masses are Bochner integrals of the scalar coordinates. -/
theorem mixturePMF_toReal_eq_integral (P : ProbabilityMeasure (GraphonSpace α μ))
    (k : ℕ) (G : SimpleGraph (Fin k)) :
    ((mixturePMF P k) G).toReal =
      ∫ x, sampleMassCoord G x ∂(P : Measure (GraphonSpace α μ)) := by
  rw [mixturePMF_apply,
    ← MeasureTheory.integral_toReal (measurable_finiteSampleLaw_apply k G).aemeasurable
      (Eventually.of_forall fun x => (finiteSampleLaw k x).apply_lt_top G)]
  exact integral_congr_ae (Eventually.of_forall fun x =>
    (sampleMassCoord_eq_toReal G x).symm)

/-- The scalar coordinates as bounded continuous functions on the compact graphon
space. -/
noncomputable def sampleMassCoordBCF {k : ℕ} (G : SimpleGraph (Fin k)) :
    BoundedContinuousFunction (GraphonSpace α μ) ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨sampleMassCoord G, continuous_sampleMassCoord G⟩

@[simp] theorem sampleMassCoordBCF_apply {k : ℕ} (G : SimpleGraph (Fin k))
    (x : GraphonSpace α μ) : sampleMassCoordBCF G x = sampleMassCoord G x := rfl

/-- **The mixture coordinates are weakly continuous**: `P ↦ ∫ sampleMassCoord G dP` is
continuous on `ProbabilityMeasure (GraphonSpace α μ)` with the topology of weak
convergence. Consequently the marginals of a weak limit of mixing measures are the
limits of the marginals. -/
theorem continuous_integral_sampleMassCoord {k : ℕ} (G : SimpleGraph (Fin k)) :
    Continuous fun P : ProbabilityMeasure (GraphonSpace α μ) =>
      ∫ x, sampleMassCoord G x ∂(P : Measure (GraphonSpace α μ)) := by
  rw [continuous_iff_continuousAt]
  intro P
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    tendsto_id (sampleMassCoordBCF G)

/-- **Prokhorov extraction**: every sequence of mixing measures on the compact
metrizable graphon space has a weakly convergent subsequence. -/
theorem exists_subseq_tendsto (Ps : ℕ → ProbabilityMeasure (GraphonSpace α μ)) :
    ∃ (P : ProbabilityMeasure (GraphonSpace α μ)) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (Ps ∘ φ) atTop (𝓝 P) := by
  obtain ⟨P, -, φ, hφ, hconv⟩ :=
    (isCompact_univ (X := ProbabilityMeasure (GraphonSpace α μ))).tendsto_subseq
      (x := Ps) (fun n => Set.mem_univ _)
  exact ⟨P, φ, hφ, hconv⟩

/-- The graphon class of a finite simple graph (its embedded step graphon, in the
graphon space). -/
noncomputable def graphClass {n : ℕ} [NeZero n] (G : SimpleGraph (Fin n)) :
    GraphonSpace α μ :=
  mk (Graphon.ofSimpleGraphOn G)

/-- **The empirical mixing measure** of an exchangeable graph law at size `n`: sample
`Gₙ ∼ L.law n` and take its graphon class. Step 3 of the #33 plan; Prokhorov extraction
applies to the sequence `empiricalMixing L n`. -/
noncomputable def empiricalMixing (L : Graphon.ExchangeableGraphLaw) (n : ℕ) [NeZero n] :
    ProbabilityMeasure (GraphonSpace α μ) :=
  ⟨((L.law n).toMeasure).map (graphClass (α := α) (μ := μ)),
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable⟩

@[simp] theorem empiricalMixing_coe (L : Graphon.ExchangeableGraphLaw) (n : ℕ)
    [NeZero n] :
    (empiricalMixing (α := α) (μ := μ) L n : Measure (GraphonSpace α μ)) =
      ((L.law n).toMeasure).map (graphClass (α := α) (μ := μ)) := rfl

end GraphonSpace
