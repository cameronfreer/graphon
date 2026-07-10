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

The compactness infrastructure for the Diaconis–Janson representation theorem (steps
3–4 of the #33 plan; the integral bridge `mixturePMF_apply_toReal` and the weak
continuity `continuous_mixturePMF_apply_toReal` live with the mixture definitions in
`Graphon/ExchangeableGraphLaw.lean`):

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
