/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.InfiniteSampler
import Graphon.InfiniteExtremality

/-!
# Functional Aldous–Hoover for dissociated laws (issue #64)

The dissociated/extreme case of the functional Aldous–Hoover theorem — classically
equivalent to the ergodic case; the formal equivalence is issue #59 — needs **no
measurable selection**: a raw representative is chosen only after the graphon class is fixed.

* `InfiniteGraph.sampleInfinite_adj` — the sampler's literal coordinates:
  `X_{ij} = 1{U_{ij} ≤ W(U_i, U_j)}` (one uniform per unordered pair, evaluated at the
  clamped representative and the `Quot.out`-canonical endpoint order);
* `InfiniteGraph.isDissociated_iff_exists_sampler` — **an infinite exchangeable graph
  law is dissociated iff it is the law of the explicit `W`-random infinite graph for
  some raw graphon `W`** — extremality collapses the mixing measure to one class, and
  the explicit sampler realizes that single fiber.
-/

open MeasureTheory

namespace InfiniteGraph

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ]

omit [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ] in
/-- The sampler's adjacency, in the literal functional Aldous–Hoover form: distinct
vertices `i, j` are adjacent exactly when the pair's uniform falls below the (clamped)
graphon value at the latent positions. -/
theorem sampleInfinite_adj (W : Graphon α μ) (ω : (ℕ → α) × (EdgeIndex → ℝ))
    {i j : ℕ} (hij : i ≠ j) :
    (sampleInfinite W ω : SimpleGraph ℕ).Adj i j ↔
      ω.2 ⟨s(i, j), fun h => hij (Sym2.mk_isDiag_iff.mp h)⟩ ≤
        clampedRep W (ω.1 (Quot.out (s(i, j) : Sym2 ℕ)).1,
          ω.1 (Quot.out (s(i, j) : Sym2 ℕ)).2) := by
  have h := coordEquiv_sampleInfinite W ω ⟨s(i, j), fun h => hij (Sym2.mk_isDiag_iff.mp h)⟩
  rw [coordEquiv_apply] at h
  rw [show (sampleInfinite W ω : SimpleGraph ℕ).Adj i j ↔
      (s(i, j) : Sym2 ℕ) ∈ (sampleInfinite W ω : SimpleGraph ℕ).edgeSet from
    (SimpleGraph.mem_edgeSet (sampleInfinite W ω : SimpleGraph ℕ)).symm]
  constructor
  · intro hmem
    by_contra hle
    rw [if_pos hmem, if_neg hle] at h
    simp at h
  · intro hle
    by_contra hmem
    rw [if_neg hmem, if_pos hle] at h
    simp at h

/-- **Functional Aldous–Hoover for dissociated laws** (issue #64, the dissociated/
extreme case; classically equivalent to ergodic — formalized in issue #59):
an infinite exchangeable graph law is dissociated iff it is the law of the explicit
`W`-random infinite graph `X_{ij} = 1{U_{ij} ≤ W(U_i, U_j)}` for some raw graphon `W`.
No measurable selection in the class variable is needed: extremality fixes a single
graphon class, and a representative is chosen for that one class. -/
@[blueprint "thm:functional-ah-dissociated"
  (title := /-- Functional Aldous–Hoover for dissociated laws -/)]
theorem isDissociated_iff_exists_sampler (M : Graphon.InfiniteExchangeableGraphLaw) :
    M.IsDissociated ↔
      ∃ W : Graphon α μ, (samplerSource μ).map (sampleInfinite W) =
        (M.law : Measure InfiniteGraph) := by
  rw [GraphonSpace.isDissociated_iff_exists_infiniteSampleExchangeableLaw
    (α := α) (μ := μ)]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨W, rfl⟩ := GraphonSpace.surjective_mk x
    refine ⟨W, ?_⟩
    rw [map_sampleInfinite_eq_infiniteSampleLaw_mk,
      GraphonSpace.infiniteSampleExchangeableLaw_law]
  · rintro ⟨W, hW⟩
    refine ⟨GraphonSpace.mk W, Graphon.InfiniteExchangeableGraphLaw.ext ?_⟩
    apply ProbabilityMeasure.toMeasure_injective
    rw [GraphonSpace.infiniteSampleExchangeableLaw_law, ← hW,
      map_sampleInfinite_eq_infiniteSampleLaw_mk]

/-- The source-map law equality for a dissociated law: extract the realizing raw
graphon. -/
theorem exists_sampler_of_isDissociated {M : Graphon.InfiniteExchangeableGraphLaw}
    (hM : M.IsDissociated) :
    ∃ W : Graphon α μ, (samplerSource μ).map (sampleInfinite W) =
      (M.law : Measure InfiniteGraph) :=
  (isDissociated_iff_exists_sampler M).mp hM

end InfiniteGraph
