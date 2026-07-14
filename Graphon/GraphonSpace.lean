/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.Compactness

/-!
# The graphon space: compact metric quotient of graphons under weak isomorphism (issue #23)

Packages the proved pseudometric theory of `cutDistance` into a bundled state space
(route vetted 2026-07-10):

* a `PseudoMetricSpace` instance on raw `Graphon α μ` with `dist = cutDistance`
  (the triangle inequality fixes the instance boundary at
  `[StandardBorelSpace α] [NullSingletonClass μ]`);
* `GraphonSpace α μ := SeparationQuotient (Graphon α μ)` — Mathlib's metric separation
  quotient, NOT a hand-rolled `Quotient`: the `MetricSpace`, `CompleteSpace`, and
  `Nonempty` instances come for free, and quotient equality is exactly
  `WeaklyIsomorphic` (`GraphonSpace.mk_eq_mk_iff`);
* `CompactSpace (GraphonSpace α μ)`: total boundedness transfers through the uniformly
  continuous surjective quotient map (`Graphon.totallyBounded` is called at `ε / 2`
  because it produces closed-ball nets while `Metric.totallyBounded_iff` wants open
  balls) and combines with the transferred completeness;
* the canonical Borel measurable space on the quotient, giving `BorelSpace`,
  `SecondCountableTopology`, `PolishSpace`, and `StandardBorelSpace` — the right home
  for graphon-valued laws. (Raw `Graphon α μ` deliberately receives NO measurable
  structure: the quotient is the object that carries random graphons.)
* `StandardGraphonSpace` — the fixed unit-interval alias for probability-facing APIs,
  so downstream theorems need not carry base-space typeclasses.

Deferred explicitly (separate campaigns): isometry/transport between quotients over
different atomless standard bases (a `MeasureIso` application), measurable selectors.
-/

open MeasureTheory

namespace Graphon

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ]

/-- The cut distance as a pseudometric on raw graphons. Not a metric: distance zero is
weak isomorphism, not equality — hence the `SeparationQuotient` below. -/
noncomputable instance instPseudoMetricSpace : PseudoMetricSpace (Graphon α μ) where
  dist := cutDistance
  dist_self := cutDistance_self
  dist_comm := cutDistance_symm
  dist_triangle := cutDistance_triangle

/-- Raw graphon space is complete: the metric Cauchy predicate is the project's
sequential `IsCauchy`, discharged by the proved `complete`. -/
noncomputable instance instCompleteSpace : CompleteSpace (Graphon α μ) := by
  apply UniformSpace.complete_of_cauchySeq_tendsto
  intro W hW
  have hC : IsCauchy W := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hW ε hε
    exact ⟨N, fun m n hm hn ↦ hN m hm n hn⟩
  obtain ⟨V, hV⟩ := complete W hC
  exact ⟨V, Metric.tendsto_atTop.mpr hV⟩

/-- Raw graphon space is totally bounded (from the proved finite-net theorem, invoked
at half radius to convert closed-ball nets into open balls). -/
theorem totallyBounded_univ :
    TotallyBounded (Set.univ : Set (Graphon α μ)) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨S, hS⟩ := totallyBounded (α := α) (μ := μ) (ε / 2) (half_pos hε)
  refine ⟨↑S, S.finite_toSet, ?_⟩
  intro W _
  obtain ⟨V, hVS, hWV⟩ := hS W
  refine Set.mem_iUnion.2 ⟨V, Set.mem_iUnion.2 ⟨hVS, ?_⟩⟩
  rw [Metric.mem_ball]
  exact lt_of_le_of_lt hWV (half_lt_self hε)

end Graphon

/-- **The graphon space**: the metric separation quotient of `Graphon α μ` under cut
distance — equivalently, graphons modulo weak isomorphism — as a compact Polish
standard-Borel metric space. -/
@[blueprint "def:graphonSpace"
  (title := /-- The graphon space -/)]
abbrev GraphonSpace (α : Type*) [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ] :=
  SeparationQuotient (Graphon α μ)

namespace GraphonSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ]

/-- The class of a graphon in the graphon space. -/
noncomputable def mk (W : Graphon α μ) : GraphonSpace α μ :=
  SeparationQuotient.mk W

@[simp] theorem dist_mk (U W : Graphon α μ) :
    dist (mk U) (mk W) = Graphon.cutDistance U W :=
  SeparationQuotient.dist_mk U W

/-- **Quotient equality is weak isomorphism**: two graphons have the same class iff
they are weakly isomorphic (cut distance zero). -/
@[simp] theorem mk_eq_mk_iff (U W : Graphon α μ) :
    mk U = mk W ↔ Graphon.WeaklyIsomorphic U W := by
  change SeparationQuotient.mk U = SeparationQuotient.mk W ↔ _
  rw [SeparationQuotient.mk_eq_mk, Metric.inseparable_iff]
  rfl

theorem surjective_mk : Function.Surjective (mk : Graphon α μ → GraphonSpace α μ) :=
  SeparationQuotient.surjective_mk

theorem uniformContinuous_mk :
    UniformContinuous (mk : Graphon α μ → GraphonSpace α μ) :=
  SeparationQuotient.uniformContinuous_mk

theorem continuous_mk : Continuous (mk : Graphon α μ → GraphonSpace α μ) :=
  SeparationQuotient.continuous_mk

theorem totallyBounded_univ :
    TotallyBounded (Set.univ : Set (GraphonSpace α μ)) := by
  have h : TotallyBounded
      ((SeparationQuotient.mk : Graphon α μ → GraphonSpace α μ) ''
        (Set.univ : Set (Graphon α μ))) :=
    Graphon.totallyBounded_univ.image SeparationQuotient.uniformContinuous_mk
  simpa [Set.image_univ, SeparationQuotient.surjective_mk.range_eq] using h

/-- **Compactness of the graphon space** (Lovász–Szegedy): complete + totally bounded. -/
@[blueprint "thm:graphonSpace-compact"
  (title := /-- Compactness of the graphon space -/)]
noncomputable instance instCompactSpace : CompactSpace (GraphonSpace α μ) := by
  rw [← isCompact_univ_iff, isCompact_iff_totallyBounded_isComplete]
  exact ⟨totallyBounded_univ, complete_univ⟩

/-- The canonical Borel measurable structure on the graphon space — the state space for
graphon-valued random elements. -/
noncomputable instance instMeasurableSpace : MeasurableSpace (GraphonSpace α μ) :=
  borel (GraphonSpace α μ)

instance instBorelSpace : BorelSpace (GraphonSpace α μ) := ⟨rfl⟩

-- The full instance stack, as inference tests: metric, complete, compact, second
-- countable, Polish, standard Borel, nonempty.
noncomputable example : MetricSpace (GraphonSpace α μ) := inferInstance
example : CompleteSpace (GraphonSpace α μ) := inferInstance
example : CompactSpace (GraphonSpace α μ) := inferInstance
example : SecondCountableTopology (GraphonSpace α μ) := inferInstance
example : PolishSpace (GraphonSpace α μ) := inferInstance
example : StandardBorelSpace (GraphonSpace α μ) := inferInstance
example : Nonempty (GraphonSpace α μ) := inferInstance

end GraphonSpace

/-- **The standard graphon space**, over the unit interval with Lebesgue measure: the
canonical fixed-domain state space for probability measures on graphons (downstream
probability APIs need not carry base-space typeclasses). Base-independence — isometry
with `GraphonSpace α μ` over any atomless standard Borel probability base — is a
deferred `MeasureIso` application. -/
abbrev StandardGraphonSpace :=
  GraphonSpace unitInterval (volume : Measure unitInterval)

namespace StandardGraphonSpace

noncomputable example : MetricSpace StandardGraphonSpace := inferInstance
example : CompactSpace StandardGraphonSpace := inferInstance
example : PolishSpace StandardGraphonSpace := inferInstance
example : StandardBorelSpace StandardGraphonSpace := inferInstance
example : Nonempty StandardGraphonSpace := inferInstance

end StandardGraphonSpace
