/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.MixtureExistence
import Graphon.MixtureUniqueness

/-!
# The Diaconis–Janson graphon-mixture representation theorem (issue #33)

Assembly of the two halves proved in `Graphon/MixtureUniqueness.lean` and
`Graphon/MixtureExistence.lean`:

* `GraphonSpace.graphon_mixture_representation` — **the representation theorem**: every
  exchangeable graph law is the mixture law of a *unique* probability measure on the
  graphon space;
* `GraphonSpace.mixtureExchangeableLawEquiv` — the packaged bijection
  `ProbabilityMeasure (GraphonSpace α μ) ≃ Graphon.ExchangeableGraphLaw`;
* `GraphonSpace.empiricalMixing_tendsto_representingMeasure` — **empirical
  convergence**: the whole sequence of empirical mixing measures converges weakly to
  the representing measure (subsequential limits are unique by the representation
  theorem, and a unique cluster point in a compact metrizable space gives convergence).
-/

open MeasureTheory

namespace GraphonSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ]

/-- **The graphon-mixture representation theorem** (Diaconis–Janson): every exchangeable
graph law is the mixture law of a unique probability measure on the graphon space —
existence by `exists_mixtureExchangeableLaw_eq`, uniqueness by
`mixtureExchangeableLaw_injective`. -/
@[blueprint "thm:graphon-mixture-representation"
  (title := /-- The graphon-mixture representation theorem -/)]
theorem graphon_mixture_representation (L : Graphon.ExchangeableGraphLaw) :
    ∃! P : ProbabilityMeasure (GraphonSpace α μ),
      mixtureExchangeableLaw (α := α) (μ := μ) P = L := by
  obtain ⟨P, hP⟩ := exists_mixtureExchangeableLaw_eq (α := α) (μ := μ) L
  exact ⟨P, hP, fun Q hQ => mixtureExchangeableLaw_injective (hQ.trans hP.symm)⟩

/-- The graphon-mixture representation, packaged as a bijection between mixing measures
on the graphon space and exchangeable graph laws. -/
noncomputable def mixtureExchangeableLawEquiv :
    ProbabilityMeasure (GraphonSpace α μ) ≃ Graphon.ExchangeableGraphLaw :=
  Equiv.ofBijective mixtureExchangeableLaw
    ⟨mixtureExchangeableLaw_injective, exists_mixtureExchangeableLaw_eq⟩

@[simp] theorem mixtureExchangeableLawEquiv_apply
    (P : ProbabilityMeasure (GraphonSpace α μ)) :
    mixtureExchangeableLawEquiv (α := α) (μ := μ) P = mixtureExchangeableLaw P := rfl

@[simp] theorem mixtureExchangeableLawEquiv_symm_apply
    (L : Graphon.ExchangeableGraphLaw) :
    mixtureExchangeableLaw ((mixtureExchangeableLawEquiv (α := α) (μ := μ)).symm L) =
      L :=
  (mixtureExchangeableLawEquiv (α := α) (μ := μ)).apply_symm_apply L

/-- **Empirical convergence to the representing measure**: the whole sequence of
empirical mixing measures of an exchangeable law converges weakly to the unique
representing measure — not merely a subsequence. Every subsequence has a Prokhorov
sub-subsequential limit; the collision estimate identifies each such limit's mixture
law with `L`; uniqueness forces every limit to be the representing measure; and a
unique cluster point in a compact metrizable space gives convergence. -/
@[blueprint "thm:empirical-convergence"
  (title := /-- Empirical convergence to the representing measure -/)]
theorem empiricalMixing_tendsto_representingMeasure (L : Graphon.ExchangeableGraphLaw) :
    Filter.Tendsto (fun n => empiricalMixing (α := α) (μ := μ) L (n + 1)) Filter.atTop
      (nhds ((mixtureExchangeableLawEquiv (α := α) (μ := μ)).symm L)) := by
  refine Filter.tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨Q, ψ, hψ, hconv⟩ := exists_subseq_tendsto
    (fun m => empiricalMixing (α := α) (μ := μ) L (ns m + 1))
  have hcomp : Filter.Tendsto
      (fun m => empiricalMixing (α := α) (μ := μ) L (ns (ψ m) + 1))
      Filter.atTop (nhds Q) := by
    simpa only [Function.comp_def] using hconv
  have hQL : mixtureExchangeableLaw Q = L :=
    mixtureExchangeableLaw_eq_of_tendsto_empiricalMixing L
      (hns.comp hψ.tendsto_atTop) hcomp
  have hQ : Q = (mixtureExchangeableLawEquiv (α := α) (μ := μ)).symm L :=
    mixtureExchangeableLaw_injective
      (hQL.trans (mixtureExchangeableLawEquiv_symm_apply (α := α) (μ := μ) L).symm)
  exact ⟨ψ, hQ ▸ hcomp⟩

end GraphonSpace
