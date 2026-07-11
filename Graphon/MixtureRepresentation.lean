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
  `ProbabilityMeasure (GraphonSpace α μ) ≃ Graphon.ExchangeableGraphLaw`.
-/

open MeasureTheory

namespace GraphonSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

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

end GraphonSpace
