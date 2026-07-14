/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.MixtureRepresentation
import Graphon.InfiniteExchangeability

/-!
# The infinite Diaconis–Janson / Aldous–Hoover correspondence (issue #53)

Composing the mixture representation with the infinite-law equivalence:

* `GraphonSpace.infiniteMixtureLawEquiv` — **every exchangeable probability law on
  infinite graphs is represented by a unique probability measure on graphon space**:
  `ProbabilityMeasure (GraphonSpace α μ) ≃ InfiniteExchangeableGraphLaw`, the
  graphon-space form of Aldous–Hoover at the level of distributions;
* simp lemmas for both directions, and the finite marginals of the represented
  infinite law (`infiniteMixtureLawEquiv_law_map_restrictFin`: the level-`k`
  restriction is the mixture marginal `mixturePMF P k`).
-/

open MeasureTheory InfiniteGraph

namespace GraphonSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ]

/-- **The infinite Diaconis–Janson / Aldous–Hoover correspondence**: probability
measures on the graphon space are exactly the exchangeable probability laws on infinite
graphs — the composition of the mixture representation with the infinite-law
equivalence. -/
@[blueprint "thm:infinite-mixture-representation"
  (title := /-- The infinite graphon-mixture representation -/)]
noncomputable def infiniteMixtureLawEquiv :
    ProbabilityMeasure (GraphonSpace α μ) ≃ Graphon.InfiniteExchangeableGraphLaw :=
  (mixtureExchangeableLawEquiv (α := α) (μ := μ)).trans
    Graphon.exchangeableGraphLawEquivInfinite

@[simp] theorem infiniteMixtureLawEquiv_apply_law
    (P : ProbabilityMeasure (GraphonSpace α μ)) :
    (infiniteMixtureLawEquiv (α := α) (μ := μ) P).law =
      Graphon.ExchangeableGraphLaw.infiniteLaw (mixtureExchangeableLaw P) := rfl

@[simp] theorem mixtureExchangeableLaw_infiniteMixtureLawEquiv_symm
    (M : Graphon.InfiniteExchangeableGraphLaw) :
    mixtureExchangeableLaw ((infiniteMixtureLawEquiv (α := α) (μ := μ)).symm M) =
      M.toExchangeableGraphLaw := by
  have h : (infiniteMixtureLawEquiv (α := α) (μ := μ)).symm M =
      (mixtureExchangeableLawEquiv (α := α) (μ := μ)).symm
        (Graphon.exchangeableGraphLawEquivInfinite.symm M) := rfl
  rw [h]
  exact mixtureExchangeableLawEquiv_symm_apply _

/-- **Finite marginals of the represented infinite law**: the level-`k` restriction of
the infinite law of a mixing measure is the mixture marginal `mixturePMF P k`. -/
theorem infiniteMixtureLawEquiv_law_map_restrictFin
    (P : ProbabilityMeasure (GraphonSpace α μ)) (k : ℕ) :
    ((infiniteMixtureLawEquiv (α := α) (μ := μ) P).law : Measure InfiniteGraph).map
      (restrictFin k) = (mixturePMF P k).toMeasure := by
  rw [infiniteMixtureLawEquiv_apply_law,
    Graphon.ExchangeableGraphLaw.infiniteLaw_map_restrictFin]
  rfl

end GraphonSpace
