/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.ExchangeableGraphLaw
import Graphon.HomDensityAlgebra

/-!
# Mixture-coordinate infrastructure (issue #33)

Shared layer between the uniqueness and existence halves of the Diaconis–Janson
correspondence:

* `GraphonSpace.homDensityCoordBCF` — the hom-density coordinates as bounded continuous
  functions on the compact graphon space;
* `GraphonSpace.integral_homDensityCoord` — the integral of a hom-density coordinate
  against a mixing measure is the upper mass of `F` under the corresponding mixture
  marginal (the coordinate is a finite upper sum of `sampleMassCoord`s, whose integrals
  are the marginal masses).

`Graphon/MixtureUniqueness.lean` builds the coordinate StarSubalgebra on top of these;
`Graphon/MixtureExistence.lean` consumes them for the Prokhorov-limit marginal
identification.
-/

open MeasureTheory

open scoped Classical

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

end GraphonSpace
