/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.InfiniteSampleLaw
import Graphon.InfiniteRepresentation
import Graphon.MixtureExtremality

/-!
# Extremality for infinite exchangeable laws (issue #55)

Transporting the Diaconis–Janson extremality criterion through the infinite
representation:

* `GraphonSpace.infiniteMixtureLawEquiv_dirac_law` — **the Dirac bridge**: the
  represented law of a Dirac mixing measure is the canonical infinite law of its point;
* `GraphonSpace.infiniteSampleExchangeableLaw` — the canonical infinite law, bundled
  with its exchangeability;
* `Graphon.InfiniteExchangeableGraphLaw.IsDissociated` — dissociation of an infinite
  law (via its finite marginals);
* `GraphonSpace.isDissociated_iff_exists_infiniteSampleExchangeableLaw` — **an infinite
  exchangeable law is dissociated iff it is the canonical law of a single graphon
  class**;
* `GraphonSpace.isDissociated_iff_representing_dirac` — equivalently, iff its
  representing measure is a Dirac.
-/

open MeasureTheory InfiniteGraph

namespace GraphonSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

/-- **The Dirac bridge**: the represented infinite law of a Dirac mixing measure is the
canonical infinite law of its point. -/
@[simp] theorem infiniteMixtureLawEquiv_dirac_law (x : GraphonSpace α μ) :
    (infiniteMixtureLawEquiv (α := α) (μ := μ) (diracProba x)).law =
      infiniteSampleLaw x := by
  rw [infiniteMixtureLawEquiv_apply_law]
  obtain ⟨W, rfl⟩ := surjective_mk x
  rw [infiniteSampleLaw_mk]
  congr 1
  exact (sampleExchangeableLaw_eq_mixture_diracProba W).symm

/-- The canonical infinite law of a graphon class, bundled with its exchangeability. -/
noncomputable def infiniteSampleExchangeableLaw (x : GraphonSpace α μ) :
    Graphon.InfiniteExchangeableGraphLaw :=
  infiniteMixtureLawEquiv (α := α) (μ := μ) (diracProba x)

@[simp] theorem infiniteSampleExchangeableLaw_law (x : GraphonSpace α μ) :
    (infiniteSampleExchangeableLaw x).law = infiniteSampleLaw x :=
  infiniteMixtureLawEquiv_dirac_law x

end GraphonSpace

namespace Graphon.InfiniteExchangeableGraphLaw

/-- **Dissociation of an infinite exchangeable law**: dissociation of its finite
marginals (upper events on disjoint vertex blocks are independent). -/
def IsDissociated (M : Graphon.InfiniteExchangeableGraphLaw) : Prop :=
  M.toExchangeableGraphLaw.IsDissociated

end Graphon.InfiniteExchangeableGraphLaw

namespace GraphonSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

/-- **Extremality at the infinite level, Dirac form**: an infinite exchangeable law is
dissociated iff its representing measure is a Dirac. -/
theorem isDissociated_iff_representing_dirac (M : Graphon.InfiniteExchangeableGraphLaw) :
    M.IsDissociated ↔
      ∃ x : GraphonSpace α μ,
        (infiniteMixtureLawEquiv (α := α) (μ := μ)).symm M = diracProba x := by
  have hM : mixtureExchangeableLaw ((infiniteMixtureLawEquiv (α := α) (μ := μ)).symm M) =
      M.toExchangeableGraphLaw :=
    mixtureExchangeableLaw_infiniteMixtureLawEquiv_symm M
  constructor
  · intro hdiss
    exact (isDissociated_mixtureExchangeableLaw_iff _).mp (by rw [hM]; exact hdiss)
  · rintro ⟨x, hx⟩
    show M.toExchangeableGraphLaw.IsDissociated
    rw [← hM]
    exact (isDissociated_mixtureExchangeableLaw_iff _).mpr ⟨x, hx⟩

/-- **Extremality at the infinite level**: an infinite exchangeable law is dissociated
iff it is the canonical law of a single graphon class. -/
theorem isDissociated_iff_exists_infiniteSampleExchangeableLaw
    (M : Graphon.InfiniteExchangeableGraphLaw) :
    M.IsDissociated ↔
      ∃ x : GraphonSpace α μ, M = infiniteSampleExchangeableLaw x := by
  rw [isDissociated_iff_representing_dirac (α := α) (μ := μ)]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [infiniteSampleExchangeableLaw, ← hx, Equiv.apply_symm_apply]
  · rintro ⟨x, rfl⟩
    exact ⟨x, by rw [infiniteSampleExchangeableLaw, Equiv.symm_apply_apply]⟩

/-- The canonical infinite law of a graphon class is dissociated. -/
theorem isDissociated_infiniteSampleExchangeableLaw (x : GraphonSpace α μ) :
    (infiniteSampleExchangeableLaw x).IsDissociated :=
  (isDissociated_iff_exists_infiniteSampleExchangeableLaw _).mpr ⟨x, rfl⟩

end GraphonSpace
