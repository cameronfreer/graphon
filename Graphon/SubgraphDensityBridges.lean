/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.SamplingFinite
import Graphon.SubgraphDensities

/-!
# Bridges from the finite subgraph densities to the empirical-graphon formulas (#94, PR 1)

The analytic half of the `t`/`t_inj`/`t_ind` interlude: on the equipartition step graphon of a
finite host `H`, the homomorphism density *is* `SimpleGraph.t` and the sampling mass *is* the
normalized exact-pullback count. Separate from `Graphon.SubgraphDensities` so the pure
density API keeps a combinatorics-only import closure. Also the collision-comparison
forms: the analytic homomorphism density is within `k²/n` of `t_inj`, and the sampling mass
within `k²/n` of `t_ind` — the quantitative content of "sampling ≈ injective sampling".
-/

open Finset MeasureTheory

open scoped Classical

namespace Graphon

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
  [StandardBorelSpace α] [NullSingletonClass μ]

/-- **The homomorphism density of the empirical graphon is `t`**: on the equipartition step
graphon of `H`, the analytic homomorphism density coincides with the combinatorial
density. -/
theorem homDensity_ofSimpleGraphOn_eq_t {n : ℕ} [NeZero n] (H : SimpleGraph (Fin n))
    {k : ℕ} (F : SimpleGraph (Fin k)) [DecidableRel F.Adj] :
    homDensity F (ofSimpleGraphOn (α := α) (μ := μ) H) = SimpleGraph.t F H := by
  rw [homDensity_ofSimpleGraphOn, SimpleGraph.t, SimpleGraph.homCount, Finset.sum_boole,
    inv_pow, inv_mul_eq_div]

/-- **The sampling mass of the empirical graphon is the normalized exact-pullback count**:
the probability that the `k`-sample of the empirical graphon of `H` equals `G` is the
proportion of all vertex maps pulling `H` back to exactly `G`. -/
theorem sampleMass_ofSimpleGraphOn_eq_pullbackCount_div {n : ℕ} [NeZero n] (H : SimpleGraph (Fin n))
    {k : ℕ} (G : SimpleGraph (Fin k)) :
    sampleMass (ofSimpleGraphOn (α := α) (μ := μ) H) G =
      SimpleGraph.pullbackCount G H / (n : ℝ) ^ k := by
  rw [sampleMass_ofSimpleGraphOn, SimpleGraph.pullbackCount, Finset.sum_boole,
    inv_pow, inv_mul_eq_div]

/-- **The analytic collision comparison**: the homomorphism density of the empirical graphon
is within `k²/n` of the injective density of the host. -/
theorem abs_homDensity_ofSimpleGraphOn_sub_tInj_le {n : ℕ} [NeZero n]
    (H : SimpleGraph (Fin n)) {k : ℕ} (F : SimpleGraph (Fin k)) [DecidableRel F.Adj] :
    |homDensity F (ofSimpleGraphOn (α := α) (μ := μ) H) - SimpleGraph.tInj F H| ≤
      (k : ℝ) ^ 2 / n := by
  rw [homDensity_ofSimpleGraphOn_eq_t]
  exact SimpleGraph.abs_t_sub_tInj_le F H

/-- **The sampling collision comparison**: the sampling mass of the empirical graphon is
within `k²/n` of the induced density of the host. -/
theorem abs_sampleMass_ofSimpleGraphOn_sub_tInd_le {n : ℕ} [NeZero n]
    (H : SimpleGraph (Fin n)) {k : ℕ} (G : SimpleGraph (Fin k)) :
    |sampleMass (ofSimpleGraphOn (α := α) (μ := μ) H) G - SimpleGraph.tInd G H| ≤
      (k : ℝ) ^ 2 / n := by
  rw [sampleMass_ofSimpleGraphOn_eq_pullbackCount_div]
  exact SimpleGraph.abs_pullbackCount_div_sub_tInd_le G H

end Graphon
