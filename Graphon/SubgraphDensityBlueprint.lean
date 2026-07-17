/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.SubgraphDensities

/-!
# Blueprint node for the finite density triangle (#94)

Annotation-only wrapper carrying the blueprint-graph node for the finite subgraph-density
triangle. Housing the `Architect` dependency here keeps `Graphon.SubgraphDensities` a pure
combinatorics module (it is an upstream/reuse candidate); the mathematical content lives
there.
-/

open scoped Classical in
/-- **The finite density triangle** (#94; Lovász §5.2.3, (5.19)–(5.21)): the zeta identity
`t_inj(F, ·) = ∑_{F' ⊇ F} t_ind(F', ·)`, its inverse Möbius form
`t_ind(F, ·) = ∑_{F' ⊇ F} (−1)^{|E(F') ∖ E(F)|} t_inj(F', ·)`, and the collision comparison
`|t − t_inj| ≤ k²/n` — all unconditional under the small-host zero convention. -/
@[blueprint "thm:finite-density-triangle"
  (title := /-- The finite density triangle -/)]
theorem finite_density_triangle_blueprint {k n : ℕ}
    (F : SimpleGraph (Fin k)) (H : SimpleGraph (Fin n)) :
    (SimpleGraph.tInj F H = ∑ F' ∈ Finset.univ.filter
        (fun F' : SimpleGraph (Fin k) => F ≤ F'), SimpleGraph.tInd F' H) ∧
      (SimpleGraph.tInd F H = ∑ F' ∈ Finset.univ.filter
          (fun F' : SimpleGraph (Fin k) => F ≤ F'),
        (-1 : ℝ) ^ (F'.edgeFinset \ F.edgeFinset).card * SimpleGraph.tInj F' H) ∧
      |SimpleGraph.t F H - SimpleGraph.tInj F H| ≤ (k : ℝ) ^ 2 / n :=
  ⟨SimpleGraph.tInj_eq_sum_tInd F H, SimpleGraph.tInd_eq_sum_neg_one_pow_tInj F H,
    SimpleGraph.abs_t_sub_tInj_le F H⟩
