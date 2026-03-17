---
---

A Lean 4 formalization of **graphon theory** &mdash; the theory of limits of dense graph sequences &mdash; building on [Mathlib](https://leanprover-community.github.io/mathlib4/).

## Main Results

- **Cut distance metric** &mdash; Cut distance is a pseudometric on graphons: symmetry, triangle inequality, and non-negativity, with pullback invariance under measure-preserving maps.
- **Szemer&eacute;di regularity lemma** &mdash; Every graphon admits arbitrarily fine regular step-function approximations, with quantitative energy increment bounds.
- **Counting lemma** &mdash; Small cut distance implies similar homomorphism densities for all finite graphs.
- **Inverse counting lemma** &mdash; Similar homomorphism densities for all finite graphs implies small cut distance.
- **Compactness** &mdash; The graphon space is totally bounded and complete in the cut distance metric.
- **Convergence equivalence** &mdash; A sequence of graphons converges in cut distance if and only if all homomorphism densities converge.

## Scope

The formalization covers:

- **Graphon infrastructure** &mdash; Graphons as symmetric measurable functions on probability spaces, with AE equivalence classes (`Graphon`).
- **Cut distance** &mdash; Cut norm, cut distance as infimum over measure-preserving couplings (`cutNormDiff`, `cutDistance`), metric properties including the triangle inequality via Rokhlin's theorem.
- **Step graphons** &mdash; Measurable partitions (`MeasurablePartition`), step functions, stepification, and partition operations (splitting, refinement).
- **Regularity** &mdash; Energy of partitions, energy increment under refinement, the full Szemer&eacute;di regularity lemma (`regularity`).
- **Homomorphism densities** &mdash; Graph homomorphism density (`homDensity`), the counting lemma (`homDensity_sub_le`), and weighted homomorphism sums.
- **Compactness** &mdash; Total boundedness via partition grids (`totallyBounded`), completeness via limit construction (`complete`).
- **Inverse counting** &mdash; Step inverse counting, quantitative inverse counting lemma (`cutDistance_le_of_homDensity_close`), and convergence equivalence (`cutDistance_tendsto_iff_homDensity_tendsto`).

## Axioms

The formalization uses two mathematical axioms beyond Lean's type theory:

| Axiom | Status | Used by |
|-------|--------|---------|
| **Rokhlin's theorem** (isomorphism of standard Borel probability spaces) | sorry'd (`exists_common_extension`) | Cut distance triangle inequality, partition alignment, compactness |
| **Algebraic determination** (Lov&aacute;sz Theorem 5.30, k&ge;2) | sorry'd (`matrix_quotient_of_weightedHomSum_eq_pos`) | Inverse counting lemma core |

All other results are fully proved.

## Components

| File | Contents |
|------|----------|
| `Graphon/Basic.lean` | Graphon definition, symmetry, boundedness, AE equivalence |
| `Graphon/Pullback.lean` | Pullback under measure-preserving maps |
| `Graphon/Step.lean` | Measurable partitions, step functions, stepification |
| `Graphon/Approximation.lean` | Rectangle averages, cut norm approximation, partition splitting |
| `Graphon/CutDistance.lean` | Cut norm, cut distance, metric properties, Rokhlin interface |
| `Graphon/Regularity.lean` | Energy, energy increment, regularity lemma |
| `Graphon/Counting.lean` | Homomorphism density, counting lemma |
| `Graphon/Compactness.lean` | Total boundedness, completeness, limit construction |
| `Graphon/MatrixDetermination.lean` | Algebraic determination of step graphons |
| `Graphon/InverseCounting.lean` | Inverse counting lemma, convergence equivalence |
| `Graphon/Convergence.lean` | Top-level convergence characterization |

## Resources

- [Blueprint (web)](https://cameronfreer.github.io/graphon/blueprint/) &middot; [Blueprint (pdf)](https://cameronfreer.github.io/graphon/blueprint/blueprint.pdf)
- [API docs](https://cameronfreer.github.io/graphon/docs/)
- [Dependency graph](https://cameronfreer.github.io/graphon/blueprint/dep_graph_document.html)

## References

- Lov&aacute;sz, L. (2012). *Large Networks and Graph Limits*. AMS Colloquium Publications, vol. 60.
- Borgs, C., Chayes, J. T., Lov&aacute;sz, L., S&oacute;s, V. T., &amp; Vesztergombi, K. (2008). Convergent sequences of dense graphs I. *Advances in Mathematics*, 219(6), 1801&ndash;1851.
- Borgs, C., Chayes, J. T., Lov&aacute;sz, L., S&oacute;s, V. T., &amp; Vesztergombi, K. (2012). Convergent sequences of dense graphs II. *Annals of Mathematics*, 176(1), 151&ndash;219.
- Szemer&eacute;di, E. (1978). Regular partitions of graphs. *Probl&egrave;mes combinatoires et th&eacute;orie des graphes*, 260, 399&ndash;401.
