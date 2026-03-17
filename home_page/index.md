---
---

A Lean 4 formalization of **graphon theory** &mdash; the theory of limits of dense graph sequences &mdash; building on [Mathlib](https://leanprover-community.github.io/mathlib4/).

## Main Results

- **Cut distance pseudometric** &mdash; Cut distance is a pseudometric on graphons: symmetry, triangle inequality, and non-negativity, with pullback invariance under measure-preserving bijections.
- **Frieze&ndash;Kannan weak regularity lemma** &mdash; Every graphon admits arbitrarily fine regular step-function approximations, with quantitative energy increment bounds.
- **Counting lemma** &mdash; Small cut distance implies similar homomorphism densities for all finite graphs.
- **Inverse counting lemma** &mdash; For every &epsilon; > 0, finitely many test graphs control cut distance up to &epsilon; (the quantitative inverse counting lemma).
- **Compactness** &mdash; The cut-distance quotient modulo weak isomorphism is a compact metric space; concretely, we prove total boundedness and completeness of the graphon pseudometric space.
- **Convergence equivalence** &mdash; A sequence of graphons converges in cut distance if and only if all homomorphism densities converge.

## Scope

The formalization covers:

- **Graphon infrastructure** &mdash; Graphons as symmetric measurable functions on probability spaces, with AE equivalence classes (`Graphon`).
- **Cut distance** &mdash; Cut norm, cut distance as infimum over measure-preserving couplings (`cutNormDiff`, `cutDistance`), pseudometric properties including the triangle inequality via Rokhlin's theorem.
- **Step graphons** &mdash; Measurable partitions (`MeasurablePartition`), step functions, stepification, and partition operations (splitting, refinement).
- **Regularity** &mdash; Energy of partitions, energy increment under refinement, the Frieze&ndash;Kannan weak regularity lemma (`regularity`).
- **Homomorphism densities** &mdash; Graph homomorphism density (`homDensity`), the counting lemma (`homDensity_sub_le`), and weighted homomorphism sums.
- **Compactness** &mdash; Total boundedness via partition grids (`totallyBounded`), completeness via limit construction (`complete`).
- **Inverse counting** &mdash; Step inverse counting, quantitative inverse counting lemma (`cutDistance_le_of_homDensity_close`), and convergence equivalence (`cutDistance_tendsto_iff_homDensity_tendsto`).

## Proof Status

Three remaining `sorry` declarations, driven by two main missing mathematical inputs: a Rokhlin-style alignment theorem and the positive-weight algebraic determination core. No custom axioms are introduced; these are `sorry`s that will be replaced with proofs.

| Pending result | `sorry` location | Used by | Progress |
|----------------|-----------------|---------|----------|
| **Rokhlin's theorem** (isomorphism of standard Borel probability spaces) | `exists_common_extension` | Cut distance triangle inequality, partition alignment, compactness | Mathlib has `PolishSpace.measurableEquiv` but not the measure-preserving version; proving this is in progress |
| **Algebraic determination** (Lov&aacute;sz Theorem 5.30, k&ge;2) | `matrix_quotient_of_weightedHomSum_eq` (positive-weight case) | Inverse counting lemma core | The k=1 case is fully proved; the k&ge;2 case requires graph algebra separation arguments that are partially built |
| **Algebraic determination axiom** (depends on the above two) | `cutDistance_zero_of_homDensity_eq` | Convergence equivalence | Proved modulo Rokhlin + algebraic determination |

All other results &mdash; including the regularity lemma, counting lemma, compactness, and the full convergence equivalence &mdash; are fully proved.

## Components

| File | Contents |
|------|----------|
| `Graphon/Basic.lean` | Graphon definition, symmetry, boundedness, AE equivalence |
| `Graphon/Pullback.lean` | Pullback under measure-preserving maps |
| `Graphon/Step.lean` | Measurable partitions, step functions, stepification |
| `Graphon/Approximation.lean` | Rectangle averages, cut norm approximation, partition splitting |
| `Graphon/CutDistance.lean` | Cut norm, cut distance, pseudometric properties, Rokhlin interface |
| `Graphon/Regularity.lean` | Energy, energy increment, Frieze&ndash;Kannan weak regularity lemma |
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
- Frieze, A. &amp; Kannan, R. (1999). Quick approximation to matrices and applications. *Combinatorica*, 19(2), 175&ndash;220.
- Borgs, C., Chayes, J. T., Lov&aacute;sz, L., S&oacute;s, V. T., &amp; Vesztergombi, K. (2008). Convergent sequences of dense graphs I. *Advances in Mathematics*, 219(6), 1801&ndash;1851.
- Borgs, C., Chayes, J. T., Lov&aacute;sz, L., S&oacute;s, V. T., &amp; Vesztergombi, K. (2012). Convergent sequences of dense graphs II. *Annals of Mathematics*, 176(1), 151&ndash;219.
