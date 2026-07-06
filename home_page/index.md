---
---

A Lean 4 formalization of **graphons** &mdash; the theory of limits of dense graph sequences &mdash; building on [Mathlib](https://leanprover-community.github.io/mathlib4/).

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

Two live `sorry` blockers remain, both driven by one missing mathematical input: a Rokhlin-style alignment theorem. No custom axioms are introduced; these are `sorry`s that will be replaced with proofs.

| Pending result | `sorry` location | Used by | Progress |
|----------------|-----------------|---------|----------|
| **Rokhlin's theorem** (isomorphism of standard Borel probability spaces) | `exists_common_extension` | Cut distance triangle inequality, partition alignment, compactness | Mathlib has `PolishSpace.measurableEquiv` but not the measure-preserving version; proving this is in progress |
| **Determination pending theorem** | `cutDistance_zero_of_homDensity_eq` | Convergence equivalence | Awaits Rokhlin, plus its own uniform-regularity assembly |

**Algebraic determination is PROVED** (2026-07-06): `matrix_quotient_of_weightedHomSum_eq` (Lov&aacute;sz Theorem 5.30, k&ge;2 positive-weight case) is axiom-clean, via the twin-free bijection and the cross-matrix super-surjective transfer (`Graphon/CrossSuper.lean`).

Seven further `sorry` statements are deliberately retained as documentation of refuted conjectures (each marked FALSE/REFUTED in its docstring); no live or public theorem depends on them (a few private off-axis helpers still do &mdash; they are quarantined with their roots). Only the two above are live. All other declarations contain no additional `sorry`s.

## Components

| File | Status | Contents |
|------|--------|----------|
| `Graphon/Basic.lean` | Core | Graphon definition, symmetry, boundedness, AE equivalence |
| `Graphon/Pullback.lean` | Core | Pullback under measure-preserving maps |
| `Graphon/Step.lean` | Core | Measurable partitions, step functions, stepification |
| `Graphon/HomDensity.lean` | Core | Homomorphism density definition and basic properties |
| `Graphon/CutNorm.lean` | Core | Cut norm, graphon integrability |
| `Graphon/Approximation.lean` | Core | Rectangle averages, cut norm approximation, partition splitting |
| `Graphon/CutDistance.lean` | Core | Cut distance, pseudometric properties, Rokhlin interface |
| `Graphon/Regularity.lean` | Core | Energy, energy increment, Frieze&ndash;Kannan weak regularity lemma |
| `Graphon/Counting.lean` | Core | Homomorphism density, counting lemma |
| `Graphon/Compactness.lean` | Core | Total boundedness, completeness, limit construction |
| `Graphon/CaiGovorov.lean` | Core | Graph-free Vandermonde argument (Cai&ndash;Govorov &sect;4) |
| `Graphon/Lovasz.lean` | Core | Connection-matrix algebra (Lov&aacute;sz &sect;3), orbit separation, rank theorem |
| `Graphon/CrossSuper.lean` | Core | Cross-matrix super-surjective transfer (Cai&ndash;Govorov Lemma 5.1, partition form) |
| `Graphon/SimpleRank.lean` | Core | K=1 simple-graph rank theorem, algebra-atom framing |
| `Graphon/CycleKrylov.lean` | Core | Cycle&ndash;Krylov spectral slice of the square-moment descent |
| `Graphon/MatrixDetermination.lean` | Core | Algebraic determination of step graphons |
| `Graphon/InverseCounting.lean` | Core | Inverse counting lemma, convergence equivalence |
| `Graphon/Convergence.lean` | Core | Top-level convergence characterization |
| `Graphon/Operations.lean` | Experimental | Pointwise product |
| `Graphon/Operator.lean` | Experimental | Kernel operator (pointwise definition) |
| `Graphon/Sampling.lean` | Core | W-random graph distribution (`sampleMass`: nonneg, sums to 1, hom-density expansion, TV closeness), expected edge density |
| `Graphon/Spectral.lean` | Frozen | Refuted closed-walk conjectures (#77), retained as documentation; outside the root import tree |

## Resources

- [Blueprint (web)](https://cameronfreer.github.io/graphon/blueprint/) &middot; [Blueprint (pdf)](https://cameronfreer.github.io/graphon/blueprint/blueprint.pdf)
- [API docs](https://cameronfreer.github.io/graphon/docs/)
- [Dependency graph](https://cameronfreer.github.io/graphon/blueprint/dep_graph_document.html)

## References

- Lov&aacute;sz, L. (2012). *Large Networks and Graph Limits*. AMS Colloquium Publications, vol. 60.
- Frieze, A. &amp; Kannan, R. (1999). Quick approximation to matrices and applications. *Combinatorica*, 19(2), 175&ndash;220.
- Borgs, C., Chayes, J. T., Lov&aacute;sz, L., S&oacute;s, V. T., &amp; Vesztergombi, K. (2008). Convergent sequences of dense graphs I. *Advances in Mathematics*, 219(6), 1801&ndash;1851.
- Borgs, C., Chayes, J. T., Lov&aacute;sz, L., S&oacute;s, V. T., &amp; Vesztergombi, K. (2012). Convergent sequences of dense graphs II. *Annals of Mathematics*, 176(1), 151&ndash;219.
