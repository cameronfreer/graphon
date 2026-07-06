# Graphons in Lean 4

A formalization of graphons in Lean 4 with Mathlib, based on Part 3 of Lovász's *Large Networks and Graph Limits*.

**[Homepage](https://cameronfreer.github.io/graphon/)** · **[Blueprint](https://cameronfreer.github.io/graphon/blueprint/)** · **[API docs](https://cameronfreer.github.io/graphon/docs/)** · **[Dependency graph](https://cameronfreer.github.io/graphon/blueprint/dep_graph_document.html)**

## Overview

A **graphon** is a symmetric measurable function `W : α² → [0,1]` on a probability space that represents the limit of a convergent sequence of dense graphs. This library formalizes the core theory of graphons, including cut distance, regularity, compactness, and the counting/inverse counting lemmas, culminating in the equivalence of cut distance convergence and homomorphism density convergence.

## Main Results

- **Cut distance pseudometric** — symmetry, triangle inequality, non-negativity, pullback invariance under measure-preserving bijections (`cutDistance_symm`, `cutDistance_triangle`, `cutDistance_pullback_eq_zero`)
- **Frieze–Kannan weak regularity lemma** — every graphon admits a step approximation of bounded complexity (`regularity`)
- **Counting lemma** — small cut distance implies similar homomorphism densities (`homDensity_sub_le`)
- **Inverse counting lemma** — finitely many test graphs control cut distance up to ε (`cutDistance_le_of_homDensity_close`)
- **Compactness** — total boundedness and completeness of the graphon pseudometric space (`totallyBounded`, `complete`)
- **Convergence equivalence** — cut distance convergence ⟺ convergence of all homomorphism densities (`cutDistance_tendsto_iff_homDensity_tendsto`)

## Proof Status

Three live `sorry` blockers remain, all on the path to the final determination theorem:

| Pending result | Location | Notes |
|----------------|----------|-------|
| **Rokhlin's theorem** | `exists_common_extension` | Mathlib has `PolishSpace.measurableEquiv` but not the measure-preserving version |
| **Twin-free bijection** (Lovász Theorem 5.30 core) | `twinfree_bijection_of_weightedHomSum_eq` | The cross-matrix algebraic core. The dispatchers `matrix_quotient_of_weightedHomSum_eq` / `_pos` contain no local `sorry` but remain sorry-dependent on this theorem. The single-matrix Lovász rank/orbit machinery (`Graphon/Lovasz.lean`) is fully proved. |
| **Determination pending theorem** | `cutDistance_zero_of_homDensity_eq` | Depends on both of the above, plus its own uniform-regularity assembly (currently a bare `sorry`) |

In addition, seven `sorry` statements are deliberately retained as **documentation of refuted conjectures** (in `Lovasz.lean`, `Spectral.lean`, and `MatrixDetermination.lean`); each is marked FALSE/REFUTED in its docstring and nothing depends on it. The raw project sorry count is therefore 10, of which only the three above are live. No custom axioms are introduced.

## Files

| File | Status | Contents |
|------|--------|----------|
| `Graphon/Basic.lean` | Core | Graphon definition, symmetry, boundedness, AE equivalence |
| `Graphon/Pullback.lean` | Core | Pullback under measure-preserving maps |
| `Graphon/Step.lean` | Core | Measurable partitions, step functions, stepification |
| `Graphon/HomDensity.lean` | Core | Homomorphism density definition and basic properties |
| `Graphon/CutNorm.lean` | Core | Cut norm, graphon integrability |
| `Graphon/Approximation.lean` | Core | Rectangle averages, cut norm approximation, partition splitting |
| `Graphon/CutDistance.lean` | Core | Cut distance, pseudometric properties, Rokhlin interface |
| `Graphon/Regularity.lean` | Core | Energy, energy increment, Frieze–Kannan weak regularity lemma |
| `Graphon/Counting.lean` | Core | Homomorphism density, counting lemma |
| `Graphon/Compactness.lean` | Core | Total boundedness, completeness, limit construction |
| `Graphon/CaiGovorov.lean` | Core | Graph-free Vandermonde argument (Cai–Govorov §4) |
| `Graphon/Lovasz.lean` | Core | Connection-matrix algebra (Lovász §3), orbit separation, rank theorem |
| `Graphon/SimpleRank.lean` | Core | K=1 simple-graph rank theorem, algebra-atom framing |
| `Graphon/CycleKrylov.lean` | Core | Cycle–Krylov spectral slice of the square-moment descent |
| `Graphon/MatrixDetermination.lean` | Core | Algebraic determination of step graphons |
| `Graphon/InverseCounting.lean` | Core | Inverse counting lemma, convergence equivalence |
| `Graphon/Convergence.lean` | Core | Top-level convergence characterization |
| `Graphon/Operations.lean` | Experimental | Pointwise product |
| `Graphon/Operator.lean` | Experimental | Kernel operator (pointwise definition) |
| `Graphon/Sampling.lean` | Experimental | Expected edge density |
| `Graphon/Spectral.lean` | Frozen | Refuted closed-walk conjectures (#77), retained as documentation; outside the root import tree |

## Design Decisions

### Parameterization by Probability Space

Rather than hardcoding the unit interval `[0,1]`, we parameterize graphons by a probability space `(α, μ)` where `μ` satisfies `[IsProbabilityMeasure μ]`. This provides:
- Greater generality for theoretical development
- Cleaner statements of pullback/pushforward operations
- The canonical type `GraphonI` specializes to the unit interval with Lebesgue measure

### AEEqFun for Quotient Structure

We represent kernels as elements of `AEEqFun` (L⁰ space), which automatically handles quotienting by almost-everywhere equality, measurability requirements, and composition with measurable functions.

### Real Codomain with AE Bounds

We use `ℝ` as the codomain (not `Set.Icc 0 1`) because it enables subtraction for cut distance calculations and avoids dependent type complications. Bounds are enforced via a.e. conditions.

## Building

Requires Lean 4 and Mathlib. To build:

```bash
lake update
lake build
```

## Dependencies

- Lean 4
- Mathlib (pinned to specific revision for reproducibility)

## References

- Lovász, L. *Large Networks and Graph Limits*. AMS Colloquium Publications, vol. 60, 2012.
- Frieze, A. & Kannan, R. "Quick Approximation to Matrices and Applications." *Combinatorica* 19(2), 175–220, 1999.
- Borgs, C., Chayes, J. T., Lovász, L., Sós, V. T., & Vesztergombi, K. "Convergent sequences of dense graphs I." *Advances in Mathematics* 219(6), 1801–1851, 2008.

## Citation

```bibtex
@software{freer2026graphon,
  author = {Cameron Freer},
  title = {Graphon Theory in {Lean} 4},
  url = {https://github.com/cameronfreer/graphon},
  year = {2026}
}
```

## License

Apache 2.0

## Author

Cameron Freer
