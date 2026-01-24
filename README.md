# Graphon Library for Lean 4

A formalization of graphon theory in Lean 4 with mathlib, based on Part 3 of Lovász's *Large Networks and Graph Limits*.

## Overview

A **graphon** is a symmetric measurable function `W : [0,1]² → [0,1]` that represents the limit of a convergent sequence of dense graphs. Graphons are fundamental objects in the theory of graph limits, providing a way to study large networks through their limiting behavior.

This library aims to formalize the core theory of graphons, including:
- The definition of graphons as equivalence classes of symmetric kernels *(Phase 1 - complete)*
- Homomorphism densities and their properties *(Phase 3 - planned)*
- The cut distance metric on the space of graphons *(Phase 8 - planned)*
- Approximation theorems connecting finite graphs to graphons *(Phase 9 - planned)*

## Current Status

### Phase 1: Core Types ✓ Complete

Located in `Graphon/Basic.lean`:

| Definition | Description |
|------------|-------------|
| `SymmKernel α μ` | Symmetric element of L⁰(α × α, ℝ), base type for kernels |
| `Graphon α μ` | Symmetric kernel with values in [0,1] a.e. |
| `SignedGraphon α μ` | Symmetric kernel with \|W\| ≤ 1 a.e., for cut distance |
| `GraphonI` | Canonical graphon type on unit interval with Lebesgue measure |

**API available:**
- `Graphon.zero`, `Graphon.one` — constant graphons (limits of empty/complete graphs)
- `Graphon.compl` — complement operation (1 - W)
- `Graphon.symm_ae`, `Graphon.ae_nonneg`, `Graphon.ae_le_one` — basic properties
- `SignedGraphon.ofGraphon` — embed a graphon as a signed graphon
- `SignedGraphon.sub` — difference of two graphons

**Simp lemmas:** `compl_compl`, `compl_zero`, `compl_one`

## Design Decisions

### Parameterization by Probability Space

Rather than hardcoding the unit interval `[0,1]`, we parameterize graphons by a probability space `(α, μ)` where `μ` satisfies `[IsProbabilityMeasure μ]`. This provides:
- Greater generality for theoretical development
- Cleaner statements of pullback/pushforward operations
- The canonical type `GraphonI` specializes to the unit interval with Lebesgue measure

The base type `SymmKernel` is defined for general measures, but `Graphon` and `SignedGraphon` operations require probability measures to ensure proper normalization and that swap is measure-preserving on the product space.

### AEEqFun for Quotient Structure

We represent kernels as elements of `AEEqFun` (L⁰ space), which automatically handles:
- Quotienting by almost-everywhere equality
- Measurability requirements
- Composition with measurable functions

### Real Codomain with AE Bounds

We use `ℝ` as the codomain (not `Set.Icc 0 1`) because:
- Enables subtraction for cut distance calculations
- Avoids dependent type complications
- Bounds are enforced via a.e. conditions

## Building

Requires Lean 4 and mathlib. To build:

```bash
lake update
lake build
```

## Roadmap

### Phase 2: Step Graphons (Next)

File: `Graphon/Step.lean`

- `MeasurablePartition` — finite measurable partition of probability space
- `Graphon.step` — step graphon from partition and matrix of values
- `Graphon.ofSimpleGraph` — graphon from finite simple graph (key bridge to combinatorics)
- Theorem: `integral_ofSimpleGraph` relating integral to edge density

### Phase 3: Homomorphism Densities

File: `Graphon/HomDensity.lean`

- `Graphon.homDensity F W` — homomorphism density t(F, W)
- `Graphon.inducedDensity F W` — induced subgraph density t_ind(F, W)
- Bridge theorem: `homDensity F (ofSimpleGraph G) = |Hom(F,G)| / n^|V(F)|`
- Basic properties: `homDensity_edge`, bounds, inclusion-exclusion

### Phase 4: Pullbacks and Weak Isomorphism

File: `Graphon/Pullback.lean`

- `Graphon.pullback φ W` — pullback by measure-preserving map
- `WeakIso` — weak isomorphism equivalence relation
- Theorem: `homDensity F (pullback φ W) = homDensity F W`

### Phase 5: Operations

File: `Graphon/Operations.lean`

- Direct sum of graphons
- Pointwise product
- Operator product (composition as integral operators)

### Phase 6: Kernel Operators

File: `Graphon/Operator.lean`

- `Graphon.toOperator` — bounded linear operator T_W : L² → L²
- Self-adjointness, compactness
- Spectral properties

### Phase 7: Cut Norm

File: `Graphon/CutNorm.lean`

- `cutNorm W = sup_{S,T} |∫_{S×T} W|`
- Seminorm properties
- Relationship to operator norm

### Phase 8: Cut Distance

File: `Graphon/CutDistance.lean`

- `cutDistance U W = inf_φ cutNorm (U - pullback φ W)`
- Pseudometric structure
- Completeness of quotient space

### Phase 9: Approximation

File: `Graphon/Approximation.lean`

- `stepify P W` — step function approximation
- Refinement stability
- Density of step graphons

### Phase 10: Counting Lemma

File: `Graphon/Counting.lean`

- Main theorem: `|homDensity F U - homDensity F W| ≤ C(F) · cutNorm (U - W)`
- Corollaries for convergence

## References

- [Lovász, L. *Large Networks and Graph Limits*. American Mathematical Society, 2012.](https://web.cs.elte.hu/~lovasz/bookxx/hombook-almost.final.pdf)
- [Borgs, C., Chayes, J., Lovász, L., Sós, V., Vesztergombi, K. "Convergent sequences of dense graphs I: Subgraph frequencies, metric properties and testing." *Advances in Mathematics* 219.6 (2008): 1801-1851.](https://arxiv.org/abs/math/0702004)

## Dependencies

- Lean 4
- mathlib (pinned to specific revision for reproducibility)

**Current mathlib imports (Phase 1):**
- `Mathlib.MeasureTheory.Function.AEEqFun` — L⁰ spaces
- `Mathlib.MeasureTheory.Measure.Prod` — product measures
- `Mathlib.MeasureTheory.Constructions.UnitInterval` — unit interval as probability space
- `Mathlib.Tactic.Linarith` — linear arithmetic tactic

**Planned mathlib imports (Phase 2+):**
- `Mathlib.Combinatorics.SimpleGraph.Density` — edge density (Phase 2)
- `Mathlib.Combinatorics.SimpleGraph.Maps` — graph homomorphisms (Phase 3)
- `Mathlib.MeasureTheory.Constructions.Pi` — product measures for densities (Phase 3)

## License

Apache 2.0

## Author

Cameron Freer
