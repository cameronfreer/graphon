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

**No live `sorry` remains.** Every headline theorem — including the determination theorem
`cutDistance_zero_of_homDensity_eq`, compactness (`totallyBounded`, `complete`, `compact`),
and the First Sampling Lemma — verifies with the standard axioms only
(`propext`, `Classical.choice`, `Quot.sound`). The two formerly-live blockers were closed:

| Formerly pending | Resolution |
|------------------|------------|
| **Rokhlin / measure-isomorphism gap** | Closed 2026-07-09 (campaigns R0–R3). The false `exists_common_extension` monolith was replaced by four corrected cores, all proved from the atomless standard-Borel measure-isomorphism theorem built graphon-independently in `Graphon/MeasureIso.lean`; the final overlay theorem `exists_mpEquiv_cutNormDiff_lt_add` is proved in `Graphon/Overlay.lean` (coupling matrix realized exactly by an MP bijection — no Birkhoff needed) |
| **First Sampling Lemma** | Proved 2026-07-08 (`first_sampling_lemma`, `Graphon/SamplingLemma.lean`): for every ε, η some sample size k works for every graphon simultaneously (Lovász Lemma 10.16 / BCLSV Thm 4.6), by recombining the pointwise AFKK cut-guessing bound (`Graphon/SamplingPointwise.lean`) with the finite rounding certificate (`Graphon/SamplingRounding.lean`) |

**Algebraic determination is PROVED** (2026-07-06): `matrix_quotient_of_weightedHomSum_eq`
(Lovász Theorem 5.30, k≥2 positive-weight case) is axiom-clean, via the twin-free bijection
`twinfree_bijection_of_weightedHomSum_eq` and the cross-matrix super transfer
(`Graphon/CrossSuper.lean`).

The project contains **zero `sorry` statements** (issue #19, completed 2026-07-11): the formerly-retained known-false stubs in `MatrixDetermination.lean`, `Lovasz.lean`, and `Spectral.lean` were all deleted, with their refutation documentation kept as prose. The CI census enforces strictly zero sorry/admit tokens. No custom axioms are introduced.

## Files

| File | Status | Contents |
|------|--------|----------|
| `Graphon/Basic.lean` | Core | Graphon definition, symmetry, boundedness, AE equivalence |
| `Graphon/Pullback.lean` | Core | Pullback under measure-preserving maps |
| `Graphon/Step.lean` | Core | Measurable partitions, step functions, stepification |
| `Graphon/HomDensity.lean` | Core | Homomorphism density definition and basic properties |
| `Graphon/CutNorm.lean` | Core | Cut norm, graphon integrability |
| `Graphon/Approximation.lean` | Core | Rectangle averages, cut norm approximation, partition splitting |
| `Graphon/CutDistance.lean` | Core | Cut distance, pseudometric properties, three of the four Rokhlin cores |
| `Graphon/MeasureIso.lean` | Core | Atomless standard-Borel measure-isomorphism theorem (graphon-independent; mod-0 iso + everywhere upgrade) |
| `Graphon/Overlay.lean` | Core | Overlay theorem: an MP bijection nearly achieves the cut distance (fourth Rokhlin core) |
| `Graphon/Regularity.lean` | Core | Energy, energy increment, Frieze–Kannan weak regularity lemma |
| `Graphon/Counting.lean` | Core | Homomorphism density, counting lemma |
| `Graphon/Compactness.lean` | Core | Total boundedness, completeness, limit construction |
| `Graphon/GraphonSpace.lean` | Core | Graphon space: compact Polish standard-Borel metric quotient under weak isomorphism |
| `Graphon/InfiniteGraph.lean` | Core | Infinite graph space: compact Polish standard-Borel; finite restrictions + measure extensionality (A–H brick A1) |
| `Graphon/CaiGovorov.lean` | Core | Graph-free Vandermonde argument (Cai–Govorov §4) |
| `Graphon/Lovasz.lean` | Core | Connection-matrix algebra (Lovász §3), orbit separation, rank theorem |
| `Graphon/CrossSuper.lean` | Core | Cross-matrix super-surjective transfer (Cai–Govorov Lemma 5.1, partition form) |
| `Graphon/SimpleRank.lean` | Core | K=1 simple-graph rank theorem, algebra-atom framing |
| `Graphon/CycleKrylov.lean` | Core | Cycle–Krylov spectral slice of the square-moment descent |
| `Graphon/MatrixDetermination.lean` | Core | Algebraic determination of step graphons |
| `Graphon/SamplingICL.lean` | Core | Sampling route: finite-graph embedding, good mass, First Sampling Lemma interface, K-independent quantitative ICL |
| `Graphon/SamplingConcentration.lean` | Core | Concentration scaffold: conditional edge distribution, weighted sampled graphon, two-stage reduction of the First Sampling Lemma |
| `Graphon/SamplingRounding.lean` | Core | Rounding half of the First Sampling Lemma, PROVED: deterministic cut certificate + finite Chernoff/union bound (`rounding_event_of_large_k`) |
| `Graphon/SamplingPointwise.lean` | Core | Pointwise half of the First Sampling Lemma: AFKK / Lovász-10.7 cut-guessing bound (`point_sampling_event_of_large_k`), McDiarmid-at-MGF + soft-max infrastructure |
| `Graphon/SamplingLemma.lean` | Core | First Sampling Lemma (`first_sampling_lemma`): recombination of the two concentration events; K-independent quantitative ICL |
| `Graphon/SamplingLaw.lean` | Core | Finite sample law: `samplePMF`/`sampleLaw`, Möbius/upper-transform engine, relabeling invariance, arbitrary-injection consistency |
| `Graphon/SamplingExamples.lean` | Core | Constant graphon samples the binomial random graph `G(V, p)` (`sampleLaw_const_eq_binomial`) |
| `Graphon/SamplingDetermination.lean` | Core | Sample laws determine the graphon (`samplePMF_eq_all_iff_weaklyIsomorphic`, `GraphonSpace` form) |
| `Graphon/SamplingCoordinates.lean` | Core | Continuous point-separating sample-law coordinates; compact coordinate embedding of the graphon space |
| `Graphon/ExchangeableGraphLaw.lean` | Core | Exchangeable graph laws (consistent finite marginals), graphon mixtures, mixtures are exchangeable |
| `Graphon/MixtureConvergence.lean` | Core | Weak-convergence layer: mixture coordinates as integrals, Prokhorov extraction, empirical mixing measures |
| `Graphon/HomDensityAlgebra.lean` | Core | Hom-density coordinates on the graphon space; multiplicativity over disjoint unions |
| `Graphon/MixtureCoordinates.lean` | Core | Shared mixture-coordinate layer: hom-density coordinates as BCFs; integrals = mixture upper masses |
| `Graphon/MixtureUniqueness.lean` | Core | Uniqueness of the graphon mixture: coordinate algebra separates points; `mixtureExchangeableLaw` injective |
| `Graphon/SamplingFinite.lean` | Core | Exact finite-sampling formula: sampling an embedded finite graph = uniform vertex-map pullback |
| `Graphon/MixtureExistence.lean` | Core | Existence of the graphon mixture: collision estimate for empirical mixing measures; every exchangeable law is a mixture |
| `Graphon/MixtureRepresentation.lean` | Core | Diaconis–Janson representation theorem: exchangeable graph laws = graphon mixtures, uniquely |
| `Graphon/MixtureExtremality.lean` | Core | Diaconis–Janson extremality: dissociated exchangeable laws = Dirac mixtures |
| `Graphon/InfiniteLaw.lean` | Core | Infinite exchangeable graph law: unique compactness-based Kolmogorov extension of the finite marginals (A–H brick A2) |
| `Graphon/InfiniteExchangeability.lean` | Core | Exchangeability of the infinite law; `ExchangeableGraphLaw ≃ InfiniteExchangeableGraphLaw` (A–H brick A3) |
| `Graphon/InfiniteRepresentation.lean` | Core | Infinite Diaconis–Janson/Aldous–Hoover correspondence: mixing measures ≃ infinite exchangeable laws |
| `Graphon/InfiniteSampleLaw.lean` | Core | Canonical infinite law of a graphon class: marginals, continuity, closed embedding |
| `Graphon/EmpiricalGraphon.lean` | Core | Empirical graphons of an infinite exchangeable graph: distributional convergence to the representing measure |
| `Graphon/InfiniteExtremality.lean` | Core | Extremality for infinite exchangeable laws: dissociated ↔ single-class canonical law ↔ Dirac |
| `Graphon/InfiniteSampler.lean` | Core | Explicit infinite sampler for a fixed graphon: explicit sampler realizes the infinite law exactly |
| `Graphon/MixtureKernel.lean` | Core | Barycenter interpretation: the represented infinite law = Measure.bind mixture of fiber laws |
| `Graphon/InfiniteSamplingConvergence.lean` | Core | Convergence in probability of the sampled empirical graphons |
| `Graphon/McDiarmid.lean` | Core | Bounded-differences concentration as `HasSubgaussianMGF` |
| `Graphon/SampleExposure.lean` | Core | Fixed-`F` exponential hom-density concentration for `G(k,W)` + summability bridge |
| `Graphon/AlmostSureSampling.lean` | Core | Almost-sure convergence of the sampled empirical graphons (Prop 11.32) |
| `Graphon/LimitGraphon.lean` | Core | The empirical graphon limit as a universal measurable random variable |
| `Graphon/DissociatedSampler.lean` | Core | Functional Aldous–Hoover for dissociated laws: dissociated = law of an explicit W-random graph |
| `Graphon/VertexTail.lean` | Core | Vertex-tail shift + σ-algebras; deletion stability; limitGraphon is tail-measurable |
| `Graphon/RestrictionIndependence.lean` | Core | Vertex-tail σ-algebra + restriction independence ⟹ dissociation |
| `Graphon/RestrictionIndependenceReverse.lean` | Core | Dissociation ⟹ restriction independence; the five-way DJ Theorem 5.5 extremality equivalence |
| `Graphon/InvariantAction.lean` | Core | Finite-permutation invariance of `limitGraphon`; invariant σ-algebra; `IsErgodic` (issue #59 part 1) |
| `Graphon/ErgodicDecomposition.lean` | Core | Fixed-fiber ergodicity: `RestrictionIndependent ⟺ IsErgodic ⟺ dissociated`; the six-way ergodic-decomposition DJ Theorem 5.5; `limitGraphon` generates the invariant σ-algebra mod null (issue #59 part 2) |
| `Graphon/RelationalSignature.lean` | Foundation | Generic AHK program (umbrella #103) R0 checkpoint: multi-sorted `RelSignature`, `RelCoord`/`RelStructure` carriers, external `NoNullary`, sortwise `map`/`comap`, digraph/bipartite/ternary examples (issue #110) |
| `Graphon/RelationalStructure.lean` | Foundation | Generic AHK program R1a: sortwise actions on relational structures — `map`/`comap` functoriality, `restrict`/`relabel`, finite restrictions `restrictFin`/`restrictLE`, padding `pad` (+ `restrict_pad`), restriction composition (issue #104) |
| `Graphon/RelationalTopology.lean` | Foundation | Generic AHK program R1b: Boolean-product topology/σ-algebra on `RelStructure` — compact (no countability) + Polish/standard-Borel (countable coords), measurable restrictions, cylinder π-system generating the product σ-algebra, finite-restriction measure extensionality (issue #104) |
| `Graphon/InfiniteDigraph.lean` | Directed | D1 (#84/#85): `InfiniteDigraph` as the one-sort binary R1 instance — inherits compact/standard-Borel + measure extensionality; `Adj`(Prop)/`adjBit`(Bool); `digraphStructureEquiv V` plain carrier equivalence with `Digraph V` (infinite + finite bridges for D2) |
| `Graphon/InverseCounting.lean` | Core | Inverse counting lemma, convergence equivalence |
| `Graphon/Convergence.lean` | Core | Top-level convergence characterization |
| `Graphon/Operations.lean` | Experimental | Pointwise product |
| `Graphon/Operator.lean` | Experimental | Kernel operator (pointwise definition) |
| `Graphon/Sampling.lean` | Core | W-random graph distribution (`sampleMass`: nonneg, sums to 1, hom-density expansion, TV closeness), expected edge density |
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
