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
- **Cut distance** &mdash; Cut norm, cut distance as infimum over measure-preserving couplings (`cutNormDiff`, `cutDistance`), pseudometric properties including the triangle inequality via the proved Rokhlin coupling cores.
- **Step graphons** &mdash; Measurable partitions (`MeasurablePartition`), step functions, stepification, and partition operations (splitting, refinement).
- **Regularity** &mdash; Energy of partitions, energy increment under refinement, the Frieze&ndash;Kannan weak regularity lemma (`regularity`).
- **Homomorphism densities** &mdash; Graph homomorphism density (`homDensity`), the counting lemma (`homDensity_sub_le`), and weighted homomorphism sums.
- **Compactness** &mdash; Total boundedness via partition grids (`totallyBounded`), completeness via limit construction (`complete`).
- **Inverse counting** &mdash; Step inverse counting, quantitative inverse counting lemma (`cutDistance_le_of_homDensity_close`), and convergence equivalence (`cutDistance_tendsto_iff_homDensity_tendsto`).

## Proof Status

**The advertised program is fully proved.** No live `sorry` remains: every headline theorem &mdash; the determination theorem `cutDistance_zero_of_homDensity_eq`, compactness (`totallyBounded`, `complete`, `compact`), the triangle inequality `cutDistance_triangle`, and the First Sampling Lemma `first_sampling_lemma` &mdash; verifies with the standard axioms only (`propext`, `Classical.choice`, `Quot.sound`). No custom axioms are introduced, and CI enforces the axiom audit and the `sorry` census.

| Formerly pending | Resolution |
|------------------|------------|
| **Rokhlin-style alignment** (was `exists_common_extension`) | The original monolith was shown unprovable as stated and replaced by four corrected cores, all proved from the atomless standard-Borel measure-isomorphism theorem built in `Graphon/MeasureIso.lean`; the final overlay core (`exists_mpEquiv_cutNormDiff_lt_add`) is proved in `Graphon/Overlay.lean` |
| **First Sampling Lemma** (Lov&aacute;sz Lemma 10.16 / BCLSV Thm 4.6) | Proved (`first_sampling_lemma`, `Graphon/SamplingLemma.lean`) by recombining the pointwise AFKK cut-guessing bound (`Graphon/SamplingPointwise.lean`) with the finite rounding certificate (`Graphon/SamplingRounding.lean`) |

**Algebraic determination is PROVED** (2026-07-06): `matrix_quotient_of_weightedHomSum_eq` (Lov&aacute;sz Theorem 5.30, k&ge;2 positive-weight case) is axiom-clean, via the twin-free bijection and the cross-matrix super-surjective transfer (`Graphon/CrossSuper.lean`).

The project contains zero `sorry` statements (issue #19, completed 2026-07-11): the formerly-retained known-false stubs in `MatrixDetermination.lean`, `Lovasz.lean`, and `Spectral.lean` were all deleted, with their refutation documentation kept as prose. The CI census enforces strictly zero sorry/admit tokens.

## Components

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
| `Graphon/Regularity.lean` | Core | Energy, energy increment, Frieze&ndash;Kannan weak regularity lemma |
| `Graphon/Counting.lean` | Core | Homomorphism density, counting lemma |
| `Graphon/Compactness.lean` | Core | Total boundedness, completeness, limit construction |
| `Graphon/GraphonSpace.lean` | Core | Graphon space: compact Polish standard-Borel metric quotient under weak isomorphism |
| `Graphon/InfiniteGraph.lean` | Core | Infinite graph space: compact Polish standard-Borel; finite restrictions + measure extensionality (A–H brick A1) |
| `Graphon/CaiGovorov.lean` | Core | Graph-free Vandermonde argument (Cai&ndash;Govorov &sect;4) |
| `Graphon/Lovasz.lean` | Core | Connection-matrix algebra (Lov&aacute;sz &sect;3), orbit separation, rank theorem |
| `Graphon/CrossSuper.lean` | Core | Cross-matrix super-surjective transfer (Cai&ndash;Govorov Lemma 5.1, partition form) |
| `Graphon/SimpleRank.lean` | Core | K=1 simple-graph rank theorem, algebra-atom framing |
| `Graphon/CycleKrylov.lean` | Core | Cycle&ndash;Krylov spectral slice of the square-moment descent |
| `Graphon/MatrixDetermination.lean` | Core | Algebraic determination of step graphons |
| `Graphon/SamplingICL.lean` | Core | Sampling route: finite-graph embedding, good mass, First Sampling Lemma interface, K-independent quantitative ICL |
| `Graphon/SamplingConcentration.lean` | Core | Concentration scaffold: conditional edge distribution, weighted sampled graphon, two-stage reduction of the First Sampling Lemma |
| `Graphon/SamplingRounding.lean` | Core | Rounding half of the First Sampling Lemma, PROVED: deterministic cut certificate + finite Chernoff/union bound (`rounding_event_of_large_k`) |
| `Graphon/SamplingPointwise.lean` | Core | Pointwise half of the First Sampling Lemma: AFKK / Lov&aacute;sz-10.7 cut-guessing bound (`point_sampling_event_of_large_k`), McDiarmid-at-MGF + soft-max infrastructure |
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
