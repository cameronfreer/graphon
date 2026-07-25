---
---

Graphons, exchangeability, and relational limit theory, formalized in Lean 4 on top of
[Mathlib](https://leanprover-community.github.io/mathlib4/).

**Core graphon program complete · zero placeholders · standard axioms only**

## Research programs

**Graphon analysis.** Graphons as symmetric measurable functions on a probability space; the cut
norm and cut distance; step approximations and Frieze&ndash;Kannan regularity; the counting and
inverse counting lemmas; compactness of the graphon space. Underneath sits an atomless
standard-Borel measure-isomorphism theorem and the overlay theorem, which together replace the
coupling step that classical treatments leave implicit.

**Diaconis&ndash;Janson and Aldous&ndash;Hoover.** Exchangeable random graphs, graphon mixtures,
and the representation theorem identifying the two; the infinite-law correspondence; empirical
graphons and their almost-sure convergence; the extremality equivalences characterizing
dissociated laws.

**Generic relational exchangeability.** A multi-sorted relational signature framework: carriers,
topology, exchangeable laws, ergodicity, and equality patterns, developed for arbitrary arity
rather than graphs alone &mdash; the setting of the Aldous&ndash;Hoover&ndash;Kallenberg theorem.

**Digraphons.** Directed graph limits: the five-component digraphon with its four reciprocal-edge
pair kernels, the directed sampler, and the special families (graphon embeddings, tournaments,
asymmetric kernels).

## Landmark results

- **`cutDistance_triangle`** &mdash; the cut distance is a pseudometric, via four corrected
  Rokhlin-style coupling cores.
- **`regularity`** &mdash; Frieze&ndash;Kannan weak regularity: bounded-complexity step
  approximation of every graphon.
- **`cutDistance_tendsto_iff_homDensity_tendsto`** &mdash; cut-distance convergence is exactly
  convergence of all homomorphism densities.
- **`first_sampling_lemma`** &mdash; a single sample size works for every graphon simultaneously.
- **`samplePMF_eq_all_iff_weaklyIsomorphic`** &mdash; the sample laws determine the graphon.
- **`graphon_mixture_representation`** &mdash; the Diaconis&ndash;Janson theorem: exchangeable
  graph laws are graphon mixtures, uniquely.
- **`tfae_ergodic_extremality`** &mdash; a six-way equivalence: dissociated, restriction
  independent, tail trivial, ergodic, extreme, Dirac-represented.
- **`InfiniteRelExchangeableLaw.condIndep_fixingAlgebra`** &mdash; for *every* exchangeable
  relational law, the fixing &sigma;-algebras of two finite vertex sets are conditionally
  independent given their intersection.
- **`ofTournament_sample_isTournament`** &mdash; the tournament digraphon almost surely samples
  a tournament: no loops, and exactly one direction between any two distinct vertices.

## Current frontier

The classical graphon program and the graph-level Diaconis&ndash;Janson / Aldous&ndash;Hoover
theory are complete. The **generic functional Aldous&ndash;Hoover&ndash;Kallenberg theorem** for
arbitrary relational signatures is in progress: the forward direction and the conditional
independence underpinning the converse are proved, while the coherent factor realization and the
kernel recursion are still being built. The
[open issues](https://github.com/cameronfreer/graphon/issues) track this work.

## Explore the formalization

- [Blueprint (web)]({{ '/blueprint/' | relative_url }}) &mdash; statements,
  dependencies, and the proof narrative
- [Blueprint (pdf)]({{ '/blueprint/blueprint.pdf' | relative_url }})
- [API documentation]({{ '/docs/' | relative_url }}) &mdash; the complete module
  and declaration inventory
- [Dependency graph]({{ '/blueprint/dep_graph_document.html' | relative_url }})
- [Repository](https://github.com/cameronfreer/graphon) &middot;
  [Verification status and history](https://github.com/cameronfreer/graphon/blob/master/docs/verification.md)

## References

- Lov&aacute;sz, L. (2012). *Large Networks and Graph Limits*. AMS Colloquium Publications, vol. 60.
- Frieze, A. &amp; Kannan, R. (1999). Quick approximation to matrices and applications.
  *Combinatorica*, 19(2), 175&ndash;220.
- Borgs, C., Chayes, J. T., Lov&aacute;sz, L., S&oacute;s, V. T., &amp; Vesztergombi, K. (2008).
  Convergent sequences of dense graphs I. *Advances in Mathematics*, 219(6), 1801&ndash;1851.
- Diaconis, P. &amp; Janson, S. (2008). Graph limits and exchangeable random graphs.
  *Rendiconti di Matematica*, 28, 33&ndash;61.
- Kallenberg, O. (2005). *Probabilistic Symmetries and Invariance Principles*. Springer.
- Austin, T. (2008). On exchangeable random variables and the statistics of large graphs and
  hypergraphs. *Probability Surveys*, 5, 80&ndash;145.
