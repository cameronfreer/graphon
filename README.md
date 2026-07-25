# Graphons in Lean 4

A Lean 4 formalization of graphons, exchangeable random graphs, digraphons, and relational
Aldous–Hoover–Kallenberg theory, built on [Mathlib](https://leanprover-community.github.io/mathlib4/).

**[Homepage](https://cameronfreer.github.io/graphon/)** ·
**[Blueprint](https://cameronfreer.github.io/graphon/blueprint/)** ·
**[API docs](https://cameronfreer.github.io/graphon/docs/)** ·
**[Dependency graph](https://cameronfreer.github.io/graphon/blueprint/dep_graph_document.html)**

A **graphon** is a symmetric measurable function `W : α² → [0,1]` on a probability space,
representing the limit of a convergent sequence of dense graphs. The library develops the
analytic theory of graphons, its probabilistic counterpart (exchangeable random graphs and their
representation theorems), and a generic multi-sorted relational framework covering directed
graphs and higher-arity structures.

## Results

### Classical graphon theory

- `cutDistance_triangle` — the cut distance is a pseudometric, via the four corrected
  Rokhlin-style coupling cores
- `regularity` — Frieze–Kannan weak regularity: every graphon has a step approximation of
  bounded complexity
- `homDensity_sub_le` / `cutDistance_le_of_homDensity_close` — the counting lemma and the
  quantitative inverse counting lemma
- `cutDistance_tendsto_iff_homDensity_tendsto` — cut-distance convergence ⟺ convergence of all
  homomorphism densities
- `totallyBounded`, `complete` — compactness of the graphon space

### Sampling and graphon representation

- `first_sampling_lemma` — one sample size works for every graphon simultaneously
  (Lovász Lemma 10.16 / BCLSV Theorem 4.6)
- `samplePMF_eq_all_iff_weaklyIsomorphic` — the sample laws determine the graphon
- `sampledEmpiricalGraphon_tendsto_ae` — almost-sure convergence of sampled empirical graphons
- `sampleLaw_const_eq_binomial` — the constant graphon samples Mathlib's `G(V, p)`
- `matrix_quotient_of_weightedHomSum_eq` — algebraic determination of step graphons
  (Lovász Theorem 5.30)

### Infinite exchangeability and extremality

- `graphon_mixture_representation` / `mixtureExchangeableLawEquiv` — the Diaconis–Janson
  representation theorem: exchangeable graph laws are graphon mixtures, uniquely
- `infiniteMixtureLawEquiv` — the infinite Diaconis–Janson / Aldous–Hoover correspondence
- `isDissociated_iff_exists_sampler` — functional Aldous–Hoover for dissociated laws: a
  dissociated law is the law of an explicit W-random graph
- `tfae_ergodic_extremality` — the six-way equivalence (dissociated ⟺ restriction-independent
  ⟺ tail-trivial ⟺ ergodic ⟺ extreme ⟺ Dirac-represented)

### Relational structures and directed graphs

- `relExchangeableLawEquiv` — finite/infinite exchangeable law equivalence for an arbitrary
  multi-sorted relational signature
- `RelExtremality.tfae_extremality` — the five-way extremality equivalence, representation-free
- `RelKernelFamily.evalLaw_isDissociated` — the forward half of functional AHK: the evaluated
  law of a kernel family over an i.i.d. latent source is dissociated
- `InfiniteRelExchangeableLaw.condIndep_fixingAlgebra` — conditional independence of the fixing
  σ-algebras over their intersection, for *every* exchangeable law
- `exchangeableDigraphLawEquiv` — exchangeable digraph laws ≃ infinite exchangeable digraph laws;
  with `Digraphon`, `sampleDigraphLaw`, and the special-family constructors `ofGraphon`,
  `ofTournament`, `ofKernel`

## Verification status

- **Zero `sorry`/`admit`** anywhere in the project — CI enforces a strict census.
- **No custom axioms.** Load-bearing declarations are audited to use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- **CI builds** the Lean project, the blueprint, and the API docs on every change.

See [docs/verification.md](docs/verification.md) for the audit policy and the project history,
including the resolution of the Rokhlin-style alignment gap and the removal of the last
known-false stubs.

## Where to start

| If you are | Start here |
|---|---|
| A mathematician reading the statements | [Blueprint](https://cameronfreer.github.io/graphon/blueprint/) |
| A Lean developer looking for declarations | [API docs](https://cameronfreer.github.io/graphon/docs/) |
| A contributor | the [open issues](https://github.com/cameronfreer/graphon/issues) |
| Looking for worked examples | `Graphon/SamplingExamples.lean`, `Graphon/DigraphonConstructors.lean` |

## Architecture

| Area | Contents |
|---|---|
| Graphon analysis | Graphons, cut norm and cut distance, step functions, regularity, counting and inverse counting, compactness |
| Measure-theoretic infrastructure | Atomless standard-Borel measure isomorphism, the overlay theorem, Lévy's downward theorem |
| Connection matrices | Lovász §3 algebra, Cai–Govorov orbit separation and rank theorem, algebraic determination |
| Sampling | W-random graphs, concentration (McDiarmid, sub-Gaussian MGF), the First Sampling Lemma, sample laws and coordinates |
| Mixture representation | Exchangeable graph laws, graphon mixtures, existence, uniqueness, Diaconis–Janson |
| Infinite laws | Kolmogorov extension, infinite exchangeability, empirical graphons, samplers, mixture kernels |
| Extremality | Vertex-tail σ-algebras, restriction independence, invariant action, ergodic decomposition |
| Relational AHK | Multi-sorted signatures, carriers and topology, exchangeable relational laws, ergodicity, equality patterns, kernel evaluator and sampler, fixing σ-algebras |
| Digraphons | Directed carriers and laws, the five-component digraphon, the directed sampler, special families |

The complete module inventory lives in [`Graphon.lean`](Graphon.lean) and the
[API docs](https://cameronfreer.github.io/graphon/docs/); it is deliberately not duplicated here.

## Building

Requires Lean 4 (via `elan`) and the pinned Mathlib revision.

```bash
lake exe cache get   # fetch the prebuilt Mathlib cache
lake build
```

The Mathlib revision is pinned in `lake-manifest.json` for reproducibility; do not run
`lake update` unless you intend to move the pin.

## References

- Lovász, L. *Large Networks and Graph Limits*. AMS Colloquium Publications, vol. 60, 2012.
- Frieze, A. & Kannan, R. "Quick Approximation to Matrices and Applications." *Combinatorica*
  19(2), 175–220, 1999.
- Borgs, C., Chayes, J. T., Lovász, L., Sós, V. T., & Vesztergombi, K. "Convergent sequences of
  dense graphs I." *Advances in Mathematics* 219(6), 1801–1851, 2008.
- Diaconis, P. & Janson, S. "Graph limits and exchangeable random graphs." *Rendiconti di
  Matematica* 28, 33–61, 2008.
- Kallenberg, O. *Probabilistic Symmetries and Invariance Principles*. Springer, 2005.
- Austin, T. "On exchangeable random variables and the statistics of large graphs and
  hypergraphs." *Probability Surveys* 5, 80–145, 2008.

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
