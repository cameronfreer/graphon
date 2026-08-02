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
- `RelKernelFamily.evalLaw_isDissociated` — the forward half of the functional
  Aldous–Hoover–Kallenberg theorem: the evaluated
  law of a kernel family over an i.i.d. latent source is dissociated
- `InfiniteRelExchangeableLaw.condIndep_fixingAlgebra` — conditional independence of the fixing
  σ-algebras over their intersection, for *every* exchangeable law, with no dissociation hypothesis
- `exchangeableDigraphLawEquiv` — exchangeable digraph laws ≃ infinite exchangeable digraph laws;
  with `Digraphon`, `sampleDigraphLaw`, and the special-family constructors `ofGraphon`,
  `ofTournament`, `ofKernel`

The **converse** direction — that every dissociated exchangeable relational law is the evaluated
law of a kernel family — is under construction. The fixing σ-algebras, the lower-rank factor, the
rank successor decomposition, and the latent infrastructure are its inputs rather than results in
their own right. Design decisions and open steps are tracked on
[issue #107](https://github.com/cameronfreer/graphon/issues/107); nothing in this section is
claimed to depend on it.

## Verification status

- **Zero `sorry`/`admit`** anywhere in the project — CI enforces a strict census.
- **Audited axiom use.** A fixed list of load-bearing declarations is checked to depend only on
  `propext`, `Classical.choice`, and `Quot.sound`. The gate covers that audited set, not every
  declaration in the repository.
- **CI**: every PR builds the Lean project and the blueprint; the `master` deployment
  additionally builds the API documentation and the homepage.

A recurring convention worth knowing when reading proofs: where only an identification *modulo a
measure* is available, statements say so eventwise (`∃ E', MeasurableSet[…] E' ∧ E' =ᵐ[μ] E`)
rather than claiming equality of σ-algebras, and kernel identities are stated almost everywhere
under a named measure. Statements are not silently strengthened to strict equality.

See [docs/verification.md](docs/verification.md) for the audit policy and what the gate does and
does not cover.

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
| Relational Aldous–Hoover–Kallenberg | Multi-sorted signatures, carriers and topology, exchangeable relational laws, ergodicity, equality patterns, kernel evaluator and sampler, fixing σ-algebras |
| Digraphons | Directed carriers and laws, the five-component digraphon, the directed sampler, special families |
| `ForMathlib` | Signature-free lemmas with no Mathlib home yet; tracked as upstream candidates in [issue #160](https://github.com/cameronfreer/graphon/issues/160) |

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
