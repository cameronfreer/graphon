# Sampling asymptotics roadmap: from the First Sampling Lemma to Aldous–Hoover

**Status:** proposed campaign ladder, 2026-07-10 (post-R3; advisor-reviewed).

> **RELEASE-QUALITY MILESTONE, 2026-07-11 (master `4877311`).** The formalization is at a
> coherent release boundary:
> - **Diaconis–Janson representation** (issue #33, PRs #25–#43): the graphon space
>   (compact Polish standard-Borel quotient), the joining theorem, point-separating
>   sample coordinates and the compact embedding, exchangeable graph laws and mixtures,
>   the exact finite-sampling formula, the collision estimate,
>   `graphon_mixture_representation` (`∃!` mixing measure) and the packaged equivalence
>   `mixtureExchangeableLawEquiv`;
> - **extremality**: `isDissociated_mixtureExchangeableLaw_iff` and
>   `isDissociated_iff_exists_sampleExchangeableLaw` (dissociated ↔ Dirac ↔
>   fixed-graphon sample law);
> - **full empirical convergence** (PR #44): `empiricalMixing_tendsto_representingMeasure`
>   — the whole empirical mixing sequence converges weakly to the representing measure;
> - **quantitative finite-marginal estimate** (PR #45):
>   `abs_mixturePMF_empiricalMixing_sub_le` (`≤ k²/(n+1)`), alongside the collision
>   estimate;
> - **zero `sorry`/`admit` proof placeholders** repository-wide (issue #19 complete,
>   PR #46; the CI census enforces strictly zero), with the 34-declaration axiom audit
>   green (`{propext, Classical.choice, Quot.sound}` only).
> Feature work pauses here; the next campaign is the explicit Aldous–Hoover realization
> layer (see the section below), which is deliberately separated from the already-proved
> mixture theorem.

> **UPDATE 2026-07-11 (later):** layers 1–2 below are **complete** — PRs #48 (the
> infinite graph space: compact Polish standard-Borel, cylinder π-system, measure
> extensionality), #49 (`infiniteLaw`: unique compactness-based Kolmogorov extension of
> the consistent marginals), #50 (exchangeability under every relabeling +
> `exchangeableGraphLawEquivInfinite : ExchangeableGraphLaw ≃
> InfiniteExchangeableGraphLaw`). The axiom audit stands at 38 declarations. Next chunk:
> the explicit infinite sampler for a **fixed raw graphon** via `Measure.infinitePi`
> (vertex + edge randomness), identified with `infiniteLaw (sampleExchangeableLaw W)`
> by A2 uniqueness; quotient-valued mixing stays a later, separate measurable-selection
> campaign.

## Next campaign: explicit Aldous–Hoover realization (layers 1–2 complete)

The mixture theorem above is the graphon-mixture content of Aldous–Hoover. What remains
is infinite-array realization infrastructure — kept deliberately separate from the
already-proved finitary results. Five layers, in dependency order:

1. **Infinite law from consistent marginals.** A probability law on `SimpleGraph ℕ`
   constructed from an `ExchangeableGraphLaw`'s consistent finite marginals
   (Kolmogorov-extension / projective-limit layer over the countable edge-indexed
   product; Mathlib's projective-limit / Ionescu-Tulcea infrastructure is the intended
   base).
2. **Exchangeability of the infinite law.** Invariance of that law under every
   finitely-supported (equivalently, arbitrary) permutation of `ℕ` — the
   infinite-arrays counterpart of the finite consistency field.
3. **Explicit random-graphon sampling.** The two-stage randomization: global randomness
   (a mixing draw from `ProbabilityMeasure (GraphonSpace α μ)`), vertex randomness
   (i.i.d. latent variables `X i ~ μ`), and edge randomness (independent
   `Bernoulli (W (X i, X j))` coins) — an explicit kernel-composition construction of a
   law on `SimpleGraph ℕ`.
4. **Marginal identification.** Equality of all finite marginals of the layer-3
   construction with the given `ExchangeableGraphLaw` (via `sampleMass`/`samplePMF` and
   the representation theorem), hence equality with the layer-1 law by uniqueness of
   the extension.
5. **Dissociated/ergodic specialization.** Under `IsDissociated` (equivalently, by
   extremality, a Dirac mixing measure), the global randomness collapses: the law is
   sampling from one deterministic graphon — the ergodic case of Aldous–Hoover.

Layers 1–2 are pure countable-product measure theory (candidates for TauCeti
upstreaming, cf. issue #24); layers 3–5 connect it to the existing graphon API.
**Relation to other plans:** `docs/post-r3-mainline-completion-plan.md` is the release-hardening
track (documentation, CI, census enforcement) and explicitly excludes new mathematics; this
document is the *next mathematical campaign* track. The parked `70-twinfree-common-host`
branch (5 commits, 625 lines, alternative common-host route for the already-proved twin-free
bijection) is groundwork on its own axis — preserve it, but do not rebase or merge it now.

## S1: expose the theorem already hidden in the sampling proof

The strongest immediate result is essentially already proved. Both halves of the First
Sampling Lemma — `point_sampling_event_of_large_k` (`Graphon/SamplingPointwise.lean`) and
`rounding_event_of_large_k` (`Graphon/SamplingRounding.lean`) — hold for **every sufficiently
large `k`, uniformly over every graphon**, but `first_sampling_lemma`
(`Graphon/SamplingLemma.lean`) currently discards that strength and returns one sample size.

First new theorem (retain the quantified `k`; proof ≈ the existing assembly):

```lean
theorem first_sampling_lemma_of_large_k (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ K, ∀ k ≥ K, ∀ (_ : NeZero k), ∀ W, 1 - η < sampleGoodMassOn W k ε
```

Immediate corollaries:

- for every graphon `W` and `ε > 0`, some finite simple graph's embedded graphon is within
  `ε` of `W` in cut distance;
- stronger: at **every sufficiently large exact vertex count** `k`, some graph on exactly `k`
  vertices approximates `W`;
- every graphon is the cut-distance limit of a sequence of finite simple graphs;
- `G(k, W) → W` in probability, uniformly over `W`.

Low risk, mathematically visible, straight from Lovász's sampling theory.
**Status: implemented — PR #16 (branch `sampling-asymptotics`), in review**, together with the
corollaries above (`exists_simpleGraph_cutDistance_lt_of_large_k`,
`exists_simpleGraph_cutDistance_lt` (successor-indexed), and
`exists_tendsto_cutDistance_ofSimpleGraphOn`).

## S2: bundle the finite random-graph law

> **Status (2026-07-10): core implemented.** The forward Möbius identity (PR #27,
> `Graphon/Sampling.lean`) and the S2 core (PR #28, `Graphon/SamplingLaw.lean`:
> `upperSum`/Möbius engine, `relabelOrderIso`, `sampleMass_map_perm`,
> `samplePMF`/`sampleLaw`, arbitrary-injection consistency `samplePMF_map_comap`) are done.
> #21 is implemented in PR #29 (constant graphon = `binomialRandom`:
> `constGraphon` + `Nonempty (Graphon α μ)` in `Basic.lean`, `ae_pairMap_of_prod`
> generalized low in the sampling stack, the law in `SamplingExamples.lean`).
> The joining theorem
> `(∀ k, samplePMF U k = samplePMF W k) ↔ WeaklyIsomorphic U W` is implemented in
> `Graphon/SamplingDetermination.lean`, cleanly connecting S2 and S3.

`sampleMass W G` is currently a family of reals. Bundle it as a probability measure on
`SimpleGraph (Fin k)` (likely via `ProbabilityMeasure`), then prove:

- relabeling invariance under `Equiv.Perm (Fin k)`;
- consistency under restriction `Fin (k+1) → Fin k`;
- the missing **forward Möbius identity** `t(F, W) = ∑_{G ⊇ F} sampleMass W G`
  (the reverse inclusion–exclusion direction already exists at `Graphon/Sampling.lean:246`);
- `sampleMass` = induced-subgraph density;
- equality of all finite sample laws ↔ equality of all homomorphism densities
  ↔ weak isomorphism.

Accompanying examples: constant graphon ⇒ Erdős–Rényi law; finite step graphon ⇒ stochastic
block model law. This turns the sampling code into a clean finite-marginal API.

## S3: package the graphon space

> **Status (2026-07-10): implemented** (`Graphon/GraphonSpace.lean`): `PseudoMetricSpace`
> on raw graphons, `GraphonSpace := SeparationQuotient`, `mk_eq_mk_iff` (= weak
> isomorphism), `CompactSpace`, Borel/Polish/standard-Borel stack, `StandardGraphonSpace`
> alias. The S2–S3 joining theorem
> `(∀ k, samplePMF U k = samplePMF W k) ↔ WeaklyIsomorphic U W` (+ its `GraphonSpace.mk`
> form) is implemented in `Graphon/SamplingDetermination.lean`. The continuous
> point-separating sample-law coordinates and the compact coordinate embedding are
> implemented in `Graphon/SamplingCoordinates.lean` (issue #32). Next: the
> Diaconis–Janson graphon-mixture correspondence (issue #33 — `ExchangeableGraphLaw`,
> unique mixture representation via Prokhorov + Stone–Weierstrass, dissociated ↔ Dirac
> extremality; the Austin functional array theorem stays a separate follow-on, see the
> comment on #33).

Implemented route (`Graphon/GraphonSpace.lean`): `cutDistance` is installed as a
`PseudoMetricSpace` on raw `Graphon α μ`, and

```lean
GraphonSpace α μ := SeparationQuotient (Graphon α μ)
```

is Mathlib's metric separation quotient — NOT a hand-rolled `Quotient` — so `MetricSpace`,
`CompleteSpace`, and `Nonempty` come for free; quotient equality is exactly
`WeaklyIsomorphic` (`GraphonSpace.mk_eq_mk_iff`); `CompactSpace` transfers total
boundedness through the uniformly continuous surjective quotient map; the canonical Borel
measurable space yields the `BorelSpace`/`SecondCountableTopology`/`PolishSpace`/
`StandardBorelSpace` stack; and `StandardGraphonSpace` is the fixed unit-interval alias.
Not cosmetic: a "random graphon" is a random element of this quotient — raw
representatives are non-unique — and the quotient is the central prerequisite for a clean
exchangeability theorem.

## The target: Aldous–Hoover in graphon form (Diaconis–Janson correspondence)

> Every exchangeable infinite random simple graph is obtained by sampling a random graphon
> class, then, conditionally, sampling i.i.d. vertices and independent edges. The
> exchangeable law is extreme/ergodic/dissociated exactly when the graphon class is
> deterministic.

Functional form: `X_{ij} = 1{U_{ij} ≤ W_{U₀}(U_i, U_j)}` with `U₀` the graphon randomizer,
`U_i` vertex variables, `U_{ij}` edge variables. This is the graph-limit correspondence of
Diaconis–Janson (arXiv:0712.2749): exchangeable infinite graph laws ↔ probability
distributions on graph-limit space; extreme laws ↔ deterministic limits.

Formalization ladder:

1. Bundled consistent finite `G(k, W)` laws (= S2).
2. Infinite `G(∞, W)` via product randomness or Kolmogorov extension.
3. Its law is vertex-exchangeable and dissociated.
4. Compact measurable graphon quotient (= S3).
5. Mixtures of graphon-generated laws.
6. Restrictions of any exchangeable graph converge a.s. to a random graphon class.
7. Identify all finite marginals with the corresponding graphon mixture.
8. Uniqueness + extreme/dissociated characterization.
9. Only then: the equivalent functional Aldous–Hoover representation.

Steps 1–4 are plausible medium-sized campaigns. Steps 6–9 are substantial probability theory
(reverse martingales, invariant/tail σ-algebras, measurable selection/kernels, ergodic
decomposition) — a multi-month direction, not the next PR.

**Boundary note (Tau Ceti).** Sequence exchangeability (de Finetti-style, as in
mrdouglasny/TauCeti) is *not* the vertex-exchangeable graph symmetry needed here: graph
exchangeability is invariance of a doubly-indexed edge array under a *single* permutation
acting simultaneously on both indices, a genuinely two-dimensional (Aldous–Hoover) notion.
When generalized-exchangeability infrastructure becomes available upstream, *consume* it —
do not copy sequence-exchangeability code and attempt to adapt it.
