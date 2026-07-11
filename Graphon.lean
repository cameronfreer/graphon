/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Graphon.Basic
import Graphon.Step
import Graphon.HomDensity
import Graphon.Pullback
import Graphon.Operations
import Graphon.Operator
import Graphon.CutNorm
import Graphon.CutDistance
import Graphon.MeasureIso
import Graphon.Approximation
import Graphon.Counting
import Graphon.Regularity
import Graphon.Overlay
import Graphon.Compactness
import Graphon.GraphonSpace
import Graphon.InfiniteGraph
import Graphon.Sampling
import Graphon.CaiGovorov
import Graphon.Lovasz
import Graphon.CrossSuper
import Graphon.SimpleRank
import Graphon.CycleKrylov
import Graphon.MatrixDetermination
import Graphon.SamplingICL
import Graphon.SamplingConcentration
import Graphon.SamplingRounding
import Graphon.SamplingPointwise
import Graphon.SamplingLemma
import Graphon.SamplingLaw
import Graphon.SamplingExamples
import Graphon.SamplingDetermination
import Graphon.SamplingCoordinates
import Graphon.ExchangeableGraphLaw
import Graphon.MixtureConvergence
import Graphon.HomDensityAlgebra
import Graphon.MixtureCoordinates
import Graphon.MixtureUniqueness
import Graphon.InverseCounting
import Graphon.SamplingFinite
import Graphon.MixtureExistence
import Graphon.MixtureRepresentation
import Graphon.MixtureExtremality
import Graphon.InfiniteLaw
import Graphon.InfiniteExchangeability
import Graphon.InfiniteRepresentation
import Graphon.MixtureKernel
import Graphon.InfiniteSamplingConvergence
import Graphon.McDiarmid
import Graphon.SampleExposure
import Graphon.AlmostSureSampling
import Graphon.LimitGraphon
import Graphon.InfiniteSampleLaw
import Graphon.EmpiricalGraphon
import Graphon.InfiniteExtremality
import Graphon.InfiniteSampler
import Graphon.DissociatedSampler
import Graphon.VertexTail
import Graphon.Convergence

/-!
# Graphons in Lean 4

A formalization of graphons — the theory of limits of dense graph sequences —
in Lean 4 using Mathlib.

## Stable core

* `Graphon.Basic` — Graphon definition, symmetry, boundedness
* `Graphon.Pullback` — Pullback under measure-preserving maps
* `Graphon.Step` — Measurable partitions, step functions
* `Graphon.HomDensity` — Homomorphism density definition
* `Graphon.CutNorm` — Cut norm, graphon integrability
* `Graphon.Approximation` — Rectangle averages, cut norm approximation
* `Graphon.CutDistance` — Cut distance, pseudometric properties, three of the four Rokhlin cores
* `Graphon.MeasureIso` — Atomless standard-Borel measure-isomorphism theorem (graphon-independent; mod-0 iso + everywhere upgrade)
* `Graphon.Overlay` — Overlay theorem: an MP bijection nearly achieves the cut distance (fourth Rokhlin core)
* `Graphon.Regularity` — Energy increment, Frieze–Kannan weak regularity lemma
* `Graphon.Counting` — Homomorphism density, counting lemma
* `Graphon.Compactness` — Total boundedness, completeness
* `Graphon.GraphonSpace` — The graphon space: compact Polish standard-Borel metric quotient under weak isomorphism (`GraphonSpace`, `StandardGraphonSpace`)
* `Graphon.InfiniteGraph` — The infinite graph space: `SimpleGraph ℕ` as a compact Polish standard-Borel space; continuous finite restrictions, cylinder π-system, finite-restriction measure extensionality (Aldous–Hoover brick A1)
* `Graphon.CaiGovorov` — Graph-free Vandermonde argument (Cai–Govorov §4), for #70 orbit separation
* `Graphon.Lovasz` — Connection-matrix algebra scaffolding (Lovász §3), incl. the Cai–Govorov #70 orbit theorem and rank theorem
* `Graphon.CrossSuper` — Cross-matrix super-surjective transfer (Cai–Govorov Lemma 5.1, two-matrix partition form)
* `Graphon.SimpleRank` — K=1 simple-graph rank theorem, algebra-atom framing (#70)
* `Graphon.CycleKrylov` — spectral slice of the cycle–Krylov square-moment proof (#70)
* `Graphon.MatrixDetermination` — Algebraic determination of step graphons
* `Graphon.SamplingICL` — Sampling route to the partition-size-independent quantitative inverse counting lemma
* `Graphon.SamplingConcentration` — Concentration scaffold for the First Sampling Lemma (conditional distribution, weighted sample, two-stage reduction)
* `Graphon.SamplingRounding` — The rounding half of the First Sampling Lemma, proved (cut certificate + finite Chernoff)
* `Graphon.SamplingPointwise` — The pointwise half of the First Sampling Lemma: AFKK cut-guessing bound, McDiarmid-at-MGF + soft-max infrastructure
* `Graphon.SamplingLemma` — The First Sampling Lemma, assembled from the two proved concentration events
* `Graphon.SamplingLaw` — The finite sample law of a graphon: `samplePMF`/`sampleLaw`, Möbius/upper-transform engine, relabeling invariance, arbitrary-injection consistency
* `Graphon.SamplingExamples` — The constant graphon samples Mathlib's binomial random graph `G(V, p)`
* `Graphon.SamplingDetermination` — The sample laws determine the graphon: `(∀ k, samplePMF U k = samplePMF W k) ↔ WeaklyIsomorphic U W`, and its `GraphonSpace` form
* `Graphon.SamplingCoordinates` — Continuous point-separating sample-law coordinates on the graphon space; compact coordinate embedding
* `Graphon.ExchangeableGraphLaw` — Exchangeable graph laws (consistent finite marginals) and graphon mixtures; mixtures are exchangeable
* `Graphon.MixtureConvergence` — Weak-convergence layer: mixture coordinates as integrals, Prokhorov extraction, empirical mixing measures
* `Graphon.HomDensityAlgebra` — Hom-density coordinates on the graphon space; multiplicativity over disjoint unions (`homDensity_sum`)
* `Graphon.MixtureCoordinates` — Shared mixture-coordinate layer: hom-density coordinates as bounded continuous functions; their integrals are mixture upper masses
* `Graphon.MixtureUniqueness` — Uniqueness of the graphon mixture: the coordinate StarSubalgebra separates points; `mixtureExchangeableLaw` is injective
* `Graphon.SamplingFinite` — The exact finite-sampling formula: sampling from an embedded finite graph is uniform vertex-map pullback
* `Graphon.MixtureExistence` — Existence of the graphon mixture: the collision estimate for empirical mixing measures; every exchangeable law is a mixture (`exists_mixtureExchangeableLaw_eq`)
* `Graphon.MixtureRepresentation` — The Diaconis–Janson representation theorem: exchangeable graph laws = graphon mixtures, uniquely (`graphon_mixture_representation`, `mixtureExchangeableLawEquiv`)
* `Graphon.MixtureExtremality` — Diaconis–Janson extremality: dissociated exchangeable laws are exactly the Dirac mixtures (`isDissociated_mixtureExchangeableLaw_iff`)
* `Graphon.InfiniteLaw` — The infinite exchangeable graph law: unique extension of consistent finite marginals to `InfiniteGraph`, via Prokhorov compactness (Aldous–Hoover brick A2)
* `Graphon.InfiniteExchangeability` — Exchangeability of the infinite law under every relabeling; the equivalence `ExchangeableGraphLaw ≃ InfiniteExchangeableGraphLaw` (Aldous–Hoover brick A3)
* `Graphon.InfiniteRepresentation` — The infinite Diaconis–Janson/Aldous–Hoover correspondence: `ProbabilityMeasure (GraphonSpace α μ) ≃ InfiniteExchangeableGraphLaw` (`infiniteMixtureLawEquiv`)
* `Graphon.InfiniteSampleLaw` — The canonical infinite law of a graphon class: quotient descent, finite-restriction marginals, weak continuity, closed embedding into infinite laws
* `Graphon.EmpiricalGraphon` — Empirical graphons of an infinite exchangeable graph: their law is the empirical mixing measure; convergence in distribution to the representing measure
* `Graphon.InfiniteExtremality` — Extremality for infinite exchangeable laws: dissociated ↔ canonical law of a single graphon class ↔ Dirac representing measure
* `Graphon.InfiniteSampler` — Explicit infinite sampler for a fixed graphon: i.i.d. sources via `Measure.infinitePi`; the measurable sampler realizes `infiniteLaw (sampleExchangeableLaw W)` exactly
* `Graphon.MixtureKernel` — The barycenter interpretation: the represented infinite law is the `Measure.bind` mixture of the canonical fiber laws (`mixtureInfiniteLaw_eq`)
* `Graphon.InfiniteSamplingConvergence` — Convergence in probability: the sampled empirical graphons of a `W`-random infinite graph tend to the class of `W` in measure
* `Graphon.McDiarmid` — Bounded-differences concentration at MGF level, packaged as `HasSubgaussianMGF` (Mathlib-upstreaming candidate)
* `Graphon.SampleExposure` — The padded vertex-exposure sampler and the fixed-`F` exponential hom-density tail `2·exp(−ε²k/(2q²))` for `G(k, W)` (Lovász Cor 10.4 form), with the explicit-sampler tail and Borel–Cantelli summability bridge
* `Graphon.AlmostSureSampling` — Almost-sure convergence of the sampled empirical graphons to the class of `W` (Lovász Prop 11.32; Borel–Cantelli over the concentration tails)
* `Graphon.LimitGraphon` — The empirical graphon limit as a universal measurable random variable: `limitGraphon` with law `infiniteMixtureLawEquiv.symm M` under every exchangeable law
* `Graphon.DissociatedSampler` — Functional Aldous–Hoover for dissociated laws: an infinite exchangeable law is dissociated iff it is the law of the explicit `W`-random graph (`isDissociated_iff_exists_sampler`)
* `Graphon.VertexTail` — Vertex-tail infrastructure: the tail shift and σ-algebras, finite-deletion stability of empirical limits, and vertex-tail measurability of `limitGraphon`
* `Graphon.InverseCounting` — Inverse counting lemma, convergence equivalence
* `Graphon.Convergence` — Top-level convergence characterization

## Experimental

* `Graphon.Operations` — Pointwise product (direct sum and operator product are future work)
* `Graphon.Operator` — Kernel operator pointwise definition (full L² API is future work)
* `Graphon.Sampling` — W-random graph distribution (`sampleMass`) and expected edge density (concentration is proved in the `Sampling*` modules above, culminating in `Graphon.SamplingLemma`)
-/
