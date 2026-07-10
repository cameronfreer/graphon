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
import Graphon.MixtureUniqueness
import Graphon.InverseCounting
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
* `Graphon.MixtureUniqueness` — Uniqueness of the graphon mixture: the coordinate StarSubalgebra separates points; `mixtureExchangeableLaw` is injective
* `Graphon.InverseCounting` — Inverse counting lemma, convergence equivalence
* `Graphon.Convergence` — Top-level convergence characterization

## Experimental

* `Graphon.Operations` — Pointwise product (direct sum and operator product are future work)
* `Graphon.Operator` — Kernel operator pointwise definition (full L² API is future work)
* `Graphon.Sampling` — W-random graph distribution (`sampleMass`) and expected edge density (concentration is proved in the `Sampling*` modules above, culminating in `Graphon.SamplingLemma`)
-/
