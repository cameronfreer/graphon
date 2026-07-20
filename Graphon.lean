/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Graphon.PermutationExtension
import Graphon.RelationalSignature
import Graphon.RelationalStructure
import Graphon.RelationalTopology
import Graphon.RelExchangeableLaw
import Graphon.RelInfiniteLaw
import Graphon.RelLawEquivalence
import Graphon.RelRestrictionBlocks
import Graphon.RelRestrictionIndependence
import Graphon.RelInvariantAction
import Graphon.RelErgodicLinks
import Graphon.RelErgodicExtreme
import Graphon.RelExtremality
import Graphon.RelEqualityPattern
import Graphon.RelKernelEvaluator
import Graphon.RelKernelSampler
import Graphon.DigraphMaps
import Graphon.InfiniteDigraph
import Graphon.SimpleGraphDigraphBridge
import Graphon.InfiniteDigraphLaw
import Graphon.ExchangeableLawBlueprint
import Graphon.Digraphon
import Graphon.SamplerSources
import Graphon.DigraphSampler
import Graphon.DigraphonConstructors
import Graphon.DigraphSamplerFamilies
import Graphon.Basic
import Graphon.Step
import Graphon.HomDensity
import Graphon.Pullback
import Graphon.Operations
import Graphon.Operator
import Graphon.CutNorm
import Graphon.CutDistance
import Graphon.LevyDownward
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
import Graphon.InjectionCounting
import Graphon.SamplingFinite
import Graphon.SubgraphDensities
import Graphon.SubgraphDensityBridges
import Graphon.SubgraphDensityBlueprint
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
import Graphon.InvariantAction
import Graphon.RestrictionIndependence
import Graphon.RestrictionIndependenceReverse
import Graphon.ErgodicDecomposition
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
* `Graphon.LevyDownward` — **Lévy's downward theorem, L¹ version** (Mathlib-upstream candidate, #24): orthogonal projections along an antitone sequence of subspaces converge to the projection onto the infimum; the `Lᵖ`-subspace of an infimum σ-algebra is the intersection; conditional expectations along an antitone sequence of σ-algebras converge in `L¹` to the conditional expectation on the infimum; and conditional expectation over a `0`-`1` σ-algebra is the mean
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
* `Graphon.InjectionCounting` — pure counting of vertex maps `Fin k → Fin n` (#94 shared infrastructure): the union (birthday) bound `card_not_injective_le` with its `k²/(n+1)` proportion form, the reciprocal vertex-map-count weight, and the descending-factorial injective-map count `card_filter_injective_eq_descFactorial` — extracted from the mixture-existence collision estimate
* `Graphon.SamplingFinite` — The exact finite-sampling formula: sampling from an embedded finite graph is uniform vertex-map pullback
* `Graphon.SubgraphDensities` — the finite subgraph densities `t`, `t_inj`, `t_ind` (#94): labeled hom / injective-hom / induced-copy counts with their normalization conventions (`n ^ k` all maps vs the `descFactorial` injective count), the all-maps exact-pullback count, with the small-host zero convention (combinatorics-only import closure)
* `Graphon.SubgraphDensityBlueprint` — annotation-only blueprint wrapper for the finite density triangle (keeping `Graphon.SubgraphDensities` Architect-free)
* `Graphon.SubgraphDensityBridges` — the analytic bridges `homDensity_ofSimpleGraphOn_eq_t` / `sampleMass_ofSimpleGraphOn_eq_pullbackCount_div` from the finite densities to the empirical-graphon sampling formulas
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
* `Graphon.RestrictionIndependence` — Toward DJ Theorem 5.5: the vertex-tail σ-algebra and restriction independence; `RestrictionIndependent ⟹ VertexTailTrivial ⟹ dissociated` (via the tail-measurable empirical limit)
* `Graphon.RestrictionIndependenceReverse` — The reverse arc closing DJ Theorem 5.5: dissociation ⟹ restriction independence (two-block Möbius factorization), and the five-way extremality `tfae_extremality`
* `Graphon.InvariantAction` — The finite-permutation action toward ergodic decomposition (#59): `limitGraphon` is invariant under every finite relabeling, hence invariant-σ-algebra measurable; `IsErgodic`
* `Graphon.ErgodicDecomposition` — The ergodic-decomposition form of extremality (#59 part 2): the six-way equivalence `tfae_ergodic_extremality` adjoining ergodicity under the finite-permutation action, and `invariant_ae_eq_limitGraphon_classifier` — `limitGraphon` generates the invariant σ-algebra modulo null sets; built from fixed-fiber ergodicity (block swap + initial-cylinder approximation)
* `Graphon.PermutationExtension` — `exists_perm_extend`: every `Fin k ↪ ℕ` extends to a permutation of `ℕ` (graph-independent; reused by the graph and relational exchangeability APIs)
* `Graphon.RelationalSignature` — Generic AHK program (umbrella #103), R0 design checkpoint (#110): purely relational multi-sorted `RelSignature`, the `RelCoord`/`RelStructure` carriers, external `NoNullary`, finite/infinite value carriers, the sortwise `RelCoord.map`/`RelStructure.comap` action, and worked digraph/bipartite/ternary examples (the ternary `(i,i,j)` exercising repeated coordinates); no topology/probability yet
* `Graphon.RelationalStructure` — Generic AHK program R1a (#104): sortwise actions on relational structures — `map`/`comap` functoriality, `restrict`/`relabel`, finite restrictions `restrictFin`/`restrictLE`, padding `pad` with the section `restrict_pad`, and restriction composition `restrictLE_restrictFin`/`restrictLE_restrictLE`; still no topology/measure (that is R1b)
* `Graphon.RelExchangeableLaw` — Generic AHK program R2a (#105): exchangeable relational laws — size-vector-indexed `ProbabilityMeasure` marginals with arbitrary sortwise-injection consistency (`RelExchangeableLaw`), the measurable sortwise restriction, diagonal cofinality, and finite-exchangeability of the marginals; no infinite extension yet (R2b/R2c)
* `Graphon.RelInfiniteLaw` — Generic AHK program R2b (#105): the compactness-based infinite extension **realizing the marginals** — diagonal padded laws (`paddedLaw`), Prokhorov subsequence extraction on the compact metrizable structure space, and marginal identification via continuity, giving `infiniteLaw` with `infiniteLaw_map_restrictFin`; exchangeability/uniqueness/equivalence is R2c
* `Graphon.RelLawEquivalence` — Generic AHK program R2c (#105): the finite/infinite exchangeable relational law equivalence — the arbitrary-injection marginal theorem, exchangeability of `infiniteLaw`, `InfiniteRelExchangeableLaw`, the permutation extension, and `relExchangeableLawEquiv : RelExchangeableLaw S ≃ InfiniteRelExchangeableLaw S`
* `Graphon.InfiniteDigraph` — Directed umbrella (#84) D1 (#85): `InfiniteDigraph` as the one-sort binary R1 instance (`digraphSig`) — inheriting compact/standard-Borel, measurable finite restrictions, and measure extensionality (all topology on `InfiniteDigraph`); `Adj` (Prop) / `adjBit` (Bool); `digraphStructureEquiv V` the plain carrier equivalence with Mathlib's `Digraph V`, giving both the infinite `digraphEquiv` and the finite `finiteDigraphEquiv` (for D2); no exchangeable-law theory (that is D2)
* `Graphon.SimpleGraphDigraphBridge` — the symmetric loopless embedding `SimpleGraph.toFiniteDigraph` with its coordinate lemma, injectivity, and range classification, in its own module preserving D1's relational/directed dependency boundary
* `Graphon.RelRestrictionBlocks` — Generic AHK program R3a (#106): sortwise vertex shift `RelStructure.drop` and block embeddings `shiftEmb`; the labeling-free restriction invariance `InfiniteRelExchangeableLaw.law_map_restrict` and shift invariance `law_map_drop`; the initial / after-block / vertex-tail σ-algebras with monotonicity and `iSup_initialAlgebra_eq`; and `IsDissociated` — dissociation as exact finite-event block factorization, with its marginal API
* `Graphon.RelRestrictionIndependence` — Generic AHK program R3b (#106): `RestrictionIndependent` and `VertexTailTrivial` for exchangeable relational laws; **dissociation ↔ restriction independence** (comap-σ-algebra independence of the block maps *is* the block-pair factorization, and the finite windows exhaust the after-block σ-algebra) and **restriction independence → vertex-tail triviality** (independence from every initial σ-algebra upgrades to self-independence); and the **representation-free closing arrow** tail-trivial → dissociated (condition on successively later diagonal tail algebras; Lévy downward + triviality + exchangeability force the block factorization), completing dissociated ↔ restriction-independent ↔ tail-trivial
* `Graphon.RelInvariantAction` — R3c (#106): the finitely supported sortwise relabeling action (`SortwiseFinSupp` with group closure), the strictly invariant σ-algebra, `IsErgodic`, and the **invariant probability simplex** `invariantProbabilityMeasures` with the finitary-invariance bridge (finitary invariance ⇒ full sortwise invariance, via finite-restriction extensionality and finitely supported window extensions) identifying it with the laws of `InfiniteRelExchangeableLaw`
* `Graphon.RelErgodicLinks` — R3c: ergodicity linked into the dissociation triangle — the sortwise block swap, in-measure approximation by initial cylinders, the 4ε approximate-independence core (restriction independence ⇒ ergodicity), vertex-tail ⊆ invariant (ergodicity ⇒ tail triviality), and the iff chain
* `Graphon.RelErgodicExtreme` — R3c: the ergodic ↔ extreme-point theorem for the relabeling group (port of Mathlib's `Ergodic.iff_mem_extremePoints`), with the new absolute-continuity lemma `eq_of_absolutelyContinuous` and the a.e.-to-strict invariant hull upgrade over the countable group
* `Graphon.RelExtremality` — R3c headline: the **five-way extremality equivalence** `tfae_extremality` (dissociated ↔ restriction-independent ↔ tail-trivial ↔ ergodic ↔ extreme), representation-free, with the `digraphSig` regression examples
* `Graphon.RelEqualityPattern` — R4 design checkpoint (#107): sort-tagged values (`RelCoord.taggedValue`), the **equality pattern** as its kernel with the **bundled label-free `EqualityPattern`** (sort-compatible setoid + `blockSort`), the **support** as a finset of tagged values (blocks ≃ support), global and **local latent indices** (`LatentIndex`; `PatternLatentIndex` — the kernel's order-free domain — and `CoordLatentIndex`, canonically equivalent and two-way relabeling-equivariant via `congrMap`), and the `Sigma.map id` transport — the interface for the functional AHK representation (sampler and representation theorem deliberately held back); binary/diagonal/ternary/bipartite examples in their own namespace
* `Graphon.RelKernelEvaluator` — R4 evaluator layer (#107): `RelKernelFamily` (the label-free measurable representing kernels `f_{r,π}` on the finite pattern-local latent product), `RelCoord.localLatents` (the coordinate's window into the global latent source), the measurable `evalStructure`, and the **equivariance theorem** `evalStructure_relabel` (relabeling the evaluated structure = precomposing the source with the latent-index action) with the pattern↔image transport square `patternLatentIndexEquivCoord_map` — latent source measure, sampler pushforward, and representation theorem deliberately held for the next layers
* `Graphon.RelKernelSampler` — R4 sampler layer (#107): the evaluator over an arbitrary carrier (`RelKernelFamily.eval`, definitionally `evalStructure` on `Vinfinite`) with the pullback transport `eval_comap`; the i.i.d. uniform `latentSource` over global subset-latent indices with relabeling invariance (via `LatentIndex.relabelEquiv`); and the **evaluated exchangeable law** `RelKernelFamily.evalLaw` with its **dissociation** `evalLaw_isDissociated` (disjoint vertex windows read disjoint nonempty subset-latent collections, so the i.i.d. source factorizes) — the forward half of the dissociated functional AHK representation; the converse representation theorem is the remaining content of #107
* `Graphon.DigraphMaps` — the minimal `Digraph.comap` pullback API for Mathlib's `Digraph` (mirroring `SimpleGraph.comap`; a Mathlib-upstream candidate tracked on #24), used by the D2 directed-law bridge
* `Graphon.InfiniteDigraphLaw` — Directed umbrella (#84) D2 (#86): the `PMF`-based finite directed law `ExchangeableDigraphLaw` (consistent under `Digraph.comap`), the finite bridge `digraphLawEquiv : ExchangeableDigraphLaw ≃ RelExchangeableLaw digraphSig` (via `finiteDigraphEquiv` + `PMF.toMeasure`/`Measure.toPMF`), and the headline `exchangeableDigraphLawEquiv : ExchangeableDigraphLaw ≃ InfiniteExchangeableDigraphLaw` composing with R2c — measurable structure stays on the relational carrier
* `Graphon.ExchangeableLawBlueprint` — annotation-only blueprint wrappers for the R2c relational (`relExchangeableLawEquiv`) and D2 directed (`exchangeableDigraphLawEquiv`) equivalences, keeping `Architect` out of the reusable foundational modules
* `Graphon.SamplerSources` — generic i.i.d. random sources (`uniform01`, `iidVertexSource`, `iidUniformSource`) shared by the graph and directed samplers
* `Graphon.Digraphon` — Directed umbrella (#84) D3a (#87): the five-component CAF `Digraphon` (four reciprocal-edge pair kernels + Bool loop, a.e. probability-vector + transpose law) with `ext`; measurable representatives; the transpose-symmetrized `pairSym`; and the **everywhere-valid 3-simplex representative** `simplexRep` (measurable, nonneg/sum-one/transpose-compatible everywhere, a.e.-equal to `pairProb`) — the prerequisite for the D3b sampler; no random sources yet
* `Graphon.DigraphSampler` — Directed umbrella (#84) D3b (#87): the per-pair four-state distribution `Digraphon.pairPMF`, the one-uniform categorical map `catOutcome` with its **exact four-state law** `uniform01_map_catOutcome`; the explicit finite/infinite digraph samplers (`sampleAdj` in the natural-number order, `sampleInfinite`, `sampleFinite`); the **exact finite-event product formula** over an arbitrary injective labeling; the sampled law (`sampleRelLaw` / `sampleDigraphLaw`) with the infinite-law identification through `exchangeableDigraphLawEquiv`; exchangeability and dissociation
* `Graphon.DigraphonConstructors` — Directed umbrella (#84) D3c (#87): the special-family digraphon constructors — the generic pointwise builder `Digraphon.ofFun`, the ordinary-graphon embedding `ofGraphon` (reciprocal edges fully correlated), the tournament digraphon `ofTournament` (exactly one direction per pair), and the asymmetric-kernel digraphon `ofKernel` (independent directions, all four products present) — each with its a.e. pair-kernel identification
* `Graphon.DigraphSamplerFamilies` — Directed umbrella (#84) D3c headlines (#87): the sampler laws of the special families — the embedded ordinary graphon samples exactly the undirected `W`-random graph (`map_sampleFinite_ofGraphon`, pushforward of `samplePMF` under the symmetric loopless embedding), the tournament digraphon samples an almost-sure tournament (`ofTournament_sample_isTournament`), and the asymmetric-kernel sample draws its two directions independently (`sampleEventIntegrand_ofKernel_ae`)
* `Graphon.RelationalTopology` — Generic AHK program R1b (#104): the Boolean-product topology / σ-algebra on `RelStructure` — compact/Polish/standard-Borel instances, measurability of the finite restrictions, the cylinder π-system `cylinders` generating the product σ-algebra (`generateFrom_cylinders_eq`; = Borel under the countability giving Polish), and finite-restriction measure extensionality (`ext_of_map_restrictFin`); no projective extension (that is R2)
* `Graphon.InverseCounting` — Inverse counting lemma, convergence equivalence
* `Graphon.Convergence` — Top-level convergence characterization

## Experimental

* `Graphon.Operations` — Pointwise product (direct sum and operator product are future work)
* `Graphon.Operator` — Kernel operator pointwise definition (full L² API is future work)
* `Graphon.Sampling` — W-random graph distribution (`sampleMass`) and expected edge density (concentration is proved in the `Sampling*` modules above, culminating in `Graphon.SamplingLemma`)
-/
