/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.SamplingRounding
import Graphon.Regularity

/-!
# The point-sampling half of the First Sampling Lemma (scaffold)

Target (PR #11):

`point_sampling_event_of_large_k : ∀ ε η > 0, ∃ K, ∀ k ≥ K, ∀ [NeZero k],
  ∀ W : Graphon α μ, PointSamplingEvent W k ε η`

matching the shape of `rounding_event_of_large_k`, so that PR #12 can pick one `k`
for both events and close `first_sampling_lemma` via `sampleGoodMassOn_of_events`.

## Design notes (recorded 2026-07-07)

* **The rounding-style union bound does NOT work here.** For a fixed index cut
  `A, B ⊆ Fin k`, the statistic `(1/k²) ∑_{i∈A,j∈B} D(xᵢ, xⱼ)` is a function of the `k`
  sampled points with bounded differences `≤ 2/k`, so vertex-exposure Azuma gives only
  `exp(−c ε² k)` tails — which loses against the `4^k` cut pairs. This is the genuine
  extra difficulty of point sampling versus rounding (where independence over `k²`
  edges gave `exp(−c k²)`).
* **The classical route** (Lovász, *Large Networks and Graph Limits*, Lemma 10.6;
  BCLSV "Convergent sequences I" §4.3) therefore bounds the EXPECTATION of the sup
  first — `E_x[d_□(W, H_{W,x})] → 0` uniformly in `W` — by the ghost-sample /
  quadratic-form argument, and only then concentrates the (bounded-differences)
  random variable `x ↦ d_□(W, H_{W,x})` around its expectation via McDiarmid/Azuma.
* **Step reduction helps but does not dodge the core.** With Frieze–Kannan
  (`regularity`, PROVED) one may reduce `W` to a step graphon `U` with `m(ε)` parts:
  `d(W,H_{W,x}) ≤ d(W,U) + d(U,H_{U,x}) + d(H_{U,x},H_{W,x})`. The middle term is
  finite (cell-frequency concentration, `m` cells, honest union bound). The last term
  is the empirical matrix of the small-cut-norm kernel `D := W − U`, and bounding ITS
  cut norm is exactly the hard expectation step — sampling does not commute with
  cut-norm smallness pointwise.
* **Mathlib support**: `Mathlib.Probability.Moments.SubGaussian` provides
  `HasSubgaussianMGF`, Hoeffding for independent sums, and the conditionally
  sub-Gaussian Azuma (`measure_sum_ge_le_of_HasCondSubgaussianMGF`); there is no
  off-the-shelf McDiarmid, so the bounded-differences step will go through the
  conditional sub-Gaussian route (Doob/vertex-exposure decomposition of
  `f(x) − E f`) or a bespoke finite version in the style of `SamplingRounding`.
* **Measurability of the witness set** (`PointSamplingEvent` carries it as data): the
  plan is to take `X := {x | discretized majorant of d_□(W, H_{W,x}) < ε}` for a
  FINITE discretization of the cut-norm sup (cell-cuts on the `H`-side suffice for a
  2-sided estimate up to constants), making `X` a finite intersection/union of
  preimages of measurable coordinate functions. If this still turns ugly, a narrowed
  named lemma for the measurable bad set stays inside the `first_sampling_lemma`
  accounting — NOT a new live input.

## Layer plan (per the PR #11 decomposition)

1. `discretized cut norm approximation` — reduce `d_□(W, H_{W,x})` to finitely many
   cut predicates in the sampled coordinates, with controlled error.
2. `bounded-differences / Azuma scaffold` — the vertex-exposure decomposition for
   functionals of the sampled point sequence.
3. `uniform tail bound` — the expectation bound (Lovász 10.6 core) + concentration,
   uniform in `W`.
4. `event packaging` — the measurable witness set for `PointSamplingEvent`.

## PR #11A architecture (settled 2026-07-07, after literature check)

Reference mechanisms: Lovász Lemmas 10.6/10.7 (bounded kernels); the modern
generalization arXiv:2203.07581 confirms the split into *systematic error*
(expectation bound; Q-subsample ghost argument, their §6.2) and *dispersion*
(vertex-exposure martingale + Azuma — deferred to PR #11B).

**Majorant + triangle decomposition.** Fix ε; let `P` be the Frieze–Kannan partition
of `W` at quality `ε' := ε/8` with `m = m(ε')` parts (uniform in `W` — PROVED
`regularity`), `U := stepify P W`. Then

  `d_□(W, H_{W,x}) ≤ ε' + d_□(U, H_{U,x}) + maxcut((W−U)[x])`

* **Frequency term** `d_□(U, H_{U,x})`: `H_{U,x}` is the equipartition step graphon
  with entries `U(xᵢ,xⱼ)`; comparing to `U` is a pure weight-perturbation problem —
  bounded by `2·∑_cells |empirical frequency − μ(cell)|` (repo tooling:
  `cutDistance_step_weight_le`-style). Its expectation is elementary:
  `E|freq − μ| ≤ 1/(2√k)` per cell via Cauchy–Schwarz + the iid variance computation
  (`E(freq−μ)² = μ(1−μ)/k`) — no concentration inequality needed, `m` cells total.
* **Core term** `maxcut(D[x])`, `D := W − U`, `‖D‖_□ ≤ ε'`, `|D| ≤ 1`: THE deep step —
  `E_x[max_{S,T ⊆ [k]} (1/k²)|∑_{i∈S,j∈T} D(xᵢ,xⱼ)|] ≤ ‖D‖_□ + O(k^{−1/4})`.
  **Mechanism (Q-subsample cut guessing; AFKK / book 10.7)**: naive union over `4^k`
  cuts fails (only `exp(−cε²k)` per-cut tails). Instead: for the maximizer `(S*,T*)`,
  the optimal `T` given `S` is the sign set of `r_j := (1/k)∑_{i∈S*} D(xᵢ,xⱼ)`;
  estimate `r_j` by a random subsample `Q` of size `q` (error `O(1/√q)` per point in
  expectation), so the near-optimal cut is DETERMINED by `(x_Q, S* ∩ Q)` — only `2^q`
  selection rules. For each FIXED rule, the cut becomes a genuine measurable set
  determined by the `Q`-coordinates, independent of the fresh coordinates, so the
  fresh-sample expectation of the rectangle sum is `≤ ‖D‖_□ + O((q + √k)/k)`.
  Union over `2^q` rules with second-moment control; `q := ⌈√k⌉` gives `O(k^{−1/4})`.
  Both `±` directions by applying to `D` and `−D`.

## PR #11A execution notes (2026-07-07 survey of repo APIs)

* **Deliverable shape** (`point_sampling_expectation_bound`): ∃K, ∀ k ≥ K, ∀ W, ∃ a
  measurable nonnegative integrable majorant `M` with
  `∀ᵐ x, cutDistance W (sampleWeightedGraphonOn W x) ≤ M x` and `∫ M < ε`.
* **KEY SIMPLIFICATION — PR #11B is just Markov.** Given the expectation bound at
  accuracy `ε·η`, Markov's inequality on the nonnegative majorant gives
  `π{M ≥ ε} ≤ η`, and `X := {M < ε} \ N` (N a measurable null superset of the
  domination-failure set) is the measurable witness for
  `PointSamplingEvent W k ε η`. NO Azuma / bounded differences needed for the
  qualitative statement — concentration would only improve η-rates.
* `regularity W ε hε : ∃ P, P.parts.card ≤ regularityBound ε ∧
  cutNormDiff W (stepify P W) ≤ ε` (proved) — the `m(ε)` source.
* `cutDistance_step_weight_le` (InverseCounting, PRIVATE — de-privatize like
  `exists_partition_with_measures`; carries the Rokhlin trace, acceptable): needs the
  SAME cell count on both sides via injective enumerations. For the frequency term
  (`d(U, H_{U,x})`), the coarsened partition (equicells grouped by the P-cell of their
  sample point) can have EMPTY groups, which break enumeration injectivity — pad empty
  groups with distinct measure-zero decorated cells (singleton-point technique from
  `exists_partition_with_measures`'s proof). This is the main construction cost of
  the frequency layer.
* The coefficient alignment (`U(xᵢ,xⱼ) = c_P(cell of xᵢ, cell of xⱼ)` at sampled
  points, clamps invisible) is a.e.-x, via the `graphonEval` transfer machinery
  (as in `ae_edge_params_aligned`) applied to BOTH `W` and `U := stepify P W`.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloq. Publ. 60 (2012),
  Lemmas 10.6, 10.7, 10.16 (First Sampling Lemma).
* C. Borgs, J.T. Chayes, L. Lovász, V.T. Sós, K. Vesztergombi, *Convergent sequences
  of dense graphs I*, Adv. Math. 219 (2008), §4.3.
* N. Alon, W. Fernandez de la Vega, R. Kannan, M. Karpinski, *Random sampling and
  approximation of MAX-CSPs*, J. Comput. Syst. Sci. 67 (2003) — the Q-subsample
  cut-guessing mechanism.
* M. Borbényi, B. Ráth, S. Rokob, *The cut norm and sampling lemmas for unbounded
  kernels*, arXiv:2203.07581 — modern treatment; confirms the systematic-error /
  dispersion split.
-/

open MeasureTheory Set Filter Finset

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

section PointSampling

variable [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

/-- **The point-sampling half of the First Sampling Lemma** (PR #11 target; sorried
scaffold — this branch ships only when it is proved). With `W`-uniform `K`: for all
`k ≥ K`, the weighted sampled graphon `H_{W,x}` is within cut distance `ε` of `W`
outside a bad set of measure `≤ η`.

Together with `rounding_event_of_large_k` and `sampleGoodMassOn_of_events`, this
closes `first_sampling_lemma` (the PR #12 recombination). -/
theorem point_sampling_event_of_large_k (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ (_ : NeZero k), ∀ W : Graphon α μ,
      PointSamplingEvent W k ε η := by
  sorry

end PointSampling

end Graphon
