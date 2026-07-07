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

/-! ## PR #11A Layers 1+2: the point-sampling majorant and its frequency accounting

This section builds the nonnegative, measurable, integrable **majorant**
`pointSamplingMajorant W ε' k x` dominating `cutDistance W (H_{W,x})` a.e., and bounds the
expectation of its *frequency* term. The deep *core* term (Layer 3, the AFKK Q-subsample
ghost argument) is isolated in the single sorried private lemma
`coreTerm_expectation_bound`.

The triangle decomposition through `U := stepify P W` (`P` the Frieze–Kannan partition of
`W` at quality `ε'`) is

  `d_□(W, H_{W,x}) ≤ d_□(W, U) + d_□(U, H_{U,x}) + d_□(H_{U,x}, H_{W,x})`
                  ` ≤ ε'      + freqTerm       + coreTerm`.

* `d_□(W, U) ≤ cutNormDiff W U ≤ ε'` — `cutDistance_le_cutNormDiff` + `regularity`.
* `d_□(H_{U,x}, H_{W,x}) ≤ coreTerm` — the PR #10 cut certificate
  `cutNormDiff_mkStepGraphon_le_of_cuts`, pointwise in `x`.
* `d_□(U, H_{U,x}) ≤ freqTerm` — the weight-perturbation construction (see
  `cutDistance_chosenStep_sampleWeighted_le_freqTerm`). -/

section PointSamplingMajorant

open scoped Classical

variable [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

/-- The chosen Frieze–Kannan partition of `W` at quality `ε'` (junk `trivialPartition`
when `ε' ≤ 0`; all theorems below carry `0 < ε'`). -/
noncomputable def chosenPartition (W : Graphon α μ) (ε' : ℝ) : MeasurablePartition α μ :=
  if hε' : 0 < ε' then (regularity W ε' hε').choose else trivialPartition

/-- The chosen step-graphon approximation `U := stepify P W`. -/
noncomputable def chosenStep (W : Graphon α μ) (ε' : ℝ) : Graphon α μ :=
  stepify (chosenPartition W ε') W

/-- The clamped, `(min,max)`-ordered evaluation of a graphon `V` at the sampled pair
`(x_i, x_j)` — matching the coefficient shape of `sampleWeightedGraphonOn`. -/
noncomputable def clampEval (V : Graphon α μ) {k : ℕ} (x : Fin k → α) (i j : Fin k) : ℝ :=
  min 1 (max 0 (V.toAEEqFun (x (min i j), x (max i j))))

/-- The empirical frequency of a cell `S` among the `k` sampled points. -/
noncomputable def empFreq {k : ℕ} (S : Set α) (x : Fin k → α) : ℝ :=
  ((Finset.univ.filter (fun i : Fin k ↦ x i ∈ S)).card : ℝ) / k

/-- The **frequency term**: `2·∑_cells |empirical frequency − μ(cell)|`, plus a `1/k`
slack absorbing the diagonal mismatch between `H_{U,x}` and the coarsened comparison
graphon (see the domination proof). -/
noncomputable def freqTerm (W : Graphon α μ) (ε' : ℝ) (k : ℕ) (x : Fin k → α) : ℝ :=
  2 * ∑ S ∈ (chosenPartition W ε').parts, |empFreq S x - (μ S).toReal| + (k : ℝ)⁻¹

/-- The **core term**: the maximum, over vertex cuts `A, B ⊆ [k]`, of the weighted cut sum
of the empirical matrix `clampEval W − clampEval U` on the equipartition. Its summand shape
matches `cutNormDiff_mkStepGraphon_le_of_cuts` exactly (weights `(μ cell)·(μ cell)`), so the
certificate applies to `d_□(H_{U,x}, H_{W,x})` directly. -/
noncomputable def coreTerm (W : Graphon α μ) (ε' : ℝ) (k : ℕ) [NeZero k] (x : Fin k → α) : ℝ :=
  (Finset.univ : Finset (Finset (Fin k) × Finset (Fin k))).sup'
    Finset.univ_nonempty
    (fun AB ↦ |∑ i ∈ AB.1, ∑ j ∈ AB.2,
      ((μ (equipartitionCell (α := α) (μ := μ) k i)).toReal *
        (μ (equipartitionCell (α := α) (μ := μ) k j)).toReal) *
      (clampEval W x i j - clampEval (chosenStep W ε') x i j)|)

/-- **The point-sampling majorant** `ε' + freqTerm + coreTerm`. -/
noncomputable def pointSamplingMajorant (W : Graphon α μ) (ε' : ℝ) (k : ℕ) [NeZero k]
    (x : Fin k → α) : ℝ :=
  ε' + freqTerm W ε' k x + coreTerm W ε' k x

/-! ### Bounds and nonnegativity -/

omit [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ] in
theorem clampEval_nonneg (V : Graphon α μ) {k : ℕ} (x : Fin k → α) (i j : Fin k) :
    0 ≤ clampEval V x i j :=
  le_min zero_le_one (le_max_left 0 _)

omit [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ] in
theorem clampEval_le_one (V : Graphon α μ) {k : ℕ} (x : Fin k → α) (i j : Fin k) :
    clampEval V x i j ≤ 1 :=
  min_le_left 1 _

theorem coreTerm_nonneg (W : Graphon α μ) (ε' : ℝ) (k : ℕ) [NeZero k] (x : Fin k → α) :
    0 ≤ coreTerm W ε' k x := by
  refine le_trans (le_of_eq ?_) (Finset.le_sup' _
    (Finset.mem_univ ((∅, ∅) : Finset (Fin k) × Finset (Fin k))))
  simp only [Finset.sum_empty, abs_zero]

/-- Crude uniform bound on the core term: `coreTerm ≤ 1`. -/
theorem coreTerm_le_one (W : Graphon α μ) (ε' : ℝ) (k : ℕ) [NeZero k] (x : Fin k → α) :
    coreTerm W ε' k x ≤ 1 := by
  refine Finset.sup'_le _ _ (fun AB _ ↦ ?_)
  have hμ : ∀ i : Fin k, (μ (equipartitionCell (α := α) (μ := μ) k i)).toReal = (k : ℝ)⁻¹ :=
    equipartitionCell_measure k
  have hbound : ∀ i ∈ AB.1, ∀ j ∈ AB.2,
      |((μ (equipartitionCell (α := α) (μ := μ) k i)).toReal *
          (μ (equipartitionCell (α := α) (μ := μ) k j)).toReal) *
        (clampEval W x i j - clampEval (chosenStep W ε') x i j)| ≤ (k : ℝ)⁻¹ * (k : ℝ)⁻¹ := by
    intro i _ j _
    rw [abs_mul, hμ i, hμ j, abs_of_nonneg (by positivity)]
    refine mul_le_of_le_one_right (by positivity) ?_
    have h1 := clampEval_le_one W x i j
    have h2 := clampEval_nonneg W x i j
    have h3 := clampEval_le_one (chosenStep W ε') x i j
    have h4 := clampEval_nonneg (chosenStep W ε') x i j
    rw [abs_le]; constructor <;> linarith
  calc |∑ i ∈ AB.1, ∑ j ∈ AB.2,
          ((μ (equipartitionCell (α := α) (μ := μ) k i)).toReal *
            (μ (equipartitionCell (α := α) (μ := μ) k j)).toReal) *
          (clampEval W x i j - clampEval (chosenStep W ε') x i j)|
      ≤ ∑ i ∈ AB.1, ∑ j ∈ AB.2, ((k : ℝ)⁻¹ * (k : ℝ)⁻¹) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj ↦ ?_)
        exact hbound i hi j hj
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin k)), ∑ j ∈ (Finset.univ : Finset (Fin k)),
          ((k : ℝ)⁻¹ * (k : ℝ)⁻¹) := by
        refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ AB.1)
          (fun i _ _ ↦ Finset.sum_nonneg fun j _ ↦ by positivity)).trans ?_
        exact Finset.sum_le_sum fun i _ ↦
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ AB.2)
            (fun j _ _ ↦ by positivity)
    _ = 1 := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hk : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
        field_simp

omit [MeasurableSpace α] [StandardBorelSpace α] in
theorem empFreq_nonneg {k : ℕ} (S : Set α) (x : Fin k → α) : 0 ≤ empFreq S x := by
  unfold empFreq; positivity

omit [MeasurableSpace α] [StandardBorelSpace α] in
theorem empFreq_le_one {k : ℕ} [NeZero k] (S : Set α) (x : Fin k → α) : empFreq S x ≤ 1 := by
  unfold empFreq
  rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k))]
  calc ((Finset.univ.filter (fun i : Fin k ↦ x i ∈ S)).card : ℝ)
      ≤ ((Finset.univ : Finset (Fin k)).card : ℝ) := by
        exact_mod_cast Finset.card_filter_le _ _
    _ = k := by rw [Finset.card_univ, Fintype.card_fin]

omit [IsProbabilityMeasure μ] [NoAtoms μ] in
/-- The frequency deviation of a single cell is at most `1`. -/
theorem abs_empFreq_sub_le_one {k : ℕ} [NeZero k] (S : Set α) (x : Fin k → α)
    (hS : (μ S).toReal ≤ 1) :
    |empFreq S x - (μ S).toReal| ≤ 1 := by
  rw [abs_le]
  have h0 := empFreq_nonneg S x
  have h1 := empFreq_le_one S x
  have h2 : 0 ≤ (μ S).toReal := ENNReal.toReal_nonneg
  constructor <;> linarith

omit [StandardBorelSpace α] [NoAtoms μ] in
theorem freqTerm_nonneg (W : Graphon α μ) (ε' : ℝ) (k : ℕ) [NeZero k] (x : Fin k → α) :
    0 ≤ freqTerm W ε' k x := by
  unfold freqTerm
  have h1 : 0 ≤ 2 * ∑ S ∈ (chosenPartition W ε').parts, |empFreq S x - (μ S).toReal| :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun S _ ↦ abs_nonneg _)
  have h2 : 0 ≤ (k : ℝ)⁻¹ := by positivity
  linarith

/-- The nonnegativity of the majorant (given `0 ≤ ε'`). -/
theorem pointSamplingMajorant_nonneg (W : Graphon α μ) {ε' : ℝ} (hε' : 0 ≤ ε') (k : ℕ)
    [NeZero k] (x : Fin k → α) : 0 ≤ pointSamplingMajorant W ε' k x := by
  unfold pointSamplingMajorant
  have h1 := freqTerm_nonneg W ε' k x
  have h2 := coreTerm_nonneg W ε' k x
  linarith

/-! ### Measurability and integrability -/

omit [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ] in
theorem measurable_clampEval (V : Graphon α μ) {k : ℕ} (i j : Fin k) :
    Measurable (fun x : Fin k → α ↦ clampEval V x i j) := by
  unfold clampEval
  refine measurable_const.min (measurable_const.max ?_)
  exact V.toAEEqFun.measurable.comp
    ((measurable_pi_apply _).prodMk (measurable_pi_apply _))

omit [StandardBorelSpace α] in
theorem measurable_empFreq {k : ℕ} {S : Set α} (hS : MeasurableSet S) :
    Measurable (fun x : Fin k → α ↦ empFreq S x) := by
  unfold empFreq
  have heq : (fun x : Fin k → α ↦
        ((Finset.univ.filter (fun i : Fin k ↦ x i ∈ S)).card : ℝ) / k)
      = fun x ↦ (∑ i : Fin k, Set.indicator S (fun _ ↦ (1 : ℝ)) (x i)) / k := by
    funext x
    rw [Finset.card_filter, Nat.cast_sum]
    refine congrArg (· / (k : ℝ)) (Finset.sum_congr rfl (fun i _ ↦ ?_))
    by_cases h : x i ∈ S <;> simp [Set.indicator, h]
  rw [heq]
  refine Measurable.div_const ?_ _
  exact Finset.measurable_sum _
    (fun i _ ↦ (measurable_const.indicator hS).comp (measurable_pi_apply i))

omit [NoAtoms μ] in
theorem measurable_freqTerm (W : Graphon α μ) (ε' : ℝ) (k : ℕ) [NeZero k] :
    Measurable (fun x : Fin k → α ↦ freqTerm W ε' k x) := by
  unfold freqTerm
  refine ((measurable_const.mul (Finset.measurable_sum _ (fun S hS ↦ ?_))).add_const _)
  exact continuous_abs.measurable.comp ((measurable_empFreq
    ((chosenPartition W ε').measurableSet_part hS)).sub measurable_const)

theorem measurable_coreTerm (W : Graphon α μ) (ε' : ℝ) (k : ℕ) [NeZero k] :
    Measurable (fun x : Fin k → α ↦ coreTerm W ε' k x) := by
  have heq : (fun x : Fin k → α ↦ coreTerm W ε' k x) =
      Finset.univ.sup' Finset.univ_nonempty
        (fun (AB : Finset (Fin k) × Finset (Fin k)) (x : Fin k → α) ↦
          |∑ i ∈ AB.1, ∑ j ∈ AB.2,
          ((μ (equipartitionCell (α := α) (μ := μ) k i)).toReal *
            (μ (equipartitionCell (α := α) (μ := μ) k j)).toReal) *
          (clampEval W x i j - clampEval (chosenStep W ε') x i j)|) := by
    funext x
    rw [Finset.sup'_apply]
    rfl
  rw [heq]
  refine Finset.measurable_sup' _ (fun AB _ ↦ ?_)
  refine continuous_abs.measurable.comp
    (Finset.measurable_sum _ (fun i _ ↦ Finset.measurable_sum _ (fun j _ ↦ ?_)))
  exact measurable_const.mul
    ((measurable_clampEval W i j).sub (measurable_clampEval (chosenStep W ε') i j))

theorem measurable_pointSamplingMajorant (W : Graphon α μ) (ε' : ℝ) (k : ℕ) [NeZero k] :
    Measurable (fun x : Fin k → α ↦ pointSamplingMajorant W ε' k x) := by
  unfold pointSamplingMajorant
  exact (measurable_const.add (measurable_freqTerm W ε' k)).add (measurable_coreTerm W ε' k)

/-- Crude uniform bound on the frequency term. -/
theorem freqTerm_le (W : Graphon α μ) (ε' : ℝ) (k : ℕ) [NeZero k] (x : Fin k → α) :
    freqTerm W ε' k x ≤ 2 * ((chosenPartition W ε').parts.card) + 1 := by
  unfold freqTerm
  have hsum : ∑ S ∈ (chosenPartition W ε').parts, |empFreq S x - (μ S).toReal|
      ≤ ((chosenPartition W ε').parts.card : ℝ) := by
    calc ∑ S ∈ (chosenPartition W ε').parts, |empFreq S x - (μ S).toReal|
        ≤ ∑ _S ∈ (chosenPartition W ε').parts, (1 : ℝ) := by
          refine Finset.sum_le_sum fun S hS ↦ abs_empFreq_sub_le_one S x ?_
          rw [← ENNReal.toReal_one]
          exact ENNReal.toReal_mono (by simp)
            (by rw [← measure_univ (μ := μ)]; exact measure_mono (Set.subset_univ _))
      _ = ((chosenPartition W ε').parts.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hkinv : (k : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  nlinarith [hsum]

theorem integrable_pointSamplingMajorant (W : Graphon α μ) (ε' : ℝ) (k : ℕ) [NeZero k] :
    Integrable (fun x : Fin k → α ↦ pointSamplingMajorant W ε' k x)
      (Measure.pi (fun _ : Fin k ↦ μ)) := by
  refine Integrable.mono' (integrable_const
      (|ε'| + (2 * ((chosenPartition W ε').parts.card) + 1) + 1))
    (measurable_pointSamplingMajorant W ε' k).aestronglyMeasurable
    (ae_of_all _ (fun x ↦ ?_))
  unfold pointSamplingMajorant
  rw [Real.norm_eq_abs, abs_le]
  have hf0 := freqTerm_nonneg W ε' k x
  have hf1 := freqTerm_le W ε' k x
  have hc0 := coreTerm_nonneg W ε' k x
  have hc1 := coreTerm_le_one W ε' k x
  have hε := le_abs_self ε'
  have hε' := neg_abs_le ε'
  constructor <;> nlinarith

/-! ### A.e. domination -/

omit [StandardBorelSpace α] [NoAtoms μ] in
/-- **Part a** (deterministic): `W` is `ε'`-close to its step approximation. -/
theorem cutDistance_W_chosenStep_le (W : Graphon α μ) {ε' : ℝ} (hε' : 0 < ε') :
    cutDistance W (chosenStep W ε') ≤ ε' := by
  refine (cutDistance_le_cutNormDiff _ _).trans ?_
  show cutNormDiff W (stepify (chosenPartition W ε') W) ≤ ε'
  rw [chosenPartition, dif_pos hε']
  exact (regularity W ε' hε').choose_spec.2

/-- **Part b** (pointwise cut certificate): the two weighted sampled graphons differ by at
most the core term. Applies `cutNormDiff_mkStepGraphon_le_of_cuts` on the equipartition. -/
theorem cutDistance_sampleWeighted_le_coreTerm (W : Graphon α μ) (ε' : ℝ) (k : ℕ) [NeZero k]
    (x : Fin k → α) :
    cutDistance (sampleWeightedGraphonOn (chosenStep W ε') x) (sampleWeightedGraphonOn W x)
      ≤ coreTerm W ε' k x := by
  refine (cutDistance_le_cutNormDiff _ _).trans ?_
  unfold sampleWeightedGraphonOn
  apply cutNormDiff_mkStepGraphon_le_of_cuts (equipartition k)
    (equipartitionCell (α := α) (μ := μ) k) (equipartitionCell_mem k)
    (equipartitionCell_injective k) (equipartitionCell_surjOn k)
  intro A B
  unfold coreTerm
  -- `|∑∑ (μc)(cU − cW)| = |∑∑ (μc)(cW − cU)| ≤ coreTerm`, with dites collapsed
  refine le_trans (le_of_eq ?_) (Finset.le_sup' _ (Finset.mem_univ (A, B)))
  rw [← abs_neg, ← Finset.sum_neg_distrib]
  refine congrArg abs (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h₀ : (∃ i', equipartitionCell (α := α) (μ := μ) k i' = equipartitionCell k i) ∧
      (∃ j', equipartitionCell (α := α) (μ := μ) k j' = equipartitionCell k j) :=
    ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
  simp only [clampEval]
  rw [dif_pos h₀, dif_pos h₀, choose_cell_eq h₀.1, choose_cell_eq h₀.2]
  ring

/-- **Part c — the frequency layer** (the weight-perturbation construction). The chosen step
graphon is `freqTerm`-close to its own weighted sample. This is the main construction cost of
the point-sampling majorant: the equicells grouped by the `P`-cell of their sample point form
a coarsened partition (with empty groups padded by decorated measure-zero singletons), and
`cutDistance_step_weight_le` bounds the cut distance by `2·∑_cells |empFreq − μ(cell)|`; the
extra `1/k` absorbs the diagonal-block mismatch between the sample graphon and the coarsened
comparison. Part of the `first_sampling_lemma` accounting, NOT a new live input. -/
private theorem cutDistance_chosenStep_sampleWeighted_le_freqTerm (W : Graphon α μ) {ε' : ℝ}
    (hε' : 0 < ε') (k : ℕ) [NeZero k] :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin k ↦ μ),
      cutDistance (chosenStep W ε') (sampleWeightedGraphonOn (chosenStep W ε') x)
        ≤ freqTerm W ε' k x := by
  sorry

/-- **A.e. domination of the cut distance by the point-sampling majorant.** Assembles the
triangle `d_□(W, H_{W,x}) ≤ d_□(W, U) + d_□(U, H_{U,x}) + d_□(H_{U,x}, H_{W,x})` from parts
a (`cutDistance_W_chosenStep_le`), c (`cutDistance_chosenStep_sampleWeighted_le_freqTerm`) and
b (`cutDistance_sampleWeighted_le_coreTerm`). -/
theorem ae_cutDistance_le_pointSamplingMajorant (W : Graphon α μ) {ε' : ℝ} (hε' : 0 < ε')
    (k : ℕ) [NeZero k] :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin k ↦ μ),
      cutDistance W (sampleWeightedGraphonOn W x) ≤ pointSamplingMajorant W ε' k x := by
  filter_upwards [cutDistance_chosenStep_sampleWeighted_le_freqTerm W hε' k] with x hc
  have ha := cutDistance_W_chosenStep_le W hε'
  have hb := cutDistance_sampleWeighted_le_coreTerm W ε' k x
  have htri1 : cutDistance W (sampleWeightedGraphonOn W x) ≤
      cutDistance W (chosenStep W ε') +
        cutDistance (chosenStep W ε') (sampleWeightedGraphonOn W x) :=
    cutDistance_triangle _ _ _
  have htri2 : cutDistance (chosenStep W ε') (sampleWeightedGraphonOn W x) ≤
      cutDistance (chosenStep W ε') (sampleWeightedGraphonOn (chosenStep W ε') x) +
        cutDistance (sampleWeightedGraphonOn (chosenStep W ε') x)
          (sampleWeightedGraphonOn W x) :=
    cutDistance_triangle _ _ _
  unfold pointSamplingMajorant
  linarith

/-! ### Layer 2: the frequency expectation bound -/

omit [IsProbabilityMeasure μ] [NoAtoms μ] in
theorem measurable_abs_empFreq_sub {k : ℕ} {S : Set α} (hS : MeasurableSet S) :
    Measurable (fun x : Fin k → α ↦ |empFreq S x - (μ S).toReal|) :=
  continuous_abs.measurable.comp ((measurable_empFreq hS).sub measurable_const)

theorem integrable_abs_empFreq_sub {k : ℕ} [NeZero k] {S : Set α} (hS : MeasurableSet S) :
    Integrable (fun x : Fin k → α ↦ |empFreq S x - (μ S).toReal|)
      (Measure.pi (fun _ : Fin k ↦ μ)) := by
  refine Integrable.mono' (integrable_const 1)
    (measurable_abs_empFreq_sub hS).aestronglyMeasurable (ae_of_all _ (fun x ↦ ?_))
  rw [Real.norm_eq_abs, abs_abs]
  have hle1 : (μ S).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono (by simp)
      (by rw [← measure_univ (μ := μ)]; exact measure_mono (Set.subset_univ _))
  exact abs_empFreq_sub_le_one S x hle1

/-- **Per-cell frequency bound** (iid variance + Cauchy–Schwarz): the mean absolute deviation
of the empirical cell frequency from the true measure is `O(1/√k)`, uniformly over cells. The
variance identity `E(empFreq − μS)² = μS(1−μS)/k ≤ 1/(4k)` (cross terms vanish by coordinate
independence) plus `E|Y| ≤ √(E Y²)` on a probability space gives the `1/(2√k)` bound.
Elementary; part of the `first_sampling_lemma` accounting, NOT a new live input. -/
private theorem integral_abs_empFreq_sub_le {k : ℕ} [NeZero k] {S : Set α}
    (hS : MeasurableSet S) :
    ∫ x, |empFreq S x - (μ S).toReal| ∂Measure.pi (fun _ : Fin k ↦ μ)
      ≤ 1 / (2 * Real.sqrt k) := by
  sorry

/-- **Layer 2 — the frequency expectation bound.** The expectation of the frequency term is at
most `m/√k + 1/k`, where `m` is the number of Frieze–Kannan cells; both terms vanish as
`k → ∞` (with `m = m(ε')` fixed). Elementary: linearity of the integral plus the per-cell
`integral_abs_empFreq_sub_le`. -/
theorem freqTerm_expectation_bound (W : Graphon α μ) (ε' : ℝ) (k : ℕ) [NeZero k] :
    ∫ x, freqTerm W ε' k x ∂Measure.pi (fun _ : Fin k ↦ μ) ≤
      ((chosenPartition W ε').parts.card : ℝ) / Real.sqrt k + (k : ℝ)⁻¹ := by
  have hint_dev : ∀ S ∈ (chosenPartition W ε').parts,
      Integrable (fun x : Fin k → α ↦ |empFreq S x - (μ S).toReal|)
        (Measure.pi (fun _ : Fin k ↦ μ)) :=
    fun S hS ↦ integrable_abs_empFreq_sub ((chosenPartition W ε').measurableSet_part hS)
  have hint_sum : Integrable (fun x : Fin k → α ↦
      ∑ S ∈ (chosenPartition W ε').parts, |empFreq S x - (μ S).toReal|)
      (Measure.pi (fun _ : Fin k ↦ μ)) :=
    integrable_finsetSum _ hint_dev
  have hsplit : ∫ x, freqTerm W ε' k x ∂Measure.pi (fun _ : Fin k ↦ μ)
      = 2 * ∑ S ∈ (chosenPartition W ε').parts,
          (∫ x, |empFreq S x - (μ S).toReal| ∂Measure.pi (fun _ : Fin k ↦ μ)) + (k : ℝ)⁻¹ := by
    unfold freqTerm
    rw [integral_add (hint_sum.const_mul 2) (integrable_const _),
      integral_const_mul, integral_finsetSum _ hint_dev, integral_const, smul_eq_mul,
      probReal_univ, one_mul]
  rw [hsplit]
  have hper : ∑ S ∈ (chosenPartition W ε').parts,
      ∫ x, |empFreq S x - (μ S).toReal| ∂Measure.pi (fun _ : Fin k ↦ μ)
        ≤ ∑ _S ∈ (chosenPartition W ε').parts, 1 / (2 * Real.sqrt k) :=
    Finset.sum_le_sum fun S hS ↦
      integral_abs_empFreq_sub_le ((chosenPartition W ε').measurableSet_part hS)
  rw [Finset.sum_const, nsmul_eq_mul] at hper
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hsqrtpos : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkpos
  have hgoal : 2 * ∑ S ∈ (chosenPartition W ε').parts,
      ∫ x, |empFreq S x - (μ S).toReal| ∂Measure.pi (fun _ : Fin k ↦ μ)
        ≤ ((chosenPartition W ε').parts.card : ℝ) / Real.sqrt k := by
    refine le_trans (by nlinarith [hper] : _ ≤ 2 * (((chosenPartition W ε').parts.card : ℝ) *
      (1 / (2 * Real.sqrt k)))) (le_of_eq ?_)
    field_simp
  linarith [hgoal]

/-- **Layer 3 — the Q-subsample / AFKK core** (deferred; see the design notes above):
the expectation of the core term is at most `ε'` plus a `k`-vanishing dispersion cost. This
is part of the `first_sampling_lemma` analytic accounting, NOT a new live input — the
naive `4^k`-cut union bound fails here (only `exp(−cε²k)` per-cut tails), so it needs the
Q-subsample cut-guessing mechanism. -/
private theorem coreTerm_expectation_bound (W : Graphon α μ) (ε' : ℝ) (hε' : 0 < ε')
    {k : ℕ} [NeZero k] :
    ∫ x, coreTerm W ε' k x ∂Measure.pi (fun _ : Fin k ↦ μ) ≤
      ε' + 8 * ((k : ℝ) ^ (-(1 / 4 : ℝ))) := by
  sorry

end PointSamplingMajorant

end Graphon
