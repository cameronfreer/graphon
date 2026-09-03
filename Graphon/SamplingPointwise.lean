/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.McDiarmid
import Graphon.SamplingRounding
import Graphon.Regularity
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The point-sampling half of the First Sampling Lemma

Main theorem:

`point_sampling_event_of_large_k : ∀ ε η > 0, ∃ K, ∀ k ≥ K, ∀ [NeZero k],
  ∀ W : Graphon α μ, PointSamplingEvent W k ε η`

matching the shape of `rounding_event_of_large_k`, so that `first_sampling_lemma` can
pick one `k` for both events and close via `sampleGoodMassOn_of_events`.

## Design notes

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
  (`regularity`) one may reduce `W` to a step graphon `U` with `m(ε)` parts:
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

## Layer structure

1. `discretized cut norm approximation` — reduce `d_□(W, H_{W,x})` to finitely many
   cut predicates in the sampled coordinates, with controlled error.
2. `bounded-differences / Azuma scaffold` — the vertex-exposure decomposition for
   functionals of the sampled point sequence.
3. `uniform tail bound` — the expectation bound (Lovász 10.6 core) + concentration,
   uniform in `W`.
4. `event packaging` — the measurable witness set for `PointSamplingEvent`.

## Architecture of the expectation bound

Reference mechanisms: Lovász Lemmas 10.6/10.7 (bounded kernels); the modern
generalization arXiv:2203.07581 confirms the split into *systematic error*
(expectation bound; Q-subsample ghost argument, their §6.2) and *dispersion*
(vertex-exposure martingale + Azuma).

**Majorant + triangle decomposition.** Fix ε; let `P` be the Frieze–Kannan partition
of `W` at quality `ε' := ε/8` with `m = m(ε')` parts (uniform in `W`, by
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

## Implementation notes

* **Deliverable shape** (`point_sampling_expectation_bound`): ∃K, ∀ k ≥ K, ∀ W, ∃ a
  measurable nonnegative integrable majorant `M` with
  `∀ᵐ x, cutDistance W (sampleWeightedGraphonOn W x) ≤ M x` and `∫ M < ε`.
* **Simplification — the bad-set form is just Markov.** Given the expectation bound at
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

open scoped ENNReal ProbabilityTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

/-! ## Layers 1+2: the point-sampling majorant and its frequency accounting

This section builds the nonnegative, measurable, integrable **majorant**
`pointSamplingMajorant W ε' k x` dominating `cutDistance W (H_{W,x})` a.e., and bounds the
expectation of its *frequency* term. The deep *core* term (Layer 3, the AFKK Q-subsample
ghost argument) is isolated in the private lemma `coreTerm_expectation_bound`.

The triangle decomposition through `U := stepify P W` (`P` the Frieze–Kannan partition of
`W` at quality `ε'`) is

  `d_□(W, H_{W,x}) ≤ d_□(W, U) + d_□(U, H_{U,x}) + d_□(H_{U,x}, H_{W,x})`
                  ` ≤ ε'      + freqTerm       + coreTerm`.

* `d_□(W, U) ≤ cutNormDiff W U ≤ ε'` — `cutDistance_le_cutNormDiff` + `regularity`.
* `d_□(H_{U,x}, H_{W,x}) ≤ coreTerm` — the cut certificate
  `cutNormDiff_mkStepGraphon_le_of_cuts`, pointwise in `x`.
* `d_□(U, H_{U,x}) ≤ freqTerm` — the weight-perturbation construction (see
  `cutDistance_chosenStep_sampleWeighted_le_freqTerm`). -/

section PointSamplingMajorant

open scoped Classical

variable [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ]

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

omit [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ] in
theorem clampEval_nonneg (V : Graphon α μ) {k : ℕ} (x : Fin k → α) (i j : Fin k) :
    0 ≤ clampEval V x i j :=
  le_min zero_le_one (le_max_left 0 _)

omit [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ] in
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

omit [IsProbabilityMeasure μ] [NullSingletonClass μ] in
/-- The frequency deviation of a single cell is at most `1`. -/
theorem abs_empFreq_sub_le_one {k : ℕ} [NeZero k] (S : Set α) (x : Fin k → α)
    (hS : (μ S).toReal ≤ 1) :
    |empFreq S x - (μ S).toReal| ≤ 1 := by
  rw [abs_le]
  have h0 := empFreq_nonneg S x
  have h1 := empFreq_le_one S x
  have h2 : 0 ≤ (μ S).toReal := ENNReal.toReal_nonneg
  constructor <;> linarith

omit [StandardBorelSpace α] [NullSingletonClass μ] in
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

omit [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ] in
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

omit [NullSingletonClass μ] in
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

omit [StandardBorelSpace α] [NullSingletonClass μ] in
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

/-- `chosenStep W ε'` is definitionally the step graphon on `chosenPartition W ε'` with the
rectangle-average coefficients `rectAverage W`. -/
theorem chosenStep_eq_mkStepGraphon (W : Graphon α μ) (ε' : ℝ) :
    chosenStep W ε' = mkStepGraphon (chosenPartition W ε') (rectAverage W)
      (fun S hS T hT ↦ rectAverage_symm W S T
        ((chosenPartition W ε').measurableSet_part hS)
        ((chosenPartition W ε').measurableSet_part hT))
      (fun S hS T hT ↦ rectAverage_mem_Icc W S T
        ((chosenPartition W ε').measurableSet_part hS)
        ((chosenPartition W ε').measurableSet_part hT)) := rfl

-- `ae_pairMap_of_prod` now lives, generalized, in `Graphon/Sampling.lean`.

/-- For a.e. sampled `x`, every sampled point lies in some part of `P`. -/
theorem ae_forall_sample_mem_part (P : MeasurablePartition α μ) {k : ℕ} [NeZero k] :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin k ↦ μ), ∀ i : Fin k, ∃ S ∈ P.parts, x i ∈ S := by
  rw [ae_all_iff]
  intro i
  exact (MeasureTheory.measurePreserving_eval (fun _ : Fin k ↦ μ) i).quasiMeasurePreserving.ae
    P.ae_covers

omit [StandardBorelSpace α] [NullSingletonClass μ] in
/-- Graphons with a.e.-equal kernels are at cut-norm difference zero (every rectangle
integral of the difference vanishes). -/
theorem cutNormDiff_eq_zero_of_ae_eq (V₁ V₂ : Graphon α μ)
    (h : ∀ᵐ p ∂(μ.prod μ), V₁.toAEEqFun p = V₂.toAEEqFun p) :
    cutNormDiff V₁ V₂ = 0 := by
  have hzero : ∀ S T : Set α, rectIntegralDiff V₁ V₂ S T = 0 := by
    intro S T
    unfold rectIntegralDiff
    rw [show (∫ p in S ×ˢ T, (V₁.toAEEqFun p - V₂.toAEEqFun p) ∂(μ.prod μ)) =
        ∫ _p in S ×ˢ T, (0 : ℝ) ∂(μ.prod μ) from
      integral_congr_ae (ae_restrict_of_ae (by
        filter_upwards [h] with p hp
        rw [hp, sub_self]))]
    simp
  refine le_antisymm ?_ (cutNormDiff_nonneg V₁ V₂)
  unfold cutNormDiff
  refine Real.iSup_le (fun S ↦ Real.iSup_le (fun _ ↦ Real.iSup_le (fun T ↦
    Real.iSup_le (fun _ ↦ ?_) le_rfl) le_rfl) le_rfl) le_rfl
  rw [hzero S T]
  simp

/-- **A.e. coefficient alignment at sampled pairs** (part c5): off the diagonal, the
clamped evaluation of the chosen step graphon at a sampled pair equals the rectangle
average of the two cells containing the samples. -/
private theorem ae_clampEval_chosenStep_eq (W : Graphon α μ) (ε' : ℝ) {k : ℕ} [NeZero k]
    {i j : Fin k} (hij : i ≠ j) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin k ↦ μ),
      ∀ S ∈ (chosenPartition W ε').parts, ∀ T ∈ (chosenPartition W ε').parts,
        x (min i j) ∈ S → x (max i j) ∈ T →
          clampEval (chosenStep W ε') x i j = rectAverage W S T := by
  have hker : ∀ᵐ p ∂(μ.prod μ),
      (chosenStep W ε').toAEEqFun p
        = mkStepFun (chosenPartition W ε') (rectAverage W) p := by
    rw [chosenStep_eq_mkStepGraphon]
    exact AEEqFun.coeFn_mk _ _
  have hmm : min i j ≠ max i j := by
    rcases lt_or_gt_of_ne hij with h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact hij
    · rw [min_eq_right h.le, max_eq_left h.le]; exact hij.symm
  filter_upwards [ae_pairMap_of_prod (min i j) (max i j) hmm hker]
    with x hx S hS T hT hxS hxT
  have heval := mkStepFun_eq_at (chosenPartition W ε') (rectAverage W) hS hT
    (Set.mk_mem_prod hxS hxT)
  have havg := rectAverage_mem_Icc W S T
    ((chosenPartition W ε').measurableSet_part hS)
    ((chosenPartition W ε').measurableSet_part hT)
  rw [clampEval, hx, heval, max_eq_right havg.1, min_eq_right havg.2]

/-- A step-graphon coefficient function built from a symmetric matrix `M` indexed through an
injective enumeration `ι : Fin n → Set α` (matching the `dite`-shape of
`sampleWeightedGraphonOn`). -/
noncomputable def coeffOfMatrix {n : ℕ} (ι : Fin n → Set α) (M : Fin n → Fin n → ℝ) :
    Set α → Set α → ℝ :=
  fun A B ↦ if h : (∃ i, ι i = A) ∧ (∃ j, ι j = B) then M h.1.choose h.2.choose else 0

omit [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ] in
theorem coeffOfMatrix_symm {n : ℕ} (ι : Fin n → Set α) (M : Fin n → Fin n → ℝ)
    (hM : ∀ i j, M i j = M j i) (A B : Set α) :
    coeffOfMatrix ι M A B = coeffOfMatrix ι M B A := by
  unfold coeffOfMatrix
  by_cases h : (∃ i, ι i = A) ∧ (∃ j, ι j = B)
  · rw [dif_pos h, dif_pos ⟨h.2, h.1⟩]; exact hM _ _
  · rw [dif_neg h, dif_neg (fun hc ↦ h ⟨hc.2, hc.1⟩)]

omit [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ] in
theorem coeffOfMatrix_mem {n : ℕ} (ι : Fin n → Set α) (M : Fin n → Fin n → ℝ)
    (hM : ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1) (A B : Set α) :
    coeffOfMatrix ι M A B ∈ Set.Icc (0 : ℝ) 1 := by
  unfold coeffOfMatrix
  by_cases h : (∃ i, ι i = A) ∧ (∃ j, ι j = B)
  · rw [dif_pos h]; exact hM _ _
  · rw [dif_neg h]; exact ⟨le_refl 0, zero_le_one⟩

omit [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ] in
theorem coeffOfMatrix_eq {n : ℕ} (ι : Fin n → Set α) (M : Fin n → Fin n → ℝ)
    (hι : Function.Injective ι) (a b : Fin n) :
    coeffOfMatrix ι M (ι a) (ι b) = M a b := by
  unfold coeffOfMatrix
  have h : (∃ i, ι i = ι a) ∧ (∃ j, ι j = ι b) := ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  rw [dif_pos h]
  exact congr_arg₂ M (hι h.1.choose_spec) (hι h.2.choose_spec)

/-- **The coarsened partition** (part c1): for a.e.-good sampled `x` (each sample lies in a
`P`-cell, recorded by the slot map `g`), the equicells grouped by the `P`-slot of their
sample assemble into a `MeasurablePartition` `Q` whose cells (enumerated by `ιQ`, matched
slot-by-slot to `ιP`) have measure equal to the empirical frequency of the corresponding
`P`-cell, and each equicell lies (a.e.) inside its group's `Q`-cell. Empty groups are padded
by distinct measure-zero points extracted from a positive-measure group. Isolated construction
step; part of the `first_sampling_lemma` accounting, NOT a new live input. -/
private theorem exists_coarsened_partition {k : ℕ} [NeZero k] (P : MeasurablePartition α μ)
    (ιP : Fin P.parts.card → Set α) (hιP_mem : ∀ i, ιP i ∈ P.parts)
    (hιP_inj : Function.Injective ιP)
    (x : Fin k → α) (g : Fin k → Fin P.parts.card) (hg : ∀ i, x i ∈ ιP (g i)) :
    ∃ (Q : MeasurablePartition α μ) (ιQ : Fin P.parts.card → Set α),
      (∀ i, ιQ i ∈ Q.parts) ∧ Function.Injective ιQ ∧
      (∀ S ∈ Q.parts, ∃ i, ιQ i = S) ∧
      (∀ s, (μ (ιQ s)).toReal = empFreq (ιP s) x) ∧
      (∀ i : Fin k, μ (equipartitionCell (α := α) (μ := μ) k i \ ιQ (g i)) = 0) := by
  classical
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  -- distinct equicells are disjoint
  have hcell_disj : ∀ i j : Fin k, i ≠ j →
      Disjoint (equipartitionCell (α := α) (μ := μ) k i)
        (equipartitionCell (α := α) (μ := μ) k j) := fun i j hij ↦
    (equipartition k).pairwiseDisjoint (Finset.mem_coe.mpr (equipartitionCell_mem k i))
      (Finset.mem_coe.mpr (equipartitionCell_mem k j))
      (fun h ↦ hij (equipartitionCell_injective k h))
  -- slot membership ↔ sample membership
  have hgiff : ∀ (i : Fin k) (s : Fin P.parts.card), g i = s ↔ x i ∈ ιP s := by
    intro i s
    refine ⟨fun h ↦ h ▸ hg i, fun hxs ↦ ?_⟩
    by_contra hne
    have hd : Disjoint (ιP (g i)) (ιP s) := P.pairwiseDisjoint
      (Finset.mem_coe.mpr (hιP_mem (g i))) (Finset.mem_coe.mpr (hιP_mem s))
      (fun h ↦ hne (hιP_inj h))
    exact Set.disjoint_left.mp hd (hg i) hxs
  have hfilter : ∀ s : Fin P.parts.card, Finset.univ.filter (fun i ↦ g i = s)
      = Finset.univ.filter (fun i ↦ x i ∈ ιP s) := by
    intro s; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hgiff i s
  -- the equicell groups
  set Grp : Fin P.parts.card → Set α := fun s ↦ ⋃ i ∈ Finset.univ.filter (fun i ↦ g i = s),
    equipartitionCell (α := α) (μ := μ) k i with hGrp_def
  have hGrp_meas : ∀ s, MeasurableSet (Grp s) := fun s ↦
    Finset.measurableSet_biUnion _ (fun i _ ↦
      (equipartition k).measurableSet_part (equipartitionCell_mem k i))
  have hGrp_toReal : ∀ s, (μ (Grp s)).toReal
      = ((Finset.univ.filter (fun i ↦ g i = s)).card : ℝ) / k := by
    intro s
    rw [hGrp_def, measure_biUnion_finset
      (fun i _ j _ hij ↦ hcell_disj i j hij)
      (fun i _ ↦ (equipartition k).measurableSet_part (equipartitionCell_mem k i)),
      ENNReal.toReal_sum (fun i _ ↦ measure_ne_top μ _),
      Finset.sum_congr rfl (fun i _ ↦ equipartitionCell_measure k i),
      Finset.sum_const, nsmul_eq_mul, ← div_eq_mul_inv]
  have hGrp_disj : ∀ s t, s ≠ t → Disjoint (Grp s) (Grp t) := by
    intro s t hst
    rw [Set.disjoint_left]
    intro a ha hb
    rw [hGrp_def, Set.mem_iUnion₂] at ha hb
    obtain ⟨i, hi, hai⟩ := ha
    obtain ⟨i', hi', hai'⟩ := hb
    rw [Finset.mem_filter] at hi hi'
    exact Set.disjoint_left.mp
      (hcell_disj i i' (by rintro rfl; exact hst (hi.2 ▸ hi'.2))) hai hai'
  -- donor group and its distinct padding points
  set i0 : Fin k := (0 : Fin k) with hi0_def
  set s0 : Fin P.parts.card := g i0 with hs0_def
  have hsub0 : equipartitionCell (α := α) (μ := μ) k i0 ⊆ Grp s0 := by
    rw [hGrp_def]
    exact Set.subset_biUnion_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
  have hcell0_ne : μ (equipartitionCell (α := α) (μ := μ) k i0) ≠ 0 := by
    intro h
    have hh := equipartitionCell_measure (α := α) (μ := μ) k i0
    rw [h, ENNReal.toReal_zero] at hh
    exact (inv_pos.mpr hkpos).ne' hh.symm
  have hμ0 : μ (Grp s0) ≠ 0 := fun h ↦
    hcell0_ne (nonpos_iff_eq_zero.mp (le_trans (measure_mono hsub0) h.le))
  have hInf : (Grp s0).Infinite := fun hfin ↦ hμ0 (hfin.measure_zero μ)
  set emb : ℕ ↪ ↥(Grp s0) := Set.Infinite.natEmbedding (Grp s0) hInf with hemb_def
  set ζ : Fin P.parts.card → α := fun s ↦ (emb s.val).1 with hζ_def
  have hζ_inj : Function.Injective ζ := fun s t h ↦
    Fin.val_injective (emb.injective (Subtype.val_injective h))
  have hζ_mem : ∀ s, ζ s ∈ Grp s0 := fun s ↦ (emb s.val).2
  set D : Finset (Fin P.parts.card) :=
    Finset.univ.filter (fun s ↦ (Finset.univ.filter (fun i ↦ g i = s)).card = 0) with hD_def
  set Remove : Set α := ζ '' ↑D with hRemove_def
  have hRemove_null : μ Remove = 0 := (D.finite_toSet.image ζ).measure_zero μ
  -- the coarsened cells
  set ιQ : Fin P.parts.card → Set α :=
    fun s ↦ (Grp s \ Remove) ∪ (if s ∈ D then ({ζ s} : Set α) else ∅) with hιQ_def
  have hιQ_measure_eq : ∀ s, μ (ιQ s) = μ (Grp s) := by
    intro s
    have hpad : μ (if s ∈ D then ({ζ s} : Set α) else ∅) = 0 := by
      split_ifs with h
      · exact measure_singleton _
      · exact measure_empty
    refine le_antisymm ?_ ?_
    · calc μ (ιQ s) ≤ μ (Grp s \ Remove) + μ (if s ∈ D then ({ζ s} : Set α) else ∅) :=
            measure_union_le _ _
        _ = μ (Grp s) := by rw [measure_sdiff_null hRemove_null, hpad, add_zero]
    · rw [hιQ_def, ← measure_sdiff_null (s := Grp s) hRemove_null]
      exact measure_mono Set.subset_union_left
  have hmeasure_final : ∀ s, (μ (ιQ s)).toReal = empFreq (ιP s) x := by
    intro s
    rw [hιQ_measure_eq s, hGrp_toReal s, hfilter s]; rfl
  -- disjointness of the coarsened cells
  have hιQ_disj : ∀ s t, s ≠ t → Disjoint (ιQ s) (ιQ t) := by
    intro s t hst
    rw [Set.disjoint_left]
    rintro a ha hb
    rw [hιQ_def] at ha hb
    rcases ha with haGs | haPs
    · rcases hb with hbGt | hbPt
      · exact Set.disjoint_left.mp (hGrp_disj s t hst) haGs.1 hbGt.1
      · by_cases htd : t ∈ D
        · rw [if_pos htd, Set.mem_singleton_iff] at hbPt
          exact haGs.2 (by rw [hbPt]; exact Set.mem_image_of_mem ζ (Finset.mem_coe.mpr htd))
        · rw [if_neg htd] at hbPt; exact hbPt
    · by_cases hsd : s ∈ D
      · rw [if_pos hsd, Set.mem_singleton_iff] at haPs
        rcases hb with hbGt | hbPt
        · exact hbGt.2 (by rw [haPs]; exact Set.mem_image_of_mem ζ (Finset.mem_coe.mpr hsd))
        · by_cases htd : t ∈ D
          · rw [if_pos htd, Set.mem_singleton_iff] at hbPt
            exact hst (hζ_inj (haPs.symm.trans hbPt))
          · rw [if_neg htd] at hbPt; exact hbPt
      · rw [if_neg hsd] at haPs; exact haPs
  have hιQ_ne : ∀ s, (ιQ s).Nonempty := by
    intro s
    by_cases hsd : s ∈ D
    · exact ⟨ζ s, Set.mem_union_right _ (by rw [if_pos hsd]; exact Set.mem_singleton _)⟩
    · have hcardpos : 0 < (Finset.univ.filter (fun i ↦ g i = s)).card :=
        Nat.pos_of_ne_zero (fun hc ↦ hsd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩))
      have hpos : μ (ιQ s) ≠ 0 := by
        rw [hιQ_measure_eq s]
        intro h
        have hh := hGrp_toReal s
        rw [h, ENNReal.toReal_zero] at hh
        have hposr : (0 : ℝ) < ((Finset.univ.filter (fun i ↦ g i = s)).card : ℝ) / k :=
          div_pos (by exact_mod_cast hcardpos) hkpos
        linarith
      exact nonempty_of_measure_ne_zero hpos
  have hιQ_inj : Function.Injective ιQ := by
    intro s t hst
    by_contra hne
    have hd := hιQ_disj s t hne
    rw [hst] at hd
    refine (hιQ_ne t).ne_empty ?_
    have := Set.disjoint_iff_inter_eq_empty.mp hd
    rwa [Set.inter_self] at this
  -- each equicell sits (a.e.) inside its group's coarsened cell
  have hsubset : ∀ i : Fin k, μ (equipartitionCell (α := α) (μ := μ) k i \ ιQ (g i)) = 0 := by
    intro i
    refine measure_mono_null ?_ hRemove_null
    intro a ⟨hai, hani⟩
    by_contra haR
    refine hani ?_
    rw [hιQ_def]
    refine Set.mem_union_left _ ⟨?_, haR⟩
    rw [hGrp_def]
    exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩) hai
  -- assemble the partition
  have hpairwise : (↑(Finset.image ιQ Finset.univ) : Set (Set α)).PairwiseDisjoint id := by
    intro S hS T hT hST
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ, true_and] at hS hT
    obtain ⟨s, rfl⟩ := hS; obtain ⟨t, rfl⟩ := hT
    exact hιQ_disj s t (fun h ↦ hST (congrArg ιQ h))
  have hcover_cells : ∀ᵐ y ∂μ, ∃ i, y ∈ equipartitionCell (α := α) (μ := μ) k i := by
    filter_upwards [(equipartition k).ae_covers] with y ⟨S, hS, hyS⟩
    obtain ⟨i, rfl⟩ := equipartitionCell_surjOn k S hS
    exact ⟨i, hyS⟩
  have hnotRemove : ∀ᵐ y ∂μ, y ∉ Remove := by
    rw [ae_iff]; simp only [not_not, Set.setOf_mem_eq]; exact hRemove_null
  have hae_covers : ∀ᵐ y ∂μ, ∃ S ∈ Finset.image ιQ Finset.univ, y ∈ S := by
    filter_upwards [hcover_cells, hnotRemove] with y ⟨i, hyi⟩ hyR
    refine ⟨ιQ (g i), Finset.mem_image.mpr ⟨g i, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [hιQ_def]
    refine Set.mem_union_left _ ⟨?_, hyR⟩
    rw [hGrp_def]
    exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩) hyi
  refine ⟨⟨Finset.image ιQ Finset.univ, ?_, hpairwise, hae_covers⟩, ιQ,
    fun i ↦ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hιQ_inj,
    ?_, hmeasure_final, hsubset⟩
  · intro S hS
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hS
    rw [hιQ_def]
    exact ((hGrp_meas s).diff (D.finite_toSet.image ζ).measurableSet).union
      (by split_ifs <;> [exact measurableSet_singleton _; exact MeasurableSet.empty])
  · intro S hS
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hS
    exact ⟨s, rfl⟩

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
  classical
  set P := chosenPartition W ε' with hP
  set m := P.parts.card with hm_def
  -- enumeration of `P.parts`
  set ιP : Fin m → Set α := fun s ↦ ((P.parts.equivFin).symm s : Set α) with hιP_def
  have hιP_mem : ∀ s, ιP s ∈ P.parts := fun s ↦ Finset.coe_mem _
  have hιP_inj : Function.Injective ιP := fun s t h ↦
    (P.parts.equivFin.symm).injective (Subtype.ext h)
  have hιP_surj : ∀ S ∈ P.parts, ∃ s, ιP s = S := by
    intro S hS; exact ⟨P.parts.equivFin ⟨S, hS⟩, by simp [hιP_def]⟩
  -- a.e. coefficient alignment over all off-diagonal pairs
  have halign_ae : ∀ᵐ x ∂Measure.pi (fun _ : Fin k ↦ μ), ∀ i j : Fin k, i ≠ j →
      ∀ S ∈ P.parts, ∀ T ∈ P.parts, x (min i j) ∈ S → x (max i j) ∈ T →
        clampEval (chosenStep W ε') x i j = rectAverage W S T := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun x h ↦ absurd hij h)
    · filter_upwards [ae_clampEval_chosenStep_eq W ε' hij] with x hx; intro _; exact hx
  filter_upwards [ae_forall_sample_mem_part P, halign_ae] with x hcov halign
  -- the slot map `g`: which `P`-cell each sample lands in
  have hcov' : ∀ i, ∃ s, x i ∈ ιP s := by
    intro i; obtain ⟨S, hS, hxS⟩ := hcov i; obtain ⟨s, hs⟩ := hιP_surj S hS
    exact ⟨s, hs ▸ hxS⟩
  set g : Fin k → Fin m := fun i ↦ (hcov' i).choose with hg_def
  have hg : ∀ i, x i ∈ ιP (g i) := fun i ↦ (hcov' i).choose_spec
  -- coarsened partition
  obtain ⟨Q, ιQ, hιQ_mem, hιQ_inj, hιQ_surj, hιQ_measure, hιQ_subset⟩ :=
    exists_coarsened_partition P ιP hιP_mem hιP_inj x g hg
  -- coefficient matrices
  set MQ : Fin m → Fin m → ℝ := fun i j ↦ rectAverage W (ιP i) (ιP j) with hMQ_def
  set Mmid : Fin k → Fin k → ℝ := fun i j ↦ rectAverage W (ιP (g i)) (ιP (g j)) with hMmid_def
  set Msample : Fin k → Fin k → ℝ := fun i j ↦ clampEval (chosenStep W ε') x i j with hMsample_def
  have hMQ_symm : ∀ i j, MQ i j = MQ j i := fun i j ↦
    rectAverage_symm W _ _ (P.measurableSet_part (hιP_mem i)) (P.measurableSet_part (hιP_mem j))
  have hMQ_mem : ∀ i j, MQ i j ∈ Set.Icc (0 : ℝ) 1 := fun i j ↦
    rectAverage_mem_Icc W _ _ (P.measurableSet_part (hιP_mem i)) (P.measurableSet_part (hιP_mem j))
  have hMmid_symm : ∀ i j, Mmid i j = Mmid j i := fun i j ↦
    rectAverage_symm W _ _ (P.measurableSet_part (hιP_mem (g i)))
      (P.measurableSet_part (hιP_mem (g j)))
  have hMmid_mem : ∀ i j, Mmid i j ∈ Set.Icc (0 : ℝ) 1 := fun i j ↦
    rectAverage_mem_Icc W _ _ (P.measurableSet_part (hιP_mem (g i)))
      (P.measurableSet_part (hιP_mem (g j)))
  have hMsample_symm : ∀ i j, Msample i j = Msample j i := by
    intro i j; simp only [hMsample_def, clampEval, min_comm i j, max_comm i j]
  have hMsample_mem : ∀ i j, Msample i j ∈ Set.Icc (0 : ℝ) 1 := fun i j ↦
    ⟨clampEval_nonneg _ x i j, clampEval_le_one _ x i j⟩
  -- coefficient functions and their symm/mem proofs
  have hcQ_symm : ∀ S ∈ Q.parts, ∀ T ∈ Q.parts,
      coeffOfMatrix ιQ MQ S T = coeffOfMatrix ιQ MQ T S :=
    fun S _ T _ ↦ coeffOfMatrix_symm ιQ MQ hMQ_symm S T
  have hcQ_mem : ∀ S ∈ Q.parts, ∀ T ∈ Q.parts,
      coeffOfMatrix ιQ MQ S T ∈ Set.Icc (0 : ℝ) 1 :=
    fun S _ T _ ↦ coeffOfMatrix_mem ιQ MQ hMQ_mem S T
  have hcMid_symm : ∀ S ∈ (equipartition (α := α) (μ := μ) k).parts,
      ∀ T ∈ (equipartition (α := α) (μ := μ) k).parts,
      coeffOfMatrix (equipartitionCell (α := α) (μ := μ) k) Mmid S T
        = coeffOfMatrix (equipartitionCell (α := α) (μ := μ) k) Mmid T S :=
    fun S _ T _ ↦ coeffOfMatrix_symm _ Mmid hMmid_symm S T
  have hcMid_mem : ∀ S ∈ (equipartition (α := α) (μ := μ) k).parts,
      ∀ T ∈ (equipartition (α := α) (μ := μ) k).parts,
      coeffOfMatrix (equipartitionCell (α := α) (μ := μ) k) Mmid S T ∈ Set.Icc (0 : ℝ) 1 :=
    fun S _ T _ ↦ coeffOfMatrix_mem _ Mmid hMmid_mem S T
  have hcSamp_symm : ∀ S ∈ (equipartition (α := α) (μ := μ) k).parts,
      ∀ T ∈ (equipartition (α := α) (μ := μ) k).parts,
      coeffOfMatrix (equipartitionCell (α := α) (μ := μ) k) Msample S T
        = coeffOfMatrix (equipartitionCell (α := α) (μ := μ) k) Msample T S :=
    fun S _ T _ ↦ coeffOfMatrix_symm _ Msample hMsample_symm S T
  have hcSamp_mem : ∀ S ∈ (equipartition (α := α) (μ := μ) k).parts,
      ∀ T ∈ (equipartition (α := α) (μ := μ) k).parts,
      coeffOfMatrix (equipartitionCell (α := α) (μ := μ) k) Msample S T ∈ Set.Icc (0 : ℝ) 1 :=
    fun S _ T _ ↦ coeffOfMatrix_mem _ Msample hMsample_mem S T
  -- the three comparison graphons
  set Qg := mkStepGraphon Q (coeffOfMatrix ιQ MQ) hcQ_symm hcQ_mem with hQg_def
  set Hmid := mkStepGraphon (equipartition k) (coeffOfMatrix (equipartitionCell k) Mmid)
    hcMid_symm hcMid_mem with hHmid_def
  have hsample_eq : sampleWeightedGraphonOn (chosenStep W ε') x
      = mkStepGraphon (equipartition k) (coeffOfMatrix (equipartitionCell k) Msample)
        hcSamp_symm hcSamp_mem := rfl
  -- (c2) weight bound
  have hc2 : cutDistance (chosenStep W ε') Qg
      ≤ 2 * ∑ s : Fin m, |(μ (ιP s)).toReal - empFreq (ιP s) x| := by
    rw [hQg_def, chosenStep_eq_mkStepGraphon]
    have hkey := cutDistance_step_weight_le P Q (rectAverage W) (coeffOfMatrix ιQ MQ)
      (fun S hS T hT ↦ rectAverage_symm W S T (P.measurableSet_part hS) (P.measurableSet_part hT))
      (fun S hS T hT ↦ rectAverage_mem_Icc W S T (P.measurableSet_part hS)
        (P.measurableSet_part hT))
      hcQ_symm hcQ_mem ιP ιQ hιP_mem hιQ_mem hιP_inj hιQ_inj hιP_surj hιQ_surj
      (fun i j ↦ (coeffOfMatrix_eq ιQ MQ hιQ_inj i j).symm)
    refine hkey.trans (le_of_eq ?_)
    simp only [hιQ_measure]
  -- (c3) coarsened vs. equipartition-refined: identical a.e., zero cut distance
  have hc3 : cutDistance Qg Hmid ≤ 0 := by
    refine (cutDistance_le_cutNormDiff _ _).trans (le_of_eq ?_)
    rw [hQg_def, hHmid_def]
    apply cutNormDiff_eq_zero_of_ae_eq
    have hcoeQ : ∀ᵐ p ∂(μ.prod μ),
        (mkStepGraphon Q (coeffOfMatrix ιQ MQ) hcQ_symm hcQ_mem).toAEEqFun p
          = mkStepFun Q (coeffOfMatrix ιQ MQ) p :=
      AEEqFun.coeFn_mk _ (mkStepFun_measurable Q (coeffOfMatrix ιQ MQ)).aestronglyMeasurable
    have hcoeM : ∀ᵐ p ∂(μ.prod μ),
        (mkStepGraphon (equipartition k) (coeffOfMatrix (equipartitionCell k) Mmid)
            hcMid_symm hcMid_mem).toAEEqFun p
          = mkStepFun (equipartition k) (coeffOfMatrix (equipartitionCell k) Mmid) p :=
      AEEqFun.coeFn_mk _ (mkStepFun_measurable _ _).aestronglyMeasurable
    have hBad : μ (⋃ i, equipartitionCell (α := α) (μ := μ) k i \ ιQ (g i)) = 0 :=
      measure_iUnion_null_iff.mpr hιQ_subset
    have hcover_cells : ∀ᵐ y ∂μ, ∃ i, y ∈ equipartitionCell (α := α) (μ := μ) k i := by
      filter_upwards [(equipartition k).ae_covers] with y ⟨S, hS, hyS⟩
      obtain ⟨i, rfl⟩ := equipartitionCell_surjOn k S hS
      exact ⟨i, hyS⟩
    have hnotbad : ∀ᵐ y ∂μ, y ∉ ⋃ i, equipartitionCell (α := α) (μ := μ) k i \ ιQ (g i) := by
      rw [ae_iff]; simp only [not_not, Set.setOf_mem_eq]; exact hBad
    have hf1 : ∀ᵐ p ∂(μ.prod μ), ∃ i, p.1 ∈ equipartitionCell (α := α) (μ := μ) k i :=
      Measure.quasiMeasurePreserving_fst.ae hcover_cells
    have hf2 : ∀ᵐ p ∂(μ.prod μ), ∃ j, p.2 ∈ equipartitionCell (α := α) (μ := μ) k j :=
      Measure.quasiMeasurePreserving_snd.ae hcover_cells
    have hb1 : ∀ᵐ p ∂(μ.prod μ), p.1 ∉ ⋃ i, equipartitionCell (α := α) (μ := μ) k i \ ιQ (g i) :=
      Measure.quasiMeasurePreserving_fst.ae hnotbad
    have hb2 : ∀ᵐ p ∂(μ.prod μ), p.2 ∉ ⋃ i, equipartitionCell (α := α) (μ := μ) k i \ ιQ (g i) :=
      Measure.quasiMeasurePreserving_snd.ae hnotbad
    filter_upwards [hcoeQ, hcoeM, hf1, hf2, hb1, hb2] with p hpQ hpM ⟨i, hpi⟩ ⟨j, hpj⟩ hbp1 hbp2
    have ha : p.1 ∈ ιQ (g i) := by
      by_contra hc; exact hbp1 (Set.mem_iUnion.mpr ⟨i, hpi, hc⟩)
    have hb : p.2 ∈ ιQ (g j) := by
      by_contra hc; exact hbp2 (Set.mem_iUnion.mpr ⟨j, hpj, hc⟩)
    rw [hpQ, hpM,
      mkStepFun_eq_at Q (coeffOfMatrix ιQ MQ) (hιQ_mem (g i)) (hιQ_mem (g j))
        (Set.mk_mem_prod ha hb),
      mkStepFun_eq_at (equipartition k) (coeffOfMatrix (equipartitionCell k) Mmid)
        (equipartitionCell_mem k i) (equipartitionCell_mem k j) (Set.mk_mem_prod hpi hpj),
      coeffOfMatrix_eq ιQ MQ hιQ_inj (g i) (g j),
      coeffOfMatrix_eq (equipartitionCell k) Mmid (equipartitionCell_injective k) i j]
  -- (c4) diagonal bound
  have halign2 : ∀ i j : Fin k, i ≠ j →
      clampEval (chosenStep W ε') x i j = rectAverage W (ιP (g i)) (ιP (g j)) := by
    intro i j hij
    have h := halign i j hij (ιP (g (min i j))) (hιP_mem _) (ιP (g (max i j))) (hιP_mem _)
      (hg (min i j)) (hg (max i j))
    rw [h]
    rcases le_total i j with hle | hle
    · rw [min_eq_left hle, max_eq_right hle]
    · rw [min_eq_right hle, max_eq_left hle]
      exact rectAverage_symm W _ _ (P.measurableSet_part (hιP_mem _))
        (P.measurableSet_part (hιP_mem _))
  have hoff : ∀ i j : Fin k, i ≠ j → Msample i j = Mmid i j := fun i j hij ↦
    halign2 i j hij
  have hc4 : cutDistance Hmid (sampleWeightedGraphonOn (chosenStep W ε') x) ≤ (k : ℝ)⁻¹ := by
    rw [hHmid_def, hsample_eq]
    refine (cutDistance_le_cutNormDiff _ _).trans ?_
    apply cutNormDiff_mkStepGraphon_le_of_cuts (equipartition k)
      (equipartitionCell (α := α) (μ := μ) k) (equipartitionCell_mem k)
      (equipartitionCell_injective k) (equipartitionCell_surjOn k)
      (coeffOfMatrix (equipartitionCell k) Mmid) (coeffOfMatrix (equipartitionCell k) Msample)
      hcMid_symm hcMid_mem hcSamp_symm hcSamp_mem (k : ℝ)⁻¹
    intro A B
    calc |∑ i ∈ A, ∑ j ∈ B,
            ((μ (equipartitionCell (α := α) (μ := μ) k i)).toReal *
              (μ (equipartitionCell (α := α) (μ := μ) k j)).toReal) *
            (coeffOfMatrix (equipartitionCell k) Mmid (equipartitionCell k i)
                (equipartitionCell k j) -
              coeffOfMatrix (equipartitionCell k) Msample (equipartitionCell k i)
                (equipartitionCell k j))|
        ≤ ∑ i ∈ A, ∑ j ∈ B, (if i = j then (k : ℝ)⁻¹ * (k : ℝ)⁻¹ else 0) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
          rw [equipartitionCell_measure, equipartitionCell_measure,
            coeffOfMatrix_eq (equipartitionCell k) Mmid (equipartitionCell_injective k) i j,
            coeffOfMatrix_eq (equipartitionCell k) Msample (equipartitionCell_injective k) i j]
          by_cases hij : i = j
          · rw [if_pos hij, abs_mul,
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹ * (k : ℝ)⁻¹)]
            have h1 : |Mmid i j - Msample i j| ≤ 1 := by
              rw [abs_le]
              obtain ⟨a0, a1⟩ := hMmid_mem i j; obtain ⟨b0, b1⟩ := hMsample_mem i j
              constructor <;> linarith
            calc (k : ℝ)⁻¹ * (k : ℝ)⁻¹ * |Mmid i j - Msample i j|
                ≤ (k : ℝ)⁻¹ * (k : ℝ)⁻¹ * 1 := by gcongr
              _ = (k : ℝ)⁻¹ * (k : ℝ)⁻¹ := mul_one _
          · rw [if_neg hij, hoff i j hij, sub_self, mul_zero, abs_zero]
      _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin k)), ∑ j ∈ (Finset.univ : Finset (Fin k)),
            (if i = j then (k : ℝ)⁻¹ * (k : ℝ)⁻¹ else 0) := by
          refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
            (fun i _ _ ↦ Finset.sum_nonneg fun j _ ↦ by split_ifs <;> positivity)).trans ?_
          refine Finset.sum_le_sum fun i _ ↦
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
              (fun j _ _ ↦ by split_ifs <;> positivity)
      _ = (k : ℝ)⁻¹ := by
          have hsingle : ∀ i : Fin k,
              (∑ j ∈ (Finset.univ : Finset (Fin k)), if i = j then (k : ℝ)⁻¹ * (k : ℝ)⁻¹ else 0)
                = (k : ℝ)⁻¹ * (k : ℝ)⁻¹ := by
            intro i; rw [Finset.sum_ite_eq univ i (fun _ ↦ (k : ℝ)⁻¹ * (k : ℝ)⁻¹)]
            simp
          rw [Finset.sum_congr rfl (fun i _ ↦ hsingle i), Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          have hk : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
          field_simp
  -- assemble
  have htri1 := cutDistance_triangle (chosenStep W ε') Qg
    (sampleWeightedGraphonOn (chosenStep W ε') x)
  have htri2 := cutDistance_triangle Qg Hmid (sampleWeightedGraphonOn (chosenStep W ε') x)
  have hreindex : ∑ s : Fin m, |(μ (ιP s)).toReal - empFreq (ιP s) x|
      = ∑ S ∈ P.parts, |empFreq S x - (μ S).toReal| :=
    Finset.sum_bij (fun s _ ↦ ιP s) (fun s _ ↦ hιP_mem s) (fun s _ t _ h ↦ hιP_inj h)
      (fun S hS ↦ by obtain ⟨s, hs⟩ := hιP_surj S hS; exact ⟨s, Finset.mem_univ s, hs⟩)
      (fun s _ ↦ abs_sub_comm _ _)
  have hfreq : freqTerm W ε' k x = 2 * ∑ S ∈ P.parts, |empFreq S x - (μ S).toReal| + (k : ℝ)⁻¹ := by
    rw [freqTerm, ← hP]
  rw [hfreq, ← hreindex]
  linarith [htri1, htri2, hc2, hc3, hc4]

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

omit [IsProbabilityMeasure μ] [NullSingletonClass μ] in
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

/-- **Cauchy–Schwarz on a probability space**: `(∫|g|)² ≤ ∫ g²`. Proved from
`0 ≤ Var[|g|] = 𝔼[|g|²] − 𝔼[|g|]²`. -/
private theorem sq_integral_abs_le {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] {g : Ω → ℝ} (hmem : MemLp g 2 ν) :
    (∫ ω, |g ω| ∂ν) ^ 2 ≤ ∫ ω, g ω ^ 2 ∂ν := by
  have habs : MemLp (fun ω ↦ |g ω|) 2 ν := hmem.abs
  have hv := ProbabilityTheory.variance_nonneg (fun ω ↦ |g ω|) ν
  rw [ProbabilityTheory.variance_eq_sub habs] at hv
  have e1 : ν[(fun ω ↦ |g ω|) ^ 2] = ∫ ω, g ω ^ 2 ∂ν := by
    simp [Pi.pow_apply, sq_abs]
  have e2 : ν[fun ω ↦ |g ω|] = ∫ ω, |g ω| ∂ν := rfl
  rw [e1, e2] at hv
  linarith

omit [StandardBorelSpace α] [NullSingletonClass μ] in
/-- **Per-cell frequency bound** (iid variance + Cauchy–Schwarz): the mean absolute deviation
of the empirical cell frequency from the true measure is `O(1/√k)`, uniformly over cells. The
variance identity `E(empFreq − μS)² = μS(1−μS)/k ≤ 1/(4k)` (cross terms vanish by coordinate
independence) plus `E|Y| ≤ √(E Y²)` on a probability space gives the `1/(2√k)` bound.
Elementary; part of the `first_sampling_lemma` accounting, NOT a new live input. -/
private theorem integral_abs_empFreq_sub_le {k : ℕ} [NeZero k] {S : Set α}
    (hS : MeasurableSet S) :
    ∫ x, |empFreq S x - (μ S).toReal| ∂Measure.pi (fun _ : Fin k ↦ μ)
      ≤ 1 / (2 * Real.sqrt k) := by
  classical
  set π : Measure (Fin k → α) := Measure.pi (fun _ : Fin k ↦ μ) with hπ
  set p : ℝ := (μ S).toReal with hp
  set χ : α → ℝ := S.indicator (fun _ ↦ (1 : ℝ)) with hχ
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  -- basic facts about χ
  have hχ_meas : Measurable χ := measurable_const.indicator hS
  have hχ_Icc : ∀ y, χ y ∈ Set.Icc (0 : ℝ) 1 := by
    intro y; rw [hχ]; by_cases h : y ∈ S <;> simp [h]
  have hχ_memLp : MemLp χ 2 μ :=
    memLp_of_bounded (ae_of_all _ hχ_Icc) hχ_meas.aestronglyMeasurable 2
  have hχ_int : ∫ y, χ y ∂μ = p := by
    rw [hχ, integral_indicator_const _ hS, smul_eq_mul, mul_one]; rfl
  -- empFreq as a scaled sum of coordinate indicators
  have hfreq : ∀ x : Fin k → α, empFreq S x = (k : ℝ)⁻¹ * ∑ i, χ (x i) := by
    intro x
    unfold empFreq
    rw [Finset.card_filter, Nat.cast_sum, div_eq_inv_mul]
    congr 1
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    by_cases h : x i ∈ S <;> simp [hχ, h]
  have hfreq_fun : (fun x : Fin k → α ↦ empFreq S x)
      = fun x ↦ (k : ℝ)⁻¹ * ∑ i, χ (x i) := funext hfreq
  -- coordinate integrability and single-coordinate mean transfer
  have hcoord_int : ∀ i : Fin k, Integrable (fun x : Fin k → α ↦ χ (x i)) π :=
    fun i ↦ (hχ_memLp.comp_measurePreserving
      (MeasureTheory.measurePreserving_eval (fun _ : Fin k ↦ μ) i)).integrable one_le_two
  have hcoord : ∀ i : Fin k, ∫ x, χ (x i) ∂π = p := by
    intro i
    have hmp := MeasureTheory.measurePreserving_eval (fun _ : Fin k ↦ μ) i
    have hmap : Measure.map (fun x : Fin k → α ↦ x i) π = μ := by rw [hπ]; exact hmp.map_eq
    have hfm : AEStronglyMeasurable χ (Measure.map (fun x : Fin k → α ↦ x i) π) := by
      rw [hmap]; exact hχ_meas.aestronglyMeasurable
    calc ∫ x, χ (x i) ∂π
        = ∫ y, χ y ∂(Measure.map (fun x : Fin k → α ↦ x i) π) :=
          (integral_map (measurable_pi_apply i).aemeasurable hfm).symm
      _ = ∫ y, χ y ∂μ := by rw [hmap]
      _ = p := hχ_int
  -- E[empFreq] = p
  have hmean : ∫ x, empFreq S x ∂π = p := by
    simp_rw [hfreq]
    rw [integral_const_mul, integral_finsetSum _ (fun i _ ↦ hcoord_int i)]
    simp_rw [hcoord]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- variance of the empirical frequency
  set Y : (Fin k → α) → ℝ := fun x ↦ ∑ i, χ (x i) with hY
  have hYsum : Y = ∑ i : Fin k, fun x : Fin k → α ↦ χ (x i) := by
    funext x; rw [hY, Finset.sum_apply]
  have hvarY : Var[Y; π] = (k : ℝ) * Var[χ; μ] := by
    rw [hYsum, ProbabilityTheory.variance_sum_pi (fun _ ↦ hχ_memLp),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hvarχ : Var[χ; μ] ≤ 1 / 4 := by
    have h := ProbabilityTheory.variance_le_sq_of_bounded (a := 0) (b := 1)
      (ae_of_all μ hχ_Icc) hχ_meas.aemeasurable
    norm_num at h ⊢
    linarith
  have hvarnn : 0 ≤ Var[χ; μ] := ProbabilityTheory.variance_nonneg _ _
  have hvarfreq : Var[fun x ↦ empFreq S x; π] ≤ 1 / (4 * (k : ℝ)) := by
    rw [hfreq_fun, show (fun x : Fin k → α ↦ (k : ℝ)⁻¹ * ∑ i, χ (x i))
        = fun x ↦ (k : ℝ)⁻¹ * Y x from rfl,
      ProbabilityTheory.variance_const_mul, hvarY]
    calc ((k : ℝ)⁻¹) ^ 2 * ((k : ℝ) * Var[χ; μ])
        ≤ ((k : ℝ)⁻¹) ^ 2 * ((k : ℝ) * (1 / 4)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hvarχ (le_of_lt hkpos)
      _ = 1 / (4 * (k : ℝ)) := by field_simp
  -- ∫ (empFreq − p)² = Var[empFreq]
  have hae : AEMeasurable (fun x ↦ empFreq S x) π := (measurable_empFreq hS).aemeasurable
  have hvar_int : ∫ x, (empFreq S x - p) ^ 2 ∂π = Var[fun x ↦ empFreq S x; π] := by
    rw [ProbabilityTheory.variance_eq_integral hae, hmean]
  -- Cauchy–Schwarz through the L² memLp of the centered frequency
  have hg_Icc : ∀ x : Fin k → α, empFreq S x - p ∈ Set.Icc (-1 : ℝ) 1 := by
    intro x
    have h0 := empFreq_nonneg S x
    have h1 := empFreq_le_one S x
    have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
    have hp1 : p ≤ 1 := by
      rw [hp, ← ENNReal.toReal_one]
      exact ENNReal.toReal_mono (by simp)
        (by rw [← measure_univ (μ := μ)]; exact measure_mono (Set.subset_univ _))
    exact ⟨by linarith, by linarith⟩
  have hg_memLp : MemLp (fun x ↦ empFreq S x - p) 2 π :=
    memLp_of_bounded (ae_of_all _ hg_Icc)
      ((measurable_empFreq hS).sub_const _).aestronglyMeasurable 2
  have hCS := sq_integral_abs_le hg_memLp
  -- conclude
  set c : ℝ := ∫ x, |empFreq S x - p| ∂π with hc
  have hc_nn : 0 ≤ c := integral_nonneg (fun x ↦ abs_nonneg _)
  have hc_sq : c ^ 2 ≤ 1 / (4 * (k : ℝ)) := by
    refine le_trans hCS ?_
    rw [hvar_int]
    exact hvarfreq
  have hsqrt4k : Real.sqrt (1 / (4 * (k : ℝ))) = 1 / (2 * Real.sqrt k) := by
    rw [one_div, one_div, Real.sqrt_inv]
    congr 1
    rw [show (4 * (k : ℝ)) = 2 ^ 2 * k by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  calc c = Real.sqrt (c ^ 2) := (Real.sqrt_sq hc_nn).symm
    _ ≤ Real.sqrt (1 / (4 * (k : ℝ))) := Real.sqrt_le_sqrt hc_sq
    _ = 1 / (2 * Real.sqrt k) := hsqrt4k

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

/-- **Frieze–Kannan control of the chosen step approximation.** By construction
`chosenStep W ε' = stepify P W` for the regularity partition `P` at quality `ε'`, so the
cut-norm difference `‖W − U‖_□` is at most `ε'`. This is the *systematic-error budget* of
the core term: the a.e. entries of the empirical difference matrix are the sampled values of
`W − U`, whose continuous cut norm the AFKK core compares against. -/
theorem chosenStep_cutNormDiff_le (W : Graphon α μ) {ε' : ℝ} (hε' : 0 < ε') :
    cutNormDiff W (chosenStep W ε') ≤ ε' := by
  unfold chosenStep chosenPartition
  rw [dif_pos hε']
  exact (regularity W ε' hε').choose_spec.2

/-- The sampled difference-matrix entry `D(x)ᵢⱼ = clampEval W x i j − clampEval U x i j`,
where `U = chosenStep W ε'`. Both clamps lie in `[0,1]`, so `D ∈ [-1,1]`. Introduced only to
compress the AFKK core proof; a private abbreviation for the summand of `coreTerm`. -/
private noncomputable def coreDiff (W : Graphon α μ) (ε' : ℝ) {k : ℕ} (x : Fin k → α)
    (i j : Fin k) : ℝ :=
  clampEval W x i j - clampEval (chosenStep W ε') x i j

omit [StandardBorelSpace α] [NullSingletonClass μ] in
/-- Each sampled difference entry has absolute value at most `1`. -/
private theorem abs_coreDiff_le_one (W : Graphon α μ) (ε' : ℝ) {k : ℕ} (x : Fin k → α)
    (i j : Fin k) : |coreDiff W ε' x i j| ≤ 1 := by
  rw [coreDiff, abs_le]
  have h1 := clampEval_le_one W x i j
  have h2 := clampEval_nonneg W x i j
  have h3 := clampEval_le_one (chosenStep W ε') x i j
  have h4 := clampEval_nonneg (chosenStep W ε') x i j
  constructor <;> linarith

/-- **Step 0 — normal form of the core term.** Each equipartition cell has measure `1/k`
(`equipartitionCell_measure`), so the `(μ cell)·(μ cell)` weights are the constant `1/k²`,
which factors out of the `sup'` of `|·|`:
`coreTerm W ε' k x = k⁻² · sup'_{A,B ⊆ [k]} |∑_{i∈A} ∑_{j∈B} D(x)ᵢⱼ|`. -/
private theorem coreTerm_eq_normalForm (W : Graphon α μ) (ε' : ℝ) {k : ℕ} [NeZero k]
    (x : Fin k → α) :
    coreTerm W ε' k x = (k : ℝ)⁻¹ ^ 2 *
      (Finset.univ : Finset (Finset (Fin k) × Finset (Fin k))).sup' Finset.univ_nonempty
        (fun AB ↦ |∑ i ∈ AB.1, ∑ j ∈ AB.2, coreDiff W ε' x i j|) := by
  rw [Finset.mul₀_sup' (by positivity) _ _ Finset.univ_nonempty]
  unfold coreTerm
  refine Finset.sup'_congr _ rfl (fun AB _ ↦ ?_)
  have hμ : ∀ i : Fin k, (μ (equipartitionCell (α := α) (μ := μ) k i)).toReal = (k : ℝ)⁻¹ :=
    equipartitionCell_measure k
  simp only [hμ, coreDiff]
  rw [← abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ)⁻¹ ^ 2 by positivity), ← abs_mul]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  ring

omit [StandardBorelSpace α] [NullSingletonClass μ] in
/-- Rectangle bound for the difference matrix: `|∑_{i∈S} ∑_{j∈T} D| ≤ |S|·|T|`, since each
entry has `|D| ≤ 1`. Shared by the block-split reduction and the integrability of the
fresh-block sup. -/
private theorem abs_coreDiff_rect_le (W : Graphon α μ) (ε' : ℝ) {k : ℕ} (x : Fin k → α)
    (S T : Finset (Fin k)) :
    |∑ i ∈ S, ∑ j ∈ T, coreDiff W ε' x i j| ≤ (S.card : ℝ) * (T.card : ℝ) := by
  calc |∑ i ∈ S, ∑ j ∈ T, coreDiff W ε' x i j|
      ≤ ∑ i ∈ S, |∑ j ∈ T, coreDiff W ε' x i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ S, ∑ _j ∈ T, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun i _ ↦ ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ ↦ ?_))
        exact abs_coreDiff_le_one W ε' x i j
    _ = (S.card : ℝ) * (T.card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- **Sub-lemma 1 — restriction to the fresh block** (pure finite combinatorics, no
probability, no cut norm). For any block `Q ⊆ [k]` with fresh complement `F = Qᶜ`, the
entries of the double cut sum that touch `Q` number at most `2·|Q|·k` and each has `|D| ≤ 1`,
so replacing every cut `(A,B)` by its fresh restriction `(A\Q, B\Q)` costs at most `2|Q|k`
inside the `sup'`. After the `1/k²` normalization this is the block-split error `2|Q|/k`:
`coreTerm ≤ k⁻² · sup'_{A,B} |∑_{i∈A\Q} ∑_{j∈B\Q} D| + 2|Q|/k`. -/
private theorem coreTerm_restrict_fresh_block (W : Graphon α μ) (ε' : ℝ) {k : ℕ} [NeZero k]
    (x : Fin k → α) (Q : Finset (Fin k)) :
    coreTerm W ε' k x ≤ (k : ℝ)⁻¹ ^ 2 *
      (Finset.univ : Finset (Finset (Fin k) × Finset (Fin k))).sup' Finset.univ_nonempty
        (fun AB ↦ |∑ i ∈ AB.1 \ Q, ∑ j ∈ AB.2 \ Q, coreDiff W ε' x i j|)
      + 2 * (Q.card : ℝ) / k := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hcard : ∀ S : Finset (Fin k), (S.card : ℝ) ≤ k := by
    intro S
    calc (S.card : ℝ) ≤ ((Finset.univ : Finset (Fin k)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.subset_univ S)
      _ = k := by rw [Finset.card_univ, Fintype.card_fin]
  have hrect : ∀ S T : Finset (Fin k),
      |∑ i ∈ S, ∑ j ∈ T, coreDiff W ε' x i j| ≤ (S.card : ℝ) * (T.card : ℝ) :=
    abs_coreDiff_rect_le W ε' x
  set fresh : Finset (Fin k) × Finset (Fin k) → ℝ :=
    fun AB ↦ |∑ i ∈ AB.1 \ Q, ∑ j ∈ AB.2 \ Q, coreDiff W ε' x i j| with hfresh
  -- pointwise: every cut's value is at most the fresh sup plus `2|Q|k`
  have hpt : ∀ AB : Finset (Fin k) × Finset (Fin k),
      |∑ i ∈ AB.1, ∑ j ∈ AB.2, coreDiff W ε' x i j|
        ≤ Finset.univ.sup' Finset.univ_nonempty fresh + 2 * (Q.card : ℝ) * (k : ℝ) := by
    intro AB
    obtain ⟨A, B⟩ := AB
    have hinner : ∀ i, ∑ j ∈ B, coreDiff W ε' x i j
        = ∑ j ∈ B ∩ Q, coreDiff W ε' x i j + ∑ j ∈ B \ Q, coreDiff W ε' x i j :=
      fun i ↦ (Finset.sum_inter_add_sum_sdiff B Q _).symm
    have hdecomp : ∑ i ∈ A, ∑ j ∈ B, coreDiff W ε' x i j
        = (∑ i ∈ A ∩ Q, ∑ j ∈ B, coreDiff W ε' x i j
            + ∑ i ∈ A \ Q, ∑ j ∈ B ∩ Q, coreDiff W ε' x i j)
          + ∑ i ∈ A \ Q, ∑ j ∈ B \ Q, coreDiff W ε' x i j := by
      rw [← Finset.sum_inter_add_sum_sdiff A Q (fun i ↦ ∑ j ∈ B, coreDiff W ε' x i j), add_assoc]
      congr 1
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ ↦ hinner i)
    have hbound : |∑ i ∈ A ∩ Q, ∑ j ∈ B, coreDiff W ε' x i j
          + ∑ i ∈ A \ Q, ∑ j ∈ B ∩ Q, coreDiff W ε' x i j| ≤ 2 * (Q.card : ℝ) * k := by
      refine (abs_add_le _ _).trans ?_
      have h1 := hrect (A ∩ Q) B
      have h2 := hrect (A \ Q) (B ∩ Q)
      have c1 : ((A ∩ Q).card : ℝ) ≤ Q.card := by
        exact_mod_cast Finset.card_le_card Finset.inter_subset_right
      have c4 : ((B ∩ Q).card : ℝ) ≤ Q.card := by
        exact_mod_cast Finset.card_le_card Finset.inter_subset_right
      have hp1 : ((A ∩ Q).card : ℝ) * (B.card : ℝ) ≤ (Q.card : ℝ) * k :=
        mul_le_mul c1 (hcard B) (by positivity) (by positivity)
      have hp2 : ((A \ Q).card : ℝ) * ((B ∩ Q).card : ℝ) ≤ (k : ℝ) * (Q.card : ℝ) :=
        mul_le_mul (hcard _) c4 (by positivity) (by positivity)
      nlinarith [h1, h2, hp1, hp2]
    calc |∑ i ∈ A, ∑ j ∈ B, coreDiff W ε' x i j|
        = |(∑ i ∈ A ∩ Q, ∑ j ∈ B, coreDiff W ε' x i j
            + ∑ i ∈ A \ Q, ∑ j ∈ B ∩ Q, coreDiff W ε' x i j)
          + ∑ i ∈ A \ Q, ∑ j ∈ B \ Q, coreDiff W ε' x i j| := by rw [hdecomp]
      _ ≤ |∑ i ∈ A ∩ Q, ∑ j ∈ B, coreDiff W ε' x i j
            + ∑ i ∈ A \ Q, ∑ j ∈ B ∩ Q, coreDiff W ε' x i j|
          + |∑ i ∈ A \ Q, ∑ j ∈ B \ Q, coreDiff W ε' x i j| := abs_add_le _ _
      _ ≤ 2 * (Q.card : ℝ) * k + Finset.univ.sup' Finset.univ_nonempty fresh := by
          gcongr
          exact Finset.le_sup' fresh (Finset.mem_univ (A, B))
      _ = Finset.univ.sup' Finset.univ_nonempty fresh + 2 * (Q.card : ℝ) * k := by ring
  rw [coreTerm_eq_normalForm]
  have hsup : Finset.univ.sup' Finset.univ_nonempty
        (fun AB : Finset (Fin k) × Finset (Fin k) ↦
          |∑ i ∈ AB.1, ∑ j ∈ AB.2, coreDiff W ε' x i j|)
      ≤ Finset.univ.sup' Finset.univ_nonempty fresh + 2 * (Q.card : ℝ) * k :=
    Finset.sup'_le _ _ (fun AB _ ↦ hpt AB)
  calc (k : ℝ)⁻¹ ^ 2 * Finset.univ.sup' Finset.univ_nonempty
          (fun AB : Finset (Fin k) × Finset (Fin k) ↦
            |∑ i ∈ AB.1, ∑ j ∈ AB.2, coreDiff W ε' x i j|)
      ≤ (k : ℝ)⁻¹ ^ 2 * (Finset.univ.sup' Finset.univ_nonempty fresh
          + 2 * (Q.card : ℝ) * k) := by
        exact mul_le_mul_of_nonneg_left hsup (by positivity)
    _ = (k : ℝ)⁻¹ ^ 2 * Finset.univ.sup' Finset.univ_nonempty fresh
          + 2 * (Q.card : ℝ) / k := by
        rw [mul_add]; congr 1; field_simp

/-- **A.e. clamp transparency.** Since a graphon takes values in `[0,1]` a.e., the clamp
`min 1 (max 0 ·)` is invisible: at a.e. sampled off-diagonal pair `(x_i, x_j)` the clamped
evaluation equals the raw kernel value. Companion to `ae_clampEval_chosenStep_eq` for the
raw-kernel side, used to identify the fresh-block rectangle sums as rectangle integrals of
`W − U`. -/
private theorem ae_clampEval_eq (V : Graphon α μ) {k : ℕ} {i j : Fin k} (hij : i ≠ j) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin k ↦ μ),
      clampEval V x i j = V.toAEEqFun (x (min i j), x (max i j)) := by
  have hmm : min i j ≠ max i j := by
    rcases lt_or_gt_of_ne hij with h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact hij
    · rw [min_eq_right h.le, max_eq_left h.le]; exact hij.symm
  filter_upwards [ae_pairMap_of_prod (min i j) (max i j) hmm V.ae_mem_Icc] with x hx
  rw [clampEval, max_eq_right hx.1, min_eq_right hx.2]

/-- At a.e. sampled off-diagonal pair, the empirical difference entry `D` equals the raw
difference kernel `W − U` (`U = chosenStep W ε'`) at the `(min,max)`-ordered sampled pair.
This is the a.e. bridge from the discrete cut sum to the continuous cut norm. -/
private theorem ae_coreDiff_eq (W : Graphon α μ) (ε' : ℝ) {k : ℕ} {i j : Fin k} (hij : i ≠ j) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin k ↦ μ),
      coreDiff W ε' x i j
        = W.toAEEqFun (x (min i j), x (max i j))
          - (chosenStep W ε').toAEEqFun (x (min i j), x (max i j)) := by
  filter_upwards [ae_clampEval_eq W hij, ae_clampEval_eq (chosenStep W ε') hij] with x hW hU
  rw [coreDiff, hW, hU]

/-- The deterministic **subsample (guessing) block** `Q ⊆ [k]` of the AFKK cut-guessing
argument: the first `⌈√k⌉` coordinates. Because coordinates are iid under `Measure.pi`, the
`Q`-block is exactly independent of the fresh complement `F = Qᶜ`, so no hypergeometric second
moment is needed. Its cardinality is `⌈√k⌉` (as `⌈√k⌉ ≤ k`). -/
private noncomputable def guessBlock (k : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun i : Fin k ↦ (i : ℕ) < Nat.ceil (Real.sqrt k))

/-! #### AFKK cut-guessing apparatus (private)

The proof of `guessBlock_integral_le_cutNormDiff` follows `docs/afkk-cut-guessing.md`
(= arXiv:2203.07581 §6.2 + Appendix §10; AFKK, JCSS 67 (2003), Lemma 3; Lovász,
*Large Networks*, Lemma 10.7). Everything here is private. The subsections marked
**(I) hypergeometric moments**, **(II) product-space McDiarmid MGF**, and
**(III) finite soft-max** are self-contained infrastructure, candidates for later
extraction. -/

/-- Sign as a real number: `sgnR true = 1`, `sgnR false = -1`. -/
private def sgnR (s : Bool) : ℝ := if s then 1 else -1

private theorem abs_sgnR (s : Bool) : |sgnR s| = 1 := by
  cases s <;> simp [sgnR]

/-- The **sign set** of the subsample row sums: `{i : 0 < ∑_{j ∈ R} m i j}`. Applied to
`R ⊆ Q` (the guessing block) this is the AFKK "rule" reconstruction of a near-optimal cut
side from the subsample. -/
private noncomputable def signSet {k : ℕ} (m : Fin k → Fin k → ℝ) (R : Finset (Fin k)) :
    Finset (Fin k) :=
  Finset.univ.filter (fun i ↦ 0 < ∑ j ∈ R, m i j)

/-- The value of the **guessed rectangle**: rows from `signSet m R'`, columns from
`signSet m R`. -/
private noncomputable def ruleVal {k : ℕ} (m : Fin k → Fin k → ℝ) (R R' : Finset (Fin k)) :
    ℝ :=
  ∑ i ∈ signSet m R', ∑ j ∈ signSet m R, m i j

/-- The **signed rule index set**: a sign bit (for the two directions of `|·|`) and a pair of
generating subsets `R ⊆ Q`, `R' ⊆ Q'`. Its cardinality is `2 · 2^{|Q|} · 2^{|Q'|}`. -/
private def signedRules {k : ℕ} (Q Q' : Finset (Fin k)) :
    Finset (Bool × Finset (Fin k) × Finset (Fin k)) :=
  (Finset.univ : Finset Bool) ×ˢ (Q.powerset ×ˢ Q'.powerset)

private theorem signedRules_nonempty {k : ℕ} (Q Q' : Finset (Fin k)) :
    (signedRules Q Q').Nonempty :=
  ⟨(true, ∅, ∅), by
    simp only [signedRules, Finset.mem_product, Finset.mem_univ, Finset.mem_powerset,
      Finset.empty_subset, and_self]⟩

private theorem signedRules_card {k : ℕ} (Q Q' : Finset (Fin k)) :
    (signedRules Q Q').card = 2 * 2 ^ Q.card * 2 ^ Q'.card := by
  rw [signedRules, Finset.card_product, Finset.card_product, Finset.card_powerset,
    Finset.card_powerset, Finset.card_univ, Fintype.card_bool]
  ring

/-- (H16) Logarithmic size of the signed rule set, in the inequality form the assembly
consumes: `log |signedRules Q Q'| ≤ (2q+1)·log 2` whenever `|Q|, |Q'| ≤ q`. -/
private theorem log_signedRules_card_le {k q : ℕ} {Q Q' : Finset (Fin k)}
    (hQ : Q.card ≤ q) (hQ' : Q'.card ≤ q) :
    Real.log ((signedRules Q Q').card) ≤ (2 * q + 1) * Real.log 2 := by
  rw [signedRules_card]
  have hpow : ((2 * 2 ^ Q.card * 2 ^ Q'.card : ℕ) : ℝ) = (2 : ℝ) ^ (Q.card + Q'.card + 1) := by
    push_cast; rw [pow_add, pow_add, pow_one]; ring
  rw [hpow, Real.log_pow]
  refine mul_le_mul_of_nonneg_right ?_ (Real.log_nonneg one_le_two)
  have hn : Q.card + Q'.card + 1 ≤ 2 * q + 1 := by omega
  exact_mod_cast hn

/-- (H1) Restricting the cuts of the fresh-block sup to any fixed block only shrinks the full
sup: each pair `(A \ Q, B \ Q)` is itself a cut. This is the ONLY place the deterministic
`guessBlock` interacts with the cut structure. -/
private theorem sup'_sdiff_le_sup' {k : ℕ} [NeZero k] (m : Fin k → Fin k → ℝ)
    (Q : Finset (Fin k)) :
    (Finset.univ : Finset (Finset (Fin k) × Finset (Fin k))).sup' Finset.univ_nonempty
        (fun AB ↦ |∑ i ∈ AB.1 \ Q, ∑ j ∈ AB.2 \ Q, m i j|)
      ≤ (Finset.univ : Finset (Finset (Fin k) × Finset (Fin k))).sup' Finset.univ_nonempty
        (fun AB ↦ |∑ i ∈ AB.1, ∑ j ∈ AB.2, m i j|) := by
  refine Finset.sup'_le _ _ (fun AB _ ↦ ?_)
  exact Finset.le_sup' (fun AB ↦ |∑ i ∈ AB.1, ∑ j ∈ AB.2, m i j|)
    (Finset.mem_univ (AB.1 \ Q, AB.2 \ Q))

omit [StandardBorelSpace α] [NullSingletonClass μ] in
/-- (H2a) The sampled difference matrix is symmetric POINTWISE (not just a.e.), by the
`(min,max)` index normalization inside `clampEval`. -/
private theorem coreDiff_symm (W : Graphon α μ) (ε' : ℝ) {k : ℕ} (x : Fin k → α)
    (i j : Fin k) : coreDiff W ε' x i j = coreDiff W ε' x j i := by
  simp only [coreDiff, clampEval, min_comm i j, max_comm i j]

omit [StandardBorelSpace α] [NullSingletonClass μ] in
/-- (H2b) Locality: `coreDiff W ε' x i j` depends on the sample only through `x i` and
`x j`. -/
private theorem coreDiff_congr (W : Graphon α μ) (ε' : ℝ) {k : ℕ} {x x' : Fin k → α}
    {i j : Fin k} (hi : x i = x' i) (hj : x j = x' j) :
    coreDiff W ε' x i j = coreDiff W ε' x' i j := by
  have hmin : x (min i j) = x' (min i j) := by
    rcases le_total i j with h | h
    · rw [min_eq_left h]; exact hi
    · rw [min_eq_right h]; exact hj
  have hmax : x (max i j) = x' (max i j) := by
    rcases le_total i j with h | h
    · rw [max_eq_right h]; exact hj
    · rw [max_eq_left h]; exact hi
  simp only [coreDiff, clampEval, hmin, hmax]

/-- (H3) Crude bound `|ruleVal m R R'| ≤ k²` for entrywise-bounded matrices; supplies
integrability and the soft-max boundedness side conditions. -/
private theorem abs_ruleVal_le {k : ℕ} (m : Fin k → Fin k → ℝ) (hm : ∀ i j, |m i j| ≤ 1)
    (R R' : Finset (Fin k)) : |ruleVal m R R'| ≤ (k : ℝ) ^ 2 := by
  have hcard : ∀ S : Finset (Fin k), (S.card : ℝ) ≤ k := by
    intro S
    calc (S.card : ℝ) ≤ ((Finset.univ : Finset (Fin k)).card : ℝ) := by
          exact_mod_cast Finset.card_le_univ S
      _ = k := by rw [Finset.card_univ, Fintype.card_fin]
  rw [ruleVal]
  calc |∑ i ∈ signSet m R', ∑ j ∈ signSet m R, m i j|
      ≤ ∑ i ∈ signSet m R', |∑ j ∈ signSet m R, m i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ signSet m R', ∑ _j ∈ signSet m R, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun i _ ↦ ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ ↦ ?_))
        exact hm i j
    _ = ((signSet m R').card : ℝ) * ((signSet m R).card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (k : ℝ) ^ 2 := by
        rw [sq]
        exact mul_le_mul (hcard _) (hcard _) (by positivity) (by positivity)

/-! ##### (H4) `⌈√k⌉₊` arithmetic -/

private theorem guessBlock_card_le (k : ℕ) [NeZero k] :
    (guessBlock k).card ≤ ⌈Real.sqrt k⌉₊ := by
  rw [guessBlock]
  calc (Finset.univ.filter (fun i : Fin k ↦ (i : ℕ) < ⌈Real.sqrt k⌉₊)).card
      ≤ (Finset.range ⌈Real.sqrt k⌉₊).card := by
        refine Finset.card_le_card_of_injOn (fun i ↦ (i : ℕ)) ?_ Fin.val_injective.injOn
        intro i hi
        simp only [Finset.mem_coe, Finset.mem_range]
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hi
    _ = ⌈Real.sqrt k⌉₊ := Finset.card_range _

private theorem sqrt_le_natCeil_sqrt (k : ℕ) : Real.sqrt k ≤ (⌈Real.sqrt k⌉₊ : ℝ) :=
  Nat.le_ceil _

private theorem natCeil_sqrt_le_add_one (k : ℕ) :
    (⌈Real.sqrt k⌉₊ : ℝ) ≤ Real.sqrt k + 1 := by
  exact (Nat.ceil_lt_add_one (Real.sqrt_nonneg k)).le

private theorem one_le_natCeil_sqrt (k : ℕ) [NeZero k] : 1 ≤ ⌈Real.sqrt k⌉₊ := by
  have h : (0 : ℝ) < Real.sqrt k :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k))
  exact Nat.lt_ceil.mpr (by simpa using h)

private theorem natCeil_sqrt_le_self (k : ℕ) [NeZero k] : ⌈Real.sqrt k⌉₊ ≤ k := by
  rw [Nat.ceil_le]
  refine (Real.sqrt_le_left (by positivity)).mpr ?_
  have hk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  nlinarith [hk]

/-! ##### (I) Hypergeometric moments of the subsample estimator

Purely finite averages over `Finset.powersetCard q Finset.univ` — sampling `q` of `k`
fixed real numbers without replacement. Reusable infrastructure. -/

/-- (H5) Enlarging a sum to its positive part over the whole index set. -/
private theorem sum_le_sum_filter_pos {k : ℕ} (c : Fin k → ℝ) (B : Finset (Fin k)) :
    ∑ j ∈ B, c j ≤ ∑ j ∈ Finset.univ.filter (fun j ↦ 0 < c j), c j := by
  rw [← Finset.sum_filter_add_sum_filter_not B (fun j ↦ 0 < c j)]
  have h2 : ∑ j ∈ B.filter (fun j ↦ ¬ 0 < c j), c j ≤ 0 := by
    refine Finset.sum_nonpos (fun j hj ↦ ?_)
    exact not_lt.mp (Finset.mem_filter.mp hj).2
  have h1 : ∑ j ∈ B.filter (fun j ↦ 0 < c j), c j
      ≤ ∑ j ∈ Finset.univ.filter (fun j ↦ 0 < c j), c j := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset_filter _ (Finset.subset_univ B)) (fun j hj _ ↦ ?_)
    exact (Finset.mem_filter.mp hj).2.le
  linarith

/-- (H6) Sign-mismatch loss: replacing the true positive set by the estimated one costs at
most the `ℓ¹` estimation error. -/
private theorem sum_filter_pos_le_add_dist {k : ℕ} (c chat : Fin k → ℝ) :
    ∑ j ∈ Finset.univ.filter (fun j ↦ 0 < c j), c j
      ≤ ∑ j ∈ Finset.univ.filter (fun j ↦ 0 < chat j), c j + ∑ j, |c j - chat j| := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun j _ ↦ ?_)
  have h1 : c j - chat j ≤ |c j - chat j| := le_abs_self _
  have h2 : -(c j - chat j) ≤ |c j - chat j| := neg_le_abs _
  have h3 : 0 ≤ |c j - chat j| := abs_nonneg _
  by_cases hc : 0 < c j <;> by_cases hch : 0 < chat j
  · rw [if_pos hc, if_pos hch]; linarith
  · rw [if_pos hc, if_neg hch]
    have hch' : chat j ≤ 0 := not_lt.mp hch
    linarith
  · rw [if_neg hc, if_pos hch]; linarith
  · rw [if_neg hc, if_neg hch]; linarith

/-- (H7a) First moment: every index lies in `C(k−1,q−1)` of the `q`-subsets. -/
private theorem sum_powersetCard_sum {k q : ℕ} (hq : 0 < q) (f : Fin k → ℝ) :
    ∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)), ∑ j ∈ Q, f j
      = ((k - 1).choose (q - 1) : ℝ) * ∑ j, f j := by
  have key : ∀ Q : Finset (Fin k), ∑ j ∈ Q, f j
      = ∑ j : Fin k, if j ∈ Q then f j else 0 := by
    intro Q; rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [Finset.sum_congr rfl (fun Q _ ↦ key Q), Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have h1 : ({j} : Finset (Fin k)) ⊆ Finset.univ := Finset.subset_univ _
  have h2 : ({j} : Finset (Fin k)).card ≤ q := by rw [Finset.card_singleton]; omega
  have hc := Finset.card_filter_powersetCard_subset ({j} : Finset (Fin k)) Finset.univ q h1 h2
  rw [Finset.card_univ, Fintype.card_fin, Finset.card_singleton] at hc
  have heq : ((Finset.powersetCard q (Finset.univ : Finset (Fin k))).filter (fun Q ↦ j ∈ Q))
      = (Finset.powersetCard q (Finset.univ : Finset (Fin k))).filter (fun x ↦ {j} ⊆ x) := by
    apply Finset.filter_congr; intro Q _; simp [Finset.singleton_subset_iff]
  rw [heq, hc]

/-- (H7b) Second moment: diagonal pairs lie in `C(k−1,q−1)` subsets, off-diagonal pairs in
`C(k−2,q−2)`. -/
private theorem sum_powersetCard_sq_sum {k q : ℕ} (hq : 2 ≤ q) (f : Fin k → ℝ) :
    ∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)), (∑ j ∈ Q, f j) ^ 2
      = ((k - 1).choose (q - 1) : ℝ) * ∑ j, f j ^ 2
        + ((k - 2).choose (q - 2) : ℝ) * ∑ j, ∑ l ∈ Finset.univ.erase j, f j * f l := by
  have hexp : ∀ Q : Finset (Fin k), (∑ j ∈ Q, f j) ^ 2
      = ∑ j ∈ Q, f j ^ 2 + ∑ j ∈ Q, ∑ l ∈ Q.erase j, f j * f l := by
    intro Q
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj ↦ ?_)
    rw [← Finset.add_sum_erase Q (fun l ↦ f j * f l) hj, sq]
  rw [Finset.sum_congr rfl (fun Q _ ↦ hexp Q), Finset.sum_add_distrib]
  rw [sum_powersetCard_sum (by omega : 0 < q) (fun j ↦ f j ^ 2)]
  congr 1
  have hperQ : ∀ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
      ∑ j ∈ Q, ∑ l ∈ Q.erase j, f j * f l
        = ∑ j : Fin k, ∑ l ∈ Finset.univ.erase j,
            if (j ∈ Q ∧ l ∈ Q) then f j * f l else 0 := by
    intro Q _
    have hR : ∀ j, (∑ l ∈ Finset.univ.erase j, if j ∈ Q ∧ l ∈ Q then f j * f l else 0)
        = if j ∈ Q then (∑ l ∈ Q.erase j, f j * f l) else 0 := by
      intro j
      by_cases hjQ : j ∈ Q
      · simp only [hjQ, true_and, if_true]
        rw [Finset.sum_ite_mem]
        congr 1
        ext l
        simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ]
        tauto
      · simp [hjQ]
    rw [Finset.sum_congr rfl (fun j _ ↦ hR j), Finset.sum_ite_mem, Finset.univ_inter]
  rw [Finset.sum_congr rfl hperQ, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l hl ↦ ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcount : ((Finset.powersetCard q (Finset.univ : Finset (Fin k))).filter
      (fun Q ↦ j ∈ Q ∧ l ∈ Q)).card = (k - 2).choose (q - 2) := by
    have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
    have hjl : j ≠ l := hlj.symm
    have hins : ({j, l} : Finset (Fin k)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hjl]), Finset.card_singleton]
    have h1 : ({j, l} : Finset (Fin k)) ⊆ Finset.univ := Finset.subset_univ _
    have h2 : ({j, l} : Finset (Fin k)).card ≤ q := by rw [hins]; omega
    have hc := Finset.card_filter_powersetCard_subset ({j, l} : Finset (Fin k))
      Finset.univ q h1 h2
    rw [Finset.card_univ, Fintype.card_fin, hins] at hc
    have hfeq : (Finset.powersetCard q (Finset.univ : Finset (Fin k))).filter
          (fun Q ↦ j ∈ Q ∧ l ∈ Q)
        = (Finset.powersetCard q (Finset.univ : Finset (Fin k))).filter (fun x ↦ {j, l} ⊆ x) := by
      apply Finset.filter_congr
      intro Q _
      simp [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    rw [hfeq, hc]
  rw [hcount]

/-- Falling-factorial identity for binomial coefficients: `(b+1)·C(a+1,b+1) = (a+1)·C(a,b)`. -/
private theorem choose_mul_aux (a b : ℕ) :
    (b + 1) * (a + 1).choose (b + 1) = (a + 1) * a.choose b := by
  rw [Nat.add_one_mul_choose_eq a b]; ring

/-- Abstract variance bound: given the first and second hypergeometric moments (`e1`, `e2`),
the binomial identity `k·D1 = q·N` and the pair bound `k²·D2 ≤ q²·N`, the average of
`(k/q·T − S₁)²` is at most `N·k²/q`. Used with `T Q = ∑_{j∈Q} f`, `S₁ = ∑ f`, `S₂ = ∑ f²`. -/
private theorem var_bound_core (k q : ℕ) (psc : Finset (Finset (Fin k)))
    (T : Finset (Fin k) → ℝ) (S₁ S₂ N D1 D2 : ℝ)
    (hS2le : S₂ ≤ k) (hS2nn : 0 ≤ S₂) (hcardR : (psc.card : ℝ) = N) (hNnn : 0 ≤ N)
    (e1 : ∑ Q ∈ psc, T Q = D1 * S₁)
    (e2 : ∑ Q ∈ psc, T Q ^ 2 = D1 * S₂ + D2 * (S₁ ^ 2 - S₂))
    (id1R : (k : ℝ) * D1 = q * N)
    (hD2nn : 0 ≤ D2) (hD2 : (k : ℝ) ^ 2 * D2 ≤ (q : ℝ) ^ 2 * N)
    (hq0 : (0 : ℝ) < q) (hk0 : (0 : ℝ) ≤ k) :
    ∑ Q ∈ psc, ((k : ℝ) / q * T Q - S₁) ^ 2 ≤ N * (k : ℝ) ^ 2 / q := by
  have hexp : ∑ Q ∈ psc, ((k : ℝ) / q * T Q - S₁) ^ 2
      = ((k : ℝ) / q) ^ 2 * (∑ Q ∈ psc, T Q ^ 2) - 2 * ((k : ℝ) / q) * S₁ * (∑ Q ∈ psc, T Q)
        + S₁ ^ 2 * (psc.card : ℝ) := by
    rw [Finset.sum_congr rfl (fun Q _ ↦ (by ring : ((k : ℝ) / q * T Q - S₁) ^ 2
        = ((k : ℝ) / q) ^ 2 * T Q ^ 2 - 2 * ((k : ℝ) / q) * S₁ * T Q + S₁ ^ 2))]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul, mul_comm ((psc.card : ℝ)) (S₁ ^ 2)]
  rw [hexp, e1, e2, hcardR, ← sub_nonneg]
  have h2 : (k : ℝ) ^ 2 * D1 * S₂ = k * q * N * S₂ := by linear_combination (k * S₂) * id1R
  have h3 : (k : ℝ) * q * S₁ ^ 2 * D1 = q ^ 2 * S₁ ^ 2 * N := by
    linear_combination (q * S₁ ^ 2) * id1R
  have hA : 0 ≤ q * N * k * (k - S₂) :=
    mul_nonneg (mul_nonneg (mul_nonneg hq0.le hNnn) hk0) (by linarith)
  have hB : 0 ≤ (k : ℝ) ^ 2 * D2 * S₂ := mul_nonneg (mul_nonneg (sq_nonneg _) hD2nn) hS2nn
  have hC : 0 ≤ S₁ ^ 2 * ((q : ℝ) ^ 2 * N - k ^ 2 * D2) := mul_nonneg (sq_nonneg _) (by linarith)
  have hexp2 : N * (k : ℝ) ^ 2 / q - (((k : ℝ) / q) ^ 2 * (D1 * S₂ + D2 * (S₁ ^ 2 - S₂))
      - 2 * ((k : ℝ) / q) * S₁ * (D1 * S₁) + S₁ ^ 2 * N)
      = (1 / q ^ 2) * (q * N * k ^ 2 - ((k : ℝ) ^ 2 * (D1 * S₂ + D2 * (S₁ ^ 2 - S₂))
          - 2 * k * q * S₁ * (D1 * S₁) + q ^ 2 * S₁ ^ 2 * N)) := by
    field_simp
  rw [hexp2]
  apply mul_nonneg (by positivity)
  nlinarith [h2, h3, hA, hB, hC]

/-- Variance bound for the without-replacement estimator: for `|f| ≤ 1`, the average of
`(k/q·∑_{j∈Q} f − ∑ f)²` over `q`-subsets is at most `C(k,q)·k²/q`. -/
private theorem sum_powersetCard_var_bound {k q : ℕ} (hq : 0 < q) (hqk : q ≤ k)
    (f : Fin k → ℝ) (hf : ∀ j, |f j| ≤ 1) :
    ∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
        ((k : ℝ) / q * ∑ j ∈ Q, f j - ∑ j, f j) ^ 2 ≤ (k.choose q : ℝ) * (k : ℝ) ^ 2 / q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hqkr : (q : ℝ) ≤ k := by exact_mod_cast hqk
  have hS2nn : 0 ≤ ∑ j, f j ^ 2 := Finset.sum_nonneg (fun j _ ↦ sq_nonneg _)
  have hS2le : (∑ j, f j ^ 2) ≤ k := by
    calc ∑ j, f j ^ 2 ≤ ∑ _j : Fin k, (1 : ℝ) :=
          Finset.sum_le_sum (fun j _ ↦ by nlinarith [hf j, abs_nonneg (f j), sq_abs (f j)])
      _ = k := by simp
  have hcardR : ((Finset.powersetCard q (Finset.univ : Finset (Fin k))).card : ℝ)
      = (k.choose q : ℝ) := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hNnn : 0 ≤ (k.choose q : ℝ) := by positivity
  have e1 : ∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)), ∑ j ∈ Q, f j
      = ((k - 1).choose (q - 1) : ℝ) * ∑ j, f j := sum_powersetCard_sum hq f
  have id1R : (k : ℝ) * ((k - 1).choose (q - 1) : ℝ) = q * (k.choose q : ℝ) := by
    have id1 : q * k.choose q = k * (k - 1).choose (q - 1) := by
      have h := choose_mul_aux (k - 1) (q - 1)
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ k), Nat.sub_add_cancel (by omega : 1 ≤ q)] at h
    exact_mod_cast id1.symm
  by_cases hq2 : 2 ≤ q
  · have hq2r : (2 : ℝ) ≤ q := by exact_mod_cast hq2
    have e2 : ∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)), (∑ j ∈ Q, f j) ^ 2
        = ((k - 1).choose (q - 1) : ℝ) * (∑ j, f j ^ 2)
          + ((k - 2).choose (q - 2) : ℝ) * ((∑ j, f j) ^ 2 - ∑ j, f j ^ 2) := by
      rw [sum_powersetCard_sq_sum hq2 f]
      congr 1
      have hP : ∀ j, ∑ l ∈ Finset.univ.erase j, f j * f l = f j * ((∑ l, f l) - f j) := by
        intro j
        rw [← Finset.mul_sum]; congr 1
        have hh := Finset.add_sum_erase Finset.univ f (Finset.mem_univ j); linarith [hh]
      rw [Finset.sum_congr rfl (fun j _ ↦ hP j)]
      rw [Finset.sum_congr rfl (fun j _ ↦ (by ring :
        f j * ((∑ l, f l) - f j) = f j * (∑ l, f l) - f j ^ 2))]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]; ring
    have hD2 : (k : ℝ) ^ 2 * ((k - 2).choose (q - 2) : ℝ) ≤ (q : ℝ) ^ 2 * (k.choose q : ℝ) := by
      have id2 : (q * (q - 1)) * k.choose q = (k * (k - 1)) * (k - 2).choose (q - 2) := by
        have id1 : q * k.choose q = k * (k - 1).choose (q - 1) := by
          have h := choose_mul_aux (k - 1) (q - 1)
          rwa [Nat.sub_add_cancel (by omega : 1 ≤ k), Nat.sub_add_cancel (by omega : 1 ≤ q)] at h
        have id1' : (q - 1) * (k - 1).choose (q - 1) = (k - 1) * (k - 2).choose (q - 2) := by
          have h := choose_mul_aux (k - 2) (q - 2)
          rw [show q - 2 + 1 = q - 1 from by omega, show k - 2 + 1 = k - 1 from by omega] at h
          exact h
        calc (q * (q - 1)) * k.choose q
            = (q - 1) * (q * k.choose q) := by ring
          _ = (q - 1) * (k * (k - 1).choose (q - 1)) := by rw [id1]
          _ = k * ((q - 1) * (k - 1).choose (q - 1)) := by ring
          _ = k * ((k - 1) * (k - 2).choose (q - 2)) := by rw [id1']
          _ = (k * (k - 1)) * (k - 2).choose (q - 2) := by ring
      have id2R : ((q * (q - 1) : ℕ) : ℝ) * (k.choose q : ℝ)
          = ((k * (k - 1) : ℕ) : ℝ) * ((k - 2).choose (q - 2) : ℝ) := by exact_mod_cast id2
      have hApos : ((q * (q - 1) : ℕ) : ℝ) = (q : ℝ) * ((q : ℝ) - 1) := by
        push_cast [Nat.cast_sub (show 1 ≤ q by omega)]; ring
      have hBval : ((k * (k - 1) : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by
        push_cast [Nat.cast_sub (show 1 ≤ k by omega)]; ring
      rw [hApos, hBval] at id2R
      have hBpos : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) := by nlinarith [hq2r, hqkr]
      have hk2A : (k : ℝ) ^ 2 * ((q : ℝ) * ((q : ℝ) - 1))
          ≤ (q : ℝ) ^ 2 * ((k : ℝ) * ((k : ℝ) - 1)) := by
        nlinarith [hqkr, hq0, hk0, mul_nonneg hq0.le hk0]
      have hkey : (k : ℝ) ^ 2 * ((k - 2).choose (q - 2) : ℝ) * ((k : ℝ) * ((k : ℝ) - 1))
          ≤ (q : ℝ) ^ 2 * (k.choose q : ℝ) * ((k : ℝ) * ((k : ℝ) - 1)) := by
        have hrw : (k : ℝ) ^ 2 * ((k - 2).choose (q - 2) : ℝ) * ((k : ℝ) * ((k : ℝ) - 1))
            = (k : ℝ) ^ 2 * ((q : ℝ) * ((q : ℝ) - 1)) * (k.choose q : ℝ) := by
          linear_combination (-(k : ℝ) ^ 2) * id2R
        rw [hrw]; nlinarith [hk2A, hNnn]
      exact le_of_mul_le_mul_right hkey hBpos
    exact var_bound_core k q (Finset.powersetCard q Finset.univ) (fun Q ↦ ∑ j ∈ Q, f j)
      (∑ j, f j) (∑ j, f j ^ 2) (k.choose q : ℝ) ((k - 1).choose (q - 1) : ℝ)
      ((k - 2).choose (q - 2) : ℝ) hS2le hS2nn hcardR hNnn e1 e2 id1R (by positivity) hD2 hq0 hk0
  · have hq1 : q = 1 := by omega
    subst hq1
    have e2 : ∑ Q ∈ Finset.powersetCard 1 (Finset.univ : Finset (Fin k)), (∑ j ∈ Q, f j) ^ 2
        = ((k - 1).choose (1 - 1) : ℝ) * (∑ j, f j ^ 2)
          + (0 : ℝ) * ((∑ j, f j) ^ 2 - ∑ j, f j ^ 2) := by
      rw [Finset.powersetCard_one, Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, Finset.sum_singleton]; simp
    exact var_bound_core k 1 (Finset.powersetCard 1 Finset.univ) (fun Q ↦ ∑ j ∈ Q, f j)
      (∑ j, f j) (∑ j, f j ^ 2) (k.choose 1 : ℝ) ((k - 1).choose (1 - 1) : ℝ) 0
      hS2le hS2nn hcardR hNnn e1 e2 id1R (le_refl 0) (by rw [mul_zero]; positivity) hq0 hk0

/-- (H7c) `ℓ¹` estimation error of the without-replacement subsample estimator: for
`|f| ≤ 1`, the average over all `q`-subsets of `|(k/q)·∑_{j∈Q} f − ∑ f|` is at most
`k/√q`. Stated unnormalized (both sides times `C(k,q)`). -/
private theorem sum_powersetCard_abs_sub_le {k q : ℕ} (hq : 0 < q) (hqk : q ≤ k)
    (f : Fin k → ℝ) (hf : ∀ j, |f j| ≤ 1) :
    ∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
        |(k : ℝ) / q * ∑ j ∈ Q, f j - ∑ j, f j|
      ≤ (k.choose q : ℝ) * ((k : ℝ) / Real.sqrt q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hNnn : 0 ≤ (k.choose q : ℝ) := by positivity
  have hvar := sum_powersetCard_var_bound hq hqk f hf
  have hWnonneg : 0 ≤ ∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
      |(k : ℝ) / q * ∑ j ∈ Q, f j - ∑ j, f j| := Finset.sum_nonneg (fun Q _ ↦ abs_nonneg _)
  have hcardR : ((Finset.powersetCard q (Finset.univ : Finset (Fin k))).card : ℝ)
      = (k.choose q : ℝ) := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := Finset.powersetCard q (Finset.univ : Finset (Fin k)))
    (f := fun Q ↦ |(k : ℝ) / q * ∑ j ∈ Q, f j - ∑ j, f j|)
  simp only [sq_abs] at hcs
  rw [hcardR] at hcs
  have hWsq : (∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
        |(k : ℝ) / q * ∑ j ∈ Q, f j - ∑ j, f j|) ^ 2
      ≤ (k.choose q : ℝ) ^ 2 * (k : ℝ) ^ 2 / q := by
    calc (∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
            |(k : ℝ) / q * ∑ j ∈ Q, f j - ∑ j, f j|) ^ 2
        ≤ (k.choose q : ℝ) * ∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
            ((k : ℝ) / q * ∑ j ∈ Q, f j - ∑ j, f j) ^ 2 := hcs
      _ ≤ (k.choose q : ℝ) * ((k.choose q : ℝ) * (k : ℝ) ^ 2 / q) :=
          mul_le_mul_of_nonneg_left hvar hNnn
      _ = (k.choose q : ℝ) ^ 2 * (k : ℝ) ^ 2 / q := by ring
  have hsqrtq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0.le
  have hrhs_nonneg : 0 ≤ (k.choose q : ℝ) * ((k : ℝ) / Real.sqrt q) := by positivity
  have hrhs_sq : ((k.choose q : ℝ) * ((k : ℝ) / Real.sqrt q)) ^ 2
      = (k.choose q : ℝ) ^ 2 * (k : ℝ) ^ 2 / q := by
    rw [mul_pow, div_pow, hsqrtq]; ring
  calc ∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
        |(k : ℝ) / q * ∑ j ∈ Q, f j - ∑ j, f j|
      = Real.sqrt ((∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
          |(k : ℝ) / q * ∑ j ∈ Q, f j - ∑ j, f j|) ^ 2) := (Real.sqrt_sq hWnonneg).symm
    _ ≤ Real.sqrt (((k.choose q : ℝ) * ((k : ℝ) / Real.sqrt q)) ^ 2) := by
        apply Real.sqrt_le_sqrt; rw [hrhs_sq]; exact hWsq
    _ = (k.choose q : ℝ) * ((k : ℝ) / Real.sqrt q) := Real.sqrt_sq hrhs_nonneg

/-- (H8) **One guessing step.** For a fixed cut `(A, B)` of a symmetric, entrywise-bounded
matrix, replacing `B` by the sign set guessed from `Q ∩ A` and averaging over the `q`-subsets
`Q` costs at most `k²/√q`. -/
private theorem cut_le_avg_signSet_step {k q : ℕ} (hq : 0 < q) (hqk : q ≤ k)
    (m : Fin k → Fin k → ℝ) (hsymm : ∀ i j, m i j = m j i) (hm : ∀ i j, |m i j| ≤ 1)
    (A B : Finset (Fin k)) :
    ∑ i ∈ A, ∑ j ∈ B, m i j
      ≤ (k.choose q : ℝ)⁻¹ * (∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
          ∑ i ∈ A, ∑ j ∈ signSet m (Q ∩ A), m i j)
        + (k : ℝ) ^ 2 / Real.sqrt q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hkq : (q : ℝ) ≤ k := by exact_mod_cast hqk
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le hq0 hkq
  have hkqpos : (0 : ℝ) < (k : ℝ) / q := div_pos hk0 hq0
  set psc := Finset.powersetCard q (Finset.univ : Finset (Fin k)) with hpsc
  set N := (k.choose q : ℝ) with hN
  set c : Fin k → ℝ := fun j ↦ ∑ i ∈ A, m i j with hc
  have hN0 : (0 : ℝ) < N := by rw [hN]; exact_mod_cast Nat.choose_pos hqk
  have hcard : (psc.card : ℝ) = N := by
    rw [hpsc, hN, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [show ∑ i ∈ A, ∑ j ∈ B, m i j = ∑ j ∈ B, c j from by
    simp only [hc]; rw [Finset.sum_comm]]
  -- H5: enlarge to the positive part
  have h5 : ∑ j ∈ B, c j ≤ ∑ j ∈ Finset.univ.filter (fun j ↦ 0 < c j), c j :=
    sum_le_sum_filter_pos c B
  -- the estimated positive set is exactly the sign set of `Q ∩ A`
  have hsign : ∀ Q, Finset.univ.filter (fun j ↦ 0 < (k : ℝ) / q * ∑ i ∈ Q ∩ A, m i j)
      = signSet m (Q ∩ A) := by
    intro Q
    rw [signSet]
    apply Finset.filter_congr
    intro j _
    rw [mul_pos_iff_of_pos_left hkqpos,
      Finset.sum_congr rfl (fun i (_ : i ∈ Q ∩ A) ↦ hsymm i j)]
  -- transpose the sign-set column sum back to the guessed rectangle
  have hswap : ∀ Q, ∑ j ∈ signSet m (Q ∩ A), c j
      = ∑ i ∈ A, ∑ j ∈ signSet m (Q ∩ A), m i j := by
    intro Q
    simp only [hc]; rw [Finset.sum_comm]
  -- one estimator instance per subset `Q`
  have hper : ∀ Q ∈ psc, ∑ j ∈ Finset.univ.filter (fun j ↦ 0 < c j), c j
      ≤ (∑ i ∈ A, ∑ j ∈ signSet m (Q ∩ A), m i j)
        + ∑ j, |c j - (k : ℝ) / q * ∑ i ∈ Q ∩ A, m i j| := by
    intro Q _
    have h6 := sum_filter_pos_le_add_dist c (fun j ↦ (k : ℝ) / q * ∑ i ∈ Q ∩ A, m i j)
    simp only [hsign Q, hswap Q] at h6
    exact h6
  -- average over `Q`: the constant left side becomes `N ·`
  have havg : N * ∑ j ∈ Finset.univ.filter (fun j ↦ 0 < c j), c j
      ≤ (∑ Q ∈ psc, ∑ i ∈ A, ∑ j ∈ signSet m (Q ∩ A), m i j)
        + ∑ Q ∈ psc, ∑ j, |c j - (k : ℝ) / q * ∑ i ∈ Q ∩ A, m i j| := by
    have hsum := Finset.sum_le_sum hper
    rw [Finset.sum_const, nsmul_eq_mul, hcard, Finset.sum_add_distrib] at hsum
    exact hsum
  -- the estimation error, averaged, is at most `N · k²/√q`
  have herr : ∑ Q ∈ psc, ∑ j, |c j - (k : ℝ) / q * ∑ i ∈ Q ∩ A, m i j|
      ≤ N * ((k : ℝ) ^ 2 / Real.sqrt q) := by
    rw [Finset.sum_comm]
    have hbound : ∀ j : Fin k, ∑ Q ∈ psc, |c j - (k : ℝ) / q * ∑ i ∈ Q ∩ A, m i j|
        ≤ N * ((k : ℝ) / Real.sqrt q) := by
      intro j
      set f : Fin k → ℝ := fun i ↦ if i ∈ A then m i j else 0 with hf
      have hfle : ∀ i, |f i| ≤ 1 := by
        intro i
        simp only [hf]
        by_cases hi : i ∈ A
        · rw [if_pos hi]; exact hm i j
        · rw [if_neg hi, abs_zero]; exact zero_le_one
      have hsub : ∀ Q, ∑ i ∈ Q, f i = ∑ i ∈ Q ∩ A, m i j := by
        intro Q; simp only [hf, Finset.sum_ite_mem]
      have htot : ∑ i, f i = c j := by
        simp only [hf, Finset.sum_ite_mem, Finset.univ_inter, hc]
      have hH7 := sum_powersetCard_abs_sub_le hq hqk f hfle
      have hrw : ∀ Q, |c j - (k : ℝ) / q * ∑ i ∈ Q ∩ A, m i j|
          = |(k : ℝ) / q * ∑ i ∈ Q, f i - ∑ i, f i| := by
        intro Q; rw [hsub Q, htot, abs_sub_comm]
      calc ∑ Q ∈ psc, |c j - (k : ℝ) / q * ∑ i ∈ Q ∩ A, m i j|
          = ∑ Q ∈ psc, |(k : ℝ) / q * ∑ i ∈ Q, f i - ∑ i, f i| :=
            Finset.sum_congr rfl (fun Q _ ↦ hrw Q)
        _ ≤ N * ((k : ℝ) / Real.sqrt q) := by rw [hpsc, hN]; exact hH7
    calc ∑ j, ∑ Q ∈ psc, |c j - (k : ℝ) / q * ∑ i ∈ Q ∩ A, m i j|
        ≤ ∑ _j : Fin k, N * ((k : ℝ) / Real.sqrt q) :=
          Finset.sum_le_sum (fun j _ ↦ hbound j)
      _ = N * ((k : ℝ) ^ 2 / Real.sqrt q) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  -- assemble
  have hkey : N * (∑ j ∈ B, c j)
      ≤ (∑ Q ∈ psc, ∑ i ∈ A, ∑ j ∈ signSet m (Q ∩ A), m i j)
        + N * ((k : ℝ) ^ 2 / Real.sqrt q) := by
    calc N * (∑ j ∈ B, c j)
        ≤ N * ∑ j ∈ Finset.univ.filter (fun j ↦ 0 < c j), c j :=
          mul_le_mul_of_nonneg_left h5 hN0.le
      _ ≤ (∑ Q ∈ psc, ∑ i ∈ A, ∑ j ∈ signSet m (Q ∩ A), m i j)
          + ∑ Q ∈ psc, ∑ j, |c j - (k : ℝ) / q * ∑ i ∈ Q ∩ A, m i j| := havg
      _ ≤ (∑ Q ∈ psc, ∑ i ∈ A, ∑ j ∈ signSet m (Q ∩ A), m i j)
          + N * ((k : ℝ) ^ 2 / Real.sqrt q) := by linarith [herr]
  apply le_of_mul_le_mul_left (a := N) _ hN0
  rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hN0.ne', one_mul]
  exact hkey

/-- (H9a) **The two-sided guessing chain**: the full cut sup is dominated by the double
average, over independent `q`-subsets `(Q, Q')`, of the best UNSIGNED rule rectangle, plus
`2k²/√q`. -/
private theorem sup'_cut_le_avg_ruleSup {k q : ℕ} [NeZero k] (hq : 0 < q) (hqk : q ≤ k)
    (m : Fin k → Fin k → ℝ) (hsymm : ∀ i j, m i j = m j i) (hm : ∀ i j, |m i j| ≤ 1) :
    (Finset.univ : Finset (Finset (Fin k) × Finset (Fin k))).sup' Finset.univ_nonempty
        (fun AB ↦ ∑ i ∈ AB.1, ∑ j ∈ AB.2, m i j)
      ≤ ((k.choose q : ℝ)⁻¹) ^ 2 *
          (∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
           ∑ Q' ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
            (signedRules Q Q').sup' (signedRules_nonempty Q Q')
              (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * m i j) ρ.2.1 ρ.2.2))
        + 2 * (k : ℝ) ^ 2 / Real.sqrt q := by
  set psc := Finset.powersetCard q (Finset.univ : Finset (Fin k)) with hpsc
  set N := (k.choose q : ℝ) with hN
  have hN0 : (0 : ℝ) < N := by rw [hN]; exact_mod_cast Nat.choose_pos hqk
  have hNinv_nn : (0 : ℝ) ≤ N⁻¹ := (inv_pos.mpr hN0).le
  have hcard : (psc.card : ℝ) = N := by
    rw [hpsc, hN, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  refine Finset.sup'_le _ _ (fun AB _ ↦ ?_)
  obtain ⟨A, B⟩ := AB
  -- transpose a guessed rectangle: rows in `A`, columns in a sign set
  have htrans : ∀ Q, ∑ i ∈ A, ∑ j ∈ signSet m (Q ∩ A), m i j
      = ∑ i ∈ signSet m (Q ∩ A), ∑ j ∈ A, m i j := by
    intro Q
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun b _ ↦ Finset.sum_congr rfl (fun a _ ↦ hsymm a b))
  -- the doubly-guessed rectangle is exactly `ruleVal`, up to a transpose
  have hback : ∀ Q Q', ∑ i ∈ signSet m (Q ∩ A),
        ∑ j ∈ signSet m (Q' ∩ signSet m (Q ∩ A)), m i j
      = ruleVal m (Q ∩ A) (Q' ∩ signSet m (Q ∩ A)) := by
    intro Q Q'
    simp only [ruleVal]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun b _ ↦ Finset.sum_congr rfl (fun a _ ↦ hsymm a b))
  -- `ruleVal m` embeds in the signed rule sup at the `true` sign bit
  have hle_sup : ∀ Q Q', ruleVal m (Q ∩ A) (Q' ∩ signSet m (Q ∩ A))
      ≤ (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * m i j) ρ.2.1 ρ.2.2) := by
    intro Q Q'
    have hone : (fun i j ↦ sgnR true * m i j) = m := by funext i j; simp [sgnR]
    have hmem : (true, Q ∩ A, Q' ∩ signSet m (Q ∩ A)) ∈ signedRules Q Q' := by
      simp only [signedRules, Finset.mem_product, Finset.mem_univ, Finset.mem_powerset,
        true_and]
      exact ⟨Finset.inter_subset_left, Finset.inter_subset_left⟩
    rw [show ruleVal m (Q ∩ A) (Q' ∩ signSet m (Q ∩ A))
        = ruleVal (fun i j ↦ sgnR true * m i j) (Q ∩ A) (Q' ∩ signSet m (Q ∩ A)) from by
      rw [hone]]
    exact Finset.le_sup' (fun ρ : Bool × Finset (Fin k) × Finset (Fin k) ↦
      ruleVal (fun i j ↦ sgnR ρ.1 * m i j) ρ.2.1 ρ.2.2) hmem
  -- per-`Q` bound: apply H8 to the transposed cut `(signSet m (Q ∩ A), A)`
  have hmainQ : ∀ Q ∈ psc, ∑ i ∈ A, ∑ j ∈ signSet m (Q ∩ A), m i j
      ≤ N⁻¹ * (∑ Q' ∈ psc, (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * m i j) ρ.2.1 ρ.2.2))
        + (k : ℝ) ^ 2 / Real.sqrt q := by
    intro Q _
    rw [htrans Q]
    have hH8 := cut_le_avg_signSet_step hq hqk m hsymm hm (signSet m (Q ∩ A)) A
    rw [← hpsc, ← hN] at hH8
    refine hH8.trans ?_
    have hstep : ∀ Q', ∑ i ∈ signSet m (Q ∩ A),
          ∑ j ∈ signSet m (Q' ∩ signSet m (Q ∩ A)), m i j
        ≤ (signedRules Q Q').sup' (signedRules_nonempty Q Q')
            (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * m i j) ρ.2.1 ρ.2.2) := by
      intro Q'
      rw [hback Q Q']
      exact hle_sup Q Q'
    have hmul := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (s := psc) (fun Q' _ ↦ hstep Q')) hNinv_nn
    linarith [hmul]
  -- assemble the two-sided chain
  have hAB := cut_le_avg_signSet_step hq hqk m hsymm hm A B
  rw [← hpsc, ← hN] at hAB
  calc ∑ i ∈ A, ∑ j ∈ B, m i j
      ≤ N⁻¹ * (∑ Q ∈ psc, ∑ i ∈ A, ∑ j ∈ signSet m (Q ∩ A), m i j)
          + (k : ℝ) ^ 2 / Real.sqrt q := hAB
    _ ≤ N⁻¹ * (∑ Q ∈ psc, (N⁻¹ * (∑ Q' ∈ psc,
          (signedRules Q Q').sup' (signedRules_nonempty Q Q')
            (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * m i j) ρ.2.1 ρ.2.2))
          + (k : ℝ) ^ 2 / Real.sqrt q)) + (k : ℝ) ^ 2 / Real.sqrt q := by
        have hmono := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hmainQ) hNinv_nn
        linarith [hmono]
    _ = (N⁻¹) ^ 2 * (∑ Q ∈ psc, ∑ Q' ∈ psc,
          (signedRules Q Q').sup' (signedRules_nonempty Q Q')
            (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * m i j) ρ.2.1 ρ.2.2))
        + 2 * (k : ℝ) ^ 2 / Real.sqrt q := by
        have hNN : N⁻¹ * N = 1 := inv_mul_cancel₀ hN0.ne'
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hcard]
        linear_combination ((k : ℝ) ^ 2 / Real.sqrt q) * hNN

/-- (H9b) **Absolute values via the sign bit**: apply the chain to `m` and `−m`; the two
one-sided rule sups embed in the signed rule sup. -/
private theorem sup'_abs_cut_le_avg_signedRuleSup {k q : ℕ} [NeZero k] (hq : 0 < q)
    (hqk : q ≤ k) (m : Fin k → Fin k → ℝ) (hsymm : ∀ i j, m i j = m j i)
    (hm : ∀ i j, |m i j| ≤ 1) :
    (Finset.univ : Finset (Finset (Fin k) × Finset (Fin k))).sup' Finset.univ_nonempty
        (fun AB ↦ |∑ i ∈ AB.1, ∑ j ∈ AB.2, m i j|)
      ≤ ((k.choose q : ℝ)⁻¹) ^ 2 *
          (∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
           ∑ Q' ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
            (signedRules Q Q').sup' (signedRules_nonempty Q Q')
              (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * m i j) ρ.2.1 ρ.2.2))
        + 2 * (k : ℝ) ^ 2 / Real.sqrt q := by
  -- the reflected matrix `m' = -m`
  set m' : Fin k → Fin k → ℝ := fun i j ↦ -m i j with hm'def
  have hsymm' : ∀ i j, m' i j = m' j i := fun i j ↦ by simp only [hm'def]; rw [hsymm i j]
  have hm'le : ∀ i j, |m' i j| ≤ 1 := fun i j ↦ by simp only [hm'def, abs_neg]; exact hm i j
  have hnegsum : ∀ A B : Finset (Fin k),
      -(∑ i ∈ A, ∑ j ∈ B, m i j) = ∑ i ∈ A, ∑ j ∈ B, m' i j := by
    intro A B
    simp only [hm'def]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [← Finset.sum_neg_distrib]
  -- `sgnR s · (−x) = sgnR (¬s) · x`
  have hsgn : ∀ (s : Bool) (x : ℝ), sgnR s * (-x) = sgnR (!s) * x := by
    intro s x; cases s <;> simp [sgnR]
  -- the sign bit turns the `m'` signed-rule sup into the `m` signed-rule sup
  have hflip : ∀ Q Q',
      (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * m' i j) ρ.2.1 ρ.2.2)
      = (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * m i j) ρ.2.1 ρ.2.2) := by
    intro Q Q'
    have hmem : ∀ ρ : Bool × Finset (Fin k) × Finset (Fin k), ρ ∈ signedRules Q Q' →
        (!ρ.1, ρ.2.1, ρ.2.2) ∈ signedRules Q Q' := by
      intro ρ hρ
      simp only [signedRules, Finset.mem_product, Finset.mem_univ, Finset.mem_powerset,
        true_and] at hρ ⊢
      exact hρ
    apply le_antisymm
    · refine Finset.sup'_le _ _ (fun ρ hρ ↦ ?_)
      rw [show ruleVal (fun i j ↦ sgnR ρ.1 * m' i j) ρ.2.1 ρ.2.2
          = ruleVal (fun i j ↦ sgnR (!ρ.1) * m i j) ρ.2.1 ρ.2.2 from by
        rw [show (fun i j ↦ sgnR ρ.1 * m' i j) = (fun i j ↦ sgnR (!ρ.1) * m i j) from by
          funext i j; simp only [hm'def]; exact hsgn ρ.1 (m i j)]]
      exact Finset.le_sup' (fun ρ : Bool × Finset (Fin k) × Finset (Fin k) ↦
        ruleVal (fun i j ↦ sgnR ρ.1 * m i j) ρ.2.1 ρ.2.2) (hmem ρ hρ)
    · refine Finset.sup'_le _ _ (fun ρ hρ ↦ ?_)
      rw [show ruleVal (fun i j ↦ sgnR ρ.1 * m i j) ρ.2.1 ρ.2.2
          = ruleVal (fun i j ↦ sgnR (!ρ.1) * m' i j) ρ.2.1 ρ.2.2 from by
        rw [show (fun i j ↦ sgnR ρ.1 * m i j) = (fun i j ↦ sgnR (!ρ.1) * m' i j) from by
          funext i j; simp only [hm'def]; rw [hsgn (!ρ.1) (m i j), Bool.not_not]]]
      exact Finset.le_sup' (fun ρ : Bool × Finset (Fin k) × Finset (Fin k) ↦
        ruleVal (fun i j ↦ sgnR ρ.1 * m' i j) ρ.2.1 ρ.2.2) (hmem ρ hρ)
  -- the two one-sided chains
  have h9a_m := sup'_cut_le_avg_ruleSup hq hqk m hsymm hm
  have h9a_m' := sup'_cut_le_avg_ruleSup hq hqk m' hsymm' hm'le
  rw [Finset.sum_congr rfl (fun Q _ ↦ Finset.sum_congr rfl (fun Q' _ ↦ hflip Q Q'))]
    at h9a_m'
  -- combine via `|·| ≤` two-sidedly
  refine Finset.sup'_le _ _ (fun AB _ ↦ ?_)
  obtain ⟨A, B⟩ := AB
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · rw [neg_le, hnegsum A B]
    exact (Finset.le_sup' (fun AB : Finset (Fin k) × Finset (Fin k) ↦
      ∑ i ∈ AB.1, ∑ j ∈ AB.2, m' i j) (Finset.mem_univ (A, B))).trans h9a_m'
  · exact (Finset.le_sup' (fun AB : Finset (Fin k) × Finset (Fin k) ↦
      ∑ i ∈ AB.1, ∑ j ∈ AB.2, m i j) (Finset.mem_univ (A, B))).trans h9a_m

omit [StandardBorelSpace α] [NullSingletonClass μ] in
/-- Measurability of the sample rule value, for the integrability side conditions. -/
private theorem measurable_ruleVal_sample (W : Graphon α μ) (ε' : ℝ) {k : ℕ}
    (s : Bool) (R R' : Finset (Fin k)) :
    Measurable (fun x : Fin k → α ↦
      ruleVal (fun i j ↦ sgnR s * coreDiff W ε' x i j) R R') := by
  have hcd : ∀ (a b : Fin k), Measurable (fun x : Fin k → α ↦ coreDiff W ε' x a b) := by
    intro a b
    simp only [coreDiff]
    exact (measurable_clampEval W a b).sub (measurable_clampEval (chosenStep W ε') a b)
  have hm : ∀ (a b : Fin k),
      Measurable (fun x : Fin k → α ↦ sgnR s * coreDiff W ε' x a b) :=
    fun a b ↦ (hcd a b).const_mul _
  have hsum : ∀ (a : Fin k) (S : Finset (Fin k)),
      Measurable (fun x : Fin k → α ↦ ∑ b ∈ S, sgnR s * coreDiff W ε' x a b) :=
    fun a S ↦ Finset.measurable_sum _ (fun b _ ↦ hm a b)
  have hrw : ∀ x : Fin k → α,
      ruleVal (fun i j ↦ sgnR s * coreDiff W ε' x i j) R R'
        = ∑ i, ∑ j,
          (if 0 < ∑ j' ∈ R', sgnR s * coreDiff W ε' x i j' then (1 : ℝ) else 0) *
          (if 0 < ∑ j' ∈ R, sgnR s * coreDiff W ε' x j j' then (1 : ℝ) else 0) *
          (sgnR s * coreDiff W ε' x i j) := by
    intro x
    simp only [ruleVal, signSet, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hP : 0 < ∑ j' ∈ R', sgnR s * coreDiff W ε' x i j'
    · simp only [hP, if_true, one_mul]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      by_cases hQ : 0 < ∑ j' ∈ R, sgnR s * coreDiff W ε' x j j' <;> simp [hQ]
    · simp [hP]
  simp only [hrw]
  refine Finset.measurable_sum _ (fun i _ ↦ Finset.measurable_sum _ (fun j _ ↦ ?_))
  refine Measurable.mul (Measurable.mul ?_ ?_) (hm i j)
  · exact Measurable.ite (measurableSet_lt measurable_const (hsum i R')) measurable_const
      measurable_const
  · exact Measurable.ite (measurableSet_lt measurable_const (hsum j R)) measurable_const
      measurable_const

omit [StandardBorelSpace α] [NullSingletonClass μ] in
/-- (H9c) **BRIDGE GATE** — the exact integrated, normalized inequality the master proof
consumes: the fixed `guessBlock` sup integral is dominated by the double average over
`q`-subsets of the signed-rule sup integrals, plus `2/√q`. The deterministic block is gone
after this point; everything downstream is uniform in `(Q, Q')`. -/
private theorem guessBlock_sup_integral_le_avg_ruleSup (W : Graphon α μ) (ε' : ℝ) {k : ℕ}
    [NeZero k] {q : ℕ} (hq : 0 < q) (hqk : q ≤ k) :
    (∫ x, (k : ℝ)⁻¹ ^ 2 * (Finset.univ : Finset (Finset (Fin k) × Finset (Fin k))).sup'
        Finset.univ_nonempty (fun AB ↦ |∑ i ∈ AB.1 \ guessBlock k, ∑ j ∈ AB.2 \ guessBlock k,
          coreDiff W ε' x i j|) ∂Measure.pi (fun _ : Fin k ↦ μ))
      ≤ ((k.choose q : ℝ)⁻¹) ^ 2 *
          (∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
           ∑ Q' ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
            ∫ x, (k : ℝ)⁻¹ ^ 2 * (signedRules Q Q').sup' (signedRules_nonempty Q Q')
              (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2)
              ∂Measure.pi (fun _ : Fin k ↦ μ))
        + 2 / Real.sqrt q := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  set π : Measure (Fin k → α) := Measure.pi (fun _ : Fin k ↦ μ) with hπ
  -- pointwise: H1 then H9b, normalized by `k⁻²`
  have hpt : ∀ x, (k : ℝ)⁻¹ ^ 2 * (Finset.univ : Finset (Finset (Fin k) × Finset (Fin k))).sup'
        Finset.univ_nonempty (fun AB ↦ |∑ i ∈ AB.1 \ guessBlock k, ∑ j ∈ AB.2 \ guessBlock k,
          coreDiff W ε' x i j|)
      ≤ ((k.choose q : ℝ)⁻¹) ^ 2 *
          (∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
           ∑ Q' ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
            (k : ℝ)⁻¹ ^ 2 * (signedRules Q Q').sup' (signedRules_nonempty Q Q')
              (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2))
        + 2 / Real.sqrt q := by
    intro x
    have h1 := sup'_sdiff_le_sup' (coreDiff W ε' x) (guessBlock k)
    have h2 := sup'_abs_cut_le_avg_signedRuleSup hq hqk (coreDiff W ε' x)
      (coreDiff_symm W ε' x) (abs_coreDiff_le_one W ε' x)
    have hfresh := h1.trans h2
    have hmul := mul_le_mul_of_nonneg_left hfresh (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹ ^ 2)
    refine hmul.trans_eq ?_
    have hSdist : (k : ℝ)⁻¹ ^ 2 * (∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
          ∑ Q' ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
            (signedRules Q Q').sup' (signedRules_nonempty Q Q')
              (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2))
        = ∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
          ∑ Q' ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
            (k : ℝ)⁻¹ ^ 2 * (signedRules Q Q').sup' (signedRules_nonempty Q Q')
              (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun Q _ ↦ Finset.mul_sum _ _ _)
    have hk2 : (k : ℝ)⁻¹ ^ 2 * (2 * (k : ℝ) ^ 2 / Real.sqrt q) = 2 / Real.sqrt q := by
      have hcancel : (k : ℝ)⁻¹ ^ 2 * (k : ℝ) ^ 2 = 1 := by
        rw [inv_pow]; exact inv_mul_cancel₀ (pow_ne_zero 2 hkne)
      calc (k : ℝ)⁻¹ ^ 2 * (2 * (k : ℝ) ^ 2 / Real.sqrt q)
          = ((k : ℝ)⁻¹ ^ 2 * (k : ℝ) ^ 2) * (2 / Real.sqrt q) := by ring
        _ = 2 / Real.sqrt q := by rw [hcancel, one_mul]
    rw [← hSdist, mul_add, hk2]
    ring
  -- LHS integrability (the same normalized fresh-block sup as in the master proof)
  have hlhs_meas : Measurable (fun x ↦ (k : ℝ)⁻¹ ^ 2 *
      (Finset.univ : Finset (Finset (Fin k) × Finset (Fin k))).sup' Finset.univ_nonempty
        (fun AB ↦ |∑ i ∈ AB.1 \ guessBlock k, ∑ j ∈ AB.2 \ guessBlock k,
          coreDiff W ε' x i j|)) := by
    have heq : (fun x ↦ (k : ℝ)⁻¹ ^ 2 * Finset.univ.sup' Finset.univ_nonempty
        (fun AB : Finset (Fin k) × Finset (Fin k) ↦ |∑ i ∈ AB.1 \ guessBlock k,
          ∑ j ∈ AB.2 \ guessBlock k, coreDiff W ε' x i j|))
        = fun x ↦ (k : ℝ)⁻¹ ^ 2 * Finset.univ.sup' Finset.univ_nonempty
          (fun (AB : Finset (Fin k) × Finset (Fin k)) (x : Fin k → α) ↦
            |∑ i ∈ AB.1 \ guessBlock k, ∑ j ∈ AB.2 \ guessBlock k, coreDiff W ε' x i j|) x := by
      funext x; rw [Finset.sup'_apply]
    rw [heq]
    refine measurable_const.mul (Finset.measurable_sup' _ (fun AB _ ↦ ?_))
    refine continuous_abs.measurable.comp
      (Finset.measurable_sum _ (fun i _ ↦ Finset.measurable_sum _ (fun j _ ↦ ?_)))
    simp only [coreDiff]
    exact (measurable_clampEval W i j).sub (measurable_clampEval (chosenStep W ε') i j)
  have hlhs_nn : ∀ x, 0 ≤ (k : ℝ)⁻¹ ^ 2 * Finset.univ.sup' Finset.univ_nonempty
      (fun AB : Finset (Fin k) × Finset (Fin k) ↦ |∑ i ∈ AB.1 \ guessBlock k,
        ∑ j ∈ AB.2 \ guessBlock k, coreDiff W ε' x i j|) := by
    intro x
    refine mul_nonneg (by positivity) (le_trans (abs_nonneg _)
      (Finset.le_sup' (fun AB : Finset (Fin k) × Finset (Fin k) ↦
        |∑ i ∈ AB.1 \ guessBlock k, ∑ j ∈ AB.2 \ guessBlock k, coreDiff W ε' x i j|)
        (Finset.mem_univ ((∅, ∅) : Finset (Fin k) × Finset (Fin k)))))
  have hlhs_le : ∀ x, (k : ℝ)⁻¹ ^ 2 * Finset.univ.sup' Finset.univ_nonempty
      (fun AB : Finset (Fin k) × Finset (Fin k) ↦ |∑ i ∈ AB.1 \ guessBlock k,
        ∑ j ∈ AB.2 \ guessBlock k, coreDiff W ε' x i j|) ≤ 1 := by
    intro x
    have hsup : Finset.univ.sup' Finset.univ_nonempty
        (fun AB : Finset (Fin k) × Finset (Fin k) ↦ |∑ i ∈ AB.1 \ guessBlock k,
          ∑ j ∈ AB.2 \ guessBlock k, coreDiff W ε' x i j|) ≤ (k : ℝ) ^ 2 := by
      refine Finset.sup'_le _ _ (fun AB _ ↦ ?_)
      refine (abs_coreDiff_rect_le W ε' x _ _).trans ?_
      have hc : ∀ S : Finset (Fin k), ((S \ guessBlock k).card : ℝ) ≤ k := by
        intro S
        calc ((S \ guessBlock k).card : ℝ)
            ≤ ((Finset.univ : Finset (Fin k)).card : ℝ) := by
              exact_mod_cast Finset.card_le_card (Finset.subset_univ _)
          _ = k := by rw [Finset.card_univ, Fintype.card_fin]
      calc ((AB.1 \ guessBlock k).card : ℝ) * ((AB.2 \ guessBlock k).card : ℝ)
          ≤ (k : ℝ) * k := mul_le_mul (hc _) (hc _) (by positivity) (by positivity)
        _ = (k : ℝ) ^ 2 := by ring
    calc (k : ℝ)⁻¹ ^ 2 * _
        ≤ (k : ℝ)⁻¹ ^ 2 * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsup (by positivity)
      _ = 1 := by field_simp
  have hint_lhs : Integrable (fun x ↦ (k : ℝ)⁻¹ ^ 2 *
      (Finset.univ : Finset (Finset (Fin k) × Finset (Fin k))).sup' Finset.univ_nonempty
        (fun AB ↦ |∑ i ∈ AB.1 \ guessBlock k, ∑ j ∈ AB.2 \ guessBlock k,
          coreDiff W ε' x i j|)) π :=
    (integrable_const (1 : ℝ)).mono' hlhs_meas.aestronglyMeasurable
      (ae_of_all _ (fun x ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (hlhs_nn x)]; exact hlhs_le x))
  -- rule-sup integrability, uniformly bounded by `1`
  have hrule_meas : ∀ Q Q' : Finset (Fin k), Measurable (fun x ↦ (k : ℝ)⁻¹ ^ 2 *
      (signedRules Q Q').sup' (signedRules_nonempty Q Q')
        (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2)) := by
    intro Q Q'
    have heq : (fun x ↦ (k : ℝ)⁻¹ ^ 2 * (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2))
        = fun x ↦ (k : ℝ)⁻¹ ^ 2 * (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun (ρ : Bool × Finset (Fin k) × Finset (Fin k)) (x : Fin k → α) ↦
            ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2) x := by
      funext x; rw [Finset.sup'_apply]
    rw [heq]
    exact measurable_const.mul (Finset.measurable_sup' _
      (fun ρ _ ↦ measurable_ruleVal_sample W ε' ρ.1 ρ.2.1 ρ.2.2))
  have hrule_bound : ∀ (Q Q' : Finset (Fin k)) (x : Fin k → α),
      |(k : ℝ)⁻¹ ^ 2 * (signedRules Q Q').sup' (signedRules_nonempty Q Q')
        (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2)| ≤ 1 := by
    intro Q Q' x
    have habs : ∀ ρ : Bool × Finset (Fin k) × Finset (Fin k),
        |ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2| ≤ (k : ℝ) ^ 2 := by
      intro ρ
      refine abs_ruleVal_le _ (fun i j ↦ ?_) _ _
      rw [abs_mul, abs_sgnR, one_mul]
      exact abs_coreDiff_le_one W ε' x i j
    have hup : (signedRules Q Q').sup' (signedRules_nonempty Q Q')
        (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2) ≤ (k : ℝ) ^ 2 :=
      Finset.sup'_le _ _ (fun ρ _ ↦ (le_abs_self _).trans (habs ρ))
    have hlow : -(k : ℝ) ^ 2 ≤ (signedRules Q Q').sup' (signedRules_nonempty Q Q')
        (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2) := by
      obtain ⟨ρ₀, hρ₀⟩ := signedRules_nonempty Q Q'
      refine le_trans ?_ (Finset.le_sup' _ hρ₀)
      exact (neg_le_neg (habs ρ₀)).trans (neg_abs_le _)
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹ ^ 2)]
    calc (k : ℝ)⁻¹ ^ 2 * |(signedRules Q Q').sup' (signedRules_nonempty Q Q')
            (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2)|
        ≤ (k : ℝ)⁻¹ ^ 2 * (k : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hlow, hup⟩) (by positivity)
      _ = 1 := by field_simp
  have hint_rule : ∀ Q Q' : Finset (Fin k), Integrable (fun x ↦ (k : ℝ)⁻¹ ^ 2 *
      (signedRules Q Q').sup' (signedRules_nonempty Q Q')
        (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2)) π := by
    intro Q Q'
    exact (integrable_const (1 : ℝ)).mono' (hrule_meas Q Q').aestronglyMeasurable
      (ae_of_all _ (fun x ↦ by rw [Real.norm_eq_abs]; exact hrule_bound Q Q' x))
  -- integrate the pointwise bound and evaluate the constant/sum integrals
  have hsum_int : Integrable (fun x ↦
      ∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
      ∑ Q' ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
        (k : ℝ)⁻¹ ^ 2 * (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2)) π :=
    integrable_finsetSum _ (fun Q _ ↦ integrable_finsetSum _ (fun Q' _ ↦ hint_rule Q Q'))
  have hint_rhs : Integrable (fun x ↦ ((k.choose q : ℝ)⁻¹) ^ 2 *
      (∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
       ∑ Q' ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
        (k : ℝ)⁻¹ ^ 2 * (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2))
      + 2 / Real.sqrt q) π :=
    (hsum_int.const_mul _).add (integrable_const _)
  calc ∫ x, (k : ℝ)⁻¹ ^ 2 * (Finset.univ : Finset (Finset (Fin k) × Finset (Fin k))).sup'
        Finset.univ_nonempty (fun AB ↦ |∑ i ∈ AB.1 \ guessBlock k, ∑ j ∈ AB.2 \ guessBlock k,
          coreDiff W ε' x i j|) ∂π
      ≤ ∫ x, (((k.choose q : ℝ)⁻¹) ^ 2 *
          (∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
           ∑ Q' ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
            (k : ℝ)⁻¹ ^ 2 * (signedRules Q Q').sup' (signedRules_nonempty Q Q')
              (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2))
          + 2 / Real.sqrt q) ∂π := integral_mono hint_lhs hint_rhs hpt
    _ = ((k.choose q : ℝ)⁻¹) ^ 2 *
          (∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
           ∑ Q' ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
            ∫ x, (k : ℝ)⁻¹ ^ 2 * (signedRules Q Q').sup' (signedRules_nonempty Q Q')
              (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2) ∂π)
        + 2 / Real.sqrt q := by
        rw [integral_add (hsum_int.const_mul _) (integrable_const _), integral_const_mul,
          integral_const, smul_eq_mul, probReal_univ, one_mul,
          integral_finsetSum _ (fun Q _ ↦ integrable_finsetSum _ (fun Q' _ ↦ hint_rule Q Q'))]
        refine congrArg (fun t ↦ ((k.choose q : ℝ)⁻¹) ^ 2 * t + 2 / Real.sqrt q) ?_
        exact Finset.sum_congr rfl (fun Q _ ↦
          integral_finsetSum _ (fun Q' _ ↦ hint_rule Q Q'))

/-! ##### Conditioning on a block (Layer 2) -/

/-- Glue a block assignment `y` and a fresh assignment `z` into a full sample; this is
`(MeasurableEquiv.piEquivPiSubtypeProd _ (· ∈ B)).symm (y, z)` in explicit form (H11a). -/
private noncomputable def blockGlue {k : ℕ} (B : Finset (Fin k))
    (y : {l : Fin k // l ∈ B} → α) (z : {l : Fin k // ¬ l ∈ B} → α) : Fin k → α :=
  fun i ↦ if h : i ∈ B then y ⟨i, h⟩ else z ⟨i, h⟩

omit [StandardBorelSpace α] [NullSingletonClass μ] in
/-- (H11a) The block-splitting equivalence, coordinatewise. -/
private theorem piEquivPiSubtypeProd_symm_eq_blockGlue {k : ℕ} (B : Finset (Fin k))
    (y : {l : Fin k // l ∈ B} → α) (z : {l : Fin k // ¬ l ∈ B} → α) :
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin k ↦ α) (· ∈ B)).symm (y, z)
      = blockGlue B y z := by
  funext i
  simp only [blockGlue, MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.symm_mk,
    MeasurableEquiv.coe_mk, Equiv.piEquivPiSubtypeProd_symm_apply]

/-- (H10) The rule value as a double sum of indicator-weighted entries — the form whose
conditional expectation Layer 2 computes. -/
private theorem ruleVal_eq_sum_ite {k : ℕ} (m : Fin k → Fin k → ℝ) (R R' : Finset (Fin k)) :
    ruleVal m R R' = ∑ i, ∑ j,
      (if 0 < ∑ j' ∈ R', m i j' then (1 : ℝ) else 0) *
      (if 0 < ∑ j' ∈ R, m j j' then (1 : ℝ) else 0) * m i j := by
  simp only [ruleVal, signSet, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hP : 0 < ∑ j' ∈ R', m i j'
  · simp only [hP, if_true, one_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hQ : 0 < ∑ j' ∈ R, m j j' <;> simp [hQ]
  · simp [hP]

omit [StandardBorelSpace α] [NullSingletonClass μ] in
/-- The pushforward of a product measure under the two-coordinate evaluation map at distinct
indices `a ≠ b` (over an arbitrary finite index type) is `μ.prod μ`. Generalizes the map
computation inside `ae_pairMap_of_prod` to an arbitrary `Fintype` index. -/
private theorem pairMap_map_prod {ι : Type*} [Fintype ι] {a b : ι} (hab : a ≠ b) :
    Measure.map (fun x : ι → α ↦ (x a, x b)) (Measure.pi (fun _ : ι ↦ μ)) = μ.prod μ := by
  have h_indep : ProbabilityTheory.iIndepFun (fun l (x : ι → α) ↦ x l)
      (Measure.pi (fun _ : ι ↦ μ)) :=
    ProbabilityTheory.iIndepFun_pi (fun _ ↦ aemeasurable_id)
  have h_indep_pair := h_indep.indepFun hab
  rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_apply _).aemeasurable (measurable_pi_apply _).aemeasurable] at h_indep_pair
  rw [show (fun x : ι → α ↦ (x a, x b))
        = fun x ↦ ((fun x : ι → α ↦ x a) x, (fun x : ι → α ↦ x b) x) from rfl,
    h_indep_pair, (MeasureTheory.measurePreserving_eval (fun _ : ι ↦ μ) a).map_eq,
    (MeasureTheory.measurePreserving_eval (fun _ : ι ↦ μ) b).map_eq]

omit [StandardBorelSpace α] [NullSingletonClass μ] in
/-- (H11b, absolute version) **Fresh-pair section bound.** For a fixed signed rule generated
inside the block `B` and a fresh ordered pair `i ≠ j`, the fresh-sample average of the
indicator-weighted entry is a rectangle integral of `W − chosenStep W ε'` over measurable
rule sets, hence at most `cutNormDiff` in absolute value, for a.e. block assignment. -/
private theorem abs_integral_pairRule_le (W : Graphon α μ) (ε' : ℝ) {k : ℕ}
    (B : Finset (Fin k)) (s : Bool) {R R' : Finset (Fin k)} (hR : R ⊆ B) (hR' : R' ⊆ B)
    {i j : Fin k} (hi : ¬ i ∈ B) (hj : ¬ j ∈ B) (hij : i ≠ j) :
    ∀ᵐ y ∂(Measure.pi (fun _ : {l : Fin k // l ∈ B} ↦ μ)),
      |∫ z, (if 0 < ∑ j' ∈ R', sgnR s * coreDiff W ε' (blockGlue B y z) i j' then (1 : ℝ)
              else 0)
          * (if 0 < ∑ j' ∈ R, sgnR s * coreDiff W ε' (blockGlue B y z) j j' then (1 : ℝ)
              else 0)
          * coreDiff W ε' (blockGlue B y z) i j
          ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))|
        ≤ cutNormDiff W (chosenStep W ε') := by
  classical
  refine ae_of_all _ (fun y ↦ ?_)
  haveI : Nonempty α := by
    by_contra h; rw [not_nonempty_iff] at h
    exact absurd (Measure.eq_zero_of_isEmpty μ) (IsProbabilityMeasure.ne_zero μ)
  set b₀ : α := Classical.arbitrary α with hb₀
  set z₀ : {l : Fin k // ¬ l ∈ B} → α := fun _ ↦ b₀ with hz₀
  set glue : α → α → ({l : Fin k // ¬ l ∈ B} → α) :=
    fun a b ↦ Function.update (Function.update z₀ ⟨i, hi⟩ a) ⟨j, hj⟩ b with hglue_def
  have hne : (⟨i, hi⟩ : {l : Fin k // ¬ l ∈ B}) ≠ ⟨j, hj⟩ := by
    intro h; exact hij (congr_arg Subtype.val h)
  have hglue_i : ∀ a b, glue a b ⟨i, hi⟩ = a := by
    intro a b; simp only [hglue_def, Function.update_of_ne hne, Function.update_self]
  have hglue_j : ∀ a b, glue a b ⟨j, hj⟩ = b := by
    intro a b; simp only [hglue_def, Function.update_self]
  -- Measurability toolkit
  have hcoreM : ∀ (a b : Fin k), Measurable (fun x : Fin k → α ↦ coreDiff W ε' x a b) := by
    intro a b; simp only [coreDiff]
    exact (measurable_clampEval W a b).sub (measurable_clampEval (chosenStep W ε') a b)
  have hbgm : Measurable (fun w : {l : Fin k // ¬ l ∈ B} → α ↦ blockGlue B y w) := by
    rw [measurable_pi_iff]; intro l
    simp only [blockGlue]
    by_cases hl : l ∈ B
    · simp only [dif_pos hl]; exact measurable_const
    · simp only [dif_neg hl]; exact measurable_pi_apply _
  -- Locality of `blockGlue ∘ glue` vs `blockGlue B y z` at the read coordinates
  have hbi : ∀ z : {l // ¬ l ∈ B} → α,
      blockGlue B y (glue (z ⟨i, hi⟩) (z ⟨j, hj⟩)) i = blockGlue B y z i := by
    intro z; simp only [blockGlue, dif_neg hi, hglue_i]
  have hbj : ∀ z : {l // ¬ l ∈ B} → α,
      blockGlue B y (glue (z ⟨i, hi⟩) (z ⟨j, hj⟩)) j = blockGlue B y z j := by
    intro z; simp only [blockGlue, dif_neg hj, hglue_j]
  have hbblock : ∀ (z : {l // ¬ l ∈ B} → α) (l : Fin k), l ∈ B →
      blockGlue B y (glue (z ⟨i, hi⟩) (z ⟨j, hj⟩)) l = blockGlue B y z l := by
    intro z l hl; simp only [blockGlue, dif_pos hl]
  -- The two-coordinate reduction of the integrand
  set Ψ : α × α → ℝ := fun p ↦
    (if 0 < ∑ j' ∈ R', sgnR s * coreDiff W ε' (blockGlue B y (glue p.1 p.2)) i j' then (1 : ℝ)
        else 0)
    * (if 0 < ∑ j' ∈ R, sgnR s * coreDiff W ε' (blockGlue B y (glue p.1 p.2)) j j' then (1 : ℝ)
        else 0)
    * coreDiff W ε' (blockGlue B y (glue p.1 p.2)) i j with hΨ_def
  have hΦ : ∀ z : {l // ¬ l ∈ B} → α,
      (if 0 < ∑ j' ∈ R', sgnR s * coreDiff W ε' (blockGlue B y z) i j' then (1 : ℝ) else 0)
      * (if 0 < ∑ j' ∈ R, sgnR s * coreDiff W ε' (blockGlue B y z) j j' then (1 : ℝ) else 0)
      * coreDiff W ε' (blockGlue B y z) i j
      = Ψ (z ⟨i, hi⟩, z ⟨j, hj⟩) := by
    intro z
    have erow_sum : (∑ j' ∈ R', sgnR s * coreDiff W ε' (blockGlue B y z) i j')
        = ∑ j' ∈ R', sgnR s
            * coreDiff W ε' (blockGlue B y (glue (z ⟨i, hi⟩) (z ⟨j, hj⟩))) i j' :=
      Finset.sum_congr rfl (fun j' hj' ↦ by
        rw [coreDiff_congr W ε' (hbi z).symm (hbblock z j' (hR' hj')).symm])
    have ecol_sum : (∑ j' ∈ R, sgnR s * coreDiff W ε' (blockGlue B y z) j j')
        = ∑ j' ∈ R, sgnR s
            * coreDiff W ε' (blockGlue B y (glue (z ⟨i, hi⟩) (z ⟨j, hj⟩))) j j' :=
      Finset.sum_congr rfl (fun j' hj' ↦ by
        rw [coreDiff_congr W ε' (hbj z).symm (hbblock z j' (hR hj')).symm])
    have eentry : coreDiff W ε' (blockGlue B y z) i j
        = coreDiff W ε' (blockGlue B y (glue (z ⟨i, hi⟩) (z ⟨j, hj⟩))) i j :=
      coreDiff_congr W ε' (hbi z).symm (hbj z).symm
    simp only [hΨ_def]
    rw [erow_sum, ecol_sum, eentry]
  -- Ψ is measurable
  have hgluepM : Measurable (fun p : α × α ↦ glue p.1 p.2) := by
    simp only [hglue_def]
    exact (measurable_update' (a := (⟨j, hj⟩ : {l // ¬ l ∈ B}))).comp
      (((measurable_update z₀ (a := (⟨i, hi⟩ : {l // ¬ l ∈ B}))).comp measurable_fst).prodMk
        measurable_snd)
  have hΨ_meas : Measurable Ψ := by
    simp only [hΨ_def]
    refine Measurable.mul (Measurable.mul ?_ ?_) ((hcoreM i j).comp (hbgm.comp hgluepM))
    · refine Measurable.ite (measurableSet_lt measurable_const ?_) measurable_const measurable_const
      exact Finset.measurable_sum _
        (fun j' _ ↦ ((hcoreM i j').comp (hbgm.comp hgluepM)).const_mul _)
    · refine Measurable.ite (measurableSet_lt measurable_const ?_) measurable_const measurable_const
      exact Finset.measurable_sum _
        (fun j' _ ↦ ((hcoreM j j').comp (hbgm.comp hgluepM)).const_mul _)
  -- Rewrite the integral: integrand → Ψ(z i, z j) → pushforward to μ.prod μ
  have hmap : Measure.map (fun z : {l // ¬ l ∈ B} → α ↦ (z ⟨i, hi⟩, z ⟨j, hj⟩))
      (Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)) = μ.prod μ := pairMap_map_prod hne
  have hpush : (∫ z, Ψ (z ⟨i, hi⟩, z ⟨j, hj⟩)
        ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)))
      = ∫ p, Ψ p ∂(μ.prod μ) := by
    have hmm := MeasureTheory.integral_map
      (μ := Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))
      (φ := fun z : {l // ¬ l ∈ B} → α ↦ (z ⟨i, hi⟩, z ⟨j, hj⟩))
      (f := Ψ)
      ((measurable_pi_apply _).prodMk (measurable_pi_apply _)).aemeasurable
      hΨ_meas.aestronglyMeasurable
    rw [hmap] at hmm
    exact hmm.symm
  rw [integral_congr_ae (ae_of_all _ hΦ), hpush]
  -- Measurable rule sets
  set S₁ : Set α :=
    {a | 0 < ∑ j' ∈ R', sgnR s * coreDiff W ε' (blockGlue B y (glue a b₀)) i j'} with hS₁_def
  set S₂ : Set α :=
    {b | 0 < ∑ j' ∈ R, sgnR s * coreDiff W ε' (blockGlue B y (glue b₀ b)) j j'} with hS₂_def
  have hgluecolM : Measurable (fun a : α ↦ glue a b₀) := by
    simp only [hglue_def]
    exact (measurable_update_left (a := (⟨j, hj⟩ : {l // ¬ l ∈ B})) (x := b₀)).comp
      (measurable_update z₀ (a := (⟨i, hi⟩ : {l // ¬ l ∈ B})))
  have hgluerowM : Measurable (fun b : α ↦ glue b₀ b) := by
    simp only [hglue_def]
    exact measurable_update (Function.update z₀ ⟨i, hi⟩ b₀) (a := (⟨j, hj⟩ : {l // ¬ l ∈ B}))
  have hS₁ : MeasurableSet S₁ := by
    apply measurableSet_lt measurable_const
    exact Finset.measurable_sum _
      (fun j' _ ↦ ((hcoreM i j').comp (hbgm.comp hgluecolM)).const_mul _)
  have hS₂ : MeasurableSet S₂ := by
    apply measurableSet_lt measurable_const
    exact Finset.measurable_sum _
      (fun j' _ ↦ ((hcoreM j j').comp (hbgm.comp hgluerowM)).const_mul _)
  -- The indicator conditions read only the relevant coordinate
  have hg₁eq : ∀ p : α × α,
      (0 < ∑ j' ∈ R', sgnR s * coreDiff W ε' (blockGlue B y (glue p.1 p.2)) i j') ↔ p.1 ∈ S₁ := by
    intro p
    simp only [hS₁_def, Set.mem_setOf_eq]
    rw [Finset.sum_congr rfl (fun j' hj' ↦ by
      rw [coreDiff_congr W ε'
        (show blockGlue B y (glue p.1 p.2) i = blockGlue B y (glue p.1 b₀) i by
          simp only [blockGlue, dif_neg hi, hglue_i])
        (show blockGlue B y (glue p.1 p.2) j' = blockGlue B y (glue p.1 b₀) j' by
          simp only [blockGlue, dif_pos (hR' hj')])])]
  have hg₂eq : ∀ p : α × α,
      (0 < ∑ j' ∈ R, sgnR s * coreDiff W ε' (blockGlue B y (glue p.1 p.2)) j j') ↔ p.2 ∈ S₂ := by
    intro p
    simp only [hS₂_def, Set.mem_setOf_eq]
    rw [Finset.sum_congr rfl (fun j' hj' ↦ by
      rw [coreDiff_congr W ε'
        (show blockGlue B y (glue p.1 p.2) j = blockGlue B y (glue b₀ p.2) j by
          simp only [blockGlue, dif_neg hj, hglue_j])
        (show blockGlue B y (glue p.1 p.2) j' = blockGlue B y (glue b₀ p.2) j' by
          simp only [blockGlue, dif_pos (hR hj')])])]
  -- A.e. clamp transparency over `μ.prod μ`
  have hclampW : ∀ᵐ p ∂(μ.prod μ), min 1 (max 0 (W.toAEEqFun p)) = W.toAEEqFun p := by
    filter_upwards [W.ae_mem_Icc] with p hp; rw [max_eq_right hp.1, min_eq_right hp.2]
  have hclampU : ∀ᵐ p ∂(μ.prod μ),
      min 1 (max 0 ((chosenStep W ε').toAEEqFun p)) = (chosenStep W ε').toAEEqFun p := by
    filter_upwards [(chosenStep W ε').ae_mem_Icc] with p hp
    rw [max_eq_right hp.1, min_eq_right hp.2]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · -- i < j : identity orientation
    have hΨrep : ∀ᵐ p ∂(μ.prod μ), Ψ p =
        (S₁ ×ˢ S₂).indicator
          (fun q ↦ W.toAEEqFun q - (chosenStep W ε').toAEEqFun q) p := by
      filter_upwards [hclampW, hclampU] with p hW hU
      have hbgi : blockGlue B y (glue p.1 p.2) i = p.1 := by
        simp only [blockGlue, dif_neg hi, hglue_i]
      have hbgj : blockGlue B y (glue p.1 p.2) j = p.2 := by
        simp only [blockGlue, dif_neg hj, hglue_j]
      have hentry : coreDiff W ε' (blockGlue B y (glue p.1 p.2)) i j
          = W.toAEEqFun p - (chosenStep W ε').toAEEqFun p := by
        simp only [coreDiff, clampEval, min_eq_left hlt.le, max_eq_right hlt.le, hbgi, hbgj,
          Prod.mk.eta]
        rw [hW, hU]
      simp only [hΨ_def]
      rw [hentry]
      by_cases h1 : p.1 ∈ S₁ <;> by_cases h2 : p.2 ∈ S₂ <;>
        simp [Set.mem_prod, hg₁eq p, hg₂eq p, h1, h2]
    calc |∫ p, Ψ p ∂(μ.prod μ)|
        = |∫ p, (S₁ ×ˢ S₂).indicator
              (fun q ↦ W.toAEEqFun q - (chosenStep W ε').toAEEqFun q) p ∂(μ.prod μ)| := by
          rw [integral_congr_ae hΨrep]
      _ = |rectIntegralDiff W (chosenStep W ε') S₁ S₂| := by
          rw [integral_indicator (hS₁.prod hS₂)]; rfl
      _ ≤ cutNormDiff W (chosenStep W ε') := abs_rectIntegralDiff_le W _ hS₁ hS₂
  · -- j < i : swapped orientation
    have hclampW_swap : ∀ᵐ p ∂(μ.prod μ),
        min 1 (max 0 (W.toAEEqFun (p.2, p.1))) = W.toAEEqFun (p.2, p.1) :=
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hclampW
    have hclampU_swap : ∀ᵐ p ∂(μ.prod μ),
        min 1 (max 0 ((chosenStep W ε').toAEEqFun (p.2, p.1)))
          = (chosenStep W ε').toAEEqFun (p.2, p.1) :=
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hclampU
    have hΨrep : ∀ᵐ p ∂(μ.prod μ), Ψ p =
        (S₂ ×ˢ S₁).indicator
          (fun q ↦ W.toAEEqFun q - (chosenStep W ε').toAEEqFun q) (Prod.swap p) := by
      filter_upwards [hclampW_swap, hclampU_swap] with p hW hU
      have hbgi : blockGlue B y (glue p.1 p.2) i = p.1 := by
        simp only [blockGlue, dif_neg hi, hglue_i]
      have hbgj : blockGlue B y (glue p.1 p.2) j = p.2 := by
        simp only [blockGlue, dif_neg hj, hglue_j]
      have hentry : coreDiff W ε' (blockGlue B y (glue p.1 p.2)) i j
          = W.toAEEqFun (p.2, p.1) - (chosenStep W ε').toAEEqFun (p.2, p.1) := by
        simp only [coreDiff, clampEval, min_eq_right hgt.le, max_eq_left hgt.le, hbgi, hbgj]
        rw [hW, hU]
      have hsw : Prod.swap p = (p.2, p.1) := rfl
      simp only [hΨ_def]
      rw [hentry]
      by_cases h1 : p.1 ∈ S₁ <;> by_cases h2 : p.2 ∈ S₂ <;>
        simp [Set.mem_prod, hsw, hg₁eq p, hg₂eq p, h1, h2]
    calc |∫ p, Ψ p ∂(μ.prod μ)|
        = |∫ p, (S₂ ×ˢ S₁).indicator
              (fun q ↦ W.toAEEqFun q - (chosenStep W ε').toAEEqFun q) (Prod.swap p)
              ∂(μ.prod μ)| := by rw [integral_congr_ae hΨrep]
      _ = |∫ p, (S₂ ×ˢ S₁).indicator
              (fun q ↦ W.toAEEqFun q - (chosenStep W ε').toAEEqFun q) p ∂(μ.prod μ)| := by
          rw [MeasureTheory.integral_prod_swap]
      _ = |rectIntegralDiff W (chosenStep W ε') S₂ S₁| := by
          rw [integral_indicator (hS₂.prod hS₁)]; rfl
      _ ≤ cutNormDiff W (chosenStep W ε') := abs_rectIntegralDiff_le W _ hS₂ hS₁

omit [StandardBorelSpace α] [NullSingletonClass μ] in
/-- (H11c) **Conditional mean of a fixed rule.** Classifying entries as fresh off-diagonal
(≤ `k²`, each ≤ `cutNormDiff` by H11b), block-touching (≤ `2|B|k`, each ≤ 1), and diagonal
(≤ `k`, each ≤ 1). -/
private theorem ae_integral_ruleVal_le (W : Graphon α μ) (ε' : ℝ) {k : ℕ} [NeZero k]
    (B : Finset (Fin k)) (s : Bool) {R R' : Finset (Fin k)} (hR : R ⊆ B) (hR' : R' ⊆ B) :
    ∀ᵐ y ∂(Measure.pi (fun _ : {l : Fin k // l ∈ B} ↦ μ)),
      (∫ z, ruleVal (fun i j ↦ sgnR s * coreDiff W ε' (blockGlue B y z) i j) R R'
          ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)))
        ≤ (k : ℝ) ^ 2 * cutNormDiff W (chosenStep W ε') + 2 * (B.card : ℝ) * k + k := by
  classical
  set πF := Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ) with hπF
  -- Gather the fresh off-diagonal bounds (H11b) into a single a.e. statement over `y`.
  have hpair : ∀ᵐ y ∂(Measure.pi (fun _ : {l : Fin k // l ∈ B} ↦ μ)),
      ∀ q : Fin k × Fin k, q.1 ∉ B → q.2 ∉ B → q.1 ≠ q.2 →
        |∫ z, (if 0 < ∑ j' ∈ R', sgnR s * coreDiff W ε' (blockGlue B y z) q.1 j' then (1 : ℝ)
                else 0)
            * (if 0 < ∑ j' ∈ R, sgnR s * coreDiff W ε' (blockGlue B y z) q.2 j' then (1 : ℝ)
                else 0)
            * coreDiff W ε' (blockGlue B y z) q.1 q.2 ∂πF|
          ≤ cutNormDiff W (chosenStep W ε') := by
    rw [ae_all_iff]
    rintro ⟨i, j⟩
    by_cases hcond : i ∉ B ∧ j ∉ B ∧ i ≠ j
    · filter_upwards [abs_integral_pairRule_le W ε' B s hR hR' hcond.1 hcond.2.1 hcond.2.2]
        with y hy _ _ _
      exact hy
    · exact ae_of_all _ (fun y hi hj hij ↦ absurd ⟨hi, hj, hij⟩ hcond)
  filter_upwards [hpair] with y hy
  -- Measurability toolkit (y fixed)
  have hbgm : Measurable (fun w : {l : Fin k // ¬ l ∈ B} → α ↦ blockGlue B y w) := by
    rw [measurable_pi_iff]; intro l
    simp only [blockGlue]
    by_cases hl : l ∈ B
    · simp only [dif_pos hl]; exact measurable_const
    · simp only [dif_neg hl]; exact measurable_pi_apply _
  have hcz : ∀ (a b : Fin k), Measurable (fun z ↦ coreDiff W ε' (blockGlue B y z) a b) := by
    intro a b
    simp only [coreDiff]
    exact ((measurable_clampEval W a b).sub (measurable_clampEval (chosenStep W ε') a b)).comp hbgm
  -- The double-sum term
  set term : ({l : Fin k // ¬ l ∈ B} → α) → Fin k → Fin k → ℝ := fun z i j ↦
    (if 0 < ∑ j' ∈ R', sgnR s * coreDiff W ε' (blockGlue B y z) i j' then (1 : ℝ) else 0)
    * (if 0 < ∑ j' ∈ R, sgnR s * coreDiff W ε' (blockGlue B y z) j j' then (1 : ℝ) else 0)
    * (sgnR s * coreDiff W ε' (blockGlue B y z) i j) with hterm_def
  have habs_term : ∀ z i j, |term z i j| ≤ 1 := by
    intro z i j
    simp only [hterm_def]
    rw [abs_mul, abs_mul, abs_mul, abs_sgnR, one_mul]
    have hA : |(if 0 < ∑ j' ∈ R', sgnR s * coreDiff W ε' (blockGlue B y z) i j' then (1 : ℝ)
        else 0)| ≤ 1 := by split_ifs <;> simp
    have hB : |(if 0 < ∑ j' ∈ R, sgnR s * coreDiff W ε' (blockGlue B y z) j j' then (1 : ℝ)
        else 0)| ≤ 1 := by split_ifs <;> simp
    exact mul_le_one₀ (mul_le_one₀ hA (abs_nonneg _) hB) (abs_nonneg _)
      (abs_coreDiff_le_one W ε' _ i j)
  have hterm_meas : ∀ i j, Measurable (fun z ↦ term z i j) := by
    intro i j
    simp only [hterm_def]
    refine Measurable.mul (Measurable.mul ?_ ?_) ((hcz i j).const_mul _)
    · exact Measurable.ite (measurableSet_lt measurable_const
        (Finset.measurable_sum _ (fun j' _ ↦ (hcz i j').const_mul _))) measurable_const
        measurable_const
    · exact Measurable.ite (measurableSet_lt measurable_const
        (Finset.measurable_sum _ (fun j' _ ↦ (hcz j j').const_mul _))) measurable_const
        measurable_const
  have hterm_int : ∀ i j, Integrable (fun z ↦ term z i j) πF := fun i j ↦
    (integrable_const 1).mono' (hterm_meas i j).aestronglyMeasurable
      (ae_of_all _ (fun z ↦ by rw [Real.norm_eq_abs]; exact habs_term z i j))
  -- ∫ ruleVal = ∑∑ ∫ term
  have hswap : (∫ z, ruleVal (fun i j ↦ sgnR s * coreDiff W ε' (blockGlue B y z) i j) R R' ∂πF)
      = ∑ i, ∑ j, ∫ z, term z i j ∂πF := by
    have hpt : ∀ z, ruleVal (fun i j ↦ sgnR s * coreDiff W ε' (blockGlue B y z) i j) R R'
        = ∑ i, ∑ j, term z i j := by
      intro z; rw [ruleVal_eq_sum_ite]
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hterm_int i j))]
    exact Finset.sum_congr rfl (fun i _ ↦ integral_finsetSum _ (fun j _ ↦ hterm_int i j))
  rw [hswap]
  -- Per-pair upper bound
  set RP : Fin k → Fin k → ℝ := fun i j ↦
    (if i ∉ B ∧ j ∉ B ∧ i ≠ j then cutNormDiff W (chosenStep W ε') else 0)
    + (if i ∈ B then (1 : ℝ) else 0) + (if j ∈ B then (1 : ℝ) else 0)
    + (if i = j then (1 : ℝ) else 0) with hRP
  have hpp : ∀ i j : Fin k, (∫ z, term z i j ∂πF) ≤ RP i j := by
    intro i j
    have hb1 : |∫ z, term z i j ∂πF| ≤ 1 := by
      calc |∫ z, term z i j ∂πF| ≤ ∫ z, |term z i j| ∂πF := abs_integral_le_integral_abs
        _ ≤ ∫ _z, (1 : ℝ) ∂πF :=
            integral_mono (hterm_int i j).abs (integrable_const 1) (fun z ↦ habs_term z i j)
        _ = 1 := by simp
    by_cases hcond : i ∉ B ∧ j ∉ B ∧ i ≠ j
    · have hterm_eq : (fun z ↦ term z i j) = fun z ↦ sgnR s *
          ((if 0 < ∑ j' ∈ R', sgnR s * coreDiff W ε' (blockGlue B y z) i j' then (1 : ℝ) else 0)
            * (if 0 < ∑ j' ∈ R, sgnR s * coreDiff W ε' (blockGlue B y z) j j' then (1 : ℝ) else 0)
            * coreDiff W ε' (blockGlue B y z) i j) := by
        funext z; simp only [hterm_def]; ring
      have hle : (∫ z, term z i j ∂πF) ≤ cutNormDiff W (chosenStep W ε') := by
        rw [show (∫ z, term z i j ∂πF)
              = sgnR s * ∫ z, (if 0 < ∑ j' ∈ R', sgnR s * coreDiff W ε' (blockGlue B y z) i j'
                    then (1 : ℝ) else 0)
                * (if 0 < ∑ j' ∈ R, sgnR s * coreDiff W ε' (blockGlue B y z) j j' then (1 : ℝ)
                    else 0)
                * coreDiff W ε' (blockGlue B y z) i j ∂πF from by
            rw [hterm_eq]; exact integral_const_mul _ _]
        calc sgnR s * ∫ z, _ ∂πF ≤ |sgnR s * ∫ z, _ ∂πF| := le_abs_self _
          _ = |∫ z, _ ∂πF| := by rw [abs_mul, abs_sgnR, one_mul]
          _ ≤ cutNormDiff W (chosenStep W ε') := hy (i, j) hcond.1 hcond.2.1 hcond.2.2
      simp only [hRP, if_pos hcond, if_neg hcond.1, if_neg hcond.2.1, if_neg hcond.2.2, add_zero]
      exact hle
    · have hb1' : (∫ z, term z i j ∂πF) ≤ 1 := (le_abs_self _).trans hb1
      have hor : i ∈ B ∨ j ∈ B ∨ i = j := by
        by_contra h; rw [not_or, not_or] at h; exact hcond ⟨h.1, h.2.1, h.2.2⟩
      have hge : (1 : ℝ) ≤ (if i ∈ B then (1 : ℝ) else 0) + (if j ∈ B then (1 : ℝ) else 0)
          + (if i = j then (1 : ℝ) else 0) := by
        rcases hor with h | h | h
        · rw [if_pos h]
          have : (0 : ℝ) ≤ (if j ∈ B then (1 : ℝ) else 0) + (if i = j then (1 : ℝ) else 0) := by
            positivity
          linarith
        · rw [if_pos h]
          have : (0 : ℝ) ≤ (if i ∈ B then (1 : ℝ) else 0) + (if i = j then (1 : ℝ) else 0) := by
            positivity
          linarith
        · rw [if_pos h]
          have : (0 : ℝ) ≤ (if i ∈ B then (1 : ℝ) else 0) + (if j ∈ B then (1 : ℝ) else 0) := by
            positivity
          linarith
      simp only [hRP, if_neg hcond, zero_add]
      linarith
  calc ∑ i, ∑ j, ∫ z, term z i j ∂πF
      ≤ ∑ i, ∑ j, RP i j :=
        Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ hpp i j))
    _ ≤ (k : ℝ) ^ 2 * cutNormDiff W (chosenStep W ε') + 2 * (B.card : ℝ) * k + k := by
        have hcN : 0 ≤ cutNormDiff W (chosenStep W ε') := cutNormDiff_nonneg _ _
        have e1 : (∑ i : Fin k, ∑ j : Fin k,
            (if i ∉ B ∧ j ∉ B ∧ i ≠ j then cutNormDiff W (chosenStep W ε') else 0))
            ≤ (k : ℝ) ^ 2 * cutNormDiff W (chosenStep W ε') := by
          have hb : ∀ i j : Fin k,
              (if i ∉ B ∧ j ∉ B ∧ i ≠ j then cutNormDiff W (chosenStep W ε') else 0)
                ≤ cutNormDiff W (chosenStep W ε') := by
            intro i j; split_ifs with h
            · exact le_refl _
            · exact hcN
          calc (∑ i : Fin k, ∑ j : Fin k,
                (if i ∉ B ∧ j ∉ B ∧ i ≠ j then cutNormDiff W (chosenStep W ε') else 0))
              ≤ ∑ _i : Fin k, ∑ _j : Fin k, cutNormDiff W (chosenStep W ε') :=
                Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ hb i j))
            _ = (k : ℝ) ^ 2 * cutNormDiff W (chosenStep W ε') := by
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                ring
        have ecard : (∑ i : Fin k, (if i ∈ B then (1 : ℝ) else 0)) = B.card := by
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
        have e2 : (∑ i : Fin k, ∑ j : Fin k, (if i ∈ B then (1 : ℝ) else 0))
            = (k : ℝ) * B.card := by
          simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [← Finset.mul_sum, ecard, mul_comm]
        have e3 : (∑ i : Fin k, ∑ j : Fin k, (if j ∈ B then (1 : ℝ) else 0))
            = (k : ℝ) * B.card := by
          rw [Finset.sum_comm]
          simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [← Finset.mul_sum, ecard, mul_comm]
        have e4 : (∑ i : Fin k, ∑ j : Fin k, (if i = j then (1 : ℝ) else 0)) = (k : ℝ) := by
          simp_rw [Finset.sum_ite_eq, Finset.mem_univ, if_true]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        simp only [hRP, Finset.sum_add_distrib]
        rw [e2, e3, e4]
        linarith

omit [StandardBorelSpace α] [NullSingletonClass μ] in
/-- (H12) **Bounded differences.** Changing one fresh coordinate changes the rule value by at
most `4k`: rule memberships of other coordinates are unchanged (their sign sums read only the
block and their own coordinate), and the changed row and column each move by at most `2k`.
The constant `4k` is load-bearing for the §6 budget. -/
private theorem abs_ruleVal_update_le (W : Graphon α μ) (ε' : ℝ) {k : ℕ}
    (B : Finset (Fin k)) (s : Bool) {R R' : Finset (Fin k)} (hR : R ⊆ B) (hR' : R' ⊆ B)
    {i₀ : Fin k} (hi₀ : ¬ i₀ ∈ B) {x x' : Fin k → α}
    (hagree : ∀ l, l ≠ i₀ → x l = x' l) :
    |ruleVal (fun i j ↦ sgnR s * coreDiff W ε' x i j) R R'
      - ruleVal (fun i j ↦ sgnR s * coreDiff W ε' x' i j) R R'| ≤ 4 * k := by
  classical
  set term : (Fin k → α) → Fin k → Fin k → ℝ := fun y i j ↦
    (if 0 < ∑ j' ∈ R', sgnR s * coreDiff W ε' y i j' then (1 : ℝ) else 0) *
    (if 0 < ∑ j' ∈ R, sgnR s * coreDiff W ε' y j j' then (1 : ℝ) else 0) *
    (sgnR s * coreDiff W ε' y i j) with hterm
  -- Membership in `B` forces `≠ i₀` (since `i₀ ∉ B`).
  have hmem_ne : ∀ l ∈ B, l ≠ i₀ := fun l hl heq ↦ hi₀ (heq ▸ hl)
  -- Row/column sign sums over subsets of `B` are unchanged for rows `≠ i₀`.
  have hsum_eq : ∀ (S : Finset (Fin k)), S ⊆ B → ∀ i : Fin k, i ≠ i₀ →
      (∑ j' ∈ S, sgnR s * coreDiff W ε' x i j') = ∑ j' ∈ S, sgnR s * coreDiff W ε' x' i j' := by
    intro S hS i hi
    refine Finset.sum_congr rfl fun j' hj' ↦ ?_
    rw [coreDiff_congr W ε' (hagree i hi) (hagree j' (hmem_ne j' (hS hj')))]
  -- Each single term has absolute value at most `1`.
  have habs_term : ∀ (y : Fin k → α) (i j : Fin k), |term y i j| ≤ 1 := by
    intro y i j
    simp only [hterm]
    rw [abs_mul, abs_mul, abs_mul, abs_sgnR, one_mul]
    have hA : |(if 0 < ∑ j' ∈ R', sgnR s * coreDiff W ε' y i j' then (1 : ℝ) else 0)| ≤ 1 := by
      split_ifs <;> simp
    have hB : |(if 0 < ∑ j' ∈ R, sgnR s * coreDiff W ε' y j j' then (1 : ℝ) else 0)| ≤ 1 := by
      split_ifs <;> simp
    exact mul_le_one₀ (mul_le_one₀ hA (abs_nonneg _) hB) (abs_nonneg _)
      (abs_coreDiff_le_one W ε' y i j)
  -- Terms with both indices `≠ i₀` are unchanged.
  have hterm_eq : ∀ i j : Fin k, i ≠ i₀ → j ≠ i₀ → term x i j = term x' i j := by
    intro i j hi hj
    simp only [hterm]
    rw [hsum_eq R' hR' i hi, hsum_eq R hR j hj, coreDiff_congr W ε' (hagree i hi) (hagree j hj)]
  -- Pointwise bound on the term difference.
  have hpt : ∀ i j : Fin k,
      |term x i j - term x' i j| ≤ if i = i₀ ∨ j = i₀ then (2 : ℝ) else 0 := by
    intro i j
    by_cases hc : i = i₀ ∨ j = i₀
    · rw [if_pos hc]
      have htri : |term x i j - term x' i j| ≤ |term x i j| + |term x' i j| := by
        have := abs_add_le (term x i j) (-(term x' i j))
        rwa [← sub_eq_add_neg, abs_neg] at this
      calc |term x i j - term x' i j| ≤ |term x i j| + |term x' i j| := htri
        _ ≤ 1 + 1 := add_le_add (habs_term x i j) (habs_term x' i j)
        _ = 2 := by norm_num
    · rw [if_neg hc]
      obtain ⟨hci, hcj⟩ := not_or.mp hc
      rw [hterm_eq i j hci hcj, sub_self, abs_zero]
  -- Count of pairs touching `i₀`.
  have hcount : (∑ i : Fin k, ∑ j : Fin k, (if i = i₀ ∨ j = i₀ then (2 : ℝ) else 0)) ≤ 4 * k := by
    have key : ∀ i : Fin k, (∑ j : Fin k, (if i = i₀ ∨ j = i₀ then (2 : ℝ) else 0))
        = (if i = i₀ then (2 * (k : ℝ)) else 2) := by
      intro i
      by_cases hi : i = i₀
      · simp only [hi, true_or, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring
      · simp only [hi, false_or, Finset.sum_ite_eq', Finset.mem_univ, if_true, if_false]
    have hrw : ∀ i : Fin k, (if i = i₀ then (2 * (k : ℝ)) else 2)
        = 2 + (if i = i₀ then (2 * (k : ℝ) - 2) else 0) := by
      intro i; by_cases hi : i = i₀ <;> simp [hi]
    calc (∑ i : Fin k, ∑ j : Fin k, (if i = i₀ ∨ j = i₀ then (2 : ℝ) else 0))
        = ∑ i : Fin k, (if i = i₀ then (2 * (k : ℝ)) else 2) := Finset.sum_congr rfl fun i _ ↦ key i
      _ = ∑ i : Fin k, (2 + (if i = i₀ then (2 * (k : ℝ) - 2) else 0)) :=
          Finset.sum_congr rfl fun i _ ↦ hrw i
      _ = (k : ℝ) * 2 + (2 * (k : ℝ) - 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_eq']
          simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mem_univ, if_true]
      _ ≤ 4 * k := by linarith
  -- Assemble.
  rw [show (fun i j ↦ sgnR s * coreDiff W ε' x i j) = fun i j ↦ sgnR s * coreDiff W ε' x i j from rfl]
  rw [ruleVal_eq_sum_ite, ruleVal_eq_sum_ite]
  have hlx : (∑ i, ∑ j,
      (if 0 < ∑ j' ∈ R', sgnR s * coreDiff W ε' x i j' then (1 : ℝ) else 0) *
      (if 0 < ∑ j' ∈ R, sgnR s * coreDiff W ε' x j j' then (1 : ℝ) else 0) *
      (sgnR s * coreDiff W ε' x i j)) = ∑ i, ∑ j, term x i j := by simp only [hterm]
  have hlx' : (∑ i, ∑ j,
      (if 0 < ∑ j' ∈ R', sgnR s * coreDiff W ε' x' i j' then (1 : ℝ) else 0) *
      (if 0 < ∑ j' ∈ R, sgnR s * coreDiff W ε' x' j j' then (1 : ℝ) else 0) *
      (sgnR s * coreDiff W ε' x' i j)) = ∑ i, ∑ j, term x' i j := by simp only [hterm]
  rw [hlx, hlx', ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hpt i j) hcount

/-! ##### (II) McDiarmid at MGF level on finite product measures

The bounded-differences implementation (coordinate-peeling induction, one application of
Hoeffding's lemma per peeled coordinate) lives in `Graphon/McDiarmid.lean`, packaged as
`ProbabilityTheory.hasSubgaussianMGF_of_bounded_differences'` (arbitrary finite index
type) and its `Fin n` special case. Here we only unpack the `HasSubgaussianMGF` form back
into the integral-form MGF bound (H13b) consumed by the soft-max/assembly layer below. -/

/-- (H13b) McDiarmid MGF bound over `Measure.pi` on an arbitrary finite index type (the
fresh-coordinate subtype), uniform bounded-difference constant. Unpacked from
`ProbabilityTheory.hasSubgaussianMGF_of_bounded_differences'` (`Graphon/McDiarmid.lean`). -/
private theorem integral_exp_mul_centered_le_pi {ι : Type*} [Fintype ι] {β : Type*}
    [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν] (f : (ι → β) → ℝ)
    (hf : Measurable f) {c : ℝ} (hc : 0 ≤ c)
    (hbd : ∀ (i : ι) (x x' : ι → β), (∀ l, l ≠ i → x l = x' l) → |f x - f x'| ≤ c)
    (t : ℝ) :
    ∫ x, Real.exp (t * (f x - ∫ x', f x' ∂Measure.pi (fun _ : ι ↦ ν)))
        ∂Measure.pi (fun _ : ι ↦ ν)
      ≤ Real.exp ((Fintype.card ι : ℝ) * (c / 2) ^ 2 * t ^ 2 / 2) := by
  classical
  have hosc : ∀ (x : ι → β) (i : ι) (b : β), |f (Function.update x i b) - f x| ≤ c :=
    fun x i b ↦ hbd i (Function.update x i b) x fun l hl ↦ Function.update_of_ne hl b x
  have hml := (ProbabilityTheory.hasSubgaussianMGF_of_bounded_differences' ν f hf c hc
    hosc).mgf_le t
  have hcoe : (((Fintype.card ι : NNReal) * (c.toNNReal / 2) ^ 2 : NNReal) : ℝ)
      = (Fintype.card ι : ℝ) * (c / 2) ^ 2 := by
    push_cast [Real.coe_toNNReal c hc]
    ring
  rwa [ProbabilityTheory.mgf, hcoe] at hml

/-! ##### (III) Finite soft-max -/

/-- (H14) **Soft-max.** If finitely many bounded variables all satisfy the sub-Gaussian MGF
bound `E[exp(t Z_r)] ≤ exp(σ² t²/2)` for `t > 0`, then
`E[max_r Z_r] ≤ √(2 σ² log N)`. Via `exp`-Jensen and `max exp ≤ ∑ exp`; no tail bounds and
no measurable selection. -/
private theorem integral_sup'_le_sqrt_two_mul_log_card {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (Z : ι → Ω → ℝ) (hmeas : ∀ r ∈ s, Measurable (Z r))
    {K : ℝ} (hbdd : ∀ r ∈ s, ∀ ω, |Z r ω| ≤ K) {σ2 : ℝ} (hσ2 : 0 < σ2)
    (hmgf : ∀ r ∈ s, ∀ t : ℝ, 0 < t →
      ∫ ω, Real.exp (t * Z r ω) ∂ν ≤ Real.exp (σ2 * t ^ 2 / 2)) :
    ∫ ω, s.sup' hs (fun r ↦ Z r ω) ∂ν ≤ Real.sqrt (2 * σ2 * Real.log s.card) := by
  have hσ2ne : σ2 ≠ 0 := ne_of_gt hσ2
  set g : Ω → ℝ := fun ω ↦ s.sup' hs (fun r ↦ Z r ω) with hg
  have hg_meas : Measurable g := by
    have hgeq : g = s.sup' hs Z := funext fun ω ↦ (Finset.sup'_apply hs Z ω).symm
    rw [hgeq]; exact Finset.measurable_sup' hs hmeas
  have hg_bd : ∀ ω, |g ω| ≤ K := by
    intro ω
    rw [abs_le]
    obtain ⟨r0, hr0⟩ := hs
    refine ⟨?_, ?_⟩
    · calc -K ≤ Z r0 ω := by have := hbdd r0 hr0 ω; rw [abs_le] at this; linarith
        _ ≤ g ω := Finset.le_sup' (fun r ↦ Z r ω) hr0
    · apply Finset.sup'_le
      intro r hr
      have := hbdd r hr ω; rw [abs_le] at this; linarith
  have hg_int : Integrable g ν :=
    (integrable_const K).mono' hg_meas.aestronglyMeasurable
      (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hg_bd ω)
  set S : ℝ := ∫ ω, g ω ∂ν with hSdef
  have main : ∀ t : ℝ, 0 < t → t * S ≤ Real.log s.card + σ2 * t ^ 2 / 2 := by
    intro t ht
    have hexpZ_int : ∀ r ∈ s, Integrable (fun ω ↦ Real.exp (t * Z r ω)) ν := by
      intro r hr
      refine (integrable_const (Real.exp (|t| * K))).mono'
        (((hmeas r hr).const_mul t).exp).aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
      rw [Real.norm_eq_abs, Real.abs_exp]
      apply Real.exp_le_exp.mpr
      calc t * Z r ω ≤ |t * Z r ω| := le_abs_self _
        _ = |t| * |Z r ω| := abs_mul _ _
        _ ≤ |t| * K := mul_le_mul_of_nonneg_left (hbdd r hr ω) (abs_nonneg t)
    have hexpg_int : Integrable (fun ω ↦ Real.exp (t * g ω)) ν := by
      refine (integrable_const (Real.exp (|t| * K))).mono'
        ((hg_meas.const_mul t).exp).aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
      rw [Real.norm_eq_abs, Real.abs_exp]
      apply Real.exp_le_exp.mpr
      calc t * g ω ≤ |t * g ω| := le_abs_self _
        _ = |t| * |g ω| := abs_mul _ _
        _ ≤ |t| * K := mul_le_mul_of_nonneg_left (hg_bd ω) (abs_nonneg t)
    have hjensen : Real.exp (∫ ω, t * g ω ∂ν) ≤ ∫ ω, Real.exp (t * g ω) ∂ν := by
      have h := convexOn_exp.map_integral_le (μ := ν) (f := fun ω ↦ t * g ω)
        Real.continuous_exp.continuousOn isClosed_univ (ae_of_all _ fun ω ↦ Set.mem_univ _)
        (hg_int.const_mul t) hexpg_int
      simpa using h
    have hmono : Monotone (fun x : ℝ ↦ Real.exp (t * x)) := by
      intro a b hab
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab ht.le)
    have hstep : ∀ ω, Real.exp (t * g ω) ≤ ∑ r ∈ s, Real.exp (t * Z r ω) := by
      intro ω
      have h1 : Real.exp (t * g ω) = s.sup' hs (fun r ↦ Real.exp (t * Z r ω)) := by
        rw [hg, Finset.apply_sup'_eq_sup'_comp hs (fun x ↦ Real.exp (t * x))
          (fun x y ↦ hmono.map_max)]
        rfl
      rw [h1]
      apply Finset.sup'_le
      intro r hr
      exact Finset.single_le_sum (f := fun r ↦ Real.exp (t * Z r ω))
        (fun r' _ ↦ Real.exp_nonneg _) hr
    have hint_sup : (∫ ω, Real.exp (t * g ω) ∂ν)
        ≤ ∫ ω, ∑ r ∈ s, Real.exp (t * Z r ω) ∂ν :=
      integral_mono hexpg_int (integrable_finsetSum s hexpZ_int) hstep
    have hsum_int : (∫ ω, ∑ r ∈ s, Real.exp (t * Z r ω) ∂ν)
        = ∑ r ∈ s, ∫ ω, Real.exp (t * Z r ω) ∂ν := integral_finsetSum s hexpZ_int
    have hsum_bd : (∑ r ∈ s, ∫ ω, Real.exp (t * Z r ω) ∂ν)
        ≤ s.card * Real.exp (σ2 * t ^ 2 / 2) := by
      calc ∑ r ∈ s, ∫ ω, Real.exp (t * Z r ω) ∂ν
          ≤ ∑ _r ∈ s, Real.exp (σ2 * t ^ 2 / 2) :=
            Finset.sum_le_sum (fun r hr ↦ hmgf r hr t ht)
        _ = s.card * Real.exp (σ2 * t ^ 2 / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    have hexpbound : Real.exp (t * S) ≤ s.card * Real.exp (σ2 * t ^ 2 / 2) := by
      have hintcm : (∫ ω, t * g ω ∂ν) = t * S := by rw [hSdef, integral_const_mul]
      calc Real.exp (t * S) = Real.exp (∫ ω, t * g ω ∂ν) := by rw [hintcm]
        _ ≤ ∫ ω, Real.exp (t * g ω) ∂ν := hjensen
        _ ≤ ∑ r ∈ s, ∫ ω, Real.exp (t * Z r ω) ∂ν := hint_sup.trans_eq hsum_int
        _ ≤ s.card * Real.exp (σ2 * t ^ 2 / 2) := hsum_bd
    have hcard_pos : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
    have hlog := Real.log_le_log (Real.exp_pos _) hexpbound
    rwa [Real.log_exp, Real.log_mul (ne_of_gt hcard_pos) (ne_of_gt (Real.exp_pos _)),
      Real.log_exp] at hlog
  by_cases hL : Real.log s.card = 0
  · rw [hL, mul_zero, Real.sqrt_zero]
    by_contra hSneg
    push Not at hSneg
    have h2 := main (S / σ2) (div_pos hSneg hσ2)
    rw [hL, zero_add] at h2
    have hcontra : S * S / σ2 ≤ S * S / σ2 / 2 := by
      have e1 : S / σ2 * S = S * S / σ2 := by ring
      have e2 : σ2 * (S / σ2) ^ 2 / 2 = S * S / σ2 / 2 := by field_simp
      rw [e1, e2] at h2; exact h2
    have hpos : (0 : ℝ) < S * S / σ2 := div_pos (mul_pos hSneg hSneg) hσ2
    linarith
  · have hLnn : 0 ≤ Real.log s.card :=
      Real.log_nonneg (by exact_mod_cast Finset.one_le_card.mpr hs)
    have hLpos : 0 < Real.log s.card := lt_of_le_of_ne hLnn (Ne.symm hL)
    set L := Real.log s.card with hLdef
    set t := Real.sqrt (2 * L / σ2) with htdef
    have ht : 0 < t := Real.sqrt_pos.mpr (div_pos (by linarith) hσ2)
    have ht2 : t ^ 2 = 2 * L / σ2 := Real.sq_sqrt (div_pos (by linarith) hσ2).le
    have hmain := main t ht
    have hbound : t * S ≤ 2 * L := by
      have heq : σ2 * t ^ 2 / 2 = L := by rw [ht2]; field_simp
      rw [heq] at hmain; linarith
    have hprod : t * Real.sqrt (2 * σ2 * L) = 2 * L := by
      rw [htdef, ← Real.sqrt_mul (div_pos (by linarith) hσ2).le,
        show (2 * L / σ2) * (2 * σ2 * L) = (2 * L) ^ 2 by field_simp,
        Real.sqrt_sq (by linarith)]
    have hfinal : t * S ≤ t * Real.sqrt (2 * σ2 * L) := by rw [hprod]; exact hbound
    exact le_of_mul_le_mul_left hfinal ht

/-! ##### Per-block assembly and rate arithmetic (Layers 2+3+4) -/

omit [StandardBorelSpace α] [NullSingletonClass μ] in
/-- Mean layer, bundled: the sup' over signed rules of the conditional means is a.e. bounded
by `k²·cutNormDiff + 2|B|k + k`, by combining the finitely many `ae_integral_ruleVal_le`
(H11c) facts over the rule set. -/
private theorem ae_sup'_mean_le (W : Graphon α μ) (ε' : ℝ) {k : ℕ} [NeZero k]
    (B : Finset (Fin k)) {Q Q' : Finset (Fin k)}
    (hRB : ∀ ρ ∈ signedRules Q Q', ρ.2.1 ⊆ B ∧ ρ.2.2 ⊆ B) :
    ∀ᵐ y ∂(Measure.pi (fun _ : {l : Fin k // l ∈ B} ↦ μ)),
      (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ ↦ ∫ z, ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j)
            ρ.2.1 ρ.2.2 ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)))
        ≤ (k : ℝ) ^ 2 * cutNormDiff W (chosenStep W ε') + 2 * (B.card : ℝ) * k + k := by
  have hbundle : ∀ᵐ y ∂(Measure.pi (fun _ : {l : Fin k // l ∈ B} ↦ μ)),
      ∀ ρ ∈ signedRules Q Q',
        (∫ z, ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
            ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)))
          ≤ (k : ℝ) ^ 2 * cutNormDiff W (chosenStep W ε') + 2 * (B.card : ℝ) * k + k := by
    rw [Filter.eventually_all_finset]
    intro ρ hρ
    exact ae_integral_ruleVal_le W ε' B ρ.1 (hRB ρ hρ).1 (hRB ρ hρ).2
  filter_upwards [hbundle] with y hy
  exact Finset.sup'_le _ _ (fun ρ hρ ↦ hy ρ hρ)

omit [StandardBorelSpace α] [NullSingletonClass μ] in
/-- Deviation layer, per block assignment `y`: the fresh-sample integral of the sup' over
signed rules of the centered rule values is bounded by `√(8k³(2q+1)log2)`. McDiarmid MGF
(H13b) with bounded-difference constant `4k` (H12) feeds the soft-max (H14), and the rule
count is controlled by H16. -/
private theorem integral_sup'_dev_le (W : Graphon α μ) (ε' : ℝ) {k : ℕ} [NeZero k]
    {q : ℕ} (B : Finset (Fin k)) {Q Q' : Finset (Fin k)}
    (hQ : Q.card ≤ q) (hQ' : Q'.card ≤ q)
    (hRB : ∀ ρ ∈ signedRules Q Q', ρ.2.1 ⊆ B ∧ ρ.2.2 ⊆ B)
    (y : {l : Fin k // l ∈ B} → α) :
    (∫ z, (signedRules Q Q').sup' (signedRules_nonempty Q Q')
        (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
          - ∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j) ρ.2.1 ρ.2.2
              ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)))
        ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)))
      ≤ Real.sqrt (8 * (k : ℝ) ^ 3 * (2 * (q : ℝ) + 1) * Real.log 2) := by
  classical
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  -- blockGlue is measurable in the fresh coordinate `z`.
  have hbgm : Measurable (fun w : {l : Fin k // ¬ l ∈ B} → α ↦ blockGlue B y w) := by
    rw [measurable_pi_iff]; intro l
    simp only [blockGlue]
    by_cases hl : l ∈ B
    · simp only [dif_pos hl]; exact measurable_const
    · simp only [dif_neg hl]; exact measurable_pi_apply _
  -- Per-rule measurability, boundedness, and integrability of `z ↦ ruleVal(blockGlue B y z)`.
  have hZmeas : ∀ ρ : Bool × Finset (Fin k) × Finset (Fin k),
      Measurable (fun z : {l : Fin k // ¬ l ∈ B} → α ↦
        ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2) :=
    fun ρ ↦ (measurable_ruleVal_sample W ε' ρ.1 ρ.2.1 ρ.2.2).comp hbgm
  have hZbdd : ∀ (ρ : Bool × Finset (Fin k) × Finset (Fin k)) (x : Fin k → α),
      |ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2| ≤ (k : ℝ) ^ 2 := by
    intro ρ x
    refine abs_ruleVal_le _ (fun i j ↦ ?_) _ _
    rw [abs_mul, abs_sgnR, one_mul]; exact abs_coreDiff_le_one W ε' x i j
  have hZint : ∀ ρ : Bool × Finset (Fin k) × Finset (Fin k),
      Integrable (fun z : {l : Fin k // ¬ l ∈ B} → α ↦
        ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2)
        (Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)) :=
    fun ρ ↦ (integrable_const ((k : ℝ) ^ 2)).mono' (hZmeas ρ).aestronglyMeasurable
      (ae_of_all _ (fun z ↦ by rw [Real.norm_eq_abs]; exact hZbdd ρ _))
  have hMbdd : ∀ ρ : Bool × Finset (Fin k) × Finset (Fin k),
      |∫ z, ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
          ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))| ≤ (k : ℝ) ^ 2 := by
    intro ρ
    calc |∫ z, ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
            ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))|
        ≤ ∫ z, |ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2|
            ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)) := abs_integral_le_integral_abs
      _ ≤ ∫ _z, (k : ℝ) ^ 2 ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)) :=
          integral_mono (hZint ρ).abs (integrable_const _) (fun z ↦ hZbdd ρ _)
      _ = (k : ℝ) ^ 2 := by rw [integral_const, smul_eq_mul, probReal_univ, one_mul]
  -- Card of the fresh index set is ≤ k.
  have hcard_le : (Fintype.card {l : Fin k // ¬ l ∈ B} : ℝ) ≤ (k : ℝ) := by
    calc (Fintype.card {l : Fin k // ¬ l ∈ B} : ℝ)
        ≤ (Fintype.card (Fin k) : ℝ) := by exact_mod_cast Fintype.card_subtype_le _
      _ = (k : ℝ) := by rw [Fintype.card_fin]
  -- Soft-max (H14), σ² = 4k³, K = 2k².
  have hmeas : ∀ ρ ∈ signedRules Q Q',
      Measurable (fun z : {l : Fin k // ¬ l ∈ B} → α ↦
        ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
          - ∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j) ρ.2.1 ρ.2.2
              ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))) :=
    fun ρ _ ↦ (hZmeas ρ).sub_const _
  have hbdd : ∀ ρ ∈ signedRules Q Q', ∀ z : {l : Fin k // ¬ l ∈ B} → α,
      |ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
        - ∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j) ρ.2.1 ρ.2.2
            ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))| ≤ 2 * (k : ℝ) ^ 2 := by
    intro ρ _ z
    have htri : |ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
        - ∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j) ρ.2.1 ρ.2.2
            ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))|
        ≤ |ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2|
          + |∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j) ρ.2.1 ρ.2.2
              ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))| := by
      have := abs_add_le (ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j)
          ρ.2.1 ρ.2.2)
        (-(∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j) ρ.2.1 ρ.2.2
            ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))))
      rwa [← sub_eq_add_neg, abs_neg] at this
    calc |ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
        - ∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j) ρ.2.1 ρ.2.2
            ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))|
        ≤ (k : ℝ) ^ 2 + (k : ℝ) ^ 2 := htri.trans (add_le_add (hZbdd ρ _) (hMbdd ρ))
      _ = 2 * (k : ℝ) ^ 2 := by ring
  have hmgf : ∀ ρ ∈ signedRules Q Q', ∀ t : ℝ, 0 < t →
      ∫ z, Real.exp (t * (ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j)
              ρ.2.1 ρ.2.2
            - ∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j) ρ.2.1 ρ.2.2
                ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))))
          ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))
        ≤ Real.exp (4 * (k : ℝ) ^ 3 * t ^ 2 / 2) := by
    intro ρ hρ t _
    have hbd : ∀ (i₀ : {l : Fin k // ¬ l ∈ B}) (x x' : {l : Fin k // ¬ l ∈ B} → α),
        (∀ l, l ≠ i₀ → x l = x' l) →
        |ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y x) i j) ρ.2.1 ρ.2.2
          - ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y x') i j) ρ.2.1 ρ.2.2|
          ≤ 4 * (k : ℝ) := by
      intro i₀ x x' hxx'
      refine abs_ruleVal_update_le W ε' B ρ.1 (hRB ρ hρ).1 (hRB ρ hρ).2 (i₀ := (i₀ : Fin k))
        i₀.property (fun l hl ↦ ?_)
      simp only [blockGlue]
      by_cases hlB : l ∈ B
      · simp only [dif_pos hlB]
      · simp only [dif_neg hlB]
        exact hxx' ⟨l, hlB⟩ (fun hcontra ↦ hl (congrArg Subtype.val hcontra))
    have h13 := integral_exp_mul_centered_le_pi μ
      (fun z : {l : Fin k // ¬ l ∈ B} → α ↦
        ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2)
      (hZmeas ρ) (show (0 : ℝ) ≤ 4 * (k : ℝ) by positivity) hbd t
    refine h13.trans (Real.exp_le_exp.mpr ?_)
    have hcexp : (4 * (k : ℝ) / 2) ^ 2 = 4 * (k : ℝ) ^ 2 := by ring
    rw [hcexp]
    have hstep : (Fintype.card {l : Fin k // ¬ l ∈ B} : ℝ) * (4 * (k : ℝ) ^ 2)
        ≤ 4 * (k : ℝ) ^ 3 := by nlinarith [hcard_le, hkpos.le, sq_nonneg (k : ℝ)]
    nlinarith [hstep, sq_nonneg t, mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4)
      (sq_nonneg (k : ℝ))) (sq_nonneg t)]
  have hdev := integral_sup'_le_sqrt_two_mul_log_card
    (Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)) (signedRules_nonempty Q Q')
    (fun ρ z ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
      - ∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j) ρ.2.1 ρ.2.2
          ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)))
    hmeas hbdd (show (0 : ℝ) < 4 * (k : ℝ) ^ 3 by positivity) hmgf
  refine hdev.trans ?_
  apply Real.sqrt_le_sqrt
  have h8 : (0 : ℝ) ≤ 8 * (k : ℝ) ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (log_signedRules_card_le hQ hQ') h8]

set_option maxHeartbeats 1000000 in
omit [StandardBorelSpace α] [NullSingletonClass μ] in
/-- Per block assignment `y`, the fresh-sample integral of the rule sup' splits into the sup'
of the conditional means plus a deviation integral (H12+H13b+H14+H16). -/
private theorem integral_sup'_blockGlue_le (W : Graphon α μ) (ε' : ℝ) {k : ℕ} [NeZero k]
    {q : ℕ} (B : Finset (Fin k)) {Q Q' : Finset (Fin k)}
    (hQ : Q.card ≤ q) (hQ' : Q'.card ≤ q)
    (hRB : ∀ ρ ∈ signedRules Q Q', ρ.2.1 ⊆ B ∧ ρ.2.2 ⊆ B)
    (y : {l : Fin k // l ∈ B} → α) :
    (∫ z, (signedRules Q Q').sup' (signedRules_nonempty Q Q')
        (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2)
        ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)))
      ≤ (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ ↦ ∫ z, ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j)
            ρ.2.1 ρ.2.2 ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)))
        + Real.sqrt (8 * (k : ℝ) ^ 3 * (2 * (q : ℝ) + 1) * Real.log 2) := by
  classical
  -- Measurability of `z ↦ ruleVal(blockGlue B y z)`.
  have hbgm : Measurable (fun w : {l : Fin k // ¬ l ∈ B} → α ↦ blockGlue B y w) := by
    rw [measurable_pi_iff]; intro l
    simp only [blockGlue]
    by_cases hl : l ∈ B
    · simp only [dif_pos hl]; exact measurable_const
    · simp only [dif_neg hl]; exact measurable_pi_apply _
  have hZmeas : ∀ ρ : Bool × Finset (Fin k) × Finset (Fin k),
      Measurable (fun z : {l : Fin k // ¬ l ∈ B} → α ↦
        ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2) :=
    fun ρ ↦ (measurable_ruleVal_sample W ε' ρ.1 ρ.2.1 ρ.2.2).comp hbgm
  have hZbdd : ∀ (ρ : Bool × Finset (Fin k) × Finset (Fin k)) (x : Fin k → α),
      |ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2| ≤ (k : ℝ) ^ 2 := by
    intro ρ x
    refine abs_ruleVal_le _ (fun i j ↦ ?_) _ _
    rw [abs_mul, abs_sgnR, one_mul]; exact abs_coreDiff_le_one W ε' x i j
  -- The rule sup' `z ↦ sup'_ρ ruleVal(blockGlue B y z)` is measurable and bounded by `k²`.
  have hGmeas : Measurable (fun z : {l : Fin k // ¬ l ∈ B} → α ↦
      (signedRules Q Q').sup' (signedRules_nonempty Q Q')
        (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j)
          ρ.2.1 ρ.2.2)) := by
    have heq : (fun z : {l : Fin k // ¬ l ∈ B} → α ↦
        (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j)
            ρ.2.1 ρ.2.2))
        = fun z ↦ (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ (z : {l : Fin k // ¬ l ∈ B} → α) ↦
            ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2) z := by
      funext z; rw [Finset.sup'_apply]
    rw [heq]
    exact Finset.measurable_sup' _ (fun ρ _ ↦ hZmeas ρ)
  have hGbdd : ∀ z : {l : Fin k // ¬ l ∈ B} → α,
      |(signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j)
            ρ.2.1 ρ.2.2)| ≤ (k : ℝ) ^ 2 := by
    intro z
    rw [abs_le]
    obtain ⟨ρ0, hρ0⟩ := signedRules_nonempty Q Q'
    refine ⟨(Finset.le_sup'_iff _).mpr ⟨ρ0, hρ0, ?_⟩,
      Finset.sup'_le _ _ (fun ρ _ ↦ (abs_le.mp (hZbdd ρ (blockGlue B y z))).2)⟩
    have hb := hZbdd ρ0 (blockGlue B y z); rw [abs_le] at hb; exact hb.1
  have hGint : Integrable (fun z ↦ (signedRules Q Q').sup' (signedRules_nonempty Q Q')
      (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2))
      (Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)) :=
    (integrable_const ((k : ℝ) ^ 2)).mono' hGmeas.aestronglyMeasurable
      (ae_of_all _ (fun z ↦ by rw [Real.norm_eq_abs]; exact hGbdd z))
  -- Deviation sup' `z ↦ sup'_ρ (ruleVal(blockGlue B y z) - mean_ρ)`.
  have hDmeas : Measurable (fun z : {l : Fin k // ¬ l ∈ B} → α ↦
      (signedRules Q Q').sup' (signedRules_nonempty Q Q')
        (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
          - ∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j) ρ.2.1 ρ.2.2
              ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)))) := by
    have heq : (fun z : {l : Fin k // ¬ l ∈ B} → α ↦
        (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
            - ∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j) ρ.2.1 ρ.2.2
                ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))))
        = fun z ↦ (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ (z : {l : Fin k // ¬ l ∈ B} → α) ↦
            ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
            - ∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j) ρ.2.1 ρ.2.2
                ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))) z := by
      funext z; rw [Finset.sup'_apply]
    rw [heq]
    exact Finset.measurable_sup' _ (fun ρ _ ↦ (hZmeas ρ).sub_const _)
  have hMbdd : ∀ ρ : Bool × Finset (Fin k) × Finset (Fin k),
      |∫ z, ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
          ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))| ≤ (k : ℝ) ^ 2 := by
    intro ρ
    have hZint : Integrable (fun z : {l : Fin k // ¬ l ∈ B} → α ↦
        ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2)
        (Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)) :=
      (integrable_const ((k : ℝ) ^ 2)).mono' (hZmeas ρ).aestronglyMeasurable
        (ae_of_all _ (fun z ↦ by rw [Real.norm_eq_abs]; exact hZbdd ρ _))
    calc |∫ z, ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
            ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))|
        ≤ ∫ z, |ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2|
            ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)) := abs_integral_le_integral_abs
      _ ≤ ∫ _z, (k : ℝ) ^ 2 ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)) :=
          integral_mono hZint.abs (integrable_const _) (fun z ↦ hZbdd ρ _)
      _ = (k : ℝ) ^ 2 := by rw [integral_const, smul_eq_mul, probReal_univ, one_mul]
  have hterm : ∀ (ρ : Bool × Finset (Fin k) × Finset (Fin k)) (z : {l : Fin k // ¬ l ∈ B} → α),
      |ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
        - ∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j) ρ.2.1 ρ.2.2
            ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))| ≤ 2 * (k : ℝ) ^ 2 := by
    intro ρ z
    have htri := abs_add_le
      (ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2)
      (-(∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j) ρ.2.1 ρ.2.2
          ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))))
    rw [← sub_eq_add_neg, abs_neg] at htri
    have := add_le_add (hZbdd ρ (blockGlue B y z)) (hMbdd ρ)
    linarith
  have hDbdd : ∀ z : {l : Fin k // ¬ l ∈ B} → α,
      |(signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
            - ∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j) ρ.2.1 ρ.2.2
                ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)))| ≤ 2 * (k : ℝ) ^ 2 := by
    intro z
    rw [abs_le]
    obtain ⟨ρ0, hρ0⟩ := signedRules_nonempty Q Q'
    refine ⟨(Finset.le_sup'_iff _).mpr ⟨ρ0, hρ0, ?_⟩,
      Finset.sup'_le _ _ (fun ρ _ ↦ (abs_le.mp (hterm ρ z)).2)⟩
    have hb := hterm ρ0 z; rw [abs_le] at hb; exact hb.1
  have hDint : Integrable (fun z ↦ (signedRules Q Q').sup' (signedRules_nonempty Q Q')
      (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
        - ∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j) ρ.2.1 ρ.2.2
            ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))))
      (Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)) :=
    (integrable_const (2 * (k : ℝ) ^ 2)).mono' hDmeas.aestronglyMeasurable
      (ae_of_all _ (fun z ↦ by rw [Real.norm_eq_abs]; exact hDbdd z))
  -- Pointwise: rule sup' ≤ mean sup' + deviation sup'.
  have hpt : ∀ z : {l : Fin k // ¬ l ∈ B} → α,
      (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2)
        ≤ (signedRules Q Q').sup' (signedRules_nonempty Q Q')
            (fun ρ ↦ ∫ z, ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j)
              ρ.2.1 ρ.2.2 ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)))
          + (signedRules Q Q').sup' (signedRules_nonempty Q Q')
            (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
              - ∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j) ρ.2.1 ρ.2.2
                  ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))) := by
    intro z
    refine Finset.sup'_le _ _ (fun ρ hρ ↦ ?_)
    have h1 : (∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j)
          ρ.2.1 ρ.2.2 ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)))
        ≤ (signedRules Q Q').sup' (signedRules_nonempty Q Q')
            (fun ρ ↦ ∫ z, ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j)
              ρ.2.1 ρ.2.2 ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))) :=
      (Finset.le_sup'_iff _).mpr ⟨ρ, hρ, le_refl _⟩
    have h2 : (ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
          - ∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j)
              ρ.2.1 ρ.2.2 ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)))
        ≤ (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
            - ∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j)
                ρ.2.1 ρ.2.2 ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))) :=
      (Finset.le_sup'_iff _).mpr ⟨ρ, hρ, le_refl _⟩
    linarith
  calc (∫ z, (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2)
          ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)))
      ≤ ∫ z, ((signedRules Q Q').sup' (signedRules_nonempty Q Q')
            (fun ρ ↦ ∫ z, ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j)
              ρ.2.1 ρ.2.2 ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)))
          + (signedRules Q Q').sup' (signedRules_nonempty Q Q')
            (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
              - ∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j)
                  ρ.2.1 ρ.2.2 ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))))
          ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)) :=
        integral_mono hGint ((integrable_const _).add hDint) hpt
    _ = (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ ↦ ∫ z, ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j)
            ρ.2.1 ρ.2.2 ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)))
        + ∫ z, (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j) ρ.2.1 ρ.2.2
            - ∫ z', ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z') i j)
                ρ.2.1 ρ.2.2 ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)))
          ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)) := by
        rw [integral_add (integrable_const _) hDint, integral_const, smul_eq_mul, probReal_univ,
          one_mul]
    _ ≤ (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ ↦ ∫ z, ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' (blockGlue B y z) i j)
            ρ.2.1 ρ.2.2 ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)))
        + Real.sqrt (8 * (k : ℝ) ^ 3 * (2 * (q : ℝ) + 1) * Real.log 2) := by
        have hdev := integral_sup'_dev_le W ε' B hQ hQ' hRB y
        linarith

/-- (H15) **Expected signed-rule sup for one block pair**, normalized. Conditional means by
H11c, deviations by H12 + H13b + the soft-max H14; only the cardinality bounds
`|Q|, |Q'| ≤ q` are consumed. -/
private theorem integral_signedRuleSup_le (W : Graphon α μ) (ε' : ℝ) {k : ℕ} [NeZero k]
    {q : ℕ} (hq : 0 < q) (Q Q' : Finset (Fin k)) (hQ : Q.card ≤ q) (hQ' : Q'.card ≤ q) :
    (∫ x, (k : ℝ)⁻¹ ^ 2 * (signedRules Q Q').sup' (signedRules_nonempty Q Q')
        (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2)
        ∂Measure.pi (fun _ : Fin k ↦ μ))
      ≤ cutNormDiff W (chosenStep W ε') + (4 * q * k + k) / (k : ℝ) ^ 2
        + Real.sqrt (8 * (k : ℝ) ^ 3 * (2 * q + 1) * Real.log 2) / (k : ℝ) ^ 2 := by
  classical
  set B := Q ∪ Q' with hB
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have hk2ne : (k : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hkne
  -- Rule generators sit inside the block `B`.
  have hRB : ∀ ρ ∈ signedRules Q Q', ρ.2.1 ⊆ B ∧ ρ.2.2 ⊆ B := by
    intro ρ hρ
    simp only [signedRules, Finset.mem_product, Finset.mem_univ, Finset.mem_powerset,
      true_and] at hρ
    exact ⟨hρ.1.trans Finset.subset_union_left, hρ.2.trans Finset.subset_union_right⟩
  have hBcard : (B.card : ℝ) ≤ 2 * q := by
    have h1 : B.card ≤ Q.card + Q'.card := Finset.card_union_le _ _
    have h2 : Q.card + Q'.card ≤ 2 * q := by omega
    calc (B.card : ℝ) ≤ ((Q.card + Q'.card : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ ((2 * q : ℕ) : ℝ) := by exact_mod_cast h2
      _ = 2 * q := by push_cast; ring
  -- The full-sample rule sup'.
  set S : (Fin k → α) → ℝ := fun x ↦ (signedRules Q Q').sup' (signedRules_nonempty Q Q')
    (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2) with hS
  have hZbdd : ∀ (ρ : Bool × Finset (Fin k) × Finset (Fin k)) (x : Fin k → α),
      |ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2| ≤ (k : ℝ) ^ 2 := by
    intro ρ x
    refine abs_ruleVal_le _ (fun i j ↦ ?_) _ _
    rw [abs_mul, abs_sgnR, one_mul]; exact abs_coreDiff_le_one W ε' x i j
  have hSmeas : Measurable S := by
    rw [hS]
    have heq : (fun x : Fin k → α ↦ (signedRules Q Q').sup' (signedRules_nonempty Q Q')
        (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2))
        = fun x ↦ (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ (x : Fin k → α) ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j)
            ρ.2.1 ρ.2.2) x := by
      funext x; rw [Finset.sup'_apply]
    rw [heq]
    exact Finset.measurable_sup' _ (fun ρ _ ↦ measurable_ruleVal_sample W ε' ρ.1 ρ.2.1 ρ.2.2)
  have hSbdd : ∀ x, |S x| ≤ (k : ℝ) ^ 2 := by
    intro x
    simp only [hS]
    rw [abs_le]
    obtain ⟨ρ0, hρ0⟩ := signedRules_nonempty Q Q'
    refine ⟨(Finset.le_sup'_iff _).mpr ⟨ρ0, hρ0, ?_⟩,
      Finset.sup'_le _ _ (fun ρ _ ↦ (abs_le.mp (hZbdd ρ x)).2)⟩
    have hb := hZbdd ρ0 x; rw [abs_le] at hb; exact hb.1
  -- Block split via the product decomposition.
  have mp : MeasurePreserving
      (⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin k ↦ α) (· ∈ B)))
      (Measure.pi (fun _ : Fin k ↦ μ))
      ((Measure.pi (fun _ : {l : Fin k // l ∈ B} ↦ μ)).prod
        (Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))) := by
    convert measurePreserving_piEquivPiSubtypeProd (fun _ : Fin k ↦ μ) (· ∈ B) using 3
  have hGeint : Integrable (fun p : ({l : Fin k // l ∈ B} → α) × ({l : Fin k // ¬ l ∈ B} → α) ↦
      S ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin k ↦ α) (· ∈ B)).symm p))
      ((Measure.pi (fun _ : {l : Fin k // l ∈ B} ↦ μ)).prod
        (Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))) :=
    (integrable_const ((k : ℝ) ^ 2)).mono'
      (hSmeas.comp (MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : Fin k ↦ α) (· ∈ B)).symm.measurable).aestronglyMeasurable
      (ae_of_all _ (fun p ↦ by rw [Real.norm_eq_abs]; exact hSbdd _))
  have hsplit : (∫ x, S x ∂(Measure.pi (fun _ : Fin k ↦ μ)))
      = ∫ y, ∫ z, S (blockGlue B y z)
          ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))
          ∂(Measure.pi (fun _ : {l : Fin k // l ∈ B} ↦ μ)) := by
    rw [← mp.symm.integral_comp' S, integral_prod _ hGeint]
    refine integral_congr_ae (ae_of_all _ fun y ↦ integral_congr_ae (ae_of_all _ fun z ↦ ?_))
    simp only [piEquivPiSubtypeProd_symm_eq_blockGlue]
  -- Per block assignment `y`, the inner integral is bounded by the mean + deviation.
  have hyb : ∀ᵐ y ∂(Measure.pi (fun _ : {l : Fin k // l ∈ B} ↦ μ)),
      (∫ z, S (blockGlue B y z) ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)))
        ≤ (k : ℝ) ^ 2 * cutNormDiff W (chosenStep W ε') + 2 * (B.card : ℝ) * k + k
          + Real.sqrt (8 * (k : ℝ) ^ 3 * (2 * (q : ℝ) + 1) * Real.log 2) := by
    filter_upwards [ae_sup'_mean_le W ε' B hRB] with y hy
    have hc := integral_sup'_blockGlue_le W ε' B hQ hQ' hRB y
    simp only [hS]
    linarith
  have hphi_int : Integrable (fun y ↦ ∫ z, S (blockGlue B y z)
      ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ)))
      (Measure.pi (fun _ : {l : Fin k // l ∈ B} ↦ μ)) := by
    refine hGeint.integral_prod_left.congr (ae_of_all _ fun y ↦ ?_)
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    simp only [piEquivPiSubtypeProd_symm_eq_blockGlue]
  have hdbl : (∫ y, ∫ z, S (blockGlue B y z)
        ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))
        ∂(Measure.pi (fun _ : {l : Fin k // l ∈ B} ↦ μ)))
      ≤ (k : ℝ) ^ 2 * cutNormDiff W (chosenStep W ε') + 2 * (B.card : ℝ) * k + k
        + Real.sqrt (8 * (k : ℝ) ^ 3 * (2 * (q : ℝ) + 1) * Real.log 2) := by
    calc (∫ y, ∫ z, S (blockGlue B y z)
            ∂(Measure.pi (fun _ : {l : Fin k // ¬ l ∈ B} ↦ μ))
            ∂(Measure.pi (fun _ : {l : Fin k // l ∈ B} ↦ μ)))
        ≤ ∫ _y, ((k : ℝ) ^ 2 * cutNormDiff W (chosenStep W ε') + 2 * (B.card : ℝ) * k + k
            + Real.sqrt (8 * (k : ℝ) ^ 3 * (2 * (q : ℝ) + 1) * Real.log 2))
            ∂(Measure.pi (fun _ : {l : Fin k // l ∈ B} ↦ μ)) :=
          integral_mono_ae hphi_int (integrable_const _) hyb
      _ = (k : ℝ) ^ 2 * cutNormDiff W (chosenStep W ε') + 2 * (B.card : ℝ) * k + k
          + Real.sqrt (8 * (k : ℝ) ^ 3 * (2 * (q : ℝ) + 1) * Real.log 2) := by
          rw [integral_const, smul_eq_mul, probReal_univ, one_mul]
  -- Normalize by `k⁻²` and absorb `|B| ≤ 2q`.
  rw [integral_const_mul, hsplit]
  refine le_trans (mul_le_mul_of_nonneg_left hdbl (by positivity)) ?_
  have key : (k : ℝ)⁻¹ ^ 2 * ((k : ℝ) ^ 2 * cutNormDiff W (chosenStep W ε') + 2 * (B.card : ℝ) * k
        + k + Real.sqrt (8 * (k : ℝ) ^ 3 * (2 * (q : ℝ) + 1) * Real.log 2))
      = cutNormDiff W (chosenStep W ε') + (2 * (B.card : ℝ) * k + k) / (k : ℝ) ^ 2
        + Real.sqrt (8 * (k : ℝ) ^ 3 * (2 * (q : ℝ) + 1) * Real.log 2) / (k : ℝ) ^ 2 := by
    rw [inv_pow]; field_simp; ring
  rw [key]
  have hk2pos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hnum : 2 * (B.card : ℝ) * k + k ≤ 4 * (q : ℝ) * k + k := by
    nlinarith [mul_le_mul_of_nonneg_right hBcard hkpos.le]
  have hdiv : (2 * (B.card : ℝ) * k + k) / (k : ℝ) ^ 2
      ≤ (4 * (q : ℝ) * k + k) / (k : ℝ) ^ 2 := (div_le_div_iff_of_pos_right hk2pos).mpr hnum
  linarith

/-- Bridge: `k^{-1/4} = (√√k)⁻¹` for `0 < k`; all rate arithmetic below is phrased through
`u := √√k`, so only this one `rpow` identity is ever needed. -/
private theorem rpow_neg_quarter_eq (k : ℕ) (hk : 0 < k) :
    (k : ℝ) ^ (-(1 / 4 : ℝ)) = (Real.sqrt (Real.sqrt k))⁻¹ := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  rw [Real.rpow_neg hk0]
  congr 1
  rw [show (1 / 4 : ℝ) = (1 / 2) * (1 / 2) by norm_num, Real.rpow_mul hk0,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]

/-- The basic `u := √√k` facts, packaged: positivity, `u² = √k`, `u⁴ = k`. -/
private theorem sqrt_sqrt_facts (k : ℕ) (hk : 0 < k) :
    0 < Real.sqrt (Real.sqrt k) ∧ (Real.sqrt (Real.sqrt k)) ^ 2 = Real.sqrt k ∧
      (Real.sqrt (Real.sqrt k)) ^ 4 = k := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hs : (0 : ℝ) < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hu : (0 : ℝ) < Real.sqrt (Real.sqrt k) := Real.sqrt_pos.mpr hs
  have hu2 : (Real.sqrt (Real.sqrt k)) ^ 2 = Real.sqrt k := Real.sq_sqrt hs.le
  refine ⟨hu, hu2, ?_⟩
  have h22 : ((Real.sqrt (Real.sqrt k)) ^ 2) ^ 2 = (Real.sqrt k) ^ 2 := by rw [hu2]
  rw [Real.sq_sqrt hk0.le] at h22
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
  exact h22

/-- (H17) **The error budget** (`k ≥ 2401`, `√k ≤ q ≤ √k + 1`): the four error terms sum to
at most `8·k^{−1/4}`. Numerically verified in `docs/afkk-cut-guessing.md` (worst coefficient
≈ 6.24 at `k` near `k₀ = 2401`; asymptotic ≈ 5.33); the per-term budget proved here is
`3/10 + 2 + 3/5 + 7/2 = 32/5 ≤ 8` in units of `k^{−1/4}`. -/
private theorem afkk_error_budget {k q : ℕ} (hk : 2401 ≤ k)
    (hq₁ : Real.sqrt k ≤ q) (hq₂ : (q : ℝ) ≤ Real.sqrt k + 1) :
    2 * (q : ℝ) / k + 2 / Real.sqrt q + (4 * q * k + k) / (k : ℝ) ^ 2
      + Real.sqrt (8 * (k : ℝ) ^ 3 * (2 * q + 1) * Real.log 2) / (k : ℝ) ^ 2
    ≤ 8 * (k : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hk1 : 0 < k := by omega
  obtain ⟨hu, hu2, hu4⟩ := sqrt_sqrt_facts k hk1
  set u : ℝ := Real.sqrt (Real.sqrt k) with hu_def
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  -- u ≥ 7 from k ≥ 2401 = 7⁴
  have h7 : 7 ≤ u := by
    by_contra h
    rw [not_le] at h
    have h4 : u ^ 4 < 7 ^ 4 := pow_lt_pow_left₀ h hu.le (by norm_num)
    rw [hu4] at h4
    have hklt : (k : ℝ) < 2401 := by norm_num at h4; linarith
    have : (2401 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hu1 : (1 : ℝ) ≤ u := by linarith
  -- q bounds in terms of u
  have hq_lo : u ^ 2 ≤ (q : ℝ) := hu2 ▸ hq₁
  have hq_up : (q : ℝ) ≤ u ^ 2 + 1 := by rw [hu2]; exact hq₂
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  -- rewrite the RHS through the bridge
  rw [rpow_neg_quarter_eq k hk1, ← hu_def]
  -- log 2 bounds
  have hL_up : Real.log 2 ≤ 0.6931472 := by
    have := Real.log_two_lt_d9
    norm_num at this ⊢
    linarith
  have hL_lo : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  -- Term 1: 2q/k ≤ (3/10)/u  [2u³ + 2u ≤ (100/49)u³ ≤ (3/10)u⁴ at u ≥ 7]
  have hT1 : 2 * (q : ℝ) / k ≤ (3 / 10) / u := by
    rw [div_le_div_iff₀ hk0 hu, ← hu4]
    have e1 : 2 * (q : ℝ) * u ≤ 2 * (u ^ 2 + 1) * u :=
      mul_le_mul_of_nonneg_right (by linarith) hu.le
    have e2 : 2 * (u ^ 2 + 1) * u ≤ (100 / 49) * u ^ 3 := by nlinarith [h7, hu]
    have e3 : (100 / 49) * u ^ 3 ≤ (3 / 10) * u ^ 4 := by nlinarith [h7, hu, pow_pos hu 3]
    linarith
  -- Term 2: 2/√q ≤ 2/u
  have hT2 : 2 / Real.sqrt q ≤ 2 / u := by
    have hsq : u ≤ Real.sqrt q := by
      have h := Real.sqrt_le_sqrt hq_lo
      rwa [Real.sqrt_sq hu.le] at h
    gcongr
  -- Term 3: (4qk + k)/k² ≤ (3/5)/u  [(4q+1)u⁵ ≤ (3/5)u⁸ ⟸ 4u² + 5 ≤ (3/5)u³]
  have hT3 : (4 * (q : ℝ) * k + k) / (k : ℝ) ^ 2 ≤ (3 / 5) / u := by
    rw [div_le_div_iff₀ (by positivity) hu, ← hu4]
    have e1 : (4 * (q : ℝ) * u ^ 4 + u ^ 4) * u ≤ (4 * (u ^ 2 + 1) + 1) * u ^ 5 := by
      nlinarith [hq_up, pow_pos hu 5, pow_pos hu 4, hu]
    have e2 : (4 * (u ^ 2 + 1) + 1) * u ^ 5 ≤ (3 / 5) * (u ^ 4) ^ 2 := by
      have h1 : (1 : ℝ) ≤ 3 * u - 20 := by linarith
      have h2 : 4 * u ^ 2 + 5 ≤ (3 / 5) * u ^ 3 := by nlinarith [h7, hu, sq_nonneg u]
      nlinarith [h2, pow_pos hu 5]
    linarith
  -- Term 4: √(8k³(2q+1)·log2)/k² ≤ (7/2)/u
  have hT4 : Real.sqrt (8 * (k : ℝ) ^ 3 * (2 * q + 1) * Real.log 2) / (k : ℝ) ^ 2
      ≤ (7 / 2) / u := by
    have haux : 8 * (2 * (q : ℝ) + 1) * Real.log 2 ≤ (49 / 4) * u ^ 2 := by
      have h1 : 8 * (2 * (q : ℝ) + 1) * Real.log 2
          ≤ 8 * (2 * (u ^ 2 + 1) + 1) * 0.6931472 := by
        have hq1 : (0 : ℝ) ≤ 2 * (q : ℝ) + 1 := by positivity
        nlinarith [hL_up, hL_lo, hq_up, hq1]
      nlinarith [h7, hu, h1]
    have hbound : 8 * (k : ℝ) ^ 3 * (2 * q + 1) * Real.log 2 ≤ ((7 / 2) * u ^ 7) ^ 2 := by
      have hfac : 8 * (k : ℝ) ^ 3 * (2 * q + 1) * Real.log 2
          = u ^ 12 * (8 * (2 * (q : ℝ) + 1) * Real.log 2) := by
        rw [← hu4]; ring
      have h12 : (0 : ℝ) ≤ u ^ 12 := by positivity
      calc 8 * (k : ℝ) ^ 3 * (2 * q + 1) * Real.log 2
          = u ^ 12 * (8 * (2 * (q : ℝ) + 1) * Real.log 2) := hfac
        _ ≤ u ^ 12 * ((49 / 4) * u ^ 2) := mul_le_mul_of_nonneg_left haux h12
        _ = ((7 / 2) * u ^ 7) ^ 2 := by ring
    have hsqrt : Real.sqrt (8 * (k : ℝ) ^ 3 * (2 * q + 1) * Real.log 2)
        ≤ (7 / 2) * u ^ 7 := by
      have h1 := Real.sqrt_le_sqrt hbound
      rwa [Real.sqrt_sq (by positivity)] at h1
    rw [div_le_div_iff₀ (by positivity) hu]
    calc Real.sqrt (8 * (k : ℝ) ^ 3 * (2 * q + 1) * Real.log 2) * u
        ≤ ((7 / 2) * u ^ 7) * u := mul_le_mul_of_nonneg_right hsqrt hu.le
      _ = (7 / 2) * u ^ 8 := by ring
      _ = 7 / 2 * (k : ℝ) ^ 2 := by rw [← hu4]; ring
  -- total: (3/10 + 2 + 3/5 + 7/2)/u = (32/5)/u ≤ 8/u
  have htotal : (3 / 10 : ℝ) / u + 2 / u + (3 / 5) / u + (7 / 2) / u ≤ 8 * u⁻¹ := by
    have hsum : (3 / 10 : ℝ) / u + 2 / u + (3 / 5) / u + (7 / 2) / u = (32 / 5) / u := by
      ring
    rw [hsum, show (8 : ℝ) * u⁻¹ = 8 / u by rw [div_eq_mul_inv]]
    gcongr
    norm_num
  linarith [hT1, hT2, hT3, hT4, htotal]

/-- (H18 arithmetic core) For `1 ≤ k < 2401`: `1 + 2⌈√k⌉₊/k ≤ 8·k^{−1/4}` — the polynomial
`u⁴ + 2u² + 2 ≤ 8u³` on `u = k^{1/4} ∈ [1,7]` (minimum slack `3` at `u = 1`). -/
private theorem small_k_arith {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 2401) :
    1 + 2 * ((⌈Real.sqrt k⌉₊ : ℝ)) / k ≤ 8 * (k : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hk0 : 0 < k := hk1
  obtain ⟨hu, hu2, hu4⟩ := sqrt_sqrt_facts k hk0
  set u : ℝ := Real.sqrt (Real.sqrt k) with hu_def
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  -- 1 ≤ u < 7
  have hu1 : 1 ≤ u := by
    by_contra h
    rw [not_le] at h
    have h4 : u ^ 4 < 1 ^ 4 := pow_lt_pow_left₀ h hu.le (by norm_num)
    rw [hu4] at h4
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    norm_num at h4
    linarith
  have hu7 : u < 7 := by
    by_contra h
    rw [not_lt] at h
    have h4 : (7 : ℝ) ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) h 4
    rw [hu4] at h4
    have : (k : ℝ) < 2401 := by exact_mod_cast hk
    norm_num at h4
    linarith
  -- ⌈√k⌉ ≤ √k + 1 = u² + 1
  have hceil : ((⌈Real.sqrt k⌉₊ : ℝ)) ≤ u ^ 2 + 1 := by
    rw [hu2]
    exact (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le
  rw [rpow_neg_quarter_eq k hk0, ← hu_def]
  -- the polynomial u⁴ + 2u² + 2 ≤ 8u³ on [1,7]
  have hpoly : u ^ 4 + 2 * u ^ 2 + 2 ≤ 8 * u ^ 3 := by
    nlinarith [hu1, hu7, sq_nonneg (u - 1), sq_nonneg (u - 3),
      mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hu7.le),
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hu7.le)) hu.le]
  have hstep : 1 + 2 * ((⌈Real.sqrt k⌉₊ : ℝ)) / k ≤ 1 + 2 * (u ^ 2 + 1) / u ^ 4 := by
    calc 1 + 2 * ((⌈Real.sqrt k⌉₊ : ℝ)) / k ≤ 1 + 2 * (u ^ 2 + 1) / (k : ℝ) := by gcongr
      _ = 1 + 2 * (u ^ 2 + 1) / u ^ 4 := by rw [hu4]
  refine hstep.trans ?_
  have h4 : (0 : ℝ) < u ^ 4 := pow_pos hu 4
  rw [show (8 : ℝ) * u⁻¹ = 8 / u by rw [div_eq_mul_inv]]
  rw [add_div' _ _ _ h4.ne', div_le_div_iff₀ h4 hu]
  nlinarith [mul_le_mul_of_nonneg_right hpoly hu.le]

/-- (H18) **Small-`k` branch** (`k < 2401 = 7⁴`): the whole statement is trivial from the
normalized sup being ≤ 1 and `1 + 2⌈√k⌉/k ≤ 8k^{−1/4}` on this range (in polynomial form
`t⁴ + 2t² + 2 ≤ 8t³` for `t = k^{1/4} ∈ [1,7]`). -/
private theorem guessBlock_integral_le_cutNormDiff_of_small (W : Graphon α μ) (ε' : ℝ)
    {k : ℕ} [NeZero k] (hk : k < 2401) :
    (∫ x, (k : ℝ)⁻¹ ^ 2 * (Finset.univ : Finset (Finset (Fin k) × Finset (Fin k))).sup'
        Finset.univ_nonempty (fun AB ↦ |∑ i ∈ AB.1 \ guessBlock k, ∑ j ∈ AB.2 \ guessBlock k,
          coreDiff W ε' x i j|) ∂Measure.pi (fun _ : Fin k ↦ μ))
      + 2 * ((guessBlock k).card : ℝ) / k
      ≤ cutNormDiff W (chosenStep W ε') + 8 * ((k : ℝ) ^ (-(1 / 4 : ℝ))) := by
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (NeZero.ne k)
  set π : Measure (Fin k → α) := Measure.pi (fun _ : Fin k ↦ μ) with hπ
  set g : (Fin k → α) → ℝ := fun x ↦ (k : ℝ)⁻¹ ^ 2 *
      (Finset.univ : Finset (Finset (Fin k) × Finset (Fin k))).sup' Finset.univ_nonempty
        (fun AB ↦ |∑ i ∈ AB.1 \ guessBlock k, ∑ j ∈ AB.2 \ guessBlock k,
          coreDiff W ε' x i j|) with hg
  -- `g` is measurable and `g ∈ [0,1]` (the `hg_meas`/`hg_le` pattern of the consumer)
  have hg_meas : Measurable g := by
    have heq : g = fun x ↦ (k : ℝ)⁻¹ ^ 2 * Finset.univ.sup' Finset.univ_nonempty
        (fun (AB : Finset (Fin k) × Finset (Fin k)) (x : Fin k → α) ↦
          |∑ i ∈ AB.1 \ guessBlock k, ∑ j ∈ AB.2 \ guessBlock k, coreDiff W ε' x i j|) x := by
      funext x; rw [hg, Finset.sup'_apply]
    rw [heq]
    refine measurable_const.mul (Finset.measurable_sup' _ (fun AB _ ↦ ?_))
    refine continuous_abs.measurable.comp
      (Finset.measurable_sum _ (fun i _ ↦ Finset.measurable_sum _ (fun j _ ↦ ?_)))
    simp only [coreDiff]
    exact (measurable_clampEval W i j).sub (measurable_clampEval (chosenStep W ε') i j)
  have hg_nn : ∀ x, 0 ≤ g x := by
    intro x
    rw [hg]
    refine mul_nonneg (by positivity) (le_trans ?_
      (Finset.le_sup' (fun AB : Finset (Fin k) × Finset (Fin k) ↦
          |∑ i ∈ AB.1 \ guessBlock k, ∑ j ∈ AB.2 \ guessBlock k, coreDiff W ε' x i j|)
        (Finset.mem_univ ((∅, ∅) : Finset (Fin k) × Finset (Fin k)))))
    exact abs_nonneg _
  have hg_le : ∀ x, g x ≤ 1 := by
    intro x
    rw [hg]
    have hsup : Finset.univ.sup' Finset.univ_nonempty
        (fun AB : Finset (Fin k) × Finset (Fin k) ↦
          |∑ i ∈ AB.1 \ guessBlock k, ∑ j ∈ AB.2 \ guessBlock k, coreDiff W ε' x i j|)
        ≤ (k : ℝ) ^ 2 := by
      refine Finset.sup'_le _ _ (fun AB _ ↦ ?_)
      refine (abs_coreDiff_rect_le W ε' x _ _).trans ?_
      have hc : ∀ S : Finset (Fin k), ((S \ guessBlock k).card : ℝ) ≤ k := by
        intro S
        calc ((S \ guessBlock k).card : ℝ)
            ≤ ((Finset.univ : Finset (Fin k)).card : ℝ) := by
              exact_mod_cast Finset.card_le_card (Finset.subset_univ _)
          _ = k := by rw [Finset.card_univ, Fintype.card_fin]
      calc ((AB.1 \ guessBlock k).card : ℝ) * ((AB.2 \ guessBlock k).card : ℝ)
          ≤ (k : ℝ) * k := mul_le_mul (hc _) (hc _) (by positivity) (by positivity)
        _ = (k : ℝ) ^ 2 := by ring
    calc (k : ℝ)⁻¹ ^ 2 * _
        ≤ (k : ℝ)⁻¹ ^ 2 * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsup (by positivity)
      _ = 1 := by field_simp
  have hg_int : Integrable g π :=
    (integrable_const (1 : ℝ)).mono' hg_meas.aestronglyMeasurable
      (ae_of_all _ (fun x ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn x)]; exact hg_le x))
  -- ∫ g ≤ 1 on the probability measure
  have hint_le : ∫ x, g x ∂π ≤ 1 := by
    have h := integral_mono hg_int (integrable_const (1 : ℝ)) hg_le
    rwa [integral_const, smul_eq_mul, probReal_univ, one_mul] at h
  -- cardinality cost and the arithmetic core
  have hcard : 2 * ((guessBlock k).card : ℝ) / k ≤ 2 * ((⌈Real.sqrt k⌉₊ : ℝ)) / k := by
    gcongr
    exact_mod_cast guessBlock_card_le k
  have harith := small_k_arith hk1 hk
  have hcn : 0 ≤ cutNormDiff W (chosenStep W ε') := cutNormDiff_nonneg _ _
  calc (∫ x, g x ∂π) + 2 * ((guessBlock k).card : ℝ) / k
      ≤ 1 + 2 * ((⌈Real.sqrt k⌉₊ : ℝ)) / k := add_le_add hint_le hcard
    _ ≤ 8 * (k : ℝ) ^ (-(1 / 4 : ℝ)) := harith
    _ ≤ cutNormDiff W (chosenStep W ε') + 8 * ((k : ℝ) ^ (-(1 / 4 : ℝ))) := by linarith

/-- **Crux — AFKK / Lovász-10.7 Q-subsample cut-guessing.** After the block-split reduction
`coreTerm_restrict_fresh_block`, the `1/k²`-normalized expectation of the fresh-block discrete
cut norm, plus the block-split cost `2|Q₀|/k`, is at most the continuous cut norm
`cutNormDiff W (chosenStep W ε')` plus `8·k^{-1/4}`.

Proof (see `docs/afkk-cut-guessing.md`): the deterministic block `Q₀ = guessBlock k` enters
only through `sup'_sdiff_le_sup'` and its cardinality. The free cut sup is bounded pointwise
by the average over pairs of `q`-subsets `(Q,Q')` of the best of `2·4^q` sign-set rules plus
`2k²/√q` (`sup'_abs_cut_le_avg_signedRuleSup`, via the finite sampling-without-replacement
second moment `sum_powersetCard_abs_sub_le` — elementary `powersetCard` combinatorics, not a
probabilistic ingredient). For each block pair, conditioning on `x_{Q∪Q'}` makes every fixed
rule a pointwise rule whose conditional mean is a rectangle integral of `W − U`, hence
`≤ cutNormDiff` (`ae_integral_ruleVal_le`); the deviations are controlled by a McDiarmid-type
MGF bound (`integral_exp_mul_centered_le_pi`, bounded differences `4k`) and a soft-max over
the rules (`integral_sup'_le_sqrt_two_mul_log_card`), giving `√(8k³(2q+1)·log 2)`
(`integral_signedRuleSup_le`). At `q = ⌈√k⌉` the budget `afkk_error_budget` sums to
`≤ 8·k^{-1/4}` for `k ≥ 2401`; smaller `k` are trivial
(`guessBlock_integral_le_cutNormDiff_of_small`).

References: Lovász, *Large Networks*, Lemma 10.7; AFKK, JCSS 67 (2003), Lemma 3;
arXiv:2203.07581 §6.2 + Appendix §10. -/
private theorem guessBlock_integral_le_cutNormDiff (W : Graphon α μ) (ε' : ℝ) (hε' : 0 < ε')
    {k : ℕ} [NeZero k] :
    (∫ x, (k : ℝ)⁻¹ ^ 2 * (Finset.univ : Finset (Finset (Fin k) × Finset (Fin k))).sup'
        Finset.univ_nonempty (fun AB ↦ |∑ i ∈ AB.1 \ guessBlock k, ∑ j ∈ AB.2 \ guessBlock k,
          coreDiff W ε' x i j|) ∂Measure.pi (fun _ : Fin k ↦ μ))
      + 2 * ((guessBlock k).card : ℝ) / k
      ≤ cutNormDiff W (chosenStep W ε') + 8 * ((k : ℝ) ^ (-(1 / 4 : ℝ))) := by
  by_cases hk : k < 2401
  · exact guessBlock_integral_le_cutNormDiff_of_small W ε' hk
  rw [not_lt] at hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  set q : ℕ := ⌈Real.sqrt k⌉₊ with hq_def
  have hq0 : 0 < q := one_le_natCeil_sqrt k
  have hqk : q ≤ k := natCeil_sqrt_le_self k
  have hchoose_pos : (0 : ℝ) < (k.choose q : ℝ) := by exact_mod_cast Nat.choose_pos hqk
  -- the bridge gate: fixed guessBlock sup ⤳ double average of signed-rule sups
  have hbridge := guessBlock_sup_integral_le_avg_ruleSup W ε' hq0 hqk
  -- each block pair's rule-sup integral is uniformly bounded (H15), so the average collapses
  set cB : ℝ := cutNormDiff W (chosenStep W ε') + (4 * q * k + k) / (k : ℝ) ^ 2
      + Real.sqrt (8 * (k : ℝ) ^ 3 * (2 * q + 1) * Real.log 2) / (k : ℝ) ^ 2 with hcB_def
  have hblock : ((k.choose q : ℝ)⁻¹) ^ 2 *
      (∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
       ∑ Q' ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
        ∫ x, (k : ℝ)⁻¹ ^ 2 * (signedRules Q Q').sup' (signedRules_nonempty Q Q')
          (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2)
          ∂Measure.pi (fun _ : Fin k ↦ μ)) ≤ cB := by
    have hsum : (∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
        ∑ Q' ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
         ∫ x, (k : ℝ)⁻¹ ^ 2 * (signedRules Q Q').sup' (signedRules_nonempty Q Q')
           (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2)
           ∂Measure.pi (fun _ : Fin k ↦ μ))
        ≤ (k.choose q : ℝ) ^ 2 * cB := by
      have hbound : ∀ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
          ∀ Q' ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
          (∫ x, (k : ℝ)⁻¹ ^ 2 * (signedRules Q Q').sup' (signedRules_nonempty Q Q')
            (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2)
            ∂Measure.pi (fun _ : Fin k ↦ μ)) ≤ cB := by
        intro Q hQ Q' hQ'
        exact integral_signedRuleSup_le W ε' hq0 Q Q'
          (le_of_eq (Finset.mem_powersetCard.mp hQ).2)
          (le_of_eq (Finset.mem_powersetCard.mp hQ').2)
      calc (∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
          ∑ Q' ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
           ∫ x, (k : ℝ)⁻¹ ^ 2 * (signedRules Q Q').sup' (signedRules_nonempty Q Q')
             (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2)
             ∂Measure.pi (fun _ : Fin k ↦ μ))
          ≤ ∑ _Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
            ∑ _Q' ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)), cB := by
            refine Finset.sum_le_sum (fun Q hQ ↦ Finset.sum_le_sum (fun Q' hQ' ↦ ?_))
            exact hbound Q hQ Q' hQ'
        _ = (k.choose q : ℝ) ^ 2 * cB := by
            simp [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]
            ring
    calc ((k.choose q : ℝ)⁻¹) ^ 2 *
        (∑ Q ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
         ∑ Q' ∈ Finset.powersetCard q (Finset.univ : Finset (Fin k)),
          ∫ x, (k : ℝ)⁻¹ ^ 2 * (signedRules Q Q').sup' (signedRules_nonempty Q Q')
            (fun ρ ↦ ruleVal (fun i j ↦ sgnR ρ.1 * coreDiff W ε' x i j) ρ.2.1 ρ.2.2)
            ∂Measure.pi (fun _ : Fin k ↦ μ))
        ≤ ((k.choose q : ℝ)⁻¹) ^ 2 * ((k.choose q : ℝ) ^ 2 * cB) := by
          exact mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = cB := by field_simp
  -- the guessBlock cardinality cost
  have hcost : 2 * ((guessBlock k).card : ℝ) / k ≤ 2 * (q : ℝ) / k := by
    have hcard : ((guessBlock k).card : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast guessBlock_card_le k
    gcongr
  -- the rate budget
  have hbudget := afkk_error_budget (k := k) (q := q) hk (sqrt_le_natCeil_sqrt k)
    (natCeil_sqrt_le_add_one k)
  have hfinal := add_le_add (hbridge.trans (by linarith : _ ≤ cB + 2 / Real.sqrt q)) hcost
  rw [hcB_def] at hfinal
  linarith [hfinal, hbudget]

/-- **Layer 3 core — AFKK cut-norm sampling** (the one deep analytic step). The
expectation of the empirical (normalized, `1/k²`-weighted) discrete cut norm of the sampled
difference matrix `D(x)ᵢⱼ = clampEval W x i j − clampEval (chosenStep W ε') x i j` is at most
the *continuous* cut norm `cutNormDiff W (chosenStep W ε')` plus a `k`-vanishing dispersion
cost.

This is the honest content of the point-sampling lemma: a cut `A, B ⊆ [k]` of the sample can
overfit the `k` random points, so the max over the `4^k` sample cuts can exceed the true cut
norm; the AFKK / book-10.7 **Q-subsample cut-guessing** mechanism shows the excess is only
`O(k^{−1/4})` in expectation. Proof (full details in `docs/afkk-cut-guessing.md`):

* Split `[k] = Q₀ ⊔ F`, `|Q₀| = ⌈√k⌉`: entries touching `Q₀` cost `≤ 2|Q₀|/k` after the
  `1/k²` normalization (`coreTerm_restrict_fresh_block`), and the fresh-block sup is at most
  the full cut sup (`sup'_sdiff_le_sup'`).
* The full cut sup is dominated, pointwise in the sample, by the average over pairs of random
  `q`-subsets of the best of the `2·4^q` signed sign-set rules, plus `2k²/√q` — the AFKK
  guessing chain (`sup'_abs_cut_le_avg_signedRuleSup`). The subsample estimator's second
  moment is a finite `powersetCard` computation (`sum_powersetCard_abs_sub_le`), not a
  probabilistic ingredient.
* Fixed rules conditioned on the block are pointwise rules: their conditional means are
  rectangle integrals of `W − U`, hence `≤ cutNormDiff` (`ae_integral_ruleVal_le`), and their
  deviations obey a McDiarmid-type MGF bound (bounded differences `4k`) combined with a
  soft-max over the rules, `√(8k³(2q+1)·log 2)` in total (`integral_signedRuleSup_le`).
* Both `±` directions ride inside the signed rule index. At `q = ⌈√k⌉` the rate budget is
  `32/5 · k^{−1/4} ≤ 8·k^{−1/4}` for `k ≥ 2401` (`afkk_error_budget`); smaller `k` are
  trivial (`guessBlock_integral_le_cutNormDiff_of_small`).

References: Lovász, *Large Networks*, Lemma 10.7; AFKK, JCSS 67 (2003), Lemma 3;
arXiv:2203.07581 §6.2 + Appendix §10. -/
private theorem coreTerm_expectation_le_cutNormDiff (W : Graphon α μ) (ε' : ℝ) (hε' : 0 < ε')
    {k : ℕ} [NeZero k] :
    ∫ x, coreTerm W ε' k x ∂Measure.pi (fun _ : Fin k ↦ μ) ≤
      cutNormDiff W (chosenStep W ε') + 8 * ((k : ℝ) ^ (-(1 / 4 : ℝ))) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  set π : Measure (Fin k → α) := Measure.pi (fun _ : Fin k ↦ μ) with hπ
  -- the `1/k²`-normalized fresh-block discrete cut norm, as a function of the sample
  set g : (Fin k → α) → ℝ := fun x ↦ (k : ℝ)⁻¹ ^ 2 *
      (Finset.univ : Finset (Finset (Fin k) × Finset (Fin k))).sup' Finset.univ_nonempty
        (fun AB ↦ |∑ i ∈ AB.1 \ guessBlock k, ∑ j ∈ AB.2 \ guessBlock k,
          coreDiff W ε' x i j|) with hg
  -- `g` is measurable (finite `sup'` of measurable functions of the sample)
  have hg_meas : Measurable g := by
    have heq : g = fun x ↦ (k : ℝ)⁻¹ ^ 2 * Finset.univ.sup' Finset.univ_nonempty
        (fun (AB : Finset (Fin k) × Finset (Fin k)) (x : Fin k → α) ↦
          |∑ i ∈ AB.1 \ guessBlock k, ∑ j ∈ AB.2 \ guessBlock k, coreDiff W ε' x i j|) x := by
      funext x; rw [hg, Finset.sup'_apply]
    rw [heq]
    refine measurable_const.mul (Finset.measurable_sup' _ (fun AB _ ↦ ?_))
    refine continuous_abs.measurable.comp
      (Finset.measurable_sum _ (fun i _ ↦ Finset.measurable_sum _ (fun j _ ↦ ?_)))
    simp only [coreDiff]
    exact (measurable_clampEval W i j).sub (measurable_clampEval (chosenStep W ε') i j)
  -- `g ∈ [0,1]`, hence integrable on the probability measure `π`
  have hg_nn : ∀ x, 0 ≤ g x := by
    intro x
    rw [hg]
    refine mul_nonneg (by positivity) (le_trans ?_
      (Finset.le_sup' (fun AB : Finset (Fin k) × Finset (Fin k) ↦
          |∑ i ∈ AB.1 \ guessBlock k, ∑ j ∈ AB.2 \ guessBlock k, coreDiff W ε' x i j|)
        (Finset.mem_univ ((∅, ∅) : Finset (Fin k) × Finset (Fin k)))))
    exact abs_nonneg _
  have hg_le : ∀ x, g x ≤ 1 := by
    intro x
    rw [hg]
    have hsup : Finset.univ.sup' Finset.univ_nonempty
        (fun AB : Finset (Fin k) × Finset (Fin k) ↦
          |∑ i ∈ AB.1 \ guessBlock k, ∑ j ∈ AB.2 \ guessBlock k, coreDiff W ε' x i j|)
        ≤ (k : ℝ) ^ 2 := by
      refine Finset.sup'_le _ _ (fun AB _ ↦ ?_)
      refine (abs_coreDiff_rect_le W ε' x _ _).trans ?_
      have hc : ∀ S : Finset (Fin k), ((S \ guessBlock k).card : ℝ) ≤ k := by
        intro S
        calc ((S \ guessBlock k).card : ℝ)
            ≤ ((Finset.univ : Finset (Fin k)).card : ℝ) := by
              exact_mod_cast Finset.card_le_card (Finset.subset_univ _)
          _ = k := by rw [Finset.card_univ, Fintype.card_fin]
      calc ((AB.1 \ guessBlock k).card : ℝ) * ((AB.2 \ guessBlock k).card : ℝ)
          ≤ (k : ℝ) * k := mul_le_mul (hc _) (hc _) (by positivity) (by positivity)
        _ = (k : ℝ) ^ 2 := by ring
    calc (k : ℝ)⁻¹ ^ 2 * _
        ≤ (k : ℝ)⁻¹ ^ 2 * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsup (by positivity)
      _ = 1 := by field_simp
  have hg_int : Integrable g π :=
    (integrable_const (1 : ℝ)).mono' hg_meas.aestronglyMeasurable
      (ae_of_all _ (fun x ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn x)]; exact hg_le x))
  -- integrate the block-split reduction `coreTerm_restrict_fresh_block`
  have hstep : ∫ x, coreTerm W ε' k x ∂π
      ≤ (∫ x, g x ∂π) + 2 * ((guessBlock k).card : ℝ) / k := by
    have hmono : ∫ x, coreTerm W ε' k x ∂π
        ≤ ∫ x, (g x + 2 * ((guessBlock k).card : ℝ) / k) ∂π := by
      refine integral_mono_of_nonneg (ae_of_all _ (fun x ↦ coreTerm_nonneg W ε' k x))
        (hg_int.add (integrable_const _)) (ae_of_all _ (fun x ↦ ?_))
      rw [hg]
      exact coreTerm_restrict_fresh_block W ε' x (guessBlock k)
    rwa [integral_add hg_int (integrable_const _), integral_const, smul_eq_mul,
      probReal_univ, one_mul] at hmono
  refine hstep.trans ?_
  simp only [hg, hπ]
  exact guessBlock_integral_le_cutNormDiff W ε' hε'

/-- **Layer 3 — the core-term expectation bound.** Combines the AFKK sampling core
`coreTerm_expectation_le_cutNormDiff` with the Frieze–Kannan budget
`chosenStep_cutNormDiff_le`: the expectation of the core term is at most `ε'` plus a
`k`-vanishing dispersion cost. Part of the `first_sampling_lemma` analytic accounting,
NOT a new live input. -/
private theorem coreTerm_expectation_bound (W : Graphon α μ) (ε' : ℝ) (hε' : 0 < ε')
    {k : ℕ} [NeZero k] :
    ∫ x, coreTerm W ε' k x ∂Measure.pi (fun _ : Fin k ↦ μ) ≤
      ε' + 8 * ((k : ℝ) ^ (-(1 / 4 : ℝ))) := by
  refine le_trans (coreTerm_expectation_le_cutNormDiff W ε' hε') ?_
  gcongr
  exact chosenStep_cutNormDiff_le W hε'

/-! ### Layer 4 — event packaging (Markov) and the uniform target theorem -/

/-- The frequency term is integrable: it is bounded by a constant on the finite-measure
product space (crude uniform bound `freqTerm_le`). -/
theorem integrable_freqTerm (W : Graphon α μ) (ε' : ℝ) (k : ℕ) [NeZero k] :
    Integrable (fun x : Fin k → α ↦ freqTerm W ε' k x) (Measure.pi (fun _ : Fin k ↦ μ)) := by
  refine Integrable.mono' (integrable_const (2 * ((chosenPartition W ε').parts.card) + 1 : ℝ))
    (measurable_freqTerm W ε' k).aestronglyMeasurable (ae_of_all _ (fun x ↦ ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (freqTerm_nonneg W ε' k x)]
  exact freqTerm_le W ε' k x

/-- The core term is integrable: it is bounded by `1` on the finite-measure product space
(`coreTerm_le_one`). -/
theorem integrable_coreTerm (W : Graphon α μ) (ε' : ℝ) (k : ℕ) [NeZero k] :
    Integrable (fun x : Fin k → α ↦ coreTerm W ε' k x) (Measure.pi (fun _ : Fin k ↦ μ)) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_coreTerm W ε' k).aestronglyMeasurable (ae_of_all _ (fun x ↦ ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (coreTerm_nonneg W ε' k x)]
  exact coreTerm_le_one W ε' k x

/-- **Markov event packaging.** On a probability space, given a nonnegative integrable `f`
a.e.-dominating `g`, if `∫ f < c·η` then the set `{f < c}` (minus a null domination-failure
set) is a measurable witness of measure `≥ 1 − η` on which `g < c` holds pointwise. This is
the qualitative concentration step (Markov's inequality on the majorant), NOT a new
mathematical input. -/
private theorem exists_event_set_of_integral_lt {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] (f g : Ω → ℝ) (hf_meas : Measurable f) (hf_int : Integrable f ν)
    (hf_nn : ∀ x, 0 ≤ f x) (hdom : ∀ᵐ x ∂ν, g x ≤ f x) {c η : ℝ} (hc : 0 < c)
    (hbound : ∫ x, f x ∂ν < c * η) :
    ∃ X : Set Ω, MeasurableSet X ∧ 1 - η ≤ (ν X).toReal ∧ ∀ x ∈ X, g x < c := by
  set Y : Set Ω := {x | f x < c} with hYdef
  have hY_meas : MeasurableSet Y := measurableSet_lt hf_meas measurable_const
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hf_nn) hf_int c
  have hlt : c * ν.real {x | c ≤ f x} < c * η := lt_of_le_of_lt hmarkov hbound
  have hcompl : ν.real {x | c ≤ f x} < η := lt_of_mul_lt_mul_left hlt hc.le
  have hset : {x | c ≤ f x} = Yᶜ := by rw [hYdef]; ext x; simp [not_lt]
  have hcompl2 : ν.real Yᶜ = 1 - ν.real Y := probReal_compl_eq_one_sub hY_meas
  rw [hset, hcompl2] at hcompl
  have hYmeasure : 1 - η ≤ (ν Y).toReal := by
    have hrfl : ν.real Y = (ν Y).toReal := rfl
    rw [hrfl] at hcompl; linarith
  set N : Set Ω := {x | ¬ g x ≤ f x} with hNdef
  have hN_null : ν N = 0 := by rw [hNdef, ← ae_iff]; exact hdom
  set N' : Set Ω := toMeasurable ν N with hN'def
  have hN'_meas : MeasurableSet N' := measurableSet_toMeasurable ν N
  have hN'_null : ν N' = 0 := by rw [hN'def, measure_toMeasurable]; exact hN_null
  have hN_sub : N ⊆ N' := subset_toMeasurable ν N
  refine ⟨Y \ N', hY_meas.diff hN'_meas, ?_, ?_⟩
  · rw [measure_sdiff_null hN'_null]; exact hYmeasure
  · rintro x ⟨hxY, hxN'⟩
    have hxN : x ∉ N := fun h ↦ hxN' (hN_sub h)
    have hdomx : g x ≤ f x := by by_contra h; exact hxN h
    have hfx : f x < c := hxY
    linarith

/-- **The point-sampling half of the First Sampling Lemma**.
With `W`-uniform `K`: for all `k ≥ K`, the weighted sampled graphon `H_{W,x}` is within
cut distance `ε` of `W` outside a bad set of measure `≤ η`.

Proof: at accuracy `ε' := εη/4`, the majorant's expectation is
`≤ 2ε' + regularityBound ε'/√k + 1/k + 8·k^{-1/4} < εη` for all large `k` — uniformly in
`W`, since `regularityBound` is `W`-free; Markov applied to the nonnegative integrable
majorant plus the a.e. domination `ae_cutDistance_le_pointSamplingMajorant` packages the
measurable event set.

Together with `rounding_event_of_large_k` and `sampleGoodMassOn_of_events`, this
closes `first_sampling_lemma` (the recombination). -/
theorem point_sampling_event_of_large_k (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ (_ : NeZero k), ∀ W : Graphon α μ,
      PointSamplingEvent W k ε η := by
  set ε' : ℝ := ε * η / 4 with hε'def
  have hε' : 0 < ε' := by rw [hε'def]; have := mul_pos hε hη; linarith
  set M : ℕ := regularityBound ε' with hMdef
  -- the dispersion tail vanishes as `k → ∞`, uniformly in `W` (`M` does not depend on `W`)
  have htail : Tendsto
      (fun k : ℕ ↦ (M : ℝ) / Real.sqrt k + (k : ℝ)⁻¹ + 8 * (k : ℝ) ^ (-(1 / 4 : ℝ)))
      atTop (nhds 0) := by
    have h1 : Tendsto (fun k : ℕ ↦ (M : ℝ) / Real.sqrt k) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have h2 : Tendsto (fun k : ℕ ↦ (k : ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have h3 : Tendsto (fun k : ℕ ↦ 8 * (k : ℝ) ^ (-(1 / 4 : ℝ))) atTop (nhds 0) := by
      have h4 := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
        tendsto_natCast_atTop_atTop).const_mul (8 : ℝ)
      simpa using h4
    simpa using (h1.add h2).add h3
  have hεη : (0 : ℝ) < ε * η / 2 := by have := mul_pos hε hη; linarith
  have hev : ∀ᶠ k : ℕ in atTop,
      (M : ℝ) / Real.sqrt k + (k : ℝ)⁻¹ + 8 * (k : ℝ) ^ (-(1 / 4 : ℝ)) < ε * η / 2 :=
    htail.eventually_lt_const hεη
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  refine ⟨K, fun k hk hNe W ↦ ?_⟩
  haveI := hNe
  have htk := hK k hk
  -- the Frieze–Kannan cell count is `≤ M`, uniformly in `W`
  have hcard : ((chosenPartition W ε').parts.card : ℝ) ≤ (M : ℝ) := by
    have hc : (chosenPartition W ε').parts.card ≤ regularityBound ε' := by
      unfold chosenPartition; rw [dif_pos hε']; exact (regularity W ε' hε').choose_spec.1
    rw [hMdef]; exact_mod_cast hc
  -- expectation of the majorant splits into the three layers
  have hsplit : ∫ x, pointSamplingMajorant W ε' k x ∂Measure.pi (fun _ : Fin k ↦ μ)
      = ε' + ∫ x, freqTerm W ε' k x ∂Measure.pi (fun _ : Fin k ↦ μ)
        + ∫ x, coreTerm W ε' k x ∂Measure.pi (fun _ : Fin k ↦ μ) := by
    have hint1 : Integrable (fun x : Fin k → α ↦ ε' + freqTerm W ε' k x)
        (Measure.pi (fun _ : Fin k ↦ μ)) :=
      (integrable_const ε').add (integrable_freqTerm W ε' k)
    simp only [pointSamplingMajorant]
    rw [integral_add hint1 (integrable_coreTerm W ε' k),
      integral_add (integrable_const ε') (integrable_freqTerm W ε' k),
      integral_const, smul_eq_mul, probReal_univ, one_mul]
  have hfbound : ∫ x, freqTerm W ε' k x ∂Measure.pi (fun _ : Fin k ↦ μ)
      ≤ (M : ℝ) / Real.sqrt k + (k : ℝ)⁻¹ := by
    refine (freqTerm_expectation_bound W ε' k).trans ?_
    gcongr
  have hcbound : ∫ x, coreTerm W ε' k x ∂Measure.pi (fun _ : Fin k ↦ μ)
      ≤ ε' + 8 * (k : ℝ) ^ (-(1 / 4 : ℝ)) := coreTerm_expectation_bound W ε' hε'
  have hexp : ∫ x, pointSamplingMajorant W ε' k x ∂Measure.pi (fun _ : Fin k ↦ μ) < ε * η := by
    have hsum := add_le_add hfbound hcbound
    have h2eps : 2 * ε' = ε * η / 2 := by rw [hε'def]; ring
    rw [hsplit]
    linarith [hsum, htk, h2eps]
  exact exists_event_set_of_integral_lt (Measure.pi (fun _ : Fin k ↦ μ)) _ _
    (measurable_pointSamplingMajorant W ε' k) (integrable_pointSamplingMajorant W ε' k)
    (fun x ↦ pointSamplingMajorant_nonneg W hε'.le k x)
    (ae_cutDistance_le_pointSamplingMajorant W hε' k) hε hexp

end PointSamplingMajorant

end Graphon
