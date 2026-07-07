/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.SamplingConcentration

/-!
# The rounding half of the First Sampling Lemma

This file proves `RoundingEvent` for all sufficiently large `k`
(`rounding_event_of_large_k`): conditionally on a.e. sampled points `x`, the Bernoulli
edge rounding `G` of the weighted sampled graphon `H_{W,x}` lands within cut distance
`ε` of `H_{W,x}` with probability `≥ 1 − η`. Together with the reduction
`sampleGoodMassOn_of_events` this leaves `PointSamplingEvent` as the only analytic
content of `first_sampling_lemma`.

The proof is finite probability — no measure-theoretic randomness beyond the finite
weighted sums `sampleMassAt`:

1. **Deterministic cut certificate** (`cutNormDiff_mkStepGraphon_le_of_cuts`): the cut
   norm of a same-partition step-graphon difference is bounded by the maximum over
   finitely many vertex cuts `A, B : Finset (Fin k)` of the corresponding weighted cut
   sums. A rectangle integral decomposes over cell products
   (`rectIntegralDiff_mkStepGraphon`), and a box-constrained bilinear form is maximized
   at cuts (`abs_bilinear_box_le`, via the signed-support trick — no induction).
2. **Bad-event decomposition**: the bad rounding event is contained in the finite union
   over cut pairs of per-cut deviation events.
3. **Finite Hoeffding / union bound**: the moment generating function of a cut sum
   factorizes over independent edges (`sum_graphs_prod`, the powerset bijection), each
   edge contributing `≤ exp(λ²)` for `|λ| ≤ 1` (`Real.exp_bound`); a Chernoff argument
   over the finite sum and a union bound over `≤ 4^k` cut pairs finish. Crude constants
   throughout — only existence of large `k` matters.
-/

open MeasureTheory Set Filter Finset

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

/-! ### Layer 1(b): box-constrained bilinear forms are maximized at cuts -/

section BilinearBox

variable {k : ℕ}

/-- **Signed-support trick** (linear case): a linear form with box-constrained
coefficients is bounded by its values at finite cuts. No induction: the upper bound is
witnessed by the cut `{i | 0 ≤ φ i}`, the lower one by its complement. -/
theorem abs_sum_box_le (w φ : Fin k → ℝ) (M : ℝ)
    (hM : ∀ A : Finset (Fin k), |∑ i ∈ A, w i * φ i| ≤ M)
    (u : Fin k → ℝ) (hu : ∀ i, u i ∈ Set.Icc 0 (w i)) :
    |∑ i, u i * φ i| ≤ M := by
  classical
  rw [abs_le]
  constructor
  · -- Lower bound via the negative-support cut.
    have h1 : ∑ i ∈ Finset.univ.filter (fun i ↦ φ i < 0), w i * φ i ≤ ∑ i, u i * φ i := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ φ i < 0)
        (fun i ↦ u i * φ i)]
      refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun i hi ↦ ?_)
        (Finset.sum_nonneg fun i hi ↦ ?_)
      · have hφ : φ i < 0 := by simpa using (Finset.mem_filter.mp hi).2
        exact mul_le_mul_of_nonpos_right ((hu i).2) hφ.le
      · have hφ : 0 ≤ φ i := by
          have := (Finset.mem_filter.mp hi).2
          simpa [not_lt] using this
        exact mul_nonneg ((hu i).1) hφ
    have h2 := hM (Finset.univ.filter (fun i ↦ φ i < 0))
    rw [abs_le] at h2
    linarith [h2.1]
  · -- Upper bound via the nonnegative-support cut.
    have h1 : ∑ i, u i * φ i ≤ ∑ i ∈ Finset.univ.filter (fun i ↦ 0 ≤ φ i), w i * φ i := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ 0 ≤ φ i)
        (fun i ↦ u i * φ i)]
      refine add_le_of_le_of_nonpos (Finset.sum_le_sum fun i hi ↦ ?_)
        (Finset.sum_nonpos fun i hi ↦ ?_)
      · have hφ : 0 ≤ φ i := by simpa using (Finset.mem_filter.mp hi).2
        exact mul_le_mul_of_nonneg_right ((hu i).2) hφ
      · have hφ : φ i < 0 := by
          have := (Finset.mem_filter.mp hi).2
          simpa [not_le] using this
        exact mul_nonpos_of_nonneg_of_nonpos ((hu i).1) hφ.le
    have h2 := hM (Finset.univ.filter (fun i ↦ 0 ≤ φ i))
    rw [abs_le] at h2
    linarith [h2.2]

/-- **Box-constrained bilinear forms are maximized at cut pairs**: two applications of
the signed-support trick. -/
theorem abs_bilinear_box_le (w : Fin k → ℝ) (d : Fin k → Fin k → ℝ) (M : ℝ)
    (hM : ∀ A B : Finset (Fin k), |∑ i ∈ A, ∑ j ∈ B, (w i * w j) * d i j| ≤ M)
    (u v : Fin k → ℝ) (hu : ∀ i, u i ∈ Set.Icc 0 (w i))
    (hv : ∀ j, v j ∈ Set.Icc 0 (w j)) :
    |∑ i, ∑ j, (u i * v j) * d i j| ≤ M := by
  have hswap : ∀ (f : Fin k → ℝ) (A : Finset (Fin k)),
      ∑ i ∈ A, ∑ j, (w i * f j) * d i j = ∑ j, f j * (∑ i ∈ A, w i * d i j) := by
    intro f A
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ by ring
  have houter : ∀ A : Finset (Fin k), |∑ i ∈ A, ∑ j, (w i * v j) * d i j| ≤ M := by
    intro A
    rw [hswap v A]
    refine abs_sum_box_le w (fun j ↦ ∑ i ∈ A, w i * d i j) M (fun B ↦ ?_) v hv
    have : ∑ j ∈ B, w j * (∑ i ∈ A, w i * d i j) = ∑ i ∈ A, ∑ j ∈ B, (w i * w j) * d i j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ by ring
    rw [this]
    exact hM A B
  have hfinal : |∑ i, u i * (∑ j, v j * d i j)| ≤ M := by
    refine abs_sum_box_le w (fun i ↦ ∑ j, v j * d i j) M (fun A ↦ ?_) u hu
    have : ∑ i ∈ A, w i * (∑ j, v j * d i j) = ∑ i ∈ A, ∑ j, (w i * v j) * d i j :=
      Finset.sum_congr rfl fun i _ ↦ by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [this]
    exact houter A
  have : ∑ i, ∑ j, (u i * v j) * d i j = ∑ i, u i * (∑ j, v j * d i j) :=
    Finset.sum_congr rfl fun i _ ↦ by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [this]
  exact hfinal

end BilinearBox

/-! ### Layer 1(a): rectangle integrals of step differences decompose over cells -/

section CutCertificate

variable [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Step functions are measurable (finite sums of indicators). -/
private theorem mkStepFun_measurable' (P : MeasurablePartition α μ)
    (c : Set α → Set α → ℝ) : Measurable (mkStepFun P c) := by
  unfold mkStepFun
  refine Finset.measurable_sum _ fun S hS ↦ Finset.measurable_sum _ fun T hT ↦ ?_
  exact measurable_const.indicator ((P.measurableSet_part hS).prod (P.measurableSet_part hT))

/-- Step functions are integrable (finite sums of indicator-constants). -/
private theorem mkStepFun_integrable' (P : MeasurablePartition α μ)
    (c : Set α → Set α → ℝ) : Integrable (mkStepFun P c) (μ.prod μ) := by
  unfold mkStepFun
  refine integrable_finsetSum _ fun S hS ↦ integrable_finsetSum _ fun T hT ↦ ?_
  exact (integrable_const _).indicator ((P.measurableSet_part hS).prod (P.measurableSet_part hT))

/-- Set integral of a step function over a rectangle: the finite sum of indicators
integrates term by term. -/
theorem setIntegral_mkStepFun (P : MeasurablePartition α μ) (c : Set α → Set α → ℝ)
    (S' T' : Set α) :
    ∫ p in S' ×ˢ T', mkStepFun P c p ∂(μ.prod μ) =
      ∑ S ∈ P.parts, ∑ T ∈ P.parts,
        ((μ (S ∩ S')).toReal * (μ (T ∩ T')).toReal) * c S T := by
  unfold mkStepFun
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun S hS ↦ ?_
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun T hT ↦ ?_
      rw [integral_indicator_const _
          ((P.measurableSet_part hS).prod (P.measurableSet_part hT)),
        measureReal_def,
        Measure.restrict_apply ((P.measurableSet_part hS).prod (P.measurableSet_part hT)),
        Set.prod_inter_prod, Measure.prod_prod, ENNReal.toReal_mul, smul_eq_mul]
    · intro T hT
      exact (Integrable.indicator (integrable_const _)
        ((P.measurableSet_part hS).prod (P.measurableSet_part hT))).integrableOn
  · intro S hS
    refine (integrable_finsetSum _ fun T hT ↦ ?_).integrableOn
    exact (Integrable.indicator (integrable_const _)
      ((P.measurableSet_part hS).prod (P.measurableSet_part hT)))

/-- **Rectangle integrals of a same-partition step-graphon difference decompose over
cell products.** -/
theorem rectIntegralDiff_mkStepGraphon (P : MeasurablePartition α μ)
    (c c' : Set α → Set α → ℝ)
    (hc_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T = c T S)
    (hc_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T ∈ Set.Icc 0 1)
    (hc'_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c' S T = c' T S)
    (hc'_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c' S T ∈ Set.Icc 0 1)
    (S' T' : Set α) :
    rectIntegralDiff (mkStepGraphon P c hc_symm hc_mem)
        (mkStepGraphon P c' hc'_symm hc'_mem) S' T' =
      ∑ S ∈ P.parts, ∑ T ∈ P.parts,
        ((μ (S ∩ S')).toReal * (μ (T ∩ T')).toReal) * (c S T - c' S T) := by
  have hU_eq : ∀ᵐ p ∂(μ.prod μ),
      (mkStepGraphon P c hc_symm hc_mem).toAEEqFun p = mkStepFun P c p :=
    AEEqFun.coeFn_mk (mkStepFun P c) (mkStepFun_measurable' P c).aestronglyMeasurable
  have hW_eq : ∀ᵐ p ∂(μ.prod μ),
      (mkStepGraphon P c' hc'_symm hc'_mem).toAEEqFun p = mkStepFun P c' p :=
    AEEqFun.coeFn_mk (mkStepFun P c') (mkStepFun_measurable' P c').aestronglyMeasurable
  have hcongr : rectIntegralDiff (mkStepGraphon P c hc_symm hc_mem)
      (mkStepGraphon P c' hc'_symm hc'_mem) S' T' =
      ∫ p in S' ×ˢ T', (mkStepFun P c p - mkStepFun P c' p) ∂(μ.prod μ) := by
    unfold rectIntegralDiff
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hU_eq, hW_eq] with p h1 h2
    rw [h1, h2]
  rw [hcongr, integral_sub, setIntegral_mkStepFun P c S' T',
    setIntegral_mkStepFun P c' S' T', ← Finset.sum_sub_distrib]
  · refine Finset.sum_congr rfl fun S _ ↦ ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun T _ ↦ by ring
  · exact (mkStepFun_integrable' P c).integrableOn
  · exact (mkStepFun_integrable' P c').integrableOn

/-- **Layer 1 — the deterministic cut certificate**: the cut norm of a same-partition
step-graphon difference is bounded by the maximum weighted cut sum over finitely many
vertex cuts `A, B : Finset (Fin k)`. Combines the cell decomposition with the box
maximum principle (`abs_bilinear_box_le`), the box constraint being
`μ(cell ∩ S') ≤ μ(cell)`. -/
theorem cutNormDiff_mkStepGraphon_le_of_cuts {k : ℕ} (P : MeasurablePartition α μ)
    (ι : Fin k → Set α) (hι_mem : ∀ i, ι i ∈ P.parts)
    (hι_inj : Function.Injective ι) (hι_surj : ∀ S ∈ P.parts, ∃ i, ι i = S)
    (c c' : Set α → Set α → ℝ)
    (hc_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T = c T S)
    (hc_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T ∈ Set.Icc 0 1)
    (hc'_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c' S T = c' T S)
    (hc'_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c' S T ∈ Set.Icc 0 1)
    (M : ℝ)
    (hM : ∀ A B : Finset (Fin k),
      |∑ i ∈ A, ∑ j ∈ B, ((μ (ι i)).toReal * (μ (ι j)).toReal) *
        (c (ι i) (ι j) - c' (ι i) (ι j))| ≤ M) :
    cutNormDiff (mkStepGraphon P c hc_symm hc_mem)
      (mkStepGraphon P c' hc'_symm hc'_mem) ≤ M := by
  classical
  have hM0 : 0 ≤ M := le_trans (by simp) (hM ∅ ∅)
  -- Reindex a parts-sum through the enumeration.
  have hreindex : ∀ f : Set α → ℝ, ∑ S ∈ P.parts, f S = ∑ i : Fin k, f (ι i) := by
    intro f
    exact (Finset.sum_bij (fun i _ ↦ ι i) (fun i _ ↦ hι_mem i)
      (fun i _ j _ hij ↦ hι_inj hij)
      (fun S hS ↦ by obtain ⟨i, hi⟩ := hι_surj S hS; exact ⟨i, Finset.mem_univ i, hi⟩)
      (fun i _ ↦ rfl)).symm
  unfold cutNormDiff
  apply Real.iSup_le _ hM0; intro S'
  apply Real.iSup_le _ hM0; intro _
  apply Real.iSup_le _ hM0; intro T'
  apply Real.iSup_le _ hM0; intro _
  rw [rectIntegralDiff_mkStepGraphon P c c' hc_symm hc_mem hc'_symm hc'_mem S' T']
  rw [hreindex]
  rw [show (∑ i : Fin k, ∑ T ∈ P.parts,
      ((μ (ι i ∩ S')).toReal * (μ (T ∩ T')).toReal) * (c (ι i) T - c' (ι i) T)) =
    ∑ i : Fin k, ∑ j : Fin k,
      ((μ (ι i ∩ S')).toReal * (μ (ι j ∩ T')).toReal) * (c (ι i) (ι j) - c' (ι i) (ι j))
    from Finset.sum_congr rfl fun i _ ↦ hreindex _]
  refine abs_bilinear_box_le (fun i ↦ (μ (ι i)).toReal)
    (fun i j ↦ c (ι i) (ι j) - c' (ι i) (ι j)) M hM
    (fun i ↦ (μ (ι i ∩ S')).toReal) (fun j ↦ (μ (ι j ∩ T')).toReal)
    (fun i ↦ ⟨ENNReal.toReal_nonneg, ?_⟩) (fun j ↦ ⟨ENNReal.toReal_nonneg, ?_⟩)
  · exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono Set.inter_subset_left)
  · exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono Set.inter_subset_left)

end CutCertificate

/-! ### Layer 3: the finite Chernoff engine

Everything here is graphon-free: `massOf p G` is the Bernoulli graph distribution with
abstract edge probabilities `p`, matching `sampleMassAt W x` definitionally when
`p e := W(x_i, x_j)`. -/

section ChernoffEngine

open scoped Classical

variable {k : ℕ}

/-- The Bernoulli graph mass with abstract edge probabilities. -/
noncomputable def massOf (p : Sym2 (Fin k) → ℝ) (G : SimpleGraph (Fin k)) : ℝ :=
  (∏ e ∈ G.edgeFinset, p e) *
    ∏ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset, (1 - p e)

/-- **Independence as algebra**: a product functional of the edge states sums over all
graphs to the product of per-edge sums (the powerset bijection + `Finset.prod_add`). -/
theorem sum_graphs_prod (F F' : Sym2 (Fin k) → ℝ) :
    ∑ G : SimpleGraph (Fin k),
      (∏ e ∈ G.edgeFinset, F e) *
        ∏ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset, F' e
      = ∏ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset, (F e + F' e) := by
  have hbij : ∑ G : SimpleGraph (Fin k),
      (∏ e ∈ G.edgeFinset, F e) *
        ∏ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset, F' e =
      ∑ S ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset.powerset,
        (∏ e ∈ S, F e) * ∏ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset \ S, F' e := by
    refine Finset.sum_nbij' (fun G ↦ G.edgeFinset)
      (fun S ↦ SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin k)))) ?_ ?_ ?_ ?_ ?_
    · exact fun G _ ↦ Finset.mem_powerset.mpr (SimpleGraph.edgeFinset_mono le_top)
    · exact fun S _ ↦ Finset.mem_univ _
    · intro G _
      rw [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet]
    · intro S hS
      ext e
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet,
        Set.mem_sdiff, Finset.mem_coe, Sym2.mem_diagSet]
      refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun hdiag ↦ ?_⟩⟩
      exact (⊤ : SimpleGraph (Fin k)).not_isDiag_of_mem_edgeSet
        (SimpleGraph.mem_edgeFinset.mp ((Finset.mem_powerset.mp hS) h)) hdiag
    · exact fun G _ ↦ rfl
  rw [hbij, ← Finset.prod_add]

/-- Elementary quadratic exponential bound: `e^s ≤ 1 + s + s²` for `|s| ≤ 1`
(from `Real.exp_bound` at order 3). -/
theorem exp_le_one_add_add_sq {s : ℝ} (hs : |s| ≤ 1) :
    Real.exp s ≤ 1 + s + s ^ 2 := by
  have h := Real.exp_bound hs (by norm_num : 0 < 3)
  have hsum : ∑ i ∈ Finset.range 3, s ^ i / (Nat.factorial i : ℝ)
      = 1 + s + s ^ 2 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num [Nat.factorial]
  rw [hsum] at h
  norm_num [Nat.factorial] at h
  have h3 : |s| ^ 3 ≤ s ^ 2 := by
    calc |s| ^ 3 ≤ |s| ^ 2 := pow_le_pow_of_le_one (abs_nonneg s) hs (by norm_num)
      _ = s ^ 2 := sq_abs s
  have h2 := abs_le.mp h
  nlinarith [h2.2, h3, sq_nonneg s]

/-- **Bernoulli MGF bound** (crude Hoeffding-lemma substitute): for `p ∈ [0,1]` and
`|t| ≤ 1`, the centered Bernoulli MGF satisfies
`p·e^{t(1−p)} + (1−p)·e^{−tp} ≤ e^{t²}`. -/
theorem bernoulli_mgf_le {p t : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (ht : |t| ≤ 1) :
    p * Real.exp (t * (1 - p)) + (1 - p) * Real.exp (-(t * p)) ≤ Real.exp (t ^ 2) := by
  obtain ⟨hp0, hp1⟩ := hp
  have habs_t : |t| ≤ 1 := ht
  have h1 : |t * (1 - p)| ≤ 1 := by
    rw [abs_mul]
    calc |t| * |1 - p| ≤ 1 * 1 := by
          refine mul_le_mul habs_t ?_ (abs_nonneg _) zero_le_one
          rw [abs_le]; constructor <;> linarith
      _ = 1 := one_mul 1
  have h2 : |-(t * p)| ≤ 1 := by
    rw [abs_neg, abs_mul]
    calc |t| * |p| ≤ 1 * 1 := by
          refine mul_le_mul habs_t ?_ (abs_nonneg _) zero_le_one
          rw [abs_le]; constructor <;> linarith
      _ = 1 := one_mul 1
  have e1 := exp_le_one_add_add_sq h1
  have e2 := exp_le_one_add_add_sq h2
  have hcomb : p * Real.exp (t * (1 - p)) + (1 - p) * Real.exp (-(t * p)) ≤
      1 + t ^ 2 * (p * (1 - p) ^ 2 + (1 - p) * p ^ 2) := by
    have hb1 : p * Real.exp (t * (1 - p)) ≤ p * (1 + t * (1 - p) + (t * (1 - p)) ^ 2) :=
      mul_le_mul_of_nonneg_left e1 hp0
    have hb2 : (1 - p) * Real.exp (-(t * p)) ≤ (1 - p) * (1 + (-(t * p)) + (-(t * p)) ^ 2) :=
      mul_le_mul_of_nonneg_left e2 (by linarith)
    nlinarith [hb1, hb2]
  have hvar : p * (1 - p) ^ 2 + (1 - p) * p ^ 2 ≤ 1 := by nlinarith
  calc p * Real.exp (t * (1 - p)) + (1 - p) * Real.exp (-(t * p))
      ≤ 1 + t ^ 2 * (p * (1 - p) ^ 2 + (1 - p) * p ^ 2) := hcomb
    _ ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
    _ ≤ Real.exp (t ^ 2) := by
        have := Real.add_one_le_exp (t ^ 2)
        linarith

/-- The centered cut statistic of a graph: `Z(G) = ∑_e κ_e (χ_e(G) − p_e)`. -/
noncomputable def cutStat (p κ : Sym2 (Fin k) → ℝ) (G : SimpleGraph (Fin k)) : ℝ :=
  ∑ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset,
    κ e * ((if e ∈ G.edgeFinset then (1 : ℝ) else 0) - p e)

/-- **MGF factorization + per-edge bound**: the exponential moment of a cut statistic is
at most `exp(λ²·4·|E(⊤)|)` for `|λ| ≤ 1/2` and `|κ| ≤ 2`. -/
theorem sum_massOf_exp_cutStat_le (p κ : Sym2 (Fin k) → ℝ)
    (hp : ∀ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset, p e ∈ Set.Icc (0 : ℝ) 1)
    (hκ : ∀ e, |κ e| ≤ 2) {lam : ℝ} (hlam : |lam| ≤ 1 / 2) :
    ∑ G : SimpleGraph (Fin k), massOf p G * Real.exp (lam * cutStat p κ G) ≤
      Real.exp (lam ^ 2 * 4 * (⊤ : SimpleGraph (Fin k)).edgeFinset.card) := by
  -- Rearrange each summand into per-edge product form.
  have hterm : ∀ G : SimpleGraph (Fin k),
      massOf p G * Real.exp (lam * cutStat p κ G) =
      (∏ e ∈ G.edgeFinset, p e * Real.exp (lam * κ e * (1 - p e))) *
        ∏ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset,
          (1 - p e) * Real.exp (-(lam * κ e * p e)) := by
    intro G
    have hsplit : (⊤ : SimpleGraph (Fin k)).edgeFinset =
        G.edgeFinset ∪ ((⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset) :=
      (Finset.union_sdiff_of_subset (SimpleGraph.edgeFinset_mono le_top)).symm
    have hsum : lam * cutStat p κ G =
        (∑ e ∈ G.edgeFinset, lam * κ e * (1 - p e)) +
          ∑ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset,
            -(lam * κ e * p e) := by
      rw [cutStat, Finset.mul_sum]
      nth_rewrite 1 [hsplit]
      rw [Finset.sum_union Finset.sdiff_disjoint.symm]
      congr 1
      · exact Finset.sum_congr rfl fun e he ↦ by rw [if_pos he]; ring
      · exact Finset.sum_congr rfl fun e he ↦ by
          rw [if_neg (Finset.mem_sdiff.mp he).2]; ring
    rw [hsum, Real.exp_add, massOf, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      ← Real.exp_sum, ← Real.exp_sum]
    ring
  rw [Finset.sum_congr rfl fun G _ ↦ hterm G, sum_graphs_prod]
  -- Per-edge MGF bound.
  calc ∏ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset,
        (p e * Real.exp (lam * κ e * (1 - p e)) +
          (1 - p e) * Real.exp (-(lam * κ e * p e)))
      ≤ ∏ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset, Real.exp ((lam * κ e) ^ 2) := by
        refine Finset.prod_le_prod (fun e he ↦ ?_) (fun e he ↦ ?_)
        · have hpe := hp e he
          exact add_nonneg (mul_nonneg hpe.1 (Real.exp_nonneg _))
            (mul_nonneg (by linarith [hpe.2]) (Real.exp_nonneg _))
        · have habs : |lam * κ e| ≤ 1 := by
            rw [abs_mul]
            calc |lam| * |κ e| ≤ (1 / 2) * 2 := by
                  refine mul_le_mul hlam (hκ e) (abs_nonneg _) (by norm_num)
              _ = 1 := by norm_num
          exact bernoulli_mgf_le (hp e he) habs
    _ ≤ Real.exp (lam ^ 2 * 4 * (⊤ : SimpleGraph (Fin k)).edgeFinset.card) := by
        rw [← Real.exp_sum]
        refine Real.exp_le_exp.mpr ?_
        calc ∑ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset, (lam * κ e) ^ 2
            ≤ ∑ _e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset, lam ^ 2 * 4 := by
              refine Finset.sum_le_sum fun e _ ↦ ?_
              have h1 : (lam * κ e) ^ 2 = lam ^ 2 * (κ e) ^ 2 := by ring
              have h2 : (κ e) ^ 2 ≤ 4 := by
                have := abs_le.mp (hκ e)
                nlinarith [this.1, this.2]
              rw [h1]
              exact mul_le_mul_of_nonneg_left h2 (sq_nonneg lam)
          _ = lam ^ 2 * 4 * (⊤ : SimpleGraph (Fin k)).edgeFinset.card := by
              rw [Finset.sum_const, nsmul_eq_mul]
              ring

/-- Bernoulli graph masses are nonnegative for `[0,1]` edge probabilities. -/
theorem massOf_nonneg {p : Sym2 (Fin k) → ℝ}
    (hp : ∀ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset, p e ∈ Set.Icc (0 : ℝ) 1)
    (G : SimpleGraph (Fin k)) : 0 ≤ massOf p G := by
  refine mul_nonneg (Finset.prod_nonneg fun e he ↦ ?_)
    (Finset.prod_nonneg fun e he ↦ ?_)
  · exact (hp e (SimpleGraph.edgeFinset_mono le_top he)).1
  · have := (hp e (Finset.sdiff_subset he)).2
    linarith

/-- **One-sided Chernoff tail** for cut statistics. -/
theorem mass_tail_le (p κ : Sym2 (Fin k) → ℝ)
    (hp : ∀ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset, p e ∈ Set.Icc (0 : ℝ) 1)
    (hκ : ∀ e, |κ e| ≤ 2) {lam t : ℝ} (hlam0 : 0 ≤ lam) (hlam : |lam| ≤ 1 / 2) :
    ∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin k) ↦ t ≤ cutStat p κ G),
      massOf p G ≤
      Real.exp (lam ^ 2 * 4 * (⊤ : SimpleGraph (Fin k)).edgeFinset.card - lam * t) := by
  classical
  calc ∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin k) ↦ t ≤ cutStat p κ G),
        massOf p G
      ≤ ∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin k) ↦ t ≤ cutStat p κ G),
        massOf p G * Real.exp (lam * (cutStat p κ G - t)) := by
        refine Finset.sum_le_sum fun G hG ↦ ?_
        have ht := (Finset.mem_filter.mp hG).2
        have h1 : (1 : ℝ) ≤ Real.exp (lam * (cutStat p κ G - t)) := by
          rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
          exact Real.exp_le_exp.mpr (mul_nonneg hlam0 (by linarith))
        calc massOf p G = massOf p G * 1 := (mul_one _).symm
          _ ≤ massOf p G * Real.exp (lam * (cutStat p κ G - t)) :=
              mul_le_mul_of_nonneg_left h1 (massOf_nonneg hp G)
    _ ≤ ∑ G : SimpleGraph (Fin k), massOf p G * Real.exp (lam * (cutStat p κ G - t)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun G _ _ ↦ mul_nonneg (massOf_nonneg hp G) (Real.exp_nonneg _))
    _ = Real.exp (-(lam * t)) *
          ∑ G : SimpleGraph (Fin k), massOf p G * Real.exp (lam * cutStat p κ G) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun G _ ↦ ?_
        rw [show lam * (cutStat p κ G - t) = lam * cutStat p κ G + -(lam * t) by ring,
          Real.exp_add]
        ring
    _ ≤ Real.exp (-(lam * t)) *
          Real.exp (lam ^ 2 * 4 * (⊤ : SimpleGraph (Fin k)).edgeFinset.card) :=
        mul_le_mul_of_nonneg_left (sum_massOf_exp_cutStat_le p κ hp hκ hlam)
          (Real.exp_nonneg _)
    _ = Real.exp (lam ^ 2 * 4 * (⊤ : SimpleGraph (Fin k)).edgeFinset.card - lam * t) := by
        rw [← Real.exp_add]
        ring_nf

/-- Negating the coefficients negates the cut statistic. -/
theorem cutStat_neg (p κ : Sym2 (Fin k) → ℝ) (G : SimpleGraph (Fin k)) :
    cutStat p (fun e ↦ -κ e) G = -cutStat p κ G := by
  rw [cutStat, cutStat, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun e _ ↦ by ring

/-- **Two-sided Chernoff tail** for cut statistics. -/
theorem mass_tail_abs_le (p κ : Sym2 (Fin k) → ℝ)
    (hp : ∀ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset, p e ∈ Set.Icc (0 : ℝ) 1)
    (hκ : ∀ e, |κ e| ≤ 2) {lam t : ℝ} (hlam0 : 0 ≤ lam) (hlam : |lam| ≤ 1 / 2) :
    ∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin k) ↦ t ≤ |cutStat p κ G|),
      massOf p G ≤
      2 * Real.exp (lam ^ 2 * 4 * (⊤ : SimpleGraph (Fin k)).edgeFinset.card - lam * t) := by
  classical
  have hκ' : ∀ e, |(fun e ↦ -κ e) e| ≤ 2 := fun e ↦ by rw [abs_neg]; exact hκ e
  have hsubset : Finset.univ.filter
      (fun G : SimpleGraph (Fin k) ↦ t ≤ |cutStat p κ G|) ⊆
      Finset.univ.filter (fun G : SimpleGraph (Fin k) ↦ t ≤ cutStat p κ G) ∪
        Finset.univ.filter (fun G : SimpleGraph (Fin k) ↦ t ≤ cutStat p (fun e ↦ -κ e) G) := by
    intro G hG
    have hthis := (Finset.mem_filter.mp hG).2
    rcases le_or_gt (cutStat p κ G) 0 with hneg | hpos
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      rw [cutStat_neg]
      rw [abs_of_nonpos hneg] at hthis
      linarith
    · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      rw [abs_of_pos hpos] at hthis
      linarith
  calc ∑ G ∈ Finset.univ.filter
        (fun G : SimpleGraph (Fin k) ↦ t ≤ |cutStat p κ G|), massOf p G
      ≤ ∑ G ∈ (Finset.univ.filter (fun G : SimpleGraph (Fin k) ↦ t ≤ cutStat p κ G) ∪
          Finset.univ.filter
            (fun G : SimpleGraph (Fin k) ↦ t ≤ cutStat p (fun e ↦ -κ e) G)),
          massOf p G :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun G _ _ ↦ massOf_nonneg hp G)
    _ ≤ (∑ G ∈ Finset.univ.filter
          (fun G : SimpleGraph (Fin k) ↦ t ≤ cutStat p κ G), massOf p G) +
        ∑ G ∈ Finset.univ.filter
          (fun G : SimpleGraph (Fin k) ↦ t ≤ cutStat p (fun e ↦ -κ e) G), massOf p G :=
        by
          have hui := Finset.sum_union_inter
            (s₁ := Finset.univ.filter (fun G : SimpleGraph (Fin k) ↦ t ≤ cutStat p κ G))
            (s₂ := Finset.univ.filter
              (fun G : SimpleGraph (Fin k) ↦ t ≤ cutStat p (fun e ↦ -κ e) G))
            (f := massOf p)
          have hnn : 0 ≤ ∑ G ∈
              (Finset.univ.filter (fun G : SimpleGraph (Fin k) ↦ t ≤ cutStat p κ G) ∩
                Finset.univ.filter
                  (fun G : SimpleGraph (Fin k) ↦ t ≤ cutStat p (fun e ↦ -κ e) G)),
              massOf p G :=
            Finset.sum_nonneg fun G _ ↦ massOf_nonneg hp G
          linarith
    _ ≤ Real.exp (lam ^ 2 * 4 * (⊤ : SimpleGraph (Fin k)).edgeFinset.card - lam * t) +
        Real.exp (lam ^ 2 * 4 * (⊤ : SimpleGraph (Fin k)).edgeFinset.card - lam * t) :=
        add_le_add (mass_tail_le p κ hp hκ hlam0 hlam)
          (mass_tail_le p (fun e ↦ -κ e) hp hκ' hlam0 hlam)
    _ = 2 * Real.exp (lam ^ 2 * 4 * (⊤ : SimpleGraph (Fin k)).edgeFinset.card - lam * t) :=
        by ring

/-- **Union bound over a finite family** of cut statistics. -/
theorem mass_bad_family_le {ι : Type*} [Fintype ι] (p : Sym2 (Fin k) → ℝ)
    (κfam : ι → Sym2 (Fin k) → ℝ)
    (hp : ∀ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset, p e ∈ Set.Icc (0 : ℝ) 1)
    (hκ : ∀ i e, |κfam i e| ≤ 2) {lam t : ℝ} (hlam0 : 0 ≤ lam) (hlam : |lam| ≤ 1 / 2) :
    ∑ G ∈ Finset.univ.filter
        (fun G : SimpleGraph (Fin k) ↦ ∃ i, t ≤ |cutStat p (κfam i) G|),
      massOf p G ≤
      (Fintype.card ι) *
        (2 * Real.exp (lam ^ 2 * 4 * (⊤ : SimpleGraph (Fin k)).edgeFinset.card - lam * t)) := by
  classical
  calc ∑ G ∈ Finset.univ.filter
        (fun G : SimpleGraph (Fin k) ↦ ∃ i, t ≤ |cutStat p (κfam i) G|), massOf p G
      ≤ ∑ i : ι, ∑ G ∈ Finset.univ.filter
          (fun G : SimpleGraph (Fin k) ↦ t ≤ |cutStat p (κfam i) G|), massOf p G := by
        have hstep1 : ∀ G ∈ Finset.univ.filter
            (fun G : SimpleGraph (Fin k) ↦ ∃ i, t ≤ |cutStat p (κfam i) G|),
            massOf p G ≤
              ∑ i : ι, if t ≤ |cutStat p (κfam i) G| then massOf p G else 0 := by
          intro G hG
          obtain ⟨i₀, hi₀⟩ := (Finset.mem_filter.mp hG).2
          calc massOf p G
              = (if t ≤ |cutStat p (κfam i₀) G| then massOf p G else 0) := by
                rw [if_pos hi₀]
            _ ≤ ∑ i : ι, if t ≤ |cutStat p (κfam i) G| then massOf p G else 0 :=
                Finset.single_le_sum
                  (f := fun i ↦ if t ≤ |cutStat p (κfam i) G| then massOf p G else 0)
                  (fun i _ ↦ by
                    split_ifs
                    · exact massOf_nonneg hp G
                    · exact le_refl 0) (Finset.mem_univ i₀)
        calc ∑ G ∈ Finset.univ.filter
              (fun G : SimpleGraph (Fin k) ↦ ∃ i, t ≤ |cutStat p (κfam i) G|), massOf p G
            ≤ ∑ G ∈ Finset.univ.filter
                (fun G : SimpleGraph (Fin k) ↦ ∃ i, t ≤ |cutStat p (κfam i) G|),
                ∑ i : ι, if t ≤ |cutStat p (κfam i) G| then massOf p G else 0 :=
              Finset.sum_le_sum hstep1
          _ ≤ ∑ G : SimpleGraph (Fin k),
                ∑ i : ι, if t ≤ |cutStat p (κfam i) G| then massOf p G else 0 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun G _ _ ↦ Finset.sum_nonneg fun i _ ↦ by
                  split_ifs
                  · exact massOf_nonneg hp G
                  · exact le_refl 0)
          _ = ∑ i : ι, ∑ G : SimpleGraph (Fin k),
                if t ≤ |cutStat p (κfam i) G| then massOf p G else 0 := Finset.sum_comm
          _ = ∑ i : ι, ∑ G ∈ Finset.univ.filter
                (fun G : SimpleGraph (Fin k) ↦ t ≤ |cutStat p (κfam i) G|), massOf p G :=
              Finset.sum_congr rfl fun i _ ↦ (Finset.sum_filter _ _).symm
    _ ≤ ∑ _i : ι,
        2 * Real.exp (lam ^ 2 * 4 * (⊤ : SimpleGraph (Fin k)).edgeFinset.card - lam * t) :=
        Finset.sum_le_sum fun i _ ↦ mass_tail_abs_le p (κfam i) hp (hκ i) hlam0 hlam
    _ = (Fintype.card ι) *
        (2 * Real.exp (lam ^ 2 * 4 * (⊤ : SimpleGraph (Fin k)).edgeFinset.card - lam * t)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

end ChernoffEngine

/-! ### Layer 2(i): almost-everywhere alignment of edge parameters -/

section AeAlignment

variable [IsProbabilityMeasure μ] {k : ℕ}

/-- A.e. symmetry at a pair of coordinates (mirror of `graphonEval_mem_Icc_ae`):
the graphon's a.e. symmetry transfers along the pair evaluation map. -/
theorem graphonEval_symm_ae (W : Graphon α μ) {i j : Fin k} (hij : i ≠ j) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin k ↦ μ),
      W.toAEEqFun (x j, x i) = W.toAEEqFun (x i, x j) := by
  have h_meas : Measurable (fun x : Fin k → α ↦ (x i, x j)) :=
    Measurable.prodMk (measurable_pi_apply _) (measurable_pi_apply _)
  have h_indep : ProbabilityTheory.iIndepFun (fun l (x : Fin k → α) ↦ x l)
      (Measure.pi (fun _ : Fin k ↦ μ)) :=
    ProbabilityTheory.iIndepFun_pi (fun _ ↦ aemeasurable_id)
  have h_indep_pair := h_indep.indepFun hij
  have h_map : Measure.map (fun x ↦ (x i, x j)) (Measure.pi (fun _ : Fin k ↦ μ)) =
      (Measure.map (fun x ↦ x i) (Measure.pi (fun _ : Fin k ↦ μ))).prod
      (Measure.map (fun x ↦ x j) (Measure.pi (fun _ : Fin k ↦ μ))) := by
    rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      (measurable_pi_apply _).aemeasurable (measurable_pi_apply _).aemeasurable]
      at h_indep_pair
    exact h_indep_pair
  have h_map_eq : Measure.map (fun x ↦ (x i, x j)) (Measure.pi (fun _ : Fin k ↦ μ)) =
      μ.prod μ := by
    rw [h_map, (MeasureTheory.measurePreserving_eval (fun _ : Fin k ↦ μ) i).map_eq,
      (MeasureTheory.measurePreserving_eval (fun _ : Fin k ↦ μ) j).map_eq]
  have h_qmp : Measure.QuasiMeasurePreserving (fun x : Fin k → α ↦ (x i, x j))
      (Measure.pi (fun _ : Fin k ↦ μ)) (μ.prod μ) := by
    constructor
    · exact h_meas
    · rw [h_map_eq]
  exact h_qmp.ae W.toSymmKernel.symm'

omit [IsProbabilityMeasure μ] in
/-- Finite a.e. conjunction over a finset (the standard induction, packaged). -/
theorem ae_all_finset {β : Type*} (s : Finset β) (Φ : β → (Fin k → α) → Prop)
    (h : ∀ b ∈ s, ∀ᵐ x ∂Measure.pi (fun _ : Fin k ↦ μ), Φ b x) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin k ↦ μ), ∀ b ∈ s, Φ b x := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s' _ ih hs
    simp only [Finset.mem_insert, forall_eq_or_imp] at hs ⊢
    filter_upwards [hs.1, ih hs.2] with x hx1 hx2
    exact ⟨hx1, hx2⟩

/-- **The aligned edge-parameter event**: for a.e. sampled points, every edge parameter
is in `[0,1]` and agrees with the clamped `(min, max)`-ordered evaluation used by the
weighted sampled graphon. -/
theorem ae_edge_params_aligned (W : Graphon α μ) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin k ↦ μ),
      ∀ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset,
        W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc (0 : ℝ) 1 ∧
        min 1 (max 0 (W.toAEEqFun
            (x (min (Quot.out e).1 (Quot.out e).2), x (max (Quot.out e).1 (Quot.out e).2))))
          = W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) := by
  refine ae_all_finset _ _ fun e he ↦ ?_
  have hne : (Quot.out e).1 ≠ (Quot.out e).2 :=
    edge_out_ne (SimpleGraph.mem_edgeFinset.mp he)
  have hIcc := graphonEval_mem_Icc_ae (V := Fin k) W hne
  rcases le_or_gt (Quot.out e).1 (Quot.out e).2 with hle | hgt
  · -- out-pair already (min, max)-ordered
    have hmin : min (Quot.out e).1 (Quot.out e).2 = (Quot.out e).1 := min_eq_left hle
    have hmax : max (Quot.out e).1 (Quot.out e).2 = (Quot.out e).2 := max_eq_right hle
    filter_upwards [hIcc] with x hx
    refine ⟨hx, ?_⟩
    rw [hmin, hmax, max_eq_right hx.1, min_eq_right hx.2]
  · -- out-pair reversed: use a.e. symmetry
    have hle' := le_of_lt hgt
    have hmin : min (Quot.out e).1 (Quot.out e).2 = (Quot.out e).2 := min_eq_right hle'
    have hmax : max (Quot.out e).1 (Quot.out e).2 = (Quot.out e).1 := max_eq_left hle'
    have hsymm := graphonEval_symm_ae W (i := (Quot.out e).2) (j := (Quot.out e).1) hne.symm
    filter_upwards [hIcc, hsymm] with x hx hsx
    refine ⟨hx, ?_⟩
    rw [hmin, hmax, hsx]
    have hx' : W.toAEEqFun (x (Quot.out e).2, x (Quot.out e).1) ∈ Set.Icc (0 : ℝ) 1 :=
      hsx ▸ hx
    rw [max_eq_right hx'.1, min_eq_right hx'.2]

end AeAlignment

/-! ### Layer 2(ii): cut coefficients and the edge regrouping -/

section CutCoeff

open scoped Classical

variable {k : ℕ}

/-- The number of ordered off-diagonal pairs of the cut `A × B` mapping to the edge
`e`. -/
noncomputable def cutCoeff (A B : Finset (Fin k)) (e : Sym2 (Fin k)) : ℝ :=
  (((A ×ˢ B).filter (fun ij : Fin k × Fin k ↦ ij.1 ≠ ij.2 ∧ s(ij.1, ij.2) = e)).card : ℝ)

/-- Each edge collects at most its two orientations. -/
theorem cutCoeff_le_two (A B : Finset (Fin k)) (e : Sym2 (Fin k)) : |cutCoeff A B e| ≤ 2 := by
  rw [cutCoeff, abs_of_nonneg (by positivity)]
  have hsub : ((A ×ˢ B).filter
      (fun ij : Fin k × Fin k ↦ ij.1 ≠ ij.2 ∧ s(ij.1, ij.2) = e)) ⊆
      {((Quot.out e).1, (Quot.out e).2), ((Quot.out e).2, (Quot.out e).1)} := by
    intro ij hij
    have h2 := (Finset.mem_filter.mp hij).2.2
    have hout : s((Quot.out e).1, (Quot.out e).2) = e := Quot.out_eq e
    rw [← hout, Sym2.eq_iff] at h2
    rcases h2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Finset.mem_insert.mpr (Or.inl (Prod.ext h1 h2))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Prod.ext h1 h2)))
  calc ((((A ×ˢ B).filter
        (fun ij : Fin k × Fin k ↦ ij.1 ≠ ij.2 ∧ s(ij.1, ij.2) = e)).card : ℝ))
      ≤ (({((Quot.out e).1, (Quot.out e).2),
          ((Quot.out e).2, (Quot.out e).1)} : Finset (Fin k × Fin k)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ 2 := by
        exact_mod_cast Finset.card_insert_le _ _ |>.trans (by simp)

/-- **Edge regrouping**: a sum of an edge functional over the off-diagonal ordered pairs
of a cut equals the `cutCoeff`-weighted sum over edges. -/
theorem sum_pairs_eq_sum_edges (A B : Finset (Fin k)) (f : Sym2 (Fin k) → ℝ) :
    ∑ ij ∈ (A ×ˢ B).filter (fun ij : Fin k × Fin k ↦ ij.1 ≠ ij.2), f s(ij.1, ij.2) =
      ∑ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset, cutCoeff A B e * f e := by
  have hmaps : ∀ ij ∈ (A ×ˢ B).filter (fun ij : Fin k × Fin k ↦ ij.1 ≠ ij.2),
      s(ij.1, ij.2) ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset := by
    intro ij hij
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact (Finset.mem_filter.mp hij).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun ij ↦ f s(ij.1, ij.2))]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  have hfil : ((A ×ˢ B).filter (fun ij : Fin k × Fin k ↦ ij.1 ≠ ij.2)).filter
      (fun ij ↦ s(ij.1, ij.2) = e) =
      (A ×ˢ B).filter (fun ij : Fin k × Fin k ↦ ij.1 ≠ ij.2 ∧ s(ij.1, ij.2) = e) := by
    rw [Finset.filter_filter]
  rw [hfil]
  calc ∑ ij ∈ (A ×ˢ B).filter
        (fun ij : Fin k × Fin k ↦ ij.1 ≠ ij.2 ∧ s(ij.1, ij.2) = e), f s(ij.1, ij.2)
      = ∑ _ij ∈ (A ×ˢ B).filter
          (fun ij : Fin k × Fin k ↦ ij.1 ≠ ij.2 ∧ s(ij.1, ij.2) = e), f e := by
        refine Finset.sum_congr rfl fun ij hij ↦ ?_
        rw [(Finset.mem_filter.mp hij).2.2]
    _ = cutCoeff A B e * f e := by
        rw [Finset.sum_const, nsmul_eq_mul, cutCoeff]

end CutCoeff

/-! ### Layer 2(iii): small combinatorial and numeric ingredients -/

section SmallIngredients

variable {k : ℕ}

/-- The `(min, max)`-normalization of an unordered pair is orientation-independent. -/
theorem minmax_out {i j : Fin k} :
    min (Quot.out s(i, j)).1 (Quot.out s(i, j)).2 = min i j ∧
      max (Quot.out s(i, j)).1 (Quot.out s(i, j)).2 = max i j := by
  have hout : s((Quot.out s(i, j)).1, (Quot.out s(i, j)).2) = s(i, j) := Quot.out_eq _
  rcases Sym2.eq_iff.mp hout with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact ⟨rfl, rfl⟩
  · rw [h1, h2]; exact ⟨min_comm _ _, max_comm _ _⟩

/-- The diagonal of a cut has at most `k` ordered pairs. -/
theorem card_diag_pairs_le (A B : Finset (Fin k)) :
    (((A ×ˢ B).filter (fun ij : Fin k × Fin k ↦ ij.1 = ij.2)).card) ≤ k := by
  classical
  calc ((A ×ˢ B).filter (fun ij : Fin k × Fin k ↦ ij.1 = ij.2)).card
      ≤ ((Finset.univ : Finset (Fin k)).image (fun i ↦ (i, i))).card := by
        refine Finset.card_le_card fun ij hij ↦ ?_
        have h := (Finset.mem_filter.mp hij).2
        exact Finset.mem_image.mpr ⟨ij.1, Finset.mem_univ _, by
          exact Prod.ext rfl h⟩
    _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
    _ = k := by rw [Finset.card_univ, Fintype.card_fin]

/-- Crude edge-count bound (local copy): `|E(⊤)| ≤ k·k`. -/
private theorem top_card_le_sq :
    ((⊤ : SimpleGraph (Fin k)).edgeFinset.card) ≤ k * k := by
  classical
  calc (⊤ : SimpleGraph (Fin k)).edgeFinset.card
      ≤ Fintype.card (Sym2 (Fin k)) := Finset.card_le_univ _
    _ = (k + 1).choose 2 := by rw [Sym2.card, Fintype.card_fin]
    _ ≤ k * k := by
        rw [Nat.choose_two_right]
        simp only [Nat.add_sub_cancel]
        rcases Nat.eq_zero_or_pos k with hk | hk
        · simp [hk]
        · refine Nat.div_le_of_le_mul ?_
          calc (k + 1) * k ≤ 2 * k * k :=
                Nat.mul_le_mul_right k (by omega : k + 1 ≤ 2 * k)
            _ = 2 * (k * k) := by ring

/-- **The eventual union-bound decay**: `4^k · 2·exp(−c·k²) ≤ η` for all large `k`. -/
theorem eventually_union_bound_small (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (4 : ℝ) ^ k * (2 * Real.exp (-(c * (k : ℝ) ^ 2))) ≤ η := by
  obtain ⟨K₁, hK₁⟩ := exists_nat_ge (2 * Real.log 4 / c)
  obtain ⟨K₂, hK₂⟩ := exists_nat_ge ((2 / c) * Real.log (2 / η))
  refine ⟨max (max K₁ K₂) 1, fun k hk ↦ ?_⟩
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast le_trans (le_max_right (max K₁ K₂) 1) hk
  have hkK₁ : 2 * Real.log 4 / c ≤ (k : ℝ) :=
    le_trans hK₁ (by
      exact_mod_cast le_trans (le_max_left K₁ K₂) (le_trans (le_max_left _ 1) hk))
  have hkK₂ : (2 / c) * Real.log (2 / η) ≤ (k : ℝ) :=
    le_trans hK₂ (by
      exact_mod_cast le_trans (le_max_right K₁ K₂) (le_trans (le_max_left _ 1) hk))
  have h4k : (4 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 4) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  -- Exponent chain: k·log4 − ck² ≤ −(c/2)k² ≤ −log(2/η).
  have hexp1 : (k : ℝ) * Real.log 4 ≤ (c / 2) * (k : ℝ) ^ 2 := by
    have h1 : 2 * Real.log 4 / c * c ≤ (k : ℝ) * c := by
      exact mul_le_mul_of_nonneg_right hkK₁ hc.le
    rw [div_mul_cancel₀ _ hc.ne'] at h1
    nlinarith [hk1, sq_nonneg ((k : ℝ) - 1)]
  have hexp2 : Real.log (2 / η) ≤ (c / 2) * (k : ℝ) ^ 2 := by
    have h1 : (2 / c) * Real.log (2 / η) * c ≤ (k : ℝ) * c :=
      mul_le_mul_of_nonneg_right hkK₂ hc.le
    rw [show (2 / c) * Real.log (2 / η) * c = 2 * Real.log (2 / η) * (c / c) by ring,
      div_self hc.ne', mul_one] at h1
    have hk2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [hk1]
    nlinarith [hk2, hc]
  calc (4 : ℝ) ^ k * (2 * Real.exp (-(c * (k : ℝ) ^ 2)))
      = 2 * Real.exp ((k : ℝ) * Real.log 4 + -(c * (k : ℝ) ^ 2)) := by
        rw [h4k, Real.exp_add]; ring
    _ ≤ 2 * Real.exp (-Real.log (2 / η)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        nlinarith [hexp1, hexp2]
    _ = η := by
        rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 2 / η)]
        field_simp

end SmallIngredients

/-! ### Layer 2(iv): the rounding theorem -/

section RoundingTheorem

open scoped Classical

variable [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

/-- Collapse of the cell-existential choice through injectivity. -/
theorem choose_cell_eq {k : ℕ} [NeZero k] {i : Fin k}
    (h : ∃ i', equipartitionCell (α := α) (μ := μ) k i'
      = equipartitionCell (α := α) (μ := μ) k i) :
    h.choose = i :=
  equipartitionCell_injective (α := α) (μ := μ) k h.choose_spec

/-- **RoundingEvent holds for all sufficiently large `k`, uniformly in the graphon** —
the finite-probability half of the First Sampling Lemma. The threshold `K` depends only
on `(ε, η)`. -/
theorem rounding_event_of_large_k (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ (_ : NeZero k), ∀ W : Graphon α μ,
      RoundingEvent W k ε η := by
  classical
  -- Parameters: λ and the decay constant.
  set lam : ℝ := min (ε / 32) (1 / 2) with hlam_def
  have hlam_pos : 0 < lam := lt_min (by positivity) (by norm_num)
  have hlam_half : |lam| ≤ 1 / 2 := by
    rw [abs_of_pos hlam_pos]
    exact min_le_right _ _
  set c : ℝ := lam * ε / 8 with hc_def
  have hc_pos : 0 < c := by positivity
  obtain ⟨K₀, hK₀⟩ := eventually_union_bound_small c η hc_pos hη
  obtain ⟨K₁, hK₁⟩ := exists_nat_ge (4 / ε)
  refine ⟨max K₀ (K₁ + 1), fun k hk _ W ↦ ?_⟩
  have hkK₀ : K₀ ≤ k := le_trans (le_max_left _ _) hk
  have hk4ε : 4 / ε ≤ (k : ℝ) :=
    le_trans hK₁ (by exact_mod_cast le_trans (Nat.le_succ K₁) (le_trans (le_max_right K₀ _) hk))
  have hk_pos : 0 < (k : ℝ) := lt_of_lt_of_le (by positivity) hk4ε
  -- The a.e. good set of sampled points.
  rw [RoundingEvent]
  filter_upwards [ae_edge_params_aligned (k := k) W] with x hx
  -- Edge parameters.
  set p : Sym2 (Fin k) → ℝ :=
    fun e ↦ W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) with hp_def
  have hp : ∀ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset, p e ∈ Set.Icc (0 : ℝ) 1 :=
    fun e he ↦ (hx e he).1
  have hmass_eq : ∀ G : SimpleGraph (Fin k), sampleMassAt W x G = massOf p G :=
    fun G ↦ rfl
  -- The bad set is contained in the union of per-cut deviation events.
  set t : ℝ := ε * (k : ℝ) ^ 2 / 4 with ht_def
  have hbad_subset : Finset.univ.filter
      (fun G : SimpleGraph (Fin k) ↦
        ¬ cutDistance (sampleWeightedGraphonOn W x) (ofSimpleGraphOn G) < ε) ⊆
      Finset.univ.filter (fun G : SimpleGraph (Fin k) ↦
        ∃ AB : Finset (Fin k) × Finset (Fin k),
          t ≤ |cutStat p (cutCoeff AB.1 AB.2) G|) := by
    intro G hG
    rw [Finset.mem_filter] at hG ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hcon
    push Not at hcon
    refine hG.2 ?_
    -- All cut statistics are small, so the certificate applies with M := ε/2.
    have hM : ∀ A B : Finset (Fin k),
        |∑ i ∈ A, ∑ j ∈ B,
          (((μ (equipartitionCell (α := α) (μ := μ) k i)).toReal *
            (μ (equipartitionCell (α := α) (μ := μ) k j)).toReal)) *
          ((min 1 (max 0 (W.toAEEqFun (x (min i j), x (max i j)))) -
            (if G.Adj i j then (1 : ℝ) else 0)))| ≤ ε / 2 := by
      intro A B
      -- Weights are 1/k; pull them out.
      have hw : ∀ i : Fin k,
          (μ (equipartitionCell (α := α) (μ := μ) k i)).toReal = ((k : ℝ))⁻¹ :=
        equipartitionCell_measure k
      have hpull : ∑ i ∈ A, ∑ j ∈ B,
          (((μ (equipartitionCell (α := α) (μ := μ) k i)).toReal *
            (μ (equipartitionCell (α := α) (μ := μ) k j)).toReal)) *
          ((min 1 (max 0 (W.toAEEqFun (x (min i j), x (max i j)))) -
            (if G.Adj i j then (1 : ℝ) else 0))) =
          ((k : ℝ))⁻¹ * ((k : ℝ))⁻¹ *
          ∑ ij ∈ A ×ˢ B,
            ((min 1 (max 0 (W.toAEEqFun (x (min ij.1 ij.2), x (max ij.1 ij.2)))) -
              (if G.Adj ij.1 ij.2 then (1 : ℝ) else 0))) := by
        rw [Finset.mul_sum, Finset.sum_product]
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hw i, hw j]
      rw [hpull, abs_mul, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ ((k : ℝ))⁻¹ * ((k : ℝ))⁻¹)]
      -- Split the pair sum into off-diagonal (the cut statistic) and diagonal (≤ k).
      have hsplit_sum : ∑ ij ∈ A ×ˢ B,
          ((min 1 (max 0 (W.toAEEqFun (x (min ij.1 ij.2), x (max ij.1 ij.2)))) -
            (if G.Adj ij.1 ij.2 then (1 : ℝ) else 0))) =
          (∑ ij ∈ (A ×ˢ B).filter (fun ij : Fin k × Fin k ↦ ij.1 ≠ ij.2),
            ((min 1 (max 0 (W.toAEEqFun (x (min ij.1 ij.2), x (max ij.1 ij.2)))) -
              (if G.Adj ij.1 ij.2 then (1 : ℝ) else 0)))) +
          ∑ ij ∈ (A ×ˢ B).filter (fun ij : Fin k × Fin k ↦ ij.1 = ij.2),
            ((min 1 (max 0 (W.toAEEqFun (x (min ij.1 ij.2), x (max ij.1 ij.2)))) -
              (if G.Adj ij.1 ij.2 then (1 : ℝ) else 0))) := by
        rw [← Finset.sum_filter_add_sum_filter_not (A ×ˢ B)
          (fun ij : Fin k × Fin k ↦ ij.1 ≠ ij.2)]
        congr 1
        refine Finset.sum_congr (Finset.filter_congr fun ij _ ↦ ?_) fun _ _ ↦ rfl
        simp
      -- Off-diagonal part: each summand is the edge functional at `s(i,j)`.
      have hoff : ∑ ij ∈ (A ×ˢ B).filter (fun ij : Fin k × Fin k ↦ ij.1 ≠ ij.2),
          ((min 1 (max 0 (W.toAEEqFun (x (min ij.1 ij.2), x (max ij.1 ij.2)))) -
            (if G.Adj ij.1 ij.2 then (1 : ℝ) else 0))) =
          -(cutStat p (cutCoeff A B) G) := by
        have hstep : ∀ ij ∈ (A ×ˢ B).filter (fun ij : Fin k × Fin k ↦ ij.1 ≠ ij.2),
            ((min 1 (max 0 (W.toAEEqFun (x (min ij.1 ij.2), x (max ij.1 ij.2)))) -
              (if G.Adj ij.1 ij.2 then (1 : ℝ) else 0))) =
            (fun e ↦ p e - (if e ∈ G.edgeFinset then (1 : ℝ) else 0)) s(ij.1, ij.2) := by
          intro ij hij
          have hne := (Finset.mem_filter.mp hij).2
          have he : s(ij.1, ij.2) ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset := by
            rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
            exact hne
          have hmm := minmax_out (i := ij.1) (j := ij.2)
          have halign := (hx _ he).2
          congr 1
          · simp only [hp_def]
            rw [← halign, hmm.1, hmm.2]
          · congr 1
            rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        rw [Finset.sum_congr rfl hstep,
          sum_pairs_eq_sum_edges A B (fun e ↦ p e - (if e ∈ G.edgeFinset then 1 else 0)),
          cutStat, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun e _ ↦ by ring
      -- Diagonal part: at most `k` in absolute value.
      have hdiag : |∑ ij ∈ (A ×ˢ B).filter (fun ij : Fin k × Fin k ↦ ij.1 = ij.2),
          ((min 1 (max 0 (W.toAEEqFun (x (min ij.1 ij.2), x (max ij.1 ij.2)))) -
            (if G.Adj ij.1 ij.2 then (1 : ℝ) else 0)))| ≤ (k : ℝ) := by
        calc |∑ ij ∈ (A ×ˢ B).filter (fun ij : Fin k × Fin k ↦ ij.1 = ij.2),
            ((min 1 (max 0 (W.toAEEqFun (x (min ij.1 ij.2), x (max ij.1 ij.2)))) -
              (if G.Adj ij.1 ij.2 then (1 : ℝ) else 0)))|
            ≤ ∑ ij ∈ (A ×ˢ B).filter (fun ij : Fin k × Fin k ↦ ij.1 = ij.2),
              |(min 1 (max 0 (W.toAEEqFun (x (min ij.1 ij.2), x (max ij.1 ij.2)))) -
                (if G.Adj ij.1 ij.2 then (1 : ℝ) else 0))| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _ij ∈ (A ×ˢ B).filter (fun ij : Fin k × Fin k ↦ ij.1 = ij.2), (1 : ℝ) := by
              refine Finset.sum_le_sum fun ij hij ↦ ?_
              have hdd := (Finset.mem_filter.mp hij).2
              have hadj : ¬ G.Adj ij.1 ij.2 := by rw [hdd]; exact G.irrefl
              rw [if_neg hadj, sub_zero,
                abs_of_nonneg (le_min zero_le_one (le_max_left 0 _))]
              exact min_le_left _ _
          _ = (((A ×ˢ B).filter (fun ij : Fin k × Fin k ↦ ij.1 = ij.2)).card : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          _ ≤ (k : ℝ) := by exact_mod_cast card_diag_pairs_le A B
      rw [hsplit_sum]
      refine le_trans (mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)) ?_
      rw [hoff, abs_neg]
      refine le_trans (mul_le_mul_of_nonneg_left
        (add_le_add (hcon (A, B)).le hdiag) (by positivity)) ?_
      have hk4 : (4 : ℝ) ≤ ε * (k : ℝ) := by rw [div_le_iff₀ hε] at hk4ε; linarith
      have hkk : (0 : ℝ) < (k : ℝ) * (k : ℝ) := by positivity
      rw [show ((k : ℝ))⁻¹ * ((k : ℝ))⁻¹ = ((k : ℝ) * (k : ℝ))⁻¹ from (mul_inv _ _).symm,
        ← div_eq_inv_mul, div_le_iff₀ hkk, ht_def]
      nlinarith [hk4, hk_pos]
    refine lt_of_le_of_lt (cutDistance_le_cutNormDiff _ _)
      (lt_of_le_of_lt ?_ (by linarith : ε / 2 < ε))
    unfold sampleWeightedGraphonOn ofSimpleGraphOn
    apply cutNormDiff_mkStepGraphon_le_of_cuts (equipartition k)
      (equipartitionCell (α := α) (μ := μ) k) (equipartitionCell_mem k)
      (equipartitionCell_injective k) (equipartitionCell_surjOn k)
    intro A B
    refine le_of_eq_of_le (congrArg abs (Finset.sum_congr rfl fun i _ ↦
      Finset.sum_congr rfl fun j _ ↦ ?_)) (hM A B)
    have h₀ : (∃ i', equipartitionCell (α := α) (μ := μ) k i' = equipartitionCell k i) ∧
        (∃ j', equipartitionCell (α := α) (μ := μ) k j' = equipartitionCell k j) :=
      ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
    rw [dif_pos h₀, dif_pos h₀, choose_cell_eq h₀.1, choose_cell_eq h₀.2]
  -- Good mass ≥ 1 − η, via good + bad = 1 and bad ≤ η.
  have hone : (∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin k) ↦
        cutDistance (sampleWeightedGraphonOn W x) (ofSimpleGraphOn G) < ε),
        sampleMassAt W x G) +
      (∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin k) ↦
        ¬ cutDistance (sampleWeightedGraphonOn W x) (ofSimpleGraphOn G) < ε),
        sampleMassAt W x G) = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not]
    exact sampleMassAt_sum_eq_one W x
  have hbad_le : (∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin k) ↦
        ¬ cutDistance (sampleWeightedGraphonOn W x) (ofSimpleGraphOn G) < ε),
        sampleMassAt W x G) ≤ η := by
    simp only [hmass_eq]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hbad_subset
      (fun G _ _ ↦ massOf_nonneg hp G)) ?_
    refine le_trans (mass_bad_family_le p
      (fun AB : Finset (Fin k) × Finset (Fin k) ↦ cutCoeff AB.1 AB.2) hp
      (fun i e ↦ cutCoeff_le_two i.1 i.2 e) hlam_pos.le hlam_half) ?_
    have hcard : (Fintype.card (Finset (Fin k) × Finset (Fin k)) : ℝ) = (4 : ℝ) ^ k := by
      rw [Fintype.card_prod, Fintype.card_finset, Fintype.card_fin]
      push_cast
      rw [← mul_pow]; norm_num
    rw [hcard]
    refine le_trans ?_ (hK₀ k hkK₀)
    have hlam_le : lam ≤ ε / 32 := by rw [hlam_def]; exact min_le_left _ _
    have hE : ((⊤ : SimpleGraph (Fin k)).edgeFinset.card : ℝ) ≤ (k : ℝ) * (k : ℝ) := by
      exact_mod_cast top_card_le_sq
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
    refine Real.exp_le_exp.mpr ?_
    rw [hc_def, ht_def]
    nlinarith [mul_nonneg (sq_nonneg lam) (sub_nonneg.mpr hE),
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hlam_le) hlam_pos.le)
        (mul_pos hk_pos hk_pos).le, hlam_pos, hk_pos]
  linarith [hone, hbad_le]

end RoundingTheorem

end Graphon
