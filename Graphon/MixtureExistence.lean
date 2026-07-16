/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Graphon.MixtureConvergence
import Graphon.MixtureCoordinates
import Graphon.SamplingFinite
import Graphon.InjectionCounting

/-!
# The collision estimate for empirical mixing measures (issue #33, existence step 5)

The empirical hom-density integrals of an exchangeable graph law converge to its upper
masses, quantitatively:

* `Graphon.ExchangeableGraphLaw.sum_upperEvent_comap` — the restriction identity from
  consistency, in `ℝ≥0∞`: for every injection `e`, the upper-event mass of the
  `n`-vertex law along `e` is the upper mass of the `k`-vertex law;
* `GraphonSpace.abs_integral_homDensityCoord_empiricalMixing_sub_le` — **the collision
  estimate**: for every exchangeable law `L`,
  `|∫ homDensityCoord F d(empiricalMixing L (n+1)) − ∑_{G ⊇ F} (L.law k G).toReal|
    ≤ k²/(n+1)`.
  Injective maps contribute the exact upper mass by consistency; non-injective maps are
  bounded by their proportion.
* `GraphonSpace.abs_mixturePMF_empiricalMixing_sub_le` — **the induced-marginal
  bound**: each marginal mass of the empirical mixing measure is within `k²/(n+1)` of
  the law's mass (exact-event analogue of the collision estimate, via
  `sampleMass_ofSimpleGraphOn` and `law_eq_sum_comap`).
* `GraphonSpace.exists_mixtureExchangeableLaw_eq` — **the existence half of the
  Diaconis–Janson correspondence**: every exchangeable graph law is the mixture law of a
  probability measure on the graphon space. A Prokhorov subsequential limit of the
  empirical mixing measures (`exists_subseq_tendsto`) has the correct hom-density
  integrals by weak convergence plus the collision estimate, hence the correct marginals
  by upper-sum injectivity (`integral_homDensityCoord` + `pmf_ext_of_upperSum`).

Combined with `mixtureExchangeableLaw_injective` (`Graphon/MixtureUniqueness.lean`),
this makes the mixture map a bijection — the full representation theorem is assembled
next.
-/

open MeasureTheory

open scoped Classical ENNReal

namespace Graphon.ExchangeableGraphLaw

/-- **The exact-event restriction identity from consistency** (in `ℝ≥0∞`): for any
injection of labels, each `k`-vertex mass is the total `n`-vertex mass of its exact
preimage event. -/
theorem law_eq_sum_comap (L : Graphon.ExchangeableGraphLaw) {k n : ℕ}
    (e : Fin k ↪ Fin n) (G : SimpleGraph (Fin k)) :
    L.law k G = ∑ H : SimpleGraph (Fin n), if G = H.comap e then L.law n H else 0 := by
  rw [← L.consistent e, PMF.map_apply, tsum_fintype]

/-- **The restriction identity from consistency** (in `ℝ≥0∞`): for any injection of
labels, the mass of the upper event `F ≤ ·.comap e` under the `n`-vertex law is the
upper mass of `F` under the `k`-vertex law. -/
theorem sum_upperEvent_comap (L : Graphon.ExchangeableGraphLaw) {k n : ℕ}
    (e : Fin k ↪ Fin n) (F : SimpleGraph (Fin k)) :
    (∑ H : SimpleGraph (Fin n), if F ≤ H.comap e then L.law n H else 0) =
      ∑ G : SimpleGraph (Fin k), if F ≤ G then L.law k G else 0 := by
  have hlaw := L.law_eq_sum_comap e
  symm
  calc (∑ G : SimpleGraph (Fin k), if F ≤ G then L.law k G else 0)
      = ∑ G : SimpleGraph (Fin k), ∑ H : SimpleGraph (Fin n),
          (if F ≤ G then (if G = H.comap e then L.law n H else 0) else 0) := by
        refine Finset.sum_congr rfl fun G _ => ?_
        split
        · exact hlaw G
        · simp
    _ = ∑ H : SimpleGraph (Fin n), ∑ G : SimpleGraph (Fin k),
          (if F ≤ G then (if G = H.comap e then L.law n H else 0) else 0) :=
        Finset.sum_comm
    _ = ∑ H : SimpleGraph (Fin n), if F ≤ H.comap e then L.law n H else 0 := by
        refine Finset.sum_congr rfl fun H _ => ?_
        have hswap : ∀ G : SimpleGraph (Fin k),
            (if F ≤ G then (if G = H.comap e then L.law n H else 0) else 0) =
            if G = H.comap e then
              (if F ≤ H.comap e then L.law n H else 0) else 0 := by
          intro G
          by_cases h1 : G = H.comap e
          · subst h1
            simp
          · rw [if_neg h1, if_neg h1]
            split <;> rfl
        rw [Finset.sum_congr rfl fun G _ => hswap G,
          Finset.sum_ite_eq' Finset.univ (H.comap e)
            (fun _ => if F ≤ H.comap e then L.law n H else 0)]
        simp

end Graphon.ExchangeableGraphLaw

namespace GraphonSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ]

/-- Averaging over a finite index set: if `S` takes the value `A` outside a bad set `B`
and never deviates from `A` by more than `1`, the average deviates from `A` by at most
the bad proportion. -/
private theorem abs_avg_sub_le {ι : Type*} [Fintype ι] [Nonempty ι] (S : ι → ℝ) (A : ℝ)
    (B : Finset ι) (hgood : ∀ i ∉ B, S i = A) (hband : ∀ i, |S i - A| ≤ 1) :
    |(Fintype.card ι : ℝ)⁻¹ * ∑ i, S i - A| ≤ (B.card : ℝ) / (Fintype.card ι : ℝ) := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have h1 : (Fintype.card ι : ℝ)⁻¹ * ∑ i, (S i - A) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, S i - A := by
    rw [Finset.sum_sub_distrib, mul_sub, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      inv_mul_cancel_left₀ hcard.ne']
  rw [← h1]
  calc |(Fintype.card ι : ℝ)⁻¹ * ∑ i, (S i - A)|
      = (Fintype.card ι : ℝ)⁻¹ * |∑ i, (S i - A)| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i, |S i - A| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ = (Fintype.card ι : ℝ)⁻¹ * ∑ i ∈ B, |S i - A| := by
        congr 1
        have hzero : (∑ i ∈ Finset.univ \ B, |S i - A|) = 0 :=
          Finset.sum_eq_zero fun i hi => by
            rw [hgood i (Finset.mem_sdiff.mp hi).2, sub_self, abs_zero]
        rw [← Finset.sum_sdiff (Finset.subset_univ B), hzero, zero_add]
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ((B.card : ℝ) * 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc (∑ i ∈ B, |S i - A|)
            ≤ ∑ _i ∈ B, (1 : ℝ) := Finset.sum_le_sum fun i _ => hband i
          _ = (B.card : ℝ) * 1 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = (B.card : ℝ) / (Fintype.card ι : ℝ) := by
        rw [mul_one, div_eq_mul_inv, mul_comm]

/-- The empirical hom-density integral is the map average of the upper-event weights
under the finite law (unfolds `empiricalMixing` through `homDensity_ofSimpleGraphOn`). -/
private theorem integral_homDensityCoord_empiricalMixing
    (L : Graphon.ExchangeableGraphLaw) (n : ℕ) [NeZero n] {k : ℕ}
    (F : SimpleGraph (Fin k)) [DecidableRel F.Adj] :
    (∫ x, homDensityCoord F x
        ∂(empiricalMixing (α := α) (μ := μ) L n : Measure (GraphonSpace α μ))) =
      ((n : ℝ)⁻¹) ^ k * ∑ f : Fin k → Fin n, ∑ H : SimpleGraph (Fin n),
        (if F ≤ H.comap f then (L.law n H).toReal else 0) := by
  have hcoord : ∀ H : SimpleGraph (Fin n),
      homDensityCoord F (graphClass (α := α) (μ := μ) H) =
        ((n : ℝ)⁻¹) ^ k * ∑ f : Fin k → Fin n,
          (if F ≤ H.comap f then (1 : ℝ) else 0) := by
    intro H
    show homDensityCoord F (mk (Graphon.ofSimpleGraphOn H)) = _
    rw [homDensityCoord_mk]
    exact (Graphon.homDensity_congr_decRel F _ _ _).trans
      (Graphon.homDensity_ofSimpleGraphOn H F)
  rw [empiricalMixing_coe,
    integral_map (measurable_of_countable _).aemeasurable
      (continuous_homDensityCoord F).aestronglyMeasurable,
    PMF.integral_eq_sum]
  calc ∑ H : SimpleGraph (Fin n),
        (L.law n H).toReal • homDensityCoord F (graphClass (α := α) (μ := μ) H)
      = ∑ H : SimpleGraph (Fin n), ∑ f : Fin k → Fin n,
          ((n : ℝ)⁻¹) ^ k * (if F ≤ H.comap f then (L.law n H).toReal else 0) := by
        refine Finset.sum_congr rfl fun H _ => ?_
        rw [hcoord H, smul_eq_mul, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => ?_
        by_cases hp : F ≤ H.comap f
        · simp only [if_pos hp]; ring
        · simp only [if_neg hp]; ring
    _ = ((n : ℝ)⁻¹) ^ k * ∑ H : SimpleGraph (Fin n), ∑ f : Fin k → Fin n,
          (if F ≤ H.comap f then (L.law n H).toReal else 0) := by
        simp only [← Finset.mul_sum]
    _ = ((n : ℝ)⁻¹) ^ k * ∑ f : Fin k → Fin n, ∑ H : SimpleGraph (Fin n),
          (if F ≤ H.comap f then (L.law n H).toReal else 0) := by
        rw [Finset.sum_comm]

/-- Total mass one, in real masses. -/
private theorem sum_law_toReal (L : Graphon.ExchangeableGraphLaw) (m : ℕ) :
    ∑ H : SimpleGraph (Fin m), (L.law m H).toReal = 1 := by
  rw [← ENNReal.toReal_one, ← (L.law m).tsum_coe, tsum_fintype,
    ENNReal.toReal_sum fun H _ => PMF.apply_ne_top _ _]

/-- **The collision estimate** (issue #33, existence step 5): the empirical hom-density
integral of an exchangeable law at size `n + 1` is within `k²/(n + 1)` of the upper mass
of `F` under the `k`-vertex marginal. Injective vertex maps contribute the exact upper
mass by consistency (`sum_upperEvent_comap`); non-injective maps are controlled by the
birthday bound (`Graphon.card_not_injective_le`). -/
theorem abs_integral_homDensityCoord_empiricalMixing_sub_le
    (L : Graphon.ExchangeableGraphLaw) (n : ℕ) {k : ℕ} (F : SimpleGraph (Fin k))
    [DecidableRel F.Adj] :
    |(∫ x, homDensityCoord F x
        ∂(empiricalMixing (α := α) (μ := μ) L (n + 1) : Measure (GraphonSpace α μ))) -
      ∑ G : SimpleGraph (Fin k), (if F ≤ G then (L.law k G).toReal else 0)| ≤
      (k * k : ℝ) / (n + 1) := by
  have hA0 : 0 ≤ ∑ G : SimpleGraph (Fin k), (if F ≤ G then (L.law k G).toReal else 0) :=
    Finset.sum_nonneg fun G _ => by split; exacts [ENNReal.toReal_nonneg, le_rfl]
  have hA1 : (∑ G : SimpleGraph (Fin k), if F ≤ G then (L.law k G).toReal else 0) ≤ 1 := by
    rw [← sum_law_toReal L k]
    exact Finset.sum_le_sum fun G _ => by split; exacts [le_rfl, ENNReal.toReal_nonneg]
  rw [integral_homDensityCoord_empiricalMixing L (n + 1) F, Graphon.inv_pow_eq_card_inv n k]
  refine le_trans (abs_avg_sub_le _ _
    (Finset.univ.filter fun f : Fin k → Fin (n + 1) => ¬ Function.Injective f) ?_ ?_)
    (Graphon.card_noninjective_div_card_le n k)
  · -- injective maps contribute the exact upper mass, by consistency
    intro f hfmem
    have hf : Function.Injective f := by
      by_contra hni
      exact hfmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hni⟩)
    have h := Graphon.ExchangeableGraphLaw.sum_upperEvent_comap L ⟨f, hf⟩ F
    have h' := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_sum fun H _ => by
        split; exacts [PMF.apply_ne_top _ _, ENNReal.zero_ne_top],
      ENNReal.toReal_sum fun G _ => by
        split; exacts [PMF.apply_ne_top _ _, ENNReal.zero_ne_top]] at h'
    simpa only [Function.Embedding.coeFn_mk, apply_ite ENNReal.toReal,
      ENNReal.toReal_zero] using h'
  · -- all values lie in [0, 1], so the deviation band is 1
    intro f
    have h0 : 0 ≤ ∑ H : SimpleGraph (Fin (n + 1)),
        (if F ≤ H.comap f then (L.law (n + 1) H).toReal else 0) :=
      Finset.sum_nonneg fun H _ => by split; exacts [ENNReal.toReal_nonneg, le_rfl]
    have h1 : (∑ H : SimpleGraph (Fin (n + 1)),
        if F ≤ H.comap f then (L.law (n + 1) H).toReal else 0) ≤ 1 := by
      rw [← sum_law_toReal L (n + 1)]
      exact Finset.sum_le_sum fun H _ => by split; exacts [le_rfl, ENNReal.toReal_nonneg]
    rw [abs_le]
    constructor <;> linarith

/-- The empirical sample-mass integral is the map average of the exact-event weights
under the finite law (unfolds `empiricalMixing` through `sampleMass_ofSimpleGraphOn`). -/
private theorem integral_sampleMassCoord_empiricalMixing
    (L : Graphon.ExchangeableGraphLaw) (n : ℕ) [NeZero n] {k : ℕ}
    (G : SimpleGraph (Fin k)) :
    (∫ x, sampleMassCoord G x
        ∂(empiricalMixing (α := α) (μ := μ) L n : Measure (GraphonSpace α μ))) =
      ((n : ℝ)⁻¹) ^ k * ∑ f : Fin k → Fin n, ∑ H : SimpleGraph (Fin n),
        (if G = H.comap f then (L.law n H).toReal else 0) := by
  have hcoord : ∀ H : SimpleGraph (Fin n),
      sampleMassCoord G (graphClass (α := α) (μ := μ) H) =
        ((n : ℝ)⁻¹) ^ k * ∑ f : Fin k → Fin n,
          (if G = H.comap f then (1 : ℝ) else 0) := by
    intro H
    show sampleMassCoord G (mk (Graphon.ofSimpleGraphOn H)) = _
    rw [sampleMassCoord_mk, Graphon.sampleMass_ofSimpleGraphOn H G]
    congr 1
    exact Finset.sum_congr rfl fun f _ => if_congr eq_comm rfl rfl
  rw [empiricalMixing_coe,
    integral_map (measurable_of_countable _).aemeasurable
      (continuous_sampleMassCoord G).aestronglyMeasurable,
    PMF.integral_eq_sum]
  calc ∑ H : SimpleGraph (Fin n),
        (L.law n H).toReal • sampleMassCoord G (graphClass (α := α) (μ := μ) H)
      = ∑ H : SimpleGraph (Fin n), ∑ f : Fin k → Fin n,
          ((n : ℝ)⁻¹) ^ k * (if G = H.comap f then (L.law n H).toReal else 0) := by
        refine Finset.sum_congr rfl fun H _ => ?_
        rw [hcoord H, smul_eq_mul, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => ?_
        by_cases hp : G = H.comap f
        · simp only [if_pos hp]; ring
        · simp only [if_neg hp]; ring
    _ = ((n : ℝ)⁻¹) ^ k * ∑ H : SimpleGraph (Fin n), ∑ f : Fin k → Fin n,
          (if G = H.comap f then (L.law n H).toReal else 0) := by
        simp only [← Finset.mul_sum]
    _ = ((n : ℝ)⁻¹) ^ k * ∑ f : Fin k → Fin n, ∑ H : SimpleGraph (Fin n),
          (if G = H.comap f then (L.law n H).toReal else 0) := by
        rw [Finset.sum_comm]

/-- **The induced-marginal bound**: each `k`-vertex marginal mass of the empirical
mixing measure at size `n + 1` is within `k²/(n + 1)` of the law's mass. Injective
vertex maps contribute the exact mass by consistency (`law_eq_sum_comap`);
non-injective maps are controlled by the birthday bound. -/
theorem abs_mixturePMF_empiricalMixing_sub_le (L : Graphon.ExchangeableGraphLaw)
    (n : ℕ) {k : ℕ} (G : SimpleGraph (Fin k)) :
    |(mixturePMF (empiricalMixing (α := α) (μ := μ) L (n + 1)) k G).toReal -
      (L.law k G).toReal| ≤ (k * k : ℝ) / (n + 1) := by
  rw [mixturePMF_apply_toReal, integral_sampleMassCoord_empiricalMixing L (n + 1) G,
    Graphon.inv_pow_eq_card_inv n k]
  refine le_trans (abs_avg_sub_le _ _
    (Finset.univ.filter fun f : Fin k → Fin (n + 1) => ¬ Function.Injective f) ?_ ?_)
    (Graphon.card_noninjective_div_card_le n k)
  · -- injective maps contribute the exact mass, by consistency
    intro f hfmem
    have hf : Function.Injective f := by
      by_contra hni
      exact hfmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hni⟩)
    have h' := congrArg ENNReal.toReal (L.law_eq_sum_comap ⟨f, hf⟩ G)
    rw [ENNReal.toReal_sum fun H _ => by
        split; exacts [PMF.apply_ne_top _ _, ENNReal.zero_ne_top]] at h'
    simpa only [Function.Embedding.coeFn_mk, apply_ite ENNReal.toReal,
      ENNReal.toReal_zero] using h'.symm
  · -- all values lie in [0, 1], so the deviation band is 1
    intro f
    have h0 : 0 ≤ ∑ H : SimpleGraph (Fin (n + 1)),
        (if G = H.comap f then (L.law (n + 1) H).toReal else 0) :=
      Finset.sum_nonneg fun H _ => by split; exacts [ENNReal.toReal_nonneg, le_rfl]
    have h1 : (∑ H : SimpleGraph (Fin (n + 1)),
        if G = H.comap f then (L.law (n + 1) H).toReal else 0) ≤ 1 := by
      rw [← sum_law_toReal L (n + 1)]
      exact Finset.sum_le_sum fun H _ => by split; exacts [le_rfl, ENNReal.toReal_nonneg]
    have hA0 : (0 : ℝ) ≤ (L.law k G).toReal := ENNReal.toReal_nonneg
    have hA1 : (L.law k G).toReal ≤ 1 := by
      rw [← sum_law_toReal L k]
      exact Finset.single_le_sum (fun G' _ => ENNReal.toReal_nonneg) (Finset.mem_univ G)
    rw [abs_le]
    constructor <;> linarith

/-- **Every weak limit of empirical mixing measures along a diverging index sequence
represents the law**: weak convergence and the collision estimate identify every
hom-density integral of the limit, and upper-sum injectivity identifies the
marginals. -/
theorem mixtureExchangeableLaw_eq_of_tendsto_empiricalMixing
    (L : Graphon.ExchangeableGraphLaw) {P : ProbabilityMeasure (GraphonSpace α μ)}
    {φ : ℕ → ℕ} (hφ : Filter.Tendsto φ Filter.atTop Filter.atTop)
    (hconv : Filter.Tendsto (fun m => empiricalMixing (α := α) (μ := μ) L (φ m + 1))
      Filter.atTop (nhds P)) :
    mixtureExchangeableLaw (α := α) (μ := μ) P = L := by
  refine Graphon.ExchangeableGraphLaw.ext fun k => ?_
  rw [mixtureExchangeableLaw_law]
  refine Graphon.pmf_ext_of_upperSum fun F => ?_
  -- weak convergence: the empirical hom-density integrals converge to the limit's
  have hconv' := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv
    (homDensityCoordBCF (α := α) (μ := μ) F)
  simp only [homDensityCoordBCF_apply] at hconv'
  -- the collision estimate: the same integrals converge to the upper mass of the law
  have hbound : ∀ m : ℕ,
      |(∫ x, homDensityCoord F x
          ∂(empiricalMixing (α := α) (μ := μ) L (φ m + 1) : Measure (GraphonSpace α μ))) -
        ∑ G : SimpleGraph (Fin k), (if F ≤ G then (L.law k G).toReal else 0)| ≤
        (k * k : ℝ) / (φ m + 1) :=
    fun m => abs_integral_homDensityCoord_empiricalMixing_sub_le L (φ m) F
  have hzero : Filter.Tendsto (fun m : ℕ => (k * k : ℝ) / ((φ m : ℝ) + 1))
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds
      (Filter.tendsto_atTop_add_const_right _ 1
        (tendsto_natCast_atTop_atTop.comp hφ))
  have hlim : Filter.Tendsto (fun m : ℕ => ∫ x, homDensityCoord F x
      ∂(empiricalMixing (α := α) (μ := μ) L (φ m + 1) : Measure (GraphonSpace α μ)))
      Filter.atTop
      (nhds (∑ G : SimpleGraph (Fin k), (if F ≤ G then (L.law k G).toReal else 0))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun m => dist_nonneg)
      (fun m => by rw [Real.dist_eq]; exact hbound m) hzero
  -- identify the limit and convert to upper sums
  have hint := tendsto_nhds_unique hconv' hlim
  rw [integral_homDensityCoord P F] at hint
  simpa only [Graphon.upperSum] using hint

/-- **The existence half of the Diaconis–Janson correspondence** (issue #33): every
exchangeable graph law is the mixture law of a probability measure on the graphon
space, obtained as a Prokhorov subsequential limit of the empirical mixing measures. -/
@[blueprint "thm:mixture-existence"
  (title := /-- Existence of the graphon mixture -/)]
theorem exists_mixtureExchangeableLaw_eq (L : Graphon.ExchangeableGraphLaw) :
    ∃ P : ProbabilityMeasure (GraphonSpace α μ),
      mixtureExchangeableLaw (α := α) (μ := μ) P = L := by
  obtain ⟨P, φ, hφ, hconv⟩ := exists_subseq_tendsto
    (fun m => empiricalMixing (α := α) (μ := μ) L (m + 1))
  refine ⟨P, mixtureExchangeableLaw_eq_of_tendsto_empiricalMixing L hφ.tendsto_atTop ?_⟩
  simpa only [Function.comp_def] using hconv

end GraphonSpace
