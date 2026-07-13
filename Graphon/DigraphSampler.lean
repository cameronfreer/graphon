/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Digraphon
import Graphon.SamplerSources
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The per-pair categorical outcome of a digraphon (directed umbrella #84, D3b step 2 / #87)

The reciprocal-edge outcome of a digraphon at a fixed pair is a **single categorical draw** over
the four states `(G i j, G j i) ∈ {0,1}²`, carrying all four probabilities — *not* two
independent Bernoullis. This file builds that mechanism from the everywhere-valid `simplexRep`:

* `Digraphon.pairPMF p` — the four-state distribution at `p`, a `PMF (Bool × Bool)` with mass
  `ENNReal.ofReal (simplexRep a b p)` on `(a, b)`;
* `Digraphon.catOutcome p` — the **one-uniform categorical map**: partition `[0,1]` by the four
  probabilities and read off the reciprocal-edge state from a single uniform;
* `Digraphon.uniform01_map_catOutcome` — **the exact four-state law**: the pushforward of the
  uniform measure under `catOutcome p` is exactly `pairPMF p`.

The generic i.i.d. sources (`MeasureTheory.uniform01`, `iidVertexSource`, `iidUniformSource`) are
reused from `Graphon.SamplerSources`; the finite/infinite samplers are the next step (D3b step 3).
-/

open MeasureTheory Set

namespace MeasureTheory.Digraphon

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} (W : Digraphon α μ)

/-! ### The four-state distribution -/

/-- **The four-state reciprocal-edge distribution** at a pair `p`, as a `PMF (Bool × Bool)`. -/
noncomputable def pairPMF (p : α × α) : PMF (Bool × Bool) :=
  PMF.ofFintype (fun ab => ENNReal.ofReal (W.simplexRep ab.1 ab.2 p))
    (by rw [← ENNReal.ofReal_sum_of_nonneg (fun ab _ => W.simplexRep_nonneg ab.1 ab.2 p),
      Fintype.sum_prod_type, W.simplexRep_sum_eq_one p, ENNReal.ofReal_one])

@[simp] theorem pairPMF_apply (p : α × α) (ab : Bool × Bool) :
    W.pairPMF p ab = ENNReal.ofReal (W.simplexRep ab.1 ab.2 p) := by
  simp only [pairPMF, PMF.ofFintype_apply]

/-! ### The one-uniform categorical outcome -/

/-- **The one-uniform categorical map**: partition `[0,1]` into four sub-intervals of lengths
`simplexRep (0,0)`, `simplexRep (0,1)`, `simplexRep (1,0)`, `simplexRep (1,1)` and read the
reciprocal-edge state off a single uniform value. -/
noncomputable def catOutcome (p : α × α) (u : ℝ) : Bool × Bool := by
  classical
  exact
    if u < W.simplexRep false false p then (false, false)
    else if u < W.simplexRep false false p + W.simplexRep false true p then (false, true)
    else if u < W.simplexRep false false p + W.simplexRep false true p + W.simplexRep true false p
      then (true, false)
    else (true, true)

theorem measurable_catOutcome (p : α × α) : Measurable (W.catOutcome p) := by
  classical
  unfold catOutcome
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const ?_
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const ?_
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const measurable_const

/-! ### The exact four-state law -/

section
variable (p : α × α)

/-- Cumulative thresholds `0 ≤ c₁ ≤ c₂ ≤ c₃ ≤ 1`. -/
private noncomputable def c1 : ℝ := W.simplexRep false false p
private noncomputable def c2 : ℝ := W.simplexRep false false p + W.simplexRep false true p
private noncomputable def c3 : ℝ :=
  W.simplexRep false false p + W.simplexRep false true p + W.simplexRep true false p

private theorem c_le : (0 : ℝ) ≤ W.c1 p ∧ W.c1 p ≤ W.c2 p ∧ W.c2 p ≤ W.c3 p ∧ W.c3 p ≤ 1 := by
  have h00 := W.simplexRep_nonneg false false p
  have h01 := W.simplexRep_nonneg false true p
  have h10 := W.simplexRep_nonneg true false p
  have h11 := W.simplexRep_nonneg true true p
  have hsum : W.simplexRep false false p + W.simplexRep false true p + W.simplexRep true false p
      + W.simplexRep true true p = 1 := by
    have h := W.simplexRep_sum_eq_one p; simp only [Fintype.sum_bool] at h; linarith
  unfold c1 c2 c3
  refine ⟨h00, by linarith, by linarith, by linarith⟩

private theorem sum_four :
    W.simplexRep false false p + W.simplexRep false true p + W.simplexRep true false p
      + W.simplexRep true true p = 1 := by
  have h := W.simplexRep_sum_eq_one p; simp only [Fintype.sum_bool] at h; linarith

/-- The preimages of the four states are the four cumulative sub-intervals. -/
private theorem catOutcome_preimage_ff :
    W.catOutcome p ⁻¹' {(false, false)} = Iio (W.c1 p) := by
  ext u
  simp only [mem_preimage, mem_singleton_iff, catOutcome, mem_Iio, c1]
  split_ifs with h1 h2 h3 <;> simp_all

private theorem catOutcome_preimage_ft :
    W.catOutcome p ⁻¹' {(false, true)} = Ico (W.c1 p) (W.c2 p) := by
  ext u
  simp only [mem_preimage, mem_singleton_iff, catOutcome, mem_Ico, c1, c2]
  constructor
  · intro h; split_ifs at h with h1 h2 h3
    · exact absurd h (by decide)
    · exact ⟨not_lt.mp h1, h2⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  · rintro ⟨hl, hr⟩
    have g1 : ¬ u < W.simplexRep false false p := by linarith
    rw [if_neg g1, if_pos hr]

private theorem catOutcome_preimage_tf :
    W.catOutcome p ⁻¹' {(true, false)} = Ico (W.c2 p) (W.c3 p) := by
  have n1 := W.simplexRep_nonneg false true p
  ext u
  simp only [mem_preimage, mem_singleton_iff, catOutcome, mem_Ico, c2, c3]
  constructor
  · intro h; split_ifs at h with h1 h2 h3
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact ⟨not_lt.mp h2, h3⟩
    · exact absurd h (by decide)
  · rintro ⟨hl, hr⟩
    have g1 : ¬ u < W.simplexRep false false p := by linarith
    have g2 : ¬ u < W.simplexRep false false p + W.simplexRep false true p := by linarith
    rw [if_neg g1, if_neg g2, if_pos hr]

private theorem catOutcome_preimage_tt :
    W.catOutcome p ⁻¹' {(true, true)} = Ici (W.c3 p) := by
  have n1 := W.simplexRep_nonneg false true p
  have n2 := W.simplexRep_nonneg true false p
  ext u
  simp only [mem_preimage, mem_singleton_iff, catOutcome, mem_Ici, c3]
  constructor
  · intro h; split_ifs at h with h1 h2 h3
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact not_lt.mp h3
  · intro hle
    have g1 : ¬ u < W.simplexRep false false p := by linarith
    have g2 : ¬ u < W.simplexRep false false p + W.simplexRep false true p := by linarith
    have g3 : ¬ u < W.simplexRep false false p + W.simplexRep false true p
        + W.simplexRep true false p := by linarith
    rw [if_neg g1, if_neg g2, if_neg g3]

private theorem uniform01_Iio {a : ℝ} (ha1 : a ≤ 1) :
    uniform01 (Iio a) = ENNReal.ofReal a := by
  rw [uniform01, Measure.restrict_apply measurableSet_Iio,
    show Iio a ∩ Icc (0 : ℝ) 1 = Ico 0 a from by
      ext x; simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
      exact ⟨fun ⟨h1, h2, _⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, le_trans h2.le ha1⟩⟩,
    Real.volume_Ico, sub_zero]

private theorem uniform01_Ico {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    uniform01 (Ico a b) = ENNReal.ofReal (b - a) := by
  rw [uniform01, Measure.restrict_apply measurableSet_Ico,
    show Ico a b ∩ Icc (0 : ℝ) 1 = Ico a b from by
      rw [inter_eq_left]; intro x hx; exact ⟨le_trans ha hx.1, le_trans hx.2.le hb⟩,
    Real.volume_Ico]

private theorem uniform01_Ici {a : ℝ} (ha : 0 ≤ a) :
    uniform01 (Ici a) = ENNReal.ofReal (1 - a) := by
  rw [uniform01, Measure.restrict_apply measurableSet_Ici,
    show Ici a ∩ Icc (0 : ℝ) 1 = Icc a 1 from by
      ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc]
      exact ⟨fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, le_trans ha h1, h2⟩⟩,
    Real.volume_Icc]

/-- **The exact four-state law**: the pushforward of the uniform measure under the one-uniform
categorical map is exactly the four-state distribution `pairPMF p`. -/
theorem uniform01_map_catOutcome :
    uniform01.map (W.catOutcome p) = (W.pairPMF p).toMeasure := by
  obtain ⟨hc0, hc12, hc23, hc31⟩ := W.c_le p
  have hsum := W.sum_four p
  refine Measure.ext_iff_singleton.mpr fun x => ?_
  rw [Measure.map_apply (W.measurable_catOutcome p) (measurableSet_singleton x),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x), pairPMF_apply]
  match x with
  | (false, false) =>
    rw [catOutcome_preimage_ff, uniform01_Iio (le_trans hc12 (le_trans hc23 hc31))]
    simp only [c1]
  | (false, true) =>
    rw [catOutcome_preimage_ft, uniform01_Ico hc0 (le_trans hc23 hc31)]
    congr 1; simp only [c1, c2]; ring
  | (true, false) =>
    rw [catOutcome_preimage_tf, uniform01_Ico (le_trans hc0 hc12) hc31]
    congr 1; simp only [c2, c3]; ring
  | (true, true) =>
    rw [catOutcome_preimage_tt, uniform01_Ici (le_trans hc0 (le_trans hc12 hc23))]
    congr 1; simp only [c3]; linarith

end

end MeasureTheory.Digraphon
