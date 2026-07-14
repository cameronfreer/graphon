/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Digraphon
import Graphon.InfiniteDigraph
import Graphon.SamplerSources
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The categorical outcome and explicit sampler of a digraphon (#84, D3b steps 2–3 / #87)

The reciprocal-edge outcome of a digraphon at a fixed pair is a **single categorical draw** over
the four states `(G i j, G j i) ∈ {0,1}²`, carrying all four probabilities — *not* two
independent Bernoullis. This file builds that mechanism from the everywhere-valid `simplexRep`,
then the explicit finite and infinite digraph samplers on top of it:

* `Digraphon.pairPMF p` — the four-state distribution at `p`, a `PMF (Bool × Bool)` with mass
  `ENNReal.ofReal (simplexRep a b p)` on `(a, b)`;
* `Digraphon.catOutcome p` — the **one-uniform categorical map**: partition `[0,1]` by the four
  probabilities and read off the reciprocal-edge state from a single uniform;
* `Digraphon.uniform01_map_catOutcome` — **the exact four-state law**: the pushforward of the
  uniform measure under `catOutcome p` is exactly `pairPMF p`;
* `Digraphon.samplerSource μ` — the sampler source: i.i.d. vertex positions (law `μ`) and one
  `[0,1]`-uniform per off-diagonal unordered pair (`OffDiagPairIndex ℕ`), independent;
* `Digraphon.sampleAdj` — the sampler's adjacency bit at an ordered pair, in the
  **natural-number order**: the diagonal reads the loop coordinate; an off-diagonal pair reads
  one coordinate of the single categorical draw at the increasing-order positions from the one
  uniform of the unordered pair (`sampleAdj_self` / `sampleAdj_of_lt` / `sampleAdj_of_gt`);
* `Digraphon.sampleInfinite` / `Digraphon.sampleFinite n` — the explicit infinite sampler (into
  `InfiniteDigraph`) and its restriction to the first `n` vertices, both measurable in the
  sources.

The generic i.i.d. sources (`MeasureTheory.uniform01`, `iidVertexSource`, `iidUniformSource`) are
reused from `Graphon.SamplerSources`. The sampler's law (exact-event product formula,
identification with `exchangeableDigraphLawEquiv`, exchangeability, dissociation) is the next
step (D3b step 4).
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

/-- **Distributional transpose equivariance**: swapping the pair transposes the four-state
distribution. (Pointwise equivariance of `catOutcome` is neither true nor needed; this
distributional form — cashing out `simplexRep_swap` — is the statement used when `Quot.out`
picks an arbitrary ordering of an unordered pair, and for relabeling.) -/
theorem pairPMF_swap (p : α × α) : W.pairPMF p.swap = (W.pairPMF p).map Prod.swap := by
  ext ab
  rw [PMF.map_apply, pairPMF_apply, W.simplexRep_swap]
  rw [tsum_eq_single ab.swap]
  · rw [Prod.swap_swap, if_pos rfl, pairPMF_apply, Prod.fst_swap, Prod.snd_swap]
  · intro cd hcd
    rw [if_neg]
    intro h
    exact hcd (by rw [← Prod.swap_swap cd, ← h])

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

/-- **Joint measurability** of the categorical outcome in *both* the pair and the uniform — the
form the sampler needs, since it evaluates `catOutcome` at `p = (Uᵢ, Uⱼ)` varying with the
sample. Each threshold is a `simplexRep` of the pair coordinate, compared with the uniform
coordinate. -/
theorem measurable_catOutcome_joint :
    Measurable (fun z : (α × α) × ℝ => W.catOutcome z.1 z.2) := by
  classical
  unfold catOutcome
  refine Measurable.ite (measurableSet_lt measurable_snd
    ((W.measurable_simplexRep false false).comp measurable_fst)) measurable_const ?_
  refine Measurable.ite (measurableSet_lt measurable_snd
    (((W.measurable_simplexRep false false).comp measurable_fst).add
      ((W.measurable_simplexRep false true).comp measurable_fst))) measurable_const ?_
  exact Measurable.ite (measurableSet_lt measurable_snd
    ((((W.measurable_simplexRep false false).comp measurable_fst).add
      ((W.measurable_simplexRep false true).comp measurable_fst)).add
      ((W.measurable_simplexRep true false).comp measurable_fst))) measurable_const measurable_const

/-- Measurability of the categorical outcome at a fixed pair — a corollary of the joint version. -/
theorem measurable_catOutcome (p : α × α) : Measurable (W.catOutcome p) :=
  W.measurable_catOutcome_joint.comp (measurable_const.prodMk measurable_id)

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

/-- **The exact single-event factor** consumed by the product-law proof: the uniform mass of the
event that the categorical outcome equals `ab` is exactly `simplexRep ab`. -/
theorem uniform01_catOutcome_singleton (ab : Bool × Bool) :
    uniform01 {u | W.catOutcome p u = ab} = ENNReal.ofReal (W.simplexRep ab.1 ab.2 p) := by
  rw [show {u | W.catOutcome p u = ab} = W.catOutcome p ⁻¹' {ab} from rfl,
    ← Measure.map_apply (W.measurable_catOutcome p) (measurableSet_singleton ab),
    W.uniform01_map_catOutcome p, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton ab),
    pairPMF_apply]

end

/-! ### The sampler source -/

/-- **The digraph sampler source**: i.i.d. vertex positions with law `μ` and one `[0,1]`-uniform
per off-diagonal unordered pair, independent. -/
noncomputable def samplerSource (μ : Measure α) :
    Measure ((ℕ → α) × (OffDiagPairIndex ℕ → ℝ)) :=
  (iidVertexSource μ).prod (iidUniformSource (OffDiagPairIndex ℕ))

instance (μ : Measure α) [IsProbabilityMeasure μ] : IsProbabilityMeasure (samplerSource μ) := by
  rw [samplerSource]; infer_instance

/-! ### The explicit sampler (D3b step 3) -/

/-- **The sampler's adjacency bit at an ordered pair** `(i, j)`, in the natural-number order:
the diagonal reads the loop coordinate at the vertex position; an off-diagonal pair reads one
coordinate of the *single* categorical draw at the increasing-order positions — for `i < j` the
first coordinate of `catOutcome (xᵢ, xⱼ)`, for `j < i` the second coordinate of
`catOutcome (xⱼ, xᵢ)` — from the one uniform attached to the unordered pair `{i, j}`. -/
noncomputable def sampleAdj (ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ)) (i j : ℕ) : Bool :=
  if h : i < j then (W.catOutcome (ω.1 i, ω.1 j) (ω.2 (OffDiagPairIndex.mk h.ne))).1
  else if h' : j < i then (W.catOutcome (ω.1 j, ω.1 i) (ω.2 (OffDiagPairIndex.mk h'.ne))).2
  else W.loopRep (ω.1 i)

/-- **The diagonal coordinate** of the sampler: the loop bit at the vertex position. -/
@[simp] theorem sampleAdj_self (ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ)) (i : ℕ) :
    W.sampleAdj ω i i = W.loopRep (ω.1 i) := by
  rw [sampleAdj, dif_neg (lt_irrefl i), dif_neg (lt_irrefl i)]

/-- **The increasing-order coordinate** of the sampler: for `i < j`, the first component of the
categorical draw at `(xᵢ, xⱼ)`. -/
theorem sampleAdj_of_lt (ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ)) {i j : ℕ} (h : i < j) :
    W.sampleAdj ω i j = (W.catOutcome (ω.1 i, ω.1 j) (ω.2 (OffDiagPairIndex.mk h.ne))).1 := by
  rw [sampleAdj, dif_pos h]

/-- **The decreasing-order coordinate** of the sampler: for `j < i`, the second component of the
categorical draw at `(xⱼ, xᵢ)` — the *same* draw as the `(j, i)` coordinate, giving the
reciprocal-edge dependence. -/
theorem sampleAdj_of_gt (ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ)) {i j : ℕ} (h : j < i) :
    W.sampleAdj ω i j = (W.catOutcome (ω.1 j, ω.1 i) (ω.2 (OffDiagPairIndex.mk h.ne))).2 := by
  rw [sampleAdj, dif_neg (Nat.lt_asymm h), dif_pos h]

/-- **Measurability of the adjacency bit** in the sources, at each fixed ordered pair — via the
joint measurability of `catOutcome`, since the pair argument varies with the sample. -/
theorem measurable_sampleAdj (i j : ℕ) :
    Measurable fun ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ) => W.sampleAdj ω i j := by
  have hx : ∀ k : ℕ, Measurable fun ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ) => ω.1 k :=
    fun k => (measurable_pi_apply k).comp measurable_fst
  have hu : ∀ e : OffDiagPairIndex ℕ,
      Measurable fun ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ) => ω.2 e :=
    fun e => (measurable_pi_apply e).comp measurable_snd
  rcases lt_trichotomy i j with h | rfl | h
  · rw [funext fun ω => W.sampleAdj_of_lt ω h]
    exact measurable_fst.comp (W.measurable_catOutcome_joint.comp
      (((hx i).prodMk (hx j)).prodMk (hu _)))
  · rw [funext fun ω => W.sampleAdj_self ω i]
    exact W.measurable_loopRep.comp (hx i)
  · rw [funext fun ω => W.sampleAdj_of_gt ω h]
    exact measurable_snd.comp (W.measurable_catOutcome_joint.comp
      (((hx j).prodMk (hx i)).prodMk (hu _)))

/-- **The explicit infinite digraph sampler**: the relational structure whose ordered-pair
coordinates are the sampler's adjacency bits. -/
noncomputable def sampleInfinite (ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ)) : InfiniteDigraph :=
  fun c => W.sampleAdj ω (c.2 0) (c.2 1)

/-- The adjacency bit of the sampled infinite digraph, unfolded. -/
@[simp] theorem adjBit_sampleInfinite (ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ)) (i j : ℕ) :
    (W.sampleInfinite ω).adjBit i j = W.sampleAdj ω i j := rfl

/-- **The infinite digraph sampler is measurable** in the sources: each ordered-pair coordinate
is a measurable adjacency bit. -/
theorem measurable_sampleInfinite : Measurable W.sampleInfinite :=
  measurable_pi_iff.mpr fun c => W.measurable_sampleAdj (c.2 0) (c.2 1)

/-- **The finite digraph sampler**: the restriction of the infinite sampler to the first `n`
vertices. -/
noncomputable def sampleFinite (n : ℕ) (ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ)) :
    FiniteDigraph n :=
  InfiniteDigraph.restrictFin n (W.sampleInfinite ω)

/-- The ordered-pair coordinate of the sampled finite digraph, unfolded. -/
@[simp] theorem sampleFinite_apply (n : ℕ) (ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ))
    (i j : Fin n) :
    W.sampleFinite n ω (digraphCoord i j) = W.sampleAdj ω i j := rfl

theorem measurable_sampleFinite (n : ℕ) : Measurable (W.sampleFinite n) :=
  (InfiniteDigraph.measurable_restrictFin n).comp W.measurable_sampleInfinite

end MeasureTheory.Digraphon
