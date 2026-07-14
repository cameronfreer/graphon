/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Digraphon
import Graphon.InfiniteDigraph
import Graphon.InfiniteDigraphLaw
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

open MeasureTheory RelSignature Set
open scoped ENNReal

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
distributional form — cashing out `simplexRep_swap` — is the statement that handles
orientation reversal under relabeling, or any alternate ordering of an unordered pair.) -/
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

/-- **The paired coordinates at an unordered pair are the single categorical draw**: for
`i < j`, the reciprocal-edge pair `(sampleAdj ω i j, sampleAdj ω j i)` is exactly
`catOutcome (xᵢ, xⱼ)` at the pair's one uniform — the reciprocal dependence in one statement,
the form the exact-event product formula consumes. -/
theorem sampleAdj_pair_of_lt (ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ)) {i j : ℕ} (h : i < j) :
    (W.sampleAdj ω i j, W.sampleAdj ω j i) =
      W.catOutcome (ω.1 i, ω.1 j) (ω.2 (OffDiagPairIndex.mk h.ne)) := by
  rw [W.sampleAdj_of_lt ω h, W.sampleAdj_of_gt ω h]

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

/-! ### The exact finite-event product formula (D3b step 4)

The probability that the sampler realizes exactly a target finite digraph, stated over an
**arbitrary injective labeling** `ι : Fin n → ℕ` of the sampled vertices: the right-hand side
does not depend on `ι` (transpose flips are absorbed by `simplexRep_swap`), which is precisely
what makes restriction-consistency and exchangeability corollaries of this one computation. -/

section ProductFormula

variable {n : ℕ}

/-- **The exact-event integrand**: the conditional probability, given vertex positions `y`,
that the sampler realizes exactly the digraph `D` — one loop indicator per vertex and one
`simplexRep` mass per unordered pair (the single categorical draw carrying both directed
edges). -/
noncomputable def sampleEventIntegrand (D : FiniteDigraph n) (y : Fin n → α) : ℝ≥0∞ :=
  (∏ i : Fin n, if W.loopRep (y i) = D (digraphCoord i i) then 1 else 0) *
    ∏ p : {p : Fin n × Fin n // p.1 < p.2},
      ENNReal.ofReal
        (W.simplexRep (D (digraphCoord p.1.1 p.1.2)) (D (digraphCoord p.1.2 p.1.1))
          (y p.1.1, y p.1.2))

theorem measurable_sampleEventIntegrand (D : FiniteDigraph n) :
    Measurable (W.sampleEventIntegrand D) := by
  refine Measurable.mul ?_ ?_
  · refine Finset.measurable_prod _ fun i _ => ?_
    exact Measurable.ite
      ((W.measurable_loopRep.comp (measurable_pi_apply i)) (measurableSet_singleton _))
      measurable_const measurable_const
  · refine Finset.measurable_prod _ fun p _ => ?_
    exact ((W.measurable_simplexRep _ _).comp
      ((measurable_pi_apply _).prodMk (measurable_pi_apply _))).ennreal_ofReal

variable {ι : Fin n → ℕ}

/-- The source uniform coordinate of an increasing pair under an injective labeling. -/
private def pairIdx (hι : Function.Injective ι) (p : {p : Fin n × Fin n // p.1 < p.2}) :
    OffDiagPairIndex ℕ :=
  OffDiagPairIndex.mk (fun h => p.2.ne (hι h))

private theorem pairIdx_injective (hι : Function.Injective ι) :
    Function.Injective (pairIdx hι) := by
  rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨k, l⟩, hkl⟩ h
  rcases OffDiagPairIndex.mk_eq_mk.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Subtype.ext (Prod.ext (hι h1) (hι h2))
  · have hil : i = l := hι h1
    have hjk : j = k := hι h2
    subst hil; subst hjk
    exact absurd hij (lt_asymm hkl)

/-- The per-pair uniform condition at fixed vertex positions: the categorical draw at the
natural-order positions realizes the (orientation-corrected) reciprocal-edge pair of `D`. -/
private def pairCondSet (ι : Fin n → ℕ) (x : ℕ → α) (D : FiniteDigraph n)
    (p : {p : Fin n × Fin n // p.1 < p.2}) : Set ℝ :=
  if ι p.1.1 < ι p.1.2 then
    {v | W.catOutcome (x (ι p.1.1), x (ι p.1.2)) v
      = (D (digraphCoord p.1.1 p.1.2), D (digraphCoord p.1.2 p.1.1))}
  else
    {v | W.catOutcome (x (ι p.1.2), x (ι p.1.1)) v
      = (D (digraphCoord p.1.2 p.1.1), D (digraphCoord p.1.1 p.1.2))}

private theorem measurableSet_pairCondSet (ι : Fin n → ℕ) (x : ℕ → α) (D : FiniteDigraph n)
    (p : {p : Fin n × Fin n // p.1 < p.2}) : MeasurableSet (W.pairCondSet ι x D p) := by
  unfold pairCondSet
  split_ifs
  · exact W.measurable_catOutcome _ (measurableSet_singleton _)
  · exact W.measurable_catOutcome _ (measurableSet_singleton _)

/-- The uniform mass of the per-pair condition is the `simplexRep` mass, independently of the
orientation of the labeling (`simplexRep_swap` absorbs the flip). -/
private theorem uniform01_pairCondSet (ι : Fin n → ℕ) (x : ℕ → α) (D : FiniteDigraph n)
    (p : {p : Fin n × Fin n // p.1 < p.2}) :
    uniform01 (W.pairCondSet ι x D p) =
      ENNReal.ofReal (W.simplexRep (D (digraphCoord p.1.1 p.1.2))
        (D (digraphCoord p.1.2 p.1.1)) (x (ι p.1.1), x (ι p.1.2))) := by
  unfold pairCondSet
  split_ifs
  · exact W.uniform01_catOutcome_singleton _ _
  · rw [W.uniform01_catOutcome_singleton]
    exact congrArg ENNReal.ofReal (W.simplexRep_swap _ _ (x (ι p.1.1), x (ι p.1.2)))

/-- Membership in the per-pair condition captures both directed-edge coordinates at once. -/
private theorem pair_mem_iff (hι : Function.Injective ι)
    (ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ)) (D : FiniteDigraph n)
    (p : {p : Fin n × Fin n // p.1 < p.2}) :
    (W.sampleAdj ω (ι p.1.1) (ι p.1.2) = D (digraphCoord p.1.1 p.1.2) ∧
        W.sampleAdj ω (ι p.1.2) (ι p.1.1) = D (digraphCoord p.1.2 p.1.1)) ↔
      ω.2 (pairIdx hι p) ∈ W.pairCondSet ι ω.1 D p := by
  obtain ⟨⟨i, j⟩, hij⟩ := p
  have hne : ι i ≠ ι j := fun h => hij.ne (hι h)
  unfold pairCondSet pairIdx
  rcases lt_or_gt_of_ne hne with h | h
  · rw [if_pos h]
    have hp := W.sampleAdj_pair_of_lt ω h
    constructor
    · rintro ⟨h1, h2⟩
      show W.catOutcome _ _ = _
      rw [← hp]
      simp only [Prod.mk.injEq]
      exact ⟨h1, h2⟩
    · intro hmem
      have hboth := hp.trans hmem
      simp only [Prod.mk.injEq] at hboth
      exact hboth
  · rw [if_neg (lt_asymm h)]
    have hp := W.sampleAdj_pair_of_lt ω h
    have hidx : OffDiagPairIndex.mk h.ne = OffDiagPairIndex.mk (fun hh => hij.ne (hι hh)) :=
      Subtype.ext Sym2.eq_swap
    rw [hidx] at hp
    constructor
    · rintro ⟨h1, h2⟩
      show W.catOutcome _ _ = _
      rw [← hp]
      simp only [Prod.mk.injEq]
      exact ⟨h2, h1⟩
    · intro hmem
      have hboth := hp.trans hmem
      simp only [Prod.mk.injEq] at hboth
      exact ⟨hboth.2, hboth.1⟩

/-- The exact event, decomposed into a positions-only loop condition and one condition per
increasing pair on the pair's own uniform. -/
private theorem event_eq (hι : Function.Injective ι) (D : FiniteDigraph n) :
    {ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ) |
        ∀ i j : Fin n, W.sampleAdj ω (ι i) (ι j) = D (digraphCoord i j)}
      = {ω | (∀ i : Fin n, W.loopRep (ω.1 (ι i)) = D (digraphCoord i i)) ∧
          ∀ p : {p : Fin n × Fin n // p.1 < p.2},
            ω.2 (pairIdx hι p) ∈ W.pairCondSet ι ω.1 D p} := by
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    refine ⟨fun i => ?_, fun p => ?_⟩
    · have hii := h i i
      rwa [W.sampleAdj_self] at hii
    · exact (W.pair_mem_iff hι ω D p).mp ⟨h p.1.1 p.1.2, h p.1.2 p.1.1⟩
  · rintro ⟨hloop, hpair⟩ i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact ((W.pair_mem_iff hι ω D ⟨(i, j), hij⟩).mpr (hpair ⟨(i, j), hij⟩)).1
    · rw [W.sampleAdj_self]
      exact hloop i
    · exact ((W.pair_mem_iff hι ω D ⟨(j, i), hij⟩).mpr (hpair ⟨(j, i), hij⟩)).2

/-- **The exact finite-event product formula** (D3b step 4), over an arbitrary injective
labeling `ι` of the sampled vertices: the probability that the sampler realizes exactly `D`
on the labels `ι` is the integral, over i.i.d. `μ`-positions, of the loop indicators times one
`simplexRep` mass per unordered pair. The right-hand side does not depend on `ι` — the source
of consistency and exchangeability. -/
theorem samplerSource_forall_sampleAdj [IsProbabilityMeasure μ]
    (hι : Function.Injective ι) (D : FiniteDigraph n) :
    samplerSource μ
        {ω | ∀ i j : Fin n, W.sampleAdj ω (ι i) (ι j) = D (digraphCoord i j)} =
      ∫⁻ y, W.sampleEventIntegrand D y ∂(Measure.pi fun _ : Fin n => μ) := by
  classical
  -- the projections onto the finitely many relevant source coordinates
  have hprojU : Measurable fun (u : OffDiagPairIndex ℕ → ℝ)
      (p : {p : Fin n × Fin n // p.1 < p.2}) => u (pairIdx hι p) :=
    measurable_pi_iff.mpr fun p => measurable_pi_apply _
  have hprojX : Measurable fun (x : ℕ → α) (i : Fin n) => x (ι i) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply _
  -- measurability of the decomposed event
  have hE : MeasurableSet {ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ) |
      (∀ i : Fin n, W.loopRep (ω.1 (ι i)) = D (digraphCoord i i)) ∧
        ∀ p : {p : Fin n × Fin n // p.1 < p.2},
          ω.2 (pairIdx hι p) ∈ W.pairCondSet ι ω.1 D p} := by
    rw [Set.setOf_and]
    refine MeasurableSet.inter ?_ ?_
    · rw [Set.setOf_forall]
      refine MeasurableSet.iInter fun i => ?_
      exact (W.measurable_loopRep.comp
        ((measurable_pi_apply (ι i)).comp measurable_fst)) (measurableSet_singleton _)
    · rw [Set.setOf_forall]
      refine MeasurableSet.iInter fun p => ?_
      unfold pairCondSet
      split_ifs
      · have hinner : Measurable fun ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ) =>
            ((ω.1 (ι p.1.1), ω.1 (ι p.1.2)), ω.2 (pairIdx hι p)) :=
          (((measurable_pi_apply _).comp measurable_fst).prodMk
            ((measurable_pi_apply _).comp measurable_fst)).prodMk
            ((measurable_pi_apply _).comp measurable_snd)
        exact (W.measurable_catOutcome_joint.comp hinner) (measurableSet_singleton _)
      · have hinner : Measurable fun ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ) =>
            ((ω.1 (ι p.1.2), ω.1 (ι p.1.1)), ω.2 (pairIdx hι p)) :=
          (((measurable_pi_apply _).comp measurable_fst).prodMk
            ((measurable_pi_apply _).comp measurable_fst)).prodMk
            ((measurable_pi_apply _).comp measurable_snd)
        exact (W.measurable_catOutcome_joint.comp hinner) (measurableSet_singleton _)
  rw [W.event_eq hι D, samplerSource, Measure.prod_apply hE]
  -- the section over the uniforms, at fixed positions
  have hsec : ∀ x : ℕ → α,
      iidUniformSource (OffDiagPairIndex ℕ) (Prod.mk x ⁻¹'
          {ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ) |
            (∀ i : Fin n, W.loopRep (ω.1 (ι i)) = D (digraphCoord i i)) ∧
              ∀ p : {p : Fin n × Fin n // p.1 < p.2},
                ω.2 (pairIdx hι p) ∈ W.pairCondSet ι ω.1 D p}) =
        W.sampleEventIntegrand D (fun i => x (ι i)) := by
    intro x
    by_cases hx : ∀ i : Fin n, W.loopRep (x (ι i)) = D (digraphCoord i i)
    · have hpre : Prod.mk x ⁻¹' {ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ) |
          (∀ i : Fin n, W.loopRep (ω.1 (ι i)) = D (digraphCoord i i)) ∧
            ∀ p : {p : Fin n × Fin n // p.1 < p.2},
              ω.2 (pairIdx hι p) ∈ W.pairCondSet ι ω.1 D p} =
          (fun (u : OffDiagPairIndex ℕ → ℝ)
              (p : {p : Fin n × Fin n // p.1 < p.2}) => u (pairIdx hι p)) ⁻¹'
            Set.univ.pi fun p => W.pairCondSet ι x D p := by
        ext u
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies,
          hx, implies_true, true_and]
      rw [hpre, ← Measure.map_apply hprojU
          (MeasurableSet.univ_pi fun p => W.measurableSet_pairCondSet ι x D p),
        iidUniformSource, Measure.infinitePi_map_comp_of_injective _ (pairIdx_injective hι),
        Measure.pi_pi]
      unfold sampleEventIntegrand
      rw [Finset.prod_congr rfl fun i _ => if_pos (hx i), Finset.prod_const_one, one_mul]
      exact Finset.prod_congr rfl fun p _ => W.uniform01_pairCondSet ι x D p
    · have hpre : Prod.mk x ⁻¹' {ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ) |
          (∀ i : Fin n, W.loopRep (ω.1 (ι i)) = D (digraphCoord i i)) ∧
            ∀ p : {p : Fin n × Fin n // p.1 < p.2},
              ω.2 (pairIdx hι p) ∈ W.pairCondSet ι ω.1 D p} = ∅ := by
        ext u
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          not_and]
        exact fun hcon => absurd hcon hx
      obtain ⟨i, hi⟩ := not_forall.mp hx
      rw [hpre, measure_empty]
      unfold sampleEventIntegrand
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi), zero_mul]
  rw [lintegral_congr hsec]
  -- change of variables onto the finite product of positions
  have hmap : (iidVertexSource μ).map (fun (x : ℕ → α) (i : Fin n) => x (ι i)) =
      Measure.pi fun _ : Fin n => μ := by
    rw [iidVertexSource]
    exact Measure.infinitePi_map_comp_of_injective _ hι
  rw [← hmap, lintegral_map (W.measurable_sampleEventIntegrand D) hprojX]

/-- **The exact-event formula for the finite sampler**: specialization of the product formula
to the identity labeling — the mass the sampled digraph law puts on a single target `D`. -/
theorem samplerSource_sampleFinite_singleton [IsProbabilityMeasure μ] (D : FiniteDigraph n) :
    samplerSource μ {ω | W.sampleFinite n ω = D} =
      ∫⁻ y, W.sampleEventIntegrand D y ∂(Measure.pi fun _ : Fin n => μ) := by
  rw [show {ω | W.sampleFinite n ω = D} =
      {ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ) |
        ∀ i j : Fin n, W.sampleAdj ω ↑i ↑j = D (digraphCoord i j)} from
    Set.ext fun ω => digraphStructure_ext_iff]
  exact W.samplerSource_forall_sampleAdj Fin.val_injective D

end ProductFormula

/-! ### The sampled exchangeable law and the infinite identification (D3b step 5)

The `ι`-freedom of the product formula makes restriction-consistency immediate, so the finite
sampler laws assemble into a `RelExchangeableLaw digraphSig`; the infinite sampler then
realizes its (R2b) infinite law, by finite-restriction measure extensionality. -/

section LawIdentification

variable [IsProbabilityMeasure μ]

instance (k : ℕ) : IsProbabilityMeasure ((samplerSource μ).map (W.sampleFinite k)) :=
  Measure.isProbabilityMeasure_map (W.measurable_sampleFinite k).aemeasurable

/-- **Restriction-consistency of the sampled finite laws**: restricting the `l`-vertex sample
along any injection `e : Fin k ↪ Fin l` reproduces the `k`-vertex sample law — both sides have
the same exact-event masses by the labeling-free product formula. -/
theorem map_sampleFinite_restrict {k l : ℕ} (e : Fin k ↪ Fin l) :
    ((samplerSource μ).map (W.sampleFinite l)).map (RelStructure.restrict fun _ : Unit => e) =
      (samplerSource μ).map (W.sampleFinite k) := by
  rw [Measure.map_map (RelSignature.measurable_restrict _) (W.measurable_sampleFinite l)]
  refine Measure.ext_of_singleton fun D => ?_
  have hcomp : Function.Injective fun i : Fin k => ((e i : Fin l) : ℕ) :=
    Fin.val_injective.comp e.injective
  rw [Measure.map_apply ((RelSignature.measurable_restrict _).comp (W.measurable_sampleFinite l))
      (measurableSet_singleton D),
    Measure.map_apply (W.measurable_sampleFinite k) (measurableSet_singleton D)]
  have h1 : (RelStructure.restrict (fun _ : Unit => e) ∘ W.sampleFinite l) ⁻¹' {D} =
      {ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ) |
        ∀ i j : Fin k, W.sampleAdj ω (e i) (e j) = D (digraphCoord i j)} := by
    ext ω
    simp only [Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff, Set.mem_setOf_eq]
    rw [digraphStructure_ext_iff]
    refine forall₂_congr fun i j => ?_
    show W.sampleFinite l ω (RelCoord.map (fun _ => ⇑e) (digraphCoord i j))
        = D (digraphCoord i j) ↔ _
    rw [digraphCoord_map]
    exact Iff.rfl
  have h2 : W.sampleFinite k ⁻¹' {D} =
      {ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ) |
        ∀ i j : Fin k, W.sampleAdj ω i j = D (digraphCoord i j)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact digraphStructure_ext_iff
  rw [h1, h2, W.samplerSource_forall_sampleAdj hcomp D,
    W.samplerSource_forall_sampleAdj Fin.val_injective D]

/-- **The sampled relational law**: the finite sampler laws, packaged as an exchangeable
relational law over `digraphSig` (consistency from the labeling-free product formula). -/
noncomputable def sampleRelLaw : RelExchangeableLaw digraphSig where
  marginal n := ⟨(samplerSource μ).map (W.sampleFinite (n ())),
    Measure.isProbabilityMeasure_map (W.measurable_sampleFinite _).aemeasurable⟩
  consistent := fun {_ _} e => W.map_sampleFinite_restrict (e ())

@[simp] theorem sampleRelLaw_marginal (n : Unit → ℕ) :
    (W.sampleRelLaw.marginal n : Measure (RelStructure digraphSig (Vfinite n))) =
      (samplerSource μ).map (W.sampleFinite (n ())) := rfl

/-- **The sampled digraph law**, in the user-facing `PMF` form of D2. -/
noncomputable def sampleDigraphLaw : ExchangeableDigraphLaw :=
  digraphLawEquiv.symm W.sampleRelLaw

@[simp] theorem sampleDigraphLaw_law (k : ℕ) :
    W.sampleDigraphLaw.law k =
      ((samplerSource μ).map (W.sampleFinite k)).toPMF.map (finiteDigraphEquiv k) := rfl

/-- **The sampler realizes the infinite exchangeable law** (D3b step 5): the pushforward of
the sampler source under the infinite sampler is exactly the (R2b) infinite law of the sampled
relational law — by finite-restriction measure extensionality, since the finite sampler *is*
the restriction of the infinite sampler. -/
theorem map_sampleInfinite :
    (samplerSource μ).map W.sampleInfinite =
      (W.sampleRelLaw.infiniteLaw : Measure InfiniteDigraph) := by
  haveI : IsProbabilityMeasure ((samplerSource μ).map W.sampleInfinite) :=
    Measure.isProbabilityMeasure_map W.measurable_sampleInfinite.aemeasurable
  refine InfiniteDigraph.ext_of_map_restrictFin fun n => ?_
  rw [Measure.map_map (InfiniteDigraph.measurable_restrictFin n) W.measurable_sampleInfinite,
    W.sampleRelLaw.infiniteLaw_map_restrictFin fun _ => n]
  rfl

/-- **The headline identification**: the sampler's infinite law is the image of the sampled
`PMF`-based digraph law under the directed finite/infinite equivalence
`exchangeableDigraphLawEquiv` (D2). -/
theorem map_sampleInfinite_eq_equiv_law :
    (samplerSource μ).map W.sampleInfinite =
      ((exchangeableDigraphLawEquiv W.sampleDigraphLaw).law : Measure InfiniteDigraph) := by
  rw [W.map_sampleInfinite, exchangeableDigraphLawEquiv_apply_law]
  exact congrArg (fun L : RelExchangeableLaw digraphSig =>
    (L.infiniteLaw : Measure InfiniteDigraph))
    (digraphLawEquiv.apply_symm_apply W.sampleRelLaw).symm

end LawIdentification

end MeasureTheory.Digraphon
