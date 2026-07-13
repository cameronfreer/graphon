/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Digraphons: the five-component CAF directed graphon (directed umbrella #84, D3a / #87)

The measure-theoretic limit object for directed graphs (Diaconis–Janson §9, Cai–Ackerman–Freer).
A general digraphon is **not** a single asymmetric kernel `A(x,y)`: reciprocal edges may be
dependent. The correct object assigns to each ordered pair a probability distribution over the
four reciprocal-edge states `(G i j, G j i) ∈ {0,1}²`, with a transpose symmetry, plus a
`{0,1}`-valued loop coordinate.

* `Digraphon α μ` — the structure: four pair kernels `pairProb a b : α × α →ₘ[μ.prod μ] ℝ`
  (`a`, `b : Bool` the two directed-edge states) that are a.e. nonnegative, sum to one a.e., and
  satisfy the a.e. transpose law `pairProb a b (y,x) = pairProb b a (x,y)`, plus a Bool-valued
  loop `loop : α →ₘ[μ] Bool`; with `Digraphon.ext`;
* `Digraphon.pairRep` / `Digraphon.loopRep` — genuine (everywhere-defined) measurable
  representatives of the pair kernels and the loop coordinate;
* `Digraphon.pairSym` — the **transpose-symmetrized** representative
  `q a b (x,y) = ½(r a b (x,y) + r b a (y,x))`, which satisfies transpose compatibility
  *everywhere* and agrees a.e. with `pairProb`;
* `Digraphon.simplexRep` — the **everywhere-valid 3-simplex representative**: `pairSym` where it
  is a genuine probability vector, and the fixed atom `δ₀₀` elsewhere. It is measurable,
  nonnegative everywhere, sums to one everywhere, transpose-compatible everywhere, and equal a.e.
  to `pairProb` — the prerequisite for a well-defined categorical sampler (D3b).

No random sources / sampler / law here — that is D3b onward.
-/

open MeasureTheory Filter

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- **A digraphon** (five-component CAF directed graphon): four reciprocal-edge pair kernels
`pairProb a b : α × α →ₘ[μ.prod μ] ℝ` (`a`, `b : Bool` the states of the two directed edges
`i → j`, `j → i`) that a.e. form a probability vector on `{0,1}²` and satisfy the transpose law,
together with a `{0,1}`-valued loop coordinate. -/
structure Digraphon (α : Type*) [MeasurableSpace α] (μ : Measure α) where
  /-- The conditional probability that `(G i j, G j i) = (a, b)`. -/
  pairProb : Bool → Bool → (α × α →ₘ[μ.prod μ] ℝ)
  /-- Each pair kernel is a.e. nonnegative. -/
  ae_nonneg : ∀ a b, ∀ᵐ p ∂(μ.prod μ), 0 ≤ pairProb a b p
  /-- The four values sum to one a.e. -/
  ae_sum_eq_one : ∀ᵐ p ∂(μ.prod μ), ∑ a : Bool, ∑ b : Bool, pairProb a b p = 1
  /-- Transpose law: swapping the pair transposes the reciprocal-edge state, a.e. -/
  transpose_ae : ∀ a b, ∀ᵐ p ∂(μ.prod μ), pairProb a b p.swap = pairProb b a p
  /-- The `{0,1}`-valued loop coordinate. -/
  loop : α →ₘ[μ] Bool

namespace Digraphon

variable {μ}

@[ext] theorem ext {W₁ W₂ : Digraphon α μ}
    (hp : W₁.pairProb = W₂.pairProb) (hl : W₁.loop = W₂.loop) : W₁ = W₂ := by
  cases W₁; cases W₂; simp only [mk.injEq]; exact ⟨hp, hl⟩

variable (W : Digraphon α μ)

/-! ### Measurable representatives -/

/-- A genuine (everywhere-defined) measurable representative of the `(a, b)` pair kernel. -/
noncomputable def pairRep (a b : Bool) : α × α → ℝ := ⇑(W.pairProb a b)

theorem measurable_pairRep (a b : Bool) : Measurable (W.pairRep a b) :=
  (W.pairProb a b).stronglyMeasurable.measurable

/-- A genuine (everywhere-defined) measurable representative of the loop coordinate. -/
noncomputable def loopRep : α → Bool := ⇑W.loop

theorem measurable_loopRep : Measurable W.loopRep :=
  W.loop.stronglyMeasurable.measurable

/-! ### The transpose-symmetrized representative -/

/-- The **transpose-symmetrized** representative
`q a b (x, y) = ½(r a b (x, y) + r b a (y, x))`. -/
noncomputable def pairSym (a b : Bool) : α × α → ℝ := fun p => (W.pairRep a b p + W.pairRep b a p.swap) / 2

theorem measurable_pairSym (a b : Bool) : Measurable (W.pairSym a b) :=
  (((W.measurable_pairRep a b).add
    ((W.measurable_pairRep b a).comp measurable_swap)).div_const 2)

/-- **Transpose compatibility of the symmetrized kernel, everywhere.** -/
theorem pairSym_swap (a b : Bool) (p : α × α) : W.pairSym a b p.swap = W.pairSym b a p := by
  simp only [pairSym, Prod.swap_swap]; ring

/-- The symmetrized kernel agrees a.e. with the given pair kernel (uses the a.e. transpose law). -/
theorem pairSym_ae_eq (a b : Bool) : W.pairSym a b =ᵐ[μ.prod μ] W.pairProb a b := by
  filter_upwards [W.transpose_ae b a] with p hp
  simp only [pairSym, pairRep]
  rw [hp]; ring

/-! ### The everywhere-valid 3-simplex representative -/

/-- Whether the symmetrized values at `p` form a genuine probability vector. -/
def IsValidAt (p : α × α) : Prop :=
  (∀ a b, 0 ≤ W.pairSym a b p) ∧ (∑ a : Bool, ∑ b : Bool, W.pairSym a b p) = 1

theorem measurableSet_isValidAt : MeasurableSet {p | W.IsValidAt p} := by
  have hnn : MeasurableSet {p : α × α | ∀ a b, 0 ≤ W.pairSym a b p} := by
    rw [show {p : α × α | ∀ a b, 0 ≤ W.pairSym a b p}
        = ⋂ a : Bool, ⋂ b : Bool, {p | 0 ≤ W.pairSym a b p} by ext p; simp]
    exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
      measurableSet_le measurable_const (W.measurable_pairSym a b)
  have hsum : MeasurableSet {p : α × α | (∑ a : Bool, ∑ b : Bool, W.pairSym a b p) = 1} :=
    measurableSet_eq_fun
      (Finset.univ.measurable_sum fun a _ => Finset.univ.measurable_sum fun b _ =>
        W.measurable_pairSym a b) measurable_const
  exact hnn.inter hsum

/-- Validity is invariant under swapping the pair. -/
theorem isValidAt_swap (p : α × α) : W.IsValidAt p.swap ↔ W.IsValidAt p := by
  have key : ∀ a b : Bool, W.pairSym a b p.swap = W.pairSym b a p := fun a b => W.pairSym_swap a b p
  have hsumswap : (∑ a : Bool, ∑ b : Bool, W.pairSym a b p.swap)
      = ∑ a : Bool, ∑ b : Bool, W.pairSym a b p := by
    simp only [Fintype.sum_bool, key]; ring
  unfold IsValidAt
  rw [hsumswap]
  refine and_congr ⟨fun h a b => ?_, fun h a b => ?_⟩ Iff.rfl
  · rw [← key b a]; exact h b a
  · rw [key a b]; exact h b a

open Classical in
/-- The **everywhere-defined 3-simplex representative**: the symmetrized kernel where it is a
genuine probability vector, and the fixed atom `δ₀₀` (all mass on `(0,0)`) elsewhere. -/
noncomputable def simplexRep (a b : Bool) : α × α → ℝ := fun p =>
  if W.IsValidAt p then W.pairSym a b p else if a = false ∧ b = false then 1 else 0

theorem measurable_simplexRep (a b : Bool) : Measurable (W.simplexRep a b) := by
  classical
  unfold simplexRep
  exact Measurable.ite W.measurableSet_isValidAt (W.measurable_pairSym a b) measurable_const

/-- **Nonnegativity everywhere.** -/
theorem simplexRep_nonneg (a b : Bool) (p : α × α) : 0 ≤ W.simplexRep a b p := by
  classical
  unfold simplexRep
  split
  · rename_i h; exact h.1 a b
  · split <;> norm_num

/-- **The four values sum to one everywhere.** -/
theorem simplexRep_sum_eq_one (p : α × α) :
    ∑ a : Bool, ∑ b : Bool, W.simplexRep a b p = 1 := by
  classical
  unfold simplexRep
  split
  · rename_i h; exact h.2
  · simp only [Fintype.sum_bool]; norm_num

/-- **Transpose compatibility everywhere.** -/
theorem simplexRep_swap (a b : Bool) (p : α × α) :
    W.simplexRep a b p.swap = W.simplexRep b a p := by
  classical
  unfold simplexRep
  by_cases h : W.IsValidAt p
  · rw [if_pos ((W.isValidAt_swap p).2 h), if_pos h, W.pairSym_swap]
  · rw [if_neg (fun hc => h ((W.isValidAt_swap p).1 hc)), if_neg h]
    by_cases hab : a = false ∧ b = false
    · rw [if_pos hab, if_pos ⟨hab.2, hab.1⟩]
    · rw [if_neg hab, if_neg (fun hc => hab ⟨hc.2, hc.1⟩)]

/-- **Agreement a.e. with the given pair kernels.** On a conull set the symmetrized values are a
valid probability vector, where `simplexRep` reduces to `pairSym`, which agrees a.e. with
`pairProb`. -/
theorem simplexRep_ae_eq (a b : Bool) : W.simplexRep a b =ᵐ[μ.prod μ] W.pairProb a b := by
  classical
  have hvalid : ∀ᵐ p ∂(μ.prod μ), W.IsValidAt p := by
    have hnn : ∀ᵐ p ∂(μ.prod μ), ∀ a b, 0 ≤ W.pairSym a b p := by
      rw [eventually_countable_forall]; intro a; rw [eventually_countable_forall]; intro b
      filter_upwards [W.pairSym_ae_eq a b, W.ae_nonneg a b] with p hpe hpn
      rw [hpe]; exact hpn
    have hsum : ∀ᵐ p ∂(μ.prod μ), (∑ a : Bool, ∑ b : Bool, W.pairSym a b p) = 1 := by
      filter_upwards [W.ae_sum_eq_one,
        (eventually_all.2 fun a => eventually_all.2 fun b => W.pairSym_ae_eq a b)] with p hps hpe
      rw [← hps]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hpe a b
    filter_upwards [hnn, hsum] with p hpn hps
    exact ⟨hpn, hps⟩
  filter_upwards [hvalid, W.pairSym_ae_eq a b] with p hpv hpe
  rw [simplexRep, if_pos hpv, hpe]

end Digraphon

end MeasureTheory
