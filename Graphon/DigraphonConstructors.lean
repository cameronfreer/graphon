/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Basic
import Graphon.Digraphon

/-!
# Special-family digraphon constructors (directed umbrella #84, D3c / #87)

The three classical families of Cai–Ackerman–Freer §2, realized as digraphons — each is a
choice of the four reciprocal-edge probabilities:

* `Digraphon.ofFun` — the generic builder from four *measurable pointwise* kernels satisfying
  the digraphon axioms a.e., with the a.e. compatibility lemmas `ofFun_pairProb_ae` / `ofFun_simplexRep_ae`;
* `Digraphon.ofGraphon W` — the **ordinary-graphon embedding**: reciprocal edges fully
  correlated (`p₁₁ = W`, `p₀₀ = 1 − W`, no antisymmetric mass, no loops) — an undirected
  graph seen as a digraph;
* `Digraphon.ofTournament A` — the **tournament digraphon**: exactly one direction per pair
  (`p₁₀ = A`, `p₀₁ = A ∘ swap`, `p₁₁ = p₀₀ = 0`, no loops), from an orientation kernel with
  `A p + A p.swap = 1` a.e.;
* `Digraphon.ofKernel A L` — the **asymmetric-kernel digraphon**: the two directions drawn
  *independently* (`p_{ab} = A^a (1−A)^{1−a} · (A∘swap)^b (1−A∘swap)^{1−b}`, all four products
  genuinely present), with an arbitrary loop coordinate `L`.

Each constructor comes with the a.e. identification of its four pair kernels
(`ofGraphon_pairProb_ae` / `ofTournament_pairProb_ae` / `ofKernel_pairProb_ae`), from which the
`simplexRep`-level compatibility is inherited via `Digraphon.simplexRep_ae_eq`. The sampler/law
identification for each family is the D3c follow-up.
-/

open MeasureTheory Filter

namespace MeasureTheory.Digraphon

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

/-- Almost-everywhere facts transport along the pair swap (the swap preserves `μ.prod μ`). -/
private theorem ae_swap {P : α × α → Prop} (h : ∀ᵐ p ∂(μ.prod μ), P p) :
    ∀ᵐ p ∂(μ.prod μ), P p.swap :=
  Measure.measurePreserving_swap.quasiMeasurePreserving.ae h

/-! ### The generic pointwise builder -/

/-- **The generic digraphon builder** from four measurable pointwise kernels satisfying the
digraphon axioms almost everywhere, together with a measurable loop coordinate. -/
noncomputable def ofFun (f : Bool → Bool → α × α → ℝ) (hmeas : ∀ a b, Measurable (f a b))
    (hnn : ∀ a b, ∀ᵐ p ∂(μ.prod μ), 0 ≤ f a b p)
    (hsum : ∀ᵐ p ∂(μ.prod μ), ∑ a : Bool, ∑ b : Bool, f a b p = 1)
    (htr : ∀ a b, ∀ᵐ p ∂(μ.prod μ), f a b p.swap = f b a p)
    (L : α → Bool) (hL : Measurable L) : Digraphon α μ where
  pairProb a b := AEEqFun.mk (f a b) (hmeas a b).aestronglyMeasurable
  ae_nonneg a b := by
    filter_upwards [AEEqFun.coeFn_mk (f a b) (hmeas a b).aestronglyMeasurable, hnn a b]
      with p hp hnn'
    rw [hp]; exact hnn'
  ae_sum_eq_one := by
    have hall : ∀ᵐ p ∂(μ.prod μ), ∀ a b : Bool,
        (AEEqFun.mk (f a b) (hmeas a b).aestronglyMeasurable : α × α →ₘ[μ.prod μ] ℝ) p
          = f a b p :=
      eventually_all.2 fun a => eventually_all.2 fun b =>
        AEEqFun.coeFn_mk (f a b) (hmeas a b).aestronglyMeasurable
    filter_upwards [hall, hsum] with p hp hsum'
    rw [← hsum']
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hp a b
  transpose_ae a b := by
    have hswap : ∀ᵐ p ∂(μ.prod μ),
        (AEEqFun.mk (f a b) (hmeas a b).aestronglyMeasurable : α × α →ₘ[μ.prod μ] ℝ) p.swap
          = f a b p.swap :=
      ae_swap (AEEqFun.coeFn_mk (f a b) (hmeas a b).aestronglyMeasurable)
    filter_upwards [hswap, AEEqFun.coeFn_mk (f b a) (hmeas b a).aestronglyMeasurable, htr a b]
      with p hp hp' htr'
    rw [hp, hp', htr']
  loop := AEEqFun.mk L hL.aestronglyMeasurable

/-- The pair kernels of `ofFun` are (a.e.) the given pointwise kernels. -/
theorem ofFun_pairProb_ae (f : Bool → Bool → α × α → ℝ) (hmeas : ∀ a b, Measurable (f a b))
    (hnn : ∀ a b, ∀ᵐ p ∂(μ.prod μ), 0 ≤ f a b p)
    (hsum : ∀ᵐ p ∂(μ.prod μ), ∑ a : Bool, ∑ b : Bool, f a b p = 1)
    (htr : ∀ a b, ∀ᵐ p ∂(μ.prod μ), f a b p.swap = f b a p)
    (L : α → Bool) (hL : Measurable L) (a b : Bool) :
    (ofFun f hmeas hnn hsum htr L hL).pairProb a b =ᵐ[μ.prod μ] f a b :=
  AEEqFun.coeFn_mk (f a b) (hmeas a b).aestronglyMeasurable

/-- The loop coordinate of `ofFun` is (a.e.) the given pointwise loop. -/
theorem ofFun_loop_ae (f : Bool → Bool → α × α → ℝ) (hmeas : ∀ a b, Measurable (f a b))
    (hnn : ∀ a b, ∀ᵐ p ∂(μ.prod μ), 0 ≤ f a b p)
    (hsum : ∀ᵐ p ∂(μ.prod μ), ∑ a : Bool, ∑ b : Bool, f a b p = 1)
    (htr : ∀ a b, ∀ᵐ p ∂(μ.prod μ), f a b p.swap = f b a p)
    (L : α → Bool) (hL : Measurable L) :
    (ofFun f hmeas hnn hsum htr L hL).loop =ᵐ[μ] L :=
  AEEqFun.coeFn_mk L hL.aestronglyMeasurable

/-- The `simplexRep` of `ofFun` agrees a.e. with the given pointwise kernels — the
`simplexRep`-level compatibility all three special families inherit. -/
theorem ofFun_simplexRep_ae (f : Bool → Bool → α × α → ℝ) (hmeas : ∀ a b, Measurable (f a b))
    (hnn : ∀ a b, ∀ᵐ p ∂(μ.prod μ), 0 ≤ f a b p)
    (hsum : ∀ᵐ p ∂(μ.prod μ), ∑ a : Bool, ∑ b : Bool, f a b p = 1)
    (htr : ∀ a b, ∀ᵐ p ∂(μ.prod μ), f a b p.swap = f b a p)
    (L : α → Bool) (hL : Measurable L) (a b : Bool) :
    (ofFun f hmeas hnn hsum htr L hL).simplexRep a b =ᵐ[μ.prod μ] f a b :=
  ((ofFun f hmeas hnn hsum htr L hL).simplexRep_ae_eq a b).trans
    (ofFun_pairProb_ae f hmeas hnn hsum htr L hL a b)

/-! ### The ordinary-graphon embedding -/

section OfGraphon

variable (W : Graphon α μ)

/-- The pointwise kernels of the graphon embedding: reciprocal edges fully correlated. -/
private noncomputable def graphonFour (W : Graphon α μ) (a b : Bool) : α × α → ℝ :=
  if a ∧ b then ⇑W.toAEEqFun else if ¬a ∧ ¬b then fun p => 1 - W.toAEEqFun p else 0

omit [SFinite μ] in
private theorem measurable_graphonFour (a b : Bool) : Measurable (graphonFour W a b) := by
  unfold graphonFour
  split_ifs
  · exact W.toAEEqFun.stronglyMeasurable.measurable
  · exact measurable_const.sub W.toAEEqFun.stronglyMeasurable.measurable
  · exact measurable_const

/-- **The ordinary-graphon embedding**: the digraphon whose reciprocal-edge distribution puts
mass `W (x, y)` on the doubly-present state and `1 − W (x, y)` on the doubly-absent state —
an undirected graph viewed as a digraph, with no loops. -/
noncomputable def ofGraphon : Digraphon α μ :=
  ofFun (graphonFour W) (measurable_graphonFour W)
    (fun a b => by
      filter_upwards [W.ae_mem_Icc] with p hp
      unfold graphonFour
      split_ifs
      · exact hp.1
      · simpa using hp.2
      · rfl)
    (by
      refine Eventually.of_forall fun p => ?_
      simp only [Fintype.sum_bool, graphonFour]
      norm_num)
    (fun a b => by
      filter_upwards [W.symm_ae] with p hsymm
      unfold graphonFour
      cases a <;> cases b <;> simp [hsymm])
    (fun _ => false) measurable_const

/-- The four pair kernels of the graphon embedding, a.e.: `p₁₁ = W`, `p₀₀ = 1 − W`, and no
antisymmetric mass. -/
theorem ofGraphon_pairProb_ae :
    ((ofGraphon W).pairProb true true =ᵐ[μ.prod μ] ⇑W.toAEEqFun) ∧
      ((ofGraphon W).pairProb false false =ᵐ[μ.prod μ] fun p => 1 - W.toAEEqFun p) ∧
        ((ofGraphon W).pairProb true false =ᵐ[μ.prod μ] 0) ∧
          ((ofGraphon W).pairProb false true =ᵐ[μ.prod μ] 0) :=
  ⟨ofFun_pairProb_ae _ _ _ _ _ _ _ true true,
    ofFun_pairProb_ae _ _ _ _ _ _ _ false false,
    ofFun_pairProb_ae _ _ _ _ _ _ _ true false,
    ofFun_pairProb_ae _ _ _ _ _ _ _ false true⟩

/-- The graphon embedding carries no loops (a.e.). -/
theorem ofGraphon_loop_ae : (ofGraphon W).loop =ᵐ[μ] fun _ => false :=
  ofFun_loop_ae _ _ _ _ _ _ _

end OfGraphon

/-! ### The tournament digraphon -/

section OfTournament

variable (A : α × α →ₘ[μ.prod μ] ℝ)

/-- The pointwise kernels of the tournament digraphon: exactly one direction per pair. -/
private noncomputable def tournamentFour (A : α × α →ₘ[μ.prod μ] ℝ) (a b : Bool) :
    α × α → ℝ :=
  if a ∧ ¬b then ⇑A else if ¬a ∧ b then fun p => A p.swap else 0

omit [SFinite μ] in
private theorem measurable_tournamentFour (a b : Bool) :
    Measurable (tournamentFour A a b) := by
  unfold tournamentFour
  split_ifs
  · exact A.stronglyMeasurable.measurable
  · exact A.stronglyMeasurable.measurable.comp measurable_swap
  · exact measurable_const

/-- **The tournament digraphon**: exactly one of the two directed edges is present at every
pair — `p₁₀ = A`, `p₀₁ = A ∘ swap`, no doubly-present or doubly-absent mass, no loops — from
an orientation kernel `A` with `A p + A p.swap = 1` a.e. -/
noncomputable def ofTournament (hnn : ∀ᵐ p ∂(μ.prod μ), 0 ≤ A p)
    (hsum : ∀ᵐ p ∂(μ.prod μ), A p + A p.swap = 1) : Digraphon α μ :=
  ofFun (tournamentFour A) (measurable_tournamentFour A)
    (fun a b => by
      filter_upwards [hnn, ae_swap hnn] with p hp hps
      unfold tournamentFour
      split_ifs
      · exact hp
      · exact hps
      · rfl)
    (by
      filter_upwards [hsum] with p hp
      simp only [Fintype.sum_bool, tournamentFour]
      norm_num
      linarith)
    (fun a b => by
      refine Eventually.of_forall fun p => ?_
      unfold tournamentFour
      cases a <;> cases b <;> simp [Prod.swap_swap])
    (fun _ => false) measurable_const

/-- The four pair kernels of the tournament digraphon, a.e. -/
theorem ofTournament_pairProb_ae (hnn : ∀ᵐ p ∂(μ.prod μ), 0 ≤ A p)
    (hsum : ∀ᵐ p ∂(μ.prod μ), A p + A p.swap = 1) :
    ((ofTournament A hnn hsum).pairProb true false =ᵐ[μ.prod μ] ⇑A) ∧
      ((ofTournament A hnn hsum).pairProb false true =ᵐ[μ.prod μ] fun p => A p.swap) ∧
        ((ofTournament A hnn hsum).pairProb true true =ᵐ[μ.prod μ] 0) ∧
          ((ofTournament A hnn hsum).pairProb false false =ᵐ[μ.prod μ] 0) :=
  ⟨ofFun_pairProb_ae _ _ _ _ _ _ _ true false,
    ofFun_pairProb_ae _ _ _ _ _ _ _ false true,
    ofFun_pairProb_ae _ _ _ _ _ _ _ true true,
    ofFun_pairProb_ae _ _ _ _ _ _ _ false false⟩

end OfTournament

/-! ### The asymmetric-kernel digraphon -/

section OfKernel

variable (A : α × α →ₘ[μ.prod μ] ℝ)

/-- The pointwise kernels of the asymmetric-kernel digraphon: the two directions drawn
independently, so each of the four states gets the corresponding product mass. -/
private noncomputable def kernelFour (A : α × α →ₘ[μ.prod μ] ℝ) (a b : Bool) :
    α × α → ℝ := fun p =>
  (if a then A p else 1 - A p) * (if b then A p.swap else 1 - A p.swap)

omit [SFinite μ] in
private theorem measurable_kernelFour (a b : Bool) : Measurable (kernelFour A a b) := by
  have hA : Measurable (⇑A) := A.stronglyMeasurable.measurable
  have hAs : Measurable fun p : α × α => A p.swap := hA.comp measurable_swap
  unfold kernelFour
  cases a <;> cases b <;>
    simp only [if_true, if_false, Bool.false_eq_true] <;>
    exact Measurable.mul (by first | exact hA | exact measurable_const.sub hA)
      (by first | exact hAs | exact measurable_const.sub hAs)

/-- **The asymmetric-kernel digraphon**: the two directed edges of a pair are drawn
**independently** — `p_{ab} (x, y)` is the product of the `a`-mass of `A (x, y)` and the
`b`-mass of `A (y, x)`, so all four reciprocal-edge products are genuinely present — with an
arbitrary loop coordinate `L`. -/
noncomputable def ofKernel (hmem : ∀ᵐ p ∂(μ.prod μ), A p ∈ Set.Icc (0 : ℝ) 1)
    (L : α → Bool) (hL : Measurable L) : Digraphon α μ :=
  ofFun (kernelFour A) (measurable_kernelFour A)
    (fun a b => by
      filter_upwards [hmem, ae_swap hmem] with p hp hps
      unfold kernelFour
      have h1 : 0 ≤ if a then A p else 1 - A p := by
        split_ifs
        · exact hp.1
        · linarith [hp.2]
      have h2 : 0 ≤ if b then A p.swap else 1 - A p.swap := by
        split_ifs
        · exact hps.1
        · linarith [hps.2]
      exact mul_nonneg h1 h2)
    (by
      refine Eventually.of_forall fun p => ?_
      simp only [Fintype.sum_bool, kernelFour, Bool.false_eq_true, if_true, if_false]
      ring)
    (fun a b => by
      refine Eventually.of_forall fun p => ?_
      unfold kernelFour
      rw [Prod.swap_swap]
      ring)
    L hL

/-- The four pair kernels of the asymmetric-kernel digraphon, a.e.: the independent products. -/
theorem ofKernel_pairProb_ae (hmem : ∀ᵐ p ∂(μ.prod μ), A p ∈ Set.Icc (0 : ℝ) 1)
    (L : α → Bool) (hL : Measurable L) (a b : Bool) :
    (ofKernel A hmem L hL).pairProb a b =ᵐ[μ.prod μ] fun p =>
      (if a then A p else 1 - A p) * (if b then A p.swap else 1 - A p.swap) :=
  ofFun_pairProb_ae _ _ _ _ _ _ _ a b

/-- The loop coordinate of the asymmetric-kernel digraphon, a.e. -/
theorem ofKernel_loop_ae (hmem : ∀ᵐ p ∂(μ.prod μ), A p ∈ Set.Icc (0 : ℝ) 1)
    (L : α → Bool) (hL : Measurable L) :
    (ofKernel A hmem L hL).loop =ᵐ[μ] L :=
  ofFun_loop_ae _ _ _ _ _ _ _

end OfKernel

end MeasureTheory.Digraphon
