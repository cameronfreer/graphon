/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.DigraphSampler
import Graphon.DigraphonConstructors
import Graphon.SamplingLaw

/-!
# Sampler laws of the special digraphon families (directed umbrella #84, D3c / #87)

One headline identification per special family of `Graphon.DigraphonConstructors` (source
crosswalk: Cai–Ackerman–Freer arXiv:1510.08440 — digraphons/sampling §2.3–2.4, the
asymmetric-function model §3.1, undirected graphs and tournaments §3.2.1–3.2.2):

* `Digraphon.ofTournament_sample_isTournament` — the sample of the tournament digraphon is
  **almost surely a tournament**: no loops, and exactly one direction between any two distinct
  vertices;
* `Digraphon.sampleEventIntegrand_ofKernel_ae` — for the asymmetric-kernel digraphon the
  exact-event integrand **factorizes over ordered pairs**: the two directions of each pair are
  independent one-directional Bernoulli draws;
* `Digraphon.map_sampleFinite_ofGraphon` — the sample of the embedded ordinary graphon **is**
  the undirected `W`-random graph: its law is the pushforward of `Graphon.samplePMF W k` under
  the symmetric loopless embedding `SimpleGraph.toFiniteDigraph`.

Everything is driven by the labeling-free exact-event product formula
(`samplerSource_forall_sampleAdj`) together with the a.e. `simplexRep` identifications of the
families; a.e. facts about the latents transport to the sample space through the coordinate
projections of the i.i.d. sources.
-/

open MeasureTheory RelSignature Set
open scoped ENNReal

namespace MeasureTheory.Digraphon

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} (W : Digraphon α μ)

/-! ### Small-event specializations of the exact-event formula -/

section SmallEvents

variable [IsProbabilityMeasure μ]

/-- The one-vertex specialization: the probability of a prescribed loop bit at vertex `i` is
the `μ`-mass of the loop condition. -/
private theorem samplerSource_loop_event (i : ℕ) (b : Bool) :
    samplerSource μ {ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ) | W.loopRep (ω.1 i) = b} =
      ∫⁻ y : Fin 1 → α, (if W.loopRep (y 0) = b then 1 else 0)
        ∂(Measure.pi fun _ : Fin 1 => μ) := by
  have hι : Function.Injective (![i] : Fin 1 → ℕ) := fun a b _ => Subsingleton.elim a b
  have hD : ∀ ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ),
      W.loopRep (ω.1 i) = b ↔ ∀ a c : Fin 1, W.sampleAdj ω (![i] a) (![i] c)
        = (fun _ : RelCoord digraphSig (Vfinite fun _ => 1) => b) (digraphCoord a c) := by
    intro ω
    constructor
    · intro h a c
      fin_cases a; fin_cases c
      simpa [W.sampleAdj_self] using h
    · intro h
      simpa [W.sampleAdj_self] using h 0 0
  rw [show {ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ) | W.loopRep (ω.1 i) = b} =
      {ω | ∀ a c : Fin 1, W.sampleAdj ω (![i] a) (![i] c)
        = (fun _ : RelCoord digraphSig (Vfinite fun _ => 1) => b) (digraphCoord a c)} from
    Set.ext fun ω => hD ω]
  refine (W.samplerSource_forall_sampleAdj hι
    (fun _ : RelCoord digraphSig (Vfinite fun _ => 1) => b)).trans ?_
  refine lintegral_congr fun y => ?_
  unfold sampleEventIntegrand
  haveI : IsEmpty {p : Fin 1 × Fin 1 // p.1 < p.2} :=
    ⟨fun p => absurd p.2 (by rw [Subsingleton.elim p.1.1 p.1.2]; exact lt_irrefl _)⟩
  rw [Finset.univ_eq_empty (α := {p : Fin 1 × Fin 1 // p.1 < p.2}), Finset.prod_empty,
    mul_one]
  simp

/-- The two-vertex event: the sample realizes a prescribed function of the four coordinates on
the labels `i < j`. -/
private theorem samplerSource_pair_event {i j : ℕ} (hij : i < j) (f : Fin 2 → Fin 2 → Bool) :
    samplerSource μ {ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ) |
        ∀ a c : Fin 2, W.sampleAdj ω (![i, j] a) (![i, j] c) = f a c} =
      ∫⁻ y : Fin 2 → α, W.sampleEventIntegrand
        (fun c : RelCoord digraphSig (Vfinite fun _ => 2) => f (c.2 0) (c.2 1)) y
        ∂(Measure.pi fun _ : Fin 2 => μ) := by
  have hι : Function.Injective (![i, j] : Fin 2 → ℕ) := by
    intro a c h
    fin_cases a <;> fin_cases c <;> simp_all
  exact W.samplerSource_forall_sampleAdj hι
    fun c : RelCoord digraphSig (Vfinite fun _ => 2) => f (c.2 0) (c.2 1)

end SmallEvents

/-! ### The tournament digraphon samples tournaments -/

section Tournament

variable [IsProbabilityMeasure μ] (A : α × α →ₘ[μ.prod μ] ℝ)
  (hnn : ∀ᵐ p ∂(μ.prod μ), 0 ≤ A p) (hsum : ∀ᵐ p ∂(μ.prod μ), A p + A p.swap = 1)

/-- Any single loop bit of the tournament sample is a.s. absent. -/
private theorem ofTournament_loop_null (i : ℕ) :
    samplerSource μ {ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ) |
      (ofTournament A hnn hsum).loopRep (ω.1 i) = true} = 0 := by
  rw [(ofTournament A hnn hsum).samplerSource_loop_event i true]
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ : Fin 1 → α, 0 ∂(Measure.pi fun _ : Fin 1 => μ) from
    (lintegral_zero).symm]
  refine lintegral_congr_ae ?_
  have h0 : ∀ᵐ y ∂(Measure.pi fun _ : Fin 1 => μ),
      (ofTournament A hnn hsum).loopRep (y 0) = false :=
    (measurePreserving_eval (fun _ : Fin 1 => μ) 0).quasiMeasurePreserving.ae
      (ofTournament_loop_ae A hnn hsum)
  filter_upwards [h0] with y hy
  rw [hy]
  simp

/-- Any single reciprocal-agreeing two-vertex configuration of the tournament sample is null:
its exact-event integrand contains a `simplexRep b b` factor, which vanishes a.e. -/
private theorem ofTournament_pair_null {i j : ℕ} (hij : i < j) (f : Fin 2 → Fin 2 → Bool)
    (hf : f 0 1 = f 1 0) :
    samplerSource μ {ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ) |
      ∀ a c : Fin 2, (ofTournament A hnn hsum).sampleAdj ω (![i, j] a) (![i, j] c) = f a c}
      = 0 := by
  rw [(ofTournament A hnn hsum).samplerSource_pair_event hij f]
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ : Fin 2 → α, 0 ∂(Measure.pi fun _ : Fin 2 => μ) from
    (lintegral_zero).symm]
  refine lintegral_congr_ae ?_
  -- the diagonal simplexRep values vanish a.e., transported to the coordinate pair (y 0, y 1)
  have hdiag : ∀ᵐ p ∂(μ.prod μ),
      (ofTournament A hnn hsum).simplexRep (f 0 1) (f 1 0) p = 0 := by
    obtain ⟨-, -, htt, hff⟩ := ofTournament_simplexRep_ae A hnn hsum
    rcases hb : f 1 0 with _ | _
    · rw [hf, hb]
      filter_upwards [hff] with p hp using hp
    · rw [hf, hb]
      filter_upwards [htt] with p hp using hp
  have h01 : ∀ᵐ y ∂(Measure.pi fun _ : Fin 2 => μ),
      (ofTournament A hnn hsum).simplexRep (f 0 1) (f 1 0) (y 0, y 1) = 0 :=
    Graphon.ae_pairMap_of_prod (0 : Fin 2) 1 (by decide) hdiag
  filter_upwards [h01] with y hy
  unfold sampleEventIntegrand
  rw [Finset.prod_eq_zero (Finset.mem_univ (⟨(0, 1), by decide⟩ :
    {p : Fin 2 × Fin 2 // p.1 < p.2})), mul_zero]
  rw [show ((fun c : RelCoord digraphSig (Vfinite fun _ => 2) => f (c.2 0) (c.2 1))
      (digraphCoord (0 : Fin 2) 1)) = f 0 1 from rfl,
    show ((fun c : RelCoord digraphSig (Vfinite fun _ => 2) => f (c.2 0) (c.2 1))
      (digraphCoord (1 : Fin 2) 0)) = f 1 0 from rfl, hy]
  simp

/-- **The tournament digraphon samples tournaments** (D3c headline): almost surely, the
sampled infinite digraph has no loops and exactly one direction between any two distinct
vertices. -/
theorem ofTournament_sample_isTournament :
    ∀ᵐ ω ∂samplerSource μ,
      (∀ i : ℕ, ((ofTournament A hnn hsum).sampleInfinite ω).adjBit i i = false) ∧
        ∀ i j : ℕ, i ≠ j →
          ((ofTournament A hnn hsum).sampleInfinite ω).adjBit j i
            = !((ofTournament A hnn hsum).sampleInfinite ω).adjBit i j := by
  have hloops : ∀ᵐ ω ∂samplerSource μ, ∀ i : ℕ,
      (ofTournament A hnn hsum).loopRep (ω.1 i) = false := by
    rw [eventually_countable_forall]
    intro i
    refine ae_iff.mpr (measure_mono_null (fun ω hω => ?_) (ofTournament_loop_null A hnn hsum i))
    simp only [Set.mem_setOf_eq] at hω ⊢
    simpa using hω
  have hpairs : ∀ᵐ ω ∂samplerSource μ, ∀ i j : ℕ, i < j →
      (ofTournament A hnn hsum).sampleAdj ω j i
        = !(ofTournament A hnn hsum).sampleAdj ω i j := by
    rw [eventually_countable_forall]
    intro i
    rw [eventually_countable_forall]
    intro j
    rcases lt_or_ge i j with hij | hij
    · have hnull : samplerSource μ (⋃ f : Fin 2 → Fin 2 → Bool, ⋃ _ : f 0 1 = f 1 0,
          {ω : (ℕ → α) × (OffDiagPairIndex ℕ → ℝ) | ∀ a c : Fin 2,
            (ofTournament A hnn hsum).sampleAdj ω (![i, j] a) (![i, j] c) = f a c}) = 0 :=
        measure_iUnion_null fun f => measure_iUnion_null fun hf =>
          ofTournament_pair_null A hnn hsum hij f hf
      refine ae_iff.mpr (measure_mono_null (fun ω hω => ?_) hnull)
      simp only [Set.mem_setOf_eq, Classical.not_imp] at hω
      obtain ⟨-, hbad⟩ := hω
      have hagree : (ofTournament A hnn hsum).sampleAdj ω j i
          = (ofTournament A hnn hsum).sampleAdj ω i j := by
        rcases hb : (ofTournament A hnn hsum).sampleAdj ω i j <;>
          rcases hb' : (ofTournament A hnn hsum).sampleAdj ω j i <;> simp_all
      refine Set.mem_iUnion.mpr ⟨fun a c =>
        (ofTournament A hnn hsum).sampleAdj ω (![i, j] a) (![i, j] c), ?_⟩
      exact Set.mem_iUnion.mpr ⟨hagree.symm, fun a c => rfl⟩
    · exact Filter.Eventually.of_forall fun ω h => absurd h (not_lt.mpr hij)
  filter_upwards [hloops, hpairs] with ω h1 h2
  refine ⟨fun i => ?_, fun i j hne => ?_⟩
  · rw [adjBit_sampleInfinite, sampleAdj_self]
    exact h1 i
  · rw [adjBit_sampleInfinite, adjBit_sampleInfinite]
    rcases lt_or_gt_of_ne hne with h | h
    · exact h2 i j h
    · rw [h2 j i h, Bool.not_not]

end Tournament

end MeasureTheory.Digraphon
