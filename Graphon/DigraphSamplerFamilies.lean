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

end MeasureTheory.Digraphon
