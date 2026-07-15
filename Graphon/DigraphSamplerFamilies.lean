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

/-! ### The asymmetric-kernel digraphon: independent directions -/

section Kernel

variable [IsProbabilityMeasure μ] (A : α × α →ₘ[μ.prod μ] ℝ)
  (hmem : ∀ᵐ p ∂(μ.prod μ), A p ∈ Set.Icc (0 : ℝ) 1) (L : α → Bool) (hL : Measurable L)

/-- The one-directional Bernoulli mass of a single ordered pair. -/
private noncomputable def dirMass (A : α × α →ₘ[μ.prod μ] ℝ) {n : ℕ} (D : FiniteDigraph n)
    (y : Fin n → α) (q : Fin n × Fin n) : ℝ :=
  if D (digraphCoord q.1 q.2) = true then A (y q.1, y q.2) else 1 - A (y q.1, y q.2)

/-- **The asymmetric-kernel sample draws its two directions independently** (D3c headline):
the exact-event integrand factorizes over *ordered* off-diagonal pairs into one-directional
Bernoulli masses, with the loop indicators reading the loop kernel `L`. -/
theorem sampleEventIntegrand_ofKernel_ae {n : ℕ} (D : FiniteDigraph n) :
    (ofKernel A hmem L hL).sampleEventIntegrand D
      =ᵐ[Measure.pi fun _ : Fin n => μ] fun y =>
        (∏ i : Fin n, if L (y i) = D (digraphCoord i i) then 1 else 0) *
          ∏ q ∈ Finset.univ.filter (fun q : Fin n × Fin n => q.1 ≠ q.2),
            ENNReal.ofReal (dirMass A D y q) := by
  classical
  -- transported a.e. facts: loop kernel per coordinate, simplexRep + membership per pair
  have hloop : ∀ᵐ y ∂(Measure.pi fun _ : Fin n => μ), ∀ i : Fin n,
      (ofKernel A hmem L hL).loopRep (y i) = L (y i) := by
    rw [eventually_countable_forall]
    exact fun i => (measurePreserving_eval (fun _ : Fin n => μ) i).quasiMeasurePreserving.ae
      (ofKernel_loop_ae A hmem L hL)
  have hpair : ∀ᵐ y ∂(Measure.pi fun _ : Fin n => μ),
      ∀ p : {p : Fin n × Fin n // p.1 < p.2},
        (ofKernel A hmem L hL).simplexRep (D (digraphCoord p.1.1 p.1.2))
            (D (digraphCoord p.1.2 p.1.1)) (y p.1.1, y p.1.2)
          = (if D (digraphCoord p.1.1 p.1.2) = true then A (y p.1.1, y p.1.2)
              else 1 - A (y p.1.1, y p.1.2)) *
            (if D (digraphCoord p.1.2 p.1.1) = true then A (y p.1.2, y p.1.1)
              else 1 - A (y p.1.2, y p.1.1)) ∧
        A (y p.1.1, y p.1.2) ∈ Set.Icc (0 : ℝ) 1 := by
    rw [eventually_countable_forall]
    intro p
    have h1 := Graphon.ae_pairMap_of_prod p.1.1 p.1.2 p.2.ne
      ((ofKernel_simplexRep_ae A hmem L hL (D (digraphCoord p.1.1 p.1.2))
        (D (digraphCoord p.1.2 p.1.1))).and hmem)
    filter_upwards [h1] with y hy
    exact ⟨hy.1, hy.2⟩
  filter_upwards [hloop, hpair] with y hy hp
  unfold sampleEventIntegrand
  congr 1
  · exact Finset.prod_congr rfl fun i _ => by rw [hy i]
  -- pair side: substitute the product form, split ofReal, reindex to ordered pairs
  have hsubst : ∀ p : {p : Fin n × Fin n // p.1 < p.2},
      ENNReal.ofReal ((ofKernel A hmem L hL).simplexRep (D (digraphCoord p.1.1 p.1.2))
          (D (digraphCoord p.1.2 p.1.1)) (y p.1.1, y p.1.2))
        = ENNReal.ofReal (dirMass A D y p.1) * ENNReal.ofReal (dirMass A D y p.1.swap) := by
    intro p
    have hpos : 0 ≤ (if D (digraphCoord p.1.1 p.1.2) = true then A (y p.1.1, y p.1.2)
        else 1 - A (y p.1.1, y p.1.2)) := by
      split_ifs
      · exact (hp p).2.1
      · linarith [(hp p).2.2]
    rw [(hp p).1, ENNReal.ofReal_mul hpos]
    rfl
  rw [Finset.prod_congr rfl fun p _ => hsubst p, Finset.prod_mul_distrib]
  -- the ordered off-diagonal pairs split into the increasing and decreasing halves
  have hlt : ∏ p : {p : Fin n × Fin n // p.1 < p.2}, ENNReal.ofReal (dirMass A D y p.1)
      = ∏ q ∈ Finset.univ.filter (fun q : Fin n × Fin n => q.1 < q.2),
          ENNReal.ofReal (dirMass A D y q) :=
    (Finset.prod_subtype (Finset.univ.filter fun q : Fin n × Fin n => q.1 < q.2)
      (fun q => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
      fun q => ENNReal.ofReal (dirMass A D y q)).symm
  have hgt : ∏ p : {p : Fin n × Fin n // p.1 < p.2}, ENNReal.ofReal (dirMass A D y p.1.swap)
      = ∏ q ∈ Finset.univ.filter (fun q : Fin n × Fin n => q.2 < q.1),
          ENNReal.ofReal (dirMass A D y q) := by
    rw [Finset.prod_subtype (p := fun q : Fin n × Fin n => q.2 < q.1)
      (Finset.univ.filter fun q : Fin n × Fin n => q.2 < q.1)
      (fun q => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
      (fun q => ENNReal.ofReal (dirMass A D y q))]
    exact Fintype.prod_equiv
      ⟨fun p => ⟨p.1.swap, p.2⟩, fun q => ⟨q.1.swap, q.2⟩,
        fun p => Subtype.ext (Prod.swap_swap _), fun q => Subtype.ext (Prod.swap_swap _)⟩
      _ _ fun p => rfl
  rw [hlt, hgt, ← Finset.prod_union (by
    simp only [Finset.disjoint_filter]
    exact fun q _ h1 => not_lt_of_gt h1)]
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext q
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | h)
    · exact h.ne
    · exact (h.ne).symm
  · intro h
    rcases lt_or_gt_of_ne h with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'

end Kernel

/-! ### The graphon embedding samples the undirected W-random graph -/

section GraphonEmbedding

open scoped Classical in
/-- The symmetric loopless embedding of a simple graph as a finite digraph. -/
noncomputable def _root_.SimpleGraph.toFiniteDigraph {k : ℕ} (G : SimpleGraph (Fin k)) :
    FiniteDigraph k :=
  fun c => decide (G.Adj (c.2 0) (c.2 1))

variable [IsProbabilityMeasure μ]

open scoped Classical in
/-- The ordered-pair coordinates of the embedded digraph read the (classically decided)
adjacency of the simple graph. -/
private theorem toFiniteDigraph_coord {k : ℕ} (G : SimpleGraph (Fin k)) (a b : Fin k) :
    G.toFiniteDigraph (digraphCoord a b) = decide (G.Adj a b) := rfl

/-- The symmetric loopless embedding is injective. -/
private theorem toFiniteDigraph_injective {k : ℕ} :
    Function.Injective (SimpleGraph.toFiniteDigraph (k := k)) := by
  intro G G' h
  ext a b
  have hc := congrFun h (digraphCoord a b)
  rw [toFiniteDigraph_coord, toFiniteDigraph_coord] at hc
  exact decide_eq_decide.mp hc

/-- **Classification of the range of the embedding**: a finite digraph is an embedded simple
graph iff its coordinates are loopless and symmetric. -/
private theorem exists_toFiniteDigraph_eq_iff {k : ℕ} (D : FiniteDigraph k) :
    (∃ G : SimpleGraph (Fin k), G.toFiniteDigraph = D) ↔
      ((∀ i, D (digraphCoord i i) = false) ∧
        ∀ i j : Fin k, D (digraphCoord i j) = D (digraphCoord j i)) := by
  classical
  constructor
  · rintro ⟨G, rfl⟩
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · rw [toFiniteDigraph_coord]
      exact decide_eq_false G.irrefl
    · rw [toFiniteDigraph_coord, toFiniteDigraph_coord]
      exact decide_eq_decide.mpr (G.adj_comm i j)
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun i j => D (digraphCoord i j) = true ∧ i ≠ j,
      ⟨fun i j hij => ⟨(h2 j i).trans hij.1, hij.2.symm⟩⟩,
      ⟨fun i hii => hii.2 rfl⟩⟩, ?_⟩
    refine digraphStructure_ext_iff.mpr fun a b => ?_
    rw [toFiniteDigraph_coord]
    by_cases hab : a = b
    · subst hab
      rw [h1 a, decide_eq_false_iff_not]
      exact fun hcon => hcon.2 rfl
    · rcases hDc : D (digraphCoord a b) with _ | _
      · rw [decide_eq_false_iff_not]
        exact fun hcon => Bool.false_ne_true (hDc ▸ hcon.1)
      · exact @decide_eq_true _ (Classical.propDecidable _) ⟨hDc, hab⟩

/-- The canonical representative of an unordered pair built from an ordered pair is that pair
or its swap. -/
private theorem out_eq_or_swap {V : Type*} (a b : V) :
    Quot.out s(a, b) = (a, b) ∨ Quot.out s(a, b) = (b, a) := by
  have h : s(a, b) = s((Quot.out s(a, b)).1, (Quot.out s(a, b)).2) := by
    simp [Sym2.mk, Quot.out_eq]
  rcases Sym2.eq_iff.mp h.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (Prod.ext h1 h2)
  · exact Or.inr (Prod.ext h1 h2)

/-- **The exact-event lintegral of the embedded digraphon at an embedded graph is the sample
mass** of the underlying `W`-random graph: the loop indicators are a.e. `1`, and the
increasing-pair `simplexRep` masses are a.e. the Bernoulli edge masses of `sampleIntegrand`,
reindexed from unordered edges to increasing pairs. -/
private theorem lintegral_sampleEventIntegrand_toFiniteDigraph (W : Graphon α μ) {k : ℕ}
    (G : SimpleGraph (Fin k)) :
    ∫⁻ y, (ofGraphon W).sampleEventIntegrand G.toFiniteDigraph y
        ∂(Measure.pi fun _ : Fin k => μ) =
      ENNReal.ofReal (Graphon.sampleMass W G) := by
  classical
  have hnn : 0 ≤ᵐ[Measure.pi fun _ : Fin k => μ] Graphon.sampleIntegrand W G := by
    filter_upwards [Graphon.ae_top_edges_mem_Icc W] with x hx
    refine mul_nonneg (Finset.prod_nonneg fun e he => ?_) (Finset.prod_nonneg fun e he => ?_)
    · exact (hx e (SimpleGraph.edgeFinset_mono le_top he)).1
    · linarith [(hx e (Finset.sdiff_subset he)).2]
  rw [Graphon.sampleMass, ofReal_integral_eq_lintegral_ofReal
    (Graphon.sampleIntegrand_integrable W G) hnn]
  refine lintegral_congr_ae ?_
  -- transported a.e. facts: no loops per coordinate, and the two diagonal `simplexRep`
  -- identifications plus a.e. symmetry per increasing pair
  have hloop : ∀ᵐ y ∂(Measure.pi fun _ : Fin k => μ), ∀ i : Fin k,
      (ofGraphon W).loopRep (y i) = false := by
    rw [eventually_countable_forall]
    exact fun i => (measurePreserving_eval (fun _ : Fin k => μ) i).quasiMeasurePreserving.ae
      (ofGraphon_loop_ae W)
  have hpair : ∀ᵐ y ∂(Measure.pi fun _ : Fin k => μ),
      ∀ p : {p : Fin k × Fin k // p.1 < p.2},
        (ofGraphon W).simplexRep true true (y p.1.1, y p.1.2)
            = W.toAEEqFun (y p.1.1, y p.1.2) ∧
          (ofGraphon W).simplexRep false false (y p.1.1, y p.1.2)
              = 1 - W.toAEEqFun (y p.1.1, y p.1.2) ∧
            W.toAEEqFun (y p.1.2, y p.1.1) = W.toAEEqFun (y p.1.1, y p.1.2) := by
    rw [eventually_countable_forall]
    intro p
    obtain ⟨htt, hff, -, -⟩ := ofGraphon_simplexRep_ae W
    filter_upwards [Graphon.ae_pairMap_of_prod p.1.1 p.1.2 p.2.ne
      ((htt.and hff).and W.symm_ae)] with y hy
    exact ⟨hy.1.1, hy.1.2, hy.2⟩
  filter_upwards [hloop, hpair, Graphon.ae_top_edges_mem_Icc W] with y hl hp hIcc
  unfold sampleEventIntegrand
  have hloop1 : (∏ i : Fin k,
      if (ofGraphon W).loopRep (y i) = G.toFiniteDigraph (digraphCoord i i) then (1 : ℝ≥0∞)
      else 0) = 1 :=
    Finset.prod_eq_one fun i _ => by
      rw [hl i, toFiniteDigraph_coord, decide_eq_false G.irrefl]
      simp
  rw [hloop1, one_mul]
  have hval : ∀ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset,
      (0 : ℝ) ≤ if e ∈ G.edgeFinset then W.toAEEqFun (y (Quot.out e).1, y (Quot.out e).2)
        else 1 - W.toAEEqFun (y (Quot.out e).1, y (Quot.out e).2) := by
    intro e he
    split_ifs
    · exact (hIcc e he).1
    · linarith [(hIcc e he).2]
  calc ∏ p : {p : Fin k × Fin k // p.1 < p.2},
        ENNReal.ofReal ((ofGraphon W).simplexRep
          (G.toFiniteDigraph (digraphCoord p.1.1 p.1.2))
          (G.toFiniteDigraph (digraphCoord p.1.2 p.1.1)) (y p.1.1, y p.1.2))
      = ∏ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset, ENNReal.ofReal
          (if e ∈ G.edgeFinset then W.toAEEqFun (y (Quot.out e).1, y (Quot.out e).2)
            else 1 - W.toAEEqFun (y (Quot.out e).1, y (Quot.out e).2)) := by
        refine Finset.prod_bij (fun p _ => s(p.1.1, p.1.2)) (fun p _ => ?_)
          (fun p _ q _ hpq => ?_) (fun e he => ?_) (fun p _ => ?_)
        · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
          exact p.2.ne
        · rcases Sym2.eq_iff.mp hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Subtype.ext (Prod.ext h1 h2)
          · exfalso
            have hlt := p.2
            rw [h1, h2] at hlt
            exact lt_asymm hlt q.2
        · have hne : (Quot.out e).1 ≠ (Quot.out e).2 :=
            Graphon.edge_out_ne (SimpleGraph.mem_edgeFinset.mp he)
          have heq : s((Quot.out e).1, (Quot.out e).2) = e := by
            simp [Sym2.mk, Quot.out_eq]
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact ⟨⟨((Quot.out e).1, (Quot.out e).2), hlt⟩, Finset.mem_univ _, heq⟩
          · exact ⟨⟨((Quot.out e).2, (Quot.out e).1), hgt⟩, Finset.mem_univ _,
              Sym2.eq_swap.trans heq⟩
        · obtain ⟨htt, hff, hsymm⟩ := hp p
          have hout : W.toAEEqFun (y (Quot.out s(p.1.1, p.1.2)).1,
                y (Quot.out s(p.1.1, p.1.2)).2)
              = W.toAEEqFun (y p.1.1, y p.1.2) := by
            rcases out_eq_or_swap p.1.1 p.1.2 with h | h
            · rw [h]
            · rw [h]
              exact hsymm
          rw [toFiniteDigraph_coord, toFiniteDigraph_coord,
            decide_eq_decide.mpr (G.adj_comm p.1.2 p.1.1)]
          by_cases hadj : G.Adj p.1.1 p.1.2
          · rw [decide_eq_true hadj, htt,
              if_pos (SimpleGraph.mem_edgeFinset.mpr (G.mem_edgeSet.mpr hadj)), hout]
          · rw [decide_eq_false hadj, hff,
              if_neg (fun hc => hadj (G.mem_edgeSet.mp
                (SimpleGraph.mem_edgeFinset.mp hc))), hout]
    _ = ENNReal.ofReal (∏ e ∈ (⊤ : SimpleGraph (Fin k)).edgeFinset,
          if e ∈ G.edgeFinset then W.toAEEqFun (y (Quot.out e).1, y (Quot.out e).2)
          else 1 - W.toAEEqFun (y (Quot.out e).1, y (Quot.out e).2)) :=
        (ENNReal.ofReal_prod_of_nonneg hval).symm
    _ = ENNReal.ofReal (Graphon.sampleIntegrand W G y) := by
        congr 1
        rw [Graphon.sampleIntegrand, mul_comm, ← Finset.prod_sdiff
          (SimpleGraph.edgeFinset_mono (le_top : G ≤ ⊤))]
        exact congrArg₂ (· * ·)
          (Finset.prod_congr rfl fun e he => if_neg (Finset.mem_sdiff.mp he).2)
          (Finset.prod_congr rfl fun e he => if_pos he)

/-- **Off the range of the embedding the exact-event lintegral vanishes**: a prescribed loop
is a.e. impossible, and an asymmetric reciprocal pair forces an a.e.-null antisymmetric
`simplexRep` factor. -/
private theorem lintegral_sampleEventIntegrand_ofGraphon_ne (W : Graphon α μ) {k : ℕ}
    {D : FiniteDigraph k}
    (hD : ¬ ((∀ i, D (digraphCoord i i) = false) ∧
      ∀ i j : Fin k, D (digraphCoord i j) = D (digraphCoord j i))) :
    ∫⁻ y, (ofGraphon W).sampleEventIntegrand D y ∂(Measure.pi fun _ : Fin k => μ) = 0 := by
  rw [lintegral_eq_zero_iff ((ofGraphon W).measurable_sampleEventIntegrand D)]
  rw [not_and_or] at hD
  rcases hD with h1 | h2
  · -- a loop bit is prescribed, but the embedding has no loops a.e.
    obtain ⟨i, hi⟩ := not_forall.mp h1
    have hi' : D (digraphCoord i i) = true := by simpa using hi
    have hloop : ∀ᵐ y ∂(Measure.pi fun _ : Fin k => μ),
        (ofGraphon W).loopRep (y i) = false :=
      (measurePreserving_eval (fun _ : Fin k => μ) i).quasiMeasurePreserving.ae
        (ofGraphon_loop_ae W)
    filter_upwards [hloop] with y hy
    unfold sampleEventIntegrand
    have hfac : (if (ofGraphon W).loopRep (y i) = D (digraphCoord i i) then (1 : ℝ≥0∞) else 0)
        = 0 := by
      rw [hy, hi']
      simp
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hfac, zero_mul]
    simp
  · -- an asymmetric pair is prescribed, but the antisymmetric masses vanish a.e.
    obtain ⟨i, hj⟩ := not_forall.mp h2
    obtain ⟨j, hij⟩ := not_forall.mp hj
    have hne : i ≠ j := fun h => hij (by rw [h])
    obtain ⟨a, b, hab, hne'⟩ : ∃ a b : Fin k, a < b ∧
        D (digraphCoord a b) ≠ D (digraphCoord b a) := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨i, j, h, hij⟩
      · exact ⟨j, i, h, fun hc => hij hc.symm⟩
    have hzero : ∀ᵐ q ∂(μ.prod μ),
        (ofGraphon W).simplexRep (D (digraphCoord a b)) (D (digraphCoord b a)) q = 0 := by
      obtain ⟨-, -, htf, hft⟩ := ofGraphon_simplexRep_ae W
      rcases hx : D (digraphCoord a b) with _ | _ <;>
        rcases hz : D (digraphCoord b a) with _ | _
      · exact absurd (hx.trans hz.symm) hne'
      · filter_upwards [hft] with q hq using hq
      · filter_upwards [htf] with q hq using hq
      · exact absurd (hx.trans hz.symm) hne'
    filter_upwards [Graphon.ae_pairMap_of_prod a b hab.ne hzero] with y hy
    unfold sampleEventIntegrand
    have hfac : ENNReal.ofReal ((ofGraphon W).simplexRep (D (digraphCoord a b))
        (D (digraphCoord b a)) (y a, y b)) = 0 := by
      rw [hy, ENNReal.ofReal_zero]
    rw [Finset.prod_eq_zero (Finset.mem_univ
      (⟨(a, b), hab⟩ : {p : Fin k × Fin k // p.1 < p.2})) hfac, mul_zero]
    simp

/-- **The embedded ordinary graphon samples the undirected `W`-random graph** (D3c headline):
the law of the `k`-vertex digraph sample of `ofGraphon W` is the pushforward of the undirected
sample law `Graphon.samplePMF W k` under the symmetric loopless embedding. -/
theorem map_sampleFinite_ofGraphon (W : Graphon α μ) (k : ℕ) :
    (samplerSource μ).map ((Digraphon.ofGraphon W).sampleFinite k) =
      ((Graphon.samplePMF W k).toMeasure).map SimpleGraph.toFiniteDigraph := by
  classical
  refine Measure.ext_of_singleton fun D => ?_
  rw [Measure.map_apply ((ofGraphon W).measurable_sampleFinite k) (measurableSet_singleton D),
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton D)]
  by_cases hD : ∃ G : SimpleGraph (Fin k), G.toFiniteDigraph = D
  · obtain ⟨G, rfl⟩ := hD
    have hpre : SimpleGraph.toFiniteDigraph ⁻¹' {G.toFiniteDigraph} = {G} := by
      ext H
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => toFiniteDigraph_injective h, fun h => by rw [h]⟩
    rw [hpre, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton G),
      Graphon.samplePMF_apply]
    exact ((ofGraphon W).samplerSource_sampleFinite_singleton G.toFiniteDigraph).trans
      (lintegral_sampleEventIntegrand_toFiniteDigraph W G)
  · have hpre : SimpleGraph.toFiniteDigraph ⁻¹' {D} = (∅ : Set (SimpleGraph (Fin k))) := by
      ext H
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun h => hD ⟨H, h⟩
    rw [hpre, measure_empty]
    exact ((ofGraphon W).samplerSource_sampleFinite_singleton D).trans
      (lintegral_sampleEventIntegrand_ofGraphon_ne W
        fun hcls => hD ((exists_toFiniteDigraph_eq_iff D).mpr hcls))

end GraphonEmbedding

end MeasureTheory.Digraphon
