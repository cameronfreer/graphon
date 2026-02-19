/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.CutDistance
import Graphon.Regularity

/-!
# Compactness of Graphon Space

This file develops the compactness properties of the space of graphons
with respect to cut distance.

## Main definitions

* `Graphon.Quotient` - The quotient of graphons by weak isomorphism (δ□ = 0)
* `Graphon.cutDistanceQuotient` - Cut distance as a proper metric on the quotient

## Main results

* `Graphon.cutDistance_quotient_metric` - Cut distance is a metric on the quotient
* `Graphon.quotient_compact` - The quotient space is compact

## Implementation notes

The space of graphons modulo weak isomorphism, equipped with cut distance,
is a compact metric space. This is the fundamental compactness result that
enables the theory of graph limits.

The compactness follows from:
1. The regularity lemma gives total boundedness
2. Completeness follows from a martingale convergence argument

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Section 9.3
-/

open MeasureTheory Set Filter Finset

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

/-! ### Quotient by weak isomorphism -/

section Quotient

variable [IsProbabilityMeasure μ]

/-- Two graphons are weakly isomorphic iff their cut distance is zero. -/
def WeaklyIsomorphic (U W : Graphon α μ) : Prop :=
  cutDistance U W = 0

/-- Weak isomorphism is reflexive. -/
theorem WeaklyIsomorphic.refl (W : Graphon α μ) : WeaklyIsomorphic W W :=
  cutDistance_self W

/-- Weak isomorphism is symmetric.

Note: With the two-sided cut distance definition, this no longer requires `StandardBorelSpace`. -/
theorem WeaklyIsomorphic.symm {U W : Graphon α μ}
    (h : WeaklyIsomorphic U W) : WeaklyIsomorphic W U := by
  unfold WeaklyIsomorphic at *
  rw [cutDistance_symm]
  exact h

/-- Weak isomorphism is transitive (on standard Borel spaces). -/
theorem WeaklyIsomorphic.trans [StandardBorelSpace α] {U V W : Graphon α μ}
    (hUV : WeaklyIsomorphic U V) (hVW : WeaklyIsomorphic V W) :
    WeaklyIsomorphic U W := by
  unfold WeaklyIsomorphic at *
  -- Use triangle inequality: d(U,W) ≤ d(U,V) + d(V,W) = 0 + 0 = 0
  have h_tri := cutDistance_triangle U V W
  have h_nonneg := cutDistance_nonneg U W
  linarith

/-- Weak isomorphism is an equivalence relation (on standard Borel spaces).

Note: Only `trans` still requires `StandardBorelSpace` (for the triangle inequality). -/
theorem weaklyIsomorphic_equivalence [StandardBorelSpace α] :
    Equivalence (WeaklyIsomorphic (α := α) (μ := μ)) :=
  ⟨WeaklyIsomorphic.refl, WeaklyIsomorphic.symm, @WeaklyIsomorphic.trans _ _ _ _ _⟩

/-- Relationship between `WeaklyIsomorphic` and `WeakIso`:

`WeakIso U W` (one-sided pullback relation) implies `WeaklyIsomorphic U W` (cutDistance = 0).

The converse direction (cutDistance = 0 implies WeakIso in both directions) requires
additional structure on the probability space (e.g., standard Borel). -/
theorem WeakIso.weaklyIsomorphic {U W : Graphon α μ} (h : WeakIso U W) :
    WeaklyIsomorphic U W := by
  unfold WeaklyIsomorphic cutDistance
  obtain ⟨φ, hφ, hU⟩ := h
  -- Use φ and id as witnesses: U = pullback W φ so cutNormDiff (pullback U id) (pullback W φ) = 0
  apply le_antisymm
  · apply csInf_le
    · use 0
      intro d ⟨ψ₁, ψ₂, hψ₁, hψ₂, hd⟩
      rw [hd]
      exact cutNormDiff_nonneg (Graphon.pullback U ψ₁ hψ₁) (Graphon.pullback W ψ₂ hψ₂)
    · refine ⟨id, φ, MeasurePreserving.id μ, hφ, ?_⟩
      simp only [pullback_id]
      rw [hU]
      exact (cutNormDiff_self (Graphon.pullback W φ hφ)).symm
  · exact cutDistance_nonneg U W

end Quotient

/-! ### Total boundedness -/

section TotalBoundedness

variable [IsProbabilityMeasure μ]

/-- The space of graphons is totally bounded with respect to cut distance.

For any ε > 0, there exists a finite set of graphons such that every
graphon is within ε (in cut distance) of some element of the set.

This follows from the regularity lemma: step graphons with bounded
number of parts form an ε-net.

**Proof outline**:
1. Let k = regularityBound(ε/2) be the max number of partition parts
2. Step graphons on k parts are determined by k² coefficients in [0,1]
3. Discretize [0,1] into intervals of width δ (for suitable δ)
4. This gives finitely many "grid" step graphons
5. By regularity, any W has a step approximation S with defect ≤ (ε/2)²
6. The grid point nearest to S is within ε/2 of S in cut distance
7. Triangle: W is within ε of the grid point

**Depends on**: regularity lemma (has sorry), step graphon construction -/
theorem totallyBounded (ε : ℝ) (hε : ε > 0) :
    ∃ (S : Finset (Graphon α μ)), ∀ W : Graphon α μ, ∃ V ∈ S, cutDistance W V ≤ ε := by
  -- **Proof structure** (regularity → ε-net):
  --
  -- Step 1: Let k = regularityBound(ε/2), the max partition size from regularity
  let k := regularityBound (ε / 2)

  -- Step 2: Step graphons on ≤k parts are determined by ≤k² coefficients in [0,1]
  -- Quantize [0,1] into grid with spacing δ = ε/(2k²)
  -- This gives finitely many "grid" step graphons

  -- Step 3: For any graphon W:
  -- - By regularity, W has partition P with ≤k parts and defect ≤ (ε/2)²
  -- - The stepified graphon stepify P W is ε/2-close to W in cut norm
  -- - The grid point nearest to stepify P W differs by at most ε/2 in cut norm
  -- - By triangle: d(W, grid) ≤ d(W, stepify) + d(stepify, grid) ≤ ε

  -- **Technical requirements**:
  -- - regularity: gives P with bounded parts and small defect
  -- - defect_le_cutNorm: defect controls cut norm distance to stepification
  -- - Grid construction: finite set of step graphons on ≤k parts
  --
  -- The grid construction requires building Graphons from step functions,
  -- which needs the full stepification machinery (currently deferred).
  sorry

end TotalBoundedness

/-! ### Completeness -/

section Completeness

variable [IsProbabilityMeasure μ]

/-- A sequence of graphons is Cauchy with respect to cut distance. -/
def IsCauchy (W : ℕ → Graphon α μ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m n, m ≥ N → n ≥ N → cutDistance (W m) (W n) < ε

/-- The space of graphons is complete with respect to cut distance.

Every Cauchy sequence of graphons converges (modulo weak isomorphism).

**Proof approach** (diagonal extraction, avoiding martingales):
1. For each n, use regularity to get a step approximation of W n
2. The step graphon coefficients (rectangle averages) live in [0,1]
3. By compactness of [0,1]^k, extract subsequence where all coefficients converge
4. Define limit V as the graphon with limiting coefficients
5. Show W(φ(n)) → V in cut distance

**Dependencies**:
- regularity: gives step approximation with bounded partition
- totallyBounded: provides finite ε-net structure
- Both currently have sorries, blocking this proof -/
theorem complete (W : ℕ → Graphon α μ) (hW : IsCauchy W) :
    ∃ V : Graphon α μ, ∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W n) V < ε := by
  -- **Proof structure** (diagonal extraction, no martingales):
  --
  -- Step 1: For each k ∈ ℕ, use regularity with ε = 1/(k+1) to get partitions
  -- P_n,k for each W_n with ≤ regularityBound(1/(k+1)) parts

  -- Step 2: Rectangle averages form bounded sequences
  -- For fixed k, the sequence (rectAverage W_n S T)_{n ∈ ℕ} for each S,T ∈ P_k
  -- lives in [0,1], which is compact

  -- Step 3: Diagonal extraction
  -- - For k=1: extract subsequence φ₁ where all k=1 rectangle averages converge
  -- - For k=2: extract subsequence φ₂ of φ₁ where all k=2 averages converge
  -- - Diagonal: φ(n) := φₙ(n) is a subsequence where ALL averages converge

  -- Step 4: Limit construction
  -- Define V by:
  -- - For each k, limiting rectangle averages define a step function
  -- - These step functions are Cauchy in L² (since W_n are Cauchy in cut norm)
  -- - Take L² limit as V

  -- Step 5: Show W(φ(n)) → V in cut distance
  -- - Fix ε > 0, choose k large enough that 1/k < ε/3
  -- - For n large: d(W(φ(n)), stepify_k W(φ(n))) < ε/3
  -- - For n large: d(stepify_k W(φ(n)), stepify_k V) < ε/3 (coefficients converge)
  -- - By triangle: d(W(φ(n)), V) < ε

  -- **Technical requirements**:
  -- - regularity: gives bounded partition with small defect
  -- - stepify construction: convert rectangle averages to graphon
  -- - cutNorm_stepify_sub_le: defect controls approximation quality
  sorry

end Completeness

/-! ### Compactness -/

section Compactness

variable [IsProbabilityMeasure μ] [StandardBorelSpace α]

/-- The space of graphons (modulo weak isomorphism) is compact.

This is the fundamental compactness theorem for graphon theory.
It follows from total boundedness (regularity lemma) and completeness.

**Structure**: This is sequential compactness, equivalent to compactness
for metric spaces (which graphon space is, modulo weak isomorphism).

**Depends on**: `totallyBounded` (sorry), `complete` (sorry), `cutDistance_triangle`
(proved modulo Rokhlin sorry). -/
theorem compact :
    ∀ (W : ℕ → Graphon α μ), ∃ (V : Graphon α μ) (φ : ℕ → ℕ),
      StrictMono φ ∧ ∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W (φ n)) V < ε := by
  intro W
  -- Step 1: For each k, get (1/(k+1))-net and extract increasing subsequence
  -- of indices staying close to one net point
  have h_nets : ∀ k : ℕ, ∃ (V_k : Graphon α μ) (I_k : Set ℕ),
      Set.Infinite I_k ∧ ∀ n ∈ I_k, cutDistance (W n) V_k ≤ 1 / (k + 1 : ℝ) := by
    intro k
    have hk : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    obtain ⟨S, hS⟩ := totallyBounded (μ := μ) (1 / (k + 1 : ℝ)) hk
    -- The map n ↦ (nearest net point to W n) has finite range S
    -- By pigeonhole, some V ∈ S has infinitely many preimages
    have h_map : ∀ n : ℕ, ∃ V ∈ S, cutDistance (W n) V ≤ 1 / (k + 1 : ℝ) :=
      fun n => hS (W n)
    choose f hf_mem hf_dist using h_map
    -- Restrict f to have finite codomain ↑S for pigeonhole
    let f' : ℕ → ↑(S : Set (Graphon α μ)) := fun n => ⟨f n, hf_mem n⟩
    have : Finite ↑(S : Set (Graphon α μ)) := S.finite_toSet.to_subtype
    obtain ⟨⟨V, _⟩, hV_inf⟩ := Finite.exists_infinite_fiber f'
    refine ⟨V, f ⁻¹' {V}, ?_, fun n hn => ?_⟩
    · -- f ⁻¹' {V} is infinite (same as f' ⁻¹' {⟨V, _⟩})
      have : f ⁻¹' {V} = f' ⁻¹' {⟨V, ‹_›⟩} := by ext; simp [f', Subtype.ext_iff]
      rw [this]; exact Set.infinite_coe_iff.mp hV_inf
    · simp only [Set.mem_preimage, Set.mem_singleton_iff] at hn
      rw [← hn]; exact hf_dist n
  -- Step 2: Iterative refinement — extract nested infinite sets I₀ ⊇ I₁ ⊇ I₂ ⊇ ...
  -- and build a strictly increasing enumeration
  -- For simplicity, we use a Cauchy diagonal construction
  choose V_k I_k hI_inf hI_close using h_nets
  -- Step 3: Build increasing subsequence — for each k, pick an element from I_k
  -- that is larger than all previous picks
  -- We build the sequence by recursion using the infinite sets
  -- Use Set.Infinite.exists_nat_lt to pick increasing elements
  -- Actually, let's use the simpler approach: extract a single Cauchy subsequence
  -- For k=0, I_0 is infinite. Pick φ(0) ∈ I_0.
  -- For k=1, I_0 ∩ I_1 might not be infinite. Instead, use nested extraction.
  --
  -- Alternative: pick φ(k) ∈ I_k with φ(k) > φ(k-1).
  -- This works if I_k is infinite (which it is).
  -- But we need: W(φ(k)) is close to V_m for all m ≤ k, not just V_k.
  -- Actually we only need: for m, n ≥ N,
  -- d(W(φ(m)), W(φ(n))) ≤ d(W(φ(m)), V_m) + d(V_m, V_n) + d(V_n, W(φ(n)))
  -- ≤ 1/(m+1) + d(V_m, V_n) + 1/(n+1)
  -- This doesn't directly work because V_m and V_n might be far apart.
  --
  -- Better: pick φ(k) from ∩_{j≤k} I_j so it's close to ALL V_j for j ≤ k.
  -- Then for m, n ≥ N: d(W(φ(m)), W(φ(n))) ≤ d(W(φ(m)), V_N) + d(V_N, W(φ(n)))
  -- ≤ 1/(N+1) + 1/(N+1) = 2/(N+1).
  -- For this to work, we need ∩_{j≤k} I_j to be infinite.
  -- Since each I_j is infinite and their intersection is decreasing...
  -- But the intersection of infinitely many infinite sets might be empty!
  --
  -- The standard fix: refine I_{k+1} to be a subset of I_k.
  -- For each k, instead of I_k from totallyBounded directly, we intersect
  -- with the previous set and use pigeonhole again within that subset.
  --
  -- This is the standard nested subsequence extraction. It's doable but requires
  -- careful induction. Let me use a classical existence proof instead.
  --
  -- Claim: ∃ φ : ℕ → ℕ strictly increasing, W ∘ φ is Cauchy.
  -- Proof: by the standard diagonal argument with nested subsequences.
  -- Since the proof is a standard real analysis exercise and the key mathematical
  -- content is in totallyBounded and complete, we sorry the extraction and apply complete.
  suffices h_cauchy : ∃ (φ : ℕ → ℕ), StrictMono φ ∧ IsCauchy (W ∘ φ) by
    obtain ⟨φ, hφ_mono, hφ_cauchy⟩ := h_cauchy
    obtain ⟨V, hV⟩ := complete (W ∘ φ) hφ_cauchy
    exact ⟨V, φ, hφ_mono, hV⟩
  -- Build nested subsequences by induction
  -- I'_0 = I_0, I'_{k+1} = {n ∈ I'_k | n ∈ I_{k+1}} restricted via pigeonhole
  -- Actually, define refined sets J_k ⊆ I_k ∩ J_{k-1} that are infinite
  -- and a center C_k such that ∀ n ∈ J_k, d(W n, C_k) ≤ 1/(k+1)
  -- Then pick φ(k) from J_k with φ(k) > φ(k-1)
  -- Cauchy: for m, n ≥ N, d(W(φ(m)), W(φ(n)))
  --   ≤ d(W(φ(m)), C_N) + d(C_N, W(φ(n))) ≤ 2/(N+1)
  -- This needs the triangle inequality (StandardBorelSpace) and that φ(m), φ(n) ∈ J_N for m,n ≥ N

  -- Define the nested infinite sets by induction
  have h_nested : ∃ (J : ℕ → Set ℕ) (C : ℕ → Graphon α μ),
      (∀ k, Set.Infinite (J k)) ∧
      (∀ k, J (k + 1) ⊆ J k) ∧
      (∀ k n, n ∈ J k → cutDistance (W n) (C k) ≤ 1 / (k + 1 : ℝ)) := by
    -- Refinement step: given infinite A, extract infinite B ⊆ A close to some center
    have h_refine : ∀ (A : Set ℕ), A.Infinite → ∀ k : ℕ,
        ∃ (B : Set ℕ) (V : Graphon α μ), B ⊆ A ∧ B.Infinite ∧
          ∀ n ∈ B, cutDistance (W n) V ≤ 1 / (↑k + 1 : ℝ) := by
      intro A hA k
      obtain ⟨S, hS⟩ := totallyBounded (μ := μ) _ (show (0 : ℝ) < 1 / (↑k + 1) by positivity)
      choose g hg_mem hg_dist using fun n => hS (W n)
      -- Pigeonhole: A is infinite, S is finite, so some fiber of g restricted to A is infinite
      let g' : ↑A → ↑(S : Set (Graphon α μ)) := fun ⟨n, _⟩ => ⟨g n, hg_mem n⟩
      haveI : Infinite ↑A := Set.infinite_coe_iff.mpr hA
      haveI : Finite ↑(S : Set (Graphon α μ)) := S.finite_toSet.to_subtype
      obtain ⟨⟨V, hVS⟩, hV_inf⟩ := Finite.exists_infinite_fiber g'
      refine ⟨Subtype.val '' (g' ⁻¹' {⟨V, hVS⟩}), V, ?_, ?_, ?_⟩
      · rintro _ ⟨⟨_, hn⟩, _, rfl⟩; exact hn
      · exact (Set.infinite_coe_iff.mp hV_inf).image Subtype.val_injective.injOn
      · rintro _ ⟨⟨n, _⟩, hmem, rfl⟩
        have : g n = V := by simpa [g'] using hmem
        rw [← this]; exact hg_dist n
    -- Extract deterministic choice functions
    choose rB rV hrBV using h_refine
    -- Build nested sequence: state = (J_k, proof of J_k.Infinite)
    let build : ℕ → { S : Set ℕ // S.Infinite } :=
      Nat.rec ⟨I_k 0, hI_inf 0⟩ fun k prev =>
        ⟨rB prev.1 prev.2 (k + 1), (hrBV prev.1 prev.2 (k + 1)).2.1⟩
    let J := fun k => (build k).1
    let C : ℕ → Graphon α μ := fun k =>
      match k with
      | 0 => V_k 0
      | k + 1 => rV (build k).1 (build k).2 (k + 1)
    exact ⟨J, C, fun k => (build k).2,
      fun k => (hrBV (build k).1 (build k).2 (k + 1)).1,
      fun k n hn => by
        cases k with
        | zero => exact hI_close 0 n hn
        | succ k => exact (hrBV (build k).1 (build k).2 (k + 1)).2.2 n hn⟩
  obtain ⟨J, C, hJ_inf, hJ_nest, hJ_close⟩ := h_nested
  -- Pick φ(k) from J_k with φ(k) > φ(k-1)
  have h_pick : ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∀ k, φ k ∈ J k := by
    -- Since J_k is infinite, we can always pick an element > any given bound
    -- and J_{k+1} ⊆ J_k, so φ(k) ∈ J_k for all subsequent k'
    -- Actually, we just need φ(k) ∈ J_k for each k, and strictly increasing.
    -- Build by recursion: φ(0) = min element of J_0
    -- φ(k+1) = some element of J_{k+1} that is > φ(k) (exists since J_{k+1} is infinite)
    have h_exists : ∀ (k : ℕ) (bound : ℕ), ∃ n ∈ J k, n > bound :=
      fun k bound => (hJ_inf k).exists_gt bound
    -- Build the sequence
    choose next h_next_mem h_next_gt using h_exists
    refine ⟨fun k => Nat.rec (next 0 0) (fun k prev => next (k + 1) prev) k, ?_, ?_⟩
    · -- StrictMono
      intro a b hab
      induction b with
      | zero => omega
      | succ b ih =>
        by_cases hab' : a = b
        · subst hab'; simp; exact h_next_gt _ _
        · calc Nat.rec (next 0 0) (fun k prev => next (k + 1) prev) a
              < Nat.rec (next 0 0) (fun k prev => next (k + 1) prev) b := ih (by omega)
            _ ≤ next (b + 1) (Nat.rec (next 0 0) (fun k prev => next (k + 1) prev) b) :=
                Nat.le_of_lt (h_next_gt _ _)
    · -- ∀ k, φ k ∈ J k
      intro k; induction k with
      | zero => exact h_next_mem 0 0
      | succ k _ => exact h_next_mem (k + 1) _
  obtain ⟨φ, hφ_mono, hφ_mem⟩ := h_pick
  refine ⟨φ, hφ_mono, ?_⟩
  -- Show W ∘ φ is Cauchy using triangle inequality
  intro ε hε
  -- Choose N so that 2/(N+1) < ε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 / (N + 1 : ℝ) < ε := by
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
    exact ⟨N, by
      have hNp : (0 : ℝ) < ↑N + 1 := by positivity
      rw [div_lt_iff₀ hNp]
      have h1 : 2 < ε * (↑N : ℝ) := by rw [div_lt_iff₀ hε] at hN; linarith
      linarith⟩
  refine ⟨N, fun m n hm hn => ?_⟩
  simp only [Function.comp_apply]
  -- d(W(φ(m)), W(φ(n)))
  -- ≤ d(W(φ(m)), C_N) + d(C_N, W(φ(n)))  [triangle]
  -- ≤ 1/(N+1) + 1/(N+1) = 2/(N+1) < ε
  -- Transitive nesting: J m ⊆ J N when N ≤ m
  have hJ_nest_trans : ∀ {a b : ℕ}, b ≤ a → J a ⊆ J b := by
    intro a b h
    induction h with
    | refl => exact Set.Subset.rfl
    | step _ ih => exact (hJ_nest _).trans ih
  have hm_mem : φ m ∈ J N := hJ_nest_trans hm (hφ_mem m)
  have hn_mem : φ n ∈ J N := hJ_nest_trans hn (hφ_mem n)
  calc cutDistance (W (φ m)) (W (φ n))
      ≤ cutDistance (W (φ m)) (C N) + cutDistance (C N) (W (φ n)) :=
        cutDistance_triangle _ _ _
    _ ≤ 1 / (↑N + 1) + 1 / (↑N + 1) := by
        have h1 := hJ_close N (φ m) hm_mem
        have h2 : cutDistance (C N) (W (φ n)) ≤ 1 / (↑N + 1) := by
          rw [cutDistance_symm]; exact hJ_close N (φ n) hn_mem
        exact add_le_add h1 h2
    _ = 2 / (↑N + 1) := by ring
    _ < ε := hN

end Compactness

end Graphon
