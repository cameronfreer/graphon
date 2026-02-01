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

variable [IsProbabilityMeasure μ]

/-- The space of graphons (modulo weak isomorphism) is compact.

This is the fundamental compactness theorem for graphon theory.
It follows from total boundedness (regularity lemma) and completeness.

**Structure**: This is sequential compactness, equivalent to compactness
for metric spaces (which graphon space is, modulo weak isomorphism). -/
theorem compact :
    ∀ (W : ℕ → Graphon α μ), ∃ (V : Graphon α μ) (φ : ℕ → ℕ),
      StrictMono φ ∧ ∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W (φ n)) V < ε := by
  intro W
  -- **Proof structure** (totallyBounded + complete → compact):
  --
  -- Step 1: Extract Cauchy subsequence using totallyBounded
  --
  -- For each k ∈ ℕ, totallyBounded gives finite (1/k)-net S_k.
  -- Pigeonhole: infinitely many W_n are within 1/k of some V_k ∈ S_k.
  --
  -- - For k=1: extract infinite subsequence I₁ with all within 1 of some V₁
  -- - For k=2: extract infinite subsequence I₂ ⊆ I₁ with all within 1/2 of some V₂
  -- - Continue...
  -- - Diagonal: φ(n) = n-th element of Iₙ

  -- Step 2: Show W ∘ φ is Cauchy
  -- For m, n ≥ N (where N chosen for ε/2):
  -- d(W(φ(m)), W(φ(n))) ≤ d(W(φ(m)), V_N) + d(V_N, W(φ(n))) < 1/N + 1/N ≤ ε

  -- Step 3: Apply complete to get limit V
  -- complete gives V such that W(φ(n)) → V in cut distance

  -- **Technical requirements**:
  -- - totallyBounded: gives finite ε-net for each ε
  -- - complete: gives limit for Cauchy sequences
  -- - Both have sorries blocking full proof
  sorry

end Compactness

end Graphon
