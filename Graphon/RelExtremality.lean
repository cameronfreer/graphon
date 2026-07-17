/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelErgodicLinks
import Graphon.RelErgodicExtreme
import Graphon.InfiniteDigraphLaw

/-!
# The five-way extremality equivalence for exchangeable relational laws (R3c, #106)

The honest, representation-free five-way characterization: for an exchangeable law on the
infinite structure space of a finite-sort signature,

**dissociated ↔ restriction-independent ↔ vertex-tail-trivial ↔ ergodic ↔ extreme point of
the invariant probability simplex**,

assembled from the R3a block machinery, the R3b triangle (closed by Lévy's downward
theorem), the R3c ergodicity links, and the ported ergodic ↔ extreme-point theorem. No
functional-AHK or mixing-representation input anywhere in the proof graph; the Dirac-mixing
description of the extreme laws is a later corollary of R5.

The directed specialization (`digraphSig`) is exercised as a regression test: the generic
equivalence applies verbatim to `InfiniteExchangeableDigraphLaw`.
-/

open MeasureTheory
open scoped ENNReal

namespace RelSignature

variable {S : RelSignature}

/-- **The five-way extremality equivalence** (R3c): dissociation, restriction independence,
vertex-tail triviality, ergodicity under the finitely supported relabelings, and genuine
extremality in the invariant probability simplex all coincide. -/
theorem tfae_extremality [Fintype S.Srt] (M : InfiniteRelExchangeableLaw S) :
    List.TFAE
      [M.IsDissociated,
        M.RestrictionIndependent,
        M.VertexTailTrivial,
        M.IsErgodic,
        (M.law : Measure (RelStructure S (Vinfinite S))) ∈
          Set.extremePoints ℝ≥0∞
            {ν : Measure (RelStructure S (Vinfinite S)) |
              (∀ σ, SortwiseFinSupp (S := S) σ → ν.map (RelStructure.relabel σ) = ν) ∧
              IsProbabilityMeasure ν}] := by
  tfae_have 1 ↔ 2 := isDissociated_iff_restrictionIndependent M
  tfae_have 1 ↔ 3 := isDissociated_iff_vertexTailTrivial M
  tfae_have 4 ↔ 1 := isErgodic_iff_isDissociated M
  tfae_have 4 ↔ 5 := M.isErgodic_iff_mem_extremePoints
  tfae_finish

/-- **Extremality ↔ dissociation**, the endpoint pairing of the five-way equivalence. -/
theorem isDissociated_iff_mem_extremePoints [Fintype S.Srt]
    (M : InfiniteRelExchangeableLaw S) :
    M.IsDissociated ↔ (M.law : Measure (RelStructure S (Vinfinite S))) ∈
      Set.extremePoints ℝ≥0∞
        {ν : Measure (RelStructure S (Vinfinite S)) |
          (∀ σ, SortwiseFinSupp (S := S) σ → ν.map (RelStructure.relabel σ) = ν) ∧
          IsProbabilityMeasure ν} :=
  (tfae_extremality M).out 0 4

end RelSignature

/-! ### Directed regression test (the `digraphSig` specialization) -/

section DigraphRegression

open RelSignature

/-- The generic five-way equivalence applies verbatim to infinite exchangeable
directed-graph laws (D2's `InfiniteExchangeableDigraphLaw = InfiniteRelExchangeableLaw
digraphSig`). -/
example (M : InfiniteExchangeableDigraphLaw) :
    M.IsDissociated ↔ M.IsErgodic :=
  (isErgodic_iff_isDissociated M).symm

example (M : InfiniteExchangeableDigraphLaw) :
    M.VertexTailTrivial ↔ (M.law : Measure InfiniteDigraph) ∈
      Set.extremePoints ℝ≥0∞
        {ν : Measure InfiniteDigraph |
          (∀ σ, SortwiseFinSupp (S := digraphSig) σ →
            ν.map (RelStructure.relabel σ) = ν) ∧ IsProbabilityMeasure ν} :=
  ((tfae_extremality M).out 2 4)

end DigraphRegression
