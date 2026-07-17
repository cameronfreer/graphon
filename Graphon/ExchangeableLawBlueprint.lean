/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.RelLawEquivalence
import Graphon.InfiniteDigraphLaw
import Graphon.DigraphSampler
import Graphon.RelExtremality

/-!
# Blueprint nodes for the relational / directed exchangeable-law equivalences

Annotation-only wrappers carrying the blueprint-graph nodes for the generic relational
finite/infinite exchangeable-law equivalence (R2c, #105) and its directed specialization
(D2, #86). Housing the `Architect` dependency and the `@[blueprint]` annotations here keeps
the reusable foundational modules `Graphon.RelLawEquivalence` and `Graphon.InfiniteDigraphLaw`
free of the blueprint framework (they are upstream/reuse candidates).

The mathematical content lives in those modules (`relExchangeableLawEquiv`,
`exchangeableDigraphLawEquiv`); the wrappers below merely record their existence for the
dependency graph.
-/

open MeasureTheory RelSignature

/-- **The generic relational exchangeable-law equivalence** (Aldous–Hoover–Kallenberg,
finite-marginal ↔ infinite-law layer): for a finite-sort, countable-relation signature the
size-vector-indexed families of consistent probability marginals correspond exactly to the
relabelling-invariant probability laws on the infinite structure space. -/
@[blueprint "thm:rel-exchangeable-law-equivalence"
  (title := /-- The generic relational exchangeable-law equivalence -/)]
theorem relExchangeableLawEquiv_blueprint {S : RelSignature} [Fintype S.Srt] [Countable S.Rel] :
    Nonempty (RelExchangeableLaw S ≃ InfiniteRelExchangeableLaw S) :=
  ⟨relExchangeableLawEquiv⟩

/-- **The directed finite/infinite exchangeable-law equivalence** (D2): the `PMF`-based
exchangeable directed-graph laws correspond exactly to the relabelling-invariant laws on the
infinite digraph space — the one-sort, single-binary-relation specialization of the generic
relational equivalence. (This is the projective-law equivalence; the directed representation
theorem is later.) -/
@[blueprint "thm:directed-exchangeable-law-equivalence"
  (title := /-- The directed finite/infinite exchangeable-law equivalence -/)]
theorem exchangeableDigraphLawEquiv_blueprint :
    Nonempty (ExchangeableDigraphLaw ≃ InfiniteExchangeableDigraphLaw) :=
  ⟨exchangeableDigraphLawEquiv⟩

/-- **The digraphon sampler realizes its exchangeable law** (D3b): sampling i.i.d. latent
positions and one categorical reciprocal-edge draw per unordered pair realizes, on the infinite
digraph space, exactly the infinite exchangeable law of the sampled `PMF`-based digraph law —
identified through the directed finite/infinite equivalence. -/
@[blueprint "thm:digraphon-sampler-realization"
  (title := /-- The digraphon sampler realizes its exchangeable law -/)]
theorem map_sampleInfinite_blueprint {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] (W : Digraphon α μ) :
    (Digraphon.samplerSource μ).map W.sampleInfinite =
      ((exchangeableDigraphLawEquiv W.sampleDigraphLaw).law : Measure InfiniteDigraph) :=
  W.map_sampleInfinite_eq_equiv_law

open scoped ENNReal in
/-- **The five-way relational extremality equivalence** (R3, #106): for an exchangeable law
on the infinite structure space of a finite-sort signature, dissociation, restriction
independence, vertex-tail triviality, ergodicity under the finitely supported sortwise
relabelings, and genuine extremality in the invariant probability simplex all coincide —
representation-free (Lévy's downward theorem closes the tail arrow; the ergodic ↔ extreme
port supplies the fifth formulation). -/
@[blueprint "thm:rel-five-way-extremality"
  (title := /-- The five-way relational extremality equivalence -/)]
theorem tfae_extremality_blueprint {S : RelSignature} [Fintype S.Srt]
    (M : InfiniteRelExchangeableLaw S) :
    List.TFAE
      [M.IsDissociated,
        M.RestrictionIndependent,
        M.VertexTailTrivial,
        M.IsErgodic,
        (M.law : MeasureTheory.Measure (RelStructure S (Vinfinite S))) ∈
          Set.extremePoints ℝ≥0∞
            (invariantProbabilityMeasures S)] :=
  tfae_extremality M
