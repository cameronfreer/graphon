/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.RelLawEquivalence
import Graphon.InfiniteDigraphLaw
import Graphon.DigraphSampler
import Graphon.SubgraphDensities

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

open scoped Classical in
/-- **The finite density triangle** (#94; Lovász §5.2.3, (5.19)–(5.21)): the zeta identity
`t_inj(F, ·) = ∑_{F' ⊇ F} t_ind(F', ·)`, its inverse Möbius form
`t_ind(F, ·) = ∑_{F' ⊇ F} (−1)^{|E(F') ∖ E(F)|} t_inj(F', ·)`, and the collision comparison
`|t − t_inj| ≤ k²/n` — all unconditional under the small-host zero convention. -/
@[blueprint "thm:finite-density-triangle"
  (title := /-- The finite density triangle: t, t_inj, t_ind -/)]
theorem finite_density_triangle_blueprint {k n : ℕ}
    (F : SimpleGraph (Fin k)) (H : SimpleGraph (Fin n)) :
    (SimpleGraph.tInj F H = ∑ F' ∈ Finset.univ.filter
        (fun F' : SimpleGraph (Fin k) => F ≤ F'), SimpleGraph.tInd F' H) ∧
      (SimpleGraph.tInd F H = ∑ F' ∈ Finset.univ.filter
          (fun F' : SimpleGraph (Fin k) => F ≤ F'),
        (-1 : ℝ) ^ (F'.edgeFinset \ F.edgeFinset).card * SimpleGraph.tInj F' H) ∧
      |SimpleGraph.t F H - SimpleGraph.tInj F H| ≤ (k : ℝ) ^ 2 / n :=
  ⟨SimpleGraph.tInj_eq_sum_tInd F H, SimpleGraph.tInd_eq_sum_neg_one_pow_tInj F H,
    SimpleGraph.abs_t_sub_tInj_le F H⟩
