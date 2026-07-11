/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.InfiniteLaw

/-!
# Exchangeability of the infinite law, and the packaged equivalence (brick A3)

The infinite law of an exchangeable graph law is invariant under every relabeling of
`ℕ`, and the finite and infinite formulations are equivalent:

* `InfiniteGraph.relabel` — relabeling by a permutation of `ℕ` (continuous, hence
  measurable);
* `InfiniteGraph.exists_perm_extend` — every injection `Fin k ↪ ℕ` extends to a
  permutation of `ℕ` (`Equiv.Set.compl` on the cofinite complements);
* `Graphon.ExchangeableGraphLaw.infiniteLaw_map_relabel` — **exchangeability of the
  infinite law**: every finite image lies in an initial segment, where injection
  consistency identifies the relabeled marginals, and uniqueness of the extension
  concludes;
* `Graphon.InfiniteExchangeableGraphLaw` — the measure-side object: a probability law
  on the infinite graph space invariant under every relabeling;
* `Graphon.exchangeableGraphLawEquivInfinite` — **the headline equivalence**
  `ExchangeableGraphLaw ≃ InfiniteExchangeableGraphLaw`, with finite marginals and the
  infinite extension as inverse maps.

This completes layers 1–2 of the Aldous–Hoover roadmap.
-/

open MeasureTheory InfiniteGraph

open scoped Classical

namespace InfiniteGraph

/-- **Relabeling** of infinite graphs by a permutation of `ℕ`. -/
def relabel (σ : Equiv.Perm ℕ) (G : InfiniteGraph) : InfiniteGraph :=
  ((G : SimpleGraph ℕ).comap σ : SimpleGraph ℕ)

@[simp] theorem relabel_adj (σ : Equiv.Perm ℕ) (G : InfiniteGraph) (a b : ℕ) :
    (relabel σ G : SimpleGraph ℕ).Adj a b ↔ (G : SimpleGraph ℕ).Adj (σ a) (σ b) :=
  Iff.rfl

/-- Edge membership under relabeling, in `Sym2` form. -/
theorem mem_edgeSet_relabel (σ : Equiv.Perm ℕ) (G : InfiniteGraph) (s : Sym2 ℕ) :
    s ∈ (relabel σ G : SimpleGraph ℕ).edgeSet ↔
      Sym2.map σ s ∈ (G : SimpleGraph ℕ).edgeSet := by
  induction s using Sym2.ind with
  | _ a b => simp [SimpleGraph.mem_edgeSet, relabel]

/-- The edge-index action of a permutation. -/
def edgeIndexMap (σ : Equiv.Perm ℕ) (e : EdgeIndex) : EdgeIndex :=
  ⟨Sym2.map σ (e : Sym2 ℕ), by
    obtain ⟨s, hs⟩ := e
    induction s using Sym2.ind with
    | _ a b =>
      simp only [Sym2.map_mk, Sym2.mk_isDiag_iff] at *
      exact fun h => hs (σ.injective h)⟩

/-- Relabeling is continuous: each output coordinate is an input coordinate. -/
theorem continuous_relabel (σ : Equiv.Perm ℕ) : Continuous (relabel σ) := by
  rw [continuous_induced_rng]
  rw [show (coordEquiv ∘ relabel σ : InfiniteGraph → EdgeIndex → Bool) =
      fun G e => coordEquiv G (edgeIndexMap σ e) from
    funext fun G => funext fun e => by
      simp only [Function.comp_apply, coordEquiv_apply, edgeIndexMap,
        mem_edgeSet_relabel]]
  exact continuous_pi fun e =>
    (continuous_apply (edgeIndexMap σ e)).comp coordHomeomorph.continuous

theorem measurable_relabel (σ : Equiv.Perm ℕ) : Measurable (relabel σ) :=
  (continuous_relabel σ).measurable

/-- Restricting a relabeled graph is comap along any finite embedding realizing the
permutation on the initial segment. -/
theorem restrictFin_relabel {k n : ℕ} (σ : Equiv.Perm ℕ) (e : Fin k ↪ Fin n)
    (he : ∀ a : Fin k, σ ↑a = ↑(e a)) (G : InfiniteGraph) :
    restrictFin k (relabel σ G) = (restrictFin n G).comap e := by
  ext a b
  simp [restrictFin, relabel, SimpleGraph.comap_adj, he]

/-- **Every injection of an initial segment into `ℕ` extends to a permutation**: the
complements are cofinite, hence equivalent, and `Equiv.Set.compl` assembles the
permutation. -/
theorem exists_perm_extend {k : ℕ} (g : Fin k ↪ ℕ) :
    ∃ σ : Equiv.Perm ℕ, ∀ a : Fin k, σ ↑a = g a := by
  classical
  let e₀ : (Set.range ((↑) : Fin k → ℕ) : Set ℕ) ≃ (Set.range g : Set ℕ) :=
    (Equiv.ofInjective _ Fin.val_injective).symm.trans (Equiv.ofInjective g g.injective)
  have hsc : ((Set.range ((↑) : Fin k → ℕ))ᶜ : Set ℕ).Infinite :=
    (Set.finite_range _).infinite_compl
  have htc : ((Set.range g)ᶜ : Set ℕ).Infinite := (Set.finite_range _).infinite_compl
  haveI := hsc.to_subtype
  haveI := htc.to_subtype
  haveI : Denumerable ((Set.range ((↑) : Fin k → ℕ))ᶜ : Set ℕ) :=
    Denumerable.ofEncodableOfInfinite _
  haveI : Denumerable ((Set.range g)ᶜ : Set ℕ) := Denumerable.ofEncodableOfInfinite _
  obtain ⟨σ, hσ⟩ := (Equiv.Set.compl e₀).symm
    ((Denumerable.eqv _).trans (Denumerable.eqv _).symm)
  refine ⟨σ, fun a => ?_⟩
  have h := hσ ⟨(↑a : ℕ), ⟨a, rfl⟩⟩
  rw [h]
  have h1 : (Equiv.ofInjective _ Fin.val_injective).symm ⟨(↑a : ℕ), ⟨a, rfl⟩⟩ = a := by
    rw [Equiv.symm_apply_eq]
    rfl
  show ((Equiv.ofInjective g g.injective)
    ((Equiv.ofInjective _ Fin.val_injective).symm ⟨(↑a : ℕ), ⟨a, rfl⟩⟩) : ℕ) = g a
  rw [h1]
  rfl

end InfiniteGraph

namespace Graphon.ExchangeableGraphLaw

/-- **Exchangeability of the infinite law**: the infinite law is invariant under every
relabeling of `ℕ`. Every finite restriction of the relabeled law lands in an initial
segment, where injection consistency identifies it with the marginal; uniqueness of the
extension concludes. -/
theorem infiniteLaw_map_relabel (L : Graphon.ExchangeableGraphLaw) (σ : Equiv.Perm ℕ) :
    (infiniteLaw L : Measure InfiniteGraph).map (relabel σ) = infiniteLaw L := by
  have key : ∀ k, (((infiniteLaw L : Measure InfiniteGraph).map (relabel σ)).map
      (restrictFin k)) = (L.law k).toMeasure := by
    intro k
    classical
    have hb : ∀ a : Fin k, σ ↑a < (Finset.univ.sup fun a : Fin k => σ ↑a) + 1 :=
      fun a => Nat.lt_succ_of_le
        (Finset.le_sup (f := fun a : Fin k => σ ↑a) (Finset.mem_univ a))
    set e : Fin k ↪ Fin ((Finset.univ.sup fun a : Fin k => σ ↑a) + 1) :=
      ⟨fun a => ⟨σ ↑a, hb a⟩, fun a b hab =>
        Fin.val_injective (σ.injective (congrArg Fin.val hab))⟩ with he
    rw [Measure.map_map (measurable_restrictFin k) (measurable_relabel σ),
      show restrictFin k ∘ relabel σ = (fun H => H.comap ⇑e) ∘
          restrictFin ((Finset.univ.sup fun a : Fin k => σ ↑a) + 1) from
        funext fun G => restrictFin_relabel σ e (fun a => rfl) G,
      ← Measure.map_map (SimpleGraph.measurable_comap ⇑e) (measurable_restrictFin _),
      infiniteLaw_map_restrictFin L,
      PMF.toMeasure_map _ _ (SimpleGraph.measurable_comap ⇑e), L.consistent e]
  have hP : (⟨(infiniteLaw L : Measure InfiniteGraph).map (relabel σ),
      Measure.isProbabilityMeasure_map (measurable_relabel σ).aemeasurable⟩ :
        ProbabilityMeasure InfiniteGraph) = infiniteLaw L :=
    eq_infiniteLaw_of_map_restrictFin key
  exact congrArg (fun P : ProbabilityMeasure InfiniteGraph =>
    (P : Measure InfiniteGraph)) hP

end Graphon.ExchangeableGraphLaw

namespace Graphon

/-- **Infinite exchangeable graph laws**: probability laws on the infinite graph space
invariant under every relabeling of `ℕ`. -/
structure InfiniteExchangeableGraphLaw where
  /-- The law on the infinite graph space. -/
  law : ProbabilityMeasure InfiniteGraph
  /-- Invariance under every relabeling. -/
  exchangeable : ∀ σ : Equiv.Perm ℕ,
    (law : Measure InfiniteGraph).map (InfiniteGraph.relabel σ) = law

@[ext] theorem InfiniteExchangeableGraphLaw.ext {M N : InfiniteExchangeableGraphLaw}
    (h : M.law = N.law) : M = N := by
  cases M
  cases N
  simpa using h

namespace InfiniteExchangeableGraphLaw

/-- The finite marginals of an infinite exchangeable law form an exchangeable graph
law: consistency under an arbitrary injection follows by extending it to a permutation
of `ℕ` (`exists_perm_extend`) and applying exchangeability. -/
noncomputable def toExchangeableGraphLaw (M : InfiniteExchangeableGraphLaw) :
    Graphon.ExchangeableGraphLaw where
  law k :=
    haveI : IsProbabilityMeasure ((M.law : Measure InfiniteGraph).map (restrictFin k)) :=
      Measure.isProbabilityMeasure_map (measurable_restrictFin k).aemeasurable
    ((M.law : Measure InfiniteGraph).map (restrictFin k)).toPMF
  consistent := by
    intro k l e
    haveI : ∀ m, IsProbabilityMeasure
        ((M.law : Measure InfiniteGraph).map (restrictFin m)) := fun m =>
      Measure.isProbabilityMeasure_map (measurable_restrictFin m).aemeasurable
    apply PMF.toMeasure_injective
    obtain ⟨σ, hσ⟩ := exists_perm_extend (e.trans Fin.valEmbedding)
    rw [← PMF.toMeasure_map _ _ (SimpleGraph.measurable_comap ⇑e),
      Measure.toPMF_toMeasure, Measure.toPMF_toMeasure,
      Measure.map_map (SimpleGraph.measurable_comap ⇑e) (measurable_restrictFin l),
      show (fun H => H.comap ⇑e) ∘ restrictFin l = restrictFin k ∘ relabel σ from
        funext fun G => (restrictFin_relabel σ e hσ G).symm,
      ← Measure.map_map (measurable_restrictFin k) (measurable_relabel σ),
      M.exchangeable σ]

/-- The finite marginals of the infinite law, unfolded. -/
theorem toExchangeableGraphLaw_law (M : InfiniteExchangeableGraphLaw) (k : ℕ) :
    haveI : IsProbabilityMeasure ((M.law : Measure InfiniteGraph).map (restrictFin k)) :=
      Measure.isProbabilityMeasure_map (measurable_restrictFin k).aemeasurable
    (M.toExchangeableGraphLaw.law k).toMeasure =
      (M.law : Measure InfiniteGraph).map (restrictFin k) := by
  haveI : IsProbabilityMeasure ((M.law : Measure InfiniteGraph).map (restrictFin k)) :=
    Measure.isProbabilityMeasure_map (measurable_restrictFin k).aemeasurable
  exact Measure.toPMF_toMeasure _

end InfiniteExchangeableGraphLaw

open Graphon.ExchangeableGraphLaw in
/-- **The headline equivalence** (Aldous–Hoover layers 1–2): exchangeable graph laws
and infinite exchangeable graph laws are the same data, with finite marginals and the
infinite extension as inverse maps. -/
noncomputable def exchangeableGraphLawEquivInfinite :
    Graphon.ExchangeableGraphLaw ≃ Graphon.InfiniteExchangeableGraphLaw where
  toFun L := ⟨infiniteLaw L, infiniteLaw_map_relabel L⟩
  invFun M := M.toExchangeableGraphLaw
  left_inv L := by
    refine Graphon.ExchangeableGraphLaw.ext fun k => ?_
    apply PMF.toMeasure_injective
    rw [InfiniteExchangeableGraphLaw.toExchangeableGraphLaw_law]
    exact infiniteLaw_map_restrictFin L k
  right_inv M := by
    refine Graphon.InfiniteExchangeableGraphLaw.ext ?_
    exact (eq_infiniteLaw_of_map_restrictFin fun k =>
      (InfiniteExchangeableGraphLaw.toExchangeableGraphLaw_law M k).symm).symm

@[simp] theorem exchangeableGraphLawEquivInfinite_apply_law
    (L : Graphon.ExchangeableGraphLaw) :
    (exchangeableGraphLawEquivInfinite L).law = Graphon.ExchangeableGraphLaw.infiniteLaw L := rfl

end Graphon
