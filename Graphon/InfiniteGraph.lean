/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Topology.Constructions
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.SimpleGraph
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# The infinite graph space (Aldous–Hoover layer 1, brick A1)

Simple graphs on `ℕ` as a compact metrizable zero-dimensional Polish standard-Borel
space, with continuous/measurable finite restrictions:

* `InfiniteGraph` — a type synonym for `SimpleGraph ℕ` carrying the edge-coordinate
  (product) topology, via the coordinate equivalence
  `InfiniteGraph.coordEquiv : InfiniteGraph ≃ (InfiniteGraph.EdgeIndex → Bool)`
  (a simple graph on `ℕ` is exactly an arbitrary `Bool` assignment on off-diagonal
  unordered pairs);
* instances: `CompactSpace`, `T2Space`, `MetrizableSpace`, `PolishSpace`,
  `MeasurableSpace` (Borel), `BorelSpace`, `StandardBorelSpace`;
* `InfiniteGraph.restrictFin k` — restriction to the first `k` vertices (continuous,
  measurable);
* `InfiniteGraph.padFin` — embedding of a finite graph on `Fin k` (measurable), with
  `restrictFin_padFin`;
* `InfiniteGraph.ext_of_map_restrictFin` — **finite-restriction measure
  extensionality**: two finite Borel measures with equal pushforwards under every
  `restrictFin k` are equal (the restriction fibers form a generating π-system).

This is the infrastructure brick for the infinite exchangeable graph law (bricks
A2–A3): the specialized Kolmogorov extension is proved from compactness of
`ProbabilityMeasure InfiniteGraph` plus this extensionality, with no general
projective-limit machinery.
-/

open MeasureTheory

open scoped Classical

/-- Simple graphs on `ℕ`, as a type synonym carrying the edge-coordinate topology and
its Borel structure. -/
def InfiniteGraph : Type := SimpleGraph ℕ

namespace InfiniteGraph

/-- The edge-coordinate index: off-diagonal unordered pairs of naturals. -/
abbrev EdgeIndex : Type := {s : Sym2 ℕ // ¬ s.IsDiag}

/-- **The coordinate equivalence**: a simple graph on `ℕ` is exactly an arbitrary
`Bool` assignment on off-diagonal unordered pairs. -/
noncomputable def coordEquiv : InfiniteGraph ≃ (EdgeIndex → Bool) where
  toFun G e := if e.1 ∈ (G : SimpleGraph ℕ).edgeSet then true else false
  invFun f := (SimpleGraph.fromEdgeSet {s : Sym2 ℕ | ∃ h : ¬ s.IsDiag, f ⟨s, h⟩ = true} :
    SimpleGraph ℕ)
  left_inv G := by
    show SimpleGraph.fromEdgeSet _ = (G : SimpleGraph ℕ)
    conv_rhs => rw [← SimpleGraph.fromEdgeSet_edgeSet (G : SimpleGraph ℕ)]
    congr 1
    ext s
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h, hs⟩
      by_contra hmem
      simp only [if_neg hmem] at hs
      exact Bool.false_ne_true hs
    · intro hs
      exact ⟨fun hdiag => ((G : SimpleGraph ℕ).not_isDiag_of_mem_edgeSet hs) hdiag,
        by simp [hs]⟩
  right_inv f := by
    funext e
    simp only [SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, Set.mem_setOf_eq]
    by_cases hf : f e = true
    · rw [if_pos]
      · exact hf.symm
      · exact ⟨⟨e.2, hf⟩, fun hdiag => e.2 hdiag⟩
    · rw [if_neg]
      · exact (Bool.not_eq_true (f e)).mp hf |>.symm
      · rintro ⟨⟨h, hft⟩, -⟩
        exact hf ((Subtype.ext rfl : (⟨(e : Sym2 ℕ), h⟩ : EdgeIndex) = e) ▸ hft)

noncomputable instance : TopologicalSpace InfiniteGraph :=
  TopologicalSpace.induced coordEquiv inferInstance

/-- The coordinate equivalence as a homeomorphism onto the full Boolean product. -/
noncomputable def coordHomeomorph : InfiniteGraph ≃ₜ (EdgeIndex → Bool) :=
  coordEquiv.toHomeomorphOfIsInducing ⟨rfl⟩

instance : CompactSpace InfiniteGraph := coordHomeomorph.symm.compactSpace

instance : T2Space InfiniteGraph := coordHomeomorph.symm.t2Space

instance : SecondCountableTopology InfiniteGraph :=
  coordHomeomorph.isEmbedding.secondCountableTopology

instance : TopologicalSpace.MetrizableSpace InfiniteGraph :=
  coordHomeomorph.isEmbedding.metrizableSpace

instance : PolishSpace (EdgeIndex → Bool) := by
  haveI : TopologicalSpace.IsCompletelyMetrizableSpace (EdgeIndex → Bool) := inferInstance
  infer_instance

instance : PolishSpace InfiniteGraph := coordEquiv.polishSpace_induced

noncomputable instance : MeasurableSpace InfiniteGraph := borel InfiniteGraph

instance : BorelSpace InfiniteGraph := ⟨rfl⟩

instance : StandardBorelSpace InfiniteGraph := inferInstance

instance : Nonempty InfiniteGraph := ⟨(⊥ : SimpleGraph ℕ)⟩

/-! ### Finite restriction and padding -/

/-- **Restriction to the first `k` vertices**. -/
def restrictFin (k : ℕ) (G : InfiniteGraph) : SimpleGraph (Fin k) :=
  (G : SimpleGraph ℕ).comap ((↑) : Fin k → ℕ)

/-- **Padding**: a finite graph on `Fin k`, viewed as an infinite graph with no edges
beyond the first `k` vertices. -/
def padFin {k : ℕ} (H : SimpleGraph (Fin k)) : InfiniteGraph :=
  (H.map Fin.valEmbedding : SimpleGraph ℕ)

@[simp] theorem restrictFin_padFin {k : ℕ} (H : SimpleGraph (Fin k)) :
    restrictFin k (padFin H) = H :=
  SimpleGraph.comap_map_eq Fin.valEmbedding H

/-- Restrictions are consistent under the initial-segment inclusions. -/
theorem restrictFin_comap {k l : ℕ} (h : k ≤ l) (G : InfiniteGraph) :
    (restrictFin l G).comap (Fin.castLEEmb h) = restrictFin k G := by
  ext a b
  simp [restrictFin, SimpleGraph.comap]

/-- Finite graph types carry the discrete topology (for the continuity statements about
finite restrictions). -/
instance (k : ℕ) : TopologicalSpace (SimpleGraph (Fin k)) := ⊥

instance (k : ℕ) : DiscreteTopology (SimpleGraph (Fin k)) := ⟨rfl⟩

/-- Singletons of finite graphs are measurable (Mathlib supplies the measurable space
in `Mathlib.MeasureTheory.Constructions.SimpleGraph` but not this instance; also
provided for countable `V` in `Graphon/SamplingLaw.lean` — this is the same
`Prop`-valued fact, safe to duplicate). -/
instance (k : ℕ) : MeasurableSingletonClass (SimpleGraph (Fin k)) where
  measurableSet_singleton G := by
    have h : MeasurableSet ({G.edgeSet} : Set (Set (Sym2 (Fin k)))) :=
      MeasurableSet.singleton G.edgeSet
    have hp := h.preimage SimpleGraph.measurable_edgeSet
    convert hp using 1
    ext H
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact SimpleGraph.edgeSet_injective.eq_iff.symm

/-- Every open set of the (discrete) finite graph type is measurable. -/
instance (k : ℕ) : OpensMeasurableSpace (SimpleGraph (Fin k)) :=
  ⟨MeasurableSpace.generateFrom_le fun s _ => (Set.to_countable s).measurableSet⟩

/-- The coordinate evaluation, unfolded. -/
@[simp] theorem coordEquiv_apply (G : InfiniteGraph) (e : EdgeIndex) :
    coordEquiv G e =
      if (e : Sym2 ℕ) ∈ (G : SimpleGraph ℕ).edgeSet then true else false := rfl

/-- Boolean indicators agree exactly when the propositions are equivalent. -/
private theorem ite_bool_eq_iff {P Q : Prop} [Decidable P] [Decidable Q] :
    ((if P then true else false) = (if Q then true else false)) ↔ (P ↔ Q) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-- The restriction maps are continuous (the target is finite discrete; each fiber is a
finite-coordinate cylinder). -/
theorem continuous_restrictFin (k : ℕ) : Continuous (restrictFin k) := by
  classical
  rw [continuous_discrete_rng]
  intro H
  have hopen : ∀ (e : EdgeIndex) (b : Bool),
      IsOpen {G : InfiniteGraph | coordEquiv G e = b} := fun e b =>
    (isOpen_discrete {b}).preimage ((continuous_apply e).comp coordHomeomorph.continuous)
  have hfiber : restrictFin k ⁻¹' {H} =
      ⋂ p : {p : Fin k × Fin k // p.1 ≠ p.2},
        {G : InfiniteGraph | coordEquiv G
          ⟨s(((p : Fin k × Fin k).1 : ℕ), ((p : Fin k × Fin k).2 : ℕ)),
            fun hdiag => p.2 (Fin.val_injective (Sym2.mk_isDiag_iff.mp hdiag))⟩ =
          if H.Adj (p : Fin k × Fin k).1 (p : Fin k × Fin k).2 then true else false} := by
    ext G
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq,
      coordEquiv_apply, SimpleGraph.mem_edgeSet, ite_bool_eq_iff]
    constructor
    · rintro rfl p
      rfl
    · intro hall
      ext a b
      by_cases hab : a = b
      · subst hab
        simp
      · exact hall ⟨(a, b), hab⟩
  rw [hfiber]
  exact isOpen_iInter_of_finite fun p => hopen _ _

theorem measurable_restrictFin (k : ℕ) : Measurable (restrictFin k) :=
  (continuous_restrictFin k).measurable

theorem measurable_padFin {k : ℕ} :
    Measurable (padFin : SimpleGraph (Fin k) → InfiniteGraph) :=
  measurable_of_countable _

/-! ### Finite-restriction measure extensionality -/

/-- **The finite-restriction cylinders**: preimages of arbitrary finite-level sets. -/
def cylinders : Set (Set InfiniteGraph) :=
  ⋃ k : ℕ, Set.range fun S : Set (SimpleGraph (Fin k)) => restrictFin k ⁻¹' S

/-- Lower-level cylinders are higher-level cylinders. -/
theorem restrictFin_preimage_comap {k l : ℕ} (h : k ≤ l) (S : Set (SimpleGraph (Fin k))) :
    restrictFin k ⁻¹' S =
      restrictFin l ⁻¹' ((fun H => H.comap (Fin.castLEEmb h)) ⁻¹' S) := by
  ext G
  simp only [Set.mem_preimage]
  rw [restrictFin_comap h G]

/-- The cylinders form a π-system (align two levels at their maximum). -/
theorem isPiSystem_cylinders : IsPiSystem cylinders := by
  rintro s hs t ht -
  simp only [cylinders, Set.mem_iUnion, Set.mem_range] at hs ht ⊢
  obtain ⟨k, S, rfl⟩ := hs
  obtain ⟨l, T, rfl⟩ := ht
  rcases le_total k l with hkl | hlk
  · exact ⟨l, (fun H => H.comap (Fin.castLEEmb hkl)) ⁻¹' S ∩ T, by
      rw [Set.preimage_inter, ← restrictFin_preimage_comap hkl]⟩
  · exact ⟨k, S ∩ (fun H => H.comap (Fin.castLEEmb hlk)) ⁻¹' T, by
      rw [Set.preimage_inter, ← restrictFin_preimage_comap hlk]⟩

/-- The restriction maps are measurable for the σ-algebra generated by the cylinders
(by construction). -/
private theorem measurable_restrictFin_generateFrom (k : ℕ) :
    @Measurable InfiniteGraph (SimpleGraph (Fin k))
      (MeasurableSpace.generateFrom cylinders) _ (restrictFin k) := fun S _ =>
  MeasurableSpace.measurableSet_generateFrom
    (Set.mem_iUnion.mpr ⟨k, Set.mem_range.mpr ⟨S, rfl⟩⟩)

/-- Each edge coordinate factors through a finite restriction, so the coordinate map is
measurable for the cylinder σ-algebra. -/
private theorem measurable_coordEquiv_generateFrom :
    @Measurable InfiniteGraph (EdgeIndex → Bool)
      (MeasurableSpace.generateFrom cylinders) _ coordEquiv := by
  classical
  letI m := MeasurableSpace.generateFrom cylinders
  rw [measurable_pi_iff]
  intro e
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, (e : Sym2 ℕ) = s(a, b) := by
    obtain ⟨⟨a, b⟩, h⟩ := Quot.exists_rep (e : Sym2 ℕ)
    exact ⟨a, b, h.symm⟩
  have ha : a < max a b + 1 := lt_of_le_of_lt (le_max_left a b) (Nat.lt_succ_self _)
  have hb : b < max a b + 1 := lt_of_le_of_lt (le_max_right a b) (Nat.lt_succ_self _)
  have hfactor : (fun G : InfiniteGraph => coordEquiv G e) = fun G =>
      if (restrictFin (max a b + 1) G).Adj ⟨a, ha⟩ ⟨b, hb⟩ then true else false := by
    funext G
    rw [coordEquiv_apply, hab]
    rfl
  rw [hfactor]
  exact (measurable_of_countable (fun H : SimpleGraph (Fin (max a b + 1)) =>
    if H.Adj ⟨a, ha⟩ ⟨b, hb⟩ then true else false)).comp
    (measurable_restrictFin_generateFrom (max a b + 1))

/-- **The cylinders generate the Borel σ-algebra** of the infinite graph space. -/
theorem generateFrom_cylinders_eq :
    MeasurableSpace.generateFrom cylinders =
      (inferInstance : MeasurableSpace InfiniteGraph) := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) ?_
  · intro s hs
    simp only [cylinders, Set.mem_iUnion, Set.mem_range] at hs
    obtain ⟨k, S, rfl⟩ := hs
    exact measurable_restrictFin k (Set.to_countable S).measurableSet
  · show (borel InfiniteGraph) ≤ _
    calc (borel InfiniteGraph)
        = (borel (EdgeIndex → Bool)).comap coordEquiv := borel_comap
      _ = (inferInstance : MeasurableSpace (EdgeIndex → Bool)).comap coordEquiv := by
          rw [← BorelSpace.measurable_eq (α := EdgeIndex → Bool)]
      _ ≤ MeasurableSpace.generateFrom cylinders :=
          measurable_iff_comap_le.mp measurable_coordEquiv_generateFrom

/-- **Finite-restriction measure extensionality**: two finite Borel measures on the
infinite graph space with equal pushforwards under every finite restriction are
equal. -/
theorem ext_of_map_restrictFin {μ ν : Measure InfiniteGraph} [IsFiniteMeasure μ]
    (h : ∀ k, μ.map (restrictFin k) = ν.map (restrictFin k)) : μ = ν := by
  refine MeasureTheory.ext_of_generate_finite cylinders generateFrom_cylinders_eq.symm
    isPiSystem_cylinders ?_ ?_
  · intro s hs
    simp only [cylinders, Set.mem_iUnion, Set.mem_range] at hs
    obtain ⟨k, S, rfl⟩ := hs
    have hS : MeasurableSet S := (Set.to_countable S).measurableSet
    rw [← Measure.map_apply (measurable_restrictFin k) hS,
      ← Measure.map_apply (measurable_restrictFin k) hS, h k]
  · have h0 := congrArg (fun m : Measure (SimpleGraph (Fin 0)) => m Set.univ) (h 0)
    simpa [Measure.map_apply (measurable_restrictFin 0) MeasurableSet.univ] using h0

/-- Probability-measure form of the finite-restriction extensionality. -/
theorem probabilityMeasure_ext_of_map_restrictFin
    {P Q : ProbabilityMeasure InfiniteGraph}
    (h : ∀ k, (P : Measure InfiniteGraph).map (restrictFin k) =
      (Q : Measure InfiniteGraph).map (restrictFin k)) : P = Q :=
  ProbabilityMeasure.toMeasure_injective (ext_of_map_restrictFin h)

end InfiniteGraph
