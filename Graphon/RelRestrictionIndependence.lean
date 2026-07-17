/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRestrictionBlocks
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.ZeroOne

/-!
# Restriction independence and vertex-tail triviality (AHK umbrella, R3b / #106)

The generic equivalence between dissociation and restriction independence, and the implication
to vertex-tail triviality, for exchangeable relational laws:

* `InfiniteRelExchangeableLaw.RestrictionIndependent` — for every block size the initial and
  after-block σ-algebras are independent;
* `InfiniteRelExchangeableLaw.VertexTailTrivial` — every vertex-tail event has law-measure
  `0` or `1`;
* `isDissociated_iff_restrictionIndependent` — **dissociation ↔ restriction independence**:
  independence of the comap σ-algebras of the two block maps *is* the block-pair map
  factorization (`IndepFun_iff_Indep` + `indepFun_iff_map_prod_eq_prod_map_map`), and the
  finite tail windows exhaust the after-block σ-algebra (R3a);
* `RestrictionIndependent.vertexTailTrivial` — a vertex-tail event is independent of every
  initial σ-algebra, hence (the initial σ-algebras generating, R3a) of itself.

**The converse `VertexTailTrivial → IsDissociated` is deliberately not here**: it is deferred
to a representation-free **downward-martingale follow-up** — an L¹ Lévy *downward* lemma
(conditional expectations along a decreasing filtration; Mathlib has only the upward theorem),
then: condition an initial finite-event indicator on successively later tail algebras, tail
triviality makes the limit constant, exchangeability moves the second block arbitrarily far
out, and L¹ convergence forces the exact block factorization. (The undirected proof instead
rides the graphon mixture representation; the generic theory keeps the five-way
characterization representation-free, with R5's Dirac-mixing as a later corollary.)
-/

open MeasureTheory ProbabilityTheory RelSignature

namespace RelSignature

variable {S : RelSignature}

/-! ### Window monotonicity -/

/-- The finite tail windows are monotone in the window size. -/
theorem RelStructure.tailWindowAlgebra_mono (k : S.Srt → ℕ) {l l' : S.Srt → ℕ}
    (h : ∀ s, l s ≤ l' s) :
    RelStructure.tailWindowAlgebra (S := S) k l ≤ RelStructure.tailWindowAlgebra (S := S) k l' := by
  refine measurable_iff_comap_le.mp ?_
  rw [show RelStructure.restrict (S := S) (shiftEmb k l) =
      RelStructure.restrictLE h ∘ RelStructure.restrict (shiftEmb k l') from rfl]
  exact (RelSignature.measurable_restrictLE h).comp
    (@Measurable.of_comap_le _ _ (RelStructure.tailWindowAlgebra k l') _
      (RelStructure.restrict (shiftEmb k l')) le_rfl)

theorem RelStructure.tailWindowAlgebra_le_tailAlgebra (k l : S.Srt → ℕ) :
    RelStructure.tailWindowAlgebra (S := S) k l ≤ RelStructure.tailAlgebra (S := S) k := by
  rw [← RelStructure.iSup_tailWindowAlgebra_eq k]
  exact le_iSup (RelStructure.tailWindowAlgebra (S := S) k) l

/-! ### The two properties -/

/-- **Restriction independence**: for every block size, the structure on the initial block is
independent of the structure on the remaining vertices. -/
def InfiniteRelExchangeableLaw.RestrictionIndependent (M : InfiniteRelExchangeableLaw S) :
    Prop :=
  ∀ k : S.Srt → ℕ, Indep (RelStructure.initialAlgebra k) (RelStructure.tailAlgebra k)
    (M.law : Measure (RelStructure S (Vinfinite S)))

/-- **Vertex-tail triviality**: every vertex-tail event has law-measure `0` or `1`. -/
def InfiniteRelExchangeableLaw.VertexTailTrivial (M : InfiniteRelExchangeableLaw S) : Prop :=
  ∀ s, MeasurableSet[RelStructure.vertexTailAlgebra] s →
    (M.law : Measure (RelStructure S (Vinfinite S))) s = 0 ∨
      (M.law : Measure (RelStructure S (Vinfinite S))) s = 1

/-! ### Dissociation ↔ restriction independence -/

/-- **Finite-window independence from dissociation**: comap-σ-algebra independence of the
initial block and a tail window is exactly the block-pair map factorization. -/
theorem InfiniteRelExchangeableLaw.IsDissociated.indep_initial_tailWindow
    {M : InfiniteRelExchangeableLaw S} (hM : M.IsDissociated) (k l : S.Srt → ℕ) :
    Indep (RelStructure.initialAlgebra k) (RelStructure.tailWindowAlgebra k l)
      (M.law : Measure (RelStructure S (Vinfinite S))) := by
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  have hwinmeas : Measurable (RelStructure.restrict (S := S) (shiftEmb k l)) := by
    rw [restrict_shiftEmb_eq]
    exact (RelSignature.measurable_restrictFin l).comp (measurable_drop k)
  rw [RelStructure.initialAlgebra, RelStructure.tailWindowAlgebra, ← IndepFun_iff_Indep,
    indepFun_iff_map_prod_eq_prod_map_map
      (RelSignature.measurable_restrictFin k).aemeasurable hwinmeas.aemeasurable,
    M.law_map_restrict (shiftEmb k l)]
  exact hM k l

/-- **Dissociation implies restriction independence**: the finite windows exhaust the
after-block σ-algebra. -/
theorem InfiniteRelExchangeableLaw.IsDissociated.restrictionIndependent
    {M : InfiniteRelExchangeableLaw S} (hM : M.IsDissociated) :
    M.RestrictionIndependent := by
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  intro k
  have hsup := indep_iSup_of_directed_le
    (fun l => (hM.indep_initial_tailWindow k l).symm)
    (fun l => (RelStructure.tailWindowAlgebra_le_tailAlgebra k l).trans
      (RelStructure.tailAlgebra_le k))
    (RelStructure.initialAlgebra_le k)
    (fun l l' => ⟨fun s => max (l s) (l' s),
      RelStructure.tailWindowAlgebra_mono k fun s => le_max_left _ _,
      RelStructure.tailWindowAlgebra_mono k fun s => le_max_right _ _⟩)
  rw [RelStructure.iSup_tailWindowAlgebra_eq] at hsup
  exact hsup.symm

/-- **Restriction independence implies dissociation**: restrict the independence to a window
and read it as the block-pair map factorization. -/
theorem InfiniteRelExchangeableLaw.RestrictionIndependent.isDissociated
    {M : InfiniteRelExchangeableLaw S} (hM : M.RestrictionIndependent) :
    M.IsDissociated := by
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  intro k l
  have hwinmeas : Measurable (RelStructure.restrict (S := S) (shiftEmb k l)) := by
    rw [restrict_shiftEmb_eq]
    exact (RelSignature.measurable_restrictFin l).comp (measurable_drop k)
  have hwin : Indep (RelStructure.initialAlgebra k) (RelStructure.tailWindowAlgebra k l)
      (M.law : Measure (RelStructure S (Vinfinite S))) :=
    indep_of_indep_of_le_right (hM k) (RelStructure.tailWindowAlgebra_le_tailAlgebra k l)
  rw [RelStructure.initialAlgebra, RelStructure.tailWindowAlgebra, ← IndepFun_iff_Indep,
    indepFun_iff_map_prod_eq_prod_map_map
      (RelSignature.measurable_restrictFin k).aemeasurable hwinmeas.aemeasurable,
    M.law_map_restrict (shiftEmb k l)] at hwin
  exact hwin

/-- **Dissociation ↔ restriction independence** (R3b). -/
theorem isDissociated_iff_restrictionIndependent (M : InfiniteRelExchangeableLaw S) :
    M.IsDissociated ↔ M.RestrictionIndependent :=
  ⟨fun h => h.restrictionIndependent, fun h => h.isDissociated⟩

/-! ### Restriction independence implies vertex-tail triviality -/

/-- **Restriction independence implies vertex-tail triviality**: a vertex-tail event is
independent of every initial σ-algebra, hence — the initial σ-algebras generating the Borel
σ-algebra — independent of itself. -/
theorem InfiniteRelExchangeableLaw.RestrictionIndependent.vertexTailTrivial
    {M : InfiniteRelExchangeableLaw S} (hM : M.RestrictionIndependent) :
    M.VertexTailTrivial := by
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  intro s hs
  have hindep : ∀ k : S.Srt → ℕ, Indep (RelStructure.initialAlgebra k)
      RelStructure.vertexTailAlgebra (M.law : Measure (RelStructure S (Vinfinite S))) :=
    fun k => indep_of_indep_of_le_right (hM k)
      (RelStructure.vertexTailAlgebra_le_tailAlgebra k)
  have hsup : Indep (⨆ k : S.Srt → ℕ, RelStructure.initialAlgebra k)
      RelStructure.vertexTailAlgebra (M.law : Measure (RelStructure S (Vinfinite S))) := by
    refine indep_iSup_of_directed_le hindep RelStructure.initialAlgebra_le
      RelStructure.vertexTailAlgebra_le ?_
    intro k k'
    exact ⟨fun s => max (k s) (k' s),
      RelStructure.initialAlgebra_mono fun s => le_max_left _ _,
      RelStructure.initialAlgebra_mono fun s => le_max_right _ _⟩
  rw [RelStructure.iSup_initialAlgebra_eq] at hsup
  have hself : Indep RelStructure.vertexTailAlgebra RelStructure.vertexTailAlgebra
      (M.law : Measure (RelStructure S (Vinfinite S))) :=
    indep_of_indep_of_le_left hsup RelStructure.vertexTailAlgebra_le
  exact measure_eq_zero_or_one_of_indep_self hself hs

/-- **Dissociation implies vertex-tail triviality** (R3b chain). -/
theorem InfiniteRelExchangeableLaw.IsDissociated.vertexTailTrivial
    {M : InfiniteRelExchangeableLaw S} (hM : M.IsDissociated) :
    M.VertexTailTrivial :=
  hM.restrictionIndependent.vertexTailTrivial

end RelSignature
