/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.RestrictionIndependence
import Graphon.HomDensityAlgebra
import Mathlib.Probability.Independence.Basic

/-!
# Dissociation implies restriction independence (Diaconis–Janson Theorem 5.5, issue #91)

The reverse arc completing the five-way extremality theorem: a dissociated law is
restriction independent. The finite content is a two-block factorization obtained from
the upper-mass dissociation criterion by a two-variable Möbius inversion; it is then
lifted from finite tail windows to the whole tail σ-algebra.
-/

open MeasureTheory Set

open scoped Classical

namespace Graphon

/-- The two-variable upper transform. -/
noncomputable def upperSum₂ {k m : ℕ}
    (p : SimpleGraph (Fin k) → SimpleGraph (Fin m) → ℝ)
    (F : SimpleGraph (Fin k)) (H : SimpleGraph (Fin m)) : ℝ :=
  upperSum (fun F' => upperSum (fun H' => p F' H') H) F

/-- The two-variable upper transform is injective. -/
theorem upperSum₂_injective {k m : ℕ}
    {p q : SimpleGraph (Fin k) → SimpleGraph (Fin m) → ℝ}
    (h : ∀ F H, upperSum₂ p F H = upperSum₂ q F H) : p = q := by
  have h1 : ∀ H F', upperSum (fun H' => p F' H') H = upperSum (fun H' => q F' H') H := by
    intro H
    have hF : (fun F' => upperSum (fun H' => p F' H') H)
        = (fun F' => upperSum (fun H' => q F' H') H) :=
      upperSum_injective (fun F => h F H)
    exact congrFun hF
  funext F'
  exact upperSum_injective (fun H => h1 H F')

end Graphon

namespace InfiniteGraph

/-- The initial-block embedding `Fin k ↪ Fin (k+m)` (the first `k` vertices), matching
`finSumFinEquiv` on `Sum.inl`. -/
def blockInit (k m : ℕ) : Fin k ↪ Fin (k + m) :=
  Function.Embedding.trans Function.Embedding.inl finSumFinEquiv.toEmbedding

/-- The tail-block embedding `Fin m ↪ Fin (k+m)` (the vertices `k, …, k+m-1`), matching
`finSumFinEquiv` on `Sum.inr`. -/
def blockTail (k m : ℕ) : Fin m ↪ Fin (k + m) :=
  Function.Embedding.trans Function.Embedding.inr finSumFinEquiv.toEmbedding

@[simp] theorem blockInit_apply (k m : ℕ) (a : Fin k) :
    (blockInit k m a : ℕ) = a := by
  rw [blockInit, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  show (finSumFinEquiv (Sum.inl a) : Fin (k + m)).val = a.val
  rw [finSumFinEquiv_apply_left, Fin.val_castAdd]

@[simp] theorem blockTail_apply (k m : ℕ) (b : Fin m) :
    (blockTail k m b : ℕ) = k + b := by
  rw [blockTail, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  show (finSumFinEquiv (Sum.inr b) : Fin (k + m)).val = k + b.val
  rw [finSumFinEquiv_apply_right, Fin.val_natAdd]

/-- The initial restriction is the initial-block comap of the `(k+m)`-restriction. -/
theorem restrictFin_eq_comap_blockInit (k m : ℕ) (G : InfiniteGraph) :
    restrictFin k G = (restrictFin (k + m) G).comap (blockInit k m) := by
  ext a b
  simp only [restrictFin, SimpleGraph.comap_adj]
  rw [blockInit_apply, blockInit_apply]

/-- The tail-window restriction is the tail-block comap of the `(k+m)`-restriction. -/
theorem restrictFin_drop_eq_comap_blockTail (k m : ℕ) (G : InfiniteGraph) :
    restrictFin m (drop k G) = (restrictFin (k + m) G).comap (blockTail k m) := by
  ext a b
  simp only [restrictFin, SimpleGraph.comap_adj, drop_adj]
  rw [blockTail_apply, blockTail_apply]
  constructor
  · intro h; rwa [Nat.add_comm k _, Nat.add_comm k _]
  · intro h; rwa [Nat.add_comm _ k, Nat.add_comm _ k]

/-- **The disjoint-union order characterization**: a graph on `Fin (k+m)` contains the
mapped disjoint union `(F ⊕g H).map finSumFinEquiv` iff its initial block contains `F`
and its tail block contains `H` (cross-block edges unrestricted). -/
theorem sum_map_le_iff {k m : ℕ} (F : SimpleGraph (Fin k)) (H : SimpleGraph (Fin m))
    (K : SimpleGraph (Fin (k + m))) :
    (F ⊕g H).map finSumFinEquiv.toEmbedding ≤ K ↔
      F ≤ K.comap (blockInit k m) ∧ H ≤ K.comap (blockTail k m) := by
  rw [SimpleGraph.map_le_iff_le_comap]
  constructor
  · intro h
    refine ⟨fun {a b} hab => ?_, fun {a b} hab => ?_⟩
    · have h2 := h ((SimpleGraph.sum_adj_inl).mpr hab)
      rw [SimpleGraph.comap_adj] at h2 ⊢
      exact h2
    · have h2 := h ((SimpleGraph.sum_adj_inr).mpr hab)
      rw [SimpleGraph.comap_adj] at h2 ⊢
      exact h2
  · rintro ⟨hF, hH⟩ u v huv
    obtain (a | a) := u <;> obtain (b | b) := v
    · have := hF ((SimpleGraph.sum_adj_inl).mp huv)
      rw [SimpleGraph.comap_adj] at this ⊢
      exact this
    · exact absurd huv (by simp [SimpleGraph.sum])
    · exact absurd huv (by simp [SimpleGraph.sum])
    · have := hH ((SimpleGraph.sum_adj_inr).mp huv)
      rw [SimpleGraph.comap_adj] at this ⊢
      exact this

end InfiniteGraph

namespace Graphon

/-- Constants factor out of the upper transform (left). -/
theorem upperSum_const_mul {k : ℕ} (c : ℝ) (p : SimpleGraph (Fin k) → ℝ)
    (F : SimpleGraph (Fin k)) :
    upperSum (fun G => c * p G) F = c * upperSum p F := by
  simp only [upperSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun G _ => ?_
  split <;> simp

/-- Constants factor out of the upper transform (right). -/
theorem upperSum_mul_const {k : ℕ} (c : ℝ) (p : SimpleGraph (Fin k) → ℝ)
    (F : SimpleGraph (Fin k)) :
    upperSum (fun G => p G * c) F = upperSum p F * c := by
  simp only [upperSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun G _ => ?_
  split <;> simp

/-- The real-valued joint mass of the two exact block events under the `(k+m)`-vertex
law. -/
noncomputable def blockJoint (L : Graphon.ExchangeableGraphLaw) (k m : ℕ)
    (F : SimpleGraph (Fin k)) (H : SimpleGraph (Fin m)) : ℝ :=
  ∑ K : SimpleGraph (Fin (k + m)),
    if K.comap (InfiniteGraph.blockInit k m) = F ∧
        K.comap (InfiniteGraph.blockTail k m) = H
      then (L.law (k + m) K).toReal else 0

/-- **Joint side** of the two-block factorization: the double upper transform of the
block joint mass is the upper mass of the mapped disjoint union (cross-block edges
unrestricted). -/
theorem upperSum₂_blockJoint (L : Graphon.ExchangeableGraphLaw) (k m : ℕ)
    (F₀ : SimpleGraph (Fin k)) (H₀ : SimpleGraph (Fin m)) :
    upperSum₂ (blockJoint L k m) F₀ H₀ =
      L.upperMass ((F₀ ⊕g H₀).map finSumFinEquiv.toEmbedding) := by
  classical
  -- expand the double upper transform to a triple sum, then collapse to a single sum
  -- over `K`
  have hLHS : upperSum₂ (blockJoint L k m) F₀ H₀ =
      ∑ K : SimpleGraph (Fin (k + m)),
        if F₀ ≤ K.comap (InfiniteGraph.blockInit k m) ∧
            H₀ ≤ K.comap (InfiniteGraph.blockTail k m)
          then (L.law (k + m) K).toReal else 0 := by
    have hpull : ∀ {ι : Type} [Fintype ι] (c : Prop) [Decidable c] (f : ι → ℝ),
        (if c then ∑ x, f x else 0) = ∑ x, if c then f x else 0 := by
      intro ι _ c _ f; split_ifs with h <;> simp
    simp only [upperSum₂, upperSum, blockJoint, hpull]
    -- now a triple sum ∑_F ∑_H ∑_K; reorder to ∑_K ∑_F ∑_H and collapse
    rw [Finset.sum_congr rfl (fun F _ => Finset.sum_comm), Finset.sum_comm]
    refine Finset.sum_congr rfl fun K _ => ?_
    -- inner: ∑_F ∑_H (if F₀≤F then if H₀≤H then if K.cInit=F ∧ K.cTail=H then Lr else 0) collapses
    rw [Finset.sum_eq_single (K.comap (InfiniteGraph.blockInit k m))]
    · rw [Finset.sum_eq_single (K.comap (InfiniteGraph.blockTail k m))]
      · simp only [and_self, ite_true, true_and]
        by_cases hF : F₀ ≤ K.comap (InfiniteGraph.blockInit k m) <;>
          by_cases hH : H₀ ≤ K.comap (InfiniteGraph.blockTail k m) <;>
          simp [hF, hH]
      · intro H hH hHne
        simp only [and_iff_right rfl]
        by_cases hF : F₀ ≤ K.comap (InfiniteGraph.blockInit k m) <;>
          by_cases hH0 : H₀ ≤ H <;> simp [hF, hH0, hHne.symm, Ne.symm hHne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro F hF hFne
      apply Finset.sum_eq_zero
      intro H _
      by_cases hF0 : F₀ ≤ F <;> by_cases hH0 : H₀ ≤ H <;>
        simp [hF0, hH0, hFne, Ne.symm hFne]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hLHS]
  simp only [Graphon.ExchangeableGraphLaw.upperMass, upperSum]
  exact Finset.sum_congr rfl fun K _ =>
    if_congr (InfiniteGraph.sum_map_le_iff F₀ H₀ K).symm rfl rfl

/-- **Product side** of the two-block factorization: the upper transform of the product
of the two marginal masses is the product of their upper masses. -/
theorem upperSum₂_prod (L : Graphon.ExchangeableGraphLaw) (k m : ℕ)
    (F₀ : SimpleGraph (Fin k)) (H₀ : SimpleGraph (Fin m)) :
    upperSum₂ (fun F H => (L.law k F).toReal * (L.law m H).toReal) F₀ H₀ =
      L.upperMass F₀ * L.upperMass H₀ := by
  rw [upperSum₂]
  simp only [upperSum_const_mul]
  rw [upperSum_mul_const]
  rfl

/-- **The exact two-block factorization** (the combinatorial heart of the reverse arc):
for a dissociated law, the joint mass of the two exact block events factors as the
product of the two marginal masses. -/
theorem blockJoint_eq_prod {L : Graphon.ExchangeableGraphLaw} (hL : L.IsDissociated)
    (k m : ℕ) (F : SimpleGraph (Fin k)) (H : SimpleGraph (Fin m)) :
    blockJoint L k m F H = (L.law k F).toReal * (L.law m H).toReal := by
  have hpq : blockJoint L k m =
      fun F H => (L.law k F).toReal * (L.law m H).toReal := by
    refine upperSum₂_injective fun F₀ H₀ => ?_
    rw [upperSum₂_blockJoint, upperSum₂_prod]
    exact hL F₀ H₀
  exact congrFun (congrFun hpq F) H

end Graphon

namespace InfiniteGraph

/-- The tail-window σ-algebra: events depending only on the graph induced on the
vertices `k, …, k+m-1`. -/
@[reducible] noncomputable def tailWindowAlgebra (k m : ℕ) : MeasurableSpace InfiniteGraph :=
  MeasurableSpace.comap (fun G => restrictFin m (drop k G)) inferInstance

theorem tailWindowAlgebra_eq_comap (k m : ℕ) :
    tailWindowAlgebra k m = (initialAlgebra m).comap (drop k) := by
  rw [tailWindowAlgebra, initialAlgebra, MeasurableSpace.comap_comp]
  rfl

theorem tailWindowAlgebra_le (k m : ℕ) :
    tailWindowAlgebra k m ≤ (inferInstance : MeasurableSpace InfiniteGraph) :=
  measurable_iff_comap_le.mp ((measurable_restrictFin m).comp (measurable_drop k))

/-- The tail-window σ-algebras exhaust the tail σ-algebra at level `k`. -/
theorem iSup_tailWindowAlgebra (k : ℕ) :
    (⨆ m, tailWindowAlgebra k m) = tailAlgebra k := by
  simp only [tailWindowAlgebra_eq_comap]
  rw [← MeasurableSpace.comap_iSup, iSup_initialAlgebra_eq]

theorem tailWindowAlgebra_mono (k : ℕ) : Monotone (tailWindowAlgebra k) := by
  intro m₁ m₂ h
  simp only [tailWindowAlgebra_eq_comap]
  exact MeasurableSpace.comap_mono (initialAlgebra_mono h)

end InfiniteGraph

namespace Graphon.InfiniteExchangeableGraphLaw

open ProbabilityTheory InfiniteGraph

/-- The block event on `SimpleGraph (Fin (k+m))`. -/
private def blockSet (k m : ℕ) (F : SimpleGraph (Fin k)) (H : SimpleGraph (Fin m)) :
    Set (SimpleGraph (Fin (k + m))) :=
  {K | K.comap (blockInit k m) = F ∧ K.comap (blockTail k m) = H}

/-- The `(k+m)`-law mass of the block event is the block joint mass (in `ℝ≥0∞`). -/
private theorem toMeasure_blockSet_toReal (L : Graphon.ExchangeableGraphLaw) (k m : ℕ)
    (F : SimpleGraph (Fin k)) (H : SimpleGraph (Fin m)) :
    ((L.law (k + m)).toMeasure (blockSet k m F H)).toReal = Graphon.blockJoint L k m F H := by
  classical
  rw [(L.law (k + m)).toMeasure_apply (Set.to_countable (blockSet k m F H)).measurableSet, tsum_fintype,
    ENNReal.toReal_sum fun K _ => by
      by_cases h : K ∈ blockSet k m F H <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, h, PMF.apply_ne_top]]
  simp only [Graphon.blockJoint, blockSet, Set.indicator, Set.mem_setOf_eq]
  refine Finset.sum_congr rfl fun K _ => ?_
  by_cases h : K.comap (blockInit k m) = F ∧ K.comap (blockTail k m) = H <;> simp [h]

/-- **Finite-window restriction independence** (from the exact block factorization): for
a dissociated law, the initial `k`-vertex σ-algebra is independent of the tail-window
σ-algebra. -/
theorem indep_initial_tailWindow (M : Graphon.InfiniteExchangeableGraphLaw)
    (hM : M.IsDissociated) (k m : ℕ) :
    Indep (InfiniteGraph.initialAlgebra k) (InfiniteGraph.tailWindowAlgebra k m)
      (M.law : Measure InfiniteGraph) := by
  classical
  haveI : IsProbabilityMeasure (M.law : Measure InfiniteGraph) := M.law.2
  set L := M.toExchangeableGraphLaw with hLdef
  haveI hpm : ∀ j, IsProbabilityMeasure
      ((M.law : Measure InfiniteGraph).map (restrictFin j)) := fun j =>
    Measure.isProbabilityMeasure_map (measurable_restrictFin j).aemeasurable
  rw [InfiniteGraph.initialAlgebra, InfiniteGraph.tailWindowAlgebra, ← IndepFun_iff_Indep,
    indepFun_iff_map_prod_eq_prod_map_map (measurable_restrictFin k).aemeasurable
      (show AEMeasurable (fun G => restrictFin m (drop k G)) _ from
        ((measurable_restrictFin m).comp (measurable_drop k)).aemeasurable)]
  refine Measure.ext_of_singleton fun p => ?_
  obtain ⟨F, H⟩ := p
  -- rewrite the joint singleton mass as the block mass
  have hpre : (fun G => (restrictFin k G, restrictFin m (drop k G))) ⁻¹'
      ({(F, H)} : Set (SimpleGraph (Fin k) × SimpleGraph (Fin m))) =
      restrictFin (k + m) ⁻¹' blockSet k m F H := by
    ext G
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, blockSet,
      Set.mem_setOf_eq, restrictFin_eq_comap_blockInit k m G,
      restrictFin_drop_eq_comap_blockTail k m G]
  have hLHS : (M.law : Measure InfiniteGraph).map
      (fun G => (restrictFin k G, restrictFin m (drop k G))) {(F, H)} =
      (L.law (k + m)).toMeasure (blockSet k m F H) := by
    rw [Measure.map_apply (f := fun G => (restrictFin k G, restrictFin m (drop k G)))
        ((measurable_restrictFin k).prodMk
          ((measurable_restrictFin m).comp (measurable_drop k)))
        (measurableSet_singleton _), hpre,
      ← Measure.map_apply (measurable_restrictFin (k + m))
        (Set.to_countable _).measurableSet, M.toExchangeableGraphLaw_law (k + m)]
  -- rewrite the product singleton mass as the product of marginal masses
  have hmarg₂ : (M.law : Measure InfiniteGraph).map
      (fun G => restrictFin m (drop k G)) = (L.law m).toMeasure := by
    rw [← Function.comp_def, ← Measure.map_map (measurable_restrictFin m) (measurable_drop k),
      M.law_map_drop k, M.toExchangeableGraphLaw_law m]
  have hRHS : ((M.law : Measure InfiniteGraph).map (restrictFin k)).prod
      ((M.law : Measure InfiniteGraph).map (fun G => restrictFin m (drop k G))) {(F, H)} =
      (L.law k).toMeasure {F} * (L.law m).toMeasure {H} := by
    rw [← Set.singleton_prod_singleton, Measure.prod_prod, M.toExchangeableGraphLaw_law k,
      hmarg₂]
  rw [hLHS, hRHS,
    (L.law k).toMeasure_apply_singleton _ (measurableSet_singleton _),
    (L.law m).toMeasure_apply_singleton _ (measurableSet_singleton _)]
  -- the two ℝ≥0∞ masses agree because their `toReal`s do (block factorization)
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ?_).mp ?_
  · exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)
  · rw [toMeasure_blockSet_toReal, Graphon.blockJoint_eq_prod hM, ENNReal.toReal_mul]

/-- **Dissociation implies restriction independence** (the reverse arc): the finite-window
independence lifts to the whole tail σ-algebra since the tail windows exhaust it. -/
theorem restrictionIndependent_of_isDissociated (M : Graphon.InfiniteExchangeableGraphLaw)
    (hM : M.IsDissociated) : M.RestrictionIndependent := by
  haveI : IsProbabilityMeasure (M.law : Measure InfiniteGraph) := M.law.2
  intro k
  have hsup := indep_iSup_of_directed_le
    (fun m => (indep_initial_tailWindow M hM k m).symm)
    (InfiniteGraph.tailWindowAlgebra_le k) (InfiniteGraph.initialAlgebra_le k)
    (Monotone.directed_le (InfiniteGraph.tailWindowAlgebra_mono k))
  rw [InfiniteGraph.iSup_tailWindowAlgebra] at hsup
  exact hsup.symm

/-- **The dissociation ↔ restriction-independence equivalence**. -/
theorem isDissociated_iff_restrictionIndependent
    (M : Graphon.InfiniteExchangeableGraphLaw) :
    M.IsDissociated ↔ M.RestrictionIndependent :=
  ⟨restrictionIndependent_of_isDissociated M,
    fun hR => GraphonSpace.isDissociated_of_vertexTailTrivial
      (vertexTailTrivial_of_restrictionIndependent hR)⟩

/-- **Diaconis–Janson Theorem 5.5** (the five-way extremality theorem). -/
@[blueprint "thm:dj-five-five"
  (title := /-- The five-way extremality theorem (Diaconis–Janson 5.5) -/)]
theorem tfae_extremality (M : Graphon.InfiniteExchangeableGraphLaw) :
    List.TFAE
      [(∃ x : StandardGraphonSpace,
          (GraphonSpace.infiniteMixtureLawEquiv (α := unitInterval) (μ := volume)).symm M
            = MeasureTheory.diracProba x),
        (∃ x : StandardGraphonSpace, M = GraphonSpace.infiniteSampleExchangeableLaw x),
        M.IsDissociated,
        M.RestrictionIndependent,
        M.VertexTailTrivial] := by
  tfae_have 3 ↔ 1 := GraphonSpace.isDissociated_iff_representing_dirac M
  tfae_have 3 ↔ 2 := GraphonSpace.isDissociated_iff_exists_infiniteSampleExchangeableLaw M
  tfae_have 3 ↔ 4 := isDissociated_iff_restrictionIndependent M
  tfae_have 4 → 5 := vertexTailTrivial_of_restrictionIndependent
  tfae_have 5 → 3 := GraphonSpace.isDissociated_of_vertexTailTrivial
  tfae_finish

end Graphon.InfiniteExchangeableGraphLaw
