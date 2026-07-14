/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.SamplingCoordinates
import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# The homomorphism-density coordinate algebra (issue #33, uniqueness bricks 1–2)

The uniqueness half of the Diaconis–Janson correspondence runs through the algebra of
descended homomorphism-density coordinates on the graphon space. This file provides its
first two bricks:

* `GraphonSpace.homDensityCoord` — homomorphism densities descend to continuous
  coordinates on the graphon space (well-defined by the counting lemma, continuous by
  Lipschitz continuity in cut distance), each a finite upper sum of `sampleMassCoord`s
  (`homDensityCoord_eq_sum_sampleMassCoord`), and jointly point-separating;
* `Graphon.homDensity_sum` — **multiplicativity over disjoint unions**:
  `homDensity (F ⊕g H) W = homDensity F W * homDensity H W`. Proof: `F ⊕g H` is the sup
  of the two vertex-embedded copies, whose edge sets are disjoint, so the integrand
  factors pointwise (`Quot.out` orientation is absorbed by the range lemma
  `out_mem_range_of_mem_edgeFinset_map` and by `homDensity_map_embedding`); the pi
  integral over `V ⊕ V'` splits by `measurePreserving_sumPiEquivProdPi_symm` and
  `integral_prod_mul`, and each factor is `homDensity` of a mapped graph, which
  `homDensity_map_embedding` reduces to the original;
* `Graphon.homDensity_sum_finAdd` — the `Fin (k + l)` corollary via
  `finSumFinEquiv`, keeping the coordinate algebra indexed by graphs on `Fin n`.

Bricks 3–4 (the multiplicatively closed coordinate span and the Polish measure
extensionality) complete the uniqueness theorem.
-/

open MeasureTheory

open scoped Classical

namespace Graphon

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

/-- Components of `Quot.out` of an edge of a mapped graph lie in the range of the
embedding. -/
private theorem out_mem_range_of_mem_edgeFinset_map {V W' : Type*} [Fintype V]
    [Fintype W'] [DecidableEq W'] {f : V ↪ W'} {F : SimpleGraph V} [DecidableRel F.Adj]
    {e : Sym2 W'} (he : e ∈ (F.map f).edgeFinset) :
    (Quot.out e).1 ∈ Set.range f ∧ (Quot.out e).2 ∈ Set.range f := by
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_map] at he
  obtain ⟨e', -, rfl⟩ := he
  induction e' with
  | _ a b =>
    have hrel : Sym2.Rel W' (Quot.out (f.sym2Map s(a, b))) (f a, f b) := by
      apply (Equivalence.quot_mk_eq_iff Sym2.Rel.is_equivalence _ _).mp
      simp only [Quot.out_eq]
      rfl
    rcases Sym2.rel_iff'.mp hrel with h | h
    · rw [show (Quot.out (f.sym2Map s(a, b))).1 = f a from congrArg Prod.fst h,
        show (Quot.out (f.sym2Map s(a, b))).2 = f b from congrArg Prod.snd h]
      exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    · rw [show (Quot.out (f.sym2Map s(a, b))).1 = f b by
          simpa using congrArg Prod.fst h,
        show (Quot.out (f.sym2Map s(a, b))).2 = f a by
          simpa using congrArg Prod.snd h]
      exact ⟨⟨b, rfl⟩, ⟨a, rfl⟩⟩

variable {V V' : Type*} [Fintype V] [Fintype V'] [DecidableEq V] [DecidableEq V']

omit [Fintype V] [Fintype V'] [DecidableEq V] [DecidableEq V'] in
/-- The disjoint sum of graphs is the sup of the two vertex-embedded copies. -/
private theorem sum_eq_map_sup_map (F : SimpleGraph V) (H : SimpleGraph V') :
    F ⊕g H = F.map Function.Embedding.inl ⊔ H.map Function.Embedding.inr := by
  ext a b
  cases a <;> cases b <;>
    simp [SimpleGraph.sum_adj, SimpleGraph.map_adj]

/-- The two vertex-embedded copies have disjoint edge sets. -/
private theorem disjoint_edgeFinset_map_inl_inr (F : SimpleGraph V) [DecidableRel F.Adj]
    (H : SimpleGraph V') [DecidableRel H.Adj] :
    Disjoint (F.map Function.Embedding.inl).edgeFinset
      (H.map Function.Embedding.inr).edgeFinset := by
  rw [Finset.disjoint_left]
  intro e heF heH
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_map] at heF heH
  obtain ⟨e₁, -, rfl⟩ := heF
  obtain ⟨e₂, -, hcontr⟩ := heH
  induction e₁ with
  | _ a b =>
    induction e₂ with
    | _ c d =>
      simp [Function.Embedding.sym2Map] at hcontr

/-- **Multiplicativity of homomorphism densities over disjoint unions**. -/
theorem homDensity_sum (F : SimpleGraph V) [DecidableRel F.Adj]
    (H : SimpleGraph V') [DecidableRel H.Adj] (W : Graphon α μ) :
    homDensity (F ⊕g H) W = homDensity F W * homDensity H W := by
  classical
  have hα : Nonempty α :=
    Set.nonempty_iff_univ_nonempty.mpr
      (nonempty_of_measure_ne_zero (μ := μ) (by simp))
  obtain ⟨a₀⟩ := hα
  -- Recast the disjoint sum as a sup (instances re-synthesized by `simp`).
  have hcast : homDensity (F ⊕g H) W = homDensity (F.map (Function.Embedding.inl : V ↪ V ⊕ V') ⊔ H.map (Function.Embedding.inr : V' ↪ V ⊕ V')) W := by
    simp only [sum_eq_map_sup_map]
  rw [hcast]
  -- The integrand factors pointwise over the disjoint edge sets.
  have hint : ∀ x : (V ⊕ V') → α,
      homDensityIntegrand (F.map (Function.Embedding.inl : V ↪ V ⊕ V') ⊔ H.map (Function.Embedding.inr : V' ↪ V ⊕ V')) W x =
        homDensityIntegrand (F.map (Function.Embedding.inl : V ↪ V ⊕ V')) W x * homDensityIntegrand (H.map (Function.Embedding.inr : V' ↪ V ⊕ V')) W x := by
    intro x
    simp only [homDensityIntegrand]
    refine (Finset.prod_congr (Finset.ext fun e => ?_) fun _ _ => rfl).trans
      (Finset.prod_union (disjoint_edgeFinset_map_inl_inr F H))
    simp
  -- The left factor depends only on the `inl` coordinates, the right only on `inr`.
  set eqv := MeasurableEquiv.sumPiEquivProdPi (fun _ : V ⊕ V' => α) with heqv
  have hleft : ∀ (y : V → α) (z z' : V' → α),
      homDensityIntegrand (F.map (Function.Embedding.inl : V ↪ V ⊕ V')) W (eqv.symm (y, z)) =
        homDensityIntegrand (F.map (Function.Embedding.inl : V ↪ V ⊕ V')) W (eqv.symm (y, z')) := by
    intro y z z'
    simp only [homDensityIntegrand]
    refine Finset.prod_congr rfl fun e he => ?_
    obtain ⟨⟨v₁, h₁⟩, ⟨v₂, h₂⟩⟩ := out_mem_range_of_mem_edgeFinset_map he
    rw [← h₁, ← h₂]
    rfl
  have hright : ∀ (y y' : V → α) (z : V' → α),
      homDensityIntegrand (H.map (Function.Embedding.inr : V' ↪ V ⊕ V')) W (eqv.symm (y, z)) =
        homDensityIntegrand (H.map (Function.Embedding.inr : V' ↪ V ⊕ V')) W (eqv.symm (y', z)) := by
    intro y y' z
    simp only [homDensityIntegrand]
    refine Finset.prod_congr rfl fun e he => ?_
    obtain ⟨⟨v₁, h₁⟩, ⟨v₂, h₂⟩⟩ := out_mem_range_of_mem_edgeFinset_map he
    rw [← h₁, ← h₂]
    rfl
  -- Transport to the product measure and split by Fubini.
  have hmp := MeasureTheory.measurePreserving_sumPiEquivProdPi_symm
    (fun _ : V ⊕ V' => μ)
  have hsplit : ∀ (G' : SimpleGraph (V ⊕ V')) (inst : DecidableRel G'.Adj),
      @homDensity α _ μ (V ⊕ V') _ G' inst W =
        ∫ p : (V → α) × (V' → α),
          @homDensityIntegrand α _ μ (V ⊕ V') _ G' inst W (eqv.symm p)
          ∂((Measure.pi fun _ : V => μ).prod (Measure.pi fun _ : V' => μ)) := by
    intro G' inst
    rw [homDensity_eq_integral, ← hmp.integral_comp']
  rw [hsplit _ _]
  set y₀ : V → α := fun _ => a₀
  set z₀ : V' → α := fun _ => a₀
  set f : (V → α) → ℝ :=
    fun y => homDensityIntegrand (F.map (Function.Embedding.inl : V ↪ V ⊕ V')) W (eqv.symm (y, z₀)) with hf
  set g : (V' → α) → ℝ :=
    fun z => homDensityIntegrand (H.map (Function.Embedding.inr : V' ↪ V ⊕ V')) W (eqv.symm (y₀, z)) with hg
  have hcongr : ∀ p : (V → α) × (V' → α),
      homDensityIntegrand (F.map (Function.Embedding.inl : V ↪ V ⊕ V') ⊔ H.map (Function.Embedding.inr : V' ↪ V ⊕ V')) W (eqv.symm p) =
        f p.1 * g p.2 := by
    intro p
    rw [hint (eqv.symm p)]
    congr 1
    · exact hleft p.1 p.2 z₀
    · exact hright p.1 y₀ p.2
  rw [integral_congr_ae (Filter.Eventually.of_forall hcongr),
    MeasureTheory.integral_prod_mul f g]
  -- Each factor is the hom density of the mapped graph.
  have hF : (∫ y, f y ∂Measure.pi fun _ : V => μ) = homDensity F W := by
    rw [← homDensity_map_embedding F (Function.Embedding.inl : V ↪ V ⊕ V') W, hsplit (F.map (Function.Embedding.inl : V ↪ V ⊕ V')) _]
    rw [integral_congr_ae (Filter.Eventually.of_forall
      (fun p : (V → α) × (V' → α) =>
        show homDensityIntegrand (F.map (Function.Embedding.inl : V ↪ V ⊕ V')) W (eqv.symm p) = f p.1 * (fun _ => (1 : ℝ)) p.2
        from by rw [hleft p.1 p.2 z₀]; simp [hf])),
      MeasureTheory.integral_prod_mul f (fun _ => (1 : ℝ))]
    simp
  have hH : (∫ z, g z ∂Measure.pi fun _ : V' => μ) = homDensity H W := by
    rw [← homDensity_map_embedding H (Function.Embedding.inr : V' ↪ V ⊕ V') W, hsplit (H.map (Function.Embedding.inr : V' ↪ V ⊕ V')) _]
    rw [integral_congr_ae (Filter.Eventually.of_forall
      (fun p : (V → α) × (V' → α) =>
        show homDensityIntegrand (H.map (Function.Embedding.inr : V' ↪ V ⊕ V')) W (eqv.symm p) = (fun _ => (1 : ℝ)) p.1 * g p.2
        from by rw [hright p.1 y₀ p.2]; simp [hg])),
      MeasureTheory.integral_prod_mul (fun _ => (1 : ℝ)) g]
    simp
  rw [hF, hH]

/-- The `Fin (k + l)` coordinate form of disjoint-union multiplicativity, via
`finSumFinEquiv`: keeps the coordinate algebra indexed by graphs on `Fin n`. -/
theorem homDensity_sum_finAdd {k l : ℕ} (F : SimpleGraph (Fin k)) [DecidableRel F.Adj]
    (H : SimpleGraph (Fin l)) [DecidableRel H.Adj] (W : Graphon α μ) :
    homDensity ((F ⊕g H).map finSumFinEquiv.toEmbedding) W =
      homDensity F W * homDensity H W := by
  classical
  rw [homDensity_map_embedding, homDensity_sum]

end Graphon

namespace GraphonSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ]

open scoped Classical

/-- **The homomorphism-density coordinate**: `homDensity F ·` descends to the graphon
space (well-defined by the counting lemma `homDensity_eq_of_cutDistance_zero`). -/
noncomputable def homDensityCoord {V : Type*} [Fintype V] (F : SimpleGraph V) :
    GraphonSpace α μ → ℝ :=
  SeparationQuotient.lift (fun W => Graphon.homDensity F W) fun U W h =>
    Graphon.homDensity_eq_of_cutDistance_zero F U W (Metric.inseparable_iff.mp h)

@[simp] theorem homDensityCoord_mk {V : Type*} [Fintype V] (F : SimpleGraph V)
    (W : Graphon α μ) : homDensityCoord F (mk W) = Graphon.homDensity F W := rfl

theorem continuous_homDensityCoord {V : Type*} [Fintype V] (F : SimpleGraph V) :
    Continuous (homDensityCoord (α := α) (μ := μ) F) :=
  SeparationQuotient.continuous_lift (Graphon.continuous_homDensity F)

/-- The hom-density coordinates are finite upper sums of the sample-mass coordinates
(the forward Möbius identity, descended): equal mixture marginals therefore give equal
integrals of every hom-density coordinate. -/
theorem homDensityCoord_eq_sum_sampleMassCoord {k : ℕ} (F : SimpleGraph (Fin k))
    (x : GraphonSpace α μ) :
    homDensityCoord F x =
      ∑ G : SimpleGraph (Fin k), if F ≤ G then sampleMassCoord G x else 0 := by
  obtain ⟨W, rfl⟩ := surjective_mk x
  simp only [homDensityCoord_mk, sampleMassCoord_mk]
  exact Graphon.homDensity_eq_sum_sampleMass W F

/-- The hom-density coordinates separate points of the graphon space (via the
determination theorem). -/
theorem homDensityCoord_eq_all_iff {x y : GraphonSpace α μ} :
    (∀ (k : ℕ) (F : SimpleGraph (Fin k)), homDensityCoord F x = homDensityCoord F y) ↔
      x = y := by
  constructor
  · intro h
    obtain ⟨U, rfl⟩ := surjective_mk x
    obtain ⟨W, rfl⟩ := surjective_mk y
    rw [mk_eq_mk_iff]
    exact Graphon.weaklyIsomorphic_of_homDensity_eq U W fun k F _ => by
      have := h k F
      simpa only [homDensityCoord_mk] using
        (Graphon.homDensity_congr_decRel F _ _ U).symm.trans
          (this.trans (Graphon.homDensity_congr_decRel F _ _ W))
  · rintro rfl
    exact fun _ _ => rfl

end GraphonSpace
