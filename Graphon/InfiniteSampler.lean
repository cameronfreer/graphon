/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.InfiniteExchangeability
import Graphon.InfiniteSampleLaw
import Graphon.Sampling
import Mathlib.Probability.ProductMeasure

/-!
# The explicit infinite sampler for a fixed graphon (issue #51, sources + sampler)

Reusable i.i.d. product sources via `Measure.infinitePi`, and the explicit measurable
sampler from those sources to the infinite graph space:

* `InfiniteGraph.vertexSource` — i.i.d. vertex positions `ℕ → α` with law `μ`;
* `InfiniteGraph.edgeSource` — i.i.d. edge uniforms on `[0,1]`, indexed by `EdgeIndex`;
* `InfiniteGraph.clampedRep W` — the everywhere-`[0,1]`-valued clamped representative
  of the graphon (a.e. equal to it);
* `InfiniteGraph.sampleInfinite W` — one uniform per unordered edge, compared against
  the clamped graphon value at the `Quot.out`-representative endpoint positions
  (matching `sampleIntegrand`'s orientation): measurable in the sources.

* `InfiniteGraph.map_sampleInfinite_restrictFin` — **the finite marginal
  identification**: the sampler's level-`k` law is exactly `samplePMF W k` (upper-event
  route: `F ≤ G` needs only the edges of `F`, so conditional edge integration produces
  the plain `W`-product; `upperSum_injective` closes);
* `InfiniteGraph.map_sampleInfinite` — **the explicit realization theorem**: the
  sampler's law is `infiniteLaw (sampleExchangeableLaw W)` (A2 uniqueness), with
  relabeling invariance (`map_sampleInfinite_relabel`) and the canonical-class form
  (`map_sampleInfinite_eq_infiniteSampleLaw_mk`) as corollaries.
-/

open MeasureTheory

open scoped Classical

namespace InfiniteGraph

/-- The uniform distribution on `[0,1]`. -/
noncomputable def uniform01 : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure uniform01 :=
  ⟨by rw [uniform01, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Icc]; norm_num⟩

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- **The vertex source**: i.i.d. positions `ℕ → α` with law `μ`. -/
noncomputable def vertexSource : Measure (ℕ → α) :=
  Measure.infinitePi fun _ : ℕ => μ

/-- **The edge source**: i.i.d. uniforms on `[0,1]`, one per unordered edge. -/
noncomputable def edgeSource : Measure (EdgeIndex → ℝ) :=
  Measure.infinitePi fun _ : EdgeIndex => uniform01

instance [IsProbabilityMeasure μ] : IsProbabilityMeasure (vertexSource μ) := by
  rw [vertexSource]; infer_instance

instance : IsProbabilityMeasure (edgeSource) := by
  rw [edgeSource]; infer_instance

/-- **The sampler source**: independent vertex positions and edge uniforms. -/
noncomputable def samplerSource : Measure ((ℕ → α) × (EdgeIndex → ℝ)) :=
  (vertexSource μ).prod edgeSource

instance [IsProbabilityMeasure μ] : IsProbabilityMeasure (samplerSource μ) := by
  rw [samplerSource]; infer_instance

variable {μ}

/-- The clamped `[0,1]`-valued representative of a graphon: an everywhere-valid edge
probability (the graphon is only a.e. `[0,1]`-valued; clamping isolates the eventual
a.e.-congruence argument). -/
noncomputable def clampedRep (W : Graphon α μ) (p : α × α) : ℝ :=
  min 1 (max 0 (W.toAEEqFun p))

theorem clampedRep_mem_Icc (W : Graphon α μ) (p : α × α) :
    clampedRep W p ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_min zero_le_one (le_max_left 0 _), min_le_left 1 _⟩

theorem measurable_clampedRep (W : Graphon α μ) : Measurable (clampedRep W) :=
  measurable_const.min (measurable_const.max W.toAEEqFun.stronglyMeasurable.measurable)

/-- The clamped representative agrees with the graphon almost everywhere. -/
theorem clampedRep_ae_eq (W : Graphon α μ) :
    ∀ᵐ p ∂(μ.prod μ), clampedRep W p = W.toAEEqFun p := by
  filter_upwards [W.ae_mem_Icc] with p hp
  rw [clampedRep, max_eq_right hp.1, min_eq_right hp.2]

/-- **The explicit infinite sampler**: include the edge `e` exactly when its uniform
falls below the clamped graphon value at the `Quot.out`-representative endpoint
positions (matching the orientation convention of `sampleIntegrand`, which eliminates
the a.e.-symmetry orientation juggling in the marginal identification). -/
noncomputable def sampleInfinite (W : Graphon α μ) (ω : (ℕ → α) × (EdgeIndex → ℝ)) :
    InfiniteGraph :=
  coordEquiv.symm fun e =>
    if ω.2 e ≤ clampedRep W (ω.1 (Quot.out (e : Sym2 ℕ)).1, ω.1 (Quot.out (e : Sym2 ℕ)).2)
    then true else false

/-- The edge coordinates of a sample, unfolded. -/
theorem coordEquiv_sampleInfinite (W : Graphon α μ) (ω : (ℕ → α) × (EdgeIndex → ℝ))
    (e : EdgeIndex) :
    coordEquiv (sampleInfinite W ω) e =
      if ω.2 e ≤ clampedRep W (ω.1 (Quot.out (e : Sym2 ℕ)).1, ω.1 (Quot.out (e : Sym2 ℕ)).2)
      then true else false := by
  rw [sampleInfinite, Equiv.apply_symm_apply]

/-- **The sampler is measurable** in the sources: each edge coordinate is a measurable
comparison. -/
theorem measurable_sampleInfinite (W : Graphon α μ) :
    Measurable (sampleInfinite W) := by
  have hsymm : Measurable (coordEquiv.symm : (EdgeIndex → Bool) → InfiniteGraph) :=
    coordHomeomorph.symm.continuous.measurable
  refine hsymm.comp ?_
  rw [measurable_pi_iff]
  intro e
  have hW : Measurable fun ω : (ℕ → α) × (EdgeIndex → ℝ) =>
      clampedRep W (ω.1 (Quot.out (e : Sym2 ℕ)).1, ω.1 (Quot.out (e : Sym2 ℕ)).2) :=
    (measurable_clampedRep W).comp
      (((measurable_pi_apply _).comp measurable_fst).prodMk
        ((measurable_pi_apply _).comp measurable_fst))
  have hu : Measurable fun ω : (ℕ → α) × (EdgeIndex → ℝ) => ω.2 e :=
    (measurable_pi_apply e).comp measurable_snd
  have hset : MeasurableSet {ω : (ℕ → α) × (EdgeIndex → ℝ) |
      ω.2 e ≤ clampedRep W (ω.1 (Quot.out (e : Sym2 ℕ)).1, ω.1 (Quot.out (e : Sym2 ℕ)).2)} :=
    measurableSet_le hu hW
  exact Measurable.ite hset measurable_const measurable_const

/-! ### The finite marginal identification (issue #51, brick 2)

`restrictFin k ∘ sampleInfinite W` pushes the sampler source forward to exactly the
finite sample law `samplePMF W k`, and hence `sampleInfinite W` realizes the infinite
exchangeable law of `sampleExchangeableLaw W`. Route: reduce singleton masses to upper
events `{G | F ≤ G}` via Möbius inversion (`upperSum_injective`); the upper event is a
finite cylinder over the (injectively indexed) edge uniforms, whose vertex-conditional
probability is the clamped edge product; integrating out the positions gives
`homDensity F W`, which is also the upper transform of `sampleMass W`. -/

section Marginal

/-- Pushing an infinite product of probability measures forward along precomposition
with an injection from a finite index type gives the finite product of the selected
factors — `Measure.infinitePi_map_restrict` for an arbitrary injection (constant-fiber
form; Mathlib upstreaming candidate, issue #24). -/
theorem _root_.MeasureTheory.Measure.infinitePi_map_comp_of_injective
    {ι δ γ : Type*} [MeasurableSpace γ] (ν : ι → Measure γ)
    [∀ i, IsProbabilityMeasure (ν i)] [Fintype δ] {f : δ → ι}
    (hf : Function.Injective f) :
    (Measure.infinitePi ν).map (fun (x : ι → γ) (d : δ) => x (f d)) =
      Measure.pi fun d => ν (f d) := by
  classical
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hm : Measurable fun (x : ι → γ) (d : δ) => x (f d) :=
    measurable_pi_iff.mpr fun d => measurable_pi_apply _
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun (x : ι → γ) (d : δ) => x (f d)) ⁻¹' Set.univ.pi s =
      Set.pi ↑(Finset.univ.image f) (Function.extend f s fun _ => Set.univ) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Finset.coe_image,
      Finset.coe_univ, Set.image_univ, Set.mem_range, forall_exists_index]
    constructor
    · rintro h i d rfl
      rw [hf.extend_apply]
      exact h d
    · intro h d
      have hd := h (f d) d rfl
      rwa [hf.extend_apply] at hd
  have hmeas : ∀ i ∈ Finset.univ.image f,
      MeasurableSet (Function.extend f s (fun _ => Set.univ) i) := by
    intro i hi
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hi
    rw [hf.extend_apply]
    exact hs d
  rw [hpre, Measure.infinitePi_pi ν hmeas,
    Finset.prod_image fun a _ b _ hab => hf hab]
  exact Finset.prod_congr rfl fun d _ => by rw [hf.extend_apply]

/-- The lower-interval mass of the uniform distribution on `[0,1]`. -/
theorem uniform01_Iic {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    uniform01 (Set.Iic c) = ENNReal.ofReal c := by
  rw [uniform01, Measure.restrict_apply measurableSet_Iic]
  have h : Set.Iic c ∩ Set.Icc 0 1 = Set.Icc 0 c := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans hc.2⟩⟩
  rw [h, Real.volume_Icc, sub_zero]

/-- The joint law of the first `k` vertex positions is the finite i.i.d. product. -/
theorem vertexSource_map_fin [IsProbabilityMeasure μ] (k : ℕ) :
    (vertexSource μ).map (fun (x : ℕ → α) (a : Fin k) => x ↑a) =
      Measure.pi fun _ : Fin k => μ :=
  Measure.infinitePi_map_comp_of_injective _ Fin.val_injective

/-- The `ℕ`-image of a non-diagonal finite edge stays non-diagonal. -/
private theorem not_isDiag_map_val {k : ℕ} {e : Sym2 (Fin k)} (he : ¬ e.IsDiag) :
    ¬ (Sym2.map (Fin.val : Fin k → ℕ) e).IsDiag :=
  fun h => he ((Sym2.isDiag_map Fin.val_injective).mp h)

/-- The edge indices of the edges of a finite graph. -/
private noncomputable def edgeEmb {k : ℕ} (F : SimpleGraph (Fin k))
    (e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset}) : EdgeIndex :=
  ⟨Sym2.map Fin.val e.1,
    not_isDiag_map_val (F.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp e.2))⟩

private theorem edgeEmb_injective {k : ℕ} (F : SimpleGraph (Fin k)) :
    Function.Injective (edgeEmb F) := fun _ _ h =>
  Subtype.ext (Sym2.map.injective Fin.val_injective (congrArg Subtype.val h))

/-- Edge membership in a sample, in terms of the sources. -/
private theorem mem_edgeSet_sampleInfinite (W : Graphon α μ)
    (ω : (ℕ → α) × (EdgeIndex → ℝ)) (i : EdgeIndex) :
    (i : Sym2 ℕ) ∈ (sampleInfinite W ω : SimpleGraph ℕ).edgeSet ↔
      ω.2 i ≤ clampedRep W
        (ω.1 (Quot.out (i : Sym2 ℕ)).1, ω.1 (Quot.out (i : Sym2 ℕ)).2) := by
  have h := coordEquiv_sampleInfinite W ω i
  rw [coordEquiv_apply] at h
  constructor
  · intro hmem
    by_contra hle
    rw [if_pos hmem, if_neg hle] at h
    exact Bool.noConfusion h
  · intro hle
    by_contra hmem
    rw [if_neg hmem, if_pos hle] at h
    exact Bool.noConfusion h

/-- Edge membership under vertex-set restriction along `Fin.val`. -/
private theorem comap_val_edgeSet {k : ℕ} (S : SimpleGraph ℕ) (e : Sym2 (Fin k)) :
    e ∈ (S.comap ((↑) : Fin k → ℕ)).edgeSet ↔ Sym2.map Fin.val e ∈ S.edgeSet := by
  induction e using Sym2.ind with
  | _ a b => simp [SimpleGraph.mem_edgeSet]

/-- The upper event unfolded: `F` embeds into the sampled graph's restriction iff every
edge uniform of `F` clears its clamped threshold. -/
private theorem le_restrictFin_sampleInfinite_iff (W : Graphon α μ) {k : ℕ}
    (F : SimpleGraph (Fin k)) (ω : (ℕ → α) × (EdgeIndex → ℝ)) :
    F ≤ restrictFin k (sampleInfinite W ω) ↔
      ∀ e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset},
        ω.2 (edgeEmb F e) ≤ clampedRep W
          (ω.1 (Quot.out (Sym2.map Fin.val e.1)).1,
            ω.1 (Quot.out (Sym2.map Fin.val e.1)).2) := by
  rw [← SimpleGraph.edgeSet_subset_edgeSet]
  constructor
  · intro hsub e
    exact (mem_edgeSet_sampleInfinite W ω (edgeEmb F e)).mp
      ((comap_val_edgeSet _ e.1).mp (hsub (SimpleGraph.mem_edgeFinset.mp e.2)))
  · intro h s hs
    exact (comap_val_edgeSet _ s).mpr
      ((mem_edgeSet_sampleInfinite W ω
        (edgeEmb F ⟨s, SimpleGraph.mem_edgeFinset.mpr hs⟩)).mpr
        (h ⟨s, SimpleGraph.mem_edgeFinset.mpr hs⟩))

/-- `Quot.out` of the `ℕ`-image of a finite edge is the `Fin.val`-image of `Quot.out`
of the edge, possibly swapped. -/
private theorem out_map_val_eq_or_swap {k : ℕ} (e : Sym2 (Fin k)) :
    Quot.out (Sym2.map Fin.val e) = (((Quot.out e).1 : ℕ), ((Quot.out e).2 : ℕ)) ∨
      Quot.out (Sym2.map Fin.val e) = (((Quot.out e).2 : ℕ), ((Quot.out e).1 : ℕ)) := by
  have h_rel : Sym2.Rel ℕ (Quot.out (Sym2.map Fin.val e))
      ((((Quot.out e).1 : ℕ), ((Quot.out e).2 : ℕ))) := by
    apply (Equivalence.quot_mk_eq_iff Sym2.Rel.is_equivalence _ _).mp
    simp only [Quot.out_eq]
    change Sym2.map Fin.val e = Sym2.map Fin.val (Quot.mk _ (Quot.out e))
    congr 1
    exact (Quot.out_eq e).symm
  rcases Sym2.rel_iff'.mp h_rel with h | h
  · exact Or.inl h
  · right
    simpa [Prod.swap] using h

/-- Both `Quot.out` components of the `ℕ`-image of a finite edge are below `k`. -/
private theorem out_map_val_lt {k : ℕ} (e : Sym2 (Fin k)) :
    (Quot.out (Sym2.map Fin.val e)).1 < k ∧ (Quot.out (Sym2.map Fin.val e)).2 < k := by
  rcases out_map_val_eq_or_swap e with h | h <;> rw [h] <;>
    exact ⟨Fin.is_lt _, Fin.is_lt _⟩

/-- The first endpoint of the `ℕ`-image of a finite edge, as an element of `Fin k`. -/
private noncomputable def outFst {k : ℕ} (e : Sym2 (Fin k)) : Fin k :=
  ⟨(Quot.out (Sym2.map Fin.val e)).1, (out_map_val_lt e).1⟩

/-- The second endpoint of the `ℕ`-image of a finite edge, as an element of `Fin k`. -/
private noncomputable def outSnd {k : ℕ} (e : Sym2 (Fin k)) : Fin k :=
  ⟨(Quot.out (Sym2.map Fin.val e)).2, (out_map_val_lt e).2⟩

/-- A.e. under the finite product, the clamped edge product at the sampler's endpoint
representatives equals the homomorphism-density integrand (a.e. `[0,1]`-congruence plus
a.e. symmetry, transported to coordinate pairs by `ae_pairMap_of_prod`). -/
private theorem ae_clampedProd_eq_integrand [IsProbabilityMeasure μ] (W : Graphon α μ)
    {k : ℕ} (F : SimpleGraph (Fin k)) :
    ∀ᵐ y ∂Measure.pi (fun _ : Fin k => μ),
      (∏ e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset},
        clampedRep W (y (outFst e.1), y (outSnd e.1))) =
        Graphon.homDensityIntegrand F W y := by
  have hedge : ∀ e ∈ F.edgeFinset, ∀ᵐ y ∂Measure.pi (fun _ : Fin k => μ),
      clampedRep W (y (outFst e), y (outSnd e)) =
        W.toAEEqFun (y (Quot.out e).1, y (Quot.out e).2) := by
    intro e he
    have hne : (Quot.out e).1 ≠ (Quot.out e).2 :=
      Graphon.edge_out_ne (SimpleGraph.mem_edgeFinset.mp he)
    rcases out_map_val_eq_or_swap e with hor | hor
    · have h1 : outFst e = (Quot.out e).1 := Fin.val_injective (congrArg Prod.fst hor)
      have h2 : outSnd e = (Quot.out e).2 := Fin.val_injective (congrArg Prod.snd hor)
      rw [h1, h2]
      exact Graphon.ae_pairMap_of_prod _ _ hne (clampedRep_ae_eq W)
    · have h1 : outFst e = (Quot.out e).2 := Fin.val_injective (congrArg Prod.fst hor)
      have h2 : outSnd e = (Quot.out e).1 := Fin.val_injective (congrArg Prod.snd hor)
      rw [h1, h2]
      have hswap : ∀ᵐ p ∂(μ.prod μ),
          clampedRep W (Prod.swap p) = W.toAEEqFun p := by
        have hc : ∀ᵐ p ∂(μ.prod μ),
            clampedRep W (Prod.swap p) = W.toAEEqFun (Prod.swap p) :=
          Measure.measurePreserving_swap.quasiMeasurePreserving.ae
            (clampedRep_ae_eq W)
        filter_upwards [hc, W.symm_ae] with p hp hsym
        rw [hp, hsym]
      refine (Graphon.ae_pairMap_of_prod _ _ hne hswap).mono fun y hy => ?_
      simpa using hy
  have hall : ∀ᵐ y ∂Measure.pi (fun _ : Fin k => μ), ∀ e ∈ F.edgeFinset,
      clampedRep W (y (outFst e), y (outSnd e)) =
        W.toAEEqFun (y (Quot.out e).1, y (Quot.out e).2) :=
    (Filter.eventually_all_finset F.edgeFinset).mpr hedge
  filter_upwards [hall] with y hy
  calc (∏ e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset},
        clampedRep W (y (outFst e.1), y (outSnd e.1)))
      = ∏ e ∈ F.edgeFinset.attach,
          W.toAEEqFun (y (Quot.out e.1).1, y (Quot.out e.1).2) := by
        rw [Finset.univ_eq_attach]
        exact Finset.prod_congr rfl fun e _ => hy e.1 e.2
    _ = ∏ e ∈ F.edgeFinset,
          W.toAEEqFun (y (Quot.out e).1, y (Quot.out e).2) :=
        Finset.prod_attach F.edgeFinset
          fun e => (W.toAEEqFun (y (Quot.out e).1, y (Quot.out e).2) : ℝ)
    _ = Graphon.homDensityIntegrand F W y := rfl

/-- **The upper-event mass of the sampler marginal is the homomorphism density**: the
heart of the finite marginal identification. -/
private theorem map_sampleInfinite_apply_le_event [IsProbabilityMeasure μ]
    (W : Graphon α μ) {k : ℕ} (F : SimpleGraph (Fin k)) :
    (samplerSource μ).map (restrictFin k ∘ sampleInfinite W) {G | F ≤ G} =
      ENNReal.ofReal (Graphon.homDensity F W) := by
  have hmeas : Measurable (restrictFin k ∘ sampleInfinite W) :=
    (measurable_restrictFin k).comp (measurable_sampleInfinite W)
  rw [Measure.map_apply hmeas ((Set.to_countable _).measurableSet)]
  have hA : (restrictFin k ∘ sampleInfinite W) ⁻¹' {G | F ≤ G} =
      {ω : (ℕ → α) × (EdgeIndex → ℝ) |
        ∀ e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset},
          ω.2 (edgeEmb F e) ∈ Set.Iic (clampedRep W
            (ω.1 (Quot.out (Sym2.map Fin.val e.1)).1,
              ω.1 (Quot.out (Sym2.map Fin.val e.1)).2))} := by
    ext ω
    simpa [Set.mem_Iic] using le_restrictFin_sampleInfinite_iff W F ω
  have hAmeas : MeasurableSet {ω : (ℕ → α) × (EdgeIndex → ℝ) |
      ∀ e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset},
        ω.2 (edgeEmb F e) ∈ Set.Iic (clampedRep W
          (ω.1 (Quot.out (Sym2.map Fin.val e.1)).1,
            ω.1 (Quot.out (Sym2.map Fin.val e.1)).2))} := by
    rw [← hA]
    exact hmeas ((Set.to_countable _).measurableSet)
  rw [hA, samplerSource, Measure.prod_apply hAmeas]
  have hsec : ∀ x : ℕ → α,
      edgeSource (Prod.mk x ⁻¹' {ω : (ℕ → α) × (EdgeIndex → ℝ) |
        ∀ e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset},
          ω.2 (edgeEmb F e) ∈ Set.Iic (clampedRep W
            (ω.1 (Quot.out (Sym2.map Fin.val e.1)).1,
              ω.1 (Quot.out (Sym2.map Fin.val e.1)).2))}) =
      ENNReal.ofReal (∏ e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset},
        clampedRep W (x (Quot.out (Sym2.map Fin.val e.1)).1,
          x (Quot.out (Sym2.map Fin.val e.1)).2)) := by
    intro x
    have hpre : Prod.mk x ⁻¹' {ω : (ℕ → α) × (EdgeIndex → ℝ) |
        ∀ e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset},
          ω.2 (edgeEmb F e) ∈ Set.Iic (clampedRep W
            (ω.1 (Quot.out (Sym2.map Fin.val e.1)).1,
              ω.1 (Quot.out (Sym2.map Fin.val e.1)).2))} =
        (fun (u : EdgeIndex → ℝ) (e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset}) =>
          u (edgeEmb F e)) ⁻¹' Set.univ.pi (fun e =>
            Set.Iic (clampedRep W (x (Quot.out (Sym2.map Fin.val e.1)).1,
              x (Quot.out (Sym2.map Fin.val e.1)).2))) := by
      ext u
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
        true_implies]
    have hgm : Measurable fun (u : EdgeIndex → ℝ)
        (e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset}) => u (edgeEmb F e) :=
      measurable_pi_iff.mpr fun e => measurable_pi_apply _
    have hmap : edgeSource.map (fun (u : EdgeIndex → ℝ)
        (e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset}) => u (edgeEmb F e)) =
        Measure.pi fun _ : {e : Sym2 (Fin k) // e ∈ F.edgeFinset} => uniform01 := by
      rw [edgeSource]
      exact Measure.infinitePi_map_comp_of_injective _ (edgeEmb_injective F)
    rw [hpre, ← Measure.map_apply hgm
        (MeasurableSet.univ_pi fun e => measurableSet_Iic), hmap, Measure.pi_pi,
      ENNReal.ofReal_prod_of_nonneg fun e _ => (clampedRep_mem_Icc W _).1]
    exact Finset.prod_congr rfl fun e _ => uniform01_Iic (clampedRep_mem_Icc W _)
  rw [lintegral_congr hsec]
  have hg : Measurable fun y : Fin k → α => ENNReal.ofReal
      (∏ e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset},
        clampedRep W (y (outFst e.1), y (outSnd e.1))) := by
    refine Measurable.ennreal_ofReal ?_
    refine Finset.measurable_prod _ fun e _ => ?_
    exact (measurable_clampedRep W).comp
      ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
  have hπ : Measurable fun (x : ℕ → α) (a : Fin k) => x ↑a :=
    measurable_pi_iff.mpr fun a => measurable_pi_apply _
  have hchange : (∫⁻ x, ENNReal.ofReal
      (∏ e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset},
        clampedRep W (x (Quot.out (Sym2.map Fin.val e.1)).1,
          x (Quot.out (Sym2.map Fin.val e.1)).2)) ∂vertexSource μ) =
      ∫⁻ y, ENNReal.ofReal (∏ e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset},
        clampedRep W (y (outFst e.1), y (outSnd e.1)))
        ∂Measure.pi (fun _ : Fin k => μ) := by
    rw [← vertexSource_map_fin (μ := μ) k, lintegral_map hg hπ]
    rfl
  have hae : (∫⁻ y, ENNReal.ofReal (∏ e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset},
        clampedRep W (y (outFst e.1), y (outSnd e.1)))
        ∂Measure.pi (fun _ : Fin k => μ)) =
      ∫⁻ y, ENNReal.ofReal (Graphon.homDensityIntegrand F W y)
        ∂Measure.pi (fun _ : Fin k => μ) :=
    lintegral_congr_ae ((ae_clampedProd_eq_integrand W F).mono fun y hy =>
      congrArg ENNReal.ofReal hy)
  rw [hchange, hae, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (Graphon.homDensityIntegrand_integrable F W)
      (Graphon.homDensityIntegrand_nonneg_ae F W),
    ← Graphon.homDensity_eq_integral]

/-- **The finite marginal identification** (issue #51, brick 2): the law of the first-
`k`-vertices restriction of the sampled infinite graph is exactly the finite sample law
`samplePMF W k`. -/
theorem map_sampleInfinite_restrictFin (W : Graphon α μ) [IsProbabilityMeasure μ]
    (k : ℕ) :
    (samplerSource μ).map (restrictFin k ∘ sampleInfinite W) =
      (Graphon.samplePMF W k).toMeasure := by
  set ν : Measure (SimpleGraph (Fin k)) :=
    (samplerSource μ).map (restrictFin k ∘ sampleInfinite W) with hν
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map
      ((measurable_restrictFin k).comp (measurable_sampleInfinite W)).aemeasurable
  have hq : (fun G => (ν {G}).toReal) = Graphon.sampleMass W := by
    refine Graphon.upperSum_injective fun F => ?_
    have hset : {G : SimpleGraph (Fin k) | F ≤ G} =
        ⋃ G ∈ Finset.univ.filter fun G : SimpleGraph (Fin k) => F ≤ G,
          ({G} : Set (SimpleGraph (Fin k))) := by
      ext G
      simp
    have hsum : ν (⋃ G ∈ Finset.univ.filter fun G : SimpleGraph (Fin k) => F ≤ G,
        ({G} : Set (SimpleGraph (Fin k)))) =
        ∑ G ∈ Finset.univ.filter fun G : SimpleGraph (Fin k) => F ≤ G, ν {G} :=
      measure_biUnion_finset (fun G₁ _ G₂ _ hne => Set.disjoint_singleton.mpr hne)
        fun G _ => measurableSet_singleton G
    have hupper : Graphon.upperSum (fun G => (ν {G}).toReal) F =
        (ν {G | F ≤ G}).toReal := by
      rw [Graphon.upperSum, ← Finset.sum_filter, hset, hsum,
        ENNReal.toReal_sum fun G _ => measure_ne_top ν _]
    rw [hupper, hν, map_sampleInfinite_apply_le_event W F,
      ENNReal.toReal_ofReal (Graphon.homDensity_nonneg F W),
      ← Graphon.upperSum_sampleMass W F]
  refine Measure.ext_of_singleton fun G => ?_
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton G),
    Graphon.samplePMF_apply, ← congrFun hq G,
    ENNReal.ofReal_toReal (measure_ne_top ν _)]

/-- **The sampler realizes the infinite exchangeable law** (issue #51): the pushforward
of the sampler source under `sampleInfinite W` is the (A2-unique) infinite law of the
sample exchangeable law of `W`. -/
@[blueprint "thm:explicit-sampler"
  (title := /-- The explicit sampler realizes the infinite law -/)]
theorem map_sampleInfinite (W : Graphon α μ) [IsProbabilityMeasure μ] :
    ((samplerSource μ).map (sampleInfinite W)) =
      ((Graphon.ExchangeableGraphLaw.infiniteLaw (Graphon.sampleExchangeableLaw W) :
        ProbabilityMeasure InfiniteGraph) : Measure InfiniteGraph) := by
  have hP : (⟨(samplerSource μ).map (sampleInfinite W),
      Measure.isProbabilityMeasure_map (measurable_sampleInfinite W).aemeasurable⟩ :
        ProbabilityMeasure InfiniteGraph) =
      Graphon.ExchangeableGraphLaw.infiniteLaw (Graphon.sampleExchangeableLaw W) := by
    refine Graphon.ExchangeableGraphLaw.eq_infiniteLaw_of_map_restrictFin fun k => ?_
    show ((samplerSource μ).map (sampleInfinite W)).map (restrictFin k) =
      ((Graphon.sampleExchangeableLaw W).law k).toMeasure
    rw [Measure.map_map (measurable_restrictFin k) (measurable_sampleInfinite W),
      map_sampleInfinite_restrictFin W k]
    rfl
  exact congrArg
    (fun P : ProbabilityMeasure InfiniteGraph => (P : Measure InfiniteGraph)) hP

/-- Exchangeability of the sampler's law: free from `map_sampleInfinite`, since the
infinite law is invariant under every relabeling of `ℕ`. -/
theorem map_sampleInfinite_relabel (W : Graphon α μ) [IsProbabilityMeasure μ]
    (σ : Equiv.Perm ℕ) :
    ((samplerSource μ).map (sampleInfinite W)).map (relabel σ) =
      (samplerSource μ).map (sampleInfinite W) := by
  rw [map_sampleInfinite, Graphon.ExchangeableGraphLaw.infiniteLaw_map_relabel]

end Marginal

/-- The canonical-class form of the realization theorem: the sampler's law is the
canonical infinite law of the graphon class of `W`. -/
theorem map_sampleInfinite_eq_infiniteSampleLaw_mk {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]
    (W : Graphon α μ) :
    (samplerSource μ).map (sampleInfinite W) =
      (GraphonSpace.infiniteSampleLaw (GraphonSpace.mk W) :
        Measure InfiniteGraph) := by
  rw [map_sampleInfinite, GraphonSpace.infiniteSampleLaw_mk]

end InfiniteGraph
