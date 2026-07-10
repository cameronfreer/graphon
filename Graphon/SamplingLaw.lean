/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Sampling
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.SimpleGraph

/-!
# The finite sample law of a graphon (S2)

Bundles the sampled-graph masses `sampleMass` (`Graphon/Sampling.lean`) into a finite
probability law and develops its algebraic API (issues #20 and #22; route vetted
2026-07-10):

* `Graphon.upperSum` / `Graphon.upperSum_injective` — the finite zeta/upper transform on
  `SimpleGraph (Fin k)` and its injectivity via Möbius inversion
  (`IncidenceAlgebra.moebius_inversion_top`). Together with the forward identity
  `homDensity_eq_sum_sampleMass`, this is the engine for every consistency statement
  below: two mass functions agree as soon as their supergraph sums agree.
* `SimpleGraph.relabelOrderIso` — relabeling by a permutation as an order isomorphism.
* `Graphon.sampleMass_map_perm` — relabeling invariance of the sample mass, proved by
  the upper-sum route (the direct inclusion–exclusion proof hits `edgeFinset`
  decidability-instance diamonds and is deliberately avoided).

This file deliberately lives above `Graphon/Sampling.lean` so that the incidence-algebra
and PMF imports stay out of the foundational sampling module.
-/

open MeasureTheory Set Filter Finset

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ### SimpleGraph relabeling plumbing (Mathlib candidates) -/

namespace SimpleGraph

private theorem map_perm_symm {V : Type*} (G : SimpleGraph V) (σ : Equiv.Perm V) :
    (G.map σ.toEmbedding).map σ.symm.toEmbedding = G := by
  rw [map_map]
  have hf : (⇑σ.symm.toEmbedding ∘ ⇑σ.toEmbedding : V → V) = id := by
    funext x
    exact σ.symm_apply_apply x
  rw [hf, map_id]

/-- Relabeling the vertices of simple graphs by a permutation, as an order isomorphism
of the subgraph lattice. -/
def relabelOrderIso {V : Type*} (σ : Equiv.Perm V) :
    SimpleGraph V ≃o SimpleGraph V where
  toFun G := G.map σ.toEmbedding
  invFun G := G.map σ.symm.toEmbedding
  left_inv G := map_perm_symm G σ
  right_inv G := by
    simpa only [Equiv.symm_symm] using map_perm_symm G σ.symm
  map_rel_iff' := by
    intro G H
    change G.map σ.toEmbedding ≤ H.map σ.toEmbedding ↔ G ≤ H
    constructor
    · intro h
      have hm := map_monotone (⇑σ.symm.toEmbedding) h
      rwa [map_perm_symm, map_perm_symm] at hm
    · exact fun h ↦ map_monotone (⇑σ.toEmbedding) h

end SimpleGraph

namespace Graphon

/-! ### The upper transform and its injectivity -/

section UpperSum

variable {k : ℕ}

open scoped Classical in
/-- The finite zeta/upper transform of a mass function on `SimpleGraph (Fin k)`: the
total mass of the supergraphs of `F`. By `homDensity_eq_sum_sampleMass`, the upper
transform of `sampleMass W` is `homDensity · W`. -/
noncomputable def upperSum (p : SimpleGraph (Fin k) → ℝ) (F : SimpleGraph (Fin k)) : ℝ :=
  ∑ G : SimpleGraph (Fin k), if F ≤ G then p G else 0

/-- **Injectivity of the upper transform** (Möbius inversion over the finite subgraph
lattice): a mass function on `SimpleGraph (Fin k)` is determined by its supergraph
sums. -/
theorem upperSum_injective {p q : SimpleGraph (Fin k) → ℝ}
    (h : ∀ F, upperSum p F = upperSum q F) : p = q := by
  classical
  letI : LocallyFiniteOrder (SimpleGraph (Fin k)) :=
    Fintype.toLocallyFiniteOrder
  have hUpper (r : SimpleGraph (Fin k) → ℝ) (F : SimpleGraph (Fin k)) :
      (∑ H ∈ Finset.Ici F, r H) = upperSum r F := by
    have hIci :
        Finset.Ici F =
          Finset.univ.filter (fun H : SimpleGraph (Fin k) => F ≤ H) := by
      ext H
      simp
    rw [hIci, upperSum, Finset.sum_filter]
  funext G
  have hp := IncidenceAlgebra.moebius_inversion_top
    p (fun F => ∑ H ∈ Finset.Ici F, p H) (fun _ => rfl) G
  have hq := IncidenceAlgebra.moebius_inversion_top
    q (fun F => ∑ H ∈ Finset.Ici F, q H) (fun _ => rfl) G
  rw [hp, hq]
  apply Finset.sum_congr rfl
  intro F hF
  congr 1
  rw [hUpper, hUpper]
  exact h F

end UpperSum

/-! ### Relabeling invariance of the sample mass -/

section Relabel

variable [IsProbabilityMeasure μ] {k : ℕ}

open scoped Classical

/-- Classical-instance core of `upperSum_sampleMass`. -/
private theorem upperSum_sampleMass_classical (W : Graphon α μ) (F : SimpleGraph (Fin k)) :
    upperSum (sampleMass W) F = homDensity F W := by
  rw [upperSum]
  exact (homDensity_eq_sum_sampleMass W F).symm

/-- The upper transform of the sample mass is the homomorphism density: the forward
Möbius identity, restated through `upperSum`. Accepts an ambient `[DecidableRel F.Adj]`
(bridged to the classical core by `homDensity_congr_decRel`). -/
theorem upperSum_sampleMass (W : Graphon α μ) (F : SimpleGraph (Fin k))
    [DecidableRel F.Adj] :
    upperSum (sampleMass W) F = homDensity F W :=
  (upperSum_sampleMass_classical W F).trans (homDensity_congr_decRel F _ _ W)

section
-- Scoped to `sampleMass_map_perm` only: the `relabelOrderIso`/`homDensity` instance
-- unification in the calc below exceeds the default heartbeat budget.
set_option maxHeartbeats 1600000

/-- **Relabeling invariance of the sample mass**: the law of the `W`-random graph is
invariant under vertex permutations. Proved by the upper-sum route: the upper transform
of the relabeled mass reindexes along `SimpleGraph.relabelOrderIso σ` to
`homDensity (F.map σ) W`, which is `homDensity F W` by `homDensity_map_embedding`;
`upperSum_injective` finishes. -/
theorem sampleMass_map_perm (W : Graphon α μ) (σ : Equiv.Perm (Fin k))
    (G : SimpleGraph (Fin k)) :
    sampleMass W (G.map σ.toEmbedding) = sampleMass W G := by
  set e := SimpleGraph.relabelOrderIso σ with he
  have key : (fun G => sampleMass W (e G)) = sampleMass W := by
    apply upperSum_injective
    intro F
    have hre : upperSum (fun G => sampleMass W (e G)) F =
        upperSum (sampleMass W) (e F) := by
      rw [upperSum, upperSum,
        ← Equiv.sum_comp e.toEquiv (fun H => if e F ≤ H then sampleMass W H else 0)]
      refine Finset.sum_congr rfl fun G _ => ?_
      exact if_congr e.le_iff_le.symm rfl rfl
    calc upperSum (fun G => sampleMass W (e G)) F
        = upperSum (sampleMass W) (e F) := hre
      _ = homDensity (e F) W := upperSum_sampleMass_classical W (e F)
      _ = homDensity F W :=
          (homDensity_congr_decRel (e F) _ _ W).trans
            (homDensity_map_embedding F σ.toEmbedding W)
      _ = upperSum (sampleMass W) F := (upperSum_sampleMass_classical W F).symm
  exact congrFun key G

end

end Relabel

end Graphon

/-! ### Measurable-space plumbing for simple graphs (Mathlib candidates) -/

namespace SimpleGraph

/-- The canonical measurable space on `SimpleGraph V` is discrete for countable `V`:
singletons are measurable. (Mathlib supplies the measurable space in
`Mathlib.MeasureTheory.Constructions.SimpleGraph` but not this instance.) -/
instance {V : Type*} [Countable V] :
    MeasurableSingletonClass (SimpleGraph V) where
  measurableSet_singleton G := by
    have h : MeasurableSet ({G.edgeSet} : Set (Set (Sym2 V))) :=
      MeasurableSet.singleton G.edgeSet
    have hp := h.preimage measurable_edgeSet
    convert hp using 1
    ext H
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact edgeSet_injective.eq_iff.symm

theorem measurable_comap {V W : Type*} (f : V → W) :
    Measurable (fun G : SimpleGraph W ↦ G.comap f) := by
  rw [measurable_iff_adj]
  intro u v
  simp only [comap_adj]
  fun_prop

theorem measurable_map_equiv {V W : Type*} (e : V ≃ W) :
    Measurable (fun G : SimpleGraph V ↦ G.map e.toEmbedding) := by
  simp_rw [← comap_symm]
  exact measurable_comap e.symm

end SimpleGraph

namespace Graphon

/-! ### The bundled sample law -/

section Law

variable [IsProbabilityMeasure μ] {k : ℕ}

/-- **The finite sample law of a graphon, as a PMF**: the distribution of the `W`-random
graph `G(k, W)` on `SimpleGraph (Fin k)` (`PMF.ofFintype` over `sampleMass`; the masses
are nonnegative and sum to one). The PMF is the finite algebraic API; `sampleLaw` below
is its thin measurable wrapper. -/
noncomputable def samplePMF (W : Graphon α μ) (k : ℕ) : PMF (SimpleGraph (Fin k)) :=
  PMF.ofFintype (fun G ↦ ENNReal.ofReal (sampleMass W G)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun G _ ↦ sampleMass_nonneg W G),
      sampleMass_sum_eq_one, ENNReal.ofReal_one])

@[simp] theorem samplePMF_apply (W : Graphon α μ) (k : ℕ) (G : SimpleGraph (Fin k)) :
    samplePMF W k G = ENNReal.ofReal (sampleMass W G) := rfl

/-- Point mass of the sample PMF as a real number. Composed with
`sampleMass_eq_sum_homDensity` (`Graphon/Sampling.lean`), this IS the reverse
Möbius/inclusion–exclusion identity at the PMF level — the intended API for expanding
PMF point masses into signed homomorphism densities (#22). -/
@[simp] theorem samplePMF_apply_toReal (W : Graphon α μ) (k : ℕ)
    (G : SimpleGraph (Fin k)) :
    (samplePMF W k G).toReal = sampleMass W G := by
  rw [samplePMF_apply, ENNReal.toReal_ofReal (sampleMass_nonneg W G)]

/-- **The finite sample law of a graphon, as a probability measure** on the canonical
measurable space of `SimpleGraph (Fin k)`. -/
noncomputable def sampleLaw (W : Graphon α μ) (k : ℕ) :
    ProbabilityMeasure (SimpleGraph (Fin k)) :=
  ⟨(samplePMF W k).toMeasure, inferInstance⟩

@[simp] theorem sampleLaw_singleton (W : Graphon α μ) (k : ℕ)
    (G : SimpleGraph (Fin k)) :
    (sampleLaw W k : Measure (SimpleGraph (Fin k))) {G}
      = ENNReal.ofReal (sampleMass W G) := by
  rw [sampleLaw, ProbabilityMeasure.coe_mk, PMF.toMeasure_apply_singleton,
    samplePMF_apply]
  exact MeasurableSet.singleton G

@[simp] theorem sampleLaw_singleton_toReal (W : Graphon α μ) (k : ℕ)
    (G : SimpleGraph (Fin k)) :
    ((sampleLaw W k : Measure (SimpleGraph (Fin k))) {G}).toReal =
      sampleMass W G := by
  rw [sampleLaw_singleton, ENNReal.toReal_ofReal (sampleMass_nonneg W G)]

end Law

/-! ### Relabeling and arbitrary-injection consistency of the sample law -/

section Consistency

variable [IsProbabilityMeasure μ] {k l : ℕ}

open scoped Classical

/-- PMF extensionality through the upper transform: two PMFs on `SimpleGraph (Fin k)`
agree as soon as all their supergraph masses agree. -/
theorem pmf_ext_of_upperSum {p q : PMF (SimpleGraph (Fin k))}
    (h : ∀ F, upperSum (fun G => (p G).toReal) F =
      upperSum (fun G => (q G).toReal) F) : p = q := by
  apply PMF.ext
  intro G
  exact (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top G) (q.apply_ne_top G)).mp
    (congrFun (upperSum_injective h) G)

/-- Normalization of the upper transform of a mapped PMF: pull the pushforward inside
the sum. -/
private theorem upperSum_pmf_map (f : SimpleGraph (Fin l) → SimpleGraph (Fin k))
    (p : PMF (SimpleGraph (Fin l))) (F : SimpleGraph (Fin k)) :
    upperSum (fun G => ((p.map f) G).toReal) F =
      ∑ H : SimpleGraph (Fin l), if F ≤ f H then (p H).toReal else 0 := by
  have hmap : ∀ G, ((p.map f) G).toReal =
      ∑ H : SimpleGraph (Fin l), if G = f H then (p H).toReal else 0 := by
    intro G
    have hfin : ∀ H ∈ Finset.univ, (if G = f H then p H else 0) ≠ (⊤ : ℝ≥0∞) := by
      intro H _
      split
      exacts [p.apply_ne_top H, ENNReal.zero_ne_top]
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum hfin]
    exact Finset.sum_congr rfl fun H _ => by split <;> simp
  have hcollapse : ∀ H : SimpleGraph (Fin l),
      (∑ G : SimpleGraph (Fin k),
        if F ≤ G then (if G = f H then (p H).toReal else 0) else 0) =
      if F ≤ f H then (p H).toReal else 0 := by
    intro H
    have hswap : ∀ G : SimpleGraph (Fin k),
        (if F ≤ G then (if G = f H then (p H).toReal else 0) else 0) =
        if G = f H then (if F ≤ f H then (p H).toReal else 0) else 0 := by
      intro G
      by_cases h1 : G = f H
      · subst h1; simp
      · simp [h1]
    rw [Finset.sum_congr rfl fun G _ => hswap G]
    exact Finset.sum_ite_eq' Finset.univ (f H) _ |>.trans (if_pos (Finset.mem_univ _))
  calc upperSum (fun G => ((p.map f) G).toReal) F
      = ∑ G : SimpleGraph (Fin k), if F ≤ G then
          (∑ H : SimpleGraph (Fin l), if G = f H then (p H).toReal else 0) else 0 := by
        rw [upperSum]; exact Finset.sum_congr rfl fun G _ => by rw [hmap]
    _ = ∑ G : SimpleGraph (Fin k), ∑ H : SimpleGraph (Fin l),
          if F ≤ G then (if G = f H then (p H).toReal else 0) else 0 := by
        refine Finset.sum_congr rfl fun G _ => ?_
        split <;> simp
    _ = ∑ H : SimpleGraph (Fin l), ∑ G : SimpleGraph (Fin k),
          if F ≤ G then (if G = f H then (p H).toReal else 0) else 0 := Finset.sum_comm
    _ = ∑ H : SimpleGraph (Fin l), if F ≤ f H then (p H).toReal else 0 :=
        Finset.sum_congr rfl fun H _ => hcollapse H

/-- Classical-instance core of `upperSum_samplePMF`. -/
private theorem upperSum_samplePMF_classical (W : Graphon α μ) (F : SimpleGraph (Fin k)) :
    upperSum (fun G => (samplePMF W k G).toReal) F = homDensity F W := by
  have hfun : (fun G : SimpleGraph (Fin k) => (samplePMF W k G).toReal) = sampleMass W :=
    funext fun G => samplePMF_apply_toReal W k G
  rw [hfun, upperSum_sampleMass_classical]

/-- The upper mass of the sample PMF is the homomorphism density. Accepts an ambient
`[DecidableRel F.Adj]`. -/
theorem upperSum_samplePMF (W : Graphon α μ) (F : SimpleGraph (Fin k))
    [DecidableRel F.Adj] :
    upperSum (fun G => (samplePMF W k G).toReal) F = homDensity F W :=
  (upperSum_samplePMF_classical W F).trans (homDensity_congr_decRel F _ _ W)

/-- **Arbitrary-injection consistency of the sample law**: restricting the `l`-vertex
`W`-random graph along any injection `Fin k ↪ Fin l` yields the `k`-vertex `W`-random
graph. (Prefix restriction and relabeling-compatible restrictions are special cases.)
Proof: upper masses of both sides are `homDensity F W`, via the Galois connection
`map_le_iff_le_comap` and `homDensity_map_embedding`; `upperSum_injective` finishes. -/
theorem samplePMF_map_comap (W : Graphon α μ) (e : Fin k ↪ Fin l) :
    (samplePMF W l).map (fun H => H.comap e) = samplePMF W k := by
  apply pmf_ext_of_upperSum
  intro F
  rw [upperSum_pmf_map]
  have h1 : (∑ H : SimpleGraph (Fin l),
        if F ≤ H.comap e then (samplePMF W l H).toReal else 0)
      = upperSum (fun H => (samplePMF W l H).toReal) (F.map e) := by
    rw [upperSum]
    exact Finset.sum_congr rfl fun H _ =>
      if_congr (SimpleGraph.map_le_iff_le_comap e F H).symm rfl rfl
  rw [h1, upperSum_samplePMF_classical, upperSum_samplePMF_classical]
  exact (homDensity_congr_decRel (F.map e) _ _ W).trans
    (homDensity_map_embedding F e W)

/-- **Relabeling invariance of the sample law** (PMF form). -/
theorem samplePMF_map_relabel (W : Graphon α μ) (σ : Equiv.Perm (Fin k)) :
    (samplePMF W k).map (fun G => G.map σ.toEmbedding) = samplePMF W k := by
  have hfun : (fun G : SimpleGraph (Fin k) => G.comap σ.symm.toEmbedding) =
      (fun G => G.map σ.toEmbedding) :=
    funext fun G => SimpleGraph.comap_symm G σ
  rw [← hfun]
  exact samplePMF_map_comap W σ.symm.toEmbedding

/-- Arbitrary-injection consistency, measure form. -/
theorem sampleLaw_map_comap (W : Graphon α μ) (e : Fin k ↪ Fin l) :
    (sampleLaw W l : Measure (SimpleGraph (Fin l))).map (fun H => H.comap e) =
      (sampleLaw W k : Measure (SimpleGraph (Fin k))) := by
  rw [sampleLaw, sampleLaw, ProbabilityMeasure.coe_mk, ProbabilityMeasure.coe_mk,
    PMF.toMeasure_map _ _ (SimpleGraph.measurable_comap ⇑e), samplePMF_map_comap]

/-- Relabeling invariance, measure form. -/
theorem sampleLaw_map_relabel (W : Graphon α μ) (σ : Equiv.Perm (Fin k)) :
    (sampleLaw W k : Measure (SimpleGraph (Fin k))).map (fun G => G.map σ.toEmbedding) =
      (sampleLaw W k : Measure (SimpleGraph (Fin k))) := by
  rw [sampleLaw, ProbabilityMeasure.coe_mk,
    PMF.toMeasure_map _ _ (SimpleGraph.measurable_map_equiv σ), samplePMF_map_relabel]

end Consistency

end Graphon
