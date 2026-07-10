/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
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

/-- The upper transform of the sample mass is the homomorphism density: the forward
Möbius identity, restated through `upperSum`. -/
theorem upperSum_sampleMass (W : Graphon α μ) (F : SimpleGraph (Fin k)) :
    upperSum (sampleMass W) F = homDensity F W := by
  rw [upperSum]
  exact (homDensity_eq_sum_sampleMass W F).symm

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
      _ = homDensity (e F) W := upperSum_sampleMass W (e F)
      _ = homDensity F W :=
          (homDensity_congr_decRel (e F) _ _ W).trans
            (homDensity_map_embedding F σ.toEmbedding W)
      _ = upperSum (sampleMass W) F := (upperSum_sampleMass W F).symm
  exact congrFun key G

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

end Graphon
