/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.SamplingDetermination

/-!
# Continuous finite-law coordinates on the graphon space (issue #32)

The finite sample laws descend to point-separating continuous coordinates on the compact
graphon space, giving a compact coordinate embedding into the product of finite
mass-function spaces — the Lovász-style bridge toward exchangeable infinite graph laws:

* `Graphon.lipschitzWith_homDensity` / `Graphon.continuous_homDensity` — each
  homomorphism density is `e(F)`-Lipschitz in cut distance (the counting lemma
  `homDensity_sub_le_of_cutDistance`), hence continuous on raw graphons;
* `Graphon.continuous_sampleMass` — each singleton sample mass is a finite signed
  combination of homomorphism densities (`sampleMass_eq_sum_homDensity`), hence
  continuous;
* `GraphonSpace.finiteSampleLaw` — the `k`-vertex sample law descends through the
  quotient (well-defined by the joining theorem);
* `GraphonSpace.finiteSampleLaw_eq_all_iff` — the coordinates separate points;
* `GraphonSpace.isClosedEmbedding_sampleCoordinates` — the combined coordinates are a
  closed embedding of the compact graphon space into `Π k, SimpleGraph (Fin k) → ℝ`.

(`PMF` carries no topology in Mathlib, so continuity statements are coordinatewise via
`toReal` masses, and the embedding lands in real-valued mass functions.)
-/

open MeasureTheory

open scoped Classical

namespace Graphon

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

/-- `dist` on raw graphons is the cut distance (definitional unfolding of
`Graphon.instPseudoMetricSpace`). -/
theorem dist_eq_cutDistance (U W : Graphon α μ) : dist U W = cutDistance U W := rfl

/-- Each homomorphism density is `e(F)`-Lipschitz in cut distance (counting lemma). -/
theorem lipschitzWith_homDensity {V : Type*} [Fintype V] (F : SimpleGraph V)
    [DecidableRel F.Adj] :
    LipschitzWith F.edgeFinset.card (fun W : Graphon α μ => homDensity F W) :=
  LipschitzWith.of_dist_le_mul fun U W => by
    rw [Real.dist_eq, dist_eq_cutDistance]
    exact_mod_cast homDensity_sub_le_of_cutDistance F U W

/-- Each homomorphism density is continuous on raw graphons. -/
theorem continuous_homDensity {V : Type*} [Fintype V] (F : SimpleGraph V)
    [DecidableRel F.Adj] :
    Continuous fun W : Graphon α μ => homDensity F W :=
  (lipschitzWith_homDensity F).continuous

/-- Each singleton sample mass is continuous on raw graphons: it is a finite signed
combination of homomorphism densities. -/
theorem continuous_sampleMass {k : ℕ} (G : SimpleGraph (Fin k)) :
    Continuous fun W : Graphon α μ => sampleMass W G := by
  have h : (fun W : Graphon α μ => sampleMass W G) = fun W =>
      ∑ S ∈ ((⊤ : SimpleGraph (Fin k)).edgeFinset \ G.edgeFinset).powerset,
        (-1 : ℝ) ^ S.card *
          homDensity
            (SimpleGraph.fromEdgeSet (↑(G.edgeFinset ∪ S) : Set (Sym2 (Fin k)))) W := by
    funext W
    exact sampleMass_eq_sum_homDensity W G
  rw [h]
  exact continuous_finset_sum _ fun S _ => continuous_const.mul (continuous_homDensity _)

end Graphon

namespace GraphonSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

/-- **The `k`-vertex sample law as a coordinate on the graphon space**: `samplePMF`
descends through the separation quotient, well-defined by the joining theorem. -/
noncomputable def finiteSampleLaw (k : ℕ) :
    GraphonSpace α μ → PMF (SimpleGraph (Fin k)) :=
  SeparationQuotient.lift (fun W => Graphon.samplePMF W k) fun U W h =>
    (Graphon.samplePMF_eq_all_iff_weaklyIsomorphic U W).mpr
      (Metric.inseparable_iff.mp h) k

@[simp] theorem finiteSampleLaw_mk (k : ℕ) (W : Graphon α μ) :
    finiteSampleLaw k (mk W) = Graphon.samplePMF W k := rfl

/-- **The sample-law coordinates separate points** of the graphon space. -/
theorem finiteSampleLaw_eq_all_iff {x y : GraphonSpace α μ} :
    (∀ k, finiteSampleLaw k x = finiteSampleLaw k y) ↔ x = y := by
  obtain ⟨U, rfl⟩ := surjective_mk x
  obtain ⟨W, rfl⟩ := surjective_mk y
  simp only [finiteSampleLaw_mk]
  exact Graphon.samplePMF_eq_all_iff_mk_eq_mk U W

/-- Each mass coordinate of each finite sample law is continuous on the graphon space. -/
theorem continuous_finiteSampleLaw_apply (k : ℕ) (G : SimpleGraph (Fin k)) :
    Continuous fun x : GraphonSpace α μ => ((finiteSampleLaw k x) G).toReal := by
  rw [SeparationQuotient.isQuotientMap_mk.continuous_iff]
  have h : ((fun x : GraphonSpace α μ => ((finiteSampleLaw k x) G).toReal) ∘
      SeparationQuotient.mk) = fun W : Graphon α μ => Graphon.sampleMass W G := by
    funext W
    exact Graphon.samplePMF_apply_toReal W k G
  rw [h]
  exact Graphon.continuous_sampleMass G

/-- The combined sample-law coordinates, into the product of finite real-valued
mass-function spaces. -/
noncomputable def sampleCoordinates (x : GraphonSpace α μ) :
    Π k : ℕ, SimpleGraph (Fin k) → ℝ :=
  fun k G => ((finiteSampleLaw k x) G).toReal

theorem continuous_sampleCoordinates :
    Continuous (sampleCoordinates : GraphonSpace α μ → Π k, SimpleGraph (Fin k) → ℝ) :=
  continuous_pi fun k => continuous_pi fun G => continuous_finiteSampleLaw_apply k G

theorem sampleCoordinates_injective :
    Function.Injective (sampleCoordinates : GraphonSpace α μ → Π k, SimpleGraph (Fin k) → ℝ) := by
  intro x y h
  rw [← finiteSampleLaw_eq_all_iff]
  intro k
  apply PMF.ext
  intro G
  have hG : ((finiteSampleLaw k x) G).toReal = ((finiteSampleLaw k y) G).toReal :=
    congrFun (congrFun h k) G
  exact (ENNReal.toReal_eq_toReal_iff' ((finiteSampleLaw k x).apply_ne_top G)
    ((finiteSampleLaw k y).apply_ne_top G)).mp hG

/-- **Compact coordinate embedding** (Lovász-style): the sample-law coordinates embed
the compact graphon space homeomorphically onto a closed subset of the product of finite
mass-function spaces — a continuous injection from a compact space into a Hausdorff
space. -/
@[blueprint "thm:sample-coordinate-embedding"
  (title := /-- Compact coordinate embedding of the graphon space -/)]
theorem isClosedEmbedding_sampleCoordinates :
    Topology.IsClosedEmbedding
      (sampleCoordinates : GraphonSpace α μ → Π k, SimpleGraph (Fin k) → ℝ) :=
  continuous_sampleCoordinates.isClosedEmbedding sampleCoordinates_injective

end GraphonSpace
