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
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ]

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
  exact continuous_finsetSum _ fun S _ => continuous_const.mul (continuous_homDensity _)

end Graphon

namespace GraphonSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NullSingletonClass μ]

/-- **The scalar mass coordinate**: the probability that the `k`-vertex sample of a
graphon class equals `G`, as a real-valued function on the graphon space (`sampleMass`
descends through the quotient, well-defined by the joining theorem). -/
noncomputable def sampleMassCoord {k : ℕ} (G : SimpleGraph (Fin k)) :
    GraphonSpace α μ → ℝ :=
  SeparationQuotient.lift (fun W => Graphon.sampleMass W G) fun U W h => by
    have hpmf := (Graphon.samplePMF_eq_all_iff_weaklyIsomorphic U W).mpr
      (Metric.inseparable_iff.mp h) k
    have h2 := congrArg (fun p : PMF (SimpleGraph (Fin k)) => (p G).toReal) hpmf
    simpa only [Graphon.samplePMF_apply_toReal] using h2

@[simp] theorem sampleMassCoord_mk {k : ℕ} (G : SimpleGraph (Fin k)) (W : Graphon α μ) :
    sampleMassCoord G (mk W) = Graphon.sampleMass W G := rfl

theorem continuous_sampleMassCoord {k : ℕ} (G : SimpleGraph (Fin k)) :
    Continuous (sampleMassCoord (α := α) (μ := μ) G) :=
  SeparationQuotient.continuous_lift (Graphon.continuous_sampleMass G)

/-- **The `k`-vertex sample law as a coordinate on the graphon space**: `samplePMF`
descends through the quotient (well-defined by the joining theorem). The scalar
`sampleMassCoord` is its `toReal` mass; downstream topology uses the scalar form
(Mathlib gives `PMF` no topology). -/
noncomputable def finiteSampleLaw (k : ℕ) :
    GraphonSpace α μ → PMF (SimpleGraph (Fin k)) :=
  SeparationQuotient.lift (fun W => Graphon.samplePMF W k) fun U W h =>
    (Graphon.samplePMF_eq_all_iff_weaklyIsomorphic U W).mpr
      (Metric.inseparable_iff.mp h) k

@[simp] theorem finiteSampleLaw_mk (k : ℕ) (W : Graphon α μ) :
    finiteSampleLaw k (mk W) = Graphon.samplePMF W k := rfl

/-- The scalar coordinate is the `toReal` mass of the descended sample law. -/
theorem sampleMassCoord_eq_toReal {k : ℕ} (G : SimpleGraph (Fin k))
    (x : GraphonSpace α μ) :
    sampleMassCoord G x = ((finiteSampleLaw k x) G).toReal := by
  obtain ⟨W, rfl⟩ := surjective_mk x
  rw [sampleMassCoord_mk, finiteSampleLaw_mk, Graphon.samplePMF_apply_toReal]

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
  have h : (fun x : GraphonSpace α μ => ((finiteSampleLaw k x) G).toReal) =
      sampleMassCoord G := by
    funext x
    rw [sampleMassCoord_eq_toReal]
  rw [h]
  exact continuous_sampleMassCoord G

/-- The combined sample-law coordinates, into the product of finite real-valued
mass-function spaces. -/
noncomputable def sampleCoordinates (x : GraphonSpace α μ) :
    Π k : ℕ, SimpleGraph (Fin k) → ℝ :=
  fun _ G => sampleMassCoord G x

@[simp] theorem sampleCoordinates_apply (x : GraphonSpace α μ) (k : ℕ)
    (G : SimpleGraph (Fin k)) :
    sampleCoordinates x k G = sampleMassCoord G x := rfl

theorem continuous_sampleCoordinates :
    Continuous (sampleCoordinates : GraphonSpace α μ → Π k, SimpleGraph (Fin k) → ℝ) :=
  continuous_pi fun _ => continuous_pi fun G => continuous_sampleMassCoord G

theorem injective_sampleCoordinates :
    Function.Injective
      (sampleCoordinates : GraphonSpace α μ → Π k, SimpleGraph (Fin k) → ℝ) := by
  intro x y h
  rw [← finiteSampleLaw_eq_all_iff]
  intro k
  apply PMF.ext
  intro G
  have hG : sampleMassCoord G x = sampleMassCoord G y := congrFun (congrFun h k) G
  rw [sampleMassCoord_eq_toReal, sampleMassCoord_eq_toReal] at hG
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
  continuous_sampleCoordinates.isClosedEmbedding injective_sampleCoordinates

/-! ### The image lies in the consistent finite probability simplices -/

theorem sampleMassCoord_nonneg {k : ℕ} (G : SimpleGraph (Fin k))
    (x : GraphonSpace α μ) : 0 ≤ sampleMassCoord G x := by
  obtain ⟨W, rfl⟩ := surjective_mk x
  rw [sampleMassCoord_mk]
  exact Graphon.sampleMass_nonneg W G

theorem sum_sampleMassCoord (k : ℕ) (x : GraphonSpace α μ) :
    ∑ G : SimpleGraph (Fin k), sampleMassCoord G x = 1 := by
  obtain ⟨W, rfl⟩ := surjective_mk x
  simp only [sampleMassCoord_mk]
  exact Graphon.sampleMass_sum_eq_one W

/-- Injection consistency of the sample-law coordinates (descends
`samplePMF_map_comap` through the quotient). -/
theorem finiteSampleLaw_map_comap {k l : ℕ} (e : Fin k ↪ Fin l) (x : GraphonSpace α μ) :
    (finiteSampleLaw l x).map (fun G => G.comap e) = finiteSampleLaw k x := by
  obtain ⟨W, rfl⟩ := surjective_mk x
  simp only [finiteSampleLaw_mk]
  exact Graphon.samplePMF_map_comap W e

/-- Scalar form of injection consistency: the coordinates satisfy the marginal
equations of a consistent family. -/
theorem sum_sampleMassCoord_comap {k l : ℕ} (e : Fin k ↪ Fin l)
    (G : SimpleGraph (Fin k)) (x : GraphonSpace α μ) :
    (∑ H : SimpleGraph (Fin l), if G = H.comap e then sampleMassCoord H x else 0) =
      sampleMassCoord G x := by
  classical
  have h := congrArg (fun p : PMF (SimpleGraph (Fin k)) => (p G).toReal)
    (finiteSampleLaw_map_comap e x)
  rw [PMF.map_apply, tsum_fintype] at h
  rw [sampleMassCoord_eq_toReal, ← h,
    ENNReal.toReal_sum fun H _ => by
      split
      exacts [(finiteSampleLaw l x).apply_ne_top H, ENNReal.zero_ne_top]]
  refine Finset.sum_congr rfl fun H _ => ?_
  split
  · rw [sampleMassCoord_eq_toReal]
  · exact ENNReal.toReal_zero

end GraphonSpace
