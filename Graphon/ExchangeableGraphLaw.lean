/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.SamplingCoordinates

/-!
# Exchangeable graph laws and graphon mixtures (issue #33, foundations)

An exchangeable (infinite) random graph is presented by its consistent finite marginals —
deliberately avoiding laws on `SimpleGraph ℕ` (Mathlib's general Kolmogorov extension is
still unfinished; the consistent-finite-laws form captures the content cleanly):

* `Graphon.ExchangeableGraphLaw` — a family `law k : PMF (SimpleGraph (Fin k))`
  consistent under every injection of labels (which subsumes relabeling invariance);
* `Graphon.sampleExchangeableLaw` — the sample laws of a fixed graphon form an
  exchangeable graph law (`samplePMF_map_comap`);
* `GraphonSpace.mixturePMF` — the `k`-vertex marginal of a **graphon mixture**: the
  sample-law masses integrated against a probability measure on the graphon space;
* `GraphonSpace.mixturePMF_dirac` — a Dirac mixture recovers the sample law of the
  underlying graphon class;
* `GraphonSpace.mixtureExchangeableLaw` — every graphon mixture is exchangeable
  (`mixturePMF_map_comap`).

The Diaconis–Janson correspondence (issue #33) states the converse: every exchangeable
graph law is a **unique** graphon mixture. This file provides its objects and the easy
direction; the representation theorem itself is the campaign target.
-/

open MeasureTheory

open scoped ENNReal Classical

namespace Graphon

/-- **An exchangeable graph law**, presented by its consistent finite marginals: a
`k`-vertex law for every `k`, consistent under restriction along every injection of
labels. Arbitrary-injection consistency subsumes relabeling invariance (permutations are
injections). -/
structure ExchangeableGraphLaw where
  /-- The `k`-vertex marginal. -/
  law : ∀ k, PMF (SimpleGraph (Fin k))
  /-- Consistency under restriction along every injection of labels. -/
  consistent : ∀ {k l : ℕ} (e : Fin k ↪ Fin l),
    (law l).map (fun G => G.comap e) = law k

@[ext] theorem ExchangeableGraphLaw.ext {L M : ExchangeableGraphLaw}
    (h : ∀ k, L.law k = M.law k) : L = M := by
  cases L
  cases M
  simp only [ExchangeableGraphLaw.mk.injEq]
  exact funext h

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

omit [StandardBorelSpace α] [NoAtoms μ] in
/-- The sample laws of a fixed graphon form an exchangeable graph law. -/
noncomputable def sampleExchangeableLaw (W : Graphon α μ) : ExchangeableGraphLaw where
  law k := samplePMF W k
  consistent e := samplePMF_map_comap W e

omit [StandardBorelSpace α] [NoAtoms μ] in
@[simp] theorem sampleExchangeableLaw_law (W : Graphon α μ) (k : ℕ) :
    (sampleExchangeableLaw W).law k = samplePMF W k := rfl

end Graphon

namespace GraphonSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

/-- Each `ENNReal`-valued mass coordinate is measurable on the graphon space. -/
theorem measurable_finiteSampleLaw_apply (k : ℕ) (G : SimpleGraph (Fin k)) :
    Measurable fun x : GraphonSpace α μ => (finiteSampleLaw k x) G := by
  have h : (fun x : GraphonSpace α μ => (finiteSampleLaw k x) G) =
      fun x => ENNReal.ofReal (((finiteSampleLaw k x) G).toReal) := by
    funext x
    rw [ENNReal.ofReal_toReal ((finiteSampleLaw k x).apply_ne_top G)]
  rw [h]
  exact ENNReal.measurable_ofReal.comp
    (continuous_finiteSampleLaw_apply k G).measurable

/-- **The `k`-vertex marginal of a graphon mixture**: sample a graphon class from `P`,
then sample the `k`-vertex graph from it. The mass of `G` is the integral of the
sample-law masses against `P`. -/
noncomputable def mixturePMF (P : ProbabilityMeasure (GraphonSpace α μ)) (k : ℕ) :
    PMF (SimpleGraph (Fin k)) :=
  PMF.ofFintype
    (fun G => ∫⁻ x, (finiteSampleLaw k x) G ∂(P : Measure (GraphonSpace α μ)))
    (by
      rw [← MeasureTheory.lintegral_finsetSum _
        fun G _ => measurable_finiteSampleLaw_apply k G]
      have h1 : ∀ x : GraphonSpace α μ,
          ∑ G : SimpleGraph (Fin k), (finiteSampleLaw k x) G = 1 := by
        intro x
        have h := (finiteSampleLaw k x).tsum_coe
        rwa [tsum_fintype] at h
      calc ∫⁻ x, ∑ G : SimpleGraph (Fin k), (finiteSampleLaw k x) G
            ∂(P : Measure (GraphonSpace α μ))
          = ∫⁻ _, 1 ∂(P : Measure (GraphonSpace α μ)) := lintegral_congr h1
        _ = 1 := by rw [lintegral_one, measure_univ])

@[simp] theorem mixturePMF_apply (P : ProbabilityMeasure (GraphonSpace α μ)) (k : ℕ)
    (G : SimpleGraph (Fin k)) :
    mixturePMF P k G =
      ∫⁻ x, (finiteSampleLaw k x) G ∂(P : Measure (GraphonSpace α μ)) := rfl

/-- A Dirac mixture recovers the sample law of the underlying graphon class. -/
@[simp] theorem mixturePMF_dirac (x : GraphonSpace α μ) (k : ℕ) :
    mixturePMF ⟨Measure.dirac x, inferInstance⟩ k = finiteSampleLaw k x := by
  apply PMF.ext
  intro G
  rw [mixturePMF_apply]
  exact lintegral_dirac' x (measurable_finiteSampleLaw_apply k G)

/-- The mixture marginal masses are Bochner integrals of the scalar coordinates
`sampleMassCoord`. -/
theorem mixturePMF_apply_toReal (P : ProbabilityMeasure (GraphonSpace α μ)) (k : ℕ)
    (G : SimpleGraph (Fin k)) :
    (mixturePMF P k G).toReal =
      ∫ x, sampleMassCoord G x ∂(P : Measure (GraphonSpace α μ)) := by
  rw [mixturePMF_apply,
    ← MeasureTheory.integral_toReal (measurable_finiteSampleLaw_apply k G).aemeasurable
      (Filter.Eventually.of_forall fun x => (finiteSampleLaw k x).apply_lt_top G)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
    (sampleMassCoord_eq_toReal G x).symm)

/-- **The mixture coordinates are weakly continuous** in the mixing measure: the exact
interface for identifying Prokhorov limits (marginals of a weak limit are the limits of
the marginals). -/
theorem continuous_mixturePMF_apply_toReal (k : ℕ) (G : SimpleGraph (Fin k)) :
    Continuous fun P : ProbabilityMeasure (GraphonSpace α μ) =>
      (mixturePMF P k G).toReal := by
  have h : (fun P : ProbabilityMeasure (GraphonSpace α μ) => (mixturePMF P k G).toReal) =
      fun P : ProbabilityMeasure (GraphonSpace α μ) =>
        ∫ x, sampleMassCoord G x ∂(P : Measure (GraphonSpace α μ)) := by
    funext P
    exact mixturePMF_apply_toReal P k G
  rw [h]
  exact ProbabilityMeasure.continuous_integral_continuousMap
    (⟨sampleMassCoord G, continuous_sampleMassCoord G⟩ : C(GraphonSpace α μ, ℝ))

/-- **Graphon mixtures are exchangeable**: the mixture marginals are consistent under
every injection of labels. -/
theorem mixturePMF_map_comap (P : ProbabilityMeasure (GraphonSpace α μ))
    {k l : ℕ} (e : Fin k ↪ Fin l) :
    (mixturePMF P l).map (fun G => G.comap e) = mixturePMF P k := by
  apply PMF.ext
  intro G
  rw [PMF.map_apply, tsum_fintype]
  calc (∑ H : SimpleGraph (Fin l), if G = H.comap e then mixturePMF P l H else 0)
      = ∑ H : SimpleGraph (Fin l), ∫⁻ x,
          (if G = H.comap e then (finiteSampleLaw l x) H else 0)
          ∂(P : Measure (GraphonSpace α μ)) := by
        refine Finset.sum_congr rfl fun H _ => ?_
        split
        · rw [mixturePMF_apply]
        · rw [lintegral_zero]
    _ = ∫⁻ x, ∑ H : SimpleGraph (Fin l),
          (if G = H.comap e then (finiteSampleLaw l x) H else 0)
          ∂(P : Measure (GraphonSpace α μ)) := by
        rw [MeasureTheory.lintegral_finsetSum]
        intro H _
        split
        · exact measurable_finiteSampleLaw_apply l H
        · exact measurable_const
    _ = ∫⁻ x, ((finiteSampleLaw l x).map (fun G' => G'.comap e)) G
          ∂(P : Measure (GraphonSpace α μ)) := by
        refine lintegral_congr fun x => ?_
        rw [PMF.map_apply, tsum_fintype]
    _ = ∫⁻ x, (finiteSampleLaw k x) G ∂(P : Measure (GraphonSpace α μ)) := by
        refine lintegral_congr fun x => ?_
        rw [finiteSampleLaw_map_comap e x]
    _ = mixturePMF P k G := (mixturePMF_apply P k G).symm

/-- **Every graphon mixture is an exchangeable graph law** — the easy direction of the
Diaconis–Janson correspondence (issue #33: the representation theorem states that this
map from mixtures to exchangeable laws is a bijection). -/
noncomputable def mixtureExchangeableLaw (P : ProbabilityMeasure (GraphonSpace α μ)) :
    Graphon.ExchangeableGraphLaw where
  law k := mixturePMF P k
  consistent e := mixturePMF_map_comap P e

@[simp] theorem mixtureExchangeableLaw_law (P : ProbabilityMeasure (GraphonSpace α μ))
    (k : ℕ) : (mixtureExchangeableLaw P).law k = mixturePMF P k := rfl

end GraphonSpace
