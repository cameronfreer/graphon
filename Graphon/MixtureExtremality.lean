/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Mathlib.MeasureTheory.Measure.DiracProba
import Graphon.MixtureRepresentation

/-!
# Extremality: dissociated exchangeable laws are the Dirac mixtures (issue #33)

The Diaconis–Janson extremality criterion (their Theorem 5.5), via upper-event
factorization:

* `Graphon.ExchangeableGraphLaw.upperMass` — the total mass of the supergraphs of `F`
  under the `k`-vertex marginal;
* `Graphon.ExchangeableGraphLaw.IsDissociated` — upper events on disjoint vertex blocks
  are independent (cross-block edges remain unrestricted);
* `GraphonSpace.isDissociated_mixtureExchangeableLaw_iff` — **a graphon mixture is
  dissociated iff the mixing measure is a Dirac**. Dissociation applied to two copies of
  `F` says every hom-density coordinate has second moment equal to its squared mean, so
  each coordinate is a.s. constant; a countable intersection and point separation of the
  coordinates collapse the mixing measure to a point.
* `GraphonSpace.isDissociated_sampleExchangeableLaw` — the exchangeable law of a fixed
  graphon is dissociated (it is the Dirac mixture at its class).

This proves the extremality criterion without formalizing the convex extreme-point
structure itself.
-/

open MeasureTheory

open scoped Classical

namespace Graphon.ExchangeableGraphLaw

/-- **The upper mass** of a finite graph under an exchangeable law: the total mass of
the supergraphs of `F` under the `k`-vertex marginal. -/
noncomputable def upperMass (L : Graphon.ExchangeableGraphLaw) {k : ℕ}
    (F : SimpleGraph (Fin k)) : ℝ :=
  Graphon.upperSum (fun G => (L.law k G).toReal) F

/-- **Dissociated exchangeable laws**: upper events on disjoint vertex blocks are
independent (Diaconis–Janson Theorem 5.5 criterion; cross-block edges remain
unrestricted). -/
def IsDissociated (L : Graphon.ExchangeableGraphLaw) : Prop :=
  ∀ {k l : ℕ} (F : SimpleGraph (Fin k)) (H : SimpleGraph (Fin l)),
    L.upperMass ((F ⊕g H).map finSumFinEquiv.toEmbedding) =
      L.upperMass F * L.upperMass H

end Graphon.ExchangeableGraphLaw

namespace GraphonSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

/-- Pointwise disjoint-union multiplicativity of the hom-density coordinates
(`homDensity_sum_finAdd`, descended through the quotient). -/
private theorem homDensityCoord_sum_finAdd {k l : ℕ} (F : SimpleGraph (Fin k))
    (H : SimpleGraph (Fin l)) (x : GraphonSpace α μ) :
    homDensityCoord ((F ⊕g H).map finSumFinEquiv.toEmbedding) x =
      homDensityCoord F x * homDensityCoord H x := by
  obtain ⟨W, rfl⟩ := surjective_mk x
  simp only [homDensityCoord_mk]
  exact (Graphon.homDensity_congr_decRel _ _ _ W).trans
    (Graphon.homDensity_sum_finAdd F H W)

/-- The upper mass of a graphon mixture is the integral of the corresponding
hom-density coordinate against the mixing measure. -/
theorem upperMass_mixtureExchangeableLaw (P : ProbabilityMeasure (GraphonSpace α μ))
    {k : ℕ} (F : SimpleGraph (Fin k)) :
    (mixtureExchangeableLaw P).upperMass F =
      ∫ x, homDensityCoord F x ∂(P : Measure (GraphonSpace α μ)) := by
  rw [integral_homDensityCoord P F]
  simp only [Graphon.ExchangeableGraphLaw.upperMass, Graphon.upperSum,
    mixtureExchangeableLaw_law]

/-- A real function whose second moment equals its squared mean is a.e. equal to its
mean (zero-variance rigidity, in the elementary `∫ (f − c)² = 0` form). -/
private theorem ae_eq_integral_of_integral_mul_self_eq {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {f : Ω → ℝ} (hf : Integrable f ν)
    (hf2 : Integrable (fun x => f x * f x) ν)
    (h : ∫ x, f x * f x ∂ν = (∫ x, f x ∂ν) * ∫ x, f x ∂ν) :
    ∀ᵐ x ∂ν, f x = ∫ y, f y ∂ν := by
  set c := ∫ x, f x ∂ν with hc
  have hexp : (fun x => (f x - c) ^ 2) =
      fun x => f x * f x - 2 * c * f x + c * c := funext fun x => by ring
  have hint : Integrable (fun x => (f x - c) ^ 2) ν := by
    rw [hexp]
    exact (hf2.sub (hf.const_mul (2 * c))).add (integrable_const _)
  have hzero : ∫ x, (f x - c) ^ 2 ∂ν = 0 := by
    rw [hexp, integral_add
        (show Integrable (fun x => f x * f x - 2 * c * f x) ν from
          hf2.sub (hf.const_mul (2 * c)))
        (integrable_const _),
      integral_sub hf2 (hf.const_mul (2 * c)), integral_const_mul, h, ← hc,
      integral_const, probReal_univ, one_smul]
    ring
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun x => sq_nonneg (f x - c)) hint).mp hzero
  filter_upwards [hae] with x hx
  have hx0 : (f x - c) ^ 2 = 0 := hx
  exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hx0)

/-- **Diaconis–Janson extremality** (their Theorem 5.5): a graphon mixture is
dissociated iff the mixing measure is a Dirac. Dissociation at two copies of `F` makes
every hom-density coordinate a.s. constant; point separation of the coordinates then
collapses the mixing measure to a point. -/
@[blueprint "thm:mixture-extremality"
  (title := /-- Dissociated laws are the Dirac mixtures -/)]
theorem isDissociated_mixtureExchangeableLaw_iff
    (P : ProbabilityMeasure (GraphonSpace α μ)) :
    (mixtureExchangeableLaw P).IsDissociated ↔ ∃ x, P = diracProba x := by
  constructor
  · intro hdiss
    -- every hom-density coordinate is a.s. its mean
    have hconst : ∀ (k : ℕ) (F : SimpleGraph (Fin k)),
        ∀ᵐ x ∂(P : Measure (GraphonSpace α μ)), homDensityCoord F x =
          ∫ y, homDensityCoord F y ∂(P : Measure (GraphonSpace α μ)) := by
      intro k F
      have hFF := hdiss F F
      simp only [upperMass_mixtureExchangeableLaw] at hFF
      rw [integral_congr_ae (Filter.Eventually.of_forall
        (fun x => homDensityCoord_sum_finAdd F F x))] at hFF
      exact ae_eq_integral_of_integral_mul_self_eq
        ((homDensityCoordBCF (α := α) (μ := μ) F).integrable _)
        (by simpa using (homDensityCoordBCF (α := α) (μ := μ) F *
          homDensityCoordBCF F).integrable (P : Measure (GraphonSpace α μ)))
        hFF
    have hae : ∀ᵐ x ∂(P : Measure (GraphonSpace α μ)),
        ∀ p : Σ k, SimpleGraph (Fin k), homDensityCoord p.2 x =
          ∫ y, homDensityCoord p.2 y ∂(P : Measure (GraphonSpace α μ)) :=
      ae_all_iff.mpr fun p => hconst p.1 p.2
    haveI : (ae (P : Measure (GraphonSpace α μ))).NeBot :=
      ae_neBot.mpr (IsProbabilityMeasure.ne_zero _)
    obtain ⟨x₀, hx₀⟩ := hae.exists
    -- all coordinates a.s. agree with those of x₀, so a.e. point is x₀
    have hone : ∀ᵐ x ∂(P : Measure (GraphonSpace α μ)), x = x₀ := by
      filter_upwards [hae] with x hx
      exact homDensityCoord_eq_all_iff.mp
        (fun k F => (hx ⟨k, F⟩).trans (hx₀ ⟨k, F⟩).symm)
    refine ⟨x₀, ProbabilityMeasure.toMeasure_injective ?_⟩
    show (P : Measure (GraphonSpace α μ)) = Measure.dirac x₀
    have hmap : (P : Measure (GraphonSpace α μ)).map id =
        (P : Measure (GraphonSpace α μ)).map (fun _ => x₀) :=
      Measure.map_congr hone
    rwa [Measure.map_id, Measure.map_const, measure_univ, one_smul] at hmap
  · rintro ⟨x, rfl⟩
    intro k l F H
    simp only [upperMass_mixtureExchangeableLaw]
    show (∫ y, homDensityCoord ((F ⊕g H).map finSumFinEquiv.toEmbedding) y
          ∂(Measure.dirac x)) =
        (∫ y, homDensityCoord F y ∂(Measure.dirac x)) *
          ∫ y, homDensityCoord H y ∂(Measure.dirac x)
    rw [integral_dirac, integral_dirac, integral_dirac]
    exact homDensityCoord_sum_finAdd F H x

/-- The exchangeable law of a fixed graphon is dissociated: it is the Dirac mixture at
its graphon class. -/
theorem isDissociated_sampleExchangeableLaw (W : Graphon α μ) :
    (Graphon.sampleExchangeableLaw W).IsDissociated := by
  have h : Graphon.sampleExchangeableLaw W =
      mixtureExchangeableLaw (α := α) (μ := μ) (diracProba (mk W)) := by
    refine Graphon.ExchangeableGraphLaw.ext fun k => ?_
    rw [mixtureExchangeableLaw_law, Graphon.sampleExchangeableLaw_law]
    exact ((mixturePMF_dirac (mk W) k).trans (finiteSampleLaw_mk k W)).symm
  rw [h]
  intro k l F H
  exact (isDissociated_mixtureExchangeableLaw_iff _).mpr ⟨mk W, rfl⟩ F H

end GraphonSpace
