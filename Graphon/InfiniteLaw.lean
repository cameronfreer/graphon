/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.InfiniteGraph
import Graphon.ExchangeableGraphLaw
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# The infinite exchangeable graph law: existence and uniqueness (brick A2)

Every exchangeable graph law extends uniquely to a probability law on the infinite
graph space — a specialized Kolmogorov extension proved from compactness, with no
general projective-limit machinery:

* `InfiniteGraph.restrictFin_padFin_of_le` — padding then restricting to a lower level
  is restriction along `Fin.castLE`;
* `Graphon.ExchangeableGraphLaw.paddedLaw` — the level-`n` law pushed forward through
  `padFin`, a probability measure on `InfiniteGraph`; its level-`k` restriction is
  exactly `L.law k` for every `k ≤ n` (`paddedLaw_map_restrictFin`, by consistency);
* `Graphon.ExchangeableGraphLaw.infiniteLaw` — **the infinite law**: a Prokhorov
  subsequential limit of the padded laws. Weak convergence against the continuous
  finite restrictions identifies every marginal (`infiniteLaw_map_restrictFin`), and
  finite-restriction measure extensionality gives uniqueness
  (`unique_of_map_restrictFin` / `eq_infiniteLaw_of_map_restrictFin`).

Brick A3 (exchangeability of `infiniteLaw` under every permutation of `ℕ`, and the
packaged equivalence with `ExchangeableGraphLaw`) builds on this.
-/

open MeasureTheory InfiniteGraph Filter

namespace InfiniteGraph

/-- Padding to level `n` and restricting to a lower level `k` is restriction along
`Fin.castLE`. -/
theorem restrictFin_padFin_of_le {k n : ℕ} (h : k ≤ n) (H : SimpleGraph (Fin n)) :
    restrictFin k (padFin H) = H.comap (Fin.castLEEmb h) := by
  ext a b
  simp only [restrictFin, padFin, SimpleGraph.comap_adj, SimpleGraph.map_adj]
  constructor
  · rintro ⟨a', b', hadj, ha', hb'⟩
    have ha2 : a' = Fin.castLEEmb h a := Fin.ext (by simpa using ha')
    have hb2 : b' = Fin.castLEEmb h b := Fin.ext (by simpa using hb')
    rw [ha2, hb2] at hadj
    exact hadj
  · intro hadj
    exact ⟨Fin.castLEEmb h a, Fin.castLEEmb h b, hadj, rfl, rfl⟩

end InfiniteGraph

namespace Graphon.ExchangeableGraphLaw

/-- **The padded law** at level `n`: the `n`-vertex law, pushed forward to the infinite
graph space through `padFin`. -/
noncomputable def paddedLaw (L : Graphon.ExchangeableGraphLaw) (n : ℕ) :
    ProbabilityMeasure InfiniteGraph :=
  ⟨((L.law n).toMeasure).map InfiniteGraph.padFin,
    Measure.isProbabilityMeasure_map measurable_padFin.aemeasurable⟩

@[simp] theorem paddedLaw_coe (L : Graphon.ExchangeableGraphLaw) (n : ℕ) :
    (paddedLaw L n : Measure InfiniteGraph) =
      ((L.law n).toMeasure).map InfiniteGraph.padFin := rfl

/-- The level-`k` restriction of the padded level-`n` law is exactly the `k`-vertex law,
for every `k ≤ n` (consistency along `Fin.castLE`). -/
theorem paddedLaw_map_restrictFin (L : Graphon.ExchangeableGraphLaw) {k n : ℕ}
    (h : k ≤ n) :
    (paddedLaw L n : Measure InfiniteGraph).map (restrictFin k) =
      (L.law k).toMeasure := by
  rw [paddedLaw_coe, Measure.map_map (measurable_restrictFin k) measurable_padFin,
    show restrictFin k ∘ padFin = fun H : SimpleGraph (Fin n) =>
        H.comap (Fin.castLEEmb h) from
      funext fun H => restrictFin_padFin_of_le h H,
    PMF.toMeasure_map _ _ (SimpleGraph.measurable_comap _), L.consistent (Fin.castLEEmb h)]

/-- **Prokhorov extraction on the infinite graph space**: every sequence of probability
measures has a weakly convergent subsequence. -/
theorem _root_.InfiniteGraph.exists_subseq_tendsto
    (Ps : ℕ → ProbabilityMeasure InfiniteGraph) :
    ∃ (P : ProbabilityMeasure InfiniteGraph) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (Ps ∘ φ) atTop (nhds P) := by
  obtain ⟨P, -, φ, hφ, hconv⟩ :=
    (isCompact_univ (X := ProbabilityMeasure InfiniteGraph)).tendsto_subseq
      (x := Ps) (fun n => Set.mem_univ _)
  exact ⟨P, φ, hφ, hconv⟩

/-- The marginal property has at most one solution (finite-restriction measure
extensionality). -/
theorem unique_of_map_restrictFin {L : Graphon.ExchangeableGraphLaw}
    {P Q : ProbabilityMeasure InfiniteGraph}
    (hP : ∀ k, (P : Measure InfiniteGraph).map (restrictFin k) = (L.law k).toMeasure)
    (hQ : ∀ k, (Q : Measure InfiniteGraph).map (restrictFin k) = (L.law k).toMeasure) :
    P = Q :=
  InfiniteGraph.probabilityMeasure_ext_of_map_restrictFin fun k =>
    (hP k).trans (hQ k).symm

/-- **Existence of the infinite law**: a Prokhorov subsequential limit of the padded
laws has every finite restriction equal to the corresponding marginal. -/
theorem exists_map_restrictFin_eq (L : Graphon.ExchangeableGraphLaw) :
    ∃ P : ProbabilityMeasure InfiniteGraph,
      ∀ k, (P : Measure InfiniteGraph).map (restrictFin k) = (L.law k).toMeasure := by
  obtain ⟨P, φ, hφ, hconv⟩ := InfiniteGraph.exists_subseq_tendsto (paddedLaw L)
  refine ⟨P, fun k => ?_⟩
  -- pushforwards converge weakly
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hconv
    (continuous_restrictFin k)
  -- and are eventually the constant `L.law k`
  set Lk : ProbabilityMeasure (SimpleGraph (Fin k)) :=
    ⟨(L.law k).toMeasure, inferInstance⟩ with hLk
  have hconst : ∀ᶠ m in atTop,
      ((paddedLaw L ∘ φ) m).map
        (continuous_restrictFin k).measurable.aemeasurable = Lk := by
    filter_upwards [hφ.tendsto_atTop.eventually_ge_atTop k] with m hm
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map]
    exact paddedLaw_map_restrictFin L hm
  have hlim : Tendsto (fun m => ((paddedLaw L ∘ φ) m).map
      (continuous_restrictFin k).measurable.aemeasurable) atTop (nhds Lk) :=
    (tendsto_congr' hconst).mpr tendsto_const_nhds
  have hPk := tendsto_nhds_unique hmap hlim
  have h2 := congrArg (fun ν : ProbabilityMeasure (SimpleGraph (Fin k)) =>
    (ν : Measure (SimpleGraph (Fin k)))) hPk
  rw [ProbabilityMeasure.toMeasure_map] at h2
  exact h2

/-- **The infinite exchangeable graph law** (specialized Kolmogorov extension via
compactness): the unique probability law on the infinite graph space whose finite
restrictions are the given marginals. -/
noncomputable def infiniteLaw (L : Graphon.ExchangeableGraphLaw) :
    ProbabilityMeasure InfiniteGraph :=
  (exists_map_restrictFin_eq L).choose

/-- **The marginal identification**: each finite restriction of the infinite law is the
corresponding finite marginal. -/
theorem infiniteLaw_map_restrictFin (L : Graphon.ExchangeableGraphLaw) (k : ℕ) :
    (infiniteLaw L : Measure InfiniteGraph).map (restrictFin k) =
      (L.law k).toMeasure :=
  (exists_map_restrictFin_eq L).choose_spec k

/-- **Uniqueness**: any probability law with the correct finite restrictions is the
infinite law. -/
theorem eq_infiniteLaw_of_map_restrictFin {L : Graphon.ExchangeableGraphLaw}
    {P : ProbabilityMeasure InfiniteGraph}
    (hP : ∀ k, (P : Measure InfiniteGraph).map (restrictFin k) = (L.law k).toMeasure) :
    P = infiniteLaw L :=
  unique_of_map_restrictFin hP (infiniteLaw_map_restrictFin L)

/-- The infinite law determines the exchangeable law (injectivity of the extension):
two exchangeable laws with the same infinite law are equal. -/
theorem infiniteLaw_injective :
    Function.Injective
      (infiniteLaw : Graphon.ExchangeableGraphLaw → ProbabilityMeasure InfiniteGraph) := by
  intro L M h
  refine Graphon.ExchangeableGraphLaw.ext fun k => ?_
  have hk : (L.law k).toMeasure = (M.law k).toMeasure := by
    rw [← infiniteLaw_map_restrictFin L k, ← infiniteLaw_map_restrictFin M k, h]
  ext G
  have := congrArg (fun m : Measure (SimpleGraph (Fin k)) => m {G}) hk
  simpa [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton G)] using this

end Graphon.ExchangeableGraphLaw
