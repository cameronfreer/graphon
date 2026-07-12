/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelExchangeableLaw
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# The infinite exchangeable relational law via compactness (AHK umbrella #103, R2b)

The compactness-based extension of a `RelExchangeableLaw` to a probability law on the
infinite structure space (issue #105), the multi-sorted analogue of
`Graphon.ExchangeableGraphLaw.infiniteLaw`. Assumptions: `[Fintype S.Srt] [Countable S.Rel]`
— raw-product compactness is countability-free, but the subsequential weak compactness runs
through the metrizable `ProbabilityMeasure` topology, which uses the countable-coordinate
Polish structure.

Route (exactly as planned): pad each **diagonal** marginal to the infinite space, extract a
weakly convergent subsequence (the space is compact), and identify every size-vector marginal
of the limit using continuity of the restriction (`continuous_restrictFin`), eventual
domination (`exists_const_ge`), and consistency.

* `RelSignature.restrict_comp_pad` — restriction of a padding along composable embeddings
  (`restrict (g ∘ e) ∘ pad e = restrict g`);
* `RelExchangeableLaw.paddedLaw` and `paddedLaw_map_restrictFin` — the diagonal padded laws
  and their finite restrictions;
* `RelExchangeableLaw.exists_map_restrictFin_eq` and `infiniteLaw` — **the infinite law**: a
  weak subsequential limit whose finite restrictions are the given marginals
  (`infiniteLaw_map_restrictFin`).

Uniqueness and the finite/infinite-law equivalence are **R2c**.
-/

open MeasureTheory Filter Topology

namespace RelSignature

variable {S : RelSignature}

/-- **Restriction of a padding along composable embeddings**: padding along `e` then
restricting along `g ∘ e` recovers restriction along `g` (generalizes `restrict_pad`, the
case `g = id`). -/
theorem restrict_comp_pad {U V W : S.Srt → Type*} (e : ∀ s, V s ↪ W s) (g : ∀ s, U s ↪ V s)
    (σ : RelStructure S V) :
    RelStructure.restrict (fun s => (g s).trans (e s)) (RelStructure.pad e σ) =
      RelStructure.restrict g σ := by
  classical
  funext c
  show RelStructure.pad e σ (RelCoord.map (fun s => ((g s).trans (e s) : U s → W s)) c)
    = σ (RelCoord.map (fun s => (g s : U s → V s)) c)
  have hmem : ∀ i, (RelCoord.map (fun s => ((g s).trans (e s) : U s → W s)) c).2 i ∈
      Set.range (e (S.argSort (RelCoord.map (fun s => ((g s).trans (e s) : U s → W s)) c).1 i)) :=
    fun i => ⟨g _ (c.2 i), rfl⟩
  rw [RelStructure.pad, dif_pos hmem]
  congr 1
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext i
  exact (e _).injective (hmem i).choose_spec

/-- The finite restriction of a diagonal padding is a restriction between size vectors. -/
theorem restrictFin_pad_diag {n : S.Srt → ℕ} {N : ℕ} (h : ∀ s, n s ≤ N)
    (σ : RelStructure S (Vfinite fun _ => N)) :
    RelStructure.restrictFin n (RelStructure.pad (fun _ => (Fin.valEmbedding : Fin N ↪ ℕ)) σ)
      = RelStructure.restrictLE h σ := by
  have hemb : (fun s => (Fin.valEmbedding : Fin (n s) ↪ ℕ))
      = (fun s => (Fin.castLEEmb (h s)).trans (Fin.valEmbedding : Fin N ↪ ℕ)) := by
    funext s; ext x; simp [Fin.castLEEmb]
  show RelStructure.restrict (fun s => (Fin.valEmbedding : Fin (n s) ↪ ℕ))
      (RelStructure.pad _ σ) = RelStructure.restrictLE h σ
  rw [hemb]; exact restrict_comp_pad _ _ σ

/-- **Prokhorov extraction**: on the (compact metrizable) infinite structure space, every
sequence of probability measures has a weakly convergent subsequence. -/
theorem exists_subseq_tendsto [Countable S.Rel]
    (Ps : ℕ → ProbabilityMeasure (RelStructure S (Vinfinite S))) :
    ∃ (P : ProbabilityMeasure (RelStructure S (Vinfinite S))) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (Ps ∘ φ) atTop (nhds P) := by
  obtain ⟨P, -, φ, hφ, hconv⟩ := (isCompact_univ
    (X := ProbabilityMeasure (RelStructure S (Vinfinite S)))).tendsto_subseq
    (x := Ps) (fun _ => Set.mem_univ _)
  exact ⟨P, φ, hφ, hconv⟩

namespace RelExchangeableLaw

variable [Fintype S.Srt] [Countable S.Rel] (L : RelExchangeableLaw S)

/-- **The diagonal padded law** at level `N`: the `N`-diagonal marginal pushed forward to the
infinite structure space through the value-embedding padding. -/
noncomputable def paddedLaw (N : ℕ) : ProbabilityMeasure (RelStructure S (Vinfinite S)) :=
  ⟨(L.marginal (fun _ => N) : Measure (RelStructure S (Vfinite fun _ => N))).map
      (RelStructure.pad (fun _ => (Fin.valEmbedding : Fin N ↪ ℕ))),
    Measure.isProbabilityMeasure_map (measurable_pad _).aemeasurable⟩

omit [Fintype S.Srt] [Countable S.Rel] in
@[simp] theorem paddedLaw_coe (N : ℕ) :
    (L.paddedLaw N : Measure (RelStructure S (Vinfinite S))) =
      (L.marginal (fun _ => N) : Measure (RelStructure S (Vfinite fun _ => N))).map
        (RelStructure.pad (fun _ => (Fin.valEmbedding : Fin N ↪ ℕ))) := rfl

omit [Fintype S.Srt] [Countable S.Rel] in
/-- The finite restriction of the diagonal padded level-`N` law is exactly the `n`-marginal,
for every size vector `n ≤ N` (by the padding/restriction identity and consistency). -/
theorem paddedLaw_map_restrictFin {n : S.Srt → ℕ} {N : ℕ} (h : ∀ s, n s ≤ N) :
    (L.paddedLaw N : Measure (RelStructure S (Vinfinite S))).map (RelStructure.restrictFin n) =
      (L.marginal n : Measure (RelStructure S (Vfinite n))) := by
  rw [paddedLaw_coe, Measure.map_map (measurable_restrictFin n) (measurable_pad _),
    show RelStructure.restrictFin n ∘ RelStructure.pad (fun _ => (Fin.valEmbedding : Fin N ↪ ℕ))
        = RelStructure.restrictLE h from funext fun σ => restrictFin_pad_diag h σ]
  exact L.marginal_map_restrictLE h

/-- **Existence of the infinite law**: a weak subsequential limit of the diagonal padded laws
has every finite restriction equal to the corresponding size-vector marginal. -/
theorem exists_map_restrictFin_eq :
    ∃ P : ProbabilityMeasure (RelStructure S (Vinfinite S)),
      ∀ n, (P : Measure (RelStructure S (Vinfinite S))).map (RelStructure.restrictFin n) =
        (L.marginal n : Measure (RelStructure S (Vfinite n))) := by
  obtain ⟨P, φ, hφ, hconv⟩ := exists_subseq_tendsto L.paddedLaw
  refine ⟨P, fun n => ?_⟩
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hconv
    (continuous_restrictFin n)
  obtain ⟨M, hM⟩ := exists_const_ge n
  set Ln : ProbabilityMeasure (RelStructure S (Vfinite n)) := L.marginal n with hLn
  have hconst : ∀ᶠ m in atTop,
      ((L.paddedLaw ∘ φ) m).map (continuous_restrictFin n).measurable.aemeasurable = Ln := by
    filter_upwards [hφ.tendsto_atTop.eventually_ge_atTop M] with m hm
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map]
    exact L.paddedLaw_map_restrictFin fun s => (hM s).trans hm
  have hlim : Tendsto (fun m => ((L.paddedLaw ∘ φ) m).map
      (continuous_restrictFin n).measurable.aemeasurable) atTop (nhds Ln) :=
    (tendsto_congr' hconst).mpr tendsto_const_nhds
  have hPn := tendsto_nhds_unique hmap hlim
  have h2 := congrArg
    (fun ν : ProbabilityMeasure (RelStructure S (Vfinite n)) =>
      (ν : Measure (RelStructure S (Vfinite n)))) hPn
  rw [ProbabilityMeasure.toMeasure_map] at h2
  exact h2

/-- **The infinite exchangeable relational law** (compactness Kolmogorov extension): a
probability law on the infinite structure space realizing the given marginals. -/
noncomputable def infiniteLaw : ProbabilityMeasure (RelStructure S (Vinfinite S)) :=
  L.exists_map_restrictFin_eq.choose

/-- **Marginal identification**: each finite restriction of the infinite law is the
corresponding size-vector marginal. -/
theorem infiniteLaw_map_restrictFin (n : S.Srt → ℕ) :
    (L.infiniteLaw : Measure (RelStructure S (Vinfinite S))).map (RelStructure.restrictFin n) =
      (L.marginal n : Measure (RelStructure S (Vfinite n))) :=
  L.exists_map_restrictFin_eq.choose_spec n

end RelExchangeableLaw

end RelSignature
