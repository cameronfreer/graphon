/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.Regularity

/-!
# The overlay theorem: an MP bijection nearly achieves the cut distance (Rokhlin campaign, R3)

This file proves the last live Rokhlin core, `exists_mpEquiv_cutNormDiff_lt_add`: on an
atomless standard Borel probability space, the cut distance — an infimum over pairs of
measure-preserving *maps* — is achieved up to any `ε > 0` by pulling back one graphon along a
single measure-preserving **bijection**, leaving the other bare. This is the classical
overlay / bijection-density fact (Borgs–Chayes–Lovász–Sós–Vesztergombi Lemma 3.5, Janson
Theorem 6.9), needed by the completeness telescope in `Graphon/Compactness.lean`.

It lives in its own file because the proof needs the Frieze–Kannan `regularity` lemma and the
atomless carving primitives of `Graphon/Regularity.lean`, which sit *downstream* of
`Graphon/CutDistance.lean` in the import graph.

The proof follows `docs/overlay-scoping.md` §4: **no Birkhoff / rational approximation.**
For *step* graphons, the value of any coupling `(φ, ψ)` is realized **exactly** by an MP
bijection: the coupling matrix `λ_{ik} = μ(φ⁻¹(S_i) ∩ ψ⁻¹(T_k))` has row and column sums
equal to the cell measures, so (atomlessly) both partitions can be refined into cells of
mass exactly `λ_{ik}`, and `exists_controlled_cell_alignment` — applied twice, once for the
answer bijection and once for a proof-only transfer — turns the matched refinements into the
required measure-preserving `α ≃ᵐ α`. The only `ε` comes from step approximation.

## Roadmap (R3)

* **O1** `exists_disjoint_subsets_of_measures` — carve finitely many disjoint subsets of
  prescribed masses out of a measurable set; `MeasurablePartition.ofCells` — assemble a
  partition from disjoint cells plus a waste cell.
* **O2** the exact step-overlay transfer (double alignment).
* **O3** assembly: `exists_mpEquiv_cutNormDiff_lt_add` (relocated here from
  `Graphon/CutDistance.lean`).
-/

open MeasureTheory Set Filter Finset

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

/-! ### O1: prescribed-mass carving and partition assembly -/

section Carving

variable [IsProbabilityMeasure μ]

/-- **Prescribed-mass carving.** Out of a measurable set `C`, carve finitely many pairwise
disjoint measurable subsets of any prescribed masses `r i` with `∑ i, r i ≤ μ C`.

This generalizes `exists_equal_chunks_inside` (equal masses `1/q`) to arbitrary prescribed
masses; it is the finite-matrix carving step of the overlay construction
(`docs/overlay-scoping.md` §4, step 1). -/
theorem exists_disjoint_subsets_of_measures [StandardBorelSpace α] [NoAtoms μ] :
    ∀ {n : ℕ} {C : Set α}, MeasurableSet C → ∀ r : Fin n → ℝ≥0∞, ∑ i, r i ≤ μ C →
    ∃ A : Fin n → Set α, (∀ i, MeasurableSet (A i)) ∧ (∀ i, A i ⊆ C) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧ ∀ i, μ (A i) = r i := by
  intro n
  induction n with
  | zero =>
    intro C _ r _
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro C hC r hr
    -- Carve the head cell of mass `r 0`.
    have hr0 : r 0 ≤ μ C :=
      le_trans (Finset.single_le_sum (fun i _ => zero_le) (Finset.mem_univ 0)) hr
    obtain ⟨A₀, hA₀meas, hA₀sub, hA₀μ⟩ := exists_measurable_subset_of_measure hC hr0
    -- Recurse on the complement within `C` with the tail masses.
    have hC' : MeasurableSet (C \ A₀) := hC.diff hA₀meas
    have hsum' : ∑ i : Fin n, r i.succ ≤ μ (C \ A₀) := by
      have hdiff : μ (C \ A₀) = μ C - r 0 := by
        rw [measure_sdiff hA₀sub hA₀meas.nullMeasurableSet (measure_ne_top μ A₀), hA₀μ]
      have h := hr
      rw [Fin.sum_univ_succ] at h
      rw [hdiff]
      exact ENNReal.le_sub_of_add_le_left (ne_top_of_le_ne_top (measure_ne_top μ C) hr0) h
    obtain ⟨A', hA'meas, hA'sub, hA'disj, hA'μ⟩ := ih hC' (fun i => r i.succ) hsum'
    refine ⟨Fin.cons A₀ A', fun i => ?_, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
    · obtain rfl | ⟨a, rfl⟩ := Fin.eq_zero_or_eq_succ i
      · simpa using hA₀meas
      · simpa using hA'meas a
    · obtain rfl | ⟨a, rfl⟩ := Fin.eq_zero_or_eq_succ i
      · simpa using hA₀sub
      · simpa using (hA'sub a).trans sdiff_subset
    · have hdisj₀ : ∀ a : Fin n, Disjoint A₀ (A' a) := fun a =>
        disjoint_sdiff_right.mono_right (hA'sub a)
      obtain rfl | ⟨a, rfl⟩ := Fin.eq_zero_or_eq_succ i <;>
        obtain rfl | ⟨b, rfl⟩ := Fin.eq_zero_or_eq_succ j
      · exact absurd rfl hij
      · simpa using hdisj₀ b
      · simpa using (hdisj₀ a).symm
      · simpa using hA'disj (fun h => hij (congrArg Fin.succ h))
    · obtain rfl | ⟨a, rfl⟩ := Fin.eq_zero_or_eq_succ i
      · simpa using hA₀μ
      · simpa using hA'μ a

end Carving

/-! ### O1: partition from disjoint cells plus a waste cell -/

/-- Assemble a `MeasurablePartition` from finitely many pairwise disjoint measurable cells,
adding the complement of their union as a waste cell. Every input cell is a part
(`mem_ofCells_parts`). -/
noncomputable def _root_.MeasurablePartition.ofCells {n : ℕ} (A : Fin n → Set α)
    (hmeas : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    MeasurablePartition α μ where
  parts := insert ((⋃ i, A i)ᶜ) (Finset.univ.image A)
  measurable_parts := by
    intro S hS
    rcases Finset.mem_insert.mp hS with rfl | hS
    · exact (MeasurableSet.iUnion hmeas).compl
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hS
      exact hmeas i
  pairwiseDisjoint := by
    intro S hS T hT hST
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_image,
      Finset.coe_univ, Set.image_univ, Set.mem_range] at hS hT
    rcases hS with rfl | ⟨i, rfl⟩ <;> rcases hT with rfl | ⟨j, rfl⟩
    · exact absurd rfl hST
    · exact disjoint_compl_left.mono_right (Set.subset_iUnion A j)
    · exact disjoint_compl_right.mono_left (Set.subset_iUnion A i)
    · exact hdisj fun h => hST (congrArg A h)
  ae_covers := Eventually.of_forall fun x => by
    by_cases hx : x ∈ ⋃ i, A i
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact ⟨A i, Finset.mem_insert_of_mem (Finset.mem_image_of_mem A (Finset.mem_univ i)), hi⟩
    · exact ⟨_, Finset.mem_insert_self _ _, hx⟩

/-- Each input cell is a part of `MeasurablePartition.ofCells`. -/
theorem _root_.MeasurablePartition.mem_ofCells_parts {n : ℕ} {A : Fin n → Set α}
    {hmeas : ∀ i, MeasurableSet (A i)}
    {hdisj : Pairwise (fun i j => Disjoint (A i) (A j))} (i : Fin n) :
    A i ∈ (MeasurablePartition.ofCells (μ := μ) A hmeas hdisj).parts :=
  Finset.mem_insert_of_mem (Finset.mem_image_of_mem A (Finset.mem_univ i))

/-! ### O2: the exact step-overlay transfer -/

section StepOverlay

variable [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Splitting a measure along the preimages of a partition under a measure-preserving map:
`∑_{T ∈ Q.parts} μ (X ∩ ψ⁻¹(T)) = μ X`. (With `ψ = id` and `X = univ` this recovers that the
part measures of a `MeasurablePartition` sum to one.) -/
theorem sum_measure_inter_preimage_parts (Q : MeasurablePartition α μ) {ψ : α → α}
    (hψ : MeasurePreserving ψ μ μ) {X : Set α} (hX : MeasurableSet X) :
    ∑ T ∈ Q.parts, μ (X ∩ ψ ⁻¹' T) = μ X := by
  have hdisj : (Q.parts : Set (Set α)).PairwiseDisjoint (fun T => X ∩ ψ ⁻¹' T) := by
    intro S hS T hT hST
    exact ((Q.pairwiseDisjoint hS hT hST).preimage ψ).mono
      Set.inter_subset_right Set.inter_subset_right
  have hmeas : ∀ T ∈ Q.parts, MeasurableSet (X ∩ ψ ⁻¹' T) := fun T hT =>
    hX.inter (hψ.measurable (Q.measurableSet_part hT))
  rw [← measure_biUnion_finset hdisj hmeas]
  have hUeq : (⋃ T ∈ Q.parts, X ∩ ψ ⁻¹' T) = X ∩ ⋃ T ∈ Q.parts, ψ ⁻¹' T := by
    simp [Set.inter_iUnion]
  rw [hUeq]
  -- The union of the part preimages is conull.
  have hU_meas : MeasurableSet (⋃ T ∈ Q.parts, ψ ⁻¹' T) :=
    Q.parts.measurableSet_biUnion fun T hT => hψ.measurable (Q.measurableSet_part hT)
  have hnull : μ ((⋃ T ∈ Q.parts, ψ ⁻¹' T)ᶜ) = 0 := by
    have hcov : ∀ᵐ x ∂μ, ∃ T ∈ Q.parts, ψ x ∈ T := hψ.quasiMeasurePreserving.ae Q.ae_covers
    have hsub : (⋃ T ∈ Q.parts, ψ ⁻¹' T)ᶜ ⊆ {x | ¬ ∃ T ∈ Q.parts, ψ x ∈ T} := by
      intro x hx ⟨T, hT, hxT⟩
      exact hx (Set.mem_biUnion hT hxT)
    apply measure_mono_null hsub
    rw [← ae_iff]
    exact hcov
  have hsplit := measure_inter_add_sdiff (μ := μ) X hU_meas
  have hdiff : μ (X \ ⋃ T ∈ Q.parts, ψ ⁻¹' T) = 0 :=
    measure_mono_null (Set.sdiff_subset_compl _ _) hnull
  rw [hdiff, add_zero] at hsplit
  exact hsplit

/-- Two measure-preserving maps that a.e. land in a common part of `P` pull a stepified
graphon back to the *same* graphon. This is the transfer engine of the overlay proof: the
stepification only sees which part a point lies in, never the point itself. -/
theorem pullback_stepify_congr (P : MeasurablePartition α μ) (U : Graphon α μ)
    {f g : α → α} (hf : MeasurePreserving f μ μ) (hg : MeasurePreserving g μ μ)
    (h : ∀ᵐ x ∂μ, ∃ S ∈ P.parts, f x ∈ S ∧ g x ∈ S) :
    pullback (stepify P U) f hf = pullback (stepify P U) g hg := by
  apply Graphon.ext
  apply SymmKernel.ext
  apply AEEqFun.ext
  have h_pf := pullback_ae (stepify P U) f hf
  have h_pg := pullback_ae (stepify P U) g hg
  have h_sf : ∀ᵐ p ∂(μ.prod μ),
      (stepify P U).toAEEqFun (f p.1, f p.2) = stepifyFun P U (f p.1, f p.2) :=
    (SymmKernel.measurePreserving_prodMap_self hf).quasiMeasurePreserving.ae (stepify_ae P U)
  have h_sg : ∀ᵐ p ∂(μ.prod μ),
      (stepify P U).toAEEqFun (g p.1, g p.2) = stepifyFun P U (g p.1, g p.2) :=
    (SymmKernel.measurePreserving_prodMap_self hg).quasiMeasurePreserving.ae (stepify_ae P U)
  have h_fst : ∀ᵐ p ∂(μ.prod μ), ∃ S ∈ P.parts, f p.1 ∈ S ∧ g p.1 ∈ S :=
    Measure.quasiMeasurePreserving_fst.ae h
  have h_snd : ∀ᵐ p ∂(μ.prod μ), ∃ S ∈ P.parts, f p.2 ∈ S ∧ g p.2 ∈ S :=
    Measure.quasiMeasurePreserving_snd.ae h
  filter_upwards [h_pf, h_pg, h_sf, h_sg, h_fst, h_snd] with p hpf hpg hsf hsg h1 h2
  obtain ⟨S₁, hS₁, hf1, hg1⟩ := h1
  obtain ⟨S₂, hS₂, hf2, hg2⟩ := h2
  rw [hpf, hsf, hpg, hsg,
    stepifyFun_eq_rectAverage P U hS₁ hS₂ (Set.mem_prod.mpr ⟨hf1, hf2⟩),
    stepifyFun_eq_rectAverage P U hS₁ hS₂ (Set.mem_prod.mpr ⟨hg1, hg2⟩)]

set_option maxHeartbeats 800000

/-- **The exact step overlay.** For step graphons, the cut-norm value of *any* coupling
`(φ, ψ)` of measure-preserving maps is achieved **exactly** by a single measure-preserving
bijection `σ`, leaving the second graphon bare.

Construction (`docs/overlay-scoping.md` §4): the coupling matrix
`λ_{ik} = μ(φ⁻¹(S_i) ∩ ψ⁻¹(T_k))` has row and column sums equal to the part measures, so
both partitions refine (atomlessly, `exists_disjoint_subsets_of_measures`) into cells of
mass exactly `λ_{ik}`. Aligning the positive-mass refined cells twice via
`exists_controlled_cell_alignment` — `σ : T_{ik} → S_{ik}` (the answer) and
`τ : T_{ik} → φ⁻¹(S_i) ∩ ψ⁻¹(T_k)` (a proof-only transfer) — makes `φ ∘ τ` and `σ` land in
a common part of `P` a.e., and `ψ ∘ τ` and `id` land in a common part of `Q` a.e.; then
`pullback_stepify_congr` plus invariance of `cutNormDiff` under the bijection `τ` give the
equality. No rational approximation or Birkhoff matching is needed. -/
theorem exists_mpEquiv_pullback_stepify_eq [StandardBorelSpace α] [NoAtoms μ]
    (P Q : MeasurablePartition α μ) (U W : Graphon α μ)
    {φ ψ : α → α} (hφ : MeasurePreserving φ μ μ) (hψ : MeasurePreserving ψ μ μ) :
    ∃ (σ : α ≃ᵐ α) (hσ : MeasurePreserving σ μ μ),
      cutNormDiff (pullback (stepify P U) σ hσ) (stepify Q W) =
        cutNormDiff (pullback (stepify P U) φ hφ) (pullback (stepify Q W) ψ hψ) := by
  classical
  -- Enumerate the parts of `P` and `Q`.
  let Sc : Fin P.parts.card → Set α := fun i => (P.parts.equivFin.symm i : Set α)
  let Tc : Fin Q.parts.card → Set α := fun k => (Q.parts.equivFin.symm k : Set α)
  have hSc_mem : ∀ i, Sc i ∈ P.parts := fun i => (P.parts.equivFin.symm i).2
  have hTc_mem : ∀ k, Tc k ∈ Q.parts := fun k => (Q.parts.equivFin.symm k).2
  have hSc_meas : ∀ i, MeasurableSet (Sc i) := fun i => P.measurableSet_part (hSc_mem i)
  have hTc_meas : ∀ k, MeasurableSet (Tc k) := fun k => Q.measurableSet_part (hTc_mem k)
  have hSc_inj : Function.Injective Sc := fun i j h =>
    P.parts.equivFin.symm.injective (Subtype.ext h)
  have hTc_inj : Function.Injective Tc := fun i j h =>
    Q.parts.equivFin.symm.injective (Subtype.ext h)
  have hSc_sum : ∀ F : Set α → ℝ≥0∞, ∑ i, F (Sc i) = ∑ S ∈ P.parts, F S := fun F => by
    rw [← Finset.sum_coe_sort P.parts F]
    exact Equiv.sum_comp P.parts.equivFin.symm fun s => F s
  have hTc_sum : ∀ F : Set α → ℝ≥0∞, ∑ k, F (Tc k) = ∑ T ∈ Q.parts, F T := fun F => by
    rw [← Finset.sum_coe_sort Q.parts F]
    exact Equiv.sum_comp Q.parts.equivFin.symm fun t => F t
  -- The coupling matrix and its marginals.
  set ℓ : Fin P.parts.card × Fin Q.parts.card → ℝ≥0∞ :=
    fun ik => μ (φ ⁻¹' Sc ik.1 ∩ ψ ⁻¹' Tc ik.2) with hℓ
  have hrow : ∀ i, ∑ k, ℓ (i, k) = μ (Sc i) := fun i =>
    calc ∑ k, ℓ (i, k) = ∑ T ∈ Q.parts, μ (φ ⁻¹' Sc i ∩ ψ ⁻¹' T) :=
          hTc_sum fun T => μ (φ ⁻¹' Sc i ∩ ψ ⁻¹' T)
      _ = μ (φ ⁻¹' Sc i) :=
          sum_measure_inter_preimage_parts Q hψ (hφ.measurable (hSc_meas i))
      _ = μ (Sc i) := hφ.measure_preimage (hSc_meas i).nullMeasurableSet
  have hcol : ∀ k, ∑ i, ℓ (i, k) = μ (Tc k) := fun k =>
    calc ∑ i, ℓ (i, k) = ∑ i, μ (ψ ⁻¹' Tc k ∩ φ ⁻¹' Sc i) := by
          simp only [hℓ, Set.inter_comm]
      _ = ∑ S ∈ P.parts, μ (ψ ⁻¹' Tc k ∩ φ ⁻¹' S) :=
          hSc_sum fun S => μ (ψ ⁻¹' Tc k ∩ φ ⁻¹' S)
      _ = μ (ψ ⁻¹' Tc k) :=
          sum_measure_inter_preimage_parts P hφ (hψ.measurable (hTc_meas k))
      _ = μ (Tc k) := hψ.measure_preimage (hTc_meas k).nullMeasurableSet
  -- Carve each `Q`-part into subcells of masses `ℓ (·, k)`, and each `P`-part into subcells
  -- of masses `ℓ (i, ·)`.
  choose TT hTT_meas hTT_sub hTT_disj hTT_μ using fun k =>
    exists_disjoint_subsets_of_measures (hTc_meas k) (fun i => ℓ (i, k)) (hcol k).le
  choose SS hSS_meas hSS_sub hSS_disj hSS_μ using fun i =>
    exists_disjoint_subsets_of_measures (hSc_meas i) (fun k => ℓ (i, k)) (hrow i).le
  -- The coupling cells themselves.
  set R : Fin P.parts.card × Fin Q.parts.card → Set α :=
    fun ik => φ ⁻¹' Sc ik.1 ∩ ψ ⁻¹' Tc ik.2 with hR
  have hR_meas : ∀ ik, MeasurableSet (R ik) := fun ik =>
    (hφ.measurable (hSc_meas ik.1)).inter (hψ.measurable (hTc_meas ik.2))
  -- Global pairwise disjointness of the three refined families over the product index.
  have hTT_gdisj : Pairwise fun ik ik' : Fin P.parts.card × Fin Q.parts.card =>
      Disjoint (TT ik.2 ik.1) (TT ik'.2 ik'.1) := by
    rintro ⟨i, k⟩ ⟨i', k'⟩ hne
    by_cases hk : k = k'
    · subst hk
      exact hTT_disj k fun h => hne (congrArg (fun z => (z, k)) h)
    · exact (Q.pairwiseDisjoint (hTc_mem k) (hTc_mem k') fun h => hk (hTc_inj h)).mono
        (hTT_sub k i) (hTT_sub k' i')
  have hSS_gdisj : Pairwise fun ik ik' : Fin P.parts.card × Fin Q.parts.card =>
      Disjoint (SS ik.1 ik.2) (SS ik'.1 ik'.2) := by
    rintro ⟨i, k⟩ ⟨i', k'⟩ hne
    by_cases hi : i = i'
    · subst hi
      exact hSS_disj i fun h => hne (congrArg (fun z => (i, z)) h)
    · exact (P.pairwiseDisjoint (hSc_mem i) (hSc_mem i') fun h => hi (hSc_inj h)).mono
        (hSS_sub i k) (hSS_sub i' k')
  have hR_gdisj : Pairwise fun ik ik' : Fin P.parts.card × Fin Q.parts.card =>
      Disjoint (R ik) (R ik') := by
    rintro ⟨i, k⟩ ⟨i', k'⟩ hne
    by_cases hi : i = i'
    · subst hi
      have hk : k ≠ k' := fun h => hne (congrArg (fun z => (i, z)) h)
      exact ((Q.pairwiseDisjoint (hTc_mem k) (hTc_mem k') fun h => hk (hTc_inj h)).preimage
        ψ).mono Set.inter_subset_right Set.inter_subset_right
    · exact ((P.pairwiseDisjoint (hSc_mem i) (hSc_mem i') fun h => hi (hSc_inj h)).preimage
        φ).mono Set.inter_subset_left Set.inter_subset_left
  -- The positive-mass indices, enumerated.
  set good : Finset (Fin P.parts.card × Fin Q.parts.card) :=
    Finset.univ.filter fun ik => ℓ ik ≠ 0 with hgood
  -- An opaque enumeration of `good` (only injectivity and summation over it are used).
  obtain ⟨eG⟩ : Nonempty (Fin good.card ≃ {ik // ik ∈ good}) := ⟨good.equivFin.symm⟩
  set ιT : Fin good.card → Set α := fun j => TT (eG j).1.2 (eG j).1.1 with hιT
  set ιS : Fin good.card → Set α := fun j => SS (eG j).1.1 (eG j).1.2 with hιS
  set ιR : Fin good.card → Set α := fun j => R (eG j).1 with hιR
  have hgood_ne : ∀ j, ℓ (eG j).1 ≠ 0 := fun j => (Finset.mem_filter.mp (eG j).2).2
  have heG_inj : Function.Injective fun j => (eG j).1 := fun a b h =>
    eG.injective (Subtype.ext h)
  have hιT_μ : ∀ j, μ (ιT j) = ℓ (eG j).1 := fun j => hTT_μ (eG j).1.2 (eG j).1.1
  have hιS_μ : ∀ j, μ (ιS j) = ℓ (eG j).1 := fun j => hSS_μ (eG j).1.1 (eG j).1.2
  have hιR_μ : ∀ j, μ (ιR j) = ℓ (eG j).1 := fun j => rfl
  -- The good cells are pairwise disjoint and (having positive mass) nonempty, hence the
  -- indexed families are injective.
  have hιT_disj : Pairwise fun a b => Disjoint (ιT a) (ιT b) := fun a b hab =>
    hTT_gdisj (heG_inj.ne hab)
  have hιS_disj : Pairwise fun a b => Disjoint (ιS a) (ιS b) := fun a b hab =>
    hSS_gdisj (heG_inj.ne hab)
  have hιR_disj : Pairwise fun a b => Disjoint (ιR a) (ιR b) := fun a b hab =>
    hR_gdisj (heG_inj.ne hab)
  have hinj_of : ∀ (ι : Fin good.card → Set α), (∀ j, μ (ι j) = ℓ (eG j).1) →
      Pairwise (fun a b => Disjoint (ι a) (ι b)) → Function.Injective ι := by
    intro ι hμι hdisj a b hab
    by_contra hne
    have hd : Disjoint (ι a) (ι b) := hdisj hne
    rw [hab, disjoint_self] at hd
    exact (nonempty_of_measure_ne_zero
      (show μ (ι b) ≠ 0 by rw [hμι]; exact hgood_ne b)).ne_empty hd
  have hιT_inj : Function.Injective ιT := hinj_of ιT hιT_μ hιT_disj
  have hιS_inj : Function.Injective ιS := hinj_of ιS hιS_μ hιS_disj
  have hιR_inj : Function.Injective ιR := hinj_of ιR hιR_μ hιR_disj
  -- Package the three families as partitions (adding waste cells) and align twice.
  obtain ⟨σ, hσ, hσ_cell⟩ := MeasurePreserving.exists_controlled_cell_alignment
    (MeasurablePartition.ofCells (μ := μ) ιT (fun j => hTT_meas _ _) hιT_disj)
    (MeasurablePartition.ofCells (μ := μ) ιS (fun j => hSS_meas _ _) hιS_disj)
    ιT ιS (fun j => MeasurablePartition.mem_ofCells_parts j)
    (fun j => MeasurablePartition.mem_ofCells_parts j) hιT_inj hιS_inj
    (fun j => by rw [hιT_μ, hιS_μ])
  obtain ⟨τ, hτ, hτ_cell⟩ := MeasurePreserving.exists_controlled_cell_alignment
    (MeasurablePartition.ofCells (μ := μ) ιT (fun j => hTT_meas _ _) hιT_disj)
    (MeasurablePartition.ofCells (μ := μ) ιR (fun j => hR_meas _) hιR_disj)
    ιT ιR (fun j => MeasurablePartition.mem_ofCells_parts j)
    (fun j => MeasurablePartition.mem_ofCells_parts j) hιT_inj hιR_inj
    (fun j => by rw [hιT_μ, hιR_μ])
  -- Almost every point lies in a good `T`-cell: their total mass is one.
  have hae_good : ∀ᵐ x ∂μ, ∃ j, x ∈ ιT j := by
    have hμU : μ (⋃ j, ιT j) = 1 := by
      rw [measure_iUnion hιT_disj fun j => hTT_meas _ _, tsum_fintype]
      calc ∑ j, μ (ιT j) = ∑ j, ℓ (eG j).1 := by simp_rw [hιT_μ]
        _ = ∑ ik ∈ good, ℓ ik := by
            rw [← Finset.sum_coe_sort good ℓ]
            exact Fintype.sum_equiv eG (fun j => ℓ (eG j).1) (fun x => ℓ x.1) fun j => rfl
        _ = ∑ ik, ℓ ik := Finset.sum_subset (Finset.subset_univ good) fun ik _ hik => by
            simp only [hgood, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hik
            exact hik
        _ = ∑ i, ∑ k, ℓ (i, k) := by rw [Fintype.sum_prod_type]
        _ = ∑ i, μ (Sc i) := by simp_rw [hrow]
        _ = ∑ S ∈ P.parts, μ S := hSc_sum μ
        _ = 1 := by
            have h1 := sum_measure_inter_preimage_parts P (MeasurePreserving.id μ)
              MeasurableSet.univ
            simpa using h1
    have hU_ae : (⋃ j, ιT j) ∈ ae μ := by
      rw [mem_ae_iff]
      exact (prob_compl_eq_zero_iff (MeasurableSet.iUnion fun j => hTT_meas _ _)).mpr hμU
    filter_upwards [hU_ae] with x hx
    exact Set.mem_iUnion.mp hx
  -- The two common-part membership facts feeding `pullback_stepify_congr`.
  have hσ_all : ∀ᵐ x ∂μ, ∀ j, x ∈ ιT j → σ x ∈ ιS j := by
    rw [Filter.eventually_all]; exact hσ_cell
  have hτ_all : ∀ᵐ x ∂μ, ∀ j, x ∈ ιT j → τ x ∈ ιR j := by
    rw [Filter.eventually_all]; exact hτ_cell
  have h1 : ∀ᵐ x ∂μ, ∃ S ∈ P.parts, (φ ∘ ⇑τ) x ∈ S ∧ σ x ∈ S := by
    filter_upwards [hae_good, hσ_all, hτ_all] with x hx hσx hτx
    obtain ⟨j, hxj⟩ := hx
    refine ⟨Sc (eG j).1.1, hSc_mem _, ?_, ?_⟩
    · exact (hτx j hxj).1
    · exact hSS_sub _ _ (hσx j hxj)
  have h2 : ∀ᵐ x ∂μ, ∃ T ∈ Q.parts, (ψ ∘ ⇑τ) x ∈ T ∧ id x ∈ T := by
    filter_upwards [hae_good, hτ_all] with x hx hτx
    obtain ⟨j, hxj⟩ := hx
    exact ⟨Tc (eG j).1.2, hTc_mem _, (hτx j hxj).2, hTT_sub _ _ hxj⟩
  -- Assemble: transfer along `τ`, then cancel it (it is a bijection).
  refine ⟨σ, hσ, ?_⟩
  have e1 : pullback (pullback (stepify P U) φ hφ) (⇑τ) hτ
      = pullback (stepify P U) (⇑σ) hσ := by
    rw [pullback_pullback]
    exact pullback_stepify_congr P U (hφ.comp hτ) hσ h1
  have e2 : pullback (pullback (stepify Q W) ψ hψ) (⇑τ) hτ = stepify Q W := by
    rw [pullback_pullback]
    have h := pullback_stepify_congr Q W (hψ.comp hτ) (MeasurePreserving.id μ) h2
    rw [h, pullback_id]
  calc cutNormDiff (pullback (stepify P U) σ hσ) (stepify Q W)
      = cutNormDiff (pullback (pullback (stepify P U) φ hφ) (⇑τ) hτ)
          (pullback (pullback (stepify Q W) ψ hψ) (⇑τ) hτ) := by rw [e1, e2]
    _ = cutNormDiff (pullback (stepify P U) φ hφ) (pullback (stepify Q W) ψ hψ) :=
        cutNormDiff_pullback_measurableEquiv _ _ τ hτ

end StepOverlay

end Graphon
