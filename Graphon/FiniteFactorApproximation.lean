/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Regularity
import Graphon.Pullback
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Finite-factor approximation of a graphon

Step 5a of the step-approximation programme (#107 remains open): every graphon is, to within
any prescribed cut-norm error, the pullback of a graphon on a **finite** factor.

`FiniteFactorApproximation U ε` bundles the data — a factor map `Ω → Fin (n + 1)`, its law,
the measure-preserving witness, and a kernel on the finite factor — together with the error
bound `cutNormDiff U (pullback kernel factor) < ε`. Packaging the factor as `Fin (n + 1)` with
a bundled `ProbabilityMeasure` keeps every instance available by construction and makes the
finite coupling machinery directly applicable.

`exists_finiteFactorApproximation`: such an approximation exists for **every** `0 < ε`, with
**no standard-Borel, surjectivity, or positive-cell hypothesis**. The construction reads the
Frieze–Kannan partition off `Graphon.regularity`, indexes its parts by an enumeration, and
sends every point to the index of its part — with a final index absorbing the null set of
points no part covers, so no covering or positivity assumption is needed. The kernel is the
matrix of rectangle averages, which `rectAverage` defines (as zero) on null cells.

This is the individual approximation used once per graphon; there is **no shared factor**
across carriers. The triangle assembly reuses the middle graphon's approximation in both
pairwise couplings — that assembly is a later unit and is not addressed here.
-/

open MeasureTheory Set

namespace Graphon

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section Enumeration

variable (P : MeasurablePartition Ω μ)

/-- The `i`-th part of a finite measurable partition, under a fixed enumeration of its parts. -/
noncomputable def enumPart (i : Fin P.parts.card) : Set Ω :=
  ((P.parts.equivFin.symm i : {S // S ∈ P.parts}) : Set Ω)

theorem enumPart_mem (i : Fin P.parts.card) : enumPart P i ∈ P.parts :=
  (P.parts.equivFin.symm i).2

theorem measurableSet_enumPart (i : Fin P.parts.card) : MeasurableSet (enumPart P i) :=
  P.measurableSet_part (enumPart_mem P i)

/-- Distinct indices enumerate distinct parts. -/
theorem enumPart_ne {i j : Fin P.parts.card} (h : i ≠ j) : enumPart P i ≠ enumPart P j := by
  intro hEq
  exact h (P.parts.equivFin.symm.injective (Subtype.ext hEq))

/-- Any part containing a point of `enumPart P i` is `enumPart P i` itself. -/
theorem eq_enumPart_of_mem {S : Set Ω} (hS : S ∈ P.parts) {x : Ω} {i : Fin P.parts.card}
    (hxS : x ∈ S) (hxi : x ∈ enumPart P i) : S = enumPart P i := by
  by_contra hne
  exact Set.disjoint_left.mp
    (P.pairwiseDisjoint (Finset.mem_coe.mpr hS)
      (Finset.mem_coe.mpr (enumPart_mem P i)) hne) hxS hxi

/-- A point lies in at most one enumerated part. -/
theorem enumPart_unique {x : Ω} {i j : Fin P.parts.card}
    (hi : x ∈ enumPart P i) (hj : x ∈ enumPart P j) : i = j := by
  by_contra hne
  exact Set.disjoint_left.mp
    (P.pairwiseDisjoint (Finset.mem_coe.mpr (enumPart_mem P i))
      (Finset.mem_coe.mpr (enumPart_mem P j)) (enumPart_ne P hne)) hi hj

open scoped Classical in
/-- **The factor map**: a point goes to the index of the part containing it. The final index
absorbs the null set of points that no part covers, so no covering hypothesis is needed. -/
noncomputable def partIndex (x : Ω) : Fin (P.parts.card + 1) :=
  if h : ∃ i, x ∈ enumPart P i then (h.choose).castSucc else Fin.last _

theorem partIndex_of_mem {x : Ω} {i : Fin P.parts.card} (hx : x ∈ enumPart P i) :
    partIndex P x = i.castSucc := by
  classical
  have h : ∃ i, x ∈ enumPart P i := ⟨i, hx⟩
  rw [partIndex, dif_pos h]
  exact congrArg _ (enumPart_unique P h.choose_spec hx)

theorem partIndex_preimage_castSucc (i : Fin P.parts.card) :
    partIndex P ⁻¹' {i.castSucc} = enumPart P i := by
  classical
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hx
    rw [partIndex] at hx
    split_ifs at hx with h
    · have hchoose : h.choose = i := Fin.castSucc_injective _ hx
      exact hchoose ▸ h.choose_spec
    · exact absurd hx.symm (Fin.castSucc_lt_last i).ne
  · exact partIndex_of_mem P

theorem partIndex_preimage_last :
    partIndex P ⁻¹' {Fin.last P.parts.card} = (⋃ i, enumPart P i)ᶜ := by
  classical
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
    not_exists]
  constructor
  · intro hx i hi
    rw [partIndex_of_mem P hi] at hx
    exact (Fin.castSucc_lt_last i).ne hx
  · intro hx
    rw [partIndex, dif_neg]
    rintro ⟨i, hi⟩
    exact hx i hi

theorem measurable_partIndex : Measurable (partIndex P) := by
  refine measurable_to_countable' fun y => ?_
  rcases Fin.eq_castSucc_or_eq_last y with ⟨i, hi⟩ | hlast
  · subst hi
    rw [partIndex_preimage_castSucc]
    exact measurableSet_enumPart P i
  · subst hlast
    rw [partIndex_preimage_last]
    exact (MeasurableSet.iUnion fun i => measurableSet_enumPart P i).compl

/-- The part carried by a factor value; the final index carries the empty set. -/
noncomputable def indexPart : Fin (P.parts.card + 1) → Set Ω :=
  Fin.lastCases ∅ (enumPart P)

@[simp] theorem indexPart_castSucc (i : Fin P.parts.card) :
    indexPart P i.castSucc = enumPart P i := by
  simp [indexPart]

@[simp] theorem indexPart_last : indexPart P (Fin.last P.parts.card) = ∅ := by
  simp [indexPart]

theorem measurableSet_indexPart (a : Fin (P.parts.card + 1)) :
    MeasurableSet (indexPart P a) := by
  rcases Fin.eq_castSucc_or_eq_last a with ⟨i, hi⟩ | hlast
  · subst hi; rw [indexPart_castSucc]; exact measurableSet_enumPart P i
  · subst hlast; rw [indexPart_last]; exact MeasurableSet.empty

end Enumeration

variable [IsProbabilityMeasure μ]

/-- **A finite-factor approximation of `U` at scale `ε`**: a factor map to a finite space,
its law, and a kernel on that finite space whose pullback is within `ε` of `U` in cut norm. -/
structure FiniteFactorApproximation (U : Graphon Ω μ) (ε : ℝ) where
  /-- The finite factor has `n + 1` points. -/
  n : ℕ
  /-- The law of the factor map on the finite factor. -/
  law : ProbabilityMeasure (Fin (n + 1))
  /-- The factor map. -/
  factor : Ω → Fin (n + 1)
  /-- The factor map pushes the carrier measure to the factor law. -/
  factor_mp : MeasurePreserving factor μ law
  /-- The approximating kernel, a graphon on the finite factor. -/
  kernel : Graphon (Fin (n + 1)) law
  /-- The pullback of the kernel is within `ε` of `U` in cut norm. -/
  error_lt : cutNormDiff U (pullback kernel factor factor_mp) < ε

section Construction

variable (P : MeasurablePartition Ω μ) (U : Graphon Ω μ)

/-- The law of the factor map: the pushforward of the carrier measure, bundled. -/
noncomputable def partLaw : ProbabilityMeasure (Fin (P.parts.card + 1)) :=
  ⟨μ.map (partIndex P), Measure.isProbabilityMeasure_map (measurable_partIndex P).aemeasurable⟩

theorem measurePreserving_partIndex : MeasurePreserving (partIndex P) μ (partLaw P) :=
  ⟨measurable_partIndex P, rfl⟩

/-- The step matrix on the finite factor: rectangle averages of `U` over the parts. Null cells
need no special treatment — `rectAverage` is zero there. -/
noncomputable def stepMatrix (a b : Fin (P.parts.card + 1)) : ℝ :=
  rectAverage U (indexPart P a) (indexPart P b)

theorem stepMatrix_symm (a b : Fin (P.parts.card + 1)) :
    stepMatrix P U a b = stepMatrix P U b a :=
  rectAverage_symm U _ _ (measurableSet_indexPart P a) (measurableSet_indexPart P b)

theorem stepMatrix_mem_Icc (a b : Fin (P.parts.card + 1)) :
    stepMatrix P U a b ∈ Icc (0 : ℝ) 1 :=
  rectAverage_mem_Icc U _ _ (measurableSet_indexPart P a) (measurableSet_indexPart P b)

/-- **The finite step kernel**: the step matrix as a graphon on the finite factor. -/
noncomputable def stepKernel : Graphon (Fin (P.parts.card + 1)) (partLaw P) := by
  let f : Fin (P.parts.card + 1) × Fin (P.parts.card + 1) → ℝ := fun q => stepMatrix P U q.1 q.2
  let hf : AEStronglyMeasurable f
      ((partLaw P : Measure (Fin (P.parts.card + 1))).prod
        (partLaw P : Measure (Fin (P.parts.card + 1)))) :=
    (Measurable.of_discrete : Measurable f).aestronglyMeasurable
  refine ⟨⟨AEEqFun.mk f hf, ?symm⟩, ?mem_Icc⟩
  case symm =>
    have h := AEEqFun.coeFn_mk f hf
    have h_swap := ae_prod_swap h
    filter_upwards [h, h_swap] with q hq hq_swap
    simp only [f, Prod.swap] at hq hq_swap ⊢
    rw [hq_swap, hq]
    exact stepMatrix_symm P U q.2 q.1
  case mem_Icc =>
    have h := AEEqFun.coeFn_mk f hf
    filter_upwards [h] with q hq
    simp only [f] at hq ⊢
    rw [hq]
    exact stepMatrix_mem_Icc P U q.1 q.2

/-- The finite step kernel agrees with the step matrix a.e. -/
theorem stepKernel_ae :
    ∀ᵐ q ∂((partLaw P : Measure (Fin (P.parts.card + 1))).prod
      (partLaw P : Measure (Fin (P.parts.card + 1)))),
      (stepKernel P U).toAEEqFun q = stepMatrix P U q.1 q.2 :=
  AEEqFun.coeFn_mk _ _

/-- **The pullback of the finite step kernel along the factor map is the stepification.**
This transports the Frieze–Kannan bound into the finite-factor form. -/
theorem pullback_stepKernel :
    pullback (stepKernel P U) (partIndex P) (measurePreserving_partIndex P) = stepify P U := by
  apply Graphon.ext
  apply SymmKernel.ext
  apply AEEqFun.ext
  have hpb := pullback_ae (stepKernel P U) (partIndex P) (measurePreserving_partIndex P)
  have hstep := stepify_ae P U
  have hkerpb : ∀ᵐ p ∂(μ.prod μ),
      (stepKernel P U).toAEEqFun (partIndex P p.1, partIndex P p.2) =
        stepMatrix P U (partIndex P p.1) (partIndex P p.2) := by
    have hmp : MeasurePreserving (Prod.map (partIndex P) (partIndex P)) (μ.prod μ)
        ((partLaw P : Measure (Fin (P.parts.card + 1))).prod
          (partLaw P : Measure (Fin (P.parts.card + 1)))) :=
      (measurePreserving_partIndex P).prod (measurePreserving_partIndex P)
    exact hmp.quasiMeasurePreserving.ae (stepKernel_ae P U)
  have hcov : ∀ᵐ p ∂(μ.prod μ), (∃ i, p.1 ∈ enumPart P i) ∧ (∃ j, p.2 ∈ enumPart P j) := by
    have hone : ∀ᵐ x ∂μ, ∃ i, x ∈ enumPart P i := by
      filter_upwards [P.ae_covers] with x hx
      obtain ⟨S, hS, hxS⟩ := hx
      refine ⟨P.parts.equivFin ⟨S, hS⟩, ?_⟩
      rwa [enumPart, Equiv.symm_apply_apply]
    have h1 : ∀ᵐ p ∂(μ.prod μ), ∃ i, p.1 ∈ enumPart P i :=
      Measure.quasiMeasurePreserving_fst.ae hone
    have h2 : ∀ᵐ p ∂(μ.prod μ), ∃ j, p.2 ∈ enumPart P j :=
      Measure.quasiMeasurePreserving_snd.ae hone
    filter_upwards [h1, h2] with p hp1 hp2 using ⟨hp1, hp2⟩
  filter_upwards [hpb, hstep, hkerpb, hcov] with p hp hps hpk hpc
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hpc
  rw [hp, hpk, hps, stepMatrix, partIndex_of_mem P hi, partIndex_of_mem P hj,
    indexPart_castSucc, indexPart_castSucc]
  exact (stepifyFun_eq_rectAverage P U (enumPart_mem P i) (enumPart_mem P j)
    (Set.mk_mem_prod hi hj)).symm

end Construction

/-- **Finite-factor approximation exists at every scale.** For every graphon and every `0 < ε`
there is a finite factor, a factor map, and a kernel on the factor whose pullback is within `ε`
of the graphon in cut norm — with no standard-Borel, surjectivity, or positive-cell hypothesis.
The factor is `Fin (n + 1)` with a bundled law, so the finite coupling machinery applies
directly. -/
theorem exists_finiteFactorApproximation (U : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (FiniteFactorApproximation U ε) := by
  obtain ⟨P, -, hP⟩ := regularity U (ε / 2) (by positivity)
  exact ⟨{ n := P.parts.card
           law := partLaw P
           factor := partIndex P
           factor_mp := measurePreserving_partIndex P
           kernel := stepKernel P U
           error_lt := by rw [pullback_stepKernel]; linarith }⟩

end Graphon
