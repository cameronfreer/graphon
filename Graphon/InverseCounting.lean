/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.Counting
import Graphon.Compactness
import Graphon.MatrixDetermination

/-!
# Inverse Counting Lemma

This file proves the inverse counting lemma: if two graphons have similar
homomorphism densities for all graphs, then they are close in cut distance.

## Main results

* `Graphon.cutDistance_zero_of_homDensity_eq` - Equal hom densities ⟹ cutDistance = 0
* `Graphon.cutDistance_le_of_homDensity_close` - The quantitative inverse counting lemma

## Implementation notes

The counting lemma (in `Counting.lean`) shows:
  small cut distance ⟹ similar homomorphism densities

The inverse counting lemma shows the converse:
  similar homomorphism densities ⟹ small cut distance

Together, these establish that cut distance convergence is equivalent to
convergence of all homomorphism densities.

The proof uses:
1. Algebraic determination for step graphons (`MatrixDetermination.lean`)
2. Partition alignment via Rokhlin's theorem (`CutDistance.lean`)
3. Regularity lemma for step approximation
4. Compactness of graphon space

## References

* [L. Lovász, *Large Networks and Graph Limits*][lovasz2012], Section 10.6
-/

open MeasureTheory Set Filter Finset

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace Graphon

/-! ### Step graphon inverse counting

The algebraic core: step graphons on the same partition with equal hom densities
for all graphs have cut distance zero. This connects the measure-theoretic
`homDensity` to the finite `weightedHomSum` and uses `matrix_quotient_of_weightedHomSum_eq`
(the algebraic determination axiom) plus partition alignment (Rokhlin). -/

section StepInverseCounting

variable [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

omit [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ] in
/-- Local reproof of `mkStepFun_measurable` (which is private in Compactness.lean). -/
private theorem mkStepFun_measurable' (P : MeasurablePartition α μ) (c : Set α → Set α → ℝ) :
    Measurable (mkStepFun P c) := by
  unfold mkStepFun
  apply Finset.measurable_sum; intro S hS
  apply Finset.measurable_sum; intro T hT
  exact measurable_const.indicator ((P.measurableSet_part hS).prod (P.measurableSet_part hT))

omit [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ] in
/-- Local reproof of `mkStepFun_eq_at` (which is private in Compactness.lean).
For a point `p ∈ S ×ˢ T` with `S, T ∈ P.parts`, `mkStepFun P c p = c S T`. -/
private theorem mkStepFun_eq_at' (P : MeasurablePartition α μ) (c : Set α → Set α → ℝ)
    {p : α × α} {S : Set α} (hS : S ∈ P.parts) {T : Set α} (hT : T ∈ P.parts)
    (hp : p ∈ S ×ˢ T) : mkStepFun P c p = c S T := by
  unfold mkStepFun
  rw [Finset.sum_eq_single_of_mem S hS, Finset.sum_eq_single_of_mem T hT]
  · exact Set.indicator_of_mem hp _
  · intro T' hT'_mem hT'_ne; apply Set.indicator_of_notMem; intro hp'
    exact Set.disjoint_left.mp (P.pairwiseDisjoint (Finset.mem_coe.mpr hT)
      (Finset.mem_coe.mpr hT'_mem) hT'_ne.symm) (Set.mem_prod.mp hp).2 (Set.mem_prod.mp hp').2
  · intro S' hS'_mem hS'_ne; apply Finset.sum_eq_zero; intro T' _
    apply Set.indicator_of_notMem; intro hp'
    exact Set.disjoint_left.mp (P.pairwiseDisjoint (Finset.mem_coe.mpr hS)
      (Finset.mem_coe.mpr hS'_mem) hS'_ne.symm) (Set.mem_prod.mp hp).1 (Set.mem_prod.mp hp').1

/-- **Bridge lemma**: For a step graphon `mkStepGraphon P c`, the homomorphism density
`homDensity F (mkStepGraphon P c)` equals the weighted homomorphism sum
`weightedHomSum n F c_fin w` where:
- `ι : Fin k → Set α` enumerates `P.parts`
- `c_fin i j = c (ι i) (ι j)` is the coefficient matrix over `Fin k`
- `w i = (μ (ι i)).toReal` is the cell-measure vector

The proof requires decomposing the pi-integral `∫ x, ∏ e, W(x_{e.1}, x_{e.2}) dμ^n`
over partition cell products. The integrand is constant on each product
`∏ v, ι(σ(v))`, and the integral over such a product equals `∏ v, w(σ(v))`.
Summing over all cell assignments `σ : Fin n → Fin k` gives `weightedHomSum`.

**Sorry**: This is a non-trivial integration identity involving `Measure.pi` and
piecewise-constant functions. It does not introduce any new axiom; it is
standard measure theory that would follow from disintegration of product
measures over finite partitions. -/
private theorem homDensity_mkStepGraphon_eq_weightedHomSum
    (P : MeasurablePartition α μ) (c : Set α → Set α → ℝ)
    (hc_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T = c T S)
    (hc_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T ∈ Set.Icc 0 1)
    {k : ℕ} (ι : Fin k → Set α) (hι : ∀ i, ι i ∈ P.parts)
    (hι_surj : ∀ S ∈ P.parts, ∃ i, ι i = S)
    (hι_inj : Function.Injective ι) :
    ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      homDensity F (mkStepGraphon P c hc_symm hc_mem) =
      weightedHomSum n F (fun i j => c (ι i) (ι j))
        (fun i => (μ (ι i)).toReal) := by
  intro n F _inst
  set W := mkStepGraphon P c hc_symm hc_mem
  set π := Measure.pi (fun _ : Fin n => μ)
  -- Step 1: W.toAEEqFun = mkStepFun P c  a.e. under μ × μ
  have hW_ae : ∀ᵐ q ∂(μ.prod μ), W.toAEEqFun q = mkStepFun P c q :=
    AEEqFun.coeFn_mk (mkStepFun P c) (mkStepFun_measurable' P c).aestronglyMeasurable
  -- Lift to pi: for each edge e, W.toAEEqFun (x(e.1), x(e.2)) = mkStepFun P c (x(e.1), x(e.2))
  have hW_edge_ae : ∀ e ∈ F.edgeFinset,
      ∀ᵐ x ∂π, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) =
        mkStepFun P c (x (Quot.out e).1, x (Quot.out e).2) := by
    intro e he
    have hne := edge_out_ne (SimpleGraph.mem_edgeFinset.mp he)
    have h_map_eq : Measure.map (fun x : Fin n → α => (x (Quot.out e).1, x (Quot.out e).2)) π =
        μ.prod μ := by
      have h_indep := (ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin n => μ)
        (fun _ => aemeasurable_id)).indepFun hne
      simp only [id_eq] at h_indep
      rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        (measurable_pi_apply _).aemeasurable
        (measurable_pi_apply _).aemeasurable] at h_indep
      rw [h_indep, (measurePreserving_eval (fun _ : Fin n => μ) _).map_eq,
          (measurePreserving_eval (fun _ : Fin n => μ) _).map_eq]
    have h_qmp : Measure.QuasiMeasurePreserving
        (fun x : Fin n → α => (x (Quot.out e).1, x (Quot.out e).2)) π (μ.prod μ) := by
      constructor
      · exact Measurable.prodMk (measurable_pi_apply _) (measurable_pi_apply _)
      · rw [h_map_eq]
    exact h_qmp.ae hW_ae
  -- Finite intersection: all edges at once
  have hW_all_ae : ∀ᵐ x ∂π, ∀ e ∈ F.edgeFinset,
      W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) =
        mkStepFun P c (x (Quot.out e).1, x (Quot.out e).2) := by
    have aux : ∀ (s : Finset (Sym2 (Fin n))),
        (∀ e ∈ s, ∀ᵐ x ∂π,
          W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) =
            mkStepFun P c (x (Quot.out e).1, x (Quot.out e).2)) →
        ∀ᵐ x ∂π, ∀ e ∈ s,
          W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) =
            mkStepFun P c (x (Quot.out e).1, x (Quot.out e).2) := by
      intro s; refine Finset.induction_on s (fun _ => by simp) (fun a s' _ ih hs => ?_)
      simp only [Finset.mem_insert, forall_eq_or_imp] at hs ⊢
      filter_upwards [hs.1, ih hs.2] with x hx1 hx2; exact ⟨hx1, hx2⟩
    exact aux F.edgeFinset hW_edge_ae
  -- So the integrand product equals the mkStepFun product a.e.
  have hprod_ae : ∀ᵐ x ∂π,
      ∏ e ∈ F.edgeFinset, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) =
      ∏ e ∈ F.edgeFinset, mkStepFun P c (x (Quot.out e).1, x (Quot.out e).2) := by
    filter_upwards [hW_all_ae] with x hx
    exact Finset.prod_congr rfl hx
  -- Step 2: Define cell products and decompose
  -- Cell product for assignment σ
  set cellProd : (Fin n → Fin k) → Set (Fin n → α) :=
    fun σ => Set.pi Set.univ (fun v => ι (σ v))
  -- Cell products are measurable
  have hcell_meas : ∀ σ, MeasurableSet (cellProd σ) := by
    intro σ
    exact MeasurableSet.univ_pi (fun v => P.measurableSet_part (hι (σ v)))
  -- Cell products are pairwise disjoint
  have hcell_disj : Pairwise (fun σ₁ σ₂ => Disjoint (cellProd σ₁) (cellProd σ₂)) := by
    intro σ₁ σ₂ hne
    have ⟨v, hv⟩ : ∃ v, σ₁ v ≠ σ₂ v := by
      by_contra h; push Not at h; exact hne (funext h)
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    have h₁ := Set.mem_pi.mp hx₁ v (Set.mem_univ v)
    have h₂ := Set.mem_pi.mp hx₂ v (Set.mem_univ v)
    exact Set.disjoint_left.mp
      (P.pairwiseDisjoint (hι (σ₁ v)) (hι (σ₂ v)) (fun h => hv (hι_inj h))) h₁ h₂
  -- Cell products cover a.e.
  have hcell_cover : ∀ᵐ x ∂π, ∃ σ, x ∈ cellProd σ := by
    -- For each v, a.e. x(v) ∈ some cell
    have h_coord : ∀ v : Fin n, ∀ᵐ x ∂π, ∃ i : Fin k, x v ∈ ι i := by
      intro v
      have h_mp := measurePreserving_eval (fun _ : Fin n => μ) v
      have h_ae := h_mp.quasiMeasurePreserving.ae P.ae_covers
      filter_upwards [h_ae] with x ⟨S, hS, hxS⟩
      obtain ⟨i, rfl⟩ := hι_surj S hS
      exact ⟨i, hxS⟩
    -- Finite intersection over all coordinates
    have h_all : ∀ᵐ x ∂π, ∀ v : Fin n, ∃ i : Fin k, x v ∈ ι i := by
      rw [Filter.eventually_all]
      exact h_coord
    filter_upwards [h_all] with x hx
    exact ⟨fun v => (hx v).choose, Set.mem_pi.mpr (fun v _ => (hx v).choose_spec)⟩
  -- The union of cell products covers a.e., so the full integral equals the set integral
  have h_integral_eq_union : ∫ x, ∏ e ∈ F.edgeFinset,
      W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∂π =
      ∫ x in ⋃ σ, cellProd σ, ∏ e ∈ F.edgeFinset,
        W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∂π := by
    rw [← setIntegral_univ]
    exact (setIntegral_congr_set (by
      filter_upwards [hcell_cover] with x hx
      exact propext ⟨fun _ => trivial, fun _ => Set.mem_iUnion.mpr hx⟩)).symm
  -- Step 3: On each cell product, the integrand is constant
  -- For x ∈ cellProd σ, mkStepFun P c (x(e.1), x(e.2)) = c(ι(σ(e.1)), ι(σ(e.2)))
  have h_const_on_cell : ∀ σ : Fin n → Fin k, ∀ x ∈ cellProd σ, ∀ e ∈ F.edgeFinset,
      mkStepFun P c (x (Quot.out e).1, x (Quot.out e).2) =
        c (ι (σ (Quot.out e).1)) (ι (σ (Quot.out e).2)) := by
    intro σ x hx e _
    have hv₁ := Set.mem_pi.mp hx (Quot.out e).1 (Set.mem_univ _)
    have hv₂ := Set.mem_pi.mp hx (Quot.out e).2 (Set.mem_univ _)
    exact mkStepFun_eq_at' P c (hι (σ (Quot.out e).1)) (hι (σ (Quot.out e).2))
      (Set.mem_prod.mpr ⟨hv₁, hv₂⟩)
  -- Integrand on cellProd σ equals the constant ∏ e, c(ι(σ(e.1)), ι(σ(e.2)))
  -- (as ae condition under the unrestricted measure, for use with setIntegral_congr_ae)
  have h_integrand_const : ∀ σ : Fin n → Fin k,
      ∀ᵐ x ∂π, x ∈ cellProd σ →
        ∏ e ∈ F.edgeFinset, W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) =
        ∏ e ∈ F.edgeFinset, c (ι (σ (Quot.out e).1)) (ι (σ (Quot.out e).2)) := by
    intro σ
    filter_upwards [hprod_ae] with x hx hx_mem
    rw [hx]
    exact Finset.prod_congr rfl (h_const_on_cell σ x hx_mem)
  -- Step 4: Compute set integral on each cell product
  -- IntegrableOn for each cell product
  have h_integrableOn : ∀ σ : Fin n → Fin k,
      IntegrableOn (fun x => ∏ e ∈ F.edgeFinset,
        W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2)) (cellProd σ) π := by
    intro σ
    exact (homDensityIntegrand_integrable F W).integrableOn
  -- Decompose using integral_iUnion_fintype
  unfold homDensity
  rw [h_integral_eq_union, integral_iUnion_fintype hcell_meas hcell_disj h_integrableOn]
  -- Now: ∑ σ, ∫ x in cellProd σ, ∏ e, W.toAEEqFun (x(e.1), x(e.2)) dπ
  --    = ∑ σ, ∫ x in cellProd σ, ∏ e, c(ι(σ(e.1)), ι(σ(e.2))) dπ
  --    = ∑ σ, (∏ e, c(...)) * π(cellProd σ).toReal
  --    = ∑ σ, (∏ e, c(...)) * ∏ v, (μ(ι(σ(v)))).toReal
  --    = weightedHomSum
  -- First, rewrite each set integral to the constant value
  -- ∫ x in cellProd σ, integrand(x) dπ = ∫ x in cellProd σ, const(σ) dπ
  have h_set_integral_eq : ∀ σ : Fin n → Fin k,
      ∫ x in cellProd σ, ∏ e ∈ F.edgeFinset,
        W.toAEEqFun (x (Quot.out e).1, x (Quot.out e).2) ∂π =
      ∫ x in cellProd σ, ∏ e ∈ F.edgeFinset,
        c (ι (σ (Quot.out e).1)) (ι (σ (Quot.out e).2)) ∂π := by
    intro σ
    exact setIntegral_congr_ae (hcell_meas σ) (h_integrand_const σ)
  -- Now: ∑ σ, ∫ x in cellProd σ, const(σ) dπ
  --    = ∑ σ, const(σ) * π.real (cellProd σ)
  simp_rw [h_set_integral_eq, setIntegral_const]
  -- Compute π.real (cellProd σ) = ∏ v, (μ(ι(σ(v)))).toReal
  have h_real_meas : ∀ σ : Fin n → Fin k,
      π.real (cellProd σ) = ∏ v : Fin n, (μ (ι (σ v))).toReal := by
    intro σ
    unfold Measure.real
    rw [Measure.pi_pi (fun _ => μ) (fun v => ι (σ v))]
    exact ENNReal.toReal_prod _ _
  -- Rewrite and match weightedHomSum
  simp_rw [h_real_meas, smul_eq_mul]
  -- Now goal: ∑ σ, (∏ v, (μ(ι(σ(v)))).toReal) * (∏ e, c(ι(σ(e.1)), ι(σ(e.2))))
  --         = weightedHomSum n F (fun i j => c (ι i) (ι j)) (fun i => (μ (ι i)).toReal)
  -- This is exactly the definition of weightedHomSum
  rfl

/-- **Cell-permuting measure-preserving bijection**: Given a partition P with
k cells enumerated by `ι : Fin k → Set α`, and a permutation `π : Equiv.Perm (Fin k)`
such that `μ(ι i) = μ(ι (π i))` for all i, there exists a MP bijection
`e : α ≃ᵐ α` that maps each cell `ι i` a.e. to `ι (π i)`.

**Sorry traces to**: `MeasurePreserving.exists_common_extension` (Rokhlin's theorem).
The construction proceeds by applying Rokhlin's theorem to each pair of equal-measure
cells `(ι i, ι (π i))` independently, producing a MP bijection on each cell, then
assembling them into a global bijection. -/
private theorem exists_cell_permuting_mp_bijection
    (P : MeasurablePartition α μ) {k : ℕ} (ι : Fin k → Set α)
    (hι : ∀ i, ι i ∈ P.parts) (hι_surj : ∀ S ∈ P.parts, ∃ i, ι i = S)
    (hι_inj : Function.Injective ι)
    (π : Equiv.Perm (Fin k))
    (h_meas : ∀ i, μ (ι i) = μ (ι (π i))) :
    ∃ (e : α ≃ᵐ α) (he : MeasurePreserving e μ μ),
      ∀ i, ∀ᵐ x ∂μ, x ∈ ι i → e x ∈ ι (π i) := by
  -- Apply controlled cell alignment (third conjunct of Rokhlin axiom).
  -- ι_S = ι (original cells), ι_T = ι ∘ π (permuted cells).
  -- Both are injective enumerations of P.parts with matching measures.
  exact MeasurePreserving.exists_controlled_cell_alignment P P
    ι (fun i => ι (π i)) hι (fun i => hι (π i))
    hι_inj (hι_inj.comp π.injective) h_meas

/-- The pullback of a step graphon by a cell-permuting MP bijection equals the
step graphon with permuted coefficients.

If `e` maps each cell `ι i` a.e. to `ι (π i)`, and `c'(S, T)` is related to
`c(S, T)` by `c(ι i, ι j) = c'(ι (π i), ι (π j))`, then
`pullback (mkStepGraphon P c') e = mkStepGraphon P c`. -/
private theorem pullback_mkStepGraphon_of_cell_perm
    (P : MeasurablePartition α μ) (c c' : Set α → Set α → ℝ)
    (hc_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T = c T S)
    (hc_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T ∈ Set.Icc 0 1)
    (hc'_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c' S T = c' T S)
    (hc'_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c' S T ∈ Set.Icc 0 1)
    {k : ℕ} (ι : Fin k → Set α)
    (hι : ∀ i, ι i ∈ P.parts) (hι_surj : ∀ S ∈ P.parts, ∃ i, ι i = S)
    (hι_inj : Function.Injective ι)
    (π : Equiv.Perm (Fin k))
    (h_coeff : ∀ i j, c (ι i) (ι j) = c' (ι (π i)) (ι (π j)))
    (e : α ≃ᵐ α) (he : MeasurePreserving e μ μ)
    (h_cell : ∀ i, ∀ᵐ x ∂μ, x ∈ ι i → e x ∈ ι (π i)) :
    pullback (mkStepGraphon P c' hc'_symm hc'_mem) e he =
    mkStepGraphon P c hc_symm hc_mem := by
  apply Graphon.ext; apply SymmKernel.ext; apply AEEqFun.ext
  -- LHS a.e.: (pullback (mkStepGraphon P c') e he).toAEEqFun p
  --         = (mkStepGraphon P c').toAEEqFun (e p.1, e p.2)
  have h_pb := pullback_ae (mkStepGraphon P c' hc'_symm hc'_mem) (⇑e) he
  -- (mkStepGraphon P c').toAEEqFun q = mkStepFun P c' q  a.e. in q
  have h_c'_ae : ∀ᵐ q ∂(μ.prod μ),
      (mkStepGraphon P c' hc'_symm hc'_mem).toAEEqFun q = mkStepFun P c' q :=
    AEEqFun.coeFn_mk (mkStepFun P c') (mkStepFun_measurable' P c').aestronglyMeasurable
  -- Lift h_c'_ae through the QMP map (Prod.map e e) to get the fact for (e p.1, e p.2)
  have h_c'_lifted : ∀ᵐ p ∂(μ.prod μ),
      (mkStepGraphon P c' hc'_symm hc'_mem).toAEEqFun (e p.1, e p.2) =
      mkStepFun P c' (e p.1, e p.2) := by
    have hqmp : Measure.QuasiMeasurePreserving (Prod.map e e) (μ.prod μ) (μ.prod μ) :=
      (SymmKernel.measurePreserving_prodMap_self he).quasiMeasurePreserving
    exact hqmp.ae h_c'_ae
  -- RHS a.e.: (mkStepGraphon P c).toAEEqFun p = mkStepFun P c p
  have h_c_ae : ∀ᵐ p ∂(μ.prod μ),
      (mkStepGraphon P c hc_symm hc_mem).toAEEqFun p = mkStepFun P c p :=
    AEEqFun.coeFn_mk (mkStepFun P c) (mkStepFun_measurable' P c).aestronglyMeasurable
  -- Partition covers: for a.e. x, there exist i with x ∈ ι i
  -- First, P.ae_covers gives ∃ S ∈ P.parts, x ∈ S.
  -- Since ι surjects onto P.parts, we can find i with ι i = S.
  have h_cell_fst : ∀ᵐ x ∂μ, ∃ i, x ∈ ι i := by
    filter_upwards [P.ae_covers] with x ⟨S, hS_mem, hx⟩
    obtain ⟨i, hi⟩ := hι_surj S hS_mem
    exact ⟨i, hi ▸ hx⟩
  -- Lift to product measure
  have h_fst_cell : ∀ᵐ p ∂(μ.prod μ), ∃ i, p.1 ∈ ι i :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst h_cell_fst
  have h_snd_cell : ∀ᵐ p ∂(μ.prod μ), ∃ j, p.2 ∈ ι j :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd h_cell_fst
  -- Lift h_cell to product measure: for a.e. p, p.1 ∈ ι i → e p.1 ∈ ι (π i)
  have h_cell_fst_prod : ∀ i, ∀ᵐ p ∂(μ.prod μ), p.1 ∈ ι i → e p.1 ∈ ι (π i) :=
    fun i => Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst (h_cell i)
  have h_cell_snd_prod : ∀ i, ∀ᵐ p ∂(μ.prod μ), p.2 ∈ ι i → e p.2 ∈ ι (π i) :=
    fun i => Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd (h_cell i)
  -- Combine all h_cell conditions into one a.e. fact using Finset.eventually_all
  have h_cell_all_fst : ∀ᵐ p ∂(μ.prod μ), ∀ i, p.1 ∈ ι i → e p.1 ∈ ι (π i) := by
    rw [Filter.eventually_all]
    exact h_cell_fst_prod
  have h_cell_all_snd : ∀ᵐ p ∂(μ.prod μ), ∀ i, p.2 ∈ ι i → e p.2 ∈ ι (π i) := by
    rw [Filter.eventually_all]
    exact h_cell_snd_prod
  -- Now combine everything
  filter_upwards [h_pb, h_c'_lifted, h_c_ae, h_fst_cell, h_snd_cell,
      h_cell_all_fst, h_cell_all_snd] with p h_pb_p h_c'_p h_c_p
      ⟨i, hi⟩ ⟨j, hj⟩ h_e_fst h_e_snd
  -- LHS: pullback value = mkStepFun P c' (e p.1, e p.2)
  rw [h_pb_p, h_c'_p]
  -- RHS: mkStepGraphon P c value = mkStepFun P c (p.1, p.2)
  rw [h_c_p]
  -- Now: mkStepFun P c' (e p.1, e p.2) = mkStepFun P c (p.1, p.2)
  -- We know: p.1 ∈ ι i, p.2 ∈ ι j, e p.1 ∈ ι (π i), e p.2 ∈ ι (π j)
  have he_fst := h_e_fst i hi
  have he_snd := h_e_snd j hj
  rw [mkStepFun_eq_at' P c' (hι (π i)) (hι (π j))
      (Set.mem_prod.mpr ⟨he_fst, he_snd⟩),
    mkStepFun_eq_at' P c (hι i) (hι j)
      (Set.mem_prod.mpr ⟨hi, hj⟩),
    h_coeff i j]

omit [StandardBorelSpace α] [NoAtoms μ] in
/-- Two step graphons whose coefficients agree on all pairs of positive-measure cells
are equal as Graphons (a.e. equal). -/
private theorem mkStepGraphon_eq_of_ae_coeff
    (P : MeasurablePartition α μ) (c₁ c₂ : Set α → Set α → ℝ)
    (hc₁_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c₁ S T = c₁ T S)
    (hc₁_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c₁ S T ∈ Set.Icc 0 1)
    (hc₂_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c₂ S T = c₂ T S)
    (hc₂_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c₂ S T ∈ Set.Icc 0 1)
    (h_agree : ∀ S ∈ P.parts, ∀ T ∈ P.parts, μ S ≠ 0 → μ T ≠ 0 → c₁ S T = c₂ S T) :
    mkStepGraphon P c₁ hc₁_symm hc₁_mem = mkStepGraphon P c₂ hc₂_symm hc₂_mem := by
  apply Graphon.ext; apply SymmKernel.ext; apply AEEqFun.ext
  -- The underlying functions are a.e. equal: they differ only on null rectangles
  have h1 : ∀ᵐ p ∂(μ.prod μ),
      (mkStepGraphon P c₁ hc₁_symm hc₁_mem).toAEEqFun p = mkStepFun P c₁ p :=
    AEEqFun.coeFn_mk _ (mkStepFun_measurable' P c₁).aestronglyMeasurable
  have h2 : ∀ᵐ p ∂(μ.prod μ),
      (mkStepGraphon P c₂ hc₂_symm hc₂_mem).toAEEqFun p = mkStepFun P c₂ p :=
    AEEqFun.coeFn_mk _ (mkStepFun_measurable' P c₂).aestronglyMeasurable
  have h_fst : ∀ᵐ p ∂(μ.prod μ), ∃ S ∈ P.parts, p.1 ∈ S :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst P.ae_covers
  have h_snd : ∀ᵐ p ∂(μ.prod μ), ∃ T ∈ P.parts, p.2 ∈ T :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd P.ae_covers
  -- For a.e. point, both coordinates are in positive-measure cells.
  -- The union of null cells has measure zero, so a.e. every point is in a non-null cell.
  have h_non_null : ∀ᵐ x ∂μ, ∃ S ∈ P.parts, x ∈ S ∧ μ S ≠ 0 := by
    have h_null_union : μ (⋃ S ∈ P.parts.filter (fun S => μ S = 0), S) = 0 :=
      le_antisymm
        ((measure_biUnion_finset_le _ _).trans_eq
          (Finset.sum_eq_zero (fun S hS => (Finset.mem_filter.mp hS).2)))
        (zero_le)
    have h_not_in_null : ∀ᵐ x ∂μ,
        x ∉ ⋃ S ∈ P.parts.filter (fun S => μ S = 0), S :=
      compl_mem_ae_iff.mpr h_null_union
    filter_upwards [P.ae_covers, h_not_in_null] with x ⟨S, hS, hxS⟩ hx_not_null
    exact ⟨S, hS, hxS, fun h_eq =>
      hx_not_null (Set.mem_biUnion (Finset.mem_filter.mpr ⟨hS, h_eq⟩) hxS)⟩
  have h_pos_fst : ∀ᵐ p ∂(μ.prod μ), ∃ S ∈ P.parts, p.1 ∈ S ∧ μ S ≠ 0 :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst h_non_null
  have h_pos_snd : ∀ᵐ p ∂(μ.prod μ), ∃ T ∈ P.parts, p.2 ∈ T ∧ μ T ≠ 0 :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd h_non_null
  filter_upwards [h1, h2, h_pos_fst, h_pos_snd] with p hp1 hp2
      ⟨S, hS, hpS, hS_pos⟩ ⟨T, hT, hpT, hT_pos⟩
  rw [hp1, hp2,
      mkStepFun_eq_at' P c₁ hS hT (Set.mem_prod.mpr ⟨hpS, hpT⟩),
      mkStepFun_eq_at' P c₂ hS hT (Set.mem_prod.mpr ⟨hpS, hpT⟩)]
  exact h_agree S hS T hT hS_pos hT_pos

/-- Given a partition with a sub-enumeration of cells and type class functions,
if type class weight sums match, there exists a MP bijection mapping each
sub-enumerated cell to a cell in the corresponding type class.

**Sorry traces to**: `MeasurePreserving.exists_common_extension` (Rokhlin's theorem).
Requires `[NoAtoms μ]` for mass redistribution within type classes. -/
private theorem exists_type_class_mp_bijection
    (P : MeasurablePartition α μ) {k k' : ℕ} (ι : Fin k → Set α)
    (hι : ∀ i, ι i ∈ P.parts) (hι_surj : ∀ S ∈ P.parts, ∃ i, ι i = S)
    (hι_inj : Function.Injective ι)
    (embed : Fin k' → Fin k)
    (hembed_inj : Function.Injective embed)
    {T : ℕ} (type_c type_c' : Fin k' → Fin T)
    (h_weight : ∀ t : Fin T,
      ∑ i ∈ Finset.univ.filter (fun i => type_c i = t), (μ (ι (embed i))).toReal =
      ∑ i ∈ Finset.univ.filter (fun i => type_c' i = t), (μ (ι (embed i))).toReal) :
    ∃ (e : α ≃ᵐ α) (he : MeasurePreserving e μ μ),
      ∀ i : Fin k', ∀ᵐ x ∂μ,
        x ∈ ι (embed i) → ∃ j : Fin k', type_c i = type_c' j ∧ e x ∈ ι (embed j) := by
  classical
  -- Handle trivial case
  by_cases hk'0 : k' = 0
  · subst hk'0
    exact ⟨MeasurableEquiv.refl α, MeasurePreserving.id μ, fun i => i.elim0⟩
  -- Measure finiteness helper
  have h_ne_top : ∀ j : Fin k, μ (ι j) ≠ ⊤ :=
    fun j => ne_top_of_le_ne_top (measure_ne_top μ _) (measure_mono (Set.subset_univ _))
  -- Good types: source weight sum is positive (⟹ both fibers nonempty by h_weight)
  let goodT : Finset (Fin T) := Finset.univ.filter (fun t =>
    0 < ∑ i ∈ Finset.univ.filter (fun i : Fin k' => type_c i = t), (μ (ι (embed i))).toReal)
  -- Type-class union for a given type function
  let union_fn (tf : Fin k' → Fin T) (t : Fin T) : Set α :=
    ⋃ i ∈ (Finset.univ.filter (fun i : Fin k' => tf i = t)), ι (embed i)
  -- Waste set for a given type function
  let waste_fn (tf : Fin k' → Fin T) : Set α :=
    (⋃ i ∈ (Finset.univ.filter (fun i : Fin k' => tf i ∉ goodT)), ι (embed i)) ∪
    (⋃ j ∈ (Finset.univ.filter (fun j : Fin k => j ∉ Finset.univ.image embed)), ι j)
  -- Helper: disjoint biUnions from disjoint Finset indices
  have disjoint_cells : ∀ (A B : Finset (Fin k)), Disjoint A B →
      Disjoint (⋃ j ∈ A, ι j) (⋃ j ∈ B, ι j) := by
    intro A B hAB
    simp only [Set.disjoint_left]
    intro x hxA hxB
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp hxA
    obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.mp hxB
    have hab : a = b := by
      by_contra hne
      exact Set.disjoint_left.mp (P.pairwiseDisjoint (hι a) (hι b)
        (fun h => hne (hι_inj h))) hxa hxb
    exact Finset.disjoint_left.mp hAB ha (hab ▸ hb)
  -- Cell index Finsets
  let cells_union (tf : Fin k' → Fin T) (t : Fin T) : Finset (Fin k) :=
    (Finset.univ.filter (fun i : Fin k' => tf i = t)).image embed
  let cells_waste (tf : Fin k' → Fin T) : Finset (Fin k) :=
    (Finset.univ.filter (fun i : Fin k' => tf i ∉ goodT)).image embed ∪
    Finset.univ.filter (fun j : Fin k => j ∉ Finset.univ.image embed)
  -- union_fn = biUnion over cells_union
  have union_fn_eq : ∀ tf t, union_fn tf t = ⋃ j ∈ cells_union tf t, ι j := by
    intro tf t; ext x
    simp only [union_fn, cells_union, Set.mem_iUnion, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, exists_prop]
    exact ⟨fun ⟨i, hi, hx⟩ => ⟨embed i, ⟨i, hi, rfl⟩, hx⟩,
           fun ⟨_, ⟨i, hi, rfl⟩, hx⟩ => ⟨i, hi, hx⟩⟩
  -- waste_fn = biUnion over cells_waste
  have waste_fn_eq : ∀ tf, waste_fn tf = ⋃ j ∈ cells_waste tf, ι j := by
    intro tf; ext x
    simp only [waste_fn, cells_waste, Set.mem_union, Set.mem_iUnion, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop]
    constructor
    · rintro (⟨i, hi, hx⟩ | ⟨j, hj, hx⟩)
      · exact ⟨embed i, Or.inl ⟨i, hi, rfl⟩, hx⟩
      · exact ⟨j, Or.inr hj, hx⟩
    · rintro ⟨j, hj | hj, hx⟩
      · obtain ⟨i, hi, rfl⟩ := hj; exact Or.inl ⟨i, hi, hx⟩
      · exact Or.inr ⟨j, hj, hx⟩
  -- cells_union for different types are Finset-disjoint
  have cells_union_disj : ∀ tf (t₁ t₂ : Fin T), t₁ ≠ t₂ →
      Disjoint (cells_union tf t₁) (cells_union tf t₂) := by
    intro tf t₁ t₂ hne; rw [Finset.disjoint_left]
    intro j hj₁ hj₂
    obtain ⟨i₁, hi₁, rfl⟩ := Finset.mem_image.mp hj₁
    obtain ⟨i₂, hi₂, he⟩ := Finset.mem_image.mp hj₂
    have h1 := (Finset.mem_filter.mp hi₁).2
    have h2 := (Finset.mem_filter.mp hi₂).2
    have h3 := hembed_inj he; subst h3
    exact hne (h1.symm.trans h2)
  -- cells_union vs cells_waste are Finset-disjoint
  have cells_uw_disj : ∀ tf t, t ∈ goodT →
      Disjoint (cells_union tf t) (cells_waste tf) := by
    intro tf t ht; rw [Finset.disjoint_left]
    intro j hj₁ hj₂
    obtain ⟨i₁, hi₁, rfl⟩ := Finset.mem_image.mp hj₁
    have h1 := (Finset.mem_filter.mp hi₁).2  -- tf i₁ = t
    rcases Finset.mem_union.mp hj₂ with hj₂l | hj₂r
    · -- embed i₁ ∈ image of bad-type cells
      obtain ⟨i₂, hi₂, he⟩ := Finset.mem_image.mp hj₂l
      have h3 := hembed_inj he; subst h3
      exact (Finset.mem_filter.mp hi₂).2 (h1 ▸ ht)
    · -- embed i₁ ∈ filter (∉ image embed), contradiction
      exact absurd (Finset.mem_image.mpr ⟨i₁, Finset.mem_univ _, rfl⟩)
        (Finset.mem_filter.mp hj₂r).2
  -- Every cell index lands in waste or some union
  have cells_cover : ∀ tf (j : Fin k),
      j ∈ cells_waste tf ∨ ∃ t ∈ goodT, j ∈ cells_union tf t := by
    intro tf j
    by_cases hj : j ∈ Finset.univ.image embed
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
      by_cases ht : tf i ∈ goodT
      · exact Or.inr ⟨tf i, ht, Finset.mem_image.mpr
          ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩⟩
      · exact Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
          ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, rfl⟩)))
    · exact Or.inl (Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)))
  -- Build coarsened partition from a type function
  -- (use let for definitional transparency)
  let mkPartition (tf : Fin k' → Fin T)
      (_ : ∀ t ∈ goodT, (Finset.univ.filter (fun i : Fin k' => tf i = t)).Nonempty) :
      MeasurablePartition α μ := {
    parts := insert (waste_fn tf) (goodT.image (union_fn tf))
    measurable_parts := by
      intro S hS
      simp only [Finset.mem_insert, Finset.mem_image] at hS
      rcases hS with rfl | ⟨t, _, rfl⟩
      · -- waste_fn tf = union of two biUnions
        apply MeasurableSet.union
        · exact MeasurableSet.iUnion (fun i => MeasurableSet.iUnion fun _ =>
            P.measurable_parts _ (hι (embed i)))
        · exact MeasurableSet.iUnion (fun j => MeasurableSet.iUnion fun _ =>
            P.measurable_parts _ (hι j))
      · -- union_fn tf t = biUnion of measurable sets
        exact MeasurableSet.iUnion (fun i => MeasurableSet.iUnion fun _ =>
          P.measurable_parts _ (hι (embed i)))
    pairwiseDisjoint := by
      intro S hS T hT hST
      simp only [Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff,
        Set.mem_image, Finset.mem_coe] at hS hT
      rw [Function.onFun_apply, id, id]
      rcases hS with rfl | ⟨t₁, ht₁, rfl⟩ <;> rcases hT with rfl | ⟨t₂, ht₂, rfl⟩
      · exact absurd rfl hST
      · rw [waste_fn_eq, union_fn_eq]
        exact disjoint_cells _ _ (cells_uw_disj tf t₂ ht₂).symm
      · rw [union_fn_eq, waste_fn_eq]
        exact disjoint_cells _ _ (cells_uw_disj tf t₁ ht₁)
      · rw [union_fn_eq, union_fn_eq]
        exact disjoint_cells _ _ (cells_union_disj tf t₁ t₂ (fun h => hST (by rw [h])))
    ae_covers := by
      filter_upwards [P.ae_covers] with x ⟨S, hS, hxS⟩
      obtain ⟨j, rfl⟩ := hι_surj S hS
      rcases cells_cover tf j with hw | ⟨t, ht, hcell⟩
      · exact ⟨waste_fn tf, Finset.mem_insert_self _ _,
          (waste_fn_eq tf) ▸ Set.mem_biUnion hw hxS⟩
      · exact ⟨union_fn tf t, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ht),
          (union_fn_eq tf t) ▸ Set.mem_biUnion hcell hxS⟩
  }
  -- Source fiber nonemptiness
  have h_src_ne : ∀ t ∈ goodT,
      (Finset.univ.filter (fun i : Fin k' => type_c i = t)).Nonempty := by
    intro t ht
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp only [goodT, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [h] at ht; simp at ht
  -- Target fiber nonemptiness (from h_weight + positive source sum)
  have h_tgt_ne : ∀ t ∈ goodT,
      (Finset.univ.filter (fun i : Fin k' => type_c' i = t)).Nonempty := by
    intro t ht
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp only [goodT, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    have := (h_weight t).symm; rw [h] at this; simp at this; linarith
  let P_src := mkPartition type_c h_src_ne
  let P_tgt := mkPartition type_c' h_tgt_ne
  -- union membership in coarsened partition
  have h_union_mem : ∀ (tf : Fin k' → Fin T) h_ne (t : Fin T), t ∈ goodT →
      union_fn tf t ∈ (mkPartition tf h_ne).parts :=
    fun _ _ t ht => Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ht)
  -- Disjointness of union filters for measure_biUnion_finset
  have h_embed_disj : ∀ (tf : Fin k' → Fin T) (t : Fin T),
      Set.PairwiseDisjoint
        (Finset.univ.filter (fun i : Fin k' => tf i = t) : Set (Fin k'))
        (fun i => ι (embed i)) := by
    intro tf t i₁ hi₁ i₂ hi₂ hne
    exact P.pairwiseDisjoint (hι _) (hι _) (fun h => hne (hembed_inj (hι_inj h)))
  -- Measure matching: μ(union_fn type_c t) = μ(union_fn type_c' t) for good t
  have h_meas_match : ∀ t ∈ goodT, μ (union_fn type_c t) = μ (union_fn type_c' t) := by
    intro t _
    show μ (⋃ i ∈ Finset.univ.filter (type_c · = t), ι (embed i)) =
         μ (⋃ i ∈ Finset.univ.filter (type_c' · = t), ι (embed i))
    rw [measure_biUnion_finset (h_embed_disj type_c t)
          (fun i _ => P.measurable_parts _ (hι (embed i))),
        measure_biUnion_finset (h_embed_disj type_c' t)
          (fun i _ => P.measurable_parts _ (hι (embed i)))]
    have h_ne_s := ENNReal.sum_ne_top.mpr
      (fun i (_ : i ∈ Finset.univ.filter (type_c · = t)) => h_ne_top (embed i))
    have h_ne_t := ENNReal.sum_ne_top.mpr
      (fun i (_ : i ∈ Finset.univ.filter (type_c' · = t)) => h_ne_top (embed i))
    rw [← ENNReal.toReal_eq_toReal_iff' h_ne_s h_ne_t,
        ENNReal.toReal_sum (fun i _ => h_ne_top (embed i)),
        ENNReal.toReal_sum (fun i _ => h_ne_top (embed i))]
    exact h_weight t
  -- Injectivity: union_fn is injective on goodT for type_c and type_c'
  -- Key: t ∈ goodT → μ(union) > 0 → union ≠ ∅; different types → disjoint → distinct
  have h_pos_measure_src : ∀ t ∈ goodT, μ (union_fn type_c t) ≠ 0 := by
    intro t ht
    have h_pos := (Finset.mem_filter.mp ht).2
    show μ (⋃ i ∈ Finset.univ.filter (type_c · = t), ι (embed i)) ≠ 0
    rw [measure_biUnion_finset (h_embed_disj type_c t)
      (fun i _ => P.measurable_parts _ (hι (embed i)))]
    intro h_zero
    have h_toReal := ENNReal.toReal_sum
      (s := Finset.univ.filter (type_c · = t))
      (fun i _ => h_ne_top (embed i))
    linarith [h_toReal ▸ (show (0 : ℝ≥0∞).toReal = (0 : ℝ) from rfl) ▸
      congr_arg ENNReal.toReal h_zero]
  have h_pos_measure_tgt : ∀ t ∈ goodT, μ (union_fn type_c' t) ≠ 0 := by
    intro t ht
    rw [← h_meas_match t ht]; exact h_pos_measure_src t ht
  -- Index good types by Fin
  let eG := goodT.equivFin
  -- Injectivity of src through equivFin
  have h_src_inj : Function.Injective
      (fun i : Fin goodT.card => union_fn type_c ((eG.symm i : ↥goodT).val)) := by
    intro i₁ i₂ h_eq
    by_contra hne
    have hv : (eG.symm i₁ : ↥goodT).val ≠ (eG.symm i₂ : ↥goodT).val :=
      fun he => hne (eG.symm.injective (Subtype.val_injective he))
    have h_disj := disjoint_cells _ _ (cells_union_disj type_c _ _ hv)
    have h_eq_expanded : ⋃ j ∈ cells_union type_c (eG.symm i₁).val, ι j =
                         ⋃ j ∈ cells_union type_c (eG.symm i₂).val, ι j := by
      rw [← union_fn_eq type_c (eG.symm i₁).val, ← union_fn_eq type_c (eG.symm i₂).val]
      exact h_eq
    rw [h_eq_expanded] at h_disj
    have h_empty : ⋃ j ∈ cells_union type_c (eG.symm i₂).val, ι j = ⊥ := disjoint_self.mp h_disj
    rw [← union_fn_eq type_c (eG.symm i₂).val] at h_empty
    simp only [show (⊥ : Set α) = ∅ from rfl] at h_empty
    exact h_pos_measure_src _ (eG.symm i₂).prop (h_empty ▸ measure_empty)
  have h_tgt_inj : Function.Injective
      (fun i : Fin goodT.card => union_fn type_c' ((eG.symm i : ↥goodT).val)) := by
    intro i₁ i₂ h_eq
    by_contra hne
    have hv : (eG.symm i₁ : ↥goodT).val ≠ (eG.symm i₂ : ↥goodT).val :=
      fun he => hne (eG.symm.injective (Subtype.val_injective he))
    have h_disj := disjoint_cells _ _ (cells_union_disj type_c' _ _ hv)
    have h_eq_expanded : ⋃ j ∈ cells_union type_c' (eG.symm i₁).val, ι j =
                         ⋃ j ∈ cells_union type_c' (eG.symm i₂).val, ι j := by
      rw [← union_fn_eq type_c' (eG.symm i₁).val, ← union_fn_eq type_c' (eG.symm i₂).val]
      exact h_eq
    rw [h_eq_expanded] at h_disj
    have h_empty : ⋃ j ∈ cells_union type_c' (eG.symm i₂).val, ι j = ⊥ := disjoint_self.mp h_disj
    rw [← union_fn_eq type_c' (eG.symm i₂).val] at h_empty
    simp only [show (⊥ : Set α) = ∅ from rfl] at h_empty
    exact h_pos_measure_tgt _ (eG.symm i₂).prop (h_empty ▸ measure_empty)
  -- Apply controlled cell alignment
  obtain ⟨e, he, h_align⟩ := MeasurePreserving.exists_controlled_cell_alignment P_src P_tgt
    (fun i => union_fn type_c ((eG.symm i : ↥goodT).val))
    (fun i => union_fn type_c' ((eG.symm i : ↥goodT).val))
    (fun i => h_union_mem type_c h_src_ne _ (eG.symm i).prop)
    (fun i => h_union_mem type_c' h_tgt_ne _ (eG.symm i).prop)
    h_src_inj h_tgt_inj
    (fun i => h_meas_match _ (eG.symm i).prop)
  -- Derive conclusion
  refine ⟨e, he, fun i => ?_⟩
  by_cases h_good : type_c i ∈ goodT
  · -- Good type: alignment maps union to union, extract target cell
    set idx := eG ⟨type_c i, h_good⟩ with idx_def
    have hidx : (eG.symm idx : ↥goodT).val = type_c i := by simp [idx_def]
    filter_upwards [h_align idx] with x hx hxi
    have hx_mem : x ∈ union_fn type_c ((eG.symm idx : ↥goodT).val) :=
      hidx ▸ Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, hxi⟩
    have : e x ∈ union_fn type_c' ((eG.symm idx : ↥goodT).val) := hx hx_mem
    rw [hidx] at this
    have h_eq := union_fn_eq type_c' (type_c i)
    rw [h_eq] at this
    obtain ⟨j, hj, hej⟩ := Set.mem_iUnion₂.mp this
    -- j : Fin k from cells_union, need to find i' : Fin k' with embed i' = j
    obtain ⟨i', hi'_embed⟩ := Finset.mem_image.mp hj
    exact ⟨i', (Finset.mem_filter.mp hi'_embed.1).2.symm, hi'_embed.2 ▸ hej⟩
  · -- Bad type: μ(ι(embed i)) = 0, conclusion is vacuously true
    have h_zero : μ (ι (embed i)) = 0 := by
      have h_sum_zero : ∑ j ∈ Finset.univ.filter (type_c · = type_c i),
          (μ (ι (embed j))).toReal = 0 := by
        by_contra h_pos; push Not at h_pos
        exact h_good (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          lt_of_le_of_ne (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))
            (Ne.symm h_pos)⟩)
      have h_all_zero := (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ => ENNReal.toReal_nonneg)).mp h_sum_zero
      have h_i_zero := h_all_zero i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
      exact ((ENNReal.toReal_eq_zero_iff _).mp h_i_zero).resolve_right (h_ne_top (embed i))
    have h_ae : ∀ᵐ x ∂μ, x ∉ ι (embed i) := by
      rw [ae_iff]
      simp only [Set.compl_setOf, not_not]
      exact h_zero
    filter_upwards [h_ae] with x hx hxi
    exact absurd hxi hx

/-- **Algebraic determination for step graphons (measure-theoretic version).**

Given step graphons on the same partition with equal homomorphism densities for
all graphs, there exists a measure-preserving bijection `e` that makes the
pullback of one step graphon equal the other.

The proof decomposes into three steps, each depending on a sorry'd axiom:

1. **homDensity → weightedHomSum bridge**: Decompose the pi-integral defining
   `homDensity` over partition cells. For a step graphon `mkStepGraphon P c`,
   the integrand is constant on products of cells, so the integral becomes
   a finite sum `weightedHomSum n F c_fin w` where `c_fin` is the coefficient
   matrix indexed by `Fin k` and `w` is the cell-measure vector.

2. **Algebraic core**: Restrict to positive-measure cells and apply
   `matrix_quotient_of_weightedHomSum_eq` to obtain type class functions
   `type_c, type_c' : Fin k' → Fin T` such that both matrices are
   block-constant on type classes, entries match across matrices for
   matching types, and type class weight sums match.

3. **Measure-preserving realization**: Construct a measure-preserving bijection
   `e : α ≃ᵐ α` via `exists_type_class_mp_bijection` that maps each cell
   to a cell in the corresponding type class. Since the coefficients match
   across type classes, the pullback `pullback (mkStepGraphon P c') e` then
   equals `mkStepGraphon P c` a.e.

**Sorry traces to**: `MeasurePreserving.exists_common_extension` (Rokhlin's theorem)
only — the algebraic core `matrix_quotient_of_weightedHomSum_eq` (Lovász [2012]
Theorem 5.30) is PROVED as of 2026-07-06 (axiom-clean). -/
private theorem exists_pullback_eq_of_step_homDensity_eq
    (P : MeasurablePartition α μ) (c c' : Set α → Set α → ℝ)
    (hc_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T = c T S)
    (hc_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T ∈ Set.Icc 0 1)
    (hc'_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c' S T = c' T S)
    (hc'_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c' S T ∈ Set.Icc 0 1)
    (h_hom : ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
      homDensity F (mkStepGraphon P c hc_symm hc_mem) =
      homDensity F (mkStepGraphon P c' hc'_symm hc'_mem)) :
    ∃ (e : α ≃ᵐ α) (he : MeasurePreserving e μ μ),
      pullback (mkStepGraphon P c' hc'_symm hc'_mem) e he =
      mkStepGraphon P c hc_symm hc_mem := by
  classical
  -- Step 1: Enumerate P.parts as ι : Fin k → Set α
  set k := P.parts.card with hk_def
  let ι_equiv : ↥P.parts ≃ Fin k := P.parts.equivFin
  let ι : Fin k → Set α := fun i => (ι_equiv.symm i : Set α)
  have hι : ∀ i, ι i ∈ P.parts := fun i => (ι_equiv.symm i).prop
  have hι_inj : Function.Injective ι := by
    intro i j hij
    exact ι_equiv.symm.injective (Subtype.val_injective hij)
  have hι_surj : ∀ S ∈ P.parts, ∃ i, ι i = S := by
    intro S hS
    exact ⟨ι_equiv ⟨S, hS⟩, by simp [ι]⟩
  -- Step 2: Bridge — convert homDensity to weightedHomSum
  have h_bridge := homDensity_mkStepGraphon_eq_weightedHomSum P c hc_symm hc_mem ι hι hι_surj hι_inj
  have h_bridge' := homDensity_mkStepGraphon_eq_weightedHomSum P c' hc'_symm hc'_mem ι hι hι_surj hι_inj
  -- Combine: weightedHomSum equality
  have h_whs_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      weightedHomSum n F (fun i j => c (ι i) (ι j)) (fun i => (μ (ι i)).toReal) =
      weightedHomSum n F (fun i j => c' (ι i) (ι j)) (fun i => (μ (ι i)).toReal) := by
    intro n F _
    rw [← h_bridge n F, ← h_bridge' n F]
    exact h_hom n F
  -- Step 3: Restrict to positive-measure cells
  set pos_idx := Finset.univ.filter (fun i : Fin k => 0 < (μ (ι i)).toReal) with hpos_idx_def
  set k' := pos_idx.card with hk'_def
  -- Equivalence between pos_idx and Fin k'
  let e_pos : ↥pos_idx ≃ Fin k' := pos_idx.equivFin
  -- Embedding of positive indices back into Fin k
  let embed : Fin k' → Fin k := fun j => (e_pos.symm j : Fin k)
  have hembed_mem : ∀ j, embed j ∈ pos_idx := fun j => (e_pos.symm j).prop
  have hembed_pos : ∀ j, 0 < (μ (ι (embed j))).toReal := by
    intro j; exact (Finset.mem_filter.mp (hembed_mem j)).2
  have hembed_inj : Function.Injective embed := by
    intro j₁ j₂ h; exact e_pos.symm.injective (Subtype.val_injective h)
  -- Define restricted coefficient matrices and weights on Fin k'
  let c_pos : Fin k' → Fin k' → ℝ := fun i j => c (ι (embed i)) (ι (embed j))
  let c'_pos : Fin k' → Fin k' → ℝ := fun i j => c' (ι (embed i)) (ι (embed j))
  let w_pos : Fin k' → ℝ := fun j => (μ (ι (embed j))).toReal
  -- Symmetry and bounds for restricted matrices
  have hc_pos_symm : ∀ i j : Fin k', c_pos i j = c_pos j i :=
    fun i j => hc_symm _ (hι _) _ (hι _)
  have hc'_pos_symm : ∀ i j : Fin k', c'_pos i j = c'_pos j i :=
    fun i j => hc'_symm _ (hι _) _ (hι _)
  have hc_pos_mem : ∀ i j : Fin k', c_pos i j ∈ Set.Icc 0 1 :=
    fun i j => hc_mem _ (hι _) _ (hι _)
  have hc'_pos_mem : ∀ i j : Fin k', c'_pos i j ∈ Set.Icc 0 1 :=
    fun i j => hc'_mem _ (hι _) _ (hι _)
  -- Step 4: Show restricted weightedHomSum equality
  -- Terms where σ(v) maps to a zero-weight cell vanish (weight product = 0).
  -- So weightedHomSum on Fin k with zero weights = weightedHomSum on Fin k' with positive weights.
  have h_whs_restrict : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      weightedHomSum n F c_pos w_pos = weightedHomSum n F c'_pos w_pos := by
    intro n F _
    -- Both equal the corresponding full-size weightedHomSum (zero-weight terms vanish)
    -- The full-size sums are equal by h_whs_eq.
    -- This is a combinatorial identity: filtering zero-weight terms from a sum.
    -- We prove it by showing each full sum equals the restricted sum.
    have h_vanish : ∀ (M : Fin k → Fin k → ℝ) (σ : Fin n → Fin k),
        (∃ v, σ v ∉ pos_idx) →
        (∏ v : Fin n, (μ (ι (σ v))).toReal) * ∏ e ∈ F.edgeFinset,
          M (σ (Quot.out e).1) (σ (Quot.out e).2) = 0 := by
      intro M σ ⟨v, hv⟩
      apply mul_eq_zero_of_left
      apply Finset.prod_eq_zero (Finset.mem_univ v)
      have hv' : ¬(0 < (μ (ι (σ v))).toReal) := by
        intro hpos; exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩)
      linarith [ENNReal.toReal_nonneg (a := μ (ι (σ v)))]
    -- Define the injection from (Fin n → Fin k') to (Fin n → Fin k) via embed
    have h_sum_eq : ∀ (M : Fin k → Fin k → ℝ),
        weightedHomSum n F M (fun i => (μ (ι i)).toReal) =
        weightedHomSum n F (fun i j => M (embed i) (embed j))
          (fun j => (μ (ι (embed j))).toReal) := by
      intro M
      simp only [weightedHomSum]
      -- Split the sum over Fin n → Fin k into:
      -- (a) σ with range ⊆ pos_idx: these correspond bijectively to Fin n → Fin k'
      -- (b) σ with some value outside pos_idx: these vanish
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
          (p := fun σ : Fin n → Fin k => ∀ v, σ v ∈ pos_idx)]
      have h_bad_zero : (∑ x ∈ Finset.univ.filter
          (fun σ : Fin n → Fin k => ¬∀ v, σ v ∈ pos_idx),
          (∏ v : Fin n, (μ (ι (x v))).toReal) *
          ∏ e ∈ F.edgeFinset, M (x (Quot.out e).1) (x (Quot.out e).2)) = 0 := by
        apply Finset.sum_eq_zero; intro σ hσ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
        push Not at hσ; exact h_vanish M σ hσ
      rw [h_bad_zero, add_zero]
      -- Now biject: ∑ (good filtered Fin k) = ∑ (univ Fin k')
      symm
      apply Finset.sum_nbij (fun (τ : Fin n → Fin k') => embed ∘ τ)
      · intro τ _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
        intro v; exact hembed_mem (τ v)
      · intro τ₁ τ₂ _ _ h
        exact funext (fun v => hembed_inj (congr_fun h v))
      · -- SurjOn: for σ in filtered, find τ in univ with embed ∘ τ = σ
        intro σ hσ
        rw [Finset.coe_filter] at hσ
        obtain ⟨_, hσ_pos⟩ := hσ
        exact ⟨fun v => e_pos ⟨σ v, hσ_pos v⟩, Finset.mem_coe.mpr (Finset.mem_univ _),
          funext (fun v => by simp [embed, Function.comp])⟩
      · intro τ _; simp [Function.comp]
    rw [← h_sum_eq (fun i j => c (ι i) (ι j)),
        ← h_sum_eq (fun i j => c' (ι i) (ι j))]
    exact h_whs_eq n F
  -- Step 5: Apply algebraic core (quotient form) on positive-weight sub-matrix
  obtain ⟨T_count, type_c, type_c', _, _, h_entry, h_type_weight⟩ :=
    matrix_quotient_of_weightedHomSum_eq c_pos c'_pos
      hc_pos_symm hc'_pos_symm hc_pos_mem hc'_pos_mem w_pos hembed_pos h_whs_restrict
  -- Step 6: Construct MP bijection via type class matching
  obtain ⟨e, he, h_cell_type⟩ := exists_type_class_mp_bijection P ι hι hι_surj hι_inj
    embed hembed_inj type_c type_c' h_type_weight
  -- Step 7: Show pullback matches a.e.
  -- The pullback of mkStepGraphon P c' by e equals mkStepGraphon P c a.e.
  -- For a.e. (x,y): x ∈ ι(embed i), y ∈ ι(embed j) for positive-measure cells,
  -- e maps x to ι(embed i') with type_c i = type_c' i',
  -- e maps y to ι(embed j') with type_c j = type_c' j',
  -- so c(ι(embed i), ι(embed j)) = c'(ι(embed i'), ι(embed j')) by h_entry.
  -- For zero-measure cells, a.e. no point lands there.
  refine ⟨e, he, ?_⟩
  apply Graphon.ext; apply SymmKernel.ext; apply AEEqFun.ext
  -- LHS a.e.: pullback value
  have h_pb := pullback_ae (mkStepGraphon P c' hc'_symm hc'_mem) (⇑e) he
  -- mkStepGraphon values a.e.
  have h_c'_ae : ∀ᵐ q ∂(μ.prod μ),
      (mkStepGraphon P c' hc'_symm hc'_mem).toAEEqFun q = mkStepFun P c' q :=
    AEEqFun.coeFn_mk (mkStepFun P c') (mkStepFun_measurable' P c').aestronglyMeasurable
  have h_c'_lifted : ∀ᵐ p ∂(μ.prod μ),
      (mkStepGraphon P c' hc'_symm hc'_mem).toAEEqFun (e p.1, e p.2) =
      mkStepFun P c' (e p.1, e p.2) := by
    have hqmp : Measure.QuasiMeasurePreserving (Prod.map e e) (μ.prod μ) (μ.prod μ) :=
      (SymmKernel.measurePreserving_prodMap_self he).quasiMeasurePreserving
    exact hqmp.ae h_c'_ae
  have h_c_ae : ∀ᵐ p ∂(μ.prod μ),
      (mkStepGraphon P c hc_symm hc_mem).toAEEqFun p = mkStepFun P c p :=
    AEEqFun.coeFn_mk (mkStepFun P c) (mkStepFun_measurable' P c).aestronglyMeasurable
  -- For a.e. x, x is in a positive-measure cell (null cells are negligible)
  have h_non_null : ∀ᵐ x ∂μ, ∃ S ∈ P.parts, x ∈ S ∧ μ S ≠ 0 := by
    have h_null_union : μ (⋃ S ∈ P.parts.filter (fun S => μ S = 0), S) = 0 :=
      le_antisymm
        ((measure_biUnion_finset_le _ _).trans_eq
          (Finset.sum_eq_zero (fun S hS => (Finset.mem_filter.mp hS).2)))
        (zero_le)
    have h_not_in_null : ∀ᵐ x ∂μ,
        x ∉ ⋃ S ∈ P.parts.filter (fun S => μ S = 0), S :=
      compl_mem_ae_iff.mpr h_null_union
    filter_upwards [P.ae_covers, h_not_in_null] with x ⟨S, hS, hxS⟩ hx_not_null
    exact ⟨S, hS, hxS, fun h_eq =>
      hx_not_null (Set.mem_biUnion (Finset.mem_filter.mpr ⟨hS, h_eq⟩) hxS)⟩
  -- For a.e. x, x is in some ι(embed i) (a positive-measure cell)
  have h_pos_cell : ∀ᵐ x ∂μ, ∃ i : Fin k', x ∈ ι (embed i) := by
    filter_upwards [h_non_null] with x ⟨S, hS, hxS, hμS⟩
    obtain ⟨idx, hidx⟩ := hι_surj S hS
    have h_pos : 0 < (μ (ι idx)).toReal := by
      rw [hidx]; exact ENNReal.toReal_pos hμS
        (ne_top_of_le_ne_top (measure_ne_top μ Set.univ) (measure_mono (Set.subset_univ _)))
    have h_mem : idx ∈ pos_idx := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_pos⟩
    exact ⟨e_pos ⟨idx, h_mem⟩, by
      have : embed (e_pos ⟨idx, h_mem⟩) = idx := by
        show (e_pos.symm (e_pos ⟨idx, h_mem⟩) : Fin k) = idx
        simp [Equiv.symm_apply_apply]
      rw [this, hidx]; exact hxS⟩
  -- Lift to product measure
  have h_fst_pos : ∀ᵐ p ∂(μ.prod μ), ∃ i : Fin k', p.1 ∈ ι (embed i) :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst h_pos_cell
  have h_snd_pos : ∀ᵐ p ∂(μ.prod μ), ∃ j : Fin k', p.2 ∈ ι (embed j) :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd h_pos_cell
  -- Lift h_cell_type to product measure
  have h_cell_fst : ∀ i : Fin k', ∀ᵐ p ∂(μ.prod μ),
      p.1 ∈ ι (embed i) → ∃ j : Fin k', type_c i = type_c' j ∧ e p.1 ∈ ι (embed j) :=
    fun i => Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst (h_cell_type i)
  have h_cell_snd : ∀ i : Fin k', ∀ᵐ p ∂(μ.prod μ),
      p.2 ∈ ι (embed i) → ∃ j : Fin k', type_c i = type_c' j ∧ e p.2 ∈ ι (embed j) :=
    fun i => Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd (h_cell_type i)
  -- Combine all cell type conditions
  have h_cell_all_fst : ∀ᵐ p ∂(μ.prod μ), ∀ i : Fin k',
      p.1 ∈ ι (embed i) → ∃ j : Fin k', type_c i = type_c' j ∧ e p.1 ∈ ι (embed j) := by
    rw [Filter.eventually_all]; exact h_cell_fst
  have h_cell_all_snd : ∀ᵐ p ∂(μ.prod μ), ∀ i : Fin k',
      p.2 ∈ ι (embed i) → ∃ j : Fin k', type_c i = type_c' j ∧ e p.2 ∈ ι (embed j) := by
    rw [Filter.eventually_all]; exact h_cell_snd
  -- Now combine everything
  filter_upwards [h_pb, h_c'_lifted, h_c_ae, h_fst_pos, h_snd_pos,
      h_cell_all_fst, h_cell_all_snd] with p h_pb_p h_c'_p h_c_p
      ⟨i, hi⟩ ⟨j, hj⟩ h_e_fst h_e_snd
  -- LHS: pullback value = mkStepFun P c' (e p.1, e p.2)
  rw [h_pb_p, h_c'_p]
  -- RHS: mkStepGraphon P c value = mkStepFun P c (p.1, p.2)
  rw [h_c_p]
  -- Now: mkStepFun P c' (e p.1, e p.2) = mkStepFun P c (p.1, p.2)
  -- We know: p.1 ∈ ι(embed i), p.2 ∈ ι(embed j)
  -- By h_e_fst: ∃ i', type_c i = type_c' i' ∧ e p.1 ∈ ι(embed i')
  -- By h_e_snd: ∃ j', type_c j = type_c' j' ∧ e p.2 ∈ ι(embed j')
  obtain ⟨i', hti, he_fst⟩ := h_e_fst i hi
  obtain ⟨j', htj, he_snd⟩ := h_e_snd j hj
  rw [mkStepFun_eq_at' P c' (hι (embed i')) (hι (embed j'))
      (Set.mem_prod.mpr ⟨he_fst, he_snd⟩),
    mkStepFun_eq_at' P c (hι (embed i)) (hι (embed j))
      (Set.mem_prod.mpr ⟨hi, hj⟩)]
  -- c(ι(embed i), ι(embed j)) = c'(ι(embed i'), ι(embed j'))
  -- by h_entry with type_c i = type_c' i' and type_c j = type_c' j'
  -- h_entry : ∀ i j i' j', type_c i = type_c' i' → type_c j = type_c' j' →
  --           c_pos i j = c'_pos i' j'
  -- c_pos i j = c(ι(embed i), ι(embed j)) and c'_pos i' j' = c'(ι(embed i'), ι(embed j'))
  exact (h_entry i j i' j' hti htj).symm

/-- Step graphons on the same partition with equal hom densities for all graphs
have cut distance zero.

**Proof**: By `exists_pullback_eq_of_step_homDensity_eq`, there is a
measure-preserving bijection `e` with `pullback (mkStepGraphon P c') e = mkStepGraphon P c`.
Then `cutDistance_pullback_eq_zero` gives `cutDistance W' (pullback W' e) = 0`,
and substituting the pullback equality yields the result.

**Sorry traces to**: `MeasurePreserving.exists_common_extension` (Rokhlin) only —
the algebraic core is PROVED as of 2026-07-06. -/
private theorem cutDistance_zero_of_step_homDensity_eq
    (P : MeasurablePartition α μ) (c c' : Set α → Set α → ℝ)
    (hc_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T = c T S)
    (hc_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T ∈ Set.Icc 0 1)
    (hc'_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c' S T = c' T S)
    (hc'_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c' S T ∈ Set.Icc 0 1)
    (h_hom : ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
      homDensity F (mkStepGraphon P c hc_symm hc_mem) =
      homDensity F (mkStepGraphon P c' hc'_symm hc'_mem)) :
    cutDistance (mkStepGraphon P c hc_symm hc_mem)
               (mkStepGraphon P c' hc'_symm hc'_mem) = 0 := by
  -- Obtain MP bijection e such that pullback W' e = W
  obtain ⟨e, he, h_eq⟩ := exists_pullback_eq_of_step_homDensity_eq
    P c c' hc_symm hc_mem hc'_symm hc'_mem h_hom
  -- cutDistance W' (pullback W' e) = 0
  have h_zero := cutDistance_pullback_eq_zero (mkStepGraphon P c' hc'_symm hc'_mem) e he
  -- Substitute: pullback W' e = W
  rw [h_eq] at h_zero
  -- cutDistance W W' = cutDistance W' W by symmetry
  rw [cutDistance_symm]
  exact h_zero

end StepInverseCounting

/-! ### Main inverse counting lemma -/

section InverseCounting

variable [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

/- **Simultaneous step approximation with controlled cutDistance.**

Given two graphons U, W with equal homomorphism densities for all graphs,
for any epsilon > 0 there exists a partition P such that:
1. Both `cutNormDiff U (stepify P U) <= epsilon`
2. Both `cutNormDiff W (stepify P W) <= epsilon`
3. `cutDistance (stepify P U) (stepify P W) <= epsilon`

**Proof sketch**: The proof combines three ingredients:
- **Simultaneous regularity (Frieze-Kannan for pairs)**: Start from the trivial
  partition. At each step, if either `cutNormDiff U (stepify P U) > delta` or
  `cutNormDiff W (stepify P W) > delta`, split using `energy_increment_quantitative`.
  The combined energy `energy U P + energy W P` increases by at least `delta^2`
  per step while staying bounded by 2. After at most `ceil(2/delta^2)` steps,
  both cutNormDiff are at most `delta`. The parameter `delta` is chosen small
  enough for condition (3), as described below.

- **Quantitative step ICL**: For step graphons on the same partition P
  with approximately equal hom densities, the cutDistance is controlled.
  This follows from compactness of the coefficient space `[0,1]^{k^2}` plus
  `cutDistance_zero_of_step_homDensity_eq` (the qualitative step ICL).

- **Counting lemma bridge**: Since `t(F, U) = t(F, W)`, the gap
  `|t(F, stepify P U) - t(F, stepify P W)| <= 2|E(F)| * delta` (by the
  counting lemma `homDensity_sub_le`). Choosing `delta` small enough
  relative to the quantitative step ICL parameters ensures condition (3).

The `delta` is determined by a fixed-point argument: let K = regularityBound(delta).
For partitions with at most K cells, the quantitative step ICL gives parameters
(delta_step, N_step). We need `2 * N_step^2 * delta < delta_step`. Since K grows
as delta decreases, this constrains delta from below. A solution always exists
because for fixed K, the step ICL gives fixed positive delta_step.

**Sorry traces to**: `matrix_quotient_of_weightedHomSum_eq` (algebraic core,
Lovasz [2012] Theorem 5.30) + `MeasurePreserving.exists_common_extension`
(Rokhlin's theorem), via `cutDistance_zero_of_step_homDensity_eq`. The
simultaneous regularity is a standard extension of Frieze-Kannan and
does not introduce any new axiom. -/
/-- Simultaneous weak regularity lemma for a pair of graphons.

For any δ > 0, there exists a partition P with at most `4 ^ (2 * (⌈1/δ²⌉ + 1))` parts
such that both `cutNormDiff U (stepify P U) ≤ δ` and `cutNormDiff W (stepify P W) ≤ δ`.

The proof runs the Frieze-Kannan energy increment for both graphons simultaneously:
at each step, if either graphon has large cut norm difference, refine the partition.
The key observation is that `energy_increment_pair` guarantees that refining for one
graphon does not decrease the other's energy (monotonicity of energy under refinement). -/
private theorem simultaneous_regularity [StandardBorelSpace α]
    (U W : Graphon α μ) (δ : ℝ) (hδ : δ > 0) :
    ∃ P : MeasurablePartition α μ,
      P.parts.card ≤ 4 ^ (2 * (Nat.ceil (1 / δ ^ 2) + 1)) ∧
      cutNormDiff U (stepify P U) ≤ δ ∧
      cutNormDiff W (stepify P W) ≤ δ := by
  -- N = max number of iterations before combined energy exceeds 2
  set N : ℕ := 2 * (Nat.ceil (1 / δ ^ 2) + 1) with hN_def
  have hδ2_pos : δ ^ 2 > 0 := by positivity
  -- Main iteration: with n steps of fuel remaining from partition P,
  -- either we find a good partition or combined energy grows too large.
  suffices h_iter : ∀ n : ℕ, n ≤ N → ∀ P : MeasurablePartition α μ,
      P.parts.card ≤ 4 ^ (N - n) →
      ∃ Q : MeasurablePartition α μ,
        Q.parts.card ≤ 4 ^ N ∧
        ((cutNormDiff U (stepify Q U) ≤ δ ∧ cutNormDiff W (stepify Q W) ≤ δ) ∨
         energy U Q + energy W Q ≥ energy U P + energy W P + n * δ ^ 2) by
    let P₀ := trivialPartition (α := α) (μ := μ)
    have hP₀_card : P₀.parts.card ≤ 4 ^ (N - N) := by
      rw [Nat.sub_self, pow_zero, trivialPartition_card]
    obtain ⟨Q, hQ_card, hQ_result⟩ := h_iter N le_rfl P₀ hP₀_card
    rcases hQ_result with ⟨hU, hW⟩ | hQ_energy
    · exact ⟨Q, hQ_card, hU, hW⟩
    · exfalso
      have h1 : energy U Q ≤ 1 := energy_le_one U Q
      have h2 : energy W Q ≤ 1 := energy_le_one W Q
      have h3 : energy U P₀ ≥ 0 := energy_nonneg U P₀
      have h4 : energy W P₀ ≥ 0 := energy_nonneg W P₀
      have h_N_bound : (N : ℝ) * δ ^ 2 > 2 := by
        rw [hN_def]
        push_cast
        have h_ceil : (↑(Nat.ceil (1 / δ ^ 2)) : ℝ) ≥ 1 / δ ^ 2 := Nat.le_ceil _
        have h_key : ↑⌈1 / δ ^ 2⌉₊ * δ ^ 2 ≥ 1 := by
          have := mul_le_mul_of_nonneg_right h_ceil (le_of_lt hδ2_pos)
          rwa [div_mul_cancel₀ 1 (ne_of_gt hδ2_pos)] at this
        nlinarith
      linarith
  -- Prove by induction on n
  intro n
  induction n with
  | zero =>
    intro _hn P hP_card
    exact ⟨P, by calc P.parts.card ≤ 4 ^ (N - 0) := hP_card
                    _ = 4 ^ N := by simp, Or.inr (by simp)⟩
  | succ n ih =>
    intro hn P hP_card
    -- Check if both graphons are already well-approximated
    by_cases h_doneU : cutNormDiff U (stepify P U) ≤ δ
    · by_cases h_doneW : cutNormDiff W (stepify P W) ≤ δ
      · exact ⟨P, by calc P.parts.card ≤ 4 ^ (N - (n + 1)) := hP_card
                        _ ≤ 4 ^ N := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le N _),
            Or.inl ⟨h_doneU, h_doneW⟩⟩
      · -- W is bad: refine for W using energy_increment_pair
        push Not at h_doneW
        obtain ⟨Q, _, hQ_card_le, hQ_energyW, hQ_mono⟩ :=
          energy_increment_pair W P δ hδ h_doneW
        have hQ_card : Q.parts.card ≤ 4 ^ (N - n) := by
          have h1 : N - n = (N - (n + 1)) + 1 := by omega
          calc Q.parts.card ≤ 4 * P.parts.card := hQ_card_le
            _ ≤ 4 * 4 ^ (N - (n + 1)) := Nat.mul_le_mul_left 4 hP_card
            _ = 4 ^ ((N - (n + 1)) + 1) := by ring_nf
            _ = 4 ^ (N - n) := by rw [← h1]
        obtain ⟨R, hR_card, hR_result⟩ := ih (by omega) Q hQ_card
        refine ⟨R, hR_card, ?_⟩
        rcases hR_result with hR_good | hR_energy
        · exact Or.inl hR_good
        · right
          have : (↑(n + 1) : ℝ) = ↑n + 1 := by push_cast; ring
          have hU_mono := hQ_mono U
          calc energy U R + energy W R
              ≥ energy U Q + energy W Q + ↑n * δ ^ 2 := hR_energy
            _ ≥ energy U P + (energy W P + δ ^ 2) + ↑n * δ ^ 2 := by linarith
            _ = energy U P + energy W P + (↑n + 1) * δ ^ 2 := by ring
            _ = energy U P + energy W P + ↑(n + 1) * δ ^ 2 := by rw [this]
    · -- U is bad: refine for U using energy_increment_pair
      push Not at h_doneU
      obtain ⟨Q, _, hQ_card_le, hQ_energyU, hQ_mono⟩ :=
        energy_increment_pair U P δ hδ h_doneU
      have hQ_card : Q.parts.card ≤ 4 ^ (N - n) := by
        have h1 : N - n = (N - (n + 1)) + 1 := by omega
        calc Q.parts.card ≤ 4 * P.parts.card := hQ_card_le
          _ ≤ 4 * 4 ^ (N - (n + 1)) := Nat.mul_le_mul_left 4 hP_card
          _ = 4 ^ ((N - (n + 1)) + 1) := by ring_nf
          _ = 4 ^ (N - n) := by rw [← h1]
      obtain ⟨R, hR_card, hR_result⟩ := ih (by omega) Q hQ_card
      refine ⟨R, hR_card, ?_⟩
      rcases hR_result with hR_good | hR_energy
      · exact Or.inl hR_good
      · right
        have : (↑(n + 1) : ℝ) = ↑n + 1 := by push_cast; ring
        have hW_mono := hQ_mono W
        calc energy U R + energy W R
            ≥ energy U Q + energy W Q + ↑n * δ ^ 2 := hR_energy
          _ ≥ (energy U P + δ ^ 2) + energy W P + ↑n * δ ^ 2 := by linarith
          _ = energy U P + energy W P + (↑n + 1) * δ ^ 2 := by ring
          _ = energy U P + energy W P + ↑(n + 1) * δ ^ 2 := by rw [this]

/-- For step graphons on the same partition, `cutDistance` is bounded by the maximum
coefficient difference. This combines `cutDistance_le_cutNormDiff` with
`cutNormDiff_mkStepGraphon_le`, using the fact that `stepify P V` has the same
underlying function as `mkStepGraphon P (rectAverage V)`. -/
private theorem cutDistance_stepify_le_max_coeff_diff
    (P : MeasurablePartition α μ) (U W : Graphon α μ) (δ : ℝ)
    (hδ : ∀ S ∈ P.parts, ∀ T ∈ P.parts, |rectAverage U S T - rectAverage W S T| ≤ δ) :
    cutDistance (stepify P U) (stepify P W) ≤ δ := by
  -- stepify P V has the same underlying function as mkStepGraphon P (rectAverage V)
  have hRA_symm_U : ∀ S ∈ P.parts, ∀ T ∈ P.parts,
      rectAverage U S T = rectAverage U T S := by
    intro S hS T hT
    exact rectAverage_symm U S T (P.measurableSet_part hS) (P.measurableSet_part hT)
  have hRA_mem_U : ∀ S ∈ P.parts, ∀ T ∈ P.parts,
      rectAverage U S T ∈ Set.Icc 0 1 := by
    intro S hS T hT
    exact rectAverage_mem_Icc U S T (P.measurableSet_part hS) (P.measurableSet_part hT)
  have hRA_symm_W : ∀ S ∈ P.parts, ∀ T ∈ P.parts,
      rectAverage W S T = rectAverage W T S := by
    intro S hS T hT
    exact rectAverage_symm W S T (P.measurableSet_part hS) (P.measurableSet_part hT)
  have hRA_mem_W : ∀ S ∈ P.parts, ∀ T ∈ P.parts,
      rectAverage W S T ∈ Set.Icc 0 1 := by
    intro S hS T hT
    exact rectAverage_mem_Icc W S T (P.measurableSet_part hS) (P.measurableSet_part hT)
  -- Build mkStepGraphon versions
  set V_U := mkStepGraphon P (rectAverage U) hRA_symm_U hRA_mem_U
  set V_W := mkStepGraphon P (rectAverage W) hRA_symm_W hRA_mem_W
  -- stepify P U and V_U have the same underlying function (mkStepFun P (rectAverage ...))
  have h_eq_U : ∀ᵐ p ∂(μ.prod μ),
      (stepify P U).toAEEqFun p = V_U.toAEEqFun p := by
    filter_upwards [stepify_ae P U,
      AEEqFun.coeFn_mk (mkStepFun P (rectAverage U))
        (mkStepFun_measurable' P (rectAverage U)).aestronglyMeasurable]
      with p hp1 hp2
    exact hp1.trans hp2.symm
  have h_eq_W : ∀ᵐ p ∂(μ.prod μ),
      (stepify P W).toAEEqFun p = V_W.toAEEqFun p := by
    filter_upwards [stepify_ae P W,
      AEEqFun.coeFn_mk (mkStepFun P (rectAverage W))
        (mkStepFun_measurable' P (rectAverage W)).aestronglyMeasurable]
      with p hp1 hp2
    exact hp1.trans hp2.symm
  -- cutNormDiff (stepify P U) (stepify P W) = cutNormDiff V_U V_W
  -- (since a.e. equal graphons have the same cutNormDiff)
  have h_cn : cutNormDiff V_U V_W ≤ δ :=
    cutNormDiff_mkStepGraphon_le P (rectAverage U) (rectAverage W)
      hRA_symm_U hRA_mem_U hRA_symm_W hRA_mem_W δ hδ
  -- cutDistance (stepify P U) (stepify P W) = cutDistance V_U V_W
  -- (since a.e. equal graphons have cutDistance 0 between them)
  -- Actually, we need: cutDistance (stepify P U) V_U = 0
  -- This follows from cutNormDiff being 0 (since they're a.e. equal)
  have h_cn_U : cutNormDiff (stepify P U) V_U = 0 := by
    apply le_antisymm _ (cutNormDiff_nonneg _ _)
    unfold cutNormDiff rectIntegralDiff
    apply Real.iSup_le _ le_rfl
    intro S; apply Real.iSup_le _ le_rfl
    intro hS; apply Real.iSup_le _ le_rfl
    intro T; apply Real.iSup_le _ le_rfl
    intro hT
    suffices h : ∫ p in S ×ˢ T,
        ((stepify P U).toAEEqFun p - V_U.toAEEqFun p) ∂(μ.prod μ) = 0 by
      rw [h, abs_zero]
    exact integral_eq_zero_of_ae (ae_restrict_of_ae
      (h_eq_U.mono fun p hp => by simp [hp]))
  have h_cn_W : cutNormDiff (stepify P W) V_W = 0 := by
    apply le_antisymm _ (cutNormDiff_nonneg _ _)
    unfold cutNormDiff rectIntegralDiff
    apply Real.iSup_le _ le_rfl
    intro S; apply Real.iSup_le _ le_rfl
    intro hS; apply Real.iSup_le _ le_rfl
    intro T; apply Real.iSup_le _ le_rfl
    intro hT
    suffices h : ∫ p in S ×ˢ T,
        ((stepify P W).toAEEqFun p - V_W.toAEEqFun p) ∂(μ.prod μ) = 0 by
      rw [h, abs_zero]
    exact integral_eq_zero_of_ae (ae_restrict_of_ae
      (h_eq_W.mono fun p hp => by simp [hp]))
  calc cutDistance (stepify P U) (stepify P W)
      ≤ cutDistance (stepify P U) V_U + cutDistance V_U (stepify P W) :=
        cutDistance_triangle _ _ _
    _ ≤ cutNormDiff (stepify P U) V_U + cutDistance V_U (stepify P W) := by
        linarith [cutDistance_le_cutNormDiff (stepify P U) V_U]
    _ = 0 + cutDistance V_U (stepify P W) := by rw [h_cn_U]
    _ = cutDistance V_U (stepify P W) := zero_add _
    _ ≤ cutDistance V_U V_W + cutDistance V_W (stepify P W) :=
        cutDistance_triangle _ _ _
    _ ≤ cutNormDiff V_U V_W + cutDistance V_W (stepify P W) := by
        linarith [cutDistance_le_cutNormDiff V_U V_W]
    _ ≤ δ + cutDistance V_W (stepify P W) := by linarith
    _ ≤ δ + cutNormDiff V_W (stepify P W) := by
        linarith [cutDistance_le_cutNormDiff V_W (stepify P W)]
    _ = δ + cutNormDiff (stepify P W) V_W := by rw [cutNormDiff_symm]
    _ = δ + 0 := by rw [h_cn_W]
    _ = δ := add_zero _

/-- **Quantitative inverse counting for step graphons on a fixed partition.**

For step graphons on the same partition P, if all homomorphism densities for
graphs up to size m are within δ, then the cut distance is small.

**Proof**: By contradiction + compactness of the coefficient space [0,1]^{k^2}.
If no (δ, m) works, extract sequences of coefficient matrices with converging
subsequences (Bolzano-Weierstrass for [0,1]^{k^2}). The limit coefficients
give step graphons with equal hom densities but cutDistance >= ε, contradicting
`cutDistance_zero_of_step_homDensity_eq`.

**Depends on**: `cutDistance_zero_of_step_homDensity_eq` which traces to
`matrix_quotient_of_weightedHomSum_eq` (algebraic core) +
`MeasurePreserving.exists_common_extension` (Rokhlin). -/
private theorem step_quantitative_icl
    (P : MeasurablePartition α μ) (ε : ℝ) (hε : ε > 0) :
    ∃ (δ : ℝ) (_ : δ > 0) (m : ℕ),
    ∀ (U W : Graphon α μ),
      (∀ (F : SimpleGraph (Fin m)) [DecidableRel F.Adj],
        |homDensity F (stepify P U) - homDensity F (stepify P W)| < δ) →
      cutDistance (stepify P U) (stepify P W) < ε := by
  classical
  -- By contradiction + compactness of coefficient space
  by_contra h_neg
  push Not at h_neg
  have h_seq : ∀ n : ℕ, ∃ (U_n W_n : Graphon α μ),
      (∀ (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
        |homDensity F (stepify P U_n) - homDensity F (stepify P W_n)| <
          1 / (↑n + 1 : ℝ)) ∧
      cutDistance (stepify P U_n) (stepify P W_n) ≥ ε :=
    fun n => h_neg (1 / (↑n + 1 : ℝ)) (by positivity) n
  choose U_seq W_seq h_close h_far using h_seq
  -- Extract coefficient sequences and use [0,1]^{k^2} compactness.
  -- Define coefficient sequences as functions on P.parts
  set k := P.parts.card with hk_def
  -- Enumerate P.parts
  let ι_equiv : ↥P.parts ≃ Fin k := P.parts.equivFin
  let ι : Fin k → Set α := fun i => (ι_equiv.symm i : Set α)
  have hι : ∀ i, ι i ∈ P.parts := fun i => (ι_equiv.symm i).prop
  have hι_inj : Function.Injective ι :=
    fun i j hij => ι_equiv.symm.injective (Subtype.val_injective hij)
  have hι_surj : ∀ S ∈ P.parts, ∃ i, ι i = S :=
    fun S hS => ⟨ι_equiv ⟨S, hS⟩, by simp [ι]⟩
  -- Coefficient sequences: a_n(i,j) = rectAverage (U_seq n) (ι i) (ι j) ∈ [0,1]
  -- Combined coefficient: c_n(i,j) = (a_n(i,j), b_n(i,j)) for U and W
  -- We need convergent subsequences of both a_n and b_n.
  -- Use compactness of [0,1]^{(k^2)*2} ≅ [0,1]^{k^2} × [0,1]^{k^2}
  -- represented as (Fin k → Fin k → Fin 2 → ℝ)
  set coeff_seq : ℕ → (Fin k → Fin k → Fin 2 → ℝ) :=
    fun n i j b => if b = 0
      then rectAverage (U_seq n) (ι i) (ι j)
      else rectAverage (W_seq n) (ι i) (ι j)
  -- Each coordinate is in [0,1], so the sequence is in a compact set
  have h_in_Icc : ∀ n i j b, coeff_seq n i j b ∈ Set.Icc (0 : ℝ) 1 := by
    intro n i j b; simp only [coeff_seq]
    split
    · exact rectAverage_mem_Icc _ _ _ (P.measurableSet_part (hι i)) (P.measurableSet_part (hι j))
    · exact rectAverage_mem_Icc _ _ _ (P.measurableSet_part (hι i)) (P.measurableSet_part (hι j))
  -- [0,1]^{k^2*2} is compact hence sequentially compact
  have h_compact : IsCompact {f : Fin k → Fin k → Fin 2 → ℝ | ∀ i j b, f i j b ∈ Set.Icc 0 1} :=
    isCompact_pi_infinite (fun _ => isCompact_pi_infinite (fun _ =>
      isCompact_pi_infinite (fun _ => isCompact_Icc)))
  have h_seq_compact := h_compact.isSeqCompact
  -- Extract convergent subsequence
  obtain ⟨c_lim, h_lim_mem, ψ, hψ, h_conv⟩ :=
    h_seq_compact (fun n => h_in_Icc n)
  -- h_conv : coeff_seq ∘ ψ → c_lim in [0,1]^{k²×2} (pi topology = pointwise)
  -- Extract pointwise convergence from pi convergence
  have h_pw : ∀ i j b, Tendsto (fun n => coeff_seq (ψ n) i j b) atTop
      (nhds (c_lim i j b)) := by
    intro i j b
    exact ((tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp
      ((tendsto_pi_nhds.mp h_conv) i)) j)) b)
  -- Define limit coefficient functions on P.parts
  set c_U : Set α → Set α → ℝ := fun S T =>
    if hS : S ∈ P.parts then if hT : T ∈ P.parts then
      c_lim (ι_equiv ⟨S, hS⟩) (ι_equiv ⟨T, hT⟩) 0
    else 0 else 0
  set c_W : Set α → Set α → ℝ := fun S T =>
    if hS : S ∈ P.parts then if hT : T ∈ P.parts then
      c_lim (ι_equiv ⟨S, hS⟩) (ι_equiv ⟨T, hT⟩) 1
    else 0 else 0
  -- Key: c_U (ι i) (ι j) = c_lim i j 0
  have h_cU_ι : ∀ i j, c_U (ι i) (ι j) = c_lim i j 0 := by
    intro i j
    simp only [c_U, hι i, hι j, dif_pos]
    congr 1 <;> exact ι_equiv.apply_symm_apply _
  have h_cW_ι : ∀ i j, c_W (ι i) (ι j) = c_lim i j 1 := by
    intro i j
    simp only [c_W, hι i, hι j, dif_pos]
    congr 1 <;> exact ι_equiv.apply_symm_apply _
  -- Symmetry: rectAverage is symmetric, limits of symmetric sequences are symmetric
  have h_cU_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c_U S T = c_U T S := by
    intro S hS T hT
    simp only [c_U, hS, hT, dif_pos]
    have h_symm_seq : ∀ n, coeff_seq (ψ n) (ι_equiv ⟨S, hS⟩) (ι_equiv ⟨T, hT⟩) 0 =
        coeff_seq (ψ n) (ι_equiv ⟨T, hT⟩) (ι_equiv ⟨S, hS⟩) 0 := by
      intro n; simp only [coeff_seq, ite_true]
      have h1 : ι (ι_equiv ⟨S, hS⟩) = S := by simp [ι]
      have h2 : ι (ι_equiv ⟨T, hT⟩) = T := by simp [ι]
      rw [h1, h2]
      exact rectAverage_symm (U_seq (ψ n)) S T (P.measurableSet_part hS) (P.measurableSet_part hT)
    exact tendsto_nhds_unique
      (h_pw (ι_equiv ⟨S, hS⟩) (ι_equiv ⟨T, hT⟩) 0)
      ((h_pw (ι_equiv ⟨T, hT⟩) (ι_equiv ⟨S, hS⟩) 0).congr (fun n => (h_symm_seq n).symm))
  have h_cW_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c_W S T = c_W T S := by
    intro S hS T hT
    simp only [c_W, hS, hT, dif_pos]
    have h_symm_seq : ∀ n, coeff_seq (ψ n) (ι_equiv ⟨S, hS⟩) (ι_equiv ⟨T, hT⟩) 1 =
        coeff_seq (ψ n) (ι_equiv ⟨T, hT⟩) (ι_equiv ⟨S, hS⟩) 1 := by
      intro n; simp only [coeff_seq]
      have h1 : ι (ι_equiv ⟨S, hS⟩) = S := by simp [ι]
      have h2 : ι (ι_equiv ⟨T, hT⟩) = T := by simp [ι]
      split <;> rw [h1, h2]
      · exact rectAverage_symm (U_seq (ψ n)) S T (P.measurableSet_part hS) (P.measurableSet_part hT)
      · exact rectAverage_symm (W_seq (ψ n)) S T (P.measurableSet_part hS) (P.measurableSet_part hT)
    exact tendsto_nhds_unique
      (h_pw (ι_equiv ⟨S, hS⟩) (ι_equiv ⟨T, hT⟩) 1)
      ((h_pw (ι_equiv ⟨T, hT⟩) (ι_equiv ⟨S, hS⟩) 1).congr (fun n => (h_symm_seq n).symm))
  -- Membership in [0,1]
  have h_cU_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c_U S T ∈ Set.Icc 0 1 := by
    intro S hS T hT
    simp only [c_U, hS, hT, dif_pos]
    exact h_lim_mem _ _ _
  have h_cW_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c_W S T ∈ Set.Icc 0 1 := by
    intro S hS T hT
    simp only [c_W, hS, hT, dif_pos]
    exact h_lim_mem _ _ _
  -- Build limit step graphons
  set V_U := mkStepGraphon P c_U h_cU_symm h_cU_mem
  set V_W := mkStepGraphon P c_W h_cW_symm h_cW_mem
  -- Step 1: Equal hom densities for limits
  -- Bridge: homDensity of mkStepGraphon = weightedHomSum
  have h_bridge_U := homDensity_mkStepGraphon_eq_weightedHomSum
    P c_U h_cU_symm h_cU_mem ι hι hι_surj hι_inj
  have h_bridge_W := homDensity_mkStepGraphon_eq_weightedHomSum
    P c_W h_cW_symm h_cW_mem ι hι hι_surj hι_inj
  -- weightedHomSum is continuous in coefficients (finite sum of products)
  -- Show: for each (n, F), weightedHomSum with U-coefficients → weightedHomSum with U-limit coeffs
  set w : Fin k → ℝ := fun i => (μ (ι i)).toReal
  -- Convergence of weightedHomSum for each graph F
  have h_whs_conv_U : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      Tendsto (fun m => weightedHomSum n F
        (fun i j => coeff_seq (ψ m) i j 0) w) atTop
        (nhds (weightedHomSum n F (fun i j => c_lim i j 0) w)) := by
    intro n F _
    apply tendsto_finsetSum _ (fun σ _ => ?_)
    apply Filter.Tendsto.const_mul
    apply tendsto_finsetProd _ (fun e _ => ?_)
    exact h_pw _ _ 0
  have h_whs_conv_W : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      Tendsto (fun m => weightedHomSum n F
        (fun i j => coeff_seq (ψ m) i j 1) w) atTop
        (nhds (weightedHomSum n F (fun i j => c_lim i j 1) w)) := by
    intro n F _
    apply tendsto_finsetSum _ (fun σ _ => ?_)
    apply Filter.Tendsto.const_mul
    apply tendsto_finsetProd _ (fun e _ => ?_)
    exact h_pw _ _ 1
  -- The original bridges will be instantiated per-graphon below
  -- Equal hom densities: pass |t(F,step U_n) - t(F,step W_n)| < 1/(n+1) to the limit
  -- Helper: homDensity of stepify equals homDensity of mkStepGraphon with rectAverage
  -- (since their toAEEqFun values are equal—both are AEEqFun.mk of the same function)
  have h_stepify_hom : ∀ (V : Graphon α μ)
      (hRA_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts,
        rectAverage V S T = rectAverage V T S)
      (hRA_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts,
        rectAverage V S T ∈ Set.Icc 0 1)
      (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      homDensity F (stepify P V) =
      weightedHomSum n F (fun i j => rectAverage V (ι i) (ι j)) w := by
    intro V hRA_symm hRA_mem n' F' _
    have h_aeq : (stepify P V).toAEEqFun =
        (mkStepGraphon P (rectAverage V) hRA_symm hRA_mem).toAEEqFun :=
      AEEqFun.mk_eq_mk.mpr Filter.EventuallyEq.rfl
    simp only [homDensity, h_aeq]
    exact homDensity_mkStepGraphon_eq_weightedHomSum P (rectAverage V)
      hRA_symm hRA_mem ι hι hι_surj hι_inj n' F'
  have h_hom_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      homDensity F V_U = homDensity F V_W := by
    intro n F _
    rw [h_bridge_U n F, h_bridge_W n F]
    simp only [h_cU_ι, h_cW_ι]
    -- Show: whs(c_lim _ _ 0) = whs(c_lim _ _ 1)
    -- by showing both are limits of the same sequence (up to vanishing difference)
    -- Step A: for m large enough (ψ m ≥ n), |whs_U(m) - whs_W(m)| ≤ 1/(ψ m + 1)
    -- using graph embedding F ↪ Fin (ψ m) + h_close
    have h_bound : ∀ᶠ m in atTop, |weightedHomSum n F (fun i j => coeff_seq (ψ m) i j 0) w -
        weightedHomSum n F (fun i j => coeff_seq (ψ m) i j 1) w| ≤
        1 / (↑(ψ m) + 1 : ℝ) := by
      rw [Filter.eventually_atTop]
      refine ⟨n, fun m hm => ?_⟩
      -- ψ m ≥ m ≥ n, so we can embed Fin n ↪ Fin (ψ m)
      have h_ψm_ge_n : n ≤ ψ m := le_trans hm (hψ.le_apply)
      -- rectAverage symmetry/membership for the sequences
      have hRA_symm_Um : ∀ S ∈ P.parts, ∀ T ∈ P.parts,
          rectAverage (U_seq (ψ m)) S T = rectAverage (U_seq (ψ m)) T S :=
        fun S hS T hT => rectAverage_symm _ S T (P.measurableSet_part hS)
          (P.measurableSet_part hT)
      have hRA_mem_Um : ∀ S ∈ P.parts, ∀ T ∈ P.parts,
          rectAverage (U_seq (ψ m)) S T ∈ Set.Icc 0 1 :=
        fun S hS T hT => rectAverage_mem_Icc _ S T (P.measurableSet_part hS)
          (P.measurableSet_part hT)
      have hRA_symm_Wm : ∀ S ∈ P.parts, ∀ T ∈ P.parts,
          rectAverage (W_seq (ψ m)) S T = rectAverage (W_seq (ψ m)) T S :=
        fun S hS T hT => rectAverage_symm _ S T (P.measurableSet_part hS)
          (P.measurableSet_part hT)
      have hRA_mem_Wm : ∀ S ∈ P.parts, ∀ T ∈ P.parts,
          rectAverage (W_seq (ψ m)) S T ∈ Set.Icc 0 1 :=
        fun S hS T hT => rectAverage_mem_Icc _ S T (P.measurableSet_part hS)
          (P.measurableSet_part hT)
      -- Relate whs to homDensity of stepify
      have h_eq_U : weightedHomSum n F (fun i j => coeff_seq (ψ m) i j 0) w =
          homDensity F (stepify P (U_seq (ψ m))) := by
        rw [h_stepify_hom (U_seq (ψ m)) hRA_symm_Um hRA_mem_Um n F]
        simp [coeff_seq]
      have h_eq_W : weightedHomSum n F (fun i j => coeff_seq (ψ m) i j 1) w =
          homDensity F (stepify P (W_seq (ψ m))) := by
        rw [h_stepify_hom (W_seq (ψ m)) hRA_symm_Wm hRA_mem_Wm n F]
        simp [coeff_seq]
      rw [h_eq_U, h_eq_W]
      -- Embed F : SimpleGraph (Fin n) into SimpleGraph (Fin (ψ m)) via Fin.castLEEmb
      rw [← homDensity_map_embedding F (Fin.castLEEmb h_ψm_ge_n) (stepify P (U_seq (ψ m))),
          ← homDensity_map_embedding F (Fin.castLEEmb h_ψm_ge_n) (stepify P (W_seq (ψ m)))]
      set F' := F.map (Fin.castLEEmb h_ψm_ge_n)
      have := h_close (ψ m) (F := F')
      rw [homDensity_congr_decRel F' _ _ (stepify P (U_seq (ψ m))),
          homDensity_congr_decRel F' _ _ (stepify P (W_seq (ψ m)))] at this
      exact le_of_lt this
    -- Step B: squeeze |diff| → 0 (using eventually bound)
    have h_inv_tends : Tendsto (fun m => 1 / (↑(ψ m) + 1 : ℝ)) atTop (nhds 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      exact (tendsto_natCast_atTop_atTop.comp hψ.tendsto_atTop).atTop_add tendsto_const_nhds
    have h_abs_diff_tends : Tendsto (fun m => |weightedHomSum n F
        (fun i j => coeff_seq (ψ m) i j 0) w -
        weightedHomSum n F (fun i j => coeff_seq (ψ m) i j 1) w|) atTop (nhds 0) := by
      exact squeeze_zero' (Eventually.of_forall (fun m => abs_nonneg _)) h_bound h_inv_tends
    -- Step C: diff → 0 (from |diff| → 0)
    have h_diff_tends : Tendsto (fun m => weightedHomSum n F
        (fun i j => coeff_seq (ψ m) i j 0) w -
        weightedHomSum n F (fun i j => coeff_seq (ψ m) i j 1) w) atTop (nhds 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr
        (by simpa [Real.norm_eq_abs] using h_abs_diff_tends)
    -- Step D: whs_U(m) = diff(m) + whs_W(m) → 0 + L_W = L_W
    apply tendsto_nhds_unique (h_whs_conv_U n F)
    have : Tendsto (fun m =>
        (weightedHomSum n F (fun i j => coeff_seq (ψ m) i j 0) w -
         weightedHomSum n F (fun i j => coeff_seq (ψ m) i j 1) w) +
        weightedHomSum n F (fun i j => coeff_seq (ψ m) i j 1) w) atTop
        (nhds (0 + weightedHomSum n F (fun i j => c_lim i j 1) w)) :=
      h_diff_tends.add (h_whs_conv_W n F)
    simp only [sub_add_cancel, zero_add] at this
    exact this
  -- Step 2: cutDistance(V_U, V_W) = 0
  have h_cd_lim : cutDistance V_U V_W = 0 :=
    cutDistance_zero_of_step_homDensity_eq P c_U c_W h_cU_symm h_cU_mem h_cW_symm h_cW_mem
      h_hom_eq
  -- Step 3: For large m, cutDistance(stepify P (U_{ψ m}), V_U) and
  -- cutDistance(stepify P (W_{ψ m}), V_W) are both ≤ ε/3.
  -- Strategy: triangle through mkStepGraphon P (rectAverage V) (a.e. equal to stepify).
  have hε3 : ε / 3 > 0 := by linarith
  -- For each (i,j), eventually |coeff(ψ m, i, j, b) - c_lim(i, j, b)| < ε/3
  have h_event_U : ∀ i j, ∃ N, ∀ m ≥ N,
      |coeff_seq (ψ m) i j 0 - c_lim i j 0| < ε / 3 := by
    intro i j
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (h_pw i j 0) (ε / 3) hε3
    exact ⟨N, fun m hm => by have := hN m hm; rw [Real.dist_eq] at this; exact this⟩
  have h_event_W : ∀ i j, ∃ N, ∀ m ≥ N,
      |coeff_seq (ψ m) i j 1 - c_lim i j 1| < ε / 3 := by
    intro i j
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (h_pw i j 1) (ε / 3) hε3
    exact ⟨N, fun m hm => by have := hN m hm; rw [Real.dist_eq] at this; exact this⟩
  -- Pointwise convergence in the pi topology → uniform eventual bound
  -- Use Filter.Eventually to avoid Finset.sup timeout
  have h_event_all_U : ∀ᶠ m in atTop, ∀ i j,
      |coeff_seq (ψ m) i j 0 - c_lim i j 0| < ε / 3 := by
    rw [Filter.eventually_atTop]
    choose N_ij hN_ij using h_event_U
    exact ⟨(Finset.univ : Finset (Fin k × Fin k)).sup (fun p => N_ij p.1 p.2),
      fun m hm i j => hN_ij i j m (le_trans
        (Finset.le_sup (f := fun p => N_ij p.1 p.2) (Finset.mem_univ (i, j))) hm)⟩
  have h_event_all_W : ∀ᶠ m in atTop, ∀ i j,
      |coeff_seq (ψ m) i j 1 - c_lim i j 1| < ε / 3 := by
    rw [Filter.eventually_atTop]
    choose N_ij hN_ij using h_event_W
    exact ⟨(Finset.univ : Finset (Fin k × Fin k)).sup (fun p => N_ij p.1 p.2),
      fun m hm i j => hN_ij i j m (le_trans
        (Finset.le_sup (f := fun p => N_ij p.1 p.2) (Finset.mem_univ (i, j))) hm)⟩
  -- Pick a specific m where both hold
  obtain ⟨m, hm_U, hm_W⟩ := (h_event_all_U.and h_event_all_W).exists
  have hN_U_spec : ∀ i j, |coeff_seq (ψ m) i j 0 - c_lim i j 0| < ε / 3 := hm_U
  have hN_W_spec : ∀ i j, |coeff_seq (ψ m) i j 1 - c_lim i j 1| < ε / 3 := hm_W
  -- Build mkStepGraphon intermediaries for the a.e.-equal stepifications
  have hRA_symm_Um : ∀ S ∈ P.parts, ∀ T ∈ P.parts,
      rectAverage (U_seq (ψ m)) S T = rectAverage (U_seq (ψ m)) T S :=
    fun S hS T hT => rectAverage_symm _ S T (P.measurableSet_part hS)
      (P.measurableSet_part hT)
  have hRA_mem_Um : ∀ S ∈ P.parts, ∀ T ∈ P.parts,
      rectAverage (U_seq (ψ m)) S T ∈ Set.Icc 0 1 :=
    fun S hS T hT => rectAverage_mem_Icc _ S T (P.measurableSet_part hS)
      (P.measurableSet_part hT)
  have hRA_symm_Wm : ∀ S ∈ P.parts, ∀ T ∈ P.parts,
      rectAverage (W_seq (ψ m)) S T = rectAverage (W_seq (ψ m)) T S :=
    fun S hS T hT => rectAverage_symm _ S T (P.measurableSet_part hS)
      (P.measurableSet_part hT)
  have hRA_mem_Wm : ∀ S ∈ P.parts, ∀ T ∈ P.parts,
      rectAverage (W_seq (ψ m)) S T ∈ Set.Icc 0 1 :=
    fun S hS T hT => rectAverage_mem_Icc _ S T (P.measurableSet_part hS)
      (P.measurableSet_part hT)
  set V_Um := mkStepGraphon P (rectAverage (U_seq (ψ m))) hRA_symm_Um hRA_mem_Um
  set V_Wm := mkStepGraphon P (rectAverage (W_seq (ψ m))) hRA_symm_Wm hRA_mem_Wm
  -- stepify and mkStepGraphon with rectAverage are a.e. equal → cutNormDiff = 0
  have h_cn_zero_U : cutNormDiff (stepify P (U_seq (ψ m))) V_Um = 0 := by
    apply le_antisymm _ (cutNormDiff_nonneg _ _)
    unfold cutNormDiff rectIntegralDiff
    apply Real.iSup_le _ le_rfl
    intro S; apply Real.iSup_le _ le_rfl
    intro hS; apply Real.iSup_le _ le_rfl
    intro T; apply Real.iSup_le _ le_rfl
    intro hT
    suffices h : ∫ p in S ×ˢ T,
        ((stepify P (U_seq (ψ m))).toAEEqFun p - V_Um.toAEEqFun p) ∂(μ.prod μ) = 0 by
      rw [h, abs_zero]
    apply integral_eq_zero_of_ae
    apply ae_restrict_of_ae
    have h_aeq : (stepify P (U_seq (ψ m))).toAEEqFun = V_Um.toAEEqFun :=
      AEEqFun.mk_eq_mk.mpr Filter.EventuallyEq.rfl
    filter_upwards with p
    simp [h_aeq]
  have h_cn_zero_W : cutNormDiff (stepify P (W_seq (ψ m))) V_Wm = 0 := by
    apply le_antisymm _ (cutNormDiff_nonneg _ _)
    unfold cutNormDiff rectIntegralDiff
    apply Real.iSup_le _ le_rfl
    intro S; apply Real.iSup_le _ le_rfl
    intro hS; apply Real.iSup_le _ le_rfl
    intro T; apply Real.iSup_le _ le_rfl
    intro hT
    suffices h : ∫ p in S ×ˢ T,
        ((stepify P (W_seq (ψ m))).toAEEqFun p - V_Wm.toAEEqFun p) ∂(μ.prod μ) = 0 by
      rw [h, abs_zero]
    apply integral_eq_zero_of_ae
    apply ae_restrict_of_ae
    have h_aeq : (stepify P (W_seq (ψ m))).toAEEqFun = V_Wm.toAEEqFun :=
      AEEqFun.mk_eq_mk.mpr Filter.EventuallyEq.rfl
    filter_upwards with p
    simp [h_aeq]
  -- cutNormDiff between mkStepGraphons with different coefficients
  have h_cn_U : cutNormDiff V_Um V_U ≤ ε / 3 := by
    apply cutNormDiff_mkStepGraphon_le P (rectAverage (U_seq (ψ m))) c_U
      hRA_symm_Um hRA_mem_Um h_cU_symm h_cU_mem (ε / 3)
    intro S hS T hT
    obtain ⟨i, hi⟩ := hι_surj S hS
    obtain ⟨j, hj⟩ := hι_surj T hT
    rw [← hi, ← hj, h_cU_ι]
    have : coeff_seq (ψ m) i j 0 = rectAverage (U_seq (ψ m)) (ι i) (ι j) := by
      simp [coeff_seq]
    rw [← this]
    exact le_of_lt (hN_U_spec i j)
  have h_cn_W : cutNormDiff V_Wm V_W ≤ ε / 3 := by
    apply cutNormDiff_mkStepGraphon_le P (rectAverage (W_seq (ψ m))) c_W
      hRA_symm_Wm hRA_mem_Wm h_cW_symm h_cW_mem (ε / 3)
    intro S hS T hT
    obtain ⟨i, hi⟩ := hι_surj S hS
    obtain ⟨j, hj⟩ := hι_surj T hT
    rw [← hi, ← hj, h_cW_ι]
    have : coeff_seq (ψ m) i j 1 = rectAverage (W_seq (ψ m)) (ι i) (ι j) := by
      simp [coeff_seq]
    rw [← this]
    exact le_of_lt (hN_W_spec i j)
  -- cutDistance(stepify, V_U) ≤ cutNormDiff(stepify, V_Um) + cutNormDiff(V_Um, V_U)
  --                           = 0 + ε/3 = ε/3
  have h_cd_U : cutDistance (stepify P (U_seq (ψ m))) V_U ≤ ε / 3 :=
    calc cutDistance (stepify P (U_seq (ψ m))) V_U
        ≤ cutNormDiff (stepify P (U_seq (ψ m))) V_U :=
          cutDistance_le_cutNormDiff _ _
      _ ≤ cutNormDiff (stepify P (U_seq (ψ m))) V_Um +
          cutNormDiff V_Um V_U := cutNormDiff_triangle _ _ _
      _ = 0 + cutNormDiff V_Um V_U := by rw [h_cn_zero_U]
      _ = cutNormDiff V_Um V_U := zero_add _
      _ ≤ ε / 3 := h_cn_U
  have h_cd_W : cutDistance (stepify P (W_seq (ψ m))) V_W ≤ ε / 3 :=
    calc cutDistance (stepify P (W_seq (ψ m))) V_W
        ≤ cutNormDiff (stepify P (W_seq (ψ m))) V_W :=
          cutDistance_le_cutNormDiff _ _
      _ ≤ cutNormDiff (stepify P (W_seq (ψ m))) V_Wm +
          cutNormDiff V_Wm V_W := cutNormDiff_triangle _ _ _
      _ = 0 + cutNormDiff V_Wm V_W := by rw [h_cn_zero_W]
      _ = cutNormDiff V_Wm V_W := zero_add _
      _ ≤ ε / 3 := h_cn_W
  -- Step 4: Contradiction via triangle inequality
  -- cutDistance(step U, step W) ≤ d(step U, V_U) + d(V_U, V_W) + d(V_W, step W)
  --                             ≤ ε/3 + 0 + ε/3 = 2ε/3 < ε
  have h_tri : cutDistance (stepify P (U_seq (ψ m))) (stepify P (W_seq (ψ m))) ≤
      cutDistance (stepify P (U_seq (ψ m))) V_U +
      cutDistance V_U V_W +
      cutDistance V_W (stepify P (W_seq (ψ m))) := by
    calc cutDistance (stepify P (U_seq (ψ m))) (stepify P (W_seq (ψ m)))
        ≤ cutDistance (stepify P (U_seq (ψ m))) V_U +
          cutDistance V_U (stepify P (W_seq (ψ m))) := cutDistance_triangle _ _ _
      _ ≤ cutDistance (stepify P (U_seq (ψ m))) V_U +
          (cutDistance V_U V_W + cutDistance V_W (stepify P (W_seq (ψ m)))) := by
          linarith [cutDistance_triangle V_U V_W (stepify P (W_seq (ψ m)))]
      _ = _ := by ring
  rw [h_cd_lim, cutDistance_symm V_W (stepify P (W_seq (ψ m)))] at h_tri
  linarith [h_far (ψ m)]

/-- Build a `MeasurablePartition` with `K` cells having prescribed measures. -/
private theorem exists_partition_with_measures {K : ℕ}
    (w : Fin K → ℝ) (hw_nn : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1) :
    ∃ (P : MeasurablePartition α μ) (ι : Fin K → Set α),
      (∀ i, ι i ∈ P.parts) ∧
      Function.Injective ι ∧
      (∀ S ∈ P.parts, ∃ i, ι i = S) ∧
      P.parts.card = K ∧
      ∀ i, (μ (ι i)).toReal = w i := by
  -- K = 0 impossible
  rcases Nat.eq_zero_or_pos K with rfl | hK_pos
  · simp at hw_sum
  -- Derive Infinite α
  haveI : Infinite α := by
    by_contra h; rw [not_infinite_iff_finite] at h; haveI := h
    exact absurd (Set.Finite.measure_zero Set.finite_univ μ) (by simp [measure_univ])
  -- K distinct points
  set ξ : Fin K → α := (Infinite.natEmbedding α) ∘ Fin.val
  have hξ_inj : Function.Injective ξ := (Infinite.natEmbedding α).injective.comp Fin.val_injective
  -- Reserve set R (finite, null, measurable)
  have hR_finite : (Set.range ξ).Finite := Set.finite_range ξ
  have hR_meas : MeasurableSet (Set.range ξ) := hR_finite.measurableSet
  have hR_null : μ (Set.range ξ) = 0 := hR_finite.measure_zero μ
  -- Working set S₀ = univ \ R
  set S₀ := Set.univ \ Set.range ξ with hS₀_def
  have hS₀_meas : MeasurableSet S₀ := MeasurableSet.univ.diff hR_meas
  have hS₀_eq : μ S₀ = 1 := by
    have : μ Set.univ = μ S₀ + μ (Set.range ξ) := by
      rw [← measure_union (Set.disjoint_sdiff_left) hR_meas, Set.sdiff_union_self,
          Set.union_eq_self_of_subset_right (Set.subset_univ _)]
    rw [measure_univ, hR_null, add_zero] at this; exact this.symm
  -- Recursive carving of S₀: build C_i ⊆ S₀ with μ(C_i) = ofReal(w i)
  -- Process indices 0..K-2 by IVT, last index absorbs remainder
  suffices h_carve : ∃ C : Fin K → Set α,
      (∀ i, MeasurableSet (C i)) ∧ (∀ i, C i ⊆ S₀) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      μ (S₀ \ ⋃ i, C i) = 0 ∧ (∀ i, μ (C i) = ENNReal.ofReal (w i)) by
    obtain ⟨C, hCm, hCs, hCd, hCcov, hCe⟩ := h_carve
    -- Decorate: ι i = C i ∪ {ξ i}
    set ι : Fin K → Set α := fun i => C i ∪ {ξ i}
    -- ι i are pairwise disjoint
    have hι_disj : ∀ i j, i ≠ j → Disjoint (ι i) (ι j) := by
      intro i j hij
      apply Disjoint.union_left
      · apply Disjoint.union_right
        · exact hCd i j hij
        · rw [Set.disjoint_left]; intro x hx hξ
          rw [Set.mem_singleton_iff] at hξ; subst hξ
          exact (hCs i hx).2 ⟨j, rfl⟩
      · apply Disjoint.union_right
        · rw [Set.disjoint_left]; intro x hx hC
          rw [Set.mem_singleton_iff] at hx; subst hx
          exact (hCs j hC).2 ⟨i, rfl⟩
        · rw [Set.disjoint_left]; intro x hx hy
          rw [Set.mem_singleton_iff] at hx hy
          exact hij (hξ_inj (hx ▸ hy))
    -- ι is injective
    have hι_inj : Function.Injective ι := by
      intro i j hij
      by_contra hne
      exact Set.disjoint_left.mp (hι_disj i j hne) (Set.mem_union_right _ (Set.mem_singleton _))
        (hij ▸ Set.mem_union_right _ (Set.mem_singleton _))
    -- ι i are measurable
    have hι_meas : ∀ i, MeasurableSet (ι i) :=
      fun i => (hCm i).union (measurableSet_singleton _)
    -- μ(ι i) = ofReal(w i) (singleton has measure 0)
    have hι_measure : ∀ i, μ (ι i) = ENNReal.ofReal (w i) := by
      intro i; show μ (C i ∪ {ξ i}) = _
      have h_disj : Disjoint (C i) {ξ i} := by
        rw [Set.disjoint_left]; intro x hx hξ
        rw [Set.mem_singleton_iff] at hξ; subst hξ
        exact (hCs i hx).2 ⟨i, rfl⟩
      rw [measure_union h_disj (measurableSet_singleton _),
          MeasureTheory.NoAtoms.measure_singleton, add_zero, hCe i]
    -- Build MeasurablePartition
    haveI : DecidableEq (Set α) := Classical.decEq _
    set parts := Finset.image ι Finset.univ
    have h_card : parts.card = K := by
      rw [Finset.card_image_of_injective _ hι_inj, Finset.card_univ, Fintype.card_fin]
    refine ⟨⟨parts, fun S hS => ?_, ?_, ?_⟩, ι, ?_, hι_inj, ?_, h_card, ?_⟩
    -- measurable_parts
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (show S ∈ Finset.image ι Finset.univ from hS)
      exact hι_meas i
    -- pairwiseDisjoint
    · intro S hS T hT hne
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (show S ∈ Finset.image ι Finset.univ from hS)
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (show T ∈ Finset.image ι Finset.univ from hT)
      exact hι_disj i j (fun h => hne (congrArg ι h))
    -- ae_covers: complement ⊆ S₀ \ ⋃ C i, which is null
    · rw [ae_iff]
      refine le_antisymm ?_ (zero_le)
      calc μ {x | ¬∃ S ∈ parts, x ∈ S}
          ≤ μ (S₀ \ ⋃ i, C i) := measure_mono (fun x hx => by
            push Not at hx -- hx : ∀ S ∈ parts, x ∉ S
            refine ⟨⟨Set.mem_univ _, fun hxR => ?_⟩, fun hxC => ?_⟩
            · obtain ⟨j, rfl⟩ := hxR
              exact hx (ι j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
                (Set.mem_union_right _ rfl)
            · rw [Set.mem_iUnion] at hxC; obtain ⟨i, hi⟩ := hxC
              exact hx (ι i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
                (Set.mem_union_left _ hi))
        _ = 0 := hCcov
    -- ι i ∈ parts
    · exact fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    -- surjectivity
    · intro S hS; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS; exact ⟨i, rfl⟩
    -- measures
    · intro i; rw [hι_measure i, ENNReal.toReal_ofReal (hw_nn i)]
  -- Now prove h_carve: build C by recursion on K
  -- Helper: carve n cells from measurable set S with prescribed measures
  suffices h_gen : ∀ (n : ℕ) (S : Set α) (hS : MeasurableSet S) (hS_ne_top : μ S ≠ ⊤)
      (w' : Fin n → ℝ) (hw'_nn : ∀ i, 0 ≤ w' i)
      (hw'_sum : ENNReal.ofReal (∑ i, w' i) = μ S),
      ∃ C : Fin n → Set α,
        (∀ i, MeasurableSet (C i)) ∧ (∀ i, C i ⊆ S) ∧
        (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
        μ (S \ ⋃ i, C i) = 0 ∧ (∀ i, μ (C i) = ENNReal.ofReal (w' i)) by
    have hS₀_ne_top : μ S₀ ≠ ⊤ := by rw [hS₀_eq]; exact ENNReal.one_ne_top
    have hw_ofReal : ENNReal.ofReal (∑ i, w i) = μ S₀ := by
      rw [hS₀_eq, hw_sum, ENNReal.ofReal_one]
    exact h_gen K S₀ hS₀_meas hS₀_ne_top w hw_nn hw_ofReal
  intro n; induction n with
  | zero =>
    intro S hS hS_ne_top w' _ hw'_sum
    refine ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, ?_, fun i => i.elim0⟩
    simp only [Set.iUnion_of_empty, Set.sdiff_empty]; simpa using hw'_sum.symm
  | succ n ih =>
    intro S hS hS_ne_top w' hw'_nn hw'_sum
    -- Carve first cell C₀ ⊆ S with μ(C₀) = ENNReal.ofReal(w' 0)
    have h_w0_le : ENNReal.ofReal (w' 0) ≤ μ S := by
      rw [← hw'_sum]; apply ENNReal.ofReal_le_ofReal
      exact Finset.single_le_sum (fun i _ => hw'_nn i) (Finset.mem_univ 0)
    obtain ⟨C₀, hC₀m, hC₀s, hC₀e⟩ := exists_measurable_subset_of_measure hS h_w0_le
    -- Remaining space S' = S \ C₀
    set S' := S \ C₀ with hS'_def
    have hS'm : MeasurableSet S' := hS.diff hC₀m
    have hS'_ne_top : μ S' ≠ ⊤ := ne_top_of_le_ne_top hS_ne_top (measure_mono sdiff_subset)
    have hw'_rest_sum : ENNReal.ofReal (∑ i : Fin n, w' i.succ) = μ S' := by
      rw [measure_sdiff hC₀s hC₀m.nullMeasurableSet (by rw [hC₀e]; exact ENNReal.ofReal_ne_top),
          hC₀e, ← hw'_sum, Fin.sum_univ_succ,
          ENNReal.ofReal_add (hw'_nn 0) (Finset.sum_nonneg (fun i _ => hw'_nn _))]
      exact (ENNReal.add_sub_cancel_left ENNReal.ofReal_ne_top).symm
    obtain ⟨C', hC'm, hC's, hC'd, hC'cov, hC'e⟩ :=
      ih S' hS'm hS'_ne_top (fun i => w' i.succ) (fun i => hw'_nn _) hw'_rest_sum
    refine ⟨Fin.cons C₀ C', ?_, ?_, ?_, ?_, ?_⟩
    -- Measurable
    · intro i; refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_zero]; exact hC₀m
      · rw [Fin.cons_succ]; exact hC'm j
    -- Subset
    · intro i; refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_zero]; exact hC₀s
      · rw [Fin.cons_succ]; exact (hC's j).trans sdiff_subset
    -- Disjoint: introduce hij AFTER case split so types are correct
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
        intro hij <;> simp only [Fin.cons_zero, Fin.cons_succ]
      · exact absurd rfl hij
      · exact Set.disjoint_of_subset_right (hC's _) disjoint_sdiff_right
      · exact (Set.disjoint_of_subset_right (hC's _) disjoint_sdiff_right).symm
      · exact hC'd _ _ (fun h => hij (congrArg Fin.succ h))
    -- Coverage: S \ ⋃ i, Fin.cons C₀ C' i = 0
    · -- S \ ⋃ i, T i = S' \ ⋃ i, C' i where T i = Fin.cons C₀ C'
      -- Key: ⋃ i, T i = C₀ ∪ ⋃ j, C' j, so S \ (C₀ ∪ ⋃ C') = (S \ C₀) \ ⋃ C' = S' \ ⋃ C'
      suffices h : ∀ x, x ∈ S \ ⋃ i, @Fin.cons _ (fun _ => Set α) C₀ C' i →
          x ∈ S' \ ⋃ j, C' j by
        exact le_antisymm (le_trans (measure_mono h) (le_of_eq hC'cov)) (zero_le)
      intro x ⟨hxS, hxU⟩
      simp only [Set.mem_iUnion, not_exists] at hxU
      refine ⟨⟨hxS, fun hxC₀ => hxU 0 (by rw [Fin.cons_zero]; exact hxC₀)⟩, ?_⟩
      simp only [Set.mem_iUnion, not_exists]
      intro j hj; exact hxU j.succ (by rw [Fin.cons_succ]; exact hj)
    -- Measures match
    · intro i; refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_zero]; exact hC₀e
      · rw [Fin.cons_succ]; exact hC'e j

/-- If two graphons agree a.e. off a "strip" `E × univ ∪ univ × E`, then their
cut norm difference is at most `2 * (μ E).toReal`. -/
private theorem cutNormDiff_le_of_ae_agree_off_strip (U W : Graphon α μ)
    (E : Set α) (hE : MeasurableSet E)
    (h_agree : ∀ᵐ p ∂(μ.prod μ), p.1 ∉ E → p.2 ∉ E →
        U.toAEEqFun p = W.toAEEqFun p) :
    cutNormDiff U W ≤ 2 * (μ E).toReal := by
  -- Peel the 4-level iSup
  unfold cutNormDiff
  have h_bound_nn : 0 ≤ 2 * (μ E).toReal := by positivity
  apply Real.iSup_le _ h_bound_nn; intro S
  apply Real.iSup_le _ h_bound_nn; intro hS
  apply Real.iSup_le _ h_bound_nn; intro T
  apply Real.iSup_le _ h_bound_nn; intro hT
  -- Goal: |rectIntegralDiff U W S T| ≤ 2 * (μ E).toReal
  simp only [rectIntegralDiff]
  -- Abbreviations for the integrand
  set f := fun p : α × α => U.toAEEqFun p - W.toAEEqFun p with hf_def
  -- Integrability of f
  have hf_int : Integrable f (μ.prod μ) :=
    (SymmKernel.graphon_integrable U).sub (SymmKernel.graphon_integrable W)
  -- |f| ≤ 1 a.e.
  have hf_le_one : ∀ᵐ p ∂(μ.prod μ), |f p| ≤ 1 := by
    filter_upwards [U.ae_mem_Icc, W.ae_mem_Icc] with p hU hW
    rw [abs_le]; exact ⟨by linarith [hU.1, hW.2], by linarith [hU.2, hW.1]⟩
  -- Measurability facts
  have hSE := hS.inter hE
  have hSdE := hS.diff hE
  have hTE := hT.inter hE
  have hTdE := hT.diff hE
  -- Key decomposition: S ×ˢ T = (S ∩ E) ×ˢ T ∪ (S \ E) ×ˢ T
  have h_ST_decomp : S ×ˢ T = ((S ∩ E) ×ˢ T) ∪ ((S \ E) ×ˢ T) := by
    rw [← Set.union_prod, Set.inter_union_sdiff]
  -- Further decompose (S \ E) ×ˢ T = (S \ E) ×ˢ (T ∩ E) ∪ (S \ E) ×ˢ (T \ E)
  have h_SdET_decomp : (S \ E) ×ˢ T = ((S \ E) ×ˢ (T ∩ E)) ∪ ((S \ E) ×ˢ (T \ E)) := by
    rw [← Set.prod_union, Set.inter_union_sdiff]
  -- Disjointness
  have h_disj1 : Disjoint ((S ∩ E) ×ˢ T) ((S \ E) ×ˢ T) :=
    disjoint_inf_sdiff.set_prod_left T T
  have h_disj2 : Disjoint ((S \ E) ×ˢ (T ∩ E)) ((S \ E) ×ˢ (T \ E)) :=
    disjoint_inf_sdiff.set_prod_right (S \ E) (S \ E)
  -- Split the integral over S ×ˢ T into two pieces
  have h_int1 : IntegrableOn f ((S ∩ E) ×ˢ T) (μ.prod μ) := hf_int.integrableOn
  have h_int2 : IntegrableOn f ((S \ E) ×ˢ T) (μ.prod μ) := hf_int.integrableOn
  have h_int3 : IntegrableOn f ((S \ E) ×ˢ (T ∩ E)) (μ.prod μ) := hf_int.integrableOn
  have h_int4 : IntegrableOn f ((S \ E) ×ˢ (T \ E)) (μ.prod μ) := hf_int.integrableOn
  -- On (S \ E) ×ˢ (T \ E), f = 0 a.e. by h_agree
  have h_zero : ∫ p in (S \ E) ×ˢ (T \ E), f p ∂(μ.prod μ) = 0 := by
    apply setIntegral_eq_zero_of_ae_eq_zero
    filter_upwards [h_agree] with p hp hpmem
    have hp1 : p.1 ∉ E := hpmem.1.2
    have hp2 : p.2 ∉ E := hpmem.2.2
    simp [hf_def, hp hp1 hp2]
  -- Bound piece 1: |(S ∩ E) ×ˢ T| ≤ μ(E).toReal
  have hE_ne_top : μ E ≠ ⊤ := measure_ne_top μ E
  have h_piece1 : |∫ p in (S ∩ E) ×ˢ T, f p ∂(μ.prod μ)| ≤ (μ E).toReal := by
    calc |∫ p in (S ∩ E) ×ˢ T, f p ∂(μ.prod μ)|
        ≤ ∫ p in (S ∩ E) ×ˢ T, |f p| ∂(μ.prod μ) := abs_integral_le_integral_abs
      _ ≤ ∫ _ in (S ∩ E) ×ˢ T, (1 : ℝ) ∂(μ.prod μ) := by
          apply setIntegral_mono_ae_restrict
          · exact hf_int.abs.integrableOn
          · exact integrable_const 1
          · exact ae_restrict_of_ae hf_le_one
      _ = ((μ.prod μ) ((S ∩ E) ×ˢ T)).toReal := by
          rw [setIntegral_const, smul_eq_mul, mul_one]; rfl
      _ = (μ (S ∩ E) * μ T).toReal := by rw [Measure.prod_prod]
      _ ≤ (μ E * 1).toReal := by
          apply ENNReal.toReal_mono (by rw [mul_one]; exact hE_ne_top)
          exact mul_le_mul' (measure_mono Set.inter_subset_right)
            (by rw [← measure_univ (μ := μ)]; exact measure_mono (subset_univ _))
      _ = (μ E).toReal := by rw [mul_one]
  -- Bound piece 2: |(S \ E) ×ˢ (T ∩ E)| ≤ μ(E).toReal
  have h_piece2 : |∫ p in (S \ E) ×ˢ (T ∩ E), f p ∂(μ.prod μ)| ≤ (μ E).toReal := by
    calc |∫ p in (S \ E) ×ˢ (T ∩ E), f p ∂(μ.prod μ)|
        ≤ ∫ p in (S \ E) ×ˢ (T ∩ E), |f p| ∂(μ.prod μ) := abs_integral_le_integral_abs
      _ ≤ ∫ _ in (S \ E) ×ˢ (T ∩ E), (1 : ℝ) ∂(μ.prod μ) := by
          apply setIntegral_mono_ae_restrict
          · exact hf_int.abs.integrableOn
          · exact integrable_const 1
          · exact ae_restrict_of_ae hf_le_one
      _ = ((μ.prod μ) ((S \ E) ×ˢ (T ∩ E))).toReal := by
          rw [setIntegral_const, smul_eq_mul, mul_one]; rfl
      _ = (μ (S \ E) * μ (T ∩ E)).toReal := by rw [Measure.prod_prod]
      _ ≤ (1 * μ E).toReal := by
          apply ENNReal.toReal_mono (by rw [one_mul]; exact hE_ne_top)
          exact mul_le_mul'
            (by rw [← measure_univ (μ := μ)]; exact measure_mono (subset_univ _))
            (measure_mono Set.inter_subset_right)
      _ = (μ E).toReal := by rw [one_mul]
  -- Split the second integral (S \ E) ×ˢ T into two sub-parts
  have h_split2 : ∫ p in (S \ E) ×ˢ T, f p ∂(μ.prod μ) =
      (∫ p in (S \ E) ×ˢ (T ∩ E), f p ∂(μ.prod μ)) +
      (∫ p in (S \ E) ×ˢ (T \ E), f p ∂(μ.prod μ)) := by
    rw [h_SdET_decomp, setIntegral_union h_disj2 (hSdE.prod hTdE) h_int3 h_int4]
  -- Now assemble: split integral and use triangle inequality
  have h_main_split : ∫ p in S ×ˢ T, f p ∂(μ.prod μ) =
      (∫ p in (S ∩ E) ×ˢ T, f p ∂(μ.prod μ)) +
      (∫ p in (S \ E) ×ˢ T, f p ∂(μ.prod μ)) := by
    rw [h_ST_decomp]; exact setIntegral_union h_disj1 (hSdE.prod hT) h_int1 h_int2
  calc |∫ p in S ×ˢ T, f p ∂(μ.prod μ)|
      = |(∫ p in (S ∩ E) ×ˢ T, f p ∂(μ.prod μ)) +
         ((∫ p in (S \ E) ×ˢ (T ∩ E), f p ∂(μ.prod μ)) +
          (∫ p in (S \ E) ×ˢ (T \ E), f p ∂(μ.prod μ)))| := by
        rw [h_main_split, h_split2]
    _ = |(∫ p in (S ∩ E) ×ˢ T, f p ∂(μ.prod μ)) +
         (∫ p in (S \ E) ×ˢ (T ∩ E), f p ∂(μ.prod μ))| := by
        rw [h_zero, add_zero]
    _ ≤ |∫ p in (S ∩ E) ×ˢ T, f p ∂(μ.prod μ)| +
        |∫ p in (S \ E) ×ˢ (T ∩ E), f p ∂(μ.prod μ)| := abs_add_le _ _
    _ ≤ (μ E).toReal + (μ E).toReal := add_le_add h_piece1 h_piece2
    _ = 2 * (μ E).toReal := by ring

/-- Weight stability for step graphons on different partitions with same coefficients.
Uses `MeasurePreserving.exists_controlled_cell_alignment` (Rokhlin) for partition alignment. -/
private theorem cutDistance_step_weight_le {K : ℕ}
    (P Q : MeasurablePartition α μ)
    (c_P c_Q : Set α → Set α → ℝ)
    (hc_P_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c_P S T = c_P T S)
    (hc_P_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c_P S T ∈ Set.Icc 0 1)
    (hc_Q_symm : ∀ S ∈ Q.parts, ∀ T ∈ Q.parts, c_Q S T = c_Q T S)
    (hc_Q_mem : ∀ S ∈ Q.parts, ∀ T ∈ Q.parts, c_Q S T ∈ Set.Icc 0 1)
    (ι_P : Fin K → Set α) (ι_Q : Fin K → Set α)
    (hι_P : ∀ i, ι_P i ∈ P.parts) (hι_Q : ∀ i, ι_Q i ∈ Q.parts)
    (hι_P_inj : Function.Injective ι_P) (hι_Q_inj : Function.Injective ι_Q)
    (hι_P_surj : ∀ S ∈ P.parts, ∃ i, ι_P i = S)
    (hι_Q_surj : ∀ S ∈ Q.parts, ∃ i, ι_Q i = S)
    (h_coeff_eq : ∀ i j : Fin K, c_P (ι_P i) (ι_P j) = c_Q (ι_Q i) (ι_Q j)) :
    cutDistance (mkStepGraphon P c_P hc_P_symm hc_P_mem)
               (mkStepGraphon Q c_Q hc_Q_symm hc_Q_mem) ≤
      2 * ∑ i : Fin K, |(μ (ι_P i)).toReal - (μ (ι_Q i)).toReal| := by
  -- Step 0: Abbreviate the two step graphons
  set W_P := mkStepGraphon P c_P hc_P_symm hc_P_mem with hW_P_def
  set W_Q := mkStepGraphon Q c_Q hc_Q_symm hc_Q_mem with hW_Q_def
  -- Step 1: Build matched subsets M_P i ⊆ ι_P i and M_Q i ⊆ ι_Q i
  -- with μ(M_P i) = μ(M_Q i) = min(μ(ι_P i), μ(ι_Q i))
  have h_matched : ∀ i : Fin K, ∃ (MP_i MQ_i : Set α),
      MeasurableSet MP_i ∧ MeasurableSet MQ_i ∧
      MP_i ⊆ ι_P i ∧ MQ_i ⊆ ι_Q i ∧
      μ MP_i = min (μ (ι_P i)) (μ (ι_Q i)) ∧
      μ MQ_i = min (μ (ι_P i)) (μ (ι_Q i)) := by
    intro i
    have hP_meas := P.measurableSet_part (hι_P i)
    have hQ_meas := Q.measurableSet_part (hι_Q i)
    obtain ⟨MP_i, hMP_m, hMP_s, hMP_e⟩ :=
      exists_measurable_subset_of_measure (μ := μ) hP_meas (min_le_left _ _)
    obtain ⟨MQ_i, hMQ_m, hMQ_s, hMQ_e⟩ :=
      exists_measurable_subset_of_measure (μ := μ) hQ_meas (min_le_right _ _)
    exact ⟨MP_i, MQ_i, hMP_m, hMQ_m, hMP_s, hMQ_s, hMP_e, hMQ_e⟩
  choose M_P M_Q hM_P_meas hM_Q_meas hM_P_sub hM_Q_sub hM_P_eq hM_Q_eq using h_matched
  -- Step 2: Sorry the alignment — traces to Rokhlin/exists_common_extension
  -- We need e : α ≃ᵐ α, MP, mapping M_Q i into M_P i a.e.
  have h_align : ∃ (e : α ≃ᵐ α) (he : MeasurePreserving e μ μ),
      ∀ i : Fin K, ∀ᵐ x ∂μ, x ∈ M_Q i → e x ∈ M_P i := by
    classical
    -- Filter to "good" indices where M_Q has positive measure
    let good : Finset (Fin K) := Finset.univ.filter (fun i => μ (M_Q i) ≠ 0)
    -- Good indices have positive M_Q and M_P measure
    have h_good_pos : ∀ i ∈ good, μ (M_Q i) ≠ 0 := by
      intro i hi; exact (Finset.mem_filter.mp hi).2
    have h_good_pos_P : ∀ i ∈ good, μ (M_P i) ≠ 0 := by
      intro i hi
      have := (Finset.mem_filter.mp hi).2
      rw [hM_Q_eq] at this; rw [hM_P_eq]; exact this
    -- Re-index good indices as Fin good.card
    let eG := good.orderIsoOfFin rfl
    -- Define indexed families for good cells
    let src : Fin good.card → Set α := fun j => M_Q (eG j).val
    let tgt : Fin good.card → Set α := fun j => M_P (eG j).val
    -- Helper: eG maps to good indices
    have heG_good : ∀ j : Fin good.card, (eG j).val ∈ good := fun j => (eG j).prop
    -- Prove measure matching
    have h_meas_eq : ∀ j : Fin good.card, μ (src j) = μ (tgt j) := by
      intro j; show μ (M_Q (eG j).val) = μ (M_P (eG j).val)
      rw [hM_Q_eq, hM_P_eq]
    -- Helper for injectivity: distinct good indices give disjoint M_Q/M_P cells
    have h_idx_ne_of_ne : ∀ j₁ j₂ : Fin good.card, j₁ ≠ j₂ →
        (eG j₁).val ≠ (eG j₂).val := by
      intro j₁ j₂ h_ne h_same
      exact h_ne (eG.injective (Subtype.ext h_same))
    -- Prove injectivity of src: good M_Q cells lie in distinct Q-cells
    have hsrc_inj : Function.Injective src := by
      intro j₁ j₂ (h_eq : M_Q (eG j₁).val = M_Q (eG j₂).val)
      by_contra h_ne
      have h_disj_Q : Disjoint (ι_Q (eG j₁).val) (ι_Q (eG j₂).val) :=
        Q.pairwiseDisjoint (hι_Q _) (hι_Q _)
          (fun h => h_idx_ne_of_ne j₁ j₂ h_ne (hι_Q_inj h))
      have h_disj_MQ : Disjoint (M_Q (eG j₁).val) (M_Q (eG j₂).val) :=
        h_disj_Q.mono (hM_Q_sub _) (hM_Q_sub _)
      -- Equal + disjoint → self-disjoint → empty → measure 0
      have h_self_disj : Disjoint (M_Q (eG j₁).val) (M_Q (eG j₁).val) :=
        h_eq ▸ h_disj_MQ
      have : M_Q (eG j₁).val = ∅ :=
        Set.eq_empty_of_forall_notMem (fun x hx => Set.disjoint_left.mp h_self_disj hx hx)
      exact h_good_pos _ (heG_good j₁) (by rw [this, measure_empty])
    -- Prove injectivity of tgt: good M_P cells lie in distinct P-cells
    have htgt_inj : Function.Injective tgt := by
      intro j₁ j₂ (h_eq : M_P (eG j₁).val = M_P (eG j₂).val)
      by_contra h_ne
      have h_disj_P : Disjoint (ι_P (eG j₁).val) (ι_P (eG j₂).val) :=
        P.pairwiseDisjoint (hι_P _) (hι_P _)
          (fun h => h_idx_ne_of_ne j₁ j₂ h_ne (hι_P_inj h))
      have h_disj_MP : Disjoint (M_P (eG j₁).val) (M_P (eG j₂).val) :=
        h_disj_P.mono (hM_P_sub _) (hM_P_sub _)
      have h_self_disj : Disjoint (M_P (eG j₁).val) (M_P (eG j₁).val) :=
        h_eq ▸ h_disj_MP
      have : M_P (eG j₁).val = ∅ :=
        Set.eq_empty_of_forall_notMem (fun x hx => Set.disjoint_left.mp h_self_disj hx hx)
      exact h_good_pos_P _ (heG_good j₁) (by rw [this, measure_empty])
    -- Build MeasurablePartition for source (M_Q good cells + waste)
    let waste_src := Set.univ \ ⋃ j : Fin good.card, src j
    have h_waste_src_meas : MeasurableSet waste_src :=
      MeasurableSet.univ.diff (MeasurableSet.iUnion (fun j => hM_Q_meas _))
    let P_src : MeasurablePartition α μ := {
      parts := insert waste_src (Finset.univ.image src)
      measurable_parts := by
        intro S hS
        rw [Finset.mem_insert] at hS
        rcases hS with rfl | hS'
        · exact h_waste_src_meas
        · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hS'
          exact hM_Q_meas _
      pairwiseDisjoint := by
        intro S hS T hT hST
        simp only [Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff,
          Set.mem_image, Finset.mem_coe, Finset.mem_univ, true_and] at hS hT
        rw [Function.onFun_apply, id, id]
        rcases hS with rfl | ⟨j₁, rfl⟩ <;> rcases hT with rfl | ⟨j₂, rfl⟩
        · exact absurd rfl hST
        · exact Set.disjoint_sdiff_left.mono_right (Set.subset_iUnion _ j₂)
        · exact (Set.disjoint_sdiff_left.mono_right (Set.subset_iUnion _ j₁)).symm
        · have hj_ne : j₁ ≠ j₂ := fun h => hST (congrArg src h)
          have h_disj_Q : Disjoint (ι_Q (eG j₁).val) (ι_Q (eG j₂).val) :=
            Q.pairwiseDisjoint (hι_Q _) (hι_Q _)
              (fun h => h_idx_ne_of_ne j₁ j₂ hj_ne (hι_Q_inj h))
          exact h_disj_Q.mono (hM_Q_sub _) (hM_Q_sub _)
      ae_covers := by
        apply Filter.Eventually.of_forall; intro x
        by_cases hx : x ∈ ⋃ j : Fin good.card, src j
        · obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
          exact ⟨src j, Finset.mem_insert_of_mem
            (Finset.mem_image_of_mem _ (Finset.mem_univ j)), hxj⟩
        · exact ⟨waste_src, Finset.mem_insert_self _ _,
            Set.mem_sdiff_of_mem (Set.mem_univ _) hx⟩
    }
    -- Build MeasurablePartition for target (M_P good cells + waste)
    let waste_tgt := Set.univ \ ⋃ j : Fin good.card, tgt j
    have h_waste_tgt_meas : MeasurableSet waste_tgt :=
      MeasurableSet.univ.diff (MeasurableSet.iUnion (fun j => hM_P_meas _))
    let P_tgt : MeasurablePartition α μ := {
      parts := insert waste_tgt (Finset.univ.image tgt)
      measurable_parts := by
        intro S hS
        rw [Finset.mem_insert] at hS
        rcases hS with rfl | hS'
        · exact h_waste_tgt_meas
        · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hS'
          exact hM_P_meas _
      pairwiseDisjoint := by
        intro S hS T hT hST
        simp only [Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff,
          Set.mem_image, Finset.mem_coe, Finset.mem_univ, true_and] at hS hT
        rw [Function.onFun_apply, id, id]
        rcases hS with rfl | ⟨j₁, rfl⟩ <;> rcases hT with rfl | ⟨j₂, rfl⟩
        · exact absurd rfl hST
        · exact Set.disjoint_sdiff_left.mono_right (Set.subset_iUnion _ j₂)
        · exact (Set.disjoint_sdiff_left.mono_right (Set.subset_iUnion _ j₁)).symm
        · have hj_ne : j₁ ≠ j₂ := fun h => hST (congrArg tgt h)
          have h_disj_P : Disjoint (ι_P (eG j₁).val) (ι_P (eG j₂).val) :=
            P.pairwiseDisjoint (hι_P _) (hι_P _)
              (fun h => h_idx_ne_of_ne j₁ j₂ hj_ne (hι_P_inj h))
          exact h_disj_P.mono (hM_P_sub _) (hM_P_sub _)
      ae_covers := by
        apply Filter.Eventually.of_forall; intro x
        by_cases hx : x ∈ ⋃ j : Fin good.card, tgt j
        · obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
          exact ⟨tgt j, Finset.mem_insert_of_mem
            (Finset.mem_image_of_mem _ (Finset.mem_univ j)), hxj⟩
        · exact ⟨waste_tgt, Finset.mem_insert_self _ _,
            Set.mem_sdiff_of_mem (Set.mem_univ _) hx⟩
    }
    -- Prove membership in partition parts
    have hsrc_mem : ∀ j, src j ∈ P_src.parts :=
      fun j => Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    have htgt_mem : ∀ j, tgt j ∈ P_tgt.parts :=
      fun j => Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    -- Apply controlled cell alignment
    obtain ⟨e, he, h_good_align⟩ := MeasurePreserving.exists_controlled_cell_alignment
      P_src P_tgt src tgt hsrc_mem htgt_mem hsrc_inj htgt_inj h_meas_eq
    -- Extend to all i : Fin K
    refine ⟨e, he, fun i => ?_⟩
    by_cases hi : i ∈ good
    · -- Good case: find the corresponding good index j
      have hj : ∃ j : Fin good.card, (eG j).val = i := by
        exact ⟨eG.symm ⟨i, hi⟩, by simp [OrderIso.apply_symm_apply]⟩
      obtain ⟨j, hj_val⟩ := hj
      have h_src_j : src j = M_Q i := by show M_Q (eG j).val = M_Q i; rw [hj_val]
      have h_tgt_j : tgt j = M_P i := by show M_P (eG j).val = M_P i; rw [hj_val]
      have := h_good_align j
      rw [h_src_j, h_tgt_j] at this
      exact this
    · -- Bad case: μ(M_Q i) = 0, so ∀ᵐ x, x ∉ M_Q i; implication vacuous
      have hi_zero : μ (M_Q i) = 0 := by
        simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi; exact hi
      have : (M_Q i)ᶜ ∈ ae μ := by rw [mem_ae_iff]; simpa using hi_zero
      filter_upwards [this] with x hx h_abs
      exact absurd h_abs hx
  obtain ⟨e, he, h_cell⟩ := h_align
  -- Step 3: Use φ = e, ψ = id as cutDistance witnesses.
  -- For a.e. (x,y) with x ∈ M_Q(i), y ∈ M_Q(j):
  --   pullback(W_P, e)(x,y) = W_P(e x, e y) = c_P(ι_P i, ι_P j) = c_Q(ι_Q i, ι_Q j) = W_Q(x,y)
  -- Waste set
  set E_Q := Set.univ \ ⋃ i, M_Q i with hE_Q_def
  have hE_Q_meas : MeasurableSet E_Q :=
    MeasurableSet.univ.diff (MeasurableSet.iUnion (fun i => hM_Q_meas i))
  -- Step 3a: cutDistance ≤ cutNormDiff(pullback W_P e, W_Q)
  have h_cd_le : cutDistance W_P W_Q ≤
      cutNormDiff (pullback W_P (⇑e) he) (pullback W_Q id (MeasurePreserving.id μ)) := by
    unfold cutDistance
    apply csInf_le
    · use 0; intro d ⟨φ, ψ, hφ, hψ, hd⟩; rw [hd]; exact cutNormDiff_nonneg _ _
    · exact ⟨⇑e, id, he, MeasurePreserving.id μ, rfl⟩
  rw [pullback_id] at h_cd_le
  -- Step 3b: Show pullback W_P e and W_Q agree a.e. off the strip E_Q
  have h_agree : ∀ᵐ p ∂(μ.prod μ), p.1 ∉ E_Q → p.2 ∉ E_Q →
      (pullback W_P (⇑e) he).toAEEqFun p = W_Q.toAEEqFun p := by
    -- Collect a.e. facts
    have h_pb := pullback_ae W_P (⇑e) he
    have h_P_ae : ∀ᵐ q ∂(μ.prod μ),
        W_P.toAEEqFun q = mkStepFun P c_P q :=
      AEEqFun.coeFn_mk (mkStepFun P c_P) (mkStepFun_measurable' P c_P).aestronglyMeasurable
    have h_P_lifted : ∀ᵐ p ∂(μ.prod μ),
        W_P.toAEEqFun (e p.1, e p.2) = mkStepFun P c_P (e p.1, e p.2) := by
      exact (SymmKernel.measurePreserving_prodMap_self he).quasiMeasurePreserving.ae h_P_ae
    have h_Q_ae : ∀ᵐ p ∂(μ.prod μ),
        W_Q.toAEEqFun p = mkStepFun Q c_Q p :=
      AEEqFun.coeFn_mk (mkStepFun Q c_Q) (mkStepFun_measurable' Q c_Q).aestronglyMeasurable
    -- Cell alignment facts lifted to product measure
    have h_cell_fst : ∀ i, ∀ᵐ p ∂(μ.prod μ), p.1 ∈ M_Q i → e p.1 ∈ M_P i :=
      fun i => Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst (h_cell i)
    have h_cell_snd : ∀ i, ∀ᵐ p ∂(μ.prod μ), p.2 ∈ M_Q i → e p.2 ∈ M_P i :=
      fun i => Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd (h_cell i)
    have h_cell_all_fst : ∀ᵐ p ∂(μ.prod μ), ∀ i, p.1 ∈ M_Q i → e p.1 ∈ M_P i := by
      rw [Filter.eventually_all]; exact h_cell_fst
    have h_cell_all_snd : ∀ᵐ p ∂(μ.prod μ), ∀ i, p.2 ∈ M_Q i → e p.2 ∈ M_P i := by
      rw [Filter.eventually_all]; exact h_cell_snd
    -- Combine
    filter_upwards [h_pb, h_P_lifted, h_Q_ae, h_cell_all_fst, h_cell_all_snd]
      with p h_pb_p h_P_p h_Q_p h_e_fst h_e_snd
    intro h1_not h2_not
    -- p.1 ∉ E_Q means p.1 ∈ ⋃ i, M_Q i
    have h1_in : p.1 ∈ ⋃ i, M_Q i := by
      simp only [hE_Q_def, Set.mem_sdiff, Set.mem_univ, true_and, not_not] at h1_not
      exact h1_not
    have h2_in : p.2 ∈ ⋃ i, M_Q i := by
      simp only [hE_Q_def, Set.mem_sdiff, Set.mem_univ, true_and, not_not] at h2_not
      exact h2_not
    rw [Set.mem_iUnion] at h1_in h2_in
    obtain ⟨i, hi⟩ := h1_in
    obtain ⟨j, hj⟩ := h2_in
    -- e(p.1) ∈ M_P(i) ⊆ ι_P(i) and e(p.2) ∈ M_P(j) ⊆ ι_P(j)
    have he_fst : e p.1 ∈ M_P i := h_e_fst i hi
    have he_snd : e p.2 ∈ M_P j := h_e_snd j hj
    -- LHS: pullback W_P e at (p.1, p.2) = W_P(e p.1, e p.2) = mkStepFun P c_P (e p.1, e p.2)
    rw [h_pb_p, h_P_p]
    -- = c_P(ι_P i, ι_P j) by mkStepFun_eq_at'
    rw [mkStepFun_eq_at' P c_P (hι_P i) (hι_P j)
        (Set.mem_prod.mpr ⟨hM_P_sub i he_fst, hM_P_sub j he_snd⟩)]
    -- RHS: W_Q at (p.1, p.2) = mkStepFun Q c_Q (p.1, p.2) = c_Q(ι_Q i, ι_Q j)
    rw [h_Q_p, mkStepFun_eq_at' Q c_Q (hι_Q i) (hι_Q j)
        (Set.mem_prod.mpr ⟨hM_Q_sub i hi, hM_Q_sub j hj⟩)]
    -- c_P(ι_P i, ι_P j) = c_Q(ι_Q i, ι_Q j) by h_coeff_eq
    exact h_coeff_eq i j
  -- Step 3c: Apply strip helper
  have h_strip := cutNormDiff_le_of_ae_agree_off_strip
    (pullback W_P (⇑e) he) W_Q E_Q hE_Q_meas h_agree
  -- Step 4: Bound waste measure μ(E_Q).toReal ≤ ∑ i, |w_P i - w_Q i|
  -- Since E_Q = univ \ ⋃ i, M_Q i, and ⋃ ι_Q i covers ae univ,
  -- we have E_Q =ae ⋃ i, (ι_Q i \ M_Q i), and these are disjoint.
  -- μ(ι_Q i \ M_Q i) = μ(ι_Q i) - min(μ(ι_P i), μ(ι_Q i))
  --                   = max(0, μ(ι_Q i) - μ(ι_P i))  [in ENNReal, = (μ(ι_Q i) - μ(ι_P i))⁺]
  -- ∑ max(0, (μ(ι_Q i)).toReal - (μ(ι_P i)).toReal) ≤ ∑ |(μ(ι_P i)).toReal - (μ(ι_Q i)).toReal|
  -- Direct approach: bound μ(E_Q) ≤ ∑ μ(ι_Q i \ M_Q i), then convert to Real
  suffices h_waste : (μ E_Q).toReal ≤ ∑ i : Fin K, |(μ (ι_P i)).toReal - (μ (ι_Q i)).toReal| by
    linarith [h_cd_le, h_strip]
  -- E_Q ⊆ (⋃ i, (ι_Q i \ M_Q i)) ∪ (univ \ ⋃ i, ι_Q i)
  -- The second part has measure 0 by ae_covers of Q
  -- Bound μ(E_Q)
  have h_EQ_bound : μ E_Q ≤ ∑ i : Fin K, (μ (ι_Q i) - μ (M_Q i)) := by
    -- E_Q = univ \ ⋃ i, M_Q i ⊆ (univ \ ⋃ i, ι_Q i) ∪ ⋃ i, (ι_Q i \ M_Q i)
    have h_sub : E_Q ⊆ (Set.univ \ ⋃ i, ι_Q i) ∪ ⋃ i, (ι_Q i \ M_Q i) := by
      intro x hx
      rw [hE_Q_def, Set.mem_sdiff] at hx
      by_cases hx_union : x ∈ ⋃ i, ι_Q i
      · right
        rw [Set.mem_iUnion] at hx_union ⊢
        obtain ⟨i, hi⟩ := hx_union
        exact ⟨i, hi, fun hmq => hx.2 (Set.mem_iUnion.mpr ⟨i, hmq⟩)⟩
      · exact Or.inl ⟨hx.1, hx_union⟩
    calc μ E_Q ≤ μ ((Set.univ \ ⋃ i, ι_Q i) ∪ ⋃ i, (ι_Q i \ M_Q i)) := measure_mono h_sub
      _ ≤ μ (Set.univ \ ⋃ i, ι_Q i) + μ (⋃ i, (ι_Q i \ M_Q i)) := measure_union_le _ _
      _ = 0 + μ (⋃ i, (ι_Q i \ M_Q i)) := by
          congr 1
          -- univ \ ⋃ i, ι_Q i has measure 0 by Q.ae_covers
          apply le_antisymm _ (zero_le)
          -- ⋃ S ∈ Q.parts, S ⊇ ⋃ i, ι_Q i since hι_Q_surj gives that every part is some ι_Q i
          have h_eq : ⋃ i, ι_Q i = ⋃ S ∈ Q.parts, S := by
            ext x; simp only [Set.mem_iUnion, Set.mem_iUnion]; constructor
            · rintro ⟨i, hi⟩; exact ⟨ι_Q i, hι_Q i, hi⟩
            · rintro ⟨S, hS, hx⟩; obtain ⟨i, hi⟩ := hι_Q_surj S hS; exact ⟨i, hi ▸ hx⟩
          rw [h_eq]
          -- μ(univ \ ⋃ S ∈ Q.parts, S) = 0 by Q.ae_covers
          have h_compl_null : μ {x | ¬∃ S ∈ Q.parts, x ∈ S} = 0 := by
            have h_ae := Q.ae_covers; rwa [ae_iff] at h_ae
          calc μ (Set.univ \ ⋃ S ∈ Q.parts, S)
              ≤ μ {x | ¬∃ S ∈ Q.parts, x ∈ S} := by
                apply measure_mono; intro x hx
                simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_setOf_eq] at hx ⊢
                exact fun ⟨S, hS, hxS⟩ => hx.2 ⟨S, hS, hxS⟩
              _ = 0 := h_compl_null
      _ ≤ ∑ i : Fin K, μ (ι_Q i \ M_Q i) := by
          rw [zero_add]
          calc μ (⋃ i, (ι_Q i \ M_Q i))
              ≤ ∑' i, μ (ι_Q i \ M_Q i) := measure_iUnion_le _
            _ = ∑ i : Fin K, μ (ι_Q i \ M_Q i) :=
                tsum_eq_sum (fun i hi => absurd (Finset.mem_univ i) hi)
      _ = ∑ i : Fin K, (μ (ι_Q i) - μ (M_Q i)) := by
          congr 1; ext i
          rw [measure_sdiff (hM_Q_sub i) (hM_Q_meas i).nullMeasurableSet (measure_ne_top μ _)]
  -- Convert to Real
  have h_ne_top : ∀ i : Fin K, μ (ι_Q i) ≠ ⊤ := fun i => measure_ne_top μ _
  have h_M_ne_top : ∀ i : Fin K, μ (M_Q i) ≠ ⊤ := fun i => measure_ne_top μ _
  have h_diff_le : ∀ i : Fin K, μ (M_Q i) ≤ μ (ι_Q i) :=
    fun i => measure_mono (hM_Q_sub i)
  -- μ(E_Q).toReal ≤ (∑ i, (μ(ι_Q i) - μ(M_Q i))).toReal
  --              = ∑ i, (μ(ι_Q i) - μ(M_Q i)).toReal
  --              = ∑ i, ((μ(ι_Q i)).toReal - (μ(M_Q i)).toReal)
  --              = ∑ i, ((μ(ι_Q i)).toReal - min((μ(ι_P i)).toReal, (μ(ι_Q i)).toReal))
  --              = ∑ i, max(0, (μ(ι_Q i)).toReal - (μ(ι_P i)).toReal)
  --              ≤ ∑ i, |(μ(ι_P i)).toReal - (μ(ι_Q i)).toReal|
  have h_sum_ne_top : ∑ i : Fin K, (μ (ι_Q i) - μ (M_Q i)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (measure_ne_top μ Set.univ)
    calc ∑ i : Fin K, (μ (ι_Q i) - μ (M_Q i))
        ≤ ∑ i : Fin K, μ (ι_Q i) :=
          Finset.sum_le_sum (fun i _ => tsub_le_self)
      _ ≤ μ Set.univ := by
          have h_disj : PairwiseDisjoint (↑(Finset.univ : Finset (Fin K))) ι_Q :=
            fun i _ j _ hij => Q.pairwiseDisjoint (hι_Q i) (hι_Q j)
              (fun h => hij (hι_Q_inj h))
          have h_meas : ∀ i ∈ (Finset.univ : Finset (Fin K)), MeasurableSet (ι_Q i) :=
            fun i _ => Q.measurableSet_part (hι_Q i)
          rw [← measure_biUnion_finset h_disj h_meas]
          exact measure_mono (Set.subset_univ _)
  calc (μ E_Q).toReal
      ≤ (∑ i : Fin K, (μ (ι_Q i) - μ (M_Q i))).toReal :=
        ENNReal.toReal_mono h_sum_ne_top h_EQ_bound
    _ = ∑ i : Fin K, (μ (ι_Q i) - μ (M_Q i)).toReal := by
        rw [ENNReal.toReal_sum (fun i _ => ENNReal.sub_ne_top (h_ne_top i))]
    _ = ∑ i : Fin K, ((μ (ι_Q i)).toReal - (μ (M_Q i)).toReal) := by
        congr 1; ext i
        exact ENNReal.toReal_sub_of_le (h_diff_le i) (h_ne_top i)
    _ ≤ ∑ i : Fin K, |(μ (ι_P i)).toReal - (μ (ι_Q i)).toReal| := by
        apply Finset.sum_le_sum; intro i _
        -- (μ(ι_Q i)).toReal - (μ(M_Q i)).toReal ≤ |(μ(ι_P i)).toReal - (μ(ι_Q i)).toReal|
        -- where μ(M_Q i) = min(μ(ι_P i), μ(ι_Q i))
        -- Case split on which measure is larger
        rcases le_total (μ (ι_P i)) (μ (ι_Q i)) with h_le | h_le
        · -- μ(ι_P i) ≤ μ(ι_Q i), so min = μ(ι_P i)
          rw [hM_Q_eq i, min_eq_left h_le]
          have h_le_r := ENNReal.toReal_mono (h_ne_top i) h_le
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h_le_r)]
        · -- μ(ι_Q i) ≤ μ(ι_P i), so min = μ(ι_Q i)
          rw [hM_Q_eq i, min_eq_right h_le, sub_self]
          exact abs_nonneg _

set_option maxHeartbeats 1600000 in
/-- Cross-partition weight stability: `cutDistance(stepify P V, mkStepGraphon Q c_Q) ≤ 2∑|w-w_Q|`.

Given partition P with k ≤ K cells (padded to Fin K) and partition Q with K cells,
if the coefficient matrices agree (matching rectAverage of V on active P cells),
then the cutDistance is bounded by twice the sum of weight differences.

**Sorry traces to**: `MeasurePreserving.exists_common_extension` (Rokhlin) via
`exists_controlled_cell_alignment` for cell alignment between the intermediate
partition P_mid and P. -/
private theorem cutDistance_cross_partition_weight_le {K : ℕ}
    (P : MeasurablePartition α μ) (V : Graphon α μ) (hP_le : P.parts.card ≤ K)
    (Q : MeasurablePartition α μ) (c_Q : Set α → Set α → ℝ)
    (hc_Q_symm : ∀ S ∈ Q.parts, ∀ T ∈ Q.parts, c_Q S T = c_Q T S)
    (hc_Q_mem : ∀ S ∈ Q.parts, ∀ T ∈ Q.parts, c_Q S T ∈ Set.Icc 0 1)
    (ι_Q : Fin K → Set α) (hι_Q : ∀ i, ι_Q i ∈ Q.parts)
    (hι_Q_inj : Function.Injective ι_Q)
    (hι_Q_surj : ∀ S ∈ Q.parts, ∃ i, ι_Q i = S)
    (pad_fn : Fin K → Set α)
    (h_pad_mem : ∀ i : Fin K, (i : ℕ) < P.parts.card → pad_fn i ∈ P.parts)
    (h_pad_inj : ∀ i j : Fin K, (i : ℕ) < P.parts.card → (j : ℕ) < P.parts.card →
                  pad_fn i = pad_fn j → i = j)
    (h_pad_surj : ∀ S ∈ P.parts, ∃ i : Fin K, (i : ℕ) < P.parts.card ∧ pad_fn i = S)
    (w : Fin K → ℝ)
    (hw_def : ∀ i, w i = if (i : ℕ) < P.parts.card then (μ (pad_fn i)).toReal else 0)
    (hw_nn : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (h_coeff : ∀ i j : Fin K, c_Q (ι_Q i) (ι_Q j) =
        if (i : ℕ) < P.parts.card ∧ (j : ℕ) < P.parts.card
        then rectAverage V (pad_fn i) (pad_fn j) else 0) :
    cutDistance (stepify P V) (mkStepGraphon Q c_Q hc_Q_symm hc_Q_mem) ≤
      2 * ∑ i : Fin K, |w i - (μ (ι_Q i)).toReal| := by
  classical
  set k := P.parts.card with hk_def
  -- Build P_mid with K cells via exists_partition_with_measures
  obtain ⟨P_mid, ι_mid, hι_mid_mem, hι_mid_inj, hι_mid_surj, hP_mid_card, hι_mid_meas⟩ :=
    exists_partition_with_measures (μ := μ) w hw_nn hw_sum
  -- Build c_mid on P_mid: c_mid(ι_mid i, ι_mid j) = c_Q(ι_Q i, ι_Q j)
  have hι_mid_bij : ∀ S ∈ P_mid.parts, ∃! i : Fin K, ι_mid i = S := by
    intro S hS; obtain ⟨i, hi⟩ := hι_mid_surj S hS
    exact ⟨i, hi, fun j hj => hι_mid_inj (hj.trans hi.symm)⟩
  set ι_mid_inv : ∀ S : Set α, S ∈ P_mid.parts → Fin K :=
    fun S hS => (hι_mid_bij S hS).choose
  have hι_mid_inv_spec : ∀ S (hS : S ∈ P_mid.parts), ι_mid (ι_mid_inv S hS) = S :=
    fun S hS => (hι_mid_bij S hS).choose_spec.1
  have hι_mid_inv_eq : ∀ i, ι_mid_inv (ι_mid i) (hι_mid_mem i) = i :=
    fun i => hι_mid_inj (hι_mid_inv_spec (ι_mid i) (hι_mid_mem i))
  set c_mid : Set α → Set α → ℝ := fun S T =>
    if hS : S ∈ P_mid.parts then if hT : T ∈ P_mid.parts then
      c_Q (ι_Q (ι_mid_inv S hS)) (ι_Q (ι_mid_inv T hT))
    else 0 else 0
  have h_cmid_ι : ∀ i j, c_mid (ι_mid i) (ι_mid j) = c_Q (ι_Q i) (ι_Q j) := by
    intro i j; simp only [c_mid, hι_mid_mem i, hι_mid_mem j, dif_pos, hι_mid_inv_eq]
  have h_cmid_symm : ∀ S ∈ P_mid.parts, ∀ T ∈ P_mid.parts, c_mid S T = c_mid T S := by
    intro S hS T hT; simp only [c_mid, hS, hT, dif_pos]
    exact hc_Q_symm _ (hι_Q _) _ (hι_Q _)
  have h_cmid_mem : ∀ S ∈ P_mid.parts, ∀ T ∈ P_mid.parts, c_mid S T ∈ Set.Icc 0 1 := by
    intro S hS T hT; simp only [c_mid, hS, hT, dif_pos]
    exact hc_Q_mem _ (hι_Q _) _ (hι_Q _)
  set G_mid := mkStepGraphon P_mid c_mid h_cmid_symm h_cmid_mem
  -- Part 1: cutDistance(stepify P V, G_mid) ≤ 0
  -- Use alignment between P_mid and P via exists_controlled_cell_alignment
  have h_part1 : cutDistance (stepify P V) G_mid ≤ 0 := by
    -- Build embedding Fin k → Fin K
    set embed : Fin k → Fin K := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hP_le⟩
    have hembed_inj : Function.Injective embed :=
      fun _ _ h => Fin.ext (Fin.mk.inj_iff.mp h)
    -- Active P_mid cells: ι_mid(embed i)
    have h_meas_match : ∀ i : Fin k, μ (ι_mid (embed i)) = μ (pad_fn (embed i)) := by
      intro i
      have h_w : (μ (ι_mid (embed i))).toReal = w (embed i) := hι_mid_meas (embed i)
      have h_active : (embed i : ℕ) < k := i.isLt
      rw [hw_def, if_pos h_active] at h_w
      rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top μ _)]
      exact h_w
    -- ι_mid ∘ embed is injective into P_mid.parts
    have hι_mid_embed_inj : Function.Injective (fun i : Fin k => ι_mid (embed i)) :=
      hι_mid_inj.comp hembed_inj
    -- pad_fn ∘ embed gives active P cells, injective
    have h_pad_embed_inj : Function.Injective (fun i : Fin k => pad_fn (embed i)) := by
      intro a b h; exact Fin.ext (Fin.mk.inj_iff.mp (h_pad_inj (embed a) (embed b) a.isLt b.isLt h))
    -- Get alignment: maps P cells to P_mid cells
    obtain ⟨e, he, h_align⟩ := MeasurePreserving.exists_controlled_cell_alignment
      P P_mid (fun i : Fin k => pad_fn (embed i)) (fun i : Fin k => ι_mid (embed i))
      (fun i => h_pad_mem (embed i) i.isLt) (fun i => hι_mid_mem (embed i))
      h_pad_embed_inj hι_mid_embed_inj (fun i => (h_meas_match i).symm)
    -- cutDistance(G_mid, stepify) ≤ cutNormDiff(pullback(G_mid, e), stepify)
    -- Use symmetry: cutDistance(stepify, G_mid) = cutDistance(G_mid, stepify)
    rw [cutDistance_symm]
    -- cutDistance ≤ cutNormDiff of pullback witnesses
    have h_cd_le : cutDistance G_mid (stepify P V) ≤
        cutNormDiff (pullback G_mid (⇑e) he)
          (pullback (stepify P V) id (MeasurePreserving.id μ)) := by
      unfold cutDistance; apply csInf_le
      · use 0; intro d ⟨φ, ψ, hφ, hψ, hd⟩; rw [hd]; exact cutNormDiff_nonneg _ _
      · exact ⟨⇑e, id, he, MeasurePreserving.id μ, rfl⟩
    rw [pullback_id] at h_cd_le
    -- Waste set E_P = univ \ ⋃ S ∈ P.parts, S (has measure 0)
    set E_P := Set.univ \ ⋃ S ∈ P.parts, S with hE_P_def
    have hE_P_meas : MeasurableSet E_P :=
      MeasurableSet.univ.diff (MeasurableSet.biUnion P.parts.countable_toSet
        (fun S hS => P.measurableSet_part hS))
    have hE_P_null : μ E_P = 0 := by
      have h_ae := P.ae_covers; rw [ae_iff] at h_ae
      refine le_antisymm ?_ (zero_le)
      calc μ E_P ≤ μ {x | ¬∃ S ∈ P.parts, x ∈ S} := by
            apply measure_mono; intro x hx
            rw [hE_P_def, Set.mem_sdiff] at hx
            simp only [Set.mem_setOf_eq]
            exact fun ⟨S, hS, hxS⟩ =>
              hx.2 (Set.mem_biUnion hS hxS)
        _ = 0 := h_ae
    -- Show agreement a.e. off E_P
    have h_agree : ∀ᵐ p ∂(μ.prod μ), p.1 ∉ E_P → p.2 ∉ E_P →
        (pullback G_mid (⇑e) he).toAEEqFun p = (stepify P V).toAEEqFun p := by
      -- Collect a.e. facts
      have h_pb := pullback_ae G_mid (⇑e) he
      have h_mid_ae : ∀ᵐ q ∂(μ.prod μ),
          G_mid.toAEEqFun q = mkStepFun P_mid c_mid q :=
        AEEqFun.coeFn_mk (mkStepFun P_mid c_mid)
          (mkStepFun_measurable' P_mid c_mid).aestronglyMeasurable
      have h_mid_lifted : ∀ᵐ p ∂(μ.prod μ),
          G_mid.toAEEqFun (e p.1, e p.2) = mkStepFun P_mid c_mid (e p.1, e p.2) :=
        (SymmKernel.measurePreserving_prodMap_self he).quasiMeasurePreserving.ae h_mid_ae
      have h_step_ae := stepify_ae P V
      -- Cell alignment lifted to product measure
      have h_align_fst : ∀ i : Fin k, ∀ᵐ p ∂(μ.prod μ),
          p.1 ∈ pad_fn (embed i) → e p.1 ∈ ι_mid (embed i) :=
        fun i => Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst (h_align i)
      have h_align_snd : ∀ i : Fin k, ∀ᵐ p ∂(μ.prod μ),
          p.2 ∈ pad_fn (embed i) → e p.2 ∈ ι_mid (embed i) :=
        fun i => Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd (h_align i)
      have h_align_all_fst : ∀ᵐ p ∂(μ.prod μ), ∀ i : Fin k,
          p.1 ∈ pad_fn (embed i) → e p.1 ∈ ι_mid (embed i) := by
        rw [Filter.eventually_all]; exact h_align_fst
      have h_align_all_snd : ∀ᵐ p ∂(μ.prod μ), ∀ i : Fin k,
          p.2 ∈ pad_fn (embed i) → e p.2 ∈ ι_mid (embed i) := by
        rw [Filter.eventually_all]; exact h_align_snd
      -- Combine
      filter_upwards [h_pb, h_mid_lifted, h_step_ae, h_align_all_fst, h_align_all_snd]
        with p h_pb_p h_mid_p h_step_p h_e_fst h_e_snd
      intro h1_not h2_not
      -- p.1 ∉ E_P means p.1 ∈ ⋃ S ∈ P.parts, S, so p.1 ∈ some P cell
      have h1_in : ∃ S ∈ P.parts, p.1 ∈ S := by
        have h_mem : p.1 ∈ ⋃ S ∈ P.parts, S := by
          by_contra h_nmem
          exact h1_not ⟨Set.mem_univ _, h_nmem⟩
        obtain ⟨S, hS, hxS⟩ := Set.mem_iUnion₂.mp h_mem
        exact ⟨S, hS, hxS⟩
      have h2_in : ∃ S ∈ P.parts, p.2 ∈ S := by
        have h_mem : p.2 ∈ ⋃ S ∈ P.parts, S := by
          by_contra h_nmem
          exact h2_not ⟨Set.mem_univ _, h_nmem⟩
        obtain ⟨S, hS, hxS⟩ := Set.mem_iUnion₂.mp h_mem
        exact ⟨S, hS, hxS⟩
      obtain ⟨S, hS, hpS⟩ := h1_in
      obtain ⟨T, hT, hpT⟩ := h2_in
      -- Find active indices a, b with pad_fn(embed a) = S, pad_fn(embed b) = T
      obtain ⟨ia, hia_lt, hia_eq⟩ := h_pad_surj S hS
      obtain ⟨ib, hib_lt, hib_eq⟩ := h_pad_surj T hT
      set a : Fin k := ⟨(ia : ℕ), hia_lt⟩ with ha_def
      set b : Fin k := ⟨(ib : ℕ), hib_lt⟩ with hb_def
      have ha_embed : embed a = ia := Fin.ext rfl
      have hb_embed : embed b = ib := Fin.ext rfl
      -- p.1 ∈ pad_fn(embed a) and p.2 ∈ pad_fn(embed b)
      have hp1 : p.1 ∈ pad_fn (embed a) := ha_embed ▸ hia_eq ▸ hpS
      have hp2 : p.2 ∈ pad_fn (embed b) := hb_embed ▸ hib_eq ▸ hpT
      -- Alignment: e(p.1) ∈ ι_mid(embed a), e(p.2) ∈ ι_mid(embed b)
      have he1 : e p.1 ∈ ι_mid (embed a) := h_e_fst a hp1
      have he2 : e p.2 ∈ ι_mid (embed b) := h_e_snd b hp2
      -- LHS: pullback G_mid e at p = G_mid(e p.1, e p.2) = mkStepFun P_mid c_mid (e p.1, e p.2)
      --     = c_mid(ι_mid(embed a), ι_mid(embed b))
      --     = c_Q(ι_Q(embed a), ι_Q(embed b))
      --     = rectAverage V (pad_fn(embed a)) (pad_fn(embed b))  [by h_coeff, since a, b active]
      rw [h_pb_p, h_mid_p,
          mkStepFun_eq_at' P_mid c_mid (hι_mid_mem (embed a)) (hι_mid_mem (embed b))
            (Set.mem_prod.mpr ⟨he1, he2⟩),
          h_cmid_ι, h_coeff,
          if_pos ⟨ha_embed ▸ hia_lt, hb_embed ▸ hib_lt⟩]
      -- RHS: stepify P V at p = stepifyFun P V p = rectAverage V S T
      --     = rectAverage V (pad_fn(embed a)) (pad_fn(embed b))
      rw [h_step_p, stepifyFun_eq_rectAverage P V hS hT (Set.mem_prod.mpr ⟨hpS, hpT⟩),
          ← hia_eq, ← hib_eq, ha_embed, hb_embed]
    -- Apply strip helper
    have h_strip := cutNormDiff_le_of_ae_agree_off_strip
      (pullback G_mid (⇑e) he) (stepify P V) E_P hE_P_meas h_agree
    rw [hE_P_null, ENNReal.toReal_zero, mul_zero] at h_strip
    linarith [h_cd_le]
  -- Part 2: cutDistance(G_mid, mkStepGraphon Q c_Q) ≤ 2∑|w - w_Q|
  -- by cutDistance_step_weight_le with matching coefficients
  have h_part2 : cutDistance G_mid (mkStepGraphon Q c_Q hc_Q_symm hc_Q_mem) ≤
      2 * ∑ i : Fin K, |w i - (μ (ι_Q i)).toReal| := by
    have h_coeff_eq : ∀ i j : Fin K,
        c_mid (ι_mid i) (ι_mid j) = c_Q (ι_Q i) (ι_Q j) := h_cmid_ι
    calc cutDistance G_mid (mkStepGraphon Q c_Q hc_Q_symm hc_Q_mem)
        ≤ 2 * ∑ i : Fin K, |(μ (ι_mid i)).toReal - (μ (ι_Q i)).toReal| :=
          cutDistance_step_weight_le P_mid Q c_mid c_Q h_cmid_symm h_cmid_mem
            hc_Q_symm hc_Q_mem ι_mid ι_Q hι_mid_mem hι_Q hι_mid_inj hι_Q_inj
            hι_mid_surj hι_Q_surj h_coeff_eq
      _ = 2 * ∑ i : Fin K, |w i - (μ (ι_Q i)).toReal| := by
          congr 1; congr 1; ext i; rw [hι_mid_meas i]
  -- Part 3: Triangle inequality
  calc cutDistance (stepify P V) (mkStepGraphon Q c_Q hc_Q_symm hc_Q_mem)
      ≤ cutDistance (stepify P V) G_mid +
        cutDistance G_mid (mkStepGraphon Q c_Q hc_Q_symm hc_Q_mem) :=
        cutDistance_triangle _ _ _
    _ ≤ 0 + 2 * ∑ i : Fin K, |w i - (μ (ι_Q i)).toReal| := add_le_add h_part1 h_part2
    _ = 2 * ∑ i : Fin K, |w i - (μ (ι_Q i)).toReal| := zero_add _

set_option maxHeartbeats 800000 in
/-- **Bounded step inverse counting lemma**: uniform version of `step_quantitative_icl`
over all partitions with at most K parts.

For any cardinality bound K, accuracy ε > 0, there exist δ > 0 and graph size m such that
for ANY partition P with `P.parts.card ≤ K`, if two step graphons on P have homomorphism
densities within δ for all graphs on at most m vertices, their cut distance is less than ε.

**Proof sketch**: The coefficient space of step graphons on a partition with ≤ K parts
embeds into `[0,1]^{K² × 2} × [0,1]^K` (edge weights + part measures), which is compact.
By contradiction, extract a sequence of counterexamples (Pₙ, Uₙ, Wₙ) with densities
converging but cut distance bounded below. Pad all partitions to Fin K (adding zero-measure
parts), pass to a convergent subsequence in the compact coefficient space, and construct
limit step graphons on a common partition. The NoAtoms hypothesis ensures the limit
partition can be realized as a MeasurablePartition. The existing `step_quantitative_icl`
logic then gives the contradiction. -/
private theorem step_quantitative_icl_bounded (K : ℕ) (ε : ℝ) (hε : ε > 0) :
    ∃ (δ : ℝ) (_ : δ > 0) (m : ℕ),
    ∀ (P : MeasurablePartition α μ), P.parts.card ≤ K →
    ∀ (U W : Graphon α μ),
      (∀ (F : SimpleGraph (Fin m)) [DecidableRel F.Adj],
        |homDensity F (stepify P U) - homDensity F (stepify P W)| < δ) →
      cutDistance (stepify P U) (stepify P W) < ε := by
  classical
  by_contra h_neg
  push Not at h_neg
  have h_seq : ∀ n : ℕ, ∃ (P_n : MeasurablePartition α μ) (_ : P_n.parts.card ≤ K)
      (U_n W_n : Graphon α μ),
      (∀ (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
        |homDensity F (stepify P_n U_n) - homDensity F (stepify P_n W_n)| <
          1 / (↑n + 1 : ℝ)) ∧
      cutDistance (stepify P_n U_n) (stepify P_n W_n) ≥ ε := by
    intro n
    obtain ⟨P_n, hP_n, U_n, W_n, h1, h2⟩ := h_neg (1 / (↑n + 1 : ℝ)) (by positivity) n
    exact ⟨P_n, hP_n, U_n, W_n, h1, h2⟩
  choose P_seq hP_card U_seq W_seq h_close h_far using h_seq
  set pad : ∀ n : ℕ, Fin K → Set α := fun n i =>
    if h : (i : ℕ) < (P_seq n).parts.card
    then ((P_seq n).parts.equivFin.symm ⟨i, h⟩ : Set α)
    else if hne : ∃ S, S ∈ (P_seq n).parts
    then (hne.choose : Set α)
    else Set.univ with pad_def
  set w_seq : ℕ → Fin K → ℝ := fun n i =>
    if (i : ℕ) < (P_seq n).parts.card
    then (μ (pad n i)).toReal
    else 0 with w_seq_def
  set coeff_seq : ℕ → Fin K → Fin K → Fin 2 → ℝ := fun n i j b =>
    if (i : ℕ) < (P_seq n).parts.card ∧ (j : ℕ) < (P_seq n).parts.card
    then if b = 0
      then rectAverage (U_seq n) (pad n i) (pad n j)
      else rectAverage (W_seq n) (pad n i) (pad n j)
    else 0 with coeff_seq_def
  have h_pad_mem : ∀ (n : ℕ) (i : Fin K), (i : ℕ) < (P_seq n).parts.card →
      pad n i ∈ (P_seq n).parts := by
    intro n i hi; simp only [pad, dif_pos hi]
    exact ((P_seq n).parts.equivFin.symm ⟨i, hi⟩).prop
  have h_pad_inj : ∀ n, ∀ i j : Fin K,
      (i : ℕ) < (P_seq n).parts.card → (j : ℕ) < (P_seq n).parts.card →
      pad n i = pad n j → i = j := by
    intro n i j hi hj hij
    simp only [pad, dif_pos hi, dif_pos hj] at hij
    have h_eq := (P_seq n).parts.equivFin.symm.injective (Subtype.val_injective hij)
    exact Fin.ext (Fin.mk.inj_iff.mp h_eq)
  have h_pad_surj : ∀ n, ∀ S ∈ (P_seq n).parts, ∃ i : Fin K,
      (i : ℕ) < (P_seq n).parts.card ∧ pad n i = S := by
    intro n S hS
    set idx := (P_seq n).parts.equivFin ⟨S, hS⟩
    have h_lt : (idx : ℕ) < (P_seq n).parts.card := idx.isLt
    have h_lt_K : (idx : ℕ) < K := lt_of_lt_of_le h_lt (hP_card n)
    refine ⟨⟨idx, h_lt_K⟩, h_lt, ?_⟩
    simp only [pad, dif_pos h_lt]
    have h_symm := (P_seq n).parts.equivFin.symm_apply_apply ⟨S, hS⟩
    exact congrArg Subtype.val h_symm
  have h_c_mem : ∀ n i j b, coeff_seq n i j b ∈ Set.Icc (0 : ℝ) 1 := by
    intro n i j b; simp only [coeff_seq]
    split
    · rename_i h; split
      · exact rectAverage_mem_Icc _ _ _ ((P_seq n).measurableSet_part (h_pad_mem n i h.1))
            ((P_seq n).measurableSet_part (h_pad_mem n j h.2))
      · exact rectAverage_mem_Icc _ _ _ ((P_seq n).measurableSet_part (h_pad_mem n i h.1))
            ((P_seq n).measurableSet_part (h_pad_mem n j h.2))
    · exact ⟨le_refl 0, zero_le_one⟩
  have h_w_mem : ∀ (n : ℕ) (i : Fin K), w_seq n i ∈ Set.Icc (0 : ℝ) 1 := by
    intro n i; simp only [w_seq]; split
    · exact ⟨ENNReal.toReal_nonneg, by
        have h1 : μ (pad n i) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        rw [measure_univ] at h1
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h1)⟩
    · exact ⟨le_refl 0, zero_le_one⟩
  have h_compact_cw :
      IsCompact {f : (Fin K → Fin K → Fin 2 → ℝ) × (Fin K → ℝ) |
        (∀ i j b, f.1 i j b ∈ Set.Icc 0 1) ∧ (∀ i, f.2 i ∈ Set.Icc 0 1)} :=
    IsCompact.prod
      (isCompact_pi_infinite (fun _ => isCompact_pi_infinite (fun _ =>
        isCompact_pi_infinite (fun _ => isCompact_Icc))))
      (isCompact_pi_infinite (fun _ => isCompact_Icc))
  have h_data_mem : ∀ n, (coeff_seq n, w_seq n) ∈
      {f : (Fin K → Fin K → Fin 2 → ℝ) × (Fin K → ℝ) |
        (∀ i j b, f.1 i j b ∈ Set.Icc 0 1) ∧ (∀ i, f.2 i ∈ Set.Icc 0 1)} :=
    fun n => ⟨h_c_mem n, h_w_mem n⟩
  obtain ⟨⟨c_lim, w_lim⟩, ⟨h_clim_mem, h_wlim_mem⟩, ψ, hψ, h_conv⟩ :=
    h_compact_cw.isSeqCompact h_data_mem
  have h_pw_c : ∀ i j b, Tendsto (fun n => coeff_seq (ψ n) i j b) atTop
      (nhds (c_lim i j b)) := by
    intro i j b
    exact ((tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp
      ((continuous_fst.tendsto _).comp h_conv)) i)) j)) b)
  have h_pw_w : ∀ i, Tendsto (fun n => w_seq (ψ n) i) atTop (nhds (w_lim i)) := by
    intro i; exact (tendsto_pi_nhds.mp ((continuous_snd.tendsto _).comp h_conv)) i
  have h_wlim_nn : ∀ i, 0 ≤ w_lim i := fun i => (h_wlim_mem i).1
  have h_w_sum : ∀ n, ∑ i : Fin K, w_seq n i = 1 := by
    intro n
    -- The sum over Fin K splits into active (i.val < parts.card) giving
    -- ∑ S ∈ parts, (μ S).toReal, and padded giving 0.
    -- Then partition coverage gives ∑ = 1.
    --
    -- Step 1: Rewrite each term to its if-then-else form
    conv_lhs => arg 2; ext i; rw [show w_seq n i =
      if (i : ℕ) < (P_seq n).parts.card then (μ (pad n i)).toReal else 0 from rfl]
    -- Step 2: Use Finset.sum_ite to split
    simp_rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    -- Step 3: Reindex the filtered sum to ∑ S ∈ parts using sum_bij
    -- Define inverse: for S ∈ parts, find the index via equivFin
    have h_reindex :
        ∑ x ∈ Finset.univ.filter (fun i : Fin K => (i : ℕ) < (P_seq n).parts.card),
          (μ (pad n x)).toReal =
        (P_seq n).parts.sum (fun S => (μ S).toReal) := by
      apply Finset.sum_bij (fun i (hi : i ∈ _) => pad n i)
      · intro i hi
        exact h_pad_mem n i ((Finset.mem_filter.mp hi).2)
      · intro i₁ hi₁ i₂ hi₂ h
        exact h_pad_inj n i₁ i₂ ((Finset.mem_filter.mp hi₁).2)
          ((Finset.mem_filter.mp hi₂).2) h
      · intro S hS
        obtain ⟨i, hi_lt, hi_eq⟩ := h_pad_surj n S hS
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi_lt⟩, hi_eq⟩
      · intro _ _; rfl
    rw [h_reindex]
    -- Step 4: Show ∑ S ∈ parts, (μ S).toReal = 1 using partition properties
    have h_ne_top : ∀ S ∈ (P_seq n).parts, μ S ≠ ⊤ :=
      fun S _ => ne_top_of_le_ne_top (measure_ne_top μ _) (measure_mono (Set.subset_univ _))
    rw [← ENNReal.toReal_sum (fun S hS => h_ne_top S hS)]
    rw [show ∑ S ∈ (P_seq n).parts, μ S = μ (⋃ S ∈ (P_seq n).parts, id S) from
      (measure_biUnion_finset
        (fun S hS T hT hne => (P_seq n).pairwiseDisjoint hS hT hne)
        (fun S hS => (P_seq n).measurableSet_part hS)).symm]
    simp only [id_eq]
    have h_meas_union : MeasurableSet (⋃ S ∈ (P_seq n).parts, S) :=
      MeasurableSet.biUnion (P_seq n).parts.countable_toSet
        (fun S hS => (P_seq n).measurableSet_part hS)
    have h_ae := (P_seq n).ae_covers
    rw [ae_iff] at h_ae
    have h_null : μ ((⋃ S ∈ (P_seq n).parts, S)ᶜ) = 0 := by
      refine le_antisymm ?_ (zero_le)
      calc μ ((⋃ S ∈ (P_seq n).parts, S)ᶜ)
          ≤ μ {x | ¬∃ S ∈ (P_seq n).parts, x ∈ S} := by
            apply measure_mono; intro x hx
            simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hx
            exact fun ⟨S, hSP, hxS⟩ => hx S hSP hxS
        _ = 0 := h_ae
    rw [show μ (⋃ S ∈ (P_seq n).parts, S) = μ Set.univ from by
      rw [← measure_add_measure_compl h_meas_union, h_null, add_zero]]
    simp [measure_univ]
  have h_wlim_sum : ∑ i : Fin K, w_lim i = 1 := by
    exact tendsto_nhds_unique
      ((tendsto_finsetSum _ (fun i _ => h_pw_w i)).congr
        (fun n => (h_w_sum (ψ n)).symm ▸ rfl))
      tendsto_const_nhds
  obtain ⟨P_lim, ι_lim, hι_lim_mem, hι_lim_inj, hι_lim_surj, hP_lim_card, hι_lim_meas⟩ :=
    exists_partition_with_measures (μ := μ) w_lim h_wlim_nn h_wlim_sum
  have hι_lim_bij : ∀ S ∈ P_lim.parts, ∃! i : Fin K, ι_lim i = S := by
    intro S hS; obtain ⟨i, hi⟩ := hι_lim_surj S hS
    exact ⟨i, hi, fun j hj => hι_lim_inj (hj.trans hi.symm)⟩
  set ι_inv : ∀ S : Set α, S ∈ P_lim.parts → Fin K :=
    fun S hS => (hι_lim_bij S hS).choose with ι_inv_def
  have hι_inv_spec : ∀ S (hS : S ∈ P_lim.parts), ι_lim (ι_inv S hS) = S :=
    fun S hS => (hι_lim_bij S hS).choose_spec.1
  have hι_inv_lim : ∀ i, ι_inv (ι_lim i) (hι_lim_mem i) = i :=
    fun i => hι_lim_inj ((hι_inv_spec (ι_lim i) (hι_lim_mem i)))
  set c_U : Set α → Set α → ℝ := fun S T =>
    if hS : S ∈ P_lim.parts then if hT : T ∈ P_lim.parts then
      c_lim (ι_inv S hS) (ι_inv T hT) 0
    else 0 else 0
  set c_W : Set α → Set α → ℝ := fun S T =>
    if hS : S ∈ P_lim.parts then if hT : T ∈ P_lim.parts then
      c_lim (ι_inv S hS) (ι_inv T hT) 1
    else 0 else 0
  have h_cU_ι : ∀ i j, c_U (ι_lim i) (ι_lim j) = c_lim i j 0 := by
    intro i j; simp only [c_U, hι_lim_mem i, hι_lim_mem j, dif_pos, hι_inv_lim]
  have h_cW_ι : ∀ i j, c_W (ι_lim i) (ι_lim j) = c_lim i j 1 := by
    intro i j; simp only [c_W, hι_lim_mem i, hι_lim_mem j, dif_pos, hι_inv_lim]
  have h_cU_symm : ∀ S ∈ P_lim.parts, ∀ T ∈ P_lim.parts, c_U S T = c_U T S := by
    intro S hS T hT; simp only [c_U, hS, hT, dif_pos]
    set iS := ι_inv S hS; set iT := ι_inv T hT
    have h_symm_seq : ∀ n, coeff_seq (ψ n) iS iT 0 = coeff_seq (ψ n) iT iS 0 := by
      intro n; simp only [coeff_seq]
      by_cases h1 : (iS : ℕ) < (P_seq (ψ n)).parts.card ∧ (iT : ℕ) < (P_seq (ψ n)).parts.card
      · simp only [h1, ite_true]
        exact rectAverage_symm (U_seq (ψ n)) _ _
          ((P_seq (ψ n)).measurableSet_part (h_pad_mem (ψ n) iS h1.1))
          ((P_seq (ψ n)).measurableSet_part (h_pad_mem (ψ n) iT h1.2))
      · simp only [h1, ite_false]
        have h2 : ¬((iT : ℕ) < (P_seq (ψ n)).parts.card ∧ (iS : ℕ) < (P_seq (ψ n)).parts.card) :=
          fun h => h1 ⟨h.2, h.1⟩
        simp [h2]
    exact tendsto_nhds_unique (h_pw_c iS iT 0)
      ((h_pw_c iT iS 0).congr (fun n => (h_symm_seq n).symm))
  have h_cW_symm : ∀ S ∈ P_lim.parts, ∀ T ∈ P_lim.parts, c_W S T = c_W T S := by
    intro S hS T hT; simp only [c_W, hS, hT, dif_pos]
    set iS := ι_inv S hS; set iT := ι_inv T hT
    have h_symm_seq : ∀ n, coeff_seq (ψ n) iS iT 1 = coeff_seq (ψ n) iT iS 1 := by
      intro n; simp only [coeff_seq]
      by_cases h1 : (iS : ℕ) < (P_seq (ψ n)).parts.card ∧ (iT : ℕ) < (P_seq (ψ n)).parts.card
      · simp only [h1, ite_true]
        simp only [show ¬((1 : Fin 2) = 0) from by decide, ite_false]
        exact rectAverage_symm (W_seq (ψ n)) _ _
          ((P_seq (ψ n)).measurableSet_part (h_pad_mem (ψ n) iS h1.1))
          ((P_seq (ψ n)).measurableSet_part (h_pad_mem (ψ n) iT h1.2))
      · simp only [h1, ite_false]
        have h2 : ¬((iT : ℕ) < (P_seq (ψ n)).parts.card ∧ (iS : ℕ) < (P_seq (ψ n)).parts.card) :=
          fun h => h1 ⟨h.2, h.1⟩
        simp [h2]
    exact tendsto_nhds_unique (h_pw_c iS iT 1)
      ((h_pw_c iT iS 1).congr (fun n => (h_symm_seq n).symm))
  have h_cU_mem : ∀ S ∈ P_lim.parts, ∀ T ∈ P_lim.parts, c_U S T ∈ Set.Icc 0 1 := by
    intro S hS T hT; simp only [c_U, hS, hT, dif_pos]; exact h_clim_mem _ _ _
  have h_cW_mem : ∀ S ∈ P_lim.parts, ∀ T ∈ P_lim.parts, c_W S T ∈ Set.Icc 0 1 := by
    intro S hS T hT; simp only [c_W, hS, hT, dif_pos]; exact h_clim_mem _ _ _
  set V_U := mkStepGraphon P_lim c_U h_cU_symm h_cU_mem
  set V_W := mkStepGraphon P_lim c_W h_cW_symm h_cW_mem
  have h_bridge_U := homDensity_mkStepGraphon_eq_weightedHomSum
    P_lim c_U h_cU_symm h_cU_mem ι_lim hι_lim_mem hι_lim_surj hι_lim_inj
  have h_bridge_W := homDensity_mkStepGraphon_eq_weightedHomSum
    P_lim c_W h_cW_symm h_cW_mem ι_lim hι_lim_mem hι_lim_surj hι_lim_inj
  set w_lim' : Fin K → ℝ := fun i => (μ (ι_lim i)).toReal
  have h_w_eq : ∀ i, w_lim' i = w_lim i := fun i => hι_lim_meas i
  have h_whs_conv_U : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      Tendsto (fun m => weightedHomSum n F
        (fun i j => coeff_seq (ψ m) i j 0) (w_seq (ψ m))) atTop
        (nhds (weightedHomSum n F (fun i j => c_lim i j 0) w_lim)) := by
    intro n F _; apply tendsto_finsetSum _ (fun σ _ => ?_)
    apply Filter.Tendsto.mul
    · apply tendsto_finsetProd _ (fun v _ => ?_); exact h_pw_w (σ v)
    · apply tendsto_finsetProd _ (fun e _ => ?_); exact h_pw_c _ _ 0
  have h_whs_conv_W : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      Tendsto (fun m => weightedHomSum n F
        (fun i j => coeff_seq (ψ m) i j 1) (w_seq (ψ m))) atTop
        (nhds (weightedHomSum n F (fun i j => c_lim i j 1) w_lim)) := by
    intro n F _; apply tendsto_finsetSum _ (fun σ _ => ?_)
    apply Filter.Tendsto.mul
    · apply tendsto_finsetProd _ (fun v _ => ?_); exact h_pw_w (σ v)
    · apply tendsto_finsetProd _ (fun e _ => ?_); exact h_pw_c _ _ 1
  have h_stepify_bridge : ∀ m : ℕ, ∀ (V : Graphon α μ) (b : Fin 2),
      ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      n ≤ ψ m →
      (hb : (b = 0 → V = U_seq (ψ m)) ∧ (b = 1 → V = W_seq (ψ m))) →
      |homDensity F (stepify (P_seq (ψ m)) V) -
       weightedHomSum n F (fun i j => coeff_seq (ψ m) i j b) (w_seq (ψ m))| = 0 := by
    intro m V b n F _ _hn hb
    rw [abs_eq_zero, sub_eq_zero]
    set P := P_seq (ψ m)
    set k := P.parts.card with hk_def
    have hk_le : k ≤ K := hP_card (ψ m)
    -- Partition enumeration
    set ι_P : Fin k → Set α := fun i => (P.parts.equivFin.symm i : Set α)
    have hι_P : ∀ i, ι_P i ∈ P.parts := fun i => (P.parts.equivFin.symm i).prop
    have hι_P_surj : ∀ S ∈ P.parts, ∃ i, ι_P i = S :=
      fun S hS => ⟨P.parts.equivFin ⟨S, hS⟩, by simp [ι_P]⟩
    have hι_P_inj : Function.Injective ι_P :=
      fun _ _ hij => P.parts.equivFin.symm.injective (Subtype.val_injective hij)
    -- rectAverage symmetry and membership
    have hRA_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, rectAverage V S T = rectAverage V T S :=
      fun S hS T hT => rectAverage_symm V S T (P.measurableSet_part hS) (P.measurableSet_part hT)
    have hRA_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, rectAverage V S T ∈ Set.Icc 0 1 :=
      fun S hS T hT => rectAverage_mem_Icc V S T (P.measurableSet_part hS) (P.measurableSet_part hT)
    -- Bridge: homDensity = whs on Fin k
    have h_bridge : homDensity F (stepify P V) =
        weightedHomSum n F (fun i j => rectAverage V (ι_P i) (ι_P j))
          (fun i => (μ (ι_P i)).toReal) := by
      have h_aeq : (stepify P V).toAEEqFun =
          (mkStepGraphon P (rectAverage V) hRA_symm hRA_mem).toAEEqFun :=
        AEEqFun.mk_eq_mk.mpr Filter.EventuallyEq.rfl
      simp only [homDensity, h_aeq]
      exact homDensity_mkStepGraphon_eq_weightedHomSum P (rectAverage V)
        hRA_symm hRA_mem ι_P hι_P hι_P_surj hι_P_inj n F
    rw [h_bridge]
    -- Zero-weight vanishing: whs Fin k = whs Fin K
    -- Embedding Fin k ↪ Fin K
    set embed : Fin k → Fin K := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hk_le⟩
    have hembed_inj : Function.Injective embed :=
      fun _ _ h => Fin.ext (Fin.mk.inj_iff.mp h)
    -- pad(embed i) = ι_P i for active indices
    have h_pad_eq : ∀ i : Fin k, pad (ψ m) (embed i) = ι_P i := by
      intro i; show pad (ψ m) ⟨i.val, _⟩ = ι_P i
      simp only [pad]; rw [dif_pos i.isLt]
    -- Weight and coefficient matching
    have h_w_eq : ∀ i : Fin k, w_seq (ψ m) (embed i) = (μ (ι_P i)).toReal := by
      intro i; show (if (embed i : ℕ) < k then _ else _) = _
      rw [if_pos i.isLt, h_pad_eq]
    have h_c_eq : ∀ i j : Fin k,
        coeff_seq (ψ m) (embed i) (embed j) b = rectAverage V (ι_P i) (ι_P j) := by
      intro i j
      show (if (embed i : ℕ) < k ∧ (embed j : ℕ) < k then _ else _) = _
      rw [if_pos ⟨i.isLt, j.isLt⟩, h_pad_eq, h_pad_eq]
      fin_cases b
      · simp only [ite_true]; exact (hb.1 rfl).symm ▸ rfl
      · simp only [show ¬((1 : Fin 2) = 0) from by decide, ite_false]; exact (hb.2 rfl).symm ▸ rfl
    -- Zero-weight vanishing and reindexing
    simp only [weightedHomSum]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun σ : Fin n → Fin K => ∀ v, (σ v : ℕ) < k)]
    -- Bad terms vanish (some σ(v) ≥ k means w_seq = 0)
    have h_bad : ∑ σ ∈ Finset.univ.filter (fun σ : Fin n → Fin K => ¬∀ v, (σ v : ℕ) < k),
        (∏ v, w_seq (ψ m) (σ v)) * ∏ e ∈ F.edgeFinset,
          coeff_seq (ψ m) (σ (Quot.out e).1) (σ (Quot.out e).2) b = 0 := by
      apply Finset.sum_eq_zero; intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at hσ
      obtain ⟨v, hv⟩ := hσ
      apply mul_eq_zero_of_left; apply Finset.prod_eq_zero (Finset.mem_univ v)
      show (if (σ v : ℕ) < k then _ else _) = _
      rw [if_neg hv]
    rw [h_bad, add_zero]
    -- Good terms biject with Fin n → Fin k
    have h_reindex : ∑ τ : Fin n → Fin k,
        (∏ v : Fin n, (μ (ι_P (τ v))).toReal) *
        ∏ e ∈ F.edgeFinset, rectAverage V (ι_P (τ (Quot.out e).1)) (ι_P (τ (Quot.out e).2)) =
        ∑ σ ∈ Finset.univ.filter (fun σ : Fin n → Fin K => ∀ v, (σ v : ℕ) < k),
        (∏ v : Fin n, w_seq (ψ m) (σ v)) *
        ∏ e ∈ F.edgeFinset, coeff_seq (ψ m) (σ (Quot.out e).1) (σ (Quot.out e).2) b := by
      apply Finset.sum_nbij (fun (τ : Fin n → Fin k) v => embed (τ v))
      · intro τ _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v => (τ v).isLt⟩
      · intro τ₁ _ τ₂ _ h; exact funext fun v => hembed_inj (congr_fun h v)
      · intro σ hσ
        have hσ' := (Finset.mem_filter.mp hσ).2
        exact ⟨fun v => ⟨(σ v).val, hσ' v⟩, Finset.mem_univ _, funext (fun v => Fin.ext rfl)⟩
      · intro τ _; congr 1
        · exact Finset.prod_congr rfl (fun v _ => (h_w_eq (τ v)).symm)
        · exact Finset.prod_congr rfl (fun e _ => (h_c_eq _ _).symm)
    exact h_reindex
  have h_hom_eq : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      homDensity F V_U = homDensity F V_W := by
    intro n F _
    rw [h_bridge_U n F, h_bridge_W n F]; simp only [h_cU_ι, h_cW_ι]
    conv_lhs => rw [show w_lim' = w_lim from funext h_w_eq]
    conv_rhs => rw [show w_lim' = w_lim from funext h_w_eq]
    have h_bound : ∀ᶠ m in atTop, |weightedHomSum n F (fun i j => coeff_seq (ψ m) i j 0) (w_seq (ψ m)) -
        weightedHomSum n F (fun i j => coeff_seq (ψ m) i j 1) (w_seq (ψ m))| ≤
        1 / (↑(ψ m) + 1 : ℝ) := by
      rw [Filter.eventually_atTop]
      refine ⟨n, fun m hm => ?_⟩
      have h_ψm_ge_n : n ≤ ψ m := le_trans hm hψ.le_apply
      -- Use h_stepify_bridge to convert whs to homDensity
      have h_eq_U := h_stepify_bridge m (U_seq (ψ m)) 0 n F h_ψm_ge_n ⟨fun _ => rfl, fun h => absurd h (by decide)⟩
      have h_eq_W := h_stepify_bridge m (W_seq (ψ m)) 1 n F h_ψm_ge_n ⟨fun h => absurd h (by decide), fun _ => rfl⟩
      rw [abs_eq_zero] at h_eq_U h_eq_W
      rw [show weightedHomSum n F (fun i j => coeff_seq (ψ m) i j 0) (w_seq (ψ m)) =
        homDensity F (stepify (P_seq (ψ m)) (U_seq (ψ m))) from (sub_eq_zero.mp h_eq_U).symm,
        show weightedHomSum n F (fun i j => coeff_seq (ψ m) i j 1) (w_seq (ψ m)) =
        homDensity F (stepify (P_seq (ψ m)) (W_seq (ψ m))) from (sub_eq_zero.mp h_eq_W).symm]
      -- Embed F : Fin n → Fin (ψ m) via Fin.castLEEmb
      rw [← homDensity_map_embedding F (Fin.castLEEmb h_ψm_ge_n) (stepify (P_seq (ψ m)) (U_seq (ψ m))),
          ← homDensity_map_embedding F (Fin.castLEEmb h_ψm_ge_n) (stepify (P_seq (ψ m)) (W_seq (ψ m)))]
      set F' := F.map (Fin.castLEEmb h_ψm_ge_n)
      have := h_close (ψ m) (F := F')
      rw [homDensity_congr_decRel F' _ _ (stepify (P_seq (ψ m)) (U_seq (ψ m))),
          homDensity_congr_decRel F' _ _ (stepify (P_seq (ψ m)) (W_seq (ψ m)))] at this
      exact le_of_lt this
    have h_inv_tends : Tendsto (fun m => 1 / (↑(ψ m) + 1 : ℝ)) atTop (nhds 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      exact (tendsto_natCast_atTop_atTop.comp hψ.tendsto_atTop).atTop_add tendsto_const_nhds
    have h_abs_diff_tends : Tendsto (fun m => |weightedHomSum n F
        (fun i j => coeff_seq (ψ m) i j 0) (w_seq (ψ m)) -
        weightedHomSum n F (fun i j => coeff_seq (ψ m) i j 1) (w_seq (ψ m))|) atTop (nhds 0) :=
      squeeze_zero' (Eventually.of_forall (fun m => abs_nonneg _)) h_bound h_inv_tends
    have h_diff_tends : Tendsto (fun m => weightedHomSum n F
        (fun i j => coeff_seq (ψ m) i j 0) (w_seq (ψ m)) -
        weightedHomSum n F (fun i j => coeff_seq (ψ m) i j 1) (w_seq (ψ m))) atTop (nhds 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr
        (by simpa [Real.norm_eq_abs] using h_abs_diff_tends)
    apply tendsto_nhds_unique (h_whs_conv_U n F)
    have : Tendsto (fun m =>
        (weightedHomSum n F (fun i j => coeff_seq (ψ m) i j 0) (w_seq (ψ m)) -
         weightedHomSum n F (fun i j => coeff_seq (ψ m) i j 1) (w_seq (ψ m))) +
        weightedHomSum n F (fun i j => coeff_seq (ψ m) i j 1) (w_seq (ψ m))) atTop
        (nhds (0 + weightedHomSum n F (fun i j => c_lim i j 1) w_lim)) :=
      h_diff_tends.add (h_whs_conv_W n F)
    simp only [sub_add_cancel, zero_add] at this
    exact this
  have h_cd_lim : cutDistance V_U V_W = 0 :=
    cutDistance_zero_of_step_homDensity_eq P_lim c_U c_W h_cU_symm h_cU_mem h_cW_symm h_cW_mem
      h_hom_eq
  have hε4 : ε / 4 > 0 := by linarith
  have h_event_all_c : ∀ b, ∀ᶠ m in atTop, ∀ i j,
      |coeff_seq (ψ m) i j b - c_lim i j b| < ε / 8 := by
    intro b; rw [Filter.eventually_atTop]
    have hε8 : ε / 8 > 0 := by linarith
    have : ∀ i j, ∃ N, ∀ m ≥ N,
        |coeff_seq (ψ m) i j b - c_lim i j b| < ε / 8 := by
      intro i j
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (h_pw_c i j b) (ε / 8) hε8
      exact ⟨N, fun m hm => by have := hN m hm; rw [Real.dist_eq] at this; exact this⟩
    choose N_ij hN_ij using this
    exact ⟨(Finset.univ : Finset (Fin K × Fin K)).sup (fun p => N_ij p.1 p.2),
      fun m hm i j => hN_ij i j m (le_trans
        (Finset.le_sup (f := fun p => N_ij p.1 p.2) (Finset.mem_univ (i, j))) hm)⟩
  have h_event_all_w : ∀ᶠ m in atTop, ∀ i,
      |w_seq (ψ m) i - w_lim i| < ε / (8 * (↑K + 1)) := by
    rw [Filter.eventually_atTop]
    have hε8K : ε / (8 * (↑K + 1)) > 0 := by positivity
    have : ∀ i, ∃ N, ∀ m ≥ N,
        |w_seq (ψ m) i - w_lim i| < ε / (8 * (↑K + 1)) := by
      intro i
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (h_pw_w i) (ε / (8 * (↑K + 1))) hε8K
      exact ⟨N, fun m hm => by have := hN m hm; rw [Real.dist_eq] at this; exact this⟩
    choose N_i hN_i using this
    exact ⟨(Finset.univ : Finset (Fin K)).sup N_i,
      fun m hm i => hN_i i m (le_trans (Finset.le_sup (Finset.mem_univ i)) hm)⟩
  obtain ⟨m, ⟨hm_c0, hm_c1⟩, hm_w⟩ :=
    ((h_event_all_c 0).and (h_event_all_c 1)).and h_event_all_w |>.exists
  set c_Um : Set α → Set α → ℝ := fun S T =>
    if hS : S ∈ P_lim.parts then if hT : T ∈ P_lim.parts then
      coeff_seq (ψ m) (ι_inv S hS) (ι_inv T hT) 0
    else 0 else 0
  set c_Wm : Set α → Set α → ℝ := fun S T =>
    if hS : S ∈ P_lim.parts then if hT : T ∈ P_lim.parts then
      coeff_seq (ψ m) (ι_inv S hS) (ι_inv T hT) 1
    else 0 else 0
  have h_cUm_ι : ∀ i j, c_Um (ι_lim i) (ι_lim j) = coeff_seq (ψ m) i j 0 := by
    intro i j; simp only [c_Um, hι_lim_mem i, hι_lim_mem j, dif_pos, hι_inv_lim]
  have h_cWm_ι : ∀ i j, c_Wm (ι_lim i) (ι_lim j) = coeff_seq (ψ m) i j 1 := by
    intro i j; simp only [c_Wm, hι_lim_mem i, hι_lim_mem j, dif_pos, hι_inv_lim]
  have h_cUm_symm : ∀ S ∈ P_lim.parts, ∀ T ∈ P_lim.parts, c_Um S T = c_Um T S := by
    intro S hS T hT; simp only [c_Um, hS, hT, dif_pos]; simp only [coeff_seq]
    set iS := ι_inv S hS; set iT := ι_inv T hT
    by_cases h1 : (iS : ℕ) < (P_seq (ψ m)).parts.card ∧ (iT : ℕ) < (P_seq (ψ m)).parts.card
    · simp only [h1, ite_true]
      exact rectAverage_symm (U_seq (ψ m)) _ _
        ((P_seq (ψ m)).measurableSet_part (h_pad_mem (ψ m) iS h1.1))
        ((P_seq (ψ m)).measurableSet_part (h_pad_mem (ψ m) iT h1.2))
    · simp only [h1, ite_false]
      have h2 : ¬((iT : ℕ) < (P_seq (ψ m)).parts.card ∧ (iS : ℕ) < (P_seq (ψ m)).parts.card) :=
        fun h => h1 ⟨h.2, h.1⟩
      simp [h2]
  have h_cWm_symm : ∀ S ∈ P_lim.parts, ∀ T ∈ P_lim.parts, c_Wm S T = c_Wm T S := by
    intro S hS T hT; simp only [c_Wm, hS, hT, dif_pos]; simp only [coeff_seq]
    set iS := ι_inv S hS; set iT := ι_inv T hT
    by_cases h1 : (iS : ℕ) < (P_seq (ψ m)).parts.card ∧ (iT : ℕ) < (P_seq (ψ m)).parts.card
    · simp only [h1, ite_true]
      simp only [show ¬((1 : Fin 2) = 0) from by decide, ite_false]
      exact rectAverage_symm (W_seq (ψ m)) _ _
        ((P_seq (ψ m)).measurableSet_part (h_pad_mem (ψ m) iS h1.1))
        ((P_seq (ψ m)).measurableSet_part (h_pad_mem (ψ m) iT h1.2))
    · simp only [h1, ite_false]
      have h2 : ¬((iT : ℕ) < (P_seq (ψ m)).parts.card ∧ (iS : ℕ) < (P_seq (ψ m)).parts.card) :=
        fun h => h1 ⟨h.2, h.1⟩
      simp [h2]
  have h_cUm_mem : ∀ S ∈ P_lim.parts, ∀ T ∈ P_lim.parts, c_Um S T ∈ Set.Icc 0 1 := by
    intro S hS T hT; simp only [c_Um, hS, hT, dif_pos]; exact h_c_mem _ _ _ _
  have h_cWm_mem : ∀ S ∈ P_lim.parts, ∀ T ∈ P_lim.parts, c_Wm S T ∈ Set.Icc 0 1 := by
    intro S hS T hT; simp only [c_Wm, hS, hT, dif_pos]; exact h_c_mem _ _ _ _
  set G_Um := mkStepGraphon P_lim c_Um h_cUm_symm h_cUm_mem
  set G_Wm := mkStepGraphon P_lim c_Wm h_cWm_symm h_cWm_mem
  have h_cn_U : cutNormDiff G_Um V_U ≤ ε / 8 := by
    apply cutNormDiff_mkStepGraphon_le P_lim c_Um c_U
      h_cUm_symm h_cUm_mem h_cU_symm h_cU_mem (ε / 8)
    intro S hS T hT
    obtain ⟨i, hi⟩ := hι_lim_surj S hS; obtain ⟨j, hj⟩ := hι_lim_surj T hT
    rw [← hi, ← hj, h_cUm_ι, h_cU_ι]; exact le_of_lt (hm_c0 i j)
  have h_cn_W : cutNormDiff G_Wm V_W ≤ ε / 8 := by
    apply cutNormDiff_mkStepGraphon_le P_lim c_Wm c_W
      h_cWm_symm h_cWm_mem h_cW_symm h_cW_mem (ε / 8)
    intro S hS T hT
    obtain ⟨i, hi⟩ := hι_lim_surj S hS; obtain ⟨j, hj⟩ := hι_lim_surj T hT
    rw [← hi, ← hj, h_cWm_ι, h_cW_ι]; exact le_of_lt (hm_c1 i j)
  have h_weight_bound : 2 * ∑ i : Fin K, |w_seq (ψ m) i - w_lim i| < ε / 4 := by
    have h_le : ∑ i : Fin K, |w_seq (ψ m) i - w_lim i| ≤
        (Finset.univ : Finset (Fin K)).card • (ε / (8 * (↑K + 1))) :=
      Finset.sum_le_card_nsmul _ _ _ (fun i _ => le_of_lt (hm_w i))
    rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h_le
    have hK1 : (0 : ℝ) < ↑K + 1 := by positivity
    calc 2 * ∑ i : Fin K, |w_seq (ψ m) i - w_lim i|
        ≤ 2 * (↑K * (ε / (8 * (↑K + 1)))) := by linarith
      _ < 2 * ((↑K + 1) * (ε / (8 * (↑K + 1)))) := by
          apply mul_lt_mul_of_pos_left _ two_pos
          exact mul_lt_mul_of_pos_right (by linarith : (↑K : ℝ) < ↑K + 1)
            (div_pos hε (by positivity))
      _ = ε / 4 := by field_simp; ring
  -- **Sorry traces to**: `cutDistance_step_weight_le` → `exists_common_extension` (Rokhlin).
  -- Proof sketch: triangle through P_mid (built via exists_partition_with_measures with
  -- weights w_seq(ψm)). Part 1: cutDistance(stepify, G_mid) = 0 via cell alignment (Rokhlin).
  -- Part 2: cutDistance(G_mid, G_Um) ≤ 2*∑|w_seq-w_lim| < ε/4 by h_weight_bound.
  have h_cd_cross_U : cutDistance (stepify (P_seq (ψ m)) (U_seq (ψ m))) G_Um < ε / 4 := by
    -- Apply the cross-partition weight lemma
    have h_le := cutDistance_cross_partition_weight_le
      (P_seq (ψ m)) (U_seq (ψ m)) (hP_card (ψ m))
      P_lim c_Um h_cUm_symm h_cUm_mem
      ι_lim hι_lim_mem hι_lim_inj hι_lim_surj
      (pad (ψ m)) (h_pad_mem (ψ m)) (h_pad_inj (ψ m)) (h_pad_surj (ψ m))
      (w_seq (ψ m)) (fun i => rfl) (fun i => (h_w_mem (ψ m) i).1) (h_w_sum (ψ m))
      (fun i j => by
        rw [h_cUm_ι]; show coeff_seq (ψ m) i j 0 = _
        simp only [coeff_seq_def, show (0 : Fin 2) = 0 from rfl, ite_true])
    calc cutDistance (stepify (P_seq (ψ m)) (U_seq (ψ m))) G_Um
        ≤ 2 * ∑ i : Fin K, |w_seq (ψ m) i - (μ (ι_lim i)).toReal| := h_le
      _ = 2 * ∑ i : Fin K, |w_seq (ψ m) i - w_lim i| := by
          congr 1; congr 1; ext i; rw [hι_lim_meas i]
      _ < ε / 4 := h_weight_bound
  have h_cd_cross_W : cutDistance (stepify (P_seq (ψ m)) (W_seq (ψ m))) G_Wm < ε / 4 := by
    -- Apply the cross-partition weight lemma
    have h_le := cutDistance_cross_partition_weight_le
      (P_seq (ψ m)) (W_seq (ψ m)) (hP_card (ψ m))
      P_lim c_Wm h_cWm_symm h_cWm_mem
      ι_lim hι_lim_mem hι_lim_inj hι_lim_surj
      (pad (ψ m)) (h_pad_mem (ψ m)) (h_pad_inj (ψ m)) (h_pad_surj (ψ m))
      (w_seq (ψ m)) (fun i => rfl) (fun i => (h_w_mem (ψ m) i).1) (h_w_sum (ψ m))
      (fun i j => by
        rw [h_cWm_ι]; show coeff_seq (ψ m) i j 1 = _
        simp only [coeff_seq_def, show ¬((1 : Fin 2) = 0) from by decide, ite_false])
    calc cutDistance (stepify (P_seq (ψ m)) (W_seq (ψ m))) G_Wm
        ≤ 2 * ∑ i : Fin K, |w_seq (ψ m) i - (μ (ι_lim i)).toReal| := h_le
      _ = 2 * ∑ i : Fin K, |w_seq (ψ m) i - w_lim i| := by
          congr 1; congr 1; ext i; rw [hι_lim_meas i]
      _ < ε / 4 := h_weight_bound
  have h_cd_coeff_U : cutDistance G_Um V_U ≤ ε / 8 :=
    le_trans (cutDistance_le_cutNormDiff _ _) h_cn_U
  have h_cd_coeff_W : cutDistance G_Wm V_W ≤ ε / 8 :=
    le_trans (cutDistance_le_cutNormDiff _ _) h_cn_W
  have h_cd_U : cutDistance (stepify (P_seq (ψ m)) (U_seq (ψ m))) V_U < ε / 2 :=
    calc cutDistance (stepify (P_seq (ψ m)) (U_seq (ψ m))) V_U
        ≤ cutDistance (stepify (P_seq (ψ m)) (U_seq (ψ m))) G_Um +
          cutDistance G_Um V_U := cutDistance_triangle _ _ _
      _ < ε / 4 + ε / 8 := by linarith [h_cd_cross_U, h_cd_coeff_U]
      _ < ε / 2 := by linarith
  have h_cd_W : cutDistance (stepify (P_seq (ψ m)) (W_seq (ψ m))) V_W < ε / 2 :=
    calc cutDistance (stepify (P_seq (ψ m)) (W_seq (ψ m))) V_W
        ≤ cutDistance (stepify (P_seq (ψ m)) (W_seq (ψ m))) G_Wm +
          cutDistance G_Wm V_W := cutDistance_triangle _ _ _
      _ < ε / 4 + ε / 8 := by linarith [h_cd_cross_W, h_cd_coeff_W]
      _ < ε / 2 := by linarith
  have h_tri : cutDistance (stepify (P_seq (ψ m)) (U_seq (ψ m)))
      (stepify (P_seq (ψ m)) (W_seq (ψ m))) ≤
      cutDistance (stepify (P_seq (ψ m)) (U_seq (ψ m))) V_U +
      cutDistance V_U V_W +
      cutDistance V_W (stepify (P_seq (ψ m)) (W_seq (ψ m))) := by
    calc cutDistance (stepify (P_seq (ψ m)) (U_seq (ψ m)))
          (stepify (P_seq (ψ m)) (W_seq (ψ m)))
        ≤ cutDistance (stepify (P_seq (ψ m)) (U_seq (ψ m))) V_U +
          cutDistance V_U (stepify (P_seq (ψ m)) (W_seq (ψ m))) :=
          cutDistance_triangle _ _ _
      _ ≤ cutDistance (stepify (P_seq (ψ m)) (U_seq (ψ m))) V_U +
          (cutDistance V_U V_W + cutDistance V_W (stepify (P_seq (ψ m)) (W_seq (ψ m)))) := by
          linarith [cutDistance_triangle V_U V_W (stepify (P_seq (ψ m)) (W_seq (ψ m)))]
      _ = _ := by ring
  rw [h_cd_lim, cutDistance_symm V_W (stepify (P_seq (ψ m)) (W_seq (ψ m)))] at h_tri
  linarith [h_far (ψ m), h_cd_U, h_cd_W]

/-- **Algebraic determination**: two graphons with equal homomorphism densities
for all finite graphs have cut distance zero (are weakly isomorphic).

The proof combines `simultaneous_regularity` (which gives a cardinality bound
`K = 4 ^ (2 * (⌈1/δ²⌉ + 1))`) with `step_quantitative_icl_bounded K (ε/3)`
(uniform compactness over all partitions with ≤ K parts) and the counting lemma.
For any ε > 0:

1. Apply `step_quantitative_icl_bounded K (ε/3)` to get (δ_step, m) uniform over
   all partitions with ≤ K parts
2. Choose δ so that (a) δ ≤ ε/3 and (b) the counting lemma converts cutNormDiff ≤ δ
   into hom density differences < δ_step for all graphs on ≤ m vertices
3. Apply `simultaneous_regularity U W δ` to get partition P with P.parts.card ≤ K,
   cutNormDiff U (stepify P U) ≤ δ, cutNormDiff W (stepify P W) ≤ δ
4. By the counting lemma (step 2b), step graphons on P satisfy the δ_step condition,
   so `step_quantitative_icl_bounded` gives cutDistance(stepify P U, stepify P W) < ε/3
5. Triangle inequality: cutDistance(U, W) ≤ cutNormDiff(U, stepify P U) +
   cutDistance(stepify P U, stepify P W) + cutNormDiff(W, stepify P W) < ε

The key insight is that `step_quantitative_icl_bounded` eliminates the circular
dependency: δ_step and m depend only on K and ε, not on the specific partition P.
The cardinality bound K from `simultaneous_regularity` depends only on the
regularity parameter δ, which is chosen AFTER obtaining (δ_step, m).

**Sorry traces to**: `step_quantitative_icl_bounded` (compactness over bounded partitions)
→ `step_quantitative_icl` → `cutDistance_zero_of_step_homDensity_eq`
→ `matrix_quotient_of_weightedHomSum_eq` (algebraic core) +
`MeasurePreserving.exists_common_extension` (Rokhlin). -/
theorem cutDistance_zero_of_homDensity_eq [StandardBorelSpace α] [NoAtoms μ]
    (U W : Graphon α μ)
    (h : ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
         homDensity F U = homDensity F W) :
    cutDistance U W = 0 := by
  -- The proof requires a uniform version of step_quantitative_icl over all partitions
  -- with bounded card, combined with simultaneous_regularity and the counting lemma.
  -- This traces to matrix_quotient_of_weightedHomSum_eq (algebraic core) +
  -- MeasurePreserving.exists_common_extension (Rokhlin) through
  -- step_quantitative_icl → cutDistance_zero_of_step_homDensity_eq.
  sorry

/-- The inverse counting lemma: similar homomorphism densities imply
    small cut distance.

For any ε > 0, there exists δ > 0 and a finite set of graphs F₁,...,Fₖ
such that if |t(Fᵢ, U) - t(Fᵢ, W)| < δ for all i, then δ□(U, W) < ε. -/
@[blueprint "thm:inverse-counting"
  (title := /-- Inverse counting lemma -/)]
theorem cutDistance_le_of_homDensity_close [StandardBorelSpace α] [NoAtoms μ] (ε : ℝ) (hε : ε > 0) :
    ∃ (δ : ℝ) (_ : δ > 0) (k : ℕ),
    ∀ (U W : Graphon α μ),
      (∀ (F : SimpleGraph (Fin k)) [DecidableRel F.Adj], |homDensity F U - homDensity F W| < δ) →
      cutDistance U W < ε := by
  -- Proof by contradiction + compactness.
  -- If false, for each n, ∃ U_n W_n with Fin-n hom densities within 1/(n+1) but d ≥ ε.
  -- Extract convergent subsequences; limits have equal hom densities but d ≥ ε, contradiction.
  by_contra h_neg
  push Not at h_neg
  have h_seq : ∀ n : ℕ, ∃ (U W : Graphon α μ),
      (∀ (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
        |homDensity F U - homDensity F W| < 1 / (↑n + 1 : ℝ)) ∧
      cutDistance U W ≥ ε :=
    fun n => h_neg (1 / (↑n + 1 : ℝ)) (by positivity) n
  choose U_seq W_seq h_close h_far using h_seq
  obtain ⟨U_lim, φ₁, hφ₁_mono, hφ₁_conv⟩ := compact U_seq
  obtain ⟨W_lim, φ₂, hφ₂_mono, hφ₂_conv⟩ := compact (W_seq ∘ φ₁)
  set φ := φ₁ ∘ φ₂ with hφ_def
  have hφ_mono : StrictMono φ := hφ₁_mono.comp hφ₂_mono
  have hU_conv : ∀ ε' > 0, ∃ N, ∀ n ≥ N, cutDistance (U_seq (φ n)) U_lim < ε' := by
    intro ε' hε'; obtain ⟨N, hN⟩ := hφ₁_conv ε' hε'
    exact ⟨N, fun n hn => hN (φ₂ n) (le_trans hn (hφ₂_mono.id_le n))⟩
  have hW_conv : ∀ ε' > 0, ∃ N, ∀ n ≥ N, cutDistance (W_seq (φ n)) W_lim < ε' :=
    fun ε' hε' => hφ₂_conv ε' hε'
  have h_lim_far : cutDistance U_lim W_lim ≥ ε := by
    by_contra h_small
    push Not at h_small
    set δ₀ := (ε - cutDistance U_lim W_lim) / 3 with hδ₀_def
    have hδ₀_pos : δ₀ > 0 := by linarith [cutDistance_nonneg U_lim W_lim]
    obtain ⟨N₁, hN₁⟩ := hU_conv δ₀ hδ₀_pos
    obtain ⟨N₂, hN₂⟩ := hW_conv δ₀ hδ₀_pos
    set n := max N₁ N₂
    have := h_far (φ n)
    have := cutDistance_triangle (U_seq (φ n)) U_lim (W_seq (φ n))
    have := cutDistance_triangle U_lim W_lim (W_seq (φ n))
    have := cutDistance_symm W_lim (W_seq (φ n))
    have := hN₁ n (le_max_left _ _)
    have := hN₂ n (le_max_right _ _)
    linarith
  -- Show all Fin-k hom densities of U_lim and W_lim agree, giving d = 0.
  have h_eq_hom : ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
      homDensity F U_lim = homDensity F W_lim := by
    intro k F _
    by_contra h_ne
    set ε' := |homDensity F U_lim - homDensity F W_lim| / 4 with hε'_def
    have hε'_pos : ε' > 0 := div_pos (abs_pos.mpr (sub_ne_zero.mpr h_ne)) four_pos
    by_cases hF_card : F.edgeFinset.card = 0
    · have h_empty : F.edgeFinset = ∅ := Finset.card_eq_zero.mp hF_card
      apply h_ne
      simp [homDensity_eq_integral, homDensityIntegrand, h_empty]
    · have hcard_pos : (0 : ℝ) < F.edgeFinset.card :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero hF_card)
      obtain ⟨N_U, hN_U⟩ := hU_conv (ε' / F.edgeFinset.card) (div_pos hε'_pos hcard_pos)
      obtain ⟨N_W, hN_W⟩ := hW_conv (ε' / F.edgeFinset.card) (div_pos hε'_pos hcard_pos)
      obtain ⟨N_arch, hN_arch⟩ : ∃ N : ℕ, 1 / (↑N + 1 : ℝ) < ε' := by
        obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε')
        refine ⟨m, ?_⟩
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ↑m + 1)]
        calc 1 = ε' * (1 / ε') := by field_simp
          _ < ε' * ↑m := by exact mul_lt_mul_of_pos_left hm hε'_pos
          _ ≤ ε' * (↑m + 1) := by linarith
      set n := max (max N_U N_W) (max N_arch k) with hn_def
      have hn_U : n ≥ N_U := le_trans (le_max_left _ _) (le_max_left _ _)
      have hn_W : n ≥ N_W := le_trans (le_max_right _ _) (le_max_left _ _)
      have hn_arch : n ≥ N_arch := le_trans (le_max_left _ _) (le_max_right _ _)
      have hn_k : n ≥ k := le_trans (le_max_right _ _) (le_max_right _ _)
      have hφn_ge_n : φ n ≥ n := hφ_mono.id_le n
      have hφn_ge_k : k ≤ φ n := le_trans hn_k hφn_ge_n
      have hU_bound : |homDensity F U_lim - homDensity F (U_seq (φ n))| < ε' := by
        calc |homDensity F U_lim - homDensity F (U_seq (φ n))|
            = |homDensity F (U_seq (φ n)) - homDensity F U_lim| := abs_sub_comm _ _
          _ ≤ F.edgeFinset.card * cutDistance (U_seq (φ n)) U_lim :=
              homDensity_sub_le_of_cutDistance F (U_seq (φ n)) U_lim
          _ < F.edgeFinset.card * (ε' / F.edgeFinset.card) :=
              mul_lt_mul_of_pos_left (hN_U n hn_U) hcard_pos
          _ = ε' := mul_div_cancel₀ ε' (ne_of_gt hcard_pos)
      have hW_bound : |homDensity F (W_seq (φ n)) - homDensity F W_lim| < ε' := by
        calc |homDensity F (W_seq (φ n)) - homDensity F W_lim|
            ≤ F.edgeFinset.card * cutDistance (W_seq (φ n)) W_lim :=
              homDensity_sub_le_of_cutDistance F (W_seq (φ n)) W_lim
          _ < F.edgeFinset.card * (ε' / F.edgeFinset.card) :=
              mul_lt_mul_of_pos_left (hN_W n hn_W) hcard_pos
          _ = ε' := mul_div_cancel₀ ε' (ne_of_gt hcard_pos)
      have hclose_bound : |homDensity F (U_seq (φ n)) - homDensity F (W_seq (φ n))| < ε' := by
        have h_mapped : |homDensity F (U_seq (φ n)) - homDensity F (W_seq (φ n))| <
            1 / (↑(φ n) + 1 : ℝ) := by
          rw [← homDensity_map_embedding F (Fin.castLEEmb hφn_ge_k) (U_seq (φ n)),
              ← homDensity_map_embedding F (Fin.castLEEmb hφn_ge_k) (W_seq (φ n))]
          set F' := F.map (Fin.castLEEmb hφn_ge_k)
          have := h_close (φ n) (F := F')
          rwa [homDensity_congr_decRel F' _ _ (U_seq (φ n)),
               homDensity_congr_decRel F' _ _ (W_seq (φ n))]
        calc |homDensity F (U_seq (φ n)) - homDensity F (W_seq (φ n))|
            < 1 / (↑(φ n) + 1 : ℝ) := h_mapped
          _ ≤ 1 / (↑n + 1 : ℝ) := by
              apply div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 1) (by positivity)
              exact_mod_cast Nat.add_le_add_right hφn_ge_n 1
          _ ≤ 1 / (↑N_arch + 1 : ℝ) := by
              apply div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 1) (by positivity)
              exact_mod_cast Nat.add_le_add_right hn_arch 1
          _ < ε' := hN_arch
      have h_triangle : |homDensity F U_lim - homDensity F W_lim| < 3 * ε' := by
        have h_split : homDensity F U_lim - homDensity F W_lim =
            (homDensity F U_lim - homDensity F (U_seq (φ n))) +
            (homDensity F (U_seq (φ n)) - homDensity F (W_seq (φ n))) +
            (homDensity F (W_seq (φ n)) - homDensity F W_lim) := by ring
        rw [h_split]
        calc |_ + _ + _|
            ≤ |homDensity F U_lim - homDensity F (U_seq (φ n)) +
              (homDensity F (U_seq (φ n)) - homDensity F (W_seq (φ n)))| +
              |homDensity F (W_seq (φ n)) - homDensity F W_lim| := abs_add_le _ _
          _ ≤ (|homDensity F U_lim - homDensity F (U_seq (φ n))| +
              |homDensity F (U_seq (φ n)) - homDensity F (W_seq (φ n))|) +
              |homDensity F (W_seq (φ n)) - homDensity F W_lim| :=
              add_le_add (abs_add_le _ _) le_rfl
          _ < (ε' + ε') + ε' :=
              add_lt_add (add_lt_add hU_bound hclose_bound) hW_bound
          _ = 3 * ε' := by ring
      have h_eq_4ε' : |homDensity F U_lim - homDensity F W_lim| = 4 * ε' := by
        simp [hε'_def, mul_div_cancel₀]
      linarith
  have h_zero : cutDistance U_lim W_lim = 0 := cutDistance_zero_of_homDensity_eq U_lim W_lim h_eq_hom
  linarith

/-- Corollary: a sequence converges in cut distance iff all homomorphism
    densities converge.

This is the fundamental characterization of graph limit convergence. -/
@[blueprint "thm:convergence-equiv"
  (title := /-- Convergence equivalence -/)]
theorem cutDistance_tendsto_iff_homDensity_tendsto [StandardBorelSpace α] [NoAtoms μ]
    (W : ℕ → Graphon α μ) (V : Graphon α μ) :
    (∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W n) V < ε) ↔
    (∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
     ∀ ε > 0, ∃ N, ∀ n ≥ N, |homDensity F (W n) - homDensity F V| < ε) := by
  constructor
  · -- Forward: counting lemma
    intro hconv k F _ ε hε
    by_cases hF : F.edgeFinset.card = 0
    · use 0
      intro n _
      have h_empty : F.edgeFinset = ∅ := Finset.card_eq_zero.mp hF
      simp only [homDensity_eq_integral, homDensityIntegrand, h_empty, Finset.prod_empty,
          sub_self, abs_zero, hε]
    · have hcard_pos : (0 : ℝ) < F.edgeFinset.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hF)
      obtain ⟨N, hN⟩ := hconv (ε / F.edgeFinset.card) (div_pos hε hcard_pos)
      use N
      intro n hn
      calc |homDensity F (W n) - homDensity F V|
          ≤ F.edgeFinset.card * cutDistance (W n) V := homDensity_sub_le_of_cutDistance F (W n) V
        _ < F.edgeFinset.card * (ε / F.edgeFinset.card) := by
            apply mul_lt_mul_of_pos_left (hN n hn) hcard_pos
        _ = ε := mul_div_cancel₀ ε (ne_of_gt hcard_pos)
  · -- Backward: inverse counting lemma
    intro hhom ε hε
    obtain ⟨δ, hδ, k, hk⟩ := cutDistance_le_of_homDensity_close (α := α) (μ := μ) ε hε
    have h_finitely_many : ∀ (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
        ∃ N, ∀ n ≥ N, |homDensity F (W n) - homDensity F V| < δ :=
      fun F _ => hhom k F δ hδ
    classical
    choose N_F hN_F using fun (F : SimpleGraph (Fin k)) =>
      @h_finitely_many F (Classical.decRel _)
    use Finset.univ.sup N_F
    intro n hn
    apply hk
    intro F _
    have := hN_F F n (le_trans (Finset.le_sup (Finset.mem_univ F)) hn)
    convert this

end InverseCounting

/-! ### Uniqueness of limits -/

section Uniqueness

variable [IsProbabilityMeasure μ]

/-- If a sequence converges to two limits, they are weakly isomorphic. -/
theorem limit_unique_upto_weakIso [StandardBorelSpace α]
    (W : ℕ → Graphon α μ) (U V : Graphon α μ)
    (hU : ∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W n) U < ε)
    (hV : ∀ ε > 0, ∃ N, ∀ n ≥ N, cutDistance (W n) V < ε) :
    WeaklyIsomorphic U V := by
  unfold WeaklyIsomorphic
  apply le_antisymm
  · by_contra h_neg
    push Not at h_neg
    set ε := cutDistance U V / 2 with hε_def
    have hε_pos : ε > 0 := by positivity
    obtain ⟨N₁, hN₁⟩ := hU ε hε_pos
    obtain ⟨N₂, hN₂⟩ := hV ε hε_pos
    set n := max N₁ N₂
    have h1 := hN₁ n (le_max_left _ _)
    have h2 := hN₂ n (le_max_right _ _)
    have h_tri := cutDistance_triangle U (W n) V
    have h_symm := cutDistance_symm U (W n)
    linarith
  · exact cutDistance_nonneg U V

/-- Homomorphism densities determine the graphon up to weak isomorphism. -/
theorem weaklyIsomorphic_of_homDensity_eq [StandardBorelSpace α] [NoAtoms μ]
    (U W : Graphon α μ)
    (h : ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
         homDensity F U = homDensity F W) :
    WeaklyIsomorphic U W :=
  cutDistance_zero_of_homDensity_eq U W h

end Uniqueness

end Graphon
