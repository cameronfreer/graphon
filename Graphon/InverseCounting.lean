/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
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
      by_contra h; push_neg at h; exact hne (funext h)
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
    exact ENNReal.toReal_prod
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
        (zero_le _)
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
    rw [← ENNReal.toReal_eq_toReal h_ne_s h_ne_t,
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
        by_contra h_pos; push_neg at h_pos
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

**Sorry traces to**: `matrix_quotient_of_weightedHomSum_eq` (algebraic core,
Lovász [2012] Theorem 5.30) + `MeasurePreserving.exists_common_extension`
(Rokhlin's theorem). -/
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
        push_neg at hσ; exact h_vanish M σ hσ
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
        (zero_le _)
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

**Sorry traces to**: `matrix_quotient_of_weightedHomSum_eq` (algebraic core) +
`MeasurePreserving.exists_common_extension` (Rokhlin). -/
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
        push_neg at h_doneW
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
      push_neg at h_doneU
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
  push_neg at h_neg
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
    apply tendsto_finset_sum _ (fun σ _ => ?_)
    apply Filter.Tendsto.const_mul
    apply tendsto_finset_prod _ (fun e _ => ?_)
    exact h_pw _ _ 0
  have h_whs_conv_W : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      Tendsto (fun m => weightedHomSum n F
        (fun i j => coeff_seq (ψ m) i j 1) w) atTop
        (nhds (weightedHomSum n F (fun i j => c_lim i j 1) w)) := by
    intro n F _
    apply tendsto_finset_sum _ (fun σ _ => ?_)
    apply Filter.Tendsto.const_mul
    apply tendsto_finset_prod _ (fun e _ => ?_)
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
  sorry

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
theorem cutDistance_le_of_homDensity_close [StandardBorelSpace α] [NoAtoms μ] (ε : ℝ) (hε : ε > 0) :
    ∃ (δ : ℝ) (_ : δ > 0) (k : ℕ),
    ∀ (U W : Graphon α μ),
      (∀ (F : SimpleGraph (Fin k)) [DecidableRel F.Adj], |homDensity F U - homDensity F W| < δ) →
      cutDistance U W < ε := by
  -- Proof by contradiction + compactness.
  -- If false, for each n, ∃ U_n W_n with Fin-n hom densities within 1/(n+1) but d ≥ ε.
  -- Extract convergent subsequences; limits have equal hom densities but d ≥ ε, contradiction.
  by_contra h_neg
  push_neg at h_neg
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
    push_neg at h_small
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
    push_neg at h_neg
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
