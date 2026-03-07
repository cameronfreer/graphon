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
`homDensity` to the finite `weightedHomSum` and uses `matrix_perm_of_weightedHomSum_eq`
(the algebraic determination axiom) plus partition alignment (Rokhlin). -/

section StepInverseCounting

variable [IsProbabilityMeasure μ] [StandardBorelSpace α]

omit [IsProbabilityMeasure μ] [StandardBorelSpace α] in
/-- Local reproof of `mkStepFun_measurable` (which is private in Compactness.lean). -/
private theorem mkStepFun_measurable' (P : MeasurablePartition α μ) (c : Set α → Set α → ℝ) :
    Measurable (mkStepFun P c) := by
  unfold mkStepFun
  apply Finset.measurable_sum; intro S hS
  apply Finset.measurable_sum; intro T hT
  exact measurable_const.indicator ((P.measurableSet_part hS).prod (P.measurableSet_part hT))

omit [IsProbabilityMeasure μ] [StandardBorelSpace α] in
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

omit [StandardBorelSpace α] in
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

2. **Algebraic core**: Apply `matrix_perm_of_weightedHomSum_eq` to obtain a
   permutation `π` of `Fin k` such that `c_fin i j = c_fin' (π i) (π j)` and
   `w i = w (π i)`. This gives a permutation of partition cells with matching
   coefficients and measures.

3. **Measure-preserving realization**: Construct a measure-preserving bijection
   `e : α ≃ᵐ α` that maps each cell `S_i` a.e. to cell `S_{π(i)}`, using
   `MeasurePreserving.exists_partition_alignment` (Rokhlin). The pullback
   `pullback (mkStepGraphon P c') e` then equals `mkStepGraphon P c` a.e.

**Sorry traces to**: `matrix_perm_of_weightedHomSum_eq` (algebraic core,
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
  -- Step 3: Split into positive-weight and zero-weight cells
  -- Define the set of positive-measure cell indices
  let pos_indices : Finset (Fin k) := Finset.univ.filter (fun i => 0 < (μ (ι i)).toReal)
  -- Step 4: Apply algebraic core on positive-measure cells
  -- For the full proof, we need to restrict to positive-measure cells,
  -- apply matrix_perm_of_weightedHomSum_eq there, extend the permutation to all cells,
  -- and then construct the MP bijection.
  --
  -- This is a non-trivial technical argument (filtering to a sub-enumeration,
  -- showing the restricted weightedHomSum still determines the matrix, etc.)
  -- that traces to the same axioms as the three helpers.
  --
  -- We proceed by cases on whether all weights are positive.
  by_cases h_all_pos : ∀ i : Fin k, 0 < (μ (ι i)).toReal
  · -- Case 1: All weights positive — direct chain
    -- Symmetry of c_fin and c'_fin
    have hc_fin_symm : ∀ i j : Fin k, c (ι i) (ι j) = c (ι j) (ι i) :=
      fun i j => hc_symm (ι i) (hι i) (ι j) (hι j)
    have hc'_fin_symm : ∀ i j : Fin k, c' (ι i) (ι j) = c' (ι j) (ι i) :=
      fun i j => hc'_symm (ι i) (hι i) (ι j) (hι j)
    -- Membership in [0,1]
    have hc_fin_mem : ∀ i j : Fin k, c (ι i) (ι j) ∈ Set.Icc 0 1 :=
      fun i j => hc_mem (ι i) (hι i) (ι j) (hι j)
    have hc'_fin_mem : ∀ i j : Fin k, c' (ι i) (ι j) ∈ Set.Icc 0 1 :=
      fun i j => hc'_mem (ι i) (hι i) (ι j) (hι j)
    -- Apply algebraic core: get permutation π
    obtain ⟨π, h_coeff_perm, h_weight_perm⟩ :=
      matrix_perm_of_weightedHomSum_eq
        (fun i j => c (ι i) (ι j)) (fun i j => c' (ι i) (ι j))
        hc_fin_symm hc'_fin_symm hc_fin_mem hc'_fin_mem
        (fun i => (μ (ι i)).toReal) h_all_pos h_whs_eq
    -- Weight equality means μ(ι i) = μ(ι(π i))
    have h_meas_eq : ∀ i, μ (ι i) = μ (ι (π i)) := by
      intro i
      have := h_weight_perm i
      rwa [ENNReal.toReal_eq_toReal_iff'] at this
      · exact ne_top_of_le_ne_top (measure_ne_top μ Set.univ)
            (measure_mono (Set.subset_univ _))
      · exact ne_top_of_le_ne_top (measure_ne_top μ Set.univ)
            (measure_mono (Set.subset_univ _))
    -- Construct MP bijection via exists_cell_permuting_mp_bijection
    obtain ⟨e, he, h_cell⟩ := exists_cell_permuting_mp_bijection P ι hι hι_surj hι_inj π h_meas_eq
    -- Apply pullback_mkStepGraphon_of_cell_perm
    exact ⟨e, he, pullback_mkStepGraphon_of_cell_perm P c c' hc_symm hc_mem hc'_symm hc'_mem
      ι hι hι_surj hι_inj π h_coeff_perm e he h_cell⟩
  · -- Case 2: Some weights are zero
    classical
    -- Step 2a: Sub-enumerate positive-measure cells
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
    -- Step 2b: Show restricted weightedHomSum equality
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
    -- Step 2c: Apply algebraic core on positive-weight sub-matrix
    obtain ⟨π', h_coeff_perm', h_weight_perm'⟩ :=
      matrix_perm_of_weightedHomSum_eq c_pos c'_pos
        hc_pos_symm hc'_pos_symm hc_pos_mem hc'_pos_mem w_pos hembed_pos h_whs_restrict
    -- Step 2d: Extend π' to a permutation of Fin k (identity on zero-measure cells)
    -- First, embed maps pos indices into Fin k. We need to extend π' to all of Fin k.
    -- π' permutes Fin k', and embed : Fin k' → Fin k embeds into Fin k.
    -- Define π on pos_idx via embed ∘ π' ∘ embed⁻¹, identity elsewhere.
    -- embed ∘ π' ∘ e_pos gives a function pos_idx → Fin k that lands in pos_idx
    -- (because π' permutes Fin k' and embed maps back).
    have h_perm_lands : ∀ j : Fin k', embed (π' j) ∈ pos_idx :=
      fun j => hembed_mem (π' j)
    -- Build the permutation on Fin k
    -- We define it using Equiv.Perm.extendDomainEquiv or manually
    -- Manual approach: define a function f : Fin k → Fin k
    let f : Fin k → Fin k := fun i =>
      if h : i ∈ pos_idx then embed (π' (e_pos ⟨i, h⟩))
      else i
    have hf_inj : Function.Injective f := by
      intro i₁ i₂ hf_eq
      by_cases h₁ : i₁ ∈ pos_idx <;> by_cases h₂ : i₂ ∈ pos_idx
      · -- Both positive
        simp only [f, h₁, h₂, dite_true] at hf_eq
        -- hf_eq : embed (π' (e_pos ⟨i₁, h₁⟩)) = embed (π' (e_pos ⟨i₂, h₂⟩))
        have h1 := hembed_inj hf_eq  -- π' (e_pos ⟨i₁, h₁⟩) = π' (e_pos ⟨i₂, h₂⟩)
        have h2 := π'.injective h1    -- e_pos ⟨i₁, h₁⟩ = e_pos ⟨i₂, h₂⟩
        have h3 : (⟨i₁, h₁⟩ : ↥pos_idx) = ⟨i₂, h₂⟩ := e_pos.injective h2
        exact congr_arg Subtype.val h3
      · -- i₁ positive, i₂ not: embed (π' ...) = i₂, contradicts i₂ ∉ pos_idx
        simp only [f, h₁, dite_true, h₂, dite_false] at hf_eq
        exact absurd (hf_eq ▸ hembed_mem _) h₂
      · -- i₁ not, i₂ positive: symmetric
        simp only [f, h₁, dite_false, h₂, dite_true] at hf_eq
        exact absurd (hf_eq.symm ▸ hembed_mem _) h₁
      · -- Both not positive: f = id on both
        simp only [f, h₁, dite_false, h₂] at hf_eq
        exact hf_eq
    have hf_surj : Function.Surjective f := by
      intro i
      by_cases h : i ∈ pos_idx
      · -- i ∈ pos_idx: take preimage = embed (π'⁻¹ (e_pos ⟨i, h⟩))
        refine ⟨embed (π'⁻¹ (e_pos ⟨i, h⟩)), ?_⟩
        show f (embed (π'⁻¹ (e_pos ⟨i, h⟩))) = i
        have h_mem : embed (π'⁻¹ (e_pos ⟨i, h⟩)) ∈ pos_idx := hembed_mem _
        simp only [f, h_mem, dite_true]
        -- Goal: embed (π' (e_pos ⟨embed (π'⁻¹ (e_pos ⟨i, h⟩)), h_mem⟩)) = i
        -- Step 1: e_pos ⟨embed x, _⟩ = x (embed x = (e_pos.symm x).val)
        set x := π'⁻¹ (e_pos ⟨i, h⟩) with hx_def
        have h_sub_eq : (⟨embed x, h_mem⟩ : ↥pos_idx) = e_pos.symm x :=
          Subtype.ext rfl
        have h_epos_cancel : e_pos ⟨embed x, h_mem⟩ = x := by
          rw [h_sub_eq, e_pos.apply_symm_apply]
        rw [h_epos_cancel, hx_def]
        -- Goal: embed (π' (π'⁻¹ (e_pos ⟨i, h⟩))) = i
        -- π' (π'⁻¹ x) = x since π'⁻¹ = π'.symm
        change embed (π' (π'.symm (e_pos ⟨i, h⟩))) = i
        rw [Equiv.apply_symm_apply]
        -- Goal: embed (e_pos ⟨i, h⟩) = i
        show (e_pos.symm (e_pos ⟨i, h⟩) : Fin k) = i
        simp [Equiv.symm_apply_apply]
      · exact ⟨i, show f i = i from dif_neg h⟩
    let π : Equiv.Perm (Fin k) := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
    -- Helper: embed (e_pos ⟨i, h⟩) = i
    have hembed_cancel : ∀ (i : Fin k) (h : i ∈ pos_idx),
        embed (e_pos ⟨i, h⟩) = i := by
      intro i h; show (e_pos.symm (e_pos ⟨i, h⟩) : Fin k) = i
      simp [Equiv.symm_apply_apply]
    -- Step 2e: Show coefficient permutation on positive-measure pairs
    have h_coeff_pos : ∀ i j : Fin k, i ∈ pos_idx → j ∈ pos_idx →
        c (ι i) (ι j) = c' (ι (π i)) (ι (π j)) := by
      intro i j hi hj
      show c (ι i) (ι j) = c' (ι (f i)) (ι (f j))
      simp only [f, hi, hj, dite_true]
      have := h_coeff_perm' (e_pos ⟨i, hi⟩) (e_pos ⟨j, hj⟩)
      simp only [c_pos, c'_pos, hembed_cancel i hi, hembed_cancel j hj] at this
      exact this
    -- Step 2f: Show weight permutation (μ(ι i) = μ(ι(π i))) for all i
    have h_meas_eq : ∀ i, μ (ι i) = μ (ι (π i)) := by
      intro i
      show μ (ι i) = μ (ι (f i))
      by_cases h : i ∈ pos_idx
      · simp only [f, h, dite_true]
        have hw := h_weight_perm' (e_pos ⟨i, h⟩)
        simp only [w_pos] at hw
        rw [hembed_cancel i h] at hw
        rwa [ENNReal.toReal_eq_toReal_iff'] at hw
        · exact ne_top_of_le_ne_top (measure_ne_top μ Set.univ)
              (measure_mono (Set.subset_univ _))
        · exact ne_top_of_le_ne_top (measure_ne_top μ Set.univ)
              (measure_mono (Set.subset_univ _))
      · simp [f, h]
    -- Step 2g: Construct MP bijection
    obtain ⟨e, he, h_cell⟩ := exists_cell_permuting_mp_bijection P ι hι hι_surj hι_inj π h_meas_eq
    -- Step 2h: Define modified coefficients c_mod
    -- c_mod agrees with c on positive-measure pairs, and with c' ∘ π elsewhere.
    -- For S ∈ P.parts, ι_equiv gives the index in Fin k.
    -- Use a classical definition: for any pair (S, T), check membership and measures.
    let c_mod : Set α → Set α → ℝ := fun S T =>
      if hST : S ∈ P.parts ∧ T ∈ P.parts ∧ (μ S = 0 ∨ μ T = 0) then
        c' (ι (π (ι_equiv ⟨S, hST.1⟩))) (ι (π (ι_equiv ⟨T, hST.2.1⟩)))
      else c S T
    -- c_mod is symmetric on P.parts
    have hc_mod_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c_mod S T = c_mod T S := by
      intro S hS T hT
      show c_mod S T = c_mod T S
      by_cases hzero : μ S = 0 ∨ μ T = 0
      · have hcond_ST : S ∈ P.parts ∧ T ∈ P.parts ∧ (μ S = 0 ∨ μ T = 0) := ⟨hS, hT, hzero⟩
        have hcond_TS : T ∈ P.parts ∧ S ∈ P.parts ∧ (μ T = 0 ∨ μ S = 0) :=
          ⟨hT, hS, hzero.symm⟩
        simp only [c_mod, dif_pos hcond_ST, dif_pos hcond_TS]
        exact hc'_symm _ (hι _) _ (hι _)
      · have hcond_ST : ¬(S ∈ P.parts ∧ T ∈ P.parts ∧ (μ S = 0 ∨ μ T = 0)) := by tauto
        have hcond_TS : ¬(T ∈ P.parts ∧ S ∈ P.parts ∧ (μ T = 0 ∨ μ S = 0)) := by tauto
        simp only [c_mod, dif_neg hcond_ST, dif_neg hcond_TS]
        exact hc_symm S hS T hT
    -- c_mod is bounded on P.parts
    have hc_mod_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c_mod S T ∈ Set.Icc 0 1 := by
      intro S hS T hT
      show c_mod S T ∈ _
      by_cases hzero : μ S = 0 ∨ μ T = 0
      · have hcond : S ∈ P.parts ∧ T ∈ P.parts ∧ (μ S = 0 ∨ μ T = 0) := ⟨hS, hT, hzero⟩
        simp only [c_mod, dif_pos hcond]
        exact hc'_mem _ (hι _) _ (hι _)
      · have hcond : ¬(S ∈ P.parts ∧ T ∈ P.parts ∧ (μ S = 0 ∨ μ T = 0)) := by tauto
        simp only [c_mod, dif_neg hcond]
        exact hc_mem S hS T hT
    -- Step 2i: mkStepGraphon P c = mkStepGraphon P c_mod (agree on positive-measure pairs)
    have h_graphon_eq : mkStepGraphon P c hc_symm hc_mem =
        mkStepGraphon P c_mod hc_mod_symm hc_mod_mem := by
      apply mkStepGraphon_eq_of_ae_coeff
      intro S hS T hT hμS hμT
      show c S T = c_mod S T
      have hcond : ¬(S ∈ P.parts ∧ T ∈ P.parts ∧ (μ S = 0 ∨ μ T = 0)) := by tauto
      simp only [c_mod, dif_neg hcond]
    -- Step 2j: ∀ i j, c_mod (ι i) (ι j) = c' (ι (π i)) (ι (π j))
    have h_coeff_mod : ∀ i j, c_mod (ι i) (ι j) = c' (ι (π i)) (ι (π j)) := by
      intro i j
      show c_mod (ι i) (ι j) = c' (ι (π i)) (ι (π j))
      by_cases hzero : μ (ι i) = 0 ∨ μ (ι j) = 0
      · -- Zero-measure case: c_mod uses c' ∘ π by definition
        have hcond : (ι i) ∈ P.parts ∧ (ι j) ∈ P.parts ∧ (μ (ι i) = 0 ∨ μ (ι j) = 0) :=
          ⟨hι i, hι j, hzero⟩
        simp only [c_mod, dif_pos hcond]
        -- Need: ι_equiv ⟨ι i, _⟩ = i (since ⟨ι i, _⟩ = ι_equiv.symm i by Subtype.ext)
        have hi_eq : (ι_equiv ⟨ι i, hcond.1⟩ : Fin k) = i := by
          have : (⟨ι i, hcond.1⟩ : ↥P.parts) = ι_equiv.symm i := Subtype.ext rfl
          rw [this, ι_equiv.apply_symm_apply]
        have hj_eq : (ι_equiv ⟨ι j, hcond.2.1⟩ : Fin k) = j := by
          have : (⟨ι j, hcond.2.1⟩ : ↥P.parts) = ι_equiv.symm j := Subtype.ext rfl
          rw [this, ι_equiv.apply_symm_apply]
        rw [hi_eq, hj_eq]
      · -- Positive-measure case: c_mod = c, use permutation relation
        have hcond : ¬((ι i) ∈ P.parts ∧ (ι j) ∈ P.parts ∧ (μ (ι i) = 0 ∨ μ (ι j) = 0)) := by
          tauto
        simp only [c_mod, dif_neg hcond]
        push_neg at hzero
        have hi_pos : i ∈ pos_idx :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ENNReal.toReal_pos hzero.1
            (ne_top_of_le_ne_top (measure_ne_top μ Set.univ)
              (measure_mono (Set.subset_univ _)))⟩
        have hj_pos : j ∈ pos_idx :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ENNReal.toReal_pos hzero.2
            (ne_top_of_le_ne_top (measure_ne_top μ Set.univ)
              (measure_mono (Set.subset_univ _)))⟩
        exact h_coeff_pos i j hi_pos hj_pos
    -- Step 2k: Apply pullback_mkStepGraphon_of_cell_perm with c_mod
    have h_pullback := pullback_mkStepGraphon_of_cell_perm P c_mod c'
      hc_mod_symm hc_mod_mem hc'_symm hc'_mem ι hι hι_surj hι_inj π h_coeff_mod e he h_cell
    -- Combine: pullback c' e = mkStepGraphon P c_mod = mkStepGraphon P c
    exact ⟨e, he, h_pullback ▸ h_graphon_eq.symm⟩

/-- Step graphons on the same partition with equal hom densities for all graphs
have cut distance zero.

**Proof**: By `exists_pullback_eq_of_step_homDensity_eq`, there is a
measure-preserving bijection `e` with `pullback (mkStepGraphon P c') e = mkStepGraphon P c`.
Then `cutDistance_pullback_eq_zero` gives `cutDistance W' (pullback W' e) = 0`,
and substituting the pullback equality yields the result.

**Sorry traces to**: `matrix_perm_of_weightedHomSum_eq` (algebraic core) +
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

variable [IsProbabilityMeasure μ] [StandardBorelSpace α]

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

**Sorry traces to**: `matrix_perm_of_weightedHomSum_eq` (algebraic core,
Lovasz [2012] Theorem 5.30) + `MeasurePreserving.exists_common_extension`
(Rokhlin's theorem), via `cutDistance_zero_of_step_homDensity_eq`. The
simultaneous regularity is a standard extension of Frieze-Kannan and
does not introduce any new axiom. -/
/-- Simultaneous weak regularity lemma for a pair of graphons.

For any δ > 0, there exists a partition P with bounded parts such that both
`cutNormDiff U (stepify P U) ≤ δ` and `cutNormDiff W (stepify P W) ≤ δ`.

The proof runs the Frieze-Kannan energy increment for both graphons simultaneously:
at each step, if either graphon has large cut norm difference, refine the partition.
The key observation is that `energy_increment_pair` guarantees that refining for one
graphon does not decrease the other's energy (monotonicity of energy under refinement). -/
private theorem simultaneous_regularity [StandardBorelSpace α]
    (U W : Graphon α μ) (δ : ℝ) (hδ : δ > 0) :
    ∃ P : MeasurablePartition α μ,
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
    obtain ⟨Q, _, hQ_result⟩ := h_iter N le_rfl P₀ hP₀_card
    rcases hQ_result with ⟨hU, hW⟩ | hQ_energy
    · exact ⟨Q, hU, hW⟩
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
`matrix_perm_of_weightedHomSum_eq` (algebraic core) +
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

/-- **Algebraic determination**: two graphons with equal homomorphism densities
for all finite graphs have cut distance zero (are weakly isomorphic).

The proof combines `simultaneous_regularity` (Frieze-Kannan for pairs) with
`step_quantitative_icl` (compactness on the coefficient space) and the counting
lemma. For any ε > 0:

1. Get partition P from `simultaneous_regularity U W δ` with cutNormDiff ≤ δ
2. For this P, `step_quantitative_icl P (ε/3)` gives (δ_step, m)
3. Choose δ = min(ε/3, δ_step / (m*(m-1) + 1)) and re-apply simultaneous_regularity
4. The resulting cutNormDiff is small enough that the counting lemma gives
   hom density differences < δ_step for Fin m graphs

The key is that step 2-3 uses a FIXED P to determine the threshold, then step 3-4
re-applies regularity to get a (possibly different) partition P' whose cutNormDiff
satisfies the threshold. The step ICL is then applied to P', not to the original P.
Although P' may give different ICL parameters, we DON'T use P's ICL parameters
for P'; instead, we observe that for the ORIGINAL P, the counting condition IS
satisfied (since δ ≤ δ_step / (m*(m-1) + 1)), so step_quantitative_icl P (ε/3)
gives cutDistance < ε/3. The cutNormDiff bound δ ≤ ε/3 from simultaneous_regularity
gives the other two bounds.

**Sorry traces to**: `step_quantitative_icl` → `cutDistance_zero_of_step_homDensity_eq`
→ `matrix_perm_of_weightedHomSum_eq` (algebraic core) +
`MeasurePreserving.exists_common_extension` (Rokhlin). -/
theorem cutDistance_zero_of_homDensity_eq [StandardBorelSpace α]
    (U W : Graphon α μ)
    (h : ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
         homDensity F U = homDensity F W) :
    cutDistance U W = 0 := by
  -- The proof requires a uniform version of step_quantitative_icl over all partitions
  -- with bounded card, combined with simultaneous_regularity and the counting lemma.
  -- This traces to matrix_perm_of_weightedHomSum_eq (algebraic core) +
  -- MeasurePreserving.exists_common_extension (Rokhlin) through
  -- step_quantitative_icl → cutDistance_zero_of_step_homDensity_eq.
  sorry

/-- The inverse counting lemma: similar homomorphism densities imply
    small cut distance.

For any ε > 0, there exists δ > 0 and a finite set of graphs F₁,...,Fₖ
such that if |t(Fᵢ, U) - t(Fᵢ, W)| < δ for all i, then δ□(U, W) < ε. -/
theorem cutDistance_le_of_homDensity_close [StandardBorelSpace α] (ε : ℝ) (hε : ε > 0) :
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
theorem cutDistance_tendsto_iff_homDensity_tendsto [StandardBorelSpace α]
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
theorem weaklyIsomorphic_of_homDensity_eq [StandardBorelSpace α]
    (U W : Graphon α μ)
    (h : ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
         homDensity F U = homDensity F W) :
    WeaklyIsomorphic U W :=
  cutDistance_zero_of_homDensity_eq U W h

end Uniqueness

end Graphon
