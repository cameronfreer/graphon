/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.LevyDownward
import Graphon.RelRestrictionBlocks
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.ZeroOne

/-!
# Restriction independence and vertex-tail triviality (AHK umbrella, R3b / #106)

The generic equivalence between dissociation and restriction independence, and the implication
to vertex-tail triviality, for exchangeable relational laws:

* `InfiniteRelExchangeableLaw.RestrictionIndependent` — for every block size the initial and
  after-block σ-algebras are independent;
* `InfiniteRelExchangeableLaw.VertexTailTrivial` — every vertex-tail event has law-measure
  `0` or `1`;
* `isDissociated_iff_restrictionIndependent` — **dissociation ↔ restriction independence**:
  independence of the comap σ-algebras of the two block maps *is* the block-pair map
  factorization (`IndepFun_iff_Indep` + `indepFun_iff_map_prod_eq_prod_map_map`), and the
  finite tail windows exhaust the after-block σ-algebra (R3a);
* `RestrictionIndependent.vertexTailTrivial` — a vertex-tail event is independent of every
  initial σ-algebra, hence (the initial σ-algebras generating, R3a) of itself.

* `VertexTailTrivial.isDissociated` / `isDissociated_iff_vertexTailTrivial` — **the closing
  arrow, representation-free**: condition the initial-event indicator on successively later
  diagonal tail algebras; Lévy's *downward* theorem (`Graphon/LevyDownward.lean`) converges
  the conditional expectations to the vertex-tail one, which tail triviality makes a.e.
  constant; exchangeability keeps the joint mass with an arbitrarily far window constant
  (`law_map_restrict_pair`); in the limit the block mass factorizes exactly. (The undirected
  proof instead rides the graphon mixture representation; the generic theory keeps the
  characterization representation-free, with R5's Dirac-mixing as a later corollary.)
-/

open MeasureTheory ProbabilityTheory RelSignature Filter Topology

namespace RelSignature

variable {S : RelSignature}

/-! ### Window monotonicity -/

/-- The finite tail windows are monotone in the window size. -/
theorem RelStructure.tailWindowAlgebra_mono (k : S.Srt → ℕ) {l l' : S.Srt → ℕ}
    (h : ∀ s, l s ≤ l' s) :
    RelStructure.tailWindowAlgebra (S := S) k l ≤ RelStructure.tailWindowAlgebra (S := S) k l' := by
  refine measurable_iff_comap_le.mp ?_
  rw [show RelStructure.restrict (S := S) (shiftEmb k l) =
      RelStructure.restrictLE h ∘ RelStructure.restrict (shiftEmb k l') from rfl]
  exact (RelSignature.measurable_restrictLE h).comp
    (@Measurable.of_comap_le _ _ (RelStructure.tailWindowAlgebra k l') _
      (RelStructure.restrict (shiftEmb k l')) le_rfl)

theorem RelStructure.tailWindowAlgebra_le_tailAlgebra (k l : S.Srt → ℕ) :
    RelStructure.tailWindowAlgebra (S := S) k l ≤ RelStructure.tailAlgebra (S := S) k := by
  rw [← RelStructure.iSup_tailWindowAlgebra_eq k]
  exact le_iSup (RelStructure.tailWindowAlgebra (S := S) k) l

/-! ### The two properties -/

/-- **Restriction independence**: for every block size, the structure on the initial block is
independent of the structure on the remaining vertices. -/
def InfiniteRelExchangeableLaw.RestrictionIndependent (M : InfiniteRelExchangeableLaw S) :
    Prop :=
  ∀ k : S.Srt → ℕ, Indep (RelStructure.initialAlgebra k) (RelStructure.tailAlgebra k)
    (M.law : Measure (RelStructure S (Vinfinite S)))

/-- **Vertex-tail triviality**: every vertex-tail event has law-measure `0` or `1`. -/
def InfiniteRelExchangeableLaw.VertexTailTrivial (M : InfiniteRelExchangeableLaw S) : Prop :=
  ∀ s, MeasurableSet[RelStructure.vertexTailAlgebra] s →
    (M.law : Measure (RelStructure S (Vinfinite S))) s = 0 ∨
      (M.law : Measure (RelStructure S (Vinfinite S))) s = 1

/-! ### Dissociation ↔ restriction independence -/

/-- **Finite-window independence from dissociation**: comap-σ-algebra independence of the
initial block and a tail window is exactly the block-pair map factorization. -/
theorem InfiniteRelExchangeableLaw.IsDissociated.indep_initial_tailWindow
    {M : InfiniteRelExchangeableLaw S} (hM : M.IsDissociated) (k l : S.Srt → ℕ) :
    Indep (RelStructure.initialAlgebra k) (RelStructure.tailWindowAlgebra k l)
      (M.law : Measure (RelStructure S (Vinfinite S))) := by
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  have hwinmeas : Measurable (RelStructure.restrict (S := S) (shiftEmb k l)) := by
    rw [restrict_shiftEmb_eq]
    exact (RelSignature.measurable_restrictFin l).comp (measurable_drop k)
  rw [RelStructure.initialAlgebra, RelStructure.tailWindowAlgebra, ← IndepFun_iff_Indep,
    indepFun_iff_map_prod_eq_prod_map_map
      (RelSignature.measurable_restrictFin k).aemeasurable hwinmeas.aemeasurable,
    M.law_map_restrict (shiftEmb k l)]
  exact hM k l

/-- **Dissociation implies restriction independence**: the finite windows exhaust the
after-block σ-algebra. -/
theorem InfiniteRelExchangeableLaw.IsDissociated.restrictionIndependent
    {M : InfiniteRelExchangeableLaw S} (hM : M.IsDissociated) :
    M.RestrictionIndependent := by
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  intro k
  have hsup := indep_iSup_of_directed_le
    (fun l => (hM.indep_initial_tailWindow k l).symm)
    (fun l => (RelStructure.tailWindowAlgebra_le_tailAlgebra k l).trans
      (RelStructure.tailAlgebra_le k))
    (RelStructure.initialAlgebra_le k)
    (fun l l' => ⟨fun s => max (l s) (l' s),
      RelStructure.tailWindowAlgebra_mono k fun s => le_max_left _ _,
      RelStructure.tailWindowAlgebra_mono k fun s => le_max_right _ _⟩)
  rw [RelStructure.iSup_tailWindowAlgebra_eq] at hsup
  exact hsup.symm

/-- **Restriction independence implies dissociation**: restrict the independence to a window
and read it as the block-pair map factorization. -/
theorem InfiniteRelExchangeableLaw.RestrictionIndependent.isDissociated
    {M : InfiniteRelExchangeableLaw S} (hM : M.RestrictionIndependent) :
    M.IsDissociated := by
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  intro k l
  have hwinmeas : Measurable (RelStructure.restrict (S := S) (shiftEmb k l)) := by
    rw [restrict_shiftEmb_eq]
    exact (RelSignature.measurable_restrictFin l).comp (measurable_drop k)
  have hwin : Indep (RelStructure.initialAlgebra k) (RelStructure.tailWindowAlgebra k l)
      (M.law : Measure (RelStructure S (Vinfinite S))) :=
    indep_of_indep_of_le_right (hM k) (RelStructure.tailWindowAlgebra_le_tailAlgebra k l)
  rw [RelStructure.initialAlgebra, RelStructure.tailWindowAlgebra, ← IndepFun_iff_Indep,
    indepFun_iff_map_prod_eq_prod_map_map
      (RelSignature.measurable_restrictFin k).aemeasurable hwinmeas.aemeasurable,
    M.law_map_restrict (shiftEmb k l)] at hwin
  exact hwin

/-- **Dissociation ↔ restriction independence** (R3b). -/
theorem isDissociated_iff_restrictionIndependent (M : InfiniteRelExchangeableLaw S) :
    M.IsDissociated ↔ M.RestrictionIndependent :=
  ⟨fun h => h.restrictionIndependent, fun h => h.isDissociated⟩

/-! ### Restriction independence implies vertex-tail triviality -/

/-- **Restriction independence implies vertex-tail triviality**: a vertex-tail event is
independent of every initial σ-algebra, hence — the initial σ-algebras generating the Borel
σ-algebra — independent of itself. -/
theorem InfiniteRelExchangeableLaw.RestrictionIndependent.vertexTailTrivial
    {M : InfiniteRelExchangeableLaw S} (hM : M.RestrictionIndependent) :
    M.VertexTailTrivial := by
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  intro s hs
  have hindep : ∀ k : S.Srt → ℕ, Indep (RelStructure.initialAlgebra k)
      RelStructure.vertexTailAlgebra (M.law : Measure (RelStructure S (Vinfinite S))) :=
    fun k => indep_of_indep_of_le_right (hM k)
      (RelStructure.vertexTailAlgebra_le_tailAlgebra k)
  have hsup : Indep (⨆ k : S.Srt → ℕ, RelStructure.initialAlgebra k)
      RelStructure.vertexTailAlgebra (M.law : Measure (RelStructure S (Vinfinite S))) := by
    refine indep_iSup_of_directed_le hindep RelStructure.initialAlgebra_le
      RelStructure.vertexTailAlgebra_le ?_
    intro k k'
    exact ⟨fun s => max (k s) (k' s),
      RelStructure.initialAlgebra_mono fun s => le_max_left _ _,
      RelStructure.initialAlgebra_mono fun s => le_max_right _ _⟩
  rw [RelStructure.iSup_initialAlgebra_eq] at hsup
  have hself : Indep RelStructure.vertexTailAlgebra RelStructure.vertexTailAlgebra
      (M.law : Measure (RelStructure S (Vinfinite S))) :=
    indep_of_indep_of_le_left hsup RelStructure.vertexTailAlgebra_le
  exact measure_eq_zero_or_one_of_indep_self hself hs

/-- **Dissociation implies vertex-tail triviality** (R3b chain). -/
theorem InfiniteRelExchangeableLaw.IsDissociated.vertexTailTrivial
    {M : InfiniteRelExchangeableLaw S} (hM : M.IsDissociated) :
    M.VertexTailTrivial :=
  hM.restrictionIndependent.vertexTailTrivial

/-! ### Vertex-tail triviality implies dissociation (the closing arrow) -/

/-- **Abstract Lévy-downward factorization step**: on a probability space, if `A` is an
ambient-measurable set and `B' n` is a `𝒢 n`-measurable set along an antitone sequence of
sub-σ-algebras whose intersection is `μ`-trivial, and if neither the masses `μ (B' n)` nor
the joint masses `μ (A ∩ B' n)` depend on `n` (equalling `μ B` and `μ (A ∩ B)`
respectively), then the joint mass factorizes exactly. -/
private theorem measure_inter_eq_mul_of_condExp_iInf {α : Type*}
    {m0 : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (𝒢 : ℕ → MeasurableSpace α) (hanti : Antitone 𝒢) (h𝒢 : ∀ n, 𝒢 n ≤ m0)
    (htriv : ∀ s, MeasurableSet[⨅ n, 𝒢 n] s → μ s = 0 ∨ μ s = 1)
    {A B : Set α} (hA : MeasurableSet A) (B' : ℕ → Set α)
    (hB' : ∀ n, MeasurableSet[𝒢 n] (B' n)) (hBmass : ∀ n, μ (B' n) = μ B)
    (hjoint : ∀ n, μ (A ∩ B' n) = μ (A ∩ B)) :
    μ (A ∩ B) = μ A * μ B := by
  have hinf : (⨅ n, 𝒢 n) ≤ m0 := (iInf_le 𝒢 0).trans (h𝒢 0)
  set f₀ : α → ℝ := A.indicator fun _ => 1 with hf₀def
  have hf₀ : Integrable f₀ μ := (integrable_const 1).indicator hA
  have hconst : μ[f₀|⨅ n, 𝒢 n] =ᵐ[μ] fun _ => ∫ x, f₀ x ∂μ :=
    condExp_ae_eq_integral_of_forall_zero_or_one hinf htriv hf₀
  have hc : ∫ x, f₀ x ∂μ = (μ A).toReal := by
    rw [hf₀def, integral_indicator_const (1 : ℝ) hA, smul_eq_mul, mul_one, measureReal_def]
  have hbound : ∀ n, |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| ≤
      (eLpNorm (μ[f₀|𝒢 n] - μ[f₀|⨅ m, 𝒢 m]) 1 μ).toReal := by
    intro n
    have hBn : MeasurableSet (B' n) := h𝒢 n _ (hB' n)
    have hg : Integrable (μ[f₀|𝒢 n] - μ[f₀|⨅ m, 𝒢 m]) μ :=
      integrable_condExp.sub integrable_condExp
    have h1 : ∫ x in B' n, (μ[f₀|𝒢 n]) x ∂μ = (μ (A ∩ B)).toReal := by
      rw [setIntegral_condExp (h𝒢 n) hf₀ (hB' n), hf₀def, setIntegral_indicator hA,
        setIntegral_const, smul_eq_mul, mul_one, Set.inter_comm (B' n) A, measureReal_def,
        hjoint n]
    have h2 : ∫ x in B' n, (μ[f₀|⨅ m, 𝒢 m]) x ∂μ = (μ A).toReal * (μ B).toReal := by
      rw [setIntegral_congr_ae hBn (hconst.mono fun x hx _ => hx), setIntegral_const,
        smul_eq_mul, hc, measureReal_def, hBmass n, mul_comm]
    have hsplit : ∫ x in B' n, (μ[f₀|𝒢 n] - μ[f₀|⨅ m, 𝒢 m]) x ∂μ =
        (μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal := by
      simp only [Pi.sub_apply]
      rw [integral_sub integrable_condExp.integrableOn integrable_condExp.integrableOn,
        h1, h2]
    calc |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal|
        = ‖∫ x in B' n, (μ[f₀|𝒢 n] - μ[f₀|⨅ m, 𝒢 m]) x ∂μ‖ := by
          rw [hsplit, Real.norm_eq_abs]
      _ ≤ ∫ x in B' n, ‖(μ[f₀|𝒢 n] - μ[f₀|⨅ m, 𝒢 m]) x‖ ∂μ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖(μ[f₀|𝒢 n] - μ[f₀|⨅ m, 𝒢 m]) x‖ ∂μ :=
          setIntegral_le_integral hg.norm (Eventually.of_forall fun x => norm_nonneg _)
      _ = (eLpNorm (μ[f₀|𝒢 n] - μ[f₀|⨅ m, 𝒢 m]) 1 μ).toReal := by
          rw [integral_norm_eq_lintegral_enorm hg.aestronglyMeasurable,
            eLpNorm_one_eq_lintegral_enorm]
  have hLevyReal : Tendsto
      (fun n => (eLpNorm (μ[f₀|𝒢 n] - μ[f₀|⨅ m, 𝒢 m]) 1 μ).toReal) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_eLpNorm_condExp_iInf 𝒢 hanti h𝒢 hf₀)
  have habs0 : |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| = 0 :=
    le_antisymm (ge_of_tendsto' hLevyReal hbound) (abs_nonneg _)
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _)
    (ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _))).mp ?_
  rw [ENNReal.toReal_mul]
  have := abs_eq_zero.mp habs0
  linarith

/-- **The core factorization**: for a vertex-tail-trivial exchangeable law, the mass of an
initial-block event intersected with an after-block window event factorizes — condition the
initial-event indicator on the diagonal tail algebras, push the window out by
exchangeability, and apply the abstract Lévy-downward step. -/
private theorem InfiniteRelExchangeableLaw.VertexTailTrivial.measure_inter_window
    [Fintype S.Srt] {M : InfiniteRelExchangeableLaw S} (hM : M.VertexTailTrivial)
    (k l : S.Srt → ℕ) {T₁ : Set (RelStructure S (Vfinite k))}
    {T₂ : Set (RelStructure S (Vfinite l))} (hT₁ : MeasurableSet T₁)
    (hT₂ : MeasurableSet T₂) :
    (M.law : Measure (RelStructure S (Vinfinite S)))
        (RelStructure.restrictFin k ⁻¹' T₁ ∩
          RelStructure.restrict (shiftEmb k l) ⁻¹' T₂) =
      (M.law : Measure (RelStructure S (Vinfinite S)))
          (RelStructure.restrictFin k ⁻¹' T₁) *
        (M.law : Measure (RelStructure S (Vinfinite S)))
          (RelStructure.restrict (shiftEmb k l) ⁻¹' T₂) := by
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  have hwinmeas : ∀ K : S.Srt → ℕ,
      Measurable (RelStructure.restrict (S := S) (shiftEmb K l)) := by
    intro K
    rw [restrict_shiftEmb_eq]
    exact (RelSignature.measurable_restrictFin l).comp (measurable_drop K)
  -- the joint mass with any window at least `k` out is the canonical block-pair mass
  have hjoint : ∀ K : S.Srt → ℕ, (∀ s, k s ≤ K s) →
      (M.law : Measure (RelStructure S (Vinfinite S)))
          (RelStructure.restrictFin k ⁻¹' T₁ ∩
            RelStructure.restrict (shiftEmb K l) ⁻¹' T₂) =
        ((M.law : Measure (RelStructure S (Vinfinite S))).map (blockPair k l))
          (T₁ ×ˢ T₂) := by
    intro K hK
    have hd : ∀ s (i : Fin (k s)) (j : Fin (l s)),
        (Fin.valEmbedding : Fin (k s) ↪ ℕ) i ≠ shiftEmb K l s j := by
      intro s i j h
      have hij : (i : ℕ) = (j : ℕ) + K s := h
      have h1 := i.isLt
      have h2 := hK s
      omega
    have hpairmeas : Measurable fun X : RelStructure S (Vinfinite S) =>
        (RelStructure.restrict (fun s => (Fin.valEmbedding : Fin (k s) ↪ ℕ)) X,
          RelStructure.restrict (shiftEmb K l) X) :=
      (RelSignature.measurable_restrictFin k).prodMk (hwinmeas K)
    rw [← M.law_map_restrict_pair (fun s => (Fin.valEmbedding : Fin (k s) ↪ ℕ))
        (shiftEmb K l) hd,
      Measure.map_apply hpairmeas (hT₁.prod hT₂)]
    rfl
  -- the window mass does not depend on the shift
  have hwindow : ∀ K : S.Srt → ℕ,
      (M.law : Measure (RelStructure S (Vinfinite S)))
          (RelStructure.restrict (shiftEmb K l) ⁻¹' T₂) =
        (M.law : Measure (RelStructure S (Vinfinite S)))
          (RelStructure.restrict (shiftEmb k l) ⁻¹' T₂) := by
    intro K
    rw [← Measure.map_apply (hwinmeas K) hT₂, ← Measure.map_apply (hwinmeas k) hT₂,
      M.law_map_restrict (shiftEmb K l), M.law_map_restrict (shiftEmb k l)]
  refine measure_inter_eq_mul_of_condExp_iInf
    (fun n => RelStructure.tailAlgebra (S := S) fun _ => n)
    (fun n m h => RelStructure.tailAlgebra_antitone fun _ => h)
    (fun n => RelStructure.tailAlgebra_le fun _ => n)
    (fun s hs => hM s (by rwa [RelStructure.vertexTailAlgebra_eq_iInf_diagonal]))
    (RelSignature.measurable_restrictFin k hT₁)
    (fun n => RelStructure.restrict (shiftEmb (fun s => max (k s) n) l) ⁻¹' T₂)
    (fun n => ?_) (fun n => hwindow fun s => max (k s) n) (fun n => ?_)
  · -- the far window is measurable for the diagonal tail algebra
    exact ((RelStructure.tailWindowAlgebra_le_tailAlgebra (fun s => max (k s) n) l).trans
      (RelStructure.tailAlgebra_antitone fun s => le_max_right (k s) n)) _
      (MeasurableSpace.measurableSet_comap.mpr ⟨T₂, hT₂, rfl⟩)
  · -- the joint mass with the far window equals the joint mass with the adjacent one
    exact (hjoint (fun s => max (k s) n) fun s => le_max_left _ _).trans
      (hjoint k fun _ => le_rfl).symm

/-- **Vertex-tail triviality implies dissociation** (representation-free): condition the
initial-event indicator on successively later diagonal tail algebras; Lévy's downward theorem
converges the conditional expectations to the vertex-tail one, which tail triviality makes
a.e. constant; exchangeability keeps the joint mass with an arbitrarily far window constant;
in the limit the block mass factorizes exactly. -/
theorem InfiniteRelExchangeableLaw.VertexTailTrivial.isDissociated [Fintype S.Srt]
    {M : InfiniteRelExchangeableLaw S} (hM : M.VertexTailTrivial) :
    M.IsDissociated := by
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  intro k l
  haveI : IsProbabilityMeasure
      ((M.law : Measure (RelStructure S (Vinfinite S))).map (RelStructure.restrictFin k)) :=
    Measure.isProbabilityMeasure_map (RelSignature.measurable_restrictFin k).aemeasurable
  haveI : IsProbabilityMeasure
      ((M.law : Measure (RelStructure S (Vinfinite S))).map (RelStructure.restrictFin l)) :=
    Measure.isProbabilityMeasure_map (RelSignature.measurable_restrictFin l).aemeasurable
  have hwinmeas : Measurable (RelStructure.restrict (S := S) (shiftEmb k l)) := by
    rw [restrict_shiftEmb_eq]
    exact (RelSignature.measurable_restrictFin l).comp (measurable_drop k)
  refine (Measure.prod_eq fun T₁ T₂ hT₁ hT₂ => ?_).symm
  rw [Measure.map_apply (measurable_blockPair k l) (hT₁.prod hT₂),
    Measure.map_apply (RelSignature.measurable_restrictFin k) hT₁,
    ← M.law_map_restrict (shiftEmb k l), Measure.map_apply hwinmeas hT₂]
  exact hM.measure_inter_window k l hT₁ hT₂

/-- **Dissociation ↔ vertex-tail triviality** (R3b complete, representation-free). -/
theorem isDissociated_iff_vertexTailTrivial [Fintype S.Srt]
    (M : InfiniteRelExchangeableLaw S) :
    M.IsDissociated ↔ M.VertexTailTrivial :=
  ⟨fun h => h.vertexTailTrivial, fun h => h.isDissociated⟩

end RelSignature
