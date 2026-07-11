/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.InfiniteSampler
import Graphon.MixtureExistence
import Graphon.McDiarmid

/-!
# Padded vertex exposure and the fixed-`F` hom-density concentration tail (issue #72, item 1)

The one-stage **padded vertex exposure** of the `W`-random graph `G(k, W)`: each sampled
vertex carries its position together with a full padded row of `k` edge coins, so that
the whole sample is a point of the finite i.i.d. product `Fin k → α × (Fin k → ℝ)` —
exactly the shape consumed by the bounded-differences MGF bound of `Graphon/McDiarmid.lean`.
Edge `{i, j}` reads its coin from row `max i j`, column `min i j`; unused entries are
harmless padding.

* `InfiniteGraph.exposedSample` — the exposed sampled graph, a measurable
  `SimpleGraph (Fin k)`-valued function of the exposure state;
* `InfiniteGraph.map_exposedSample` — **the law identification**: pushing the exposure
  source forward along `exposedSample W k` gives exactly the finite sample law
  `samplePMF W k` (upper events factor into per-edge coin cylinders; Möbius inversion
  via `Graphon.upperSum_injective` closes, as in
  `InfiniteGraph.map_sampleInfinite_restrictFin`);
* `InfiniteGraph.abs_homDensity_exposedSample_update_le` — **the oscillation bound**:
  updating a single exposed vertex moves the hom-density of a fixed `F` on `q` vertices
  by at most `q / k` (only vertex maps whose range contains the updated vertex can
  change status).

Feeding the oscillation bound to `ProbabilityTheory.hasSubgaussianMGF_of_bounded_differences`
and moving the center from the sample mean to `homDensity F W` by the public collision
estimate (`GraphonSpace.abs_integral_homDensityCoord_empiricalMixing_sub_le`, specialized
to `sampleExchangeableLaw W`) yields the public tail (issue #72 item 1, toward
Lovász Cor 10.4; consumed by the Borel–Cantelli assembly of issue #71):

* `Graphon.measureReal_abs_homDensity_sampled_sub_le` — **exponential concentration of
  the sampled hom-density at fixed `F`**: for `2q² ≤ εk`, the `samplePMF W k`-probability
  that `|t(F, G(k,W)) − t(F,W)| ≥ ε` is at most `2 exp(−ε²k / (2q²))`;
* `InfiniteGraph.samplerSource_abs_homDensity_restrictFin_sub_le` — the same tail for
  the explicit sampler `restrictFin k ∘ sampleInfinite W`;
* `InfiniteGraph.tsum_samplerSource_homDensity_tail_ne_top` — **the summability
  bridge**: for each fixed `ε > 0` the tail masses at sizes `n + 1` have finite total,
  in the exact shape consumed by Borel–Cantelli (`MeasureTheory.ae_eventually_notMem`).
-/

open MeasureTheory

open scoped Classical ENNReal NNReal

namespace InfiniteGraph

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ### The exposure source -/

/-- One padded coin row: `k` i.i.d. uniforms on `[0, 1]`. -/
noncomputable def coinRowMeasure (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi fun _ : Fin k => uniform01

instance (k : ℕ) : IsProbabilityMeasure (coinRowMeasure k) := by
  rw [coinRowMeasure]; infer_instance

/-- The per-vertex exposure state: an i.i.d. position with law `μ` together with an
independent full padded coin row. -/
noncomputable def exposureVertexMeasure (μ : Measure α) (k : ℕ) :
    Measure (α × (Fin k → ℝ)) :=
  μ.prod (coinRowMeasure k)

instance [IsProbabilityMeasure μ] (k : ℕ) :
    IsProbabilityMeasure (exposureVertexMeasure μ k) := by
  rw [exposureVertexMeasure]; infer_instance

/-- **The exposure source**: `k` i.i.d. exposed vertices — a finite i.i.d. product, the
state space of the bounded-differences inequality. -/
noncomputable def exposureMeasure (μ : Measure α) (k : ℕ) :
    Measure (Fin k → α × (Fin k → ℝ)) :=
  Measure.pi fun _ : Fin k => exposureVertexMeasure μ k

instance [IsProbabilityMeasure μ] (k : ℕ) :
    IsProbabilityMeasure (exposureMeasure μ k) := by
  rw [exposureMeasure]; infer_instance

/-! ### The exposed sampled graph -/

/-- **The exposed sampled graph**: include the edge `{i, j}` exactly when the coin in
row `max i j`, column `min i j` falls below the clamped graphon value at the
`Quot.out`-representative endpoint positions (the same orientation convention as
`sampleInfinite`/`sampleIntegrand`, which eliminates a.e.-symmetry juggling in the law
identification). Symmetric because `max`, `min`, and `s(i, j)` are; irreflexive by the
`i ≠ j` conjunct. -/
noncomputable def exposedSample (W : Graphon α μ) (k : ℕ)
    (x : Fin k → α × (Fin k → ℝ)) : SimpleGraph (Fin k) where
  Adj i j := i ≠ j ∧ (x (max i j)).2 (min i j) ≤
    clampedRep W ((x (Quot.out s(i, j)).1).1, (x (Quot.out s(i, j)).2).1)
  symm := ⟨by
    intro i j h
    refine ⟨h.1.symm, ?_⟩
    have h2 := h.2
    rwa [max_comm j i, min_comm j i, show s(j, i) = s(i, j) from Sym2.eq_swap]⟩
  loopless := ⟨fun i h => h.1 rfl⟩

/-- The adjacency of the exposed sample, unfolded. -/
theorem exposedSample_adj (W : Graphon α μ) (k : ℕ) (x : Fin k → α × (Fin k → ℝ))
    (i j : Fin k) :
    (exposedSample W k x).Adj i j ↔ i ≠ j ∧ (x (max i j)).2 (min i j) ≤
      clampedRep W ((x (Quot.out s(i, j)).1).1, (x (Quot.out s(i, j)).2).1) :=
  Iff.rfl

/-- **The exposed sample is measurable** in the exposure state: each adjacency is a
measurable comparison of coordinate evaluations. -/
theorem measurable_exposedSample (W : Graphon α μ) (k : ℕ) :
    Measurable (exposedSample W k) := by
  rw [SimpleGraph.measurable_iff_adj]
  intro i j
  simp only [exposedSample_adj]
  have hcoin : Measurable fun x : Fin k → α × (Fin k → ℝ) => (x (max i j)).2 (min i j) :=
    (measurable_pi_apply (min i j)).comp (measurable_snd.comp (measurable_pi_apply _))
  have hthr : Measurable fun x : Fin k → α × (Fin k → ℝ) =>
      clampedRep W ((x (Quot.out s(i, j)).1).1, (x (Quot.out s(i, j)).2).1) :=
    (measurable_clampedRep W).comp
      ((measurable_fst.comp (measurable_pi_apply _)).prodMk
        (measurable_fst.comp (measurable_pi_apply _)))
  exact measurable_const.and (measurableSet_setOf.mp (measurableSet_le hcoin hthr))

/-! ### The law identification -/

section Marginal

/-- The coin row read by an edge: the larger `Quot.out` endpoint. -/
private noncomputable def rowIdx {k : ℕ} (e : Sym2 (Fin k)) : Fin k :=
  max (Quot.out e).1 (Quot.out e).2

/-- The coin column read by an edge: the smaller `Quot.out` endpoint. -/
private noncomputable def colIdx {k : ℕ} (e : Sym2 (Fin k)) : Fin k :=
  min (Quot.out e).1 (Quot.out e).2

/-- The (column, row) pair reassembles the edge: `e ↦ (rowIdx e, colIdx e)` is
injective. -/
private theorem mk_colIdx_rowIdx {k : ℕ} (e : Sym2 (Fin k)) :
    s(colIdx e, rowIdx e) = e := by
  rw [colIdx, rowIdx]
  rcases le_total (Quot.out e).1 (Quot.out e).2 with h | h
  · rw [min_eq_left h, max_eq_right h]
    exact Quot.out_eq e
  · rw [min_eq_right h, max_eq_left h, Sym2.eq_swap]
    exact Quot.out_eq e

/-- `Quot.out` of a two-element unordered pair is the pair or its swap. -/
private theorem out_mk_eq_or_swap {k : ℕ} (i j : Fin k) :
    Quot.out s(i, j) = (i, j) ∨ Quot.out s(i, j) = (j, i) := by
  have h : s((Quot.out s(i, j)).1, (Quot.out s(i, j)).2) = s(i, j) := Quot.out_eq _
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (Prod.ext h1 h2)
  · exact Or.inr (Prod.ext h1 h2)

/-- Edge membership in the exposed sample, at the `Quot.out` representatives. -/
private theorem mem_edgeSet_exposedSample (W : Graphon α μ) (k : ℕ)
    (x : Fin k → α × (Fin k → ℝ)) {e : Sym2 (Fin k)}
    (hne : (Quot.out e).1 ≠ (Quot.out e).2) :
    e ∈ (exposedSample W k x).edgeSet ↔
      (x (rowIdx e)).2 (colIdx e) ≤
        clampedRep W ((x (Quot.out e).1).1, (x (Quot.out e).2).1) := by
  have hout : s((Quot.out e).1, (Quot.out e).2) = e := Quot.out_eq e
  constructor
  · intro h
    have hadj : (exposedSample W k x).Adj (Quot.out e).1 (Quot.out e).2 := by
      rwa [← e.out_eq] at h
    rw [exposedSample_adj, hout] at hadj
    exact hadj.2
  · intro h
    have hadj : (exposedSample W k x).Adj (Quot.out e).1 (Quot.out e).2 := by
      rw [exposedSample_adj, hout]
      exact ⟨hne, h⟩
    rwa [← e.out_eq]

/-- The upper event unfolded: `F` embeds into the exposed sample iff every edge coin of
`F` clears its clamped threshold. -/
private theorem le_exposedSample_iff (W : Graphon α μ) {k : ℕ} (F : SimpleGraph (Fin k))
    (x : Fin k → α × (Fin k → ℝ)) :
    F ≤ exposedSample W k x ↔
      ∀ e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset},
        (x (rowIdx e.1)).2 (colIdx e.1) ≤
          clampedRep W ((x (Quot.out e.1).1).1, (x (Quot.out e.1).2).1) := by
  rw [← SimpleGraph.edgeSet_subset_edgeSet]
  constructor
  · intro hsub e
    exact (mem_edgeSet_exposedSample W k x
      (Graphon.edge_out_ne (SimpleGraph.mem_edgeFinset.mp e.2))).mp
      (hsub (SimpleGraph.mem_edgeFinset.mp e.2))
  · intro h s hs
    exact (mem_edgeSet_exposedSample W k x (Graphon.edge_out_ne hs)).mpr
      (h ⟨s, SimpleGraph.mem_edgeFinset.mpr hs⟩)

/-- The mass of a simultaneous coin cylinder over injectively indexed (row, column)
pairs: the product of the individual `uniform01` lower-interval masses. -/
private theorem coinRows_pi_forall_le {k : ℕ} {ι : Type*} [Fintype ι]
    (r c : ι → Fin k) (hinj : Function.Injective fun e => (r e, c e)) (t : ι → ℝ)
    (ht : ∀ e, t e ∈ Set.Icc (0 : ℝ) 1) :
    (Measure.pi fun _ : Fin k => coinRowMeasure k)
        {u : Fin k → Fin k → ℝ | ∀ e, u (r e) (c e) ≤ t e} =
      ∏ e, ENNReal.ofReal (t e) := by
  set S : Fin k → Fin k → Set ℝ :=
    fun i j => {a | ∀ e, r e = i → c e = j → a ≤ t e} with hS
  have hset : {u : Fin k → Fin k → ℝ | ∀ e, u (r e) (c e) ≤ t e} =
      Set.univ.pi fun i => Set.univ.pi fun j => S i j := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, hS]
    constructor
    · rintro h i j e rfl rfl
      exact h e
    · intro h e
      exact h (r e) (c e) e rfl rfl
  have hrow : ∀ i, coinRowMeasure k (Set.univ.pi fun j => S i j) = ∏ j, uniform01 (S i j) :=
    fun i => by rw [coinRowMeasure, Measure.pi_pi]
  rw [hset, Measure.pi_pi]
  simp_rw [hrow]
  -- Reindex the double product over the injective image of the edge set.
  have hS_on : ∀ e, S (r e) (c e) = Set.Iic (t e) := by
    intro e
    ext a
    simp only [hS, Set.mem_setOf_eq, Set.mem_Iic]
    constructor
    · intro h
      exact h e rfl rfl
    · intro h e' hre' hce'
      have he' : e' = e := hinj (Prod.ext hre' hce')
      rw [he']
      exact h
  have hS_off : ∀ i j, (∀ e, (r e, c e) ≠ (i, j)) → S i j = Set.univ := by
    intro i j hij
    refine Set.eq_univ_iff_forall.mpr fun a e hre hce => ?_
    exact absurd (Prod.ext hre hce) (hij e)
  calc (∏ i, ∏ j, uniform01 (S i j))
      = ∏ p : Fin k × Fin k, uniform01 (S p.1 p.2) :=
        (Fintype.prod_prod_type fun p : Fin k × Fin k => uniform01 (S p.1 p.2)).symm
    _ = ∏ p ∈ Finset.univ.image fun e : ι => (r e, c e), uniform01 (S p.1 p.2) := by
        refine (Finset.prod_subset (Finset.subset_univ _) fun p _ hp => ?_).symm
        have hnone : ∀ e, (r e, c e) ≠ p := by
          intro e he
          exact hp (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, he⟩)
        rw [hS_off p.1 p.2 fun e he => hnone e (he.trans (Prod.mk.eta))]
        exact measure_univ
    _ = ∏ e : ι, uniform01 (S (r e) (c e)) :=
        Finset.prod_image fun e _ e' _ h => hinj h
    _ = ∏ e : ι, ENNReal.ofReal (t e) := by
        refine Finset.prod_congr rfl fun e _ => ?_
        rw [hS_on e]
        exact uniform01_Iic (ht e)

/-- A.e. under the finite product, the clamped edge product at the `Quot.out`
representatives equals the homomorphism-density integrand. -/
private theorem ae_clampedProd_eq_integrand' [IsProbabilityMeasure μ] (W : Graphon α μ)
    {k : ℕ} (F : SimpleGraph (Fin k)) :
    ∀ᵐ y ∂Measure.pi (fun _ : Fin k => μ),
      (∏ e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset},
        clampedRep W (y (Quot.out e.1).1, y (Quot.out e.1).2)) =
        Graphon.homDensityIntegrand F W y := by
  have hedge : ∀ e ∈ F.edgeFinset, ∀ᵐ y ∂Measure.pi (fun _ : Fin k => μ),
      clampedRep W (y (Quot.out e).1, y (Quot.out e).2) =
        W.toAEEqFun (y (Quot.out e).1, y (Quot.out e).2) := by
    intro e he
    exact Graphon.ae_pairMap_of_prod _ _
      (Graphon.edge_out_ne (SimpleGraph.mem_edgeFinset.mp he)) (clampedRep_ae_eq W)
  have hall : ∀ᵐ y ∂Measure.pi (fun _ : Fin k => μ), ∀ e ∈ F.edgeFinset,
      clampedRep W (y (Quot.out e).1, y (Quot.out e).2) =
        W.toAEEqFun (y (Quot.out e).1, y (Quot.out e).2) :=
    (Filter.eventually_all_finset F.edgeFinset).mpr hedge
  filter_upwards [hall] with y hy
  calc (∏ e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset},
        clampedRep W (y (Quot.out e.1).1, y (Quot.out e.1).2))
      = ∏ e ∈ F.edgeFinset.attach,
          W.toAEEqFun (y (Quot.out e.1).1, y (Quot.out e.1).2) := by
        rw [Finset.univ_eq_attach]
        exact Finset.prod_congr rfl fun e _ => hy e.1 e.2
    _ = ∏ e ∈ F.edgeFinset,
          W.toAEEqFun (y (Quot.out e).1, y (Quot.out e).2) :=
        Finset.prod_attach F.edgeFinset
          fun e => (W.toAEEqFun (y (Quot.out e).1, y (Quot.out e).2) : ℝ)
    _ = Graphon.homDensityIntegrand F W y := rfl

/-- **The upper-event mass of the exposed-sample law is the homomorphism density**: the
heart of the law identification. Coordinate-split the exposure source with
`MeasurableEquiv.arrowProdEquivProdArrow`, integrate the coins out row by row
(`Measure.pi_pi` twice), and identify the position integral with `homDensity F W`. -/
private theorem map_exposedSample_apply_le_event [IsProbabilityMeasure μ]
    (W : Graphon α μ) {k : ℕ} (F : SimpleGraph (Fin k)) :
    (exposureMeasure μ k).map (exposedSample W k) {G | F ≤ G} =
      ENNReal.ofReal (Graphon.homDensity F W) := by
  rw [Measure.map_apply (measurable_exposedSample W k) ((Set.to_countable _).measurableSet)]
  -- The upper event as a per-edge coin condition.
  have hA : exposedSample W k ⁻¹' {G | F ≤ G} =
      {x : Fin k → α × (Fin k → ℝ) |
        ∀ e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset},
          (x (rowIdx e.1)).2 (colIdx e.1) ≤
            clampedRep W ((x (Quot.out e.1).1).1, (x (Quot.out e.1).2).1)} := by
    ext x
    simpa using le_exposedSample_iff W F x
  -- The coordinate-split event.
  set E' : Set ((Fin k → α) × (Fin k → Fin k → ℝ)) :=
    {p | ∀ e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset},
      p.2 (rowIdx e.1) (colIdx e.1) ≤
        clampedRep W (p.1 (Quot.out e.1).1, p.1 (Quot.out e.1).2)} with hE'
  have hE'meas : MeasurableSet E' := by
    rw [hE', Set.setOf_forall]
    refine MeasurableSet.iInter fun e => ?_
    exact measurableSet_le
      ((measurable_pi_apply (colIdx e.1)).comp
        ((measurable_pi_apply (rowIdx e.1)).comp measurable_snd))
      ((measurable_clampedRep W).comp
        (((measurable_pi_apply _).comp measurable_fst).prodMk
          ((measurable_pi_apply _).comp measurable_fst)))
  have mp := measurePreserving_arrowProdEquivProdArrow α (Fin k → ℝ) (Fin k)
    (fun _ => μ) (fun _ => coinRowMeasure k)
  have hpre : (MeasurableEquiv.arrowProdEquivProdArrow α (Fin k → ℝ) (Fin k)) ⁻¹' E' =
      exposedSample W k ⁻¹' {G | F ≤ G} := by
    rw [hA]
    rfl
  rw [← hpre, show exposureMeasure μ k =
      Measure.pi fun _ : Fin k => (μ.prod (coinRowMeasure k)) from rfl,
    mp.measure_preimage hE'meas.nullMeasurableSet,
    Measure.prod_apply hE'meas]
  -- Integrate the coins out, section by section.
  have hsec : ∀ y : Fin k → α,
      (Measure.pi fun _ : Fin k => coinRowMeasure k) (Prod.mk y ⁻¹' E') =
        ENNReal.ofReal (∏ e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset},
          clampedRep W (y (Quot.out e.1).1, y (Quot.out e.1).2)) := by
    intro y
    have hinj : Function.Injective
        fun e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset} => (rowIdx e.1, colIdx e.1) := by
      intro e e' h
      have h1 : rowIdx e.1 = rowIdx e'.1 := congrArg Prod.fst h
      have h2 : colIdx e.1 = colIdx e'.1 := congrArg Prod.snd h
      exact Subtype.ext (by rw [← mk_colIdx_rowIdx e.1, ← mk_colIdx_rowIdx e'.1, h1, h2])
    have := coinRows_pi_forall_le (fun e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset} =>
        rowIdx e.1) (fun e => colIdx e.1) hinj
      (fun e => clampedRep W (y (Quot.out e.1).1, y (Quot.out e.1).2))
      (fun e => clampedRep_mem_Icc W _)
    rw [show Prod.mk y ⁻¹' E' = {u : Fin k → Fin k → ℝ |
        ∀ e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset}, u (rowIdx e.1) (colIdx e.1) ≤
          clampedRep W (y (Quot.out e.1).1, y (Quot.out e.1).2)} from rfl, this,
      ENNReal.ofReal_prod_of_nonneg fun e _ => (clampedRep_mem_Icc W _).1]
  rw [lintegral_congr hsec]
  -- Identify the position integral with the homomorphism density.
  have hae : (∫⁻ y, ENNReal.ofReal (∏ e : {e : Sym2 (Fin k) // e ∈ F.edgeFinset},
        clampedRep W (y (Quot.out e.1).1, y (Quot.out e.1).2))
        ∂Measure.pi (fun _ : Fin k => μ)) =
      ∫⁻ y, ENNReal.ofReal (Graphon.homDensityIntegrand F W y)
        ∂Measure.pi (fun _ : Fin k => μ) :=
    lintegral_congr_ae ((ae_clampedProd_eq_integrand' W F).mono fun y hy =>
      congrArg ENNReal.ofReal hy)
  rw [hae, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (Graphon.homDensityIntegrand_integrable F W)
      (Graphon.homDensityIntegrand_nonneg_ae F W),
    ← Graphon.homDensity_eq_integral]

/-- **The law identification** (issue #72, item 1, commit 2): the exposed sampled graph
of the exposure source has law exactly `samplePMF W k` — the padded coin rows are
integrated out. Singleton masses via `Measure.ext_of_singleton`, then Möbius inversion
via `Graphon.upperSum_injective` on the upper-event masses. -/
theorem map_exposedSample (W : Graphon α μ) [IsProbabilityMeasure μ] (k : ℕ) :
    (exposureMeasure μ k).map (exposedSample W k) =
      (Graphon.samplePMF W k).toMeasure := by
  set ν : Measure (SimpleGraph (Fin k)) :=
    (exposureMeasure μ k).map (exposedSample W k) with hν
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_exposedSample W k).aemeasurable
  have hq : (fun G => (ν {G}).toReal) = Graphon.sampleMass W := by
    refine Graphon.upperSum_injective fun F => ?_
    have hset : {G : SimpleGraph (Fin k) | F ≤ G} =
        ⋃ G ∈ Finset.univ.filter fun G : SimpleGraph (Fin k) => F ≤ G,
          ({G} : Set (SimpleGraph (Fin k))) := by
      ext G
      simp
    have hsum : ν (⋃ G ∈ Finset.univ.filter fun G : SimpleGraph (Fin k) => F ≤ G,
        ({G} : Set (SimpleGraph (Fin k)))) =
        ∑ G ∈ Finset.univ.filter fun G : SimpleGraph (Fin k) => F ≤ G, ν {G} :=
      measure_biUnion_finset (fun G₁ _ G₂ _ hne => Set.disjoint_singleton.mpr hne)
        fun G _ => measurableSet_singleton G
    have hupper : Graphon.upperSum (fun G => (ν {G}).toReal) F =
        (ν {G | F ≤ G}).toReal := by
      rw [Graphon.upperSum, ← Finset.sum_filter, hset, hsum,
        ENNReal.toReal_sum fun G _ => measure_ne_top ν _]
    rw [hupper, hν, map_exposedSample_apply_le_event W F,
      ENNReal.toReal_ofReal (Graphon.homDensity_nonneg F W),
      ← Graphon.upperSum_sampleMass W F]
  refine Measure.ext_of_singleton fun G => ?_
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton G),
    Graphon.samplePMF_apply, ← congrFun hq G,
    ENNReal.ofReal_toReal (measure_ne_top ν _)]

end Marginal

/-! ### The oscillation bound -/

section Oscillation

/-- Adjacency in the exposed sample reads only the two endpoint states. -/
private theorem exposedSample_adj_congr (W : Graphon α μ) {k : ℕ}
    {x x' : Fin k → α × (Fin k → ℝ)} {u v : Fin k} (hu : x u = x' u) (hv : x v = x' v) :
    ((exposedSample W k x).Adj u v ↔ (exposedSample W k x').Adj u v) := by
  have hmax : x (max u v) = x' (max u v) := by
    rcases max_choice u v with h | h <;> rw [h] <;> assumption
  have ho1 : x (Quot.out s(u, v)).1 = x' (Quot.out s(u, v)).1 := by
    rcases out_mk_eq_or_swap u v with h | h <;> rw [h] <;> assumption
  have ho2 : x (Quot.out s(u, v)).2 = x' (Quot.out s(u, v)).2 := by
    rcases out_mk_eq_or_swap u v with h | h <;> rw [h] <;> assumption
  rw [exposedSample_adj, exposedSample_adj, hmax, ho1, ho2]

/-- Updating an exposed vertex outside the range of a vertex map does not change the
pulled-back sample. -/
private theorem comap_exposedSample_update (W : Graphon α μ) {k : ℕ}
    (x : Fin k → α × (Fin k → ℝ)) {i : Fin k} (b : α × (Fin k → ℝ))
    {q : ℕ} {φ : Fin q → Fin k} (hφ : i ∉ Set.range φ) :
    (exposedSample W k (Function.update x i b)).comap φ =
      (exposedSample W k x).comap φ := by
  ext u v
  simp only [SimpleGraph.comap_adj]
  exact exposedSample_adj_congr W
    (Function.update_of_ne (fun h => hφ ⟨u, h⟩) b x)
    (Function.update_of_ne (fun h => hφ ⟨v, h⟩) b x)

/-- At most `q * k ^ (q - 1)` vertex maps `Fin q → Fin k` contain a given vertex in
their range (union bound over the `q` positions). -/
private theorem card_filter_range_mem_le (q k : ℕ) (i : Fin k) :
    (Finset.univ.filter fun φ : Fin q → Fin k => i ∈ Set.range φ).card ≤
      q * k ^ (q - 1) := by
  have hsub : (Finset.univ.filter fun φ : Fin q → Fin k => i ∈ Set.range φ) ⊆
      Finset.univ.biUnion fun a : Fin q =>
        Finset.univ.filter fun φ : Fin q → Fin k => φ a = i := by
    intro φ hφ
    obtain ⟨a, ha⟩ := (Finset.mem_filter.mp hφ).2
    exact Finset.mem_biUnion.mpr
      ⟨a, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
  refine le_trans (Finset.card_le_card hsub)
    (le_trans Finset.card_biUnion_le (le_of_eq ?_))
  have hcard : ∀ a : Fin q,
      (Finset.univ.filter fun φ : Fin q → Fin k => φ a = i).card = k ^ (q - 1) := by
    intro a
    have e : {φ : Fin q → Fin k // φ a = i} ≃ ({b : Fin q // b ≠ a} → Fin k) :=
      { toFun := fun φ b => φ.1 b.1
        invFun := fun g => ⟨fun b => if h : b = a then i else g ⟨b, h⟩, by simp⟩
        left_inv := by
          rintro ⟨φ, hφ⟩
          refine Subtype.ext (funext fun b => ?_)
          by_cases hb : b = a
          · subst hb; simpa using hφ.symm
          · simp [hb]
        right_inv := fun g => funext fun b => by
          simp [b.2] }
    have hne : Fintype.card {b : Fin q // b ≠ a} = q - 1 := by
      have hc := Fintype.card_subtype_compl (fun b : Fin q => b = a)
      rwa [Fintype.card_subtype_eq, Fintype.card_fin] at hc
    rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin,
      hne]
  calc (∑ a : Fin q,
        (Finset.univ.filter fun φ : Fin q → Fin k => φ a = i).card)
      = ∑ _a : Fin q, k ^ (q - 1) := Finset.sum_congr rfl fun a _ => hcard a
    _ = q * k ^ (q - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

variable [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

/-- The hom-density of the embedded exposed sample is a measurable function of the
exposure state (any function out of the countable discrete graph space is). -/
theorem measurable_homDensity_exposedSample (W : Graphon α μ) {k : ℕ} [NeZero k]
    {q : ℕ} (F : SimpleGraph (Fin q)) [DecidableRel F.Adj] :
    Measurable fun x : Fin k → α × (Fin k → ℝ) =>
      Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
        (exposedSample W k x)) := by
  have h : Measurable fun G : SimpleGraph (Fin k) =>
      Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ) G) :=
    measurable_of_countable _
  exact h.comp (measurable_exposedSample W k)

/-- **The oscillation bound** (issue #72, item 1, commit 2): updating one exposed
vertex moves the hom-density of a fixed `F` on `q` vertices by at most `q / k` — only
the at most `q * k ^ (q - 1)` vertex maps whose range contains the updated vertex can
change upper-event status (`homDensity_ofSimpleGraphOn`). This is the bounded-differences
hypothesis of `ProbabilityTheory.hasSubgaussianMGF_of_bounded_differences`, stated for
the exact function fed to it. -/
theorem abs_homDensity_exposedSample_update_le (W : Graphon α μ) {k : ℕ} [NeZero k]
    {q : ℕ} (F : SimpleGraph (Fin q)) [DecidableRel F.Adj]
    (x : Fin k → α × (Fin k → ℝ)) (i : Fin k) (b : α × (Fin k → ℝ)) :
    |Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
        (exposedSample W k (Function.update x i b))) -
      Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
        (exposedSample W k x))| ≤ (q : ℝ) / k := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  rw [Graphon.homDensity_ofSimpleGraphOn, Graphon.homDensity_ofSimpleGraphOn,
    ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k : ℝ)⁻¹) ^ q)]
  -- Termwise: maps avoiding `i` do not change status; the rest move by at most 1.
  have hterm : ∀ φ : Fin q → Fin k,
      |(if F ≤ (exposedSample W k (Function.update x i b)).comap φ then (1 : ℝ) else 0) -
        (if F ≤ (exposedSample W k x).comap φ then (1 : ℝ) else 0)| ≤
        if i ∈ Set.range φ then (1 : ℝ) else 0 := by
    intro φ
    by_cases hφ : i ∈ Set.range φ
    · rw [if_pos hφ]
      split_ifs <;> norm_num
    · rw [if_neg hφ, comap_exposedSample_update W x b hφ, sub_self, abs_zero]
  have hsum : |∑ φ : Fin q → Fin k,
      ((if F ≤ (exposedSample W k (Function.update x i b)).comap φ then (1 : ℝ) else 0) -
        (if F ≤ (exposedSample W k x).comap φ then (1 : ℝ) else 0))| ≤
      (q : ℝ) * (k : ℝ) ^ (q - 1) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _)
      (le_trans (Finset.sum_le_sum fun φ _ => hterm φ) ?_)
    rw [Finset.sum_boole]
    have := card_filter_range_mem_le q k i
    calc ((Finset.univ.filter fun φ : Fin q → Fin k => i ∈ Set.range φ).card : ℝ)
        ≤ ((q * k ^ (q - 1) : ℕ) : ℝ) := Nat.cast_le.mpr this
      _ = (q : ℝ) * (k : ℝ) ^ (q - 1) := by push_cast; ring
  refine le_trans (mul_le_mul_of_nonneg_left hsum (by positivity)) ?_
  -- Arithmetic: `k⁻ᑫ · q · k^(q-1) ≤ q / k`.
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp
  · have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkpos
    have hpow : (k : ℝ) ^ q = (k : ℝ) ^ (q - 1) * k := by
      rw [← pow_succ, Nat.sub_add_cancel hq]
    have heq : ((k : ℝ)⁻¹) ^ q * ((q : ℝ) * (k : ℝ) ^ (q - 1)) = (q : ℝ) / k := by
      rw [inv_pow, hpow]
      field_simp
    exact le_of_eq heq

end Oscillation

/-! ### The fixed-`F` exponential concentration tail -/

section ConcentrationTail

variable [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

omit [StandardBorelSpace α] [NoAtoms μ] in
/-- Hom-densities of a graph on no vertices are constantly `1` (empty edge product). -/
private theorem homDensity_fin_zero (F : SimpleGraph (Fin 0)) [DecidableRel F.Adj]
    (X : Graphon α μ) : Graphon.homDensity F X = 1 := by
  have hemp : F.edgeFinset = ∅ :=
    Finset.eq_empty_of_forall_notMem fun e he => (Quot.out e).1.elim0
  simp [Graphon.homDensity_eq_integral, Graphon.homDensityIntegrand, hemp]

/-- The exposure expectation of the embedded hom-density is its expectation under the
finite sample law (change of variables along the law identification). -/
private theorem integral_homDensity_exposedSample (W : Graphon α μ) {q : ℕ}
    (F : SimpleGraph (Fin q)) [DecidableRel F.Adj] (k : ℕ) [NeZero k] :
    (∫ x, Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
        (exposedSample W k x)) ∂exposureMeasure μ k) =
      ∫ G, Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ) G)
        ∂(Graphon.samplePMF W k).toMeasure := by
  have hg : Measurable fun G : SimpleGraph (Fin k) =>
      Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ) G) :=
    measurable_of_countable _
  rw [← map_exposedSample W k,
    integral_map (measurable_exposedSample W k).aemeasurable hg.aestronglyMeasurable]

/-- **The bias bound**: the mean of the embedded hom-density under the finite sample
law at size `n + 1` is within `q² / (n + 1)` of `homDensity F W` — the public collision
estimate specialized to `sampleExchangeableLaw W`, whose upper-mass side is
`homDensity F W` by the forward Möbius identity `upperSum_sampleMass`. -/
private theorem abs_integral_homDensity_samplePMF_sub_le (W : Graphon α μ) {q : ℕ}
    (F : SimpleGraph (Fin q)) [DecidableRel F.Adj] (n : ℕ) :
    |(∫ G, Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ) G)
        ∂(Graphon.samplePMF W (n + 1)).toMeasure) - Graphon.homDensity F W| ≤
      (q * q : ℝ) / (n + 1) := by
  have hcol := GraphonSpace.abs_integral_homDensityCoord_empiricalMixing_sub_le
    (α := α) (μ := μ) (Graphon.sampleExchangeableLaw W) n F
  have hcoord : ∀ G : SimpleGraph (Fin (n + 1)),
      GraphonSpace.homDensityCoord F (GraphonSpace.graphClass (α := α) (μ := μ) G) =
        Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ) G) := by
    intro G
    show GraphonSpace.homDensityCoord F
      (GraphonSpace.mk (Graphon.ofSimpleGraphOn G)) = _
    rw [GraphonSpace.homDensityCoord_mk]
    exact Graphon.homDensity_congr_decRel F _ _ _
  have h1 : (∫ x, GraphonSpace.homDensityCoord F x
      ∂(GraphonSpace.empiricalMixing (α := α) (μ := μ)
        (Graphon.sampleExchangeableLaw W) (n + 1) : Measure (GraphonSpace α μ))) =
      ∫ G, Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ) G)
        ∂(Graphon.samplePMF W (n + 1)).toMeasure := by
    rw [GraphonSpace.empiricalMixing_coe,
      integral_map (measurable_of_countable _).aemeasurable
        (GraphonSpace.continuous_homDensityCoord F).aestronglyMeasurable]
    simp only [hcoord]
    rfl
  have h2 : (∑ G : SimpleGraph (Fin q),
      if F ≤ G then ((Graphon.sampleExchangeableLaw W).law q G).toReal else 0) =
      Graphon.homDensity F W := by
    rw [← Graphon.upperSum_sampleMass W F, Graphon.upperSum]
    refine Finset.sum_congr rfl fun G _ => ?_
    split_ifs
    · exact Graphon.samplePMF_apply_toReal W q G
    · rfl
  rw [h1, h2] at hcol
  exact hcol

/-- **Exponential concentration of the sampled hom-density, fixed `F`** (issue #72,
item 1; toward Lovász Cor 10.4): for a fixed graph `F` on `q` vertices and a sample
size `k` with `2q² ≤ εk` (so that the collision bias `q²/k` is at most `ε/2`), the
probability under the sample law `G(k, W)` that the hom-density of `F` deviates from
`t(F, W)` by at least `ε` is at most `2 exp(−ε²k / (2q²))`.

Both tails come from `ProbabilityTheory.hasSubgaussianMGF_of_bounded_differences`
applied to the padded vertex exposure (variance proxy `q²/(4k)`), centered at the
sample mean; the center moves to `t(F, W)` by the collision estimate. For `q = 0`
the density is constantly `1` and the tail set is empty. -/
theorem _root_.Graphon.measureReal_abs_homDensity_sampled_sub_le (W : Graphon α μ)
    {q : ℕ} (F : SimpleGraph (Fin q)) [DecidableRel F.Adj] {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} [NeZero k] (hk : 2 * (q : ℝ) ^ 2 ≤ ε * k) :
    ((Graphon.samplePMF W k).toMeasure).real
      {G | ε ≤ |Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ) G) -
        Graphon.homDensity F W|} ≤
      2 * Real.exp (-(ε ^ 2 * k) / (2 * (q : ℝ) ^ 2)) := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · -- `q = 0`: the density is constantly 1 and the tail set is empty.
    subst hq
    have hset : {G : SimpleGraph (Fin k) |
        ε ≤ |Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ) G) -
          Graphon.homDensity F W|} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun G hG => ?_
      rw [Set.mem_setOf_eq, homDensity_fin_zero F, homDensity_fin_zero F, sub_self,
        abs_zero] at hG
      exact absurd hG (not_le.mpr hε)
    rw [hset, measureReal_empty]
    positivity
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
    have hq0 : ((q : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hq)
    have hn0 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    have hn0' : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    -- The centered hom-density of the exposed sample is sub-Gaussian.
    have hsub := ProbabilityTheory.hasSubgaussianMGF_of_bounded_differences
      (exposureVertexMeasure μ (n + 1))
      (fun x => Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
        (exposedSample W (n + 1) x)))
      (measurable_homDensity_exposedSample W F)
      ((q : ℝ) / ((n + 1 : ℕ) : ℝ)) (by positivity)
      (fun x i b => abs_homDensity_exposedSample_update_le W F x i b)
    rw [show (Measure.pi fun _ : Fin (n + 1) => exposureVertexMeasure μ (n + 1)) =
      exposureMeasure μ (n + 1) from rfl] at hsub
    -- Chernoff, both tails, at deviation `ε / 2`.
    have htail₁ := hsub.measure_ge_le (ε := ε / 2) (le_of_lt (half_pos hε))
    have htail₂ := hsub.neg.measure_ge_le (ε := ε / 2) (le_of_lt (half_pos hε))
    -- The exponent, explicitly.
    have hc₀ : ((((n + 1 : ℕ) : ℝ≥0) *
        (Real.toNNReal ((q : ℝ) / ((n + 1 : ℕ) : ℝ)) / 2) ^ 2 : ℝ≥0) : ℝ) =
        ((n + 1 : ℕ) : ℝ) * (((q : ℝ) / ((n + 1 : ℕ) : ℝ)) / 2) ^ 2 := by
      rw [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_div,
        Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ (q : ℝ) / ((n + 1 : ℕ) : ℝ)),
        NNReal.coe_natCast, NNReal.coe_ofNat]
    have hexp : -(ε / 2) ^ 2 / (2 * ((((n + 1 : ℕ) : ℝ≥0) *
        (Real.toNNReal ((q : ℝ) / ((n + 1 : ℕ) : ℝ)) / 2) ^ 2 : ℝ≥0) : ℝ)) =
        -(ε ^ 2 * ((n + 1 : ℕ) : ℝ)) / (2 * (q : ℝ) ^ 2) := by
      rw [hc₀]
      field_simp
    -- The bias: the sample mean is within `ε / 2` of `t(F, W)`.
    have hbias : |(∫ y, Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
        (exposedSample W (n + 1) y)) ∂exposureMeasure μ (n + 1)) -
        Graphon.homDensity F W| ≤ ε / 2 := by
      rw [integral_homDensity_exposedSample W F (n + 1)]
      refine le_trans (abs_integral_homDensity_samplePMF_sub_le W F n) ?_
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      push_cast at hk ⊢
      nlinarith [hk]
    -- Transfer to the exposure source and split into the two tails.
    have hA : MeasurableSet {G : SimpleGraph (Fin (n + 1)) |
        ε ≤ |Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ) G) -
          Graphon.homDensity F W|} := (Set.to_countable _).measurableSet
    rw [← map_exposedSample W (n + 1),
      map_measureReal_apply (measurable_exposedSample W (n + 1)) hA]
    have hincl : exposedSample W (n + 1) ⁻¹'
        {G | ε ≤ |Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ) G) -
          Graphon.homDensity F W|} ⊆
        {x | ε / 2 ≤ Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
            (exposedSample W (n + 1) x)) -
          ∫ y, Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
            (exposedSample W (n + 1) y)) ∂exposureMeasure μ (n + 1)} ∪
        {x | ε / 2 ≤ -(Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
            (exposedSample W (n + 1) x)) -
          ∫ y, Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
            (exposedSample W (n + 1) y)) ∂exposureMeasure μ (n + 1))} := by
      intro x hx
      rw [Set.mem_preimage, Set.mem_setOf_eq] at hx
      set fx := Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
        (exposedSample W (n + 1) x)) with hfx
      set I := ∫ y, Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
        (exposedSample W (n + 1) y)) ∂exposureMeasure μ (n + 1) with hI
      have habs : ε / 2 ≤ |fx - I| := by
        have htri : |fx - Graphon.homDensity F W| ≤ |fx - I| +
            |I - Graphon.homDensity F W| := abs_sub_le _ _ _
        have := abs_nonneg (fx - I)
        linarith [hbias, hx]
      rcases le_abs.mp habs with h | h
      · exact Or.inl h
      · exact Or.inr h
    calc (exposureMeasure μ (n + 1)).real (exposedSample W (n + 1) ⁻¹'
        {G | ε ≤ |Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ) G) -
          Graphon.homDensity F W|})
        ≤ (exposureMeasure μ (n + 1)).real
            ({x | ε / 2 ≤ Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
                (exposedSample W (n + 1) x)) -
              ∫ y, Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
                (exposedSample W (n + 1) y)) ∂exposureMeasure μ (n + 1)} ∪
            {x | ε / 2 ≤ -(Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
                (exposedSample W (n + 1) x)) -
              ∫ y, Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
                (exposedSample W (n + 1) y)) ∂exposureMeasure μ (n + 1))}) :=
          measureReal_mono hincl
      _ ≤ (exposureMeasure μ (n + 1)).real
            {x | ε / 2 ≤ Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
                (exposedSample W (n + 1) x)) -
              ∫ y, Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
                (exposedSample W (n + 1) y)) ∂exposureMeasure μ (n + 1)} +
          (exposureMeasure μ (n + 1)).real
            {x | ε / 2 ≤ -(Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
                (exposedSample W (n + 1) x)) -
              ∫ y, Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
                (exposedSample W (n + 1) y)) ∂exposureMeasure μ (n + 1))} :=
          measureReal_union_le _ _
      _ ≤ Real.exp (-(ε / 2) ^ 2 / (2 * ((((n + 1 : ℕ) : ℝ≥0) *
              (Real.toNNReal ((q : ℝ) / ((n + 1 : ℕ) : ℝ)) / 2) ^ 2 : ℝ≥0) : ℝ))) +
          Real.exp (-(ε / 2) ^ 2 / (2 * ((((n + 1 : ℕ) : ℝ≥0) *
              (Real.toNNReal ((q : ℝ) / ((n + 1 : ℕ) : ℝ)) / 2) ^ 2 : ℝ≥0) : ℝ))) :=
          add_le_add htail₁ htail₂
      _ = 2 * Real.exp (-(ε ^ 2 * ((n + 1 : ℕ) : ℝ)) / (2 * (q : ℝ) ^ 2)) := by
          rw [hexp]
          ring

/-- The fixed-`F` tail for the **explicit sampler**: the same bound for the event that
the hom-density of the first-`k`-vertices restriction of the sampled infinite graph
deviates from `t(F, W)`, via the finite marginal identification
`map_sampleInfinite_restrictFin`. -/
theorem samplerSource_abs_homDensity_restrictFin_sub_le (W : Graphon α μ)
    {q : ℕ} (F : SimpleGraph (Fin q)) [DecidableRel F.Adj] {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} [NeZero k] (hk : 2 * (q : ℝ) ^ 2 ≤ ε * k) :
    (samplerSource μ).real
      {ω | ε ≤ |Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
        (restrictFin k (sampleInfinite W ω))) - Graphon.homDensity F W|} ≤
      2 * Real.exp (-(ε ^ 2 * k) / (2 * (q : ℝ) ^ 2)) := by
  have hmeas : Measurable (restrictFin k ∘ sampleInfinite W) :=
    (measurable_restrictFin k).comp (measurable_sampleInfinite W)
  have hA : MeasurableSet {G : SimpleGraph (Fin k) |
      ε ≤ |Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ) G) -
        Graphon.homDensity F W|} := (Set.to_countable _).measurableSet
  have h := Graphon.measureReal_abs_homDensity_sampled_sub_le W F hε (k := k) hk
  rw [← map_sampleInfinite_restrictFin W k, map_measureReal_apply hmeas hA] at h
  exact h

/-- **The summability bridge** (issue #72, item 1; consumed by the Borel–Cantelli
assembly of issue #71 via `MeasureTheory.ae_eventually_notMem`): for each fixed `ε > 0`,
the total sampler-source mass of the fixed-`F` deviation events at sizes `n + 1` is
finite — finitely many initial terms are bounded by `1`, the rest decay geometrically. -/
theorem tsum_samplerSource_homDensity_tail_ne_top (W : Graphon α μ)
    {q : ℕ} (F : SimpleGraph (Fin q)) [DecidableRel F.Adj] {ε : ℝ} (hε : 0 < ε) :
    (∑' n : ℕ, samplerSource μ
      {ω | ε ≤ |Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
        (restrictFin (n + 1) (sampleInfinite W ω))) - Graphon.homDensity F W|}) ≠ ∞ := by
  have hofReal : ∀ n : ℕ, samplerSource μ
      {ω | ε ≤ |Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
        (restrictFin (n + 1) (sampleInfinite W ω))) - Graphon.homDensity F W|} =
      ENNReal.ofReal ((samplerSource μ).real
        {ω | ε ≤ |Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
          (restrictFin (n + 1) (sampleInfinite W ω))) - Graphon.homDensity F W|}) :=
    fun n => (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hsummable : Summable fun n : ℕ => (samplerSource μ).real
      {ω | ε ≤ |Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
        (restrictFin (n + 1) (sampleInfinite W ω))) - Graphon.homDensity F W|} := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · -- `q = 0`: every deviation event is empty.
      subst hq
      have hzero : ∀ n : ℕ, (samplerSource μ).real
          {ω | ε ≤ |Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
            (restrictFin (n + 1) (sampleInfinite W ω))) - Graphon.homDensity F W|} = 0 := by
        intro n
        have hset : {ω : (ℕ → α) × (EdgeIndex → ℝ) |
            ε ≤ |Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
              (restrictFin (n + 1) (sampleInfinite W ω))) - Graphon.homDensity F W|} =
            ∅ := by
          refine Set.eq_empty_iff_forall_notMem.mpr fun ω hω => ?_
          rw [Set.mem_setOf_eq, homDensity_fin_zero F, homDensity_fin_zero F, sub_self,
            abs_zero] at hω
          exact absurd hω (not_le.mpr hε)
        rw [hset, measureReal_empty]
      exact (summable_congr fun n => (hzero n).symm).mp summable_zero
    · -- `q ≥ 1`: geometric decay beyond the bias threshold.
      have hq0 : ((q : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hq)
      set N := ⌈2 * (q : ℝ) ^ 2 / ε⌉₊ with hN
      rw [← summable_nat_add_iff N]
      refine Summable.of_nonneg_of_le
        (f := fun n : ℕ => 2 * Real.exp (-(ε ^ 2 * ((n + N + 1 : ℕ) : ℝ)) /
          (2 * (q : ℝ) ^ 2)))
        (fun n => measureReal_nonneg) (fun n => ?_) ?_
      · -- the tail bound applies at size `n + N + 1`
        refine samplerSource_abs_homDensity_restrictFin_sub_le W F hε ?_
        have h1 : 2 * (q : ℝ) ^ 2 / ε ≤ (N : ℝ) := Nat.le_ceil _
        have h2 : (N : ℝ) ≤ ((n + N + 1 : ℕ) : ℝ) := by push_cast; linarith
        have h3 := (div_le_iff₀ hε).mp (le_trans h1 h2)
        linarith
      · -- summability of the geometric bound
        have hcpos : (0 : ℝ) < ε ^ 2 / (2 * (q : ℝ) ^ 2) := by positivity
        have hsum := Real.summable_exp_nat_mul_of_ge
          (c := -(ε ^ 2 / (2 * (q : ℝ) ^ 2))) (neg_lt_zero.mpr hcpos)
          (f := fun i : ℕ => (i : ℝ) + N + 1)
          (fun i => by linarith [Nat.cast_nonneg (α := ℝ) N])
        refine ((hsum.mul_left 2).congr fun n => ?_)
        have harg : -(ε ^ 2 / (2 * (q : ℝ) ^ 2)) * ((n : ℝ) + N + 1) =
            -(ε ^ 2 * ((n + N + 1 : ℕ) : ℝ)) / (2 * (q : ℝ) ^ 2) := by
          push_cast
          ring
        rw [harg]
  calc (∑' n : ℕ, samplerSource μ
      {ω | ε ≤ |Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
        (restrictFin (n + 1) (sampleInfinite W ω))) - Graphon.homDensity F W|})
      = ∑' n : ℕ, ENNReal.ofReal ((samplerSource μ).real
          {ω | ε ≤ |Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
            (restrictFin (n + 1) (sampleInfinite W ω))) - Graphon.homDensity F W|}) :=
        tsum_congr hofReal
    _ ≠ ∞ := hsummable.tsum_ofReal_ne_top

end ConcentrationTail

end InfiniteGraph
