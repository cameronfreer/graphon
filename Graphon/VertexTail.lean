/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.EmpiricalGraphon
import Graphon.LimitGraphon
import Graphon.SamplingFinite

/-!
# Vertex-tail infrastructure (issue #97, Campaign A, PR 2)

Tail restriction of infinite graphs, finite-deletion stability of empirical-graphon
limits, and tail measurability of the universal empirical limit:

* `GraphonSpace.graphClass_comap_perm` — the graphon class of a finite graph is
  invariant under vertex permutations (hom densities are map averages, and
  precomposition by a permutation is a bijection on maps);
* `InfiniteGraph.drop` — the tail restriction: the graph induced on `{k, k+1, …}`,
  reindexed to `ℕ`; continuous and measurable, with the window identity
  `restrictFin_drop`;
* `InfiniteGraph.tailAlgebra` / `InfiniteGraph.vertexTailAlgebra` — the σ-algebra of
  events depending only on the graph on `{k, k+1, …}`, and their infimum over `k`;
* `GraphonSpace.abs_homDensity_drop_window_sub_le` — **the counting comparison**: the
  hom density of a window of the `k`-tail differs from that of the enlarged window of
  the original graph by at most `q·k/(n+1)`;
* `GraphonSpace.tendsto_empiricalGraphon_drop_iff` — **finite-deletion stability**:
  the empirical graphons of the `k`-tail converge to `x` iff those of the original
  graph do;
* `GraphonSpace.limitGraphon_drop` — the universal empirical limit is invariant under
  tail restriction, pointwise everywhere;
* `GraphonSpace.measurable_limitGraphon_vertexTailAlgebra` — **the empirical limit is
  vertex-tail measurable** — the key input for the tail-triviality step of issue #91.
-/

open MeasureTheory InfiniteGraph Filter

open scoped Classical Topology

/-! ### Permutation invariance of the finite graph classes -/

namespace GraphonSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

/-- **Permutation invariance of the graphon class of a finite graph**: relabeling the
vertices by a permutation does not change the graphon class. Hom densities in an
embedded finite graph are map averages (`homDensity_ofSimpleGraphOn`), and
precomposition by a permutation is a bijection on vertex maps. -/
theorem graphClass_comap_perm {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n))
    (H : SimpleGraph (Fin n)) :
    graphClass (α := α) (μ := μ) (H.comap σ) = graphClass H := by
  refine (mk_eq_mk_iff _ _).mpr
    (Graphon.weaklyIsomorphic_of_homDensity_eq _ _ fun k F _ => ?_)
  rw [Graphon.homDensity_ofSimpleGraphOn, Graphon.homDensity_ofSimpleGraphOn]
  congr 1
  refine Fintype.sum_equiv (Equiv.piCongrRight fun _ : Fin k => σ) _ _ fun f => ?_
  rw [SimpleGraph.comap_comap]
  rfl

end GraphonSpace

/-! ### Tail restriction and the vertex-tail σ-algebra -/

namespace InfiniteGraph

/-- **Tail restriction**: the graph induced on the vertices `{k, k+1, …}`, reindexed
to `ℕ`. -/
def drop (k : ℕ) (G : InfiniteGraph) : InfiniteGraph :=
  ((G : SimpleGraph ℕ).comap (· + k) : SimpleGraph ℕ)

@[simp] theorem drop_adj (k : ℕ) (G : InfiniteGraph) (a b : ℕ) :
    (drop k G : SimpleGraph ℕ).Adj a b ↔ (G : SimpleGraph ℕ).Adj (a + k) (b + k) :=
  Iff.rfl

@[simp] theorem drop_zero (G : InfiniteGraph) : drop 0 G = G := by
  show ((G : SimpleGraph ℕ).comap (· + 0) : SimpleGraph ℕ) = (G : SimpleGraph ℕ)
  ext a b
  simp

/-- Tail restrictions compose additively. -/
theorem drop_drop (k l : ℕ) (G : InfiniteGraph) :
    drop k (drop l G) = drop (k + l) G := by
  show (((G : SimpleGraph ℕ).comap (· + l)).comap (· + k) : SimpleGraph ℕ) =
    (G : SimpleGraph ℕ).comap (· + (k + l))
  ext a b
  simp

/-- Edge membership under tail restriction, in `Sym2` form. -/
theorem mem_edgeSet_drop (k : ℕ) (G : InfiniteGraph) (s : Sym2 ℕ) :
    s ∈ (drop k G : SimpleGraph ℕ).edgeSet ↔
      Sym2.map (· + k) s ∈ (G : SimpleGraph ℕ).edgeSet := by
  induction s using Sym2.ind with
  | _ a b => simp [SimpleGraph.mem_edgeSet, drop]

/-- The edge-index action of the tail shift. -/
def dropEdgeIndexMap (k : ℕ) (e : EdgeIndex) : EdgeIndex :=
  ⟨Sym2.map (· + k) (e : Sym2 ℕ), by
    obtain ⟨s, hs⟩ := e
    induction s using Sym2.ind with
    | _ a b =>
      simp only [Sym2.map_mk, Sym2.mk_isDiag_iff] at hs ⊢
      omega⟩

/-- Tail restriction is continuous: each output edge coordinate is an input edge
coordinate. -/
theorem continuous_drop (k : ℕ) : Continuous (drop k) := by
  rw [continuous_induced_rng]
  rw [show (coordEquiv ∘ drop k : InfiniteGraph → EdgeIndex → Bool) =
      fun G e => coordEquiv G (dropEdgeIndexMap k e) from
    funext fun G => funext fun e => by
      simp only [Function.comp_apply, coordEquiv_apply, dropEdgeIndexMap,
        mem_edgeSet_drop]]
  exact continuous_pi fun e =>
    (continuous_apply (dropEdgeIndexMap k e)).comp coordHomeomorph.continuous

theorem measurable_drop (k : ℕ) : Measurable (drop k) :=
  (continuous_drop k).measurable

/-- **The window identity**: the first `m` vertices of the `k`-tail form the graph
induced on the vertices `{k, …, m + k − 1}` of the original graph. -/
theorem restrictFin_drop (m k : ℕ) (G : InfiniteGraph) :
    restrictFin m (drop k G) = (restrictFin (m + k) G).comap (Fin.addNatEmb k) := by
  ext a b
  simp [restrictFin, drop, SimpleGraph.comap_adj]

/-- **The tail σ-algebra at level `k`**: events depending only on the graph induced on
the vertices `{k, k+1, …}` (the tail restriction `drop k` sees exactly the tail-induced
subgraph, reindexed). -/
@[reducible] noncomputable def tailAlgebra (k : ℕ) : MeasurableSpace InfiniteGraph :=
  MeasurableSpace.comap (drop k) inferInstance

/-- Each tail σ-algebra is a sub-σ-algebra of the Borel σ-algebra. -/
theorem tailAlgebra_le (k : ℕ) :
    tailAlgebra k ≤ (inferInstance : MeasurableSpace InfiniteGraph) :=
  measurable_iff_comap_le.mp (measurable_drop k)

/-- **The vertex-tail σ-algebra** `⋂ₖ σ(G|{k, k+1, …})`: events depending only on
arbitrarily late vertex tails. -/
@[reducible] noncomputable def vertexTailAlgebra : MeasurableSpace InfiniteGraph :=
  ⨅ k, tailAlgebra k

theorem vertexTailAlgebra_le_tailAlgebra (k : ℕ) :
    vertexTailAlgebra ≤ tailAlgebra k :=
  iInf_le _ k

theorem vertexTailAlgebra_le :
    vertexTailAlgebra ≤ (inferInstance : MeasurableSpace InfiniteGraph) :=
  (vertexTailAlgebra_le_tailAlgebra 0).trans (tailAlgebra_le 0)

end InfiniteGraph

/-! ### Finite-deletion stability of empirical limits -/

namespace GraphonSpace

/-- The pure arithmetic core of the counting comparison: if `A` counts a subfamily of
the `S`-family, with `A ≤ a^q`, `S − A ≤ b^q − a^q`, and `b − a ≤ k`, then the
normalized counts `A/a^q` and `S/b^q` differ by at most `q·k/a`. -/
private theorem abs_inv_pow_mul_sub_le {a b A S : ℝ} (q k : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) (hba : b - a ≤ k) (hA0 : 0 ≤ A) (hAa : A ≤ a ^ q)
    (hAS : A ≤ S) (hSA : S - A ≤ b ^ q - a ^ q) :
    |a⁻¹ ^ q * A - b⁻¹ ^ q * S| ≤ q * k / a := by
  have hu : (0:ℝ) < a ^ q := pow_pos ha q
  have hv : (0:ℝ) < b ^ q := pow_pos hb q
  have huv : a ^ q ≤ b ^ q := pow_le_pow_left₀ ha.le hab q
  have hinvle : (b ^ q)⁻¹ ≤ (a ^ q)⁻¹ := by
    have h6 : (a ^ q)⁻¹ - (b ^ q)⁻¹ = (b ^ q - a ^ q) / (a ^ q * b ^ q) := by
      field_simp
    have h7 : 0 ≤ (b ^ q - a ^ q) / (a ^ q * b ^ q) :=
      div_nonneg (by linarith) (mul_nonneg hu.le hv.le)
    rw [← h6] at h7
    linarith
  -- both normalized counts lie in a common interval of length `1 − aᑫ/bᑫ`
  have hmain : |a⁻¹ ^ q * A - b⁻¹ ^ q * S| ≤ 1 - a ^ q * (b ^ q)⁻¹ := by
    rw [inv_pow, inv_pow]
    have hkey : (a ^ q)⁻¹ * A - (b ^ q)⁻¹ * S =
        A * ((a ^ q)⁻¹ - (b ^ q)⁻¹) - (S - A) * (b ^ q)⁻¹ := by ring
    rw [hkey]
    have hP0 : 0 ≤ A * ((a ^ q)⁻¹ - (b ^ q)⁻¹) := mul_nonneg hA0 (by linarith)
    have hP1 : A * ((a ^ q)⁻¹ - (b ^ q)⁻¹) ≤ 1 - a ^ q * (b ^ q)⁻¹ := by
      have h1 : A * ((a ^ q)⁻¹ - (b ^ q)⁻¹) ≤ a ^ q * ((a ^ q)⁻¹ - (b ^ q)⁻¹) :=
        mul_le_mul_of_nonneg_right hAa (by linarith)
      have h2 : a ^ q * ((a ^ q)⁻¹ - (b ^ q)⁻¹) = 1 - a ^ q * (b ^ q)⁻¹ := by
        rw [mul_sub, mul_inv_cancel₀ hu.ne']
      linarith
    have hQ0 : 0 ≤ (S - A) * (b ^ q)⁻¹ :=
      mul_nonneg (by linarith) (inv_nonneg.mpr hv.le)
    have hQ1 : (S - A) * (b ^ q)⁻¹ ≤ 1 - a ^ q * (b ^ q)⁻¹ := by
      have h1 : (S - A) * (b ^ q)⁻¹ ≤ (b ^ q - a ^ q) * (b ^ q)⁻¹ :=
        mul_le_mul_of_nonneg_right hSA (inv_nonneg.mpr hv.le)
      have h2 : (b ^ q - a ^ q) * (b ^ q)⁻¹ = 1 - a ^ q * (b ^ q)⁻¹ := by
        rw [sub_mul, mul_inv_cancel₀ hv.ne']
      linarith
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- Bernoulli: `1 − (a/b)ᑫ ≤ q·(1 − a/b) ≤ q·k/b ≤ q·k/a`
  have hratio : a ^ q * (b ^ q)⁻¹ = (a / b) ^ q := by rw [div_pow, div_eq_mul_inv]
  have h2 : 1 - a / b ≤ (k:ℝ) / b := by
    have h3 : 0 ≤ ((k:ℝ) - (b - a)) / b := div_nonneg (by linarith) hb.le
    have h4 : ((k:ℝ) - (b - a)) / b = (k:ℝ) / b - (1 - a / b) := by
      field_simp
    rw [h4] at h3
    linarith
  have hbern : 1 - (a / b) ^ q ≤ (q:ℝ) * (1 - a / b) := by
    have hr0 : (0:ℝ) ≤ a / b := div_nonneg ha.le hb.le
    have h := one_add_mul_le_pow (a := a / b - 1) (by linarith) q
    have h1 : (1 : ℝ) + (a / b - 1) = a / b := by ring
    rw [h1] at h
    have h5 : (q:ℝ) * (a / b - 1) = -((q:ℝ) * (1 - a / b)) := by ring
    linarith
  calc |a⁻¹ ^ q * A - b⁻¹ ^ q * S| ≤ 1 - a ^ q * (b ^ q)⁻¹ := hmain
    _ = 1 - (a / b) ^ q := by rw [hratio]
    _ ≤ (q:ℝ) * (1 - a / b) := hbern
    _ ≤ (q:ℝ) * ((k:ℝ) / b) := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg q)
    _ = (q:ℝ) * k / b := by ring
    _ ≤ (q:ℝ) * k / a := div_le_div_of_nonneg_left (by positivity) ha hab

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

/-- **The counting comparison**: the hom density of a size-`(n+1)` window of the
`k`-tail differs from that of the size-`(n+k+1)` window of the original graph by at
most `q·k/(n+1)`. Both densities are normalized map counts
(`homDensity_ofSimpleGraphOn`); the shift `f ↦ f + k` injects the tail-window maps into
the big-window maps, the missing maps (those hitting the first `k` vertices) number at
most `(n+k+1)^q − (n+1)^q`, and the normalization mismatch is controlled by
Bernoulli's inequality. -/
theorem abs_homDensity_drop_window_sub_le {q : ℕ} (F : SimpleGraph (Fin q))
    [DecidableRel F.Adj] (k n : ℕ) (G : InfiniteGraph) :
    |Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
        (restrictFin (n + 1) (drop k G))) -
      Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
        (restrictFin (n + k + 1) G))| ≤ q * k / (n + 1) := by
  classical
  set H : SimpleGraph (Fin (n + k + 1)) := restrictFin (n + k + 1) G with hH
  -- the map-shift injection into the big window
  set g : (Fin q → Fin (n + 1)) → (Fin q → Fin (n + k + 1)) :=
    fun f i => ⟨(f i : ℕ) + k, by omega⟩ with hg
  have hginj : Function.Injective g := by
    intro f₁ f₂ h
    funext i
    have h1 := congrArg Fin.val (congrFun h i)
    simp only [hg] at h1
    exact Fin.ext (by omega)
  have hcomap : ∀ f : Fin q → Fin (n + 1),
      (restrictFin (n + 1) (drop k G)).comap f = H.comap (g f) := by
    intro f
    ext x y
    simp [restrictFin, hH, hg]
  rw [Graphon.homDensity_ofSimpleGraphOn, Graphon.homDensity_ofSimpleGraphOn]
  simp only [hcomap]
  set A : ℝ := ∑ f : Fin q → Fin (n + 1), if F ≤ H.comap (g f) then (1:ℝ) else 0 with hA
  set S : ℝ :=
    ∑ f' : Fin q → Fin (n + k + 1), if F ≤ H.comap f' then (1:ℝ) else 0 with hS
  -- the counting facts
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact Finset.sum_nonneg fun f _ => by split <;> norm_num
  have hAa : A ≤ ((n + 1 : ℕ) : ℝ) ^ q := by
    rw [hA]
    calc ∑ f : Fin q → Fin (n + 1), (if F ≤ H.comap (g f) then (1:ℝ) else 0)
        ≤ ∑ _f : Fin q → Fin (n + 1), (1:ℝ) :=
          Finset.sum_le_sum fun f _ => by split <;> norm_num
      _ = ((n + 1 : ℕ) : ℝ) ^ q := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
            Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
          push_cast
          ring
  have himg : ∑ f' ∈ Finset.univ.image g, (if F ≤ H.comap f' then (1:ℝ) else 0) = A := by
    rw [hA]
    exact Finset.sum_image fun f₁ _ f₂ _ h => hginj h
  have hAS : A ≤ S := by
    rw [← himg, hS]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun f' _ _ => by split <;> norm_num
  have hsplit := Finset.sum_sdiff
    (f := fun f' => if F ≤ H.comap f' then (1:ℝ) else 0)
    (Finset.subset_univ (Finset.univ.image g))
  rw [himg, ← hS] at hsplit
  have hrest : ∑ f' ∈ Finset.univ \ Finset.univ.image g,
      (if F ≤ H.comap f' then (1:ℝ) else 0) ≤
      ((n + k + 1 : ℕ) : ℝ) ^ q - ((n + 1 : ℕ) : ℝ) ^ q := by
    have hcardle : Fintype.card (Fin q → Fin (n + 1)) ≤
        Fintype.card (Fin q → Fin (n + k + 1)) := by
      simp only [Fintype.card_fun, Fintype.card_fin]
      exact Nat.pow_le_pow_left (by omega) q
    calc ∑ f' ∈ Finset.univ \ Finset.univ.image g,
        (if F ≤ H.comap f' then (1:ℝ) else 0)
        ≤ ∑ _f' ∈ Finset.univ \ Finset.univ.image g, (1:ℝ) :=
          Finset.sum_le_sum fun f' _ => by split <;> norm_num
      _ = ((Finset.univ \ Finset.univ.image g).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ((n + k + 1 : ℕ) : ℝ) ^ q - ((n + 1 : ℕ) : ℝ) ^ q := by
          rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
            Finset.card_image_of_injective _ hginj, Finset.card_univ,
            Nat.cast_sub hcardle]
          simp only [Fintype.card_fun, Fintype.card_fin]
          push_cast
          ring
  have hSA : S - A ≤ ((n + k + 1 : ℕ) : ℝ) ^ q - ((n + 1 : ℕ) : ℝ) ^ q := by
    linarith
  have hfin := abs_inv_pow_mul_sub_le (a := ((n + 1 : ℕ) : ℝ))
    (b := ((n + k + 1 : ℕ) : ℝ)) q k (by positivity) (by positivity)
    (by push_cast; linarith) (by push_cast; linarith) hA0 hAa hAS hSA
  exact hfin.trans (le_of_eq (by push_cast; ring))

/-- Two real sequences whose `k`-shifted difference vanishes converge together. -/
private theorem tendsto_iff_of_sub_shift_tendsto_zero {c : ℝ} (k : ℕ) (u v : ℕ → ℝ)
    (h : Tendsto (fun n => u n - v (n + k)) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 c) ↔ Tendsto v atTop (𝓝 c) := by
  constructor
  · intro hu
    rw [← tendsto_add_atTop_iff_nat k]
    simpa using hu.sub h
  · intro hv
    simpa using ((tendsto_add_atTop_iff_nat k).mpr hv).add h

/-- **Finite-deletion stability of empirical limits** (issue #97): the empirical
graphons of the `k`-tail of an infinite graph converge to `x` iff those of the original
graph do. Via the hom-density characterization of cut-distance convergence
(`cutDistance_tendsto_iff_homDensity_tendsto`), the counting comparison, and the index
shift `n ↦ n + k`. -/
theorem tendsto_empiricalGraphon_drop_iff (k : ℕ) (G : InfiniteGraph)
    (x : GraphonSpace α μ) :
    Tendsto (fun n => empiricalGraphon (α := α) (μ := μ) n (drop k G)) atTop (𝓝 x) ↔
      Tendsto (fun n => empiricalGraphon (α := α) (μ := μ) n G) atTop (𝓝 x) := by
  obtain ⟨V, rfl⟩ := surjective_mk x
  -- convergence of empirical graphons ↔ convergence of all hom densities
  have hchar : ∀ H : InfiniteGraph,
      Tendsto (fun n => empiricalGraphon (α := α) (μ := μ) n H) atTop (𝓝 (mk V)) ↔
        ∀ (p : ℕ) (F : SimpleGraph (Fin p)) [DecidableRel F.Adj], ∀ ε > 0, ∃ N,
          ∀ n ≥ N, |Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
              (restrictFin (n + 1) H)) - Graphon.homDensity F V| < ε := by
    intro H
    rw [Metric.tendsto_atTop]
    simp only [empiricalGraphon, graphClass, dist_mk]
    exact Graphon.cutDistance_tendsto_iff_homDensity_tendsto
      (fun n => Graphon.ofSimpleGraphOn (restrictFin (n + 1) H)) V
  rw [hchar, hchar]
  refine forall_congr' fun p => forall_congr' fun F => forall_congr' fun inst => ?_
  -- per fixed test graph `F`: the two hom-density sequences converge together
  have hdiff : Tendsto (fun n =>
      Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
        (restrictFin (n + 1) (drop k G))) -
      Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
        (restrictFin (n + k + 1) G))) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n : ℕ => (p:ℝ) * k / (n + 1))
    · intro n
      rw [Real.norm_eq_abs]
      exact abs_homDensity_drop_window_sub_le F k n G
    · have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h1 := h0.const_mul ((p:ℝ) * k)
      rw [mul_zero] at h1
      exact h1.congr fun n => by rw [mul_one_div]
  have hten : ∀ (w : ℕ → ℝ) (c : ℝ),
      Tendsto w atTop (𝓝 c) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |w n - c| < ε := by
    intro w c
    rw [Metric.tendsto_atTop]
    simp only [Real.dist_eq]
  exact ((hten (fun n => Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
      (restrictFin (n + 1) (drop k G)))) (Graphon.homDensity F V)).symm.trans
    ((tendsto_iff_of_sub_shift_tendsto_zero k _ _ hdiff).trans
      (hten (fun n => Graphon.homDensity F (Graphon.ofSimpleGraphOn (α := α) (μ := μ)
        (restrictFin (n + 1) G))) (Graphon.homDensity F V))))

/-- **Finite-deletion stability of the empirical convergence set**: the `k`-tail of an
infinite graph has convergent empirical graphons iff the graph does. -/
theorem mem_empiricalConvergenceSet_drop_iff (k : ℕ) (G : InfiniteGraph) :
    drop k G ∈ empiricalConvergenceSet ↔ G ∈ empiricalConvergenceSet := by
  simp only [empiricalConvergenceSet, Set.mem_setOf_eq]
  exact exists_congr fun x => tendsto_empiricalGraphon_drop_iff k G x

/-- **The universal empirical limit is invariant under tail restriction** — pointwise,
everywhere: on the convergence set by uniqueness of limits, off it both sides take the
canonical default (membership transfers). -/
theorem limitGraphon_drop (k : ℕ) (G : InfiniteGraph) :
    limitGraphon (drop k G) = limitGraphon G := by
  by_cases hG : G ∈ empiricalConvergenceSet
  · obtain ⟨x, hx⟩ := hG
    rw [limitGraphon_eq_of_tendsto ((tendsto_empiricalGraphon_drop_iff k G x).mpr hx),
      limitGraphon_eq_of_tendsto hx]
  · have hG' : drop k G ∉ empiricalConvergenceSet := fun h =>
      hG ((mem_empiricalConvergenceSet_drop_iff k G).mp h)
    simp only [limitGraphon, dif_neg hG, dif_neg hG']

end GraphonSpace
