/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.InvariantAction
import Graphon.RestrictionIndependence
import Graphon.RestrictionIndependenceReverse
import Mathlib.MeasureTheory.Measure.MeasuredSets

/-!
# Ergodic decomposition of exchangeable graph laws (issue #59, part 2)

The fixed-fiber ergodicity argument: a permutation-invariant event has `M.law`-measure
`0` or `1`, giving the ergodicity links of the DJ 5.5 / #59 equivalence.

Infrastructure:
* `InfiniteGraph.FinSupp.one` / `.inv` / `.mul` — the finitely supported permutations of
  `ℕ` are closed under identity, inverse, and composition (a subgroup of `Equiv.Perm ℕ`);
* `InfiniteGraph.swapBlock k` — the involution swapping the block `[0, k)` with `[k, 2k)`
  (fixing everything past `2k`), a finitely supported permutation;
* `InfiniteGraph.restrictFin_relabel_swapBlock` — relabeling by `swapBlock k` moves the
  initial `k`-window onto the `k`-tail window:
  `restrictFin k (relabel (swapBlock k) G) = restrictFin k (drop k G)`; hence
* `InfiniteGraph.relabel_swapBlock_preimage_mem_tailAlgebra` — the `swapBlock k`
  relabeling carries every `initialAlgebra k` event into a `tailAlgebra k` event;
* `Graphon.InfiniteExchangeableGraphLaw.exists_initialAlgebra_measure_symmDiff_lt` —
  **in-measure approximation by initial cylinders**: every Borel event is approximated in
  `M.law`-measure by an event depending on only finitely many vertices (via
  `exists_measure_symmDiff_lt_of_generateFrom_isSetRing`, the initial cylinders being a
  set-ring that generates the Borel σ-algebra).

Fixed-fiber ergodicity:
* `InfiniteGraph.vertexTailAlgebra_le_invariantAlgebra` — every vertex-tail event is
  finite-permutation invariant;
* `Graphon.InfiniteExchangeableGraphLaw.measure_invariant_eq_zero_or_one_of_restrictionIndependent`
  — under restriction independence, every invariant event is null or conull (the `4ε`
  approximate-independence estimate);
* `isErgodic_of_restrictionIndependent` and `vertexTailTrivial_of_isErgodic` — the two new
  links closing `RestrictionIndependent ⟹ IsErgodic ⟹ VertexTailTrivial`.
-/

open MeasureTheory Set

open scoped ENNReal symmDiff

namespace InfiniteGraph

/-! ### The finitely supported permutations form a subgroup -/

/-- The identity is finitely supported. -/
theorem FinSupp.one : FinSupp (1 : Equiv.Perm ℕ) := ⟨0, fun _ _ => rfl⟩

/-- The inverse of a finitely supported permutation is finitely supported. -/
theorem FinSupp.inv {σ : Equiv.Perm ℕ} (hσ : FinSupp σ) : FinSupp σ⁻¹ := by
  obtain ⟨N, hN⟩ := hσ
  refine ⟨N, fun x hx => ?_⟩
  calc σ⁻¹ x = σ⁻¹ (σ x) := by rw [hN x hx]
    _ = x := σ.symm_apply_apply x

/-- The composition of two finitely supported permutations is finitely supported. -/
theorem FinSupp.mul {σ τ : Equiv.Perm ℕ} (hσ : FinSupp σ) (hτ : FinSupp τ) :
    FinSupp (σ * τ) := by
  obtain ⟨Nσ, hσ⟩ := hσ
  obtain ⟨Nτ, hτ⟩ := hτ
  refine ⟨max Nσ Nτ, fun x hx => ?_⟩
  rw [Equiv.Perm.mul_apply, hτ x ((le_max_right Nσ Nτ).trans hx),
    hσ x ((le_max_left Nσ Nτ).trans hx)]

/-! ### The block swap `[0, k) ↔ [k, 2k)` -/

/-- The block-swap function: exchange `[0, k)` with `[k, 2k)`, fixing the rest. -/
def swapBlockFun (k i : ℕ) : ℕ := if i < k then i + k else if i < 2 * k then i - k else i

theorem swapBlockFun_involutive (k : ℕ) : Function.Involutive (swapBlockFun k) := by
  intro i
  simp only [swapBlockFun]
  split_ifs <;> omega

/-- **The block swap** `[0, k) ↔ [k, 2k)`: a finitely supported involution of `ℕ`. -/
def swapBlock (k : ℕ) : Equiv.Perm ℕ := (swapBlockFun_involutive k).toPerm

@[simp] theorem swapBlock_apply (k i : ℕ) : swapBlock k i = swapBlockFun k i :=
  congrFun (swapBlockFun_involutive k).coe_toPerm i

theorem swapBlock_apply_of_lt (k : ℕ) {i : ℕ} (hi : i < k) : swapBlock k i = i + k := by
  simp only [swapBlock_apply, swapBlockFun, if_pos hi]

/-- The block swap is finitely supported (it fixes everything past `2k`). -/
theorem finSupp_swapBlock (k : ℕ) : FinSupp (swapBlock k) := by
  refine ⟨2 * k, fun x hx => ?_⟩
  simp only [swapBlock_apply, swapBlockFun]
  split_ifs <;> omega

/-! ### The block swap carries initial cylinders to tail cylinders -/

/-- **The block swap moves the initial window onto the tail window**: the graph induced
on the first `k` vertices after relabeling by `swapBlock k` equals the graph induced on
`{k, …, 2k−1}` — the first `k` vertices of the `k`-tail. -/
theorem restrictFin_relabel_swapBlock (k : ℕ) (G : InfiniteGraph) :
    restrictFin k (relabel (swapBlock k) G) = restrictFin k (drop k G) := by
  rw [restrictFin_relabel (swapBlock k) (Fin.addNatEmb k)
      (fun a => by
        have : ((Fin.addNatEmb k a : Fin (k + k)) : ℕ) = (a : ℕ) + k := by
          simp [Fin.addNatEmb]
        rw [this]; exact swapBlock_apply_of_lt k a.isLt),
    restrictFin_drop k k G]

/-- **The block-swap relabeling carries an `initialAlgebra k` event into a `tailAlgebra k`
event**: it moves dependence on the first `k` vertices to dependence on `{k, …, 2k−1}`,
which is contained in the tail `{k, k+1, …}`. -/
theorem relabel_swapBlock_preimage_mem_tailAlgebra (k : ℕ) {B : Set InfiniteGraph}
    (hB : MeasurableSet[initialAlgebra k] B) :
    MeasurableSet[tailAlgebra k] (relabel (swapBlock k) ⁻¹' B) := by
  obtain ⟨S, hS, rfl⟩ := hB
  refine ⟨restrictFin k ⁻¹' S, measurable_restrictFin k hS, ?_⟩
  ext G
  simp only [Set.mem_preimage]
  rw [← restrictFin_relabel_swapBlock k G]

/-! ### In-measure approximation by initial cylinders -/

/-- The events depending on only finitely many vertices form a ring of sets. -/
theorem isSetRing_iUnion_initialAlgebra :
    MeasureTheory.IsSetRing
      (⋃ k, {A : Set InfiniteGraph | MeasurableSet[initialAlgebra k] A}) where
  empty_mem := by
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨0, @MeasurableSet.empty _ (initialAlgebra 0)⟩
  union_mem := by
    intro s t hs ht
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hs ht ⊢
    obtain ⟨k, hs⟩ := hs
    obtain ⟨l, ht⟩ := ht
    exact ⟨max k l, (initialAlgebra_mono (le_max_left k l) _ hs).union
      (initialAlgebra_mono (le_max_right k l) _ ht)⟩
  sdiff_mem := by
    intro s t hs ht
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hs ht ⊢
    obtain ⟨k, hs⟩ := hs
    obtain ⟨l, ht⟩ := ht
    exact ⟨max k l, (initialAlgebra_mono (le_max_left k l) _ hs).diff
      (initialAlgebra_mono (le_max_right k l) _ ht)⟩

/-- The Borel σ-algebra is generated by the finite-vertex events. -/
theorem generateFrom_iUnion_initialAlgebra :
    (inferInstance : MeasurableSpace InfiniteGraph) =
      MeasurableSpace.generateFrom
        (⋃ k, {A : Set InfiniteGraph | MeasurableSet[initialAlgebra k] A}) :=
  ((MeasurableSpace.generateFrom_iUnion_measurableSet initialAlgebra).trans
    iSup_initialAlgebra_eq).symm

end InfiniteGraph

namespace Graphon.InfiniteExchangeableGraphLaw

/-- **In-measure approximation by initial cylinders**: every Borel event `s` is
approximated in `M.law`-measure, to within any `ε > 0`, by an event `t` depending on only
the first `k` vertices for some `k`. The initial cylinders form a set-ring generating the
Borel σ-algebra, so `exists_measure_symmDiff_lt_of_generateFrom_isSetRing` applies. -/
theorem exists_initialAlgebra_measure_symmDiff_lt (M : Graphon.InfiniteExchangeableGraphLaw)
    {s : Set InfiniteGraph} (hs : MeasurableSet s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ k, ∃ t, MeasurableSet[InfiniteGraph.initialAlgebra k] t ∧
      (M.law : Measure InfiniteGraph) (t ∆ s) < ε := by
  haveI : IsProbabilityMeasure (M.law : Measure InfiniteGraph) := M.law.2
  obtain ⟨t, ht, hlt⟩ := MeasureTheory.exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (μ := (M.law : Measure InfiniteGraph)) InfiniteGraph.isSetRing_iUnion_initialAlgebra
    ⟨{Set.univ}, Set.countable_singleton _, by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Set.mem_iUnion.mpr ⟨0, @MeasurableSet.univ _ (InfiniteGraph.initialAlgebra 0)⟩, by
      rw [Set.sUnion_singleton, Set.compl_univ, measure_empty]⟩
    InfiniteGraph.generateFrom_iUnion_initialAlgebra hs hε
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ht
  exact ⟨k, t, hk, hlt⟩

end Graphon.InfiniteExchangeableGraphLaw

/-! ### Fixed-fiber ergodicity: invariant events are trivial -/

namespace InfiniteGraph

/-- A permutation supported below `N` acts trivially past the `N`-tail:
`drop N ∘ relabel σ = drop N`. -/
theorem drop_comp_relabel_of_finSupp {σ : Equiv.Perm ℕ} {N : ℕ}
    (hN : ∀ x, N ≤ x → σ x = x) : drop N ∘ relabel σ = drop N := by
  funext G
  show ((((G : SimpleGraph ℕ).comap σ).comap (· + N)) : SimpleGraph ℕ) =
    (((G : SimpleGraph ℕ).comap (· + N)) : SimpleGraph ℕ)
  ext a b
  simp only [SimpleGraph.comap_adj]
  rw [hN (a + N) (Nat.le_add_left N a), hN (b + N) (Nat.le_add_left N b)]

/-- **Every vertex-tail event is permutation-invariant**: the vertex-tail σ-algebra is a
sub-σ-algebra of the finite-permutation-invariant σ-algebra. A finitely supported
permutation acts trivially on all sufficiently late tails. -/
theorem vertexTailAlgebra_le_invariantAlgebra :
    vertexTailAlgebra ≤ invariantAlgebra := fun s hs =>
  ⟨vertexTailAlgebra_le s hs, fun σ hσ => by
    obtain ⟨N, hN⟩ := hσ
    obtain ⟨T, _hT, hTs⟩ := vertexTailAlgebra_le_tailAlgebra N s hs
    rw [← hTs, ← Set.preimage_comp, drop_comp_relabel_of_finSupp hN]⟩

end InfiniteGraph

namespace Graphon.InfiniteExchangeableGraphLaw

open InfiniteGraph MeasureTheory

open scoped ENNReal symmDiff

/-- **Fixed-fiber ergodicity**: under restriction independence, every finite-permutation-
invariant event has `M.law`-measure `0` or `1`. Approximate the invariant `A` by an
initial cylinder `B`, move `B` to a disjoint tail block `B' = relabel (swapBlock k) ⁻¹' B`
(invariance keeps `μ (A ∆ B') < ε`, exchangeability keeps `μ B' = μ B`, independence gives
`μ (B ∩ B') = μ B · μ B'`); comparing `A` with `B ∩ B'` yields `|a − a²| ≤ 4ε` for every
`ε`, where `a = μ.real A`, so `a` is a fixed point of `t ↦ t²`. -/
theorem measure_invariant_eq_zero_or_one_of_restrictionIndependent
    {M : Graphon.InfiniteExchangeableGraphLaw} (hM : M.RestrictionIndependent)
    {A : Set InfiniteGraph} (hA : MeasurableSet[invariantAlgebra] A) :
    (M.law : Measure InfiniteGraph) A = 0 ∨ (M.law : Measure InfiniteGraph) A = 1 := by
  classical
  set μ : Measure InfiniteGraph := (M.law : Measure InfiniteGraph) with hμ
  haveI : IsProbabilityMeasure μ := M.law.2
  obtain ⟨hA_meas, hA_inv⟩ := hA
  have hex : ∀ τ : Equiv.Perm ℕ, μ.map (relabel τ) = μ := fun τ => by
    rw [hμ]; exact M.exchangeable τ
  set a : ℝ := μ.real A with ha
  have ha0 : 0 ≤ a := measureReal_nonneg
  have ha1 : a ≤ 1 := measureReal_le_one
  -- the key fixed-point estimate: |a - a²| ≤ 4ε for every ε > 0
  have hbound : ∀ ε : ℝ, 0 < ε → |a - a * a| ≤ 4 * ε := by
    intro ε hε
    obtain ⟨k, B, hB_init, hBA⟩ :=
      M.exists_initialAlgebra_measure_symmDiff_lt hA_meas (ENNReal.ofReal_pos.mpr hε)
    rw [← hμ] at hBA
    have hB_meas : MeasurableSet B := initialAlgebra_le k B hB_init
    set σ : Equiv.Perm ℕ := swapBlock k with hσdef
    have hσ : FinSupp σ := finSupp_swapBlock k
    set B' : Set InfiniteGraph := relabel σ ⁻¹' B with hB'def
    have hB'_tail : MeasurableSet[tailAlgebra k] B' :=
      relabel_swapBlock_preimage_mem_tailAlgebra k hB_init
    have hB'_meas : MeasurableSet B' := measurable_relabel σ hB_meas
    have hμB' : μ B' = μ B := by
      rw [hB'def, ← Measure.map_apply (measurable_relabel σ) hB_meas, hex σ]
    have hBB' : μ (B ∩ B') = μ B * μ B' :=
      (ProbabilityTheory.Indep_iff (initialAlgebra k) (tailAlgebra k) μ).mp
        (by rw [hμ]; exact hM k) B B' hB_init hB'_tail
    have hAB' : μ (A ∆ B') < ENNReal.ofReal ε := by
      have hpre : A ∆ B' = relabel σ ⁻¹' (A ∆ B) := by
        rw [Set.preimage_symmDiff, hA_inv σ hσ, hB'def]
      rw [hpre, ← Measure.map_apply (measurable_relabel σ) (hA_meas.symmDiff hB_meas), hex σ,
        symmDiff_comm]
      exact hBA
    -- pass to real measures
    have hμreal_B' : μ.real B' = μ.real B := congrArg ENNReal.toReal hμB'
    have hbb : μ.real (B ∩ B') = μ.real B * μ.real B' := by
      show (μ (B ∩ B')).toReal = (μ B).toReal * (μ B').toReal
      rw [hBB', ENNReal.toReal_mul]
    set b : ℝ := μ.real B with hb
    rw [hμreal_B'] at hbb
    have hb0 : 0 ≤ b := measureReal_nonneg
    have hb1 : b ≤ 1 := measureReal_le_one
    have hdAB : μ.real (A ∆ B) < ε := by
      have h : μ (A ∆ B) < ENNReal.ofReal ε := by rw [symmDiff_comm]; exact hBA
      exact ENNReal.toReal_lt_of_lt_ofReal h
    have hdAB' : μ.real (A ∆ B') < ε := ENNReal.toReal_lt_of_lt_ofReal hAB'
    have hab : |a - b| ≤ μ.real (A ∆ B) :=
      abs_measureReal_sub_le_measureReal_symmDiff hA_meas.nullMeasurableSet
        hB_meas.nullMeasurableSet
    have hsub : A ∆ (B ∩ B') ⊆ (A ∆ B) ∪ (A ∆ B') := by
      intro x hx
      simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_union] at hx ⊢
      tauto
    have hdint : μ.real (A ∆ (B ∩ B')) ≤ μ.real (A ∆ B) + μ.real (A ∆ B') :=
      (measureReal_mono hsub).trans (measureReal_union_le _ _)
    have habb : |a - b * b| ≤ μ.real (A ∆ (B ∩ B')) := by
      rw [← hbb]
      exact abs_measureReal_sub_le_measureReal_symmDiff hA_meas.nullMeasurableSet
        (hB_meas.inter hB'_meas).nullMeasurableSet
    have h1 : |a - b * b| ≤ 2 * ε := by
      calc |a - b * b| ≤ μ.real (A ∆ (B ∩ B')) := habb
        _ ≤ μ.real (A ∆ B) + μ.real (A ∆ B') := hdint
        _ ≤ 2 * ε := by linarith
    have hab' : |a - b| ≤ ε := le_of_lt (lt_of_le_of_lt hab hdAB)
    have h2 : |b * b - a * a| ≤ 2 * ε := by
      have hprod : |b * b - a * a| = |a - b| * (a + b) := by
        rw [show b * b - a * a = -((a - b) * (a + b)) by ring, abs_neg, abs_mul,
          abs_of_nonneg (show (0 : ℝ) ≤ a + b by linarith)]
      rw [hprod]
      calc |a - b| * (a + b) ≤ ε * 2 :=
            mul_le_mul hab' (by linarith) (by positivity) (le_of_lt hε)
        _ = 2 * ε := by ring
    calc |a - a * a| ≤ |a - b * b| + |b * b - a * a| := abs_sub_le a (b * b) (a * a)
      _ ≤ 2 * ε + 2 * ε := by linarith
      _ = 4 * ε := by ring
  -- the fixed-point estimate forces a = a²
  have hle0 : |a - a * a| ≤ 0 := by
    by_contra h
    rw [not_le] at h
    have := hbound (|a - a * a| / 8) (by linarith)
    linarith
  have hfix : a = a * a := by
    have := abs_nonpos_iff.mp hle0
    linarith
  -- a ∈ {0, 1}, hence μ A ∈ {0, 1}
  have hfin : μ A ≠ ∞ := measure_ne_top μ A
  have ha01' : a = 0 ∨ a = 1 := by
    have hz : a * (1 - a) = 0 := by nlinarith [hfix]
    rcases mul_eq_zero.mp hz with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases ha01' with h0 | h1
  · exact Or.inl (((ENNReal.toReal_eq_zero_iff (μ A)).mp h0).resolve_right hfin)
  · exact Or.inr (by rw [← ENNReal.ofReal_toReal hfin, show (μ A).toReal = (1 : ℝ) from h1,
      ENNReal.ofReal_one])

/-- **Restriction independence implies ergodicity** (a link of the DJ 5.5 / #59 chain). -/
theorem isErgodic_of_restrictionIndependent
    {M : Graphon.InfiniteExchangeableGraphLaw} (hM : M.RestrictionIndependent) :
    M.IsErgodic := fun _ hs =>
  measure_invariant_eq_zero_or_one_of_restrictionIndependent hM hs

/-- **Ergodicity implies vertex-tail triviality**: every vertex-tail event is
permutation-invariant (`vertexTailAlgebra_le_invariantAlgebra`). -/
theorem vertexTailTrivial_of_isErgodic
    {M : Graphon.InfiniteExchangeableGraphLaw} (hM : M.IsErgodic) :
    M.VertexTailTrivial := fun s hs =>
  hM s (InfiniteGraph.vertexTailAlgebra_le_invariantAlgebra s hs)

/-! ### The ergodicity links of the extremality equivalence (#59) -/

/-- **Ergodicity ↔ dissociation**: closing `RestrictionIndependent ⟹ IsErgodic ⟹
VertexTailTrivial` against the #91 equivalences. -/
theorem isErgodic_iff_isDissociated (M : Graphon.InfiniteExchangeableGraphLaw) :
    M.IsErgodic ↔ M.IsDissociated :=
  ⟨fun hM => (isDissociated_iff_vertexTailTrivial M).mpr (vertexTailTrivial_of_isErgodic hM),
    fun hM => isErgodic_of_restrictionIndependent
      ((isDissociated_iff_restrictionIndependent M).mp hM)⟩

/-- **Ergodicity ↔ restriction independence**. -/
theorem isErgodic_iff_restrictionIndependent (M : Graphon.InfiniteExchangeableGraphLaw) :
    M.IsErgodic ↔ M.RestrictionIndependent :=
  (isErgodic_iff_isDissociated M).trans (isDissociated_iff_restrictionIndependent M)

/-- **Ergodicity ↔ vertex-tail triviality**. -/
theorem isErgodic_iff_vertexTailTrivial (M : Graphon.InfiniteExchangeableGraphLaw) :
    M.IsErgodic ↔ M.VertexTailTrivial :=
  (isErgodic_iff_isDissociated M).trans (isDissociated_iff_vertexTailTrivial M)

/-- **The ergodic-decomposition form of Diaconis–Janson Theorem 5.5** (#59): the six-way
extremality equivalence, adjoining ergodicity under the finite-permutation action to the
five-way `tfae_extremality`. -/
@[blueprint "thm:dj-five-five-ergodic"
  (title := /-- The ergodic-decomposition form of extremality (#59) -/)]
theorem tfae_ergodic_extremality (M : Graphon.InfiniteExchangeableGraphLaw) :
    List.TFAE
      [(∃ x : StandardGraphonSpace,
          (GraphonSpace.infiniteMixtureLawEquiv (α := unitInterval) (μ := volume)).symm M
            = MeasureTheory.diracProba x),
        (∃ x : StandardGraphonSpace, M = GraphonSpace.infiniteSampleExchangeableLaw x),
        M.IsDissociated,
        M.RestrictionIndependent,
        M.VertexTailTrivial,
        M.IsErgodic] := by
  tfae_have 3 ↔ 1 := GraphonSpace.isDissociated_iff_representing_dirac M
  tfae_have 3 ↔ 2 := GraphonSpace.isDissociated_iff_exists_infiniteSampleExchangeableLaw M
  tfae_have 3 ↔ 4 := isDissociated_iff_restrictionIndependent M
  tfae_have 3 ↔ 5 := isDissociated_iff_vertexTailTrivial M
  tfae_have 3 ↔ 6 := (isErgodic_iff_isDissociated M).symm
  tfae_finish

end Graphon.InfiniteExchangeableGraphLaw
