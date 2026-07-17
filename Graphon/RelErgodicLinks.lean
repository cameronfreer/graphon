/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelInvariantAction
import Mathlib.MeasureTheory.Measure.MeasuredSets

/-!
# Ergodicity links for exchangeable relational laws (R3c step 3, #106)

The generic port of the undirected fixed-fiber ergodicity argument
(`Graphon/ErgodicDecomposition.lean`): a sortwise-permutation-invariant event has law-measure
`0` or `1` under restriction independence, closing ergodicity into the R3b triangle.

Infrastructure:
* `RelSignature.sortwiseSwapBlock k` — the sortwise involution swapping the block `[0, k s)`
  with `[k s, 2 k s)` in each sort (fixing everything past `2 k s`), finitely supported with a
  common bound under `[Fintype S.Srt]` (`sortwiseFinSupp_swapBlock`);
* `RelStructure.restrictFin_relabel_sortwiseSwapBlock` — the block swap moves the initial
  `k`-window onto the `k`-tail window; hence
* `RelStructure.relabel_sortwiseSwapBlock_preimage_mem_tailAlgebra` — the block-swap
  relabeling carries every `initialAlgebra k` event into a `tailAlgebra k` event;
* `RelSignature.exists_initialAlgebra_measure_symmDiff_lt` — **in-measure approximation by
  initial cylinders**: every measurable event is approximated in law-measure by an event
  depending on only an initial block (the initial cylinders form a set-ring generating the
  σ-algebra).

Fixed-fiber ergodicity:
* `RelStructure.vertexTailAlgebra_le_invariantAlgebra` — every vertex-tail event is invariant
  under all finitely supported sortwise relabelings;
* `InfiniteRelExchangeableLaw.measure_invariant_eq_zero_or_one_of_restrictionIndependent` —
  under restriction independence, every invariant event is null or conull (the `4ε`
  approximate-independence estimate);
* `RestrictionIndependent.isErgodic` and `IsErgodic.vertexTailTrivial` — the two links
  closing `RestrictionIndependent ⟹ IsErgodic ⟹ VertexTailTrivial`;
* `isErgodic_iff_isDissociated` / `isErgodic_iff_restrictionIndependent` /
  `isErgodic_iff_vertexTailTrivial` — ergodicity joins the R3b equivalences.
-/

open MeasureTheory Set

open scoped ENNReal symmDiff

namespace RelSignature

variable {S : RelSignature}

/-! ### The sortwise block swap `[0, k s) ↔ [k s, 2 k s)` -/

/-- The block-swap function: exchange `[0, k)` with `[k, 2k)`, fixing the rest. -/
def swapBlockFun (k i : ℕ) : ℕ := if i < k then i + k else if i < 2 * k then i - k else i

theorem swapBlockFun_involutive (k : ℕ) : Function.Involutive (swapBlockFun k) := by
  intro i
  simp only [swapBlockFun]
  split_ifs <;> omega

/-- **The sortwise block swap** `[0, k s) ↔ [k s, 2 k s)`: in each sort, the involution of `ℕ`
swapping the initial `k s`-block with the following one. -/
def sortwiseSwapBlock (k : S.Srt → ℕ) : ∀ _ : S.Srt, Equiv.Perm ℕ := fun s =>
  (swapBlockFun_involutive (k s)).toPerm

@[simp] theorem sortwiseSwapBlock_apply (k : S.Srt → ℕ) (s : S.Srt) (i : ℕ) :
    sortwiseSwapBlock k s i = swapBlockFun (k s) i :=
  congrFun (swapBlockFun_involutive (k s)).coe_toPerm i

theorem sortwiseSwapBlock_apply_of_lt (k : S.Srt → ℕ) (s : S.Srt) {i : ℕ} (hi : i < k s) :
    sortwiseSwapBlock k s i = i + k s := by
  simp only [sortwiseSwapBlock_apply, swapBlockFun, if_pos hi]

/-- The sortwise block swap is finitely supported with a **common** bound: each sort's swap
fixes everything past `2 * k s`, and finitely many sorts have a common bound. -/
theorem sortwiseFinSupp_swapBlock [Fintype S.Srt] (k : S.Srt → ℕ) :
    SortwiseFinSupp (sortwiseSwapBlock k) := by
  obtain ⟨N, hN⟩ := exists_const_ge fun s => 2 * k s
  refine ⟨N, fun s x hx => ?_⟩
  have := hN s
  simp only [sortwiseSwapBlock_apply, swapBlockFun]
  split_ifs <;> omega

/-! ### The block swap carries initial cylinders to tail cylinders -/

/-- **The block swap moves the initial window onto the tail window**: restricting the swapped
structure to the initial `k`-block is restricting the original structure to the `k`-block
after `k`. -/
theorem RelStructure.restrictFin_relabel_sortwiseSwapBlock (k : S.Srt → ℕ) :
    RelStructure.restrictFin (S := S) k ∘ RelStructure.relabel (sortwiseSwapBlock k) =
      RelStructure.restrict (shiftEmb k k) := by
  funext X
  show RelStructure.comap _ (RelStructure.comap _ X) = RelStructure.comap _ X
  rw [← RelStructure.comap_comp]
  congr 1
  funext s i
  exact sortwiseSwapBlock_apply_of_lt k s i.isLt

/-- **The block-swap relabeling carries an `initialAlgebra k` event into a `tailAlgebra k`
event**: it moves dependence on the initial `k`-block to dependence on the following
`k`-block, which is contained in the `k`-tail. -/
theorem RelStructure.relabel_sortwiseSwapBlock_preimage_mem_tailAlgebra (k : S.Srt → ℕ)
    {B : Set (RelStructure S (Vinfinite S))}
    (hB : MeasurableSet[RelStructure.initialAlgebra k] B) :
    MeasurableSet[RelStructure.tailAlgebra k]
      (RelStructure.relabel (sortwiseSwapBlock k) ⁻¹' B) := by
  obtain ⟨T, hT, rfl⟩ := hB
  refine ⟨RelStructure.restrictFin k ⁻¹' T, RelSignature.measurable_restrictFin k hT, ?_⟩
  ext X
  simp only [Set.mem_preimage]
  rw [show RelStructure.restrictFin k (RelStructure.relabel (sortwiseSwapBlock k) X) =
      RelStructure.restrict (shiftEmb k k) X from
    congrFun (RelStructure.restrictFin_relabel_sortwiseSwapBlock k) X]
  exact Iff.rfl

/-! ### In-measure approximation by initial cylinders -/

/-- The events depending on only an initial block form a ring of sets. -/
theorem isSetRing_iUnion_initialAlgebra :
    MeasureTheory.IsSetRing
      (⋃ k : S.Srt → ℕ, {A : Set (RelStructure S (Vinfinite S)) |
        MeasurableSet[RelStructure.initialAlgebra k] A}) where
  empty_mem := by
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨fun _ => 0, @MeasurableSet.empty _ (RelStructure.initialAlgebra fun _ => 0)⟩
  union_mem := by
    intro s t hs ht
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hs ht ⊢
    obtain ⟨k, hs⟩ := hs
    obtain ⟨l, ht⟩ := ht
    exact ⟨fun s => max (k s) (l s),
      (RelStructure.initialAlgebra_mono (fun s => le_max_left (k s) (l s)) _ hs).union
        (RelStructure.initialAlgebra_mono (fun s => le_max_right (k s) (l s)) _ ht)⟩
  sdiff_mem := by
    intro s t hs ht
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hs ht ⊢
    obtain ⟨k, hs⟩ := hs
    obtain ⟨l, ht⟩ := ht
    exact ⟨fun s => max (k s) (l s),
      (RelStructure.initialAlgebra_mono (fun s => le_max_left (k s) (l s)) _ hs).diff
        (RelStructure.initialAlgebra_mono (fun s => le_max_right (k s) (l s)) _ ht)⟩

/-- The product σ-algebra is generated by the initial-block events. -/
theorem generateFrom_iUnion_initialAlgebra :
    (inferInstance : MeasurableSpace (RelStructure S (Vinfinite S))) =
      MeasurableSpace.generateFrom
        (⋃ k : S.Srt → ℕ, {A : Set (RelStructure S (Vinfinite S)) |
          MeasurableSet[RelStructure.initialAlgebra k] A}) :=
  ((MeasurableSpace.generateFrom_iUnion_measurableSet
    (RelStructure.initialAlgebra (S := S))).trans RelStructure.iSup_initialAlgebra_eq).symm

/-- **In-measure approximation by initial cylinders**: every measurable event `s` is
approximated in `M.law`-measure, to within any `ε > 0`, by an event `t` depending on only the
initial `k`-block for some size vector `k`. The initial cylinders form a set-ring generating
the σ-algebra, so `exists_measure_symmDiff_lt_of_generateFrom_isSetRing` applies. -/
theorem InfiniteRelExchangeableLaw.exists_initialAlgebra_measure_symmDiff_lt
    (M : InfiniteRelExchangeableLaw S) {s : Set (RelStructure S (Vinfinite S))}
    (hs : MeasurableSet s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ k : S.Srt → ℕ, ∃ t, MeasurableSet[RelStructure.initialAlgebra k] t ∧
      (M.law : Measure (RelStructure S (Vinfinite S))) (t ∆ s) < ε := by
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  obtain ⟨t, ht, hlt⟩ := MeasureTheory.exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (μ := (M.law : Measure (RelStructure S (Vinfinite S)))) isSetRing_iUnion_initialAlgebra
    ⟨{Set.univ}, Set.countable_singleton _, by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Set.mem_iUnion.mpr
        ⟨fun _ => 0, @MeasurableSet.univ _ (RelStructure.initialAlgebra fun _ => 0)⟩, by
      rw [Set.sUnion_singleton, Set.compl_univ, measure_empty]⟩
    generateFrom_iUnion_initialAlgebra hs hε
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ht
  exact ⟨k, t, hk, hlt⟩

/-! ### Fixed-fiber ergodicity: invariant events are trivial -/

/-- A sortwise permutation family supported below `N` acts trivially past the diagonal
`N`-tail: `drop N ∘ relabel σ = drop N`. -/
theorem RelStructure.drop_comp_relabel_of_sortwiseFinSupp {σ : ∀ _ : S.Srt, Equiv.Perm ℕ}
    {N : ℕ} (hN : ∀ s (x : ℕ), N ≤ x → σ s x = x) :
    RelStructure.drop (S := S) (fun _ => N) ∘ RelStructure.relabel σ =
      RelStructure.drop fun _ => N := by
  funext X
  show RelStructure.comap _ (RelStructure.comap _ X) = RelStructure.comap _ X
  rw [← RelStructure.comap_comp]
  congr 1
  funext s i
  exact hN s (i + N) (Nat.le_add_left N i)

/-- **Every vertex-tail event is invariant**: the vertex-tail σ-algebra is a sub-σ-algebra of
the finitely-supported-relabeling-invariant σ-algebra. A finitely supported sortwise family
acts trivially on all sufficiently late tails. -/
theorem RelStructure.vertexTailAlgebra_le_invariantAlgebra :
    RelStructure.vertexTailAlgebra (S := S) ≤ RelStructure.invariantAlgebra := fun A hA =>
  ⟨RelStructure.vertexTailAlgebra_le A hA, fun σ hσ => by
    obtain ⟨N, hN⟩ := hσ
    obtain ⟨T, _hT, hTA⟩ := RelStructure.vertexTailAlgebra_le_tailAlgebra (fun _ => N) A hA
    rw [← hTA, ← Set.preimage_comp, RelStructure.drop_comp_relabel_of_sortwiseFinSupp hN]⟩

/-- **Fixed-fiber ergodicity**: under restriction independence, every event strictly
invariant under all finitely supported sortwise relabelings has `M.law`-measure `0` or `1`.
Approximate the invariant `A` by an initial cylinder `B`, move `B` to a disjoint tail block
`B' = relabel (sortwiseSwapBlock k) ⁻¹' B` (invariance keeps `μ (A ∆ B') < ε`,
exchangeability keeps `μ B' = μ B`, independence gives `μ (B ∩ B') = μ B · μ B'`); comparing
`A` with `B ∩ B'` yields `|a − a²| ≤ 4ε` for every `ε`, where `a = μ.real A`, so `a` is a
fixed point of `t ↦ t²`. -/
theorem InfiniteRelExchangeableLaw.measure_invariant_eq_zero_or_one_of_restrictionIndependent
    [Fintype S.Srt] {M : InfiniteRelExchangeableLaw S} (hM : M.RestrictionIndependent)
    {A : Set (RelStructure S (Vinfinite S))}
    (hA : MeasurableSet[RelStructure.invariantAlgebra] A) :
    (M.law : Measure (RelStructure S (Vinfinite S))) A = 0 ∨
      (M.law : Measure (RelStructure S (Vinfinite S))) A = 1 := by
  classical
  set μ : Measure (RelStructure S (Vinfinite S)) :=
    (M.law : Measure (RelStructure S (Vinfinite S))) with hμ
  haveI : IsProbabilityMeasure μ := M.law.2
  obtain ⟨hA_meas, hA_inv⟩ := hA
  have hex : ∀ τ : ∀ _ : S.Srt, Equiv.Perm ℕ, μ.map (RelStructure.relabel τ) = μ := fun τ => by
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
    have hB_meas : MeasurableSet B := RelStructure.initialAlgebra_le k B hB_init
    set σ : ∀ _ : S.Srt, Equiv.Perm ℕ := sortwiseSwapBlock k with hσdef
    have hσ : SortwiseFinSupp σ := sortwiseFinSupp_swapBlock k
    set B' : Set (RelStructure S (Vinfinite S)) := RelStructure.relabel σ ⁻¹' B with hB'def
    have hB'_tail : MeasurableSet[RelStructure.tailAlgebra k] B' :=
      RelStructure.relabel_sortwiseSwapBlock_preimage_mem_tailAlgebra k hB_init
    have hB'_meas : MeasurableSet B' := measurable_relabel σ hB_meas
    have hμB' : μ B' = μ B := by
      rw [hB'def, ← Measure.map_apply (measurable_relabel σ) hB_meas, hex σ]
    have hBB' : μ (B ∩ B') = μ B * μ B' :=
      (ProbabilityTheory.Indep_iff (RelStructure.initialAlgebra k)
          (RelStructure.tailAlgebra k) μ).mp
        (by rw [hμ]; exact hM k) B B' hB_init hB'_tail
    have hAB' : μ (A ∆ B') < ENNReal.ofReal ε := by
      have hpre : A ∆ B' = RelStructure.relabel σ ⁻¹' (A ∆ B) := by
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

/-! ### The ergodicity links of the R3b triangle -/

/-- **Restriction independence implies ergodicity**. -/
theorem InfiniteRelExchangeableLaw.RestrictionIndependent.isErgodic [Fintype S.Srt]
    {M : InfiniteRelExchangeableLaw S} (hM : M.RestrictionIndependent) :
    M.IsErgodic := fun _ hs =>
  measure_invariant_eq_zero_or_one_of_restrictionIndependent hM hs

/-- **Ergodicity implies vertex-tail triviality**: every vertex-tail event is invariant
(`vertexTailAlgebra_le_invariantAlgebra`). -/
theorem InfiniteRelExchangeableLaw.IsErgodic.vertexTailTrivial
    {M : InfiniteRelExchangeableLaw S} (hM : M.IsErgodic) :
    M.VertexTailTrivial := fun s hs =>
  hM s (RelStructure.vertexTailAlgebra_le_invariantAlgebra s hs)

/-- **Ergodicity ↔ dissociation**: closing `RestrictionIndependent ⟹ IsErgodic ⟹
VertexTailTrivial` against the R3b equivalences. -/
theorem isErgodic_iff_isDissociated [Fintype S.Srt] (M : InfiniteRelExchangeableLaw S) :
    M.IsErgodic ↔ M.IsDissociated :=
  ⟨fun hM => (isDissociated_iff_vertexTailTrivial M).mpr hM.vertexTailTrivial,
    fun hM => ((isDissociated_iff_restrictionIndependent M).mp hM).isErgodic⟩

/-- **Ergodicity ↔ restriction independence**. -/
theorem isErgodic_iff_restrictionIndependent [Fintype S.Srt]
    (M : InfiniteRelExchangeableLaw S) :
    M.IsErgodic ↔ M.RestrictionIndependent :=
  (isErgodic_iff_isDissociated M).trans (isDissociated_iff_restrictionIndependent M)

/-- **Ergodicity ↔ vertex-tail triviality**. -/
theorem isErgodic_iff_vertexTailTrivial [Fintype S.Srt] (M : InfiniteRelExchangeableLaw S) :
    M.IsErgodic ↔ M.VertexTailTrivial :=
  (isErgodic_iff_isDissociated M).trans (isDissociated_iff_vertexTailTrivial M)

end RelSignature
