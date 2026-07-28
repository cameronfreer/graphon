/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRankAlgebra
import Graphon.RelPollingInfrastructure

/-!
# The family polling tail (R4 converse piece 3, #107)

The conditioning tower for the peel step of rankwise relative independence. Fix a finite family
`F` of rank-`n` supports and a distinguished member `A₀`. For each other member `A` write

`C_A = A ∩ A₀` (of rank `< n`, by `card_inter_lt_of_ne`) and `D_A = A \ A₀`,

and poll the `D_A` *together*, as one common copy of their union, so overlaps — hence equality
patterns — survive. The tower is

`rankTailAlgebra q = lowerRankAlgebra n ⊔ ⨆_{m ≥ q} ⨆_{A ∈ F.erase A₀} fixingAlgebra (C_A ∪ Q_m D_A)`.

The spacing bound `K` and the tail cutoff `q` are deliberately named differently: `K` is fixed
once, above the whole finite union *including* `A₀`, so every subset copy shares one geometry,
while `q` varies along the tail.

No nonemptiness hypothesis: the empty family and rank zero degenerate through the definitions.

## The shift is not finitely supported

`pollPerm K U` moves one block at *every* slot, so it displaces infinitely many vertices. Two
consequences for the peel argument, both easy to get wrong:

* the invariance of the conditioning factor must come from the **arbitrary-permutation** form of
  `comap_relabel_lowerRankAlgebra`, not a finite-support version;
* the distinguished `fixingAlgebra A₀`-event is **not** known to be exactly invariant under the
  shift. Its invariance is only modulo the law, from
  `InfiniteRelExchangeableLaw.relabel_preimage_ae_eq_of_fixingAlgebra`. Nothing structural breaks:
  the tail engine takes `f ∘ T =ᵐ f`, not a strict equality.

Finitely supported test permutations appear only in the *pairwise* argument's raw intersection
identification, which does not generalize here — see `RelStructure.rankTailAlgebra` below.
-/

open MeasureTheory

namespace RelSignature

variable {S : RelSignature}

/-! ### The polled union and its fixation of `A₀` -/

open scoped Classical in
/-- **The polled union**: the vertices of the non-distinguished members lying outside `A₀`,
collected into one set. Polling moves *this* — not each member separately — so the overlaps
between members, hence their equality patterns, survive. -/
noncomputable def pollUnion (F : Finset (Finset (Σ s : S.Srt, Vinfinite S s)))
    (A₀ : Finset (Σ s : S.Srt, Vinfinite S s)) : Finset (Σ s : S.Srt, Vinfinite S s) :=
  (F.erase A₀).biUnion fun A => A \ A₀

open scoped Classical in
/-- Each member's own polled part sits inside the common union — the copies are cut from one
block. -/
theorem sdiff_subset_pollUnion {F : Finset (Finset (Σ s : S.Srt, Vinfinite S s))}
    {A₀ A : Finset (Σ s : S.Srt, Vinfinite S s)} (hA : A ∈ F.erase A₀) :
    A \ A₀ ⊆ pollUnion F A₀ := by
  classical
  exact Finset.subset_biUnion_of_mem (fun A => A \ A₀) hA

open scoped Classical in
/-- The polled union is disjoint from `A₀` by construction. -/
theorem notMem_pollUnion_of_mem {F : Finset (Finset (Σ s : S.Srt, Vinfinite S s))}
    {A₀ : Finset (Σ s : S.Srt, Vinfinite S s)} {v : Σ s : S.Srt, Vinfinite S s} (hv : v ∈ A₀) :
    v ∉ pollUnion F A₀ := by
  classical
  simp only [pollUnion, Finset.mem_biUnion, not_exists]
  rintro A ⟨-, hmem⟩
  exact (Finset.mem_sdiff.mp hmem).2 hv

open scoped Classical in
/-- **The poll shift fixes `A₀` pointwise.** The shift moves only residues lying in the polled
union, and `A₀` is disjoint from it and below the spacing bound.

This is exact — a genuine pointwise fixation — even though the shift itself is *not* finitely
supported. What is only a.e. is the invariance of a `fixingAlgebra A₀`-*event* under the shift;
that comes separately from
`InfiniteRelExchangeableLaw.relabel_preimage_ae_eq_of_fixingAlgebra`. -/
theorem pollPerm_pollUnion_fixes {K : ℕ} [NeZero K]
    {F : Finset (Finset (Σ s : S.Srt, Vinfinite S s))}
    {A₀ : Finset (Σ s : S.Srt, Vinfinite S s)} (hK : ∀ v ∈ A₀, v.2 < K) :
    ∀ v ∈ A₀, pollPerm K (pollUnion F A₀) v.1 v.2 = v.2 := fun v hv =>
  pollPerm_apply_of_notMem K (pollUnion F A₀) (hK v hv) (notMem_pollUnion_of_mem hv)

open scoped Classical in
/-- **The family polling tail.** The conditioning factor of the peel step at cutoff `q`. -/
@[implicit_reducible]
noncomputable def RelStructure.rankTailAlgebra (n K : ℕ)
    (F : Finset (Finset (Σ s : S.Srt, Vinfinite S s)))
    (A₀ : Finset (Σ s : S.Srt, Vinfinite S s)) (q : ℕ) :
    MeasurableSpace (RelStructure S (Vinfinite S)) :=
  RelStructure.lowerRankAlgebra n ⊔
    ⨆ m, ⨆ _ : q ≤ m, ⨆ A ∈ F.erase A₀,
      RelStructure.fixingAlgebra ((A ∩ A₀) ∪ pollBlock K (A \ A₀) m)

open scoped Classical in
theorem RelStructure.rankTailAlgebra_le (n K : ℕ)
    (F : Finset (Finset (Σ s : S.Srt, Vinfinite S s)))
    (A₀ : Finset (Σ s : S.Srt, Vinfinite S s)) (q : ℕ) :
    RelStructure.rankTailAlgebra (S := S) n K F A₀ q ≤
      (inferInstance : MeasurableSpace (RelStructure S (Vinfinite S))) :=
  sup_le (RelStructure.lowerRankAlgebra_le n)
    (iSup₂_le fun _ _ => iSup₂_le fun _ _ => RelStructure.fixingAlgebra_le _)

open scoped Classical in
/-- **Antitone in the cutoff**: a later cutoff admits fewer generators. -/
theorem RelStructure.rankTailAlgebra_antitone (n K : ℕ)
    (F : Finset (Finset (Σ s : S.Srt, Vinfinite S s)))
    (A₀ : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Antitone (RelStructure.rankTailAlgebra (S := S) n K F A₀) := by
  intro p q hpq
  -- unfold both sides rather than unifying through the reducible definition, which blows up
  simp only [RelStructure.rankTailAlgebra]
  refine sup_le le_sup_left (iSup₂_le fun m hm => ?_)
  exact le_trans (le_iSup₂_of_le m (hpq.trans hm) le_rfl) le_sup_right

open scoped Classical in
/-- **The lower-rank factor sits inside every stage**, as a summand. -/
theorem RelStructure.lowerRankAlgebra_le_rankTailAlgebra (n K : ℕ)
    (F : Finset (Finset (Σ s : S.Srt, Vinfinite S s)))
    (A₀ : Finset (Σ s : S.Srt, Vinfinite S s)) (q : ℕ) :
    RelStructure.lowerRankAlgebra (S := S) n ≤ RelStructure.rankTailAlgebra n K F A₀ q :=
  le_sup_left

open scoped Classical in
/-- **At cutoff `0` the tower contains the original conditioning factor of the peel step.**
Poll slot `0` is the identity, and `(A ∩ A₀) ∪ (A \ A₀) = A`, so each other member's own fixing
algebra is a generator. -/
theorem RelStructure.le_rankTailAlgebra_zero (n K : ℕ)
    (F : Finset (Finset (Σ s : S.Srt, Vinfinite S s)))
    (A₀ : Finset (Σ s : S.Srt, Vinfinite S s)) :
    RelStructure.lowerRankAlgebra (S := S) n ⊔
        (⨆ A ∈ F.erase A₀, RelStructure.fixingAlgebra A) ≤
      RelStructure.rankTailAlgebra n K F A₀ 0 := by
  classical
  refine sup_le le_sup_left (iSup₂_le fun A hA => le_sup_right.trans' ?_)
  refine le_trans (le_of_eq ?_) (le_iSup₂_of_le 0 le_rfl (le_iSup₂_of_le A hA le_rfl))
  congr 1
  rw [pollBlock_zero]
  refine (Finset.ext fun v => ?_).symm
  by_cases h : v ∈ A₀ <;> simp [h]

/-! ### The exact tail shift -/

section Shift

variable [Fintype S.Srt] {n K : ℕ} [NeZero K]
  {F : Finset (Finset (Σ s : S.Srt, Vinfinite S s))}
  {A₀ : Finset (Σ s : S.Srt, Vinfinite S s)}

open scoped Classical in
/-- Every vertex of the polled union lies below the spacing bound, once `K` bounds the whole
family. -/
theorem lt_of_mem_pollUnion (hKF : ∀ A ∈ F, ∀ v ∈ A, v.2 < K)
    {v : Σ s : S.Srt, Vinfinite S s} (hv : v ∈ pollUnion F A₀) : v.2 < K := by
  classical
  simp only [pollUnion, Finset.mem_biUnion] at hv
  obtain ⟨A, hA, hvA⟩ := hv
  exact hKF A (Finset.mem_of_mem_erase hA) v (Finset.mem_sdiff.mp hvA).1

open scoped Classical in
/-- **Layer 1 — the image identity for one copied support.** The shift fixes the `C_A` part
pointwise and advances the block part by one slot. -/
theorem image_pollPerm_generator (hKF : ∀ A ∈ F, ∀ v ∈ A, v.2 < K)
    (hK₀ : ∀ v ∈ A₀, v.2 < K) {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    (hA : A ∈ F.erase A₀) (m : ℕ) :
    ((A ∩ A₀) ∪ pollBlock K (A \ A₀) m).image
        (Sigma.map id fun s => ⇑(pollPerm K (pollUnion F A₀) s)) =
      (A ∩ A₀) ∪ pollBlock K (A \ A₀) (m + 1) := by
  classical
  rw [Finset.image_union,
    image_pollPerm_of_notMem
      (fun v hv => hK₀ v (Finset.mem_inter.mp hv).2)
      (fun v hv => notMem_pollUnion_of_mem (Finset.mem_inter.mp hv).2),
    pollBlock_image_pollPerm_of_subset (sdiff_subset_pollUnion hA)
      (fun v hv => lt_of_mem_pollUnion hKF hv)]

open scoped Classical in
/-- **Layer 2 — the comap equality for one generator.** Uses the arbitrary-permutation transport,
since the shift is not finitely supported. -/
theorem comap_relabel_fixingAlgebra_generator (hKF : ∀ A ∈ F, ∀ v ∈ A, v.2 < K)
    (hK₀ : ∀ v ∈ A₀, v.2 < K) {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    (hA : A ∈ F.erase A₀) (m : ℕ) :
    MeasurableSpace.comap (RelStructure.relabel (pollPerm K (pollUnion F A₀)))
        (RelStructure.fixingAlgebra ((A ∩ A₀) ∪ pollBlock K (A \ A₀) m)) =
      RelStructure.fixingAlgebra ((A ∩ A₀) ∪ pollBlock K (A \ A₀) (m + 1)) := by
  classical
  rw [RelStructure.fixingAlgebra_comap_relabel_of_fintype,
    image_pollPerm_generator hKF hK₀ hA m]

open scoped Classical in
/-- **The exact tail shift** (layers 3–5): pulling the tail algebra back along the poll shift is
the next stage of the tail.

The three summands move independently: the lower-rank factor is carried to itself by
`comap_relabel_lowerRankAlgebra` — which is why that lemma had to allow an arbitrary permutation,
the shift not being finitely supported — each generator advances one slot by layer 2, and the
inner tail reindexes from `m ≥ q` to `m ≥ q + 1`. -/
theorem RelStructure.comap_relabel_rankTailAlgebra (hKF : ∀ A ∈ F, ∀ v ∈ A, v.2 < K)
    (hK₀ : ∀ v ∈ A₀, v.2 < K) (q : ℕ) :
    MeasurableSpace.comap (RelStructure.relabel (pollPerm K (pollUnion F A₀)))
        (RelStructure.rankTailAlgebra (S := S) n K F A₀ q) =
      RelStructure.rankTailAlgebra n K F A₀ (q + 1) := by
  classical
  -- the generator rewrite is conditional on `A ∈ F.erase A₀`, so it is applied per member
  -- inside the bounds rather than by `simp`
  simp only [RelStructure.rankTailAlgebra, MeasurableSpace.comap_sup,
    MeasurableSpace.comap_iSup, RelStructure.comap_relabel_lowerRankAlgebra]
  congr 1
  refine le_antisymm (iSup₂_le fun m hm => iSup₂_le fun A hA => ?_)
    (iSup₂_le fun m hm => iSup₂_le fun A hA => ?_)
  · rw [comap_relabel_fixingAlgebra_generator hKF hK₀ hA m]
    exact le_iSup₂_of_le (m + 1) (by omega) (le_iSup₂_of_le A hA le_rfl)
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    refine le_iSup₂_of_le m' (by omega) (le_iSup₂_of_le A hA ?_)
    rw [comap_relabel_fixingAlgebra_generator hKF hK₀ hA m']

end Shift

/-! ### Stabilization of the conditional expectation -/

section Stabilization

variable [Fintype S.Srt] [Countable S.Rel] {n K : ℕ} [NeZero K]
  {F : Finset (Finset (Σ s : S.Srt, Vinfinite S s))}
  {A₀ : Finset (Σ s : S.Srt, Vinfinite S s)}

open scoped Classical in
/-- **The distinguished indicator is a.e. invariant under the poll shift.**

The shift fixes `A₀` pointwise and exactly (`pollPerm_pollUnion_fixes`), but it is not finitely
supported, so a `fixingAlgebra A₀`-event is only invariant *modulo the law* — that is what
`relabel_preimage_ae_eq_of_fixingAlgebra` supplies. The tail engine takes exactly this. -/
theorem indicator_comp_relabel_pollPerm_ae_eq (M : InfiniteRelExchangeableLaw S)
    (hK₀ : ∀ v ∈ A₀, v.2 < K) {E : Set (RelStructure S (Vinfinite S))}
    (hE : MeasurableSet[RelStructure.fixingAlgebra A₀] E) :
    (E.indicator fun _ => (1 : ℝ)) ∘
        RelStructure.relabel (pollPerm K (pollUnion F A₀)) =ᵐ[
      (M.law : Measure (RelStructure S (Vinfinite S)))] E.indicator fun _ => (1 : ℝ) := by
  classical
  have hset := M.relabel_preimage_ae_eq_of_fixingAlgebra hE
    (pollPerm_pollUnion_fixes (F := F) hK₀)
  have hcomp : (E.indicator fun _ => (1 : ℝ)) ∘
      RelStructure.relabel (pollPerm K (pollUnion F A₀)) =
      (RelStructure.relabel (pollPerm K (pollUnion F A₀)) ⁻¹' E).indicator fun _ => (1 : ℝ) := by
    funext X
    simp only [Function.comp_apply, Set.indicator_apply, Set.mem_preimage]
  rw [hcomp]
  exact indicator_ae_eq_of_ae_eq_set hset

open scoped Classical in
/-- **Consecutive stabilization**: along the tail, the conditional expectation of the
distinguished indicator does not change.

All five inputs are now in place — the shift is measure preserving, the tail is antitone, the
comap identity is exact, the indicator is square-integrable, and its invariance is a.e. -/
theorem condExp_indicator_rankTailAlgebra_succ (M : InfiniteRelExchangeableLaw S)
    (hKF : ∀ A ∈ F, ∀ v ∈ A, v.2 < K) (hK₀ : ∀ v ∈ A₀, v.2 < K)
    {E : Set (RelStructure S (Vinfinite S))}
    (hE : MeasurableSet[RelStructure.fixingAlgebra A₀] E) (q : ℕ) :
    (M.law : Measure (RelStructure S (Vinfinite S)))[E.indicator fun _ => (1 : ℝ)|
          RelStructure.rankTailAlgebra n K F A₀ q]
        =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))]
      (M.law : Measure (RelStructure S (Vinfinite S)))[E.indicator fun _ => (1 : ℝ)|
        RelStructure.rankTailAlgebra n K F A₀ (q + 1)] := by
  classical
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  exact condExp_ae_eq_condExp_of_comap_eq (measurable_relabel _)
    (M.measurePreserving_relabel _)
    (RelStructure.rankTailAlgebra_le n K F A₀ q)
    (RelStructure.rankTailAlgebra_antitone n K F A₀ (Nat.le_succ q))
    (RelStructure.comap_relabel_rankTailAlgebra hKF hK₀ q)
    (memLp_indicator_const 2 hE.1 1 (Or.inr (measure_ne_top _ _)))
    (indicator_comp_relabel_pollPerm_ae_eq M hK₀ hE)

end Stabilization

/-! ### The Lévy passage -/

section Levy

open Filter Topology

variable [Fintype S.Srt] [Countable S.Rel] {n K : ℕ} [NeZero K]
  {F : Finset (Finset (Σ s : S.Srt, Vinfinite S s))}
  {A₀ : Finset (Σ s : S.Srt, Vinfinite S s)}

open scoped Classical in
/-- The conditional expectation is constant along the whole tail, by induction from the
consecutive equality. -/
private theorem condExp_indicator_rankTailAlgebra_eq_zero (M : InfiniteRelExchangeableLaw S)
    (hKF : ∀ A ∈ F, ∀ v ∈ A, v.2 < K) (hK₀ : ∀ v ∈ A₀, v.2 < K)
    {E : Set (RelStructure S (Vinfinite S))}
    (hE : MeasurableSet[RelStructure.fixingAlgebra A₀] E) (q : ℕ) :
    (M.law : Measure (RelStructure S (Vinfinite S)))[E.indicator fun _ => (1 : ℝ)|
          RelStructure.rankTailAlgebra n K F A₀ 0]
        =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))]
      (M.law : Measure (RelStructure S (Vinfinite S)))[E.indicator fun _ => (1 : ℝ)|
        RelStructure.rankTailAlgebra n K F A₀ q] := by
  induction q with
  | zero => exact EventuallyEq.refl _ _
  | succ p ih =>
      exact ih.trans (condExp_indicator_rankTailAlgebra_succ M hKF hK₀ hE p)

open scoped Classical in
/-- **The Lévy passage**: the conditional expectation over the whole tail agrees with the one
over its intersection.

Indicator-specific and private, following the pairwise proof: the approximating sequence is a.e.
constant by the induction above, so its `L¹` distance to the Lévy limit is a constant sequence
tending to `0`, hence `0`. -/
private theorem condExp_indicator_rankTailAlgebra_iInf (M : InfiniteRelExchangeableLaw S)
    (hKF : ∀ A ∈ F, ∀ v ∈ A, v.2 < K) (hK₀ : ∀ v ∈ A₀, v.2 < K)
    {E : Set (RelStructure S (Vinfinite S))}
    (hE : MeasurableSet[RelStructure.fixingAlgebra A₀] E) :
    (M.law : Measure (RelStructure S (Vinfinite S)))[E.indicator fun _ => (1 : ℝ)|
          RelStructure.rankTailAlgebra n K F A₀ 0]
        =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))]
      (M.law : Measure (RelStructure S (Vinfinite S)))[E.indicator fun _ => (1 : ℝ)|
        ⨅ q, RelStructure.rankTailAlgebra n K F A₀ q] := by
  classical
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  set μ : Measure (RelStructure S (Vinfinite S)) :=
    (M.law : Measure (RelStructure S (Vinfinite S))) with hμ
  set f : RelStructure S (Vinfinite S) → ℝ := E.indicator fun _ => (1 : ℝ) with hf
  have hfL : MemLp f 2 μ := memLp_indicator_const 2 hE.1 1 (Or.inr (measure_ne_top _ _))
  have hint : Integrable f μ := hfL.integrable one_le_two
  have hlevy := tendsto_eLpNorm_condExp_iInf (RelStructure.rankTailAlgebra (S := S) n K F A₀)
    (RelStructure.rankTailAlgebra_antitone n K F A₀)
    (RelStructure.rankTailAlgebra_le n K F A₀) hint
  have hconst : ∀ q,
      eLpNorm (μ[f|RelStructure.rankTailAlgebra n K F A₀ q] -
          μ[f|⨅ p, RelStructure.rankTailAlgebra (S := S) n K F A₀ p]) 1 μ =
        eLpNorm (μ[f|RelStructure.rankTailAlgebra n K F A₀ 0] -
          μ[f|⨅ p, RelStructure.rankTailAlgebra (S := S) n K F A₀ p]) 1 μ :=
    fun q => eLpNorm_congr_ae
      ((condExp_indicator_rankTailAlgebra_eq_zero M hKF hK₀ hE q).symm.sub
        (EventuallyEq.refl _ _))
  have hzero : eLpNorm (μ[f|RelStructure.rankTailAlgebra n K F A₀ 0] -
      μ[f|⨅ p, RelStructure.rankTailAlgebra (S := S) n K F A₀ p]) 1 μ = 0 :=
    (tendsto_nhds_unique (by simpa only [hconst] using hlevy) tendsto_const_nhds).symm
  have hinfle : (⨅ p, RelStructure.rankTailAlgebra (S := S) n K F A₀ p) ≤
      (inferInstance : MeasurableSpace (RelStructure S (Vinfinite S))) :=
    (iInf_le _ 0).trans (RelStructure.rankTailAlgebra_le n K F A₀ 0)
  have hmeas : AEStronglyMeasurable
      (μ[f|RelStructure.rankTailAlgebra n K F A₀ 0] -
        μ[f|⨅ p, RelStructure.rankTailAlgebra (S := S) n K F A₀ p]) μ :=
    ((stronglyMeasurable_condExp.mono (RelStructure.rankTailAlgebra_le n K F A₀ 0)).sub
      (stronglyMeasurable_condExp.mono hinfle)).aestronglyMeasurable
  have hsub := (eLpNorm_eq_zero_iff hmeas one_ne_zero).mp hzero
  filter_upwards [hsub] with x hx
  have hx0 : (μ[f|RelStructure.rankTailAlgebra n K F A₀ 0]) x -
      (μ[f|⨅ p, RelStructure.rankTailAlgebra (S := S) n K F A₀ p]) x = 0 := hx
  linarith

end Levy

end RelSignature
