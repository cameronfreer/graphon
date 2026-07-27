/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelFixingAlgebra
import Graphon.RelErgodicLinks
import Graphon.RelPollingInfrastructure
import Mathlib.Probability.Independence.Conditional

/-!
# Conditional independence of the fixing σ-algebras (R4 converse piece 2b, #107)

The relative-independence core of the converse representation theorem, following Austin,
*On exchangeable random variables and the statistics of large graphs and hypergraphs*
(Probab. Surveys 2008, arXiv:0801.1698), Lemma 3.11 and Proposition 3.12 (pp. 107–108),
whose mechanism is the `L²` "tail property" squeeze of the proof of Theorem 3.1 (p. 99);
the closest Kallenberg precursor is Lemma 7.6 (*Probabilistic Symmetries*, pp. 308–322).
Target (public, final layer): for **every** exchangeable law `M` — no dissociation —

`CondIndep (fixingAlgebra (A ∩ B)) (fixingAlgebra A) (fixingAlgebra B)
  (fixingAlgebra_le _) M.law`.

This first layer is the measure-theoretic engine, all `private`:

* the **`L²` squeeze** `condExp_ae_eq_condExp_of_integral_sq_le`: nested conditioning
  algebras whose conditional expectations have comparable energies produce equal
  conditional expectations (Pythagoras for the projections);
* **transport** `condExp_comp_of_measurePreserving`: conditional expectation commutes with
  a measure-preserving map along `MeasurableSpace.comap`;
* the **tail-property engine** `condExp_ae_eq_condExp_of_comap_eq` combining the two: if a
  measure-preserving `T` fixes `f` a.e. and pulls the conditioning algebra `m₁` back to a
  sub-algebra `m₂ ≤ m₁`, then `μ[f|m₁] =ᵐ[μ] μ[f|m₂]` — Austin's Theorem 3.1 step,
  abstracted.

No completion and no law enter any definition here. On top of the engine sit the **a.e.
invariance** of `fixingAlgebra A`-events under *every* sortwise permutation fixing `A`
(`relabel_preimage_ae_eq_of_fixingAlgebra`, the `f ∘ T =ᵐ f` input), and the **poll geometry**
the engine runs on:

* `pollIndex` / `pollShift` — poll slots along a two-sided `ℤ`-orbit transported to `ℕ`. The
  two-sidedness is forced: a *unilateral* shift of the blocks is not a bijection (slot `0`
  would have no preimage), so the negative half serves as predecessor reservoir;
* `pollBlock` / `pollPerm` — the copies `Q m` of `D = B \ A` in slot `m` (with `Q 0 = D`) and
  the sortwise permutation that carries `Q m` onto `Q (m+1)` while fixing every vertex below
  the layout bound outside `D`, in particular all of `A`;
* `pollTailAlgebra` — the tail **joins** `𝒯 n = ⨆_{m ≥ n} fixingAlgebra (C ∪ Q m)`, with
  `C = A ∩ B`. The individual `fixingAlgebra (C ∪ Q m)` are *not* usable: over distinct deep
  blocks they are pairwise incomparable (hence no antitone sequence for Lévy downward), and
  `fixingAlgebra (C ∪ Q m) ≤ fixingAlgebra B` is false — monotonicity would demand
  `C ∪ Q m ⊆ B`, while `Q m` lies outside `B`. The joins are antitone, dominate
  `fixingAlgebra B` at `n = 0`, satisfy `comap (relabel ρ) (𝒯 n) = 𝒯 (n+1)` exactly, and have
  `⨅ n, 𝒯 n = fixingAlgebra C` — the last a **raw** σ-algebra equality, no law and no null
  sets, available because the generators are fixing algebras rather than coordinate-generated
  window algebras (an earlier draft of this file carried such window algebras; the join route
  makes them unnecessary, so they are gone).

The layer closes with the **reduction** `condExp_fixingAlgebra_ae_eq_condExp_inter`:
`μ[f|fixingAlgebra B] =ᵐ μ[f|fixingAlgebra (A ∩ B)]` for `f` a.e. invariant under the
permutations fixing `A`, and its indicator form for a `fixingAlgebra A`-event. This is the
`(⋆)` half of Austin's Proposition 3.12; the conditional-independence assembly is the next
layer.
-/

open MeasureTheory

open scoped ENNReal symmDiff

namespace RelSignature



/-! ### Invariance under a single permutation -/

section PermInvariant

variable {S : RelSignature}

/-- **The invariance algebra of a single sortwise permutation**: the events literally fixed by
one relabeling. Each `fixingAlgebra A` with `σ` in its stabilizer is contained in it, and —
being a σ-algebra — so is any *join* of such; this is what transfers invariance from the
generators of the tail joins to the whole join. -/
@[implicit_reducible]
private def permInvariantAlgebra (σ : ∀ _ : S.Srt, Equiv.Perm ℕ) :
    MeasurableSpace (RelStructure S (Vinfinite S)) where
  MeasurableSet' E := MeasurableSet E ∧ RelStructure.relabel σ ⁻¹' E = E
  measurableSet_empty := ⟨MeasurableSet.empty, Set.preimage_empty⟩
  measurableSet_compl := fun E hE => ⟨hE.1.compl, by rw [Set.preimage_compl, hE.2]⟩
  measurableSet_iUnion := fun f hf => ⟨MeasurableSet.iUnion fun i => (hf i).1, by
    rw [Set.preimage_iUnion]
    exact Set.iUnion_congr fun i => (hf i).2⟩

private theorem fixingAlgebra_le_permInvariantAlgebra {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    {σ : ∀ _ : S.Srt, Equiv.Perm ℕ} (hσ : SortwiseFixing (S := S) A σ) :
    RelStructure.fixingAlgebra A ≤ permInvariantAlgebra σ := fun _ hE => ⟨hE.1, hE.2 σ hσ⟩

end PermInvariant

/-! ### The tail joins of the poll factors -/

section PollTail

variable {S : RelSignature}

open scoped Classical in
/-- The `m`-th **poll factor's** vertex set: the conditioning set together with the `m`-th poll
block. -/
private noncomputable def pollFactor (C D : Finset (Σ s : S.Srt, Vinfinite S s)) (N m : ℕ) :
    Finset (Σ s : S.Srt, Vinfinite S s) :=
  C ∪ pollBlock N D m

open scoped Classical in
private theorem mem_pollFactor {C D : Finset (Σ s : S.Srt, Vinfinite S s)} {N m : ℕ}
    {v : Σ s : S.Srt, Vinfinite S s} : v ∈ pollFactor C D N m ↔ v ∈ C ∨ v ∈ pollBlock N D m :=
  Finset.mem_union

/-- **The tail join of the poll factors**: `⨆_{m ≥ n} fixingAlgebra (C ∪ Q m)`.

This — not the individual `fixingAlgebra (C ∪ Q m)` — is the object the tail engine runs on.
Individual poll factors over distinct deep blocks are pairwise *incomparable*, so they form no
antitone sequence, and `fixingAlgebra (C ∪ Q m) ≤ fixingAlgebra B` fails outright (monotonicity
would demand `C ∪ Q m ⊆ B`, whereas `Q m` was placed outside `B`). The joins repair both
defects at once: they are antitone in `n`, they dominate `fixingAlgebra B` at `n = 0`, the
shift pulls `𝒯 n` back exactly onto `𝒯 (n+1)`, and their intersection is `fixingAlgebra C`. -/
@[implicit_reducible]
private noncomputable def pollTailAlgebra (C D : Finset (Σ s : S.Srt, Vinfinite S s))
    (N n : ℕ) : MeasurableSpace (RelStructure S (Vinfinite S)) :=
  ⨆ m, ⨆ _ : n ≤ m, RelStructure.fixingAlgebra (pollFactor C D N m)

private theorem pollTailAlgebra_antitone (C D : Finset (Σ s : S.Srt, Vinfinite S s)) (N : ℕ) :
    Antitone (pollTailAlgebra C D N) := fun _ _ hn =>
  iSup₂_le fun m hm => le_iSup₂_of_le m (hn.trans hm) le_rfl

private theorem pollTailAlgebra_le (C D : Finset (Σ s : S.Srt, Vinfinite S s)) (N n : ℕ) :
    pollTailAlgebra C D N n ≤ (inferInstance : MeasurableSpace (RelStructure S (Vinfinite S))) :=
  iSup₂_le fun _ _ => RelStructure.fixingAlgebra_le _

/-- **The polled algebra dominates the `B`-factor**: poll slot `0` is `D` itself, so for
`B = C ∪ D` the algebra `fixingAlgebra B` is literally one of the generators of `𝒯 0`. -/
private theorem fixingAlgebra_le_pollTailAlgebra_zero {B C D : Finset (Σ s : S.Srt, Vinfinite S s)}
    {N : ℕ} (hB : ∀ v, v ∈ B ↔ v ∈ C ∨ v ∈ D) :
    RelStructure.fixingAlgebra B ≤ pollTailAlgebra C D N 0 :=
  le_iSup₂_of_le 0 le_rfl (le_of_eq (by
    congr 1
    exact Finset.ext fun v => by rw [hB v, mem_pollFactor, pollBlock_zero]))

/-- **Transport of the tail joins**: pulling `𝒯 n` back along the poll shift is exactly
`𝒯 (n+1)` — an equality of measurable spaces, obtained generator-by-generator from
`fixingAlgebra_comap_relabel_of_fintype` and the reindexing `m ↦ m + 1`. This is the
hypothesis `comap T m₁ = m₂` of the tail engine, with `m₂ ≤ m₁` supplied by antitonicity. -/
private theorem comap_relabel_pollTailAlgebra [Fintype S.Srt]
    {C D : Finset (Σ s : S.Srt, Vinfinite S s)} {N : ℕ} [NeZero N] (hC : ∀ v ∈ C, v.2 < N)
    (hCD : ∀ v ∈ C, v ∉ D) (hD : ∀ v ∈ D, v.2 < N) (n : ℕ) :
    MeasurableSpace.comap (RelStructure.relabel (pollPerm N D))
        (pollTailAlgebra C D N n) = pollTailAlgebra C D N (n + 1) := by
  classical
  have hgen : ∀ m : ℕ, MeasurableSpace.comap (RelStructure.relabel (pollPerm N D))
      (RelStructure.fixingAlgebra (pollFactor C D N m)) =
      RelStructure.fixingAlgebra (pollFactor C D N (m + 1)) := by
    intro m
    rw [RelStructure.fixingAlgebra_comap_relabel_of_fintype]
    congr 1
    refine Finset.ext fun v => ?_
    rw [mem_pollFactor, Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rcases mem_pollFactor.mp hw with hwC | hwQ
      · exact Or.inl (by
          rw [← image_pollPerm_of_notMem hC hCD]; exact Finset.mem_image_of_mem _ hwC)
      · exact Or.inr (by
          rw [← pollBlock_image_pollPerm hD]; exact Finset.mem_image_of_mem _ hwQ)
    · rintro (hvC | hvQ)
      · obtain ⟨w, hw, rfl⟩ :=
          Finset.mem_image.mp (by rw [image_pollPerm_of_notMem hC hCD]; exact hvC)
        exact ⟨w, mem_pollFactor.mpr (Or.inl hw), rfl⟩
      · obtain ⟨w, hw, rfl⟩ :=
          Finset.mem_image.mp (by rw [pollBlock_image_pollPerm hD]; exact hvQ)
        exact ⟨w, mem_pollFactor.mpr (Or.inr hw), rfl⟩
  rw [pollTailAlgebra, pollTailAlgebra]
  simp_rw [MeasurableSpace.comap_iSup, hgen]
  refine le_antisymm (iSup₂_le fun m hm => le_iSup₂_of_le (m + 1) (by omega) le_rfl)
    (iSup₂_le fun m hm => ?_)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact le_iSup₂_of_le m' (by omega) le_rfl

/-- **The tail joins shrink to the conditioning factor**: `⨅ n, 𝒯 n = fixingAlgebra C`, a *raw*
equality of σ-algebras — no law, no null sets. This is available precisely because the
generators are fixing algebras rather than window algebras: a finitely supported permutation
fixing `C` fixes every sufficiently deep poll block outright, hence lies in the stabilizer of
every generator of `𝒯 n` for large `n`, hence fixes every event of the join. -/
private theorem iInf_pollTailAlgebra {C D : Finset (Σ s : S.Srt, Vinfinite S s)}
    {N : ℕ} [NeZero N] :
    (⨅ n, pollTailAlgebra C D N n) = RelStructure.fixingAlgebra C := by
  have hproj : ∀ (n : ℕ) (E : Set (RelStructure S (Vinfinite S))),
      MeasurableSet[⨅ k, pollTailAlgebra C D N k] E → MeasurableSet[pollTailAlgebra C D N n] E :=
    fun n => iInf_le (fun k => pollTailAlgebra C D N k) n
  have hforward : ∀ E : Set (RelStructure S (Vinfinite S)),
      MeasurableSet[⨅ k, pollTailAlgebra C D N k] E →
        MeasurableSet[RelStructure.fixingAlgebra C] E := by
    intro E hE
    refine ⟨pollTailAlgebra_le C D N 0 E (hproj 0 E hE), ?_⟩
    intro σ hσ
    obtain ⟨M, hM⟩ := hσ.1
    obtain ⟨n, hn⟩ := exists_le_pollIndex M
    have hfix : ∀ m, n ≤ m → SortwiseFixing (S := S) (pollFactor C D N m) σ := by
      intro m hm
      refine ⟨hσ.1, fun v hv => ?_⟩
      rcases mem_pollFactor.mp hv with hvC | hvQ
      · exact hσ.2 v hvC
      · refine hM v.1 v.2 (le_trans ?_ (le_of_mem_pollBlock hvQ))
        calc M = M * 1 := (Nat.mul_one M).symm
          _ ≤ pollIndex m * N :=
            Nat.mul_le_mul (hn m hm) (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
    have hle : pollTailAlgebra C D N n ≤ permInvariantAlgebra σ := by
      rw [pollTailAlgebra]
      exact iSup₂_le fun m hm => fixingAlgebra_le_permInvariantAlgebra (hfix m hm)
    exact (hle E (hproj n E hE)).2
  refine le_antisymm hforward (le_iInf fun n => ?_)
  rw [pollTailAlgebra]
  exact le_iSup₂_of_le n le_rfl
    (RelStructure.fixingAlgebra_mono fun v hv => mem_pollFactor.mpr (Or.inl hv))

end PollTail

/-! ### The core reduction: conditioning on `𝓕 B` collapses to `𝓕 (A ∩ B)` -/

section Reduction

open Filter Topology

variable {S : RelSignature}

/-- **The polled reduction**, in the raw form the poll geometry produces it: for a
square-integrable `f` that is a.e. invariant under every sortwise permutation fixing `A`,
conditioning on `fixingAlgebra B` is conditioning on `fixingAlgebra C`, whenever `B` splits as
`C ⊔ D` with `D` laid out below the bound `N` and disjoint from `A ∪ C`.

The proof is Austin's polling argument (arXiv:0801.1698, Prop. 3.12) run on the tail joins:
the shift `pollPerm N D` fixes `A`, so the tail engine gives `μ[f|𝒯 n] =ᵐ μ[f|𝒯 (n+1)]` at
every `n`; induction makes the whole sequence a.e. constant; Lévy downward
(`tendsto_eLpNorm_condExp_iInf`) identifies its `L¹` limit with `μ[f|⨅ n, 𝒯 n]`, which
`iInf_pollTailAlgebra` rewrites as `μ[f|fixingAlgebra C]`; and the tower property over
`fixingAlgebra B ≤ 𝒯 0` transfers the conclusion back to `B`.

No dissociation is used, and the degenerate case `B ⊆ A` needs no separate treatment: there
`D = ∅`, every poll block is empty, `𝒯 n = fixingAlgebra C` throughout, and each step above
holds trivially. -/
private theorem condExp_fixingAlgebra_ae_eq_of_poll [Fintype S.Srt]
    (M : InfiniteRelExchangeableLaw S)
    {A B C D : Finset (Σ s : S.Srt, Vinfinite S s)} {N : ℕ} [NeZero N]
    (hC : ∀ v ∈ C, v.2 < N) (hCD : ∀ v ∈ C, v ∉ D) (hD : ∀ v ∈ D, v.2 < N)
    (hA : ∀ v ∈ A, v.2 < N) (hAD : ∀ v ∈ A, v ∉ D)
    (hB : ∀ v, v ∈ B ↔ v ∈ C ∨ v ∈ D) (hCB : C ⊆ B)
    {f : RelStructure S (Vinfinite S) → ℝ}
    (hf : MemLp f 2 (M.law : Measure (RelStructure S (Vinfinite S))))
    (hinv : ∀ σ : ∀ _ : S.Srt, Equiv.Perm ℕ, (∀ v ∈ A, σ v.1 v.2 = v.2) →
      f ∘ RelStructure.relabel σ =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))] f) :
    (M.law : Measure (RelStructure S (Vinfinite S)))[f|RelStructure.fixingAlgebra B]
        =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))]
      (M.law : Measure (RelStructure S (Vinfinite S)))[f|RelStructure.fixingAlgebra C] := by
  set μ : Measure (RelStructure S (Vinfinite S)) :=
    (M.law : Measure (RelStructure S (Vinfinite S))) with hμ
  haveI : IsProbabilityMeasure μ := M.law.2
  have hint : Integrable f μ := hf.integrable one_le_two
  have hinf : (⨅ n, pollTailAlgebra C D N n) = RelStructure.fixingAlgebra C :=
    iInf_pollTailAlgebra
  -- the poll shift fixes every vertex of `A`, so stage-1b invariance applies to it
  have hfρ : f ∘ RelStructure.relabel (pollPerm N D) =ᵐ[μ] f :=
    hinv _ fun v hv => pollPerm_apply_of_notMem N D (hA v hv) (hAD v hv)
  -- step 1: the tail engine stabilizes the conditional expectations along the tail joins
  have hstep : ∀ n, μ[f|pollTailAlgebra C D N n] =ᵐ[μ] μ[f|pollTailAlgebra C D N (n + 1)] :=
    fun n => condExp_ae_eq_condExp_of_comap_eq (measurable_relabel _)
      (M.measurePreserving_relabel _) (pollTailAlgebra_le C D N n)
      (pollTailAlgebra_antitone C D N (Nat.le_succ n))
      (comap_relabel_pollTailAlgebra hC hCD hD n) hf hfρ
  have hstab : ∀ n, μ[f|pollTailAlgebra C D N 0] =ᵐ[μ] μ[f|pollTailAlgebra C D N n] := by
    intro n
    induction n with
    | zero => exact EventuallyEq.refl _ _
    | succ k ih => exact ih.trans (hstep k)
  -- step 2: the `L¹` limit of an a.e. constant sequence is that constant
  have hlevy := tendsto_eLpNorm_condExp_iInf (pollTailAlgebra C D N)
    (pollTailAlgebra_antitone C D N) (pollTailAlgebra_le C D N) hint
  have hconst : ∀ n,
      eLpNorm (μ[f|pollTailAlgebra C D N n] - μ[f|⨅ k, pollTailAlgebra C D N k]) 1 μ =
      eLpNorm (μ[f|pollTailAlgebra C D N 0] - μ[f|⨅ k, pollTailAlgebra C D N k]) 1 μ :=
    fun n => eLpNorm_congr_ae ((hstab n).symm.sub (EventuallyEq.refl _ _))
  have hzero :
      eLpNorm (μ[f|pollTailAlgebra C D N 0] - μ[f|⨅ k, pollTailAlgebra C D N k]) 1 μ = 0 :=
    (tendsto_nhds_unique (by simpa only [hconst] using hlevy) tendsto_const_nhds).symm
  have hinfle : (⨅ k, pollTailAlgebra C D N k) ≤
      (inferInstance : MeasurableSpace (RelStructure S (Vinfinite S))) := by
    rw [hinf]; exact RelStructure.fixingAlgebra_le C
  have hT0 : μ[f|pollTailAlgebra C D N 0] =ᵐ[μ] μ[f|RelStructure.fixingAlgebra C] := by
    have hmeas : AEStronglyMeasurable
        (μ[f|pollTailAlgebra C D N 0] - μ[f|⨅ k, pollTailAlgebra C D N k]) μ :=
      ((stronglyMeasurable_condExp.mono (pollTailAlgebra_le C D N 0)).sub
        (stronglyMeasurable_condExp.mono hinfle)).aestronglyMeasurable
    have hsub := (eLpNorm_eq_zero_iff hmeas one_ne_zero).mp hzero
    rw [← hinf]
    filter_upwards [hsub] with x hx
    have hx0 : (μ[f|pollTailAlgebra C D N 0]) x - (μ[f|⨅ k, pollTailAlgebra C D N k]) x = 0 := hx
    linarith
  -- step 3: tower over `fixingAlgebra B ≤ 𝒯 0`
  calc μ[f|RelStructure.fixingAlgebra B]
      =ᵐ[μ] μ[μ[f|pollTailAlgebra C D N 0]|RelStructure.fixingAlgebra B] :=
        (condExp_condExp_of_le (fixingAlgebra_le_pollTailAlgebra_zero hB)
          (pollTailAlgebra_le C D N 0)).symm
    _ =ᵐ[μ] μ[μ[f|RelStructure.fixingAlgebra C]|RelStructure.fixingAlgebra B] :=
        condExp_congr_ae hT0
    _ = μ[f|RelStructure.fixingAlgebra C] :=
        condExp_of_stronglyMeasurable (RelStructure.fixingAlgebra_le B)
          (stronglyMeasurable_condExp.mono (RelStructure.fixingAlgebra_mono hCB))
          integrable_condExp

open scoped Classical in
/-- **The core reduction** (Austin, arXiv:0801.1698, Prop. 3.12; Kallenberg, *Probabilistic
Symmetries*, Lemma 7.6): for square-integrable `f` a.e. invariant under every sortwise
permutation fixing `A`, conditioning on `fixingAlgebra B` is conditioning on
`fixingAlgebra (A ∩ B)`. The poll blocks are the deep copies of `B \ A`, laid out above the
common bound of `A` and `B`. -/
private theorem condExp_fixingAlgebra_ae_eq_condExp_inter [Fintype S.Srt]
    (M : InfiniteRelExchangeableLaw S) (A B : Finset (Σ s : S.Srt, Vinfinite S s))
    {f : RelStructure S (Vinfinite S) → ℝ}
    (hf : MemLp f 2 (M.law : Measure (RelStructure S (Vinfinite S))))
    (hinv : ∀ σ : ∀ _ : S.Srt, Equiv.Perm ℕ, (∀ v ∈ A, σ v.1 v.2 = v.2) →
      f ∘ RelStructure.relabel σ =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))] f) :
    (M.law : Measure (RelStructure S (Vinfinite S)))[f|RelStructure.fixingAlgebra B]
        =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))]
      (M.law : Measure (RelStructure S (Vinfinite S)))[f|RelStructure.fixingAlgebra (A ∩ B)] := by
  set N : ℕ := max (A.sup fun v => v.2) (B.sup fun v => v.2) + 1 with hN
  haveI : NeZero N := ⟨Nat.succ_ne_zero _⟩
  have hAlt : ∀ v ∈ A, v.2 < N := fun v hv =>
    Nat.lt_succ_of_le (le_trans (Finset.le_sup hv) (le_max_left _ _))
  have hBlt : ∀ v ∈ B, v.2 < N := fun v hv =>
    Nat.lt_succ_of_le (le_trans (Finset.le_sup hv) (le_max_right _ _))
  refine condExp_fixingAlgebra_ae_eq_of_poll (D := B \ A) M
    (fun v hv => hAlt v (Finset.mem_inter.mp hv).1) (fun v hv hvD =>
      (Finset.mem_sdiff.mp hvD).2 (Finset.mem_inter.mp hv).1)
    (fun v hv => hBlt v (Finset.mem_sdiff.mp hv).1) hAlt
    (fun v hv hvD => (Finset.mem_sdiff.mp hvD).2 hv) (fun v => ?_)
    Finset.inter_subset_right hf hinv
  rw [Finset.mem_inter, Finset.mem_sdiff]
  by_cases hvA : v ∈ A <;> simp [hvA]

open scoped Classical in
/-- **The reduction for a fixing-algebra event** — the form the conditional-independence
assembly consumes: `E[1_E | 𝓕 B] =ᵐ E[1_E | 𝓕 (A ∩ B)]` for every `fixingAlgebra A`-event `E`.
The invariance hypothesis is supplied by stage 1b
(`relabel_preimage_ae_eq_of_fixingAlgebra`), which upgrades the finitary invariance built into
`fixingAlgebra A` to invariance under *every* sortwise permutation fixing `A`. -/
private theorem condExp_indicator_fixingAlgebra_ae_eq_condExp_inter [Fintype S.Srt]
    [Countable S.Rel] (M : InfiniteRelExchangeableLaw S)
    (A B : Finset (Σ s : S.Srt, Vinfinite S s)) {E : Set (RelStructure S (Vinfinite S))}
    (hE : MeasurableSet[RelStructure.fixingAlgebra A] E) :
    (M.law : Measure (RelStructure S (Vinfinite S)))[E.indicator fun _ => (1 : ℝ)|
          RelStructure.fixingAlgebra B]
        =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))]
      (M.law : Measure (RelStructure S (Vinfinite S)))[E.indicator fun _ => (1 : ℝ)|
        RelStructure.fixingAlgebra (A ∩ B)] := by
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  refine condExp_fixingAlgebra_ae_eq_condExp_inter M A B
    (memLp_indicator_const 2 hE.1 1 (Or.inr (measure_ne_top _ _))) fun σ hσ => ?_
  have hcomp : (E.indicator fun _ => (1 : ℝ)) ∘ RelStructure.relabel σ =
      (RelStructure.relabel σ ⁻¹' E).indicator fun _ => (1 : ℝ) := by
    funext X
    simp only [Function.comp_apply, Set.indicator_apply, Set.mem_preimage]
  rw [hcomp]
  exact indicator_ae_eq_of_ae_eq_set (M.relabel_preimage_ae_eq_of_fixingAlgebra hE hσ)

end Reduction

/-! ### The conditional-independence theorem -/

section CondIndep

open ProbabilityTheory

variable {S : RelSignature}

open scoped Classical in
/-- **Conditional independence of the fixing σ-algebras over their intersection** (Austin,
*On exchangeable random variables and the statistics of large graphs and hypergraphs*,
Probab. Surveys 2008, arXiv:0801.1698, Lemma 3.11 and Proposition 3.12, pp. 107–108;
Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Lemma 7.6, p. 308 — the
closest precursor there; Lemmas 7.18–7.19 belong to the later realization recursion, not to
this statement):

for **every** exchangeable law `M` — no dissociation — the fixing σ-algebras of two finite
tagged vertex sets are conditionally independent given the fixing σ-algebra of their
intersection.

The relativized `fixingAlgebra ∅ = invariantAlgebra` carries whatever global information the
law has (which is why no `NoNullary` hypothesis appears, and why dissociation is not needed:
under a dissociated law the conditioning factor at `A ∩ B = ∅` is trivial, but that is a
consequence, not an assumption). At `A = B`, and likewise at `A = ∅` or `B = ∅`, one outer
algebra equals the conditioning algebra and the statement is tautological; the content is at
disjoint nonempty `A, B`.

Proof: `condIndep_iff` reduces to a factorization of `μ⟦E₁ ∩ E₂ | 𝓕 (A ∩ B)⟧` for
`E₁ ∈ 𝓕 A`, `E₂ ∈ 𝓕 B`. Write `1_{E₁ ∩ E₂} = 1_{E₁} · 1_{E₂}`, tower from `𝓕 (A ∩ B)` through
`𝓕 B`, pull the `𝓕 B`-measurable `1_{E₂}` out, replace `E[1_{E₁} | 𝓕 B]` by
`E[1_{E₁} | 𝓕 (A ∩ B)]` using the polled reduction
`condExp_indicator_fixingAlgebra_ae_eq_condExp_inter`, and pull that `𝓕 (A ∩ B)`-measurable
factor out. -/
theorem InfiniteRelExchangeableLaw.condIndep_fixingAlgebra [Fintype S.Srt] [Countable S.Rel]
    (M : InfiniteRelExchangeableLaw S) (A B : Finset (Σ s : S.Srt, Vinfinite S s)) :
    CondIndep (RelStructure.fixingAlgebra (A ∩ B)) (RelStructure.fixingAlgebra A)
      (RelStructure.fixingAlgebra B) (RelStructure.fixingAlgebra_le _)
      (M.law : Measure (RelStructure S (Vinfinite S))) := by
  set μ : Measure (RelStructure S (Vinfinite S)) :=
    (M.law : Measure (RelStructure S (Vinfinite S))) with hμ
  haveI : IsProbabilityMeasure μ := M.law.2
  rw [condIndep_iff _ _ _ _ (RelStructure.fixingAlgebra_le A) (RelStructure.fixingAlgebra_le B)]
  intro t₁ t₂ ht₁ ht₂
  have hL₁ : MemLp (t₁.indicator fun _ => (1 : ℝ)) 2 μ :=
    memLp_indicator_const 2 ht₁.1 1 (Or.inr (measure_ne_top _ _))
  have hL₂ : MemLp (t₂.indicator fun _ => (1 : ℝ)) 2 μ :=
    memLp_indicator_const 2 ht₂.1 1 (Or.inr (measure_ne_top _ _))
  have hprod : Integrable
      ((t₁.indicator fun _ => (1 : ℝ)) * t₂.indicator fun _ => (1 : ℝ)) μ :=
    hL₁.integrable_mul hL₂
  have hprod' : Integrable
      ((μ[t₁.indicator fun _ => (1 : ℝ)|RelStructure.fixingAlgebra (A ∩ B)]) *
        t₂.indicator fun _ => (1 : ℝ)) μ :=
    (hL₁.condExp one_le_two).integrable_mul hL₂
  have ht₂meas : AEStronglyMeasurable[RelStructure.fixingAlgebra B]
      (t₂.indicator fun _ => (1 : ℝ)) μ :=
    (stronglyMeasurable_const.indicator ht₂).aestronglyMeasurable
  have hinter : (t₁ ∩ t₂).indicator (fun _ => (1 : ℝ)) =
      (t₁.indicator fun _ => (1 : ℝ)) * t₂.indicator fun _ => (1 : ℝ) := by
    rw [show (fun _ : RelStructure S (Vinfinite S) => (1 : ℝ)) = 1 from rfl,
      Set.inter_indicator_one]
  rw [hinter]
  calc μ[(t₁.indicator fun _ => (1 : ℝ)) * t₂.indicator fun _ => (1 : ℝ)|
        RelStructure.fixingAlgebra (A ∩ B)]
      =ᵐ[μ] μ[μ[(t₁.indicator fun _ => (1 : ℝ)) * t₂.indicator fun _ => (1 : ℝ)|
          RelStructure.fixingAlgebra B]|RelStructure.fixingAlgebra (A ∩ B)] :=
        (condExp_condExp_of_le (RelStructure.fixingAlgebra_mono Finset.inter_subset_right)
          (RelStructure.fixingAlgebra_le B)).symm
    _ =ᵐ[μ] μ[(μ[t₁.indicator fun _ => (1 : ℝ)|RelStructure.fixingAlgebra B]) *
          t₂.indicator fun _ => (1 : ℝ)|RelStructure.fixingAlgebra (A ∩ B)] :=
        condExp_congr_ae (condExp_mul_of_aestronglyMeasurable_right ht₂meas hprod
          (hL₁.integrable one_le_two))
    _ =ᵐ[μ] μ[(μ[t₁.indicator fun _ => (1 : ℝ)|RelStructure.fixingAlgebra (A ∩ B)]) *
          t₂.indicator fun _ => (1 : ℝ)|RelStructure.fixingAlgebra (A ∩ B)] :=
        condExp_congr_ae
          ((condExp_indicator_fixingAlgebra_ae_eq_condExp_inter M A B ht₁).mul
            (Filter.EventuallyEq.refl _ _))
    _ =ᵐ[μ] (μ[t₁.indicator fun _ => (1 : ℝ)|RelStructure.fixingAlgebra (A ∩ B)]) *
          μ[t₂.indicator fun _ => (1 : ℝ)|RelStructure.fixingAlgebra (A ∩ B)] :=
        condExp_mul_of_aestronglyMeasurable_left
          stronglyMeasurable_condExp.aestronglyMeasurable hprod' (hL₂.integrable one_le_two)

end CondIndep

end RelSignature
