/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelMarkedRepresentation
import Graphon.RelSpareScreening

/-!
# Rank one: conditional independence of the marked rows given the environment

Fix a pooled rank extension `Q` of a rank-one representation. The **environment** is the pair
(purely spare structure, whole pooled latent array); at rank one the latter is the single
empty-support coordinate, which every pooled relabeling fixes. The **marked row** of an original
vertex `v` is the marked observation at `{v}`: the pooled structure on every coordinate whose
support lies in the original copy of `v` together with all spare vertices.

The theorem of this module is the finite-family identity: for distinct original vertices and
cylinder events of their marked rows, the conditional probability of the intersection given the
environment is the product of the conditional probabilities.

The proof polls the spare copy. A single pooled transposition exchanging the original copy of
`v` with a spare vertex outside every footprint carries the row cylinder at `v` onto a purely
spare cylinder, an event of the environment, and fixes every other event under test. Pooled
invariance therefore identifies the probability of a row cylinder against an environment
cylinder with the probability of the polled copy against the same cylinder. Polled copies at
distinct spare vertices are exchangeable, so their averages form a Cauchy sequence in `L²`,
with an explicit second-moment computation. The limit is identified with the conditional
probability of the row cylinder by testing against environment cylinders, and the product
identity follows from the multilinearity of the averages.
-/

universe u

open MeasureTheory ProbabilityTheory

namespace RelSignature

variable {S : RelSignature.{u}}

/-! ### Rank one: the latent array is fixed by every pooled relabeling -/

/-- At rank one every pooled relabeling fixes the pooled latent array. -/
theorem pooledRankLatentRelabel_one_apply (ρ : ∀ s, Equiv.Perm (PoolVertex S s))
    (ω : PooledRankLatentSpace S 1) : pooledRankLatentRelabel ρ 1 ω = ω := by
  funext A
  rw [pooledRankLatentRelabel_apply]
  congr 1
  exact Subtype.ext ((Finset.card_eq_zero.mp (Nat.lt_one_iff.mp (latentIndexPerm ρ 1 A).2)).trans
    (Finset.card_eq_zero.mp (Nat.lt_one_iff.mp A.2)).symm)

/-- The pooled coupling space at rank one. -/
abbrev PooledOne (S : RelSignature.{u}) :=
  RelStructure S (PoolVertex S) × PooledRankLatentSpace S 1

/-- The structure relabeling on the rank-one pooled coupling space. -/
def structureRelabel (ρ : ∀ s, Equiv.Perm (PoolVertex S s)) : PooledOne S → PooledOne S :=
  fun p => (RelStructure.relabel ρ p.1, p.2)

theorem measurable_structureRelabel (ρ : ∀ s, Equiv.Perm (PoolVertex S s)) :
    Measurable (structureRelabel (S := S) ρ) :=
  ((measurable_relabel ρ).comp measurable_fst).prodMk measurable_snd

/-! ### Coordinate cylinders on the coupling space -/

/-- The event that finitely many structure coordinates, read through `ψ`, land in `T`. -/
def cylEvent {ι : Type*} (ψ : ι → RelCoord S (PoolVertex S)) (T : Set (ι → Bool)) :
    Set (PooledOne S) :=
  {p | (fun i => p.1 (ψ i)) ∈ T}

theorem measurableSet_cylEvent {ι : Type*} (ψ : ι → RelCoord S (PoolVertex S))
    {T : Set (ι → Bool)} (hT : MeasurableSet T) : MeasurableSet (cylEvent ψ T) :=
  (measurable_pi_lambda _ fun _ => (measurable_pi_apply _).comp measurable_fst) hT

theorem preimage_structureRelabel_cylEvent (ρ : ∀ s, Equiv.Perm (PoolVertex S s)) {ι : Type*}
    (ψ : ι → RelCoord S (PoolVertex S)) (T : Set (ι → Bool)) :
    structureRelabel ρ ⁻¹' cylEvent ψ T =
      cylEvent (fun i => RelCoord.map (fun s => ⇑(ρ s)) (ψ i)) T := rfl

/-- The latent event of the rank-one coupling. -/
def latentEvent (L : Set (PooledRankLatentSpace S 1)) : Set (PooledOne S) := {p | p.2 ∈ L}

theorem preimage_structureRelabel_latentEvent (ρ : ∀ s, Equiv.Perm (PoolVertex S s))
    (L : Set (PooledRankLatentSpace S 1)) :
    structureRelabel ρ ⁻¹' latentEvent L = latentEvent L := rfl

/-! ### The environment -/

/-- The environment observation: purely spare structure and the pooled latent array. -/
def envObs : PooledOne S → RelStructure S (Vinfinite S) × PooledRankLatentSpace S 1 :=
  fun p => (restrictPool S p.1, p.2)

theorem measurable_envObs : Measurable (envObs (S := S)) :=
  (measurable_restrictPool.comp measurable_fst).prodMk measurable_snd

/-- The environment σ-algebra. -/
noncomputable abbrev envAlg (S : RelSignature.{u}) : MeasurableSpace (PooledOne S) :=
  MeasurableSpace.comap (envObs (S := S)) inferInstance

theorem envAlg_le : envAlg S ≤ (inferInstance : MeasurableSpace (PooledOne S)) :=
  measurable_envObs.comap_le

/-- A pooled coordinate all of whose entries are spare. -/
def RelCoord.PurelySpare (c : RelCoord S (PoolVertex S)) : Prop :=
  ∀ i, ∃ b, c.2 i = Sum.inr b

/-- Read a purely spare coordinate on the spare copy. -/
def RelCoord.spareRead (c : RelCoord S (PoolVertex S)) : RelCoord S (Vinfinite S) :=
  RelCoord.map (fun _ => Sum.elim id id) c

theorem RelCoord.map_inr_spareRead {c : RelCoord S (PoolVertex S)} (hc : c.PurelySpare) :
    RelCoord.map (fun s => (poolVertex S s : Vinfinite S s → PoolVertex S s)) c.spareRead = c := by
  show (⟨c.1, fun i => Sum.inr (Sum.elim id id (c.2 i))⟩ : RelCoord S (PoolVertex S)) = ⟨c.1, c.2⟩
  congr 1
  funext i
  obtain ⟨b, hb⟩ := hc i
  rw [hb]
  rfl

/-- **A purely spare coordinate cylinder is an environment event.** -/
theorem measurableSet_envAlg_cylEvent_of_purelySpare {ι : Type*}
    {ψ : ι → RelCoord S (PoolVertex S)} (hψ : ∀ i, (ψ i).PurelySpare) {T : Set (ι → Bool)}
    (hT : MeasurableSet T) : MeasurableSet[envAlg S] (cylEvent ψ T) := by
  refine ⟨Prod.fst ⁻¹' {Z : RelStructure S (Vinfinite S) | (fun i => Z (ψ i).spareRead) ∈ T},
    measurable_fst ((measurable_pi_lambda _ fun _ => measurable_pi_apply _) hT), ?_⟩
  ext p
  simp only [Set.mem_preimage, Set.mem_setOf_eq, cylEvent]
  have : ∀ i, restrictPool S p.1 (ψ i).spareRead = p.1 (ψ i) := fun i => by
    show p.1 (RelCoord.map _ (ψ i).spareRead) = p.1 (ψ i)
    rw [RelCoord.map_inr_spareRead (hψ i)]
  simp only [envObs, this]

theorem measurableSet_envAlg_latentEvent {L : Set (PooledRankLatentSpace S 1)}
    (hL : MeasurableSet L) : MeasurableSet[envAlg S] (latentEvent L) :=
  ⟨Prod.snd ⁻¹' L, measurable_snd hL, rfl⟩

/-! ### The transposition of an original vertex with a spare vertex -/

open scoped Classical in
/-- The pooled transposition exchanging the original copy of `v` with the spare vertex `w` of
the same sort. -/
noncomputable def swapPair (v : Σ s : S.Srt, Vinfinite S s) (w : ℕ) :
    ∀ s, Equiv.Perm (PoolVertex S s) :=
  fun s => if s = v.1 then Equiv.swap (Sum.inl v.2) (Sum.inr w) else 1

open scoped Classical in
/-- The pooled transposition of two spare vertices of one sort. -/
noncomputable def spareSwap (s₀ : S.Srt) (w w' : ℕ) : ∀ s, Equiv.Perm (PoolVertex S s) :=
  fun s => if s = s₀ then Equiv.swap (Sum.inr w) (Sum.inr w') else 1

/-- Two sortwise maps agreeing on the entries of a coordinate transport it identically. -/
theorem RelCoord.map_congr_entries {f g : ∀ s, PoolVertex S s → PoolVertex S s}
    (c : RelCoord S (PoolVertex S)) (h : ∀ i, f _ (c.2 i) = g _ (c.2 i)) :
    RelCoord.map f c = RelCoord.map g c :=
  congrArg (fun w => (⟨c.1, w⟩ : RelCoord S (PoolVertex S))) (funext h)

/-- A swap fixes a coordinate none of whose entries is a swapped point. -/
theorem RelCoord.map_swapPair_of_notMem (v : Σ s : S.Srt, Vinfinite S s) (w : ℕ)
    (c : RelCoord S (PoolVertex S))
    (hv : (⟨v.1, Sum.inl v.2⟩ : Σ s : S.Srt, PoolVertex S s) ∉ c.support)
    (hw : (⟨v.1, Sum.inr w⟩ : Σ s : S.Srt, PoolVertex S s) ∉ c.support) :
    RelCoord.map (fun s => ⇑(swapPair v w s)) c = c := by
  classical
  refine (RelCoord.map_congr_entries (g := fun _ x => x) c fun i => ?_).trans rfl
  show swapPair v w _ (c.2 i) = c.2 i
  simp only [swapPair]
  split_ifs with hs
  · refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
    · intro h
      exact hv ((RelCoord.mem_support_iff _ _).mpr ⟨i, Sigma.ext hs (heq_of_eq h)⟩)
    · intro h
      exact hw ((RelCoord.mem_support_iff _ _).mpr ⟨i, Sigma.ext hs (heq_of_eq h)⟩)
  · rfl

theorem RelCoord.map_spareSwap_of_notMem (s₀ : S.Srt) (w w' : ℕ) (c : RelCoord S (PoolVertex S))
    (hw : (⟨s₀, Sum.inr w⟩ : Σ s : S.Srt, PoolVertex S s) ∉ c.support)
    (hw' : (⟨s₀, Sum.inr w'⟩ : Σ s : S.Srt, PoolVertex S s) ∉ c.support) :
    RelCoord.map (fun s => ⇑(spareSwap s₀ w w' s)) c = c := by
  classical
  refine (RelCoord.map_congr_entries (g := fun _ x => x) c fun i => ?_).trans rfl
  show spareSwap s₀ w w' _ (c.2 i) = c.2 i
  simp only [spareSwap]
  split_ifs with hs
  · refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
    · intro h
      exact hw ((RelCoord.mem_support_iff _ _).mpr ⟨i, Sigma.ext hs (heq_of_eq h)⟩)
    · intro h
      exact hw' ((RelCoord.mem_support_iff _ _).mpr ⟨i, Sigma.ext hs (heq_of_eq h)⟩)
  · rfl

/-! ### Pooled invariance at rank one -/

/-- The structure relabeling as a measurable equivalence. -/
noncomputable def structureRelabelEquiv (ρ : ∀ s, Equiv.Perm (PoolVertex S s)) :
    PooledOne S ≃ᵐ PooledOne S :=
  (RelStructure.congrCarrier fun s => (ρ s).symm).prodCongr (MeasurableEquiv.refl _)

theorem structureRelabelEquiv_coe (ρ : ∀ s, Equiv.Perm (PoolVertex S s)) :
    ((structureRelabelEquiv ρ : PooledOne S ≃ᵐ PooledOne S) : PooledOne S → PooledOne S) =
      structureRelabel ρ := rfl

namespace InfiniteRelExchangeableLaw

variable {M : InfiniteRelExchangeableLaw S} [Countable S.Srt] [Countable S.Rel]
  {C : M.RankRepresentation 1}

/-- **Every pooled relabeling preserves the rank-one pooled law**, acting on the structure
alone. -/
theorem PooledRankExtension.measurePreserving_structureRelabel (Q : PooledRankExtension C)
    (ρ : ∀ s, Equiv.Perm (PoolVertex S s)) :
    MeasurePreserving (structureRelabel ρ) (Q.law : Measure (PooledOne S))
      (Q.law : Measure (PooledOne S)) := by
  refine ⟨measurable_structureRelabel ρ, ?_⟩
  have h : structureRelabel (S := S) ρ =
      Prod.map (RelStructure.relabel ρ) (pooledRankLatentRelabel ρ 1) := by
    funext p
    exact Prod.ext rfl (pooledRankLatentRelabel_one_apply ρ p.2).symm
  rw [h]
  exact Q.invariant ρ

/-- Integrals are invariant under the structure relabeling. -/
theorem PooledRankExtension.integral_structureRelabel (Q : PooledRankExtension C)
    (ρ : ∀ s, Equiv.Perm (PoolVertex S s)) (F : PooledOne S → ℝ) :
    ∫ p, F (structureRelabel ρ p) ∂(Q.law : Measure (PooledOne S)) =
      ∫ p, F p ∂(Q.law : Measure (PooledOne S)) :=
  MeasurePreserving.integral_comp' (f := structureRelabelEquiv ρ)
    (Q.measurePreserving_structureRelabel ρ) F

end InfiniteRelExchangeableLaw

/-! ### Marked rows and their polls -/

/-- The cylinder event of the marked row of `v` determined by finitely many marked coordinates. -/
def rowEvent (v : Σ s : S.Srt, Vinfinite S s) (t : Finset (MarkedCoord (S := S) {v}))
    (T : Set (t → Bool)) : Set (PooledOne S) :=
  cylEvent (fun c : t => c.1.1) T

theorem rowEvent_eq (v : Σ s : S.Srt, Vinfinite S s) (t : Finset (MarkedCoord (S := S) {v}))
    (T : Set (t → Bool)) :
    rowEvent v t T =
      (markedObs {v} ∘ Prod.fst) ⁻¹' (cylinder t T : Set (MarkedSpace (S := S) {v})) :=
  rfl

/-- **The poll of the row of `v` at the spare vertex `w`**: the same cylinder read after
exchanging the original copy of `v` with `w`. -/
def pollEvent (v : Σ s : S.Srt, Vinfinite S s) (w : ℕ) (t : Finset (MarkedCoord (S := S) {v}))
    (T : Set (t → Bool)) : Set (PooledOne S) :=
  cylEvent (fun c : t => RelCoord.map (fun s => ⇑(swapPair v w s)) c.1.1) T

theorem preimage_structureRelabel_swapPair_rowEvent (v : Σ s : S.Srt, Vinfinite S s) (w : ℕ)
    (t : Finset (MarkedCoord (S := S) {v})) (T : Set (t → Bool)) :
    structureRelabel (swapPair v w) ⁻¹' rowEvent v t T = pollEvent v w t T := rfl

/-- A spare vertex is fresh for a coordinate at a sort when the coordinate has no entry there. -/
def FreshFor (s₀ : S.Srt) (w : ℕ) (c : RelCoord S (PoolVertex S)) : Prop :=
  (⟨s₀, Sum.inr w⟩ : Σ s : S.Srt, PoolVertex S s) ∉ c.support

/-- The largest spare index read by a coordinate. -/
noncomputable def RelCoord.spareBound (c : RelCoord S (PoolVertex S)) : ℕ :=
  (Finset.univ : Finset (Fin (S.arity c.1))).sup fun i => Sum.elim (fun _ => 0) id (c.2 i)

theorem freshFor_of_spareBound_lt (s₀ : S.Srt) {w : ℕ} (c : RelCoord S (PoolVertex S))
    (hw : c.spareBound < w) : FreshFor s₀ w c := by
  intro h
  obtain ⟨i, hi⟩ := (RelCoord.mem_support_iff _ _).mp h
  have h2 : c.2 i = Sum.inr w := by
    have := congrArg (fun x : Σ s : S.Srt, PoolVertex S s => Sum.elim (fun _ => 0) id x.2) hi
    simp only [RelCoord.taggedValue, Sum.elim_inr, id] at this
    rcases hx : c.2 i with a | b
    · rw [hx] at this
      simp at this
      omega
    · rw [hx] at this
      simp only [Sum.elim_inr, id] at this
      rw [this]
  have : w ≤ c.spareBound := by
    refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun i => Sum.elim (fun _ => 0) id (c.2 i))
      (Finset.mem_univ i))
    rw [h2]
    rfl
  omega

/-- The entries of a marked coordinate at `{v}` are the original copy of `v` or spare vertices. -/
theorem MarkedCoord.entry_singleton (v : Σ s : S.Srt, Vinfinite S s)
    (c : MarkedCoord (S := S) {v}) (i : Fin (S.arity c.1.1)) :
    (S.argSort c.1.1 i = v.1 ∧ c.1.2 i = Sum.inl v.2) ∨ ∃ b, c.1.2 i = Sum.inr b := by
  have hmem := c.2 _ ((RelCoord.mem_support_iff _ _).mpr ⟨i, rfl⟩)
  rcases hmem with ⟨a, ha, hA⟩ | ⟨b, hb⟩
  · left
    rw [Finset.mem_singleton] at hA
    obtain ⟨hs, hv⟩ := Sigma.mk.inj_iff.mp hA
    refine ⟨hs, ?_⟩
    have ha' : c.1.2 i = Sum.inl a := ha
    rw [ha']
    exact congrArg Sum.inl (eq_of_heq hv)
  · exact Or.inr ⟨b, hb⟩

/-- **A polled row coordinate is purely spare** when the poll vertex is fresh. -/
theorem purelySpare_map_swapPair (v : Σ s : S.Srt, Vinfinite S s) {w : ℕ}
    (c : MarkedCoord (S := S) {v}) (hw : FreshFor v.1 w c.1) :
    (RelCoord.map (fun s => ⇑(swapPair v w s)) c.1).PurelySpare := by
  classical
  intro i
  show ∃ b, swapPair v w _ (c.1.2 i) = Sum.inr b
  rcases MarkedCoord.entry_singleton v c i with ⟨hs, hi⟩ | ⟨b, hb⟩
  · refine ⟨w, ?_⟩
    simp only [swapPair, if_pos hs, hi]
    exact Equiv.swap_apply_left _ _
  · refine ⟨b, ?_⟩
    simp only [swapPair, hb]
    split_ifs with hs
    · refine Equiv.swap_apply_of_ne_of_ne (by simp) ?_
      intro h
      exact hw ((RelCoord.mem_support_iff _ _).mpr ⟨i, Sigma.ext hs (heq_of_eq (hb.trans h))⟩)
    · rfl

/-! ### Fixing lemmas for polled and environment coordinates -/

/-- A fresh spare vertex distinct from the poll vertex stays fresh for the polled coordinate. -/
theorem freshFor_map_swapPair (v : Σ s : S.Srt, Vinfinite S s) {w u : ℕ}
    (c : RelCoord S (PoolVertex S)) (hu : FreshFor v.1 u c) (huw : u ≠ w) :
    FreshFor v.1 u (RelCoord.map (fun s => ⇑(swapPair v w s)) c) := by
  classical
  intro h
  obtain ⟨i, hi⟩ := (RelCoord.mem_support_iff _ _).mp h
  obtain ⟨hs, hx⟩ := Sigma.mk.inj_iff.mp hi
  have hx' : swapPair v w _ (c.2 i) = Sum.inr u := eq_of_heq hx
  refine hu ((RelCoord.mem_support_iff _ _).mpr ⟨i, Sigma.ext hs (heq_of_eq ?_)⟩)
  simp only [swapPair] at hx'
  split_ifs at hx' with hs'
  · rcases hc : c.2 i with a | b
    · rw [hc] at hx'
      by_cases ha : (Sum.inl a : PoolVertex S v.1) = Sum.inl v.2
      · rw [ha, Equiv.swap_apply_left] at hx'
        exact absurd (Sum.inr.inj hx').symm huw
      · rw [Equiv.swap_apply_of_ne_of_ne ha (by simp)] at hx'
        exact absurd hx' (by simp)
    · rw [hc] at hx'
      by_cases hb : (Sum.inr b : PoolVertex S v.1) = Sum.inr w
      · rw [hb, Equiv.swap_apply_right] at hx'
        exact absurd hx' (by simp)
      · rw [Equiv.swap_apply_of_ne_of_ne (by simp) hb] at hx'
        exact hc.trans hx'
  · exact hx'

/-- A polled coordinate has no entry at the original copy of `v`. -/
theorem notMem_inl_of_purelySpare (v : Σ s : S.Srt, Vinfinite S s)
    {c : RelCoord S (PoolVertex S)} (hc : c.PurelySpare) :
    (⟨v.1, Sum.inl v.2⟩ : Σ s : S.Srt, PoolVertex S s) ∉ c.support := by
  intro h
  obtain ⟨i, hi⟩ := (RelCoord.mem_support_iff _ _).mp h
  obtain ⟨-, hx⟩ := Sigma.mk.inj_iff.mp hi
  obtain ⟨b, hb⟩ := hc i
  have h1 : c.2 i = Sum.inl v.2 := eq_of_heq hx
  rw [hb] at h1
  exact Sum.inr_ne_inl h1

/-- A swap with a fresh spare vertex fixes the row coordinates of a different original vertex. -/
theorem map_swapPair_of_ne (v v' : Σ s : S.Srt, Vinfinite S s) (hvv' : v ≠ v') {w : ℕ}
    (c : MarkedCoord (S := S) {v'}) (hw : FreshFor v.1 w c.1) :
    RelCoord.map (fun s => ⇑(swapPair v w s)) c.1 = c.1 := by
  refine RelCoord.map_swapPair_of_notMem v w c.1 ?_ hw
  intro h
  rcases c.2 _ h with ⟨a, ha, hA⟩ | ⟨b, hb⟩
  · rw [Finset.mem_singleton] at hA
    have ha' : v.2 = a := Sum.inl.inj ha
    subst ha'
    exact hvv' (hA.symm.trans (Sigma.eta v)).symm
  · exact Sum.inl_ne_inr hb

/-- **A spare swap carries the poll at `w` to the poll at `w'`.** -/
theorem map_spareSwap_map_swapPair (v : Σ s : S.Srt, Vinfinite S s) {w w' : ℕ}
    (c : MarkedCoord (S := S) {v}) (hw : FreshFor v.1 w c.1) (hw' : FreshFor v.1 w' c.1) :
    RelCoord.map (fun s => ⇑(spareSwap v.1 w w' s))
        (RelCoord.map (fun s => ⇑(swapPair v w s)) c.1) =
      RelCoord.map (fun s => ⇑(swapPair v w' s)) c.1 := by
  classical
  rw [← RelCoord.map_comp]
  refine RelCoord.map_congr_entries c.1 fun i => ?_
  show spareSwap v.1 w w' _ (swapPair v w _ (c.1.2 i)) = swapPair v w' _ (c.1.2 i)
  rcases MarkedCoord.entry_singleton v c i with ⟨hs, hi⟩ | ⟨b, hb⟩
  · simp only [swapPair, spareSwap, if_pos hs, hi, Equiv.swap_apply_left]
  · simp only [swapPair, spareSwap, hb]
    split_ifs with hs
    · have hbw : (Sum.inr b : PoolVertex S v.1) ≠ Sum.inr w := fun h =>
        hw ((RelCoord.mem_support_iff _ _).mpr ⟨i, Sigma.ext hs (heq_of_eq (hb.trans h))⟩)
      have hbw' : (Sum.inr b : PoolVertex S v.1) ≠ Sum.inr w' := fun h =>
        hw' ((RelCoord.mem_support_iff _ _).mpr ⟨i, Sigma.ext hs (heq_of_eq (hb.trans h))⟩)
      rw [Equiv.swap_apply_of_ne_of_ne (by simp) hbw, Equiv.swap_apply_of_ne_of_ne hbw hbw',
        Equiv.swap_apply_of_ne_of_ne (by simp) hbw']
    · rfl

/-! ### Sets fixed by the swaps at `v` beyond a bound -/

/-- A set of the coupling space is **swap-fixed at `v` beyond `b`** if every transposition of the
original copy of `v` with a spare vertex beyond `b` fixes it. -/
def SwapFixed (v : Σ s : S.Srt, Vinfinite S s) (b : ℕ) (K : Set (PooledOne S)) : Prop :=
  ∀ w, b < w → structureRelabel (swapPair v w) ⁻¹' K = K

theorem SwapFixed.mono {v : Σ s : S.Srt, Vinfinite S s} {b b' : ℕ} (h : b ≤ b')
    {K : Set (PooledOne S)} (hK : SwapFixed v b K) : SwapFixed v b' K :=
  fun w hw => hK w (lt_of_le_of_lt h hw)

theorem swapFixed_univ (v : Σ s : S.Srt, Vinfinite S s) (b : ℕ) :
    SwapFixed v b (Set.univ : Set (PooledOne S)) := fun _ _ => rfl

theorem SwapFixed.inter {v : Σ s : S.Srt, Vinfinite S s} {b : ℕ} {K K' : Set (PooledOne S)}
    (hK : SwapFixed v b K) (hK' : SwapFixed v b K') : SwapFixed v b (K ∩ K') := fun w hw => by
  rw [Set.preimage_inter, hK w hw, hK' w hw]

theorem swapFixed_latentEvent (v : Σ s : S.Srt, Vinfinite S s) (b : ℕ)
    (L : Set (PooledRankLatentSpace S 1)) : SwapFixed v b (latentEvent L) := fun _ _ => rfl

/-- A cylinder none of whose coordinates reads the original copy of `v` is swap-fixed beyond the
largest spare index it reads. -/
theorem swapFixed_cylEvent (v : Σ s : S.Srt, Vinfinite S s) {ι : Type*}
    (ψ : ι → RelCoord S (PoolVertex S))
    (hψ : ∀ i, (⟨v.1, Sum.inl v.2⟩ : Σ s : S.Srt, PoolVertex S s) ∉ (ψ i).support)
    {b : ℕ} (hb : ∀ i, (ψ i).spareBound ≤ b) (T : Set (ι → Bool)) :
    SwapFixed v b (cylEvent ψ T) := by
  intro w hw
  rw [preimage_structureRelabel_cylEvent]
  congr 1
  funext i
  exact RelCoord.map_swapPair_of_notMem v w (ψ i) (hψ i)
    (freshFor_of_spareBound_lt v.1 (ψ i) (lt_of_le_of_lt (hb i) hw))

/-- The row of a different original vertex is swap-fixed at `v`. -/
theorem swapFixed_rowEvent_of_ne {v v' : Σ s : S.Srt, Vinfinite S s} (hvv' : v ≠ v')
    (t : Finset (MarkedCoord (S := S) {v'})) (T : Set (t → Bool)) :
    SwapFixed v (t.sup fun c => c.1.spareBound) (rowEvent v' t T) := by
  intro w hw
  show structureRelabel (swapPair v w) ⁻¹' cylEvent (fun c : t => c.1.1) T = _
  rw [preimage_structureRelabel_cylEvent]
  congr 1
  funext c
  exact map_swapPair_of_ne v v' hvv' c (freshFor_of_spareBound_lt v.1 c.1.1
    (lt_of_le_of_lt (Finset.le_sup (f := fun c : MarkedCoord (S := S) {v'} => c.1.spareBound)
      c.2) hw))

/-- The row of `v` itself is carried to its poll by the swap. -/
theorem preimage_swapPair_rowEvent_inter {v : Σ s : S.Srt, Vinfinite S s}
    (t : Finset (MarkedCoord (S := S) {v})) (T : Set (t → Bool)) {b : ℕ} {K : Set (PooledOne S)}
    (hK : SwapFixed v b K) {w : ℕ} (hw : b < w) :
    structureRelabel (swapPair v w) ⁻¹' (rowEvent v t T ∩ K) = pollEvent v w t T ∩ K := by
  rw [Set.preimage_inter, preimage_structureRelabel_swapPair_rowEvent, hK w hw]

/-! ### The environment generators -/

variable (S) in
/-- The generating π-system of the environment σ-algebra: purely spare structure cylinders
crossed with latent events. -/
def envGenerators : Set (Set (PooledOne S)) :=
  Set.preimage (envObs (S := S)) ''
    Set.image2 (· ×ˢ ·) (measurableCylinders fun _ : RelCoord S (Vinfinite S) => Bool)
      {L : Set (PooledRankLatentSpace S 1) | MeasurableSet L}

theorem isPiSystem_envGenerators : IsPiSystem (envGenerators S) :=
  (isPiSystem_measurableCylinders.prod MeasurableSpace.isPiSystem_measurableSet).comap _

theorem envAlg_eq_generateFrom :
    envAlg S = MeasurableSpace.generateFrom (envGenerators S) := by
  have hspan : IsCountablySpanning
      (measurableCylinders fun _ : RelCoord S (Vinfinite S) => Bool) :=
    ⟨fun _ => Set.univ, fun _ => univ_mem_measurableCylinders _, Set.iUnion_const _⟩
  rw [envGenerators, ← MeasurableSpace.comap_generateFrom, generateFrom_eq_prod
    generateFrom_measurableCylinders MeasurableSpace.generateFrom_measurableSet hspan
    isCountablySpanning_measurableSet]

theorem measurableSet_envAlg_of_mem_envGenerators {G : Set (PooledOne S)}
    (hG : G ∈ envGenerators S) : MeasurableSet[envAlg S] G := by
  rw [envAlg_eq_generateFrom]
  exact MeasurableSpace.measurableSet_generateFrom hG

/-- The spare-copy reading of an original coordinate. -/
def RelCoord.toSpare (c : RelCoord S (Vinfinite S)) : RelCoord S (PoolVertex S) :=
  RelCoord.map (fun s => (poolVertex S s : Vinfinite S s → PoolVertex S s)) c

theorem RelCoord.notMem_inl_support_toSpare (v : Σ s : S.Srt, Vinfinite S s)
    (c : RelCoord S (Vinfinite S)) :
    (⟨v.1, Sum.inl v.2⟩ : Σ s : S.Srt, PoolVertex S s) ∉ c.toSpare.support := by
  intro h
  obtain ⟨i, hi⟩ := (RelCoord.mem_support_iff _ _).mp h
  obtain ⟨-, hx⟩ := Sigma.mk.inj_iff.mp hi
  exact Sum.inr_ne_inl (eq_of_heq hx)

/-- An environment generator, read on the coupling space. -/
theorem envObs_preimage_prod_cylinder (t : Finset (RelCoord S (Vinfinite S))) (T : Set (t → Bool))
    (L : Set (PooledRankLatentSpace S 1)) :
    envObs ⁻¹' ((cylinder t T : Set (RelStructure S (Vinfinite S))) ×ˢ L) =
      cylEvent (fun c : t => c.1.toSpare) T ∩ latentEvent L :=
  Set.ext fun _ => Iff.rfl

/-- **Every environment generator is swap-fixed at every original vertex** beyond some bound. -/
theorem exists_swapFixed_of_mem_envGenerators (v : Σ s : S.Srt, Vinfinite S s)
    {G : Set (PooledOne S)} (hG : G ∈ envGenerators S) : ∃ b, SwapFixed v b G := by
  obtain ⟨X, hX, hGX⟩ := hG
  obtain ⟨A, hA, L, hL, hXAL⟩ := hX
  obtain ⟨t, T, -, hcyl⟩ := (mem_measurableCylinders _).mp hA
  refine ⟨t.sup fun c => c.toSpare.spareBound, ?_⟩
  have h1 : G = cylEvent (fun c : t => c.1.toSpare) T ∩ latentEvent L := by
    rw [← hGX, ← hXAL, hcyl]
    exact envObs_preimage_prod_cylinder t T L
  rw [h1]
  refine SwapFixed.inter ?_ (swapFixed_latentEvent v _ L)
  exact swapFixed_cylEvent v _ (fun c => RelCoord.notMem_inl_support_toSpare v c.1)
    (fun c => Finset.le_sup (f := fun c : RelCoord S (Vinfinite S) => c.toSpare.spareBound) c.2) T

/-! ### Row bounds -/

/-- The spare bound of a row cylinder: every spare vertex beyond it is fresh for all its
coordinates. -/
noncomputable def rowBound {v : Σ s : S.Srt, Vinfinite S s}
    (t : Finset (MarkedCoord (S := S) {v})) : ℕ :=
  t.sup fun c => c.1.spareBound

/-- The canonical fresh spare vertex of the row. -/
noncomputable def rowFresh {v : Σ s : S.Srt, Vinfinite S s}
    (t : Finset (MarkedCoord (S := S) {v})) : ℕ :=
  rowBound t + 1

theorem rowBound_lt_rowFresh {v : Σ s : S.Srt, Vinfinite S s}
    (t : Finset (MarkedCoord (S := S) {v})) :
    rowBound t < rowFresh t :=
  Nat.lt_succ_self _

theorem freshFor_of_rowBound_lt {v : Σ s : S.Srt, Vinfinite S s}
    {t : Finset (MarkedCoord (S := S) {v})} {w : ℕ} (hw : rowBound t < w) (c : t) :
    FreshFor v.1 w c.1.1 :=
  freshFor_of_spareBound_lt v.1 c.1.1
    (lt_of_le_of_lt (Finset.le_sup (f := fun c : MarkedCoord (S := S) {v} => c.1.spareBound) c.2)
      hw)

/-! ### Poll blocks -/

/-- The block of `N` fresh spare vertices polled at stage `N`. -/
noncomputable def pollBlockRow {v : Σ s : S.Srt, Vinfinite S s}
    (t : Finset (MarkedCoord (S := S) {v})) (N : ℕ) : Finset ℕ :=
  Finset.Ico (rowBound t + N) (rowBound t + 2 * N)

theorem rowBound_lt_of_mem_pollBlockRow {v : Σ s : S.Srt, Vinfinite S s}
    {t : Finset (MarkedCoord (S := S) {v})} {N w : ℕ} (hw : w ∈ pollBlockRow t N) :
    rowBound t < w := by
  rw [pollBlockRow, Finset.mem_Ico] at hw
  omega

theorem le_of_mem_pollBlockRow {v : Σ s : S.Srt, Vinfinite S s}
    {t : Finset (MarkedCoord (S := S) {v})} {N w : ℕ} (hw : w ∈ pollBlockRow t N) :
    rowBound t + N ≤ w := by
  rw [pollBlockRow, Finset.mem_Ico] at hw
  exact hw.1

theorem card_pollBlockRow {v : Σ s : S.Srt, Vinfinite S s} (t : Finset (MarkedCoord (S := S) {v}))
    (N : ℕ) : (pollBlockRow t N).card = N := by
  rw [pollBlockRow, Nat.card_Ico]
  omega

/-! ### The freeze identity and the pair moments -/

namespace InfiniteRelExchangeableLaw

variable {M : InfiniteRelExchangeableLaw S} [Countable S.Srt] [Countable S.Rel]
  {C : M.RankRepresentation 1} (Q : PooledRankExtension C)

/-- The rank-one pooled law, as a measure on the coupling space. -/
noncomputable abbrev PooledRankExtension.lawOne : Measure (PooledOne S) :=
  (Q.law : Measure (PooledOne S))

instance : IsProbabilityMeasure Q.lawOne := Q.law.2

section Row

variable (v : Σ s : S.Srt, Vinfinite S s) (t : Finset (MarkedCoord (S := S) {v}))
  (T : Set (t → Bool))

omit [Countable S.Srt] [Countable S.Rel] in
theorem measurableSet_rowEvent (hT : MeasurableSet T) : MeasurableSet (rowEvent v t T) :=
  measurableSet_cylEvent (fun c : t => c.1.1) hT

omit [Countable S.Srt] [Countable S.Rel] in
theorem measurableSet_pollEvent (hT : MeasurableSet T) (w : ℕ) :
    MeasurableSet (pollEvent v w t T) :=
  measurableSet_cylEvent (fun c : t => RelCoord.map (fun s => ⇑(swapPair v w s)) c.1.1) hT

/-- **The freeze identity**: against a set fixed by the transposition, the row cylinder and its
poll have the same probability. -/
theorem PooledRankExtension.measure_rowEvent_inter_eq_pollEvent (hT : MeasurableSet T)
    {K : Set (PooledOne S)} (hK : MeasurableSet K) {w : ℕ}
    (hKw : structureRelabel (swapPair v w) ⁻¹' K = K) :
    Q.lawOne (rowEvent v t T ∩ K) = Q.lawOne (pollEvent v w t T ∩ K) := by
  have h := (Q.measurePreserving_structureRelabel (swapPair v w)).measure_preimage
    ((measurableSet_rowEvent v t T hT).inter hK).nullMeasurableSet
  rw [Set.preimage_inter, preimage_structureRelabel_swapPair_rowEvent, hKw] at h
  exact h.symm

omit [Countable S.Srt] [Countable S.Rel] in
/-- A poll at a fresh spare vertex is an environment event. -/
theorem measurableSet_envAlg_pollEvent (hT : MeasurableSet T) {w : ℕ} (hw : rowBound t < w) :
    MeasurableSet[envAlg S] (pollEvent v w t T) :=
  measurableSet_envAlg_cylEvent_of_purelySpare
    (ψ := fun c : t => RelCoord.map (fun s => ⇑(swapPair v w s)) c.1.1)
    (fun c => purelySpare_map_swapPair v c.1 (freshFor_of_rowBound_lt hw c)) hT

omit [Countable S.Srt] [Countable S.Rel] in
/-- A poll at `w'` is fixed by the transposition with a different fresh vertex `w`. -/
theorem preimage_swapPair_pollEvent {w w' : ℕ} (hw : rowBound t < w) (hw' : rowBound t < w')
    (hww' : w ≠ w') :
    structureRelabel (swapPair v w) ⁻¹' pollEvent v w' t T = pollEvent v w' t T := by
  show structureRelabel (swapPair v w) ⁻¹' cylEvent _ T = cylEvent _ T
  rw [preimage_structureRelabel_cylEvent]
  congr 1
  funext c
  exact RelCoord.map_swapPair_of_notMem v w _
    (notMem_inl_of_purelySpare v (purelySpare_map_swapPair v c.1 (freshFor_of_rowBound_lt hw' c)))
    (freshFor_map_swapPair v c.1.1 (freshFor_of_rowBound_lt hw c) hww')

omit [Countable S.Srt] [Countable S.Rel] in
/-- A spare swap of two fresh vertices fixes the row cylinder. -/
theorem preimage_spareSwap_rowEvent {w w' : ℕ} (hw : rowBound t < w) (hw' : rowBound t < w') :
    structureRelabel (spareSwap v.1 w w') ⁻¹' rowEvent v t T = rowEvent v t T := by
  show structureRelabel (spareSwap v.1 w w') ⁻¹' cylEvent _ T = cylEvent _ T
  rw [preimage_structureRelabel_cylEvent]
  congr 1
  funext c
  exact RelCoord.map_spareSwap_of_notMem v.1 w w' c.1.1 (freshFor_of_rowBound_lt hw c)
    (freshFor_of_rowBound_lt hw' c)

omit [Countable S.Srt] [Countable S.Rel] in
/-- A spare swap of two fresh vertices carries the poll at one to the poll at the other. -/
theorem preimage_spareSwap_pollEvent {w w' : ℕ} (hw : rowBound t < w) (hw' : rowBound t < w') :
    structureRelabel (spareSwap v.1 w w') ⁻¹' pollEvent v w t T = pollEvent v w' t T := by
  show structureRelabel (spareSwap v.1 w w') ⁻¹' cylEvent _ T = cylEvent _ T
  rw [preimage_structureRelabel_cylEvent]
  congr 1
  funext c
  exact map_spareSwap_map_swapPair v c (freshFor_of_rowBound_lt hw c)
    (freshFor_of_rowBound_lt hw' c)

/-- **The pair moment of the polls**: two polls at distinct fresh vertices meet with the
probability of the row meeting its canonical poll. -/
theorem PooledRankExtension.measure_pollEvent_inter_pollEvent (hT : MeasurableSet T) {w w' : ℕ}
    (hw : rowBound t < w) (hw' : rowBound t < w') (hww' : w ≠ w') :
    Q.lawOne (pollEvent v w t T ∩ pollEvent v w' t T) =
      Q.lawOne (rowEvent v t T ∩ pollEvent v (rowFresh t) t T) := by
  have h1 : Q.lawOne (pollEvent v w t T ∩ pollEvent v w' t T) =
      Q.lawOne (rowEvent v t T ∩ pollEvent v w' t T) :=
    (Q.measure_rowEvent_inter_eq_pollEvent v t T hT (measurableSet_pollEvent v t T hT w')
      (preimage_swapPair_pollEvent v t T hw hw' hww')).symm
  rw [h1]
  have hfresh := rowBound_lt_rowFresh t
  have h2 := (Q.measurePreserving_structureRelabel
    (spareSwap v.1 (rowFresh t) w')).measure_preimage
    ((measurableSet_rowEvent v t T hT).inter
      (measurableSet_pollEvent v t T hT (rowFresh t))).nullMeasurableSet
  rw [Set.preimage_inter, preimage_spareSwap_rowEvent v t T hfresh hw',
    preimage_spareSwap_pollEvent v t T hfresh hw'] at h2
  exact h2

/-! ### The empirical averages of the polls -/

/-- **The empirical average of the polls** over the block at stage `N`. -/
noncomputable def pollAverage (N : ℕ) : PooledOne S → ℝ :=
  fun p => (N : ℝ)⁻¹ * ∑ w ∈ pollBlockRow t N, (pollEvent v w t T).indicator (fun _ => (1 : ℝ)) p

omit [Countable S.Srt] [Countable S.Rel] in
theorem stronglyMeasurable_envAlg_pollAverage (hT : MeasurableSet T) (N : ℕ) :
    StronglyMeasurable[envAlg S] (pollAverage v t T N) := by
  letI : MeasurableSpace (PooledOne S) := envAlg S
  have hsum : StronglyMeasurable
      (∑ w ∈ pollBlockRow t N, (pollEvent v w t T).indicator (fun _ => (1 : ℝ))) :=
    Finset.stronglyMeasurable_sum _ fun w hw => stronglyMeasurable_const.indicator
      (measurableSet_envAlg_pollEvent v t T hT (rowBound_lt_of_mem_pollBlockRow hw))
  have : pollAverage v t T N = fun p => (N : ℝ)⁻¹ *
      (∑ w ∈ pollBlockRow t N, (pollEvent v w t T).indicator (fun _ => (1 : ℝ))) p := by
    funext p
    simp only [pollAverage, Finset.sum_apply]
  rw [this]
  exact hsum.const_mul _

omit [Countable S.Srt] [Countable S.Rel] in
theorem measurable_pollAverage (hT : MeasurableSet T) (N : ℕ) :
    Measurable (pollAverage v t T N) := by
  refine (Finset.measurable_sum _ fun w _ => ?_).const_mul _
  exact measurable_const.indicator (measurableSet_pollEvent v t T hT w)

omit [Countable S.Srt] [Countable S.Rel] in
theorem pollAverage_nonneg (N : ℕ) (p : PooledOne S) : 0 ≤ pollAverage v t T N p :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))
    (Finset.sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)

omit [Countable S.Srt] [Countable S.Rel] in
theorem pollAverage_le_one (N : ℕ) (p : PooledOne S) : pollAverage v t T N p ≤ 1 := by
  unfold pollAverage
  have hsum :
      ∑ w ∈ pollBlockRow t N, (pollEvent v w t T).indicator (fun _ => (1 : ℝ)) p ≤ (N : ℝ) := by
    calc ∑ w ∈ pollBlockRow t N, (pollEvent v w t T).indicator (fun _ => (1 : ℝ)) p
        ≤ ∑ _w ∈ pollBlockRow t N, (1 : ℝ) :=
          Finset.sum_le_sum fun _ _ => Set.indicator_le_self' (fun _ _ => zero_le_one) _
      _ = (N : ℝ) := by rw [Finset.sum_const, card_pollBlockRow, nsmul_eq_mul, mul_one]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    calc (N : ℝ)⁻¹ * ∑ w ∈ pollBlockRow t N, (pollEvent v w t T).indicator (fun _ => (1 : ℝ)) p
        ≤ (N : ℝ)⁻¹ * N := by gcongr
      _ = 1 := inv_mul_cancel₀ hNpos.ne'

omit [Countable S.Srt] [Countable S.Rel] in
theorem norm_pollAverage_le_one (N : ℕ) (p : PooledOne S) : ‖pollAverage v t T N p‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [pollAverage_nonneg v t T N p], pollAverage_le_one v t T N p⟩

theorem integrable_pollAverage (hT : MeasurableSet T) (N : ℕ) :
    Integrable (pollAverage v t T N) Q.lawOne :=
  (integrable_const (1 : ℝ)).mono' (measurable_pollAverage v t T hT N).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_pollAverage_le_one v t T N))

theorem memLp_two_pollAverage (hT : MeasurableSet T) (N : ℕ) :
    MemLp (pollAverage v t T N) 2 Q.lawOne :=
  MemLp.of_bound (measurable_pollAverage v t T hT N).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (norm_pollAverage_le_one v t T N))

/-- The pair moment function of the polls. -/
noncomputable def pollMoment (w w' : ℕ) : ℝ :=
  Q.lawOne.real (pollEvent v w t T ∩ pollEvent v w' t T)

/-- The common value of the off-diagonal pair moments. -/
noncomputable def pollConstant : ℝ := Q.lawOne.real (rowEvent v t T ∩ pollEvent v (rowFresh t) t T)

theorem pollMoment_eq_pollConstant (hT : MeasurableSet T) {w w' : ℕ} (hw : rowBound t < w)
    (hw' : rowBound t < w') (hww' : w ≠ w') :
    pollMoment Q v t T w w' = pollConstant Q v t T := by
  rw [pollMoment, pollConstant, measureReal_def, measureReal_def,
    Q.measure_pollEvent_inter_pollEvent v t T hT hw hw' hww']

theorem pollConstant_le_pollMoment (hT : MeasurableSet T) {w w' : ℕ} (hw : rowBound t < w)
    (hw' : rowBound t < w') : pollConstant Q v t T ≤ pollMoment Q v t T w w' := by
  by_cases hww' : w = w'
  · subst hww'
    rw [← pollMoment_eq_pollConstant Q v t T hT hw (Nat.lt_succ_of_lt hw)
      (Nat.ne_of_lt (Nat.lt_succ_self w)), pollMoment, pollMoment, Set.inter_self]
    exact measureReal_mono Set.inter_subset_left
  · rw [pollMoment_eq_pollConstant Q v t T hT hw hw' hww']

theorem pollMoment_le_one (w w' : ℕ) : pollMoment Q v t T w w' ≤ 1 := measureReal_le_one

theorem pollConstant_nonneg : 0 ≤ pollConstant Q v t T := measureReal_nonneg

omit [Countable S.Srt] [Countable S.Rel] in
/-- The product of two averages, expanded as a double sum of indicators of intersections. -/
theorem pollAverage_mul_pollAverage (N M : ℕ) :
    (fun p => pollAverage v t T N p * pollAverage v t T M p) = fun p =>
      (N : ℝ)⁻¹ * (M : ℝ)⁻¹ * ∑ w ∈ pollBlockRow t N, ∑ w' ∈ pollBlockRow t M,
        (pollEvent v w t T ∩ pollEvent v w' t T).indicator (fun _ => (1 : ℝ)) p := by
  funext p
  simp only [pollAverage]
  rw [mul_mul_mul_comm, Finset.sum_mul_sum]
  have : ∀ w w', (pollEvent v w t T ∩ pollEvent v w' t T).indicator (fun _ => (1 : ℝ)) p =
      (pollEvent v w t T).indicator (fun _ => (1 : ℝ)) p *
        (pollEvent v w' t T).indicator (fun _ => (1 : ℝ)) p := by
    intro w w'
    by_cases h1 : p ∈ pollEvent v w t T <;> by_cases h2 : p ∈ pollEvent v w' t T <;>
      simp [h1, h2]
  simp only [this]

/-- The integral of the product of two averages. -/
theorem integral_pollAverage_mul (hT : MeasurableSet T) (N M : ℕ) :
    ∫ p, pollAverage v t T N p * pollAverage v t T M p ∂Q.lawOne =
      (N : ℝ)⁻¹ * (M : ℝ)⁻¹ * ∑ w ∈ pollBlockRow t N, ∑ w' ∈ pollBlockRow t M,
        pollMoment Q v t T w w' := by
  rw [pollAverage_mul_pollAverage, integral_const_mul, integral_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun w' _ => ?_
      rw [integral_indicator_const _ ((measurableSet_pollEvent v t T hT w).inter
        (measurableSet_pollEvent v t T hT w')), smul_eq_mul, mul_one]
      rfl
    · intro w' _
      exact (integrable_const 1).indicator ((measurableSet_pollEvent v t T hT w).inter
        (measurableSet_pollEvent v t T hT w'))
  · intro w _
    exact integrable_finsetSum _ fun w' _ => (integrable_const 1).indicator
      ((measurableSet_pollEvent v t T hT w).inter (measurableSet_pollEvent v t T hT w'))

theorem integrable_pollAverage_mul (hT : MeasurableSet T) (N M : ℕ) :
    Integrable (fun p => pollAverage v t T N p * pollAverage v t T M p) Q.lawOne := by
  rw [pollAverage_mul_pollAverage]
  refine Integrable.const_mul (integrable_finsetSum _ fun w _ => integrable_finsetSum _
    fun w' _ => (integrable_const 1).indicator ?_) _
  exact (measurableSet_pollEvent v t T hT w).inter (measurableSet_pollEvent v t T hT w')

/-- **The cross moment is at least the constant.** -/
theorem pollConstant_le_integral_pollAverage_mul (hT : MeasurableSet T) {N M : ℕ} (hN : 1 ≤ N)
    (hM : 1 ≤ M) :
    pollConstant Q v t T ≤ ∫ p, pollAverage v t T N p * pollAverage v t T M p ∂Q.lawOne := by
  rw [integral_pollAverage_mul Q v t T hT]
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hsum : (N : ℝ) * M * pollConstant Q v t T ≤
      ∑ w ∈ pollBlockRow t N, ∑ w' ∈ pollBlockRow t M, pollMoment Q v t T w w' := by
    calc (N : ℝ) * M * pollConstant Q v t T
        = ∑ _w ∈ pollBlockRow t N, ∑ _w' ∈ pollBlockRow t M, pollConstant Q v t T := by
          simp only [Finset.sum_const, card_pollBlockRow, nsmul_eq_mul]
          ring
      _ ≤ _ := by
          refine Finset.sum_le_sum fun w hw => Finset.sum_le_sum fun w' hw' => ?_
          exact pollConstant_le_pollMoment Q v t T hT (rowBound_lt_of_mem_pollBlockRow hw)
            (rowBound_lt_of_mem_pollBlockRow hw')
  calc pollConstant Q v t T
      = (N : ℝ)⁻¹ * (M : ℝ)⁻¹ * ((N : ℝ) * M * pollConstant Q v t T) := by
        field_simp
    _ ≤ _ := by gcongr

/-- **The diagonal moment is at most the constant plus `1 / N`.** -/
theorem integral_pollAverage_sq_le (hT : MeasurableSet T) {N : ℕ} (hN : 1 ≤ N) :
    ∫ p, pollAverage v t T N p * pollAverage v t T N p ∂Q.lawOne ≤
      pollConstant Q v t T + (N : ℝ)⁻¹ := by
  rw [integral_pollAverage_mul Q v t T hT]
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hrow : ∀ w ∈ pollBlockRow t N,
      ∑ w' ∈ pollBlockRow t N, pollMoment Q v t T w w' ≤ N * pollConstant Q v t T + 1 := by
    intro w hw
    calc ∑ w' ∈ pollBlockRow t N, pollMoment Q v t T w w'
        ≤ ∑ w' ∈ pollBlockRow t N, (pollConstant Q v t T + if w' = w then 1 else 0) := by
          refine Finset.sum_le_sum fun w' hw' => ?_
          by_cases h : w' = w
          · subst h
            simp only [if_true]
            linarith [pollMoment_le_one Q v t T w' w', pollConstant_nonneg Q v t T]
          · simp only [h, if_false, add_zero]
            exact le_of_eq (pollMoment_eq_pollConstant Q v t T hT
              (rowBound_lt_of_mem_pollBlockRow hw) (rowBound_lt_of_mem_pollBlockRow hw')
              (Ne.symm h))
      _ = N * pollConstant Q v t T + 1 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, card_pollBlockRow, nsmul_eq_mul,
            Finset.sum_ite_eq' _ _ (fun _ => (1 : ℝ)), if_pos hw]
  calc (N : ℝ)⁻¹ * (N : ℝ)⁻¹ * ∑ w ∈ pollBlockRow t N, ∑ w' ∈ pollBlockRow t N,
        pollMoment Q v t T w w'
      ≤ (N : ℝ)⁻¹ * (N : ℝ)⁻¹ * ∑ _w ∈ pollBlockRow t N, (N * pollConstant Q v t T + 1) := by
        gcongr with w hw
        exact hrow w hw
    _ = pollConstant Q v t T + (N : ℝ)⁻¹ := by
        rw [Finset.sum_const, card_pollBlockRow, nsmul_eq_mul]
        field_simp

/-- **The Cauchy estimate**: the averages at stages `N` and `M` are within `1 / N + 1 / M` in
mean square. -/
theorem integral_sq_pollAverage_sub_le (hT : MeasurableSet T) {N M : ℕ} (hN : 1 ≤ N)
    (hM : 1 ≤ M) :
    ∫ p, (pollAverage v t T N p - pollAverage v t T M p) ^ 2 ∂Q.lawOne ≤
      (N : ℝ)⁻¹ + (M : ℝ)⁻¹ := by
  have hexp : (fun p => (pollAverage v t T N p - pollAverage v t T M p) ^ 2) =
      fun p => (pollAverage v t T N p * pollAverage v t T N p -
        (2 : ℝ) * (pollAverage v t T N p * pollAverage v t T M p)) +
        pollAverage v t T M p * pollAverage v t T M p := by
    funext p
    ring
  rw [hexp, integral_add, integral_sub, integral_const_mul]
  · linarith [integral_pollAverage_sq_le Q v t T hT hN, integral_pollAverage_sq_le Q v t T hT hM,
      pollConstant_le_integral_pollAverage_mul Q v t T hT hN hM]
  · exact integrable_pollAverage_mul Q v t T hT N N
  · exact (integrable_pollAverage_mul Q v t T hT N M).const_mul _
  · exact (integrable_pollAverage_mul Q v t T hT N N).sub
      ((integrable_pollAverage_mul Q v t T hT N M).const_mul _)
  · exact integrable_pollAverage_mul Q v t T hT M M

/-! ### The limit of the averages -/

/-- The averages from stage `1` on, as elements of `L²`. -/
noncomputable def pollAverageLp (hT : MeasurableSet T) (N : ℕ) : Lp ℝ 2 Q.lawOne :=
  (memLp_two_pollAverage Q v t T hT (N + 1)).toLp _

theorem dist_pollAverageLp_eq (hT : MeasurableSet T) (N M : ℕ) :
    dist (pollAverageLp Q v t T hT N) (pollAverageLp Q v t T hT M) =
      Real.sqrt (∫ p, (pollAverage v t T (N + 1) p - pollAverage v t T (M + 1) p) ^ 2
        ∂Q.lawOne) := by
  rw [dist_edist, pollAverageLp, pollAverageLp, Lp.edist_toLp_toLp,
    MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
      ((memLp_two_pollAverage Q v t T hT (N + 1)).sub (memLp_two_pollAverage Q v t T hT (M + 1))),
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _),
    Real.sqrt_eq_rpow, one_div]
  congr 2
  funext p
  simp only [ENNReal.toReal_ofNat, Pi.sub_apply, Real.norm_eq_abs, Real.rpow_two, sq_abs]

theorem cauchySeq_pollAverageLp (hT : MeasurableSet T) :
    CauchySeq (pollAverageLp Q v t T hT) := by
  refine cauchySeq_of_le_tendsto_0 (fun K : ℕ => Real.sqrt (2 * ((K : ℝ) + 1)⁻¹)) ?_ ?_
  · intro n m K hn hm
    rw [dist_pollAverageLp_eq]
    refine Real.sqrt_le_sqrt ?_
    have h1 := integral_sq_pollAverage_sub_le Q v t T hT (Nat.succ_le_succ (Nat.zero_le n))
      (Nat.succ_le_succ (Nat.zero_le m))
    have hn' : ((K : ℝ) + 1)⁻¹⁻¹ ≤ ((n : ℝ) + 1)⁻¹⁻¹ := by
      rw [inv_inv, inv_inv]; exact_mod_cast Nat.succ_le_succ hn
    have hm' : ((K : ℝ) + 1)⁻¹⁻¹ ≤ ((m : ℝ) + 1)⁻¹⁻¹ := by
      rw [inv_inv, inv_inv]; exact_mod_cast Nat.succ_le_succ hm
    have hn'' : ((n : ℝ) + 1)⁻¹ ≤ ((K : ℝ) + 1)⁻¹ :=
      inv_anti₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ hn)
    have hm'' : ((m : ℝ) + 1)⁻¹ ≤ ((K : ℝ) + 1)⁻¹ :=
      inv_anti₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ hm)
    push_cast at h1
    linarith
  · have h : Filter.Tendsto (fun K : ℕ => 2 * ((K : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
      simpa [one_div] using this
    have hs := (Real.continuous_sqrt.tendsto 0).comp h
    rw [Real.sqrt_zero] at hs
    exact hs

/-- **The `L²` limit of the averages, projected onto the environment.** There is an
environment-measurable integrable function which the averages approach in `L¹`. -/
theorem exists_rowLimit (hT : MeasurableSet T) :
    ∃ g : PooledOne S → ℝ, StronglyMeasurable[envAlg S] g ∧ Integrable g Q.lawOne ∧
      Filter.Tendsto (fun N => eLpNorm (pollAverage v t T (N + 1) - g) 1 Q.lawOne)
        Filter.atTop (nhds 0) := by
  obtain ⟨gLp, hgLp⟩ := cauchySeq_tendsto_of_complete (cauchySeq_pollAverageLp Q v t T hT)
  set g₀ : PooledOne S → ℝ := ⇑gLp with hg₀
  have hg₀int : Integrable g₀ Q.lawOne := (Lp.memLp gLp).integrable one_le_two
  refine ⟨Q.lawOne[g₀ | envAlg S], stronglyMeasurable_condExp, integrable_condExp, ?_⟩
  have hbound : ∀ N, eLpNorm (pollAverage v t T (N + 1) - Q.lawOne[g₀ | envAlg S]) 1 Q.lawOne ≤
      ENNReal.ofReal (dist (pollAverageLp Q v t T hT N) gLp) := by
    intro N
    have hsm := stronglyMeasurable_envAlg_pollAverage v t T hT (N + 1)
    have hint := integrable_pollAverage Q v t T hT (N + 1)
    have h1 : pollAverage v t T (N + 1) - Q.lawOne[g₀ | envAlg S] =ᵐ[Q.lawOne]
        Q.lawOne[pollAverage v t T (N + 1) - g₀ | envAlg S] := by
      refine ((condExp_sub hint hg₀int _).trans ?_).symm
      rw [condExp_of_stronglyMeasurable envAlg_le hsm hint]
    calc eLpNorm (pollAverage v t T (N + 1) - Q.lawOne[g₀ | envAlg S]) 1 Q.lawOne
        ≤ eLpNorm (pollAverage v t T (N + 1) - Q.lawOne[g₀ | envAlg S]) 2 Q.lawOne :=
          eLpNorm_le_eLpNorm_of_exponent_le one_le_two
            (hint.sub integrable_condExp).aestronglyMeasurable
      _ = eLpNorm (Q.lawOne[pollAverage v t T (N + 1) - g₀ | envAlg S]) 2 Q.lawOne :=
          eLpNorm_congr_ae h1
      _ ≤ eLpNorm (pollAverage v t T (N + 1) - g₀) 2 Q.lawOne :=
          eLpNorm_condExp_le_eLpNorm _ one_le_two
      _ = eLpNorm (⇑(pollAverageLp Q v t T hT N) - ⇑gLp) 2 Q.lawOne :=
          eLpNorm_congr_ae
            ((MemLp.coeFn_toLp (memLp_two_pollAverage Q v t T hT (N + 1))).symm.sub
              Filter.EventuallyEq.rfl)
      _ = ENNReal.ofReal (dist (pollAverageLp Q v t T hT N) gLp) := by
          rw [← Lp.edist_def, edist_dist]
  have hdist : Filter.Tendsto (fun N => ENNReal.ofReal (dist (pollAverageLp Q v t T hT N) gLp))
      Filter.atTop (nhds 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_iff_dist_tendsto_zero.mp hgLp)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdist (fun _ => bot_le)
    hbound

/-- **The set integrals of a limit against a swap-fixed set and an environment generator.** -/
theorem setIntegral_rowLimit (hT : MeasurableSet T) {g : PooledOne S → ℝ}
    (hgi : Integrable g Q.lawOne)
    (hg : Filter.Tendsto (fun N => eLpNorm (pollAverage v t T (N + 1) - g) 1 Q.lawOne)
      Filter.atTop (nhds 0))
    {K : Set (PooledOne S)} (hK : MeasurableSet K) {b : ℕ} (hKb : SwapFixed v b K)
    {G : Set (PooledOne S)} (hG : G ∈ envGenerators S) :
    ∫ p in K ∩ G, g p ∂Q.lawOne = Q.lawOne.real (rowEvent v t T ∩ (K ∩ G)) := by
  obtain ⟨bG, hbG⟩ := exists_swapFixed_of_mem_envGenerators v hG
  have hGm : MeasurableSet G := envAlg_le _ (measurableSet_envAlg_of_mem_envGenerators hG)
  have hKG : SwapFixed v (max b bG) (K ∩ G) :=
    (hKb.mono (le_max_left _ _)).inter (hbG.mono (le_max_right _ _))
  have hconv := tendsto_setIntegral_of_L1' g hgi.aestronglyMeasurable
    (Filter.Eventually.of_forall fun N => integrable_pollAverage Q v t T hT (N + 1)) hg (K ∩ G)
  have hev : (fun _ : ℕ => Q.lawOne.real (rowEvent v t T ∩ (K ∩ G))) =ᶠ[Filter.atTop]
      fun N => ∫ p in K ∩ G, pollAverage v t T (N + 1) p ∂Q.lawOne := by
    filter_upwards [Filter.eventually_ge_atTop (max b bG)] with N hN
    have hterm : ∀ w ∈ pollBlockRow t (N + 1),
        ∫ p in K ∩ G, (pollEvent v w t T).indicator (fun _ => (1 : ℝ)) p ∂Q.lawOne =
          Q.lawOne.real (rowEvent v t T ∩ (K ∩ G)) := by
      intro w hw
      have hwb : max b bG < w := lt_of_lt_of_le (Nat.lt_succ_of_le hN)
        (le_trans (Nat.le_add_left _ _) (le_of_mem_pollBlockRow hw))
      rw [setIntegral_indicator (measurableSet_pollEvent v t T hT w), setIntegral_const,
        smul_eq_mul, mul_one, Set.inter_comm, measureReal_def, measureReal_def,
        ← Q.measure_rowEvent_inter_eq_pollEvent v t T hT (hK.inter hGm) (hKG w hwb)]
    simp only [pollAverage]
    rw [integral_const_mul, integral_finsetSum (pollBlockRow t (N + 1))
      (f := fun w p => (pollEvent v w t T).indicator (fun _ => (1 : ℝ)) p) (fun w _ =>
        ((integrable_const (1 : ℝ)).indicator (measurableSet_pollEvent v t T hT w)).integrableOn),
      Finset.sum_congr rfl hterm, Finset.sum_const, card_pollBlockRow, nsmul_eq_mul,
      inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero N))]
  exact tendsto_nhds_unique hconv (tendsto_const_nhds.congr' hev)

/-! ### The peel identity -/

omit [Countable S.Srt] [Countable S.Rel] in
theorem univ_mem_envGenerators : (Set.univ : Set (PooledOne S)) ∈ envGenerators S :=
  ⟨Set.univ ×ˢ Set.univ, ⟨Set.univ, univ_mem_measurableCylinders _, Set.univ,
    (MeasurableSet.univ : MeasurableSet (Set.univ : Set (PooledRankLatentSpace S 1))), rfl⟩,
    by simp⟩

/-- **Conditioning on the environment peels the row of `v` off a swap-fixed set**: the limit `g`
of the averages multiplies. -/
theorem PooledRankExtension.condExp_rowEvent_inter_ae_eq_mul (hT : MeasurableSet T)
    {g : PooledOne S → ℝ} (hgm : StronglyMeasurable[envAlg S] g) (hgi : Integrable g Q.lawOne)
    (hg : Filter.Tendsto (fun N => eLpNorm (pollAverage v t T (N + 1) - g) 1 Q.lawOne)
      Filter.atTop (nhds 0))
    {K : Set (PooledOne S)} (hK : MeasurableSet K) {b : ℕ} (hKb : SwapFixed v b K) :
    Q.lawOne⟦rowEvent v t T ∩ K | envAlg S⟧ =ᵐ[Q.lawOne] g * Q.lawOne⟦K | envAlg S⟧ := by
  have hHm : MeasurableSet (rowEvent v t T) := measurableSet_rowEvent v t T hT
  have hKint : Integrable (K.indicator fun _ => (1 : ℝ)) Q.lawOne :=
    (integrable_const 1).indicator hK
  have hHKint : Integrable ((rowEvent v t T ∩ K).indicator fun _ => (1 : ℝ)) Q.lawOne :=
    (integrable_const 1).indicator (hHm.inter hK)
  have hgK : (fun p => g p * K.indicator (fun _ => (1 : ℝ)) p) = K.indicator g := by
    funext p
    by_cases hp : p ∈ K <;> simp [hp]
  have hgKint : Integrable (g * K.indicator fun _ => (1 : ℝ)) Q.lawOne := by
    show Integrable (fun p => g p * K.indicator (fun _ => (1 : ℝ)) p) Q.lawOne
    rw [hgK]
    exact hgi.indicator hK
  have hpull : Q.lawOne[g * K.indicator (fun _ => (1 : ℝ)) | envAlg S] =ᵐ[Q.lawOne]
      g * Q.lawOne⟦K | envAlg S⟧ :=
    condExp_mul_of_stronglyMeasurable_left hgm hgKint hKint
  set f₁ := Q.lawOne⟦rowEvent v t T ∩ K | envAlg S⟧ with hf₁
  set f₂ : PooledOne S → ℝ := g * Q.lawOne⟦K | envAlg S⟧ with hf₂
  have hf₂int : Integrable f₂ Q.lawOne := integrable_condExp.congr hpull
  have hf₂m : StronglyMeasurable[envAlg S] f₂ := hgm.mul stronglyMeasurable_condExp
  -- the set integrals agree on the generators
  have hbasic : ∀ G ∈ envGenerators S,
      ∫ p in G, f₁ p ∂Q.lawOne = ∫ p in G, f₂ p ∂Q.lawOne := by
    intro G hG
    have hGm : MeasurableSet[envAlg S] G := measurableSet_envAlg_of_mem_envGenerators hG
    have hGm' : MeasurableSet G := envAlg_le _ hGm
    rw [hf₁, setIntegral_condExp envAlg_le hHKint hGm, setIntegral_indicator (hHm.inter hK),
      setIntegral_const, smul_eq_mul, mul_one,
      show G ∩ (rowEvent v t T ∩ K) = rowEvent v t T ∩ (K ∩ G) by
        rw [Set.inter_comm G, Set.inter_assoc],
      ← setIntegral_rowLimit Q v t T hT hgi hg hK hKb hG, hf₂,
      setIntegral_congr_ae hGm' (hpull.mono fun p hp _ => hp.symm),
      setIntegral_condExp envAlg_le hgKint hGm,
      show (fun p => (g * K.indicator fun _ => (1 : ℝ)) p) = K.indicator g from hgK,
      setIntegral_indicator hK, Set.inter_comm]
  have huniv : ∫ p, f₁ p ∂Q.lawOne = ∫ p, f₂ p ∂Q.lawOne := by
    have := hbasic Set.univ univ_mem_envGenerators
    rwa [Measure.restrict_univ] at this
  have hall : ∀ s, MeasurableSet[envAlg S] s →
      ∫ p in s, f₁ p ∂Q.lawOne = ∫ p in s, f₂ p ∂Q.lawOne := by
    refine MeasurableSpace.induction_on_inter (m := envAlg S) envAlg_eq_generateFrom
      isPiSystem_envGenerators ?_ (fun G hG => hbasic G hG) ?_ ?_
    · simp
    · intro s hs h
      have hs' : MeasurableSet s := envAlg_le _ hs
      have e1 := integral_add_compl hs' integrable_condExp (f := f₁)
      have e2 := integral_add_compl hs' hf₂int (f := f₂)
      linarith
    · intro f hdisj hfm h
      have hfm' : ∀ i, MeasurableSet (f i) := fun i => envAlg_le _ (hfm i)
      rw [integral_iUnion hfm' hdisj integrable_condExp.integrableOn,
        integral_iUnion hfm' hdisj hf₂int.integrableOn]
      exact tsum_congr h
  exact ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' envAlg_le
    (fun s _ _ => integrable_condExp.integrableOn) (fun s _ _ => hf₂int.integrableOn)
    (fun s hs _ => hall s hs) stronglyMeasurable_condExp.aestronglyMeasurable
    hf₂m.aestronglyMeasurable

/-- **The row conditional probability multiplies against swap-fixed sets.** -/
theorem PooledRankExtension.condExp_rowEvent_inter (hT : MeasurableSet T) {K : Set (PooledOne S)}
    (hK : MeasurableSet K) {b : ℕ} (hKb : SwapFixed v b K) :
    Q.lawOne⟦rowEvent v t T ∩ K | envAlg S⟧ =ᵐ[Q.lawOne]
      Q.lawOne⟦rowEvent v t T | envAlg S⟧ * Q.lawOne⟦K | envAlg S⟧ := by
  obtain ⟨g, hgm, hgi, hg⟩ := exists_rowLimit Q v t T hT
  have hK' := Q.condExp_rowEvent_inter_ae_eq_mul v t T hT hgm hgi hg hK hKb
  have huniv := Q.condExp_rowEvent_inter_ae_eq_mul v t T hT hgm hgi hg MeasurableSet.univ
    (swapFixed_univ v 0)
  rw [Set.inter_univ, Set.indicator_univ, condExp_const envAlg_le] at huniv
  filter_upwards [hK', huniv] with p hp hp'
  rw [hp, Pi.mul_apply, Pi.mul_apply, hp']
  simp

end Row

/-! ### The finite-family product identity -/

omit [Countable S.Srt] [Countable S.Rel] in
/-- A finite intersection of rows at other vertices is swap-fixed at `v`. -/
theorem swapFixed_biInter_rowEvent {ι : Type*} (v : ι → Σ s : S.Srt, Vinfinite S s)
    (hv : Function.Injective v) (t : ∀ i, Finset (MarkedCoord (S := S) {v i}))
    (T : ∀ i, Set (t i → Bool)) (F : Finset ι) {i : ι} (hi : i ∉ F) :
    SwapFixed (v i) (F.sup fun j => rowBound (t j)) (⋂ j ∈ F, rowEvent (v j) (t j) (T j)) := by
  intro w hw
  rw [Set.preimage_iInter₂]
  refine Set.iInter₂_congr fun j hj => ?_
  have hij : v i ≠ v j := fun h => hi (hv h ▸ hj)
  exact (swapFixed_rowEvent_of_ne hij (t j) (T j)).mono
    (Finset.le_sup (f := fun j => rowBound (t j)) hj) w hw

/-- **Conditional independence of the marked rows given the environment, at rank one**: for
distinct original vertices and cylinder events of their marked rows, the conditional probability
of the intersection given the environment is the product of the conditional probabilities. -/
theorem PooledRankExtension.condExp_iInter_rowEvent_eq_prod {ι : Type*}
    (v : ι → Σ s : S.Srt, Vinfinite S s) (hv : Function.Injective v)
    (t : ∀ i, Finset (MarkedCoord (S := S) {v i})) (T : ∀ i, Set (t i → Bool))
    (hT : ∀ i, MeasurableSet (T i)) (F : Finset ι) :
    Q.lawOne⟦⋂ i ∈ F, rowEvent (v i) (t i) (T i) | envAlg S⟧ =ᵐ[Q.lawOne]
      ∏ i ∈ F, Q.lawOne⟦rowEvent (v i) (t i) (T i) | envAlg S⟧ := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ, Finset.prod_empty]
    rw [Set.indicator_univ, condExp_const envAlg_le]
    exact Filter.EventuallyEq.rfl
  | insert i F hi ih =>
    rw [Finset.set_biInter_insert, Finset.prod_insert hi]
    have hKm : MeasurableSet (⋂ j ∈ F, rowEvent (v j) (t j) (T j)) :=
      Finset.measurableSet_biInter _ fun j _ => measurableSet_rowEvent (v j) (t j) (T j) (hT j)
    have hpeel := Q.condExp_rowEvent_inter (v i) (t i) (T i) (hT i) hKm
      (swapFixed_biInter_rowEvent v hv t T F hi)
    filter_upwards [hpeel, ih] with p hp hp'
    rw [hp, Pi.mul_apply, Pi.mul_apply, hp']

end InfiniteRelExchangeableLaw

end RelSignature
