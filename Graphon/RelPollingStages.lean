/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelAustinPolling
import Graphon.RelPollGeometry
import Graphon.RelPooledFixingSeam

/-!
# The finite-stage polling conditionings (R4 converse, #107, #197)

The law-free layer of the pooled fixing-factor polling argument: the observation maps and
conditioning σ-algebras of Austin's reservoir argument, their **exact** transport under the two
motions the argument uses, and the identification of their limit with the polling conditioning
`sourcePollingCond`. No measure appears.

## The stages

For a set `W` of pooled tagged vertices, `avoidCond n W` reads the part of the polling
conditioning that **avoids `W`**: the pooled latent coordinates at supports disjoint from `W`,
and the mixed rank-`n` relation coordinates (those with a spare vertex) whose support is disjoint
from `W`. Its pullback `avoidAlgebra n W` decreases in `W`, and at `W = ∅` it is exactly the
pullback of `sourcePollingCond` (`avoidAlgebra_empty`).

## The two motions

* A **half-preserving** pooled permutation — one sending each half to itself, such as the
  original-half shift of a poll block — transports the stage at `W` exactly to the stage at the
  image of `W` (`comap_pooledJointRelabel_avoidAlgebra`). Mixedness is preserved, so the mixed
  coordinates avoiding `W` correspond bijectively to those avoiding the image of `W`.
* A pooled permutation **supported inside `W`** — a boundary-crossing finite swap of vertices of
  `W`, say — fixes the stage at `W` exactly (`comap_pooledJointRelabel_avoidAlgebra_of_fix`),
  since every coordinate the stage reads is fixed pointwise. This is where the argument uses
  boundary crossings, and it is why they cost nothing here: the stage is chosen to avoid the
  vertices being swapped.

What is **not** claimed: transport of the stage at `W` under a boundary-crossing permutation that
moves vertices outside `W`. A mixed support can then be carried onto a wholly original one, and
the family of mixed coordinates is not stable. The argument never needs that transport.

## The limit

For a decreasing sequence `W m` of avoided sets such that every finite set of vertices is
eventually avoided, the stages increase to the full polling conditioning
(`iSup_avoidAlgebra`): a *raw* equality of σ-algebras, since every coordinate of the conditioning
is a coordinate of some stage. This is the supremum direction, where no distributivity problem
arises. The tail joins of the original-carrier engine were intersections; here the stages are
nested the other way, and the conditional expectations along them converge upward.
-/

open MeasureTheory

namespace RelSignature

open InfiniteRelExchangeableLaw

universe u

variable {S : RelSignature.{u}} {n : ℕ}

/-! ### The stages -/

/-- Pooled latent indices avoiding `W`. -/
def AvoidLatentIndex (S : RelSignature.{u}) (n : ℕ) (W : Set (Σ s : S.Srt, PoolVertex S s)) :=
  {I : PooledRankLatentIndex S n // ∀ v ∈ I.1, v ∉ W}

open scoped Classical in
/-- Mixed rank-`n` coordinates avoiding `W`: relation coordinates whose support has cardinality
`n`, contains a spare vertex, and is disjoint from `W`. -/
def AvoidCoord (S : RelSignature.{u}) (n : ℕ) (W : Set (Σ s : S.Srt, PoolVertex S s)) :=
  {c : RelCoord S (PoolVertex S) // c.support.card = n ∧ (∃ v ∈ c.support, Sum.isRight v.2) ∧
    ∀ v ∈ c.support, v ∉ W}

open scoped Classical in
/-- The observation space of the stage at `W`. -/
abbrev AvoidSpace (S : RelSignature.{u}) (n : ℕ) (W : Set (Σ s : S.Srt, PoolVertex S s)) :=
  (AvoidLatentIndex S n W → ℝ) × (AvoidCoord S n W → Bool)

open scoped Classical in
/-- **The stage at `W`**: the part of the polling conditioning avoiding `W`. -/
def avoidCond (n : ℕ) (W : Set (Σ s : S.Srt, PoolVertex S s)) :
    RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → AvoidSpace S n W :=
  fun p => (fun I => p.2 I.1, fun c => p.1 c.1)

open scoped Classical in
theorem measurable_avoidCond (n : ℕ) (W : Set (Σ s : S.Srt, PoolVertex S s)) :
    Measurable (avoidCond (S := S) n W) :=
  (measurable_pi_lambda _ fun _ => measurable_snd.eval).prodMk
    (measurable_pi_lambda _ fun _ => measurable_fst.eval)

open scoped Classical in
/-- The conditioning σ-algebra of the stage at `W`. -/
@[implicit_reducible]
def avoidAlgebra (n : ℕ) (W : Set (Σ s : S.Srt, PoolVertex S s)) :
    MeasurableSpace (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) :=
  MeasurableSpace.comap (avoidCond n W) inferInstance

open scoped Classical in
theorem avoidAlgebra_le (n : ℕ) (W : Set (Σ s : S.Srt, PoolVertex S s)) :
    avoidAlgebra (S := S) n W ≤
      (inferInstance :
        MeasurableSpace (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) :=
  (measurable_avoidCond n W).comap_le

open scoped Classical in
/-- A stage factors through any stage avoiding less. -/
theorem avoidAlgebra_mono {W W' : Set (Σ s : S.Srt, PoolVertex S s)} (h : W ⊆ W') :
    avoidAlgebra (S := S) n W' ≤ avoidAlgebra n W := by
  have hfac : avoidCond (S := S) n W' = (fun x : AvoidSpace S n W =>
      ((fun I : AvoidLatentIndex S n W' => x.1 ⟨I.1, fun v hv hvW => I.2 v hv (h hvW)⟩),
        fun c : AvoidCoord S n W' =>
          x.2 ⟨c.1, c.2.1, c.2.2.1, fun v hv hvW => c.2.2.2 v hv (h hvW)⟩))
      ∘ avoidCond n W := rfl
  rw [avoidAlgebra, hfac, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono ((measurable_pi_lambda _ fun _ => measurable_fst.eval).prodMk
    (measurable_pi_lambda _ fun _ => measurable_snd.eval)).comap_le

/-! ### The stage at `∅` is the polling conditioning -/

open scoped Classical in
/-- **The stage at `∅` is the polling conditioning**: the same coordinates, read once as latents
and mixed coordinates, once as latents and clusters. -/
theorem avoidAlgebra_empty (n : ℕ) :
    avoidAlgebra (S := S) n ∅ =
      MeasurableSpace.comap (InfiniteRelExchangeableLaw.sourcePollingCond (S := S) (n := n))
        inferInstance := by
  refine le_antisymm ?_ ?_
  · -- the stage is a function of the polling conditioning
    have hfac : avoidCond (S := S) n ∅ = (fun y : PooledRankLatentSpace S n × ClusterSpace S n =>
        ((fun I : AvoidLatentIndex S n ∅ => y.1 I.1),
          fun c : AvoidCoord S n ∅ => y.2 ⟨c.1.support, c.2.1, c.2.2.1⟩ ⟨c.1, rfl⟩)) ∘
        InfiniteRelExchangeableLaw.sourcePollingCond := rfl
    rw [avoidAlgebra, hfac, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono ((measurable_pi_lambda _ fun _ => measurable_fst.eval).prodMk
      (measurable_pi_lambda _ fun _ => measurable_snd.eval.eval)).comap_le
  · have hfac : InfiniteRelExchangeableLaw.sourcePollingCond (S := S) (n := n) =
        (fun x : AvoidSpace S n ∅ =>
        ((fun I : PooledRankLatentIndex S n => x.1 ⟨I, fun _ _ h => h⟩),
          fun (Ac : MixedClusterIndex S n) (c : BlockIndexOver (PoolVertex S) Ac.1) =>
            x.2 ⟨c.1, by rw [c.2]; exact Ac.2.1, by rw [c.2]; exact Ac.2.2, fun _ _ h => h⟩)) ∘
        avoidCond n ∅ := rfl
    rw [avoidAlgebra, hfac, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono ((measurable_pi_lambda _ fun _ => measurable_fst.eval).prodMk
      (measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ =>
        measurable_snd.eval)).comap_le

/-! ### Exact transport under the two motions -/

/-- The joint pooled relabeling by an arbitrary pooled permutation family. -/
noncomputable def pooledJointRelabel (ρ : ∀ s, Equiv.Perm (PoolVertex S s)) (n : ℕ) :
    RelStructure S (PoolVertex S) × PooledRankLatentSpace S n →
      RelStructure S (PoolVertex S) × PooledRankLatentSpace S n :=
  Prod.map (RelStructure.relabel ρ) (pooledRankLatentRelabel ρ n)

theorem measurable_pooledJointRelabel (ρ : ∀ s, Equiv.Perm (PoolVertex S s)) (n : ℕ) :
    Measurable (pooledJointRelabel (S := S) ρ n) :=
  (measurable_relabel ρ).prodMap (pooledRankLatentRelabel ρ n).measurable

/-- A pooled permutation family sending each half to itself. -/
def HalfPreserving (ρ : ∀ s, Equiv.Perm (PoolVertex S s)) : Prop :=
  ∀ s v, Sum.isRight (ρ s v) = Sum.isRight v

theorem HalfPreserving.inv {ρ : ∀ s, Equiv.Perm (PoolVertex S s)} (h : HalfPreserving ρ) :
    HalfPreserving fun s => (ρ s)⁻¹ := fun s v => by
  conv_rhs => rw [← (ρ s).apply_symm_apply v]
  exact (h s _).symm

/-- The image of an avoided set under a pooled permutation family. -/
def imageSet (ρ : ∀ s, Equiv.Perm (PoolVertex S s)) (W : Set (Σ s : S.Srt, PoolVertex S s)) :
    Set (Σ s : S.Srt, PoolVertex S s) :=
  (Sigma.map id fun s => ⇑(ρ s)) '' W

open scoped Classical in
/-- The stage at `W`, read after the joint relabeling, is a function of the stage at the image of
`W`: every coordinate the former reads is the image of one the latter reads. Half-preservation
keeps the transported coordinates mixed. -/
private theorem avoidCond_comp_pooledJointRelabel {ρ : ∀ s, Equiv.Perm (PoolVertex S s)}
    (hρ : HalfPreserving ρ) {W W' : Set (Σ s : S.Srt, PoolVertex S s)} (hW' : imageSet ρ W = W') :
    ∃ Φ : AvoidSpace S n W' → AvoidSpace S n W, Measurable Φ ∧
      avoidCond n W ∘ pooledJointRelabel ρ n = Φ ∘ avoidCond n W' := by
  subst hW'
  have hinj : Function.Injective (Sigma.map id fun s => ⇑(ρ s) :
      (Σ s : S.Srt, PoolVertex S s) → Σ s : S.Srt, PoolVertex S s) :=
    Function.injective_id.sigma_map fun s => (ρ s).injective
  refine ⟨fun x =>
    ((fun I : AvoidLatentIndex S n W => x.1 ⟨latentIndexPerm ρ n I.1, fun v hv hvW => ?_⟩),
      fun c : AvoidCoord S n W => x.2 ⟨RelCoord.map (fun s => ⇑(ρ s)) c.1, ?_, ?_, ?_⟩), ?_, ?_⟩
  · -- the moved latent index avoids the moved set
    rw [latentIndexPerm_apply_coe] at hv
    simp only [Finset.mem_image] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨u, hu, hu'⟩ := hvW
    exact I.2 w hw (hinj hu' ▸ hu)
  · rw [RelCoord.support_map]
    convert (Finset.card_image_of_injective c.1.support hinj).trans c.2.1
  · obtain ⟨v, hv, hvr⟩ := c.2.2.1
    refine ⟨Sigma.map id (fun s => ⇑(ρ s)) v, ?_, ?_⟩
    · rw [RelCoord.support_map]
      simp only [Finset.mem_image]
      exact ⟨v, hv, rfl⟩
    · show Sum.isRight (ρ v.1 v.2) = true
      rw [hρ]
      exact hvr
  · intro v hv hvW
    rw [RelCoord.support_map] at hv
    simp only [Finset.mem_image] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨u, hu, hu'⟩ := hvW
    exact c.2.2.2 w hw (hinj hu' ▸ hu)
  · exact (measurable_pi_lambda _ fun _ => measurable_fst.eval).prodMk
      (measurable_pi_lambda _ fun _ => measurable_snd.eval)
  · rfl

open scoped Classical in
/-- **Exact transport under a half-preserving permutation**: the pullback of the stage at `W`
along the joint relabeling is the stage at the image of `W`. -/
theorem comap_pooledJointRelabel_avoidAlgebra {ρ : ∀ s, Equiv.Perm (PoolVertex S s)}
    (hρ : HalfPreserving ρ) (W : Set (Σ s : S.Srt, PoolVertex S s)) :
    MeasurableSpace.comap (pooledJointRelabel ρ n) (avoidAlgebra (S := S) n W) =
      avoidAlgebra n (imageSet ρ W) := by
  refine le_antisymm ?_ ?_
  · obtain ⟨Φ, hΦ, hfac⟩ := avoidCond_comp_pooledJointRelabel (n := n) hρ (W := W) rfl
    rw [avoidAlgebra, MeasurableSpace.comap_comp, hfac, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hΦ.comap_le
  · -- the inverse permutation carries the image of `W` back to `W`
    have hWW : imageSet (fun s => (ρ s)⁻¹) (imageSet ρ W) = W := by
      rw [imageSet, imageSet, Set.image_image]
      have hid : (fun v : Σ s : S.Srt, PoolVertex S s =>
          Sigma.map id (fun s => ⇑(ρ s)⁻¹) (Sigma.map id (fun s => ⇑(ρ s)) v)) = id := by
        funext v
        obtain ⟨s, x⟩ := v
        show (⟨s, (ρ s)⁻¹ (ρ s x)⟩ : Σ s : S.Srt, PoolVertex S s) = ⟨s, x⟩
        rw [show (ρ s)⁻¹ (ρ s x) = x from (ρ s).symm_apply_apply x]
      rw [hid, Set.image_id]
    obtain ⟨Φ, hΦ, hfac⟩ := avoidCond_comp_pooledJointRelabel (n := n) hρ.inv hWW
    -- precompose with the relabeling by `ρ` and cancel
    have hcancel : pooledJointRelabel (fun s => (ρ s)⁻¹) n ∘ pooledJointRelabel ρ n = id := by
      funext p
      refine Prod.ext ?_ ?_
      · show RelStructure.comap _ (RelStructure.comap _ p.1) = p.1
        rw [← RelStructure.comap_comp]
        convert RelStructure.comap_id p.1 using 2
        funext s x
        exact (ρ s).apply_symm_apply x
      · show pooledRankLatentRelabel (fun s => (ρ s)⁻¹) n (pooledRankLatentRelabel ρ n p.2) = p.2
        funext I
        rw [pooledRankLatentRelabel_apply, pooledRankLatentRelabel_apply]
        rw [show latentIndexPerm ρ n (latentIndexPerm (fun s => (ρ s)⁻¹) n I) = I from
          Subtype.ext (by
            rw [latentIndexPerm_apply_coe, latentIndexPerm_apply_coe]
            ext v
            simp only [Finset.mem_image]
            constructor
            · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
              obtain ⟨s, x⟩ := u
              show (⟨s, ρ s ((ρ s)⁻¹ x)⟩ : Σ s : S.Srt, PoolVertex S s) ∈ I.1
              rw [show ρ s ((ρ s)⁻¹ x) = x from (ρ s).apply_symm_apply x]
              exact hu
            · intro hv
              refine ⟨Sigma.map id (fun s => ⇑(ρ s)⁻¹) v, ⟨v, hv, rfl⟩, ?_⟩
              obtain ⟨s, x⟩ := v
              show (⟨s, ρ s ((ρ s)⁻¹ x)⟩ : Σ s : S.Srt, PoolVertex S s) = ⟨s, x⟩
              rw [show ρ s ((ρ s)⁻¹ x) = x from (ρ s).apply_symm_apply x])]
    have hfac' : avoidCond n (imageSet ρ W) =
        Φ ∘ avoidCond n W ∘ pooledJointRelabel ρ n := by
      rw [← Function.comp_assoc, ← hfac, Function.comp_assoc, hcancel, Function.comp_id]
    show MeasurableSpace.comap (avoidCond n (imageSet ρ W)) inferInstance ≤
      MeasurableSpace.comap (pooledJointRelabel ρ n)
        (MeasurableSpace.comap (avoidCond n W) inferInstance)
    rw [hfac', ← MeasurableSpace.comap_comp, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (MeasurableSpace.comap_mono hΦ.comap_le)

open scoped Classical in
/-- **Exact invariance under a permutation supported inside `W`**: every coordinate the stage at
`W` reads is fixed pointwise, so the stage is fixed. This is the transport under the
boundary-crossing swaps of the insertion step. -/
theorem comap_pooledJointRelabel_avoidAlgebra_of_fix {ρ : ∀ s, Equiv.Perm (PoolVertex S s)}
    {W : Set (Σ s : S.Srt, PoolVertex S s)}
    (hρ : ∀ v : Σ s : S.Srt, PoolVertex S s, v ∉ W → ρ v.1 v.2 = v.2) :
    MeasurableSpace.comap (pooledJointRelabel ρ n) (avoidAlgebra (S := S) n W) =
      avoidAlgebra n W := by
  have hfix : avoidCond (S := S) n W ∘ pooledJointRelabel ρ n = avoidCond n W := by
    funext p
    refine Prod.ext ?_ ?_
    · funext I
      show p.2 (latentIndexPerm ρ n I.1) = p.2 I.1
      have hfixI : ∀ w ∈ I.1.1, Sigma.map id (fun s => ⇑(ρ s)) w = w := by
        intro w hw
        obtain ⟨s, x⟩ := w
        show (⟨s, ρ s x⟩ : Σ s : S.Srt, PoolVertex S s) = ⟨s, x⟩
        rw [hρ ⟨s, x⟩ (I.2 _ hw)]
      rw [show latentIndexPerm ρ n I.1 = I.1 from Subtype.ext (by
        rw [latentIndexPerm_apply_coe]
        ext v
        simp only [Finset.mem_image]
        constructor
        · rintro ⟨w, hw, rfl⟩
          rw [hfixI w hw]
          exact hw
        · intro hv
          exact ⟨v, hv, hfixI v hv⟩)]
    · funext c
      show p.1 (RelCoord.map (fun s => ⇑(ρ s)) c.1) = p.1 c.1
      rw [show RelCoord.map (fun s => ⇑(ρ s)) c.1 = c.1 from by
        show (⟨c.1.1, fun i => ρ _ (c.1.2 i)⟩ : RelCoord S (PoolVertex S)) = ⟨c.1.1, c.1.2⟩
        rw [show (fun i => ρ (S.argSort c.1.1 i) (c.1.2 i)) = c.1.2 from funext fun i =>
          hρ ⟨_, c.1.2 i⟩ (c.2.2.2 _ ((RelCoord.mem_support_iff _ _).mpr ⟨i, rfl⟩))]]
  rw [avoidAlgebra, MeasurableSpace.comap_comp, hfix]

/-! ### The limit of the stages -/

open scoped Classical in
/-- **The stages increase to the polling conditioning.** For a decreasing sequence of avoided
sets such that every finite set of vertices is eventually avoided, the supremum of the stages is
the stage at `∅` — a raw equality: every coordinate of the polling conditioning is read by some
stage. -/
theorem iSup_avoidAlgebra (W : ℕ → Set (Σ s : S.Srt, PoolVertex S s))
    (hev : ∀ F : Finset (Σ s : S.Srt, PoolVertex S s), ∃ m, ∀ v ∈ F, v ∉ W m) :
    (⨆ m, avoidAlgebra (S := S) n (W m)) = avoidAlgebra n ∅ := by
  refine le_antisymm (iSup_le fun m => avoidAlgebra_mono (Set.empty_subset _)) ?_
  -- the stage at `∅` is the join of its coordinates
  rw [avoidAlgebra, show (inferInstance : MeasurableSpace (AvoidSpace S n ∅)) =
      MeasurableSpace.prod _ _ from rfl,
    show avoidCond (S := S) n ∅ = fun p => ((avoidCond n ∅ p).1, (avoidCond n ∅ p).2) from rfl,
    MeasurableSpace.comap_prodMk]
  refine sup_le ?_ ?_
  · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun I => ?_
    obtain ⟨m, hm⟩ := hev I.1.1
    refine le_trans ?_ (le_iSup (fun m => avoidAlgebra (S := S) n (W m)) m)
    rw [MeasurableSpace.comap_comp]
    have hfac : ((fun x : AvoidLatentIndex S n ∅ → ℝ => x I) ∘ fun p => (avoidCond n ∅ p).1) =
        (fun x : AvoidSpace S n (W m) => x.1 ⟨I.1, hm⟩) ∘ avoidCond n (W m) := rfl
    rw [hfac, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_fst.eval).comap_le
  · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun c => ?_
    obtain ⟨m, hm⟩ := hev c.1.support
    refine le_trans ?_ (le_iSup (fun m => avoidAlgebra (S := S) n (W m)) m)
    rw [MeasurableSpace.comap_comp]
    have hfac : ((fun x : AvoidCoord S n ∅ → Bool => x c) ∘ fun p => (avoidCond n ∅ p).2) =
        (fun x : AvoidSpace S n (W m) => x.2 ⟨c.1, c.2.1, c.2.2.1, hm⟩) ∘ avoidCond n (W m) :=
      rfl
    rw [hfac, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_snd.eval).comap_le

/-! ### The reservoir: tails of poll blocks, in both halves

The reservoir must contain the poll blocks in **both** halves: the insertion step swaps an
original block with its spare copy, and a swap moving an original vertex necessarily moves a spare
one, so both must lie inside the avoided set for the stage to be fixed. The shift accordingly
applies the poll permutation synchronously to both halves. -/

section Reservoir

variable (N : ℕ) [NeZero N] (D : Finset (Σ s : S.Srt, Vinfinite S s))

/-- The original and spare copies of a vertex set of the original carrier. -/
def bothHalves (B : Finset (Σ s : S.Srt, Vinfinite S s)) : Set (Σ s : S.Srt, PoolVertex S s) :=
  (Sigma.map id fun s => ⇑(originalVertex S s)) '' (B : Set _) ∪
    (Sigma.map id fun s => ⇑(poolVertex S s)) '' (B : Set _)

/-- **The reservoir at stage `m`**: both copies of the poll blocks in slots `m` and beyond. -/
def reservoir (m : ℕ) : Set (Σ s : S.Srt, PoolVertex S s) :=
  ⋃ k ∈ Set.Ici m, bothHalves (pollBlock N D k)

omit [NeZero N] in
theorem reservoir_antitone : Antitone (reservoir (S := S) N D) := fun _ _ h =>
  Set.biUnion_subset_biUnion_left fun _ hk => Set.mem_Ici.mpr (le_trans h hk)

omit [NeZero N] in
theorem mem_reservoir {m : ℕ} {v : Σ s : S.Srt, PoolVertex S s} :
    v ∈ reservoir N D m ↔ ∃ k, m ≤ k ∧ ∃ w ∈ pollBlock N D k,
      Sigma.map id (fun s => ⇑(originalVertex S s)) w = v ∨
        Sigma.map id (fun s => ⇑(poolVertex S s)) w = v := by
  simp only [reservoir, bothHalves, Set.mem_iUnion, Set.mem_Ici, Set.mem_union, Set.mem_image,
    Finset.mem_coe, exists_prop]
  constructor
  · rintro ⟨k, hk, ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩⟩
    · exact ⟨k, hk, w, hw, Or.inl rfl⟩
    · exact ⟨k, hk, w, hw, Or.inr rfl⟩
  · rintro ⟨k, hk, w, hw, rfl | rfl⟩
    · exact ⟨k, hk, Or.inl ⟨w, hw, rfl⟩⟩
    · exact ⟨k, hk, Or.inr ⟨w, hw, rfl⟩⟩

/-- The underlying original vertex of a pooled vertex. -/
def poolValue (v : Σ s : S.Srt, PoolVertex S s) : ℕ := Sum.elim id id v.2

omit [NeZero N] in
theorem poolValue_of_mem_reservoir {m : ℕ} {v : Σ s : S.Srt, PoolVertex S s}
    (hv : v ∈ reservoir N D m) : ∃ k, m ≤ k ∧ pollIndex k * N ≤ poolValue v := by
  obtain ⟨k, hk, w, hw, rfl | rfl⟩ := (mem_reservoir N D).mp hv <;>
    exact ⟨k, hk, le_of_mem_pollBlock hw⟩

/-- **Finite-set exhaustion**: the reservoirs eventually avoid any finite set. -/
theorem exists_reservoir_disjoint (F : Finset (Σ s : S.Srt, PoolVertex S s)) :
    ∃ m, ∀ v ∈ F, v ∉ reservoir N D m := by
  classical
  set K : ℕ := (F.sup poolValue) + 1 with hK
  obtain ⟨m, hm⟩ := exists_le_pollIndex K
  refine ⟨m, fun v hv hres => ?_⟩
  obtain ⟨k, hmk, h1⟩ := poolValue_of_mem_reservoir N D hres
  have h2 : K ≤ pollIndex k := hm k hmk
  have h3 : poolValue v ≤ K - 1 := by
    rw [hK, Nat.add_sub_cancel]
    exact Finset.le_sup (f := poolValue) hv
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have h5 : K ≤ pollIndex k * N := le_trans h2 (Nat.le_mul_of_pos_right _ hN)
  have hK1 : 1 ≤ K := Nat.le_add_left 1 _
  exact lt_irrefl _ (lt_of_le_of_lt (h5.trans (h1.trans h3)) (Nat.sub_lt hK1 Nat.one_pos))

omit [NeZero N] in
/-- A vertex of a positive slot sits at or above the layout bound. -/
theorem le_of_mem_pollBlock_pos {k : ℕ} (hk : 0 < k) {w : Σ s : S.Srt, Vinfinite S s}
    (hw : w ∈ pollBlock N D k) : N ≤ w.2 := by
  have h1 : pollIndex k * N ≤ w.2 := le_of_mem_pollBlock hw
  have h2 : 1 ≤ pollIndex k := by
    by_contra h0
    have h0' : pollIndex k = 0 := by omega
    have : pollEquivInt (k : ℤ) = pollEquivInt 0 := by rw [← pollIndex, h0', pollEquivInt_zero]
    have := pollEquivInt.injective this
    omega
  exact le_trans (Nat.le_mul_of_pos_left _ h2) h1

omit [NeZero N] in
/-- An original-carrier vertex below the bound and outside `D` lies in no poll block. -/
theorem notMem_pollBlock_of_lt {w : Σ s : S.Srt, Vinfinite S s} (hw : w.2 < N) (hwD : w ∉ D)
    (k : ℕ) : w ∉ pollBlock N D k := by
  intro hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · rw [pollBlock_zero] at hk
    exact hwD hk
  · exact lt_irrefl _ (lt_of_lt_of_le hw (le_of_mem_pollBlock_pos N D hpos hk))

omit [NeZero N] in
/-- **The target is avoided**: the original copy of a vertex below the bound and outside `D` lies
in no reservoir. -/
theorem notMem_reservoir_of_lt {m : ℕ} {w : Σ s : S.Srt, Vinfinite S s} (hw : w.2 < N)
    (hwD : w ∉ D) : Sigma.map id (fun s => ⇑(originalVertex S s)) w ∉ reservoir N D m := by
  intro hres
  obtain ⟨k, -, u, hu, hu'⟩ := (mem_reservoir N D).mp hres
  rcases hu' with hu' | hu'
  · have hinj : Function.Injective (Sigma.map id fun s => ⇑(originalVertex S s) :
        (Σ s : S.Srt, Vinfinite S s) → Σ s : S.Srt, PoolVertex S s) :=
      Function.injective_id.sigma_map fun s => (originalVertex S s).injective
    exact notMem_pollBlock_of_lt N D hw hwD k (hinj hu' ▸ hu)
  · -- an original copy is never a spare copy
    have := congrArg (fun v : Σ s : S.Srt, PoolVertex S s => Sum.isRight v.2) hu'
    exact Bool.noConfusion this

/-- **The synchronous pooled poll shift**: the poll permutation on both halves at once.
Half-preserving, with finitely many active sorts and infinite vertex support. -/
noncomputable def pooledPollPerm : ∀ s, Equiv.Perm (PoolVertex S s) :=
  fun s => Equiv.sumCongr (pollPerm N D s) (pollPerm N D s)

theorem halfPreserving_pooledPollPerm : HalfPreserving (pooledPollPerm (S := S) N D) := by
  intro s v
  cases v <;> rfl

open scoped Classical in
theorem pooledPollPerm_eq_one : ∀ s, s ∉ D.image Sigma.fst → pooledPollPerm (S := S) N D s = 1 := by
  intro s hs
  show Equiv.sumCongr (pollPerm N D s) (pollPerm N D s) = 1
  rw [pollPerm_eq_one_of_notMem N D hs]
  ext x
  cases x <;> rfl

theorem pooledPollPerm_original (w : Σ s : S.Srt, Vinfinite S s) :
    Sigma.map id (fun s => ⇑(pooledPollPerm (S := S) N D s))
        (Sigma.map id (fun s => ⇑(originalVertex S s)) w) =
      Sigma.map id (fun s => ⇑(originalVertex S s))
        (Sigma.map id (fun s => ⇑(pollPerm N D s)) w) := rfl

theorem pooledPollPerm_pool (w : Σ s : S.Srt, Vinfinite S s) :
    Sigma.map id (fun s => ⇑(pooledPollPerm (S := S) N D s))
        (Sigma.map id (fun s => ⇑(poolVertex S s)) w) =
      Sigma.map id (fun s => ⇑(poolVertex S s))
        (Sigma.map id (fun s => ⇑(pollPerm N D s)) w) := rfl

open scoped Classical in
/-- **The image law**: the synchronous shift carries the reservoir at stage `m` onto the reservoir
at stage `m + 1`, exactly. -/
theorem imageSet_pooledPollPerm_reservoir (hD : ∀ v ∈ D, v.2 < N) (m : ℕ) :
    imageSet (pooledPollPerm (S := S) N D) (reservoir N D m) = reservoir N D (m + 1) := by
  ext v
  rw [imageSet, Set.mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨k, hmk, w, hw, rfl | rfl⟩ := (mem_reservoir N D).mp hu
    · refine (mem_reservoir N D).mpr ⟨k + 1, by omega,
        Sigma.map id (fun s => ⇑(pollPerm N D s)) w, ?_, Or.inl (pooledPollPerm_original N D w)⟩
      rw [← pollBlock_image_pollPerm hD k]
      exact Finset.mem_image_of_mem _ hw
    · refine (mem_reservoir N D).mpr ⟨k + 1, by omega,
        Sigma.map id (fun s => ⇑(pollPerm N D s)) w, ?_, Or.inr (pooledPollPerm_pool N D w)⟩
      rw [← pollBlock_image_pollPerm hD k]
      exact Finset.mem_image_of_mem _ hw
  · intro hv
    obtain ⟨k, hmk, w, hw, hw'⟩ := (mem_reservoir N D).mp hv
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [← pollBlock_image_pollPerm hD k'] at hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    rcases hw' with rfl | rfl
    · exact ⟨Sigma.map id (fun s => ⇑(originalVertex S s)) u,
        (mem_reservoir N D).mpr ⟨k', by omega, u, hu, Or.inl rfl⟩,
        (pooledPollPerm_original N D u).symm⟩
    · exact ⟨Sigma.map id (fun s => ⇑(poolVertex S s)) u,
        (mem_reservoir N D).mpr ⟨k', by omega, u, hu, Or.inr rfl⟩,
        (pooledPollPerm_pool N D u).symm⟩

/-- **The inverse orientation**: pulling the reservoir at stage `m + 1` back along the inverse
shift is the reservoir at stage `m`. -/
theorem imageSet_pooledPollPerm_inv_reservoir (hD : ∀ v ∈ D, v.2 < N) (m : ℕ) :
    imageSet (fun s => (pooledPollPerm (S := S) N D s)⁻¹) (reservoir N D (m + 1)) =
      reservoir N D m := by
  rw [← imageSet_pooledPollPerm_reservoir N D hD m, imageSet, imageSet, Set.image_image]
  convert Set.image_id _ using 2
  funext u
  obtain ⟨s, x⟩ := u
  show (⟨s, (pooledPollPerm N D s)⁻¹ (pooledPollPerm N D s x)⟩ : Σ s : S.Srt, PoolVertex S s) =
    ⟨s, x⟩
  rw [show (pooledPollPerm N D s)⁻¹ (pooledPollPerm N D s x) = x from
    (pooledPollPerm N D s).symm_apply_apply x]

/-- **The reservoir filtration**: the stages avoiding the reservoirs, increasing in `m`. -/
noncomputable def reservoirFiltration (n : ℕ) : Filtration ℕ
    (inferInstance : MeasurableSpace (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))
    where
  seq m := avoidAlgebra n (reservoir N D m)
  mono' := fun _ _ h => avoidAlgebra_mono (reservoir_antitone N D h)
  le' := fun _ => avoidAlgebra_le n _

omit [NeZero N] in
theorem reservoirFiltration_apply (n m : ℕ) :
    reservoirFiltration (S := S) N D n m = avoidAlgebra n (reservoir N D m) := rfl

/-- The filtration's supremum is the polling conditioning. -/
theorem iSup_reservoirFiltration (n : ℕ) :
    (⨆ m, reservoirFiltration (S := S) N D n m) =
      MeasurableSpace.comap (InfiniteRelExchangeableLaw.sourcePollingCond (S := S) (n := n))
        inferInstance := by
  rw [← avoidAlgebra_empty]
  exact iSup_avoidAlgebra (reservoir N D) (exists_reservoir_disjoint N D)

/-- **Adjacent stages under the inverse shift**: the larger stage `m + 1` pulls back along the
inverse synchronous shift to the smaller stage `m`, exactly. This is the `comap T m₁ = m₂` input
of the tail engine, in the orientation Lévy upward needs. -/
theorem comap_pooledJointRelabel_inv_reservoirFiltration (hD : ∀ v ∈ D, v.2 < N) (n m : ℕ) :
    MeasurableSpace.comap (pooledJointRelabel (fun s => (pooledPollPerm (S := S) N D s)⁻¹) n)
        (reservoirFiltration N D n (m + 1)) = reservoirFiltration N D n m := by
  rw [reservoirFiltration_apply, reservoirFiltration_apply,
    comap_pooledJointRelabel_avoidAlgebra (halfPreserving_pooledPollPerm N D).inv,
    imageSet_pooledPollPerm_inv_reservoir N D hD m]

/-! ### The boundary swap

The insertion step exchanges the original block at slot `m` with its spare copy. The swap is a
finite boundary-crossing motion: it moves exactly the two copies of the slot-`m` block, both of
which lie in the stage-`m` reservoir, so the stage at `m` is fixed by
`comap_pooledJointRelabel_avoidAlgebra_of_fix`, while the target support — original, below the
bound, outside `D` — is fixed pointwise. -/

open scoped Classical in
/-- The swap of the two halves on the vertices of `B`, on one sort. -/
noncomputable def swapHalvesFun (B : Finset (Σ s : S.Srt, Vinfinite S s)) (s : S.Srt) :
    PoolVertex S s → PoolVertex S s
  | Sum.inl x => if (⟨s, x⟩ : Σ s : S.Srt, Vinfinite S s) ∈ B then Sum.inr x else Sum.inl x
  | Sum.inr x => if (⟨s, x⟩ : Σ s : S.Srt, Vinfinite S s) ∈ B then Sum.inl x else Sum.inr x

open scoped Classical in
theorem swapHalvesFun_involutive (B : Finset (Σ s : S.Srt, Vinfinite S s)) (s : S.Srt) :
    Function.Involutive (swapHalvesFun (S := S) B s) := by
  intro x
  rcases x with x | x <;> by_cases hx : (⟨s, x⟩ : Σ s : S.Srt, Vinfinite S s) ∈ B <;>
    simp [swapHalvesFun, hx]

open scoped Classical in
/-- **The boundary swap** of a vertex set of the original carrier: exchanges each vertex's
original and spare copies, fixing everything else. -/
noncomputable def boundarySwap (B : Finset (Σ s : S.Srt, Vinfinite S s)) :
    ∀ s, Equiv.Perm (PoolVertex S s) :=
  fun s => (swapHalvesFun_involutive B s).toPerm

open scoped Classical in
theorem boundarySwap_apply (B : Finset (Σ s : S.Srt, Vinfinite S s)) (s : S.Srt)
    (x : PoolVertex S s) : boundarySwap (S := S) B s x = swapHalvesFun B s x := rfl

open scoped Classical in
/-- A vertex moved by the swap lies in one of the two copies of `B`. -/
theorem mem_bothHalves_of_boundarySwap_ne (B : Finset (Σ s : S.Srt, Vinfinite S s))
    (v : Σ s : S.Srt, PoolVertex S s) (hv : boundarySwap B v.1 v.2 ≠ v.2) :
    v ∈ bothHalves B := by
  obtain ⟨s, x | x⟩ := v
  · by_cases hx : (⟨s, x⟩ : Σ s : S.Srt, Vinfinite S s) ∈ B
    · exact Or.inl ⟨⟨s, x⟩, hx, rfl⟩
    · exact absurd (by simp [boundarySwap_apply, swapHalvesFun, hx]) hv
  · by_cases hx : (⟨s, x⟩ : Σ s : S.Srt, Vinfinite S s) ∈ B
    · exact Or.inr ⟨⟨s, x⟩, hx, rfl⟩
    · exact absurd (by simp [boundarySwap_apply, swapHalvesFun, hx]) hv

omit [NeZero N] in
/-- Both copies of the slot-`m` block lie in the stage-`m` reservoir. -/
theorem bothHalves_subset_reservoir (m : ℕ) :
    bothHalves (pollBlock N D m) ⊆ reservoir N D m :=
  Set.subset_biUnion_of_mem (u := fun k => bothHalves (pollBlock N D k)) (Set.mem_Ici.mpr le_rfl)

omit [NeZero N] in
open scoped Classical in
/-- **The swap is supported inside the reservoir**: every vertex outside the stage-`m` reservoir
is fixed. This is the hypothesis of the exact stage-invariance theorem. -/
theorem boundarySwap_fix_of_notMem_reservoir (m : ℕ) :
    ∀ v : Σ s : S.Srt, PoolVertex S s, v ∉ reservoir N D m →
      boundarySwap (pollBlock N D m) v.1 v.2 = v.2 := by
  intro v hv
  by_contra hne
  exact hv (bothHalves_subset_reservoir N D m (mem_bothHalves_of_boundarySwap_ne _ v hne))

omit [NeZero N] in
open scoped Classical in
/-- **The target is fixed** by every boundary swap: an original vertex below the bound and outside
`D` lies in no poll block. -/
theorem boundarySwap_original_of_lt (m : ℕ) {w : Σ s : S.Srt, Vinfinite S s} (hw : w.2 < N)
    (hwD : w ∉ D) :
    boundarySwap (pollBlock N D m) w.1 (originalVertex S w.1 w.2) = originalVertex S w.1 w.2 := by
  show swapHalvesFun (pollBlock N D m) w.1 (Sum.inl w.2) = Sum.inl w.2
  simp [swapHalvesFun, notMem_pollBlock_of_lt N D hw hwD m]

open scoped Classical in
/-- **The swap carries the original copy of the block to the spare copy.** -/
theorem boundarySwap_original_of_mem (B : Finset (Σ s : S.Srt, Vinfinite S s))
    {w : Σ s : S.Srt, Vinfinite S s} (hw : w ∈ B) :
    boundarySwap (S := S) B w.1 (originalVertex S w.1 w.2) = poolVertex S w.1 w.2 := by
  show swapHalvesFun B w.1 (Sum.inl w.2) = Sum.inr w.2
  simp [swapHalvesFun, hw]

open scoped Classical in
/-- The swap has finite support on both halves and finitely many active sorts, so it conjugates
into the finite-active subgroup. -/
theorem pooledFiniteActive_boundarySwap (B : Finset (Σ s : S.Srt, Vinfinite S s)) :
    PooledFiniteActive (boundarySwap (S := S) B) := by
  refine ⟨⟨(B.sup fun v => v.2) + 1, fun s x hx => ?_⟩, ⟨B.image Sigma.fst, fun s hs => ?_⟩⟩
  · have hnot : (⟨s, x⟩ : Σ s : S.Srt, Vinfinite S s) ∉ B := fun h =>
      absurd (Nat.lt_succ_of_le (Finset.le_sup (f := fun v : Σ s : S.Srt, Vinfinite S s => v.2) h))
        (not_lt.mpr hx)
    constructor <;> simp [boundarySwap_apply, swapHalvesFun, hnot]
  · ext x
    have hnot : ∀ y : ℕ, (⟨s, y⟩ : Σ s : S.Srt, Vinfinite S s) ∉ B := fun y h =>
      hs (Finset.mem_image_of_mem Sigma.fst h)
    rcases x with x | x <;> simp [boundarySwap_apply, swapHalvesFun, hnot]

omit [NeZero N] in
/-- **The insertion geometry, packaged**: the boundary swap at slot `m` fixes the stage-`m`
reservoir's conditioning algebra exactly. -/
theorem comap_pooledJointRelabel_boundarySwap_reservoirFiltration (n m : ℕ) :
    MeasurableSpace.comap (pooledJointRelabel (boundarySwap (pollBlock N D m)) n)
        (reservoirFiltration N D n m) = reservoirFiltration N D n m :=
  comap_pooledJointRelabel_avoidAlgebra_of_fix (boundarySwap_fix_of_notMem_reservoir N D m)

end Reservoir

end RelSignature
