/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelAustinPolling

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

end RelSignature
