/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelPollingTail

/-!
# The refined polling conditioning `𝔅_fix` and its reservoir stages (R4 converse, #107, #197)

The unit-3 refinement of the polling conditioning: the pooled latents together with the **pooled
finite-active fixing algebras at every mixed support**, in place of the raw blocks there. The
insertion step of the fixing-factor polling argument needs it: a fixing event carried by a swap
onto a mixed support is a fixing event there, and the available interfaces do not represent the
transported fixing events through the raw polling base. The obstruction is a missing premise for
this proof, not a claim about every proof.

The existing Austin base is preserved; this is a separate, richer conditioning, and nothing here
claims that conditional independence given it descends to the raw base.

## Exact algebra transport, not factor realization

The stages are defined from the **full** pooled finite-active fixing algebras, and their transport
under the two motions is exact by conjugation
(`comap_relabel_pooledFiniteActiveFixingAlgebra`): a finite-active pooled permutation carries the
fixing algebra at `X` to the one at its image, and one fixing `X` pointwise fixes it. The
synchronous shift has infinite vertex support but finitely many active sorts, which is all
conjugation needs.
The countable factor realization of `Graphon.RelFiniteActiveBasis` is not used here; its
coordinate equivariance covers finitely supported permutations only, and its generation of the
fixing algebras is modulo the law.

## Contents

* `fixStage n W` — the refined stage avoiding `W`: latents at supports avoiding `W`, joined with
  the fixing algebras at mixed supports avoiding `W`; `fixBase n = fixStage n ∅`.
* `comap_pooledJointRelabel_fixStage` — exact transport under a half-preserving permutation with
  finitely many active sorts; `comap_pooledJointRelabel_fixStage_of_fix` — exact invariance
  under a finite-active permutation supported inside `W`.
* `iSup_fixStage` — the stages along an exhausting antitone sequence increase to `fixBase`.
* `fixReservoirFiltration` and its tail property `condExp_fixBase_eq_fixReservoirFiltration_zero`,
  by the same energy argument as the raw case.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace RelSignature

open InfiniteRelExchangeableLaw

universe u

variable {S : RelSignature.{u}} {n : ℕ}

/-! ### Transport of the pooled finite-active fixing algebra -/

open scoped Classical in
/-- The conjugate carries the identified support to the identified image. -/
theorem identifiedSupport_image (ρ : ∀ s, Equiv.Perm (PoolVertex S s))
    (X : Finset (Σ s : S.Srt, PoolVertex S s)) :
    (identifiedSupport X).image (Sigma.map id fun s => ⇑(conjPooled ρ s)) =
      identifiedSupport (X.image (Sigma.map id fun s => ⇑(ρ s))) := by
  ext v
  simp only [identifiedSupport, Finset.mem_image, mem_supportImage_iff]
  constructor
  · rintro ⟨u, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨Sigma.map id (fun s => ⇑(ρ s)) w, ⟨w, hw, rfl⟩, ?_⟩
    obtain ⟨s, x⟩ := w
    show (⟨s, poolVertexEquiv S s (ρ s x)⟩ : Σ s : S.Srt, Vinfinite S s) =
      ⟨s, poolVertexEquiv S s (ρ s ((poolVertexEquiv S s).symm (poolVertexEquiv S s x)))⟩
    rw [Equiv.symm_apply_apply]
  · rintro ⟨u, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨Sigma.map id (fun s => ⇑((poolVertexEquiv S s).toEmbedding)) w, ⟨w, hw, rfl⟩, ?_⟩
    obtain ⟨s, x⟩ := w
    show (⟨s, poolVertexEquiv S s (ρ s ((poolVertexEquiv S s).symm (poolVertexEquiv S s x)))⟩ :
      Σ s : S.Srt, Vinfinite S s) = ⟨s, poolVertexEquiv S s (ρ s x)⟩
    rw [Equiv.symm_apply_apply]

open scoped Classical in
/-- **Exact transport of the pooled finite-active fixing algebra** under a pooled permutation
with finitely many active sorts: the pullback along the relabeling is the fixing algebra at the
image support. By conjugation to the identified carrier. -/
theorem comap_relabel_pooledFiniteActiveFixingAlgebra {ρ : ∀ s, Equiv.Perm (PoolVertex S s)}
    (hρ : ∃ T : Finset S.Srt, ∀ s, s ∉ T → ρ s = 1) (X : Finset (Σ s : S.Srt, PoolVertex S s)) :
    MeasurableSpace.comap (RelStructure.relabel ρ) (pooledFiniteActiveFixingAlgebra X) =
      pooledFiniteActiveFixingAlgebra (X.image (Sigma.map id fun s => ⇑(ρ s))) := by
  have h1 : MeasurableSpace.comap (RelStructure.relabel ρ) (MeasurableSpace.comap
      (poolStructureEquiv S) (RelStructure.finiteActiveFixingAlgebra (identifiedSupport X))) =
      MeasurableSpace.comap (poolStructureEquiv S) (MeasurableSpace.comap
        (RelStructure.relabel (conjPooled ρ))
        (RelStructure.finiteActiveFixingAlgebra (identifiedSupport X))) := by
    rw [MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
    congr 1
    funext Y
    exact poolStructureEquiv_relabel ρ Y
  show MeasurableSpace.comap (RelStructure.relabel ρ) (MeasurableSpace.comap
      (poolStructureEquiv S) (RelStructure.finiteActiveFixingAlgebra (identifiedSupport X))) =
    MeasurableSpace.comap (poolStructureEquiv S) (RelStructure.finiteActiveFixingAlgebra
      (identifiedSupport (X.image (Sigma.map id fun s => ⇑(ρ s)))))
  rw [h1, RelStructure.finiteActiveFixingAlgebra_comap_relabel
    (sortwiseFiniteActive_conjPooled hρ), identifiedSupport_image]

/-! ### The refined stages -/

open scoped Classical in
/-- The latent half of a stage: pooled latents at supports avoiding `W`. -/
@[implicit_reducible]
noncomputable def latentStage (n : ℕ) (W : Set (Σ s : S.Srt, PoolVertex S s)) :
    MeasurableSpace (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) :=
  MeasurableSpace.comap (fun p => fun I : AvoidLatentIndex S n W => p.2 I.1) inferInstance

/-- Mixed rank-`n` supports avoiding `W`. -/
def MixedAvoiding (S : RelSignature.{u}) (n : ℕ) (W : Set (Σ s : S.Srt, PoolVertex S s)) :=
  {X : MixedClusterIndex S n // ∀ v ∈ X.1, v ∉ W}

open scoped Classical in
/-- The fixing half of a stage: the pooled finite-active fixing algebras at the mixed supports
avoiding `W`, pulled back through the structure coordinate. -/
@[implicit_reducible]
noncomputable def fixingStage (n : ℕ) (W : Set (Σ s : S.Srt, PoolVertex S s)) :
    MeasurableSpace (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) :=
  ⨆ X : MixedAvoiding S n W, MeasurableSpace.comap
    (Prod.fst : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → _)
    (pooledFiniteActiveFixingAlgebra X.1.1)

open scoped Classical in
/-- **The refined stage at `W`.** -/
@[implicit_reducible]
noncomputable def fixStage (n : ℕ) (W : Set (Σ s : S.Srt, PoolVertex S s)) :
    MeasurableSpace (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) :=
  latentStage n W ⊔ fixingStage n W

/-- **The refined polling conditioning `𝔅_fix`**: the stage at `∅`. -/
noncomputable abbrev fixBase (n : ℕ) :
    MeasurableSpace (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) :=
  fixStage n ∅

open scoped Classical in
theorem latentStage_le (W : Set (Σ s : S.Srt, PoolVertex S s)) :
    latentStage (S := S) n W ≤
      (inferInstance :
      MeasurableSpace (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) :=
  (measurable_pi_lambda _ fun _ => measurable_snd.eval).comap_le

open scoped Classical in
theorem pooledFiniteActiveFixingAlgebra_le (X : Finset (Σ s : S.Srt, PoolVertex S s)) :
    pooledFiniteActiveFixingAlgebra X ≤
      (inferInstance : MeasurableSpace (RelStructure S (PoolVertex S))) := by
  rw [pooledFiniteActiveFixingAlgebra]
  exact (MeasurableSpace.comap_mono (RelStructure.finiteActiveFixingAlgebra_le _)).trans
    (poolStructureEquiv S).measurable.comap_le

open scoped Classical in
theorem fixingStage_le (W : Set (Σ s : S.Srt, PoolVertex S s)) :
    fixingStage (S := S) n W ≤
      (inferInstance :
      MeasurableSpace (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) :=
  iSup_le fun X => (MeasurableSpace.comap_mono (pooledFiniteActiveFixingAlgebra_le X.1.1)).trans
    measurable_fst.comap_le

open scoped Classical in
theorem fixStage_le (W : Set (Σ s : S.Srt, PoolVertex S s)) :
    fixStage (S := S) n W ≤
      (inferInstance :
      MeasurableSpace (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) :=
  sup_le (latentStage_le W) (fixingStage_le W)

open scoped Classical in
theorem latentStage_mono {W W' : Set (Σ s : S.Srt, PoolVertex S s)} (h : W ⊆ W') :
    latentStage (S := S) n W' ≤ latentStage n W := by
  have hfac : (fun p : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n =>
      fun I : AvoidLatentIndex S n W' => p.2 I.1) =
      (fun x : AvoidLatentIndex S n W → ℝ => fun I : AvoidLatentIndex S n W' =>
        x ⟨I.1, fun v hv hvW => I.2 v hv (h hvW)⟩) ∘
        fun p => fun I : AvoidLatentIndex S n W => p.2 I.1 := rfl
  rw [latentStage, hfac, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_lambda _ fun _ => measurable_pi_apply _).comap_le

open scoped Classical in
theorem fixingStage_mono {W W' : Set (Σ s : S.Srt, PoolVertex S s)} (h : W ⊆ W') :
    fixingStage (S := S) n W' ≤ fixingStage n W :=
  iSup_le fun X => le_iSup (fun X : MixedAvoiding S n W => MeasurableSpace.comap
    (Prod.fst : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → _)
    (pooledFiniteActiveFixingAlgebra X.1.1)) ⟨X.1, fun v hv hvW => X.2 v hv (h hvW)⟩

open scoped Classical in
theorem fixStage_mono {W W' : Set (Σ s : S.Srt, PoolVertex S s)} (h : W ⊆ W') :
    fixStage (S := S) n W' ≤ fixStage n W :=
  sup_le_sup (latentStage_mono h) (fixingStage_mono h)

/-! ### Exact transport -/

open scoped Classical in
/-- The latent half transports exactly under any pooled permutation. -/
theorem comap_pooledJointRelabel_latentStage (ρ : ∀ s, Equiv.Perm (PoolVertex S s))
    (W : Set (Σ s : S.Srt, PoolVertex S s)) :
    MeasurableSpace.comap (pooledJointRelabel ρ n) (latentStage (S := S) n W) =
      latentStage n (imageSet ρ W) := by
  have hinj : Function.Injective (Sigma.map id fun s => ⇑(ρ s) :
      (Σ s : S.Srt, PoolVertex S s) → Σ s : S.Srt, PoolVertex S s) :=
    Function.injective_id.sigma_map fun s => (ρ s).injective
  -- the moved index avoids the moved set, and conversely
  have hfwd : ∀ I : AvoidLatentIndex S n W, ∀ v ∈ (latentIndexPerm ρ n I.1).1,
      v ∉ imageSet ρ W := by
    intro I v hv hvW
    rw [latentIndexPerm_apply_coe] at hv
    simp only [Finset.mem_image] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨u, hu, hu'⟩ := hvW
    exact I.2 w hw (hinj hu' ▸ hu)
  have hbwd : ∀ I : AvoidLatentIndex S n (imageSet ρ W),
      ∀ v ∈ (latentIndexPerm (fun s => (ρ s)⁻¹) n I.1).1, v ∉ W := by
    intro I v hv hvW
    rw [latentIndexPerm_apply_coe] at hv
    simp only [Finset.mem_image] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    refine I.2 w hw ⟨_, hvW, ?_⟩
    obtain ⟨s, x⟩ := w
    show (⟨s, ρ s ((ρ s)⁻¹ x)⟩ : Σ s : S.Srt, PoolVertex S s) = ⟨s, x⟩
    rw [show ρ s ((ρ s)⁻¹ x) = x from (ρ s).apply_symm_apply x]
  refine le_antisymm ?_ ?_
  · have hfac : (fun p : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n =>
        fun I : AvoidLatentIndex S n W => p.2 I.1) ∘ pooledJointRelabel ρ n =
        (fun x : AvoidLatentIndex S n (imageSet ρ W) → ℝ => fun I : AvoidLatentIndex S n W =>
          x ⟨latentIndexPerm ρ n I.1, hfwd I⟩) ∘
          fun p => fun I : AvoidLatentIndex S n (imageSet ρ W) => p.2 I.1 := rfl
    simp only [latentStage]
    rw [MeasurableSpace.comap_comp, hfac, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono
      (measurable_pi_lambda _ fun _ => measurable_pi_apply _).comap_le
  · have hfac : (fun p : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n =>
        fun I : AvoidLatentIndex S n (imageSet ρ W) => p.2 I.1) =
        (fun x : AvoidLatentIndex S n W → ℝ => fun I : AvoidLatentIndex S n (imageSet ρ W) =>
          x ⟨latentIndexPerm (fun s => (ρ s)⁻¹) n I.1, hbwd I⟩) ∘
          ((fun p : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n =>
            fun I : AvoidLatentIndex S n W => p.2 I.1) ∘ pooledJointRelabel ρ n) := by
      funext p I
      show p.2 I.1 = p.2 (latentIndexPerm ρ n (latentIndexPerm (fun s => (ρ s)⁻¹) n I.1))
      rw [show latentIndexPerm ρ n (latentIndexPerm (fun s => (ρ s)⁻¹) n I.1) = I.1 from
        Subtype.ext (by
          rw [latentIndexPerm_apply_coe, latentIndexPerm_apply_coe]
          ext v
          simp only [Finset.mem_image]
          constructor
          · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
            obtain ⟨s, x⟩ := u
            show (⟨s, ρ s ((ρ s)⁻¹ x)⟩ : Σ s : S.Srt, PoolVertex S s) ∈ I.1.1
            rw [show ρ s ((ρ s)⁻¹ x) = x from (ρ s).apply_symm_apply x]
            exact hu
          · intro hv
            refine ⟨Sigma.map id (fun s => ⇑(ρ s)⁻¹) v, ⟨v, hv, rfl⟩, ?_⟩
            obtain ⟨s, x⟩ := v
            show (⟨s, ρ s ((ρ s)⁻¹ x)⟩ : Σ s : S.Srt, PoolVertex S s) = ⟨s, x⟩
            rw [show ρ s ((ρ s)⁻¹ x) = x from (ρ s).apply_symm_apply x])]
    simp only [latentStage]
    rw [hfac, ← MeasurableSpace.comap_comp, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (MeasurableSpace.comap_mono
      (measurable_pi_lambda _ fun _ => measurable_pi_apply _).comap_le)

open scoped Classical in
/-- The fixing half transports exactly under a half-preserving permutation with finitely many
active sorts: mixedness is preserved, and each fixing algebra moves by conjugation. -/
theorem comap_pooledJointRelabel_fixingStage {ρ : ∀ s, Equiv.Perm (PoolVertex S s)}
    (hρ : HalfPreserving ρ) (hρfin : ∃ T : Finset S.Srt, ∀ s, s ∉ T → ρ s = 1)
    (W : Set (Σ s : S.Srt, PoolVertex S s)) :
    MeasurableSpace.comap (pooledJointRelabel ρ n) (fixingStage (S := S) n W) =
      fixingStage n (imageSet ρ W) := by
  have hinj : Function.Injective (Sigma.map id fun s => ⇑(ρ s) :
      (Σ s : S.Srt, PoolVertex S s) → Σ s : S.Srt, PoolVertex S s) :=
    Function.injective_id.sigma_map fun s => (ρ s).injective
  have hinv : ∀ s x, ρ s ((ρ s)⁻¹ x) = x := fun s x => (ρ s).apply_symm_apply x
  -- each generator pulls back to the generator at the moved support
  have hgen : ∀ X : Finset (Σ s : S.Srt, PoolVertex S s),
      MeasurableSpace.comap (pooledJointRelabel ρ n) (MeasurableSpace.comap
        (Prod.fst : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → _)
        (pooledFiniteActiveFixingAlgebra X)) =
      MeasurableSpace.comap
        (Prod.fst : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → _)
        (pooledFiniteActiveFixingAlgebra (X.image (Sigma.map id fun s => ⇑(ρ s)))) := by
    intro X
    rw [MeasurableSpace.comap_comp, show (Prod.fst ∘ pooledJointRelabel ρ n :
        RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → RelStructure S (PoolVertex S)) =
        RelStructure.relabel ρ ∘ Prod.fst from rfl,
      ← MeasurableSpace.comap_comp, comap_relabel_pooledFiniteActiveFixingAlgebra hρfin]
  -- the moved support of a mixed support avoiding `W` is mixed and avoids the image of `W`
  have hmoved : ∀ X : MixedAvoiding S n W,
      (X.1.1.image (Sigma.map id fun s => ⇑(ρ s))).card = n ∧
        (∃ v ∈ X.1.1.image (Sigma.map id fun s => ⇑(ρ s)), Sum.isRight v.2) ∧
        ∀ v ∈ X.1.1.image (Sigma.map id fun s => ⇑(ρ s)), v ∉ imageSet ρ W := by
    intro X
    refine ⟨by rw [Finset.card_image_of_injective _ hinj]; exact X.1.2.1, ?_, ?_⟩
    · obtain ⟨v, hv, hvr⟩ := X.1.2.2
      refine ⟨Sigma.map id (fun s => ⇑(ρ s)) v, Finset.mem_image_of_mem _ hv, ?_⟩
      show Sum.isRight (ρ v.1 v.2) = true
      rw [hρ]; exact hvr
    · intro v hv hvW
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨u, hu, hu'⟩ := hvW
      exact X.2 w hw (hinj hu' ▸ hu)
  have hback : ∀ Y : MixedAvoiding S n (imageSet ρ W),
      (Y.1.1.image (Sigma.map id fun s => ⇑(ρ s)⁻¹)).card = n ∧
        (∃ v ∈ Y.1.1.image (Sigma.map id fun s => ⇑(ρ s)⁻¹), Sum.isRight v.2) ∧
        ∀ v ∈ Y.1.1.image (Sigma.map id fun s => ⇑(ρ s)⁻¹), v ∉ W := by
    intro Y
    have hinj' : Function.Injective (Sigma.map id fun s => ⇑(ρ s)⁻¹ :
        (Σ s : S.Srt, PoolVertex S s) → Σ s : S.Srt, PoolVertex S s) :=
      Function.injective_id.sigma_map fun s => (ρ s)⁻¹.injective
    refine ⟨by rw [Finset.card_image_of_injective _ hinj']; exact Y.1.2.1, ?_, ?_⟩
    · obtain ⟨v, hv, hvr⟩ := Y.1.2.2
      refine ⟨Sigma.map id (fun s => ⇑(ρ s)⁻¹) v, Finset.mem_image_of_mem _ hv, ?_⟩
      show Sum.isRight ((ρ v.1)⁻¹ v.2) = true
      rw [hρ.inv]; exact hvr
    · intro v hv hvW
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      refine Y.2 w hw ⟨_, hvW, ?_⟩
      obtain ⟨s, x⟩ := w
      show (⟨s, ρ s ((ρ s)⁻¹ x)⟩ : Σ s : S.Srt, PoolVertex S s) = ⟨s, x⟩
      rw [hinv]
  have himg : ∀ Y : MixedAvoiding S n (imageSet ρ W),
      (Y.1.1.image (Sigma.map id fun s => ⇑(ρ s)⁻¹)).image (Sigma.map id fun s => ⇑(ρ s)) =
        Y.1.1 := by
    intro Y
    rw [Finset.image_image]
    refine (Finset.image_congr fun v _ => ?_).trans Y.1.1.image_id
    obtain ⟨s, x⟩ := v
    show (⟨s, ρ s ((ρ s)⁻¹ x)⟩ : Σ s : S.Srt, PoolVertex S s) = ⟨s, x⟩
    rw [hinv]
  rw [fixingStage, MeasurableSpace.comap_iSup]
  simp_rw [hgen]
  refine le_antisymm (iSup_le fun X => ?_) (iSup_le fun Y => ?_)
  · exact le_iSup (fun Y : MixedAvoiding S n (imageSet ρ W) => MeasurableSpace.comap
      (Prod.fst : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → _)
      (pooledFiniteActiveFixingAlgebra Y.1.1)) ⟨⟨_, (hmoved X).1, (hmoved X).2.1⟩, (hmoved X).2.2⟩
  · refine le_trans ?_ (le_iSup (fun X : MixedAvoiding S n W => MeasurableSpace.comap
      (Prod.fst : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → _)
      (pooledFiniteActiveFixingAlgebra (X.1.1.image (Sigma.map id fun s => ⇑(ρ s)))))
      ⟨⟨_, (hback Y).1, (hback Y).2.1⟩, (hback Y).2.2⟩)
    rw [show ((⟨⟨_, (hback Y).1, (hback Y).2.1⟩, (hback Y).2.2⟩ : MixedAvoiding S n W)).1.1.image
      (Sigma.map id fun s => ⇑(ρ s)) = Y.1.1 from himg Y]

open scoped Classical in
/-- **Exact transport of the refined stage** under a half-preserving permutation with finitely
many active sorts. -/
theorem comap_pooledJointRelabel_fixStage {ρ : ∀ s, Equiv.Perm (PoolVertex S s)}
    (hρ : HalfPreserving ρ) (hρfin : ∃ T : Finset S.Srt, ∀ s, s ∉ T → ρ s = 1)
    (W : Set (Σ s : S.Srt, PoolVertex S s)) :
    MeasurableSpace.comap (pooledJointRelabel ρ n) (fixStage (S := S) n W) =
      fixStage n (imageSet ρ W) := by
  rw [fixStage, fixStage, MeasurableSpace.comap_sup, comap_pooledJointRelabel_latentStage,
    comap_pooledJointRelabel_fixingStage hρ hρfin]

open scoped Classical in
/-- **Exact invariance of the refined stage** under a permutation with finitely many active sorts
supported inside `W`: every latent coordinate it reads is fixed, and every fixing algebra it
reads is at a support fixed pointwise, hence fixed by conjugation. -/
theorem comap_pooledJointRelabel_fixStage_of_fix {ρ : ∀ s, Equiv.Perm (PoolVertex S s)}
    (hρfin : ∃ T : Finset S.Srt, ∀ s, s ∉ T → ρ s = 1) {W : Set (Σ s : S.Srt, PoolVertex S s)}
    (hρ : ∀ v : Σ s : S.Srt, PoolVertex S s, v ∉ W → ρ v.1 v.2 = v.2) :
    MeasurableSpace.comap (pooledJointRelabel ρ n) (fixStage (S := S) n W) = fixStage n W := by
  have hfixI : ∀ I : AvoidLatentIndex S n W, latentIndexPerm ρ n I.1 = I.1 := by
    intro I
    have hfixw : ∀ w ∈ I.1.1, Sigma.map id (fun s => ⇑(ρ s)) w = w := by
      intro w hw
      obtain ⟨s, x⟩ := w
      show (⟨s, ρ s x⟩ : Σ s : S.Srt, PoolVertex S s) = ⟨s, x⟩
      rw [hρ ⟨s, x⟩ (I.2 _ hw)]
    refine Subtype.ext ?_
    rw [latentIndexPerm_apply_coe]
    ext v
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hfixw w hw]
      exact hw
    · intro hv
      exact ⟨v, hv, hfixw v hv⟩
  have hfixX : ∀ X : MixedAvoiding S n W, X.1.1.image (Sigma.map id fun s => ⇑(ρ s)) = X.1.1 := by
    intro X
    refine (Finset.image_congr fun v hv => ?_).trans X.1.1.image_id
    obtain ⟨s, x⟩ := v
    show (⟨s, ρ s x⟩ : Σ s : S.Srt, PoolVertex S s) = ⟨s, x⟩
    rw [hρ ⟨s, x⟩ (X.2 _ hv)]
  rw [fixStage, MeasurableSpace.comap_sup]
  congr 1
  · have hfix : (fun p : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n =>
        fun I : AvoidLatentIndex S n W => p.2 I.1) ∘ pooledJointRelabel ρ n =
        fun p => fun I : AvoidLatentIndex S n W => p.2 I.1 := by
      funext p I
      show p.2 (latentIndexPerm ρ n I.1) = p.2 I.1
      rw [hfixI I]
    rw [latentStage, MeasurableSpace.comap_comp, hfix]
  · rw [fixingStage, MeasurableSpace.comap_iSup]
    refine iSup_congr fun X => ?_
    rw [MeasurableSpace.comap_comp, show (Prod.fst ∘ pooledJointRelabel ρ n :
        RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → RelStructure S (PoolVertex S)) =
        RelStructure.relabel ρ ∘ Prod.fst from rfl,
      ← MeasurableSpace.comap_comp, comap_relabel_pooledFiniteActiveFixingAlgebra hρfin, hfixX X]

/-! ### The supremum -/

open scoped Classical in
/-- **The refined stages increase to `𝔅_fix`** along an exhausting antitone sequence: every
generator — a latent coordinate, or the fixing algebra at a mixed support — is read by some
stage. -/
theorem iSup_fixStage (W : ℕ → Set (Σ s : S.Srt, PoolVertex S s))
    (hev : ∀ F : Finset (Σ s : S.Srt, PoolVertex S s), ∃ m, ∀ v ∈ F, v ∉ W m) :
    (⨆ m, fixStage (S := S) n (W m)) = fixBase n := by
  refine le_antisymm (iSup_le fun m => fixStage_mono (Set.empty_subset _)) (sup_le ?_ ?_)
  · rw [latentStage, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun I => ?_
    obtain ⟨m, hm⟩ := hev I.1.1
    refine le_trans ?_ (le_trans le_sup_left (le_iSup (fun m => fixStage (S := S) n (W m)) m))
    rw [MeasurableSpace.comap_comp, latentStage]
    have hfac : ((fun x : AvoidLatentIndex S n ∅ → ℝ => x I) ∘
        fun p : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n =>
          fun I : AvoidLatentIndex S n ∅ => p.2 I.1) =
        (fun x : AvoidLatentIndex S n (W m) → ℝ => x ⟨I.1, hm⟩) ∘
          fun p => fun I : AvoidLatentIndex S n (W m) => p.2 I.1 := rfl
    rw [hfac, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le
  · refine iSup_le fun X => ?_
    obtain ⟨m, hm⟩ := hev X.1.1
    exact le_trans (le_iSup (fun X : MixedAvoiding S n (W m) => MeasurableSpace.comap
      (Prod.fst : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → _)
      (pooledFiniteActiveFixingAlgebra X.1.1)) ⟨X.1, hm⟩)
      (le_trans le_sup_right (le_iSup (fun m => fixStage (S := S) n (W m)) m))

/-! ### The reservoir filtration and its tail property -/

section Tail

variable (N : ℕ) [NeZero N] (D : Finset (Σ s : S.Srt, Vinfinite S s))

/-- **The refined reservoir filtration**: the refined stages avoiding the reservoirs. -/
noncomputable def fixReservoirFiltration (n : ℕ) : Filtration ℕ
    (inferInstance : MeasurableSpace (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))
    where
  seq m := fixStage n (reservoir N D m)
  mono' := fun _ _ h => fixStage_mono (reservoir_antitone N D h)
  le' := fun _ => fixStage_le _

omit [NeZero N] in
theorem fixReservoirFiltration_apply (n m : ℕ) :
    fixReservoirFiltration (S := S) N D n m = fixStage n (reservoir N D m) := rfl

theorem iSup_fixReservoirFiltration (n : ℕ) :
    (⨆ m, fixReservoirFiltration (S := S) N D n m) = fixBase n :=
  iSup_fixStage (reservoir N D) (exists_reservoir_disjoint N D)

/-- Adjacent refined stages under the inverse synchronous shift. -/
theorem comap_inverseShift_fixReservoirFiltration (hD : ∀ v ∈ D, v.2 < N) (n m : ℕ) :
    MeasurableSpace.comap (inverseShift N D n) (fixReservoirFiltration N D n (m + 1)) =
      fixReservoirFiltration N D n m := by
  rw [fixReservoirFiltration_apply, fixReservoirFiltration_apply, inverseShift,
    comap_pooledJointRelabel_fixStage (halfPreserving_pooledPollPerm N D).inv
      (inverseShift_eq_one N D), imageSet_pooledPollPerm_inv_reservoir N D hD m]

variable [Countable S.Srt] [Countable S.Rel] {M : InfiniteRelExchangeableLaw S}
  {C : M.RankRepresentation n}

/-- Adjacent refined stages agree, for a fixing event of the target. -/
theorem condExp_fixReservoirFiltration_succ (Q : PooledRankExtension C) (hD : ∀ v ∈ D, v.2 < N)
    {A : Finset (Σ s : S.Srt, Vinfinite S s)} (hA : ∀ v ∈ A, v.2 < N) (hAD : ∀ v ∈ A, v ∉ D)
    {E : Set (RelStructure S (PoolVertex S))}
    (hE : MeasurableSet[pooledFiniteActiveFixingAlgebra (supportImage (originalVertex S) A)] E)
    (m : ℕ) :
    ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        Prod.fst ⁻¹' E | fixReservoirFiltration N D n (m + 1)⟧)
      =ᵐ[(Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))]
    ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        Prod.fst ⁻¹' E | fixReservoirFiltration N D n m⟧) := by
  haveI := C.isProbabilityMeasure_P
  obtain ⟨E₀, hE₀, hEeq⟩ := hE
  have hEmeas : MeasurableSet E := by
    rw [← hEeq]; exact (poolStructureEquiv S).measurable (hE₀.1)
  refine condExp_ae_eq_condExp_of_comap_eq (measurable_pooledJointRelabel _ n)
    (measurePreserving_inverseShift Q N D) ((fixReservoirFiltration N D n).le (m + 1))
    ((fixReservoirFiltration N D n).mono (Nat.le_succ m))
    (comap_inverseShift_fixReservoirFiltration N D hD n m)
    (memLp_indicator_const 2 (measurable_fst hEmeas) 1 (Or.inr (measure_ne_top _ _))) ?_
  have hfix : ∀ v ∈ supportImage (originalVertex S) A,
      (pooledPollPerm (S := S) N D v.1)⁻¹ v.2 = v.2 := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := (mem_supportImage_iff _ _ _).mp hv
    exact pooledPollPerm_inv_original_of_lt N D (hA w hw) (hAD w hw)
  have hinv := Q.relabel_preimage_ae_eq_of_pooledFiniteActiveFixingAlgebra_fst ⟨E₀, hE₀, hEeq⟩
    (inverseShift_eq_one N D) hfix
  exact indicator_ae_eq_of_ae_eq_set hinv

theorem condExp_fixReservoirFiltration_eq_zero (Q : PooledRankExtension C)
    (hD : ∀ v ∈ D, v.2 < N) {A : Finset (Σ s : S.Srt, Vinfinite S s)} (hA : ∀ v ∈ A, v.2 < N)
    (hAD : ∀ v ∈ A, v ∉ D) {E : Set (RelStructure S (PoolVertex S))}
    (hE : MeasurableSet[pooledFiniteActiveFixingAlgebra (supportImage (originalVertex S) A)] E)
    (m : ℕ) :
    ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        Prod.fst ⁻¹' E | fixReservoirFiltration N D n m⟧)
      =ᵐ[(Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))]
    ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        Prod.fst ⁻¹' E | fixReservoirFiltration N D n 0⟧) := by
  induction m with
  | zero => exact EventuallyEq.refl _ _
  | succ k ih => exact (condExp_fixReservoirFiltration_succ N D Q hD hA hAD hE k).trans ih

/-- **The refined tail property**: conditioning on `𝔅_fix` is conditioning on the refined stage
avoiding the whole reservoir. -/
theorem condExp_fixBase_eq_fixReservoirFiltration_zero (Q : PooledRankExtension C)
    (hD : ∀ v ∈ D, v.2 < N) {A : Finset (Σ s : S.Srt, Vinfinite S s)} (hA : ∀ v ∈ A, v.2 < N)
    (hAD : ∀ v ∈ A, v ∉ D) {E : Set (RelStructure S (PoolVertex S))}
    (hE : MeasurableSet[pooledFiniteActiveFixingAlgebra (supportImage (originalVertex S) A)] E) :
    ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        Prod.fst ⁻¹' E | fixBase n⟧)
      =ᵐ[(Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))]
    ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))⟦
        Prod.fst ⁻¹' E | fixReservoirFiltration N D n 0⟧) := by
  haveI := C.isProbabilityMeasure_P
  set μ : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) :=
    (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) with hμ
  set ℱ := fixReservoirFiltration (S := S) N D n with hℱ
  set f : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → ℝ :=
    (Prod.fst ⁻¹' E).indicator fun _ => (1 : ℝ) with hf
  have hlevy : ∀ᵐ x ∂μ, Tendsto (fun m => (μ[f | ℱ m]) x) atTop (𝓝 ((μ[f | ⨆ m, ℱ m]) x)) :=
    tendsto_ae_condExp f
  have hconst : ∀ᵐ x ∂μ, ∀ m, (μ[f | ℱ m]) x = (μ[f | ℱ 0]) x :=
    ae_all_iff.mpr fun m => condExp_fixReservoirFiltration_eq_zero N D Q hD hA hAD hE m
  rw [← iSup_fixReservoirFiltration N D n]
  filter_upwards [hlevy, hconst] with x hx hcx
  have hx' : Tendsto (fun m => (μ[f | ℱ m]) x) atTop (𝓝 ((μ[f | ℱ 0]) x)) := by
    rw [show (fun m => (μ[f | ℱ m]) x) = fun _ => (μ[f | ℱ 0]) x from funext fun m => hcx m]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hx hx'

end Tail

end RelSignature
