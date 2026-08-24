/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelLatentGeometry
import Graphon.RelEqualityPattern

/-!
# Carrier-parametric observation layer (R4 converse, #107)

The observations used by recovery and screening — local latents, blocks of raw relation
coordinates, and the rank-truncated remainder — over an **arbitrary sortwise carrier**. The
`Vinfinite`-indexed originals become compatibility aliases, and the pooled statements instantiate
this core rather than introducing parallel pooled definitions.

## The transport boundary

The three observations do **not** transport equally well, and the difference is a matter of truth,
not of proof effort:

* `localLatentsOver` and `blockMapOver` are **local** — they read only coordinates supported inside
  a given finite set — so they admit naturality along an arbitrary sortwise **embedding** of
  carriers: an embedding restricts to a bijection between the supports inside `A` and those inside
  its image.
* `restObservationOver` is **global**: its remainder ranges over *every* rank-`≤ n` coordinate of
  the ambient carrier other than the one at `A`. Along an embedding into a larger carrier the
  target remainder sees coordinates outside the image, which the source remainder cannot, so an
  embedding-level commuting law would be **false**. It transports only along a carrier
  **equivalence**.

Screening therefore transports along the canonical `poolVertexEquiv`, which the pooled uniqueness
identity makes available; recovery, being local, is free to use embeddings.
-/

open MeasureTheory

namespace RelSignature

universe u v

variable {S : RelSignature.{u}} {V W : S.Srt → Type v}

/-! ### Local latents -/

/-- The latent coordinates visible at `A`: supports contained in `A`. -/
def LocalLatentIndexOver (V : S.Srt → Type v) (A : Finset (Σ s : S.Srt, V s)) (n : ℕ) :=
  {B : LatentIndexOver S V n // B.1 ⊆ A}

instance [Countable S.Srt] [∀ s, Countable (V s)] (A : Finset (Σ s : S.Srt, V s)) (n : ℕ) :
    Countable (LocalLatentIndexOver V A n) := Subtype.countable

/-- The local latent space at `A`. -/
abbrev LocalLatentSpaceOver (V : S.Srt → Type v) (A : Finset (Σ s : S.Srt, V s)) (n : ℕ) :=
  LocalLatentIndexOver V A n → ℝ

/-- Restriction of the latent array to the coordinates visible at `A`. -/
def localLatentsOver (A : Finset (Σ s : S.Srt, V s)) (n : ℕ) :
    LatentSpaceOver S V n → LocalLatentSpaceOver V A n := fun ω B => ω B.1

theorem measurable_localLatentsOver (A : Finset (Σ s : S.Srt, V s)) (n : ℕ) :
    Measurable (localLatentsOver (S := S) A n) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-! ### Blocks of raw relation coordinates -/

open scoped Classical in
/-- Raw relation coordinates whose tagged support is exactly `A`. -/
def BlockIndexOver (V : S.Srt → Type v) (A : Finset (Σ s : S.Srt, V s)) :=
  {c : RelCoord S V // c.support = A}

open scoped Classical in
instance [Countable S.Rel] [∀ s, Countable (V s)] (A : Finset (Σ s : S.Srt, V s)) :
    Countable (BlockIndexOver V A) := Subtype.countable

open scoped Classical in
/-- The block of the structure at `A`. -/
abbrev BlockSpaceOver (V : S.Srt → Type v) (A : Finset (Σ s : S.Srt, V s)) :=
  BlockIndexOver V A → Bool

open scoped Classical in
/-- Read the block at `A` off a structure. -/
def blockMapOver (A : Finset (Σ s : S.Srt, V s)) :
    RelStructure S V → BlockSpaceOver V A := fun X c => X c.1

open scoped Classical in
theorem measurable_blockMapOver [Countable S.Rel] [∀ s, Countable (V s)]
    (A : Finset (Σ s : S.Srt, V s)) :
    Measurable (blockMapOver (S := S) A) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-! ### The rank-truncated remainder

Global, hence transportable only along carrier equivalences — see the module header. -/

open scoped Classical in
/-- Coordinates of rank at most `n` other than those at `A`. -/
def RestIndexOver (V : S.Srt → Type v) (n : ℕ) (A : Finset (Σ s : S.Srt, V s)) :=
  {c : RelCoord S V // c.support.card ≤ n ∧ c.support ≠ A}

open scoped Classical in
instance [Countable S.Rel] [∀ s, Countable (V s)] (n : ℕ) (A : Finset (Σ s : S.Srt, V s)) :
    Countable (RestIndexOver V n A) := Subtype.countable

open scoped Classical in
/-- The remaining rank-`≤ n` structure. -/
abbrev RestSpaceOver (V : S.Srt → Type v) (n : ℕ) (A : Finset (Σ s : S.Srt, V s)) :=
  RestIndexOver V n A → Bool

open scoped Classical in
/-- **The rank-truncated remainder observation** over a carrier: the other blocks of rank at most
`n`, together with the whole latent array. -/
def restObservationOver (n : ℕ) (A : Finset (Σ s : S.Srt, V s)) :
    RelStructure S V × LatentSpaceOver S V n →
      RestSpaceOver V n A × LatentSpaceOver S V n :=
  fun p => (fun c => p.1 c.1, p.2)

open scoped Classical in
theorem measurable_restObservationOver [Countable S.Rel] [∀ s, Countable (V s)] (n : ℕ)
    (A : Finset (Σ s : S.Srt, V s)) :
    Measurable (restObservationOver (S := S) n A) :=
  (measurable_pi_lambda _ fun _ => measurable_fst.eval).prodMk measurable_snd

/-! ### Reindexing does not move the conditioning algebra

Screening conditions on a σ-algebra generated by an observation map. Transporting the observation
through a measurable *equivalence* of codomains leaves that σ-algebra unchanged — measurability in
both directions is exactly what makes the comap survive. Named here so the screening assembly can
straighten a transported conditioning map without a further probabilistic lemma. -/

/-- **Postcomposition with a measurable equivalence does not change the generated σ-algebra.** -/
theorem comap_measurableEquiv_comp {Ω α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (φ : α ≃ᵐ β) (f : Ω → α) :
    MeasurableSpace.comap (⇑φ ∘ f) inferInstance = MeasurableSpace.comap f inferInstance := by
  rw [← MeasurableSpace.comap_comp, φ.measurableEmbedding.comap_eq]

/-! ### Coordinate transport along a carrier equivalence

The coordinate mirror of `RelStructure.congrCarrier`, bundled once here: the remainder index is
global, so its transport needs a genuine equivalence of coordinates rather than an embedding. -/

/-- **Transport of relation coordinates along a sortwise equivalence of carriers**, bundled. -/
def RelCoord.congrCarrier (e : ∀ s, V s ≃ W s) : RelCoord S V ≃ RelCoord S W where
  toFun := RelCoord.map fun s => ⇑(e s)
  invFun := RelCoord.map fun s => ⇑(e s).symm
  left_inv c := by
    refine congrArg (fun w => (⟨c.1, w⟩ : RelCoord S V)) (funext fun i => ?_)
    exact (e _).symm_apply_apply (c.2 i)
  right_inv c := by
    refine congrArg (fun w => (⟨c.1, w⟩ : RelCoord S W)) (funext fun i => ?_)
    exact (e _).apply_symm_apply (c.2 i)

@[simp] theorem RelCoord.congrCarrier_apply (e : ∀ s, V s ≃ W s) (c : RelCoord S V) :
    RelCoord.congrCarrier e c = RelCoord.map (fun s => ⇑(e s)) c := rfl

@[simp] theorem RelCoord.congrCarrier_symm_apply (e : ∀ s, V s ≃ W s) (c : RelCoord S W) :
    (RelCoord.congrCarrier e).symm c = RelCoord.map (fun s => ⇑(e s).symm) c := rfl

/-! ### Support and index transport

Equivalences first, with pointwise `_apply` lemmas; the function-level naturality laws are derived
from these. Keeping the bijections primitive is what limits coercion and `DecidableEq` friction. -/

open scoped Classical in
/-- The image of a support under a sortwise embedding of carriers. -/
noncomputable def supportImage (e : ∀ s, V s ↪ W s) (A : Finset (Σ s : S.Srt, V s)) :
    Finset (Σ s : S.Srt, W s) :=
  A.image (Sigma.map id fun s => ⇑(e s))

open scoped Classical in
/-- **Membership in a support image**, stated without an image in the type so that no `DecidableEq`
instance appears in it. Over a carrier with a natural instance — `PoolVertex`, whose `Sum` gives
one — that instance is not definitionally the classical one used to form the image, which makes
image-shaped rewriting unusable there; this form is not. -/
theorem mem_supportImage_iff (e : ∀ s, V s ↪ W s) (A : Finset (Σ s : S.Srt, V s))
    (v : Σ s : S.Srt, W s) :
    v ∈ supportImage e A ↔ ∃ w ∈ A, Sigma.map id (fun s => ⇑(e s)) w = v :=
  Finset.mem_image

theorem injective_sigmaMap (e : ∀ s, V s ↪ W s) :
    Function.Injective (Sigma.map id fun s => ⇑(e s) : (Σ s : S.Srt, V s) → Σ s : S.Srt, W s) :=
  Function.injective_id.sigma_map fun s => (e s).injective

open scoped Classical in
theorem supportImage_injective (e : ∀ s, V s ↪ W s) :
    Function.Injective (supportImage (S := S) e) :=
  fun _ _ h => Finset.image_injective (injective_sigmaMap e) h

open scoped Classical in
/-- The image of a coordinate's support is the support of the transported coordinate. -/
theorem supportImage_support (e : ∀ s, V s ↪ W s) (d : RelCoord S V) :
    supportImage e d.support = (RelCoord.map (fun s => ⇑(e s)) d).support :=
  (RelCoord.support_map _ d).symm

open scoped Classical in
@[simp] theorem mem_supportImage_map {e : ∀ s, V s ↪ W s} {A : Finset (Σ s : S.Srt, V s)}
    {v : Σ s : S.Srt, V s} :
    Sigma.map id (fun s => ⇑(e s)) v ∈ supportImage e A ↔ v ∈ A :=
  (injective_sigmaMap e).mem_finset_image

open scoped Classical in
/-- **A support lies inside `A` exactly when its image lies inside the image of `A`.** This is the
bijection underlying local naturality: an embedding restricts to a bijection between the supports
inside `A` and those inside its image. -/
theorem latentIndexEmbed_subset_supportImage_iff (e : ∀ s, V s ↪ W s)
    {A : Finset (Σ s : S.Srt, V s)} {n : ℕ} (B : LatentIndexOver S V n) :
    (latentIndexEmbed e n B).1 ⊆ supportImage e A ↔ B.1 ⊆ A := by
  classical
  rw [latentIndexEmbed_coe, supportImage]
  constructor
  · intro h v hv
    have hmem := h (Finset.mem_image_of_mem (Sigma.map id fun s => ⇑(e s)) hv)
    rwa [(injective_sigmaMap e).mem_finset_image] at hmem
  · intro h w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_image_of_mem _ (h hv)

open scoped Classical in
/-- Transporting a coordinate carries its support to the image of that support. -/
theorem RelCoord.support_congrCarrier (e : ∀ s, V s ≃ W s) (c : RelCoord S V) :
    (RelCoord.congrCarrier e c).support =
      supportImage (fun s => (e s).toEmbedding) c.support := by
  rw [RelCoord.congrCarrier_apply, RelCoord.support_map, supportImage]
  rfl

/-! ### Local latents transport along an embedding

Index equivalence, then the space-level measurable equivalence, then the pointwise lemma, then the
exact naturality theorem against `localLatentsOver`. The inverse needs no `Finset.preimage`:
a support inside the image of `A` is the image of the sub-support of `A` that lands in it. -/

open scoped Classical in
/-- A support inside `supportImage e A` is the image of the part of `A` that lands in it. -/
theorem image_filter_mem (e : ∀ s, V s ↪ W s) {A : Finset (Σ s : S.Srt, V s)}
    {B : Finset (Σ s : S.Srt, W s)} (h : B ⊆ supportImage e A) :
    (A.filter fun v => Sigma.map id (fun s => ⇑(e s)) v ∈ B).image
        (Sigma.map id fun s => ⇑(e s)) = B := by
  ext w
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨v, ⟨-, hv⟩, rfl⟩
    exact hv
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (h hw)
    exact ⟨v, ⟨hv, hw⟩, rfl⟩

open scoped Classical in
/-- **The local latent index transports along an embedding.** -/
noncomputable def localLatentIndexCongr (e : ∀ s, V s ↪ W s)
    (A : Finset (Σ s : S.Srt, V s)) (n : ℕ) :
    LocalLatentIndexOver V A n ≃ LocalLatentIndexOver W (supportImage e A) n where
  toFun B := ⟨latentIndexEmbed e n B.1,
    (latentIndexEmbed_subset_supportImage_iff e B.1).mpr B.2⟩
  invFun B := ⟨⟨A.filter fun v => Sigma.map id (fun s => ⇑(e s)) v ∈ B.1.1, by
      have hcard := B.1.2
      rw [← image_filter_mem e B.2,
        Finset.card_image_of_injective _ (injective_sigmaMap e)] at hcard
      exact hcard⟩,
    Finset.filter_subset _ _⟩
  left_inv B := by
    refine Subtype.ext (Subtype.ext ?_)
    show A.filter (fun v => Sigma.map id (fun s => ⇑(e s)) v ∈
      (latentIndexEmbed e n B.1).1) = B.1.1
    ext v
    simp only [Finset.mem_filter, latentIndexEmbed_coe]
    rw [(injective_sigmaMap e).mem_finset_image]
    exact ⟨fun h => h.2, fun h => ⟨B.2 h, h⟩⟩
  right_inv B := by
    refine Subtype.ext (Subtype.ext ?_)
    rw [latentIndexEmbed_coe]
    exact image_filter_mem e B.2

open scoped Classical in
/-- The local latent space equivalence induced by an embedding, as a **measurable** equivalence. -/
noncomputable def localLatentSpaceCongr (e : ∀ s, V s ↪ W s)
    (A : Finset (Σ s : S.Srt, V s)) (n : ℕ) :
    LocalLatentSpaceOver W (supportImage e A) n ≃ᵐ LocalLatentSpaceOver V A n where
  toEquiv := Equiv.arrowCongr (localLatentIndexCongr e A n).symm (Equiv.refl ℝ)
  measurable_toFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _

open scoped Classical in
@[simp] theorem localLatentSpaceCongr_apply (e : ∀ s, V s ↪ W s)
    (A : Finset (Σ s : S.Srt, V s)) (n : ℕ)
    (x : LocalLatentSpaceOver W (supportImage e A) n) (B : LocalLatentIndexOver V A n) :
    localLatentSpaceCongr e A n x B = x (localLatentIndexCongr e A n B) := rfl

open scoped Classical in
/-- **Exact naturality of the local latents against an embedding.** Reading the latents visible at
`A` after restricting along `e` is reading those visible at the image of `A` and transporting. -/
theorem localLatentsOver_latentRestrictOver (e : ∀ s, V s ↪ W s)
    (A : Finset (Σ s : S.Srt, V s)) (n : ℕ) :
    localLatentsOver (S := S) A n ∘ latentRestrictOver e n =
      localLatentSpaceCongr e A n ∘ localLatentsOver (supportImage e A) n := by
  funext ω B
  rfl

open scoped Classical in
/-- Transporting a support along a carrier equivalence and back is the identity. -/
theorem supportImage_symm_supportImage (e : ∀ s, V s ≃ W s) (A : Finset (Σ s : S.Srt, V s)) :
    supportImage (fun s => (e s).symm.toEmbedding) (supportImage (fun s => (e s).toEmbedding) A)
      = A := by
  rw [supportImage, supportImage, Finset.image_image]
  refine (Finset.image_congr fun v _ => ?_).trans A.image_id
  obtain ⟨s, x⟩ := v
  show (⟨s, (e s).symm ((e s) x)⟩ : Σ s : S.Srt, V s) = ⟨s, x⟩
  rw [(e s).symm_apply_apply]

open scoped Classical in
/-- The transported support has the same cardinality. -/
theorem card_supportImage (e : ∀ s, V s ↪ W s) (A : Finset (Σ s : S.Srt, V s)) :
    (supportImage e A).card = A.card :=
  Finset.card_image_of_injective _ (injective_sigmaMap e)

/-! ### Blocks transport along an embedding

The inverse is the delicate point and is kept **local to the exact-support subtype**: a coordinate
whose support is exactly `supportImage e A` has every argument in the image of `e`, which supplies
the range witness for each argument. Nothing pretends `e` is globally surjective. -/

open scoped Classical in
/-- Every argument of a coordinate with support exactly `supportImage e A` lies in the range of the
embedding — the range witness the inverse needs, available only on this subtype. -/
theorem exists_preimage_of_block (e : ∀ s, V s ↪ W s) {A : Finset (Σ s : S.Srt, V s)}
    (c : BlockIndexOver W (supportImage e A)) (i : Fin (S.arity c.1.1)) :
    ∃ v : V (S.argSort c.1.1 i), e _ v = c.1.2 i := by
  have hmem : c.1.taggedValue i ∈ c.1.support := (RelCoord.mem_support_iff _ _).mpr ⟨i, rfl⟩
  rw [c.2] at hmem
  obtain ⟨u, -, heq⟩ := Finset.mem_image.mp hmem
  obtain ⟨s, v⟩ := u
  rw [Sigma.mk.injEq] at heq
  obtain ⟨h1, h2⟩ := heq
  subst h1
  exact ⟨v, eq_of_heq h2⟩

open scoped Classical in
/-- The chosen preimage of an argument. -/
noncomputable def blockPreimage (e : ∀ s, V s ↪ W s) {A : Finset (Σ s : S.Srt, V s)}
    (c : BlockIndexOver W (supportImage e A)) (i : Fin (S.arity c.1.1)) :
    V (S.argSort c.1.1 i) := (exists_preimage_of_block e c i).choose

open scoped Classical in
@[simp] theorem blockPreimage_spec (e : ∀ s, V s ↪ W s) {A : Finset (Σ s : S.Srt, V s)}
    (c : BlockIndexOver W (supportImage e A)) (i : Fin (S.arity c.1.1)) :
    e _ (blockPreimage e c i) = c.1.2 i := (exists_preimage_of_block e c i).choose_spec

open scoped Classical in
theorem map_blockPreimage (e : ∀ s, V s ↪ W s) {A : Finset (Σ s : S.Srt, V s)}
    (c : BlockIndexOver W (supportImage e A)) :
    RelCoord.map (fun s => ⇑(e s)) (⟨c.1.1, blockPreimage e c⟩ : RelCoord S V) = c.1 :=
  congrArg (fun w => (⟨c.1.1, w⟩ : RelCoord S W)) (funext fun i => blockPreimage_spec e c i)

open scoped Classical in
/-- **The block index transports along an embedding.** -/
noncomputable def blockIndexCongr (e : ∀ s, V s ↪ W s) (A : Finset (Σ s : S.Srt, V s)) :
    BlockIndexOver V A ≃ BlockIndexOver W (supportImage e A) where
  toFun c := ⟨RelCoord.map (fun s => ⇑(e s)) c.1, by
    rw [RelCoord.support_map, c.2]; rfl⟩
  invFun c := ⟨⟨c.1.1, blockPreimage e c⟩, by
    refine supportImage_injective e ?_
    rw [supportImage_support, map_blockPreimage e c, c.2]⟩
  left_inv c := by
    refine Subtype.ext ?_
    refine congrArg (fun w => (⟨c.1.1, w⟩ : RelCoord S V)) (funext fun i => ?_)
    exact (e _).injective (blockPreimage_spec e ⟨RelCoord.map (fun s => ⇑(e s)) c.1, by
      rw [RelCoord.support_map, c.2]; rfl⟩ i)
  right_inv c := Subtype.ext (map_blockPreimage e c)

open scoped Classical in
/-- The block space equivalence induced by an embedding, as a **measurable** equivalence. -/
noncomputable def blockSpaceCongr (e : ∀ s, V s ↪ W s) (A : Finset (Σ s : S.Srt, V s)) :
    BlockSpaceOver W (supportImage e A) ≃ᵐ BlockSpaceOver V A where
  toEquiv := Equiv.arrowCongr (blockIndexCongr e A).symm (Equiv.refl Bool)
  measurable_toFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _

open scoped Classical in
@[simp] theorem blockSpaceCongr_apply (e : ∀ s, V s ↪ W s) (A : Finset (Σ s : S.Srt, V s))
    (x : BlockSpaceOver W (supportImage e A)) (c : BlockIndexOver V A) :
    blockSpaceCongr e A x c = x (blockIndexCongr e A c) := rfl

open scoped Classical in
/-- **Exact naturality of the block against an embedding.** -/
theorem blockMapOver_restrict (e : ∀ s, V s ↪ W s) (A : Finset (Σ s : S.Srt, V s)) :
    blockMapOver (S := S) A ∘ RelStructure.restrict e =
      blockSpaceCongr e A ∘ blockMapOver (supportImage e A) := by
  funext X c
  rfl

/-! ### The remainder transports along a carrier equivalence

Bundled as a measurable equivalence, not merely an index bijection, so that the screening assembly
can straighten the transported remainder codomain directly. -/

open scoped Classical in
/-- **The remainder index transports along a carrier equivalence.** An equivalence is required:
the remainder ranges over every rank-`≤ n` coordinate of the ambient carrier, so an embedding into
a larger carrier would leave coordinates outside its image unmatched. -/
noncomputable def restIndexCongr (e : ∀ s, V s ≃ W s) (n : ℕ)
    (A : Finset (Σ s : S.Srt, V s)) :
    RestIndexOver V n A ≃ RestIndexOver W n (supportImage (fun s => (e s).toEmbedding) A) where
  toFun c := ⟨RelCoord.congrCarrier e c.1, by
    obtain ⟨c, hcard, hne⟩ := c
    rw [RelCoord.support_congrCarrier, supportImage]
    refine ⟨?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (injective_sigmaMap fun s => (e s).toEmbedding)]
      exact hcard
    · exact fun h => hne (supportImage_injective _ h)⟩
  invFun c := ⟨(RelCoord.congrCarrier e).symm c.1, by
    obtain ⟨c, hcard, hne⟩ := c
    refine ⟨?_, ?_⟩
    · have hsupp : (RelCoord.congrCarrier e ((RelCoord.congrCarrier e).symm c)).support =
          supportImage (fun s => (e s).toEmbedding)
            ((RelCoord.congrCarrier e).symm c).support :=
        RelCoord.support_congrCarrier e _
      rw [Equiv.apply_symm_apply, supportImage] at hsupp
      rw [← Finset.card_image_of_injective
        (((RelCoord.congrCarrier e).symm c).support)
        (injective_sigmaMap fun s => (e s).toEmbedding), ← hsupp]
      exact hcard
    · intro h
      refine hne ?_
      have hsupp : (RelCoord.congrCarrier e ((RelCoord.congrCarrier e).symm c)).support =
          supportImage (fun s => (e s).toEmbedding)
            ((RelCoord.congrCarrier e).symm c).support :=
        RelCoord.support_congrCarrier e _
      rw [Equiv.apply_symm_apply] at hsupp
      rw [hsupp, h]⟩
  left_inv c := Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv c := Subtype.ext (Equiv.apply_symm_apply _ _)

open scoped Classical in
/-- The remainder space equivalence induced by a carrier equivalence, as a **measurable**
equivalence. -/
noncomputable def restSpaceCongr (e : ∀ s, V s ≃ W s) (n : ℕ)
    (A : Finset (Σ s : S.Srt, V s)) :
    RestSpaceOver W n (supportImage (fun s => (e s).toEmbedding) A) ≃ᵐ RestSpaceOver V n A where
  toEquiv := Equiv.arrowCongr (restIndexCongr e n A).symm (Equiv.refl Bool)
  measurable_toFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _

open scoped Classical in
@[simp] theorem restSpaceCongr_apply (e : ∀ s, V s ≃ W s) (n : ℕ)
    (A : Finset (Σ s : S.Srt, V s))
    (x : RestSpaceOver W n (supportImage (fun s => (e s).toEmbedding) A))
    (c : RestIndexOver V n A) :
    restSpaceCongr e n A x c = x (restIndexCongr e n A c) := rfl

open scoped Classical in
/-- **Exact naturality of the remainder against a carrier equivalence.** Observing after
transporting the whole joint object from `W` back to `V` is observing on `W` and reindexing both
remainder outputs. An equivalence throughout — the remainder is global. -/
theorem restObservationOver_congrCarrier (e : ∀ s, V s ≃ W s) (n : ℕ)
    (A : Finset (Σ s : S.Srt, V s)) :
    restObservationOver (S := S) n A ∘
        Prod.map (RelStructure.restrict fun s => (e s).toEmbedding)
          (latentRestrictOver (fun s => (e s).toEmbedding) n) =
      Prod.map (restSpaceCongr e n A) (latentCongrOver e n) ∘
        restObservationOver n (supportImage (fun s => (e s).toEmbedding) A) := by
  funext p
  rfl

end RelSignature
