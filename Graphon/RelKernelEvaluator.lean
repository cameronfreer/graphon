/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelEqualityPattern
import Graphon.RelationalTopology

/-!
# The measurable kernel evaluator over pattern-local latents (R4 evaluator layer, #107)

The second R4 layer, on the settled #137 interface: a **kernel family** assigns to every
relation symbol and every abstract equality pattern a measurable Boolean function of the
pattern-local latents; the **evaluator** reads each coordinate of the infinite structure off
the global latent source through its local window. **No latent source measure, sampler
pushforward, dissociation, or representation theorem here** — those are the subsequent
layers; this file settles the evaluator and its equivariance.

* `RelKernelFamily S` — the label-free representing kernels `f_{r,π}`, measurable on the
  finite product `PatternLatentIndex π → ℝ`;
* `RelCoord.localLatents` — the local latent window of a coordinate: the global source
  restricted along `patternLatentIndexEquivCoord` and the canonical projection;
* `RelKernelFamily.evalStructure` — the evaluated infinite structure, measurable in the
  global source;
* `RelKernelFamily.evalStructure_relabel` — **equivariance**: relabeling the evaluated
  structure is evaluating at the relabeled latents — the statement that will make
  exchangeability of the evaluated law a coordinatewise check.
-/

open Function MeasureTheory

namespace RelSignature

variable {S : RelSignature}

/-! ### Kernel families -/

/-- **A representing kernel family**: for every relation symbol and every abstract equality
pattern, a measurable Boolean function of the pattern-local latents. Label-free by
construction — the kernel sees only the pattern and its blocks, never vertex labels. -/
structure RelKernelFamily (S : RelSignature) where
  /-- The kernel at a relation symbol and pattern. -/
  toFun : ∀ (r : S.Rel) (π : EqualityPattern S r), (PatternLatentIndex π → ℝ) → Bool
  /-- Each kernel is measurable on the finite latent product. -/
  measurable : ∀ (r : S.Rel) (π : EqualityPattern S r), Measurable (toFun r π)

/-! ### The local latent window -/

/-- **The local latent window of a coordinate**: the global latent source read through the
coordinate's pattern-local indices (via the canonical equivalence and projection). -/
noncomputable def RelCoord.localLatents (c : RelCoord S (Vinfinite S))
    (ω : LatentIndex S (Vinfinite S) → ℝ) :
    PatternLatentIndex c.equalityPattern → ℝ := fun A =>
  ω (CoordLatentIndex.toLatentIndex (patternLatentIndexEquivCoord c A))

theorem RelCoord.measurable_localLatents (c : RelCoord S (Vinfinite S)) :
    Measurable fun ω : LatentIndex S (Vinfinite S) → ℝ => c.localLatents ω := by
  rw [measurable_pi_iff]
  intro A
  exact measurable_pi_apply _

/-! ### The evaluator -/

/-- **The evaluated infinite structure**: each coordinate is its kernel applied to its local
latent window. -/
noncomputable def RelKernelFamily.evalStructure (F : RelKernelFamily S)
    (ω : LatentIndex S (Vinfinite S) → ℝ) : RelStructure S (Vinfinite S) := fun c =>
  F.toFun c.1 c.equalityPattern (c.localLatents ω)

@[simp] theorem RelKernelFamily.evalStructure_apply (F : RelKernelFamily S)
    (ω : LatentIndex S (Vinfinite S) → ℝ) (c : RelCoord S (Vinfinite S)) :
    F.evalStructure ω c = F.toFun c.1 c.equalityPattern (c.localLatents ω) := rfl

/-- **The evaluator is measurable** in the global latent source. -/
theorem RelKernelFamily.measurable_evalStructure (F : RelKernelFamily S) :
    Measurable F.evalStructure := by
  rw [measurable_pi_iff]
  intro c
  exact (F.measurable c.1 c.equalityPattern).comp (c.measurable_localLatents)

/-! ### Equivariance -/

section Equivariance

variable {V W : S.Srt → Type*}

/-- **The value of a support block** (definitional): `patternQuotientEquivSupport` sends the
block of position `i` to the sort-tagged value at `i`. -/
theorem RelCoord.patternQuotientEquivSupport_mk (c : RelCoord S V) (i : Fin (S.arity c.1)) :
    (c.patternQuotientEquivSupport ⟦i⟧).1 = c.taggedValue i := rfl

/-- **Membership characterization of the labeled avatar of a block-set**: a tagged value lies
in `patternLatentIndexEquivCoord c A` iff it is the support value of one of the blocks
in `A`. -/
theorem mem_patternLatentIndexEquivCoord (c : RelCoord S V)
    (A : PatternLatentIndex c.equalityPattern) {v : Σ s : S.Srt, V s} :
    v ∈ (patternLatentIndexEquivCoord c A).1 ↔
      ∃ q ∈ A.1, (c.patternQuotientEquivSupport q).1 = v := by
  show v ∈ (A.1.map c.patternQuotientEquivSupport.toEmbedding).map
      (Function.Embedding.subtype _) ↔ _
  simp only [Finset.mem_map, Function.Embedding.coe_subtype, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨w, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨c.patternQuotientEquivSupport q, ⟨q, hq, rfl⟩, rfl⟩

open scoped Classical in
/-- **Membership characterization of the relabeling equivalence**: the forward direction of
`CoordLatentIndex.congrMap` is the image under `Sigma.map id`. -/
theorem CoordLatentIndex.mem_congrMap {f : ∀ s, V s → W s} (hf : ∀ s, Injective (f s))
    (c : RelCoord S V) (A : CoordLatentIndex c) {w : Σ s : S.Srt, W s} :
    w ∈ (CoordLatentIndex.congrMap hf c A).1 ↔
      ∃ v ∈ A.1, Sigma.map id (fun s => f s) v = w :=
  Finset.mem_image

/-- Transport of pattern-local indices along `rfl` is the identity. -/
@[simp] theorem PatternLatentIndex.congr_rfl {r : S.Rel} {π : EqualityPattern S r} :
    PatternLatentIndex.congr (rfl : π = π) = Equiv.refl _ := rfl

/-- **Cast taming**: membership of a block in a transported pattern-local index reduces to
membership in the original — both sides typecheck because the two patterns share the
positions `Fin (S.arity r)`. -/
theorem PatternLatentIndex.congr_mem_mk {r : S.Rel} {π π' : EqualityPattern S r}
    (h : π = π') (A : PatternLatentIndex π) (i : Fin (S.arity r)) :
    (⟦i⟧ : Quotient π'.toSetoid) ∈ (PatternLatentIndex.congr h A).1 ↔
      (⟦i⟧ : Quotient π.toSetoid) ∈ A.1 := by
  subst h
  rw [PatternLatentIndex.congr_rfl]
  exact Iff.rfl

/-- **The transport square**: the labeled avatar of a block-set of the relabeled coordinate
is the relabeling (`CoordLatentIndex.congrMap`) of the labeled avatar of the same block-set
read through the pattern identification `RelCoord.equalityPattern_map`. -/
theorem patternLatentIndexEquivCoord_map {f : ∀ s, V s → W s} (hf : ∀ s, Injective (f s))
    (c : RelCoord S V) (A' : PatternLatentIndex (RelCoord.map f c).equalityPattern) :
    patternLatentIndexEquivCoord (RelCoord.map f c) A' =
      CoordLatentIndex.congrMap hf c
        (patternLatentIndexEquivCoord c
          (PatternLatentIndex.congr (RelCoord.equalityPattern_map hf c) A')) := by
  refine Subtype.ext (Finset.ext fun v => ?_)
  simp only [mem_patternLatentIndexEquivCoord, CoordLatentIndex.mem_congrMap hf]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨i, rfl⟩ := q.exists_rep
    exact ⟨(c.patternQuotientEquivSupport ⟦i⟧).1,
      ⟨⟦i⟧, (PatternLatentIndex.congr_mem_mk _ A' i).mpr hq, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨q, hq, rfl⟩, rfl⟩
    obtain ⟨i, rfl⟩ := q.exists_rep
    exact ⟨⟦i⟧, (PatternLatentIndex.congr_mem_mk _ A' i).mp hq, rfl⟩

/-- **The local latent window is equivariant**: the window of the relabeled coordinate at a
block-set is the window of the original coordinate, read off the source precomposed with the
global latent-index action, at the transported block-set. -/
theorem RelCoord.localLatents_map {f : ∀ s, Vinfinite S s → Vinfinite S s}
    (hf : ∀ s, Injective (f s)) (c : RelCoord S (Vinfinite S))
    (ω : LatentIndex S (Vinfinite S) → ℝ)
    (A' : PatternLatentIndex (RelCoord.map f c).equalityPattern) :
    (RelCoord.map f c).localLatents ω A' =
      c.localLatents (fun A => ω (LatentIndex.map f A))
        (PatternLatentIndex.congr (RelCoord.equalityPattern_map hf c) A') := by
  show ω (CoordLatentIndex.toLatentIndex (patternLatentIndexEquivCoord (RelCoord.map f c) A')) = _
  rw [patternLatentIndexEquivCoord_map hf c A', CoordLatentIndex.congrMap_toLatentIndex]
  rfl

/-- **Kernel applications transport along pattern equalities**: if the patterns agree and the
latent arguments correspond under `PatternLatentIndex.congr`, the kernel values agree. -/
theorem RelKernelFamily.toFun_congr (F : RelKernelFamily S) {r : S.Rel}
    {π₁ π₂ : EqualityPattern S r} (h : π₁ = π₂)
    {ℓ₁ : PatternLatentIndex π₁ → ℝ} {ℓ₂ : PatternLatentIndex π₂ → ℝ}
    (hℓ : ∀ A, ℓ₁ A = ℓ₂ (PatternLatentIndex.congr h A)) :
    F.toFun r π₁ ℓ₁ = F.toFun r π₂ ℓ₂ := by
  subst h
  exact congrArg (F.toFun r π₁) (funext fun A => hℓ A)

/-- **Equivariance of the evaluator**: relabeling the evaluated structure by a sortwise
family of permutations is evaluating at the source precomposed with the latent-index action
of the permutations. Orientation: `relabel σ` reads coordinate `c` at `RelCoord.map σ c`,
so the source is precomposed with `LatentIndex.map σ` (the forward action, not `σ⁻¹`) —
relabeling the structure = precomposing the latent source with the latent-index action. -/
theorem RelKernelFamily.evalStructure_relabel (F : RelKernelFamily S)
    (σ : ∀ _ : S.Srt, Equiv.Perm ℕ) (ω : LatentIndex S (Vinfinite S) → ℝ) :
    RelStructure.relabel σ (F.evalStructure ω) =
      F.evalStructure (fun A => ω (LatentIndex.map (fun s => ⇑(σ s)) A)) := by
  funext c
  exact F.toFun_congr (RelCoord.equalityPattern_map (fun s => (σ s).injective) c)
    (RelCoord.localLatents_map (fun s => (σ s).injective) c ω)

end Equivariance

end RelSignature
