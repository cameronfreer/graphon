/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.InfiniteDigraph
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Setoid.Basic

/-!
# Equality patterns, supports, and subset latent indices (R4 design checkpoint, #106 sequel)

The design layer of the functional Aldous–Hoover–Kallenberg representation: the vocabulary in
which the dissociated representation's sampler and representation theorem will be stated.
**This file deliberately contains no sampler and no representation theorem** — it fixes the
interface (a review checkpoint) before those are built.

Design decisions, made explicit:

* **Sort-tagging.** The atom of the design is `RelCoord.taggedValue c i : Σ s, V s` — the
  value at position `i` *tagged with its sort*. All downstream notions factor through it, so
  equality of raw vertex values across *different* sorts never counts: vertex `3` of sort `A`
  and vertex `3` of sort `B` are distinct tagged values.
* **The equality pattern is a kernel.** `RelCoord.pattern c := Setoid.ker c.taggedValue` —
  positions are equivalent exactly when they carry the same sort-tagged value. No choice of
  canonical representative is made; the pattern's blocks are canonically the support
  (`patternQuotientEquivSupport`).
* **The support is a finset of tagged values**, `RelCoord.support c ⊆ Σ s, V s` — the
  "vertices the coordinate actually reads", abstractly (not positions).
* **Latent indices are nonempty finite sets of tagged values**: `LatentIndex S V`. The
  eventual dissociated representation reads the coordinate at `c` off latents `U_A` for
  `A ⊆ c.support` nonempty; one latent source indexed by `LatentIndex S (Vinfinite S)` will
  serve every coordinate. Nonemptiness excludes a global (`U_∅`) latent — the dissociated
  normal form.
* **Transport is by `Sigma.map id`.** A sortwise map `f : ∀ s, V s → W s` acts on tagged
  values, supports, and latent indices through `Sigma.map id f`; all equivariance statements
  are phrased through this single action. Sortwise *injective* maps preserve patterns
  (`pattern_map`), act injectively on latent indices, and carry subset-latents of a support
  to subset-latents of the image support — the equivariance the representation theorem needs
  so that exchangeability can be checked coordinatewise.

The examples section instantiates the binary (`digraphSig`) off-diagonal and diagonal
coordinates, a ternary signature with a repeated entry, and a two-sort bipartite signature
where equal raw values in different sorts are *not* identified.
-/

open Function

namespace RelSignature

variable {S : RelSignature} {V W X : S.Srt → Type*}

/-! ### Sort-tagged values, patterns, and supports -/

/-- **The sort-tagged value** at a position of a coordinate: the value together with its
sort. The atom through which patterns, supports, and latent indices all factor. -/
def RelCoord.taggedValue (c : RelCoord S V) (i : Fin (S.arity c.1)) : Σ s : S.Srt, V s :=
  ⟨S.argSort c.1 i, c.2 i⟩

/-- **The equality pattern** of a coordinate: the kernel of the sort-tagged value map —
positions are equivalent exactly when they carry the same value *of the same sort*. -/
def RelCoord.pattern (c : RelCoord S V) : Setoid (Fin (S.arity c.1)) :=
  Setoid.ker c.taggedValue

theorem RelCoord.pattern_iff (c : RelCoord S V) (i j : Fin (S.arity c.1)) :
    c.pattern i j ↔ c.taggedValue i = c.taggedValue j := Iff.rfl

open scoped Classical in
/-- **The support** of a coordinate: the finite set of sort-tagged values it reads. -/
noncomputable def RelCoord.support (c : RelCoord S V) : Finset (Σ s : S.Srt, V s) :=
  (Finset.univ : Finset (Fin (S.arity c.1))).image c.taggedValue

open scoped Classical in
theorem RelCoord.mem_support_iff (c : RelCoord S V) (v : Σ s : S.Srt, V s) :
    v ∈ c.support ↔ ∃ i, c.taggedValue i = v := by
  simp [RelCoord.support]

/-- A coordinate of a positive-arity relation has nonempty support. -/
theorem RelCoord.support_nonempty (c : RelCoord S V) (h : 0 < S.arity c.1) :
    c.support.Nonempty := by
  refine ⟨c.taggedValue ⟨0, h⟩, ?_⟩
  rw [c.mem_support_iff]
  exact ⟨⟨0, h⟩, rfl⟩

open scoped Classical in
/-- **The pattern's blocks are the support**: the quotient by the equality pattern is
canonically the set of sort-tagged values read — the "abstract support blocks". -/
noncomputable def RelCoord.patternQuotientEquivSupport (c : RelCoord S V) :
    Quotient c.pattern ≃ {v // v ∈ c.support} :=
  (Setoid.quotientKerEquivRange c.taggedValue).trans
    (Equiv.subtypeEquiv (Equiv.refl _) fun v => by
      simp [Set.mem_range, RelCoord.mem_support_iff])

/-! ### Subset latent indices -/

/-- **A latent index**: a nonempty finite set of sort-tagged vertices. The dissociated
functional representation attaches one uniform latent to every such index; the coordinate at
`c` reads only the latents indexed by nonempty subsets of `c.support`. -/
abbrev LatentIndex (S : RelSignature) (V : S.Srt → Type*) : Type _ :=
  {A : Finset (Σ s : S.Srt, V s) // A.Nonempty}

open scoped Classical in
/-- The action of a sortwise map on latent indices, through `Sigma.map id`. -/
noncomputable def LatentIndex.map (f : ∀ s, V s → W s) (A : LatentIndex S V) :
    LatentIndex S W :=
  ⟨A.1.image (Sigma.map id f), A.2.image _⟩

open scoped Classical in
@[simp] theorem LatentIndex.map_coe (f : ∀ s, V s → W s) (A : LatentIndex S V) :
    (LatentIndex.map f A : Finset (Σ s : S.Srt, W s)) = A.1.image (Sigma.map id f) := rfl

/-! ### Transport and equivariance -/

/-- Tagged values transport along sortwise maps through `Sigma.map id` (definitional). -/
theorem RelCoord.taggedValue_map (f : ∀ s, V s → W s) (c : RelCoord S V)
    (i : Fin (S.arity c.1)) :
    (RelCoord.map f c).taggedValue i = Sigma.map id (fun s => f s) (c.taggedValue i) := rfl

/-- `Sigma.map id` of a sortwise injective family is injective. -/
theorem injective_sigmaMap_of_sortwise {f : ∀ s, V s → W s}
    (hf : ∀ s, Injective (f s)) : Injective (Sigma.map id (fun s => f s)) :=
  injective_id.sigma_map hf

/-- **Patterns are invariant under sortwise injections**: relabeling by an injective sortwise
map neither merges nor splits equality-pattern blocks. -/
theorem RelCoord.pattern_map {f : ∀ s, V s → W s} (hf : ∀ s, Injective (f s))
    (c : RelCoord S V) :
    (RelCoord.map f c).pattern = c.pattern := by
  refine Setoid.ext fun i j => ?_
  show (RelCoord.map f c).taggedValue i = (RelCoord.map f c).taggedValue j ↔
    c.taggedValue i = c.taggedValue j
  rw [RelCoord.taggedValue_map, RelCoord.taggedValue_map]
  exact ⟨fun h => injective_sigmaMap_of_sortwise hf h, fun h => congrArg _ h⟩

open scoped Classical in
/-- **Supports transport covariantly**: the support of the relabeled coordinate is the image
of the support. -/
theorem RelCoord.support_map (f : ∀ s, V s → W s) (c : RelCoord S V) :
    (RelCoord.map f c).support = c.support.image (Sigma.map id (fun s => f s)) := by
  ext v
  simp only [RelCoord.mem_support_iff, Finset.mem_image]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨c.taggedValue i, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

/-- The latent-index action is functorial: composition. -/
theorem LatentIndex.map_map (f : ∀ s, V s → W s) (g : ∀ s, W s → X s)
    (A : LatentIndex S V) :
    LatentIndex.map g (LatentIndex.map f A) =
      LatentIndex.map (fun s => g s ∘ f s) A := by
  refine Subtype.ext ?_
  classical
  simp only [LatentIndex.map_coe, Finset.image_image]
  exact Finset.image_congr fun v _ => by
    obtain ⟨s, x⟩ := v
    rfl

/-- The latent-index action is functorial: identity. -/
theorem LatentIndex.map_id (A : LatentIndex S V) :
    LatentIndex.map (fun _ => id) A = A := by
  refine Subtype.ext ?_
  classical
  simp only [LatentIndex.map_coe]
  exact Finset.image_congr (fun v _ => by obtain ⟨s, x⟩ := v; rfl) |>.trans A.1.image_id

/-- **Sortwise injections act injectively on latent indices** — the equivariance that lets
the eventual sampler pull one latent source back along any relabeling. -/
theorem LatentIndex.map_injective {f : ∀ s, V s → W s} (hf : ∀ s, Injective (f s)) :
    Injective (LatentIndex.map (S := S) f) := by
  classical
  rintro ⟨A, hA⟩ ⟨B, hB⟩ h
  refine Subtype.ext (Finset.image_injective (injective_sigmaMap_of_sortwise hf) ?_)
  simpa [LatentIndex.map] using congrArg Subtype.val h

open scoped Classical in
/-- **Subset-latents transport into subset-latents**: a nonempty subset of the support of
`c` maps to a nonempty subset of the support of the relabeled coordinate. -/
theorem LatentIndex.map_subset_support {f : ∀ s, V s → W s} {c : RelCoord S V}
    {A : LatentIndex S V} (hA : A.1 ⊆ c.support) :
    (LatentIndex.map f A).1 ⊆ (RelCoord.map f c).support := by
  rw [RelCoord.support_map]
  exact Finset.image_subset_image hA

end RelSignature

/-! ### Examples: binary, diagonal, ternary, bipartite -/

section Examples

open RelSignature

open scoped Classical

/-- Binary off-diagonal (`digraphSig`, one sort): distinct vertices give the discrete
pattern — the two positions are inequivalent. -/
example {i j : ℕ} (h : i ≠ j) : ¬ (digraphCoord (V := ℕ) i j).pattern 0 1 := by
  intro hcon
  exact h (congrArg (fun v : Σ _ : Unit, ℕ => v.2) hcon)

/-- Binary diagonal: the loop coordinate identifies its two positions. -/
example (i : ℕ) : (digraphCoord (V := ℕ) i i).pattern 0 1 := rfl

/-- Binary supports: an off-diagonal coordinate reads two vertices, a loop reads one. -/
example {i j : ℕ} (h : i ≠ j) : (digraphCoord (V := ℕ) i j).support.card = 2 := by
  rw [show (digraphCoord (V := ℕ) i j).support = {⟨(), i⟩, ⟨(), j⟩} from by
    ext v
    rw [RelCoord.mem_support_iff]
    constructor
    · rintro ⟨a, rfl⟩
      fin_cases a <;> simp [RelCoord.taggedValue, digraphCoord]
    · intro hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ⟨0, rfl⟩
      · rw [Finset.mem_singleton] at hv
        subst hv
        exact ⟨1, rfl⟩]
  rw [Finset.card_insert_of_notMem (by simp [h]), Finset.card_singleton]

example (i : ℕ) : (digraphCoord (V := ℕ) i i).support.card = 1 := by
  rw [show (digraphCoord (V := ℕ) i i).support = {⟨(), i⟩} from by
    ext v
    rw [RelCoord.mem_support_iff]
    constructor
    · rintro ⟨a, rfl⟩
      fin_cases a <;> simp [RelCoord.taggedValue, digraphCoord]
    · intro hv
      rw [Finset.mem_singleton] at hv
      subst hv
      exact ⟨0, rfl⟩]
  exact Finset.card_singleton _

/-- A one-sort ternary signature. -/
abbrev ternarySig : RelSignature where
  Srt := Unit
  Rel := Unit
  arity := fun _ => 3
  argSort := fun _ _ => ()

/-- The running ternary coordinate `(0, 1, 0)`: a repeated entry. -/
def ternaryExample : RelCoord ternarySig fun _ => ℕ := ⟨(), ![0, 1, 0]⟩

/-- Ternary with a repeated entry: positions `0` and `2` are identified, `0` and `1` are
not. -/
example : ternaryExample.pattern 0 2 := rfl

example : ¬ ternaryExample.pattern 0 1 := by
  intro hcon
  exact Nat.zero_ne_one (congrArg (fun v : Σ _ : Unit, ℕ => v.2) hcon)

/-- A two-sort bipartite binary signature: position `0` is a left vertex, position `1` a
right vertex. -/
abbrev bipartiteSig : RelSignature where
  Srt := Bool
  Rel := Unit
  arity := fun _ => 2
  argSort := fun _ i => decide (i = 1)

/-- The running bipartite coordinate with equal raw values in both positions. -/
def bipartiteExample (n : ℕ) : RelCoord bipartiteSig fun _ => ℕ := ⟨(), ![n, n]⟩

/-- **Sort-awareness**: in the bipartite signature, equal *raw* vertex values in the two
positions are still inequivalent — the sorts differ, so the tagged values differ. -/
example (n : ℕ) : ¬ (bipartiteExample n).pattern 0 1 := by
  intro hcon
  exact Bool.false_ne_true (congrArg Sigma.fst hcon)

/-- Correspondingly, the bipartite support of the equal-raw-values coordinate still has two
elements: one per sort. -/
example (n : ℕ) : (bipartiteExample n).support.card = 2 := by
  rw [show (bipartiteExample n).support = {⟨false, n⟩, ⟨true, n⟩} from by
    ext v
    rw [RelCoord.mem_support_iff]
    constructor
    · rintro ⟨a, rfl⟩
      fin_cases a <;> simp [RelCoord.taggedValue, bipartiteExample]
    · intro hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ⟨0, rfl⟩
      · rw [Finset.mem_singleton] at hv
        subst hv
        exact ⟨1, rfl⟩]
  rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]

end Examples
