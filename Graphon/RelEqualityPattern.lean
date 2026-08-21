/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelationalStructure
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Setoid.Basic
import Mathlib.Tactic.FinCases

/-!
# Equality patterns, supports, and subset latent indices (R4 design checkpoint, #107)

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
* **Patterns are bundled independently of coordinates.** `EqualityPattern S r` packages a
  setoid on the positions of `r` *together with sort compatibility* (equivalent positions
  have equal `argSort`), so an abstract pattern `π` exists without any labeled coordinate;
  `RelCoord.equalityPattern` extracts the bundled pattern of a coordinate, and
  `EqualityPattern.blockSort` is the induced sort of each block — per-sort counts are
  *derived*, never stored (no coherence obligations).
* **Local latent indices are bundled per pattern and per coordinate.**
  `PatternLatentIndex π` (nonempty finite subsets of the blocks) is the label-free,
  order-free domain the representing kernel `f_{r,π}` will consume;
  `CoordLatentIndex c` (nonempty subsets of the support) is its labeled avatar, with the
  canonical equivalence `patternLatentIndexEquivCoord` and the *two-way* relabeling
  equivalence `CoordLatentIndex.congrMap` along sortwise injections.
* **Transport is by `Sigma.map id`.** A sortwise map `f : ∀ s, V s → W s` acts on tagged
  values, supports, and latent indices through `Sigma.map id f`; all equivariance statements
  are phrased through this single action. Sortwise *injective* maps preserve patterns
  (`pattern_map`), act injectively on latent indices, and carry subset-latents of a support
  to subset-latents of the image support — the equivariance the representation theorem needs
  so that exchangeability can be checked coordinatewise.

The examples section instantiates a local one-sort binary signature (off-diagonal and
diagonal coordinates), a ternary signature with a repeated entry, and a two-sort bipartite
signature where equal raw values in different sorts are *not* identified — all namespaced,
with no dependency on the directed development.
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

open scoped Classical in
/-- **The support is no larger than the arity**: it is the image of the finitely many positions.
Stated over an abstract carrier, where no natural `DecidableEq` competes with the classical
instance used to form the image. -/
theorem RelCoord.card_support_le (c : RelCoord S V) : c.support.card ≤ S.arity c.1 := by
  refine le_trans Finset.card_image_le ?_
  simp

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

/-- **The relabeling equivalence of latent indices** along a sortwise family of equivalences:
`LatentIndex.map` packaged as an `Equiv`, with inverse the action of the sortwise inverses —
the bijectivity the latent source's exchangeability pulls back along. -/
noncomputable def LatentIndex.relabelEquiv (σ : ∀ s, V s ≃ W s) :
    LatentIndex S V ≃ LatentIndex S W where
  toFun := LatentIndex.map fun s => ⇑(σ s)
  invFun := LatentIndex.map fun s => ⇑(σ s).symm
  left_inv A := by
    rw [LatentIndex.map_map,
      show (fun s => ⇑(σ s).symm ∘ ⇑(σ s)) = fun _ => id from
        funext fun s => (σ s).symm_comp_self,
      LatentIndex.map_id]
  right_inv A := by
    rw [LatentIndex.map_map,
      show (fun s => ⇑(σ s) ∘ ⇑(σ s).symm) = fun _ => id from
        funext fun s => (σ s).self_comp_symm,
      LatentIndex.map_id]

@[simp] theorem LatentIndex.relabelEquiv_apply (σ : ∀ s, V s ≃ W s) (A : LatentIndex S V) :
    LatentIndex.relabelEquiv σ A = LatentIndex.map (fun s => ⇑(σ s)) A := rfl

@[simp] theorem LatentIndex.relabelEquiv_symm_apply (σ : ∀ s, V s ≃ W s)
    (A : LatentIndex S W) :
    (LatentIndex.relabelEquiv σ).symm A = LatentIndex.map (fun s => ⇑(σ s).symm) A := rfl

/-- **Sortwise-disjoint ranges give disjoint latent-index images**: latent indices are
*nonempty*, so images under sortwise maps whose ranges are disjoint in every sort can never
coincide — the combinatorial heart of dissociation of the evaluated law. -/
theorem LatentIndex.map_ne_map_of_disjoint {U : S.Srt → Type*} {f : ∀ s, V s → W s}
    {g : ∀ s, U s → W s} (hd : ∀ s x y, f s x ≠ g s y)
    (A : LatentIndex S V) (B : LatentIndex S U) :
    LatentIndex.map f A ≠ LatentIndex.map g B := by
  classical
  intro h
  obtain ⟨⟨s, x⟩, hx⟩ := A.2
  have hmem : (⟨s, f s x⟩ : Σ s : S.Srt, W s) ∈
      (LatentIndex.map g B : Finset (Σ s : S.Srt, W s)) := by
    rw [← h, LatentIndex.map_coe]
    exact Finset.mem_image_of_mem _ hx
  rw [LatentIndex.map_coe] at hmem
  obtain ⟨⟨t, y⟩, -, hEq⟩ := Finset.mem_image.mp hmem
  obtain ⟨ht, hval⟩ := Sigma.mk.inj_iff.mp hEq
  subst ht
  exact hd t x y (eq_of_heq hval).symm

/-! ### Bundled patterns -/

/-- **An abstract equality pattern** for the relation symbol `r`: a setoid on the positions
together with **sort compatibility** — equivalent positions carry the same sort. This is the
label-free datum the representing kernel `f_{r,π}` is indexed by; a labeled coordinate only
ever enters through `RelCoord.equalityPattern`. -/
@[ext] structure EqualityPattern (S : RelSignature) (r : S.Rel) where
  /-- The equivalence of positions. -/
  toSetoid : Setoid (Fin (S.arity r))
  /-- Equivalent positions have equal sorts. -/
  sort_eq : ∀ ⦃i j⦄, toSetoid i j → S.argSort r i = S.argSort r j

/-- The bundled equality pattern of a labeled coordinate. -/
def RelCoord.equalityPattern (c : RelCoord S V) : EqualityPattern S c.1 :=
  ⟨c.pattern, fun _ _ h => congrArg Sigma.fst h⟩

@[simp] theorem RelCoord.equalityPattern_toSetoid (c : RelCoord S V) :
    c.equalityPattern.toSetoid = c.pattern := rfl

/-- **Bundled patterns are invariant under sortwise injections.** -/
theorem RelCoord.equalityPattern_map {f : ∀ s, V s → W s} (hf : ∀ s, Injective (f s))
    (c : RelCoord S V) :
    (RelCoord.map f c).equalityPattern = c.equalityPattern :=
  EqualityPattern.ext (RelCoord.pattern_map hf c)

/-- **The sort of a block**: `argSort` descends to the pattern's quotient by sort
compatibility. Per-sort block counts or multisets are derived from this, not stored. -/
def EqualityPattern.blockSort {r : S.Rel} (π : EqualityPattern S r) :
    Quotient π.toSetoid → S.Srt :=
  Quotient.lift (S.argSort r) fun _ _ h => π.sort_eq h

@[simp] theorem EqualityPattern.blockSort_mk {r : S.Rel} (π : EqualityPattern S r)
    (i : Fin (S.arity r)) : π.blockSort ⟦i⟧ = S.argSort r i := rfl

/-! ### Local latent indices -/

/-- **The pattern-local latent indices**: nonempty finite subsets of the blocks of an
abstract pattern — the label-free, order-free argument domain of the representing kernel
`f_{r,π} : (PatternLatentIndex π → I) → …`. -/
abbrev PatternLatentIndex {r : S.Rel} (π : EqualityPattern S r) : Type _ :=
  {A : Finset (Quotient π.toSetoid) // A.Nonempty}

/-- The blocks of a pattern form a finite type (positions are `Fin`; classical
decidability of the setoid). -/
noncomputable instance {r : S.Rel} (π : EqualityPattern S r) : Fintype (Quotient π.toSetoid) :=
  @Quotient.fintype _ _ π.toSetoid (Classical.decRel _)

/-- **Pattern-local latent indices form a finite type** — the local latent source of a
single coordinate is a finite product, as the evaluator layer requires. -/
noncomputable instance {r : S.Rel} (π : EqualityPattern S r) :
    Fintype (PatternLatentIndex π) := by
  classical
  haveI : Fintype (Finset (Quotient π.toSetoid)) := Finset.fintype
  exact Subtype.fintype _

instance {r : S.Rel} (π : EqualityPattern S r) : Finite (PatternLatentIndex π) :=
  Finite.of_fintype _

/-- **The coordinate-local latent indices**: nonempty subsets of the support — the labeled
avatar of `PatternLatentIndex`, and the sub-collection of the global `LatentIndex` a single
coordinate reads (canonical projection `CoordLatentIndex.toLatentIndex`). -/
abbrev CoordLatentIndex (c : RelCoord S V) : Type _ :=
  {A : Finset (Σ s : S.Srt, V s) // A.Nonempty ∧ A ⊆ c.support}

/-- **The canonical projection into the global latent indices**: forget the support bound. -/
def CoordLatentIndex.toLatentIndex {c : RelCoord S V} (A : CoordLatentIndex c) :
    LatentIndex S V :=
  ⟨A.1, A.2.1⟩

@[simp] theorem CoordLatentIndex.toLatentIndex_coe {c : RelCoord S V}
    (A : CoordLatentIndex c) :
    (CoordLatentIndex.toLatentIndex A : Finset (Σ s : S.Srt, V s)) = A.1 := rfl

theorem CoordLatentIndex.toLatentIndex_injective (c : RelCoord S V) :
    Injective (CoordLatentIndex.toLatentIndex (c := c)) := fun _ _ h =>
  Subtype.ext (congrArg (fun A : LatentIndex S V => (A : Finset (Σ s : S.Srt, V s))) h)

open scoped Classical in
/-- Finsets of members of `s` are the subsets of `s`. -/
private noncomputable def finsetMemEquivSubsets {α : Type*} (s : Finset α) :
    Finset {v // v ∈ s} ≃ {A : Finset α // A ⊆ s} where
  toFun B := ⟨B.map (Function.Embedding.subtype _), fun v hv => by
    obtain ⟨⟨w, hw⟩, -, rfl⟩ := Finset.mem_map.mp hv
    exact hw⟩
  invFun A := A.1.subtype (· ∈ s)
  left_inv B := by
    ext ⟨v, hv⟩
    rw [Finset.mem_subtype, Finset.mem_map]
    constructor
    · rintro ⟨w, hwB, hEq⟩
      rwa [show w = ⟨v, hv⟩ from Subtype.ext hEq] at hwB
    · intro h
      exact ⟨⟨v, hv⟩, h, rfl⟩
  right_inv A := by
    refine Subtype.ext ?_
    show (A.1.subtype (· ∈ s)).map (Function.Embedding.subtype _) = A.1
    rw [Finset.subtype_map]
    exact Finset.filter_true_of_mem fun v hv => A.2 hv

open scoped Classical in
/-- **The canonical equivalence between pattern-local and coordinate-local latent
indices**, through `patternQuotientEquivSupport`: the kernel's order-free domain is the
labeled coordinate's subset-latent collection. -/
noncomputable def patternLatentIndexEquivCoord (c : RelCoord S V) :
    PatternLatentIndex c.equalityPattern ≃ CoordLatentIndex c :=
  ((((c.patternQuotientEquivSupport.finsetCongr.trans
      (finsetMemEquivSubsets c.support)).subtypeEquiv fun B => by
        simp [finsetMemEquivSubsets, Equiv.finsetCongr_apply, Finset.map_nonempty]).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _)).trans
    (Equiv.subtypeEquivRight fun A => and_comm))

/-- Transport of pattern-local indices along an equality of patterns. -/
def PatternLatentIndex.congr {r : S.Rel} {π π' : EqualityPattern S r} (h : π = π') :
    PatternLatentIndex π ≃ PatternLatentIndex π' := by
  subst h
  exact Equiv.refl _

open scoped Classical in
/-- **The two-way relabeling equivalence of coordinate-local latent indices** along a
sortwise injection — not merely the one-way `map_subset_support`: the forward direction is
the image under `Sigma.map id` (so it agrees with the global `LatentIndex.map`,
`CoordLatentIndex.congrMap_toLatentIndex`), and the inverse is the preimage, well-defined
because the image support bounds the target. -/
noncomputable def CoordLatentIndex.congrMap {f : ∀ s, V s → W s}
    (hf : ∀ s, Injective (f s)) (c : RelCoord S V) :
    CoordLatentIndex c ≃ CoordLatentIndex (RelCoord.map f c) where
  toFun A := ⟨A.1.image (Sigma.map id fun s => f s), A.2.1.image _, by
    rw [RelCoord.support_map]
    exact Finset.image_subset_image A.2.2⟩
  invFun B := ⟨B.1.preimage (Sigma.map id fun s => f s)
      (injective_sigmaMap_of_sortwise hf).injOn, by
    obtain ⟨b, hb⟩ := B.2.1
    have hmem := B.2.2 hb
    rw [RelCoord.support_map] at hmem
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hmem
    exact ⟨w, Finset.mem_preimage.mpr hb⟩, by
    intro w hw
    have hmem := B.2.2 (Finset.mem_preimage.mp hw)
    rw [RelCoord.support_map] at hmem
    obtain ⟨w', hw', hEq⟩ := Finset.mem_image.mp hmem
    rwa [← injective_sigmaMap_of_sortwise hf hEq]⟩
  left_inv A := by
    refine Subtype.ext ?_
    ext w
    rw [Finset.mem_preimage]
    constructor
    · intro hw
      obtain ⟨w', hw', hEq⟩ := Finset.mem_image.mp hw
      rwa [← injective_sigmaMap_of_sortwise hf hEq]
    · exact fun hw => Finset.mem_image_of_mem _ hw
  right_inv B := by
    refine Subtype.ext ?_
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      rw [Finset.mem_preimage] at hw
      exact hw
    · intro hv
      have hmem := B.2.2 hv
      rw [RelCoord.support_map] at hmem
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hmem
      refine Finset.mem_image_of_mem _ ?_
      rw [Finset.mem_preimage]
      exact hv

open scoped Classical in
/-- **Coherence with the global action**: the local relabeling equivalence projects to the
global `LatentIndex.map` — the two transports never disagree. -/
@[simp] theorem CoordLatentIndex.congrMap_toLatentIndex {f : ∀ s, V s → W s}
    (hf : ∀ s, Injective (f s)) (c : RelCoord S V) (A : CoordLatentIndex c) :
    CoordLatentIndex.toLatentIndex (CoordLatentIndex.congrMap hf c A) =
      LatentIndex.map f (CoordLatentIndex.toLatentIndex A) :=
  Subtype.ext rfl


end RelSignature

/-! ### Examples: binary, diagonal, ternary, bipartite -/

namespace RelSignature.PatternExamples

open RelSignature

open scoped Classical

/-- A local one-sort binary signature (kept local so this generic file does not depend on
the directed development; the directed `digraphSig` has the same shape). -/
abbrev binarySig : RelSignature where
  Srt := Unit
  Rel := Unit
  arity := fun _ => 2
  argSort := fun _ _ => ()

/-- The binary coordinate at an ordered pair. -/
@[reducible] def binaryExample (i j : ℕ) : RelCoord binarySig fun _ => ℕ := ⟨(), ![i, j]⟩

/-- Binary off-diagonal: distinct vertices give the discrete pattern — the two positions are
inequivalent. -/
example {i j : ℕ} (h : i ≠ j) : ¬ (binaryExample i j).pattern 0 1 := by
  intro hcon
  exact h (congrArg (fun v : Σ _ : Unit, ℕ => v.2) hcon)

/-- Binary diagonal: the loop coordinate identifies its two positions. -/
example (i : ℕ) : (binaryExample i i).pattern 0 1 := rfl

/-- Binary supports: an off-diagonal coordinate reads two vertices, a loop reads one. -/
example {i j : ℕ} (h : i ≠ j) : (binaryExample i j).support.card = 2 := by
  have hset : (binaryExample i j).support = {⟨(), i⟩, ⟨(), j⟩} := by
    ext v
    rw [RelCoord.mem_support_iff]
    constructor
    · rintro ⟨a, rfl⟩
      fin_cases a
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · intro hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ⟨0, rfl⟩
      · rw [Finset.mem_singleton] at hv
        subst hv
        exact ⟨1, rfl⟩
  rw [hset, Finset.card_insert_of_notMem (by simp [h]), Finset.card_singleton]

example (i : ℕ) : (binaryExample i i).support.card = 1 := by
  have hset : (binaryExample i i).support = {⟨(), i⟩} := by
    ext v
    rw [RelCoord.mem_support_iff]
    constructor
    · rintro ⟨a, rfl⟩
      fin_cases a
      · exact Finset.mem_singleton_self _
      · exact Finset.mem_singleton_self _
    · intro hv
      rw [Finset.mem_singleton] at hv
      subst hv
      exact ⟨0, rfl⟩
  rw [hset]
  exact Finset.card_singleton _

/-- A one-sort ternary signature. -/
abbrev ternarySig : RelSignature where
  Srt := Unit
  Rel := Unit
  arity := fun _ => 3
  argSort := fun _ _ => ()

/-- The running ternary coordinate `(0, 1, 0)`: a repeated entry. -/
@[reducible] def ternaryExample : RelCoord ternarySig fun _ => ℕ := ⟨(), ![0, 1, 0]⟩

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
@[reducible] def bipartiteExample (n : ℕ) : RelCoord bipartiteSig fun _ => ℕ := ⟨(), ![n, n]⟩

/-- **Sort-awareness**: in the bipartite signature, equal *raw* vertex values in the two
positions are still inequivalent — the sorts differ, so the tagged values differ. -/
example (n : ℕ) : ¬ (bipartiteExample n).pattern 0 1 := by
  intro hcon
  exact Bool.false_ne_true (congrArg Sigma.fst hcon)

/-- Correspondingly, the bipartite support of the equal-raw-values coordinate still has two
elements: one per sort. -/
example (n : ℕ) : (bipartiteExample n).support.card = 2 := by
  have hset : (bipartiteExample n).support = {⟨false, n⟩, ⟨true, n⟩} := by
    ext v
    rw [RelCoord.mem_support_iff]
    constructor
    · rintro ⟨a, rfl⟩
      fin_cases a
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · intro hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ⟨0, rfl⟩
      · rw [Finset.mem_singleton] at hv
        subst hv
        exact ⟨1, rfl⟩
  rw [hset, Finset.card_insert_of_notMem (by simp), Finset.card_singleton]

end RelSignature.PatternExamples
