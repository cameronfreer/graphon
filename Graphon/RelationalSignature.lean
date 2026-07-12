/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Basic

/-!
# Relational signatures and their structure carriers (AHK umbrella #103, R0 design checkpoint)

A deliberately small, dependency-light checkpoint (issue #110) that locks the carrier design
for the generic Aldous–Hoover–Kallenberg program **before** R1/R2 build size vectors,
sortwise embeddings, topology, and measure theory on top of it. There is **no topology, no
probability, no projective extension, and no extremality here** — only the data design and
the sortwise-map machinery that the later layers will reuse, so the carrier decision stays
easy to revise.

## Contents

* `RelSignature` — a purely relational, multi-sorted signature (no function symbols, no
  constants): a type of sort labels, a type of relation symbols, an arity, and the sort of
  each argument position;
* `RelCoord` / `RelStructure` — the coordinate type of a structure over a sort-indexed value
  family, and a Boolean-valued structure on those coordinates;
* `NoNullary` — the arity-positivity hypothesis, kept **external** (a predicate, not a field
  of `RelSignature`) so nullary relations can be admitted later without redesigning the
  signature;
* `Vfinite` / `Vinfinite` — the finite (size-vector) and infinite (`ℕ`) value carriers;
* `RelCoord.map` / `RelStructure.comap` — the action of a **sortwise** family of maps
  `∀ s, V s → W s` on coordinates and on structures (the exact machinery R1/R2 relabelling
  and consistency will rely on);
* worked `Examples`: the one-sort binary **digraph** signature, the two-sort binary
  **bipartite** signature, and a one-sort **ternary** signature with a repeated-coordinate
  tuple `(i, i, j)` — the latter exercises the equality-pattern design that is the genuinely
  new difficulty at arbitrary arity.

## Design decisions locked here

* **Sort-label field name.** `Sort` is a reserved token in Lean 4, so the field is named
  `Srt` (accessed as `S.Srt`). This is the only cosmetic deviation from the `Σ.Sort`
  notation used in the issue discussion.
* **Universes.** The sort-label type and the relation-symbol type share a single universe
  `Type u` (`RelSignature : Type (u+1)`); the value carrier `V : S.Srt → Type v` uses an
  independent universe `v`. A split `Type u`/`Type u'` for sorts vs. relations is possible
  but unnecessary (it only ever appears as `max u u'`) and trips the `checkUnivs` linter, so
  it is deferred. The worked examples all live in `Type` (universe `0`).
* **Boolean relations.** `RelStructure` is `RelCoord → Bool`. Finite-valued relations are a
  later extension; Boolean is already the full campaign.
* **Nullary relations.** Admitted structurally (an `arity R = 0` relation is legal data), but
  the intended theorems assume `NoNullary`; the empty-tag / global-latent `ξ_∅` behaviour is
  restored only in R5 (#108).

## External representation theorem this program targets (R0 acceptance item)

The functional representation formalized in R4 (#107) is the Aldous–Hoover–Kallenberg
theorem. In **Kallenberg, *Probabilistic Symmetries and Invariance Principles* (Springer,
2005), §7.5**: **Theorem 7.22** is the *jointly* exchangeable representation of an array
`X : ℕ^d → E` as `X_J = f((ξ_{J'})_{J' ⊆ J})` (measurable `f`, i.i.d. `U[0,1]` latents `ξ`
indexed by the **subsets** `J' ⊆ J`), and **Corollary 7.23** is its *separately*
exchangeable, fixed-dimensional consequence. The general multi-sorted action here **mixes
joint and separate symmetries**, so it is not literally either single statement — R1/R2 make
the exact mixture explicit. For relational structures the latents are indexed by finite
subsets of *tagged vertices* `Σ s : S.Srt, ℕ`; **R4 formalizes the dissociated
specialization without the empty-subset latent `ξ_∅`**, and R5 (#108) restores the full
general-law form with `ξ_∅`. Locating and confirming these exact statements against the
printing is part of R0's acceptance.
-/

universe u v w

/-- A **purely relational, multi-sorted signature**: sort labels `Srt`, relation symbols
`Rel`, an `arity` for each relation, and the sort `argSort R i` of each argument position
`i` of `R`. No function symbols or constants. (The field is `Srt` because `Sort` is a
reserved token in Lean 4.) -/
structure RelSignature where
  /-- The type of sort labels. -/
  Srt : Type u
  /-- The type of relation symbols. -/
  Rel : Type u
  /-- The arity of each relation symbol. -/
  arity : Rel → ℕ
  /-- The sort of each argument position of each relation. -/
  argSort : (R : Rel) → Fin (arity R) → Srt

namespace RelSignature

/-- **A coordinate of a relational structure** over the sort-indexed value family `V`: a
relation symbol `R` together with a value `V (argSort R i)` in each argument position `i`. -/
abbrev RelCoord (S : RelSignature) (V : S.Srt → Type v) : Type _ :=
  Σ R : S.Rel, (i : Fin (S.arity R)) → V (S.argSort R i)

/-- **A relational structure** over the value family `V`: a Boolean value at every
coordinate (whether the tuple stands in the relation). -/
def RelStructure (S : RelSignature) (V : S.Srt → Type v) : Type _ := RelCoord S V → Bool

/-- **Arity positivity**, kept as an external predicate rather than a field of
`RelSignature`, so nullary relations can be added later without changing the signature. -/
def NoNullary (S : RelSignature) : Prop := ∀ R : S.Rel, 0 < S.arity R

/-- The **finite value carrier** for a size vector `n : S.Srt → ℕ`: sort `s` has `n s`
vertices. -/
abbrev Vfinite {S : RelSignature} (n : S.Srt → ℕ) : S.Srt → Type := fun s => Fin (n s)

/-- The **infinite value carrier**: every sort has vertex set `ℕ`. -/
abbrev Vinfinite (S : RelSignature) : S.Srt → Type := fun _ => ℕ

/-- The **action of a sortwise family of maps** `f : ∀ s, V s → W s` on coordinates: relabel
each argument by the map for its sort, keeping the relation symbol. This is the coordinate
half of the relabelling / consistency machinery R1 and R2 will build on. -/
def RelCoord.map {S : RelSignature} {V W : S.Srt → Type*} (f : ∀ s, V s → W s) :
    RelCoord S V → RelCoord S W :=
  fun c => ⟨c.1, fun i => f (S.argSort c.1 i) (c.2 i)⟩

/-- The **pullback of a structure along a sortwise family of maps**: `comap f g` asks
whether the `f`-image tuple stands in `g`. (For a sortwise permutation this is the generic
relabelling action.) -/
def RelStructure.comap {S : RelSignature} {V W : S.Srt → Type*} (f : ∀ s, V s → W s) :
    RelStructure S W → RelStructure S V :=
  fun g c => g (RelCoord.map f c)

@[simp] theorem RelStructure.comap_apply {S : RelSignature} {V W : S.Srt → Type*}
    (f : ∀ s, V s → W s) (g : RelStructure S W) (c : RelCoord S V) :
    RelStructure.comap f g c = g (RelCoord.map f c) := rfl

@[simp] theorem RelCoord.map_fst {S : RelSignature} {V W : S.Srt → Type*} (f : ∀ s, V s → W s)
    (c : RelCoord S V) : (RelCoord.map f c).1 = c.1 := rfl

/-! ### Worked examples

The example signatures are `abbrev`s (reducible) so that the acceptance checks reduce by
`rfl`; R1 will introduce its own opaque definitions. -/

namespace Examples

/-- **Directed graphs**: one sort, one binary relation, ordered arguments, diagonal allowed
(the R1 instance underlying #85). -/
abbrev digraphSig : RelSignature where
  Srt := Unit
  Rel := Unit
  arity := fun _ => 2
  argSort := fun _ _ => ()

/-- **Bipartite / separately exchangeable**: two sorts, one binary relation whose first
argument is the first sort and second argument the second sort. -/
abbrev bipartiteSig : RelSignature where
  Srt := Bool
  Rel := Unit
  arity := fun _ => 2
  argSort := fun _ => ![false, true]

/-- **A one-sort ternary relation** — the smallest signature that exercises repeated
argument coordinates (the equality-pattern design of R4/#107). -/
abbrev ternarySig : RelSignature where
  Srt := Unit
  Rel := Unit
  arity := fun _ => 3
  argSort := fun _ _ => ()

/-- A ternary coordinate `(i, i, j)` with the first two arguments **equal** — the design
admits repeated coordinates, and their equality pattern is intrinsic to the tuple. -/
abbrev ternaryRepeated (i j : ℕ) : RelCoord ternarySig (Vinfinite ternarySig) :=
  ⟨(), ![i, i, j]⟩

/-- The repeated coordinate really does carry the same vertex in positions `0` and `1`. -/
example (i j : ℕ) : (ternaryRepeated i j).2 0 = (ternaryRepeated i j).2 1 := rfl

/-- A sortwise map **preserves existing equalities**: positions `0` and `1` were equal in
`(i, i, j)`, so they stay equal after `RelCoord.map`. (A noninjective map may also *create*
new coincidences; it does not preserve the exact partition — that needs injectivity, below.) -/
example (f : ℕ → ℕ) (i j : ℕ) :
    (RelCoord.map (S := ternarySig) (fun _ => f) (ternaryRepeated i j)).2 0 =
      (RelCoord.map (S := ternarySig) (fun _ => f) (ternaryRepeated i j)).2 1 := rfl

/-- **An injective sortwise map preserves the exact equality partition**: two argument
positions are equal after mapping iff they were equal before (`Function.Injective.eq_iff`).
This is the property R4's representing functions rely on. -/
example {f : ℕ → ℕ} (hf : Function.Injective f) (i j : ℕ) (a b : Fin 3) :
    ((RelCoord.map (S := ternarySig) (fun _ => f) (ternaryRepeated i j)).2 a =
        (RelCoord.map (S := ternarySig) (fun _ => f) (ternaryRepeated i j)).2 b) ↔
      ((ternaryRepeated i j).2 a = (ternaryRepeated i j).2 b) := by
  simp only [RelCoord.map]
  exact hf.eq_iff

/-- The digraph, bipartite, and ternary signatures satisfy arity positivity. -/
example : NoNullary digraphSig := fun _ => by show 0 < 2; decide
example : NoNullary bipartiteSig := fun _ => by show 0 < 2; decide
example : NoNullary ternarySig := fun _ => by show 0 < 3; decide

/-- An example bipartite coordinate: the ordered pair `(a, b)` with `a` in the first sort
and `b` in the second. -/
abbrev bipartiteEdge (a b : ℕ) : RelCoord bipartiteSig (Vinfinite bipartiteSig) :=
  ⟨(), ![a, b]⟩

end Examples

end RelSignature
