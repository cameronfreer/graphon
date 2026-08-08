/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelationalSignature
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic

/-!
# Sortwise actions on relational structures (AHK umbrella #103, R1a)

The combinatorial layer of the generic Aldous–Hoover–Kallenberg carrier (issue #104),
generalizing the finite-restriction / relabelling / padding operations of
`Graphon/InfiniteGraph.lean` to arbitrary multi-sorted relational signatures. **No topology
or measure theory yet** — the Boolean-product equivalence and the standard-Borel / cylinder
layer are R1b; the projective extension is R2.

Everything is built from the sortwise pullback `RelStructure.comap` of R0:

* `RelCoord.map_id` / `RelCoord.map_comp`, `RelStructure.comap_id` / `RelStructure.comap_comp`
  — functoriality of the coordinate pushforward and the structure pullback;
* `RelStructure.restrict` — restriction to a sub-carrier along a sortwise family of
  embeddings; `RelStructure.relabel` — relabelling by a sortwise family of permutations;
* `RelStructure.restrictFin n` — the induced structure on the first `n s` vertices of each
  sort (the `restrictFin` analog); `RelStructure.restrictLE` — restriction between size
  vectors `n ≤ m`;
* `RelStructure.pad` — padding a finite structure into a larger carrier along sortwise
  embeddings (the `padFin` analog: the padded structure holds only on tuples all of whose
  arguments come from the sub-carrier), with `RelStructure.restrict_pad` (padding is a
  section of restriction — the `restrictFin_padFin` analog);
* `RelStructure.restrictLE_restrictFin` / `RelStructure.restrictLE_restrictLE` — restrictions
  compose (the `restrictFin_comap` analog).
-/

namespace RelSignature

variable {S : RelSignature}

/-! ### Functoriality -/

@[simp] theorem RelCoord.map_id {V : S.Srt → Type*} (c : RelCoord S V) :
    RelCoord.map (fun _ => id) c = c := rfl

theorem RelCoord.map_comp {V W X : S.Srt → Type*} (f : ∀ s, V s → W s) (g : ∀ s, W s → X s)
    (c : RelCoord S V) :
    RelCoord.map (fun s => g s ∘ f s) c = RelCoord.map g (RelCoord.map f c) := rfl

@[simp] theorem RelStructure.comap_id {V : S.Srt → Type*} (σ : RelStructure S V) :
    RelStructure.comap (fun _ => id) σ = σ := rfl

theorem RelStructure.comap_comp {V W X : S.Srt → Type*} (f : ∀ s, V s → W s)
    (g : ∀ s, W s → X s) (σ : RelStructure S X) :
    RelStructure.comap (fun s => g s ∘ f s) σ =
      RelStructure.comap f (RelStructure.comap g σ) := rfl

/-! ### Restriction and relabelling -/

/-- **Restriction to a sub-carrier** along a sortwise family of embeddings. -/
def RelStructure.restrict {V W : S.Srt → Type*} (e : ∀ s, V s ↪ W s) :
    RelStructure S W → RelStructure S V :=
  RelStructure.comap fun s => (e s : V s → W s)

/-- **Relabelling** by a sortwise family of permutations. -/
def RelStructure.relabel {V : S.Srt → Type*} (σ : ∀ s, Equiv.Perm (V s)) :
    RelStructure S V → RelStructure S V :=
  RelStructure.comap fun s => (σ s : V s → V s)

/-- **The moved-window law**: restriction along `e` after an *arbitrary* relabeling is
restriction along the moved window `(e s).trans (ρ s).toEmbedding`. Definitional. A mixed
permutation does not commute with restriction to the same half — but it does move the
restricted window, and this is the form the mixed-window marginal theorem consumes. -/
theorem RelStructure.restrict_relabel {V W : S.Srt → Type*} (e : ∀ s, V s ↪ W s)
    (ρ : ∀ s, Equiv.Perm (W s)) (X : RelStructure S W) :
    RelStructure.restrict e (RelStructure.relabel ρ X) =
      RelStructure.restrict (fun s => (e s).trans (ρ s).toEmbedding) X := rfl

/-- **Finite restriction**: the structure induced on the first `n s` vertices of each sort. -/
def RelStructure.restrictFin (n : S.Srt → ℕ) :
    RelStructure S (Vinfinite S) → RelStructure S (Vfinite n) :=
  RelStructure.comap fun s => (Fin.valEmbedding : Fin (n s) → ℕ)

/-- **Restriction between size vectors** `n ≤ m`. -/
def RelStructure.restrictLE {n m : S.Srt → ℕ} (h : ∀ s, n s ≤ m s) :
    RelStructure S (Vfinite m) → RelStructure S (Vfinite n) :=
  RelStructure.comap fun s => (Fin.castLEEmb (h s) : Fin (n s) → Fin (m s))

/-! ### Padding -/

open scoped Classical in
/-- **Padding** a finite structure into a larger carrier along a sortwise family of
embeddings: the padded structure holds on a tuple exactly when every argument comes from the
sub-carrier (is in the range of the embedding) and the original structure holds on the
pulled-back tuple. This is the relational analog of `SimpleGraph.map` along an embedding
(`padFin`). -/
noncomputable def RelStructure.pad {V W : S.Srt → Type*} (e : ∀ s, V s ↪ W s) :
    RelStructure S V → RelStructure S W :=
  fun σ d =>
    if h : ∀ i, d.2 i ∈ Set.range (e (S.argSort d.1 i)) then
      σ ⟨d.1, fun i => (h i).choose⟩
    else false

/-- **Restriction undoes padding** (`restrictFin_padFin` analog): padding a structure along a
sortwise embedding family and then restricting back recovers the original structure. -/
@[simp] theorem RelStructure.restrict_pad {V W : S.Srt → Type*} (e : ∀ s, V s ↪ W s)
    (σ : RelStructure S V) : RelStructure.restrict e (RelStructure.pad e σ) = σ := by
  classical
  funext c
  show RelStructure.pad e σ (RelCoord.map (fun s => (e s : V s → W s)) c) = σ c
  have hmem : ∀ i, (RelCoord.map (fun s => (e s : V s → W s)) c).2 i ∈
      Set.range (e (S.argSort (RelCoord.map (fun s => (e s : V s → W s)) c).1 i)) :=
    fun i => ⟨c.2 i, rfl⟩
  rw [RelStructure.pad, dif_pos hmem]
  congr 1
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext i
  exact (e _).injective (hmem i).choose_spec

/-! ### Restrictions compose -/

/-- **Restrictions between size vectors compose** (the `restrictFin_comap` analog). -/
theorem RelStructure.restrictLE_restrictLE {n m k : S.Srt → ℕ}
    (hnm : ∀ s, n s ≤ m s) (hmk : ∀ s, m s ≤ k s) (σ : RelStructure S (Vfinite k)) :
    RelStructure.restrictLE hnm (RelStructure.restrictLE hmk σ) =
      RelStructure.restrictLE (fun s => (hnm s).trans (hmk s)) σ := by
  rw [RelStructure.restrictLE, RelStructure.restrictLE, RelStructure.restrictLE,
    ← RelStructure.comap_comp]
  congr 1

/-- **A finite restriction factors through any coarser one** (the `restrictFin_comap`
analog): restricting the `m`-restriction down to `n ≤ m` equals the direct `n`-restriction. -/
theorem RelStructure.restrictLE_restrictFin {n m : S.Srt → ℕ} (h : ∀ s, n s ≤ m s)
    (σ : RelStructure S (Vinfinite S)) :
    RelStructure.restrictLE h (RelStructure.restrictFin m σ) = RelStructure.restrictFin n σ := by
  rw [RelStructure.restrictLE, RelStructure.restrictFin, RelStructure.restrictFin,
    ← RelStructure.comap_comp]
  congr 1

/-- Finite restriction is `restrict` along the value embeddings, so padding along them is a
section of `restrictFin`. -/
@[simp] theorem RelStructure.restrictFin_pad (n : S.Srt → ℕ) (σ : RelStructure S (Vfinite n)) :
    RelStructure.restrictFin n
        (RelStructure.pad (fun s => (Fin.valEmbedding : Fin (n s) ↪ ℕ)) σ) = σ :=
  RelStructure.restrict_pad _ σ

/-- **Restriction of a padding along composable embeddings**: padding along `e` then
restricting along `g ∘ e` recovers restriction along `g` (generalizes `restrict_pad`, the
case `g = id`). -/
theorem restrict_comp_pad {U V W : S.Srt → Type*} (e : ∀ s, V s ↪ W s) (g : ∀ s, U s ↪ V s)
    (σ : RelStructure S V) :
    RelStructure.restrict (fun s => (g s).trans (e s)) (RelStructure.pad e σ) =
      RelStructure.restrict g σ := by
  classical
  funext c
  show RelStructure.pad e σ (RelCoord.map (fun s => ((g s).trans (e s) : U s → W s)) c)
    = σ (RelCoord.map (fun s => (g s : U s → V s)) c)
  have hmem : ∀ i, (RelCoord.map (fun s => ((g s).trans (e s) : U s → W s)) c).2 i ∈
      Set.range (e (S.argSort (RelCoord.map (fun s => ((g s).trans (e s) : U s → W s)) c).1 i)) :=
    fun i => ⟨g _ (c.2 i), rfl⟩
  rw [RelStructure.pad, dif_pos hmem]
  congr 1
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext i
  exact (e _).injective (hmem i).choose_spec

/-- The finite restriction of a diagonal padding is a restriction between size vectors. -/
theorem restrictFin_pad_diag {n : S.Srt → ℕ} {N : ℕ} (h : ∀ s, n s ≤ N)
    (σ : RelStructure S (Vfinite fun _ => N)) :
    RelStructure.restrictFin n (RelStructure.pad (fun _ => (Fin.valEmbedding : Fin N ↪ ℕ)) σ)
      = RelStructure.restrictLE h σ := by
  have hemb : (fun s => (Fin.valEmbedding : Fin (n s) ↪ ℕ))
      = (fun s => (Fin.castLEEmb (h s)).trans (Fin.valEmbedding : Fin N ↪ ℕ)) := by
    funext s; ext x; simp [Fin.castLEEmb]
  show RelStructure.restrict (fun s => (Fin.valEmbedding : Fin (n s) ↪ ℕ))
      (RelStructure.pad _ σ) = RelStructure.restrictLE h σ
  rw [hemb]; exact restrict_comp_pad _ _ σ

end RelSignature
