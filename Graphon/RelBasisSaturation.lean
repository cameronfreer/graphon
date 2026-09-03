/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelBasisSyntax
import Graphon.RelErgodicExtreme

/-!
# The saturated atom family (R4 converse piece 3, #107)

The atoms of the coherent basis: one **seed** family of events per finite tagged vertex set,
saturated by the finitely supported relabelings.

## The construction

An atom is a pair `(seed, f)` where `seed` is a seed event anchored at some finite `A` and `f`
is a sortwise-injective reassignment of the vertices of `A`. Its anchor is the reassigned vertex
set and its event is `relabel τ ⁻¹' seed` for any finitely supported `τ` agreeing with `f` on
`A` — and **any** such `τ` gives the same event, because two finitely supported permutations
agreeing on `A` differ by one fixing `A`, which fixes every `fixingAlgebra A`-event
(`relabel_preimage_eq_of_agree`). This is **orbit compression**: the orbit of a seed under the
finitely supported relabelings is indexed by restrictions to its anchor, which is countable under
`[Countable S.Srt]` even though `FinSuppPerm S` itself is countable only under finitely many
sorts. The full finitely supported action is kept, as post-composition on the reassignment:
`act_one` and `act_mul` are definitional, the anchor law is `Finset.image_image`, and the event
law is `relabel_preimage_relabel_preimage` followed by orbit compression.

Saturation is built into the index rather than imposed afterwards: every relabel of every seed
is already an atom, so the family is closed under the action *by construction*, with no orbit
representatives and no choices to make equivariant.

## Contents

* `RelSignature.SeedData` — a countable family of `fixingAlgebra A`-events for each finite `A`,
  the structural input to the construction, produced from separability of the law by `seedDataOf`
  further down this file;
* `RelSignature.SaturatedAtom` and its `anchor` / `event` / `act`, with the four atom-level laws
  `BasisExpr` needs, plus `Countable`;
* `RelSignature.InfiniteRelExchangeableLaw.nonempty_coherentBasis` — the assembly: every
  exchangeable law has a coherent basis, under `[Countable S.Srt] [Countable S.Rel]` alone.
-/

open MeasureTheory MeasurableSpace

namespace RelSignature

variable {S : RelSignature}

/-! ### Countability of the relabeling subgroup -/

/-- The finitely supported sortwise permutations form a countable group under finitely many
sorts — the subgroup itself lives beside `SortwiseFinSupp` in `Graphon.RelInvariantAction`;
countability is recorded here, where `Fintype S.Srt` is in play. -/
instance [Fintype S.Srt] : Countable (FinSuppPerm S) :=
  (countable_setOf_sortwiseFinSupp (S := S)).to_subtype

/-! ### Seed data -/

/-- **Seed data**: a countable family of events for each finite tagged vertex set, each
measurable for the corresponding fixing algebra.

This is the input to the saturated construction, kept abstract so that the algebra below is
independent of *how* the seeds are produced. The seeds that matter come from separability of the
law — `MeasureTheory.isSeparable_trim` applied to `fixingAlgebra A` — and carry measure density
as well; that is supplied separately, since none of the structural laws need it. -/
structure SeedData (S : RelSignature) where
  /-- The seed events available over `A`. -/
  seed : Finset (Σ s : S.Srt, Vinfinite S s) → Set (Set (RelStructure S (Vinfinite S)))
  /-- Countably many seeds over each `A`. -/
  countable_seed : ∀ A, (seed A).Countable
  /-- Each seed over `A` is a `fixingAlgebra A`-event. -/
  seed_mem : ∀ A, ∀ E ∈ seed A, MeasurableSet[RelStructure.fixingAlgebra A] E

namespace SeedData

variable (D : SeedData S)

/-- The seeds, bundled with the vertex set they are anchored at. -/
def Index := Σ A : Finset (Σ s : S.Srt, Vinfinite S s),
  {E : Set (RelStructure S (Vinfinite S)) // E ∈ D.seed A}

instance [Countable S.Srt] : Countable D.Index := by
  haveI : ∀ A, Countable {E : Set (RelStructure S (Vinfinite S)) // E ∈ D.seed A} :=
    fun A => (D.countable_seed A).to_subtype
  unfold Index
  infer_instance

end SeedData

/-! ### Seed data from separability -/

section OfSeparable

variable [Countable S.Rel] (M : InfiniteRelExchangeableLaw S)

/-- The countable measure-dense family for `fixingAlgebra A` supplied by separability of the
law. `[Countable S.Rel]` alone gives `IsSeparable M.law`; `isSeparable_trim` transports that to
each fixing algebra, and this is its chosen witness. -/
noncomputable def seedOf (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Set (Set (RelStructure S (Vinfinite S))) :=
  (MeasureTheory.isSeparable_trim (μ := (M.law : Measure (RelStructure S (Vinfinite S))))
    (RelStructure.fixingAlgebra_le A)).1.choose

theorem countable_seedOf (A : Finset (Σ s : S.Srt, Vinfinite S s)) : (seedOf M A).Countable :=
  (MeasureTheory.isSeparable_trim (μ := (M.law : Measure (RelStructure S (Vinfinite S))))
    (RelStructure.fixingAlgebra_le A)).1.choose_spec.1

/-- **The density carried alongside the seeds.** Kept out of `SeedData`, which stays structural:
the atom-level laws never look at the law, and only the final `CoherentBasis.density` field
does. -/
theorem measureDense_seedOf (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    @Measure.MeasureDense (RelStructure S (Vinfinite S)) (RelStructure.fixingAlgebra A)
      ((M.law : Measure (RelStructure S (Vinfinite S))).trim (RelStructure.fixingAlgebra_le A))
      (seedOf M A) :=
  (MeasureTheory.isSeparable_trim (μ := (M.law : Measure (RelStructure S (Vinfinite S))))
    (RelStructure.fixingAlgebra_le A)).1.choose_spec.2

/-- **The seed data of a law**: the separability-supplied families, packaged structurally. -/
noncomputable def seedDataOf : SeedData S where
  seed := seedOf M
  countable_seed := countable_seedOf M
  seed_mem := fun A => @Measure.MeasureDense.measurable (RelStructure S (Vinfinite S))
    (RelStructure.fixingAlgebra A) _ _ (measureDense_seedOf M A)

@[simp] theorem seedDataOf_seed (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    (seedDataOf M).seed A = seedOf M A := rfl

end OfSeparable

/-! ### The saturated atoms, orbit-compressed

The orbit of a seed anchored at `A` under the finitely supported relabelings is determined by the
restriction of the relabeling to `A`: two finitely supported permutations agreeing on `A` differ
by one fixing `A`, which fixes every `fixingAlgebra A`-event. So an atom is indexed not by a
permutation but by its restriction to the anchor — a sortwise-injective assignment of vertices to
the finitely many vertices of `A` — which is countable under `[Countable S.Srt]` even though
`FinSuppPerm S` itself is not. The full finitely supported action is kept; only the orbit
indexing changes. -/

/-- A sortwise-injective reassignment of the vertices of `A`. -/
def SortwiseInjOn (A : Finset (Σ s : S.Srt, Vinfinite S s)) (f : {v // v ∈ A} → ℕ) : Prop :=
  ∀ v w, v.1.1 = w.1.1 → f v = f w → v = w

/-- **A saturated atom**: a seed together with a sortwise-injective reassignment of its anchor's
vertices. Saturation is part of the index, so the atom family is closed under the relabeling
action by construction — no orbit representatives, and nothing to make equivariant after the
fact. -/
def SaturatedAtom (D : SeedData S) :=
  Σ i : D.Index, {f : {v // v ∈ i.1} → ℕ // SortwiseInjOn i.1 f}

namespace SaturatedAtom

variable {D : SeedData S}

instance [Countable S.Srt] : Countable (SaturatedAtom D) := by
  unfold SaturatedAtom
  infer_instance

open scoped Classical in
/-- A global sortwise injection agreeing with `f` on `A`: `f` on `A`, and a shift above all the
values of `f` elsewhere. -/
private noncomputable def globalInj {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    {f : {v // v ∈ A} → ℕ} (hf : SortwiseInjOn A f) (s : S.Srt) : Vinfinite S s ↪ Vinfinite S s :=
  ⟨fun x => if h : (⟨s, x⟩ : Σ s : S.Srt, Vinfinite S s) ∈ A then f ⟨⟨s, x⟩, h⟩
      else x + (A.attach.sup f + 1), by
    intro a b hab
    simp only at hab
    have hlt : ∀ (v : Σ s : S.Srt, Vinfinite S s) (hv : v ∈ A), f ⟨v, hv⟩ < A.attach.sup f + 1 :=
      fun v hv => Nat.lt_succ_of_le (Finset.le_sup (f := f) (Finset.mem_attach _ ⟨v, hv⟩))
    by_cases ha : (⟨s, a⟩ : Σ s : S.Srt, Vinfinite S s) ∈ A <;>
      by_cases hb : (⟨s, b⟩ : Σ s : S.Srt, Vinfinite S s) ∈ A
    · rw [dif_pos ha, dif_pos hb] at hab
      exact congrArg (fun v : Σ s : S.Srt, Vinfinite S s => v.2)
        (congrArg Subtype.val (hf ⟨⟨s, a⟩, ha⟩ ⟨⟨s, b⟩, hb⟩ rfl hab))
    · rw [dif_pos ha, dif_neg hb] at hab
      have h1 := hlt ⟨s, a⟩ ha
      have h2 : f ⟨⟨s, a⟩, ha⟩ = (b : ℕ) + (A.attach.sup f + 1) := hab
      exact absurd h1 (Nat.not_lt.mpr (h2 ▸ Nat.le_add_left _ _))
    · rw [dif_neg ha, dif_pos hb] at hab
      have h1 := hlt ⟨s, b⟩ hb
      have h2 : (a : ℕ) + (A.attach.sup f + 1) = f ⟨⟨s, b⟩, hb⟩ := hab
      exact absurd h1 (Nat.not_lt.mpr (h2 ▸ Nat.le_add_left _ _))
    · rw [dif_neg ha, dif_neg hb] at hab
      have h2 : (a : ℕ) + (A.attach.sup f + 1) = (b : ℕ) + (A.attach.sup f + 1) := hab
      exact Nat.add_right_cancel h2⟩

/-- A finitely supported relabeling agreeing with the reassignment on the anchor. -/
noncomputable def extendPerm {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    {f : {v // v ∈ A} → ℕ} (hf : SortwiseInjOn A f) : FinSuppPerm S :=
  Classical.choose (exists_finSuppPerm_agree_on_finset (globalInj hf) A)

theorem extendPerm_apply {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    {f : {v // v ∈ A} → ℕ} (hf : SortwiseInjOn A f) (v : Σ s : S.Srt, Vinfinite S s)
    (hv : v ∈ A) : (extendPerm hf).1 v.1 v.2 = f ⟨v, hv⟩ := by
  classical
  have h := Classical.choose_spec (exists_finSuppPerm_agree_on_finset (globalInj hf) A) v hv
  unfold extendPerm
  rw [h]
  show (if h : (⟨v.1, v.2⟩ : Σ s : S.Srt, Vinfinite S s) ∈ A then f ⟨⟨v.1, v.2⟩, h⟩
    else v.2 + (A.attach.sup f + 1)) = f ⟨v, hv⟩
  rw [dif_pos (by simpa using hv)]

/-- **Orbit compression**: two finitely supported relabelings agreeing on `A` pull a
`fixingAlgebra A`-event back to the same event. -/
theorem relabel_preimage_eq_of_agree {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    {E : Set (RelStructure S (Vinfinite S))} (hE : MeasurableSet[RelStructure.fixingAlgebra A] E)
    (τ τ' : FinSuppPerm S) (h : ∀ v ∈ A, τ.1 v.1 v.2 = τ'.1 v.1 v.2) :
    RelStructure.relabel τ.1 ⁻¹' E = RelStructure.relabel τ'.1 ⁻¹' E := by
  have hπ : SortwiseFixing (S := S) A (τ⁻¹ * τ').1 := ⟨(τ⁻¹ * τ').2, fun v hv => by
    show (τ.1 v.1)⁻¹ (τ'.1 v.1 v.2) = v.2
    rw [← h v hv]
    exact (τ.1 v.1).symm_apply_apply v.2⟩
  have hfix := hE.2 _ hπ
  conv_rhs => rw [show τ' = τ * (τ⁻¹ * τ') from by group]
  show _ = RelStructure.relabel (fun s => τ.1 s * (τ⁻¹ * τ').1 s) ⁻¹' E
  rw [← RelStructure.relabel_preimage_relabel_preimage, hfix]

open scoped Classical in
/-- The anchor of an atom: the seed's vertex set, reassigned. -/
noncomputable def anchor (a : SaturatedAtom D) : Finset (Σ s : S.Srt, Vinfinite S s) :=
  a.1.1.attach.image fun v => ⟨v.1.1, a.2.1 v⟩

/-- The event of an atom: the seed event, pulled back along an extension of the reassignment. -/
noncomputable def event (a : SaturatedAtom D) : Set (RelStructure S (Vinfinite S)) :=
  RelStructure.relabel (extendPerm a.2.2).1 ⁻¹' a.1.2.1

/-- **The action: post-composition on the reassignment.** -/
def act (σ : FinSuppPerm S) (a : SaturatedAtom D) : SaturatedAtom D :=
  ⟨a.1, ⟨fun v => σ.1 v.1.1 (a.2.1 v), fun v w hs hfw =>
    a.2.2 v w hs (by
      have h1 : σ.1 v.1.1 (a.2.1 v) = σ.1 w.1.1 (a.2.1 w) := hfw
      rw [← hs] at h1
      exact (σ.1 v.1.1).injective h1)⟩⟩

theorem act_one (a : SaturatedAtom D) : act 1 a = a := rfl

theorem act_mul (σ τ : FinSuppPerm S) (a : SaturatedAtom D) :
    act (σ * τ) a = act σ (act τ a) := rfl

open scoped Classical in
/-- The anchor transports by the image map. -/
theorem anchor_act (σ : FinSuppPerm S) (a : SaturatedAtom D) :
    anchor (act σ a) = (anchor a).image (Sigma.map id fun s => ⇑(σ.1 s)) := by
  show a.1.1.attach.image _ = (a.1.1.attach.image _).image _
  rw [Finset.image_image]
  rfl

open scoped Classical in
/-- The anchor is the image of the seed's vertex set under any extension of the
reassignment. -/
theorem anchor_eq_image (a : SaturatedAtom D) :
    anchor a = a.1.1.image (Sigma.map id fun s => ⇑((extendPerm a.2.2).1 s)) := by
  classical
  ext v
  rw [anchor, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨w, -, rfl⟩
    refine ⟨w.1, w.2, ?_⟩
    show (⟨w.1.1, (extendPerm a.2.2).1 w.1.1 w.1.2⟩ : Σ s : S.Srt, Vinfinite S s) =
      ⟨w.1.1, a.2.1 w⟩
    rw [extendPerm_apply a.2.2 w.1 w.2]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨w, hw⟩, Finset.mem_attach _ _, ?_⟩
    show (⟨w.1, a.2.1 ⟨w, hw⟩⟩ : Σ s : S.Srt, Vinfinite S s) =
      ⟨w.1, (extendPerm a.2.2).1 w.1 w.2⟩
    rw [extendPerm_apply a.2.2 w hw]

/-- The event transports by preimage, exactly: an extension of the moved reassignment agrees
with the moved extension on the anchor, and orbit compression identifies the two pullbacks. -/
theorem event_act (σ : FinSuppPerm S) (a : SaturatedAtom D) :
    event (act σ a) = RelStructure.relabel σ.1 ⁻¹' event a := by
  rw [event, event, RelStructure.relabel_preimage_relabel_preimage]
  refine relabel_preimage_eq_of_agree (D.seed_mem _ _ a.1.2.2) _ (σ * extendPerm a.2.2)
    fun v hv => ?_
  rw [extendPerm_apply (act σ a).2.2 v hv]
  show σ.1 v.1 (a.2.1 ⟨v, hv⟩) = σ.1 v.1 ((extendPerm a.2.2).1 v.1 v.2)
  rw [extendPerm_apply a.2.2 v hv]

/-- Every atom event lies in the fixing algebra of its own anchor. -/
theorem event_mem (a : SaturatedAtom D) :
    MeasurableSet[RelStructure.fixingAlgebra (anchor a)] (event a) := by
  classical
  have hmem : MeasurableSet[RelStructure.fixingAlgebra a.1.1] a.1.2.1 :=
    D.seed_mem a.1.1 a.1.2.1 a.1.2.2
  have htrans := RelStructure.fixingAlgebra_comap_relabel (extendPerm a.2.2).2 a.1.1
  rw [anchor_eq_image, ← htrans]
  exact ⟨a.1.2.1, hmem, rfl⟩

end SaturatedAtom

/-! ### The coherent basis of a law -/

section Assembly

variable [Countable S.Srt] [Countable S.Rel] (M : InfiniteRelExchangeableLaw S)

omit [Countable S.Srt] in
open scoped Classical in
/-- The identity atom over a seed: anchor `A` and event the seed itself, since the identity
relabeling moves neither. This is the inclusion witness for the density field. -/
private theorem seedOf_mem_indexed {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    {E : Set (RelStructure S (Vinfinite S))} (hE : E ∈ seedOf M A) :
    ∃ i : BasisExpr (SaturatedAtom (seedDataOf M)),
      BasisExpr.anchorOf SaturatedAtom.anchor i ⊆ A ∧
        BasisExpr.eval SaturatedAtom.event i = E := by
  have hid : SortwiseInjOn A fun v : {v // v ∈ A} => v.1.2 := fun v w hs hx =>
    Subtype.ext (Sigma.ext hs (heq_of_eq hx))
  refine ⟨.atom ⟨⟨A, ⟨E, hE⟩⟩, ⟨_, hid⟩⟩, ?_, ?_⟩
  · show SaturatedAtom.anchor (D := seedDataOf M) ⟨⟨A, ⟨E, hE⟩⟩, ⟨_, hid⟩⟩ ⊆ A
    intro v hv
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hv
    exact w.2
  · show RelStructure.relabel (SaturatedAtom.extendPerm hid).1 ⁻¹' E = E
    have hEfix : MeasurableSet[RelStructure.fixingAlgebra A] E := (seedDataOf M).seed_mem A E hE
    exact hEfix.2 _ ⟨(SaturatedAtom.extendPerm hid).2, fun v hv => by
      rw [SaturatedAtom.extendPerm_apply hid v hv]⟩

open scoped Classical in
/-- **Every exchangeable law has a coherent basis.**

Assembled from the three layers: the seeds come from separability of the law
(`measureDense_seedOf`), the atoms saturate them under the finitely supported subgroup, and the
Boolean syntax closes them under finite operations while keeping the anchor computed and the
action strict.

Stated as `Nonempty` rather than registered as an instance: a coherent basis is *chosen* data —
the seeds alone involve a choice — so an instance would make later independent choices behave
like typeclass diamonds. Consumers should take a basis as an argument.

No `NoNullary` hypothesis: whatever global information the law carries lives in
`fixingAlgebra ∅ = invariantAlgebra`, which is one of the factors. -/
private noncomputable def coherentBasisOf : CoherentBasis M :=
  {
    ι := BasisExpr (SaturatedAtom (seedDataOf M))
    countable_ι := inferInstance
    anchor := BasisExpr.anchorOf (SaturatedAtom.anchor (D := seedDataOf M))
    event := BasisExpr.eval (SaturatedAtom.event (D := seedDataOf M))
    event_mem := BasisExpr.eval_mem (SaturatedAtom.event_mem (D := seedDataOf M))
    bot := .bot
    anchor_bot := rfl
    event_bot := rfl
    compl := .compl
    anchor_compl := fun _ => rfl
    event_compl := fun _ => rfl
    inter := .inter
    anchor_inter := fun _ _ => rfl
    event_inter := fun _ _ => rfl
    act := BasisExpr.act (SaturatedAtom.act (D := seedDataOf M))
    act_one := BasisExpr.act_one (atomAct := SaturatedAtom.act (D := seedDataOf M))
      (SaturatedAtom.act_one (D := seedDataOf M))
    act_mul := fun σ τ => BasisExpr.act_mul
      (atomAct := SaturatedAtom.act (D := seedDataOf M))
      fun a => SaturatedAtom.act_mul (D := seedDataOf M) σ τ a
    anchor_act := fun σ => BasisExpr.anchorOf_act
      (atomAnchor := SaturatedAtom.anchor (D := seedDataOf M))
      (atomAct := SaturatedAtom.act (D := seedDataOf M))
      fun a => SaturatedAtom.anchor_act (D := seedDataOf M) σ a
    event_act := fun σ => BasisExpr.eval_act
      (atomEvent := SaturatedAtom.event (D := seedDataOf M))
      (atomAct := SaturatedAtom.act (D := seedDataOf M))
      fun a => SaturatedAtom.event_act (D := seedDataOf M) σ a
    density := fun A => by
      -- the seeds are already among the indexed events, so density transfers by monotonicity
      refine @MeasureTheory.Measure.MeasureDense.mono (RelStructure S (Vinfinite S))
        (RelStructure.fixingAlgebra A)
        ((M.law : Measure (RelStructure S (Vinfinite S))).trim (RelStructure.fixingAlgebra_le A))
        (seedOf M A) _ (measureDense_seedOf M A) (fun E hE => seedOf_mem_indexed M hE) ?_
      rintro - ⟨i, hiA, rfl⟩
      exact RelStructure.fixingAlgebra_mono hiA _
        (BasisExpr.eval_mem (SaturatedAtom.event_mem (D := seedDataOf M)) i) }

theorem InfiniteRelExchangeableLaw.nonempty_coherentBasis : Nonempty (CoherentBasis M) :=
  ⟨coherentBasisOf M⟩

end Assembly

end RelSignature
