/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelCoherentBasis
import Mathlib.Tactic.DeriveEncodable

/-!
# The Boolean syntax layer for a coherent basis (R4 converse piece 3, #107)

The index type of a `RelSignature.CoherentBasis` must be closed under finite Boolean operations
and carry a strict action of the finitely supported relabelings. Both are obtained here by
taking the indices to be **formal expressions** over a set of atoms, rather than a set of events
closed under the operations.

## Why syntax rather than a closed family of events

Two things go wrong if the index is a family of *events*:

* **The anchor is not determined by the event.** The same set can arise anchored at different
  finite vertex sets, so an event-indexed family forces a *choice* of anchor, and then
  `anchor_act` demands that choice be equivariant — which is the coherence problem again.
* **The action laws stop being strict.** Closing a family of events under complement and
  intersection and then acting on it requires choosing representatives of equal events, and
  `act_one` / `act_mul` hold only up to that choice.

With syntax both problems vanish: `anchor` and `event` are *computed* by recursion, so the
anchor travels with the expression, and `act` acts on the syntax tree, so its laws follow by
structural induction from the corresponding laws on atoms.

## Contents

* `RelSignature.BasisExpr` — formal Boolean expressions over an atom type;
* `BasisExpr.eval` / `BasisExpr.anchorOf` — the event and anchor of an expression, by recursion;
* `BasisExpr.act` — the relabeling action on expressions, with `act_one` and `act_mul` proved by
  induction from the atom-level laws;
* `BasisExpr.instCountable` — countability, so the resulting index type is countable.
-/

open MeasureTheory MeasurableSpace

namespace RelSignature

/-! ### The syntax -/

/-- **Formal Boolean expressions** over an atom type `α`: the formal Boolean-expression syntax
with `⊥`, complement, and intersection — unquotiented terms, not the free Boolean ring itself.
Union and difference are derived, so the image of `eval` is a set ring.

The index of a `CoherentBasis` is built from this rather than from a closed family of events,
so that the anchor is computed from the expression and the relabeling action is structural. -/
inductive BasisExpr (α : Type*) where
  /-- The empty event, anchored at `∅`. -/
  | bot : BasisExpr α
  /-- An atom. -/
  | atom : α → BasisExpr α
  /-- Complement; the anchor is unchanged. -/
  | compl : BasisExpr α → BasisExpr α
  /-- Intersection; the anchor is the union of the two anchors. -/
  | inter : BasisExpr α → BasisExpr α → BasisExpr α
  deriving Encodable

namespace BasisExpr

variable {α : Type*}

instance instCountable [Countable α] : Countable (BasisExpr α) := by
  letI : Encodable α := Encodable.ofCountable α
  infer_instance

variable {S : RelSignature}

/-! ### Evaluation -/

open scoped Classical in
/-- **The anchor of an expression**, computed structurally: `⊥` is anchored at `∅`, complement
preserves the anchor, and intersection takes the union — which is exactly what keeps the
indices anchored inside `A` closed under the operations. -/
noncomputable def anchorOf (atomAnchor : α → Finset (Σ s : S.Srt, Vinfinite S s)) :
    BasisExpr α → Finset (Σ s : S.Srt, Vinfinite S s)
  | .bot => ∅
  | .atom a => atomAnchor a
  | .compl e => anchorOf atomAnchor e
  | .inter e f => anchorOf atomAnchor e ∪ anchorOf atomAnchor f

/-- **The event of an expression**, computed structurally. -/
def eval (atomEvent : α → Set (RelStructure S (Vinfinite S))) :
    BasisExpr α → Set (RelStructure S (Vinfinite S))
  | .bot => ∅
  | .atom a => atomEvent a
  | .compl e => (eval atomEvent e)ᶜ
  | .inter e f => eval atomEvent e ∩ eval atomEvent f

/-- Every expression evaluates into the fixing algebra of its own anchor, provided the atoms do.
The intersection case is where the anchor-as-union convention pays: both sides are pushed up to
the union by `fixingAlgebra_mono`. -/
theorem eval_mem {atomAnchor : α → Finset (Σ s : S.Srt, Vinfinite S s)}
    {atomEvent : α → Set (RelStructure S (Vinfinite S))}
    (hatom : ∀ a, MeasurableSet[RelStructure.fixingAlgebra (atomAnchor a)] (atomEvent a)) :
    ∀ e : BasisExpr α,
      MeasurableSet[RelStructure.fixingAlgebra (anchorOf atomAnchor e)] (eval atomEvent e)
  | .bot => @MeasurableSet.empty _ (RelStructure.fixingAlgebra _)
  | .atom a => hatom a
  | .compl e => (eval_mem hatom e).compl
  | .inter e f => by
      classical
      exact ((RelStructure.fixingAlgebra_mono Finset.subset_union_left) _
          (eval_mem hatom e)).inter
        ((RelStructure.fixingAlgebra_mono Finset.subset_union_right) _ (eval_mem hatom f))

/-! ### The relabeling action -/

/-- **The action on expressions**, induced by an action on atoms. Typed by the finitely
supported subgroup, matching `CoherentBasis.act`. -/
def act (atomAct : FinSuppPerm S → α → α) (σ : FinSuppPerm S) : BasisExpr α → BasisExpr α
  | .bot => .bot
  | .atom a => .atom (atomAct σ a)
  | .compl e => .compl (act atomAct σ e)
  | .inter e f => .inter (act atomAct σ e) (act atomAct σ f)

/-- The action is trivial at the identity, by induction from the atom-level law. -/
theorem act_one {atomAct : FinSuppPerm S → α → α} (hone : ∀ a, atomAct 1 a = a) :
    ∀ e : BasisExpr α, act atomAct 1 e = e
  | .bot => rfl
  | .atom a => by simp only [act, hone]
  | .compl e => by simp only [act, act_one hone e]
  | .inter e f => by simp only [act, act_one hone e, act_one hone f]

/-- The action is multiplicative, by induction from the atom-level law. The orientation matches
the contravariance of `RelStructure.relabel`. -/
theorem act_mul {atomAct : FinSuppPerm S → α → α} {σ τ : FinSuppPerm S}
    (hmul : ∀ a, atomAct (σ * τ) a = atomAct σ (atomAct τ a)) :
    ∀ e : BasisExpr α, act atomAct (σ * τ) e = act atomAct σ (act atomAct τ e)
  | .bot => rfl
  | .atom a => by simp only [act, hmul]
  | .compl e => by simp only [act, act_mul hmul e]
  | .inter e f => by simp only [act, act_mul hmul e, act_mul hmul f]

open scoped Classical in
/-- The action transports anchors by the image map, provided the atoms do. -/
theorem anchorOf_act {atomAnchor : α → Finset (Σ s : S.Srt, Vinfinite S s)}
    {atomAct : FinSuppPerm S → α → α} {σ : FinSuppPerm S}
    (hanchor : ∀ a, atomAnchor (atomAct σ a) =
      (atomAnchor a).image (Sigma.map id fun s => ⇑(σ.1 s))) :
    ∀ e : BasisExpr α, anchorOf atomAnchor (act atomAct σ e) =
      (anchorOf atomAnchor e).image (Sigma.map id fun s => ⇑(σ.1 s))
  | .bot => by simp only [act, anchorOf, Finset.image_empty]
  | .atom a => by simp only [act, anchorOf, hanchor]
  | .compl e => by simp only [act, anchorOf, anchorOf_act hanchor e]
  | .inter e f => by
      simp only [act, anchorOf, anchorOf_act hanchor e, anchorOf_act hanchor f,
        Finset.image_union]

/-- The action transports events by preimage — **exactly**, with no null sets, provided the
atoms do. Complement and intersection commute with preimage on the nose, which is the whole
reason the syntax layer keeps the action strict. -/
theorem eval_act {atomEvent : α → Set (RelStructure S (Vinfinite S))}
    {atomAct : FinSuppPerm S → α → α} {σ : FinSuppPerm S}
    (hevent : ∀ a, atomEvent (atomAct σ a) = RelStructure.relabel σ.1 ⁻¹' atomEvent a) :
    ∀ e : BasisExpr α,
      eval atomEvent (act atomAct σ e) = RelStructure.relabel σ.1 ⁻¹' eval atomEvent e
  | .bot => by simp only [act, eval, Set.preimage_empty]
  | .atom a => by simp only [act, eval, hevent]
  | .compl e => by simp only [act, eval, eval_act hevent e, Set.preimage_compl]
  | .inter e f => by
      simp only [act, eval, eval_act hevent e, eval_act hevent f, Set.preimage_inter]

end BasisExpr

end RelSignature
