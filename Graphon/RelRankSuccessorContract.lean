/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRankRepresentation

/-!
# The successor contract (R4 converse, #107)

Interface only: the shared witness type that **both** successor constructions must produce, and
the two identically typed statements they target. No construction is performed here.

## Why a witness type rather than `Nonempty (RankRepresentation (n + 1))`

A theorem returning merely `Nonempty (M.RankRepresentation (n + 1))` does not characterize a
successor construction at all: it could ignore `C` entirely and produce an unrelated rank-`(n+1)`
representation. That is the same kind of underdetermined contract that caused the earlier failure,
so the compatibility is made an **explicit observable**:

```
next.P.map (Prod.map id (rankLatentProjection (Nat.le_succ n))) = C.P
```

Truncating the successor's latents back to rank `n` returns `C.P` on the nose — exactly, not
almost everywhere and not up to isomorphism.

## What the witness deliberately does not carry

* **No independence field** beyond what `RankRepresentation` already states — recovery and
  screening at the working rank are fields of `next` itself, and nothing further is asserted.
* **No equality between the two routes' outputs.** They prove the same existence statement by
  different means and will not produce canonically equal representations; asserting otherwise
  would be false. The public induction may cite whichever lands first, and the other remains an
  independently audited proof path.
-/

open MeasureTheory

namespace RelSignature

namespace InfiniteRelExchangeableLaw

variable {S : RelSignature} [Countable S.Srt] [Countable S.Rel]
  {M : InfiniteRelExchangeableLaw S} {n : ℕ}

/-- **A successor witness**: a rank-`(n+1)` representation whose latent truncation returns the
given rank-`n` representation exactly. This is what both routes must produce. -/
structure RankSuccessor (C : M.RankRepresentation n) where
  /-- The next representation. -/
  next : M.RankRepresentation (n + 1)
  /-- **Exact truncation compatibility**: forgetting the fresh rank-`n` latent layer returns `C.P`
  on the nose. Without this the statement would not mention `C` at all. -/
  truncation :
    next.P.map (Prod.map id (rankLatentProjection (S := S) (Nat.le_succ n))) = C.P

namespace RankSuccessor

variable {C : M.RankRepresentation n} (D : RankSuccessor C)

omit [Countable S.Rel] in
/-- The truncation map is measurable, so the witness's identity is an identity of pushforwards
along a measurable map. -/
theorem measurable_truncation :
    Measurable (Prod.map (id : RelStructure S (Vinfinite S) → _)
      (rankLatentProjection (S := S) (Nat.le_succ n))) :=
  measurable_id.prodMap (measurable_rankLatentProjection _)

/-- The successor's structure marginal is still the law — a consequence of truncation
compatibility, recorded so consumers need not re-derive it. -/
theorem next_map_fst : D.next.P.map Prod.fst = (M.law : Measure (RelStructure S (Vinfinite S))) :=
  D.next.map_fst

end RankSuccessor

/-! ### Regression: the rank-zero base

At rank zero the latent cube is a single point — there is no support of cardinality below `0` —
so the truncation observable degenerates exactly as it should: it constrains only the structure
marginal, which `RankRepresentation` already pins. This records why the base case imposes nothing
extra, and it is the first of the shared regressions the contract must survive. -/

instance : IsEmpty (RankLatentIndex S 0) := ⟨fun A => absurd A.2 (Nat.not_lt_zero _)⟩

instance : Subsingleton (RankLatentSpace S 0) :=
  ⟨fun _ _ => funext fun A => absurd A.2 (Nat.not_lt_zero _)⟩

omit [Countable S.Srt] [Countable S.Rel] in
/-- **The rank-zero latent cube carries no information.** Any two points of it agree, so a
rank-zero representation is determined by its structure marginal. -/
theorem rankLatentSpace_zero_subsingleton (ω ω' : RankLatentSpace S 0) : ω = ω' :=
  Subsingleton.elim _ _

/-- **The successor statement**, as a proposition: every rank-`n` representation admits a
successor witness. Both routes target this exact statement, and neither is proved here. -/
def SuccessorStatement (S : RelSignature) [Countable S.Srt] [Countable S.Rel] : Prop :=
  ∀ (M : InfiniteRelExchangeableLaw S) (n : ℕ) (C : M.RankRepresentation n),
    Nonempty (RankSuccessor C)

/-- The Kallenberg route's target: the shared successor statement, reached by directly
constructing the correlated subset latents. Stated here, proved in its own unit. -/
abbrev KallenbergSuccessor (S : RelSignature) [Countable S.Srt] [Countable S.Rel] : Prop :=
  SuccessorStatement S

/-- The Austin route's target: the shared successor statement, reached through polling, an
enriched lower-rank object, a conditional kernel, and noise outsourcing. Stated here, proved in
its own unit. -/
abbrev AustinSuccessor (S : RelSignature) [Countable S.Srt] [Countable S.Rel] : Prop :=
  SuccessorStatement S

/-- The two route targets are the same proposition — by construction, not by an asserted
identification of their outputs. Whichever is proved first discharges the induction step; the
other remains an independent proof of the same statement. -/
theorem austinSuccessor_eq_kallenbergSuccessor
    (S : RelSignature) [Countable S.Srt] [Countable S.Rel] :
    AustinSuccessor S = KallenbergSuccessor S := rfl

end InfiniteRelExchangeableLaw

end RelSignature
