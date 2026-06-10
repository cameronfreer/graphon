/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Lovasz

/-!
# The simple-graph rank theorem, K=1 (task #70) — non-circular algebra-atom framing

This module is the FRESH-PROJECT scaffold for the K=1 simple-graph rank theorem
(Lovász TR-2004-82 §3/§4.2 for *simple* rooted profiles), the last open paper-root
after #62/#73 (multigraph reconstruction) closed sorry-free.

## The problem

`Graphon/Lovasz.lean` proves `InRootedProfileSpan.of_const_on_orbit` (orbit-invariant
functions lie in the rooted simple-profile span) via `mkRootedSeparator` →
`k1_orbit_sep_aux` → `tupleEquivSimple_implies_orbit` — a **triangular cycle** whose
actual sorry sits at the "both non-surjective" branch of Lemma 2.4 K=1
(`Lovasz.lean` L7589). All three statements are mutually equivalent; none has an
independently proved base case.

## The non-circular reformulation (this file)

Replace orbit-separators (which need the cycle) by **definitional** separators:

1. **Algebra atoms.** `algebraAtomRel B W i j ↔ ∀ f ∈ InRootedProfileSpan, f i = f j`.
   This relation is *exactly* `rootedProfileEquiv` (`algebraAtomRel_iff_rootedProfileEquiv`,
   PROVED below — both directions are trivial). The atoms of the rooted-profile algebra
   are the rooted-profile-equivalence classes, NOT (a priori) the orbits.

2. **Idempotent indicators.** For ¬`rootedProfileEquiv i j` a separating rooted profile
   exists **by definition** (`exists_rpe_separator` — no `k1_orbit_sep_aux`!). Lagrange
   interpolation over the atom partition then puts each atom indicator `rpeIndicator`
   in the span (`rpeIndicator_mem_span`), and every atom-invariant function follows
   (`InRootedProfileSpan.of_const_on_rpe`). Both PROVED below, non-circularly —
   only `hB` (symmetry) is needed, no `hW`/`htwin`.

3. **The hard theorem** (the genuine #70 content, SORRY):
   `vertexOrbitRel_of_rootedProfileEquiv` : atoms = orbits, i.e.
   `rootedProfileEquiv B W i j → vertexOrbitRel B W i j` (twin-free `B`, `W > 0`).
   Once proved, `of_const_on_orbit` is re-derived non-circularly
   (`InRootedProfileSpan.of_const_on_orbit_noncircular`, PROVED modulo the hard theorem),
   and the whole #70 cascade closes.

4. **Minimal test case — FULLY PROVED (2026-06-10, sorry-free)**: plain
   square-moment descent `sqMoment_descends_of_rootedProfileEquiv` is
   formalized in `Graphon/CycleKrylov.lean` via the
   **cycle–Krylov–kernel argument** (see also
   `scripts/validate_sqmoment_cycle_krylov.py`): with `ε = B i - B j`,
   `u = B i + B j`, `M = B ∘ D_W`, rooted (q+2)-cycle differences are exactly
   `⟨ε, M^q u⟩_W`; rpe kills them for `q ≥ 1`; `u = M (D_W⁻¹ (e i + e j)) ∈ Im M`
   and self-adjointness give `u ∈ span{M^q u : q ≥ 1}`; hence
   `gap = ⟨ε, u⟩_W = 0`. Needs only `hB`, `hW` — no twin-freeness. The classwise
   form (`classwise_sqMoment_descends`, SORRY) is reduced by the same argument
   (palindromic decorated cycles) to the **singular-`M` stratum**:
   `gap_g = ⟨D_g ε, P_ker(M) (D_g u)⟩_W`, zero whenever `det B ≠ 0`.

5. **Decorated tree observables** (PROVED, §6): the span is closed under the
   weighted adjacency step `weightedAdj` (pendant attachment), so all tree
   observables with atom-invariant decorations descend; in particular classwise
   FIRST moments descend (`first_moment_descends_of_rootedProfileEquiv`) — the
   atom partition is an equitable partition of `(B, W)`. A uniform span expression
   of the square moment is impossible by `W`-grading (see §6 docstring), so the
   open content is genuinely per-instance: within-atom distributions beyond means.

## Known-BAD routes (do not retry; see project memory `lovasz-70-orbit-separation-simple`)

- closed-walk / trace observables;
- WL / color-refinement / fractional automorphisms (`stable_imp_vertexOrbitRel` is
  KNOWN-FALSE — Frucht graph);
- marker gadget (Cor 2.6 augmentation): the square moment leaks one step past the
  marker (`1ᵐ = 1` collapses only marker-incident multi-edges, not the `p–t` double
  edge), so the augmented simple profile does not determine it;
- "the proved multigraph theorem shortcuts it": converting multi-separators to simple
  ones is exactly the cycle.

## Sorry inventory of this file (2)

- `vertexOrbitRel_of_rootedProfileEquiv` — THE #70 paper-root (atoms = orbits).
- `classwise_sqMoment_descends` — minimal obstruction / test case (classwise form;
  the plain `sqMoment_descends_of_rootedProfileEquiv` is derived from it at `g = 1`).
-/

namespace Graphon.Lovasz

/-! ### §1 — `rootedProfileEquiv` is an equivalence relation -/

/-- Reflexivity of rooted-profile equivalence. -/
theorem rootedProfileEquiv.refl {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (i : Fin T) : rootedProfileEquiv B W i i :=
  fun _ _ _ => rfl

/-- Symmetry of rooted-profile equivalence. -/
theorem rootedProfileEquiv.symm {T : ℕ} {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    {i j : Fin T} (h : rootedProfileEquiv B W i j) : rootedProfileEquiv B W j i :=
  fun n F inst => (@h n F inst).symm

/-- Transitivity of rooted-profile equivalence. -/
theorem rootedProfileEquiv.trans {T : ℕ} {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    {i j k : Fin T} (h₁ : rootedProfileEquiv B W i j) (h₂ : rootedProfileEquiv B W j k) :
    rootedProfileEquiv B W i k :=
  fun n F inst => (@h₁ n F inst).trans (@h₂ n F inst)

/-! ### §2 — Algebra atoms of the rooted-profile span -/

/-- **Algebra-atom relation** of the rooted-profile span: two vertices are
atom-related iff *every* function in the span agrees on them. The atoms of the
(finite-dimensional, multiplicatively closed) subalgebra
`InRootedProfileSpan B W ⊆ (Fin T → ℝ)` are the classes of this relation. -/
def algebraAtomRel {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (i j : Fin T) : Prop :=
  ∀ f : Fin T → ℝ, InRootedProfileSpan B W f → f i = f j

/-- **The atom partition is the rooted-profile-equivalence partition** — NOT (a priori)
the orbit partition. Both directions are trivial and non-circular:
generators are in the span (`of_profile`), and span members are constant on
rooted-profile classes (`const_on_rpe`). Identifying these atoms with *orbits*
is the genuine open theorem `vertexOrbitRel_of_rootedProfileEquiv` below. -/
theorem algebraAtomRel_iff_rootedProfileEquiv {T : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (i j : Fin T) :
    algebraAtomRel B W i j ↔ rootedProfileEquiv B W i j := by
  constructor
  · intro h n F inst
    exact h (rootedProfileFun B W F) (InRootedProfileSpan.of_profile B W F)
  · intro h f hf
    exact hf.const_on_rpe h

/-! ### §3 — Definitional separators (the non-circular ingredient)

For the orbit relation, producing a separating rooted profile from
`¬ vertexOrbitRel B W i j` requires the rank theorem itself (`k1_orbit_sep_aux`
— the cycle). For rooted-profile equivalence the separator is **free**: it is the
literal content of the negated definition. This is what makes the atom framing
non-circular. -/

/-- **Rooted-profile-equivalence separator**: explicit witness record for
`¬ rootedProfileEquiv B W i j`. Mirrors `RootedSeparator` (private in
`Lovasz.lean`) but is built from the *definition* of the equivalence, not from
the orbit-separation cycle. -/
structure RpeSeparator {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (i j : Fin T) where
  /-- Number of unlabeled vertices. -/
  n : ℕ
  /-- The separating rooted simple graph. -/
  F : SimpleGraph (Fin (n + 1))
  /-- Bundled decidability instance for `F.Adj`. -/
  inst : DecidableRel F.Adj
  /-- The separation property. -/
  sep : @rootedProfile T n B W i F inst ≠ @rootedProfile T n B W j F inst

/-- Non-equivalent vertices are separated by some rooted profile — by definition. -/
theorem exists_rpe_separator {T : ℕ} {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    {i j : Fin T} (h : ¬ rootedProfileEquiv B W i j) :
    ∃ (n : ℕ) (F : SimpleGraph (Fin (n + 1))) (inst : DecidableRel F.Adj),
      @rootedProfile T n B W i F inst ≠ @rootedProfile T n B W j F inst := by
  unfold rootedProfileEquiv at h
  push_neg at h
  exact h

/-- Build an `RpeSeparator` from non-equivalence via `Classical.choose`. -/
noncomputable def mkRpeSeparator {T : ℕ} {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    {i j : Fin T} (h : ¬ rootedProfileEquiv B W i j) : RpeSeparator B W i j :=
  let h' := exists_rpe_separator h
  { n := h'.choose
    F := h'.choose_spec.choose
    inst := h'.choose_spec.choose_spec.choose
    sep := h'.choose_spec.choose_spec.choose_spec }

/-! ### §4 — Local algebra-closure helpers

File-local re-derivations of closure lemmas that are `private` in `Lovasz.lean`
(`finset_prod`, `finset_sum`, `profile_sub_const`, `lagrange_factor`). Verbatim
ports; kept private here too. -/

/-- Difference of a rooted profile from a constant lies in the span. -/
private theorem InRootedProfileSpan.profile_sub_const {T n : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj] (j : Fin T) :
    InRootedProfileSpan B W
      (fun v => rootedProfile B W v F - rootedProfile B W j F) := by
  have h₁ : InRootedProfileSpan B W (rootedProfileFun B W F) :=
    InRootedProfileSpan.of_profile B W F
  have h₂ : InRootedProfileSpan B W (fun _ => -(rootedProfile B W j F)) :=
    InRootedProfileSpan.const B W _
  have h_combined := h₁.add h₂
  convert h_combined using 2

/-- Lagrange factor: scaled difference function. -/
private theorem InRootedProfileSpan.lagrange_factor {T n : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (F : SimpleGraph (Fin (n + 1))) [DecidableRel F.Adj] (i j : Fin T) :
    InRootedProfileSpan B W
      (fun v => (rootedProfile B W v F - rootedProfile B W j F) /
                (rootedProfile B W i F - rootedProfile B W j F)) := by
  have h := (InRootedProfileSpan.profile_sub_const B W F j).smul
    (1 / (rootedProfile B W i F - rootedProfile B W j F))
  convert h using 1
  funext v
  rw [mul_comm, mul_one_div]

/-- Closure of `InRootedProfileSpan` under `Finset.prod`. -/
private theorem InRootedProfileSpan.finset_prod {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    {α : Type*} (S : Finset α) (g : α → Fin T → ℝ)
    (hg : ∀ a ∈ S, InRootedProfileSpan B W (g a)) :
    InRootedProfileSpan B W (fun v => ∏ a ∈ S, g a v) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact InRootedProfileSpan.one B W
  | insert a S ha_notin ih =>
    have h_a : InRootedProfileSpan B W (g a) := hg a (Finset.mem_insert_self a S)
    have h_S : InRootedProfileSpan B W (fun v => ∏ a ∈ S, g a v) := ih (fun b hb =>
      hg b (Finset.mem_insert_of_mem hb))
    have h_mul := InRootedProfileSpan.mul hB h_a h_S
    convert h_mul using 1
    funext v
    rw [Finset.prod_insert ha_notin]

/-- Closure of `InRootedProfileSpan` under `Finset.sum`. -/
private theorem InRootedProfileSpan.finset_sum {T : ℕ}
    {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ}
    {α : Type*} (S : Finset α) (g : α → Fin T → ℝ)
    (hg : ∀ a ∈ S, InRootedProfileSpan B W (g a)) :
    InRootedProfileSpan B W (fun v => ∑ a ∈ S, g a v) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact InRootedProfileSpan.zero B W
  | insert a S ha_notin ih =>
    have h_a : InRootedProfileSpan B W (g a) := hg a (Finset.mem_insert_self a S)
    have h_S : InRootedProfileSpan B W (fun v => ∑ a ∈ S, g a v) := ih (fun b hb =>
      hg b (Finset.mem_insert_of_mem hb))
    have h_add := h_a.add h_S
    convert h_add using 1
    funext v
    rw [Finset.sum_insert ha_notin]
    rfl

/-! ### §5 — Idempotent atom indicators (Lovász §4.2, non-circular) -/

/-- **Atom indicator** of the rooted-profile-equivalence class of `i`: the 0/1
function picking out the algebra atom containing `i`. The §4.2 idempotents of
the rooted-profile algebra. -/
noncomputable def rpeIndicator {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (i : Fin T) : Fin T → ℝ :=
  fun v => open Classical in if rootedProfileEquiv B W i v then (1 : ℝ) else 0

/-- The atom indicators are idempotent (pointwise 0/1). -/
theorem rpeIndicator_idem {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) (i : Fin T) :
    (fun v => rpeIndicator B W i v * rpeIndicator B W i v) = rpeIndicator B W i := by
  funext v
  unfold rpeIndicator
  split_ifs <;> norm_num

/-- Atom indicators are constant on atoms. -/
theorem rpeIndicator_const_on_rpe {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (i : Fin T) : ∀ a b, rootedProfileEquiv B W a b →
      rpeIndicator B W i a = rpeIndicator B W i b := by
  intro a b hab
  unfold rpeIndicator
  by_cases h : rootedProfileEquiv B W i a
  · rw [if_pos h, if_pos (h.trans hab)]
  · rw [if_neg h, if_neg (fun h' => h (h'.trans hab.symm))]

set_option maxHeartbeats 800000 in
/-- **Atom indicators lie in the rooted-profile span** — the non-circular
Lagrange interpolation. Separators come from `mkRpeSeparator` (definitional),
NOT from `mkRootedSeparator`/`k1_orbit_sep_aux` (the cycle). Note the
hypotheses: only symmetry of `B` (for `InRootedProfileSpan.mul`); no
twin-freeness, no positivity. -/
theorem rpeIndicator_mem_span {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (i : Fin T) :
    InRootedProfileSpan B W (rpeIndicator B W i) := by
  classical
  -- Factor function: uses RpeSeparator for the explicit instance.
  let factor : Fin T → Fin T → ℝ := fun j v =>
    if h : ¬ rootedProfileEquiv B W j i then
      let s := mkRpeSeparator h
      letI : DecidableRel s.F.Adj := s.inst
      (rootedProfile B W v s.F - rootedProfile B W j s.F) /
      (rootedProfile B W i s.F - rootedProfile B W j s.F)
    else 1
  let nonRpe : Finset (Fin T) := Finset.univ.filter (fun j => ¬ rootedProfileEquiv B W j i)
  let lagInd : Fin T → ℝ := fun v => ∏ j ∈ nonRpe, factor j v
  have lagInd_span : InRootedProfileSpan B W lagInd := by
    apply InRootedProfileSpan.finset_prod B hB W nonRpe factor
    intro j hj
    have hj_rpe : ¬ rootedProfileEquiv B W j i := by
      simp only [nonRpe, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hj
    show InRootedProfileSpan B W (factor j)
    simp only [factor, dif_pos hj_rpe]
    let s := mkRpeSeparator hj_rpe
    letI : DecidableRel s.F.Adj := s.inst
    exact InRootedProfileSpan.lagrange_factor B W s.F i j
  -- Show lagInd = rpeIndicator B W i.
  have lagInd_eq : lagInd = rpeIndicator B W i := by
    funext v
    unfold rpeIndicator
    by_cases hv : rootedProfileEquiv B W i v
    · rw [if_pos hv]
      show ∏ j ∈ nonRpe, factor j v = (1 : ℝ)
      apply Finset.prod_eq_one
      intro j hj
      have hj_rpe : ¬ rootedProfileEquiv B W j i := by
        simp only [nonRpe, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact hj
      simp only [factor, dif_pos hj_rpe]
      let s := mkRpeSeparator hj_rpe
      letI : DecidableRel s.F.Adj := s.inst
      have h_denom_ne : rootedProfile B W i s.F - rootedProfile B W j s.F ≠ 0 :=
        sub_ne_zero.mpr s.sep.symm
      have h_eq : rootedProfile B W v s.F = rootedProfile B W i s.F :=
        (@hv s.n s.F s.inst).symm
      rw [h_eq]
      exact div_self h_denom_ne
    · rw [if_neg hv]
      show ∏ j ∈ nonRpe, factor j v = (0 : ℝ)
      have h_v_no : ¬ rootedProfileEquiv B W v i := fun h => hv h.symm
      have h_v_mem : v ∈ nonRpe := by
        simp only [nonRpe, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h_v_no
      refine Finset.prod_eq_zero h_v_mem ?_
      simp only [factor, dif_pos h_v_no]
      let s := mkRpeSeparator h_v_no
      letI : DecidableRel s.F.Adj := s.inst
      show (rootedProfile B W v s.F - rootedProfile B W v s.F) /
           (rootedProfile B W i s.F - rootedProfile B W v s.F) = 0
      rw [sub_self, zero_div]
  rw [← lagInd_eq]
  exact lagInd_span

set_option maxHeartbeats 800000 in
/-- **Atom-invariant functions lie in the rooted-profile span** — the
non-circular K=1 fullness theorem (Lovász §4.2 for the simple rooted algebra).
Together with `algebraAtomRel_iff_rootedProfileEquiv` this says: the span is
EXACTLY the functions constant on algebra atoms. The open question (#70) is
only whether atoms = orbits. -/
theorem InRootedProfileSpan.of_const_on_rpe {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (f : Fin T → ℝ)
    (hf : ∀ i j, rootedProfileEquiv B W i j → f i = f j) :
    InRootedProfileSpan B W f := by
  classical
  -- classSize i := card of the atom of i. Always ≥ 1.
  set classSize : Fin T → ℕ := fun i =>
    (Finset.univ.filter (fun j => rootedProfileEquiv B W i j)).card with hclassSize_def
  have heq : f = fun v => ∑ i : Fin T,
      (f i / (classSize i : ℝ)) * rpeIndicator B W i v := by
    funext v
    -- Sum picks out i with v in the atom of i.
    have h_sum_filter :
        (∑ i : Fin T, (f i / (classSize i : ℝ)) * rpeIndicator B W i v) =
        ∑ i ∈ Finset.univ.filter (fun i => rootedProfileEquiv B W i v),
            f i / (classSize i : ℝ) := by
      unfold rpeIndicator
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with h <;> simp
    rw [h_sum_filter]
    -- For i in the atom of v: f i = f v and classSize i = classSize v.
    have h_summands : ∀ i ∈ Finset.univ.filter (fun i => rootedProfileEquiv B W i v),
        f i / (classSize i : ℝ) = f v / (classSize v : ℝ) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hfi : f i = f v := hf i v hi
      have h_size : classSize i = classSize v := by
        have h_set_eq :
            (Finset.univ.filter (fun j => rootedProfileEquiv B W i j)) =
            (Finset.univ.filter (fun j => rootedProfileEquiv B W v j)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h_ij => hi.symm.trans h_ij, fun h_vj => hi.trans h_vj⟩
        rw [hclassSize_def]
        exact congrArg Finset.card h_set_eq
      rw [hfi, h_size]
    rw [Finset.sum_congr rfl h_summands]
    rw [Finset.sum_const, nsmul_eq_mul]
    -- card of filter = classSize v.
    have hcard : (Finset.univ.filter (fun i => rootedProfileEquiv B W i v)).card =
        classSize v := by
      rw [hclassSize_def]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    rw [hcard]
    -- (classSize v : ℝ) > 0 since v is in its own atom.
    have h_pos : (0 : ℝ) < (classSize v : ℝ) := by
      have h_pos_nat : 0 < classSize v := by
        rw [hclassSize_def]
        apply Finset.card_pos.mpr
        refine ⟨v, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact rootedProfileEquiv.refl B W v
      exact_mod_cast h_pos_nat
    rw [mul_div_assoc']
    rw [mul_comm (classSize v : ℝ) (f v), mul_div_assoc, div_self (ne_of_gt h_pos), mul_one]
  rw [heq]
  exact InRootedProfileSpan.finset_sum Finset.univ
    (fun i v => (f i / (classSize i : ℝ)) * rpeIndicator B W i v)
    (fun i _ => (rpeIndicator_mem_span B hB W i).smul (f i / (classSize i : ℝ)))

/-! ### §6 — Span closure under the weighted adjacency step (decorated trees)

The pendant-attachment construction: given a rooted graph `G`, attach a new
root by a single edge to `G`'s old root. Its rooted profile realizes the
weighted adjacency operator `weightedAdj B W f i = ∑ t, W t * B i t * f t`
applied to `G`'s profile. Consequently the rooted-profile span is closed
under `weightedAdj` (`InRootedProfileSpan.weightedAdj`).

Together with `mul`/`const`/`of_const_on_rpe`, this generates **every
decorated-tree observable**: stars are products of first moments, paths are
iterated `weightedAdj`, and arbitrary trees with atom-invariant decorations
at every vertex follow by induction (decorations enter via `of_const_on_rpe`,
multiplied in before each `weightedAdj` step). In particular the classwise
first moments `∑ t, W t * B v t * 1_C(t)` (atom `C`) are atom-invariant
functions of the root (`first_moment_descends_of_rootedProfileEquiv`).

**Why no direct expression of the square moment exists** (attack step 2,
negative): under the scaling `W ↦ λW`, the profile of a rooted graph with
`m` unlabeled vertices scales as `λ^m`, while `∑ t, W t * B v t ^ 2` scales
as `λ¹`. A `(B, W)`-uniform span representation could therefore use only
graphs with exactly one unlabeled vertex — `K₂` and `K₁` — whose profiles
are `m₁(v) = ∑ t, W t * B v t` and `1`; generic `B` refutes
`sqMoment = a·m₁ + b`. So square-moment descent cannot be a uniform algebra
identity; it must use the per-instance atom structure (or new mathematics).
The constructions below are ported from the `rootAttach` block of
`MatrixDetermination.lean` (private there), adapted from `rootedEval` to
`rootedProfile`/`simpleEvalAt`. -/

/-- Attach a new root vertex (vertex 0) to the old root (vertex 1) by an edge.
Old vertices of `G` are shifted up by 1 in the new graph. -/
private def rootAttach (n : ℕ) (G : SimpleGraph (Fin (n + 1))) :
    SimpleGraph (Fin (n + 2)) where
  Adj u v :=
    (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) ∨
    (1 ≤ u.val ∧ 1 ≤ v.val ∧
      G.Adj ⟨u.val - 1, by omega⟩ ⟨v.val - 1, by omega⟩)
  symm := by
    intro u v h
    rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv, hadj⟩
    · right; left; exact ⟨hv, hu⟩
    · left; exact ⟨hv, hu⟩
    · right; right; exact ⟨hv, hu, G.symm hadj⟩
  loopless := by
    intro v h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨_, _, hadj⟩
    · omega
    · omega
    · exact G.loopless _ hadj

private instance rootAttachDecRel (n : ℕ) (G : SimpleGraph (Fin (n + 1)))
    [DecidableRel G.Adj] : DecidableRel (rootAttach n G).Adj :=
  fun u v =>
    inferInstanceAs (Decidable
      ((u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) ∨
       (1 ≤ u.val ∧ 1 ≤ v.val ∧
        G.Adj ⟨u.val - 1, by omega⟩ ⟨v.val - 1, by omega⟩)))

/-- The edge finset of `rootAttach n G` is the bridge edge plus shifted `G`-edges. -/
private theorem rootAttach_edgeFinset (n : ℕ) (G : SimpleGraph (Fin (n + 1)))
    [DecidableRel G.Adj] :
    (rootAttach n G).edgeFinset =
      insert s((0 : Fin (n + 2)), ⟨1, by omega⟩)
        (G.edgeFinset.map (Fin.succEmb (n + 1)).sym2Map) := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, Finset.mem_insert, Finset.mem_map,
    Function.Embedding.sym2Map_apply]
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      change ((a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0) ∨
        (1 ≤ a.val ∧ 1 ≤ b.val ∧
          G.Adj ⟨a.val - 1, by omega⟩ ⟨b.val - 1, by omega⟩)) at he
      rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb, hadj⟩
      · left; exact Sym2.eq_iff.mpr (Or.inl ⟨Fin.ext ha, Fin.ext hb⟩)
      · left; exact Sym2.eq_iff.mpr (Or.inr ⟨Fin.ext ha, Fin.ext hb⟩)
      · right
        refine ⟨s(⟨a.val - 1, by omega⟩, ⟨b.val - 1, by omega⟩), hadj, ?_⟩
        simp only [Sym2.map_pair_eq, Fin.coe_succEmb]
        exact Sym2.eq_iff.mpr
          (Or.inl ⟨Fin.ext (by simp; omega), Fin.ext (by simp; omega)⟩)
  · intro he
    rcases he with rfl | ⟨e', he', rfl⟩
    · -- Bridge edge: s(0, ⟨1,_⟩) is in rootAttach
      rw [SimpleGraph.mem_edgeSet]
      exact Or.inl ⟨rfl, rfl⟩
    · -- Shifted G-edge
      induction e' using Sym2.ind with
      | _ a b =>
        rw [SimpleGraph.mem_edgeSet] at he'
        simp only [Sym2.map_pair_eq, Fin.coe_succEmb, SimpleGraph.mem_edgeSet]
        exact Or.inr (Or.inr ⟨by simp, by simp, by convert he' using 2⟩)

/-- The bridge edge is not a shifted `G`-edge. -/
private theorem rootAttach_bridge_not_mem_shifted (n : ℕ)
    (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] :
    s((0 : Fin (n + 2)), ⟨1, by omega⟩) ∉
      G.edgeFinset.map (Fin.succEmb (n + 1)).sym2Map := by
  intro hmem
  rw [Finset.mem_map] at hmem
  obtain ⟨e, _, he⟩ := hmem
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq, Fin.coe_succEmb] at he
    rw [Sym2.eq_iff] at he
    rcases he with ⟨h1, _⟩ | ⟨_, h1⟩ <;>
      exact absurd (congr_arg Fin.val h1) (by simp [Fin.val_succ])

/-- The edge product over `rootAttach n G` equals the bridge term times the shifted
`G`-edge product (requires symmetric matrix). -/
private theorem rootAttach_prod_eq {k : ℕ} (n : ℕ) (G : SimpleGraph (Fin (n + 1)))
    [DecidableRel G.Adj] (c : Fin k → Fin k → ℝ) (hc : ∀ i j, c i j = c j i)
    (τ : Fin (n + 2) → Fin k) :
    ∏ e ∈ (rootAttach n G).edgeFinset,
      c (τ (Quot.out e).1) (τ (Quot.out e).2) =
    c (τ 0) (τ (Fin.succ (0 : Fin (n + 1)))) *
    ∏ e ∈ G.edgeFinset,
      c (τ (Fin.succ (Quot.out e).1)) (τ (Fin.succ (Quot.out e).2)) := by
  have h1eq : (⟨1, by omega⟩ : Fin (n + 2)) = Fin.succ (0 : Fin (n + 1)) :=
    Fin.ext (by simp)
  rw [rootAttach_edgeFinset,
    Finset.prod_insert (rootAttach_bridge_not_mem_shifted n G),
    Finset.prod_map G.edgeFinset (Fin.succEmb (n + 1)).sym2Map]
  congr 1
  · -- Bridge edge: resolve Quot.out
    have hout := Quot.out_eq s((0 : Fin (n + 2)), ⟨1, by omega⟩)
    rw [Sym2.mk_eq_mk_iff] at hout
    rcases hout with h | h
    · rw [congr_arg Prod.fst h, congr_arg Prod.snd h, h1eq]
    · have h1 := congr_arg Prod.fst h; have h2 := congr_arg Prod.snd h
      simp only [Prod.swap] at h1 h2
      rw [h1, h2, h1eq, hc]
  · congr 1; ext e
    -- Shifted edge: resolve Quot.out of mapped edge (use symmetry of c)
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq, Fin.coe_succEmb]
      have hout := Quot.out_eq s(Fin.succ a, Fin.succ b)
      rw [Sym2.mk_eq_mk_iff] at hout
      have hout' := Quot.out_eq s(a, b)
      rw [Sym2.mk_eq_mk_iff] at hout'
      rcases hout with h | h <;> rcases hout' with h' | h'
      · rw [congr_arg Prod.fst h, congr_arg Prod.snd h,
            congr_arg Prod.fst h', congr_arg Prod.snd h']
      · rw [congr_arg Prod.fst h, congr_arg Prod.snd h]
        simp only [Prod.swap] at h'
        rw [congr_arg Prod.fst h', congr_arg Prod.snd h', hc]
      · simp only [Prod.swap] at h
        rw [congr_arg Prod.fst h, congr_arg Prod.snd h,
            congr_arg Prod.fst h', congr_arg Prod.snd h', hc]
      · simp only [Prod.swap] at h h'
        rw [congr_arg Prod.fst h, congr_arg Prod.snd h,
            congr_arg Prod.fst h', congr_arg Prod.snd h']

/-- `rootedProfile` in `Fin.cons` form (bridging `simpleEvalAt`'s dif-based
coordinate assignment to the cons-based one). -/
private theorem rootedProfile_eq_cons {T n : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (i : Fin T) (F : SimpleGraph (Fin (n + 1)))
    [DecidableRel F.Adj] :
    rootedProfile B W i F =
      ∑ σ : Fin n → Fin T, (∏ u : Fin n, W (σ u)) *
        ∏ e ∈ F.edgeFinset,
          B (Fin.cons (α := fun _ => Fin T) i σ (Quot.out e).1)
            (Fin.cons (α := fun _ => Fin T) i σ (Quot.out e).2) := by
  unfold rootedProfile simpleEvalAt
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hτ : ∀ u : Fin (n + 1),
      (if h : (u : ℕ) < 1 then (fun _ : Fin 1 => i) ⟨u.val, h⟩
       else σ ⟨u.val - 1, by have := u.isLt; omega⟩) =
        Fin.cons (α := fun _ => Fin T) i σ u := by
    intro u
    rcases Fin.eq_zero_or_eq_succ u with rfl | ⟨x, rfl⟩
    · rw [dif_pos (by norm_num)]
      simp
    · rw [dif_neg (by simp), Fin.cons_succ]
      congr 1
  simp only [hτ]

/-- **Pendant attachment realizes the weighted adjacency operator** on rooted
profiles: `rootedProfile(rootAttach G)(v) = ∑ t, W t · B v t · rootedProfile(G)(t)`. -/
private theorem rootedProfile_rootAttach {T n : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] (v : Fin T) :
    rootedProfile B W v (rootAttach n G) =
      ∑ t : Fin T, W t * B v t * rootedProfile B W t G := by
  rw [rootedProfile_eq_cons, sum_fin_succ_eq_sum_cons]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [rootedProfile_eq_cons, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ' _ => ?_
  have h_edges := rootAttach_prod_eq n G B hB (Fin.cons v (Fin.cons t σ'))
  simp only [Fin.cons_zero, Fin.cons_succ] at h_edges
  rw [h_edges, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

/-- **The rooted-profile span is closed under the weighted adjacency step**:
if `g` is in the span, so is `weightedAdj B W g = fun v => ∑ t, W t * B v t * g t`.
Witnessed by pendant attachment on each generator. Non-circular (only `hB`). -/
theorem InRootedProfileSpan.weightedAdj {T : ℕ} {B : Fin T → Fin T → ℝ}
    (hB : ∀ i j, B i j = B j i) {W : Fin T → ℝ} {g : Fin T → ℝ}
    (hg : InRootedProfileSpan B W g) :
    InRootedProfileSpan B W (weightedAdj B W g) := by
  classical
  obtain ⟨N, fam, c, hgeq⟩ := hg
  refine ⟨N, fun k => ⟨(fam k).1 + 1, rootAttach (fam k).1 (fam k).2.1,
    @rootAttachDecRel _ _ (fam k).2.2⟩, c, ?_⟩
  funext v
  simp only [Graphon.Lovasz.weightedAdj, hgeq, rootedProfileFun, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  letI : DecidableRel (fam k).2.1.Adj := (fam k).2.2
  rw [rootedProfile_rootAttach B hB W (fam k).2.1 v, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- **Classwise first moments descend** (attack steps 1+3, PROVED).

If `i, j` are rooted-profile equivalent and `g` is any atom-invariant
decoration (e.g. the atom indicator `1_C`), the `g`-decorated first moments
agree. With `g = 1_C` this says `∑_{t ∈ C} W t * B i t = ∑_{t ∈ C} W t * B j t`
for every algebra atom `C`: the atom partition is an **equitable partition**
of the weighted graph `(B, W)`, and the atom-quotient matrix
`B̄(D, C) := ∑_{t ∈ C} W t * B(s, t)` (any `s ∈ D`) is well defined. -/
theorem first_moment_descends_of_rootedProfileEquiv {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    {i j : Fin T} (h : rootedProfileEquiv B W i j)
    {g : Fin T → ℝ} (hg : ∀ a b, rootedProfileEquiv B W a b → g a = g b) :
    ∑ t : Fin T, W t * B i t * g t = ∑ t : Fin T, W t * B j t * g t :=
  ((InRootedProfileSpan.of_const_on_rpe B hB W g hg).weightedAdj hB).const_on_rpe h

/-! ### §7 — THE hard theorem: algebra atoms = orbits (#70 paper-root) -/

/-- **The K=1 simple-graph rank theorem** (#70 paper-root, SORRY).

Rooted-profile equivalence implies vertex-orbit equivalence: the atoms of the
rooted simple-profile algebra are exactly the `(B, W)`-automorphism orbits.
Equivalent (given the proved scaffold in this file) to each of:
- `InRootedProfileSpan.of_const_on_orbit` proved without the separator cycle;
- `label_unlabeled_square_moment_descends` (the `Lovasz.lean` form);
- `algebraAtomRel = vertexOrbitRel` (`algebraAtomRel_eq_vertexOrbitRel` below).

**Hypotheses are necessary**: with twin rows (e.g. all-ones `B`) all vertices are
rooted-profile equivalent but orbits can be finer-grained in `W`-degenerate setups;
`hW` rules out zero-weight collapse.

**Known-BAD routes** (module docstring above): closed walks, WL/fractional,
marker gadget, multigraph shortcut, and anything through `k1_orbit_sep_aux`.

**Intended attack** (UPDATED 2026-06-09 — the test case FELL): the minimal
obstruction `sqMoment_descends_of_rootedProfileEquiv` is resolved by the
cycle–Krylov–kernel mechanism (see its docstring). Lift plan for the full
theorem: higher multigraph observables `∑ t, W t * B i t ^ k * …` should fall
to the same mechanism applied to the Hadamard powers `B^{∘(k-1)}` — theta-graph
(multi-path) rooted observables provide kernels in the algebra generated by
ordinary AND Hadamard products of `M` (coherent-closure-like), with
`B^{∘(k-1)} (e i)`-type vectors again in the relevant images. Once all
multigraph rooted evaluations descend, conclude via the PROVED multigraph
Lemma 2.4 (`tupleEquivMulti_implies_orbit`-chain) at K=1. -/
theorem vertexOrbitRel_of_rootedProfileEquiv {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    {i j : Fin T} (h : rootedProfileEquiv B W i j) :
    vertexOrbitRel B W i j := by
  sorry

/-- **Atoms = orbits**, packaged form of the rank theorem.
Proved modulo `vertexOrbitRel_of_rootedProfileEquiv`. -/
theorem algebraAtomRel_eq_vertexOrbitRel {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j) (i j : Fin T) :
    algebraAtomRel B W i j ↔ vertexOrbitRel B W i j := by
  rw [algebraAtomRel_iff_rootedProfileEquiv]
  exact ⟨vertexOrbitRel_of_rootedProfileEquiv B hB W hW htwin,
    rootedProfileEquiv_of_vertexOrbitRel B W⟩

/-- **Non-circular `of_const_on_orbit`** — the cascade target. Once the rank
theorem above is proved, this replaces the cyclically-proved
`InRootedProfileSpan.of_const_on_orbit` in `Lovasz.lean` and discharges the
L7589 sorry chain. Proof: an orbit-invariant function is atom-invariant
(atoms = orbits), and atom-invariant functions are in the span (§5, proved). -/
theorem InRootedProfileSpan.of_const_on_orbit_noncircular {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    (f : Fin T → ℝ)
    (hf : ∀ i j, vertexOrbitRel B W i j → f i = f j) :
    InRootedProfileSpan B W f :=
  InRootedProfileSpan.of_const_on_rpe B hB W f (fun i j hij =>
    hf i j (vertexOrbitRel_of_rootedProfileEquiv B hB W hW htwin hij))

/-! ### §8 — The minimal obstruction: square-moment descent

§6 proved that **first** moments with atom-invariant decorations descend.
The square moment `∑ t, W t * B i t ^ 2` decomposes over atoms as
`∑_C ∑_{t ∈ C} W t * B i t ^ 2`, so the sharpest currently-underivable
family (attack step 4) is the **classwise square moments**: within each
atom `C`, the distribution of `B(i, ·)|_C` beyond its (known) mean.
Cycle-type observables (triangles etc. through the root, decorated) give
bilinear couplings `∑_{t,s} W t W s B(i,t) B(t,s) B(s,i) 1_C(t) 1_D(s)` —
quadratic in the row but never the diagonal `t = s` term in isolation;
formalizing those requires a two-point attachment construction (deferred). -/

/-- The `W`-weighted square moment of row `i`: `∑ t, W t * B i t ^ 2`.
This is `starProbe 2` (a MULTIGRAPH observable — it needs a double edge `i–t`);
the simple rooted algebra only produces `Wᵏ`-weighted (k ≥ 2) square moments on
coincident unlabeled vertices. It is the sharpest known observable not visibly
in the simple span. -/
noncomputable def sqMoment {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (i : Fin T) : ℝ :=
  ∑ t : Fin T, W t * B i t ^ 2

/-- The square moment is orbit-invariant (direct, via `Equiv.sum_comp`). -/
theorem sqMoment_const_on_orbit {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    {i j : Fin T} (h : vertexOrbitRel B W i j) :
    sqMoment B W i = sqMoment B W j := by
  obtain ⟨σ, ⟨hW_σ, hB_σ⟩, hσij⟩ := h
  unfold sqMoment
  have hreidx : (∑ t : Fin T, W t * B j t ^ 2) =
      ∑ t : Fin T, W (σ t) * B j (σ t) ^ 2 :=
    (Equiv.sum_comp σ (fun t => W t * B j t ^ 2)).symm
  rw [hreidx]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hW_σ t, ← hσij, hB_σ i t]

/-! #### Cycle–Krylov slice 1 — weighted inner product, self-adjointness, gap identity

Formalization of the algebraic core of the cycle–Krylov–kernel proof
(`docs/sqmoment-cycle-krylov.md`). The operator `M` is the existing
`weightedAdj B W` (`Lovasz.lean`); iterates are `weightedAdjIter B W q`.
Slice 2 (separate): the rooted-cycle profile identity
`cycleDiff q = wInner W (rowDiff B i j) (weightedAdjIter B W q (rowSum B i j))`
and the span/range argument closing the gap. -/

/-- **Weighted inner product** `⟨f, g⟩_W = ∑ t, W t * f t * g t`. The form
with respect to which `weightedAdj B W` is self-adjoint (for symmetric `B`). -/
noncomputable def wInner {T : ℕ} (W : Fin T → ℝ) (f g : Fin T → ℝ) : ℝ :=
  ∑ t : Fin T, W t * f t * g t

/-- Row difference `ε = B i - B j` of the cycle–Krylov argument. -/
noncomputable def rowDiff {T : ℕ} (B : Fin T → Fin T → ℝ) (i j : Fin T) :
    Fin T → ℝ :=
  fun t => B i t - B j t

/-- Row sum `u = B i + B j` of the cycle–Krylov argument. -/
noncomputable def rowSum {T : ℕ} (B : Fin T → Fin T → ℝ) (i j : Fin T) :
    Fin T → ℝ :=
  fun t => B i t + B j t

/-- **Self-adjointness of the weighted adjacency operator** with respect to
`wInner W`: `⟨M f, g⟩_W = ⟨f, M g⟩_W`, using symmetry of `B`. -/
theorem wInner_weightedAdj_comm {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (f g : Fin T → ℝ) :
    wInner W (weightedAdj B W f) g = wInner W f (weightedAdj B W g) := by
  unfold wInner weightedAdj
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hB y x]
  ring

/-- Iterates of `weightedAdj` commute with one application (used to iterate
self-adjointness). -/
theorem weightedAdjIter_weightedAdj_comm {T : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (q : ℕ) (f : Fin T → ℝ) :
    weightedAdjIter B W q (weightedAdj B W f) =
      weightedAdj B W (weightedAdjIter B W q f) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    show weightedAdj B W (weightedAdjIter B W q (weightedAdj B W f)) = _
    rw [ih]
    rfl

/-- **Iterated self-adjointness**: `⟨M^[q] f, g⟩_W = ⟨f, M^[q] g⟩_W`. -/
theorem wInner_weightedAdjIter_comm {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) :
    ∀ (q : ℕ) (f g : Fin T → ℝ),
      wInner W (weightedAdjIter B W q f) g = wInner W f (weightedAdjIter B W q g) := by
  intro q
  induction q with
  | zero => intro f g; rfl
  | succ q ih =>
    intro f g
    show wInner W (weightedAdj B W (weightedAdjIter B W q f)) g =
         wInner W f (weightedAdj B W (weightedAdjIter B W q g))
    rw [wInner_weightedAdj_comm B hB, ih f (weightedAdj B W g),
      weightedAdjIter_weightedAdj_comm]

/-- **The gap identity** (Step 4 input of the cycle–Krylov proof):
`sqMoment i - sqMoment j = ⟨ε, u⟩_W`. -/
theorem sqMoment_sub_eq_wInner {T : ℕ} (B : Fin T → Fin T → ℝ)
    (W : Fin T → ℝ) (i j : Fin T) :
    sqMoment B W i - sqMoment B W j = wInner W (rowDiff B i j) (rowSum B i j) := by
  unfold sqMoment wInner rowDiff rowSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- **`u ∈ Im M`** (Step 2 of the cycle–Krylov proof): the row sum is the
image under `weightedAdj` of the `W`-rescaled pair indicator. Uses `hW` and
symmetry of `B`. -/
theorem rowSum_eq_weightedAdj {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (hW : ∀ t, 0 < W t)
    (i j : Fin T) :
    rowSum B i j = weightedAdj B W
      (fun t => (if t = i then 1 else 0) / W t + (if t = j then 1 else 0) / W t) := by
  classical
  have key : ∀ a x : Fin T,
      (∑ t : Fin T, W t * B x t * ((if t = a then (1 : ℝ) else 0) / W t)) = B x a := by
    intro a x
    rw [Finset.sum_eq_single a]
    · rw [if_pos rfl, mul_one_div, mul_comm (W a) (B x a), mul_div_assoc,
        div_self (hW a).ne', mul_one]
    · intro t _ ht
      rw [if_neg ht, zero_div, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ a) h
  funext x
  unfold rowSum weightedAdj
  rw [show (∑ t : Fin T, W t * B x t *
        ((if t = i then (1 : ℝ) else 0) / W t + (if t = j then 1 else 0) / W t)) =
      ∑ t : Fin T, (W t * B x t * ((if t = i then (1 : ℝ) else 0) / W t) +
        W t * B x t * ((if t = j then 1 else 0) / W t)) from
    Finset.sum_congr rfl fun t _ => by ring]
  rw [Finset.sum_add_distrib, key i x, key j x, hB x i, hB x j]

/-- Symmetry of the weighted inner product. -/
theorem wInner_comm {T : ℕ} (W : Fin T → ℝ) (f g : Fin T → ℝ) :
    wInner W f g = wInner W g f := by
  unfold wInner
  exact Finset.sum_congr rfl fun t _ => by ring

/-- `weightedAdj` is additive. -/
theorem weightedAdj_add {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (f g : Fin T → ℝ) :
    weightedAdj B W (fun t => f t + g t) =
      fun t => weightedAdj B W f t + weightedAdj B W g t := by
  funext x
  unfold weightedAdj
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- Iterates of `weightedAdj` are additive. -/
theorem weightedAdjIter_add {T : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    ∀ (q : ℕ) (f g : Fin T → ℝ),
      weightedAdjIter B W q (fun t => f t + g t) =
        fun t => weightedAdjIter B W q f t + weightedAdjIter B W q g t := by
  intro q
  induction q with
  | zero => intro f g; rfl
  | succ q ih =>
    intro f g
    show weightedAdj B W (weightedAdjIter B W q (fun t => f t + g t)) = _
    rw [ih f g, weightedAdj_add]
    rfl

/-- **Polarization for self-adjoint iterates**: with `K = M^[q]`,
`⟨f - g, K (f + g)⟩_W = ⟨f, K f⟩_W - ⟨g, K g⟩_W` — the cross terms cancel by
(iterated) self-adjointness. -/
theorem wInner_sub_iter_add {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (q : ℕ) (f g : Fin T → ℝ) :
    wInner W (fun t => f t - g t)
        (weightedAdjIter B W q (fun t => f t + g t)) =
      wInner W f (weightedAdjIter B W q f) -
        wInner W g (weightedAdjIter B W q g) := by
  rw [weightedAdjIter_add B W q f g]
  have expand : ∀ t, W t * (f t - g t) *
        (weightedAdjIter B W q f t + weightedAdjIter B W q g t) =
      (W t * f t * weightedAdjIter B W q f t +
        W t * f t * weightedAdjIter B W q g t) -
      (W t * g t * weightedAdjIter B W q f t +
        W t * g t * weightedAdjIter B W q g t) := fun t => by ring
  unfold wInner
  simp only [expand]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcross : (∑ t : Fin T, W t * f t * weightedAdjIter B W q g t) =
      ∑ t : Fin T, W t * g t * weightedAdjIter B W q f t := by
    have h1 := wInner_weightedAdjIter_comm B hB W q g f
    have h2 := wInner_comm W (weightedAdjIter B W q g) f
    -- h1 : ⟨K g, f⟩ = ⟨g, K f⟩;  h2 : ⟨K g, f⟩ = ⟨f, K g⟩
    have := h2.symm.trans h1
    exact this
  rw [hcross]
  ring

/-- **Closed-walk profile as a weighted inner product**:
`CW(v, q+2) = ⟨B v ·, M^[q] (B v ·)⟩_W`. -/
theorem closedWalkProfile_eq_wInner {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (v : Fin T) (q : ℕ) :
    closedWalkProfile B W v (q + 2) =
      wInner W (fun t => B v t) (weightedAdjIter B W q (fun t => B v t)) := by
  have hg : (fun x => B x v) = fun t => B v t := funext fun t => hB t v
  show weightedAdjIter B W (q + 1) (fun x => B x v) v = _
  rw [hg]
  show weightedAdj B W (weightedAdjIter B W q (fun t => B v t)) v = _
  unfold weightedAdj wInner
  rfl

/-- **Cycle difference identity, recursive/algebraic form** (Step 1 of the
cycle–Krylov proof): closed-walk profile differences are exactly
`⟨ε, M^[q] u⟩_W`. The graph side — `rootedProfile` of `rootedCycleGraph`
equals `closedWalkProfile` — is the separate plumbing slice (the existing
focused sorry `rootedProfile_rootedCycleGraph_eq_closedWalkProfile` in
`Lovasz.lean`). -/
theorem closedWalkProfile_sub_eq_wInner {T : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (i j : Fin T) (q : ℕ) :
    closedWalkProfile B W i (q + 2) - closedWalkProfile B W j (q + 2) =
      wInner W (rowDiff B i j) (weightedAdjIter B W q (rowSum B i j)) := by
  rw [closedWalkProfile_eq_wInner B hB W i q, closedWalkProfile_eq_wInner B hB W j q]
  exact (wInner_sub_iter_add B hB W q (fun t => B i t) (fun t => B j t)).symm

/-- **Classwise square-moment descent** (SORRY — reduced to the singular-`M`
stratum, 2026-06-09).

If `i, j` are rooted-profile equivalent and `g` is atom-invariant, the
`g`-decorated square moments agree. With `g = 1_C` this is the within-atom
square moment `∑_{t ∈ C} W t * B i t ^ 2`.

**Status after the cycle–Krylov breakthrough** (see
`sqMoment_descends_of_rootedProfileEquiv` for the resolved `g = 1` case):
palindromic decorated rooted cycles give `⟨ε, D_g M^q D_g u⟩_W = 0` for
`q ≥ 1` (`ε = B i - B j`, `u = B i + B j`, `M = B ∘ D_W`, `D_g` the
diagonal of `g`), so by the same spectral step the classwise gap equals
`⟨D_g ε, P₀ (D_g u)⟩_W` with `P₀` the `ker M`-projection. This VANISHES
whenever `det B ≠ 0`; the open residue is only the singular-`B` stratum
(where `D_g u ∉ Im M` is possible). Numerical search for counterexamples
(LM cutting-plane, `scripts/falsify_classwise_sqmoment.py`) found none and
went infeasible at both T=4 and T=5 once long-cycle cuts entered.

No harder than #70: it follows from the rank theorem
(`classwise_sqMoment_of_rank_theorem` below). -/
theorem classwise_sqMoment_descends {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    {i j : Fin T} (h : rootedProfileEquiv B W i j)
    {g : Fin T → ℝ} (hg : ∀ a b, rootedProfileEquiv B W a b → g a = g b) :
    ∑ t : Fin T, W t * B i t ^ 2 * g t = ∑ t : Fin T, W t * B j t ^ 2 * g t := by
  sorry

/-! **Minimal test case for the rank theorem** — square-moment descent:
**FULLY PROVED** (sorry-free, no twin-freeness) as
`sqMoment_descends_of_rootedProfileEquiv` in `Graphon/CycleKrylov.lean`, by
the cycle–Krylov–kernel argument (`docs/sqmoment-cycle-krylov.md`): the
algebraic slices in this file (`sqMoment_sub_eq_wInner`,
`rowSum_eq_weightedAdj`, `closedWalkProfile_sub_eq_wInner`) + the abstract
Krylov-kernel lemma + the rooted-cycle bridge in `Lovasz.lean`. It lives there
(not here) because the spectral slice imports inner-product-space machinery
that must stay out of the `Lovasz.lean` import chain. -/

/-- The reduction direction, made formal: the rank theorem implies square-moment
descent. (So the test case is no harder than #70; the conjecture is that it is
also the crux.) Stated with the rank theorem as an explicit hypothesis to keep
this lemma sorry-free. -/
theorem sqMoment_descends_of_rank_theorem {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hrank : ∀ {i j : Fin T}, rootedProfileEquiv B W i j → vertexOrbitRel B W i j)
    {i j : Fin T} (h : rootedProfileEquiv B W i j) :
    sqMoment B W i = sqMoment B W j :=
  sqMoment_const_on_orbit B W (hrank h)

/-- The classwise reduction direction: the rank theorem implies classwise
square-moment descent (reindex by the automorphism; the decoration is
atom-invariant, hence invariant along orbits). So the sharpened test case is
also no harder than #70. Sorry-free (rank theorem as explicit hypothesis). -/
theorem classwise_sqMoment_of_rank_theorem {T : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (hrank : ∀ {a b : Fin T}, rootedProfileEquiv B W a b → vertexOrbitRel B W a b)
    {i j : Fin T} (h : rootedProfileEquiv B W i j)
    {g : Fin T → ℝ} (hg : ∀ a b, rootedProfileEquiv B W a b → g a = g b) :
    ∑ t : Fin T, W t * B i t ^ 2 * g t = ∑ t : Fin T, W t * B j t ^ 2 * g t := by
  obtain ⟨σ, ⟨hW_σ, hB_σ⟩, hσij⟩ := hrank h
  have hreidx : (∑ t : Fin T, W t * B j t ^ 2 * g t) =
      ∑ t : Fin T, W (σ t) * B j (σ t) ^ 2 * g (σ t) :=
    (Equiv.sum_comp σ (fun t => W t * B j t ^ 2 * g t)).symm
  rw [hreidx]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hW_σ t, ← hσij, hB_σ i t]
  have hgt : g t = g (σ t) :=
    hg t (σ t) (rootedProfileEquiv_of_vertexOrbitRel B W ⟨σ, ⟨hW_σ, hB_σ⟩, rfl⟩)
  rw [hgt]

end Graphon.Lovasz
