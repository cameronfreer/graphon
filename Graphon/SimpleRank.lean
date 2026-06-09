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

4. **Minimal test case** (SORRY): `sqMoment_descends_of_rootedProfileEquiv` —
   `rootedProfileEquiv i j → ∑ t, W t * B i t ^ 2 = ∑ t, W t * B j t ^ 2`.
   The `W¹`-weighted square moment is the sharpest known observable NOT visibly in the
   simple span (it needs a double edge `i–t`; simple profiles only produce
   `Wᵏ`-weighted (k ≥ 2) coincidences). If square-moment descent is provable
   non-circularly, the full rank theorem is likely tractable; if not, it cleanly
   isolates the true paper-root.

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
- `sqMoment_descends_of_rootedProfileEquiv` — minimal obstruction / test case.
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

/-! ### §6 — THE hard theorem: algebra atoms = orbits (#70 paper-root) -/

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

**Intended attack**: first prove the minimal obstruction
`sqMoment_descends_of_rootedProfileEquiv` below; if that succeeds non-circularly,
lift its mechanism to all multigraph observables (each multigraph evaluation is a
polynomial obstruction of the same shape), then conclude via the PROVED multigraph
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

/-! ### §7 — The minimal obstruction: square-moment descent -/

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

/-- **Minimal test case for the rank theorem** (SORRY) — square-moment descent.

If `i` and `j` have equal rooted simple-graph profiles, their `W¹`-weighted
square moments agree. This is the FIRST concrete obstruction beyond the simple
algebra: `B i t ^ 2` with a single `W t` weight is not a simple-graph factor
(it would need a double edge), so `const_on_rpe` does not apply directly.

- Provable non-circularly ⟹ the full rank theorem
  `vertexOrbitRel_of_rootedProfileEquiv` is likely tractable by the same
  mechanism lifted to all multigraph observables.
- NOT provable non-circularly ⟹ this statement IS the clean paper-root.

It follows trivially from the rank theorem (`sqMoment_descends_of_rank_theorem`
below), so any independent proof here is strictly upstream progress. -/
theorem sqMoment_descends_of_rootedProfileEquiv {T : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i)
    (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j)
    {i j : Fin T} (h : rootedProfileEquiv B W i j) :
    sqMoment B W i = sqMoment B W j := by
  sorry

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

end Graphon.Lovasz
