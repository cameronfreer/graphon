/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.Lovasz

/-!
# Cross-matrix super-surjective transfer (Cai–Govorov Lemma 5.1, two-matrix form)

Port of the proved single-matrix chunk 3A of `Graphon/Lovasz.lean`
(`testEvalEq_implies_orbit_super` / `superMap`) to the CROSS-matrix setting: the left
tuple `ξ : Fin K → Fin T` probes `(B, W)` and the right tuple `ψ : Fin K → Fin T'`
probes `(B', W')`, with matched test-moment profiles as the input interface.

The deliverable is the **partition form** (`cross_super_partition`): classes
`C : Fin T → Finset (Fin T')` that are nonempty, pairwise disjoint, covering, with
`W t = ∑_{t' ∈ C t} W' t'` and the block-averaged edge relation. The star/edge tests
cannot separate a fractional refinement across two matrices of different sizes, so
bijectivity is NOT proved here; the consumer (`Graphon/MatrixDetermination.lean`)
combines the two symmetric partitions, forcing `T = T'` by counting, whence all classes
are singletons and the partition collapses to a weight- and entry-preserving bijection.

Only LEFT twin-freeness is needed for the partition.

## Main statements

* `class_balance_two` — the aligned-Vandermonde extraction over two DIFFERENT index
  types (the port of `Lovasz.aligned_moments_class_balance_of_bound`, whose two families
  shared one index type).
* `exists_large_const_image_subset` — pigeonhole: a `ψ`-constant subset of size `≥ M`
  inside each `ξ`-fibre of size `≥ T'·M`.
* `cross_super_partition` — the partition deliverable.
-/

namespace Graphon.CrossSuper

open Finset

/-! ## The two-sided aligned-Vandermonde extraction -/

/-- **Aligned-Vandermonde extraction over two index types** (port of
`Lovasz.aligned_moments_class_balance_of_bound`; there the two profile families shared
one index type, here `ι` and `κ` differ). If the moment sums of the two weighted profile
families agree for every exponent vector bounded by `2·N` (with `N` bounding the number
of distinct values of every coordinate on each side), then the `a`-mass and `b`-mass of
every profile level set agree. -/
theorem class_balance_two {ι κ : Type*} [Fintype ι] [Fintype κ] {s : ℕ}
    (x : ι → Fin s → ℝ) (y : κ → Fin s → ℝ) (a : ι → ℝ) (b : κ → ℝ) (N : ℕ)
    (hNx : ∀ c, (univ.image fun i ↦ x i c).card ≤ N)
    (hNy : ∀ c, (univ.image fun j ↦ y j c).card ≤ N)
    (hmom : ∀ k : Fin s → ℕ, (∀ c, k c < 2 * N) →
        ∑ i, a i * ∏ c, x i c ^ k c = ∑ j, b j * ∏ c, y j c ^ k c)
    (z : Fin s → ℝ) :
    ∑ i ∈ univ.filter (fun i ↦ x i = z), a i
      = ∑ j ∈ univ.filter (fun j ↦ y j = z), b j := by
  classical
  set bb : (ι ⊕ κ) → Fin s → ℝ := Sum.elim x y with hbb
  set aa : (ι ⊕ κ) → ℝ := Sum.elim a (fun j ↦ -b j) with haa
  have hbound : ∀ c, (univ.image (fun p ↦ bb p c)).card ≤ 2 * N := by
    intro c
    have hsub : univ.image (fun p ↦ bb p c)
        ⊆ (univ.image (fun i ↦ x i c)) ∪ (univ.image (fun j ↦ y j c)) := by
      rw [Finset.image_subset_iff]
      rintro (i | j) _
      · simp only [hbb, Sum.elim_inl]
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (mem_univ i))
      · simp only [hbb, Sum.elim_inr]
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (mem_univ j))
    calc (univ.image (fun p ↦ bb p c)).card
        ≤ ((univ.image (fun i ↦ x i c)) ∪ (univ.image (fun j ↦ y j c))).card :=
          Finset.card_le_card hsub
      _ ≤ (univ.image (fun i ↦ x i c)).card + (univ.image (fun j ↦ y j c)).card :=
          Finset.card_union_le _ _
      _ ≤ N + N := Nat.add_le_add (hNx c) (hNy c)
      _ = 2 * N := (two_mul N).symm
  have hmoments : ∀ ℓ : Fin s → ℕ, (∀ c, ℓ c < 2 * N) →
      ∑ p, aa p * ∏ c, bb p c ^ ℓ c = 0 := by
    intro ℓ hb
    rw [Fintype.sum_sum_type]
    simp only [hbb, haa, Sum.elim_inl, Sum.elim_inr]
    rw [hmom ℓ hb]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring
  have key := Graphon.CaiGovorov.multivariate_vandermonde_class_sums_zero_of_bound bb aa
    (2 * N) hbound hmoments z
  rw [Finset.sum_filter, Fintype.sum_sum_type] at key
  simp only [hbb, haa, Sum.elim_inl, Sum.elim_inr, ← Finset.sum_filter] at key
  have hneg : ∑ j ∈ univ.filter (fun j ↦ y j = z), -b j
      = -∑ j ∈ univ.filter (fun j ↦ y j = z), b j := Finset.sum_neg_distrib b
  rw [hneg] at key
  linarith

/-! ## Pigeonhole and block regrouping -/

/-- **Pigeonhole** (port of `Lovasz.exists_large_const_image_subset`). Inside each
`ξ`-fibre of size `≥ T'·M` there is a subset of size `≥ M` on which `ψ` is constant. -/
theorem exists_large_const_image_subset {T T' K : ℕ} (ξ : Fin K → Fin T)
    (ψ : Fin K → Fin T') (M : ℕ) (hT' : 0 < T')
    (hξ : ∀ v : Fin T, T' * M ≤ (univ.filter (fun i ↦ ξ i = v)).card) (v : Fin T) :
    ∃ (gv : Fin T') (J : Finset (Fin K)),
      J ⊆ univ.filter (fun i ↦ ξ i = v) ∧ M ≤ J.card ∧ ∀ i ∈ J, ψ i = gv := by
  classical
  have hmaps : ∀ i ∈ univ.filter (fun i ↦ ξ i = v), ψ i ∈ (univ : Finset (Fin T')) :=
    fun i _ ↦ mem_univ _
  have hcard : (univ : Finset (Fin T')).card * M
      ≤ (univ.filter (fun i ↦ ξ i = v)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact hξ v
  have hne : (univ : Finset (Fin T')).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hT')
  obtain ⟨gv, _, hgv⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hmaps hne hcard
  exact ⟨gv, (univ.filter (fun i ↦ ξ i = v)).filter (fun i ↦ ψ i = gv),
    Finset.filter_subset _ _, hgv, fun i hi ↦ (Finset.mem_filter.mp hi).2⟩

/-- Regroup a product over a pairwise-disjoint union `⋃ᵥ J v` of a function that is
constant (`= c v`) on each block into `∏ᵥ (c v) ^ (k v)`, where `k v` is the block size
(port of `Lovasz.prod_biUnion_const`). -/
theorem prod_biUnion_const {T K : ℕ} {J : Fin T → Finset (Fin K)}
    (hdisj : Set.PairwiseDisjoint (↑(univ : Finset (Fin T))) J)
    {f : Fin K → ℝ} {c : Fin T → ℝ} (hc : ∀ v, ∀ i ∈ J v, f i = c v)
    {k : Fin T → ℕ} (hcard : ∀ v, (J v).card = k v) :
    ∏ i ∈ univ.biUnion J, f i = ∏ v, (c v) ^ k v := by
  rw [Finset.prod_biUnion hdisj]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  have hconst : ∏ i ∈ J v, f i = ∏ i ∈ J v, c v :=
    Finset.prod_congr rfl fun i hi ↦ hc v i hi
  rw [hconst, Finset.prod_const, hcard v]

/-- `class_balance_two` over an arbitrary finite coordinate type (reindexed through
`Fintype.equivFin`). -/
theorem class_balance_two' {ι κ γ : Type*} [Fintype ι] [Fintype κ] [Fintype γ]
    (x : ι → γ → ℝ) (y : κ → γ → ℝ) (a : ι → ℝ) (b : κ → ℝ) (N : ℕ)
    (hNx : ∀ c, (univ.image fun i ↦ x i c).card ≤ N)
    (hNy : ∀ c, (univ.image fun j ↦ y j c).card ≤ N)
    (hmom : ∀ k : γ → ℕ, (∀ c, k c < 2 * N) →
        ∑ i, a i * ∏ c, x i c ^ k c = ∑ j, b j * ∏ c, y j c ^ k c)
    (z : γ → ℝ) :
    ∑ i ∈ univ.filter (fun i ↦ x i = z), a i
      = ∑ j ∈ univ.filter (fun j ↦ y j = z), b j := by
  classical
  let e : γ ≃ Fin (Fintype.card γ) := Fintype.equivFin γ
  have hmom' : ∀ k : Fin (Fintype.card γ) → ℕ, (∀ c, k c < 2 * N) →
      ∑ i, a i * ∏ c, x i (e.symm c) ^ k c = ∑ j, b j * ∏ c, y j (e.symm c) ^ k c := by
    intro k hk
    have hx : ∀ i : ι, ∏ c, x i (e.symm c) ^ k c = ∏ c, x i c ^ k (e c) := fun i ↦ by
      rw [← Equiv.prod_comp e (fun c ↦ x i (e.symm c) ^ k c)]
      exact Finset.prod_congr rfl fun c _ ↦ by rw [Equiv.symm_apply_apply]
    have hy : ∀ j : κ, ∏ c, y j (e.symm c) ^ k c = ∏ c, y j c ^ k (e c) := fun j ↦ by
      rw [← Equiv.prod_comp e (fun c ↦ y j (e.symm c) ^ k c)]
      exact Finset.prod_congr rfl fun c _ ↦ by rw [Equiv.symm_apply_apply]
    simp only [hx, hy]
    exact hmom (fun c ↦ k (e c)) (fun c ↦ hk (e c))
  have key := class_balance_two (fun i c ↦ x i (e.symm c)) (fun j c ↦ y j (e.symm c))
    a b N (fun c ↦ hNx (e.symm c)) (fun c ↦ hNy (e.symm c)) hmom' (fun c ↦ z (e.symm c))
  have hfx : ∀ i : ι, ((fun c ↦ x i (e.symm c)) = fun c ↦ z (e.symm c)) ↔ x i = z := by
    intro i
    constructor
    · intro hfun
      funext c
      have := congrFun hfun (e c)
      simpa [Equiv.symm_apply_apply] using this
    · rintro rfl; rfl
  have hfy : ∀ j : κ, ((fun c ↦ y j (e.symm c)) = fun c ↦ z (e.symm c)) ↔ y j = z := by
    intro j
    constructor
    · intro hfun
      funext c
      have := congrFun hfun (e c)
      simpa [Equiv.symm_apply_apply] using this
    · rintro rfl; rfl
  rwa [Finset.filter_congr (fun i _ ↦ hfx i), Finset.filter_congr (fun j _ ↦ hfy j)] at key

/-! ## Aligned star moments and the weight balance -/

/-- Exponent label-set selection (port of `Lovasz.exists_exponent_label_set`): inside
given blocks of size `≥ 2·(T+T')`, select sub-blocks of exact sizes `k v`. -/
theorem exists_exponent_label_set {T T' K : ℕ} {J : Fin T → Finset (Fin K)}
    (hJcard : ∀ v, 2 * (T + T') ≤ (J v).card)
    (k : Fin T → ℕ) (hk : ∀ v, k v < 2 * (T + T')) :
    ∃ Kf : Fin T → Finset (Fin K),
      (∀ v, Kf v ⊆ J v) ∧ (∀ v, (Kf v).card = k v) := by
  choose Kf hsub hc using fun v ↦
    Finset.exists_subset_card_eq (s := J v) (n := k v)
      (le_trans (hk v).le (hJcard v))
  exact ⟨Kf, hsub, hc⟩

/-- Blocks lying in distinct `ξ`-fibres are pairwise disjoint. -/
theorem fiber_blocks_pairwiseDisjoint {T K : ℕ} {ξ : Fin K → Fin T}
    {J : Fin T → Finset (Fin K)}
    (hsub : ∀ v, J v ⊆ univ.filter (fun i ↦ ξ i = v)) :
    Set.PairwiseDisjoint (↑(univ : Finset (Fin T))) J := by
  intro v _ v' _ hvv'
  refine Finset.disjoint_left.mpr fun i hi hi' ↦ hvv' ?_
  have h1 := (Finset.mem_filter.mp (hsub v hi)).2
  have h2 := (Finset.mem_filter.mp (hsub v' hi')).2
  rw [← h1, ← h2]

/-- **Aligned star-moment bridge** (port of `Lovasz.aligned_moments_of_testEvalEq_super`).
With `ξ ≡ v` and `ψ ≡ g v` on each block `J v`, the star-test equalities specialize, for
every bounded exponent vector `k`, to the aligned cross-moment identity. -/
theorem aligned_star_moments {T T' K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (B' : Fin T' → Fin T' → ℝ) (W' : Fin T' → ℝ)
    (ξ : Fin K → Fin T) (ψ : Fin K → Fin T')
    (g : Fin T → Fin T') (J : Fin T → Finset (Fin K))
    (hsub : ∀ v, J v ⊆ univ.filter (fun i ↦ ξ i = v))
    (hJcard : ∀ v, 2 * (T + T') ≤ (J v).card)
    (hconst : ∀ v, ∀ i ∈ J v, ψ i = g v)
    (hstar : ∀ S : Finset (Fin K),
      ∑ t, W t * ∏ i ∈ S, B (ξ i) t = ∑ t', W' t' * ∏ i ∈ S, B' (ψ i) t')
    (k : Fin T → ℕ) (hk : ∀ v, k v < 2 * (T + T')) :
    ∑ t, W t * ∏ v, (B v t) ^ k v = ∑ t', W' t' * ∏ v, (B' (g v) t') ^ k v := by
  classical
  obtain ⟨Kf, hKf_sub, hKf_card⟩ := exists_exponent_label_set (T' := T') hJcard k hk
  have hdisj : Set.PairwiseDisjoint (↑(univ : Finset (Fin T))) Kf :=
    fiber_blocks_pairwiseDisjoint (fun v ↦ (hKf_sub v).trans (hsub v))
  have hLHS : ∀ t, ∏ i ∈ univ.biUnion Kf, B (ξ i) t = ∏ v, (B v t) ^ k v := fun t ↦
    prod_biUnion_const hdisj
      (fun v i hi ↦ by
        rw [(Finset.mem_filter.mp (hsub v (hKf_sub v hi))).2])
      hKf_card
  have hRHS : ∀ t', ∏ i ∈ univ.biUnion Kf, B' (ψ i) t' = ∏ v, (B' (g v) t') ^ k v :=
    fun t' ↦ prod_biUnion_const hdisj
      (fun v i hi ↦ by rw [hconst v i (hKf_sub v hi)])
      hKf_card
  calc ∑ t, W t * ∏ v, (B v t) ^ k v
      = ∑ t, W t * ∏ i ∈ univ.biUnion Kf, B (ξ i) t :=
        Finset.sum_congr rfl fun t _ ↦ by rw [hLHS t]
    _ = ∑ t', W' t' * ∏ i ∈ univ.biUnion Kf, B' (ψ i) t' := hstar _
    _ = ∑ t', W' t' * ∏ v, (B' (g v) t') ^ k v :=
        Finset.sum_congr rfl fun t' _ ↦ by rw [hRHS t']

open scoped Classical in
/-- The matching class of a left vertex `t`: right vertices whose `g`-probed profile
equals the column profile of `t`. -/
noncomputable def matchClass {T T' : ℕ} (B : Fin T → Fin T → ℝ) (B' : Fin T' → Fin T' → ℝ)
    (g : Fin T → Fin T') (t : Fin T) : Finset (Fin T') :=
  univ.filter (fun t' ↦ ∀ v, B v t = B' (g v) t')

/-- **Weight balance** (port of `Lovasz.aligned_star_moments_weight_balance`): left
twin-freeness collapses the left profile level set to `{t}`, so the two-sided
Vandermonde extraction reads `W t = ∑_{t' ∈ matchClass t} W' t'`. -/
theorem cross_weight_balance {T T' : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (B' : Fin T' → Fin T' → ℝ) (W' : Fin T' → ℝ)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j)
    (g : Fin T → Fin T')
    (haligned : ∀ k : Fin T → ℕ, (∀ v, k v < 2 * (T + T')) →
        ∑ t, W t * ∏ v, (B v t) ^ k v = ∑ t', W' t' * ∏ v, (B' (g v) t') ^ k v)
    (t : Fin T) :
    W t = ∑ t' ∈ matchClass B B' g t, W' t' := by
  classical
  have hNx : ∀ c : Fin T, (univ.image fun t ↦ B c t).card ≤ T + T' := fun c ↦
    le_trans (Finset.card_image_le.trans (by simp)) (Nat.le_add_right T T')
  have hNy : ∀ c : Fin T, (univ.image fun t' ↦ B' (g c) t').card ≤ T + T' := fun c ↦
    le_trans (Finset.card_image_le.trans (by simp)) (Nat.le_add_left T' T)
  have hbal := class_balance_two (fun t v ↦ B v t) (fun t' v ↦ B' (g v) t') W W'
    (T + T') hNx hNy haligned (fun v ↦ B v t)
  have hsingle : (univ.filter (fun u ↦ (fun v ↦ B v u) = fun v ↦ B v t)) = {t} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hprof
      by_contra hne
      refine htwin u t hne ?_
      funext v
      rw [hB u v, hB t v]
      exact congrFun hprof v
    · rintro rfl; rfl
  rw [hsingle, Finset.sum_singleton] at hbal
  rw [hbal]
  refine Finset.sum_congr ?_ (fun _ _ ↦ rfl)
  apply Finset.filter_congr
  intro t' _
  constructor
  · intro h v; exact (congrFun h v).symm
  · intro h; funext v; exact (h v).symm

/-! ## Aligned edge moments and the pair balance -/

/-- **Aligned edge-moment bridge** (port of
`Lovasz.aligned_edge_moments_of_testEvalEq_super`). With `ξ ≡ v` and `ψ ≡ g v` on each
block, the edge-test equalities specialize to the aligned cross pair-moment identity. -/
theorem aligned_edge_moments {T T' K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (B' : Fin T' → Fin T' → ℝ) (W' : Fin T' → ℝ)
    (ξ : Fin K → Fin T) (ψ : Fin K → Fin T')
    (g : Fin T → Fin T') (J : Fin T → Finset (Fin K))
    (hsub : ∀ v, J v ⊆ univ.filter (fun i ↦ ξ i = v))
    (hJcard : ∀ v, 2 * (T + T') ≤ (J v).card)
    (hconst : ∀ v, ∀ i ∈ J v, ψ i = g v)
    (hedge : ∀ Sₗ Sτ : Finset (Fin K),
      ∑ t, ∑ u, W t * W u * B t u * (∏ i ∈ Sₗ, B (ξ i) t) * (∏ i ∈ Sτ, B (ξ i) u)
        = ∑ t', ∑ u', W' t' * W' u' * B' t' u'
            * (∏ i ∈ Sₗ, B' (ψ i) t') * (∏ i ∈ Sτ, B' (ψ i) u'))
    (k l : Fin T → ℕ) (hk : ∀ v, k v < 2 * (T + T')) (hl : ∀ v, l v < 2 * (T + T')) :
    ∑ x, ∑ y, W x * W y * B x y * (∏ v, (B v x) ^ k v) * (∏ v, (B v y) ^ l v)
      = ∑ x', ∑ y', W' x' * W' y' * B' x' y'
          * (∏ v, (B' (g v) x') ^ k v) * (∏ v, (B' (g v) y') ^ l v) := by
  classical
  obtain ⟨Kf, hKf_sub, hKf_card⟩ := exists_exponent_label_set (T' := T') hJcard k hk
  obtain ⟨Lf, hLf_sub, hLf_card⟩ := exists_exponent_label_set (T' := T') hJcard l hl
  have hKdisj : Set.PairwiseDisjoint (↑(univ : Finset (Fin T))) Kf :=
    fiber_blocks_pairwiseDisjoint (fun v ↦ (hKf_sub v).trans (hsub v))
  have hLdisj : Set.PairwiseDisjoint (↑(univ : Finset (Fin T))) Lf :=
    fiber_blocks_pairwiseDisjoint (fun v ↦ (hLf_sub v).trans (hsub v))
  have hKL : ∀ t, ∏ i ∈ univ.biUnion Kf, B (ξ i) t = ∏ v, (B v t) ^ k v := fun t ↦
    prod_biUnion_const hKdisj
      (fun v i hi ↦ by rw [(Finset.mem_filter.mp (hsub v (hKf_sub v hi))).2]) hKf_card
  have hLL : ∀ t, ∏ i ∈ univ.biUnion Lf, B (ξ i) t = ∏ v, (B v t) ^ l v := fun t ↦
    prod_biUnion_const hLdisj
      (fun v i hi ↦ by rw [(Finset.mem_filter.mp (hsub v (hLf_sub v hi))).2]) hLf_card
  have hKR : ∀ t', ∏ i ∈ univ.biUnion Kf, B' (ψ i) t' = ∏ v, (B' (g v) t') ^ k v :=
    fun t' ↦ prod_biUnion_const hKdisj
      (fun v i hi ↦ by rw [hconst v i (hKf_sub v hi)]) hKf_card
  have hLR : ∀ t', ∏ i ∈ univ.biUnion Lf, B' (ψ i) t' = ∏ v, (B' (g v) t') ^ l v :=
    fun t' ↦ prod_biUnion_const hLdisj
      (fun v i hi ↦ by rw [hconst v i (hLf_sub v hi)]) hLf_card
  calc ∑ x, ∑ y, W x * W y * B x y * (∏ v, (B v x) ^ k v) * (∏ v, (B v y) ^ l v)
      = ∑ x, ∑ y, W x * W y * B x y * (∏ i ∈ univ.biUnion Kf, B (ξ i) x)
          * (∏ i ∈ univ.biUnion Lf, B (ξ i) y) :=
        Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ by
          rw [hKL x, hLL y]
    _ = ∑ x', ∑ y', W' x' * W' y' * B' x' y' * (∏ i ∈ univ.biUnion Kf, B' (ψ i) x')
          * (∏ i ∈ univ.biUnion Lf, B' (ψ i) y') := hedge _ _
    _ = ∑ x', ∑ y', W' x' * W' y' * B' x' y'
          * (∏ v, (B' (g v) x') ^ k v) * (∏ v, (B' (g v) y') ^ l v) :=
        Finset.sum_congr rfl fun x' _ ↦ Finset.sum_congr rfl fun y' _ ↦ by
          rw [hKR x', hLR y']

/-- **Pair balance** (port of `Lovasz.aligned_edge_moments_pair_balance`): left
twin-freeness collapses the left pair level set to `{(t, u)}`, so the two-sided 2D
Vandermonde extraction reads the block-averaged edge relation. -/
theorem cross_edge_balance {T T' : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (B' : Fin T' → Fin T' → ℝ) (W' : Fin T' → ℝ)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j)
    (g : Fin T → Fin T')
    (haligned : ∀ k l : Fin T → ℕ,
      (∀ v, k v < 2 * (T + T')) → (∀ v, l v < 2 * (T + T')) →
        ∑ x, ∑ y, W x * W y * B x y * (∏ v, (B v x) ^ k v) * (∏ v, (B v y) ^ l v)
          = ∑ x', ∑ y', W' x' * W' y' * B' x' y'
              * (∏ v, (B' (g v) x') ^ k v) * (∏ v, (B' (g v) y') ^ l v))
    (t u : Fin T) :
    W t * W u * B t u
      = ∑ t' ∈ matchClass B B' g t, ∑ u' ∈ matchClass B B' g u,
          W' t' * W' u' * B' t' u' := by
  classical
  have himgL : ∀ (v : Fin T) (f : Fin T × Fin T → Fin T),
      (univ.image fun p ↦ B v (f p)).card ≤ T + T' := by
    intro v f
    have hsub' : (univ.image fun p : Fin T × Fin T ↦ B v (f p))
        ⊆ univ.image (fun x ↦ B v x) := by
      rw [Finset.image_subset_iff]
      intro p _
      exact Finset.mem_image_of_mem _ (mem_univ (f p))
    exact le_trans (Finset.card_le_card hsub')
      (le_trans (Finset.card_image_le.trans (by simp)) (Nat.le_add_right T T'))
  have himgR : ∀ (v : Fin T) (f : Fin T' × Fin T' → Fin T'),
      (univ.image fun q ↦ B' (g v) (f q)).card ≤ T + T' := by
    intro v f
    have hsub' : (univ.image fun q : Fin T' × Fin T' ↦ B' (g v) (f q))
        ⊆ univ.image (fun x ↦ B' (g v) x) := by
      rw [Finset.image_subset_iff]
      intro q _
      exact Finset.mem_image_of_mem _ (mem_univ (f q))
    exact le_trans (Finset.card_le_card hsub')
      (le_trans (Finset.card_image_le.trans (by simp)) (Nat.le_add_left T' T))
  have hbal := class_balance_two'
    (x := fun p : Fin T × Fin T ↦ Sum.elim (fun v ↦ B v p.1) (fun v ↦ B v p.2))
    (y := fun q : Fin T' × Fin T' ↦
      Sum.elim (fun v ↦ B' (g v) q.1) (fun v ↦ B' (g v) q.2))
    (a := fun p ↦ W p.1 * W p.2 * B p.1 p.2)
    (b := fun q ↦ W' q.1 * W' q.2 * B' q.1 q.2)
    (N := T + T')
    (fun c ↦ by cases c with
      | inl v => exact himgL v Prod.fst
      | inr v => exact himgL v Prod.snd)
    (fun c ↦ by cases c with
      | inl v => exact himgR v Prod.fst
      | inr v => exact himgR v Prod.snd)
    (fun k hk ↦ by
      have hL : ∀ p : Fin T × Fin T,
          ∏ c, Sum.elim (fun v ↦ B v p.1) (fun v ↦ B v p.2) c ^ k c
            = (∏ v, (B v p.1) ^ k (Sum.inl v)) * ∏ v, (B v p.2) ^ k (Sum.inr v) :=
        fun p ↦ by rw [Fintype.prod_sum_type]; simp only [Sum.elim_inl, Sum.elim_inr]
      have hR : ∀ q : Fin T' × Fin T',
          ∏ c, Sum.elim (fun v ↦ B' (g v) q.1) (fun v ↦ B' (g v) q.2) c ^ k c
            = (∏ v, (B' (g v) q.1) ^ k (Sum.inl v))
                * ∏ v, (B' (g v) q.2) ^ k (Sum.inr v) :=
        fun q ↦ by rw [Fintype.prod_sum_type]; simp only [Sum.elim_inl, Sum.elim_inr]
      simp only [hL, hR]
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      have := haligned (fun v ↦ k (Sum.inl v)) (fun v ↦ k (Sum.inr v))
        (fun v ↦ hk (Sum.inl v)) (fun v ↦ hk (Sum.inr v))
      calc ∑ p1, ∑ p2, W p1 * W p2 * B p1 p2
            * ((∏ v, (B v p1) ^ k (Sum.inl v)) * ∏ v, (B v p2) ^ k (Sum.inr v))
          = ∑ p1, ∑ p2, W p1 * W p2 * B p1 p2
              * (∏ v, (B v p1) ^ k (Sum.inl v)) * ∏ v, (B v p2) ^ k (Sum.inr v) :=
            Finset.sum_congr rfl fun p1 _ ↦ Finset.sum_congr rfl fun p2 _ ↦ by ring
        _ = ∑ q1, ∑ q2, W' q1 * W' q2 * B' q1 q2
              * (∏ v, (B' (g v) q1) ^ k (Sum.inl v))
              * ∏ v, (B' (g v) q2) ^ k (Sum.inr v) := this
        _ = ∑ q1, ∑ q2, W' q1 * W' q2 * B' q1 q2
              * ((∏ v, (B' (g v) q1) ^ k (Sum.inl v))
                * ∏ v, (B' (g v) q2) ^ k (Sum.inr v)) :=
            Finset.sum_congr rfl fun q1 _ ↦ Finset.sum_congr rfl fun q2 _ ↦ by ring)
    (z := Sum.elim (fun v ↦ B v t) (fun v ↦ B v u))
  have hsingle : (univ.filter fun p : Fin T × Fin T ↦
      Sum.elim (fun v ↦ B v p.1) (fun v ↦ B v p.2)
        = Sum.elim (fun v ↦ B v t) (fun v ↦ B v u)) = {(t, u)} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hprof
      have h1 : ∀ v, B v p.1 = B v t := fun v ↦ by
        simpa using congrFun hprof (Sum.inl v)
      have h2 : ∀ v, B v p.2 = B v u := fun v ↦ by
        simpa using congrFun hprof (Sum.inr v)
      have hp1 : p.1 = t := by
        by_contra hne
        exact htwin p.1 t hne (funext fun v ↦ by rw [hB p.1 v, hB t v]; exact h1 v)
      have hp2 : p.2 = u := by
        by_contra hne
        exact htwin p.2 u hne (funext fun v ↦ by rw [hB p.2 v, hB u v]; exact h2 v)
      exact Prod.ext hp1 hp2
    · rintro rfl; rfl
  have hprod : (univ.filter fun q : Fin T' × Fin T' ↦
      Sum.elim (fun v ↦ B' (g v) q.1) (fun v ↦ B' (g v) q.2)
        = Sum.elim (fun v ↦ B v t) (fun v ↦ B v u))
      = matchClass B B' g t ×ˢ matchClass B B' g u := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      matchClass]
    constructor
    · intro hprof
      refine ⟨fun v ↦ ?_, fun v ↦ ?_⟩
      · simpa using (congrFun hprof (Sum.inl v)).symm
      · simpa using (congrFun hprof (Sum.inr v)).symm
    · rintro ⟨h1, h2⟩
      funext c
      cases c with
      | inl v => simpa using (h1 v).symm
      | inr v => simpa using (h2 v).symm
  rw [hsingle, hprod, Finset.sum_singleton] at hbal
  rw [hbal, Finset.sum_product]

/-! ## The partition deliverable -/

/-- **Cross-matrix super partition** (Cai–Govorov Lemma 5.1, two-matrix partition form).
From matched test-moment profiles of a left tuple `ξ` with fibers of size
`≥ T'·2·(T+T')` and a right tuple `ψ`, the right vertex set partitions into classes
`C t` (one per left vertex) with matching weights and block-averaged entries. Only LEFT
twin-freeness is used. -/
theorem cross_super_partition {T T' K : ℕ}
    (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (B' : Fin T' → Fin T' → ℝ) (W' : Fin T' → ℝ)
    (hB_symm : ∀ i j, B i j = B j i)
    (hW_pos : ∀ i, 0 < W i) (hW'_pos : ∀ i, 0 < W' i)
    (htwin : ∀ i j : Fin T, i ≠ j → B i ≠ B j)
    (hT' : 0 < T')
    (ξ : Fin K → Fin T) (ψ : Fin K → Fin T')
    (hsup : ∀ v : Fin T,
      T' * (2 * (T + T')) ≤ (univ.filter (fun i ↦ ξ i = v)).card)
    (hmatch : ∀ c : Graphon.Lovasz.TestCoord K,
      Graphon.Lovasz.testMoment B W c ξ = Graphon.Lovasz.testMoment B' W' c ψ) :
    ∃ C : Fin T → Finset (Fin T'),
      (∀ t, (C t).Nonempty) ∧
      (∀ t u, t ≠ u → Disjoint (C t) (C u)) ∧
      (∀ t' : Fin T', ∃ t, t' ∈ C t) ∧
      (∀ t, W t = ∑ t' ∈ C t, W' t') ∧
      (∀ t u, W t * W u * B t u
        = ∑ t' ∈ C t, ∑ u' ∈ C u, W' t' * W' u' * B' t' u') := by
  classical
  -- The pigeonhole data: blocks and the preliminary map.
  choose g J hsub hJcard hconst using fun v ↦
    exists_large_const_image_subset ξ ψ (2 * (T + T')) hT' hsup v
  -- Closed forms of the matched test moments.
  have hstar : ∀ S : Finset (Fin K),
      ∑ t, W t * ∏ i ∈ S, B (ξ i) t = ∑ t', W' t' * ∏ i ∈ S, B' (ψ i) t' := fun S ↦ by
    simpa [Graphon.Lovasz.testMoment] using hmatch (Sum.inl S)
  have hedge : ∀ Sₗ Sτ : Finset (Fin K),
      ∑ t, ∑ u, W t * W u * B t u * (∏ i ∈ Sₗ, B (ξ i) t) * (∏ i ∈ Sτ, B (ξ i) u)
        = ∑ t', ∑ u', W' t' * W' u' * B' t' u'
            * (∏ i ∈ Sₗ, B' (ψ i) t') * (∏ i ∈ Sτ, B' (ψ i) u') := fun Sₗ Sτ ↦ by
    simpa [Graphon.Lovasz.testMoment] using hmatch (Sum.inr (Sₗ, Sτ))
  -- The aligned identities.
  have haligned := aligned_star_moments B W B' W' ξ ψ g J hsub hJcard hconst hstar
  have haligned2 := aligned_edge_moments B W B' W' ξ ψ g J hsub hJcard hconst hedge
  refine ⟨matchClass B B' g, ?_, ?_, ?_, ?_, ?_⟩
  · -- Nonempty: the class carries the full weight W t > 0.
    intro t
    have hbal := cross_weight_balance B hB_symm W B' W' htwin g haligned t
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.sum_empty] at hbal
    exact (hW_pos t).ne' hbal
  · -- Disjoint: a shared member forces equal columns, hence equal rows.
    intro t u htu
    refine Finset.disjoint_left.mpr fun t' ht ht' ↦ htu ?_
    simp only [matchClass, Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
    by_contra hne
    refine htwin t u hne (funext fun v ↦ ?_)
    rw [hB_symm t v, hB_symm u v, ht v, ht' v]
  · -- Covering: total weights match and all weights are positive.
    intro t'
    by_contra hnone
    push Not at hnone
    have hdisj' : Set.PairwiseDisjoint (↑(univ : Finset (Fin T)))
        (matchClass B B' g) := by
      intro t _ u _ htu
      refine Finset.disjoint_left.mpr fun x hx hx' ↦ htu ?_
      simp only [matchClass, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
      by_contra hne
      refine htwin t u hne (funext fun v ↦ ?_)
      rw [hB_symm t v, hB_symm u v, hx v, hx' v]
    have htot : ∑ t, W t = ∑ t', W' t' := by simpa using hstar ∅
    have hU : ∑ t, W t = ∑ x ∈ univ.biUnion (matchClass B B' g), W' x := by
      rw [Finset.sum_biUnion hdisj']
      exact Finset.sum_congr rfl fun t _ ↦
        cross_weight_balance B hB_symm W B' W' htwin g haligned t
    have hmem : t' ∉ univ.biUnion (matchClass B B' g) := by
      rw [Finset.mem_biUnion]
      rintro ⟨t, _, ht⟩
      exact hnone t ht
    have hlt : ∑ x ∈ univ.biUnion (matchClass B B' g), W' x < ∑ x, W' x :=
      Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (mem_univ t') hmem
        (hW'_pos t') (fun x _ _ ↦ (hW'_pos x).le)
    rw [← hU, htot] at hlt
    exact lt_irrefl _ hlt
  · exact cross_weight_balance B hB_symm W B' W' htwin g haligned
  · exact cross_edge_balance B hB_symm W B' W' htwin g haligned2

end Graphon.CrossSuper
