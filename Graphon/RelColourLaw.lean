/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelLatentLocalization

/-!
# Colour laws on a one-sort, one-relation signature (R4 converse, #107)

Route-neutral machinery for laws on `oneSortSig k` — one sort and one relation of arity `k` —
built from independent fair vertex colours. A structure
`F d` is read off a Boolean colouring `d : ℕ → Bool`; the colours come from the fresh singleton
layer of the rank-two latent cube. When `F` is equivariant and depends on the colouring only
through its differences, the law `colourLaw F` is exchangeable and its empty and singleton fixing
algebras are trivial modulo the law (`fixing_trivial_of_card_lt_two`): the pullback of a fixing
event to the cube is invariant under permutations fixing the vertex, hence almost surely a
function of the local window there by the relative Hewitt–Savage theorem, while it is also a
function of the colouring relative to that vertex, which is independent of the window
(`indepFun_relColour_window`).

Consumed by the ternary parity regression and by the bipartite screening test.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RelSignature

/-- The one-sort signature with a single relation of arity `k`. -/
abbrev oneSortSig (k : ℕ) : RelSignature where
  Srt := Unit
  Rel := Unit
  arity := fun _ => k
  argSort := fun _ _ => ()

namespace ColourLaw

variable {k : ℕ}

abbrev Colours (k : ℕ) := RankSupport (oneSortSig k) 1 → ℝ

/-- The singleton support at a vertex. -/
def vertexSupport (k : ℕ) (v : ℕ) : RankSupport (oneSortSig k) 1 :=
  ⟨{⟨(), v⟩}, Finset.card_singleton _⟩

variable (k) in
theorem vertexSupport_injective : Function.Injective (vertexSupport k) := by
  intro a b h
  have := congrArg Subtype.val h
  simpa [vertexSupport] using this

/-- The colour of a vertex, read off its own fresh coordinate. -/
noncomputable def colour (ω : Colours k) (v : ℕ) : Bool := decide (ω (vertexSupport k v) ≤ 1 / 2)

theorem measurable_colour (v : ℕ) : Measurable fun ω : Colours k => colour ω v :=
  measurable_decideLe (measurable_pi_apply _)

theorem measurable_colours : Measurable fun ω : Colours k => fun v => colour ω v :=
  measurable_pi_lambda _ measurable_colour

/-! ### The relabeling action on the fresh layer -/

/-- A permutation of the vertices permutes the singleton supports. -/
noncomputable def supportPerm (σ : Equiv.Perm ℕ) :
    RankSupport (oneSortSig k) 1 ≃ RankSupport (oneSortSig k) 1 :=
  rankSupportPerm (fun _ : Unit => σ) 1

open scoped Classical in
@[simp] theorem supportPerm_vertexSupport (σ : Equiv.Perm ℕ) (v : ℕ) :
    supportPerm σ (vertexSupport k v) = vertexSupport k (σ v) := by
  refine Subtype.ext ?_
  show ({(⟨(), v⟩ : Σ _ : Unit, ℕ)} : Finset _).image (Sigma.map id fun _ => ⇑σ)
    = ({⟨(), σ v⟩} : Finset (Σ _ : Unit, ℕ))
  rw [Finset.image_singleton]
  rfl

theorem colour_comp_supportPerm (σ : Equiv.Perm ℕ) (ω : Colours k) (v : ℕ) :
    colour (fun A => ω (supportPerm σ A)) v = colour ω (σ v) := by
  simp [colour]

abbrev Cube (k : ℕ) := RankLatentSpace (oneSortSig k) 2

/-- The fresh singleton layer of a rank-two latent point. -/
noncomputable def freshLayer (ω : Cube k) : Colours k := (rankLatentSpaceSuccEquiv 1 ω).2

theorem measurable_freshLayer : Measurable (freshLayer (k := k)) :=
  (rankLatentSpaceSuccEquiv 1).measurable.snd

theorem source_map_freshLayer :
    (rankLatentSource (oneSortSig k) 2).map freshLayer =
      iidUniformSource (RankSupport (oneSortSig k) 1) := by
  have h : freshLayer (k := k) = Prod.snd ∘ rankLatentSpaceSuccEquiv 1 := rfl
  rw [h, ← Measure.map_map measurable_snd (rankLatentSpaceSuccEquiv 1).measurable,
    rankLatentSource_map_rankLatentSpaceSuccEquiv, Measure.map_snd_prod]
  simp

/-- The finitely supported rank-support action agrees with the full-permutation helper. -/
theorem rankSupportEquiv_eq_supportPerm (σ : FinSuppPerm (oneSortSig k))
    (A : RankSupport (oneSortSig k) 1) : rankSupportEquiv σ 1 A = supportPerm (σ.1 ()) A := by
  refine Subtype.ext ?_
  refine Finset.ext fun w => ?_
  simp only [rankSupportEquiv, supportPerm, rankSupportPerm, Equiv.coe_fn_mk, Finset.mem_image]

open scoped Classical in
theorem freshLayer_rankLatentRelabel (σ : FinSuppPerm (oneSortSig k)) (ω : Cube k) :
    freshLayer (rankLatentRelabel σ 2 ω) = fun A => freshLayer ω (supportPerm (σ.1 ()) A) := by
  funext A
  show (rankLatentSpaceSuccEquiv 1 (rankLatentRelabel σ 2 ω)).2 A = _
  rw [show rankLatentSpaceSuccEquiv 1 (rankLatentRelabel σ 2 ω) =
      MeasurableEquiv.prodCongr (rankLatentRelabel σ 1) (rankSupportLatentRelabel σ 1)
        (rankLatentSpaceSuccEquiv 1 ω) from
    congrFun (rankLatentSpaceSuccEquiv_rankLatentRelabel σ 1) ω]
  show freshLayer ω (rankSupportEquiv σ 1 A) = _
  rw [rankSupportEquiv_eq_supportPerm]

/-- **Exact equivariance on the cube.** -/
def singIndex (k : ℕ) (w : ℕ) : RankLatentIndex (oneSortSig k) 2 :=
  ⟨{⟨(), w⟩}, by simp⟩

variable (k) in
theorem singIndex_injective : Function.Injective (singIndex k) := by
  intro a b h
  have := congrArg Subtype.val h
  simpa [singIndex] using this

/-- The colour of a vertex reads the singleton coordinate. -/
theorem colour_freshLayer (ω : Cube k) (w : ℕ) :
    colour (freshLayer ω) w = decide (ω (singIndex k w) ≤ 1 / 2) := by
  show decide ((rankLatentSpaceSuccEquiv 1 ω).2 (vertexSupport k w) ≤ 1 / 2) = _
  rfl

/-- The colouring relative to a reference vertex `v`: the difference of colours. -/
noncomputable def relColour (v : ℕ) (ω : Cube k) : ℕ → Bool :=
  fun w => xor (colour (freshLayer ω) w) (colour (freshLayer ω) v)

/-- The colouring with the reference vertex blanked out. -/
noncomputable def offColour (v : ℕ) (ω : Cube k) : ℕ → Bool :=
  fun w => if w = v then false else colour (freshLayer ω) w

/-- Flipping every colour except the reference vertex. -/
def flipOff (v : ℕ) (b : Bool) (d : ℕ → Bool) : ℕ → Bool :=
  fun w => if w = v then false else xor (d w) b

theorem measurable_flipOff (v : ℕ) (b : Bool) : Measurable (flipOff v b) :=
  measurable_pi_lambda _ fun w => by
    by_cases h : w = v
    · simp only [flipOff, if_pos h]; exact measurable_const
    · simp only [flipOff, if_neg h]
      exact Measurable.comp (g := fun x : Bool => xor x b) Measurable.of_discrete
        (measurable_pi_apply w)

theorem relColour_eq_flipOff (v : ℕ) (ω : Cube k) :
    relColour v ω = flipOff v (colour (freshLayer ω) v) (offColour v ω) := by
  funext w
  by_cases h : w = v
  · subst h; simp [relColour, flipOff]
  · simp [relColour, flipOff, offColour, h]


theorem measurable_offColour (v : ℕ) : Measurable (offColour (k := k) v) :=
  measurable_pi_lambda _ fun w => by
    by_cases h : w = v
    · simp only [offColour, if_pos h]; exact measurable_const
    · simp only [offColour, if_neg h]
      exact (measurable_colour w).comp measurable_freshLayer

theorem measurable_relColour (v : ℕ) : Measurable (relColour (k := k) v) :=
  measurable_pi_lambda _ fun w =>
    Measurable.comp (g := fun p : Bool × Bool => xor p.1 p.2) Measurable.of_discrete
      (((measurable_colour w).comp measurable_freshLayer).prodMk
        ((measurable_colour v).comp measurable_freshLayer))

/-! ### The local window at a vertex is independent of the relative colouring -/

/-- The singleton support at `v`. -/
def vertexFinset (v : ℕ) : Finset (Σ _ : Unit, ℕ) := {⟨(), v⟩}

variable (k) in
/-- The local window at `v`. -/
noncomputable abbrev window (v : ℕ) :=
  localLatents (S := (oneSortSig k)) (vertexFinset v) 2

theorem measurable_window (v : ℕ) : Measurable (window k v) :=
  measurable_localLatents (S := (oneSortSig k)) _ 2

/-- The reference colour is a function of the local window. -/
theorem colour_v_eq_window (v : ℕ) (ω : Cube k) :
    colour (freshLayer ω) v =
      decide (window k v ω ⟨singIndex k v, by simp [singIndex, vertexFinset]⟩ ≤ 1 / 2) :=
  colour_freshLayer ω v

open scoped Classical in
/-- The blanked colouring reads only singleton coordinates away from `v`, the window reads only
coordinates inside `{v}`: they are independent. -/
theorem indepFun_offColour_window (v : ℕ) :
    IndepFun (offColour v) (window k v) (rankLatentSource (oneSortSig k) 2) := by
  set μ := rankLatentSource (oneSortSig k) 2 with hμ
  set m : RankLatentIndex (oneSortSig k) 2 → MeasurableSpace (Cube k) :=
    fun i => MeasurableSpace.comap (fun ω : Cube k => ω i) inferInstance with hm
  have hind : iIndep m μ := by
    have h := iIndepFun_infinitePi (P := fun _ : RankLatentIndex (oneSortSig k) 2 => uniform01)
      (X := fun _ x => x) fun _ => measurable_id
    exact h
  set Sset : Set (RankLatentIndex (oneSortSig k) 2) := {i | ∃ w, w ≠ v ∧ i = singIndex k w} with hS
  set Tset : Set (RankLatentIndex (oneSortSig k) 2) := {i | i.1 ⊆ vertexFinset v} with hT
  have hST : Disjoint Sset Tset := by
    rw [Set.disjoint_left]
    rintro i ⟨w, hwv, rfl⟩ hi
    apply hwv
    have := hi (Finset.mem_singleton_self (⟨(), w⟩ : Σ _ : Unit, ℕ))
    simpa [vertexFinset] using this
  have hdisj := indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le) hind hST
  have hoffm : @Measurable (Cube k) (ℕ → Bool) (⨆ i ∈ Sset, m i) _ (offColour v) := by
    letI : MeasurableSpace (Cube k) := ⨆ i ∈ Sset, m i
    refine measurable_pi_iff.mpr fun w => ?_
    by_cases h : w = v
    · simp only [offColour, if_pos h]; exact measurable_const
    · simp only [offColour, if_neg h]
      rw [show (fun ω : Cube k => colour (freshLayer ω) w) =
          fun ω => decide (ω (singIndex k w) ≤ 1 / 2) from funext fun ω => colour_freshLayer ω w]
      refine measurable_decideLe ?_
      exact Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ∈ Sset) => m i)
        (singIndex k w) ⟨w, h, rfl⟩)
  have hwinm : @Measurable (Cube k) (LocalLatentSpace (S := (oneSortSig k)) (vertexFinset v) 2)
      (⨆ i ∈ Tset, m i) _ (window k v) := by
    letI : MeasurableSpace (Cube k) := ⨆ i ∈ Tset, m i
    refine measurable_pi_iff.mpr fun B => ?_
    exact Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ∈ Tset) => m i) B.1 B.2)
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hdisj hoffm.comap_le)
    hwinm.comap_le

/-- The uniform threshold bit is fair. -/
theorem uniform01_Iic_half : uniform01 (Set.Iic (1 / 2 : ℝ)) = 1 / 2 := by
  rw [uniform01_Iic (by norm_num)]
  rw [show (1 / 2 : ℝ) = ((1 : ℝ) / 2) from rfl]
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]

theorem uniform01_map_decide_not :
    (uniform01.map fun t : ℝ => decide (t ≤ 1 / 2)).map not =
      uniform01.map fun t : ℝ => decide (t ≤ 1 / 2) := by
  have hm : Measurable fun t : ℝ => decide (t ≤ 1 / 2) := measurable_decideLe measurable_id
  rw [Measure.map_map Measurable.of_discrete hm]
  refine Measure.ext_of_singleton fun b => ?_
  rw [Measure.map_apply (Measurable.of_discrete.comp hm) (measurableSet_singleton b),
    Measure.map_apply hm (measurableSet_singleton b)]
  have h1 : (fun t : ℝ => decide (t ≤ 1 / 2)) ⁻¹' {true} = Set.Iic (1 / 2 : ℝ) := by
    ext t; simp
  have h2 : (fun t : ℝ => decide (t ≤ 1 / 2)) ⁻¹' {false} = (Set.Iic (1 / 2 : ℝ))ᶜ := by
    ext t; simp
  have hc : uniform01 (Set.Iic (1 / 2 : ℝ))ᶜ = 1 / 2 := by
    rw [prob_compl_eq_one_sub measurableSet_Iic, uniform01_Iic_half, one_div,
      ENNReal.one_sub_inv_two]
  cases b
  · rw [show (not ∘ fun t : ℝ => decide (t ≤ 1 / 2)) ⁻¹' {false} =
        (fun t : ℝ => decide (t ≤ 1 / 2)) ⁻¹' {true} from by ext t; simp, h1, h2,
      uniform01_Iic_half, hc]
  · rw [show (not ∘ fun t : ℝ => decide (t ≤ 1 / 2)) ⁻¹' {true} =
        (fun t : ℝ => decide (t ≤ 1 / 2)) ⁻¹' {false} from by ext t; simp, h1, h2,
      uniform01_Iic_half, hc]

/-- The law of the blanked colouring is invariant under flipping all colours off `v`. -/
theorem map_offColour_flip (v : ℕ) :
    (rankLatentSource (oneSortSig k) 2).map (flipOff v true ∘ offColour v) =
      (rankLatentSource (oneSortSig k) 2).map (offColour v) := by
  set g : ℕ → ℝ → Bool := fun w t => if w = v then false else decide (t ≤ 1 / 2) with hg
  set g' : ℕ → ℝ → Bool := fun w t => if w = v then false else !decide (t ≤ 1 / 2) with hg'
  have hgm : ∀ w, Measurable (g w) := fun w => by
    by_cases h : w = v
    · simp only [hg, if_pos h]; exact measurable_const
    · simp only [hg, if_neg h]; exact measurable_decideLe measurable_id
  have hgm' : ∀ w, Measurable (g' w) := fun w => by
    by_cases h : w = v
    · simp only [hg', if_pos h]; exact measurable_const
    · simp only [hg', if_neg h]
      exact Measurable.comp (g := not) Measurable.of_discrete (measurable_decideLe measurable_id)
  have hread : Measurable fun (ω : Cube k) (w : ℕ) => ω (singIndex k w) :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  have hoff : offColour v = (fun (x : ℕ → ℝ) (w : ℕ) => g w (x w)) ∘
      fun (ω : Cube k) (w : ℕ) => ω (singIndex k w) := by
    funext ω w
    simp only [offColour, Function.comp_apply, hg, colour_freshLayer]
  have hflip : flipOff v true ∘ offColour v = (fun (x : ℕ → ℝ) (w : ℕ) => g' w (x w)) ∘
      fun (ω : Cube k) (w : ℕ) => ω (singIndex k w) := by
    funext ω w
    show (if w = v then false else xor (offColour v ω w) true) =
      (if w = v then false else !decide (ω (singIndex k w) ≤ 1 / 2))
    by_cases h : w = v
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      show xor (if w = v then false else colour (freshLayer ω) w) true = _
      rw [if_neg h, colour_freshLayer, Bool.xor_true]
  have hsrc : (rankLatentSource (oneSortSig k) 2).map
      (fun (ω : Cube k) (w : ℕ) => ω (singIndex k w)) =
      Measure.infinitePi fun _ : ℕ => uniform01 := by
    rw [rankLatentSource, iidUniformSource]
    exact Measure.map_infinitePi_infinitePi_of_inj (singIndex_injective k)
  have hψ : Measurable fun (x : ℕ → ℝ) (w : ℕ) => g w (x w) :=
    measurable_pi_lambda _ fun w => (hgm w).comp (measurable_pi_apply w)
  have hψ' : Measurable fun (x : ℕ → ℝ) (w : ℕ) => g' w (x w) :=
    measurable_pi_lambda _ fun w => (hgm' w).comp (measurable_pi_apply w)
  rw [hflip, hoff, ← Measure.map_map hψ' hread, ← Measure.map_map hψ hread, hsrc,
    Measure.infinitePi_map_pi (μ := fun _ : ℕ => uniform01) (f := g') hgm',
    Measure.infinitePi_map_pi (μ := fun _ : ℕ => uniform01) (f := g) hgm]
  congr 1
  funext w
  by_cases h : w = v
  · simp only [hg, hg', if_pos h]
  · simp only [hg, hg', if_neg h]
    rw [← uniform01_map_decide_not, Measure.map_map Measurable.of_discrete
      (measurable_decideLe measurable_id : Measurable fun t : ℝ => decide (t ≤ 1 / 2))]
    rfl

/-- **The relative colouring is independent of the local window at `v`.** -/
theorem indepFun_relColour_window (v : ℕ) :
    IndepFun (relColour v) (window k v) (rankLatentSource (oneSortSig k) 2) := by
  set μ := rankLatentSource (oneSortSig k) 2 with hμ
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro B C hB hC
  have hoff := (indepFun_iff_measure_inter_preimage_eq_mul.mp
    (indepFun_offColour_window (k := k) v))
  -- the two window events reading the reference bit
  set C₀ : Set (LocalLatentSpace (S := (oneSortSig k)) (vertexFinset v) 2) :=
    {ℓ | decide (ℓ ⟨singIndex k v, by simp [singIndex, vertexFinset]⟩ ≤ 1 / 2) = false} with hC₀
  set C₁ : Set (LocalLatentSpace (S := (oneSortSig k)) (vertexFinset v) 2) :=
    {ℓ | decide (ℓ ⟨singIndex k v, by simp [singIndex, vertexFinset]⟩ ≤ 1 / 2) = true} with hC₁
  have hC₀m : MeasurableSet C₀ :=
    (measurable_decideLe (measurable_pi_apply _)) (measurableSet_singleton false)
  have hC₁m : MeasurableSet C₁ :=
    (measurable_decideLe (measurable_pi_apply _)) (measurableSet_singleton true)
  have hbit : ∀ ω : Cube k, colour (freshLayer ω) v = false ↔ window k v ω ∈ C₀ := fun ω => by
    rw [colour_v_eq_window]; rfl
  have hbit' : ∀ ω : Cube k, colour (freshLayer ω) v = true ↔ window k v ω ∈ C₁ := fun ω => by
    rw [colour_v_eq_window]; rfl
  -- split the relative-colour event by the reference bit
  have hsplit : ∀ D : Set (LocalLatentSpace (S := (oneSortSig k)) (vertexFinset v) 2),
      relColour v ⁻¹' B ∩ window k v ⁻¹' D =
        (offColour v ⁻¹' B ∩ window k v ⁻¹' (D ∩ C₀)) ∪
          (offColour v ⁻¹' (flipOff v true ⁻¹' B) ∩ window k v ⁻¹' (D ∩ C₁)) := by
    intro D
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_union, relColour_eq_flipOff]
    rcases hcv : colour (freshLayer ω) v with _ | _
    · have h0 : window k v ω ∈ C₀ := (hbit ω).mp hcv
      have h1 : window k v ω ∉ C₁ := fun h => by
        have := (hbit' ω).mpr h; rw [hcv] at this; exact Bool.false_ne_true this
      have hid : flipOff v false (offColour v ω) = offColour v ω := by
        funext w; by_cases h : w = v <;> simp [flipOff, offColour, h]
      rw [hid]
      constructor
      · rintro ⟨hB', hD⟩; exact Or.inl ⟨hB', hD, h0⟩
      · rintro (⟨hB', hD, -⟩ | ⟨-, -, h⟩)
        · exact ⟨hB', hD⟩
        · exact absurd h h1
    · have h1 : window k v ω ∈ C₁ := (hbit' ω).mp hcv
      have h0 : window k v ω ∉ C₀ := fun h => by
        have := (hbit ω).mpr h; rw [hcv] at this; exact Bool.false_ne_true this.symm
      constructor
      · rintro ⟨hB', hD⟩; exact Or.inr ⟨hB', hD, h1⟩
      · rintro (⟨-, -, h⟩ | ⟨hB', hD, -⟩)
        · exact absurd h h0
        · exact ⟨hB', hD⟩
  have hdisj : ∀ D : Set (LocalLatentSpace (S := (oneSortSig k)) (vertexFinset v) 2),
      Disjoint (offColour v ⁻¹' B ∩ window k v ⁻¹' (D ∩ C₀))
        (offColour v ⁻¹' (flipOff v true ⁻¹' B) ∩ window k v ⁻¹' (D ∩ C₁)) := by
    intro D
    rw [Set.disjoint_left]
    rintro ω ⟨-, -, h0⟩ ⟨-, -, h1⟩
    have := ((hbit ω).mpr h0).symm.trans ((hbit' ω).mpr h1)
    exact Bool.false_ne_true this
  have hflipB : MeasurableSet (flipOff v true ⁻¹' B) := measurable_flipOff v true hB
  have hlaw : μ (offColour v ⁻¹' (flipOff v true ⁻¹' B)) = μ (offColour v ⁻¹' B) := by
    rw [← Set.preimage_comp, ← Measure.map_apply ((measurable_flipOff v true).comp
      (measurable_offColour v)) hB, map_offColour_flip,
      Measure.map_apply (measurable_offColour v) hB]
  -- the general identity
  have key : ∀ D : Set (LocalLatentSpace (S := (oneSortSig k)) (vertexFinset v) 2),
      MeasurableSet D →
      μ (relColour v ⁻¹' B ∩ window k v ⁻¹' D) = μ (offColour v ⁻¹' B) * μ (window k v ⁻¹' D) := by
    intro D hD
    rw [hsplit D, measure_union (hdisj D)
      (((measurable_offColour v) hflipB).inter ((measurable_window v) (hD.inter hC₁m))),
      hoff B (D ∩ C₀) hB (hD.inter hC₀m), hoff (flipOff v true ⁻¹' B) (D ∩ C₁) hflipB
        (hD.inter hC₁m), hlaw, ← mul_add, Set.preimage_inter, Set.preimage_inter,
      ← measure_union ?_ ((measurable_window v) hD |>.inter ((measurable_window v) hC₁m))]
    · congr 1
      rw [← Set.inter_union_distrib_left]
      congr 1
      have hcover : window k v ⁻¹' C₀ ∪ window k v ⁻¹' C₁ = Set.univ := by
        ext ω
        simp only [Set.mem_union, Set.mem_preimage, Set.mem_univ, iff_true]
        rcases h : colour (freshLayer ω) v with _ | _
        · exact Or.inl ((hbit ω).mp h)
        · exact Or.inr ((hbit' ω).mp h)
      rw [hcover, Set.inter_univ]
    · rw [Set.disjoint_left]
      rintro ω ⟨-, h0⟩ ⟨-, h1⟩
      exact Bool.false_ne_true (((hbit ω).mpr h0).symm.trans ((hbit' ω).mpr h1))
  have hB' : μ (relColour v ⁻¹' B) = μ (offColour v ⁻¹' B) := by
    have := key Set.univ MeasurableSet.univ
    simpa using this
  rw [key C hC, hB']

theorem uniform01_Iic_half_compl : uniform01 (Set.Iic (1 / 2 : ℝ))ᶜ = 1 / 2 := by
  rw [prob_compl_eq_one_sub measurableSet_Iic, uniform01_Iic_half, one_div,
    ENNReal.one_sub_inv_two]

/-- Two distinct vertices' colours are two independent fair bits. -/
theorem source_colour_pair {u v : ℕ} (huv : u ≠ v) (b : Bool) :
    iidUniformSource (RankSupport (oneSortSig k) 1)
      {ω | colour ω u = b ∧ colour ω v = !b} = 1 / 4 := by
  classical
  have hne : vertexSupport k u ≠ vertexSupport k v := fun h => huv (vertexSupport_injective k h)
  set t : RankSupport (oneSortSig k) 1 → Set ℝ := fun A =>
    if A = vertexSupport k u then (if b then Set.Iic (1 / 2 : ℝ) else (Set.Iic (1 / 2 : ℝ))ᶜ)
    else (if b then (Set.Iic (1 / 2 : ℝ))ᶜ else Set.Iic (1 / 2 : ℝ)) with ht
  have hset : {ω : Colours k | colour ω u = b ∧ colour ω v = !b} =
      Set.pi ({vertexSupport k u, vertexSupport k v} :
        Finset (RankSupport (oneSortSig k) 1)) t := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, ht,
      if_neg hne.symm, colour]
    cases b <;> simp
  have hmeas : ∀ A ∈ ({vertexSupport k u, vertexSupport k v} :
      Finset (RankSupport (oneSortSig k) 1)), MeasurableSet (t A) := by
    intro A _
    simp only [ht]
    split_ifs <;> first | exact measurableSet_Iic | exact measurableSet_Iic.compl
  rw [hset, iidUniformSource, Measure.infinitePi_pi _ hmeas, Finset.prod_pair hne]
  simp only [ht, if_pos rfl, if_neg hne.symm]
  have h4 : (2 : ℝ≥0∞)⁻¹ * 2⁻¹ = 4⁻¹ := by
    rw [← ENNReal.mul_inv (by simp) (by simp)]; norm_num
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, uniform01_Iic_half_compl, uniform01_Iic_half]
    rw [one_div, one_div, h4]
  · simp only [↓reduceIte, uniform01_Iic_half_compl, uniform01_Iic_half]
    rw [one_div, one_div, h4]


/-! ### Laws read off the colouring -/

/-- The full colouring of a fresh layer. -/
noncomputable def colours (ω : Colours k) : ℕ → Bool := fun v => colour ω v

variable (F : (ℕ → Bool) → RelStructure (oneSortSig k) (Vinfinite (oneSortSig k)))

/-- **The colour law** of a structure map. -/
noncomputable def colourLaw : Measure (RelStructure (oneSortSig k) (Vinfinite (oneSortSig k))) :=
  (iidUniformSource (RankSupport (oneSortSig k) 1)).map (F ∘ colours)

variable {F}

theorem measurable_comp_colours (hF : Measurable F) : Measurable (F ∘ colours (k := k)) :=
  hF.comp measurable_colours

theorem isProbabilityMeasure_colourLaw (hF : Measurable F) : IsProbabilityMeasure (colourLaw F) :=
  Measure.isProbabilityMeasure_map (measurable_comp_colours hF).aemeasurable

/-- Equivariance of `F` transports to the fresh layer. -/
theorem comp_colours_supportPerm
    (hequiv : ∀ (σ : Equiv.Perm ℕ) (d : ℕ → Bool),
      F (d ∘ σ) = RelStructure.relabel (fun _ : Unit => σ) (F d))
    (σ : Equiv.Perm ℕ) (ω : Colours k) :
    F (colours fun A => ω (supportPerm σ A)) =
      RelStructure.relabel (fun _ : Unit => σ) (F (colours ω)) := by
  rw [← hequiv]
  exact congrArg F (funext fun v => colour_comp_supportPerm σ ω v)

theorem colourLaw_map_relabel (hF : Measurable F)
    (hequiv : ∀ (σ : Equiv.Perm ℕ) (d : ℕ → Bool),
      F (d ∘ σ) = RelStructure.relabel (fun _ : Unit => σ) (F d))
    (σ : ∀ _ : Unit, Equiv.Perm ℕ) :
    (colourLaw F).map (RelStructure.relabel σ) = colourLaw F := by
  rw [colourLaw, Measure.map_map (measurable_relabel σ) (measurable_comp_colours hF),
    show RelStructure.relabel σ ∘ (F ∘ colours) =
      (F ∘ colours) ∘ (fun ω : Colours k => fun A => ω (supportPerm (σ ()) A)) from by
        funext ω
        exact (comp_colours_supportPerm hequiv (σ ()) ω).symm,
    ← Measure.map_map (measurable_comp_colours hF)
      (measurable_pi_lambda _ fun _ => measurable_pi_apply _),
    iidUniformSource, Measure.infinitePi_map_comp_equiv _ (supportPerm (σ ()))]

/-- The colour law, read off the rank-two cube. -/
theorem colourLaw_eq_map_cube (hF : Measurable F) :
    colourLaw F = (rankLatentSource (oneSortSig k) 2).map (F ∘ colours ∘ freshLayer) := by
  rw [colourLaw, ← source_map_freshLayer, Measure.map_map (measurable_comp_colours hF)
    measurable_freshLayer]
  rfl

/-- **Exact equivariance on the cube.** -/
theorem comp_colours_freshLayer_rankLatentRelabel
    (hequiv : ∀ (σ : Equiv.Perm ℕ) (d : ℕ → Bool),
      F (d ∘ σ) = RelStructure.relabel (fun _ : Unit => σ) (F d))
    (σ : FinSuppPerm (oneSortSig k)) (ω : Cube k) :
    F (colours (freshLayer (rankLatentRelabel σ 2 ω))) =
      RelStructure.relabel σ.1 (F (colours (freshLayer ω))) := by
  rw [freshLayer_rankLatentRelabel, comp_colours_supportPerm hequiv]

/-- A structure map depending only on colour differences reads the relative colouring. -/
theorem comp_colours_freshLayer_eq_relColour
    (hflip : ∀ (d : ℕ → Bool) (b : Bool), F (fun v => xor (d v) b) = F d) (v : ℕ) (ω : Cube k) :
    F (colours (freshLayer ω)) = F (relColour v ω) :=
  (hflip _ _).symm

/-! ### Triviality of the empty and singleton fixing algebras -/

/-- **Fixing events at fewer than two vertices are null or conull** under a colour law whose
structure map is measurable, equivariant, and invariant under a global colour flip. -/
theorem fixing_trivial_of_card_lt_two (hF : Measurable F)
    (hequiv : ∀ (σ : Equiv.Perm ℕ) (d : ℕ → Bool),
      F (d ∘ σ) = RelStructure.relabel (fun _ : Unit => σ) (F d))
    (hflip : ∀ (d : ℕ → Bool) (b : Bool), F (fun v => xor (d v) b) = F d)
    {A : Finset (Σ _ : Unit, ℕ)} (hA : A.card < 2)
    {E : Set (RelStructure (oneSortSig k) (Vinfinite (oneSortSig k)))}
    (hE : MeasurableSet[RelStructure.fixingAlgebra A] E) :
    colourLaw F E = 0 ∨ colourLaw F E = 1 := by
  classical
  -- reduce to a singleton support
  obtain ⟨v, hAv⟩ : ∃ v : ℕ, A ⊆ vertexFinset v := by
    rcases Nat.lt_succ_iff.mp hA |>.eq_or_lt with h1 | h0
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
      obtain ⟨u, w⟩ := a
      cases u
      exact ⟨w, le_rfl⟩
    · have : A = ∅ := Finset.card_eq_zero.mp (Nat.lt_one_iff.mp h0)
      exact ⟨0, by rw [this]; exact Finset.empty_subset _⟩
  have hE' : MeasurableSet[RelStructure.fixingAlgebra (vertexFinset v)] E :=
    RelStructure.fixingAlgebra_mono hAv E hE
  set μ := rankLatentSource (oneSortSig k) 2 with hμ
  have hFm : Measurable (F ∘ colours ∘ freshLayer (k := k)) :=
    (measurable_comp_colours hF).comp measurable_freshLayer
  set D : Set (Cube k) := (F ∘ colours ∘ freshLayer) ⁻¹' E with hD
  have hDm : MeasurableSet D := hFm hE'.1
  have hlaw : colourLaw F E = μ D := by
    rw [colourLaw_eq_map_cube hF, Measure.map_apply hFm hE'.1]
  -- invariance of the pullback
  have hinv : ∀ σ : FinSuppPerm (oneSortSig k), SortwiseFixing (vertexFinset v) σ.1 →
      rankLatentRelabel σ 2 ⁻¹' D =ᵐ[μ] D := by
    intro σ hσ
    refine Filter.EventuallyEq.of_eq ?_
    rw [hD, ← Set.preimage_comp,
      show (F ∘ colours ∘ freshLayer) ∘ rankLatentRelabel σ 2 =
        RelStructure.relabel σ.1 ∘ (F ∘ colours ∘ freshLayer) from
        funext fun ω => comp_colours_freshLayer_rankLatentRelabel hequiv σ ω,
      Set.preimage_comp, hE'.2 σ.1 hσ]
  obtain ⟨D', ⟨C, hC, rfl⟩, hD'⟩ :=
    rankLatentSource_exists_local_ae_eq_of_ae_invariant (vertexFinset v) hDm hinv
  -- the pullback is a function of the relative colouring
  have hDrel : D = relColour v ⁻¹' (F ⁻¹' E) := by
    ext ω
    simp only [hD, Set.mem_preimage, Function.comp_apply,
      comp_colours_freshLayer_eq_relColour hflip v]
  have hBm : MeasurableSet (F ⁻¹' E) := hF hE'.1
  have hind := (indepFun_iff_measure_inter_preimage_eq_mul.mp (indepFun_relColour_window v))
    (F ⁻¹' E) C hBm hC
  have hsq : μ D = μ D * μ D := by
    calc μ D = μ (D ∩ window k v ⁻¹' C) := by
          refine (measure_congr ?_).symm
          exact ((Filter.EventuallyEq.refl _ D).inter hD').trans
            (Filter.EventuallyEq.of_eq (Set.inter_self D))
      _ = μ D * μ (window k v ⁻¹' C) := by rw [hDrel]; exact hind
      _ = μ D * μ D := by rw [measure_congr hD']
  rw [hlaw]
  rcases eq_or_ne (μ D) 0 with h0 | h0
  · exact Or.inl h0
  · right
    have h1 : 1 * μ D = μ D * μ D := by rw [one_mul]; exact hsq
    exact ((ENNReal.mul_left_inj h0 (measure_ne_top _ _)).mp h1).symm

end ColourLaw

end RelSignature
