/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelKernelEvaluator
import Graphon.RelRestrictionBlocks
import Graphon.SamplerSources

/-!
# The evaluated exchangeable law of a kernel family (R4 sampler layer, #107)

The third R4 layer, on the merged evaluator (`Graphon.RelKernelEvaluator`): the i.i.d.
uniform **latent source** over the global subset-latent indices, and the pushforward of that
source through the `RelKernelFamily` evaluator — an **exchangeable** infinite relational law.
The representation theorem (the converse: every dissociated exchangeable law arises this way)
is deliberately *not* here; see issue #107 for its campaign plan.

* `RelKernelFamily.eval` — the evaluator over an **arbitrary carrier** `V`, agreeing
  definitionally with `evalStructure` on `Vinfinite`; its pullback transport `eval_comap`
  generalizes `evalStructure_relabel` to sortwise injections between carriers;
* `RelSignature.latentSource` — one i.i.d. `[0,1]`-uniform per nonempty finite set of
  sort-tagged vertices, with relabeling invariance `latentSource_map_relabel` (via
  `LatentIndex.relabelEquiv` and `Measure.infinitePi_map_comp_equiv`);
* `RelKernelFamily.evalMeasure` / `RelKernelFamily.evalLaw` — the evaluated law, packaged as
  an `InfiniteRelExchangeableLaw`: relabeling the structure is precomposing the source with
  the latent-index action (`evalStructure_relabel`), which preserves the source;
* `RelKernelFamily.evalLaw_isDissociated` — **dissociation**: disjoint vertex windows read
  disjoint collections of *nonempty* subset-latent indices
  (`LatentIndex.map_ne_map_of_disjoint`), so the i.i.d. source factorizes across the blocks
  (`Measure.infinitePi_map_prodMk_of_disjoint`); every finite restriction marginal is the
  same finite-block pushforward `evalMeasure_map_restrict`, independently of the injection.
-/

open Function MeasureTheory

namespace RelSignature

variable {S : RelSignature}

/-! ### The evaluator over an arbitrary carrier -/

section GeneralEvaluator

variable {V W : S.Srt → Type*}

/-- **The local latent window over an arbitrary carrier**: the latent source read through
the coordinate's pattern-local indices — the arbitrary-carrier form of
`RelCoord.localLatents` (definitionally equal to it on `Vinfinite`). -/
noncomputable def RelCoord.latentWindow (c : RelCoord S V) (η : LatentIndex S V → ℝ) :
    PatternLatentIndex c.equalityPattern → ℝ := fun A =>
  η (CoordLatentIndex.toLatentIndex (patternLatentIndexEquivCoord c A))

/-- On the infinite carrier the general window is the evaluator layer's `localLatents`. -/
theorem RelCoord.latentWindow_eq_localLatents (c : RelCoord S (Vinfinite S))
    (ω : LatentIndex S (Vinfinite S) → ℝ) :
    c.latentWindow ω = c.localLatents ω := rfl

/-- **The evaluated structure over an arbitrary carrier**: each coordinate is its kernel
applied to its local latent window. -/
noncomputable def RelKernelFamily.eval (F : RelKernelFamily S) (η : LatentIndex S V → ℝ) :
    RelStructure S V := fun c =>
  F.toFun c.1 c.equalityPattern (c.latentWindow η)

/-- On the infinite carrier the general evaluator is `evalStructure` (definitional). -/
theorem RelKernelFamily.eval_eq_evalStructure (F : RelKernelFamily S) :
    F.eval (V := Vinfinite S) = F.evalStructure := rfl

/-- **The general evaluator is measurable** in the latent source. -/
theorem RelKernelFamily.measurable_eval (F : RelKernelFamily S) :
    Measurable (F.eval (V := V)) := by
  rw [measurable_pi_iff]
  intro c
  refine (F.measurable c.1 c.equalityPattern).comp ?_
  rw [measurable_pi_iff]
  intro A
  exact measurable_pi_apply _

/-- **The local latent window transports along sortwise injections**: the window of the
mapped coordinate is the window of the original coordinate, read off the source precomposed
with the global latent-index action, at the transported block-set — the arbitrary-carrier
generalization of `RelCoord.localLatents_map`. -/
theorem RelCoord.latentWindow_map {f : ∀ s, V s → W s} (hf : ∀ s, Injective (f s))
    (c : RelCoord S V) (η : LatentIndex S W → ℝ)
    (A' : PatternLatentIndex (RelCoord.map f c).equalityPattern) :
    (RelCoord.map f c).latentWindow η A' =
      c.latentWindow (fun A => η (LatentIndex.map f A))
        (PatternLatentIndex.congr (RelCoord.equalityPattern_map hf c) A') := by
  show η (CoordLatentIndex.toLatentIndex (patternLatentIndexEquivCoord (RelCoord.map f c) A')) = _
  rw [patternLatentIndexEquivCoord_map hf c A', CoordLatentIndex.congrMap_toLatentIndex]
  rfl

/-- **Pullback commutes with evaluation**: pulling the evaluated structure back along a
sortwise injective family is evaluating at the source precomposed with the latent-index
action — the arbitrary-carrier generalization of `evalStructure_relabel`, covering both
relabelings and finite restrictions. -/
theorem RelKernelFamily.eval_comap {f : ∀ s, V s → W s} (hf : ∀ s, Injective (f s))
    (F : RelKernelFamily S) (η : LatentIndex S W → ℝ) :
    RelStructure.comap f (F.eval η) = F.eval fun A => η (LatentIndex.map f A) := by
  funext c
  exact F.toFun_congr (RelCoord.equalityPattern_map hf c)
    (RelCoord.latentWindow_map hf c η)

end GeneralEvaluator

/-! ### The latent source and the evaluated law -/

/-- **The global latent source**: one i.i.d. `[0,1]`-uniform per nonempty finite set of
sort-tagged vertices — the randomness the dissociated functional representation consumes. -/
noncomputable def latentSource (S : RelSignature) :
    Measure (LatentIndex S (Vinfinite S) → ℝ) :=
  iidUniformSource (LatentIndex S (Vinfinite S))

instance : IsProbabilityMeasure (latentSource S) := by
  rw [latentSource]; infer_instance

/-- **Relabeling invariance of the latent source**: precomposition with the latent-index
action of a sortwise permutation family preserves the i.i.d. source — the action is a
bijection of the index set (`LatentIndex.relabelEquiv`), and i.i.d. products are invariant
under index bijections. -/
theorem latentSource_map_relabel (σ : ∀ _ : S.Srt, Equiv.Perm ℕ) :
    (latentSource S).map
        (fun (ω : LatentIndex S (Vinfinite S) → ℝ) A =>
          ω (LatentIndex.map (fun s => ⇑(σ s)) A)) =
      latentSource S := by
  rw [latentSource, iidUniformSource]
  exact Measure.infinitePi_map_comp_equiv _ (LatentIndex.relabelEquiv fun s => σ s)

/-- **The evaluated measure** of a kernel family: the latent source pushed through the
evaluator. -/
noncomputable def RelKernelFamily.evalMeasure (F : RelKernelFamily S) :
    Measure (RelStructure S (Vinfinite S)) :=
  (latentSource S).map F.evalStructure

instance (F : RelKernelFamily S) : IsProbabilityMeasure F.evalMeasure :=
  Measure.isProbabilityMeasure_map F.measurable_evalStructure.aemeasurable

/-- **Exchangeability of the evaluated measure**: relabeling the evaluated structure is
precomposing the latent source with the latent-index action (`evalStructure_relabel`), and
the source is invariant under that action (`latentSource_map_relabel`). -/
theorem RelKernelFamily.evalMeasure_map_relabel (F : RelKernelFamily S)
    (σ : ∀ _ : S.Srt, Equiv.Perm ℕ) :
    F.evalMeasure.map (RelStructure.relabel σ) = F.evalMeasure := by
  rw [RelKernelFamily.evalMeasure,
    Measure.map_map (measurable_relabel σ) F.measurable_evalStructure,
    show RelStructure.relabel σ ∘ F.evalStructure =
        F.evalStructure ∘ (fun ω A => ω (LatentIndex.map (fun s => ⇑(σ s)) A)) from
      funext fun ω => F.evalStructure_relabel σ ω,
    ← Measure.map_map F.measurable_evalStructure
      (measurable_pi_iff.mpr fun _ => measurable_pi_apply _),
    latentSource_map_relabel σ]

/-- **The evaluated exchangeable law** of a kernel family — the forward half of the
dissociated functional Aldous–Hoover–Kallenberg representation. -/
noncomputable def RelKernelFamily.evalLaw (F : RelKernelFamily S) :
    InfiniteRelExchangeableLaw S where
  law := ⟨F.evalMeasure, inferInstance⟩
  exchangeable := F.evalMeasure_map_relabel

@[simp] theorem RelKernelFamily.evalLaw_law (F : RelKernelFamily S) :
    (F.evalLaw.law : Measure (RelStructure S (Vinfinite S))) = F.evalMeasure := rfl

/-! ### Dissociation of the evaluated law -/

section Dissociation

variable [Fintype S.Srt]

/-- Latent indices over a finite carrier form a finite type — the two blocks of the
dissociation pair each read a *finite* latent window. -/
noncomputable instance (n : S.Srt → ℕ) : Fintype (LatentIndex S (Vfinite n)) := by
  classical
  haveI : Fintype (Finset (Σ s : S.Srt, Fin (n s))) := Finset.fintype
  exact Subtype.fintype _

/-- **Every finite sortwise-injective restriction of the evaluated measure is the same
finite-block pushforward** — independently of the injection: restriction commutes with
evaluation (`eval_comap`), and the precomposed source projects to the i.i.d. finite latent
block (`Measure.infinitePi_map_comp_of_injective`). -/
theorem RelKernelFamily.evalMeasure_map_restrict (F : RelKernelFamily S)
    {n : S.Srt → ℕ} (e : ∀ s, Fin (n s) ↪ ℕ) :
    F.evalMeasure.map (RelStructure.restrict e) =
      (Measure.pi fun _ : LatentIndex S (Vfinite n) => uniform01).map
        (F.eval (V := Vfinite n)) := by
  have hpre : Measurable fun (ω : LatentIndex S (Vinfinite S) → ℝ)
      (B : LatentIndex S (Vfinite n)) => ω (LatentIndex.map (fun s => ⇑(e s)) B) :=
    measurable_pi_iff.mpr fun _ => measurable_pi_apply _
  rw [RelKernelFamily.evalMeasure,
    Measure.map_map (measurable_restrict e) F.measurable_evalStructure,
    show RelStructure.restrict e ∘ F.evalStructure =
        F.eval (V := Vfinite n) ∘
          (fun ω B => ω (LatentIndex.map (fun s => ⇑(e s)) B)) from
      funext fun ω => F.eval_comap (fun s => (e s).injective) ω,
    ← Measure.map_map F.measurable_eval hpre,
    latentSource, iidUniformSource,
    Measure.infinitePi_map_comp_of_injective _
      (LatentIndex.map_injective fun s => (e s).injective)]

/-- **The joint block law of the evaluated measure factorizes**: the two vertex windows are
disjoint, so the nonempty subset-latent collections they read are disjoint
(`LatentIndex.map_ne_map_of_disjoint`), and the i.i.d. source splits into a product across
them (`Measure.infinitePi_map_prodMk_of_disjoint`). -/
theorem RelKernelFamily.evalMeasure_map_blockPair (F : RelKernelFamily S) (k l : S.Srt → ℕ) :
    F.evalMeasure.map (blockPair k l) =
      (F.evalMeasure.map (RelStructure.restrictFin k)).prod
        (F.evalMeasure.map (RelStructure.restrictFin l)) := by
  have hd : ∀ (A : LatentIndex S (Vfinite k)) (B : LatentIndex S (Vfinite l)),
      LatentIndex.map (fun s (i : Fin (k s)) => (i : ℕ)) A ≠
        LatentIndex.map (fun s => ⇑(shiftEmb k l s)) B :=
    LatentIndex.map_ne_map_of_disjoint fun s x y h => by
      have hx := x.isLt
      have hy : ⇑(shiftEmb k l s) y = (y : ℕ) + k s := rfl
      omega
  have hpre : Measurable fun (ω : LatentIndex S (Vinfinite S) → ℝ) =>
      (fun B : LatentIndex S (Vfinite k) =>
          ω (LatentIndex.map (fun s (i : Fin (k s)) => (i : ℕ)) B),
        fun B : LatentIndex S (Vfinite l) =>
          ω (LatentIndex.map (fun s => ⇑(shiftEmb k l s)) B)) :=
    (measurable_pi_iff.mpr fun _ => measurable_pi_apply _).prodMk
      (measurable_pi_iff.mpr fun _ => measurable_pi_apply _)
  calc F.evalMeasure.map (blockPair k l)
      = ((Measure.pi fun _ : LatentIndex S (Vfinite k) => uniform01).map
            (F.eval (V := Vfinite k))).prod
          ((Measure.pi fun _ : LatentIndex S (Vfinite l) => uniform01).map
            (F.eval (V := Vfinite l))) := by
        rw [RelKernelFamily.evalMeasure,
          Measure.map_map (measurable_blockPair k l) F.measurable_evalStructure,
          show blockPair k l ∘ F.evalStructure =
              Prod.map (F.eval (V := Vfinite k)) (F.eval (V := Vfinite l)) ∘
                (fun ω =>
                  (fun B => ω (LatentIndex.map (fun s (i : Fin (k s)) => (i : ℕ)) B),
                    fun B => ω (LatentIndex.map (fun s => ⇑(shiftEmb k l s)) B))) from
            funext fun ω => Prod.ext
              (F.eval_comap (fun s => Fin.val_injective) ω)
              (F.eval_comap (fun s => (shiftEmb k l s).injective) ω),
          ← Measure.map_map (F.measurable_eval.prodMap F.measurable_eval) hpre,
          latentSource, iidUniformSource,
          Measure.infinitePi_map_prodMk_of_disjoint _
            (LatentIndex.map_injective fun s => Fin.val_injective)
            (LatentIndex.map_injective fun s => (shiftEmb k l s).injective) hd,
          ← Measure.map_prod_map _ _ F.measurable_eval F.measurable_eval]
    _ = (F.evalMeasure.map (RelStructure.restrictFin k)).prod
          (F.evalMeasure.map (RelStructure.restrictFin l)) := by
        rw [show RelStructure.restrictFin (S := S) k =
              RelStructure.restrict (fun s => (Fin.valEmbedding : Fin (k s) ↪ ℕ)) from rfl,
          show RelStructure.restrictFin (S := S) l =
              RelStructure.restrict (fun s => (Fin.valEmbedding : Fin (l s) ↪ ℕ)) from rfl,
          F.evalMeasure_map_restrict, F.evalMeasure_map_restrict]

/-- **The evaluated law is dissociated** — disjoint vertex windows read disjoint collections
of nonempty subset-latent indices, and the i.i.d. latent source factorizes across them. With
exchangeability (`evalLaw`), this completes the forward half of the dissociated functional
Aldous–Hoover–Kallenberg representation. -/
theorem RelKernelFamily.evalLaw_isDissociated (F : RelKernelFamily S) :
    F.evalLaw.IsDissociated := by
  intro k l
  exact F.evalMeasure_map_blockPair k l

end Dissociation

end RelSignature
