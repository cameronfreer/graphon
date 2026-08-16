/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelPooledExtension
import Graphon.RelStationaryExtension
import Graphon.ForMathlib.CondExpComap
import Graphon.ForMathlib.CondIndepSup

/-!
# The joint restriction theorem for a pooled rank extension (R4 converse, #107)

Stage 3 of the pooled-latent extension gate, organizing result:

`PooledRankExtension.map_restrict_embedding` — for **every** sortwise embedding
`e : ∀ s, Vinfinite S s ↪ PoolVertex S s`, restricting the extension jointly along `e` returns the
representation exactly:

```
Q.law.map (Prod.map (RelStructure.restrict e) (latentRestrictOver e n)) = C.P
```

This is joint, not a structure marginal: the structure and the latents are restricted along the
same embedding, so it recovers the joint `(X, U_{<n})` law and says strictly more than a
structure-only window theorem.

Cancelling that restriction at the canonical embedding gives `PooledRankExtension.law_eq`, a
**uniqueness theorem**: every pooled rank extension is the cheap one, `(C.pooledExtension)`. The
four route-neutral consequences of the gate are transports through that single identity:

* `PooledRankExtension.map_snd` — the pooled latent marginal is the pooled i.i.d. source;
* `PooledRankExtension.toStationaryExtension` — the structure marginal is a `StationaryExtension M`;
* `PooledRankExtension.lower_recovers` — local recovery on every pooled support below rank `n`, the
  decoder conjugated through the local and block measurable equivalences;
* `PooledRankExtension.screening` — screening on every pooled support of rank `n`, assembled from
  `condIndepFun_comp_measurePreserving`, `CondIndepFun.comp` on the codomains, and
  `CondIndepFun.congr_cond` with `comap_measurableEquiv_comp` on the conditioning algebra.

Nothing route-specific appears: no fresh rank-`n` latent extraction and nothing at rank `n + 1`.

The joint restriction theorem is proved by joint-cylinder extensionality together with finite
agreement by a mixed pooled permutation. On a joint cylinder the combined vertex support is finite; the partial assignment
`originalVertex v ↦ e v` on it is a finite partial injection of the pooled carrier, since both
embeddings are injective, so it extends to a pooled permutation `ρ` with `ρ (ov v) = e v` there.
Both restrictions then read the same moved coordinates, and the full mixed invariance of the
extension absorbs `ρ`. Choosing `ρ` separately on each sort is exactly what the *full* action
permits — no finite-support or uniform-bound issue arises.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

namespace InfiniteRelExchangeableLaw

universe u

variable {S : RelSignature.{u}} [Countable S.Srt] [Countable S.Rel]
  {M : InfiniteRelExchangeableLaw S} {n : ℕ}

/-- **Finite agreement by a pooled permutation**: any sortwise embedding into the pooled carrier
agrees with a pooled permutation composed with the original embedding, on any finite set of
original vertices. The permutation is chosen independently on each sort, which the full mixed
action allows. -/
theorem exists_poolPerm_agree (e : ∀ s, Vinfinite S s ↪ PoolVertex S s)
    (V : Finset (Σ s : S.Srt, Vinfinite S s)) :
    ∃ ρ : ∀ s, Equiv.Perm (PoolVertex S s),
      ∀ v ∈ V, ρ v.1 (originalVertex S v.1 v.2) = e v.1 v.2 := by
  classical
  set W : Finset ℕ := V.image (fun v => v.2) with hW
  have hsort : ∀ s : S.Srt, ∃ ρ : Equiv.Perm (PoolVertex S s),
      ∀ x ∈ W, ρ (originalVertex S s x) = e s x := by
    intro s
    set pv : PoolVertex S s ≃ ℕ := poolVertexEquiv S s with hpv
    set g : ℕ → ℕ := fun y =>
      if h : ∃ x, pv (originalVertex S s x) = y then pv (e s h.choose) else y with hg
    have hinj : ∀ x₁ x₂ : ℕ, pv (originalVertex S s x₁) = pv (originalVertex S s x₂) → x₁ = x₂ :=
      fun x₁ x₂ h => (originalVertex S s).injective (pv.injective h)
    have hgval : ∀ x : ℕ, g (pv (originalVertex S s x)) = pv (e s x) := by
      intro x
      have hex : ∃ x', pv (originalVertex S s x') = pv (originalVertex S s x) := ⟨x, rfl⟩
      rw [hg]
      simp only [dif_pos hex]
      exact congrArg (fun z => pv (e s z)) (hinj _ _ hex.choose_spec)
    have hInjOn : Set.InjOn g ↑(W.image fun x => pv (originalVertex S s x)) := by
      intro y₁ hy₁ y₂ hy₂ hy
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hy₁ hy₂
      obtain ⟨x₁, -, rfl⟩ := hy₁
      obtain ⟨x₂, -, rfl⟩ := hy₂
      rw [hgval, hgval] at hy
      exact congrArg (fun z => pv (originalVertex S s z))
        ((e s).injective (pv.injective hy))
    obtain ⟨σ, hσ⟩ := exists_perm_extend_of_injOn hInjOn
    refine ⟨pv.symm.permCongr σ, fun x hx => ?_⟩
    have hmem : pv (originalVertex S s x) ∈ W.image fun x => pv (originalVertex S s x) :=
      Finset.mem_image.mpr ⟨x, hx, rfl⟩
    show pv.symm (σ (pv (originalVertex S s x))) = e s x
    rw [hσ _ hmem, hgval, Equiv.symm_apply_apply]
  choose ρ hρ using hsort
  refine ⟨ρ, fun v hv => hρ v.1 v.2 ?_⟩
  exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

/-- **The joint restriction theorem.** Restricting a pooled rank extension along *any* sortwise
embedding into the pooled carrier — structure and latents together — returns the representation
exactly. Mixed windows are included: the embedding may land anywhere in the pooled carrier. -/
theorem PooledRankExtension.map_restrict_embedding {C : M.RankRepresentation n}
    (Q : PooledRankExtension C) (e : ∀ s, Vinfinite S s ↪ PoolVertex S s) :
    (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)).map
      (Prod.map (RelStructure.restrict e) (latentRestrictOver e n)) = C.P := by
  classical
  haveI := C.isProbabilityMeasure_P
  have hjointE : Measurable
      (Prod.map (RelStructure.restrict e) (latentRestrictOver (S := S) e n)) :=
    (measurable_restrict e).prodMap (measurable_latentRestrictOver e n)
  haveI : IsProbabilityMeasure
      ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)).map
        (Prod.map (RelStructure.restrict e) (latentRestrictOver (S := S) e n))) :=
    Measure.isProbabilityMeasure_map hjointE.aemeasurable
  refine ext_of_prod_cylinders ?_ (by simp)
  rintro A hA B hB
  have hAmeas : MeasurableSet A := MeasurableSet.of_mem_measurableCylinders hA
  have hBmeas : MeasurableSet B := MeasurableSet.of_mem_measurableCylinders hB
  rw [mem_measurableCylinders] at hA hB
  obtain ⟨Fs, T, hT, rfl⟩ := hA
  obtain ⟨Fl, T', hT', rfl⟩ := hB
  obtain ⟨ρ, hρ⟩ := exists_poolPerm_agree e
    (Fs.biUnion RelCoord.support ∪ Fl.biUnion fun A => A.1)
  have hmemL : ∀ v ∈ Fs.biUnion RelCoord.support,
      ρ v.1 (originalVertex S v.1 v.2) = e v.1 v.2 := fun v hv =>
    hρ v (Finset.mem_union_left _ hv)
  have hmemR : ∀ v ∈ Fl.biUnion fun A => A.1,
      ρ v.1 (originalVertex S v.1 v.2) = e v.1 v.2 := fun v hv =>
    hρ v (Finset.mem_union_right _ hv)
  -- on this cylinder, restricting along `e` is restricting along `ov` after relabeling by `ρ`
  have hstruct : RelStructure.restrict e ⁻¹' cylinder Fs T
      = (restrictOriginal S ∘ RelStructure.relabel ρ) ⁻¹' cylinder Fs T := by
    ext X
    simp only [Set.mem_preimage, mem_cylinder, Function.comp_apply]
    refine Iff.of_eq (congrArg (fun y => y ∈ T) ?_)
    funext c
    show X (RelCoord.map (fun s => ⇑(e s)) c)
      = X (RelCoord.map (fun s => ⇑(ρ s)) (RelCoord.map (fun s => ⇑(originalVertex S s)) c))
    refine congrArg X (Sigma.ext rfl (heq_of_eq (funext fun i => ?_)))
    exact (hmemL ((c : RelCoord S (Vinfinite S)).taggedValue i)
      (Finset.mem_biUnion.mpr ⟨c, c.2, (RelCoord.mem_support_iff _ _).mpr ⟨i, rfl⟩⟩)).symm
  have hlat : latentRestrictOver e n ⁻¹' cylinder Fl T'
      = (restrictOriginalLatents S n ∘ pooledRankLatentRelabel ρ n) ⁻¹' cylinder Fl T' := by
    ext ω
    simp only [Set.mem_preimage, mem_cylinder, Function.comp_apply]
    refine Iff.of_eq (congrArg (fun y => y ∈ T') ?_)
    funext i
    show ω (latentIndexEmbed e n i)
      = ω (latentIndexPerm ρ n (latentIndexEmbed (fun s => originalVertex S s) n i))
    exact congrArg ω (latentIndexEmbed_eq_of_agree fun v hv =>
      hmemR v (Finset.mem_biUnion.mpr ⟨i, i.2, hv⟩))
  have hOvMeas : Measurable (Prod.map (restrictOriginal S) (restrictOriginalLatents S n)) :=
    (measurable_restrictOriginal).prodMap (measurable_restrictOriginalLatents n)
  have hRhoMeas : Measurable
      (Prod.map (RelStructure.relabel ρ) (pooledRankLatentRelabel ρ n)) :=
    (measurable_relabel ρ).prodMap (pooledRankLatentRelabel ρ n).measurable
  have hcomp : Prod.map (RelStructure.restrict e) (latentRestrictOver (S := S) e n) ⁻¹'
        (cylinder Fs T ×ˢ cylinder Fl T')
      = Prod.map (RelStructure.relabel ρ) (pooledRankLatentRelabel ρ n) ⁻¹'
          (Prod.map (restrictOriginal S) (restrictOriginalLatents S n) ⁻¹'
            (cylinder Fs T ×ˢ cylinder Fl T')) := by
    rw [Set.preimage_prod_map_prod, hstruct, hlat, Set.preimage_prod_map_prod,
      Set.preimage_prod_map_prod, Set.preimage_comp, Set.preimage_comp]
  calc ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)).map
        (Prod.map (RelStructure.restrict e) (latentRestrictOver (S := S) e n)))
        (cylinder Fs T ×ˢ cylinder Fl T')
      = (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))
          (Prod.map (RelStructure.relabel ρ) (pooledRankLatentRelabel ρ n) ⁻¹'
            (Prod.map (restrictOriginal S) (restrictOriginalLatents S n) ⁻¹'
              (cylinder Fs T ×ˢ cylinder Fl T'))) := by
        rw [Measure.map_apply hjointE (hAmeas.prod hBmeas), hcomp]
    _ = ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)).map
          (Prod.map (RelStructure.relabel ρ) (pooledRankLatentRelabel ρ n)))
            (Prod.map (restrictOriginal S) (restrictOriginalLatents S n) ⁻¹'
              (cylinder Fs T ×ˢ cylinder Fl T')) :=
        (Measure.map_apply hRhoMeas (hOvMeas (hAmeas.prod hBmeas))).symm
    _ = (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))
          (Prod.map (restrictOriginal S) (restrictOriginalLatents S n) ⁻¹'
            (cylinder Fs T ×ˢ cylinder Fl T')) := by rw [Q.invariant ρ]
    _ = C.P (cylinder Fs T ×ˢ cylinder Fl T') := by
        rw [← Measure.map_apply hOvMeas (hAmeas.prod hBmeas), Q.map_restrictOriginal]

/-! ### The transport characterization -/

/-- **Transport characterization**: identifying the pooled carrier with the original one by
`poolVertexEquiv` carries *any* pooled rank extension back to the representation, jointly. This is
the organizing theorem at the canonical embedding, and it is stated before recovery or screening
deliberately — it isolates the map directions while the claim is still just an equality of joint
laws. -/
theorem PooledRankExtension.map_poolVertexEquiv {C : M.RankRepresentation n}
    (Q : PooledRankExtension C) :
    (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)).map
        (Prod.map (RelStructure.restrict fun s => (poolVertexEquiv S s).symm.toEmbedding)
          (latentRestrictOver (fun s => (poolVertexEquiv S s).symm.toEmbedding) n)) = C.P :=
  Q.map_restrict_embedding _

/-! ### The canonical law identity -/

variable (S n) in
/-- **The canonical joint identification** of the pooled objects with the original ones, bundled as
a measurable equivalence: `poolVertexEquiv` on the structure and its latent transport. Its forward
map is exactly the restriction appearing in `map_poolVertexEquiv`, which is what lets that theorem
be *cancelled* rather than merely stated. -/
noncomputable def pooledJointEquiv :
    (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n) ≃ᵐ
      (RelStructure S (Vinfinite S) × RankLatentSpace S n) :=
  (RelStructure.congrCarrier fun s => poolVertexEquiv S s).prodCongr
    (latentCongrOver (fun s => (poolVertexEquiv S s).symm) n)

omit [Countable S.Srt] [Countable S.Rel] in
theorem pooledJointEquiv_coe :
    ((pooledJointEquiv S n : _ ≃ᵐ _) : _ → _) =
      Prod.map (RelStructure.restrict fun s => (poolVertexEquiv S s).symm.toEmbedding)
        (latentRestrictOver (fun s => (poolVertexEquiv S s).symm.toEmbedding) n) := rfl

omit [Countable S.Srt] [Countable S.Rel] in
theorem pooledJointEquiv_symm_coe :
    (((pooledJointEquiv S n : _ ≃ᵐ _).symm : _ ≃ᵐ _) : _ → _) =
      RankRepresentation.pooledTransport (S := S) (n := n) := rfl

/-- **The canonical law identity**: a pooled rank extension is *determined* — it is the cheap one.
Every marginal, `StationaryExtension`, recovery and screening statement about a pooled extension is
therefore a transport of the corresponding statement about `C.P`, rather than a separate measure
argument. -/
theorem PooledRankExtension.law_eq {C : M.RankRepresentation n} (Q : PooledRankExtension C) :
    (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) =
      ((C.pooledExtension).law :
        Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) := by
  haveI := C.isProbabilityMeasure_P
  calc (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))
      = ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)).map
          (pooledJointEquiv S n)).map (pooledJointEquiv S n).symm :=
        (MeasurableEquiv.map_symm_map _).symm
    _ = C.P.map (pooledJointEquiv S n).symm := by
        rw [pooledJointEquiv_coe, Q.map_poolVertexEquiv]
    _ = ((C.pooledExtension).law :
          Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) := rfl

/-- **The canonical identification is measure-preserving** from a pooled extension to the
representation. This is the handle for transporting conditional-independence statements: composing
with a measure-preserving map pulls `C.P`-statements *back* to `Q.law`, so nothing has to be pushed
forward and no further conditional-expectation theorem is needed. -/
theorem PooledRankExtension.measurePreserving_pooledJointEquiv {C : M.RankRepresentation n}
    (Q : PooledRankExtension C) :
    MeasurePreserving (pooledJointEquiv S n)
      (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) C.P :=
  ⟨(pooledJointEquiv S n).measurable, by
    rw [pooledJointEquiv_coe]; exact Q.map_poolVertexEquiv⟩

/-! ### Consequence 1: the pooled latent marginal -/

/-- **The pooled latent marginal is the pooled i.i.d. source.** A transport of `C.map_snd` through
the canonical identity, with the source transport doing the work on the latent factor. -/
theorem PooledRankExtension.map_snd {C : M.RankRepresentation n} (Q : PooledRankExtension C) :
    (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)).map Prod.snd =
      pooledRankLatentSource S n := by
  haveI := C.isProbabilityMeasure_P
  rw [Q.law_eq, RankRepresentation.pooledExtension_law_coe,
    Measure.map_map measurable_snd RankRepresentation.measurable_pooledTransport,
    show Prod.snd ∘ RankRepresentation.pooledTransport (S := S) (n := n) =
      latentCongrOver (fun s => poolVertexEquiv S s) n ∘ Prod.snd from rfl,
    ← Measure.map_map (latentCongrOver (fun s => poolVertexEquiv S s) n).measurable
      measurable_snd,
    C.map_snd, rankLatentSource_eq_latentSourceOver, pooledRankLatentSource,
    latentSourceOver_map_latentCongrOver (fun s => poolVertexEquiv S s) n]

/-! ### Consequence 2: the structure marginal is a stationary extension -/

/-- **The structure marginal of a pooled rank extension is a stationary extension of the law.**
Both fields are the corresponding pooled field composed with `Prod.fst`. -/
noncomputable def PooledRankExtension.toStationaryExtension {C : M.RankRepresentation n}
    (Q : PooledRankExtension C) : StationaryExtension M where
  law := ⟨(Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)).map
      Prod.fst, by
    haveI : IsProbabilityMeasure
        (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) := Q.law.2
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable⟩
  map_restrictOriginal := by
    haveI := C.isProbabilityMeasure_P
    rw [ProbabilityMeasure.coe_mk,
      Measure.map_map measurable_restrictOriginal measurable_fst,
      show restrictOriginal S ∘ (Prod.fst :
          RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → _) =
        Prod.fst ∘ Prod.map (restrictOriginal S) (restrictOriginalLatents S n) from rfl,
      ← Measure.map_map measurable_fst
        (measurable_restrictOriginal.prodMap (measurable_restrictOriginalLatents n)),
      Q.map_restrictOriginal, C.map_fst]
  invariant := by
    intro ρ
    rw [ProbabilityMeasure.coe_mk, Measure.map_map (measurable_relabel ρ) measurable_fst,
      show RelStructure.relabel ρ ∘ (Prod.fst :
          RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → _) =
        Prod.fst ∘ Prod.map (RelStructure.relabel ρ) (pooledRankLatentRelabel ρ n) from rfl,
      ← Measure.map_map measurable_fst
        ((measurable_relabel ρ).prodMap (pooledRankLatentRelabel ρ n).measurable),
      Q.invariant ρ]

/-! ### Consequence 3: local recovery on pooled supports -/

open scoped Classical in
/-- **Local recovery holds on every pooled support below rank `n`** — mixed supports included.
`C.lower_recovers` is pulled back along the canonical identification, and the decoder is conjugated
through the local and block measurable equivalences. The only almost-everywhere step is the
transported identity itself. -/
theorem PooledRankExtension.lower_recovers {C : M.RankRepresentation n}
    (Q : PooledRankExtension C) (A : Finset (Σ s : S.Srt, PoolVertex S s)) (hA : A.card < n) :
    ∃ g : LocalLatentSpaceOver (PoolVertex S) A n → BlockSpaceOver (PoolVertex S) A,
      Measurable g ∧
      blockMapOver A ∘ Prod.fst =ᵐ[(Q.law :
          Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))]
        g ∘ localLatentsOver A n ∘ Prod.snd := by
  haveI := C.isProbabilityMeasure_P
  classical
  set e : ∀ s, Vinfinite S s ↪ PoolVertex S s :=
    fun s => (poolVertexEquiv S s).symm.toEmbedding with he
  -- present the pooled support as the image of an original one, once and for all
  obtain ⟨A₀, hA₀card, rfl⟩ :
      ∃ A₀ : Finset (Σ s : S.Srt, Vinfinite S s), A₀.card < n ∧ supportImage e A₀ = A := by
    refine ⟨supportImage (fun s => (poolVertexEquiv S s).toEmbedding) A, ?_, ?_⟩
    · rw [card_supportImage]; exact hA
    · rw [he]; exact supportImage_symm_supportImage (fun s => poolVertexEquiv S s) A
  obtain ⟨g₀, hg₀meas, hg₀⟩ := C.lower_recovers A₀ hA₀card
  have hpull := (Q.measurePreserving_pooledJointEquiv).quasiMeasurePreserving.ae_eq_comp hg₀
  refine ⟨(blockSpaceCongr e A₀).symm ∘ g₀ ∘ localLatentSpaceCongr e A₀ n, ?_, ?_⟩
  · exact ((blockSpaceCongr e A₀).symm.measurable.comp hg₀meas).comp
      (localLatentSpaceCongr e A₀ n).measurable
  · filter_upwards [hpull] with p hp
    have hb : blockMap A₀ (RelStructure.restrict e p.1)
        = blockSpaceCongr e A₀ (blockMapOver (supportImage e A₀) p.1) :=
      congrFun (blockMapOver_restrict e A₀) p.1
    have hl : localLatents A₀ n (latentRestrictOver e n p.2)
        = localLatentSpaceCongr e A₀ n (localLatentsOver (supportImage e A₀) n p.2) :=
      congrFun (localLatentsOver_latentRestrictOver e A₀ n) p.2
    have hp' : blockSpaceCongr e A₀ (blockMapOver (supportImage e A₀) p.1)
        = g₀ (localLatentSpaceCongr e A₀ n (localLatentsOver (supportImage e A₀) n p.2)) := by
      rw [← hb, ← hl]; exact hp
    show blockMapOver (supportImage e A₀) p.1 = _
    calc blockMapOver (supportImage e A₀) p.1
        = (blockSpaceCongr e A₀).symm
            (blockSpaceCongr e A₀ (blockMapOver (supportImage e A₀) p.1)) :=
          ((blockSpaceCongr e A₀).symm_apply_apply _).symm
      _ = _ := by rw [hp']; rfl

/-! ### Consequence 4: screening on pooled supports -/

open scoped Classical in
/-- **Screening holds on every pooled support of rank `n`** — mixed supports included. Pure
assembly: pull `C.screening` back through the canonical identification, strip the output
equivalences with `CondIndepFun.comp`, and straighten the conditioning algebra with
`CondIndepFun.congr_cond`. No conditional-expectation reasoning appears. -/
theorem PooledRankExtension.screening {C : M.RankRepresentation n}
    (Q : PooledRankExtension C) (A : Finset (Σ s : S.Srt, PoolVertex S s)) (hA : A.card = n) :
    CondIndepFun (MeasurableSpace.comap (localLatentsOver A n ∘ Prod.snd) inferInstance)
      (((measurable_localLatentsOver A n).comp measurable_snd).comap_le)
      (blockMapOver A ∘ Prod.fst) (restObservationOver n A)
      (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)) := by
  haveI := C.isProbabilityMeasure_P
  classical
  set eqv : ∀ s, Vinfinite S s ≃ PoolVertex S s := fun s => (poolVertexEquiv S s).symm with heqv
  set e : ∀ s, Vinfinite S s ↪ PoolVertex S s := fun s => (eqv s).toEmbedding with he
  obtain ⟨A₀, hA₀card, rfl⟩ :
      ∃ A₀ : Finset (Σ s : S.Srt, Vinfinite S s), A₀.card = n ∧ supportImage e A₀ = A := by
    refine ⟨supportImage (fun s => (poolVertexEquiv S s).toEmbedding) A, ?_, ?_⟩
    · rw [card_supportImage]; exact hA
    · rw [he, heqv]; exact supportImage_symm_supportImage (fun s => poolVertexEquiv S s) A
  -- step 1: pull the representation's screening back along the canonical identification
  have hpull := condIndepFun_comp_measurePreserving Q.measurePreserving_pooledJointEquiv
    ((measurable_localLatents A₀ n).comp measurable_snd).comap_le
    ((measurable_blockMap A₀).comp measurable_fst) (measurable_restObservation n A₀)
    (C.screening A₀ hA₀card)
  -- step 2: strip the output equivalences (post-composition never touches the dependent proof)
  have hstrip := hpull.comp (blockSpaceCongr e A₀).symm.measurable
    ((restSpaceCongr eqv n A₀).prodCongr (latentCongrOver eqv n)).symm.measurable
  have hf : ⇑(blockSpaceCongr e A₀).symm ∘
      ((blockMap A₀ ∘ Prod.fst) ∘ ⇑(pooledJointEquiv S n)) =
      blockMapOver (supportImage e A₀) ∘ Prod.fst := by
    rw [pooledJointEquiv_coe]
    funext p
    show (blockSpaceCongr e A₀).symm (blockMapOver A₀ (RelStructure.restrict e p.1)) = _
    have hnat := congrFun (blockMapOver_restrict e A₀) p.1
    simp only [Function.comp_apply] at hnat
    rw [hnat]
    simp
  have hg : ⇑((restSpaceCongr eqv n A₀).prodCongr (latentCongrOver eqv n)).symm ∘
      (restObservation n A₀ ∘ ⇑(pooledJointEquiv S n)) =
      restObservationOver n (supportImage e A₀) := by
    rw [pooledJointEquiv_coe]
    funext p
    show ((restSpaceCongr eqv n A₀).prodCongr (latentCongrOver eqv n)).symm
      (restObservationOver n A₀ (Prod.map (RelStructure.restrict e)
        (latentRestrictOver (S := S) e n) p)) = _
    have hnat := congrFun (restObservationOver_congrCarrier eqv n A₀) p
    simp only [Function.comp_apply] at hnat
    rw [hnat, show Prod.map (⇑(restSpaceCongr eqv n A₀)) (⇑(latentCongrOver eqv n)) =
        ⇑((restSpaceCongr eqv n A₀).prodCongr (latentCongrOver eqv n)) from rfl,
      MeasurableEquiv.symm_apply_apply]
  rw [hf, hg] at hstrip
  -- step 3: straighten the conditioning algebra
  refine hstrip.congr_cond ?_ _
  rw [MeasurableSpace.comap_comp,
    show (localLatents A₀ n ∘ Prod.snd) ∘ ⇑(pooledJointEquiv S n) =
      ⇑(localLatentSpaceCongr e A₀ n) ∘
        (localLatentsOver (supportImage e A₀) n ∘ Prod.snd) from by
      rw [pooledJointEquiv_coe]
      funext p
      have hnat := congrFun (localLatentsOver_latentRestrictOver e A₀ n) p.2
      simp only [Function.comp_apply] at hnat ⊢
      exact hnat]
  exact comap_measurableEquiv_comp (localLatentSpaceCongr e A₀ n) _

end InfiniteRelExchangeableLaw

end RelSignature
