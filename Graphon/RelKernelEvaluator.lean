/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelEqualityPattern
import Graphon.RelationalTopology

/-!
# The measurable kernel evaluator over pattern-local latents (R4 evaluator layer, #107)

The second R4 layer, on the settled #137 interface: a **kernel family** assigns to every
relation symbol and every abstract equality pattern a measurable Boolean function of the
pattern-local latents; the **evaluator** reads each coordinate of the infinite structure off
the global latent source through its local window. **No latent source measure, sampler
pushforward, dissociation, or representation theorem here** — those are the subsequent
layers; this file settles the evaluator and its equivariance.

* `RelKernelFamily S` — the label-free representing kernels `f_{r,π}`, measurable on the
  finite product `PatternLatentIndex π → ℝ`;
* `RelCoord.localLatents` — the local latent window of a coordinate: the global source
  restricted along `patternLatentIndexEquivCoord` and the canonical projection;
* `RelKernelFamily.evalStructure` — the evaluated infinite structure, measurable in the
  global source;
* `RelKernelFamily.evalStructure_relabel` — **equivariance**: relabeling the evaluated
  structure is evaluating at the relabeled latents — the statement that will make
  exchangeability of the evaluated law a coordinatewise check.
-/

open Function MeasureTheory

namespace RelSignature

variable {S : RelSignature}

/-! ### Kernel families -/

/-- **A representing kernel family**: for every relation symbol and every abstract equality
pattern, a measurable Boolean function of the pattern-local latents. Label-free by
construction — the kernel sees only the pattern and its blocks, never vertex labels. -/
structure RelKernelFamily (S : RelSignature) where
  /-- The kernel at a relation symbol and pattern. -/
  toFun : ∀ (r : S.Rel) (π : EqualityPattern S r), (PatternLatentIndex π → ℝ) → Bool
  /-- Each kernel is measurable on the finite latent product. -/
  measurable : ∀ (r : S.Rel) (π : EqualityPattern S r), Measurable (toFun r π)

/-! ### The local latent window -/

/-- **The local latent window of a coordinate**: the global latent source read through the
coordinate's pattern-local indices (via the canonical equivalence and projection). -/
noncomputable def RelCoord.localLatents (c : RelCoord S (Vinfinite S))
    (ω : LatentIndex S (Vinfinite S) → ℝ) :
    PatternLatentIndex c.equalityPattern → ℝ := fun A =>
  ω (CoordLatentIndex.toLatentIndex (patternLatentIndexEquivCoord c A))

theorem RelCoord.measurable_localLatents (c : RelCoord S (Vinfinite S)) :
    Measurable fun ω : LatentIndex S (Vinfinite S) → ℝ => c.localLatents ω := by
  rw [measurable_pi_iff]
  intro A
  exact measurable_pi_apply _

/-! ### The evaluator -/

/-- **The evaluated infinite structure**: each coordinate is its kernel applied to its local
latent window. -/
noncomputable def RelKernelFamily.evalStructure (F : RelKernelFamily S)
    (ω : LatentIndex S (Vinfinite S) → ℝ) : RelStructure S (Vinfinite S) := fun c =>
  F.toFun c.1 c.equalityPattern (c.localLatents ω)

@[simp] theorem RelKernelFamily.evalStructure_apply (F : RelKernelFamily S)
    (ω : LatentIndex S (Vinfinite S) → ℝ) (c : RelCoord S (Vinfinite S)) :
    F.evalStructure ω c = F.toFun c.1 c.equalityPattern (c.localLatents ω) := rfl

/-- **The evaluator is measurable** in the global latent source. -/
theorem RelKernelFamily.measurable_evalStructure (F : RelKernelFamily S) :
    Measurable F.evalStructure := by
  rw [measurable_pi_iff]
  intro c
  exact (F.measurable c.1 c.equalityPattern).comp (c.measurable_localLatents)

end RelSignature
