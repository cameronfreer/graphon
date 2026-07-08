# Rokhlin scoping memo: what `exists_common_extension` actually needs to say

**Status**: pre-campaign scoping (2026-07-08), per the directive: *"scope whether the
graphon route needs the full `MeasurePreserving.exists_common_extension` or only a
specialized common-extension lemma sufficient for `cutDistance_triangle` and partition
alignment."*

**Answer: neither — the stub as stated appears to be UNPROVABLE (two of its three
conjuncts look false), and the graphon route needs three *narrower, corrected* lemmas,
whose common core is the measure isomorphism theorem (absent from Mathlib).**

## 1. The stub and its consumers

`MeasurePreserving.exists_common_extension` (`Graphon/CutDistance.lean:1065`, the
project's single live sorry) bundles three conjuncts. Hypotheses: `[StandardBorelSpace α]`,
`μ` a probability measure — **note: `[NoAtoms μ]` is NOT assumed**.

| Conjunct | Content | Sole consumers |
|---|---|---|
| 1 | map alignment: MP `ψ₁ φ₂ : α → α` ⇒ ∃ MP **bijections** `χ₁ χ₂` with `ψ₁∘χ₁ =ᵐ φ₂∘χ₂` | `exists_common_extension_maps` → `cutDistance_triangle` (CutDistance:1256) |
| 2 | partition alignment: ∀ `P Q`, ∃ MP bijection `e`, every `P`-cell `S` has a `Q`-cell `T` with `μ(S Δ e⁻¹T) = 0` | `exists_partition_alignment` → Compactness net argument (Compactness:493) |
| 3 | controlled cell alignment: measure-matched injective cell families ⇒ aligning MP bijection | `exists_controlled_cell_alignment` → InverseCounting:292 (self-alignment), :680, :1737 |

## 2. Findings: two conjuncts are false as stated

**Conjunct 1 is false.** Take `(α, μ) = ([0,1], λ)`, `ψ₁ = id`,
`φ₂ = doubling (x ↦ 2x mod 1)` (both MP). The conclusion demands a bijection `χ₁` with
`χ₁ =ᵐ doubling ∘ χ₂`. But `doubling ∘ χ₂` is essentially 2-to-1: on any conull set `E`,
the set `A := {x ∈ [0, 1/2) : x ∈ χ₂(E), x + 1/2 ∈ χ₂(E)}` has measure `1/2`, and each
`x ∈ A` produces a distinct collision pair for `doubling ∘ χ₂`, so no injective map can
agree with it a.e. Contradiction. *(The classical fact — Kechris 17.41-adjacent — is a
COUPLING statement: the common extension lives on a fibered product / joining, with MP
**maps**, not automorphisms of `α` itself.)*

**Conjunct 2 is false.** The two-sided null differences force `μ S = μ T` cell-by-cell,
i.e. `P` and `e⁻¹Q` are equal mod 0 — impossible when the measure profiles differ:
`P = {A, Aᶜ}` with `μ A = 1/2` vs `Q = trivialPartition`.

**Conjunct 3 needs `[NoAtoms μ]`.** With atoms: `α = {a,b,c}`, `μ = (1/2, 1/4, 1/4)`,
cells `ι_S = ({b,c})`, `ι_T = ({a})` have matching measures `1/2`, but no bijection maps
a two-atom cell into a one-atom cell (a.e. = everywhere on atoms). With `[NoAtoms μ]`
conjunct 3 is the honest Rokhlin consequence and is TRUE.

*(Both counterexamples are paper-level; the campaign's Phase R0 should re-verify them —
ideally as certified `/lean4:disprove` refutations of the as-stated forms — before any
restatement lands.)*

## 3. What each consumer actually needs

- **`cutDistance_triangle`**: the file's `cutDistance` is an infimum over pullbacks along
  arbitrary MP **maps** (not bijections). The triangle proof needs to co-align two
  alignments of the middle graphon `W`: MP maps `χ₁ χ₂` with `ψ∘χ₁ =ᵐ φ'∘χ₂` — the
  **coupling form with maps**, which is consistent (unlike the bijection form) and
  should suffice for pullback composition. To keep `χᵢ : α → α` (the file's types), the
  fibered-product coupling space must be re-typed through the measure isomorphism.
- **Compactness net argument** (:493): uses conjunct 2 on `(P₀, P_W)`. Since conjunct 2
  is false in general, this step needs re-derivation: either the net is (or can be)
  built so the relevant partitions have matching measure profiles (then the corrected,
  measure-matched alignment applies), or the argument needs a one-sided/refinement
  variant. **This is the one consumer where the downstream proof itself may need
  surgery, not just a lemma swap.**
- **InverseCounting ×3**: all three uses are measure-matched injective families —
  corrected conjunct 3 (with `[NoAtoms μ]`, available at all three sites) suffices
  verbatim.

## 4. Mathlib inventory

| Ingredient | Status |
|---|---|
| Borel isomorphism theorem (`PolishSpace.measurableEquivOfNotCountable : α ≃ᵐ β` for uncountable standard Borel) | **present** |
| Disintegration / conditional kernels (`Measure.condKernel`, standard Borel) | **present** |
| **Measure isomorphism theorem** (atomless standard Borel probability ≅ mod-0 `([0,1], Lebesgue)`) | **ABSENT — the genuine gap** |
| Interval rearrangement on `[0,1]` (measure-matched finite families of sets ⇒ MP a.e. alignment) | absent as such; constructible from CDF machinery |

## 5. Recommended campaign shape

- **R0 — restate.** Replace the bundled stub by three separate declarations with
  corrected hypotheses: (i) coupling form of map alignment (MP maps, `[NoAtoms μ]`);
  (ii) measure-matched partition alignment; (iii) conjunct 3 + `[NoAtoms μ]`. Fix the
  three consumer sites (mechanical for InverseCounting and probably for the triangle;
  real work possible in Compactness). Statement changes here are *corrections of a
  sorried stub's contract*, but they touch consumers — do this first and get the
  whole project green with the narrowed stubs before proving anything.
- **R1 — the core.** `exists_measurePreserving_equiv_mod0_unitInterval`: atomless
  standard Borel probability space ≅ mod-0 `([0,1], λ)`. Construction: Borel iso to
  `[0,1]` (Mathlib) → pushforward `ν` → CDF `F(x) = ν[0,x]` pushes `ν` to `λ`
  (continuity from `NoAtoms`) → mod-0 invertibility by discarding the null set where
  `F` is locally constant → upgrade mod-0 iso to an everywhere `≃ᵐ` by null-set
  patching (uncountable-Borel patching, standard). **Mathlib-upstreamable.**
- **R2 — derive.** (iii) via interval rearrangement on `[0,1]` conjugated through R1;
  (i) via `Measure.condKernel` coupling + R1 re-typing; whatever corrected form
  Compactness needs.

Effort: R1 is a focused measure-theory campaign (CDF + mod-0 bookkeeping — fiddly but
classical); R0 is mostly plumbing with one open question (Compactness); R2 is
medium-sized derivation work. No step needs new combinatorics.

## 6. Impact

Every remaining `sorryAx` trace in the project (`cutDistance_triangle`,
`first_sampling_lemma`, `sampling_quantitative_icl`, `cutDistance_zero_of_homDensity_eq`,
Compactness alignment) flows through this one stub; R0–R2 would make the entire graphon
program axiom-clean.
